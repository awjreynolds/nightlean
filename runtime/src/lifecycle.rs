//! Pure ticket lifecycle model for host-managed persistence and CAS evidence.
//!
//! This module stores public lifecycle identifiers and evidence flags only. It
//! performs no I/O, clock reads, or random generation. `Accepted` records a host
//! report, not a successful commit. Only a validated `CasCommitted` event records
//! CAS success. The host remains responsible for the truth of persistence,
//! submission, acceptance, and CAS notifications.

use std::fmt;

/// The externally observable phase of a lifecycle attempt.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Phase {
    Open,
    Prepared,
    Submitted,
    Uncertain,
    AwaitingCas,
    Committed,
    Rejected,
    Cancelled,
    Failed,
    Conflicted,
}

/// A lifecycle transition failure.
///
/// Display messages are static and never include caller supplied identifiers.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    Identity,
    InvalidState,
    InvalidResponse,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Identity => "lifecycle identity is invalid or does not match",
            Self::InvalidState => "event is invalid in the current lifecycle phase",
            Self::InvalidResponse => "host response is invalid",
        })
    }
}

impl std::error::Error for Error {}

/// Inputs that advance or report the lifecycle.
#[derive(Debug, PartialEq, Eq)]
pub enum Event {
    ExecutionSucceeded,
    ExecutionFailed,
    Cancel,
    Bind {
        transaction_id: String,
    },
    Persisted {
        transaction_id: String,
        attempt_id: String,
    },
    Submitted {
        transaction_id: String,
        attempt_id: String,
    },
    Accepted {
        transaction_id: String,
        attempt_id: String,
    },
    Rejected {
        transaction_id: String,
        attempt_id: String,
    },
    Uncertain {
        transaction_id: String,
        attempt_id: String,
    },
    CasCommitted {
        transaction_id: String,
        attempt_id: String,
        base_revision: String,
        revision: String,
    },
    CasConflict {
        transaction_id: String,
        attempt_id: String,
        base_revision: String,
        revision: String,
    },
}

/// Work the host must perform after a successful transition.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Effect {
    None,
    /// Submit or retry the same CAS request, keyed by attempt, transaction, and base revision.
    RequestCas,
    /// Discard locally retained update material after a terminal outcome.
    /// Durable persistence and deduplication receipts remain host responsibilities.
    DropJournal,
}

/// Pure state for one ticket attempt.
///
/// Identifiers and evidence flags are private so callers must advance the model
/// through [`Lifecycle::apply`].
pub struct Lifecycle {
    phase: Phase,
    attempt_id: String,
    base_revision: String,
    transaction_id: Option<String>,
    successful_execution: bool,
    persisted: bool,
    submitted: bool,
    accepted_host_evidence: bool,
    committed_revision: Option<String>,
    conflict_revision: Option<String>,
}

impl Lifecycle {
    /// Start an attempt with canonical 256-bit identities and a bounded ASCII
    /// base revision.
    ///
    /// Attempt IDs and transaction IDs are exactly 64 lowercase hexadecimal
    /// characters without a `0x` prefix. This model makes no claim about how the
    /// host generated an identity. Revisions contain 1 to 128 ASCII alphanumeric
    /// characters or `-`, `_`, `.`, and `:`.
    pub fn new(attempt_id: String, base_revision: String) -> Result<Self, Error> {
        if !is_canonical_hash(&attempt_id) {
            return Err(Error::Identity);
        }
        if !is_revision(&base_revision) {
            return Err(Error::InvalidResponse);
        }
        Ok(Self {
            phase: Phase::Open,
            attempt_id,
            base_revision,
            transaction_id: None,
            successful_execution: false,
            persisted: false,
            submitted: false,
            accepted_host_evidence: false,
            committed_revision: None,
            conflict_revision: None,
        })
    }

    pub fn phase(&self) -> Phase {
        self.phase
    }

    pub fn transaction_id(&self) -> Option<&str> {
        self.transaction_id.as_deref()
    }

    /// Whether the host reported persisting this attempt's journal entry.
    /// This is historical evidence and stays true after a terminal cleanup effect.
    pub fn persisted(&self) -> bool {
        self.persisted
    }

    /// Whether the host reported that the transaction was accepted.
    /// This does not imply CAS success.
    pub fn accepted_host_evidence(&self) -> bool {
        self.accepted_host_evidence
    }

    pub fn committed_revision(&self) -> Option<&str> {
        self.committed_revision.as_deref()
    }

    pub fn attempt_id(&self) -> &str {
        &self.attempt_id
    }

    pub fn base_revision(&self) -> &str {
        &self.base_revision
    }

    /// Check internal state relationships without consulting the host.
    ///
    /// A committed phase requires successful execution, a bound transaction,
    /// persistence and submission evidence, accepted host evidence, and a
    /// validated CAS revision different from the immutable base revision.
    pub fn invariant(&self) -> bool {
        if !is_canonical_hash(&self.attempt_id)
            || !is_revision(&self.base_revision)
            || self
                .transaction_id
                .as_deref()
                .is_some_and(|id| !is_canonical_hash(id))
        {
            return false;
        }

        let has_transaction = self.transaction_id.is_some();
        let has_commit = self.committed_revision.is_some();
        let has_conflict = self.conflict_revision.is_some();
        if self.committed_revision.as_deref().is_some_and(|revision| {
            !is_revision(revision) || revision == self.base_revision.as_str()
        }) || self.conflict_revision.as_deref().is_some_and(|revision| {
            !is_revision(revision) || revision == self.base_revision.as_str()
        }) {
            return false;
        }

        match self.phase {
            Phase::Open => {
                !self.successful_execution
                    && !has_transaction
                    && !self.persisted
                    && !self.submitted
                    && !self.accepted_host_evidence
                    && !has_commit
                    && !has_conflict
            }
            Phase::Prepared => {
                self.successful_execution
                    && (has_transaction || !self.persisted)
                    && !self.submitted
                    && !self.accepted_host_evidence
                    && !has_commit
                    && !has_conflict
            }
            Phase::Submitted => {
                self.successful_execution
                    && has_transaction
                    && self.persisted
                    && self.submitted
                    && !self.accepted_host_evidence
                    && !has_commit
                    && !has_conflict
            }
            Phase::Uncertain => {
                self.successful_execution
                    && has_transaction
                    && self.persisted
                    && self.submitted
                    && !self.accepted_host_evidence
                    && !has_commit
                    && !has_conflict
            }
            Phase::AwaitingCas => {
                self.successful_execution
                    && has_transaction
                    && self.persisted
                    && self.submitted
                    && self.accepted_host_evidence
                    && !has_commit
                    && !has_conflict
            }
            Phase::Committed => {
                self.successful_execution
                    && has_transaction
                    && self.persisted
                    && self.submitted
                    && self.accepted_host_evidence
                    && has_commit
                    && !has_conflict
            }
            Phase::Rejected => {
                self.successful_execution
                    && has_transaction
                    && self.persisted
                    && self.submitted
                    && !self.accepted_host_evidence
                    && !has_commit
                    && !has_conflict
            }
            Phase::Cancelled => {
                (self.successful_execution || (!has_transaction && !self.persisted))
                    && (!self.persisted || has_transaction)
                    && !self.submitted
                    && !self.accepted_host_evidence
                    && !has_commit
                    && !has_conflict
            }
            Phase::Failed => {
                !self.successful_execution
                    && !has_transaction
                    && !self.persisted
                    && !self.submitted
                    && !self.accepted_host_evidence
                    && !has_commit
                    && !has_conflict
            }
            Phase::Conflicted => {
                self.successful_execution
                    && has_transaction
                    && self.persisted
                    && self.submitted
                    && self.accepted_host_evidence
                    && !has_commit
                    && has_conflict
            }
        }
    }

    /// Apply an event, validating all supplied identity and response fields
    /// before mutating state.
    pub fn apply(&mut self, event: Event) -> Result<Effect, Error> {
        match event {
            Event::ExecutionSucceeded => match self.phase {
                Phase::Open => {
                    self.successful_execution = true;
                    self.phase = Phase::Prepared;
                    Ok(Effect::None)
                }
                Phase::Prepared if self.successful_execution => Ok(Effect::None),
                _ => Err(Error::InvalidState),
            },
            Event::ExecutionFailed => match self.phase {
                Phase::Open => {
                    self.phase = Phase::Failed;
                    Ok(Effect::DropJournal)
                }
                Phase::Failed => Ok(Effect::None),
                _ => Err(Error::InvalidState),
            },
            Event::Cancel => match self.phase {
                Phase::Open | Phase::Prepared => {
                    self.phase = Phase::Cancelled;
                    Ok(Effect::DropJournal)
                }
                Phase::Cancelled => Ok(Effect::None),
                _ => Err(Error::InvalidState),
            },
            Event::Bind { transaction_id } => {
                if !is_canonical_hash(&transaction_id) {
                    return Err(Error::Identity);
                }
                if let Some(bound_id) = self.transaction_id.as_deref() {
                    return if bound_id == transaction_id.as_str() {
                        Ok(Effect::None)
                    } else {
                        Err(Error::Identity)
                    };
                }
                if self.phase != Phase::Prepared {
                    return Err(Error::InvalidState);
                }
                self.transaction_id = Some(transaction_id);
                Ok(Effect::None)
            }
            Event::Persisted {
                transaction_id,
                attempt_id,
            } => {
                self.validate_identity(&transaction_id, &attempt_id)?;
                if self.persisted {
                    return Ok(Effect::None);
                }
                if self.phase != Phase::Prepared {
                    return Err(Error::InvalidState);
                }
                self.persisted = true;
                Ok(Effect::None)
            }
            Event::Submitted {
                transaction_id,
                attempt_id,
            } => {
                self.validate_identity(&transaction_id, &attempt_id)?;
                if self.submitted {
                    return Ok(Effect::None);
                }
                if self.phase != Phase::Prepared || !self.persisted {
                    return Err(Error::InvalidState);
                }
                self.submitted = true;
                self.phase = Phase::Submitted;
                Ok(Effect::None)
            }
            Event::Uncertain {
                transaction_id,
                attempt_id,
            } => {
                self.validate_identity(&transaction_id, &attempt_id)?;
                match self.phase {
                    Phase::Submitted => {
                        self.phase = Phase::Uncertain;
                        Ok(Effect::None)
                    }
                    Phase::Uncertain | Phase::AwaitingCas => Ok(Effect::None),
                    _ => Err(Error::InvalidState),
                }
            }
            Event::Accepted {
                transaction_id,
                attempt_id,
            } => {
                self.validate_identity(&transaction_id, &attempt_id)?;
                match self.phase {
                    Phase::Submitted | Phase::Uncertain => {
                        self.accepted_host_evidence = true;
                        self.phase = Phase::AwaitingCas;
                        Ok(Effect::RequestCas)
                    }
                    Phase::AwaitingCas => Ok(Effect::RequestCas),
                    Phase::Committed => Ok(Effect::None),
                    _ => Err(Error::InvalidState),
                }
            }
            Event::Rejected {
                transaction_id,
                attempt_id,
            } => {
                self.validate_identity(&transaction_id, &attempt_id)?;
                match self.phase {
                    Phase::Submitted | Phase::Uncertain => {
                        self.phase = Phase::Rejected;
                        Ok(Effect::DropJournal)
                    }
                    Phase::Rejected => Ok(Effect::None),
                    _ => Err(Error::InvalidState),
                }
            }
            Event::CasCommitted {
                transaction_id,
                attempt_id,
                base_revision,
                revision,
            } => {
                self.validate_cas_response(
                    &transaction_id,
                    &attempt_id,
                    &base_revision,
                    &revision,
                )?;
                match self.phase {
                    Phase::AwaitingCas if self.cas_evidence_ready() => {
                        self.committed_revision = Some(revision);
                        self.phase = Phase::Committed;
                        Ok(Effect::DropJournal)
                    }
                    Phase::AwaitingCas => Err(Error::InvalidState),
                    Phase::Committed
                        if self.committed_revision.as_deref() == Some(revision.as_str()) =>
                    {
                        Ok(Effect::None)
                    }
                    Phase::Committed => Err(Error::InvalidResponse),
                    _ => Err(Error::InvalidState),
                }
            }
            Event::CasConflict {
                transaction_id,
                attempt_id,
                base_revision,
                revision,
            } => {
                self.validate_cas_response(
                    &transaction_id,
                    &attempt_id,
                    &base_revision,
                    &revision,
                )?;
                match self.phase {
                    Phase::AwaitingCas if self.cas_evidence_ready() => {
                        self.conflict_revision = Some(revision);
                        self.phase = Phase::Conflicted;
                        Ok(Effect::DropJournal)
                    }
                    Phase::AwaitingCas => Err(Error::InvalidState),
                    Phase::Conflicted
                        if self.conflict_revision.as_deref() == Some(revision.as_str()) =>
                    {
                        Ok(Effect::None)
                    }
                    Phase::Conflicted => Err(Error::InvalidResponse),
                    _ => Err(Error::InvalidState),
                }
            }
        }
    }

    fn validate_transaction(&self, transaction_id: &str) -> Result<(), Error> {
        if !is_canonical_hash(transaction_id)
            || self.transaction_id.as_deref() != Some(transaction_id)
        {
            return Err(Error::Identity);
        }
        Ok(())
    }

    fn cas_evidence_ready(&self) -> bool {
        self.successful_execution
            && self.transaction_id.is_some()
            && self.persisted
            && self.submitted
            && self.accepted_host_evidence
    }

    fn validate_identity(&self, transaction_id: &str, attempt_id: &str) -> Result<(), Error> {
        self.validate_transaction(transaction_id)?;
        if !is_canonical_hash(attempt_id) || self.attempt_id.as_str() != attempt_id {
            return Err(Error::Identity);
        }
        Ok(())
    }

    fn validate_cas_response(
        &self,
        transaction_id: &str,
        attempt_id: &str,
        base_revision: &str,
        revision: &str,
    ) -> Result<(), Error> {
        self.validate_identity(transaction_id, attempt_id)?;
        if !is_revision(base_revision) || !is_revision(revision) {
            return Err(Error::InvalidResponse);
        }
        if base_revision != self.base_revision.as_str() {
            return Err(Error::Identity);
        }
        if revision == self.base_revision.as_str() {
            return Err(Error::InvalidResponse);
        }
        Ok(())
    }
}

fn is_canonical_hash(value: &str) -> bool {
    value.len() == 64
        && value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

fn is_revision(value: &str) -> bool {
    !value.is_empty()
        && value.len() <= 128
        && value
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'-' | b'_' | b'.' | b':'))
}

#[cfg(test)]
mod tests {
    use super::{Effect, Error, Event, Lifecycle, Phase};

    const ATTEMPT: &str = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
    const TX: &str = "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";
    const OTHER_TX: &str = "cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc";

    fn lifecycle() -> Lifecycle {
        Lifecycle::new(ATTEMPT.to_owned(), "rev-1".to_owned()).unwrap()
    }

    fn prepared() -> Lifecycle {
        let mut model = lifecycle();
        assert_eq!(model.apply(Event::ExecutionSucceeded), Ok(Effect::None));
        assert_eq!(model.phase(), Phase::Prepared);
        assert!(model.invariant());
        model
    }

    fn bound_persisted() -> Lifecycle {
        let mut model = prepared();
        assert_eq!(
            model.apply(Event::Bind {
                transaction_id: TX.to_owned(),
            }),
            Ok(Effect::None)
        );
        assert_eq!(
            model.apply(Event::Persisted {
                transaction_id: TX.to_owned(),
                attempt_id: ATTEMPT.to_owned(),
            }),
            Ok(Effect::None)
        );
        assert!(model.invariant());
        model
    }

    fn submitted() -> Lifecycle {
        let mut model = bound_persisted();
        assert_eq!(
            model.apply(Event::Submitted {
                transaction_id: TX.to_owned(),
                attempt_id: ATTEMPT.to_owned(),
            }),
            Ok(Effect::None)
        );
        assert_eq!(model.phase(), Phase::Submitted);
        assert!(model.invariant());
        model
    }

    fn awaiting_cas() -> Lifecycle {
        let mut model = submitted();
        assert_eq!(
            model.apply(Event::Accepted {
                transaction_id: TX.to_owned(),
                attempt_id: ATTEMPT.to_owned(),
            }),
            Ok(Effect::RequestCas)
        );
        assert_eq!(model.phase(), Phase::AwaitingCas);
        assert!(model.accepted_host_evidence());
        assert_eq!(model.committed_revision(), None);
        assert!(model.invariant());
        model
    }

    fn assert_unchanged_after_error(model: &mut Lifecycle, event: Event, expected: Error) {
        let phase = model.phase();
        let transaction_id = model.transaction_id().map(str::to_owned);
        let persisted = model.persisted();
        let accepted = model.accepted_host_evidence();
        let committed_revision = model.committed_revision().map(str::to_owned);
        assert_eq!(model.apply(event), Err(expected));
        assert_eq!(model.phase(), phase);
        assert_eq!(model.transaction_id(), transaction_id.as_deref());
        assert_eq!(model.persisted(), persisted);
        assert_eq!(model.accepted_host_evidence(), accepted);
        assert_eq!(model.committed_revision(), committed_revision.as_deref());
        assert!(model.invariant());
    }

    #[test]
    fn constructor_checks_attempt_and_revision_without_echoing_values() {
        assert_eq!(
            Lifecycle::new("bad-attempt".to_owned(), "rev-1".to_owned())
                .err()
                .unwrap(),
            Error::Identity
        );
        assert_eq!(
            Lifecycle::new(ATTEMPT.to_owned(), "not a revision".to_owned())
                .err()
                .unwrap(),
            Error::InvalidResponse
        );
        assert_eq!(
            Lifecycle::new(ATTEMPT.to_owned(), "rev-1".to_owned())
                .unwrap()
                .phase(),
            Phase::Open
        );
        assert_eq!(
            Error::Identity.to_string(),
            "lifecycle identity is invalid or does not match"
        );
    }

    #[test]
    fn valid_execution_persistence_acceptance_and_cas_flow() {
        let mut model = awaiting_cas();
        assert_eq!(
            model.apply(Event::CasCommitted {
                transaction_id: TX.to_owned(),
                attempt_id: ATTEMPT.to_owned(),
                base_revision: "rev-1".to_owned(),
                revision: "rev-2".to_owned(),
            }),
            Ok(Effect::DropJournal)
        );
        assert_eq!(model.phase(), Phase::Committed);
        assert_eq!(model.committed_revision(), Some("rev-2"));
        assert!(model.persisted());
        assert!(model.invariant());
    }

    #[test]
    fn valid_transitions_cover_uncertain_rejection_cancel_failure_and_conflict() {
        let mut uncertain = submitted();
        let uncertain_event = || Event::Uncertain {
            transaction_id: TX.to_owned(),
            attempt_id: ATTEMPT.to_owned(),
        };
        assert_eq!(uncertain.apply(uncertain_event()), Ok(Effect::None));
        assert_eq!(uncertain.phase(), Phase::Uncertain);
        assert_eq!(uncertain.apply(uncertain_event()), Ok(Effect::None));
        assert_eq!(
            uncertain.apply(Event::Accepted {
                transaction_id: TX.to_owned(),
                attempt_id: ATTEMPT.to_owned(),
            }),
            Ok(Effect::RequestCas)
        );
        assert!(uncertain.invariant());

        let mut rejected = submitted();
        let reject_event = || Event::Rejected {
            transaction_id: TX.to_owned(),
            attempt_id: ATTEMPT.to_owned(),
        };
        assert_eq!(rejected.apply(reject_event()), Ok(Effect::DropJournal));
        assert_eq!(rejected.phase(), Phase::Rejected);
        assert_eq!(rejected.apply(reject_event()), Ok(Effect::None));
        assert!(rejected.invariant());

        let mut cancelled = prepared();
        assert_eq!(cancelled.apply(Event::Cancel), Ok(Effect::DropJournal));
        assert_eq!(cancelled.phase(), Phase::Cancelled);
        assert_eq!(cancelled.apply(Event::Cancel), Ok(Effect::None));
        assert!(cancelled.invariant());

        let mut failed = lifecycle();
        assert_eq!(
            failed.apply(Event::ExecutionFailed),
            Ok(Effect::DropJournal)
        );
        assert_eq!(failed.phase(), Phase::Failed);
        assert_eq!(failed.apply(Event::ExecutionFailed), Ok(Effect::None));
        assert!(failed.invariant());

        let mut conflicted = awaiting_cas();
        let conflict_event = || Event::CasConflict {
            transaction_id: TX.to_owned(),
            attempt_id: ATTEMPT.to_owned(),
            base_revision: "rev-1".to_owned(),
            revision: "rev-3".to_owned(),
        };
        assert_eq!(conflicted.apply(conflict_event()), Ok(Effect::DropJournal));
        assert_eq!(conflicted.phase(), Phase::Conflicted);
        assert_eq!(conflicted.apply(conflict_event()), Ok(Effect::None));
        assert!(conflicted.invariant());
    }

    #[test]
    fn errors_leave_state_unchanged() {
        let mut open = lifecycle();
        assert_unchanged_after_error(
            &mut open,
            Event::Accepted {
                transaction_id: TX.to_owned(),
                attempt_id: ATTEMPT.to_owned(),
            },
            Error::Identity,
        );

        let mut prepared = prepared();
        assert_unchanged_after_error(
            &mut prepared,
            Event::Submitted {
                transaction_id: TX.to_owned(),
                attempt_id: ATTEMPT.to_owned(),
            },
            Error::Identity,
        );

        let mut waiting = awaiting_cas();
        assert_unchanged_after_error(
            &mut waiting,
            Event::CasCommitted {
                transaction_id: TX.to_owned(),
                attempt_id: ATTEMPT.to_owned(),
                base_revision: "rev-1".to_owned(),
                revision: "rev-1".to_owned(),
            },
            Error::InvalidResponse,
        );
        assert_unchanged_after_error(
            &mut waiting,
            Event::CasConflict {
                transaction_id: TX.to_owned(),
                attempt_id: ATTEMPT.to_owned(),
                base_revision: "rev-1".to_owned(),
                revision: "rev-1".to_owned(),
            },
            Error::InvalidResponse,
        );
    }

    #[test]
    fn wrong_attempt_transaction_and_base_are_rejected_without_mutation() {
        let mut model = submitted();
        assert_unchanged_after_error(
            &mut model,
            Event::Accepted {
                transaction_id: TX.to_owned(),
                attempt_id: OTHER_TX.to_owned(),
            },
            Error::Identity,
        );
        assert_unchanged_after_error(
            &mut model,
            Event::Accepted {
                transaction_id: OTHER_TX.to_owned(),
                attempt_id: ATTEMPT.to_owned(),
            },
            Error::Identity,
        );

        let mut waiting = awaiting_cas();
        assert_unchanged_after_error(
            &mut waiting,
            Event::CasCommitted {
                transaction_id: TX.to_owned(),
                attempt_id: ATTEMPT.to_owned(),
                base_revision: "rev-stale".to_owned(),
                revision: "rev-2".to_owned(),
            },
            Error::Identity,
        );
    }

    #[test]
    fn acceptance_requests_cas_but_never_commits_by_itself() {
        let mut model = submitted();
        assert_eq!(
            model.apply(Event::Accepted {
                transaction_id: TX.to_owned(),
                attempt_id: ATTEMPT.to_owned(),
            }),
            Ok(Effect::RequestCas)
        );
        assert_eq!(model.phase(), Phase::AwaitingCas);
        assert_eq!(model.committed_revision(), None);
        assert!(model.invariant());
    }

    #[test]
    fn accepted_retry_reissues_same_cas_and_uncertainty_never_commits() {
        let mut model = submitted();
        let uncertain = || Event::Uncertain {
            transaction_id: TX.to_owned(),
            attempt_id: ATTEMPT.to_owned(),
        };
        let accepted = || Event::Accepted {
            transaction_id: TX.to_owned(),
            attempt_id: ATTEMPT.to_owned(),
        };
        assert_eq!(model.apply(uncertain()), Ok(Effect::None));
        assert_eq!(model.apply(uncertain()), Ok(Effect::None));
        assert_eq!(model.apply(accepted()), Ok(Effect::RequestCas));
        assert_eq!(model.apply(uncertain()), Ok(Effect::None));
        assert_eq!(model.apply(accepted()), Ok(Effect::RequestCas));
        assert_eq!(model.phase(), Phase::AwaitingCas);
        assert_eq!(model.committed_revision(), None);
        assert!(model.invariant());
    }

    #[test]
    fn cancellation_after_submission_and_commit_is_rejected() {
        let mut model = submitted();
        assert_unchanged_after_error(&mut model, Event::Cancel, Error::InvalidState);

        let mut committed = awaiting_cas();
        assert_eq!(
            committed.apply(Event::CasCommitted {
                transaction_id: TX.to_owned(),
                attempt_id: ATTEMPT.to_owned(),
                base_revision: "rev-1".to_owned(),
                revision: "rev-2".to_owned(),
            }),
            Ok(Effect::DropJournal)
        );
        assert_unchanged_after_error(&mut committed, Event::Cancel, Error::InvalidState);
    }

    #[test]
    fn duplicate_commit_is_idempotent_and_conflicting_commit_is_rejected() {
        let mut model = awaiting_cas();
        let committed = || Event::CasCommitted {
            transaction_id: TX.to_owned(),
            attempt_id: ATTEMPT.to_owned(),
            base_revision: "rev-1".to_owned(),
            revision: "rev-2".to_owned(),
        };
        assert_eq!(model.apply(committed()), Ok(Effect::DropJournal));
        assert_eq!(model.apply(committed()), Ok(Effect::None));
        assert_eq!(model.committed_revision(), Some("rev-2"));
        assert_unchanged_after_error(
            &mut model,
            Event::CasCommitted {
                transaction_id: TX.to_owned(),
                attempt_id: ATTEMPT.to_owned(),
                base_revision: "rev-1".to_owned(),
                revision: "rev-3".to_owned(),
            },
            Error::InvalidResponse,
        );
    }

    #[test]
    fn binding_is_immutable_and_persistence_is_required_before_submission() {
        let mut model = prepared();
        assert_unchanged_after_error(
            &mut model,
            Event::Submitted {
                transaction_id: TX.to_owned(),
                attempt_id: ATTEMPT.to_owned(),
            },
            Error::Identity,
        );
        assert_eq!(
            model.apply(Event::Bind {
                transaction_id: TX.to_owned(),
            }),
            Ok(Effect::None)
        );
        assert_eq!(
            model.apply(Event::Bind {
                transaction_id: TX.to_owned(),
            }),
            Ok(Effect::None)
        );
        assert_unchanged_after_error(
            &mut model,
            Event::Bind {
                transaction_id: OTHER_TX.to_owned(),
            },
            Error::Identity,
        );
        assert!(model.invariant());
    }
}
