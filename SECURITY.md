# Security

Nightlean is research-stage software. Published proofs have explicit scopes and assumptions. The project makes no production-readiness or end-to-end verified-contract claim. The [architecture and assurance overview](docs/designs/architecture.md#assurance-boundaries) records the current boundaries.

## Report a vulnerability

Use [GitHub private vulnerability reporting](https://github.com/awjreynolds/nightlean/security/advisories/new) for suspected vulnerabilities. Avoid posting exploitable details in a public issue before coordination.

Include the affected revision and target profile, a minimal reproduction, the expected and observed behavior, and the security boundary affected. Remove live credentials, wallet seeds, private witnesses and private-state journals from the report. Synthetic test data is preferable.

Lean source and imports are executable development inputs. The circuit DSL does not sandbox elaborators or metaprograms. Compile trusted source in an appropriate development environment. Localnet development identities and fixtures are public test data.
