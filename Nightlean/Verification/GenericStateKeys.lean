import Nightlean.Verification.NativeRelation

namespace Nightlean.Verification.GenericStateKeys

private theorem eraseDups_length_le {α : Type} [BEq α] (items : List α) :
    items.eraseDups.length ≤ items.length := by
  cases items with
  | nil => simp
  | cons head tail =>
    rw [List.eraseDups_cons]
    simp only [List.length_cons]
    exact Nat.succ_le_succ (Nat.le_trans (eraseDups_length_le
      (tail.filter fun item => !(item == head))) (List.length_filter_le _ _))
termination_by items.length
decreasing_by
  simp_wf
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

theorem nodup_of_eraseDups_length_eq {α : Type} [BEq α] [LawfulBEq α]
    (items : List α) (sameLength : items.eraseDups.length = items.length) : items.Nodup := by
  induction items with
  | nil => simp
  | cons head tail ih =>
    rw [List.eraseDups_cons] at sameLength
    simp only [List.length_cons] at sameLength
    have dedupBound := eraseDups_length_le (tail.filter fun item => !(item == head))
    have filterBound := List.length_filter_le (fun item => !(item == head)) tail
    have filterLength : (tail.filter fun item => !(item == head)).length = tail.length := by
      omega
    have allRetained := List.length_filter_eq_length_iff.mp filterLength
    have unchanged : (tail.filter fun item => !(item == head)) = tail :=
      List.filter_eq_self.mpr allRetained
    have headAbsent : head ∉ tail := by
      intro member
      simpa using allRetained head member
    rw [unchanged] at sameLength
    exact List.nodup_cons.mpr ⟨headAbsent, ih (Nat.succ.inj sameLength)⟩

end Nightlean.Verification.GenericStateKeys
