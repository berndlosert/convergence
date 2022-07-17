import data.set.basic

open set

variables {α : Type*}

namespace set

lemma subset_eq_nonempty {s t : set α} (hsub : t ⊆ s) (hne : t.nonempty) : s.nonempty :=
begin
  rw ← empty_ssubset at *,
  exact ssubset_of_ssubset_of_subset hne hsub,
end

lemma ne_empty_iff_exists_elem {s : set α} : ¬ (s = ∅) ↔ ∃ x, x ∈ s :=
begin
  split,
  { intros hne, 
    change s ≠ ∅ at hne, 
    rw [ne_empty_iff_nonempty, nonempty_def] at hne, 
    assumption },
  { intros hexists, 
    change s ≠ ∅, 
    rw ne_empty_iff_nonempty,
    exact nonempty_def.mpr hexists }
end

end set