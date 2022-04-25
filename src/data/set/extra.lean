import data.set.basic

open set

variables {α : Type*}

namespace set

lemma subset_eq_nonempty {s t : set α} (hsub : t ⊆ s) (hne : t.nonempty) : s.nonempty :=
begin
  rw ← empty_ssubset at *,
  exact ssubset_of_ssubset_of_subset hne hsub,
end

end set