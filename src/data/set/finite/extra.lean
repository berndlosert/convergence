import data.set.finite

lemma set.finite.induction_on' {α : Type*} {p : Π (s : set α), s.finite → Prop}
  {S : set α} (h : S.finite) (h₁ : ∀ h, p ∅ h)
  (h₂ : ∀ {a s h₁ h₂}, a ∈ S → s ⊆ S → a ∉ s → p s h₁ → p (insert a s) h₂) : p S h :=
begin
  classical,
  have h₃ := @finset.induction_on' α (λ s, p (s : set α) (finset.finite_to_set _))
    (by apply_instance) h.to_finset (h₁ set.finite_empty),
  specialize h₃ _,
  { rintro x t h₃ h₄ h₅ h₆, push_cast,
    apply @h₂ x t (finset.finite_to_set _) (set.finite_of_fintype _)
    ((set.finite.mem_to_finset h).mp h₃) ((set.subset_to_finset_iff h).mp h₄)
    (mt finset.mem_coe.mp h₅) h₆ },
  simp only [set.finite.coe_to_finset] at h₃,
  assumption,
end