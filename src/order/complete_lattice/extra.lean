import order.complete_lattice

variables {α β : Type*}

lemma Sup_image_le [complete_semilattice_Sup β] 
  {f g : α → β} (hle : f ≤ g) (s : set α) : Sup (f '' s) ≤ Sup (g '' s) :=
begin
  refine Sup_le_Sup_of_forall_exists_le _,
  intros y hy,
  obtain ⟨x, hx, heq⟩ := set.mem_image_iff_bex.mp hy,
  use g x, refine ⟨set.mem_image_of_mem g hx, _⟩,
  rw ← heq, exact hle x,
end