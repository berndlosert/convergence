
import algebra.group.extra
import data.set.extra
import data.set.pointwise
import order.filter.basic
import order.filter.pointwise

open filter function
open_locale filter pointwise

variables {α G M : Type*}

namespace filter

/-!
### Basic stuff
-/

lemma inf_neq_bot_iff {f g : filter α} : 
  (f ⊓ g) ≠ ⊥ ↔ ∀ (s ∈ f) (t ∈ g), s ∩ t ≠ ∅ :=
begin
  let hiff := iff.not inf_eq_bot_iff,
  push_neg at hiff,
  assumption,
end

lemma mem_inv_iff [has_involutive_inv α] {s : set α} {f : filter α} : 
  s ∈ f⁻¹ ↔ ∃ t ∈ f, t⁻¹ ⊆ s :=
begin
  split,
  { assume hmem : s ∈ f⁻¹,
    change s ∈ map has_inv.inv f at hmem,
    rw mem_map_iff_exists_image at hmem,
    obtain ⟨t, ht, hsub⟩ := hmem,
    rw [set.image_inv] at hsub,
    exact ⟨t, ht, hsub⟩ },
  { rintro ⟨t, ht, hsub⟩,
    exact mem_of_superset (filter.inv_mem_inv ht) hsub }
end

lemma inf_ne_bot {f g : filter α} [f.ne_bot] (hle : f ≤ g) : (f ⊓ g).ne_bot :=
begin
  rw inf_of_le_left hle,
  assumption
end

/-!
### Pointwise stuff
-/

lemma inv_smul_of_smul [group G] [mul_action G α] {g : filter G} {f f' : filter α} 
  (hle : f' ≤ g • f) [hf' : f'.ne_bot] : ((g⁻¹ • f') ⊓ f).ne_bot :=
begin
  rw ← forall_mem_nonempty_iff_ne_bot,
  intros s hmem,
  obtain ⟨s₁, hs₁, s₂, hs₂, hsub₁⟩ := mem_inf_iff_superset.mp hmem,
  obtain ⟨t₁, s₃, ht₁, hs₃, hsub₂⟩ := filter.mem_smul.mp hs₁,
  refine set.subset_eq_nonempty hsub₁ _,
  obtain ⟨t₂, ht₂, hsub₃⟩ := filter.mem_inv_iff.mp ht₁,
  have hsub₄ : t₂⁻¹ • s₃ ⊆ s₁, 
    from subset_trans (set.smul_subset_smul_right hsub₃) hsub₂,
  refine set.subset_eq_nonempty (set.inter_subset_inter_left s₂ hsub₄) _,
  let s₄ : set α := s₃ ∩ (t₂ • s₂),
  have hne : s₄.nonempty, 
    from forall_mem_nonempty_iff_ne_bot.mpr hf' s₄
      (f'.inter_sets hs₃ (filter.le_def.mp hle (t₂ • s₂) (filter.smul_mem_smul ht₂ hs₂))),
  obtain ⟨y, hy⟩ := set.nonempty_def.mp hne,
  rw set.nonempty_def,
  obtain ⟨hy₁, hy₂⟩ := hy,
  change y ∈ set.image2 (•) t₂ s₂ at hy₂,
  obtain ⟨a, x, ha, hx, hy'⟩ := set.mem_image2.mp hy₂,
  have heq' : a⁻¹ • y = x, by simp [← hy', ← mul_smul],
  have hmem' : x ∈ t₂⁻¹ • s₃,
  begin
    simp [← heq'],
    have : a⁻¹ ∈ has_inv.inv '' t₂, from set.mem_image_of_mem (has_inv.inv) ha,
    have : a⁻¹ ∈ t₂⁻¹, by rwa set.image_inv at this, 
    exact set.mem_image2_of_mem this hy₁,
  end,
  exact ⟨x, hmem', hx⟩,
end

/-- `partial_smul` lifted to filters. -/
def partial_smul [has_partial_scalar M α] 
  (g : filter M) (f : filter α) : filter α := 
map (uncurry (•) : M × α → α) ((g ×ᶠ f) ⊓ 𝓟 (smul_dom M α))

infix ` •ᶠ `:73 := filter.partial_smul

end filter
