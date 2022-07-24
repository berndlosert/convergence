
import algebra.group.extra
import data.set.extra
import data.set.pointwise
import order.filter.basic
import order.filter.pointwise

open filter function
open_locale filter pointwise

variables {α β G M : Type*}

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

lemma prod_inf_principal_mem_iff {f : filter α} {g : filter β} {s : set (α × β)} :
  ∀ t, t ∈ (f ×ᶠ g) ⊓ 𝓟 s ↔ ∃ (u ∈ f) (v ∈ g), (u ×ˢ v) ∩ s ⊆ t :=
begin
  intros t,
  split,
  { intro hmem,
    obtain ⟨l, hl, r, hr, heq⟩ := mem_inf_iff.mp hmem,
    obtain ⟨u, hu, v, hv, hsub⟩ := mem_prod_iff.mp hl,
    let hsub' := mem_principal.mp hr,
    let hsub'' := set.inter_subset_inter hsub hsub',
    rw ← heq at hsub'',
    exact ⟨u, hu, v, hv, hsub''⟩,
  },
  { rintro ⟨u, hu, v, hv, hsub⟩,
    rw mem_inf_iff_superset,
    have hsub' : u ×ˢ v ∈ f ×ᶠ g := 
      mem_prod_iff.mpr ⟨u, hu, v, hv, subset_refl (u ×ˢ v) ⟩,
    exact ⟨u ×ˢ v, hsub', s, mem_principal_self s, hsub⟩,
  },
end

lemma inf_ne_bot {f g : filter α} [f.ne_bot] (hle : f ≤ g) : (f ⊓ g).ne_bot :=
begin
  rw inf_of_le_left hle,
  assumption
end

/-!
### Pointwise stuff
-/

lemma mem_inv_iff [_root_.has_involutive_inv α] {f : filter α} {s : set α} :
  s ∈ f⁻¹ ↔ ∃ t ∈ f, t⁻¹ ⊆ s :=
begin
  split,
  { assume hmem,
    change s ∈ map has_inv.inv f at hmem,
    rw mem_map_iff_exists_image at hmem,
    obtain ⟨t, ht, hsub⟩ := hmem,
    rw [set.image_inv] at hsub,
    exact ⟨t, ht, hsub⟩ },
  { rintro ⟨t, ht, hsub⟩,
    exact mem_of_superset (filter.inv_mem_inv ht) hsub }
end

lemma mem_inv_smul_iff [has_smul G α] [_root_.has_involutive_inv G] {g : filter G} {f : filter α} {u : set α} :
  u ∈ g⁻¹ • f ↔ ∃ t s, t ∈ g ∧ s ∈ f ∧ t⁻¹ • s ⊆ u :=
begin
  split,
  { intros hmem,
    obtain ⟨t', s, ht', hs, hsub⟩ := mem_smul.mp hmem,
    rw mem_inv_iff at ht',
    obtain ⟨t, ht, hsub'⟩ := ht',
    refine ⟨t, s, ht, hs, _⟩,
    exact subset_trans (set.smul_subset_smul_right hsub') hsub },
  { rintros ⟨t, s, ht, hs, hsub⟩,
    have ht' : t⁻¹ ∈ g⁻¹ := inv_mem_inv ht,
    rw filter.mem_smul,
    refine ⟨t⁻¹, s, ht', hs, hsub⟩ }
end

lemma inv_smul_inf_ne_bot [group G] [mul_action G α] {g : filter G} {f f' : filter α} 
  (hle : f' ≤ g • f) [hf' : f'.ne_bot] : ((g⁻¹ • f') ⊓ f).ne_bot :=
begin
  rw ← forall_mem_nonempty_iff_ne_bot,
  intros s hmem,
  obtain ⟨s₁, hs₁, s₂, hs₂, hsub₁⟩ := mem_inf_iff_superset.mp hmem,
  obtain ⟨t₁, s₃, ht₁, hs₃, hsub₂⟩ := mem_inv_smul_iff.mp hs₁,
  refine set.subset_eq_nonempty hsub₁ _,
  refine set.subset_eq_nonempty (set.inter_subset_inter_left s₂ hsub₂) _,
  let s₄ : set α := s₃ ∩ (t₁ • s₂),
  have hne : s₄.nonempty, 
    from forall_mem_nonempty_iff_ne_bot.mpr hf' s₄
      (f'.inter_sets hs₃ (filter.le_def.mp hle (t₁ • s₂) (filter.smul_mem_smul ht₁ hs₂))),
  obtain ⟨y, hy⟩ := set.nonempty_def.mp hne,
  rw set.nonempty_def,
  obtain ⟨hy₁, hy₂⟩ := hy,
  change y ∈ set.image2 (•) t₁ s₂ at hy₂,
  obtain ⟨a, x, ha, hx, hy'⟩ := set.mem_image2.mp hy₂,
  have heq' : a⁻¹ • y = x, by simp [← hy', ← mul_smul],
  have hmem' : x ∈ t₁⁻¹ • s₃,
  begin
    simp [← heq'],
    have : a⁻¹ ∈ has_inv.inv '' t₁, from set.mem_image_of_mem (has_inv.inv) ha,
    have : a⁻¹ ∈ t₁⁻¹, by rwa set.image_inv at this, 
    exact set.mem_image2_of_mem this hy₁,
  end,
  exact ⟨x, hmem', hx⟩,
end

/-- The partial scalar multiplication of two filters. -/
def partial_smul [has_partial_smul M α] 
  (g : filter M) (f : filter α) : filter α := 
map (uncurry (•) : M × α → α) ((g ×ᶠ f) ⊓ 𝓟 (smul_dom M α))

end filter
