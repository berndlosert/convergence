import algebra.group.defs
import data.set.basic
import data.set.finite
import data.set.prod
import data.set.pointwise
import algebra.support
import order.complete_lattice
import order.filter.basic
import order.filter.pointwise

open filter function
open_locale filter pointwise

variables {α β G M : Type*}

/-!
### Partial scalar actions
-/

/-- Typeclass for partial scalar actions. `smul_defined a x` means that `a • x` is defined. -/
class has_partial_smul (M α : Type*) extends has_smul M α :=
(smul_defined : M → α → Prop)

export has_partial_smul

/-- The domain of defintion of a partial action. -/
def smul_dom (M α : Type*) [has_partial_smul M α] := { p : M × α | smul_defined p.1 p.2 }

lemma smul_dom_mem_iff [has_partial_smul M α] {a : M} {x : α} :
  smul_defined a x ↔ (a, x) ∈ smul_dom M α := by tautology

/-- The partial_smul of two sets. -/
def set.partial_smul [has_partial_smul M α] (t : set M) (s : set α) : set α :=
  (λ p : M × α, p.1 • p.2) '' ((t ×ˢ s) ∩ smul_dom M α)

/-- The partial scalar multiplication of two filters. -/
def filter.partial_smul [has_partial_smul M α] 
  (g : filter M) (f : filter α) : filter α := 
map (λ p : M × α, p.1 • p.2) ((g ×ᶠ f) ⊓ 𝓟 (smul_dom M α))  

/-- Typeclass for partial actions of groups. -/
class partial_mul_action (G α : Type*) [group G]
  extends has_partial_smul G α :=
(one_smul : ∀ (x : α), smul_defined 1 x ∧ (1 : G) • x = x)
(mul_smul : ∀ {a b : G} {x : α}, smul_defined b x → smul_defined a (b • x) →
  smul_defined (a * b) x ∧ (a * b) • x = a • (b • x))
(inv_smul_cancel_left : ∀ {a : G} {x y : α}, 
  smul_defined a x → a • x = y → smul_defined a⁻¹ y ∧ x = a⁻¹ • y)

export partial_mul_action

lemma partial_mul_action.injective [group G] [partial_mul_action G α]:
  ∀ {a : G} {x y : α}, smul_defined a x → smul_defined a y → a • x = a • y → x = y :=
begin
  intros a x y hdef₁ hdef₂ heq₁,
  obtain ⟨hdef₃, heq₂⟩ := inv_smul_cancel_left hdef₁ heq₁,
  obtain ⟨hdef₄, heq₃⟩ := mul_smul hdef₂ hdef₃,
  simp [(one_smul y).2] at heq₃,
  exact (rfl.congr (eq.symm heq₃)).mp heq₂,
end

/-!
### Enveloping action
-/

def envelope (G α : Type*) [group G] [partial_mul_action G α] : G × α → G × α → Prop :=
 λ ⟨a, x⟩ ⟨b, y⟩, smul_defined (b⁻¹ * a) x ∧ (b⁻¹ * a) • x = y

namespace envelope

abbreviation space (G α : Type*) [group G] [partial_mul_action G α] := quot (envelope G α)

def embed (G : Type*) {α : Type*} [group G] [partial_mul_action G α]
  (x : α) : space G α := quot.mk (envelope G α) (1, x)

variables [group G] [partial_mul_action G α]

lemma is_reflexive : reflexive (envelope G α) := 
begin
  rintro (⟨a, x⟩ : G × α),
  unfold envelope, simp,
  exact one_smul x,
end

lemma is_symmetric : symmetric (envelope G α) :=
begin
  rintro ⟨a, x⟩ ⟨b, y⟩,
  unfold envelope, rintro ⟨hdef, heq⟩,
  obtain ⟨hdef', heq'⟩ := inv_smul_cancel_left hdef heq,
  simp at *, exact ⟨hdef', eq.symm heq'⟩,
end

lemma is_transitive : transitive (envelope G α) := 
begin
  rintro ⟨a, x⟩ ⟨b, y⟩ ⟨c, z⟩ : G × α,
  unfold envelope,
  rintro ⟨hdef₁, heq₁⟩ ⟨hdef₂, heq₂⟩,
  rw [← heq₁] at hdef₂,
  rw [← heq₁] at heq₂,
  obtain ⟨hdef₃, heq₃⟩ := mul_smul hdef₁ hdef₂,
  simp [mul_assoc] at hdef₃,
  simp [mul_assoc, heq₂] at heq₃,
  exact ⟨hdef₃, heq₃⟩,
end

lemma is_equivalence : equivalence (envelope G α) := ⟨is_reflexive, is_symmetric, is_transitive⟩

instance : setoid (G × α) := 
{ r := envelope G α,
  iseqv := is_equivalence }

instance : has_smul G (G × α) := ⟨λ a ⟨b, x⟩, (a * b, x)⟩

lemma act_congr (a : G) (bx cy : G × α) (heq : bx ≈ cy) : a • bx ≈ a • cy := 
begin
  obtain ⟨b, x⟩ := bx,
  obtain ⟨c, y⟩ := cy,
  change smul_defined ((a * c)⁻¹ * (a * b)) x ∧ ((a * c)⁻¹ * (a * b)) • x = y,
  simp [mul_assoc],
  assumption,
end

lemma act_congr_sound (a : G) (bx cy : G × α) (heq : bx ≈ cy) : 
  ⟦a • bx⟧ = ⟦a • cy⟧ :=
quotient.sound (act_congr a bx cy heq)

def act_lifted (a : G) (bx : G × α) : space G α := ⟦a • bx⟧

instance : has_smul G (space G α) :=
⟨λ a bx, quotient.lift (act_lifted a) (act_congr_sound a) bx⟩

end envelope  

/-!
### Extra set stuff
-/

namespace set

lemma mem_pair_iff {x y z : α} : x ∈ ({y, z} : set α) ↔ x = y ∨ x = z := by simp

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


/-!
### Extra lattice stuff
-/

lemma Sup_image_le [complete_semilattice_Sup β] 
  {f g : α → β} (hle : f ≤ g) (s : set α) : Sup (f '' s) ≤ Sup (g '' s) :=
begin
  refine Sup_le_Sup_of_forall_exists_le _,
  intros y hy,
  obtain ⟨x, hx, heq⟩ := set.mem_image_iff_bex.mp hy,
  use g x, refine ⟨set.mem_image_of_mem g hx, _⟩,
  rw ← heq, exact hle x,
end

/-!
### Extra filter stuff
-/

namespace filter

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
### Extra filter pointwise stuff
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
  have heq' : a⁻¹ • y = x, by simp [← hy', ← mul_action.mul_smul],
  have hmem' : x ∈ t₁⁻¹ • s₃,
  begin
    simp [← heq'],
    have : a⁻¹ ∈ has_inv.inv '' t₁, from set.mem_image_of_mem (has_inv.inv) ha,
    have : a⁻¹ ∈ t₁⁻¹, by rwa set.image_inv at this, 
    exact set.mem_image2_of_mem this hy₁,
  end,
  exact ⟨x, hmem', hx⟩,
end

-- lemma mem_partial_smul_of_le_iff [has_partial_smul M α] {g : filter M} {f : filter α} {h : ultrafilter α}
--   (hle : ↑h ≤ partial_smul g f) {s : set α} :
--   s ∈ h ↔ ∃ t s, t ∈ g ∧ s ∈ f ∧ 
end filter