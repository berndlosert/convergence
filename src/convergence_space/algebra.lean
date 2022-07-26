import tactic
import order.filter.partial
import convergence_space.basic
import data.set.pointwise
import order.filter.pointwise
import extra

noncomputable theory
open set filter classical option function prod
open convergence_space
open_locale classical filter pointwise

variables {M G α β γ : Type*}

/-!
### Convergence semigroups, monoids, groups
-/

/-- Basic hypothesis to talk about a convergence monoid or a convergence
  semigroup. A convergence monoid over `M`, for example, is obtained by
  requiring both the instances monoid `M` and has_continuous_mul `M`. -/
class has_continuous_mul (α : Type*)
  [convergence_space α] [has_mul α] : Prop :=
(continuous_mul : continuous2 ((*) : α → α → α))

open has_continuous_mul

/-- Class `has_continuous_smul M α` says that the scalar multiplication
  `(•) : M → α → α` is continuous in both arguments. -/
class has_continuous_smul (M α : Type*)
  [has_smul M α] [convergence_space M] [convergence_space α] : Prop :=
(continuous_smul : continuous2 ((•) : M → α → α))

open has_continuous_smul

/-- A convergence group is a group in which the multiplication and inversion
  operations are continuous. -/
class convergence_group (G : Type*)
  [convergence_space G] [group G] extends has_continuous_mul G : Prop :=
(continuous_inv : continuous (has_inv.inv : G → G))

open convergence_group

/-- Class `has_continuous_partial_smul M α` says that the partial scalar multiplication
  is continuous on `smul_dom`. -/
class has_continuous_partial_smul (M α : Type*) [has_partial_smul M α]
  [convergence_space M] [convergence_space α] : Prop :=
(continuous_partial_smul : ∀ {a : M} {x : α} {g : filter M} {f : filter α},
  converges g a → converges f x → smul_defined a x → converges (partial_smul g f) (a • x))

export has_continuous_partial_smul

/-!
### Enveloping action
-/

namespace envelope

variables [group G] [partial_mul_action G α]
variables [convergence_space G] [convergence_group G]
variables [convergence_space α]

lemma embed.continuous : continuous (embed G : α → space G α) := 
continuous.comp continuous_quot_mk (continuous.prod.mk 1)

instance : has_continuous_smul G (G × α) :=
{ continuous_smul :=
  begin
    rw continuous2_continuous_iff,
    unfold continuous,
    rintro ⟨a₁, ⟨a₂, x⟩⟩ : G × (G × α),
    rintro k : filter (G × (G × α)),
    rintro hk : converges k (a₁, (a₂, x)),
    let act : G × (G × α) → G × α := uncurry has_smul.smul,
    let mul : G × G → G := uncurry has_mul.mul,
    let rlassoc := (equiv.prod_assoc G G α).symm.to_fun,
    have heq : act = prod.map mul id ∘ rlassoc, by { funext; tidy },
    let g₁ : filter G := map fst k,
    let hg₁ : converges g₁ a₁ := hk.1,
    let g₂ : filter G := map (fst ∘ snd) k,
    let hg₂ : converges g₂ a₂ := hk.2.1,
    let f : filter α := map (snd ∘ snd) k,
    let hf : converges f x := hk.2.2,
    let g : filter (G × G) := g₁ ×ᶠ g₂,
    let a : G × G := (a₁, a₂),
    have hg : converges g a := prod.converges hg₁ hg₂,
    have : converges (map mul g) (mul a), from continuous2_continuous_iff.mp continuous_mul hg,
    have hconv : converges (map mul g ×ᶠ f) (mul a, x), from prod.converges this hf,
    have hle : k ≤ g₁ ×ᶠ (g₂ ×ᶠ f), from calc
      k ≤ map fst k ×ᶠ map snd k : filter.le_prod_map_fst_snd
      ... = g₁ ×ᶠ map snd k : by tauto
      ... ≤ g₁ ×ᶠ (map fst (map snd k) ×ᶠ map snd (map snd k)) :
        prod_mono (le_refl g₁) filter.le_prod_map_fst_snd
      ... = g₁ ×ᶠ (map (fst ∘ snd) k ×ᶠ map (snd ∘ snd) k) :
        by simp [filter.map_map]
      ... = g₁ ×ᶠ (g₂ ×ᶠ f) : by tauto,
    have heq' : map act (g₁ ×ᶠ (g₂ ×ᶠ f)) = map mul g ×ᶠ f, from calc
      map act (g₁ ×ᶠ (g₂ ×ᶠ f)) = map (prod.map mul id ∘ rlassoc) (g₁ ×ᶠ (g₂ ×ᶠ f)) :
        by rw heq
      ... = map (prod.map mul id) (map rlassoc (g₁ ×ᶠ (g₂ ×ᶠ f))) :
        by simp [← filter.map_map]
      ... = map (prod.map mul id) (map (equiv.prod_assoc G G α).symm (g₁ ×ᶠ (g₂ ×ᶠ f))) :
        by tauto
      ... = map (prod.map mul id) ((g₁ ×ᶠ g₂) ×ᶠ f) :
        by simp [← prod_assoc, filter.map_map]
      ... = map mul g ×ᶠ f :
        by simp [← filter.prod_map_map_eq'],
    have hle' : map act k ≤ map mul g ×ᶠ f, from eq.subst heq' (map_mono hle),
    exact le_converges hle' hconv,
  end }

instance
[convergence_space G] [convergence_group G]
[convergence_space α] [partial_mul_action G α] [has_continuous_partial_smul G α] :
has_continuous_smul G (space G α) :=
{ continuous_smul :=
  begin
    let act : G × (G × α) → (G × α) := uncurry (•),
    let qact : G × space G α → space G α := uncurry (•),
    let idquot : G × (G × α) → G × space G α := 
      prod.map id (quot.mk (envelope G α)),
    let quot_mk : G × α → space G α := quot.mk (envelope G α),
    have heq : qact ∘ idquot = quot_mk ∘ act, by { funext, tidy },
    have hqmap : quotient_map idquot, 
      from quotient_map.prod_map quotient_map.id quotient_map_quot_mk,
    have hcontr : continuous (quot_mk ∘ act), 
      from continuous.comp continuous_quot_mk (continuous2_continuous_iff.mp has_continuous_smul.continuous_smul),
    have hcont : continuous qact, begin
      rw [quotient_map.continuous_iff hqmap, heq],
      assumption,
    end,
    exact continuous2_continuous_iff.mpr hcont,
  end }

end envelope

/-!
### Adherence restrictive
-/

/-- A continuous action of a monoid `G` on `α` is adherence restrictive if for all convergent
  filters `g` on `G` and all filters `f` on `α` with `adh f = ∅`, `adh (g • f) = ∅`. -/
def adh_restrictive (G : Type*) (α : Type*) [group G] [convergence_space G] 
  [convergence_group G] [convergence_space α] [mul_action G α] [has_continuous_smul G α] : Prop :=
∀ {g : filter G} {f : filter α} {a : G}, g.ne_bot ∧ converges g a ∧ adh f = ∅ → adh (g • f) = ∅

/-- This is a weaker version of `adh_restrictive` where instead of considering the adherence in `α`,
  it considers the adherence in the enveloping space. -/
def weakly_adh_restrictive (G : Type*) (α : Type*) [group G] [convergence_space G] [convergence_group G] 
  [convergence_space α] [partial_mul_action G α] [has_continuous_partial_smul G α] : Prop :=
∀ {g : filter G} {f : filter α} {a : G}, g.ne_bot → converges g a → ((g ×ᶠ f) ⊓ 𝓟 (smul_dom G α)).ne_bot
  → adh (map (envelope.embed G) f) = ∅ → adh (partial_smul g f) = ∅

lemma not_adh_restrictive (G : Type*) (α : Type*) [group G] [convergence_space G] 
  [convergence_group G] [convergence_space α] [mul_action G α] [has_continuous_smul G α] :
  ¬ (adh_restrictive G α) → ∃ (g : filter G) (f : filter α) (a : G) (x : α), 
    g.ne_bot ∧ converges g a ∧ adh f = ∅ ∧ x ∈ adh (g • f) :=
begin
  intro hcontra,
  unfold adh_restrictive at hcontra,
  rw not_forall at hcontra,
  obtain ⟨g, rest₁⟩ := hcontra,
  rw not_forall at rest₁,
  obtain ⟨f, rest₂⟩ := rest₁,
  rw not_forall at rest₂,
  obtain ⟨a, rest₃⟩ := rest₂,
  rw not_imp at rest₃,
  obtain ⟨⟨hnb, hconv, hadh⟩, rest₄⟩ := rest₃,
  rw set.eq_empty_iff_forall_not_mem at rest₄,
  rw not_forall at rest₄,
  obtain ⟨x, hmem⟩ := rest₄,
  rw set.not_not_mem at hmem,
  exact ⟨g, f, a, x, hnb, hconv, hadh, hmem⟩,
end

lemma adh_restrictive_result {G α : Type*} [group G] [convergence_space G] [convergence_group G] 
  [convergence_space α] [mul_action G α] [has_continuous_smul G α] : 
  adh_restrictive G α :=
classical.by_contradiction 
begin
  assume hcontra : ¬ adh_restrictive G α,
  obtain ⟨g, f, a, x, hnb, hconv, hadh, hmem⟩ := not_adh_restrictive G α hcontra,
  haveI : g.ne_bot := hnb,
  change x ∈ adh (g • f) at hmem,
  change adheres (g • f) x at hmem,
  unfold adheres at hmem,
  obtain ⟨h', hnb', hle', hconv'⟩ := hmem,
  haveI : h'.ne_bot := hnb',
  let k' := ultrafilter.of h',
  have hle'' : ↑k' ≤ g • f, from (le_trans (ultrafilter.of_le h') hle'),
  set k : filter α := g⁻¹ • ↑k' with hdef,
  haveI : k.ne_bot := filter.ne_bot.smul (filter.ne_bot_inv_iff.mpr hnb) k'.ne_bot,
  have hconv : converges k (a⁻¹ • x),
  begin
    have hconv_inv_g : converges g⁻¹ a⁻¹, from continuous_inv hconv,
    have hconv_k' : converges ↑k' x, 
      from le_converges (ultrafilter.of_le h') hconv',
    exact continuous_smul hconv_inv_g hconv_k',
  end,
  have hmem : a⁻¹ • x ∈ adh f, 
  begin
    have hconv' : converges (k ⊓ f) (a⁻¹ • x), 
      from le_converges inf_le_left hconv,
    haveI hnbI : (k ⊓ f).ne_bot := filter.inv_smul_inf_ne_bot hle'',
    have hadh'' : adheres f (a⁻¹ • x) := ⟨k ⊓ f, hnbI, inf_le_right, hconv'⟩,
    assumption,
  end,
  rw set.eq_empty_iff_forall_not_mem at hadh,
  unfold adh at hadh,
  exact absurd hmem (hadh (a⁻¹ • x)),
end

lemma weakly_adh_restrictive_result {G α : Type*} [group G] [convergence_space G] [convergence_group G] 
  [convergence_space α] [partial_mul_action G α] 
  [has_continuous_partial_smul G α] : weakly_adh_restrictive G α :=
begin
  intros g f a hgnb hgconv hnb,
  haveI : g.ne_bot := hgnb,
  rw ← not_imp_not,
  intro hadh,
  obtain ⟨x, hx⟩ := ne_empty_iff_exists_elem.mp hadh,
  change adheres (partial_smul g f) x at hx,
  rw adheres.exists_ultrafilter (partial_smul g f) x at hx,
  obtain ⟨h, hle, hconv⟩ := hx,
  have hconv' : converges (g⁻¹ • map (envelope.embed G) ↑h) (a⁻¹ • envelope.embed G x) :=
    continuous_smul (continuous_inv hgconv) (envelope.embed.continuous hconv),
  have hmem : a⁻¹ • envelope.embed G x ∈ adh (map (envelope.embed G) f) :=
  begin
    change adheres (map (envelope.embed G) f) (a⁻¹ • envelope.embed G x),
    change ∃ (f' : filter (envelope.space G α)) [f'.ne_bot], f' ≤ map (envelope.embed G) f ∧ converges f' (a⁻¹ • envelope.embed G x),
    let f' := g⁻¹ • filter.map (envelope.embed G) ↑h ⊓ map (envelope.embed G) f, use f', split,
    { rw inf_ne_bot_iff,
      intros s hs s' hs',
      rw filter.mem_inv_smul_iff at hs,
      obtain ⟨t, s₁, ht, hs₁, hsub⟩ := hs,
      rw filter.mem_map_iff_exists_image at *,
    }
    -- { rw ← filter.forall_mem_nonempty_iff_ne_bot,
    --   intros s hs,
    --   rw filter.mem_inf_iff at hs,
    --   obtain ⟨t₁, ht₁, t₂, ht₂, heq⟩ := hs,
    --   obtain ⟨s₁, s₂, hs₁, hs₂, hsub⟩ := filter.mem_smul.mp ht₁,
    --   obtain ⟨u₁, hu₁, hsub'⟩ := (filter.mem_inv_iff s₁).mp hs₁,
    --   obtain ⟨u₂, hu₂, hsub''⟩ := filter.mem_map_iff_exists_image.mp hs₂,
    --   sorry },
    split,
    { exact inf_le_right },
    { exact le_converges inf_le_left hconv' },
  end,
  rw ne_empty_iff_exists_elem,
  exact ⟨a⁻¹ • envelope.embed G x, hmem⟩
end