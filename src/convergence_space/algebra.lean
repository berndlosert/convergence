import tactic
import order.filter.partial
import convergence_space.basic
import data.set.pointwise
import order.filter.pointwise
import algebra.group.extra
import group_theory.group_action.extra
import order.filter.extra

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
  converges g a → converges f x → smul_defined a x → converges (g •ᶠ f) (a • x))

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

/-- This is the "partial" version of `adh_restrictive`. -/
def partial_adh_restrictive (G : Type*) (α : Type*) [group G] [convergence_space G] [convergence_group G] 
  [convergence_space α] [partial_mul_action G α] [has_continuous_partial_smul G α] : Prop :=
∀ {g : filter G} {f : filter α} {a : G}, g.ne_bot ∧ converges g a ∧ adh f = ∅ ∧ (g •ᶠ f).ne_bot
  → adh (g •ᶠ f) = ∅

/-- This is a weaker version of `partial_adh_restrictive` where instead of considering the adherence in `α`,
  it considers the adherence in the enveloping space. -/
def weakly_adh_restrictive (G : Type*) (α : Type*) [group G] [convergence_space G] [convergence_group G] 
  [convergence_space α] [partial_mul_action G α] [has_continuous_partial_smul G α] : Prop :=
∀ {g : filter G} {f : filter α} {a : G}, g.ne_bot ∧ converges g a ∧ 
  adh (map (envelope.embed G) f) = ∅ ∧ (g •ᶠ f).ne_bot → adh (g •ᶠ f) = ∅

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

lemma not_partial_adh_restrictive (G : Type*) (α : Type*) [group G] [convergence_space G] 
  [convergence_group G] [convergence_space α] [partial_mul_action G α] [has_continuous_partial_smul G α] :
  ¬ (partial_adh_restrictive G α) → ∃ (g : filter G) (f : filter α) (a : G) (x : α), 
    g.ne_bot ∧ converges g a ∧ adh f = ∅ ∧ (g •ᶠ f).ne_bot ∧ x ∈ adh (g •ᶠ f) :=
begin
  intro hcontra,
  unfold partial_adh_restrictive at hcontra,
  rw not_forall at hcontra,
  obtain ⟨g, rest₁⟩ := hcontra,
  rw not_forall at rest₁,
  obtain ⟨f, rest₂⟩ := rest₁,
  rw not_forall at rest₂,
  obtain ⟨a, rest₃⟩ := rest₂,
  rw not_imp at rest₃,
  obtain ⟨⟨hnb, hconv, hadh, hnb'⟩, rest₄⟩ := rest₃,
  rw set.eq_empty_iff_forall_not_mem at rest₄,
  rw not_forall at rest₄,
  obtain ⟨x, hmem⟩ := rest₄,
  rw set.not_not_mem at hmem,
  exact ⟨g, f, a, x, hnb, hconv, hadh, hnb', hmem⟩,
end

lemma not_weakly_adh_restrictive (G : Type*) (α : Type*) [group G] [convergence_space G] 
  [convergence_group G] [convergence_space α] [partial_mul_action G α] [has_continuous_partial_smul G α] :
  ¬ (weakly_adh_restrictive G α) → ∃ (g : filter G) (f : filter α) (a : G) (x : α), 
    g.ne_bot ∧ converges g a ∧ adh (map (envelope.embed G) f) = ∅ ∧ (g •ᶠ f).ne_bot ∧ x ∈ adh (g •ᶠ f) :=
begin
  intro hcontra,
  unfold weakly_adh_restrictive at hcontra,
  rw not_forall at hcontra,
  obtain ⟨g, rest₁⟩ := hcontra,
  rw not_forall at rest₁,
  obtain ⟨f, rest₂⟩ := rest₁,
  rw not_forall at rest₂,
  obtain ⟨a, rest₃⟩ := rest₂,
  rw not_imp at rest₃,
  obtain ⟨⟨hnb, hconv, hadh, hnb'⟩, rest₄⟩ := rest₃,
  rw set.eq_empty_iff_forall_not_mem at rest₄,
  rw not_forall at rest₄,
  obtain ⟨x, hmem⟩ := rest₄,
  rw set.not_not_mem at hmem,
  exact ⟨g, f, a, x, hnb, hconv, hadh, hnb', hmem⟩,
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
    haveI hnbI : (k ⊓ f).ne_bot := filter.inv_smul_of_smul hle'',
    have hadh'' : adheres f (a⁻¹ • x) := ⟨k ⊓ f, hnbI, inf_le_right, hconv'⟩,
    assumption,
  end,
  rw set.eq_empty_iff_forall_not_mem at hadh,
  unfold adh at hadh,
  exact absurd hmem (hadh (a⁻¹ • x)),
end

lemma partial_adh_restrictive_result {G α : Type*} [group G] [convergence_space G] [convergence_group G] 
  [convergence_space α] [partial_mul_action G α] [has_continuous_partial_smul G α] 
  (hcl : is_closed (smul_dom G α)) : partial_adh_restrictive G α :=
classical.by_contradiction 
begin
  assume hcontra : ¬ partial_adh_restrictive G α,
  obtain ⟨g, f, a, x, hnb, hconv, hadh, hnb', hmem⟩ := not_partial_adh_restrictive G α hcontra,
  haveI : g.ne_bot := hnb,
  change x ∈ adh (g •ᶠ f) at hmem,
  change adheres (g •ᶠ f) x at hmem,
  unfold adheres at hmem,
  obtain ⟨h', hnb', hle', hconv'⟩ := hmem,
  haveI : h'.ne_bot := hnb',
  let h := ultrafilter.of h',
  have hle'' : ↑h ≤ g •ᶠ f, from (le_trans (ultrafilter.of_le h') hle'),
  haveI hnb'' : ((g⁻¹ •ᶠ ↑h) ⊓ f).ne_bot, from
  begin
    rw [ne_bot_iff, inf_neq_bot_iff],
    unfold filter.partial_smul,
    intros l hl s hs,
    rw mem_map_iff_exists_image at hl,
    let d := smul_dom G α,
    obtain ⟨w, hw, hsubw⟩ := hl,
    change w ∈ (g⁻¹ ×ᶠ ↑h) ⊓ 𝓟 d at hw,
    obtain ⟨u, hu, v, hv, hsub⟩ := (filter.prod_inf_principal_mem_iff w).mp hw,
    obtain ⟨t, ht, hsub'⟩ := (filter.mem_inv_iff u).mp hu,
    have ht' : t⁻¹ ∈ g⁻¹ := filter.inv_mem_inv ht,
    let w' := (t ×ˢ s) ∩ d,
    have hw' : w' ∈ (g ×ᶠ f) ⊓ 𝓟 d := 
      (filter.prod_inf_principal_mem_iff w').mpr ⟨t, ht, s, hs, subset_refl w'⟩,
    let smul := uncurry (•),
    let v' := smul '' w',
    have : v' ∈ g •ᶠ f := filter.image_mem_map hw',
    have hv' : v' ∈ ↑h := filter.le_def.mp hle'' v' this,
    let v₀ := v ∩ v',
    have hne : v₀.nonempty := ultrafilter.nonempty_of_mem (h.inter_sets hv hv'),
    let y : α := hne.some,
    let hy : y ∈ v₀ := hne.some_mem,
    have hex : ∃ (b ∈ t) (z ∈ s), smul_defined b z ∧ b • z = y, from
    begin
      have : y ∈ v' :=  set.mem_of_mem_inter_right hy,
      obtain ⟨⟨b, z⟩, hmem, heq⟩ := (set.mem_image smul w' y).mp this,
      obtain ⟨hmem', hd⟩ := (set.mem_inter_iff (b, z) (t ×ˢ s) d).mp hmem,
      obtain ⟨hb, hz⟩ := hmem', 
      exact ⟨b, hb, z, hz, hd, heq⟩,
    end,
    obtain ⟨b, hb, z, hz, hdef, heq⟩ := hex,
    obtain ⟨hdef', heq'⟩ := inv_smul_cancel_left hdef heq,
    have : (b⁻¹, y) ∈ (t⁻¹ ×ˢ v₀) ∩ d := 
      set.mem_inter (set.mk_mem_prod (set.inv_mem_inv.mpr hb) hy) hdef',
    have : (b⁻¹, y) ∈ (u ×ˢ v) ∩ d :=
      set.mem_of_mem_of_subset this 
        (set.inter_subset_inter_left d 
          (set.prod_subset_prod_iff.mpr 
            (or.inl ⟨hsub', set.inter_subset_left v v'⟩))),
    have : (b⁻¹, y) ∈ w := set.mem_of_mem_of_subset this hsub,
    have : uncurry has_smul.smul (b⁻¹, y) ∈ l := (set.maps_to'.mpr hsubw) this,
    change b⁻¹ • y ∈ l at this,
    have : z ∈ l, by { rw heq', assumption },
    have : z ∈ l ∩ s := ⟨this, hz⟩,
    exact set.nonempty.ne_empty (set.nonempty_def.mpr ⟨z, this⟩),
  end,
  have hdef : smul_defined a⁻¹ x, from
  begin
    change (a⁻¹, x) ∈ smul_dom G α,
    change smul_dom G α = closure (smul_dom G α) at hcl,
    rw set.ext_iff.mp hcl,
    unfold closure,
    let k : filter (G × α) := (g⁻¹ ×ᶠ ↑h) ⊓ 𝓟 (smul_dom G α),
    have : (g⁻¹ •ᶠ ↑h) ⊓ f ≤ g⁻¹ •ᶠ ↑h := inf_le_left,
    have : (g⁻¹ •ᶠ ↑h).ne_bot := filter.ne_bot.mono hnb'' this,
    have hk₀ : k.ne_bot := (filter.map_ne_bot_iff (uncurry (•) : G × α → α)).mp this,
    have : converges ↑h x := le_converges (ultrafilter.of_le h') hconv',
    have : converges (g⁻¹ ×ᶠ ↑h) (a⁻¹, x) := prod.converges (continuous_inv hconv) this,
    have hk₁ : converges k (a⁻¹, x) := le_converges inf_le_left this,
    have hk₂ : smul_dom G α ∈ k := filter.le_principal_iff.mp inf_le_right,
    refine ⟨k, hk₀, hk₁, hk₂⟩,
  end,
  have : converges g⁻¹ a⁻¹, from continuous_inv hconv, 
  have : converges (g⁻¹ •ᶠ ↑h) (a⁻¹ • x), 
    from continuous_partial_smul this (le_converges (ultrafilter.of_le h') hconv') hdef,
  have : converges ((g⁻¹ •ᶠ ↑h) ⊓ f) (a⁻¹ • x), from le_converges inf_le_left this,
  have : (a⁻¹ • x) ∈ adh f := ⟨(g⁻¹ •ᶠ ↑h) ⊓ f, hnb'', inf_le_right, this⟩,
  rw set.eq_empty_iff_forall_not_mem at hadh,
  unfold adh at hadh,
  exact absurd this (hadh (a⁻¹ • x)),
end

lemma weakly_adh_restrictive_result {G α : Type*} [group G] [convergence_space G] [convergence_group G] 
  [convergence_space α] [partial_mul_action G α] 
  [has_continuous_partial_smul G α] : weakly_adh_restrictive G α :=
classical.by_contradiction
begin
  assume hcontra : ¬ weakly_adh_restrictive G α,
  obtain ⟨g, f, a, x, hnb, hconv, hadh, hnb', hmem⟩ := not_weakly_adh_restrictive G α hcontra,
    haveI : g.ne_bot := hnb,
  change x ∈ adh (g •ᶠ f) at hmem,
  change adheres (g •ᶠ f) x at hmem,
  unfold adheres at hmem,
  obtain ⟨h', hnb', hle', hconv'⟩ := hmem,
  haveI : h'.ne_bot := hnb',
  let h := ultrafilter.of h',
  have hle'' : ↑h ≤ g •ᶠ f, from (le_trans (ultrafilter.of_le h') hle'),
  haveI hnb'' : ((g⁻¹ •ᶠ ↑h) ⊓ f).ne_bot, from
  begin
    rw [ne_bot_iff, inf_neq_bot_iff],
    unfold filter.partial_smul,
    intros l hl s hs,
    rw mem_map_iff_exists_image at hl,
    let d := smul_dom G α,
    obtain ⟨w, hw, hsubw⟩ := hl,
    change w ∈ (g⁻¹ ×ᶠ ↑h) ⊓ 𝓟 d at hw,
    obtain ⟨u, hu, v, hv, hsub⟩ := (filter.prod_inf_principal_mem_iff w).mp hw,
    obtain ⟨t, ht, hsub'⟩ := (filter.mem_inv_iff u).mp hu,
    have ht' : t⁻¹ ∈ g⁻¹ := filter.inv_mem_inv ht,
    let w' := (t ×ˢ s) ∩ d,
    have hw' : w' ∈ (g ×ᶠ f) ⊓ 𝓟 d := 
      (filter.prod_inf_principal_mem_iff w').mpr ⟨t, ht, s, hs, subset_refl w'⟩,
    let smul := uncurry (•),
    let v' := smul '' w',
    have : v' ∈ g •ᶠ f := filter.image_mem_map hw',
    have hv' : v' ∈ ↑h := filter.le_def.mp hle'' v' this,
    let v₀ := v ∩ v',
    have hne : v₀.nonempty := ultrafilter.nonempty_of_mem (h.inter_sets hv hv'),
    let y : α := hne.some,
    let hy : y ∈ v₀ := hne.some_mem,
    have hex : ∃ (b ∈ t) (z ∈ s), smul_defined b z ∧ b • z = y, from
    begin
      have : y ∈ v' :=  set.mem_of_mem_inter_right hy,
      obtain ⟨⟨b, z⟩, hmem, heq⟩ := (set.mem_image smul w' y).mp this,
      obtain ⟨hmem', hd⟩ := (set.mem_inter_iff (b, z) (t ×ˢ s) d).mp hmem,
      obtain ⟨hb, hz⟩ := hmem', 
      exact ⟨b, hb, z, hz, hd, heq⟩,
    end,
    obtain ⟨b, hb, z, hz, hdef, heq⟩ := hex,
    obtain ⟨hdef', heq'⟩ := inv_smul_cancel_left hdef heq,
    have : (b⁻¹, y) ∈ (t⁻¹ ×ˢ v₀) ∩ d := 
      set.mem_inter (set.mk_mem_prod (set.inv_mem_inv.mpr hb) hy) hdef',
    have : (b⁻¹, y) ∈ (u ×ˢ v) ∩ d :=
      set.mem_of_mem_of_subset this 
        (set.inter_subset_inter_left d 
          (set.prod_subset_prod_iff.mpr 
            (or.inl ⟨hsub', set.inter_subset_left v v'⟩))),
    have : (b⁻¹, y) ∈ w := set.mem_of_mem_of_subset this hsub,
    have : uncurry has_smul.smul (b⁻¹, y) ∈ l := (set.maps_to'.mpr hsubw) this,
    change b⁻¹ • y ∈ l at this,
    have : z ∈ l, by { rw heq', assumption },
    have : z ∈ l ∩ s := ⟨this, hz⟩,
    exact set.nonempty.ne_empty (set.nonempty_def.mpr ⟨z, this⟩),
  end,
  have hdef : smul_defined a⁻¹ x, from
  begin
    change (a⁻¹, x) ∈ smul_dom G α,
    change smul_dom G α = closure (smul_dom G α) at hcl,
    rw set.ext_iff.mp hcl,
    unfold closure,
    let k : filter (G × α) := (g⁻¹ ×ᶠ ↑h) ⊓ 𝓟 (smul_dom G α),
    have : (g⁻¹ •ᶠ ↑h) ⊓ f ≤ g⁻¹ •ᶠ ↑h := inf_le_left,
    have : (g⁻¹ •ᶠ ↑h).ne_bot := filter.ne_bot.mono hnb'' this,
    have hk₀ : k.ne_bot := (filter.map_ne_bot_iff (uncurry (•) : G × α → α)).mp this,
    have : converges ↑h x := le_converges (ultrafilter.of_le h') hconv',
    have : converges (g⁻¹ ×ᶠ ↑h) (a⁻¹, x) := prod.converges (continuous_inv hconv) this,
    have hk₁ : converges k (a⁻¹, x) := le_converges inf_le_left this,
    have hk₂ : smul_dom G α ∈ k := filter.le_principal_iff.mp inf_le_right,
    refine ⟨k, hk₀, hk₁, hk₂⟩,
  end,
  have : converges g⁻¹ a⁻¹, from continuous_inv hconv, 
  have : converges (g⁻¹ •ᶠ ↑h) (a⁻¹ • x), 
    from continuous_partial_smul this (le_converges (ultrafilter.of_le h') hconv') hdef,
  have : converges ((g⁻¹ •ᶠ ↑h) ⊓ f) (a⁻¹ • x), from le_converges inf_le_left this,
  have : (a⁻¹ • x) ∈ adh f := ⟨(g⁻¹ •ᶠ ↑h) ⊓ f, hnb'', inf_le_right, this⟩,
  rw set.eq_empty_iff_forall_not_mem at hadh,
  unfold adh at hadh,
  exact absurd this (hadh (a⁻¹ • x)),
  sorry,
end