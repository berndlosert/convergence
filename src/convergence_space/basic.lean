import tactic
import order.filter.partial
import order.filter.ultrafilter
import order.filter.bases
import algebra.support
import category_theory.concrete_category.bundled

noncomputable theory
open set function filter classical option category_theory
open_locale classical filter

variables {α β γ : Type*}

-------------------------------------------------------------------------------
-- Definition
-------------------------------------------------------------------------------

/-- Instances of this class will be refered to as convergence structures. -/
@[ext] class convergence_space (α : Type*) :=
(converges : filter α → α → Prop)
(pure_converges : ∀ x, converges (pure x) x)
(le_converges : ∀ {f g}, f ≤ g → ∀ {x}, converges g x → converges f x)

open convergence_space

section
variables (p : convergence_space α)
def converges_ (f : filter α) (x : α) : Prop := @converges _ p f x
def pure_converges_ (x : α) : converges (pure x) x := @pure_converges _ p x
def le_converges_ ⦃f g : filter α⦄ (hle : f ≤ g) {x : α}
  (hconv : converges g x) : converges f x :=
@le_converges _ p _ _ hle _ hconv
end

theorem convergence_space_eq_iff {p q : convergence_space α} :
  p = q ↔ ∀ f x, @converges _ p f x ↔ @converges _ q f x :=
by simp [funext_iff, convergence_space.ext_iff p q]

-------------------------------------------------------------------------------
-- Parital ordering
-------------------------------------------------------------------------------

instance : has_le (convergence_space α) :=
⟨λ p q, ∀ {f x}, @converges _ p f x → @converges _ q f x⟩

instance : partial_order (convergence_space α) := {
  le_refl :=
  begin
    unfold has_le.le,
    intros,
    assumption,
  end,
  le_trans :=
  begin
    assume p q r : convergence_space α,
    assume hpq : p ≤ q,
    assume hqr : q ≤ r,
    assume f : filter α,
    assume x : α,
    assume hconv : converges_ p f x,
    exact (hqr (hpq hconv))
  end,
  le_antisymm :=
  begin
    assume p q : convergence_space α,
    assume hpq : p ≤ q,
    assume hqp : q ≤ p,
    ext f x,
    exact iff.intro hpq hqp,
  end,
  ..convergence_space.has_le
}

-------------------------------------------------------------------------------
-- Discrete/indiscrete convergence spaces
-------------------------------------------------------------------------------

/-- The indiscrete convergence structure is the one where everb filter
  converges to everb point. -/
def indiscrete : convergence_space α := ⟨λ f x, true, by tauto, by tauto⟩

instance : has_top (convergence_space α) := ⟨indiscrete⟩

/-- The discrete convergence structure is the one where the onlb proper filters
  that converge are the `pure` ones. -/
def discrete : convergence_space α := ⟨λ f x, f ≤ pure x, by tauto, by tauto⟩

instance : has_bot (convergence_space α) := ⟨discrete⟩

-------------------------------------------------------------------------------
-- Infimum and supremum of convergence spaces
-------------------------------------------------------------------------------

instance : has_inf (convergence_space α) :=
{ inf := λ p q,
  { converges := fun f x, (converges_ p f x) ∧ (converges_ q f x),
    pure_converges :=
    begin
      assume x : α,
      exact and.intro (pure_converges_ p x) (pure_converges_ q x),
    end,
    le_converges :=
    begin
      assume f g : filter α,
      assume hle : f ≤ g,
      assume x : α,
      assume hconv : (converges_ p g x) ∧ (converges_ q g x),
      exact and.intro (le_converges_ p hle hconv.left) (le_converges_ q hle hconv.right)
    end }}

instance : has_Inf (convergence_space α) :=
{ Inf := λ ps,
  { converges := λ f x, ∀ {p : convergence_space α}, p ∈ ps → converges_ p f x,
    pure_converges :=
    begin
      assume x : α,
      assume p : convergence_space α,
      assume : p ∈ ps,
      exact pure_converges_ p x,
    end,
    le_converges :=
    begin
      assume f g : filter α,
      assume hle : f ≤ g,
      assume x : α,
      assume hconv : ∀ {p : convergence_space α}, p ∈ ps → converges_ p g x,
      assume p : convergence_space α,
      assume hmem : p ∈ ps,
      exact le_converges_ p hle (hconv hmem)
    end }}

instance : has_sup (convergence_space α) :=
{ sup := λ p q,
  { converges := λ f x, (converges_ p f x) ∨ (converges_ q f x),
    pure_converges :=
    begin
      assume x : α,
      exact or.inl (pure_converges_ p x),
    end,
    le_converges :=
    begin
      assume f g : filter α,
      assume hle : f ≤ g,
      assume x : α,
      assume hconv : (converges_ p g x) ∨ (converges_ q g x),
      exact or.elim hconv
        (assume hl, or.inl (le_converges_ p hle hl))
        (assume hr, or.inr (le_converges_ q hle hr))
    end }}

instance : has_Sup (convergence_space α) :=
{ Sup := λ ps,
  { converges := λ f x, (f ≤ pure x) ∨
      (∃ p : convergence_space α, p ∈ ps ∧ converges_ p f x),
    pure_converges := by tauto,
    le_converges :=
    begin
      assume f g : filter α,
      assume hle : f ≤ g,
      assume x : α,
      assume hor : (g ≤ pure x) ∨
        (∃ p : convergence_space α, p ∈ ps ∧ converges_ p g x),
      cases hor,
        case or.inl : hle' begin
          exact or.inl (le_trans hle hle')
        end,
        case or.inr : hconv begin
          exact exists.elim hconv begin
            assume p : convergence_space α,
            assume hconv' : p ∈ ps ∧ converges_ p g x,
            exact or.inr
              (exists.intro p
                (and.intro hconv'.left (le_converges_ p hle hconv'.right)))
          end,
        end,
    end }}

-------------------------------------------------------------------------------
-- Lattice of convergence spaces
-------------------------------------------------------------------------------

instance : semilattice_sup (convergence_space α) :=
{ le_sup_left :=
  begin
    assume p q : convergence_space α,
    assume f : filter α,
    assume x : α,
    assume : converges_ p f x,
    exact or.inl this,
  end,
  le_sup_right :=
  begin
    assume p q : convergence_space α,
    assume f : filter α,
    assume x : α,
    assume : converges_ q f x,
    exact or.inr this,
  end,
  sup_le :=
  begin
    assume p q r : convergence_space α,
    assume hle : p ≤ r,
    assume hle' : q ≤ r,
    assume f : filter α,
    assume x : α,
    assume : converges_ (p ⊔ q) f x,
    cases this,
      exact hle this,
      exact hle' this,
  end,
  ..convergence_space.partial_order,
  ..convergence_space.has_sup }

instance : complete_semilattice_Sup (convergence_space α) :=
{ le_Sup :=
  begin
    assume ps : set (convergence_space α),
    assume p : convergence_space α,
    assume hmem : p ∈ ps,
    assume f : filter α,
    assume x : α,
    assume : converges_ p f x,
    exact or.inr (exists.intro p (and.intro hmem this)),
  end,
  Sup_le :=
  begin
    assume qs : set (convergence_space α),
    assume p : convergence_space α,
    assume hle : ∀ q ∈ qs, q ≤ p,
    assume f : filter α,
    assume x : α,
    assume : converges_ (Sup qs) f x,
    cases this,
      case or.inl : hle' begin
        exact le_converges_ p hle' (pure_converges_ p x)
      end,
      case or.inr : hconv begin
        exact exists.elim hconv begin
          assume q : convergence_space α,
          assume hconv' : q ∈ qs ∧ converges_ q f x,
          exact (hle q hconv'.left) hconv'.right
        end,
      end,
  end,
  ..convergence_space.partial_order,
  ..convergence_space.has_Sup }

instance : semilattice_inf (convergence_space α) :=
{ inf_le_left :=
  begin
    assume p q : convergence_space α,
    assume f : filter α,
    assume x : α,
    assume : converges_ (p ⊓ q) f x,
    exact this.left,
  end,
  inf_le_right :=
  begin
    assume p q : convergence_space α,
    assume f : filter α,
    assume x : α,
    assume : converges_ (p ⊓ q) f x,
    exact this.right,
  end,
  le_inf :=
  begin
    assume p q r : convergence_space α,
    assume hle : p ≤ q,
    assume hle' : p ≤ r,
    assume f : filter α,
    assume x : α,
    assume hp : converges_ p f x,
    have hq : converges_ q f x, from hle hp,
    have hr : converges_ r f x, from hle' hp,
    exact and.intro hq hr,
  end,
  ..convergence_space.partial_order,
  ..convergence_space.has_inf }

instance : complete_semilattice_Inf (convergence_space α) :=
{ Inf_le :=
  begin
    assume ps : set (convergence_space α),
    assume p : convergence_space α,
    assume hmem : p ∈ ps,
    assume f : filter α,
    assume x : α,
    assume : converges_ (Inf ps) f x,
    exact this hmem,
  end,
  le_Inf :=
  begin
    assume ps : set (convergence_space α),
    assume q : convergence_space α,
    assume hle : ∀ p : convergence_space α, p ∈ ps → q ≤ p,
    assume f : filter α,
    assume x : α,
    assume hconv : converges_ q f x,
    assume p : convergence_space α,
    assume hmem : p ∈ ps,
    exact (hle p hmem) hconv,
  end,
  ..convergence_space.partial_order,
  ..convergence_space.has_Inf }

instance : lattice (convergence_space α) :=
{ ..convergence_space.semilattice_sup,
  ..convergence_space.semilattice_inf }

instance : complete_lattice (convergence_space α) :=
{ bot_le :=
  begin
    assume p : convergence_space α,
    assume f : filter α,
    assume x : α,
    assume : converges_ discrete f x,
    exact le_converges_ p this (pure_converges_ p x),
  end,
  le_top := by intros; tauto,
  ..convergence_space.lattice,
  ..convergence_space.complete_semilattice_Sup,
  ..convergence_space.complete_semilattice_Inf,
  ..convergence_space.has_top,
  ..convergence_space.has_bot }

-------------------------------------------------------------------------------
-- Continuity
-------------------------------------------------------------------------------

def continuous [convergence_space α] [convergence_space β] (m : α → β) : Prop :=
∀ ⦃x f⦄, converges f x → converges (map m f) (m x)

lemma continuous.comp [convergence_space α] [convergence_space β]
  [convergence_space γ] {g : β → γ} {f : α → β} (hg : continuous g)
  (hf : continuous f) : continuous (g ∘ f) :=
begin
  assume x : α,
  assume l : filter α,
  assume : converges l x,
  have : converges (map f l) (f x), from hf this,
  have : converges (map g (map f l)) (g (f x)), from hg this,
  convert this,
end

lemma continuous_id [convergence_space α] : continuous (id : α → α) :=
begin
  assume x : α,
  assume f : filter α,
  assume : converges f x,
  simp [filter.map_id],
  exact this,
end

structure homeomorph (α β : Type*) [convergence_space α] [convergence_space β]
  extends α ≃ β :=
(continuous_to_fun : continuous to_fun)
(continuous_inv_fun : continuous inv_fun)

-------------------------------------------------------------------------------
-- Induced/coinduced convergence space
-------------------------------------------------------------------------------

/-- Given `m : α → β`, where `β` is convergence space, the induced convergence
  structure on `α` is the grextest convergence structure making `m`
  continuous. -/
def convergence_space.induced (m : α → β) [convergence_space β] :
  convergence_space α :=
{ converges := λ f x, converges (map m f) (m x),
  pure_converges := by simp [filter.map_pure, pure_converges],
  le_converges :=
  begin
    assume f g : filter α,
    assume hle : f ≤ g,
    assume x : α,
    assume hconv : converges (map m g) (m x),
    have hle' : map m f ≤ map m g, apply map_mono hle,
    apply le_converges hle' hconv
  end }

lemma continuous.induced_le (m : α → β) [p : convergence_space α]
  [convergence_space β] (hm : continuous m) :
  p ≤ convergence_space.induced m :=
begin
  unfold has_le.le,
  assume f : filter α,
  assume x : α,
  assume : converges_ p f x,
  exact hm this,
end

inductive coinduced_converges (f : α → β) [convergence_space α] (lb : filter β) (y : β) : Prop
| pure_case (_ : lb ≤ pure y) : coinduced_converges
| other_case (la : filter α) (x : α) (_ : lb ≤ map f la) (_ : y = f x) (_ : converges la x) : coinduced_converges

/-- Given `f : α → β`, where `α` is convergence space, the coinduced convergence
 -- structure on `β` is the least convergence structure making `f`
 -- continuous. -/
def convergence_space.coinduced (f : α → β) [convergence_space α] : convergence_space β := {
  converges := coinduced_converges f,
  pure_converges := λ b, coinduced_converges.pure_case (le_refl (pure b)),
  le_converges := begin
    assume lb₁ lb₂ : filter β,
    assume : lb₁ ≤ lb₂,
    assume y : β,
    assume h : coinduced_converges f lb₂ y,
    cases h,
      case pure_case begin
        have : lb₁ ≤ pure y, from calc
          lb₁ ≤ lb₂ : (by assumption : lb₁ ≤ lb₂)
          ... ≤ pure y : (by assumption : lb₂ ≤ pure y),
        exact coinduced_converges.pure_case (by assumption : lb₁ ≤ pure y),
      end,
      case other_case : la x _ _ _ begin
        have : lb₁ ≤ map f la, from calc
          lb₁ ≤ lb₂ : (by assumption : lb₁ ≤ lb₂)
          ... ≤ map f la : (by assumption : lb₂ ≤ map f la),
        exact coinduced_converges.other_case la x
          (by assumption : lb₁ ≤ map f la)
          (by assumption : y = f x)
          (by assumption : converges la x)
        end
  end,
}

lemma continuous.le_coinduced (f : α → β) [convergence_space α] [q : convergence_space β] (hf : continuous f)
: convergence_space.coinduced f ≤ q
:= begin
  unfold has_le.le,
  assume lb : filter β,
  assume y : β,
  assume h : converges_ (convergence_space.coinduced f) lb y,
  cases h,
    case pure_case begin
      exact le_converges_ q h (pure_converges_ q y),
    end,
    case other_case : la x h₀ h₁ h₂ begin
      have : converges_ q (map f la) (f x), from hf h₂,
      rw h₁,
      exact le_converges_ q h₀ this,
    end
end

-------------------------------------------------------------------------------
-- Limits, adherence, interior, closure, open, closed, neighborhoods
-------------------------------------------------------------------------------

section
variables [convergence_space α]
def lim (l : filter α) : set α := { x | converges l x }
def adheres (l : filter α) (x : α) : Prop := ∃ l' ≤ l, converges l' x
def adh (l : filter α) : set α := { x | adheres l x }
def interior (s : set α) : set α := { x ∈ s | ∀ l, converges l x → s ∈ l }
def is_open (s : set α) : Prop := s = interior s
def cl (s : set α) : set α := { x | ∃ (l : filter α) [ne_bot l], converges l x ∧ s ∈ l }
def is_closed (s : set α) : Prop := s = cl s
def is_dense (s : set α) : Prop := ∀ x, x ∈ cl s
def is_strictly_dense (s : set α) : Prop :=
∀ {x : α} {l : filter α}, converges l x → ∃ l', (s ∈ l') ∧ (converges l' x) ∧ (l ≤ filter.generate (cl '' l.sets))
def nhds (x : α) : filter α := ⨅ l ∈ {l' : filter α | converges l' x}, l
end

-------------------------------------------------------------------------------
-- Convergence spaces constructions
-------------------------------------------------------------------------------

instance {p : α → Prop} [convergence_space α] : convergence_space (subtype p) :=
convergence_space.induced (coe : subtype p → α)

instance {r : α → α → Prop} [convergence_space α] : convergence_space (quot r) :=
convergence_space.coinduced (quot.mk r)

instance [convergence_space α] [convergence_space β] : convergence_space (α × β) :=
convergence_space.induced prod.fst ⊓ convergence_space.induced prod.snd

/-
lemma prod_fst_continuous [convergence_space α] [convergence_space β]
: continuous (prod.fst : α × β → α)
:= begin
  unfold continuous,
  assume p : α × β,
  assume l : filter (α × β),
  assume h : converges l p,
  have : converges_ (convergence_space.induced prod.fst) l p.fst, from
  --have : converges_ (convergence_space.induced prod.fst)
end
-/

instance [convergence_space α] : convergence_space (option α) :=
convergence_space.coinduced some

-------------------------------------------------------------------------------
-- The convergence space C(α,β)
-------------------------------------------------------------------------------

structure continuous_map (α β : Type*) [convergence_space α] [convergence_space β] :=
(to_fun : α → β)
(continuous_to_fun : continuous to_fun)

notation `C(` α `, ` β `)` := continuous_map α β

namespace continuous_map

variables [convergence_space α] [convergence_space β]

instance : has_coe_to_fun (C(α, β)) (λ _, α → β) := ⟨continuous_map.to_fun⟩

@[simp] lemma to_fun_eq_coe {f : C(α, β)} : f.to_fun = (f : α → β) := rfl

def eval (fa : C(α,β) × α) : β := fa.1 fa.2

variables {α β} {f g : continuous_map α β}

@[simp] theorem eval_comp_prod : eval ∘ prod.mk f = f := begin
  apply funext,
  assume x : α,
  apply comp_apply,
end

protected lemma continuous (f : C(α, β)) : continuous f := f.continuous_to_fun

end continuous_map

instance [convergence_space α] [convergence_space β] : convergence_space C(α, β) := {
  converges := λ l f, ∀ (a : α) (l' : filter α), converges l' a → converges (map continuous_map.eval (l ×ᶠ l')) (f a),
  pure_converges := begin
    assume f : C(α, β),
    assume x : α,
    assume l' : filter α,
    assume h : converges l' x,
    have h' : map continuous_map.eval (pure f ×ᶠ l') = map f l', from calc
      map continuous_map.eval (pure f ×ᶠ l') = map continuous_map.eval (map (prod.mk f) l') : by simp [filter.pure_prod]
      ... = map (continuous_map.eval ∘ prod.mk f) l' : by simp [filter.map_map]
      ... = map f l' : by simp [continuous_map.eval_comp_prod],
    rw h',
    exact f.continuous_to_fun h
  end,
  le_converges := begin
    assume l l' : filter C(α, β),
    assume h₁ : l ≤ l',
    assume f : C(α, β),
    intro h, -- h : converges l' f,
    assume x : α,
    assume la : filter α,
    assume ha : converges la x,
    have h₂ : l ×ᶠ la ≤ l' ×ᶠ la, from filter.prod_mono h₁ (partial_order.le_refl la),
    have h₃ : map continuous_map.eval (l ×ᶠ la) ≤ map continuous_map.eval (l' ×ᶠ la), from filter.map_mono h₂,
    exact le_converges h₃ (h x la ha),
  end,
}

-------------------------------------------------------------------------------
-- Separation aaioms
-------------------------------------------------------------------------------

class t0_space (α : Type*) [convergence_space α] : Prop :=
(t0_prop : ∀ x y : α, converges (pure x) y → converges (pure y) x → x = y)

class r0_space (α : Type*) [convergence_space α] : Prop :=
(r0_prop : ∀ x y, converges (pure x) y → ∀ (l : filter α), converges l x ↔ converges l y)

class t1_space (α : Type*) [convergence_space α] : Prop :=
(t1_prop : ∀ x y : α, converges (pure x) y → x = y)

class r1_space (α : Type*) [convergence_space α] : Prop :=
(r1_prop : ∀ x y, ∃ (l : filter α) [ne_bot l], converges l x ∧ converges l y → ∀ (l' : filter α), converges l' x ↔ converges l' y)

class t2_space (α : Type*) [convergence_space α] : Prop :=
(t2_prop : ∀ x y, ∀ (l : filter α) [ne_bot l], converges l x ∧ converges l y → x = y)

class r2_space (α : Type*) [convergence_space α] : Prop :=
(r2_prop : ∀ (x : α) (l : filter α), converges l x → converges (filter.generate (cl '' l.sets)) x)

class t3_space (α : Type*) [convergence_space α] extends t0_space α, r2_space α.

-------------------------------------------------------------------------------
-- Compact sets/spaces
-------------------------------------------------------------------------------

def is_compact [convergence_space α] (s : set α) := ∀ ⦃l : ultrafilter α⦄, s ∈ l → ∃ x, converges l.to_filter x

class compact_space (α : Type*) [convergence_space α] : Prop :=
(compact_prop : is_compact (univ : set α))

theorem is_compact.image {f : α → β} {s : set α} [convergence_space α] [convergence_space β]
  (h₀ : is_compact s) (h₁ : continuous f) : is_compact (f '' s) :=
begin
  unfold is_compact,
  assume lb : ultrafilter β,
  assume h₂ : f '' s ∈ lb,
  let la := ultrafilter.of_comap_inf_principal h₂,
  let h₃ : ultrafilter.map f la = lb := ultrafilter.of_comap_inf_principal_eq_of_map h₂,
  let h₄ : s ∈ la := ultrafilter.of_comap_inf_principal_mem h₂,
  obtain ⟨x, h₅ : converges la.to_filter x⟩ := h₀ h₄,
  have : converges (map f la) (f x) := h₁ h₅,
  rw ← h₃,
  use f x,
  tauto,
end

-------------------------------------------------------------------------------
-- Quotient maps
-------------------------------------------------------------------------------

def quotient_map [convergence_space α] [q : convergence_space β] (f : α → β) : Prop :=
surjective f ∧ q = convergence_space.coinduced f

lemma quotient_map_iff [convergence_space α] [q : convergence_space β] {f : α → β} :
quotient_map f ↔ surjective f ∧ ∀ lb y, converges lb y ↔ ∃ la x, (lb ≤ map f la) ∧ (y = f x) ∧ (converges la x) := begin
  split,
  -- Proving → direction.
  assume h : quotient_map f,
  split,
  exact h.1,
  assume lb : filter β,
  assume y : β,
  split,
  rw h.2,
  assume h' : converges_ (convergence_space.coinduced f) lb y,
  cases h',
    case pure_case begin
      obtain ⟨x, ha⟩ := h.1 y,
      rw ← ha at h',
      rw ← filter.map_pure at h',
      exact ⟨pure x, x, h', eq.symm ha, pure_converges x⟩,
    end,
    case other_case : la x h₁ h₂ h₃ begin
      exact ⟨la, x, h₁, h₂, h₃⟩,
    end,
  rintro ⟨la : filter α, x : α, h₁ : lb ≤ map f la, h₂ : y = f x, h₃ : converges la x⟩,
  rw h.2,
  exact coinduced_converges.other_case la x h₁ h₂ h₃,
  -- Proving ← direction
  intro h,
  unfold quotient_map,
  split,
  exact h.1,
  rw convergence_space_eq_iff,
  assume lb : filter β,
  assume y : β,
  rw h.2,
  split,
  rintro ⟨la : filter α, x : α, h₁ : lb ≤ map f la, h₂ : y = f x, h₃ : converges la x⟩,
  exact coinduced_converges.other_case la x h₁ h₂ h₃,
  assume h' : converges_ (convergence_space.coinduced f) lb y,
  cases h',
    case pure_case begin
      obtain ⟨x, ha⟩ := h.1 y,
      rw ← ha at h',
      rw ← filter.map_pure at h',
      exact ⟨pure x, x, h', eq.symm ha, pure_converges x⟩,
    end,
    case other_case : la x h₁ h₂ h₃ begin
      exact ⟨la, x, h₁, h₂, h₃⟩,
    end,
 end

/-
lemma quotient_prod_map
{α₁ β₁ : Type*} [p₁ : convergence_space α₁] [q₁ : convergence_space β₁] {f₁ : α₁ → β₁} (h₁ : quotient_map f₁)
{α₂ β₂ : Type*} [p₂ : convergence_space α₂] [q₂ : convergence_space β₂] {f₂ : α₂ → β₂} (h₂ : quotient_map f₂)
: quotient_map (prod.map f₁ f₂) := begin
  rw quotient_map_iff,
  rw quotient_map_iff at h₁,
  rw quotient_map_iff at h₂,
  split,
  exact surjective.prod_map h₁.1 h₂.1,
  rintros (l' : filter (β₁ × β₂)) (⟨b₁, b₂⟩ : β₁ × β₂),
  split,
  assume h : prod.convergence_space.converges l' (b₁, b₂),
  let l'₁ := map prod.fst l',
  let l'₂ := map prod.snd l',
  have hb₁ : q₁.converges l'₁ b₁, sorry,
  have hb₂ : q₂.converges l'₂ b₂, sorry,
  obtain ⟨l₁, a₁, le₁, eq₁, converges₁⟩ := (h₁.2 l'₁ b₁).mp hb₁,
  obtain ⟨l₂, a₂, le₂, eq₂, converges₂⟩ := (h₂.2 l'₂ b₂).mp hb₂,
  let l := l₁ ×ᶠ l₂,
  let a := (a₁, a₂),
  use l,
  use a,
end
-/

-------------------------------------------------------------------------------
-- Categorb Conv of convergence spaces
-------------------------------------------------------------------------------

universe u

def Conv : Type (u+1) := bundled convergence_space
