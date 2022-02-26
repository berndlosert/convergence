import tactic
import order.filter.partial
import order.filter.ultrafilter
import order.filter.bases
import algebra.support
import category_theory.concrete_category.bundled

noncomputable theory
open set function filter classical option category_theory
open_locale classical filter

variables {α α₁ α₂ β β₁ β₂ γ : Type*}

/-!
### Definition
-/

/-- Instances of this class will be refered to as convergence structures. -/
@[ext] class convergence_space (α : Type*) :=
(converges : filter α → α → Prop)
(pure_converges : ∀ x, converges (pure x) x)
(le_converges : ∀ {f g}, f ≤ g → ∀ {x}, converges g x → converges f x)

open convergence_space

section
variables (p : convergence_space α)
@[simp] def converges_ (f : filter α) (x : α) : Prop := @converges _ p f x
@[simp] def pure_converges_ (x : α) : converges (pure x) x := @pure_converges _ p x
@[simp] def le_converges_ ⦃f g : filter α⦄ (hle : f ≤ g) {x : α}
  (hconv : converges g x) : converges f x :=
@le_converges _ p _ _ hle _ hconv
end

theorem convergence_space_eq_iff {p q : convergence_space α} :
  p = q ↔ ∀ f x, converges_ p f x ↔ converges_ q f x :=
by simp [funext_iff, convergence_space.ext_iff p q]

/-!
### Parital ordering
-/

instance : has_le (convergence_space α) :=
⟨λ p q, ∀ {f x}, converges_ p f x → converges_ q f x⟩

instance : partial_order (convergence_space α) := 
{ le_refl :=
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
  ..convergence_space.has_le }

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

/-!
### Infimum and supremum of convergence spaces
-/

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

/-!
### Lattice of convergence spaces
-/

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

/-!
### Continuity
-/

def continuous [convergence_space α] [convergence_space β] (m : α → β) : Prop :=
∀ ⦃x f⦄, converges f x → converges (map m f) (m x)

def continuous_ (p : convergence_space α) (q : convergence_space β)
  (m : α → β) : Prop :=
@continuous α β p q m

lemma continuous.comp [convergence_space α] [convergence_space β]
  [convergence_space γ] {m' : β → γ} {m : α → β} (hcont' : continuous m')
  (hcont : continuous m) : continuous (m' ∘ m) :=
begin
  assume x : α,
  assume f : filter α,
  assume : converges f x,
  have : converges (map m f) (m x), from hcont this,
  have : converges (map m' (map m f)) (m' (m x)), from hcont' this,
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

lemma continuous_id' {α : Type*} [convergence_space α] : continuous (λ x : α, x) :=
continuous_id

lemma continuous_const [convergence_space α] [convergence_space β] {y : β} :
  continuous (λ (x : α), y) :=
begin
  assume x : α,
  assume f : filter α,
  assume : converges f x,
  simp,
  exact le_converges (tendsto_const_pure) (pure_converges y),
end

lemma continuous_le_dom {p p' : convergence_space α} {q : convergence_space β}
  {m : α → β} (hle : p' ≤ p) (hcont : continuous_ p q m) :
  continuous_ p' q m :=
begin
  assume x : α,
  assume f : filter α,
  assume : converges_ p' f x,
  have : converges_ p f x, from hle this,
  exact hcont this,
end

lemma continuous_inf_dom_left {p p' : convergence_space α}
  {q : convergence_space β} {m : α → β} :
  continuous_ p q m → continuous_ (p ⊓ p') q m :=
continuous_le_dom inf_le_left

lemma continuous_inf_dom_right {p p' : convergence_space α}
  {q : convergence_space β} {m : α → β} :
  continuous_ p' q m → continuous_ (p ⊓ p') q m :=
continuous_le_dom inf_le_right

lemma continuous_inf_rng [p : convergence_space α] {q q' : convergence_space β} {m : α → β}
  (hcont : continuous_ p q m) (hcont' : continuous_ p q' m) : continuous_ p (q ⊓ q') m :=
begin
  assume x : α,
  assume f : filter α,
  assume hp : converges f x,
  have hq : converges_ q (map m f) (m x), from hcont hp,
  have hq' : converges_ q' (map m f) (m x), from hcont' hp,
  exact and.intro hq hq',
end

structure homeomorph (α β : Type*) [convergence_space α] [convergence_space β]
  extends α ≃ β :=
(continuous_to_fun : continuous to_fun)
(continuous_inv_fun : continuous inv_fun)

/-!
### Induced convergence space
-/

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

lemma continuous_induced_dom {m : α → β} {q : convergence_space β} :
  continuous_ (@convergence_space.induced α β m q) q m :=
begin
  assume x : α,
  assume f : filter α,
  let p := @convergence_space.induced α β m q,
  assume hconv : converges_ p f x,
  assumption,
end

lemma continuous_induced_rng {m₁ : α → β} {m₂ : β → γ}
  [p : convergence_space α] [q : convergence_space β] [r : convergence_space γ]
  (hcont : continuous (m₂ ∘ m₁)) : continuous_ p (convergence_space.induced m₂) m₁ :=
begin
  assume x : α,
  assume f : filter α,
  assume hconv : converges f x,
  have : converges (map m₂ (map m₁ f)) (m₂ (m₁ x)), from hcont hconv,
  assumption,
end

/-!
### Coinduced convergence space
-/

/-- Given `m : α → β`, where `α` is convergence space, the coinduced convergence
  structure on `β` is the least convergence structure making `m`
  continuous. -/
def convergence_space.coinduced (m : α → β) [convergence_space α] :
  convergence_space β :=
{ converges := λ g y, (g ≤ pure y) ∨
    ∃ f x, (g ≤ map m f) ∧ (m x = y) ∧ (converges f x),
  pure_converges := λ b, or.inl (le_refl (pure b)),
  le_converges :=
  begin
    assume g₁ g₂ : filter β,
    assume hle : g₁ ≤ g₂,
    assume y : β,
    intro hconv,
    exact or.elim hconv
      (λ hle' : g₂ ≤ pure y, or.inl (le_trans hle hle'))
      (λ ⟨f, x, hle', heq, hconv'⟩,
        or.inr ⟨f, x, le_trans hle hle', heq, hconv'⟩)
  end }

lemma continuous.le_coinduced (m : α → β) [convergence_space α]
  [q : convergence_space β] (hm : continuous m) :
  convergence_space.coinduced m ≤ q :=
begin
  unfold has_le.le,
  assume g : filter β,
  assume y : β,
  assume hconv : converges_ (convergence_space.coinduced m) g y,
  cases hconv,
    case or.inl begin
      exact le_converges_ q hconv (pure_converges_ q y),
    end,
    case or.inr : hexists begin
      obtain ⟨f, x, h₀, h₁, h₂⟩ := hexists,
      have : converges_ q (map m f) (m x), from hm h₂,
      rw ← h₁,
      exact le_converges_ q h₀ this,
    end
end

lemma coinduced_id [p : convergence_space α] : convergence_space.coinduced id = p :=
begin
  rw convergence_space_eq_iff,
  assume f : filter α,
  assume x : α,
  split,
  assume hconv : converges_ (convergence_space.coinduced id) f x,
  cases hconv,
    case or.inl begin
      exact le_converges_ p hconv (pure_converges_ p x),
    end,
    case or.inr : hexists begin
      obtain ⟨g, y, hle, heq, hconv'⟩ := hexists,
      simp at hle,
      simp at heq,
      rw ← heq,
      exact le_converges_ p hle hconv',
    end,
  assume hconv : converges_ p f x,
  exact or.inr ⟨f, x, le_refl f, rfl, hconv⟩,
end

lemma continuous_iff_coinduced_le {m : α → β}
  [convergence_space α] [q : convergence_space β]  : 
  continuous m ↔ convergence_space.coinduced m ≤ q :=
begin
  split,
  assume hcont : continuous m,
  unfold has_le.le,
  assume g : filter β,
  assume y : β,
  assume hconv : converges_ (convergence_space.coinduced m) g y,
  cases hconv,
    case or.inl begin
      exact le_converges_ q hconv (pure_converges_ q y),
    end,
    case or.inr : hexists begin
      obtain ⟨f, x, hle, heq, hconv'⟩ := hexists,
      rw ← heq,
      exact le_converges_ q hle (hcont hconv'),
    end,
  assume hle : convergence_space.coinduced m ≤ q,
  assume x : α,
  assume f : filter α,
  assume hconv : converges f x,
  exact hle (or.inr ⟨f, x, le_refl (map m f), rfl, hconv⟩),
end

lemma coinduced_compose [convergence_space α]
  {m₁ : α → β} {m₂ : β → γ} : 
  @convergence_space.coinduced _ _ m₂ (convergence_space.coinduced m₁) = 
  convergence_space.coinduced (m₂ ∘ m₁) :=
begin
  rw convergence_space_eq_iff,
  assume h : filter γ,
  assume z : γ,
  let p := @convergence_space.coinduced _ _ m₂ (convergence_space.coinduced m₁),
  let q := convergence_space.coinduced (m₂ ∘ m₁),
  split,
  assume hconv : converges_ p h z,
  cases hconv,
    case or.inl begin
      exact or.inl hconv,
    end,
    case or.inr : hg begin
      obtain ⟨g, y, hg₁, hg₂, hg₃⟩ := hg,
      cases hg₃,
        case or.inl begin
          have hle' : h ≤ pure (m₂ y), from calc
            h ≤ map m₂ g : hg₁
            ... ≤ map m₂ (pure y) : map_mono hg₃
            ... = pure (m₂ y) : by rw filter.map_pure,
          rw ← hg₂,
          exact or.inl hle',
        end,
        case or.inr : hf begin
          obtain ⟨f, x, hf₁, hf₂, hf₃⟩ := hf,
          have hle : h ≤ map (m₂ ∘ m₁) f, from calc
            h ≤ map m₂ (map m₁ f) : le_trans hg₁ (map_mono hf₁)
            ... = map (m₂ ∘ m₁) f : by rw filter.map_map,
          have heq : (m₂ ∘ m₁) x = z, from calc
            (m₂ ∘ m₁) x = m₂ (m₁ x) : by tauto
            ... = m₂ y : by rw hf₂
            ... = z : by rw hg₂,
          exact or.inr ⟨f, x, hle, heq, hf₃⟩,
        end
    end,
  assume hconv : converges_ q h z,
  cases hconv,
    case or.inl begin
      exact or.inl hconv,
    end,
    case or.inr : hexists begin
      obtain ⟨f, x, hf₁, hf₂, hf₃⟩ := hexists,
      let g : filter β := map m₁ f,
      let y : β := m₁ x,
      let hg₁ : h ≤ map m₂ g := by tauto,
      let hg₂ : m₂ y = z := by tauto,
      let hg₃ : converges_ (convergence_space.coinduced m₁) g y := 
        or.inr ⟨f, x, le_refl (map m₁ f), rfl, hf₃⟩,
      exact or.inr ⟨g, y, hg₁, hg₂, hg₃⟩,
    end
end

lemma continuous_coinduced_rng [p : convergence_space α]
  {m : α → β} : continuous_ p (convergence_space.coinduced m) m :=
begin
  assume x : α,
  assume f : filter α,
  assume hconv : converges f x,
  exact or.inr ⟨f, x, le_refl (map m f), rfl, hconv⟩,
end

/-!
### Limits, adherence, interior, closure, open, closed, neighborhoods
-/

section

variables [convergence_space α]

/-- The set of all limits of a filter. -/
def lim (f : filter α) : set α := { x | converges f x }

/-- A point `x` adheres to a filter `f` there is some proper filter
  smaller than `f` that converges to `x`. -/
def adheres (f : filter α) (x : α) : Prop :=
∃ (g : filter α) [ne_bot g], g ≤ f ∧ converges g x

/-- The set of all point that adhere to a filter. -/
def adh (f : filter α) : set α := { x | adheres f x }

/-- The interior of a set `s` consists of those points in `s` that are
  limits of proper filters containing s. -/
def interior (s : set α) : set α := { x ∈ s | ∀ f, converges f x → s ∈ f }

/-- A set is open if it equals its interior. -/
def is_open (s : set α) : Prop := s = interior s

/-- The closure of a set `s` consists of all those points that are limits
  of proper filters that contain `s`. -/
def closure (s : set α) : set α :=
{ x | ∃ (f : filter α) [ne_bot f], converges f x ∧ s ∈ f }

/-- A set is closed if it equals its closure. -/
def is_closed (s : set α) : Prop := s = closure s

/-- A set `s` is dense of every point in the space belongs to `closure s`. -/
def is_dense (s : set α) : Prop := ∀ x, x ∈ closure s

/-- `cl f` is the filter generated by the closure of all the elements of `f`. -/
def cl (f : filter α) : filter α := filter.generate (closure '' f.sets)

/-- A set `s` is strictly dense if -/
def is_strictly_dense (s : set α) : Prop :=
∀ {x : α} {f : filter α}, converges f x →
  ∃ g, (s ∈ g) ∧ (converges g x) ∧ (f ≤ cl g)

/-- The neighborhood filter of `x` is the infimum of all filters converging
  to `x`. -/
def nhds (x : α) : filter α := ⨅ f ∈ {g : filter α | converges g x}, f

end

/-!
### Product spaces
-/

section

variables [convergence_space α] [convergence_space β]

instance : convergence_space (α × β) :=
convergence_space.induced prod.fst ⊓ convergence_space.induced prod.snd

lemma continuous_fst : continuous (@prod.fst α β) :=
continuous_inf_dom_left continuous_induced_dom

lemma continuous_snd : continuous (@prod.snd α β) :=
continuous_inf_dom_right continuous_induced_dom

lemma prod.converges {f : filter α} {g : filter β} {x : α} {y : β}
  (hf : converges f x) (hg : converges g y) : converges (f ×ᶠ g) (x, y) :=
begin
  unfold converges,
  have hf' : converges (map prod.fst (f ×ᶠ g)) x,
    from le_converges tendsto_fst hf,
  have hg' : converges (map prod.snd (f ×ᶠ g)) y,
    from le_converges tendsto_snd hg,
  exact and.intro hf' hg',
end

lemma prod.converges' {f : filter (α × β)} {x : α × β}
  (hfst : converges (map prod.fst f) (prod.fst x))
  (hsnd : converges (map prod.snd f) (prod.snd x)) :
  (converges f x) :=
⟨hfst, hsnd⟩

lemma continuous.prod_mk [convergence_space α] [convergence_space β₁]
  [convergence_space β₂] {m₁ : α → β₁} {m₂ : α → β₂}
  (hcont₁ : continuous m₁) (hcont₂ : continuous m₂) : continuous (λx, (m₁ x, m₂ x)) :=
continuous_inf_rng (continuous_induced_rng hcont₁) (continuous_induced_rng hcont₂)

lemma continuous.prod.mk [convergence_space α] [convergence_space β] (x : α) : 
  continuous (prod.mk x : β → α × β) :=
continuous_const.prod_mk continuous_id'

end

/-!
### Other convergence spaces constructions
-/

instance {p : α → Prop} [convergence_space α] : convergence_space (subtype p) :=
convergence_space.induced (coe : subtype p → α)

instance {r : α → α → Prop} [convergence_space α] : convergence_space (quot r) :=
convergence_space.coinduced (quot.mk r)

instance [convergence_space α] : convergence_space (option α) :=
convergence_space.coinduced some

/-!
### The convergence space C(α,β)
-/

/-- Bundled continuous maps. -/
structure continuous_map (α β : Type*)
  [convergence_space α] [convergence_space β] :=
(to_fun : α → β)
(continuous_to_fun : continuous to_fun)

notation `C(` α `, ` β `)` := continuous_map α β

namespace continuous_map

variables [convergence_space α] [convergence_space β]

instance : has_coe_to_fun (C(α, β)) (λ _, α → β) := ⟨continuous_map.to_fun⟩

@[simp] lemma to_fun_eq_coe {f : C(α, β)} : f.to_fun = (f : α → β) := rfl

def eval : C(α,β) × α → β := λ ⟨f, x⟩, f x

variables {α β} {f g : continuous_map α β}

@[simp] theorem eval_comp_prod : eval ∘ prod.mk f = f := begin
  apply funext,
  assume x : α,
  apply comp_apply,
end

protected lemma continuous (f : C(α, β)) : continuous f := f.continuous_to_fun

end continuous_map

instance [convergence_space α] [convergence_space β] :
  convergence_space C(α, β) :=
{ converges := λ f m, ∀ (x : α) (g : filter α),
    converges g x → converges (map continuous_map.eval (f ×ᶠ g)) (m x),
  pure_converges :=
  begin
    assume m : C(α, β),
    assume x : α,
    assume g : filter α,
    assume hconv : converges g x,
    have hmap : map continuous_map.eval (pure m ×ᶠ g) = map m g, from calc
      map continuous_map.eval (pure m ×ᶠ g)
          = map continuous_map.eval (map (prod.mk m) g) :
            by simp [filter.pure_prod]
      ... = map (continuous_map.eval ∘ prod.mk m) g :
            by simp [filter.map_map]
      ... = map m g : by simp [continuous_map.eval_comp_prod],
    rw hmap,
    exact m.continuous_to_fun hconv
  end,
  le_converges :=
  begin
    assume f g : filter C(α, β),
    assume hle : f ≤ g,
    assume m : C(α, β),
    intros hconv, -- hconv : converges g m,
    assume x : α,
    assume f' : filter α,
    assume hconv' : converges f' x,
    have hle₁ : f ×ᶠ f' ≤ g ×ᶠ f',
      from filter.prod_mono hle (partial_order.le_refl f'),
    have hle₂ : map continuous_map.eval (f ×ᶠ f') ≤
      map continuous_map.eval (g ×ᶠ f'), from filter.map_mono hle₁,
    exact le_converges hle₂ (hconv x f' hconv'),
  end,
}

/-!
### Separation axioms
-/

/-- In a T₀ space, the equality of two points can be determined by checking
  if the corresponding pure filters converge to the other point. -/
class t0_space (α : Type*) [convergence_space α] : Prop :=
(t0_prop : ∀ x y : α, converges (pure x) y ∧ converges (pure y) x ↔ x = y)

/-- In an R₀ space, if `pure x` converges to `y`, then `x` and `y` have the
  same convergent filters. -/
class r0_space (α : Type*) [convergence_space α] : Prop :=
(r0_prop : ∀ x y, converges (pure x) y →
∀ (f : filter α), converges f x ↔ converges f y)

/-- In a T₁ space, the `pure` filters have exactly one limit. -/
class t1_space (α : Type*) [convergence_space α] : Prop :=
(t1_prop : ∀ x y : α, converges (pure x) y → x = y)

/-- In an R₁ space, if a `x` and `y` are the limits of a proper filter, then
  they share the same convergent filters. -/
class r1_space (α : Type*) [convergence_space α] : Prop :=
(r1_prop : ∀ x y, ∃ (f : filter α) [ne_bot f], converges f x ∧ converges f y →
  ∀ (g : filter α), converges g x ↔ converges g y)

/-- In a T₂ space, every proper filter has exactly one limit. -/
class t2_space (α : Type*) [convergence_space α] : Prop :=
(t2_prop : ∀ x y, ∀ (f : filter α) [ne_bot f],
  converges f x ∧ converges f y → x = y)

/-- In an R₂ space, if a filter converges, then so does its closure. -/
class r2_space (α : Type*) [convergence_space α] : Prop :=
(r2_prop : ∀ (x : α) (f : filter α), converges f x → converges (cl f) x)

/-- A T₃ space is a T₀ & R₂ space. -/
class t3_space (α : Type*) [convergence_space α] extends
  t0_space α, r2_space α.

/-!
### Compact sets/spaces
-/

def is_compact [convergence_space α] (s : set α) :=
∀ ⦃f : ultrafilter α⦄, s ∈ f → ∃ x, converges f.to_filter x

class compact_space (α : Type*) [convergence_space α] : Prop :=
(compact_prop : is_compact (univ : set α))

theorem is_compact.image {m : α → β} {s : set α}
  [convergence_space α] [convergence_space β]
  (hcom : is_compact s) (hcont : continuous m) : is_compact (m '' s) :=
begin
  unfold is_compact,
  assume g : ultrafilter β,
  assume hmem : m '' s ∈ g,
  let f := ultrafilter.of_comap_inf_principal hmem,
  let heq : ultrafilter.map m f = g :=
    ultrafilter.of_comap_inf_principal_eq_of_map hmem,
  let hmem' : s ∈ f := ultrafilter.of_comap_inf_principal_mem hmem,
  obtain ⟨x, hconv : converges f.to_filter x⟩ := hcom hmem',
  have : converges (map m f) (m x) := hcont hconv,
  rw ← heq,
  use m x,
  tauto,
end

/-!
### Quotient maps
-/

/-- A surjective map `m : α → β` where β has the coinduced convergence is
  called a quotient map. -/
def quotient_map [convergence_space α] [q : convergence_space β]
(m : α → β) : Prop := surjective m ∧ q = convergence_space.coinduced m

lemma quotient_map.converges [convergence_space α] [q : convergence_space β]
  {m : α → β} (hquot : quotient_map m) (g : filter β) (y : β) :
  converges g y ↔ ∃ f x, (g ≤ map m f) ∧ (m x = y) ∧ (converges f x) :=
begin
  split,
  -- Proof of → direction.
  assume : converges g y,
  rw hquot.2 at this,
  cases this,
    case or.inl begin
      obtain ⟨x, heq⟩ := hquot.1 y,
      rw ← heq at this,
      rw ← filter.map_pure at this,
      exact ⟨pure x, x, this, heq, pure_converges x⟩,
    end,
    case or.inr : hexists begin
      exact hexists,
    end,
  -- Proof of ← direction.
  rintro hexists,
  rw hquot.2,
  exact or.inr hexists,
end

lemma quotient_map_iff [convergence_space α] [q : convergence_space β]
  {m : α → β} : quotient_map m ↔ surjective m ∧ ∀ g y, converges g y ↔
  ∃ f x, (g ≤ map m f) ∧ (m x = y) ∧ (converges f x) :=
begin
  split,
  -- Proving → direction.
  assume hlhs : quotient_map m,
  split,
  exact hlhs.1,
  assume g : filter β,
  assume y : β,
  exact quotient_map.converges hlhs g y,
  -- Proving ← direction
  intro hrhs,
  unfold quotient_map,
  split,
  exact hrhs.1,
  rw convergence_space_eq_iff,
  assume g : filter β,
  assume y : β,
  change converges_ q g y ↔ g ≤ pure y ∨
    ∃ (f : filter α) (x : α), g ≤ map m f ∧ m x = y ∧ converges f x,
  split,
  assume hconv : converges_ q g y,
  exact or.inr ((hrhs.2 g y).mp hconv),
  intro hconj,
  cases hconj,
    case or.inl begin
      exact le_converges_ q hconj (pure_converges_ q y),
    end,
    case or.inr begin
      exact ((hrhs.2 g y).mpr hconj),
    end,
end

lemma quotient_map.continuous_iff [convergence_space α] [convergence_space β]
  [convergence_space γ] {m₁ : α → β} {m₂ : β → γ} (hquot : quotient_map m₁) :
  continuous m₂ ↔ continuous (m₂ ∘ m₁) :=
by rw [continuous_iff_coinduced_le, continuous_iff_coinduced_le, hquot.right, coinduced_compose]

lemma quotient_map.id [convergence_space α] : quotient_map (@id α) :=
⟨assume a, ⟨a, rfl⟩, coinduced_id.symm⟩

lemma quotient_map.prod_map
  [convergence_space α₁] [convergence_space β₁]
  {m₁ : α₁ → β₁} (hquot₁ : quotient_map m₁)
  [convergence_space α₂] [convergence_space β₂]
  {m₂ : α₂ → β₂} (hquot₂ : quotient_map m₂) :
  quotient_map (prod.map m₁ m₂) :=
begin
  rw quotient_map_iff,
  rw quotient_map_iff at hquot₁,
  rw quotient_map_iff at hquot₂,
  split,
  exact surjective.prod_map hquot₁.1 hquot₂.1,
  rintros (g : filter (β₁ × β₂)) (⟨y₁, y₂⟩ : β₁ × β₂),
  split,
  assume hconv : convergence_space.converges g (y₁, y₂),
  let g₁ := map prod.fst g,
  let g₂ := map prod.snd g,
  have hg₁ : converges g₁ y₁, from continuous_fst hconv,
  have hg₂ : converges g₂ y₂, from continuous_snd hconv,
  obtain ⟨f₁, x₁, hle₁, heq₁, hf₁⟩ := (hquot₁.2 g₁ y₁).mp hg₁,
  obtain ⟨f₂, x₂, hle₂, heq₂, hf₂⟩ := (hquot₂.2 g₂ y₂).mp hg₂,
  let f := f₁ ×ᶠ f₂,
  let x := (x₁, x₂),
  use f,
  use x,
  have hle : g ≤ map (prod.map m₁ m₂) f, from calc
    g ≤ map prod.fst g ×ᶠ map prod.snd g : filter.le_prod_map_fst_snd
    ... = g₁ ×ᶠ g₂ : by tauto
    ... ≤ map m₁ f₁ ×ᶠ map m₂ f₂ : prod_mono hle₁ hle₂
    ... = map (prod.map m₁ m₂) (f₁ ×ᶠ f₂) : prod_map_map_eq' m₁ m₂ f₁ f₂,
  have heq : prod.map m₁ m₂ x = (y₁, y₂), from calc
    prod.map m₁ m₂ x = prod.map m₁ m₂ (x₁, x₂) : by tauto
      ... = (m₁ x₁, m₂ x₂) : by rw (prod.map_mk m₁ m₂ x₁ x₂)
      ... = (y₁, y₂) : by rw [heq₁, heq₂],
  have hconv' : converges f x, from prod.converges hf₁ hf₂,
  exact ⟨hle, heq, hconv'⟩,
  rintro ⟨f, x, hle, heq, hf⟩,
  let f₁ := map prod.fst f,
  let f₂ := map prod.snd f,
  simp [prod.map_mk m₁ m₂ x.1 x.2] at heq,
  let g₁ := map prod.fst g,
  let g₂ := map prod.snd g,
  have hle₁ : g₁ ≤ map m₁ f₁, from calc
    g₁ ≤ map prod.fst (map (prod.map m₁ m₂) f) : map_mono hle
    ... = map (prod.fst ∘ prod.map m₁ m₂) f : map_map
    ... = map (m₁ ∘ prod.fst) f : by rw (prod.map_fst' m₁ m₂)
    ... = map m₁ f₁ : by simp,
  have hle₂ : g₂ ≤ map m₂ f₂, from calc
    g₂ ≤ map prod.snd (map (prod.map m₁ m₂) f) : map_mono hle
    ... = map (prod.snd ∘ prod.map m₁ m₂) f : map_map
    ... = map (m₂ ∘ prod.snd) f : by rw (prod.map_snd' m₁ m₂)
    ... = map m₂ f₂ : by simp,
  have hg₁ : converges g₁ y₁,
    from (hquot₁.2 g₁ y₁).mpr ⟨f₁, x.1, hle₁, heq.1, hf.1⟩,
  have hg₂ : converges g₂ y₂,
    from (hquot₂.2 g₂ y₂).mpr ⟨f₂, x.2, hle₂, heq.2, hf.2⟩,
  exact ⟨hg₁, hg₂⟩,
end

lemma quotient_map_quot_mk [convergence_space α] {r : α → α → Prop} :
  quotient_map (quot.mk r) :=
⟨quot.exists_rep, rfl⟩

lemma continuous_quot_mk [convergence_space α] 
  {r : α → α → Prop} : continuous (quot.mk r) :=
continuous_coinduced_rng

/-!
### Category Conv of convergence spaces
-/

universe u

def Conv : Type (u+1) := bundled convergence_space
