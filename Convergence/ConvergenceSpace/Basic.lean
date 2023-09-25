import Mathlib.Order.Filter.Ultrafilter
import Mathlib.Algebra.Support
import Mathlib.Order.Filter.Lift
import Mathlib.Tactic.Continuity

set_option autoImplicit true

noncomputable section

open Set Filter

/-!
# Basic theory of convergence spaces

The following presents the basic theory of convergence spaces.

## Notation

* We use the letters `p`, `q`, etc. for convergence structures.
* We use the letters `F`, `G`, etc. for filters.
* We use the greek letters `α`, `β`, etc. for spaces.
* We use the letters `s`, `t`, etc. for sets.
* We use the letters `x`, `y`, etc. for points in spaces.
* Hypotheses will always start with an "h", e.g. `hconv`, `hle`, etc.
* Variables denoting collections will end in "s". For example `ps` will stand for a
  set of convergence structures.

## References

* Preuss, Foundations of Topology
* Gary Richardson, personal correspondence
-/

/-!
### Definition
-/

/--
An instance or value of type `ConvergenceSpace α` is called a "convergence structure".

**Remarks**:
* Preuss calls convergence spaces "generalized convergence spaces".
* For `x : α`, the principal filter on `x` is denoted `pure x`. These are the dot filters
  from Preuss and Richardson. We will call them pure filters.
* In mathlib, `F ≤ G` means `G ⊆ F`, but we still read it as "`F` is finer than `G`" or
  "`G` is coarser than `F`".
* Filters in mathlib can contain the empty set. These filters are the bottom filters,
  denoted ⊥. Some definitions from the literature are slightly modified to account for
  bottom filters, but for the most part, we won't need to worry about them.
-/
@[ext]
class ConvergenceSpace (α : Type*) where
  converges : Filter α → α → Prop
  pure_converges : ∀ x, converges (pure x) x
  le_converges : ∀ {F G}, F ≤ G → ∀ {x}, converges G x → converges F x

open ConvergenceSpace

/- These will come in handy when we are not using instance arguments. -/
section
variable (p : ConvergenceSpace α)

@[simp]
def converges_ (F : Filter α) (x : α) : Prop := @converges _ p F x

@[simp]
def pure_converges_ (x : α) : converges (pure x) x := @pure_converges _ p x

@[simp]
def le_converges_ ⦃F G : Filter α⦄ (hle : F ≤ G) {x : α}
  (hconv : converges G x) : converges F x :=
@le_converges _ p _ _ hle _ hconv
end

/- In any convergence space, the bottom filter converges to every point. This
is OK though, since we never care what the bottom filter does. -/
theorem bot_converges [ConvergenceSpace α] (x : α) : converges ⊥ x :=
le_converges bot_le (pure_converges x)

/-!
### Ordering
-/

/--
The ordering on convergence structures on the type `α` is defined so that `p ≤ q`
means `p`-convergence implies `q`-convergence. We read `p ≤ q` as "`p` is finer
than `q`" or "`q` is coarser than `p`".

**Remarks**
* Preus defines `p ≤ q` to mean that id : (α, p) → (α, q) is continuous
  (see p. 30, Def. 1.1.4). This is the same as our definition.
* Dr. Richardson defines it backwards, i.e. he writes `p ≥ q` for our `p ≤ q`.
* The reading "`p` is finer than `q`" that we adopted is the same one used by Preuss
  and Dr. Richardson.
* In the context of topologies, "`t1` is finer than `t2`" means `t2 ⊆ t1`. This meaning
  is consistent with our meaning.
-/

@[simp]
instance : LE (ConvergenceSpace α) where
  le p q := ∀ {F x}, converges_ p F x → converges_ q F x

instance : PartialOrder (ConvergenceSpace α) where
  le_refl := by
    repeat intro
    assumption
  le_trans := by
    intros p q r hpq hqr F x hconv
    exact (hqr (hpq hconv))
  le_antisymm := by
    intros p q hpq hqp
    ext F x
    exact Iff.intro hpq hqp

/-!
### Initial and final convergence structures

Here, we follow the definitions from Preuss. The initial convergence structure is defined
on p. 32 at the top of the page; the final convergence structre is defined on p. 68 in
Remark 2.3.1.4.

**Remark**
The terminolgoy "initial" and "final" is backwards from their categorical meaning. For
example, if you think of the family f : ∀ i : ι, α → β i as projections, then the initial
convergence convergence structure will yield be the product convergence structure (and
products are terminal objects, as is well known). See Preuss, p. 18 for the topological
version of this example.
-/

def ConvergenceSpace.initial {ι : Type*} {β : ι → Type*}
  (p : ∀ i : ι, ConvergenceSpace (β i)) (f : ∀ i : ι, α → β i) : ConvergenceSpace α where
  converges F x := ∀ i : ι, converges_ (p i) (map (f i) F) ((f i) x)
  pure_converges x i := by rw [Filter.map_pure]; exact pure_converges_ (p i) ((f i) x)
  le_converges hle x hconv i := le_converges_ (p i) (Filter.map_mono hle) (hconv i)

def ConvergenceSpace.final (ι : Type*) (α : ι → Type*) (β : Type*)
  (p : ∀ i : ι, ConvergenceSpace (α i)) (f : ∀ i : ι, α i → β) : ConvergenceSpace β where
  converges G y := G ≤ pure y ∨ ∃ i F x,
    converges_ (p i) F x ∧ G ≤ Filter.map (f i) F ∧ f i x = y
  pure_converges x := by simp
  le_converges := by
    intros G G' hle y hconv
    cases' hconv with hle' hex
    · exact Or.inl (le_trans hle hle')
    · obtain ⟨i, F, x, hconv', hle', heq⟩ := hex
      refine Or.inr ⟨i, F, x, hconv', le_trans hle hle', heq⟩

/-!
### Lattice of convergence structures

We define the lattice of convergence structures on `α` by defining what `sInf ps` means
for any set of convergence structures `ps` on `α`. Basically, `sInf ps` is the initial
convergence structure of the `id` functions with respect to the family obtained from
`ps`.

The resulting lattice will have the discrete convergence structure as the bottom element
and the indiscrete convergence structure as the top element.
-/

instance : Bot (ConvergenceSpace α) where
  bot := {
    converges := λ F x ↦ F ≤ pure x,
    pure_converges := by tauto,
    le_converges := by tauto
  }

instance : Top (ConvergenceSpace α) where
  top := {
    converges := λ F x ↦ true,
    pure_converges := by tauto,
    le_converges := by tauto
  }

instance : Inf (ConvergenceSpace α) where
  inf p q := {
    converges := λ F x ↦ (converges_ p F x) ∧ (converges_ q F x),
    pure_converges := λ x ↦ And.intro (pure_converges_ p x) (pure_converges_ q x),
    le_converges := λ {F} {G} hle x hconv ↦
      And.intro (le_converges_ p hle hconv.left) (le_converges_ q hle hconv.right)
  }

instance : Sup (ConvergenceSpace α) where
  sup p q := {
    converges := λ F x ↦ (converges_ p F x) ∨ (converges_ q F x),
    pure_converges := λ x ↦ Or.inl (pure_converges_ p x),
    le_converges := λ {F} {G} hle x hconv ↦ Or.elim hconv
      (λ hl ↦ Or.inl (le_converges_ p hle hl))
      (λ hr ↦ Or.inr (le_converges_ q hle hr))
  }

instance : InfSet (ConvergenceSpace α) where
  sInf ps := {
    converges := λ f x ↦ ∀ {p}, p ∈ ps → converges_ p f x,
    pure_converges := λ x p ps ↦ pure_converges_ p x,
    le_converges := λ {F} {G} hle x hconv p hmem ↦ le_converges_ p hle (hconv hmem)
  }

instance : SupSet (ConvergenceSpace α) where
  sSup ps := {
    converges := λ f x ↦ f ≤ pure x ∨
      ∃ p, p ∈ ps ∧ converges_ p f x,
    pure_converges := by
      intros x
      exact Or.inl (le_refl (pure x)),
    le_converges := by
      intros F G hle x hor
      rcases hor with hle'|⟨p, hmem, hconv⟩
      · exact Or.inl (le_trans hle hle')
      · refine Or.inr ⟨p, hmem, le_converges_ p hle hconv⟩
  }

instance : SemilatticeInf (ConvergenceSpace α) where
  inf_le_left p q F x hconv := hconv.left
  inf_le_right p q F x hconv := hconv.right
  le_inf p q r hle hle' F x hp := And.intro (hle hp) (hle' hp)

instance : SemilatticeSup (ConvergenceSpace α) where
  le_sup_left p q F x hconv := Or.inl hconv
  le_sup_right p q F x hconv := Or.inr hconv
  sup_le p q r hle hle' F x hconv := hconv.elim hle hle'

instance : CompleteSemilatticeInf (ConvergenceSpace α) where
  sInf_le ps p hmem F x hconv := hconv hmem
  le_sInf ps q hle F x hconv p hmem := (hle p hmem) hconv

instance : CompleteSemilatticeSup (ConvergenceSpace α) where
  le_sSup ps p hmem F x hconv := Or.inr (Exists.intro p (And.intro hmem hconv))
  sSup_le qs p hle F x hconv :=
    hconv.elim
      (λ hle' ↦ le_converges_ p hle' (pure_converges_ p x))
      (λ hexists ↦ Exists.elim hexists (λ q hconv' ↦ (hle q hconv'.left) hconv'.right))

instance : CompleteLattice (ConvergenceSpace α) where
  inf_le_left := SemilatticeInf.inf_le_left
  inf_le_right := SemilatticeInf.inf_le_right
  le_inf := SemilatticeInf.le_inf
  le_sSup := CompleteSemilatticeSup.le_sSup
  sSup_le := CompleteSemilatticeSup.sSup_le
  sInf_le := CompleteSemilatticeInf.sInf_le
  le_sInf := CompleteSemilatticeInf.le_sInf
  le_top p := by intros; tauto
  bot_le p F x hconv := le_converges_ p hconv (pure_converges_ p x)


-- /-!
-- ### Continuity
-- -/

-- /-- A function `m` between converges spaces is continuous at a point `x`
--   if whenever a filter converges to `x`, it's image under `m` converges to `m x`. --/
-- def continuous_at [convergence_space α] [convergence_space β] (m : α → β) (x : α) :=
-- ∀ ⦃f⦄, converges f x → converges (map m f) (m x)

-- def continuous [convergence_space α] [convergence_space β] (m : α → β) : Prop :=
-- ∀ ⦃x⦄, continuous_at m x

-- def continuous_ (p : convergence_space α) (q : convergence_space β)
--   (m : α → β) : Prop :=
-- @continuous α β p q m

-- lemma continuous.comp [convergence_space α] [convergence_space β]
--   [convergence_space γ] {m' : β → γ} {m : α → β} (hcont' : continuous m')
--   (hcont : continuous m) : continuous (m' ∘ m) :=
-- λ x f hconv, by convert (hcont' (hcont hconv))

-- lemma continuous_id [convergence_space α] : continuous (id : α → α) :=
-- λ x f hconv, by simpa [filter.map_id]

-- lemma continuous_id' {α : Type*} [convergence_space α] : continuous (λ x : α, x) :=
-- continuous_id

-- lemma continuous_const [convergence_space α] [convergence_space β] {y : β} :
--   continuous (λ (x : α), y) :=
-- λ x f hconv, le_converges (tendsto_const_pure) (pure_converges y)

-- lemma continuous_le_dom {p p' : convergence_space α} {q : convergence_space β}
--   {m : α → β} (hle : p' ≤ p) (hcont : continuous_ p q m) :
--   continuous_ p' q m :=
-- λ x f hconv, hcont (hle hconv)

-- lemma continuous_inf_dom_left {p p' : convergence_space α}
--   {q : convergence_space β} {m : α → β} :
--   continuous_ p q m → continuous_ (p ⊓ p') q m :=
-- continuous_le_dom inf_le_left

-- lemma continuous_inf_dom_right {p p' : convergence_space α}
--   {q : convergence_space β} {m : α → β} :
--   continuous_ p' q m → continuous_ (p ⊓ p') q m :=
-- continuous_le_dom inf_le_right

-- lemma continuous_inf_rng [p : convergence_space α] {q q' : convergence_space β} {m : α → β}
--   (hcont : continuous_ p q m) (hcont' : continuous_ p q' m) : continuous_ p (q ⊓ q') m :=
-- λ x f hp, and.intro (hcont hp) (hcont' hp)

-- structure homeomorph (α β : Type*) [convergence_space α] [convergence_space β]
--   extends α ≃ β :=
-- (continuous_to_fun : continuous to_fun)
-- (continuous_inv_fun : continuous inv_fun)

-- /-!
-- ### Induced convergence structure
-- -/

-- /-- Given `m : α → β`, where `β` is a convergence space, the induced convergence
--   structure on `α` is the greatest (coarsest) convergence structure making `m`
--   continuous. -/
-- def convergence_space.induced (m : α → β) [convergence_space β] :
--   convergence_space α :=
-- { converges := λ f x, converges (map m f) (m x),
--   pure_converges := by simp [filter.map_pure, pure_converges],
--   le_converges := λ f g hle x hconv, le_converges (map_mono hle) hconv }

-- lemma continuous.induced_le (m : α → β) [p : convergence_space α]
--   [convergence_space β] (hm : continuous m) :
--   p ≤ convergence_space.induced m :=
-- λ f x hconv, hm hconv

-- lemma continuous_induced_dom {m : α → β} {q : convergence_space β} :
--   continuous_ (@convergence_space.induced α β m q) q m :=
-- λ x f hconv, hconv

-- lemma continuous_induced_rng {m₁ : α → β} {m₂ : β → γ}
--   [p : convergence_space α] [q : convergence_space β] [r : convergence_space γ]
--   (hcont : continuous (m₂ ∘ m₁)) : continuous_ p (convergence_space.induced m₂) m₁ :=
-- λ x f hconv, hcont hconv

-- /-!
-- ### Coinduced convergence structure
-- -/

-- /-- Given `m : α → β`, where `α` is a convergence space, the coinduced convergence
--   structure on `β` is the least (finest) convergence structure making `m` continuous. -/
-- def convergence_space.coinduced (m : α → β) [convergence_space α] :
--   convergence_space β :=
-- { converges := λ g y, (g ≤ pure y) ∨
--     ∃ f x, (g ≤ map m f) ∧ (m x = y) ∧ (converges f x),
--   pure_converges := λ b, or.inl (le_refl (pure b)),
--   le_converges := λ g₁ g₂ hle y hconv,
--     or.elim hconv
--       (λ hle' : g₂ ≤ pure y, or.inl (le_trans hle hle'))
--       (λ ⟨f, x, hle', heq, hconv'⟩,
--         or.inr ⟨f, x, le_trans hle hle', heq, hconv'⟩) }

-- lemma continuous.le_coinduced (m : α → β) [convergence_space α]
--   [q : convergence_space β] (hm : continuous m) :
--   convergence_space.coinduced m ≤ q :=
-- λ g y hconv, hconv.elim
--   (λ hle, le_converges_ q hle (pure_converges_ q y))
--   (λ ⟨f, x, h₀, h₁, h₂⟩, by { rw ← h₁, exact le_converges_ q h₀ (hm h₂) })

-- lemma coinduced_id [p : convergence_space α] : convergence_space.coinduced id = p :=
-- begin
--   ext f x, split,
--   { assume hconv, cases hconv,
--     { exact le_converges_ p hconv (pure_converges_ p x) },
--     { obtain ⟨g, y, hle, heq, hconv'⟩ := hconv,
--       simp at *, rw ← heq, exact le_converges_ p hle hconv' }},
--   { assume hconv : converges_ p f x,
--     exact or.inr ⟨f, x, le_refl f, rfl, hconv⟩, }
-- end

-- lemma continuous_iff_coinduced_le {m : α → β}
--   [convergence_space α] [q : convergence_space β]  :
--   continuous m ↔ convergence_space.coinduced m ≤ q :=
-- begin
--   split,
--   { assume hcont g y hconv, cases hconv,
--     { exact le_converges_ q hconv (pure_converges_ q y) },
--     { obtain ⟨f, x, hle, heq, hconv'⟩ := hconv,
--       rw ← heq, exact le_converges_ q hle (hcont hconv') }},
--   { assume hle x f hconv, exact hle (or.inr ⟨f, x, le_refl (map m f), rfl, hconv⟩) }
-- end

-- lemma coinduced_compose [convergence_space α]
--   {m₁ : α → β} {m₂ : β → γ} :
--   @convergence_space.coinduced _ _ m₂ (convergence_space.coinduced m₁) =
--   convergence_space.coinduced (m₂ ∘ m₁) :=
-- begin
--   ext h z, split,
--   { assume hconv, cases hconv,
--     { exact or.inl hconv },
--     { obtain ⟨g, y, hg₁, hg₂, hg₃⟩ := hconv,
--       cases hg₃,
--       { have : h ≤ pure z, from calc
--             h ≤ map m₂ g : hg₁
--             ... ≤ map m₂ (pure y) : map_mono hg₃
--             ... = pure (m₂ y) : by rw filter.map_pure
--             ... = pure z : by rw hg₂,
--         exact or.inl this },
--       { obtain ⟨f, x, hf₁, hf₂, hf₃⟩ := hg₃,
--           have hle : h ≤ map (m₂ ∘ m₁) f, from calc
--             h ≤ map m₂ (map m₁ f) : le_trans hg₁ (map_mono hf₁)
--             ... = map (m₂ ∘ m₁) f : by rw filter.map_map,
--           have heq : (m₂ ∘ m₁) x = z, by simp [hf₂, hg₂],
--           exact or.inr ⟨f, x, hle, heq, hf₃⟩ }}},
--   { assume hconv, cases hconv,
--     { exact or.inl hconv },
--     { obtain ⟨f, x, hf₁, hf₂, hf₃⟩ := hconv,
--       let g : filter β := map m₁ f,
--       let y : β := m₁ x,
--       let hg₁ : h ≤ map m₂ g := by tauto,
--       let hg₂ : m₂ y = z := by tauto,
--       let hg₃ : converges_ (convergence_space.coinduced m₁) g y :=
--         or.inr ⟨f, x, le_refl (map m₁ f), rfl, hf₃⟩,
--       exact or.inr ⟨g, y, hg₁, hg₂, hg₃⟩ }}
-- end

-- lemma continuous_coinduced_rng [p : convergence_space α]
--   {m : α → β} : continuous_ p (convergence_space.coinduced m) m :=
-- λ x f hconv, or.inr ⟨f, x, le_refl (map m f), rfl, hconv⟩

-- /-!
-- ### More definitions
-- -/

-- section

-- variables [convergence_space α]

-- /-- The set of all limits of a filter. -/
-- def lim (f : filter α) : set α := { x | converges f x }

-- /-- A filter is convergent if it has a limit. -/
-- def convergent (f : filter α) : Prop := ∃ x, converges f x

-- /-- A point `x` adheres to a filter `f` if there is some non-trivial filter
--   smaller than `f` that converges to `x`. -/
-- def adheres (f : filter α) (x : α) : Prop :=
-- ∃ (g : filter α) [ne_bot g], g ≤ f ∧ converges g x

-- lemma adheres.exists_ultrafilter (f : filter α) (x : α) :
--   adheres f x ↔ ∃ (g : ultrafilter α), ↑g ≤ f ∧ converges ↑g x :=
-- begin
--   split,
--   { rintros ⟨g, hnb, hle, hconv⟩,
--     haveI : g.ne_bot := hnb,
--     obtain ⟨g', hle'⟩ := filter.exists_ultrafilter_le g,
--     exact ⟨g', le_trans hle' hle, le_converges hle' hconv⟩ },
--   { rintros ⟨g, hle, hconv⟩,
--     exact ⟨↑g, g.ne_bot, hle, hconv⟩ }
-- end

-- /-- The set of all points that adhere to a filter. -/
-- def adh (f : filter α) : set α := { x | adheres f x }

-- /-- The interior of a set `s` consists of those points `x ∈ s` with the property
--   that every non-trivial filter converging to `x` contains `s`.  -/
-- def interior (s : set α) : set α :=
-- { x ∈ s | ∀ (f : filter α) [ne_bot f], converges f x → s ∈ f }

-- /-- A set is open if it equals its interior. -/
-- def is_open (s : set α) : Prop := s = interior s

-- /-- The closure of a set `s` consists of all those points that are the limits of
--   the non-trivial filters containing `s`. -/
-- def closure (s : set α) : set α :=
-- { x | ∃ (f : filter α) [ne_bot f], converges f x ∧ s ∈ f }

-- /-- A set is closed if it equals its closure. -/
-- def is_closed (s : set α) : Prop := s = closure s

-- /-- A set `s` is dense if every point in the space belongs to `closure s`. -/
-- def is_dense (s : set α) : Prop := ∀ x, x ∈ closure s

-- /-- `cl f` is the filter generated by the closure of all the sets of `f`. -/
-- def cl (f : filter α) : filter α := filter.generate (closure '' f.sets)

-- /-- A set `s` is strictly dense if `converges f x` implies there is a filter `g`
--   that contains `s`, converges to `x` and satisfies `f ≤ cl g`. -/
-- def is_strictly_dense (s : set α) : Prop :=
-- ∀ {x : α} {f : filter α}, converges f x → ∃ g, (s ∈ g) ∧ (converges g x) ∧ (f ≤ cl g)

-- /-- The neighborhood filter of `x` is the infimum of all filters converging to `x`. -/
-- def nhds (x : α) : filter α := ⨅ f ∈ { g | converges g x }, f

-- end

-- /-!
-- ### Product spaces
-- -/

-- section

-- variables [convergence_space α] [convergence_space β]

-- instance : convergence_space (α × β) :=
-- convergence_space.induced fst ⊓ convergence_space.induced snd

-- lemma continuous_fst : continuous (@fst α β) :=
-- continuous_inf_dom_left continuous_induced_dom

-- lemma continuous_snd : continuous (@snd α β) :=
-- continuous_inf_dom_right continuous_induced_dom

-- lemma prod.converges {f : filter α} {g : filter β} {x : α} {y : β}
--   (hf : converges f x) (hg : converges g y) : converges (f ×ᶠ g) (x, y) :=
-- and.intro
--   (le_converges tendsto_fst hf : converges (map fst (f ×ᶠ g)) x)
--   (le_converges tendsto_snd hg : converges (map snd (f ×ᶠ g)) y)

-- lemma continuous.prod_mk [convergence_space α] [convergence_space β₁]
--   [convergence_space β₂] {m₁ : α → β₁} {m₂ : α → β₂}
--   (hcont₁ : continuous m₁) (hcont₂ : continuous m₂) : continuous (λx, (m₁ x, m₂ x)) :=
-- continuous_inf_rng (continuous_induced_rng hcont₁) (continuous_induced_rng hcont₂)

-- lemma continuous.prod.mk [convergence_space α] [convergence_space β] (x : α) :
--   continuous (prod.mk x : β → α × β) :=
-- continuous_const.prod_mk continuous_id'

-- def continuous2 [convergence_space α] [convergence_space β] [convergence_space γ]
--   (m : α → β → γ) : Prop :=
-- ∀ ⦃x y f g⦄, converges f x → converges g y → converges (map₂ m f g) (m x y)

-- lemma continuous2_continuous_iff [convergence_space α] [convergence_space β] [convergence_space γ]
--   {m : α → β → γ} : continuous2 m ↔ continuous (uncurry m) :=
-- begin
--   split,
--   { rintros hcont2 ⟨x, y⟩ h ⟨hconv₁, hconv₂⟩,
--     have : converges (map₂ m (map fst h) (map snd h)) (m x y),
--       from hcont2 hconv₁ hconv₂,
--     rw ← map_prod_eq_map₂ at this,
--     exact le_converges (map_mono le_prod_map_fst_snd) this },
--   { intros hcont x y f g hf hg,
--     rw ← map_prod_eq_map₂,
--     exact hcont (prod.converges hf hg) },
-- end

-- end

-- /-!
-- ### Other convergence spaces constructions
-- -/

-- instance {p : α → Prop} [convergence_space α] : convergence_space (subtype p) :=
-- convergence_space.induced (coe : subtype p → α)

-- instance {r : α → α → Prop} [convergence_space α] : convergence_space (quot r) :=
-- convergence_space.coinduced (quot.mk r)

-- instance [convergence_space α] : convergence_space (option α) :=
-- convergence_space.coinduced some

-- instance [convergence_space α] : convergence_space (part α) :=
-- convergence_space.coinduced part.some

-- /-!
-- ### The convergence space C(α,β)
-- -/

-- /-- Bundled continuous maps. -/
-- structure continuous_map (α β : Type*)
--   [convergence_space α] [convergence_space β] :=
-- (to_fun : α → β)
-- (continuous_to_fun : continuous to_fun)

-- notation `C(` α `, ` β `)` := continuous_map α β

-- namespace continuous_map

-- variables [convergence_space α] [convergence_space β]

-- instance : has_coe_to_fun (C(α, β)) (λ _, α → β) := ⟨continuous_map.to_fun⟩

-- @[simp] lemma to_fun_eq_coe {m : C(α, β)} : m.to_fun = (m : α → β) := rfl

-- def eval : C(α, β) × α → β := λ ⟨m, x⟩, m x

-- @[simp] lemma eval_comp_prod {m : C(α, β)} : eval ∘ prod.mk m = m :=
-- by { apply funext, intro, apply comp_apply }

-- protected lemma continuous (m : C(α, β)) : continuous m := m.continuous_to_fun

-- lemma map_eval_eq {m : C(α, β)} {f : filter α} :
--   map continuous_map.eval (pure m ×ᶠ f) = map m f :=
-- by simp [pure_prod, filter.map_map, eval_comp_prod]

-- end continuous_map

-- instance [convergence_space α] [convergence_space β] :
--   convergence_space C(α, β) :=
-- { converges := λ f m, ∀ (x : α) (g : filter α),
--     converges g x → converges (map continuous_map.eval (f ×ᶠ g)) (m x),
--   pure_converges := λ m x g hconv,
--     by { rw continuous_map.map_eval_eq, exact m.continuous_to_fun hconv},
--   le_converges := λ f g hle m hconv x f' hconv',
--     le_converges (map_mono (prod_mono hle (le_refl f'))) (hconv x f' hconv') }

-- /-!
-- ### Separation axioms
-- -/

-- /-- In a T₀ space, the equality of two points can be determined by checking
--   if the corresponding pure filters converge to the other point. -/
-- class t0_space (α : Type*) [convergence_space α] : Prop :=
-- (t0_prop : ∀ x y : α, converges (pure x) y ∧ converges (pure y) x ↔ x = y)

-- abbreviation kolmogorov_space := t0_space

-- /-- In an R₀ space, if `pure x` converges to `y`, then `x` and `y` have the
--   same convergent filters. -/
-- class r0_space (α : Type*) [convergence_space α] : Prop :=
-- (r0_prop : ∀ x y, converges (pure x) y →
-- ∀ (f : filter α), converges f x ↔ converges f y)

-- /-- In a T₁ space, pure filters have exactly one limit. -/
-- class t1_space (α : Type*) [convergence_space α] : Prop :=
-- (t1_prop : ∀ x y : α, converges (pure x) y → x = y)

-- abbreviation frechet_space := t1_space

-- /-- In an R₁ space, if `x` and `y` are the limits of a non-trivial filter, then
--   they share the same convergent filters. -/
-- class r1_space (α : Type*) [convergence_space α] : Prop :=
-- (r1_prop : ∀ x y, ∃ (f : filter α) [ne_bot f], converges f x ∧ converges f y →
--   ∀ (g : filter α), converges g x ↔ converges g y)

-- /-- In a T₂ space, every non-trivial filter has exactly one limit. -/
-- class t2_space (α : Type*) [convergence_space α] : Prop :=
-- (t2_prop : ∀ x y, ∀ (f : filter α) [ne_bot f],
--   converges f x ∧ converges f y → x = y)

-- abbreviation hausdorff_space := t2_space

-- /-- In an R₂ space, if a filter converges, then so does its closure. -/
-- class r2_space (α : Type*) [convergence_space α] : Prop :=
-- (r2_prop : ∀ (x : α) (f : filter α), converges f x → converges (cl f) x)

-- abbreviation regular_space := r2_space

-- /-- A T₃ space is a T₀ & R₂ space. -/
-- class t3_space (α : Type*) [convergence_space α] extends
--   t0_space α, r2_space α.


-- /-!
-- ### Compact sets/spaces
-- -/

-- def is_compact [convergence_space α] (s : set α) :=
-- ∀ ⦃f : ultrafilter α⦄, s ∈ f → ∃ x ∈ s, converges f.to_filter x

-- class compact_space (α : Type*) [convergence_space α] : Prop :=
-- (compact_prop : is_compact (univ : set α))

-- theorem is_compact.image {m : α → β} {s : set α}
--   [convergence_space α] [convergence_space β]
--   (hcom : is_compact s) (hcont : continuous m) : is_compact (m '' s) :=
-- begin
--   assume g hmem,
--   rw ← ultrafilter.of_comap_inf_principal_eq_of_map hmem,
--   obtain ⟨x, hx, hconv⟩ := hcom (ultrafilter.of_comap_inf_principal_mem hmem),
--   exact ⟨m x, mem_image_of_mem m hx, hcont hconv⟩,
-- end

-- /-!
-- ### Locally compact sets/spaces
-- -/

-- /-- A set `s` is locally compact if every convergent filter containing `s` contains
--   a compact set. -/
-- def is_locally_compact [convergence_space α] (s : set α) :=
-- ∀ ⦃f : filter α⦄, s ∈ f → (∃ x : α, converges f x) → ∃ t ∈ f, is_compact t

-- class locally_compact_space (α : Type*) [convergence_space α] : Prop :=
-- (locally_compact_prop : is_locally_compact (univ : set α))

-- /-!
-- ### Quotient maps
-- -/

-- /-- A surjective map `m : α → β` where β has the coinduced convergence is
--   called a quotient map. -/
-- def quotient_map [convergence_space α] [q : convergence_space β]
-- (m : α → β) : Prop := surjective m ∧ q = convergence_space.coinduced m

-- lemma quotient_map.converges [convergence_space α] [q : convergence_space β]
--   {m : α → β} (hquot : quotient_map m) (g : filter β) (y : β) :
--   converges g y ↔ ∃ f x, (g ≤ map m f) ∧ (m x = y) ∧ (converges f x) :=
-- begin
--   split,
--   { assume hconv, rw hquot.2 at hconv, cases hconv,
--     { obtain ⟨x, heq⟩ := hquot.1 y,
--       rw [← heq, ← filter.map_pure] at hconv,
--       exact ⟨pure x, x, hconv, heq, pure_converges x⟩ },
--     { exact hconv }},
--   { rintro hexists, rw hquot.2, exact or.inr hexists }
-- end

-- lemma quotient_map_iff [convergence_space α] [q : convergence_space β]
--   {m : α → β} : quotient_map m ↔ surjective m ∧ ∀ g y, converges g y ↔
--   ∃ f x, (g ≤ map m f) ∧ (m x = y) ∧ (converges f x) :=
-- begin
--   split,
--   { assume hlhs, exact and.intro hlhs.1 (λ g y, quotient_map.converges hlhs g y) },
--   { assume hrhs, refine and.intro hrhs.1 _, ext g y,
--     change converges_ q g y ↔ g ≤ pure y ∨
--       ∃ (f : filter α) (x : α), g ≤ map m f ∧ m x = y ∧ converges f x,
--     refine iff.intro (λ hconv, or.inr ((hrhs.2 g y).mp hconv)) _,
--     intro hconv,
--     exact hconv.elim
--       (λ hle, le_converges_ q hle (pure_converges_ q y))
--       (λ hexists, ((hrhs.2 g y).mpr hexists)) }
-- end

-- lemma quotient_map.continuous_iff [convergence_space α] [convergence_space β]
--   [convergence_space γ] {m₁ : α → β} {m₂ : β → γ} (hquot : quotient_map m₁) :
--   continuous m₂ ↔ continuous (m₂ ∘ m₁) :=
-- by rw [continuous_iff_coinduced_le, continuous_iff_coinduced_le, hquot.right, coinduced_compose]

-- lemma quotient_map.id [convergence_space α] : quotient_map (@id α) :=
-- ⟨assume a, ⟨a, rfl⟩, coinduced_id.symm⟩

-- lemma quotient_map.prod_map
--   [convergence_space α₁] [convergence_space β₁]
--   {m₁ : α₁ → β₁} (hquot₁ : quotient_map m₁)
--   [convergence_space α₂] [convergence_space β₂]
--   {m₂ : α₂ → β₂} (hquot₂ : quotient_map m₂) :
--   quotient_map (prod.map m₁ m₂) :=
-- begin
--   rw quotient_map_iff at *,
--   refine and.intro (surjective.prod_map hquot₁.1 hquot₂.1) _,
--   rintros (g : filter (β₁ × β₂)) (⟨y₁, y₂⟩ : β₁ × β₂),
--   split,
--   { assume hconv,
--     let g₁ := map fst g,
--     let g₂ := map snd g,
--     have hg₁ : converges g₁ y₁, from continuous_fst hconv,
--     have hg₂ : converges g₂ y₂, from continuous_snd hconv,
--     obtain ⟨f₁, x₁, hle₁, heq₁, hf₁⟩ := (hquot₁.2 g₁ y₁).mp hg₁,
--     obtain ⟨f₂, x₂, hle₂, heq₂, hf₂⟩ := (hquot₂.2 g₂ y₂).mp hg₂,
--     let f := f₁ ×ᶠ f₂,
--     let x := (x₁, x₂),
--     have hle : g ≤ map (prod.map m₁ m₂) f, from calc
--       g ≤ map fst g ×ᶠ map snd g : le_prod_map_fst_snd
--       ... = g₁ ×ᶠ g₂ : by tauto
--       ... ≤ map m₁ f₁ ×ᶠ map m₂ f₂ : prod_mono hle₁ hle₂
--       ... = map (prod.map m₁ m₂) (f₁ ×ᶠ f₂) : prod_map_map_eq' m₁ m₂ f₁ f₂,
--     have heq : prod.map m₁ m₂ x = (y₁, y₂),
--       by { rw [prod.map_mk m₁ m₂ x₁ x₂, heq₁, heq₂] },
--     have hconv' : converges f x, from prod.converges hf₁ hf₂,
--     exact ⟨f, x, hle, heq, hconv'⟩ },
--   { rintro ⟨f, x, hle, heq, hf⟩,
--     let f₁ := map fst f,
--     let f₂ := map snd f,
--     simp [prod.map_mk m₁ m₂ x.1 x.2] at heq,
--     let g₁ := map fst g,
--     let g₂ := map snd g,
--     have hle₁ : g₁ ≤ map m₁ f₁, from calc
--       g₁ ≤ map fst (map (prod.map m₁ m₂) f) : map_mono hle
--       ... = map (fst ∘ prod.map m₁ m₂) f : map_map
--       ... = map (m₁ ∘ fst) f : by rw (prod.map_fst' m₁ m₂)
--       ... = map m₁ f₁ : by simp,
--     have hle₂ : g₂ ≤ map m₂ f₂, from calc
--       g₂ ≤ map snd (map (prod.map m₁ m₂) f) : map_mono hle
--       ... = map (snd ∘ prod.map m₁ m₂) f : map_map
--       ... = map (m₂ ∘ snd) f : by rw (prod.map_snd' m₁ m₂)
--       ... = map m₂ f₂ : by simp,
--     have hg₁ : converges g₁ y₁,
--       from (hquot₁.2 g₁ y₁).mpr ⟨f₁, x.1, hle₁, heq.1, hf.1⟩,
--     have hg₂ : converges g₂ y₂,
--       from (hquot₂.2 g₂ y₂).mpr ⟨f₂, x.2, hle₂, heq.2, hf.2⟩,
--     exact ⟨hg₁, hg₂⟩ }
-- end

-- lemma quotient_map_quot_mk [convergence_space α] {r : α → α → Prop} :
--   quotient_map (quot.mk r) :=
-- ⟨quot.exists_rep, rfl⟩

-- lemma continuous_quot_mk [convergence_space α]
--   {r : α → α → Prop} : continuous (quot.mk r) :=
-- continuous_coinduced_rng

-- /-!
-- ### Category Conv of convergence spaces
-- -/

-- universe u

-- def Conv : Type (u+1) := bundled convergence_space
