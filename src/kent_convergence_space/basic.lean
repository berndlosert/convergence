import tactic
import order.filter.partial
import algebra.support
import convergence_space.basic

noncomputable theory
open set filter classical convergence_space
open_locale classical filter

variables {α β : Type*}

/-!
### Definition
-/

@[ext] class kent_convergence_space (α : Type*) extends convergence_space α :=
(kent_converges : ∀ {f x}, converges f x → converges (f ⊔ pure x) x)

open kent_convergence_space

namespace kent_convergence_space

instance : has_coe (kent_convergence_space α) (convergence_space α) := 
{ coe := λ p, p.to_convergence_space }

@[simp, norm_cast] theorem coe_inj {p q : kent_convergence_space α} :
  (↑p : convergence_space α)= ↑q ↔ p = q :=
by { rw kent_convergence_space.ext_iff, tauto }

lemma coe_injective : function.injective (coe : kent_convergence_space α → convergence_space α) :=
λ s t, coe_inj.1

end kent_convergence_space

@[simp] def kent_converges_ {α : Type*} (p : kent_convergence_space α)
  {f : filter α} {x : α} (h : converges_ ↑p f x) : converges_ ↑p (f ⊔ pure x) x
:= @kent_converges _ p _ _ h

/-!
### Ordering
-/

/-- The ordering is the one inherited from convergence spaces. -/

instance : has_le (kent_convergence_space α) := ⟨λ p q, ↑p ≤ (↑q : convergence_space α)⟩

instance : partial_order (kent_convergence_space α) := 
  partial_order.lift coe kent_convergence_space.coe_injective

/-!
### Lattice of Kent convergence structures
-/

/-- Just like convergence structures, Kent convergence structures also 
  form a complete lattice. The infimum/supremum are formed in the same
  manner as convergence spaces. -/

instance : has_bot (kent_convergence_space α) :=
{ bot := 
  { kent_converges :=
    begin
      intros f x hconv,
      unfold converges at *,
      have : f ⊔ pure x ≤ pure x, from calc
        f ⊔ pure x ≤ pure x ⊔ pure x : sup_le_sup_right hconv (pure x)
        ... = pure x : sup_idem,
      assumption
    end,
    ..convergence_space.has_bot.bot }}

instance : has_top (kent_convergence_space α) :=
{ top := { kent_converges := by tauto, ..convergence_space.has_top.top }}

instance : has_inf (kent_convergence_space α) := 
{ inf := λ p q, let super : convergence_space α := ↑p ⊓ ↑q in 
  { converges := converges_ super,
    pure_converges := pure_converges_ super,
    le_converges := le_converges_ super,
    kent_converges := λ f x hconv, 
    ⟨kent_converges_ p hconv.1, kent_converges_ q hconv.2⟩ }}

instance : has_sup (kent_convergence_space α) :=
{ sup := λ p q, let super : convergence_space α := ↑p ⊔ ↑q in 
  { converges := converges_ super,
    pure_converges := pure_converges_ super,
    le_converges := le_converges_ super,
    kent_converges :=
    begin
      intros f x hconv,
      cases hconv,
      { exact or.inl (kent_converges_ p hconv) },
      { exact or.inr (kent_converges_ q hconv) }
    end }}

instance : has_Inf (kent_convergence_space α) :=
{ Inf := λ ps, let super : convergence_space α := Inf (coe '' ps) in
  { converges := converges_ super,
    pure_converges := pure_converges_ super,
    le_converges := le_converges_ super,
    kent_converges :=
    begin
      intros f x hconv p hp,
      obtain ⟨q, hq, heq⟩ := mem_image_iff_bex.mp hp,
      rw ← heq at *,
      exact kent_converges_ q (hconv hp)
    end }}

instance : has_Sup (kent_convergence_space α) :=
{ Sup := λ ps, let super : convergence_space α := Sup (coe '' ps) in
  { converges := converges_ super,
    pure_converges := pure_converges_ super,
    le_converges := le_converges_ super,
    kent_converges := 
    begin
      intros f x hconv,
      cases hconv,
      { rw sup_of_le_right hconv,
        exact pure_converges_ super x },
      { obtain ⟨p, hp, hconv'⟩ := hconv,
        refine or.inr ⟨p, hp, _⟩,
        obtain ⟨q, hq, heq⟩ := mem_image_iff_bex.mp hp,
        rw ← heq at *,
        exact kent_converges_ q hconv' }
    end }}

instance : semilattice_inf (kent_convergence_space α) :=
by { refine function.injective.semilattice_inf coe kent_convergence_space.coe_injective _, tauto }

instance : semilattice_sup (kent_convergence_space α) :=
by { refine function.injective.semilattice_sup coe kent_convergence_space.coe_injective _, tauto }

lemma kent_convergence_space.coe_Inf (ps : set (kent_convergence_space α)) : 
  (↑(Inf ps) : convergence_space α) = Inf (coe '' ps) :=
by { ext, tauto }

lemma kent_convergence_space.coe_Sup (ps : set (kent_convergence_space α)) : 
  (↑(Sup ps) : convergence_space α) = Sup (coe '' ps) :=
by { ext, tauto }

instance : complete_semilattice_Inf (kent_convergence_space α) :=
{ Inf_le :=
  begin
    intros ps p hmem f x hconv,
    rw kent_convergence_space.coe_Inf at hconv,
    exact hconv (mem_image_of_mem coe hmem),
  end,
  le_Inf :=
  begin
    intros ps q hle, 
    change ↑q ≤ ↑(Inf ps),
    rw kent_convergence_space.coe_Inf,
    intros f x hconv p hp,
    obtain ⟨r, hr, heq⟩ := mem_image_iff_bex.mp hp,
    rw ← heq,
    exact hle r hr hconv,
  end,
  ..kent_convergence_space.partial_order,
  ..kent_convergence_space.has_Inf }

instance : complete_semilattice_Sup (kent_convergence_space α) :=
{ le_Sup :=
  begin
    intros ps p hmem f x hconv,
    rw kent_convergence_space.coe_Sup,
    unfold Sup, simp,
    exact or.inr ⟨p, hmem, hconv⟩,
  end,
  Sup_le := 
  begin
    intros qs p hle f x hconv,
    cases hconv,
    { exact le_converges_ ↑p hconv (pure_converges_ ↑p x) },
    { obtain ⟨q, hq, hconv'⟩ := hconv,
      obtain ⟨r, hr, heq⟩ := mem_image_iff_bex.mp hq,
      rw ← heq at hconv',
      exact (hle r hr) hconv',
      }
  end,
  ..kent_convergence_space.partial_order,
  ..kent_convergence_space.has_Sup }

instance : complete_lattice (kent_convergence_space α) :=
complete_lattice_of_complete_semilattice_Inf (kent_convergence_space α)

/-!
### Induced Kent convergence space
-/

def kent_convergence_space.induced (m : α → β) [kent_convergence_space β] : kent_convergence_space α :=
let ind := convergence_space.induced m in 
{ kent_converges :=
  begin
    assume f : filter α,
    assume x : α,
    assume h : converges (map m f) (m x),
    let f₁ := map m f,
    let f₂ := f ⊔ pure x,
    let y := m x,
    show converges (map m f₂) y, 
    begin
      rw [filter.map_sup, filter.map_pure],
      simp [kent_converges h],
    end,
  end,
  ..ind }

/-!
### Coinduced Kent convergence space
-/

def kent_convergence_space.coinduced (m : α → β) [kent_convergence_space α] : kent_convergence_space β :=
let coind := convergence_space.coinduced m in 
{ kent_converges := 
  begin
    assume g : filter β,
    assume y  : β,
    assume hconv : converges_ coind g y,
    cases hconv,
      case or.inl
      begin
        have : g ⊔ pure y = pure y, from calc
          g ⊔ pure y  = pure y ⊔ g : sup_comm
          ... = pure y : by rw sup_of_le_left hconv,
        have : converges_ coind (pure y) y, from pure_converges_ coind y,
        show converges_ coind (g ⊔ pure y) y, 
        begin
          rw (by assumption : g ⊔ pure y = pure y),
          assumption,
        end,
      end,
      case or.inr : hex
      begin
        obtain ⟨f, x, hle, heq, hconv⟩ := hex,
        let f' := f ⊔ pure x,
        have hle' : g ⊔ pure y ≤ map m f', from calc
          g ⊔ pure y ≤ map m f ⊔ pure y : sup_le_sup_right hle (pure y)
          ... = map m f ⊔ pure (m x) : by rw heq
          ... = map m f ⊔ map m (pure x) : by rw filter.map_pure
          ... = map m (f ⊔ pure x) : map_sup,
        have hconv' : converges f' x, 
        begin
          apply kent_converges,
          assumption
        end,
        exact or.inr ⟨f', x, hle', heq, hconv'⟩,
      end,
  end,
  ..coind }

/-!
### Constructions
-/

def kent_modification (p : convergence_space α) : kent_convergence_space α :=
  Inf { q : kent_convergence_space α | p ≤ q }

instance {p : α → Prop} [kent_convergence_space α] : kent_convergence_space (subtype p) :=
kent_convergence_space.induced (coe : subtype p → α)

instance {r : α → α → Prop} [kent_convergence_space α] : kent_convergence_space (quot r) :=
kent_convergence_space.coinduced (quot.mk r)

instance [kent_convergence_space α] [kent_convergence_space β] : kent_convergence_space (α × β) :=
kent_convergence_space.induced prod.fst ⊓ kent_convergence_space.induced prod.snd
