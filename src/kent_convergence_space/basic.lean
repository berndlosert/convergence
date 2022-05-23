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

@[simp] def kent_converges_ {α : Type*} (p : kent_convergence_space α)
  {f : filter α} {x : α} (h : converges_ p.to_convergence_space f x) : 
  converges_ p.to_convergence_space (f ⊔ pure x) x
:= @kent_converges _ p _ _ h

instance : has_coe (kent_convergence_space α) (convergence_space α) := 
{ coe := λ p, p.to_convergence_space }

/-!
### Parital ordering
-/

instance : has_le (kent_convergence_space α) :=
⟨λ p q, p.to_convergence_space ≤ q.to_convergence_space⟩

/-!
### Top/bottom
-/

instance : has_top (kent_convergence_space α) :=
{ top := { kent_converges := by tauto, ..convergence_space.has_top.top }}

instance : has_bot (kent_convergence_space α) :=
let indiscrete : kent_convergence_space α :=
{ kent_converges :=
  begin
    intros f x hconv,
    unfold converges at *,
    have : f ⊔ pure x ≤ pure x, from calc
      f ⊔ pure x ≤ pure x ⊔ pure x : sup_le_sup_right hconv (pure x)
      ... = pure x : sup_idem,
    assumption
  end,
  ..convergence_space.has_bot.bot }
in { bot := indiscrete }

/-!
### Infimum and supremum
-/

instance : has_inf (kent_convergence_space α) := 
{ inf := λ p q, let super : convergence_space α := ↑p ⊓ ↑q in 
  { converges := converges_ super,
    pure_converges := pure_converges_ super,
    le_converges := le_converges_ super,
    kent_converges := 
    begin
      assume f : filter α,
      assume x : α,
      assume hconv : converges_ super f x,
      obtain ⟨hp, hq⟩ := hconv,
      exact ⟨kent_converges_ p hp, kent_converges_ q hq⟩,
    end }}

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

instance {p : α → Prop} [kent_convergence_space α] : kent_convergence_space (subtype p) :=
kent_convergence_space.induced (coe : subtype p → α)

instance {r : α → α → Prop} [kent_convergence_space α] : kent_convergence_space (quot r) :=
kent_convergence_space.coinduced (quot.mk r)

instance [kent_convergence_space α] [kent_convergence_space β] : kent_convergence_space (α × β) :=
kent_convergence_space.induced prod.fst ⊓ kent_convergence_space.induced prod.snd
