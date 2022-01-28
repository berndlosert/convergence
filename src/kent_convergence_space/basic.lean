import tactic
import order.filter.partial
import algebra.support
import convergence_space.basic

noncomputable theory
open set filter classical convergence_space
open_locale classical filter

variables {X Y : Type*}

-------------------------------------------------------------------------------
-- Definition
-------------------------------------------------------------------------------

@[ext] class kent_convergence_space (X : Type*) extends convergence_space X :=
(kent_converges : ∀ {x} {ℱ}, converges ℱ x → converges (ℱ ⊔ pure x) x)

open kent_convergence_space

def kent_converges_ {X : Type*} (p : kent_convergence_space X)
{x : X} {ℱ : filter X} (h : converges_ p.to_convergence_space ℱ x)
: converges_ p.to_convergence_space (ℱ ⊔ pure x) x
:= @kent_converges _ p _ _ h

instance : has_coe (kent_convergence_space X) (convergence_space X) := {
  coe := λ p, p.to_convergence_space,
}

-------------------------------------------------------------------------------
-- Supremum and infimum of Kent convergence spaces
-------------------------------------------------------------------------------

instance : has_inf (kent_convergence_space X) := {
  inf := λ p q, let super : convergence_space X := ↑p ⊓ ↑q in {
    converges := converges_ super,
    pure_converges := pure_converges_ super,
    le_converges := le_converges_ super,
    kent_converges := begin
      assume x : X,
      assume ℱ : filter X,
      assume h : converges_ super ℱ x,
      cases h,
        case or.inl : hp begin
          exact or.inl (kent_converges_ p hp),
        end,
        case or.inr : hq begin
          exact or.inr (kent_converges_ q hq),
        end,
    end,
  }
}

-------------------------------------------------------------------------------
-- Induced/coinduced Kent convergence space
-------------------------------------------------------------------------------

def kent_convergence_space.induced (f : X → Y) [kent_convergence_space Y] : kent_convergence_space X :=
let ind := convergence_space.induced f in {
  kent_converges :=
    begin
      assume x : X,
      assume ℱ : filter X,
      assume h : converges (map f ℱ) (f x),
      let ℱ₁ := map f ℱ,
      let ℱ₂ := ℱ ⊔ pure x,
      let y := f x,
      show converges (map f ℱ₂) y, begin
        rw [filter.map_sup, filter.map_pure],
        simp [kent_converges h],
      end,
    end,
  ..ind
}

def kent_convergence_space.coinduced (f : X → Y) [kent_convergence_space X] : kent_convergence_space Y :=
let coind := convergence_space.coinduced f in {
  kent_converges := begin
    assume y  : Y,
    assume 𝒢 : filter Y,
    assume h : converges_ coind 𝒢 y,
    cases h,
      case pure_case begin
        have : 𝒢 ⊔ pure y = pure y, from calc
          𝒢 ⊔ pure y  = pure y ⊔ 𝒢 : sup_comm
          ... = pure y : by rw sup_of_le_left h,
        have : converges_ coind (pure y) y, from pure_converges_ coind y,
        show converges_ coind (𝒢 ⊔ pure y) y, begin
          rw (by assumption : 𝒢 ⊔ pure y = pure y),
          assumption,
        end,
      end,
      case other_case : ℱ x _ _ _ begin
        let ℱ' := ℱ ⊔ pure x,
        have : 𝒢 ⊔ pure y ≤ map f ℱ', from calc
          𝒢 ⊔ pure y ≤ map f ℱ ⊔ pure y : sup_le_sup_right (by assumption : 𝒢 ≤ map f ℱ) (pure y)
          ... = map f ℱ ⊔ pure (f x) : by rw (by assumption : y = f x)
          ... = map f ℱ ⊔ map f (pure x) : by rw filter.map_pure
          ... = map f (ℱ ⊔ pure x) : map_sup,
        have : converges ℱ' x, begin
          apply kent_converges,
          assumption
        end,
        apply coinduced_converges.other_case ℱ' x
          (by assumption : 𝒢 ⊔ pure y ≤ map f ℱ')
          (by assumption : y = f x)
          (by assumption : converges ℱ' x)
      end,
  end,
  ..coind
}

-------------------------------------------------------------------------------
-- Constructions
-------------------------------------------------------------------------------

instance {p : X → Prop} [kent_convergence_space X] : kent_convergence_space (subtype p) :=
kent_convergence_space.induced (coe : subtype p → X)

instance {r : X → X → Prop} [kent_convergence_space X] : kent_convergence_space (quot r) :=
kent_convergence_space.coinduced (quot.mk r)

instance [kent_convergence_space X] [kent_convergence_space Y] : kent_convergence_space (X × Y) :=
kent_convergence_space.induced prod.fst ⊓ kent_convergence_space.induced prod.snd
