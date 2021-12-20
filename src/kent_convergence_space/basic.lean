import tactic
import order.filter.partial
import algebra.support
import convergence_space.basic

noncomputable theory
open set filter classical
open_locale classical filter
open has_sup has_inf has_mem has_top has_bot

variables {X Y : Type*}
variables {a b : Type*}

-------------------------------------------------------------------------------
-- Definition
-------------------------------------------------------------------------------

structure kent_convergence_space (X : Type*) extends convergence_space X :=
(kent_converges : ∀ {x} {ℱ}, converges ℱ x -> converges (ℱ ⊔ pure x) x)

attribute [ext] kent_convergence_space
attribute [class] kent_convergence_space

open kent_convergence_space

instance : has_coe (kent_convergence_space X) (convergence_space X) := {
  coe := λ p, p.to_convergence_space,
}

-------------------------------------------------------------------------------
-- Induced/coinduced Kent convergence space
-------------------------------------------------------------------------------

def kent_convergence_space.induced (f : X -> Y) (q : kent_convergence_space Y) : kent_convergence_space X :=
let ind := convergence_space.induced f q in {
  kent_converges :=
    begin
      assume x : X,
      assume ℱ : filter X,
      assume h : q.converges (map f ℱ) (f x),
      let ℱ₁ := map f ℱ,
      let ℱ₂ := ℱ ⊔ pure x,
      let y := f x,
      show q.converges (map f ℱ₂) y, begin
        rw [filter.map_sup, filter.map_pure],
        simp [q.kent_converges h],
      end,
    end,
  ..ind
}

def kent_convergence_space.coinduced (f : X -> Y) (p : kent_convergence_space X) : kent_convergence_space Y :=
let coind := convergence_space.coinduced f p in {
  kent_converges := begin
    assume y  : Y,
    assume 𝒢 : filter Y,
    assume h : coind.converges 𝒢 y,
    cases h,
      case pure_case begin
        have : 𝒢 ⊔ pure y = pure y, from calc
          𝒢 ⊔ pure y  = pure y ⊔ 𝒢 : sup_comm
          ... = pure y : by rw sup_of_le_left h,
        have : coind.converges (pure y) y, from coind.pure_converges y,
        show coind.converges (𝒢 ⊔ pure y) y, begin
          rw (by assumption : 𝒢 ⊔ pure y = pure y),
          assumption,
        end,
      end,
      case other_case : ℱ x _ _ _ begin
        let ℱ' := ℱ ⊔ pure x,
        have : 𝒢 ⊔ pure y <= map f ℱ', from calc
          𝒢 ⊔ pure y <= map f ℱ ⊔ pure y : sup_le_sup_right (by assumption : 𝒢 ≤ map f ℱ) (pure y)
          ... = map f ℱ ⊔ pure (f x) : by rw (by assumption : y = f x)
          ... = map f ℱ ⊔ map f (pure x) : by rw filter.map_pure
          ... = map f (ℱ ⊔ pure x) : map_sup,
        have : p.converges ℱ' x, begin
          apply p.kent_converges,
          assumption
        end,
        apply coinduced_converges.other_case ℱ' x
          (by assumption : sup 𝒢 (pure y) <= map f ℱ')
          (by assumption : y = f x)
          (by assumption : p.converges ℱ' x)
      end,
  end,
  ..coind
}

-------------------------------------------------------------------------------
-- Convergence spaces constructions
-------------------------------------------------------------------------------

instance {p : X -> Prop} [q : kent_convergence_space X] : kent_convergence_space (subtype p) :=
kent_convergence_space.induced coe q

instance {r : X -> X -> Prop} [q : kent_convergence_space X] : kent_convergence_space (quot r) :=
kent_convergence_space.coinduced (quot.mk r) q

--instance [p : convergence_space a] [q : convergence_space b] : convergence_space (prod a b) :=
--inf (convergence_space.induced prod.fst p) (convergence_space.induced prod.snd q)
