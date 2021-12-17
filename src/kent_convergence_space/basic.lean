import tactic
import order.filter.partial
import algebra.support
import convergence_space.basic

noncomputable theory
open set filter classical
open_locale classical filter
open has_sup has_inf has_mem has_top has_bot

variables {a b : Type*}

-------------------------------------------------------------------------------
-- Definition
-------------------------------------------------------------------------------

structure kent_convergence_space (a : Type*) extends convergence_space a :=
(kent_converges : forall {x} {l}, converges l x -> converges (sup l (pure x)) x)

attribute [ext] kent_convergence_space
attribute [class] kent_convergence_space

open kent_convergence_space

-------------------------------------------------------------------------------
-- Induced/coinduced Kent convergence space
-------------------------------------------------------------------------------

def induced (f : a -> b) (q : kent_convergence_space b) : kent_convergence_space a :=
let ind := convergence_space.induced f q.to_convergence_space in {
  kent_converges :=
    begin
      assume x : a,
      assume l : filter a,
      assume h : q.converges (map f l) (f x),
      let l1 := map f l,
      let l2 := sup l (pure x),
      let y := f x,
      show q.converges (map f l2) y, begin
        rw [filter.map_sup, filter.map_pure],
        simp [q.kent_converges h],
      end,
    end,
  ..ind
}

def coinduced (f : a -> b) [p : kent_convergence_space a] : kent_convergence_space b :=
let coind := convergence_space.coinduced f p.to_convergence_space in {
  kent_converges := begin
    assume y : b,
    assume l' : filter b,
    assume h : coind.converges l' y,
    cases h,
      case pure_case begin
        have : sup l' (pure y) = pure y, from calc
          sup l' (pure y) = sup (pure y) l' : sup_comm
                      ... = pure y          : by rw sup_of_le_left h,
        have : coind.converges (pure y) y, from coind.pure_converges y,
        show coind.converges (sup l' (pure y)) y, begin
          rw (by assumption : sup l' (pure y) = pure y),
          assumption,
        end,
      end,
      case other_case : l x _ _ _ begin
        let l'' := sup l (pure x),
        have : sup l' (pure y) <= map f l'', from calc
          sup l' (pure y) <= sup (map f l) (pure y)         : sup_le_sup_right (by assumption : l' <= map f l) (pure y)
                      ...  = sup (map f l) (pure (f x))     : by rw (by assumption : y = f x)
                      ...  = sup (map f l) (map f (pure x)) : by rw filter.map_pure
                      ...  = map f (sup l (pure x))         : map_sup,
        have : p.converges l'' x, begin
          apply p.kent_converges,
          assumption
        end,
        apply coinduced_converges.other_case l'' x
          (by assumption : sup l' (pure y) <= map f l'')
          (by assumption : y = f x)
          (by assumption : p.converges l'' x)
      end,
  end,
  ..coind
}
