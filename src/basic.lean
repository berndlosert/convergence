import order.filter.ultrafilter
import order.filter.partial
import algebra.support

noncomputable theory
open set filter classical
open_locale classical filter
open has_sup

variables {a b : Type*}

-------------------------------------------------------------------------------
-- Definition of convergence space and specializations thereof
-------------------------------------------------------------------------------

class convergence_space (a : Type*) :=
(conv : filter a -> a -> Prop)
(pure_conv : forall {x : a}, conv (pure x) x)
(le_conv : forall {x : a} {l l' : filter a}, l <= l' -> conv l' x -> conv l x) -- l <= l' means l' ⊆ l

attribute [ext] convergence_space

class kent_convergence_space (a : Type*) extends convergence_space a :=
(kent_conv : forall {x : a} {l : filter a}, conv l x -> conv (sup l (pure x)) x)

class limit_space (a : Type*) extends kent_convergence_space a :=
(sup_conv : forall {x : a} {l l' : filter a}, conv l x -> conv l' x -> conv (sup l l') x) -- l ⊔ l' means l ∩ l'

class pseudotopological_space (a : Type*) extends limit_space a :=
(ultra_conv : forall {x : a} {l : filter a}, (forall {u : ultrafilter a}, conv u.to_filter x) -> conv l x)

open convergence_space kent_convergence_space limit_space

def lim [convergence_space a] (l : filter a) : set a := set_of (conv l)

structure continuous [convergence_space a] [convergence_space b] (f : a -> b) : Prop :=
(filter_conv : forall {x : a} {l : filter a}, conv l x -> conv (map f l) (f x))

class hausdorff_space [convergence_space a] : Prop :=
(hausdorff_prop : forall (l : filter a) [ne_bot l], subsingleton (lim l))
