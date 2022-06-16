import tactic
import order.filter.partial
import algebra.support
import kent_convergence_space.basic

noncomputable theory
open set filter classical kent_convergence_space
open_locale classical filter

variables {α β : Type*} 

/-!
### Definition
-/

@[ext] class limit_space (α : Type*) extends kent_convergence_space α :=
(sup_converges : ∀ {f g x}, converges f x -> converges g x -> converges (f ⊔ g) x) -- f ⊔ g means f ∩ g

open limit_space

@[simp] def sup_converges_ {α : Type*} (p : limit_space α) {f g : filter α} {x : α} 
  (hf : converges_ p.to_convergence_space f x) (hg : converges_ p.to_convergence_space g x) : 
  converges_ p.to_convergence_space (f ⊔ g) x
:= @sup_converges _ p _ _ _ hf hg

instance : has_coe (limit_space α) (kent_convergence_space α) := 
{ coe := λ p, p.to_kent_convergence_space }

namespace limit_space

@[simp, norm_cast] theorem coe_inj {p q : limit_space α} :
  (↑p : convergence_space α)= ↑q ↔ p = q :=
by { rw limit_space.ext_iff, rw kent_convergence_space.ext_iff, tauto }

lemma coe_injective : function.injective (coe : limit_space α → convergence_space α) :=
λ s t, coe_inj.1

end limit_space

/-!
### Ordering
-/

/-- The ordering is the one inherited from convergence spaces. -/

instance : has_le (limit_space α) := ⟨λ p q, ↑p ≤ (↑q : convergence_space α)⟩

instance : partial_order (limit_space α) := 
  partial_order.lift coe limit_space.coe_injective

/-!
### Lattice of limit structures
-/

/-- Just like convergence spaces, limit spaces also form a complete lattice. -/

instance : has_top (limit_space α) :=
{ top := { sup_converges := by tauto, ..kent_convergence_space.has_top.top }}

instance : has_bot (limit_space α) :=
{ bot := 
  { sup_converges :=
    begin
      intros f g x hf hg,
      have : f ⊔ g ≤ pure x, from calc
        f ⊔ g ≤ pure x ⊔ pure x : sup_le_sup hf hg
        ... = pure x : sup_idem,
      assumption
    end,
    ..kent_convergence_space.has_bot.bot }}
/-
instance : has_inf (kent_convergence_space α) := 
{ inf := λ p q, let super : convergence_space α := ↑p ⊓ ↑q in 
  { converges := converges_ super,
    pure_converges := pure_converges_ super,
    le_converges := le_converges_ super,
    kent_converges := λ f x hconv, 
    ⟨kent_converges_ p hconv.1, kent_converges_ q hconv.2⟩ }}

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
        refine kent_converges_ q (hconv hp)
      end }}

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

lemma coe_Inf (ps : set (kent_convergence_space α)) : 
  (↑(Inf ps) : convergence_space α) = Inf (coe '' ps) :=
by { ext, tauto }


instance : complete_semilattice_Inf (kent_convergence_space α) :=
{ Inf_le :=
  begin
    intros ps p hmem f x hconv,
    rw coe_Inf at hconv,
    exact hconv (mem_image_of_mem coe hmem),
  end,
  le_Inf :=
  begin
    intros ps q hle, 
    change ↑q ≤ ↑(Inf ps),
    rw coe_Inf,
    intros f x hconv p hp,
    obtain ⟨r, hr, heq⟩ := mem_image_iff_bex.mp hp,
    rw ← heq,
    exact hle r hr hconv,
  end,
  ..kent_convergence_space.partial_order,
  ..kent_convergence_space.has_Inf }
-/