import tactic
import order.filter.partial
import algebra.support
import kent_convergence_space.basic

noncomputable theory
open set filter classical kent_convergence_space convergence_space
open_locale classical filter

variables {α β : Type*} 

/-!
### Definition
-/

@[ext] class limit_space (α : Type*) extends kent_convergence_space α :=
(sup_converges : ∀ {f g x}, converges f x -> converges g x -> converges (f ⊔ g) x) -- f ⊔ g means f ∩ g

open limit_space

namespace limit_space

instance has_coe : has_coe (limit_space α) (kent_convergence_space α) := 
{ coe := λ p, p.to_kent_convergence_space }

@[simp, norm_cast] theorem coe_inj {p q : limit_space α} :
  (↑p : kent_convergence_space α)= ↑q ↔ p = q :=
by { rw limit_space.ext_iff, tauto }

lemma coe_injective : function.injective (coe : limit_space α → kent_convergence_space α) :=
λ s t, coe_inj.1

end limit_space

@[simp] def sup_converges_ {α : Type*} (p : limit_space α) {f g : filter α} {x : α} 
  (hf : converges_ ↑p f x) (hg : converges_ ↑p g x) : converges_ ↑p (f ⊔ g) x
:= @sup_converges _ p _ _ _ hf hg

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

instance : has_inf (limit_space α) := 
{ inf := λ p q, let super : kent_convergence_space α := ↑p ⊓ ↑q in 
  { converges := converges_ super,
    pure_converges := pure_converges_ super,
    le_converges := le_converges_ super,
    kent_converges := λ _ _, kent_converges_ super,
    sup_converges := λ f g x hf hg,
     ⟨sup_converges_ p hf.1 hg.1, sup_converges_ q hf.2 hg.2⟩ }}

instance : has_Inf (limit_space α) :=
  { Inf := λ ps, let super : kent_convergence_space α := Inf (coe '' ps) in
    { converges := converges_ super,
      pure_converges := pure_converges_ super,
      le_converges := le_converges_ super,
      kent_converges := λ _ _, kent_converges_ super,
      sup_converges :=
      begin
        intros f g x hf hg p hp,
        obtain ⟨q, hq, heq⟩ := mem_image_iff_bex.mp hp,
        rw ← heq at *,
        obtain ⟨q', hq', heq'⟩ := mem_image_iff_bex.mp hq,
        rw ← heq' at *,
        exact sup_converges_ q' (hf hp) (hg hp)
      end }}

instance : has_sup (limit_space α) :=
{ sup := λ p q,
  { converges := λ f x, ∃ g h, converges_ ↑p g x ∧ converges_ ↑q h x ∧ f ≤ g ⊔ h,
    pure_converges := λ x, 
      ⟨pure x, pure x, pure_converges_ ↑p x, pure_converges_ ↑q x, le_of_eq (sup_idem.symm)⟩,
    le_converges :=
    begin
      rintros f g hle x ⟨g', h', hg', hh', hle'⟩,
      exact ⟨g', h', hg', hh', trans hle hle'⟩
    end,
    kent_converges :=
    begin
      rintros f x ⟨g, h, hg, hh, hle⟩,
      refine ⟨g ⊔ pure x, h ⊔ pure x, kent_converges_ ↑p hg, kent_converges_ ↑q hh, _⟩,
      rw [sup_left_comm, sup_right_idem, sup_left_comm, ← sup_assoc],
      exact sup_le_sup_right hle (pure x),
    end,
    sup_converges :=
    begin
      rintros f f' x ⟨g, h, hg, hh, hle⟩ ⟨g', h', hg', hh', hle'⟩,
      have hgg' := sup_converges_ p hg hg',
      have hhh' := sup_converges_ q hh hh',
      refine ⟨g ⊔ g', h ⊔ h', hgg', hhh', _⟩,
      calc f ⊔ f' ≤ (g ⊔ h) ⊔ (g' ⊔ h') : sup_le_sup hle hle'
      ... = (g ⊔ g') ⊔ (h ⊔ h') : sup_sup_sup_comm g h g' h'
    end }}

instance : has_Sup (limit_space α) :=
{ Sup := λ ps,
  { converges := λ f x, ∃ g : limit_space α → filter α, 
      ∀ (p : limit_space α), p ∈ ps → converges_ ↑p (g p) x ∧ f ≤ Inf (g '' ps),
    pure_converges := λ x, by { use (λ _, pure x), intros, simp },
    le_converges :=
    begin
      rintros f g hle x ⟨h, hall⟩,
      use h, intros p hmem,
      obtain ⟨hconv, hle'⟩ := hall p hmem,
      exact ⟨hconv, le_trans hle hle'⟩
    end,
    kent_converges :=
    begin
      rintros f x ⟨g, hall⟩,
      let h : limit_space α → filter α := λ p, g p ⊔ pure x,
      use h, intros p hmem,
      obtain ⟨hconv, hle⟩ := hall p hmem,
      refine ⟨kent_converges_ p hconv, _⟩,
      simp [h], intros q hq,
      have : f ≤ g q := le_trans hle (Inf_le (mem_image_of_mem g hq)),
      exact le_sup_of_le_left this,
    end,
    sup_converges :=
    begin
      rintros f f' x ⟨g, hall⟩ ⟨g', hall'⟩,

    end }}
/-
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