import tactic
import order.filter.partial
import algebra.support
import kent_convergence_space.basic
import order.complete_lattice.extra

noncomputable theory
open set filter classical kent_convergence_space convergence_space
open_locale classical filter

variables {α β : Type*} 

/-!
### Definition
-/

@[ext] class limit_space (α : Type*) extends convergence_space α :=
(sup_converges : ∀ {f g x}, converges f x -> converges g x -> converges (f ⊔ g) x) -- f ⊔ g means f ∩ g

open limit_space

namespace limit_space

instance has_coe : has_coe (limit_space α) (convergence_space α) := 
{ coe := λ p, p.to_convergence_space }

@[simp, norm_cast] theorem coe_inj {p q : limit_space α} :
  (↑p : convergence_space α)= ↑q ↔ p = q :=
by { rw limit_space.ext_iff, tauto }

lemma coe_injective : function.injective (coe : limit_space α → convergence_space α) :=
λ s t, coe_inj.1

end limit_space

@[simp] def sup_converges_ {α : Type*} (p : limit_space α) {f g : filter α} {x : α} 
  (hf : converges_ ↑p f x) (hg : converges_ ↑p g x) : converges_ ↑p (f ⊔ g) x
:= @sup_converges _ p _ _ _ hf hg

instance limit_space.to_kent_convergence_space 
  [limit_space α] : kent_convergence_space α :=
{ converges := converges,
  pure_converges := pure_converges,
  le_converges := λ f g hle hconv, le_converges hle,
  kent_converges := λ f x hconv, sup_converges hconv (pure_converges x) }

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

/-- Limit structures form a complete lattice. Infimums are formed like in convergence 
  spaces. Supremums are different: `h` converges to `x` with respect to `p ⊔ q` when there
  exists filters `g, h` such that `g` converges to `x` with respect to `p`, `h` converges
  to `x` with respect to `q` and `f ≤ g ⊔ h`. -/

instance : has_top (limit_space α) :=
{ top := { sup_converges := by tauto, ..convergence_space.has_top.top }}

instance : has_bot (limit_space α) :=
{ bot := 
  { sup_converges :=
    begin
      intros f g x hf hg,
      calc f ⊔ g ≤ pure x ⊔ pure x : sup_le_sup hf hg
      ... = pure x : sup_idem,
    end,
    ..convergence_space.has_bot.bot }}

instance : has_inf (limit_space α) := 
{ inf := λ p q, let super : convergence_space α := ↑p ⊓ ↑q in 
  { converges := converges_ super,
    pure_converges := pure_converges_ super,
    le_converges := le_converges_ super,
    sup_converges := λ f g x hf hg,
     ⟨sup_converges_ p hf.1 hg.1, sup_converges_ q hf.2 hg.2⟩ }}

instance : has_sup (limit_space α) :=
{ sup := λ p q, let super : convergence_space α := ↑p ⊔ ↑q in
  { converges := λ f x, ∃ g₁ g₂, f ≤ g₁ ⊔ g₂ ∧ converges_ super g₁ x ∧ converges_ super g₂ x,
    pure_converges := λ x, by refine ⟨pure x, pure x, _, _, _⟩; simp,
    le_converges :=
    begin
      rintros f g hle x ⟨g₁, g₂, hle', hg₁, hg₂⟩,
      exact ⟨g₁, g₂, trans hle hle', hg₁, hg₂⟩
    end,
    sup_converges :=
    begin
      rintros f f' x ⟨g₁, g₂, hle, hg₁, hg₂⟩ ⟨g₁', g₂', hle', hg₁', hg₂'⟩,
      refine ⟨g₁ ⊔ g₁', g₂ ⊔ g₂', _, _, _⟩,
      { calc f ⊔ f' ≤ (g₁ ⊔ g₂) ⊔ (g₁' ⊔ g₂') : sup_le_sup hle hle'
        ... = (g₁ ⊔ g₁') ⊔ (g₂ ⊔ g₂') : sup_sup_sup_comm g₁ g₂ g₁' g₂' },
      { cases hg₁, cases hg₁', 
        exact or.inl (sup_converges_ p hg₁ hg₁'), 
        sorry,},
      
    end }}
    
instance : has_Inf (limit_space α) :=
  { Inf := λ ps, let super : convergence_space α := Inf (coe '' ps) in
    { converges := converges_ super,
      pure_converges := pure_converges_ super,
      le_converges := le_converges_ super,
      sup_converges :=
      begin
        intros f g x hf hg p hp,
        obtain ⟨q, hq, heq⟩ := mem_image_iff_bex.mp hp,
        rw ← heq at *,
        exact sup_converges_ q (hf hp) (hg hp)
      end }}

instance : has_Sup (limit_space α) :=
{ Sup := λ ps,
  { converges := λ f x, f ≤ pure x ∨ ∃ g : limit_space α → filter α, 
      f ≤ Sup (g '' ps) ∧ ∀ p : limit_space α, p ∈ ps → converges_ ↑p (g p) x,
    pure_converges := 
    begin
      intros x, use (λ _, pure x), split,
      -- intros p hmem, refine ⟨pure_converges_ p x, _⟩,
      rw [nonempty.image_const ⟨p, hmem⟩ (pure x), Sup_singleton],
      tauto,
    end,
    le_converges :=
    begin
      rintros f g hle x ⟨h, hall⟩,
      use h, intros p hmem,
      obtain ⟨hconv, hle'⟩ := hall p hmem,
      exact ⟨hconv, le_trans hle hle'⟩
    end,
    sup_converges :=
    begin
      rintros f f' x ⟨g, hall⟩ ⟨g', hall'⟩,
      let h : limit_space α → filter α := λ p, g p ⊔ g' p,
      use h, intros p hmem,
      obtain ⟨hconv, hle⟩ := hall p hmem,
      obtain ⟨hconv', hle'⟩ := hall' p hmem,
      refine ⟨sup_converges_ p hconv hconv', _⟩,
      have : g ≤ h, by intros p; simp [h],
      have hSup : Sup (g '' ps) ≤ Sup (h '' ps) := Sup_image_le this ps,
      have : g' ≤ h, by intros p; simp [h],
      have hSup' : Sup (g' '' ps) ≤ Sup (h '' ps) := Sup_image_le this ps,
      calc f ⊔ f' ≤ Sup (g '' ps) ⊔ Sup (g' '' ps) : sup_le_sup hle hle'
      ... ≤ Sup (h '' ps) : sup_le hSup hSup' 
    end }}
}

instance : semilattice_inf (limit_space α) :=
by { refine function.injective.semilattice_inf coe limit_space.coe_injective _, tauto }

instance : semilattice_sup (limit_space α) :=
{ le_sup_left := λ p q f x hconv, ⟨f, pure x, le_sup_left, hconv, pure_converges_ ↑q x⟩,
  le_sup_right := λ p q f x hconv, ⟨pure x, f, le_sup_right, pure_converges_ ↑p x, hconv⟩,
  sup_le := λ p q r hp hq f x ⟨g₁, g₂, hle, hg₁, hg₂⟩, 
    le_converges_ r hle (sup_converges_ r (hp hg₁) (hq hg₂)),
  ..limit_space.partial_order,
  ..limit_space.has_sup }

lemma limit_space.coe_Inf (ps : set (limit_space α)) : 
  (↑(Inf ps) : convergence_space α) = Inf (coe '' ps) :=
by { ext, tauto }

instance : complete_semilattice_Inf (limit_space α) :=
{ Inf_le :=
  begin
    intros ps p hmem f x hconv,
    rw limit_space.coe_Inf at hconv,
    exact hconv (mem_image_of_mem coe hmem),
  end,
  le_Inf :=
  begin
    intros ps q hle, 
    change ↑q ≤ ↑(Inf ps),
    rw limit_space.coe_Inf,
    intros f x hconv p hp,
    obtain ⟨r, hr, heq⟩ := mem_image_iff_bex.mp hp,
    rw ← heq,
    exact hle r hr hconv,
  end,
  ..limit_space.partial_order,
  ..limit_space.has_Inf }

instance : complete_semilattice_Sup (limit_space α) :=
{ le_Sup :=
  begin
    intros ps p hp f x hconv,
    let g : limit_space α → filter α := λ _, f ⊔ pure x,
    use g, intros q hq, simp [g],
    rw [nonempty.image_const ⟨p, hp⟩ (pure x), Sup_singleton],
    refine ⟨_, le_refl (pure x)⟩,
    change converges_ ↑q f x,
  end,
  Sup_le := λ qs p hle f x hconv, sorry,
  ..limit_space.partial_order,
  ..limit_space.has_Sup }  

instance : complete_lattice (limit_space α) :=
complete_lattice_of_complete_semilattice_Inf (limit_space α)  