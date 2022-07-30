import tactic
import order.filter.partial
import algebra.support
import kent_convergence_space.basic
import order.complete_lattice.extra
import data.fin.tuple

noncomputable theory
open set filter classical kent_convergence_space convergence_space
open_locale classical filter

variables {α β : Type*} 

/-!
### Definition
-/

@[ext] class limit_space (α : Type*) extends convergence_space α :=
(sup_converges : ∀ {f g x}, converges f x → converges g x → converges (f ⊔ g) x)

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

@[simp] def sup_converges_ (p : limit_space α) {f g : filter α} {x : α} 
  (hf : converges_ ↑p f x) (hg : converges_ ↑p g x) : converges_ ↑p (f ⊔ g) x
:= @sup_converges _ p _ _ _ hf hg

instance limit_space.to_kent_convergence_space 
  [limit_space α] : kent_convergence_space α :=
{ converges := converges,
  pure_converges := pure_converges,
  le_converges := λ f g hle hconv, le_converges hle,
  kent_converges := λ f x hconv, sup_converges hconv (pure_converges x) }

lemma Sup_converges [limit_space α] {fs : set (filter α)} (hfin : fs.finite)
  {x : α} (hconv : ∀ f ∈ fs, converges f x) : converges (Sup fs) x :=
begin
  refine set.finite.induction_on' hfin _ _,
  { simp, exact bot_converges x },
  { intros g gs hmem hsub hnmem hSup,
    rw [set.insert_eq, Sup_union], simp, 
    have hg : converges g x := hconv g hmem,
    exact sup_converges hg hSup}
end

lemma Sup_converges_ (p : limit_space α) {fs : set (filter α)} (hfin : fs.finite)
  {x : α} (hconv : ∀ f ∈ fs, converges_ ↑p f x) : converges_ ↑p (Sup fs) x :=
@Sup_converges _ p fs hfin x hconv

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
{ sup := λ p q,
  { converges := λ f x, ∃ g₁ g₂, f ≤ g₁ ⊔ g₂ ∧ converges_ ↑p g₁ x ∧ converges_ ↑q g₂ x,
    pure_converges := λ x, by refine ⟨pure x, pure x, _, _, _⟩; simp,
    le_converges :=
    begin
      rintros f g hle x ⟨g₁, g₂, hle', hg₁, hg₂⟩,
      exact ⟨g₁, g₂, trans hle hle', hg₁, hg₂⟩
    end,
    sup_converges :=
    begin
      rintros f f' x ⟨g₁, g₂, hle, hg₁, hg₂⟩ ⟨g₁', g₂', hle', hg₁', hg₂'⟩,
      refine ⟨g₁ ⊔ g₁', g₂ ⊔ g₂', _, sup_converges_ p hg₁ hg₁', sup_converges_ q hg₂ hg₂'⟩,
      calc f ⊔ f' ≤ (g₁ ⊔ g₂) ⊔ (g₁' ⊔ g₂') : sup_le_sup hle hle'
      ... = (g₁ ⊔ g₁') ⊔ (g₂ ⊔ g₂') : sup_sup_sup_comm g₁ g₂ g₁' g₂'
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
{ Sup := λ ps, let super : convergence_space α := Sup (coe '' ps) in
  { converges := λ f x, ∃ gs : set (filter α), gs.nonempty ∧ gs.finite ∧
      f ≤ Sup gs ∧ ∀ g, g ∈ gs → converges_ super g x,
    pure_converges := λ x, 
      ⟨{ pure x }, set.singleton_nonempty (pure x), set.finite_singleton (pure x), by simp, by simp⟩,
    le_converges :=
    begin
      intros f f' hle x hconv,
      obtain ⟨gs, hne, hfin, hle', hconv'⟩ := hconv,
      exact ⟨gs, hne, hfin, le_trans hle hle', hconv'⟩
    end,
    sup_converges :=
    begin
      rintros f₁ f₂ x hf₁ hf₂,
      obtain ⟨gs₁, hne₁, hfin₁, hle₁, hconv₁⟩ := hf₁,
      obtain ⟨gs₂, hne₂, hfin₂, hle₂, hconv₂⟩ := hf₂,
      refine ⟨gs₁ ∪ gs₂, set.nonempty.inl hne₁, set.finite_union.mpr ⟨hfin₁, hfin₂⟩, _, _⟩,
      rw Sup_union,
      exact sup_le_sup hle₁ hle₂,
      intros g hmem, cases hmem,
      { exact hconv₁ g hmem },
      { exact hconv₂ g hmem }
    end }}

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
    refine ⟨{ f }, set.singleton_nonempty f, set.finite_singleton f, by simp, _⟩,
    intros g hmem,
    rw set.mem_singleton_iff.mp hmem,
    exact or.inr ⟨p, mem_image_of_mem coe hp, hconv⟩,
  end,
  Sup_le :=
  begin
    rintros qs p hle f x ⟨gs, hne, hfin, hle', hconv⟩,
    have hg : ∀ g ∈ gs, converges_ ↑p g x,
    begin
      intros g hmem,
      let hconv' : g ≤ pure x ∨
        ∃ q : convergence_space α, q ∈ coe '' qs ∧ converges_ q g x := hconv g hmem,
      exact hconv'.elim 
        (λ hg : g ≤ pure x, le_converges_ ↑p hg (pure_converges_ ↑p x))
        (λ hexists : (∃ q : convergence_space α, q ∈ coe '' qs ∧ converges_ q g x),
        begin
          obtain ⟨q, hq, hg⟩ := hexists,
          rw set.mem_image_iff_bex at hq,
          obtain ⟨q', hq', heq⟩ := hq,
          rw ← heq at hg,
          exact (hle q' hq') hg,
        end),
    end,
    have hSup : converges_ ↑p (Sup gs) x, from Sup_converges_ p hfin hg,
    exact le_converges_ p hle' hSup,
  end,
  ..limit_space.partial_order,
  ..limit_space.has_Sup }

instance : lattice (limit_space α) :=
{ ..limit_space.semilattice_sup,
  ..limit_space.semilattice_inf }

instance : complete_lattice (limit_space α) :=
{ bot_le := λ p f x hconv, le_converges_ p hconv (pure_converges_ p x),
  le_top := by intros; tauto,
  ..limit_space.has_bot,
  ..limit_space.has_top,
  ..limit_space.lattice,
  ..limit_space.complete_semilattice_Inf,
  ..limit_space.complete_semilattice_Sup }