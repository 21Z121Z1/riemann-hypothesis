import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.KeyFormulaPowOfKeyFormula
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0051
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0016
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0037
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0036
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0067
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.NonemptyRingHomComplex
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KeyCl GlobalTheory.KeyPow

namespace GlobalTheory.KeyRuleUnique

set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
open Cardinal in

theorem _root_.GlobalTheory.KeyRuleUnique.nonempty_ringHom_complex (K : Type) [Field K] [CharZero K]
    [Countable K] : Nonempty (K →+* ℂ) := by
  let F := FractionRing (MvPolynomial ℝ K)
  let L := AlgebraicClosure F
  let i : K →+* L := (algebraMap F L).comp ((algebraMap (MvPolynomial ℝ K) F).comp MvPolynomial.C)
  haveI : CharZero L := (RingHom.charZero_iff i.injective).1 inferInstance
  have hK : #K ≤ 𝔠 := mk_le_aleph0.trans aleph0_le_continuum
  have hP : #(MvPolynomial ℝ K) = 𝔠 := by
    rw [MvPolynomial.cardinalMk_eq_max_lift]
    simp only [lift_id, mk_real]
    rw [max_eq_right hK, max_eq_left aleph0_le_continuum]
  have hF : #F = 𝔠 := by rw [FractionRing.cardinalMk, hP]
  have hL : #L = 𝔠 := by
    apply le_antisymm
    · calc #L ≤ max #F ℵ₀ := Algebra.IsAlgebraic.cardinalMk_le_max F L
        _ = 𝔠 := by rw [hF, max_eq_left aleph0_le_continuum]
    · rw [← hF]
      exact mk_le_of_injective (algebraMap F L).injective
  have hlt : ℵ₀ < #L := hL ▸ aleph0_lt_continuum
  obtain ⟨e⟩ := IsAlgClosed.ringEquiv_of_equiv_of_char_eq (K := L) (L := ℂ) 0 hlt
    (Cardinal.eq.1 (hL.trans mk_complex.symm))
  exact ⟨e.toRingHom.comp i⟩

theorem value_of_normalAt {N : ℕ → ℕ} {κ : Rule} (hH : Homog N κ) (hT : ThetaOne κ) (x : KeyIn ℂ)
    {τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ} {a b : Fin x.P.g → ℂ} {c : ℂ} (hab : charHalf x.P.g a b) (hc : c ≠ 0)
    (hM : M.det ≠ 0) (h : NormalAt x τ M a b c) : (κ ℂ x : ℂ) = (M.det ^ 4 / c ^ 8) ^ N x.P.g := by
  refine value_at_normalForm N 0 (κ ℂ) x.P.g a b (Nat.zero_le _)
    (fun P hg rig hr th hth v hv th' hth' v' hv' a M _ => hH ℂ P hg rig hr th hth v hv th' hth' v' hv' a M)
    (fun y hy σ hσ => ?_) x rfl τ M c hc hM h
  obtain ⟨u, h₁, h₂, h₃, h₄, h₅, h₆⟩ := (normalAt_one_iff y σ _ _).1 hσ
  exact hT y u σ _ _ h₁ h₂ (fun i => hab.1 _) (fun i => hab.2 _) h₃ h₄ h₅ h₆

theorem rule_unique : ∀ (N : ℕ → ℕ) (κ κ' : Rule), Homog N κ → Funct κ → ThetaOne κ → Homog N κ' → Funct κ' → ThetaOne κ' → ∀ (K : Type) [Field K] [CharZero K] (x : KeyIn K), κ K x = κ' K x := by
  intro N κ κ' hH hF hT hH' hF' hT' K _ _ x
  obtain ⟨K₀, x₀, hK₀, hx₀⟩ := (GlobalTheory.T.keyData_descend_countable_subrings GlobalTheory.firstFiveLaws.1).2 K x
  obtain ⟨σ⟩ := nonempty_ringHom_complex K₀
  obtain ⟨y, hy⟩ := exists_keyPB_ring x₀ σ
  obtain ⟨⟨τ, M, a, b, c, hab, hc, hM, hN⟩, -⟩ := KeyNormalExists.exists_normalAt GlobalTheory.thetaUnifAV_all y
  have e : (κ ℂ y : ℂ) = κ' ℂ y := by
    rw [value_of_normalAt hH hT y hab hc hM hN, value_of_normalAt hH' hT' y hab hc hM hN]
  rw [hF K₀ ℂ σ x₀ y hy, hF' K₀ ℂ σ x₀ y hy] at e
  apply Units.ext
  rw [hF K₀ K _ x₀ x hx₀, hF' K₀ K _ x₀ x hx₀, σ.injective e]

end GlobalTheory.KeyRuleUnique
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SiegelFamilyStandardLevelPointsSameComponentStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelFamily_standard_level_points_same_component : Out.Laws → Out.Laws2 → ThetaUnifAV → GlobalTheory.TorusAlgebraic → ∀ (h k : ℕ) (K : Type) [Field K] (ζ : K) (σ : K →+* ℂ) (F : SFam h k ζ), 1 ≤ h → 3 ≤ k → Odd k → σ ζ = Complex.exp (-(2 * Real.pi * Complex.I) / k) → ∀ (τ τ' : Matrix (Fin h) (Fin h) ℂ) (p q : Sp ℂ ⟶ F.X), p ≫ F.s = spMap σ → q ≫ F.s = spMap σ → PtAt F.univ p τ → PtAt F.univ q τ' → SameComp F.s σ p q := by
  first | exact @GlobalTheory.SiegelConnected.sameComp_of_ptAt | exact GlobalTheory.SiegelConnected.sameComp_of_ptAt | (intros; apply GlobalTheory.SiegelConnected.sameComp_of_ptAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaKeyRulePowComplexStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KeyCl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaKeyRule_pow_complex : ∀ κ : Rule, Homog (fun _ => 1) κ → ThetaOne κ → ∀ (x y : KeyIn ℂ) (j : ℕ), GlobalTheory.KeyPow.IsKeyPow y x j → κ ℂ y = κ ℂ x ^ j := by
  first | exact @GlobalTheory.KeyCl.value_pow_complex | exact GlobalTheory.KeyCl.value_pow_complex | (intros; apply GlobalTheory.KeyCl.value_pow_complex <;> assumption)
end

