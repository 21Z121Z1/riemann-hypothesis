import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0648
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0641
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FintypeResidue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0601
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0650
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0632
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0649
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.PullHEq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HdgAffIso
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequence
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0651
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.UnipotentTateFunctionalEquation
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0653

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetNeZeroOfGramNondegenerateStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_ne_zero_of_gram_nondegenerate : ∀ (D : D7) (W : HSp D) (b₀ : HermE D W.rank), b₀.1.det ≠ 0 → ∀ x₀, gramQ W x₀ = b₀.1 → x₀.det ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.ColumnSplitting.Frame.det_ne_zero_of_gramQ | exact GlobalTheory.CompanionTheory.ColumnSplitting.Frame.det_ne_zero_of_gramQ | (intros; apply GlobalTheory.CompanionTheory.ColumnSplitting.Frame.det_ne_zero_of_gramQ <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetRowRepStatement
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_row_rep : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (i j : ℕ) (c : Fin j → 𝓀[F]), GeneralLinearGroup.det (rowRep i j c) = uniformizerUnit F ^ ((i : ℤ) + j) := by
  first | exact @GlobalTheory.CompanionTheory.LFUDom.det_rowRep_eq_zpow | exact GlobalTheory.CompanionTheory.LFUDom.det_rowRep_eq_zpow | (intros; apply GlobalTheory.CompanionTheory.LFUDom.det_rowRep_eq_zpow <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetTorusPowerStatement
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_torus_power : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ) (l : Fin n → ℤ), GeneralLinearGroup.det (torusPow F n l) = uniformizerUnit F ^ (∑ i, l i) := by
  first | exact @GlobalTheory.CompanionTheory.LFUDom.det_torusPow_eq | exact GlobalTheory.CompanionTheory.LFUDom.det_torusPow_eq | (intros; apply GlobalTheory.CompanionTheory.LFUDom.det_torusPow_eq <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentiableBoundaryZetaTermStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical
open Ad3 Ad3.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.differentiable_boundary_zeta_term : ∀ (μ : Measure G2) (𝓕 : Set G2) (mK : Measure KA) (𝓓 : Set Jd) (H : G2 → ℂ) (c : HeckeCharacter ℚ),
  Set0 μ 𝓕 mK 𝓓 → Aut H → Differentiable ℂ (GlobalTheory.CompanionTheory.RSZeta.Bd μ 𝓕 H c) := by
  first | exact @GlobalTheory.CompanionTheory.RSZeta.Bd_differentiable | exact GlobalTheory.CompanionTheory.RSZeta.Bd_differentiable | (intros; apply GlobalTheory.CompanionTheory.RSZeta.Bd_differentiable <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentiablePartialZetaIntegralStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical
open Ad3 Ad3.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.differentiable_partial_zeta_integral : ∀ (μ : Measure G2) (𝓕 : Set G2) (mK : Measure KA) (𝓓 : Set Jd) (H : G2 → ℂ) (Φ : (Fin 2 → 𝔸[ℚ]) → ℂ) (c : HeckeCharacter ℚ),
  Ad3.R.G3 → Set0 μ 𝓕 mK 𝓓 → Aut H → Φ ∈ Adele2.schwartzBruhat2 ℚ → Differentiable ℂ (GlobalTheory.CompanionTheory.RSZeta.Zp μ 𝓕 H c Φ) := by
  first | exact @GlobalTheory.CompanionTheory.RSZeta.differentiable_Zp | exact GlobalTheory.CompanionTheory.RSZeta.differentiable_Zp | (intros; apply GlobalTheory.CompanionTheory.RSZeta.differentiable_Zp <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DigitCharacterSumValuesStatement
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.digit_character_sum_values : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), Ad3.IsStd ψ → ∀ (j : ℕ) (m : ℤ),
  (0 ≤ m → ∑ c : Fin j → 𝓀[F], ((ψ (-(digitSum F j c) * (GLnLocal.uniformizer F : F) ^ m) : Circle) : ℂ) = (qF F : ℂ) ^ j) ∧
  (m < 0 → -m ≤ j → ∑ c : Fin j → 𝓀[F], ((ψ (-(digitSum F j c) * (GLnLocal.uniformizer F : F) ^ m) : Circle) : ℂ) = 0) := by
  first | exact @GlobalTheory.CompanionTheory.LFUDom.charsum | exact GlobalTheory.CompanionTheory.LFUDom.charsum | (intros; apply GlobalTheory.CompanionTheory.LFUDom.charsum <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleComplexClassSurjectiveStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.double_complex_class_surjective : ∀ {R : Type} [CommRing R] (K : DCx.{w} R) (a j : ℕ), (∀ p q, a < q → Subsingleton ((K.col p).H q)) →
    Function.Surjective (clsZ K (a + j) j) := by
  first | exact @GlobalTheory.CompanionTheory.CechSerre.clsZ_surjective_of_acyclic | exact GlobalTheory.CompanionTheory.CechSerre.clsZ_surjective_of_acyclic | (intros; apply GlobalTheory.CompanionTheory.CechSerre.clsZ_surjective_of_acyclic <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleComplexClassZeroOfLeadZeroStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.double_complex_class_zero_of_lead_zero : ∀ {R : Type} [CommRing R] (K : DCx.{w} R) (a j : ℕ), (∀ p q, q < a → Subsingleton ((K.col p).H q)) →
    ∀ z : Zf K (a + j) j, leadE K j a z = 0 → clsZ K (a + j) j z = 0 := by
  first | exact @GlobalTheory.CompanionTheory.RowInj.clsZ_eq_zero_of_leadE | exact GlobalTheory.CompanionTheory.RowInj.clsZ_eq_zero_of_leadE | (intros; apply GlobalTheory.CompanionTheory.RowInj.clsZ_eq_zero_of_leadE <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleComplexLeadSurjectiveStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.double_complex_lead_surjective : ∀ {R : Type} [CommRing R] (K : DCx.{w} R) (a j : ℕ), (∀ p q, q < a → Subsingleton ((K.col p).H q)) →
    Function.Surjective (leadE K j a (n := a + j)) := by
  first | exact @GlobalTheory.CompanionTheory.CechSerre.leadE_surjective | exact GlobalTheory.CompanionTheory.CechSerre.leadE_surjective | (intros; apply GlobalTheory.CompanionTheory.CechSerre.leadE_surjective <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleComplexLeadZeroOfClassZeroStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.double_complex_lead_zero_of_class_zero : ∀ {R : Type} [CommRing R] (K : DCx.{w} R) (a j : ℕ), (∀ p q, a < q → Subsingleton ((K.col p).H q)) →
    ∀ z : Zf K (a + j) j, clsZ K (a + j) j z = 0 → leadE K j a z = 0 := by
  first | exact @GlobalTheory.CompanionTheory.CechSerre.RowKer.leadE_eq_zero | exact GlobalTheory.CompanionTheory.CechSerre.RowKer.leadE_eq_zero | (intros; apply GlobalTheory.CompanionTheory.CechSerre.RowKer.leadE_eq_zero <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleComplexMapLeadCompatStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.double_complex_map_lead_compat : ∀ {R : Type} [CommRing R] (K L : DCx.{1} R) (φ : DCx.Hom K L (RingHom.id R)) (a j : ℕ) (z : Zf K (a + j) j),
    ∃ z' : Zf L (a + j) j, clsZ L (a + j) j z' = φ.tot.mapH (a + j) (clsZ K (a + j) j z) ∧
      ∃ (y : (L.col j).H a) (hy : (colH L a).d j y = 0) (y₀ : (K.col j).H a) (hy₀ : (colH K a).d j y₀ = 0),
        leadE K j a z = (colH K a).cls y₀ hy₀ ∧ leadE L j a z' = (colH L a).cls y hy ∧ y = (φ.col j).mapH a y₀ := by
  first | exact @GlobalTheory.CompanionTheory.CechSerre.leadE_map | exact GlobalTheory.CompanionTheory.CechSerre.leadE_map | (intros; apply GlobalTheory.CompanionTheory.CechSerre.leadE_map <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualFWeightLe
section
open MeasureTheory

namespace GlobalTheory.CompanionTheory.Parseval

lemma geom_real (p q r s ζ N D : ℝ) (hD : D = p * s - q * r) (hD0 : D ≠ 0) (hN : 0 ≤ N)
    (h0 : |(s * ζ - r) / D| ≤ N) (h1 : |(p - q * ζ) / D| ≤ N) :
    ((1 + N) ^ 2)⁻¹ ≤ 4 * ((1 + |ζ - (p * q + r * s) / (q ^ 2 + s ^ 2)| /
      (|D| / Real.sqrt (q ^ 2 + s ^ 2))) ^ 2)⁻¹ := by
  have hm : 0 < q ^ 2 + s ^ 2 := by
    rcases eq_or_ne q 0 with hq | hq
    · rcases eq_or_ne s 0 with hs | hs
      · exact absurd (by rw [hD, hq, hs]; ring) hD0
      · positivity
    · positivity
  obtain ⟨m, hmdef⟩ : ∃ m, m = q ^ 2 + s ^ 2 := ⟨_, rfl⟩
  obtain ⟨l, hldef⟩ : ∃ l, l = (p * q + r * s) / (q ^ 2 + s ^ 2) := ⟨_, rfl⟩
  rw [← hldef, ← hmdef]
  rw [← hmdef] at hm
  obtain ⟨t, htdef⟩ : ∃ t, t = |ζ - l| / (|D| / Real.sqrt m) := ⟨_, rfl⟩
  rw [← htdef]
  have ht0 : 0 ≤ t := by rw [htdef]; positivity
  have hD2 : 0 < D ^ 2 := by positivity
  have ht2 : t ^ 2 = (ζ - l) ^ 2 * m / D ^ 2 := by
    rw [htdef, div_pow, div_pow, sq_abs, sq_abs, Real.sq_sqrt hm.le]
    field_simp
  have hid : (s * ζ - r) ^ 2 + (p - q * ζ) ^ 2 = m * (ζ - l) ^ 2 + D ^ 2 / m := by
    rw [hldef, ← hmdef]
    have hm' : m ≠ 0 := hm.ne'
    field_simp
    rw [hD, hmdef]
    ring
  have hx : ((s * ζ - r) / D) ^ 2 ≤ N ^ 2 := sq_le_sq.2 (by rwa [abs_of_nonneg hN])
  have hy : ((p - q * ζ) / D) ^ 2 ≤ N ^ 2 := sq_le_sq.2 (by rwa [abs_of_nonneg hN])
  have hsum : ((s * ζ - r) / D) ^ 2 + ((p - q * ζ) / D) ^ 2 = t ^ 2 + 1 / m := by
    rw [div_pow, div_pow, ← add_div, hid, ht2]
    field_simp
  have hinv : 0 < 1 / m := by positivity
  have ht4 : t ^ 2 ≤ 2 * N ^ 2 := by linarith
  have ht : t ≤ 2 * N := by
    by_contra hc
    push_neg at hc
    nlinarith
  have hle : (1 + t) ^ 2 ≤ 4 * (1 + N) ^ 2 := by nlinarith
  rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  linarith

theorem dualF_weight_le : ∀ (h : Ad3.LR.M22) (ζ : ℝ), (Matrix.of h).det ≠ 0 →
    ((1 + ‖GlobalTheory.CompanionTheory.Parseval.dualF h ζ‖) ^ 2)⁻¹ ≤ 4 * GlobalTheory.CompanionTheory.Parseval.wt
      (|(Matrix.of h).det| / Real.sqrt (h 0 1 ^ 2 + h 1 1 ^ 2))
      ((h 0 0 * h 0 1 + h 1 0 * h 1 1) / (h 0 1 ^ 2 + h 1 1 ^ 2)) ζ := by
  intro h ζ hD
  have hdet : (Matrix.of h).det = h 0 0 * h 1 1 - h 0 1 * h 1 0 := by
    rw [Matrix.det_fin_two]
    rfl
  have h0 := norm_le_pi_norm (dualF h ζ) 0
  have h1 := norm_le_pi_norm (dualF h ζ) 1
  rw [Real.norm_eq_abs] at h0 h1
  exact geom_real (h 0 0) (h 0 1) (h 1 0) (h 1 1) ζ _ _ hdet hD (norm_nonneg _) h0 h1

end GlobalTheory.CompanionTheory.Parseval
end

