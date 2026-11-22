import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0632
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0614
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0519
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0242
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0346
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0641
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0480
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.SSmoothW
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0576
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankinSelbergMeromorphicContinuation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FintypeResidue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0601

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableOnLowerZetaIntegrand
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical
open Ad3 Ad3.R

namespace GlobalTheory.CompanionTheory.RSZeta

def dyShell (n : ℕ) : Set ℝ := {x | x * 2 ^ n ∈ Set.Ico (1 : ℝ) 2}

theorem measurableSet_dyShell (n : ℕ) : MeasurableSet (dyShell n) :=
  (measurable_id.mul_const ((2 : ℝ) ^ n)) measurableSet_Ico

theorem exists_mem_dyShell {x : ℝ} (h0 : 0 < x) (h1 : x < 1) : ∃ n : ℕ, x ∈ dyShell (n + 1) := by
  have hex : ∃ m : ℕ, 1 ≤ x * 2 ^ m := by
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt x⁻¹ (one_lt_two : (1 : ℝ) < 2)
    refine ⟨m, ?_⟩
    have := mul_lt_mul_of_pos_left hm h0
    rw [mul_inv_cancel₀ h0.ne'] at this
    exact this.le
  have hspec := Nat.find_spec hex
  have hne : Nat.find hex ≠ 0 := by
    intro h
    rw [h] at hspec
    simp at hspec
    linarith
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hne
  have hmin : ¬ 1 ≤ x * 2 ^ k := Nat.find_min hex (by omega)
  rw [hk] at hspec
  refine ⟨k, hspec, ?_⟩
  have : x * 2 ^ (k + 1) = 2 * (x * 2 ^ k) := by ring
  show x * 2 ^ (k + 1) < 2
  rw [this]
  linarith [not_le.1 hmin]

def lowW (H : G2 → ℂ) (σ : ℝ) (g : G2) : ℝ≥0∞ := ‖H g‖ₑ * ENNReal.ofReal (Dt g ^ σ)

theorem measurable_lowW {H : G2 → ℂ} (hH : Aut H) (σ : ℝ) : Measurable (lowW H σ) :=
  hH.cont.measurable.enorm.mul (ENNReal.measurable_ofReal.comp (measurable_Dt.pow_const σ))

theorem linv_lowW {H : G2 → ℂ} (hH : Aut H) (σ : ℝ) : LInv (lowW H σ) := fun γ g => by
  simp only [lowW, hH.left γ g, Dt_dia]

theorem lowW_dg {H : G2 → ℂ} (hH : Aut H) (σ : ℝ) {z : Jd} (hz : md z ^ 2 = 1 / 2) (g : G2) :
    lowW H σ (dg2 z z * g) = ENNReal.ofReal ((1 / 2 : ℝ) ^ σ) * lowW H σ g := by
  simp only [lowW, hH.cen z g, Dt_dg, hz]
  rw [Real.mul_rpow (by norm_num) (Dt_pos g).le, ENNReal.ofReal_mul (by positivity)]
  ring

def lowS (H : G2 → ℂ) (σ : ℝ) (n : ℕ) : G2 → ℝ≥0∞ := Set.indicator {g | Dt g ∈ dyShell n} (lowW H σ)

theorem measurable_lowS {H : G2 → ℂ} (hH : Aut H) (σ : ℝ) (n : ℕ) : Measurable (lowS H σ n) :=
  (measurable_lowW hH σ).indicator (measurable_Dt (measurableSet_dyShell n))

theorem lowS_dg {H : G2 → ℂ} (hH : Aut H) (σ : ℝ) {z : Jd} (hz : md z ^ 2 = 1 / 2) (n : ℕ) (g : G2) :
    lowS H σ (n + 1) (dg2 z z * g) = ENNReal.ofReal ((1 / 2 : ℝ) ^ σ) * lowS H σ n g := by
  have hm : Dt (dg2 z z * g) ∈ dyShell (n + 1) ↔ Dt g ∈ dyShell n := by
    have e : 1 / 2 * Dt g * 2 ^ (n + 1) = Dt g * 2 ^ n := by ring
    simp only [dyShell, Set.mem_setOf_eq, Dt_dg, hz, e]
  by_cases h : Dt g ∈ dyShell n
  · rw [lowS, lowS, Set.indicator_of_mem (show dg2 z z * g ∈ {g | Dt g ∈ dyShell (n + 1)} from hm.2 h),
      Set.indicator_of_mem (show g ∈ {g | Dt g ∈ dyShell n} from h), lowW_dg hH σ hz]
  · rw [lowS, lowS, Set.indicator_of_notMem (show dg2 z z * g ∉ {g | Dt g ∈ dyShell (n + 1)} from fun h' => h (hm.1 h')),
      Set.indicator_of_notMem (show g ∉ {g | Dt g ∈ dyShell n} from h), mul_zero]

theorem lintegral_lowS_zero {μ : Measure G2} {𝓕 : Set G2} {mK : Measure KA} {𝓓 : Set Jd} {H : G2 → ℂ}
    (h0 : Set0 μ 𝓕 mK 𝓓) (hH : Aut H) {σ : ℝ} (hσ : 0 < σ) :
    ∫⁻ g in 𝓕, lowS H σ 0 g ∂μ < ∞ := by
  obtain ⟨C, hC⟩ := hH.bdd
  have hb : MeasurableSet band := by
    have : band = {g | Dt g ∈ Set.Ico (1 : ℝ) 2} := rfl
    rw [this]
    exact measurable_Dt measurableSet_Ico
  have hle : ∀ g, lowS H σ 0 g ≤ Set.indicator band (fun _ => ENNReal.ofReal (C * 2 ^ σ)) g := by
    intro g
    have hiff : g ∈ {g | Dt g ∈ dyShell 0} ↔ g ∈ band := by
      show Dt g * 2 ^ 0 ∈ Set.Ico (1 : ℝ) 2 ↔ (1 ≤ Dt g ∧ Dt g < 2)
      simp
    by_cases h : g ∈ band
    · have hs := hiff.2 h
      rw [lowS, Set.indicator_of_mem hs, Set.indicator_of_mem h, lowW]
      have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC g)
      rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul (norm_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul (hC g)
        (Real.rpow_le_rpow (Dt_pos g).le h.2.le hσ.le) (by have := Dt_pos g; positivity) hC0)
    · have hs : g ∉ {g | Dt g ∈ dyShell 0} := fun h' => h (hiff.1 h')
      rw [lowS, Set.indicator_of_notMem hs, Set.indicator_of_notMem h]
  calc ∫⁻ g in 𝓕, lowS H σ 0 g ∂μ
      ≤ ∫⁻ g in 𝓕, Set.indicator band (fun _ => ENNReal.ofReal (C * 2 ^ σ)) g ∂μ :=
        lintegral_mono hle
    _ = ENNReal.ofReal (C * 2 ^ σ) * μ (𝓕 ∩ band) := by
        rw [lintegral_indicator hb, setLIntegral_const, Measure.restrict_apply hb, Set.inter_comm band 𝓕]
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top h0.vol

theorem lintegral_lowS_succ {μ : Measure G2} {𝓕 : Set G2} {mK : Measure KA} {𝓓 : Set Jd} {H : G2 → ℂ}
    (hG : Ad3.R.G1a) (h0 : Set0 μ 𝓕 mK 𝓓) (hH : Aut H) (σ : ℝ) {z : Jd} (hz : md z ^ 2 = 1 / 2) (n : ℕ) :
    ∫⁻ g in 𝓕, lowS H σ (n + 1) g ∂μ = ENNReal.ofReal ((1 / 2 : ℝ) ^ σ) * ∫⁻ g in 𝓕, lowS H σ n g ∂μ := by
  have hT := ((hG μ 𝓕 mK 𝓓 h0).2.2 (fun g => dg2 z z * g) (Or.inr (Or.inr ⟨z, rfl⟩))).1 (lowS H σ (n + 1))
    (measurable_lowS hH σ (n + 1)) (linv_ind (linv_lowW hH σ) (dyShell (n + 1)))
  rw [← hT, ← lintegral_const_mul _ (measurable_lowS hH σ n)]
  exact lintegral_congr fun g => lowS_dg hH σ hz n g

theorem lintegral_lowW_lt_top {μ : Measure G2} {𝓕 : Set G2} {mK : Measure KA} {𝓓 : Set Jd} {H : G2 → ℂ}
    (hG : Ad3.R.G1a) (h0 : Set0 μ 𝓕 mK 𝓓) (hH : Aut H) {σ : ℝ} (hσ : 0 < σ) :
    ∫⁻ g in 𝓕 ∩ {g | Dt g < 1}, lowW H σ g ∂μ < ∞ := by
  obtain ⟨z, hz, -⟩ := (hG μ 𝓕 mK 𝓓 h0).2.1 (1 / 2) (by norm_num)
  set q : ℝ≥0∞ := ENNReal.ofReal ((1 / 2 : ℝ) ^ σ) with hq
  have hq1 : q < 1 := by
    rw [hq, ENNReal.ofReal_lt_one]
    exact Real.rpow_lt_one (by norm_num) (by norm_num) hσ
  have hpow : ∀ n, ∫⁻ g in 𝓕, lowS H σ n g ∂μ = q ^ n * ∫⁻ g in 𝓕, lowS H σ 0 g ∂μ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [lintegral_lowS_succ hG h0 hH σ hz n, ih, pow_succ']; ring
  have hS : MeasurableSet {g : G2 | Dt g < 1} := measurable_Dt measurableSet_Iio
  have hle : ∀ g, Set.indicator {g : G2 | Dt g < 1} (lowW H σ) g ≤ ∑' n, lowS H σ n g := by
    intro g
    by_cases h : g ∈ {g : G2 | Dt g < 1}
    · obtain ⟨n, hn⟩ := exists_mem_dyShell (Dt_pos g) h
      rw [Set.indicator_of_mem h]
      refine le_trans (le_of_eq ?_) (ENNReal.le_tsum (n + 1))
      rw [lowS, Set.indicator_of_mem (show g ∈ {g | Dt g ∈ dyShell (n + 1)} from hn)]
    · rw [Set.indicator_of_notMem h]
      exact zero_le
  calc ∫⁻ g in 𝓕 ∩ {g | Dt g < 1}, lowW H σ g ∂μ
      = ∫⁻ g in 𝓕, Set.indicator {g : G2 | Dt g < 1} (lowW H σ) g ∂μ := by
        rw [lintegral_indicator hS, Measure.restrict_restrict hS, Set.inter_comm 𝓕]
    _ ≤ ∫⁻ g in 𝓕, ∑' n, lowS H σ n g ∂μ := lintegral_mono hle
    _ = ∑' n, ∫⁻ g in 𝓕, lowS H σ n g ∂μ :=
        lintegral_tsum fun n => (measurable_lowS hH σ n).aemeasurable
    _ = (∑' n, q ^ n) * ∫⁻ g in 𝓕, lowS H σ 0 g ∂μ := by
        rw [tsum_congr hpow, ENNReal.tsum_mul_right]
    _ < ∞ := by
        refine ENNReal.mul_lt_top ?_ (lintegral_lowS_zero h0 hH hσ)
        rw [ENNReal.tsum_geometric]
        exact ENNReal.inv_lt_top.2 (tsub_pos_of_lt hq1)

theorem integrableOn_low (μ : Measure G2) (𝓕 : Set G2) (mK : Measure KA) (𝓓 : Set Jd) (H : G2 → ℂ)
    (c : HeckeCharacter ℚ) (hG : Ad3.R.G1a) (h0 : Set0 μ 𝓕 mK 𝓓) (hH : Aut H) (_hc : IsOfFinOrder c)
    (s : ℂ) (hs : 0 < s.re) :
    IntegrableOn (fun g => H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ s) (𝓕 ∩ {g | Dt g < 1}) μ := by
  refine ⟨(measurable_w hH c s).aestronglyMeasurable, ?_⟩
  have hn : ∀ g, ‖H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ s‖ₑ = lowW H s.re g := by
    intro g
    rw [enorm_mul, enorm_mul, lowW, ← ofReal_norm_eq_enorm (cdet c g), norm_cdet,
      ← ofReal_norm_eq_enorm (((Dt g : ℝ) : ℂ) ^ s), Complex.norm_cpow_eq_rpow_re_of_pos (Dt_pos g)]
    simp
  rw [HasFiniteIntegral]
  simp_rw [hn]
  exact lintegral_lowW_lt_top hG h0 hH hs

end GlobalTheory.CompanionTheory.RSZeta
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrablePowerWeightReal
section
open MeasureTheory

namespace GlobalTheory.CompanionTheory.RealTateConv

theorem abs_rpow_le_two_rpow_mul_one_add_abs_rpow (r : ℝ) {x : ℝ} (hx : 1 < |x|) :
    |x| ^ r ≤ (2 : ℝ) ^ |r| * (1 + |x|) ^ r := by
  have hx0 : 0 < |x| := by linarith
  have h1x : 0 < 1 + |x| := by linarith
  rcases le_or_gt 0 r with hr | hr
  · have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ |r| := Real.one_le_rpow (by norm_num) (abs_nonneg r)
    have h3 : |x| ^ r ≤ (1 + |x|) ^ r := Real.rpow_le_rpow hx0.le (by linarith) hr
    have h4 : 0 ≤ (1 + |x|) ^ r := Real.rpow_nonneg h1x.le r
    nlinarith
  · have h3 : (2 * |x|) ^ r ≤ (1 + |x|) ^ r :=
      Real.rpow_le_rpow_of_nonpos h1x (by linarith) hr.le
    rw [Real.mul_rpow (by norm_num) hx0.le] at h3
    have h5 : (2 : ℝ) ^ |r| * (2 : ℝ) ^ r = 1 := by
      rw [abs_of_neg hr, ← Real.rpow_add (by norm_num)]
      simp
    have h6 : (0 : ℝ) ≤ (2 : ℝ) ^ |r| := by positivity
    calc |x| ^ r = (2 : ℝ) ^ |r| * ((2 : ℝ) ^ r * |x| ^ r) := by
          rw [← mul_assoc, h5, one_mul]
      _ ≤ (2 : ℝ) ^ |r| * (1 + |x|) ^ r := mul_le_mul_of_nonneg_left h3 h6

theorem integrable_abs_rpow_mul_one_add_abs_rpow :
    ∀ (r N : ℝ), -1 < r → r + 1 < N →
      MeasureTheory.Integrable (fun x : ℝ => |x| ^ r * (1 + |x|) ^ (-N)) := by
  intro r N hr hN
  have hG : Integrable (fun x : ℝ => (Set.Icc (-1 : ℝ) 1).indicator (fun x => |x| ^ r) x +
      (2 : ℝ) ^ |r| * (1 + ‖x‖) ^ (-(N - r))) :=
    ((integrableOn_abs_rpow hr).integrable_indicator measurableSet_Icc).add
      ((integrable_one_add_norm (by simp; linarith)).const_mul _)
  have hm : AEStronglyMeasurable (fun x : ℝ => |x| ^ r * (1 + |x|) ^ (-N)) volume :=
    ((measurable_abs.pow_const r).mul
      ((measurable_const.add measurable_abs).pow_const _)).aestronglyMeasurable
  refine hG.mono' hm (ae_of_all _ fun x => ?_)
  have h1x : 0 < 1 + |x| := by positivity
  have hA : 0 ≤ |x| ^ r := Real.rpow_nonneg (abs_nonneg x) r
  have hB : 0 ≤ (1 + |x|) ^ (-N) := Real.rpow_nonneg h1x.le _
  rw [Real.norm_of_nonneg (mul_nonneg hA hB)]
  have hC : 0 ≤ (2 : ℝ) ^ |r| * (1 + ‖x‖) ^ (-(N - r)) := by positivity
  by_cases hx : x ∈ Set.Icc (-1 : ℝ) 1
  · rw [Set.indicator_of_mem hx]
    have h1 : (1 + |x|) ^ (-N) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg x]) (by linarith)
    nlinarith
  · rw [Set.indicator_of_notMem hx, zero_add, Real.norm_eq_abs,
      show -(N - r) = r + -N by ring, Real.rpow_add h1x, ← mul_assoc]
    have hx1 : 1 < |x| := by
      by_contra h
      exact hx (abs_le.1 (not_lt.1 h))
    exact mul_le_mul_of_nonneg_right (abs_rpow_le_two_rpow_mul_one_add_abs_rpow r hx1) hB

end GlobalTheory.CompanionTheory.RealTateConv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableSchwartzAHaar
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.CompanionTheory.WSum
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WSum

theorem integrable_schwartzA_haar : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n : ℕ) (μ : Measure (Mx D m n))
    [μ.IsAddHaarMeasure] (φ : Mx D m n → ℂ), φ ∈ schwartzA θ m n → Integrable φ μ := by
  intro D θ hθ m n μ _ φ hφ
  induction hφ using Submodule.span_induction with
  | mem φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    haveI : IsModuleTopology (Af D.host.F) (GlobalTheory.RegSch.IkSchwartz.AEf D) := ⟨rfl⟩
    haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
    haveI : IsTopologicalRing (GlobalTheory.RegSch.IkSchwartz.AEf D) := IsModuleTopology.isTopologicalRing (Af D.host.F) _
    haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele D.host.F
    haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele D.host.F
    haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField D.host.F
    obtain ⟨e0⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E) (Af D.host.F)
    haveI : LocallyCompactSpace (GlobalTheory.RegSch.IkSchwartz.AEf D) := e0.isClosedEmbedding.locallyCompactSpace
    haveI : SecondCountableTopology (GlobalTheory.RegSch.IkSchwartz.AEf D) := e0.secondCountableTopology
    haveI : T2Space (GlobalTheory.RegSch.IkSchwartz.AEf D) := e0.isEmbedding.t2Space
    letI : MeasurableSpace (Fin m → Fin n → GlobalTheory.RegSch.IkSchwartz.AEf D) := borel _
    haveI : BorelSpace (Fin m → Fin n → GlobalTheory.RegSch.IkSchwartz.AEf D) := ⟨rfl⟩
    haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
    haveI := (GlobalTheory.TowerRestrict.lattice_Mx D m n).1
    obtain ⟨e, he⟩ := GlobalTheory.RegSch.IkSchwartz.exists_split hθ m n
    let μr : Measure (D.what₂.Tau → Fin m → Fin n → ℂ) := Measure.addHaar
    let ν : Measure (Fin m → Fin n → GlobalTheory.RegSch.IkSchwartz.AEf D) := Measure.addHaar
    obtain ⟨c, hc⟩ := GlobalTheory.PartialIntegral.exists_integral_split e μ μr ν
    have h := (hc f g (f.integrable) (hg.1.continuous.integrable_of_hasCompactSupport hg.2)).1
    simpa only [he] using h
  | zero => exact integrable_zero _ _ _
  | add φ ψ _ _ h1 h2 => exact h1.add h2
  | smul c φ _ h => exact h.smul c

end GlobalTheory.CompanionTheory.WSum

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableThetaKernelFibers
section
noncomputable section

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

namespace GlobalTheory.CompanionTheory.ColumnSplitting.Form

theorem continuous_jn_pair {D : D7} {a r t n : ℕ} (hn : r + t = n) :
    Continuous fun z : Mx D a r × Mx D a t => jn hn z.1 z.2 := by
  unfold jn
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Matrix.submatrix_apply, id]
  cases (finSumFinEquiv.trans (finCongr hn)).symm j with
  | inl c => simpa using continuous_fst.matrix_elem i c
  | inr c => simpa using continuous_snd.matrix_elem i c

theorem continuous_yv_pair {D : D7} {r t : ℕ} (V : HSp D) (b₀ : HermE D r) :
    Continuous (yv (t := t) V b₀) := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  unfold yv ip
  exact continuous_const.matrix_mul ((continuous_adj.comp continuous_fst).matrix_mul
    (continuous_const.matrix_mul continuous_snd))

theorem nuT_form : ZpEq → AcEq → JnPi → Ext0 → Fub4 → ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t)
    (hn : W.rank + t = n) (I : IkD d n) θ, IsInfFam θ → ∀ (μ : Measure (Mx D W.rank t)), μ.IsAddHaarMeasure →
    ∀ (b₀ : HermE D W.rank), b₀.1.det ≠ 0 → ∀ x₀, gramQ W x₀ = b₀.1 → ∀ Φ ∈ schwartzA θ B.rank n,
    ∀ η ∈ schwartzA θ W.rank t, Integrable (core hn I x₀ Φ η) (I.νK.prod (Q0 I μ)) →
    Integrable (fun z => Φ (jn hn z.1 z.2) * conj (η (yv B b₀ z))) (nuT hn I μ x₀) ∧
    ∫ z, Φ (jn hn z.1 z.2) * conj (η (yv B b₀ z)) ∂(nuT hn I μ x₀) =
      ∫ y, orb W I.m (ikp I fun X => Φ (mm X (bl hn 1 y 0 1))) (ext0 hn x₀) * conj (η y) ∂μ := by
  intro hZ hA hJ hE hF D n t B W d hn I θ hθ μ hμ b₀ hb x₀ hx Φ hΦ η hη hint
  obtain ⟨g1, g2⟩ := top_pair (D := D) B.rank W.rank t
  obtain ⟨-, -, p3, -, p5⟩ := top_mx (D := D) B.rank W.rank
  obtain ⟨-, -, p3', -, p5'⟩ := top_mx (D := D) B.rank t
  have hΦc := (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ _ _ Φ hΦ).1
  have hηc := (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ _ _ η hη).1
  have hGc : Continuous fun z : Mx D B.rank W.rank × Mx D B.rank t =>
      Φ (jn hn z.1 z.2) * conj (η (yv B b₀ z)) :=
    (hΦc.comp (continuous_jn_pair hn)).mul
      (Complex.continuous_conj.comp (hηc.comp (continuous_yv_pair B b₀)))
  have hπ := measurable_pi hn I x₀
  have hcomp : (fun z : Mx D B.rank W.rank × Mx D B.rank t => Φ (jn hn z.1 z.2) * conj (η (yv B b₀ z))) ∘
      (fun p : I.l.K × Par D n t W => ac B ((p.1 : GA D B)⁻¹) (zp d hn x₀ p.2)) = core hn I x₀ Φ η := by
    funext p
    obtain ⟨k, q⟩ := p
    simp only [Function.comp, core]
    rw [hJ D n t B W d hn x₀ _ q, (hA D W.rank t B b₀ _ _).2.1, (hZ D n t B W d hn b₀ hb x₀ hx q).2.1]
  refine ⟨?_, ?_⟩
  · unfold nuT
    rw [integrable_map_measure hGc.aestronglyMeasurable hπ.aemeasurable, hcomp]
    exact hint
  · have e1 : ∫ z, Φ (jn hn z.1 z.2) * conj (η (yv B b₀ z)) ∂(nuT hn I μ x₀) =
        ∫ p, core hn I x₀ Φ η p ∂(I.νK.prod (Q0 I μ)) := by
      unfold nuT
      rw [integral_map hπ.aemeasurable hGc.aestronglyMeasurable, ← hcomp]
      rfl
    rw [e1]
    obtain ⟨-, i2, i3, i4, i5⟩ := top_mx (D := D) t n
    obtain ⟨-, j2, j3, j4, j5⟩ := top_mx (D := D) W.rank t
    obtain ⟨-, k2, k3, -, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
    have : BorelSpace (GA D W) := ⟨rfl⟩
    obtain ⟨hc, 𝓕, hf⟩ := I.cov₁
    have := hf.1
    have := I.haar
    have := I.probK
    have e2 := (hF I.l.K (GA D W) (Mx D t n) (Mx D W.rank t) I.νK I.m I.μ₁ μ).1 _ hint
    unfold Q0
    rw [e2]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    simp only [core]
    simp_rw [integral_mul_const]
    congr 1
    unfold orb
    refine integral_congr_ae (ae_of_all _ fun h => ?_)
    simp only [hE D n t W hn x₀ h, ikp, ikS, projS, XU]
    refine integral_congr_ae (ae_of_all _ fun u => integral_congr_ae (ae_of_all _ fun k => ?_))
    simp only [mm, Matrix.mul_assoc]

end GlobalTheory.CompanionTheory.ColumnSplitting.Form

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableZFOfBound
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.LFGInt

open Ad3

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem summable_cut {p r C B : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hr0 : 0 < r) (hr1 : r < 1) :
    Summable fun k : ℤ => ‖(((if p ^ k ≤ B then C * r ^ k else 0 : ℝ) : ℂ))‖ := by
  set f : ℤ → ℝ := fun k => ‖(((if p ^ k ≤ B then C * r ^ k else 0 : ℝ) : ℂ))‖ with hf
  have hpos : Summable fun n : ℕ => f n := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
      ((summable_geometric_of_lt_one hr0.le hr1).mul_left |C|)
    simp only [hf]
    split_ifs
    · simp [abs_mul, abs_of_pos hr0]
    · simp only [Complex.ofReal_zero, norm_zero]
      positivity
  have hneg : Summable fun n : ℕ => f (-(n : ℤ)) := by
    have ht := tendsto_pow_atTop_atTop_of_one_lt (one_lt_inv₀ hp0 |>.mpr hp1)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (ht.eventually (Filter.eventually_gt_atTop B))
    refine summable_of_ne_finset_zero (s := Finset.range N) fun n hn => ?_
    have hn' : N ≤ n := by simpa using hn
    have hB : ¬ p ^ (-(n : ℤ)) ≤ B := by
      rw [_root_.zpow_neg, zpow_natCast, ← inv_pow]
      exact not_le.mpr (hN n hn')
    simp only [hf, if_neg hB, Complex.ofReal_zero, norm_zero]
  exact Summable.of_nat_of_neg hpos hneg

variable [MeasurableSpace F] [BorelSpace F]

end GlobalTheory.CompanionTheory.LFGInt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralMatrixRowRepExists
section
noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.LFUDom

section AntiTranspose

variable {R : Type*} [CommRing R]

def antiTr (A : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 2) (Fin 2) R :=
  !![A 1 1, A 0 1; A 1 0, A 0 0]

theorem antiTr_mul (A B : Matrix (Fin 2) (Fin 2) R) : antiTr (A * B) = antiTr B * antiTr A := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [antiTr, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem antiTr_one : antiTr (1 : Matrix (Fin 2) (Fin 2) R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [antiTr]

theorem antiTr_antiTr (A : Matrix (Fin 2) (Fin 2) R) : antiTr (antiTr A) = A := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [antiTr]

def antiTrGL (g : GL (Fin 2) R) : GL (Fin 2) R where
  val := antiTr (g : Matrix (Fin 2) (Fin 2) R)
  inv := antiTr ((g⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R)
  val_inv := by rw [← antiTr_mul, Units.inv_mul, antiTr_one]
  inv_val := by rw [← antiTr_mul, Units.mul_inv, antiTr_one]

theorem coe_antiTrGL (g : GL (Fin 2) R) :
    (antiTrGL g : Matrix (Fin 2) (Fin 2) R) = antiTr (g : Matrix (Fin 2) (Fin 2) R) := rfl

theorem antiTrGL_mul (x y : GL (Fin 2) R) : antiTrGL (x * y) = antiTrGL y * antiTrGL x :=
  Units.ext (antiTr_mul _ _)

theorem antiTrGL_inv (x : GL (Fin 2) R) : antiTrGL x⁻¹ = (antiTrGL x)⁻¹ :=
  Units.ext rfl

theorem antiTrGL_antiTrGL (x : GL (Fin 2) R) : antiTrGL (antiTrGL x) = x :=
  Units.ext (antiTr_antiTr _)

end AntiTranspose

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem antiTr_entries_mem {A : Matrix (Fin 2) (Fin 2) F} (hA : ∀ a b, A a b ∈ 𝒪[F]) (a b : Fin 2) :
    antiTr A a b ∈ 𝒪[F] := by
  fin_cases a <;> fin_cases b <;> simpa [antiTr] using hA _ _

theorem antiTrGL_mem_integralGL {x : GL (Fin 2) F} (hx : x ∈ integralGL F 2) :
    antiTrGL x ∈ integralGL F 2 := by
  obtain ⟨h1, h2⟩ := (mem_integralGL_iff F 2).1 hx
  refine (mem_integralGL_iff F 2).2 ⟨fun a b => antiTr_entries_mem h1 a b, fun a b => ?_⟩
  rw [← antiTrGL_inv]
  exact antiTr_entries_mem h2 a b

theorem antiTrGL_rowRep (l : Fin 2 → ℕ) (c : NormalData F l) :
    antiTrGL (rowRep (l 1) (l 0) (c ⟨(0, 1), by decide⟩)) = normalGL F l c := by
  refine Units.ext ?_
  rw [coe_antiTrGL, coe_rowRep, coe_normalGL]
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [antiTr] using (normalMat_self l c 0).symm
  · simpa [antiTr] using (normalMat_of_lt l c (i := 0) (j := 1) (by decide)).symm
  · simpa [antiTr] using (normalMat_of_gt l c (i := 1) (j := 0) (by decide)).symm
  · simpa [antiTr] using (normalMat_self l c 1).symm

theorem exists_mul_rowRep_inv_mem (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (g : GL (Fin 2) F)
    (hg : ∀ a b, (g : Matrix (Fin 2) (Fin 2) F) a b ∈ 𝒪[F]) :
    ∃ (i j : ℕ) (c : Fin j → 𝓀[F]), g * (rowRep i j c)⁻¹ ∈ integralGL F 2 := by
  obtain ⟨l, c, hc⟩ := exists_normalGL (g := antiTrGL g) (fun a b => antiTr_entries_mem hg a b)
  have h1 : (normalGL F l c)⁻¹ * antiTrGL g ∈ integralGL F 2 := QuotientGroup.eq.1 hc
  refine ⟨l 1, l 0, c ⟨(0, 1), by decide⟩, ?_⟩
  have h2 : antiTrGL (g * (rowRep (l 1) (l 0) (c ⟨(0, 1), by decide⟩))⁻¹) ∈ integralGL F 2 := by
    rw [antiTrGL_mul, antiTrGL_inv, antiTrGL_rowRep]
    exact h1
  have h3 := antiTrGL_mem_integralGL h2
  rwa [antiTrGL_antiTrGL] at h3

end GlobalTheory.CompanionTheory.LFUDom
end
end

