import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRadNMulLevM
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0614
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0639
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0641
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanLocalIntegral
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
import Formalism.RealPlaceAnalysis.Bundle0004
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0011
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AutomorphicSpectrum.PublishedTheorems.PublishedGlobalResults.HasInfCharOfIsRegAlg
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteSpectrumGLTwoOfCuspidalSpectrum
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ClozelPurity.EopV
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0632
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0592
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CanonicalShuffleCountProduct
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0607
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0615
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartCompactSupportContinuous
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0597

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsDetUnipotentRadicalEqOne
section
noncomputable section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.CompanionTheory.QKAvg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.QKAvg

theorem absDet_radN (D : D7) (B W : HSp D) (t : ℕ) (d : HypDec B W t) :
    ∀ n ∈ radN d, GlobalTheory.RegSW.absDet d n = 1 := by
  intro n hn
  obtain ⟨c, b, hcb⟩ := hn
  have hX : mt B (n : GA D B) ⬝ d.jX = d.jX := by
    rw [hcb, mt_mul, Matrix.mul_assoc, d.nB_jX, d.nC_jX]
  have hon : GlobalTheory.RegSW.onX d n = 1 := by
    apply Units.ext
    rw [GlobalTheory.RegSW.eq_of_mul_jX d (GlobalTheory.RegSW.mul_jX d n), hX, d.pX_jX, Units.val_one]
  simp only [GlobalTheory.RegSW.absDet, MonoidHom.comp_apply, hon, map_one]

end GlobalTheory.CompanionTheory.QKAvg
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsIntegralTranslatesBound
section
noncomputable section

open MeasureTheory Complex Set
open Ad3 Ad3.LR Ad3.LR.C

namespace GlobalTheory.CompanionTheory.AbsWm

open GlobalTheory.CompanionTheory.WmFE (jj nn)

lemma re_I_nn_div (g : Matrix (Fin 2) (Fin 2) ℝ) :
    (I * nn g / jj g).re = g.det / normSq (jj g) := by
  rw [Complex.div_re]
  simp [nn, jj, Matrix.det_fin_two]
  ring

lemma norm_exp_kernel (g : Matrix (Fin 2) (Fin 2) ℝ) (a : ℝ) :
    ‖Complex.exp (-2 * Real.pi * I * ((a : ℂ) * nn g / jj g))‖ =
      Real.exp (-(2 * Real.pi * (a * g.det) / normSq (jj g))) := by
  rw [Complex.norm_exp]
  congr 1
  have h : -2 * (Real.pi : ℂ) * I * ((a : ℂ) * nn g / jj g) =
      ((-2 * Real.pi * a : ℝ) : ℂ) * (I * nn g / jj g) := by
    push_cast
    ring
  rw [h, Complex.re_ofReal_mul, re_I_nn_div]
  ring

lemma norm_Wm (k : ℕ) (g : Matrix (Fin 2) (Fin 2) ℝ) (a : ℝ) (h : 0 < a * g.det) :
    ‖Wm k (d2 a * g)‖ = (a * g.det) ^ ((2 * (k : ℝ) - 1) / 2) *
      normSq (jj g) ^ (-((2 * (k : ℝ) - 1) / 2)) *
      Real.exp (-(2 * Real.pi * (a * g.det) / normSq (jj g))) := by
  rw [GlobalTheory.CompanionTheory.WmFE.real_whittaker_torus_mul k g a h, norm_mul, norm_mul, norm_exp_kernel, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg h.le _), norm_zpow]
  congr 2
  rw [normSq_eq_norm_sq, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), ← Real.rpow_intCast]
  congr 1
  push_cast
  ring

lemma integrand_eq (k : ℕ) (σ : ℝ) (g : Matrix (Fin 2) (Fin 2) ℝ) (ε : ℝ)
    (hε : ε = 1 ∨ ε = -1) (hD : 0 < ε * g.det) (x : ℝ) (hx : 0 < x) :
    x⁻¹ * (‖Wm k (d2 (ε * x) * g)‖ * |ε * x| ^ (σ - 1 / 2)) =
      (|g.det| ^ ((2 * (k : ℝ) - 1) / 2) * normSq (jj g) ^ (-((2 * (k : ℝ) - 1) / 2))) *
      (x ^ ((k : ℝ) - 1 + σ - 1) *
        Real.exp (-(2 * Real.pi * |g.det| / normSq (jj g) * x))) := by
  have habs : |ε * x| = x := by
    rcases hε with rfl | rfl <;> simp [abs_of_pos hx]
  have hE : ε * g.det = |g.det| := by
    have h1 : |ε * g.det| = |g.det| := by
      rcases hε with rfl | rfl <;> simp
    rw [← h1, abs_of_pos hD]
  have ha : ε * x * g.det = x * |g.det| := by
    rw [← hE]
    ring
  have hpos : 0 < ε * x * g.det := by
    rw [ha]
    exact mul_pos hx (by rw [← hE]; exact hD)
  have hx1 : x ^ ((k : ℝ) - 1 + σ - 1) =
      x⁻¹ * (x ^ ((2 * (k : ℝ) - 1) / 2) * x ^ (σ - 1 / 2)) := by
    rw [← Real.rpow_add hx, ← Real.rpow_neg_one, ← Real.rpow_add hx]
    congr 1
    ring
  have harg : 2 * Real.pi * (x * |g.det|) / normSq (jj g) =
      2 * Real.pi * |g.det| / normSq (jj g) * x := by
    ring
  rw [norm_Wm k g _ hpos, ha, habs, Real.mul_rpow hx.le (abs_nonneg _), harg, hx1]
  ring

lemma mulR_reduce (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (f : ℝ → ℝ) (hf : ∀ x, ε * x < 0 → f x = 0)
    (hi : IntegrableOn (fun x : ℝ => x⁻¹ * f (ε * x)) (Ioi 0)) :
    Integrable (fun a : ℝˣ => f a) mulR ∧
      ∫ a : ℝˣ, f a ∂mulR = ∫ x in Ioi (0 : ℝ), x⁻¹ * f (ε * x) := by
  have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  constructor
  · let H : ℝ → ℝ := fun x => |x|⁻¹ * f (ε * x)
    have hHon : IntegrableOn H (Ioi 0) := by
      refine hi.congr_fun (fun x hx => ?_) measurableSet_Ioi
      simp [H, abs_of_pos (mem_Ioi.1 hx)]
    have hsupp : Function.support H ⊆ Ioi 0 := by
      intro x hx
      by_contra hn
      have hx0 : x ≤ 0 := not_lt.1 hn
      apply hx
      rcases hx0.lt_or_eq with h | h
      · have : ε * (ε * x) < 0 := by rw [← mul_assoc, hεε, one_mul]; exact h
        simp [H, hf _ this]
      · simp [H, h]
    have hH : Integrable H := (integrableOn_iff_integrable_of_support_subset hsupp).1 hHon
    have hH2 : Integrable (fun x : ℝ => H (ε * x)) := by
      rcases hε with rfl | rfl
      · simpa using hH
      · simpa using hH.comp_neg
    have hH3 : Integrable (fun x : ℝ => |x|⁻¹ * f x) := by
      refine hH2.congr (ae_of_all _ fun x => ?_)
      have h1 : |ε * x| = |x| := by rcases hε with rfl | rfl <;> simp
      simp only [H, h1, ← mul_assoc, hεε, one_mul]
    have hC : Integrable (fun x : ℝ => |x|⁻¹ • ((f x : ℝ) : ℂ)) := by
      refine hH3.ofReal.congr (ae_of_all _ fun x => ?_)
      simp
    have hU := (GlobalTheory.CompanionTheory.RealTateConv.integrable_mulR_iff (fun x => ((f x : ℝ) : ℂ))).2 hC
    simpa using hU.re
  · have h := GlobalTheory.CompanionTheory.WmFE.integral_mulR_eps ε hε (fun x => ((f x : ℝ) : ℂ))
      (fun x hx => by simp [hf x hx])
    have e : ∀ x : ℝ, (x : ℂ)⁻¹ * ((f (ε * x) : ℝ) : ℂ) = ((x⁻¹ * f (ε * x) : ℝ) : ℂ) := by
      intro x
      push_cast
      rfl
    simp only [e] at h
    rw [integral_complex_ofReal, integral_complex_ofReal] at h
    exact_mod_cast h

theorem abs_integral_weight_translates : Ad3.LR.C.AbsoluteZetaIntegralBound := by
  intro k hk σ h0 h1
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hA : 0 < (k : ℝ) - 1 + σ := by linarith
  refine ⟨Real.Gamma ((k : ℝ) - 1 + σ) * (2 * Real.pi) ^ (-((k : ℝ) - 1 + σ)), fun g hg => ?_⟩
  obtain ⟨ε, hε, hD⟩ : ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ 0 < ε * g.det := by
    rcases lt_or_gt_of_ne hg with h | h
    · exact ⟨-1, Or.inr rfl, by linarith⟩
    · exact ⟨1, Or.inl rfl, by linarith⟩
  have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hN : 0 < normSq (jj g) := normSq_pos.2 (GlobalTheory.CompanionTheory.WmFE.jj_ne hg)
  have hDa : 0 < |g.det| := abs_pos.2 hg
  have hc : 0 < 2 * Real.pi * |g.det| / normSq (jj g) := by positivity
  let f : ℝ → ℝ := fun x => ‖Wm k (d2 x * g)‖ * |x| ^ (σ - 1 / 2)
  have hf : ∀ x, ε * x < 0 → f x = 0 := by
    intro x hx
    have hneg : ¬ 0 < x * g.det := by
      have h2 : x * g.det = (ε * x) * (ε * g.det) := by
        calc x * g.det = (ε * ε) * (x * g.det) := by rw [hεε, one_mul]
          _ = _ := by ring
      rw [h2]
      exact not_lt.2 (mul_neg_of_neg_of_pos hx hD).le
    simp [f, GlobalTheory.CompanionTheory.WmFE.real_whittaker_torus_mul_zero k g x hneg]
  have hcongr : ∀ x ∈ Ioi (0 : ℝ), x⁻¹ * f (ε * x) =
      (|g.det| ^ ((2 * (k : ℝ) - 1) / 2) * normSq (jj g) ^ (-((2 * (k : ℝ) - 1) / 2))) *
      (x ^ ((k : ℝ) - 1 + σ - 1) *
        Real.exp (-(2 * Real.pi * |g.det| / normSq (jj g) * x))) :=
    fun x hx => integrand_eq k σ g ε hε hD x hx
  have hi : IntegrableOn (fun x : ℝ => x⁻¹ * f (ε * x)) (Ioi 0) := by
    have hb := GlobalTheory.CompanionTheory.WmFE.integrableOn_rpow_exp (σ := (k : ℝ) - 1 + σ - 1) (by linarith) hc
    exact IntegrableOn.congr_fun (hb.const_mul _) (fun x hx => (hcongr x hx).symm) measurableSet_Ioi
  obtain ⟨r1, r2⟩ := mulR_reduce ε hε f hf hi
  refine ⟨r1, ?_⟩
  have hNR : normSq (jj g) = g 1 0 ^ 2 + g 1 1 ^ 2 := by
    simp [jj, Complex.normSq_apply]
    ring
  have hinv : (1 / (2 * Real.pi * |g.det| / normSq (jj g))) ^ ((k : ℝ) - 1 + σ) =
      (2 * Real.pi) ^ (-((k : ℝ) - 1 + σ)) * |g.det| ^ (-((k : ℝ) - 1 + σ)) *
        normSq (jj g) ^ ((k : ℝ) - 1 + σ) := by
    have h2 : 1 / (2 * Real.pi * |g.det| / normSq (jj g)) =
        (2 * Real.pi)⁻¹ * |g.det|⁻¹ * normSq (jj g) := by
      field_simp
    have hp : 0 < 2 * Real.pi := by positivity
    rw [h2, Real.mul_rpow (by positivity) hN.le, Real.mul_rpow (by positivity) (by positivity),
      Real.inv_rpow hp.le, Real.inv_rpow hDa.le, Real.rpow_neg hp.le, Real.rpow_neg hDa.le]
  have hD1 : |g.det| ^ (1 / 2 - σ) =
      |g.det| ^ ((2 * (k : ℝ) - 1) / 2) * |g.det| ^ (-((k : ℝ) - 1 + σ)) := by
    rw [← Real.rpow_add hDa]
    congr 1
    ring
  have hN1 : normSq (jj g) ^ ((2 * σ - 1) / 2) =
      normSq (jj g) ^ (-((2 * (k : ℝ) - 1) / 2)) * normSq (jj g) ^ ((k : ℝ) - 1 + σ) := by
    rw [← Real.rpow_add hN]
    congr 1
    ring
  rw [show (∫ a : ℝˣ, ‖Wm k (d2 a * g)‖ * |(a : ℝ)| ^ (σ - 1 / 2) ∂mulR) =
      ∫ a : ℝˣ, f a ∂mulR from rfl, r2, setIntegral_congr_fun measurableSet_Ioi hcongr,
    integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi hA hc, hinv, ← hNR, hD1, hN1]
  ring

end GlobalTheory.CompanionTheory.AbsWm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbscissaConvergenceIdentity
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

namespace GlobalTheory.CompanionTheory.ColumnSplitting.GramAct

theorem ip_mt {D : D7} {a b : ℕ} (V : HSp D) (g : GA D V) (x : Mx D V.rank a) (y : Mx D V.rank b) :
    ip V (mm (mt V g) x) (mm (mt V g) y) = ip V x y := by
  have hu : adj (mt V g) * (gA V * mt V g) = gA V := mt_unitary V g
  unfold ip mm
  rw [adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA V), ← Matrix.mul_assoc (adj (mt V g)), hu]

theorem acEq : AcEq := by
  intro D r t V b₀ g z
  have h12 : ip V (ac V g z).1 (ac V g z).2 = ip V z.1 z.2 := ip_mt V g z.1 z.2
  have h22 : ip V (ac V g z).2 (ac V g z).2 = ip V z.2 z.2 := ip_mt V g z.2 z.2
  have hy : yv V b₀ (ac V g z) = yv V b₀ z := by
    unfold yv
    rw [h12]
  refine ⟨ip_mt V g z.1 z.1, hy, ?_⟩
  unfold qv
  rw [h22, hy]

end GlobalTheory.CompanionTheory.ColumnSplitting.GramAct

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanLocalIntegralStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_local_integral : Ad3.R.E5 := by
  first | exact @GlobalTheory.CompanionTheory.RealArchimedeanCharacter.E5 | exact GlobalTheory.CompanionTheory.RealArchimedeanCharacter.E5 | (intros; apply GlobalTheory.CompanionTheory.RealArchimedeanCharacter.E5 <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanTateIntegralStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_tate_integral : Ad3.LR.C.TateInt := by
  first | exact @GlobalTheory.CompanionTheory.RealTateConv.tateInt | exact GlobalTheory.CompanionTheory.RealTateConv.tateInt | (intros; apply GlobalTheory.CompanionTheory.RealTateConv.tateInt <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AuxiliaryCuspLemmaStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.aux_statement_20 : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ π : CuspSub E a, (∀ τ : E →+* ℂ, ∃ m, π.HasInfChar τ m) → ∃ s : ℂ, GlobalTheory.DiscSpec.IsNormalised (π.twist (GlobalTheory.CuspRep.Model.absC E s)) := by
  first | exact @GlobalTheory.CompanionTheory.Clozel.exists_twist_isNormalised | exact GlobalTheory.CompanionTheory.Clozel.exists_twist_isNormalised | (intros; apply GlobalTheory.CompanionTheory.Clozel.exists_twist_isNormalised <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundaryZetaTermFunctionalEquation
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical
open Ad3 Ad3.R

namespace GlobalTheory.CompanionTheory.RSZeta

theorem restrict_Dt_two_null {μ : Measure G2} {𝓕 : Set G2} {mK : Measure KA} {𝓓 : Set Jd}
    (hG : Ad3.R.G1a) (h0 : Set0 μ 𝓕 mK 𝓓) : (μ.restrict 𝓕) {g | Dt g ∈ ({2} : Set ℝ)} = 0 := by
  obtain ⟨h1, hz, hT⟩ := hG μ 𝓕 mK 𝓓 h0
  obtain ⟨z, hz2, -⟩ := hz 2 (by norm_num)
  have hinv := (hT (fun g => dg2 z z * g) (Or.inr (Or.inr ⟨z, rfl⟩))).1
  have hS : MeasurableSet {g : G2 | Dt g ∈ ({2} : Set ℝ)} := measurable_Dt (measurableSet_singleton _)
  have hS1 : MeasurableSet {g : G2 | Dt g = 1} := measurable_Dt (measurableSet_singleton (1 : ℝ))
  have key := hinv (Set.indicator {g : G2 | Dt g ∈ ({2} : Set ℝ)} (fun _ => (1 : ℝ≥0∞)))
    (measurable_const.indicator hS) (linv_ind (fun _ _ => rfl) _)
  have e1 : (fun g : G2 => Set.indicator {g : G2 | Dt g ∈ ({2} : Set ℝ)} (fun _ => (1 : ℝ≥0∞)) (dg2 z z * g))
      = Set.indicator {g : G2 | Dt g = 1} (fun _ => (1 : ℝ≥0∞)) := by
    funext g
    have : (dg2 z z * g ∈ {g : G2 | Dt g ∈ ({2} : Set ℝ)}) ↔ g ∈ {g : G2 | Dt g = 1} := by
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, Dt_dg, hz2]
      constructor <;> intro h <;> linarith
    by_cases hg : g ∈ {g : G2 | Dt g = 1}
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (this.2 hg)]
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg (this.1 h))]
  rw [e1, lintegral_indicator_const hS1, lintegral_indicator_const hS, one_mul, one_mul] at key
  rw [← key]
  exact le_antisymm ((Measure.restrict_apply_le _ _).trans h1.le) bot_le

theorem Bd_reflect : ∀ (μ : Measure G2) (𝓕 : Set G2) (mK : Measure KA) (𝓓 : Set Jd) (H : G2 → ℂ) (c : HeckeCharacter ℚ),
    Ad3.R.G1a → Set0 μ 𝓕 mK 𝓓 → Aut H → IsOfFinOrder c → ∀ s : ℂ,
      GlobalTheory.CompanionTheory.RSZeta.Bd μ 𝓕 H c⁻¹ (-s) = 2 ^ (-s) * GlobalTheory.CompanionTheory.RSZeta.Bd μ 𝓕 H c s := by
  intro μ 𝓕 mK 𝓓 H c hG h0 hH hc s
  have hnull2 := restrict_Dt_two_null hG h0
  obtain ⟨h1, hz, hT⟩ := hG μ 𝓕 mK 𝓓 h0
  obtain ⟨z, hz2, hzc⟩ := hz (1 / 2) (by norm_num)
  have hzc := hzc c hc
  set w : G2 → ℂ := fun g => H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ s with hw
  set w' : G2 → ℂ := fun g => H g * cdet c⁻¹ g * ((Dt g : ℝ) : ℂ) ^ (-s) with hw'
  have mS : ∀ A : Set ℝ, MeasurableSet A → MeasurableSet {g : G2 | Dt g ∈ A} := fun A hA => measurable_Dt hA
  have hband : band = {g : G2 | Dt g ∈ Set.Ico (1 : ℝ) 2} := rfl
  have mB : MeasurableSet band := hband ▸ mS _ measurableSet_Ico

  have b1 : Bd μ 𝓕 H c⁻¹ (-s) = ∫ g in 𝓕, Set.indicator {g : G2 | Dt g ∈ Set.Ico (1 : ℝ) 2} w' g ∂μ := by
    rw [setIntegral_indicator (mS _ measurableSet_Ico)]; rfl
  have b2 : Bd μ 𝓕 H c s = ∫ g in 𝓕, Set.indicator {g : G2 | Dt g ∈ Set.Ico (1 : ℝ) 2} w g ∂μ := by
    rw [setIntegral_indicator (mS _ measurableSet_Ico)]; rfl

  have r1 := (hT Ad3.R.inv2 (Or.inl rfl)).2 (Set.indicator {g : G2 | Dt g ∈ Set.Ico (1 : ℝ) 2} w')
    ((measurable_w hH c⁻¹ (-s)).indicator (mS _ measurableSet_Ico)) (linv_ind (linv_w hH c⁻¹ (-s)) _)
  have e1 : (fun g : G2 => Set.indicator {g : G2 | Dt g ∈ Set.Ico (1 : ℝ) 2} w' (Ad3.R.inv2 g))
      = Set.indicator {g : G2 | Dt g ∈ Set.Ioc (1 / 2 : ℝ) 1} w := by
    funext g
    have hp := Dt_pos g
    have hm : (Ad3.R.inv2 g ∈ {g : G2 | Dt g ∈ Set.Ico (1 : ℝ) 2}) ↔ g ∈ {g : G2 | Dt g ∈ Set.Ioc (1 / 2 : ℝ) 1} := by
      simp only [Set.mem_setOf_eq, Set.mem_Ico, Set.mem_Ioc, module_det_inverse_twist]
      rw [one_le_inv₀ hp, inv_lt_comm₀ hp (by norm_num)]
      constructor
      · rintro ⟨a, b⟩; exact ⟨by norm_num at b ⊢; linarith, a⟩
      · rintro ⟨a, b⟩; exact ⟨b, by norm_num at a ⊢; linarith⟩
    have hv : w' (Ad3.R.inv2 g) = w g := by
      simp only [hw, hw', Aut.inv2 hH, character_det_inverse_twist, module_cpow_det_inverse_twist, inv_inv, neg_neg]
    by_cases hg : g ∈ {g : G2 | Dt g ∈ Set.Ioc (1 / 2 : ℝ) 1}
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (hm.2 hg), hv]
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg (hm.1 h))]

  have r2 := (hT (fun g => dg2 z z * g) (Or.inr (Or.inr ⟨z, rfl⟩))).2
    (Set.indicator {g : G2 | Dt g ∈ Set.Ioc (1 / 2 : ℝ) 1} w)
    ((measurable_w hH c s).indicator (mS _ measurableSet_Ioc)) (linv_ind (linv_w hH c s) _)
  have hhalf : (((1 / 2 : ℝ) : ℝ) : ℂ) ^ s = 2 ^ (-s) := by
    have : (((1 / 2 : ℝ) : ℝ) : ℂ) = (2 : ℂ)⁻¹ := by push_cast; norm_num
    rw [this, Complex.inv_cpow _ _ (by simpa using Real.pi_pos.ne), Complex.cpow_neg]
  have e2 : (fun g : G2 => Set.indicator {g : G2 | Dt g ∈ Set.Ioc (1 / 2 : ℝ) 1} w (dg2 z z * g))
      = fun g => 2 ^ (-s) * Set.indicator {g : G2 | Dt g ∈ Set.Ioc (1 : ℝ) 2} w g := by
    funext g
    have hm : (dg2 z z * g ∈ {g : G2 | Dt g ∈ Set.Ioc (1 / 2 : ℝ) 1}) ↔ g ∈ {g : G2 | Dt g ∈ Set.Ioc (1 : ℝ) 2} := by
      simp only [Set.mem_setOf_eq, Set.mem_Ioc, Dt_dg, hz2]
      constructor
      · rintro ⟨a, b⟩; exact ⟨by linarith, by linarith⟩
      · rintro ⟨a, b⟩; exact ⟨by linarith, by linarith⟩
    have hv : w (dg2 z z * g) = 2 ^ (-s) * w g := by
      simp only [hw]
      rw [hH.cen, cdet_dg c z hzc, cpow_dg, hz2, hhalf]
      ring
    by_cases hg : g ∈ {g : G2 | Dt g ∈ Set.Ioc (1 : ℝ) 2}
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (hm.2 hg), hv]
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg (hm.1 h)), mul_zero]

  have ae1 : ∀ᵐ g ∂(μ.restrict 𝓕), Dt g ≠ 1 :=
    ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 h1)
  have ae2 : ∀ᵐ g ∂(μ.restrict 𝓕), Dt g ≠ 2 := by
    have := measure_eq_zero_iff_ae_notMem.1 hnull2
    simpa using this
  have r3 : ∫ g in 𝓕, Set.indicator {g : G2 | Dt g ∈ Set.Ioc (1 : ℝ) 2} w g ∂μ
      = ∫ g in 𝓕, Set.indicator {g : G2 | Dt g ∈ Set.Ico (1 : ℝ) 2} w g ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [ae1, ae2] with g g1 g2
    have hm : g ∈ {g : G2 | Dt g ∈ Set.Ioc (1 : ℝ) 2} ↔ g ∈ {g : G2 | Dt g ∈ Set.Ico (1 : ℝ) 2} := by
      simp only [Set.mem_setOf_eq, Set.mem_Ioc, Set.mem_Ico]
      constructor
      · rintro ⟨a, b⟩; exact ⟨a.le, lt_of_le_of_ne b g2⟩
      · rintro ⟨a, b⟩; exact ⟨lt_of_le_of_ne a (Ne.symm g1), b.le⟩
    by_cases hg : g ∈ {g : G2 | Dt g ∈ Set.Ioc (1 : ℝ) 2}
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (hm.1 hg)]
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg (hm.2 h))]
  rw [b1, b2, ← r1, e1, ← r2, e2, integral_const_mul, r3]

end GlobalTheory.CompanionTheory.RSZeta

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CanonicalSegmentsReverseOrderedStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonical_segments_reverse_ordered : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {h : ℕ} (Γ : Fin h → Segment k), IsCanon Γ → IsRevOrdered Γ := by
  first | exact @GlobalTheory.CompanionTheory.Canon.isRevOrdered_of_isCanon | exact GlobalTheory.CompanionTheory.Canon.isRevOrdered_of_isCanon | (intros; apply GlobalTheory.CompanionTheory.Canon.isRevOrdered_of_isCanon <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CanonicalShuffleCountProductStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonical_shuffle_count_product : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {h : ℕ} (Γ : Fin h → Segment k), IsCanon Γ → shuffleCount (List.ofFn fun i => decWord (Γ i)).flatten (fun i => decWord (Γ i)) = ∏ i, (Finset.univ.filter fun j => j ≤ i ∧ Γ j = Γ i).card := by
  first | exact @GlobalTheory.CompanionTheory.WordCount.shuffleCount_canon | exact GlobalTheory.CompanionTheory.WordCount.shuffleCount_canon | (intros; apply GlobalTheory.CompanionTheory.WordCount.shuffleCount_canon <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapacityEquivalenceStatement
section
open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capacity_equivalence : GlobalTheory.CompanionTheory.EGlue.CapEquiv := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.capEquiv | exact GlobalTheory.CompanionTheory.EGlue.capEquiv | (intros; apply GlobalTheory.CompanionTheory.EGlue.capEquiv <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralCharacterIntegralPropertiesStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.central_character_integral_properties : Ad3.R.G1a → Ad3.R.G1 := by
  first | exact @GlobalTheory.CompanionTheory.FundamentalDomainCentralCharacter.fundamental_domain_integral_central_vanishing | exact GlobalTheory.CompanionTheory.FundamentalDomainCentralCharacter.fundamental_domain_integral_central_vanishing | (intros; apply GlobalTheory.CompanionTheory.FundamentalDomainCentralCharacter.fundamental_domain_integral_central_vanishing <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartCompactSupportContinuousStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_compact_support_continuous : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ) (φ : (Fin (n + 1) → Fin (M + 2) → R ⊗[F] E) → ℝ), Continuous φ → HasCompactSupport φ → tsupport φ ⊆ freeCell (R ⊗[F] E) M n → Continuous (fun p : (Fin 1 → Fin (M + 2) → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) => φ (chartS R σ J p.1 p.2.1 p.2.2.1 p.2.2.2)) ∧ HasCompactSupport (fun p : (Fin 1 → Fin (M + 2) → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) => φ (chartS R σ J p.1 p.2.1 p.2.2.1 p.2.2.2)) ∧ ∀ p ∈ tsupport (fun p : (Fin 1 → Fin (M + 2) → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) => φ (chartS R σ J p.1 p.2.1 p.2.2.1 p.2.2.2)), IsUnit (p.1 0 0) ∧ LinearIndependent (R ⊗[F] E) p.2.2.2 := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStage.ChartTest.test_chart | exact GlobalTheory.CompanionTheory.WeilSiegel.HypStage.ChartTest.test_chart | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypStage.ChartTest.test_chart <;> assumption)
end

