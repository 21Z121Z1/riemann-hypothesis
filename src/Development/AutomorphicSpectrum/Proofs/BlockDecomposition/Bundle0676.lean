import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.UnipotentTateFunctionalEquation
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0653
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0656
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0519
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0641
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FintypeResidue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0601
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0655
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0642
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0646
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0658
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0616
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0657
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0580
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRadNMulLevM
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.Bundle0001

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableCatPhase
section
open MeasureTheory

noncomputable section

namespace GlobalTheory.CompanionTheory.Parseval.Ibp

open Ad3 Ad3.LR

def dirY (j : Fin 2) : M23 := fun r c => if r = j ∧ c = 2 then 1 else 0

def phase (ξ y : Fin 2 → ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ((ξ 0 * y 0 + ξ 1 * y 1 : ℝ) : ℂ))

lemma cat_add_smul (A : M22) (y : Fin 2 → ℝ) (j : Fin 2) (t : ℝ) :
    cat A (y + t • Pi.single j (1 : ℝ)) = cat A y + t • dirY j := by
  funext r c
  fin_cases j <;> fin_cases r <;> fin_cases c <;> simp [cat, dirY]

lemma continuous_cat (A : M22) : Continuous (cat A) := by
  refine continuous_pi fun r => continuous_pi fun c => ?_
  fin_cases c
  · simpa [cat] using continuous_const
  · simpa [cat] using continuous_const
  · simpa [cat] using continuous_apply r

lemma norm_le_norm_cat (A : M22) (y : Fin 2 → ℝ) : ‖y‖ ≤ ‖cat A y‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun r => ?_
  have h1 : ‖cat A y r 2‖ ≤ ‖cat A y r‖ := norm_le_pi_norm (cat A y r) 2
  have h2 : ‖cat A y r‖ ≤ ‖cat A y‖ := norm_le_pi_norm (cat A y) r
  have h3 : cat A y r 2 = y r := by simp [cat]
  rw [h3] at h1
  exact h1.trans h2

lemma integrable_cat (Φ : Sw) (A : M22) : Integrable (fun y : Fin 2 → ℝ => Φ (cat A y)) := by
  set C : ℝ := 2 ^ 3 * ((Finset.Iic ((3, 0) : ℕ × ℕ)).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2) Φ
  have hint : Integrable (fun y : Fin 2 → ℝ => C * (1 + ‖y‖) ^ (-(3 : ℝ))) :=
    (integrable_one_add_norm (by rw [Module.finrank_fin_fun]; norm_num)).const_mul C
  refine hint.mono' (Φ.continuous.comp (continuous_cat A)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  have hb := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (3, 0)) (k := 3) (n := 0)
    le_rfl le_rfl Φ (cat A y)
  rw [norm_iteratedFDeriv_zero] at hb
  have hpos : 0 < (1 + ‖y‖) ^ 3 := by positivity
  have hle : (1 + ‖y‖) ^ 3 ≤ (1 + ‖cat A y‖) ^ 3 := by
    have := norm_le_norm_cat A y
    gcongr
  have hb' : (1 + ‖y‖) ^ 3 * ‖Φ (cat A y)‖ ≤ C :=
    (mul_le_mul_of_nonneg_right hle (norm_nonneg _)).trans hb
  have he : (1 + ‖y‖) ^ (-(3 : ℝ)) = ((1 + ‖y‖) ^ 3)⁻¹ := by
    rw [Real.rpow_neg (by positivity)]
    norm_cast
  rw [he, ← div_eq_mul_inv, le_div_iff₀ hpos]
  linarith

lemma continuous_phase (ξ : Fin 2 → ℝ) : Continuous (phase ξ) := by
  unfold phase
  fun_prop

lemma norm_phase (ξ y : Fin 2 → ℝ) : ‖phase ξ y‖ = 1 := by
  unfold phase
  have : 2 * (Real.pi : ℂ) * Complex.I * ((ξ 0 * y 0 + ξ 1 * y 1 : ℝ) : ℂ) =
      ((2 * Real.pi * (ξ 0 * y 0 + ξ 1 * y 1) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

lemma integrable_cat_phase (Φ : Sw) (A : M22) (ξ : Fin 2 → ℝ) :
    Integrable (fun y : Fin 2 → ℝ => Φ (cat A y) * phase ξ y) := by
  refine (integrable_cat Φ A).mono
    ((Φ.continuous.comp (continuous_cat A)).mul (continuous_phase ξ)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  simp [norm_phase]

lemma hasLineDerivAt_cat (Φ : Sw) (A : M22) (j : Fin 2) (y : Fin 2 → ℝ) :
    HasLineDerivAt ℝ (fun y : Fin 2 → ℝ => Φ (cat A y))
      (LineDeriv.lineDerivOp (dirY j) Φ (cat A y)) y (Pi.single j (1 : ℝ)) := by
  have h : HasFDerivAt Φ (fderiv ℝ Φ (cat A y)) (cat A y) :=
    (Φ.differentiableAt).hasFDerivAt
  have h2 := h.hasLineDerivAt (dirY j)
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  unfold HasLineDerivAt at h2 ⊢
  have e : (fun t : ℝ => Φ (cat A (y + t • Pi.single j (1 : ℝ)))) =
      fun t : ℝ => Φ (cat A y + t • dirY j) := by
    funext t; rw [cat_add_smul]
  rw [e]
  exact h2

lemma dot_add_smul (ξ y : Fin 2 → ℝ) (j : Fin 2) (t : ℝ) :
    ξ 0 * (y + t • Pi.single j (1 : ℝ) : Fin 2 → ℝ) 0 + ξ 1 * (y + t • Pi.single j (1 : ℝ) : Fin 2 → ℝ) 1 =
      (ξ 0 * y 0 + ξ 1 * y 1) + t * ξ j := by
  fin_cases j <;> simp <;> ring

lemma hasLineDerivAt_phase (ξ : Fin 2 → ℝ) (j : Fin 2) (y : Fin 2 → ℝ) :
    HasLineDerivAt ℝ (phase ξ) (2 * (Real.pi : ℂ) * Complex.I * (ξ j : ℂ) * phase ξ y) y
      (Pi.single j (1 : ℝ)) := by
  unfold HasLineDerivAt
  set a : ℝ := ξ 0 * y 0 + ξ 1 * y 1 with ha
  set c : ℂ := 2 * (Real.pi : ℂ) * Complex.I with hc
  have e : (fun t : ℝ => phase ξ (y + t • Pi.single j (1 : ℝ))) =
      fun t : ℝ => Complex.exp (c * ((a + t * ξ j : ℝ) : ℂ)) := by
    funext t
    unfold phase
    rw [dot_add_smul]
  rw [e]
  have h1 : HasDerivAt (fun t : ℝ => a + t * ξ j) (ξ j) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (ξ j)).const_add a
  have h2 : HasDerivAt (fun t : ℝ => ((a + t * ξ j : ℝ) : ℂ)) (ξ j : ℂ) 0 := h1.ofReal_comp
  have h3 := (h2.const_mul c).cexp
  have e0 : c * ((a + 0 * ξ j : ℝ) : ℂ) = c * (a : ℂ) := by simp
  rw [e0] at h3
  have e1 : c * (ξ j : ℂ) * phase ξ y = Complex.exp (c * (a : ℂ)) * (c * (ξ j : ℂ)) := by
    unfold phase
    rw [mul_comm]
  rw [e1]
  exact h3

theorem fz_lineDeriv (Φ : Sw) (j : Fin 2) (A : M22) (ξ : Fin 2 → ℝ) :
    fz (LineDeriv.lineDerivOp (dirY j) Φ) A ξ =
      -(2 * (Real.pi : ℂ) * Complex.I * (ξ j : ℂ)) * fz Φ A ξ := by
  set c : ℂ := 2 * (Real.pi : ℂ) * Complex.I * (ξ j : ℂ) with hc
  set Ψ : Sw := LineDeriv.lineDerivOp (dirY j) Φ with hΨ
  have key := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (μ := (volume : Measure (Fin 2 → ℝ))) (B := ContinuousLinearMap.mul ℝ ℂ)
    (f := fun y => Φ (cat A y)) (f' := fun y => Ψ (cat A y))
    (g := phase ξ) (g' := fun y => c * phase ξ y) (v := Pi.single j (1 : ℝ))
    (integrable_cat_phase Ψ A ξ)
    (by
      have := (integrable_cat_phase Φ A ξ).const_mul c
      refine this.congr (Filter.Eventually.of_forall fun y => ?_)
      simp only [ContinuousLinearMap.mul_apply']
      ring)
    (integrable_cat_phase Φ A ξ)
    (fun y _ => hasLineDerivAt_cat Φ A j y)
    (fun y _ => hasLineDerivAt_phase ξ j y)
  simp only [ContinuousLinearMap.mul_apply'] at key
  have e1 : fz Ψ A ξ = ∫ y, Ψ (cat A y) * phase ξ y := rfl
  have e2 : fz Φ A ξ = ∫ y, Φ (cat A y) * phase ξ y := rfl
  have e3 : ∫ y, Φ (cat A y) * (c * phase ξ y) = c * ∫ y, Φ (cat A y) * phase ξ y := by
    rw [← integral_const_mul]
    congr 1
    funext y
    ring
  rw [e1, e2]
  rw [e3] at key
  linear_combination key

theorem main : ∀ (Φ : Ad3.LR.Sw) (j : Fin 2), ∃ Ψ : Ad3.LR.Sw, ∀ (A : Ad3.LR.M22) (ξ : Fin 2 → ℝ),
    GlobalTheory.CompanionTheory.Parseval.fz Ψ A ξ =
      -(2 * (Real.pi : ℂ) * Complex.I * (ξ j : ℂ)) * GlobalTheory.CompanionTheory.Parseval.fz Φ A ξ :=
  fun Φ j => ⟨LineDeriv.lineDerivOp (dirY j) Φ, fun A ξ => fz_lineDeriv Φ j A ξ⟩

end GlobalTheory.CompanionTheory.Parseval.Ibp
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableSchwartzAHaarStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.CompanionTheory.WSum
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_of_mem_schwartzA : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n : ℕ) (μ : Measure (Mx D m n)) [μ.IsAddHaarMeasure] (φ : Mx D m n → ℂ), φ ∈ schwartzA θ m n → Integrable φ μ := by
  first | exact @GlobalTheory.CompanionTheory.WSum.integrable_schwartzA_haar | exact GlobalTheory.CompanionTheory.WSum.integrable_schwartzA_haar | (intros; apply GlobalTheory.CompanionTheory.WSum.integrable_schwartzA_haar <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableThetaKernelFibersStatement
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
theorem _root_.GlobalTheory.T.integrable_theta_kernel_fibers : ZpEq → AcEq → JnPi → Ext0 → Fub4 → ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) (I : IkD d n) θ, IsInfFam θ → ∀ (μ : Measure (Mx D W.rank t)), μ.IsAddHaarMeasure → ∀ (b₀ : HermE D W.rank), b₀.1.det ≠ 0 → ∀ x₀, gramQ W x₀ = b₀.1 → ∀ Φ ∈ schwartzA θ B.rank n, ∀ η ∈ schwartzA θ W.rank t, Integrable (core hn I x₀ Φ η) (I.νK.prod (Q0 I μ)) → Integrable (fun z => Φ (jn hn z.1 z.2) * conj (η (yv B b₀ z))) (nuT hn I μ x₀) ∧ ∫ z, Φ (jn hn z.1 z.2) * conj (η (yv B b₀ z)) ∂(nuT hn I μ x₀) = ∫ y, orb W I.m (ikp I fun X => Φ (mm X (bl hn 1 y 0 1))) (ext0 hn x₀) * conj (η y) ∂μ := by
  first | exact @GlobalTheory.CompanionTheory.ColumnSplitting.Form.nuT_form | exact GlobalTheory.CompanionTheory.ColumnSplitting.Form.nuT_form | (intros; apply GlobalTheory.CompanionTheory.ColumnSplitting.Form.nuT_form <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralMatrixRowRepExistsStatement
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_matrix_row_rep_exists : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (g : GL (Fin 2) F), (∀ a b, (g : Matrix (Fin 2) (Fin 2) F) a b ∈ 𝒪[F]) →
  ∃ (i j : ℕ) (c : Fin j → 𝓀[F]), g * (rowRep i j c)⁻¹ ∈ integralGL F 2 := by
  first | exact @GlobalTheory.CompanionTheory.LFUDom.exists_mul_rowRep_inv_mem | exact GlobalTheory.CompanionTheory.LFUDom.exists_mul_rowRep_inv_mem | (intros; apply GlobalTheory.CompanionTheory.LFUDom.exists_mul_rowRep_inv_mem <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralRightCosetDecompositionStatement
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_right_coset_decomposition : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μ] (K : Subgroup G),
  IsOpen (K : Set G) → IsCompact (K : Set G) → ∀ (ι : Type) (R : ι → G) (S : Finset ι) (f : G → ℂ),
  (∀ a b, R a * (R b)⁻¹ ∈ K → a = b) → (∀ κ ∈ K, ∀ g, f (κ * g) = f g) →
  (∀ g, f g ≠ 0 → ∃ a ∈ S, g * (R a)⁻¹ ∈ K) →
  ∫ g, f g ∂μ = ((μ.real (K : Set G) : ℝ) : ℂ) * ∑ a ∈ S, f (R a) := by
  first | exact @GlobalTheory.CompanionTheory.LFUDom.integral_eq_measure_mul_sum_cosets | exact GlobalTheory.CompanionTheory.LFUDom.integral_eq_measure_mul_sum_cosets | (intros; apply GlobalTheory.CompanionTheory.LFUDom.integral_eq_measure_mul_sum_cosets <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IpSmulRight
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L PositivityTheory.Rg.Rsw.Em
open IsDedekindDomain NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.OrbExist

variable {D : D7} {a b c n r t : ℕ}

theorem adj_rat_herm (b₀ : HermE D r) : adj (rat b₀.1) = rat b₀.1 := by
  have hb := b₀.2
  ext i j
  have h2 : D.sp.cm.sig (b₀.1 j i) = b₀.1 i j := by
    have := congrFun (congrFun hb i) j
    simpa using this
  change cA D (incA D (b₀.1 j i)) = incA D (b₀.1 i j)
  rw [← h2]
  rfl

theorem rat_inv_mul (b₀ : HermE D r) (hb : b₀.1.det ≠ 0) : mm (rat b₀.1⁻¹) (rat b₀.1) = (1 : Mx D r r) := by
  have h : b₀.1⁻¹ * b₀.1 = 1 := Matrix.nonsing_inv_mul _ (Ne.isUnit hb)
  have := congrArg (fun M : Matrix (Fin r) (Fin r) D.host.E => M.map (incA D)) h
  simpa [rat, mm, Matrix.map_mul] using this

theorem rat_mul_inv (b₀ : HermE D r) (hb : b₀.1.det ≠ 0) : mm (rat b₀.1) (rat b₀.1⁻¹) = (1 : Mx D r r) := by
  have h : b₀.1 * b₀.1⁻¹ = 1 := Matrix.mul_nonsing_inv _ (Ne.isUnit hb)
  have := congrArg (fun M : Matrix (Fin r) (Fin r) D.host.E => M.map (incA D)) h
  simpa [rat, mm, Matrix.map_mul] using this

theorem adj_ip (V : HSp D) (x : Mx D V.rank a) (y : Mx D V.rank b) : adj (ip V x y) = ip V y x := by
  unfold ip mm
  rw [adj_mul, adj_mul, adj_adj, adj_gA, Matrix.mul_assoc]

theorem adj_add_r (x y : Mx D a b) : adj (x + y) = adj x + adj y := by
  ext i j
  simp [adj]

theorem adj_one_r : adj (1 : Mx D a a) = 1 := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [adj]
  · have h' : j ≠ i := fun q => h q.symm
    simp [adj, Matrix.one_apply, h, h']

theorem adj_rat_inv (b₀ : HermE D r) (hb : b₀.1.det ≠ 0) : adj (rat b₀.1⁻¹) = rat b₀.1⁻¹ := by
  have h1 : adj (mm (rat b₀.1⁻¹) (rat b₀.1)) = 1 := by rw [rat_inv_mul b₀ hb, adj_one_r]
  have h2 : mm (rat b₀.1) (adj (rat b₀.1⁻¹)) = 1 := by
    have := h1
    simp only [mm] at this ⊢
    rwa [adj_mul, adj_rat_herm] at this
  have h3 := congrArg (fun M : Mx D r r => mm (rat b₀.1⁻¹) M) h2
  simp only [mm] at h3
  have h4 : mm (rat b₀.1⁻¹) (rat b₀.1) = (1 : Mx D r r) := rat_inv_mul b₀ hb
  simp only [mm] at h4
  rwa [← Matrix.mul_assoc, h4, Matrix.one_mul, Matrix.mul_one] at h3

theorem ip_add_right (V : HSp D) (x : Mx D V.rank a) (y y' : Mx D V.rank b) :
    ip V x (y + y') = ip V x y + ip V x y' := by
  unfold ip mm
  rw [Matrix.mul_add, Matrix.mul_add]

theorem ip_add_left (V : HSp D) (x x' : Mx D V.rank a) (y : Mx D V.rank b) :
    ip V (x + x') y = ip V x y + ip V x' y := by
  unfold ip mm
  rw [adj_add_r, Matrix.add_mul]

theorem ip_mul_right (V : HSp D) (x : Mx D V.rank a) (y : Mx D V.rank b) (w : Mx D b c) :
    ip V x (mm y w) = mm (ip V x y) w := by
  unfold ip mm
  simp only [Matrix.mul_assoc]

theorem ip_mul_left (V : HSp D) (x : Mx D V.rank a) (y : Mx D V.rank b) (w : Mx D a c) :
    ip V (mm x w) y = mm (adj w) (ip V x y) := by
  unfold ip mm
  rw [adj_mul, Matrix.mul_assoc]

theorem ip_smul_right (V : HSp D) (e : AE D) (x : Mx D V.rank a) (y : Mx D V.rank b) :
    ip V x (e • y) = e • ip V x y := by
  unfold ip mm
  rw [Matrix.mul_smul, Matrix.mul_smul]

theorem qv_mem (V : HSp D) (b₀ : HermE D r) (z : Mx D V.rank r × Mx D V.rank t) : qv V b₀ z ∈ hermA D t := by
  change adj (qv V b₀ z) = qv V b₀ z
  have hp : adj (pr b₀ (yv V b₀ z) (yv V b₀ z)) = pr b₀ (yv V b₀ z) (yv V b₀ z) := by
    have hr : (b₀.1.map (incA D)) = rat b₀.1 := rfl
    unfold pr
    rw [hr, adj_mul, adj_mul, adj_adj, adj_rat_herm, Matrix.mul_assoc]
  have hs : ∀ x y : Mx D t t, adj (x - y) = adj x - adj y := by
    intro x y
    ext i j
    simp [adj]
  unfold qv
  rw [hs, hp, adj_ip]

theorem yv_smul (V : HSp D) (b₀ : HermE D r) (e : AE D) (z : Mx D V.rank r × Mx D V.rank t) (h : e • z.2 = z.2) :
    e • yv V b₀ z = yv V b₀ z := by
  unfold yv
  conv_rhs => rw [← h, ip_smul_right]
  simp only [mm]
  rw [Matrix.mul_smul]

theorem qv_smul (V : HSp D) (b₀ : HermE D r) (e : AE D) (z : Mx D V.rank r × Mx D V.rank t) (h : e • z.2 = z.2) :
    e • qv V b₀ z = qv V b₀ z := by
  have h1 : e • ip V z.2 z.2 = ip V z.2 z.2 := by
    have := ip_smul_right V e z.2 z.2
    rw [h] at this
    exact this.symm
  have h2 : e • pr b₀ (yv V b₀ z) (yv V b₀ z) = pr b₀ (yv V b₀ z) (yv V b₀ z) := by
    unfold pr
    rw [← Matrix.mul_smul, ← Matrix.mul_smul, yv_smul V b₀ e z h]
  unfold qv
  rw [smul_sub, h1, h2]

theorem pr_add (b₀ : HermE D r) (u u' w w' : Mx D r t) :
    pr b₀ (u + u') (w + w') = pr b₀ u w + pr b₀ u w' + (pr b₀ u' w + pr b₀ u' w') := by
  unfold pr
  rw [adj_add_r, Matrix.mul_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]

theorem alg4 {M : Type} [AddCommGroup M] (c p a a' s : M) :
    c + a + (a' + s) - (p + a + (a' + s)) = c - p := by abel

theorem qv_shear (V : HSp D) (b₀ : HermE D r) (hb : b₀.1.det ≠ 0) (e : AE D) (z₁ : Mx D V.rank r) (z₂ : Mx D V.rank t)
    (y : Mx D r t) (hG : ip V z₁ z₁ = e • rat b₀.1) (hy : e • y = y) :
    qv V b₀ (z₁, z₂ + mm z₁ y) = qv V b₀ (z₁, z₂) := by
  have hr : (b₀.1.map (incA D)) = rat b₀.1 := rfl
  have hGy : mm (ip V z₁ z₁) y = mm (rat b₀.1) y := by
    rw [hG]
    simp only [mm]
    rw [Matrix.smul_mul, ← Matrix.mul_smul, hy]
  have hyv : yv V b₀ (z₁, z₂ + mm z₁ y) = yv V b₀ (z₁, z₂) + y := by
    unfold yv
    simp only
    rw [ip_add_right, ip_mul_right, hGy]
    simp only [mm]
    rw [Matrix.mul_add, ← Matrix.mul_assoc]
    have := rat_inv_mul b₀ hb
    simp only [mm] at this
    rw [this, Matrix.one_mul]
  have hPi := rat_inv_mul b₀ hb
  have hPi' := rat_mul_inv b₀ hb
  have hu : adj (yv V b₀ (z₁, z₂)) = mm (ip V z₂ z₁) (rat b₀.1⁻¹) := by
    unfold yv
    simp only [mm]
    rw [adj_mul, adj_rat_inv b₀ hb, adj_ip]
  have hpu : ∀ w : Mx D r t, pr b₀ (yv V b₀ (z₁, z₂)) w = mm (ip V z₂ z₁) w := by
    intro w
    unfold pr
    rw [hu, hr]
    simp only [mm] at hPi ⊢
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (rat b₀.1⁻¹), hPi, Matrix.one_mul]
  have hpu' : ∀ w : Mx D r t, pr b₀ w (yv V b₀ (z₁, z₂)) = mm (adj w) (ip V z₁ z₂) := by
    intro w
    unfold pr yv
    rw [hr]
    simp only [mm] at hPi' ⊢
    rw [← Matrix.mul_assoc (rat b₀.1), hPi', Matrix.one_mul]
  have hpyy : pr b₀ y y = mm (adj y) (mm (ip V z₁ z₁) y) := by
    rw [hGy, pr, hr]
  unfold qv
  rw [hyv]
  simp only
  rw [pr_add, hpu (yv V b₀ (z₁, z₂)), hpu y, hpu', hpyy, ip_add_left, ip_add_right, ip_add_right, ip_mul_left, ip_mul_left,
    ip_mul_right, ip_mul_right]
  exact alg4 _ _ _ _ _

theorem qv_col (V : HSp D) (b₀ : HermE D r) (z₁ : Mx D V.rank r) (z₂ : Mx D V.rank t) (g : Mx D t t) :
    qv V b₀ (z₁, mm z₂ g) = mm (mm (adj g) (qv V b₀ (z₁, z₂))) g := by
  have hyv : yv V b₀ (z₁, mm z₂ g) = mm (yv V b₀ (z₁, z₂)) g := by
    unfold yv
    simp only
    rw [ip_mul_right]
    simp only [mm]
    rw [Matrix.mul_assoc]
  unfold qv
  rw [hyv]
  simp only
  rw [ip_mul_left, ip_mul_right]
  unfold pr
  simp only [mm]
  rw [adj_mul, Matrix.mul_sub, Matrix.sub_mul]
  simp only [Matrix.mul_assoc]

theorem pch_conj (ψ : AddChar (AF D.host.F) ℂ) (x q h : Mx D t t) :
    pch ψ x (mm (mm (adj h) q) h) = pch ψ (mm (mm h x) (adj h)) q := by
  unfold pch
  congr 2
  simp only [mm]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

end GlobalTheory.CompanionTheory.OrbExist

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrregularProjectionImageNullStatement
section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irregular_projection_image_null : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i] (D : ℕ)
    (Ψ : GlobalTheory.CompanionTheory.MixZ.ArchEq.LinProj n D) (c : GlobalTheory.AlgChart (i ≫ mpStr ℤ m n) σ₀ D),
    volume (GlobalTheory.CompanionTheory.MixZ.ArchEq.projCoord i Ψ '' {y | y ∈ c.e.source ∧
      (∃ z, GlobalTheory.CompanionTheory.MixZ.ArchEq.Over i y z ∧ Ψ (segre z) 0 ≠ 0) ∧ ¬ GlobalTheory.CompanionTheory.MixZ.ArchEq.IsRegAt i Ψ c y}) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.ArchEq.volume_image_crit | exact GlobalTheory.CompanionTheory.MixZ.ArchEq.volume_image_crit | (intros; apply GlobalTheory.CompanionTheory.MixZ.ArchEq.volume_image_crit <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsClosedUnipotentRadicalStabilizerStatement
section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.CompanionTheory.QKAvg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosed_unipotent_radical_stabilizer : ∀ (D : D7) (B W : HSp D) (t : ℕ) (d : HypDec B W t), IsClosed (radN d : Set (GlobalTheory.RegSW.stab d)) := by
  first | exact @GlobalTheory.CompanionTheory.QKAvg.isClosed_radN | exact GlobalTheory.CompanionTheory.QKAvg.isClosed_radN | (intros; apply GlobalTheory.CompanionTheory.QKAvg.isClosed_radN <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IteratedIntegralsFourFactorsStatement
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
theorem _root_.GlobalTheory.T.iterated_integrals_four_factors : Fub4 := by
  first | exact @GlobalTheory.CompanionTheory.ColumnSplitting.iterated_integrals_four_factors_holds | exact GlobalTheory.CompanionTheory.ColumnSplitting.iterated_integrals_four_factors_holds | (intros; apply GlobalTheory.CompanionTheory.ColumnSplitting.iterated_integrals_four_factors_holds <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaDecompositionGlTwoHoldsStatement
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_decomposition_gl_two_holds : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (g : GL (Fin 2) F), ∃ (x : F) (m n : ℤ), ∃ κ ∈ GLnLocal.integralGL F 2, g = Ad3.uni2 x * Ad3.dg2 (unifUnit F ^ m) (unifUnit F ^ n) * κ := by
  first | exact @GlobalTheory.CompanionTheory.GIntIw.iwasawa_decomposition_gl_two | exact GlobalTheory.CompanionTheory.GIntIw.iwasawa_decomposition_gl_two | (intros; apply GlobalTheory.CompanionTheory.GIntIw.iwasawa_decomposition_gl_two <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaRegionMeasureBoundStatement
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_region_measure_bound : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (μ : Measure (GL (Fin 2) F)) [μ.IsMulLeftInvariant] (m n L : ℤ), IsOpen {g : GL (Fin 2) F | ∃ x : F, (modulus x : ℝ) ≤ (residueCard F : ℝ) ^ (L - m) ∧ ∃ κ ∈ GLnLocal.integralGL F 2, g = Ad3.uni2 x * Ad3.dg2 (unifUnit F ^ m) (unifUnit F ^ n) * κ} ∧ (n ≤ L → μ {g : GL (Fin 2) F | ∃ x : F, (modulus x : ℝ) ≤ (residueCard F : ℝ) ^ (L - m) ∧ ∃ κ ∈ GLnLocal.integralGL F 2, g = Ad3.uni2 x * Ad3.dg2 (unifUnit F ^ m) (unifUnit F ^ n) * κ} ≤ ENNReal.ofReal ((residueCard F : ℝ) ^ (L - n)) * μ (GLnLocal.integralGL F 2 : Set (GL (Fin 2) F))) := by
  first | exact @GlobalTheory.CompanionTheory.IwasawaShell.shell_open_volume | exact GlobalTheory.CompanionTheory.IwasawaShell.shell_open_volume | (intros; apply GlobalTheory.CompanionTheory.IwasawaShell.shell_open_volume <;> assumption)
end

