import Formalism.HermitianCurvature.HeisenbergConjugationMeasurePreserving
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0108
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRRCentre
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRRSec
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0167
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRRMatFrom
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0170
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0171
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ZeroNotMemTsupportPsiL
import Formalism.HermitianCurvature.StatementPB
import Formalism.LatticeRigidity.HeightMinimum.SqrtAbsNormLeProd

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.BXiAsm
section
namespace Formalism.FourierDecayAlt.P.BXiAsm
open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem closed_of (hX : XiExists) : LemmaBClosed := Formalism.FourierDecayAlt.P.b_lemmaBClosed_of hX

theorem norm_of (hX : XiExists) : LemmaBNorm :=
  Formalism.FourierDecayAlt.Final.lemma_b_norm_of_parts (closed_of hX) Formalism.FourierDecayAlt.Final.conjugation_invariance_all Formalism.FourierDecayAlt.Final.dilation_jacobian_all
    Formalism.FourierDecayAlt.Final.integral_bound_all

theorem any_of (hX : XiExists) : LemmaBAny :=
  Formalism.FourierDecayAlt.Final.lemma_b_from_norm_bound (norm_of hX) Formalism.FourierDecayAlt.Final.integral_norm_bound_variant_b

end Formalism.FourierDecayAlt.P.BXiAsm

namespace Formalism.FourierDecayAlt.P

theorem b_any_of_xi : Formalism.FourierDecayAlt.B2.LemmaBAny := Formalism.FourierDecayAlt.P.BXiAsm.any_of exists_auxiliary_xi

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRRotK
section
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem rotation_K_invariance_holds : GTRRotK :=
  gTRRotK_of_mat_fin_centre_sec_ode_wirt rotation_matrix_form_holds rotation_finite_from_matrix rotation_centre_condition rotation_section_holds rotation_ode_holds rotation_wirtinger_holds

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.FormModel
section
namespace Formalism.FourierDecayAlt.P.FormNormSumIdentities

open Formalism.FourierDecayAlt

noncomputable section

def FormModel : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P0 : M.Par)
    (T : D.LevTower P0.k P0.r Wp Wq) (sg : ℂ) (j : Fin (P0.r + 1)) (w : List C.Letter) (a : ℝ) (mm : ℕ)
    (ε' : ℝ) (Sg : Set (B.Mat P0.k (P0.r - j))),
    0 < ε' → P5.Auser P0 w.length + 1 ≤ a → P5.mmUser P0 w.length ≤ mm →
    5 + (2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length ≤ mm →
    (∀ γ ∈ Sg, ε' ≤ Formalism.QuantumDeterminants.Gf P0.k (P0.r - j) (T.bs j).z (T.bs j).z' γ) →
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V]
      (Mo : U.CCModel P0.k (P0.r - j) (Wd.Ix (Fin w.length) → (Wq →L[ℂ] Wp)) a mm Sg V),
      ∃ (Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (Cp : ℝ), 0 ≤ Cp ∧ (∀ u, (Bf u u).re ≤ (Cp * ‖u‖) ^ 2) ∧
        ∀ (u u' : V) (x x' : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (ε'' : ℝ), 0 < ε'' →
          (∀ e, JC.CCCoefM (T.bs j) (P5.Auser P0 w.length + 1) (P5.mmUser P0 w.length) ε'' (x e)) →
          (∀ e, JC.CCCoefM (T.bs j) (P5.Auser P0 w.length + 1) (P5.mmUser P0 w.length) ε'' (x' e)) →
          (∀ e, ∀ γ ∈ B.GV P0.k (P0.r - j), Mo.ev u γ e = x e γ) →
          (∀ e, ∀ γ ∈ B.GV P0.k (P0.r - j), Mo.ev u' γ e = x' e γ) →
          Bf u u' = D.formLev T sg j w x x'

end

end Formalism.FourierDecayAlt.P.FormNormSumIdentities
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HerAnalyticFAllOfTop
section
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerB

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA

section Top

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

end Top

def HerTopAll : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    herK S P z z' π π' L st l0 D (Fin.last P.r) ≤ TopCls X μ

def StepFormAll : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    StepDens (S := S) P z z' π π' μ L st (herK S P z z' π π' L st l0 D) l0 ∧
      FormInt S P z z' π π' μ L st l0 (herK S P z z' π π' L st l0 D)

end Formalism.FourierDecayAlt.P5.HerB
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.NormCDZPsiCLe
section
open MeasureTheory Filter Topology
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerB

section Lim

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem tendsto_int_uv_ae (I J : α → ℂ) (hI : Integrable I μ) (hJ : Integrable J μ) (u v : ℕ → α → ℂ) (M : ℝ)
    (hum : ∀ n, AEStronglyMeasurable (u n) μ) (hvm : ∀ n, AEStronglyMeasurable (v n) μ)
    (hu : ∀ n x, ‖u n x‖ ≤ 1) (hv : ∀ n x, ‖v n x‖ ≤ M) (hl : ∀ᵐ x ∂μ, ∀ᶠ n in atTop, u n x = 1 ∧ v n x = 0) :
    Tendsto (fun n => ∫ x, (u n x * I x + v n x * J x) ∂μ) atTop (𝓝 (∫ x, I x ∂μ)) := by
  refine tendsto_integral_of_dominated_convergence (fun x => ‖I x‖ + M * ‖J x‖)
    (fun n => ((hum n).mul hI.1).add ((hvm n).mul hJ.1)) (hI.norm.add (hJ.norm.const_mul M))
    (fun n => Filter.Eventually.of_forall fun x => ?_) ?_
  · calc ‖u n x * I x + v n x * J x‖ ≤ ‖u n x * I x‖ + ‖v n x * J x‖ := norm_add_le _ _
      _ ≤ 1 * ‖I x‖ + M * ‖J x‖ := by
        rw [norm_mul, norm_mul]
        exact add_le_add (mul_le_mul_of_nonneg_right (hu n x) (norm_nonneg _))
          (mul_le_mul_of_nonneg_right (hv n x) (norm_nonneg _))
      _ = ‖I x‖ + M * ‖J x‖ := by ring
  · filter_upwards [hl] with x hx
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hx] with n hn
    rw [hn.1, hn.2]
    ring

end Lim

section Main

def psiC (n : ℕ) (c : ℂ) : ℂ := ((psiL n c : ℝ) : ℂ)

theorem psiC_contDiff (n : ℕ) : ContDiff ℝ ∞ (psiC n) := Complex.ofRealCLM.contDiff.comp (psiL_contDiff n)

theorem fderiv_psiC (n : ℕ) (c : ℂ) : fderiv ℝ (psiC n) c = Complex.ofRealCLM.comp (fderiv ℝ (psiL n) c) := by
  have hd : DifferentiableAt ℝ (psiL n) c := (psiL_contDiffAt n c).differentiableAt (by simp)
  exact (Complex.ofRealCLM.hasFDerivAt.comp c hd.hasFDerivAt).fderiv

theorem norm_c_dZ_psiC_le {C : ℝ} (hC : ∀ t, ‖deriv bumpR t‖ ≤ C) (n : ℕ) (c : ℂ) :
    ‖c * NF.dZ (psiC n) c‖ ≤ C := by
  by_cases hc : c = 0
  · subst hc
    simp only [zero_mul, norm_zero]
    exact (norm_nonneg _).trans (hC 0)
  · rw [dZ_eq, fderiv_psiC, norm_mul]
    simp only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]
    have hD := norm_mul_fderiv_psiL_le hC n c hc
    have ha : ‖((fderiv ℝ (psiL n) c 1 : ℝ) : ℂ)‖ ≤ ‖fderiv ℝ (psiL n) c‖ := by
      rw [Complex.norm_real]
      simpa using (fderiv ℝ (psiL n) c).le_opNorm 1
    have hb : ‖((fderiv ℝ (psiL n) c Complex.I : ℝ) : ℂ)‖ ≤ ‖fderiv ℝ (psiL n) c‖ := by
      rw [Complex.norm_real]
      simpa using (fderiv ℝ (psiL n) c).le_opNorm Complex.I
    have hz : ‖(1 / 2 : ℂ) * (((fderiv ℝ (psiL n) c 1 : ℝ) : ℂ) -
        Complex.I * ((fderiv ℝ (psiL n) c Complex.I : ℝ) : ℂ))‖ ≤ ‖fderiv ℝ (psiL n) c‖ := by
      rw [norm_mul]
      have h3 : ‖((fderiv ℝ (psiL n) c 1 : ℝ) : ℂ) - Complex.I * ((fderiv ℝ (psiL n) c Complex.I : ℝ) : ℂ)‖ ≤
          2 * ‖fderiv ℝ (psiL n) c‖ := by
        calc _ ≤ ‖((fderiv ℝ (psiL n) c 1 : ℝ) : ℂ)‖ + ‖Complex.I * ((fderiv ℝ (psiL n) c Complex.I : ℝ) : ℂ)‖ :=
              norm_sub_le _ _
          _ ≤ ‖fderiv ℝ (psiL n) c‖ + ‖fderiv ℝ (psiL n) c‖ := by
              rw [norm_mul, Complex.norm_I, one_mul]
              exact add_le_add ha hb
          _ = 2 * ‖fderiv ℝ (psiL n) c‖ := by ring
      have h2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
      rw [h2]
      linarith
    calc ‖c‖ * _ ≤ ‖c‖ * ‖fderiv ℝ (psiL n) c‖ := mul_le_mul_of_nonneg_left hz (norm_nonneg c)
      _ ≤ C := hD

theorem psiC_eventually (c : ℂ) (hc : c ≠ 0) :
    ∀ᶠ n : ℕ in atTop, psiC n c = 1 ∧ c * NF.dZ (psiC n) c = 0 := by
  obtain ⟨N, hN⟩ := exists_nat_gt |Real.log ‖c‖|
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  have hlt : |Real.log ‖c‖| < (n : ℝ) + 1 := by
    have : (N : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hev := psiL_one_near n c hc hlt
  refine ⟨?_, ?_⟩
  · simp [psiC, hev.eq_of_nhds]
  · rw [dZ_eq, fderiv_psiC, hev.fderiv_eq]
    simp

theorem dZ_mul {φ f : ℂ → ℂ} {c : ℂ} (hφ : DifferentiableAt ℝ φ c) (hf : DifferentiableAt ℝ f c) :
    NF.dZ (fun w => φ w * f w) c = NF.dZ φ c * f c + φ c * NF.dZ f c := by
  have h : fderiv ℝ (fun w => φ w * f w) c = φ c • fderiv ℝ f c + f c • fderiv ℝ φ c := fderiv_mul hφ hf
  rw [dZ_eq, dZ_eq, dZ_eq, h]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem pLogAdj (f g : ℂ → ℂ) (hf : ContDiffOn ℝ 1 f {c | c ≠ 0}) (hg : ContDiffOn ℝ 1 g {c | c ≠ 0})
    (h0 : Integrable (fun c => f c * conj (g c) / ((‖c‖ ^ 2 : ℝ) : ℂ)))
    (h1 : Integrable (fun c => c * NF.dZ f c * conj (g c) / ((‖c‖ ^ 2 : ℝ) : ℂ)))
    (h2 : Integrable (fun c => f c * conj (conj c * NF.dZb g c) / ((‖c‖ ^ 2 : ℝ) : ℂ))) :
    ∫ c, c * NF.dZ f c * conj (g c) / ((‖c‖ ^ 2 : ℝ) : ℂ) =
      -∫ c, f c * conj (conj c * NF.dZb g c) / ((‖c‖ ^ 2 : ℝ) : ℂ) := by
  obtain ⟨C, hC⟩ := exists_deriv_bump_bound
  have hUo : IsOpen {c : ℂ | c ≠ 0} := isOpen_ne
  have hfd : ∀ c ≠ 0, DifferentiableAt ℝ f c := fun c hc =>
    (hf.differentiableOn one_ne_zero c hc).differentiableAt (hUo.mem_nhds hc)
  set F : ℕ → ℂ → ℂ := fun n c => psiC n c * f c with hF
  have hFc : ∀ n, ContDiff ℝ 1 (F n) := by
    intro n
    refine contDiff_iff_contDiffAt.mpr fun c => ?_
    by_cases hc : c = 0
    · subst hc
      refine ContDiffAt.congr_of_eventuallyEq (contDiffAt_const (c := (0 : ℂ))) ?_
      filter_upwards [psiL_zero_near0 n] with w hw
      simp [hF, psiC, hw]
    · exact ((psiC_contDiff n).contDiffAt.of_le (by simp)).mul
        ((hf.contDiffAt (hUo.mem_nhds hc)))
  have hψs : ∀ n, tsupport (psiC n) ⊆ tsupport (psiL n) := fun n =>
    tsupport_comp_subset (g := fun x : ℝ => (x : ℂ)) Complex.ofReal_zero (psiL n)
  have hFs : ∀ n, HasCompactSupport (F n) := fun n =>
    (((psiL_hasCompactSupport n).comp_left (g := fun x : ℝ => (x : ℂ)) Complex.ofReal_zero).mul_right)
  have hF0 : ∀ n, (0 : ℂ) ∉ tsupport (F n) := fun n h =>
    zero_notMem_tsupport_psiL n (hψs n ((tsupport_mul_subset_left) h))
  have key := fun n => pLogAdj_cpt (F n) g (hFc n) (hFs n) (hF0 n) hg
  have hLe : ∀ n, (fun c => c * NF.dZ (F n) c * conj (g c) / ((‖c‖ ^ 2 : ℝ) : ℂ)) = fun c =>
      psiC n c * (c * NF.dZ f c * conj (g c) / ((‖c‖ ^ 2 : ℝ) : ℂ)) +
        (c * NF.dZ (psiC n) c) * (f c * conj (g c) / ((‖c‖ ^ 2 : ℝ) : ℂ)) := by
    intro n; funext c
    by_cases hc : c = 0
    · subst hc; simp
    · have hd := dZ_mul (φ := psiC n) (f := f) (((psiC_contDiff n).differentiable (by simp)) c) (hfd c hc)
      rw [show NF.dZ (F n) c = NF.dZ (fun w => psiC n w * f w) c from rfl, hd]
      ring
  have hRe : ∀ n, (fun c => F n c * conj (conj c * NF.dZb g c) / ((‖c‖ ^ 2 : ℝ) : ℂ)) = fun c =>
      psiC n c * (f c * conj (conj c * NF.dZb g c) / ((‖c‖ ^ 2 : ℝ) : ℂ)) +
        (0 : ℂ) * (f c * conj (g c) / ((‖c‖ ^ 2 : ℝ) : ℂ)) := by
    intro n; funext c; simp only [hF]; ring
  have hψm : ∀ n, AEStronglyMeasurable (psiC n) volume := fun n => (psiC_contDiff n).continuous.aestronglyMeasurable
  have hvm : ∀ n, AEStronglyMeasurable (fun c : ℂ => c * NF.dZ (psiC n) c) volume := fun n =>
    (continuous_id.mul (dZ_contDiff (psiC_contDiff n)).continuous).aestronglyMeasurable
  have hae : ∀ᵐ c ∂(volume : Measure ℂ), c ≠ 0 := Measure.ae_ne volume 0
  have hL := tendsto_int_uv_ae _ _ h1 h0 (fun n => psiC n) (fun n c => c * NF.dZ (psiC n) c) C hψm hvm
    (fun n c => by simpa [psiC] using psiL_le_one n c) (fun n c => norm_c_dZ_psiC_le hC n c)
    (hae.mono fun c hc => psiC_eventually c hc)
  have hR := tendsto_int_uv_ae _ _ h2 h0 (fun n => psiC n) (fun _ _ => (0 : ℂ)) C hψm
    (fun _ => aestronglyMeasurable_const)
    (fun n c => by simpa [psiC] using psiL_le_one n c)
    (fun _ _ => by simpa using (norm_nonneg _).trans (hC 0))
    (hae.mono fun c hc => (psiC_eventually c hc).mono fun n hn => ⟨hn.1, rfl⟩)
  have hL' : Tendsto (fun n => ∫ c, c * NF.dZ (F n) c * conj (g c) / ((‖c‖ ^ 2 : ℝ) : ℂ)) atTop
      (𝓝 (∫ c, c * NF.dZ f c * conj (g c) / ((‖c‖ ^ 2 : ℝ) : ℂ))) := by
    simp only [hLe]; exact hL
  have hR' : Tendsto (fun n => ∫ c, c * NF.dZ (F n) c * conj (g c) / ((‖c‖ ^ 2 : ℝ) : ℂ)) atTop
      (𝓝 (-∫ c, f c * conj (conj c * NF.dZb g c) / ((‖c‖ ^ 2 : ℝ) : ℂ))) := by
    simp only [key, hRe]; exact hR.neg
  exact tendsto_nhds_unique hL' hR'

end Main

end Formalism.FourierDecayAlt.P5.HerB
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularityBundleFromHypotheses
section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.FourierDecayAlt.P.S3dx4

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

theorem quadConv_of (hSch : SchurH) (hNIs : NormIdSm) (hNI : NormInv) (hGS : GrowthS) (hGG : GrowthG)
    (hDD : DecDD) (hBC : BeConv) : More.QuadConv := by
  intro hIn k r Wp Wq _ _ _ _ _ _ _ _ D ε lam h H _ _ _ σ w0 u u' νq νq' hS1 hS2 l l' hbe hbe'
  exact ⟨fun γ hγ => quadA_of hSch hNIs hNI hGG hDD hBC hIn D hS1 hS2 hbe hbe' hγ,
    quadB_of hNI hGS hGG hDD hIn D hS1 hbe⟩

end Formalism.FourierDecayAlt.P.S3dx4

theorem Formalism.FourierDecayAlt.P.regularity_bundle_from_hypotheses : Formalism.FourierDecayAlt.ThreeDimData.More.MoreOfSteps :=
  fun hSch hNIs hNI hGS hGG hDD hBC _ =>
    ⟨Formalism.FourierDecayAlt.P.S3dx4.phiReg_of hSch hNIs hGG hDD hBC, Formalism.FourierDecayAlt.P.S3dx4.ooConv_of hSch hNIs hNI hGG hDD hBC,
      Formalism.FourierDecayAlt.P.S3dx4.quadConv_of hSch hNIs hNI hGS hGG hDD hBC⟩
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SecondDerivativeHolds
section
namespace Formalism.FourierDecayAlt.P.HilbertSchmidtNorm

open Formalism.FourierDecayAlt.PB Finset NumberField

open scoped ComplexOrder ComplexConjugate

open Classical

theorem localCores : Formalism.FourierDecayAlt.PB.LocalCores :=
  ⟨Formalism.FourierDecayAlt.Final.jx_pSDAgree,
   Formalism.FourierDecayAlt.Final.jx_schurProduct,
   Formalism.FourierDecayAlt.Final.jx_productDomination,
   Formalism.FourierDecayAlt.Final.jx_diagScale,
   Formalism.FourierDecayAlt.Final.jx_diagPhase,
   Formalism.FourierDecayAlt.Final.jx_blockDiagPSD,
   Formalism.FourierDecayAlt.Final.jx_productLemma,
   Formalism.FourierDecayAlt.Final.jx_scaleOk,
   Formalism.FourierDecayAlt.Final.jx_phaseOk,
   Formalism.FourierDecayAlt.Final.jx_outsideSysOk,
   Formalism.FourierDecayAlt.Final.jx_outsideDomination,
   Formalism.FourierDecayAlt.Final.jx_localPullback,
   Formalism.FourierDecayAlt.Final.jx_localUnitHeads,
   Formalism.FourierDecayAlt.Final.jx_topPullback,
   Formalism.FourierDecayAlt.Final.jx_topUnitHeads,
   Formalism.FourierDecayAlt.Final.jx_globalOfLocal,
   Formalism.FourierDecayAlt.Final.jx_uniformMajorantOn,
   Formalism.FourierDecayAlt.Final.jx_axiomsFromSystems,
   Formalism.FourierDecayAlt.Final.jx_axiomsFromFamilies,
   Formalism.FourierDecayAlt.Final.jx_kernelOfLocal,
   Formalism.FourierDecayAlt.Final.jx_localKernelPSD,
   Formalism.FourierDecayAlt.Final.tc_domMinOfText,
   Formalism.FourierDecayAlt.Final.tc_domAfterOfLocal,
   Formalism.FourierDecayAlt.Final.gram_determinant_dual_bound_a,
   Formalism.FourierDecayAlt.Final.parahoric_gram_matrix,
   Formalism.FourierDecayAlt.Final.zero_level_ones_vector,
   Formalism.FourierDecayAlt.Final.singleBlockParseval_true,
   Formalism.FourierDecayAlt.Final.theta_equality_first,
   Formalism.FourierDecayAlt.Final.singleBlockThetaProps_true,
   Formalism.FourierDecayAlt.Final.ns_support,
   Formalism.FourierDecayAlt.Final.ns_block_diagonal,
   Formalism.FourierDecayAlt.Final.latticeAverage_of_gram⟩

theorem globalCores : Formalism.FourierDecayAlt.PB.GlobalCores :=
  ⟨Formalism.FourierDecayAlt.Final.tc_theoremAAfter,
   Formalism.FourierDecayAlt.Final.tc_recursionWithDens,
   Formalism.FourierDecayAlt.Final.tc_domScaleTop,
   Formalism.FourierDecayAlt.Final.tc_sumBoundMax,
   Formalism.FourierDecayAlt.Final.tc_recHypScaleTop,
   Formalism.FourierDecayAlt.Final.tc_densSum,
   Formalism.FourierDecayAlt.Final.tc_densLeTwo,
   Formalism.FourierDecayAlt.Final.tc_densSize,
   Formalism.FourierDecayAlt.Final.tc_densChain,
   Formalism.FourierDecayAlt.Final.poisson_summation_text,
   Formalism.FourierDecayAlt.Final.jx_poissonJoint,
   Formalism.FourierDecayAlt.Final.jx_poissonStepJoint,
   Formalism.SA.P.smoothedSumBound,
   Formalism.FourierDecayAlt.Final.lattices_general_position_bound,
   Formalism.FourierDecayAlt.Final.ideals_match,
   Formalism.FourierDecayAlt.Final.ideal_norm_formula,
   Formalism.FourierDecayAlt.Final.field_extension_degree_facts,
   Formalism.FourierDecayAlt.Final.jx_frameProducts,
   Formalism.FourierDecayAlt.Final.jx_xIsLamOne,
   Formalism.FourierDecayAlt.Final.jx_latticeSumsJoint,
   Formalism.FourierDecayAlt.Final.jx_instSizes,
   Formalism.FourierDecayAlt.Final.jx_instLatticeSums,
   Formalism.FourierDecayAlt.Final.sz_sizesMain,
   Formalism.FourierDecayAlt.Final.jx_sizesToRecursion,
   Formalism.FourierDecayAlt.Final.jx_globPositive,
   Formalism.FourierDecayAlt.Final.counting_theorem,
   Formalism.FourierDecayAlt.Final.jx_formGivesMain⟩

end Formalism.FourierDecayAlt.P.HilbertSchmidtNorm

namespace Formalism.FourierDecayAlt.P

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceIntCut
section
namespace Formalism.FourierDecayAlt.P.FormNormSumIdentities

open Formalism.FourierDecayAlt MeasureTheory

noncomputable section

def SliceIntCut : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P0 : M.Par)
    (T : D.LevTower P0.k P0.r Wp Wq) (w : List C.Letter) (f : B.Mat P0.k P0.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ)
    (ε : ℝ) (i : ℕ) (hi : i ≤ P0.r),
    1 ≤ i → 2 ≤ P0.k → B.CkOn ⊤ (B.GV P0.k P0.r) f → (∃ R : ℝ, ∀ g ∈ B.GV P0.k P0.r, f g ≠ 0 → B.gN g ≤ R) →
    C6.IsCut0 χ → 0 < ε → ∀ (p : C.LPt) (hp : D.IsLocPt p i), ∀ (e : Wd.Ix (Fin w.length)),
    ∀ γ ∈ B.GV P0.k (P0.r - D.ptSize p),
    Integrable (fun ξ : U.Xi P0.k (D.ptSize p) 0 (P0.r - D.ptSize p) (D.ptPerm p) =>
        U.psiStar P0.k (P0.r - D.ptSize p) (D.ptPerm p) (D.castV (by have := hp.2; omega) T.base.z) (D.castV (by have := hp.2; omega) T.base.z') ξ •
          D.castF (by have := hp.2; omega) (D.uwG P0.k P0.r T.base.z T.base.z' (D.cutF T.base χ f ε) i hi w e)
            (U.gaXi P0.k (P0.r - D.ptSize p) (D.ptPerm p) (D.ptDiag p) ξ (fun a => a.elim0) γ))
      (U.muXi P0.k (D.ptSize p) 0 (P0.r - D.ptSize p) (D.ptPerm p))

end

end Formalism.FourierDecayAlt.P.FormNormSumIdentities
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceOmBlock
section
namespace Formalism.FourierDecayAlt.P.FormNormSumIdentities

open Formalism.FourierDecayAlt MeasureTheory

noncomputable section

def kapB (n : ℕ) : ℝ := Real.pi ^ ((n + 1) * (n + 4) / 2)

theorem ptSize_two (h : C.LPt) (n : ℕ) (t c : ℂ) :
    D.ptSize (h ++ [(n + 1, t), (1, c)]) = D.ptSize h + (n + 1 + 1) := by
  simp [D.ptSize, List.map_append, List.sum_append]

def SliceOmBlock : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (z z' : Fin (2 * r + k + 1) → ℂ) (F : B.Mat k r → E) (h p : C.LPt) (n : ℕ) (t c : ℂ)
    (hp : p = h ++ [(n + 1, t), (1, c)]) (hle : D.ptSize p ≤ r) (γ : B.Mat k (r - D.ptSize p)),
    D.IsLocPt p (D.ptSize p) →
    Integrable (fun ξ : U.Xi k (D.ptSize p) 0 (r - D.ptSize p) (D.ptPerm p) =>
        U.psiStar k (r - D.ptSize p) (D.ptPerm p) (D.castV (by omega) z) (D.castV (by omega) z') ξ •
          D.castF (by omega) F (U.gaXi k (r - D.ptSize p) (D.ptPerm p) (D.ptDiag p) ξ (fun a => a.elim0) γ))
      (U.muXi k (D.ptSize p) 0 (r - D.ptSize p) (D.ptPerm p)) →
    D.sliceAt k r z z' F p γ =
      ((kapB n : ℝ) : ℂ) •
        G.OmBlock U.betaU (n + 1) (fun Z => U.PhiFun k (r - D.ptSize p) (D.ptPerm h) (D.ptDiag h)
          (D.castV (by subst hp; rw [ptSize_two] at hle ⊢; omega) z)
          (D.castV (by subst hp; rw [ptSize_two] at hle ⊢; omega) z')
          (D.castF (by subst hp; rw [ptSize_two] at hle ⊢; omega) F) Z γ) t c

end

end Formalism.FourierDecayAlt.P.FormNormSumIdentities
end

