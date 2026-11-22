import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0446
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0429
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviIrreducibleTensorDecomposition
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0447
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0449
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0244
import Development.WeilBound.CoreStatements.PlaceConnectedComponents.IsOpenQuotientMapArt0
import GroundTheory.LocalFields.Bundle0013
import GroundTheory.LocalFields.KroneckerWeber
import GroundTheory.PAdicHodge.FieldOfNormsCyclBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0107
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0716
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0327

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.L2ConvolutionLocallyCompactMem
section
open MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.AutomorphicL2Convolution

private theorem descend_eq_sec_lemma {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {Γ : Subgroup G} [DiscreteTopology Γ]
    {φ : G → ℂ} (hφ : LeftInv Γ φ) (q : Quot Γ) : descend Γ φ q = φ (sec Γ q) := by
  have h2 : mk Γ (Quotient.out q) = mk Γ (sec Γ q) := (Quotient.out_eq q).trans (mk_sec q).symm
  obtain ⟨γ, hγ⟩ := mk_eq_iff.1 h2
  show φ (Quotient.out q) = φ (sec Γ q)
  rw [← hγ, hφ _ γ.2]

private theorem descend_rmul_lemma_2 {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {Γ : Subgroup G} [DiscreteTopology Γ]
    {φ : G → ℂ} (hφ : LeftInv Γ φ) (g : G) (q : Quot Γ) :
    descend Γ φ (rmul Γ g q) = φ (sec Γ q * g) := by
  rw [descend_eq_sec_lemma hφ]
  have h1 : rmul Γ g q = mk Γ (sec Γ q * g) := by
    rw [← rmul_mk, mk_sec]
  have h2 : mk Γ (sec Γ (rmul Γ g q)) = mk Γ (sec Γ q * g) := (mk_sec _).trans h1
  obtain ⟨γ, hγ⟩ := mk_eq_iff.1 h2
  rw [← hγ, hφ _ γ.2]

private theorem coeFn_R_lemma_3 {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {Γ : Subgroup G} [DiscreteTopology Γ]
    {μ : Measure G} [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {φ : G → ℂ} (h : MemL2Quotient Γ μ φ) (g : G) :
    ∀ᵐ q ∂(GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ),
      (((R Γ μ) g) h.toL2 : Lp ℂ 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)) q = φ (sec Γ q * g) := by
  have h2 : (fun q => (h.toL2 : Lp ℂ 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)) (rmul Γ g q)) =ᵐ[GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ]
      fun q => descend Γ φ (rmul Γ g q) :=
    (measurePreserving_rmul g).quasiMeasurePreserving.ae_eq_comp h.coeFn_toL2
  refine (coeFn_R g h.toL2).trans (h2.trans (Filter.Eventually.of_forall fun q => ?_))
  exact descend_rmul_lemma_2 h.1 g q

private theorem integral_norm_sq_lemma_4 {α : Type} [MeasurableSpace α] {m : Measure α} (F : Lp ℂ 2 m) :
    ∫ q, ‖F q‖ ^ 2 ∂m = ‖F‖ ^ 2 := by
  have h1 := MeasureTheory.L2.inner_def (𝕜 := ℂ) F F
  simp only [inner_self_eq_norm_sq_to_K] at h1
  simp_rw [← RCLike.ofReal_pow] at h1
  rw [integral_ofReal] at h1
  exact (RCLike.ofReal_inj.mp h1).symm

private theorem setIntegral_norm_le_lemma_5 {α : Type} [MeasurableSpace α] {m : Measure α} {S : Set α}
    (hS : m S < ∞) (F : Lp ℂ 2 m) :
    ∫ q in S, ‖F q‖ ∂m ≤ ((∫ q in S, (1 : ℝ) ∂m) + ‖F‖ ^ 2) / 2 := by
  haveI : IsFiniteMeasure (m.restrict S) := isFiniteMeasure_restrict.2 hS.ne
  have hsq : Integrable (fun q => ‖F q‖ ^ 2) m := (Lp.memLp F).norm.integrable_sq
  have hint1 : Integrable (fun q => (1 + ‖F q‖ ^ 2) / 2) (m.restrict S) :=
    ((integrable_const (1 : ℝ)).add hsq.restrict).div_const 2
  calc ∫ q in S, ‖F q‖ ∂m ≤ ∫ q in S, (1 + ‖F q‖ ^ 2) / 2 ∂m := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun q => norm_nonneg (F q)) hint1
          (Filter.Eventually.of_forall fun q => ?_)
        nlinarith [sq_nonneg (‖F q‖ - 1)]
    _ = ((∫ q in S, (1 : ℝ) ∂m) + ∫ q in S, ‖F q‖ ^ 2 ∂m) / 2 := by
        rw [integral_div, integral_add (integrable_const (1 : ℝ)) hsq.restrict]
    _ ≤ ((∫ q in S, (1 : ℝ) ∂m) + ‖F‖ ^ 2) / 2 := by
        have := setIntegral_le_integral (s := S) hsq (Filter.Eventually.of_forall fun q => by positivity)
        rw [integral_norm_sq_lemma_4 F] at this
        linarith

theorem memL2_convolution_mem {G L : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [DiscreteTopology Γ]
    (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μ] [Group L]
    [TopologicalSpace L] [IsTopologicalGroup L] [SecondCountableTopology L] [T2Space L] [LocallyCompactSpace L]
    [MeasurableSpace L] [BorelSpace L] (ν : Measure L) [IsFiniteMeasureOnCompacts ν] (j : L →* G)
    (hj : Continuous j) (D : L → ℂ) (hD : Continuous D) (hDc : HasCompactSupport D) (φ ψ : G → ℂ)
    (_hφ : Continuous φ) (h : MemL2Quotient Γ μ φ) (hψ : ∀ g, ψ g = ∫ y, φ (g * j y) * D y ∂ν) :
    ∃ h' : MemL2Quotient Γ μ ψ, ∀ W : Submodule ℂ (L2 Γ μ), IsSubrep (R Γ μ) W → h.toL2 ∈ W → h'.toL2 ∈ W := by
  classical
  have hLφ : LeftInv Γ φ := h.1
  have hπ' : GlobalTheory.OpTrace.IsUnitaryRep ((R Γ μ).comp j) :=
    ⟨fun y w => norm_R (j y) w, fun w => (continuous_R w).comp hj⟩
  have hDint : Integrable D ν := hD.integrable_of_hasCompactSupport hDc
  obtain ⟨hTint, hTv⟩ := isRepOp_of_integrable (μ := ν) hπ' hDint h.toL2
  set T := GlobalTheory.OpTrace.repOp ((R Γ μ).comp j) ν D with hTdef
  have hLψ : LeftInv Γ ψ := by
    intro γ hγ g
    rw [hψ (γ * g), hψ g]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show φ (γ * g * j y) * D y = φ (g * j y) * D y
    rw [mul_assoc γ g (j y), hLφ γ hγ]
  have hmeasH : Measurable fun p : L × Quot Γ => φ (sec Γ p.2 * j p.1) * D p.1 :=
    (_hφ.measurable.comp ((measurableEmbedding_sec.measurable.comp measurable_snd).mul
      (hj.measurable.comp measurable_fst))).mul (hD.measurable.comp measurable_fst)
  have hprod : ∀ S : Set (Quot Γ), MeasurableSet S → GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ S < ∞ →
      Integrable (fun p : L × Quot Γ => φ (sec Γ p.2 * j p.1) * D p.1)
        (ν.prod ((GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ).restrict S)) := by
    intro S hS hSf
    haveI : IsFiniteMeasure ((GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ).restrict S) := isFiniteMeasure_restrict.2 hSf.ne
    rw [integrable_prod_iff hmeasH.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall fun y => ?_, ?_⟩
    · have hc := coeFn_R_lemma_3 h (j y)
      refine ((((Lp.memLp (((R Γ μ) (j y)) h.toL2 : Lp ℂ 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ))).restrict S).integrable
        one_le_two).mul_const (D y)).congr ?_
      exact ae_restrict_of_ae (hc.mono fun q hq => by simp only [hq])
    · refine Integrable.mono'
        (hDint.norm.mul_const (((∫ q in S, (1 : ℝ) ∂(GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)) +
          ‖(h.toL2 : Lp ℂ 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ))‖ ^ 2) / 2))
        (hmeasH.norm.aestronglyMeasurable.integral_prod_right') (Filter.Eventually.of_forall fun y => ?_)
      have hc := coeFn_R_lemma_3 h (j y)
      rw [Real.norm_of_nonneg (integral_nonneg fun q => norm_nonneg _)]
      have e1 : ∫ q, ‖φ (sec Γ q * j y) * D y‖ ∂((GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ).restrict S)
          = (∫ q in S, ‖(((R Γ μ) (j y)) h.toL2 : Lp ℂ 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)) q‖ ∂(GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)) * ‖D y‖ := by
        simp_rw [norm_mul]
        rw [integral_mul_const]
        congr 1
        exact integral_congr_ae (ae_restrict_of_ae (hc.mono fun q hq => by simp only [hq]))
      have hb := setIntegral_norm_le_lemma_5 hSf ((((R Γ μ) (j y)) h.toL2 : Lp ℂ 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)))
      have hn : ‖(((R Γ μ) (j y)) h.toL2 : Lp ℂ 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ))‖
          = ‖(h.toL2 : Lp ℂ 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ))‖ := norm_R _ _
      rw [hn] at hb
      show ∫ q, ‖φ (sec Γ q * j y) * D y‖ ∂((GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ).restrict S) ≤ _
      rw [e1, mul_comm _ (‖D y‖)]
      exact mul_le_mul_of_nonneg_left hb (norm_nonneg _)
  have hkey : (fun q => (T h.toL2 : Lp ℂ 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)) q) =ᵐ[GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ]
      fun q => ψ (sec Γ q) := by
    refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite ?_ ?_ ?_
    · intro S hS hSf
      haveI : IsFiniteMeasure ((GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ).restrict S) := isFiniteMeasure_restrict.2 hSf.ne
      exact ((Lp.memLp (T h.toL2 : Lp ℂ 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ))).restrict S).integrable one_le_two
    · intro S hS hSf
      exact (hprod S hS hSf).integral_prod_right.congr
        (Filter.Eventually.of_forall fun q => (hψ (sec Γ q)).symm)
    · intro S hS hSf
      have hSf' : GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ S ≠ ∞ := hSf.ne
      have hstep : ∀ y, ⟪indicatorConstLp 2 hS hSf' (1 : ℂ),
          (D y • ((((R Γ μ).comp j) y h.toL2 : L2 Γ μ) : Lp ℂ 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)))⟫_ℂ
          = ∫ q in S, φ (sec Γ q * j y) * D y ∂(GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) := by
        intro y
        have hc := coeFn_R_lemma_3 h (j y)
        rw [inner_smul_right, L2.inner_indicatorConstLp_one, integral_mul_const, mul_comm (D y)]
        congr 1
        exact integral_congr_ae (ae_restrict_of_ae (hc.mono fun q hq => by
          simp only [MonoidHom.comp_apply]; exact hq))
      calc ∫ q in S, (T h.toL2 : Lp ℂ 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)) q ∂(GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)
          = ⟪indicatorConstLp 2 hS hSf' (1 : ℂ), (T h.toL2 : Lp ℂ 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ))⟫_ℂ :=
            (L2.inner_indicatorConstLp_one hS hSf' _).symm
        _ = ⟪indicatorConstLp 2 hS hSf' (1 : ℂ),
              ((∫ y, D y • ((R Γ μ).comp j) y h.toL2 ∂ν : L2 Γ μ) : Lp ℂ 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ))⟫_ℂ := by
            rw [hTv]; rfl
        _ = ∫ y, ⟪indicatorConstLp 2 hS hSf' (1 : ℂ),
              (D y • ((((R Γ μ).comp j) y h.toL2 : L2 Γ μ) : Lp ℂ 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)))⟫_ℂ ∂ν :=
            (integral_inner hTint _).symm
        _ = ∫ y, ∫ q in S, φ (sec Γ q * j y) * D y ∂(GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) ∂ν :=
            integral_congr_ae (Filter.Eventually.of_forall hstep)
        _ = ∫ q in S, ∫ y, φ (sec Γ q * j y) * D y ∂ν ∂(GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) :=
            integral_integral_swap (hprod S hS hSf)
        _ = ∫ q in S, ψ (sec Γ q) ∂(GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) :=
            integral_congr_ae (Filter.Eventually.of_forall fun q => (hψ (sec Γ q)).symm)
  have hae : descend Γ ψ =ᵐ[GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ] fun q => (T h.toL2 : Lp ℂ 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)) q :=
    Filter.EventuallyEq.trans (Filter.Eventually.of_forall fun q => descend_eq_sec_lemma hLψ q) hkey.symm
  have hmem : MemL2Quotient Γ μ ψ := ⟨hLψ, MemLp.ae_eq hae.symm (Lp.memLp _)⟩
  refine ⟨hmem, fun W hW hvW => ?_⟩
  have hEq : hmem.toL2 = T h.toL2 := Lp.ext (hmem.coeFn_toL2.trans hae)
  rw [hEq]
  exact IsSubrep.map_mem_of_isRepOp (π := (R Γ μ).comp j) ⟨hW.1, fun y w hw => hW.2 (j y) w hw⟩
    (isRepOp_of_integrable hπ' hDint) hvW

end GlobalTheory.CompanionTheory.AutomorphicL2Convolution
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LastRowUpdateNhdsGeneration
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep

variable {k : Type} [Field k] {n : ℕ}

def lastRowMat (r : Fin (n + 1) → k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k :=
  (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k).updateRow (Fin.last n) r

def rowInv (r : Fin (n + 1) → k) : Fin (n + 1) → k :=
  fun j => if j = Fin.last n then (r (Fin.last n))⁻¹ else -r j * (r (Fin.last n))⁻¹

theorem lastRowMat_mul_last (r s : Fin (n + 1) → k) (j : Fin (n + 1)) :
    (lastRowMat r * lastRowMat s) (Fin.last n) j =
      (if j = Fin.last n then 0 else r j) + r (Fin.last n) * s j := by
  rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
  simp only [GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowMat, Matrix.updateRow_self,
    Matrix.updateRow_ne (Fin.castSucc_ne_last _), Matrix.one_apply]
  congr 1
  first
  | refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [Fin.castSucc_ne_last]
    · simp [Fin.castSucc_ne_last]
  | induction j using Fin.lastCases with
    | last => simp [Fin.castSucc_ne_last]
    | cast j => simp [Fin.castSucc_ne_last]

theorem lastRowMat_mul_rowInv {r : Fin (n + 1) → k} (hr : r (Fin.last n) ≠ 0) :
    lastRowMat r * lastRowMat (rowInv r) = 1 := by
  ext i j
  by_cases hi : i = Fin.last n
  · subst hi
    rw [GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowMat_mul_last]
    by_cases hj : j = Fin.last n
    · subst hj
      first
      | simp [GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.rowInv, hr]
      | (simp only [GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.rowInv, if_true, ite_true, zero_add, Matrix.one_apply_eq]
         exact mul_inv_cancel₀ hr)
    · rw [Matrix.one_apply_ne (Ne.symm hj), if_neg hj]
      simp only [GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.rowInv, if_neg hj]
      linear_combination (-r j) * mul_inv_cancel₀ hr
  · first
    | (rw [Matrix.mul_apply]
       simp only [GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowMat, Matrix.updateRow_ne hi]
       rw [← Matrix.mul_apply, Matrix.one_mul, Matrix.updateRow_ne hi])
    | simp [Matrix.mul_apply, GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowMat, Matrix.updateRow_ne hi, Matrix.one_apply,
        Matrix.updateRow_apply, hi]

def lastRowGL (r : Fin (n + 1) → k) (hr : r (Fin.last n) ≠ 0) : GL (Fin (n + 1)) k where
  val := lastRowMat r
  inv := lastRowMat (rowInv r)
  val_inv := lastRowMat_mul_rowInv hr
  inv_val := mul_eq_one_comm.1 (lastRowMat_mul_rowInv hr)

def invRow (x : GL (Fin (n + 1)) k) : Fin (n + 1) → k :=
  fun j => ((x⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) j

theorem invRow_one : invRow (1 : GL (Fin (n + 1)) k) (Fin.last n) = 1 := by
  simp [GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow]

theorem vecMul_eLast (x : GL (Fin (n + 1)) k) :
    vecMul (eLast k n) (lastRowMat (invRow x) * (x : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) = eLast k n := by
  have h : vecMul (GlobalTheory.BZMir.eLast k n) (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowMat (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow x)) =
      vecMul (GlobalTheory.BZMir.eLast k n)
        ((x⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) := by
    ext j
    first
    | simp [GlobalTheory.BZMir.eLast, Matrix.single_vecMul, GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowMat, GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow]
    | simp [GlobalTheory.BZMir.eLast, Matrix.vecMul, dotProduct, Pi.single_apply,
        GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowMat, GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow, Matrix.updateRow_apply]
  rw [← Matrix.vecMul_vecMul, h, Matrix.vecMul_vecMul, Units.inv_mul, Matrix.vecMul_one]

section Top

variable [TopologicalSpace k] [IsTopologicalDivisionRing k] [T1Space k]

theorem continuous_invRow : Continuous (invRow : GL (Fin (n + 1)) k → _) := by
  have hc : Continuous fun x : GL (Fin (n + 1)) k =>
      ((x⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) :=
    Units.continuous_coe_inv (M := Matrix (Fin (n + 1)) (Fin (n + 1)) k)
  unfold GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow
  first
  | exact continuous_pi fun j => hc.matrix_elem (Fin.last n) j
  | exact continuous_pi fun j => (continuous_apply j).comp ((continuous_apply (Fin.last n)).comp hc)

theorem continuous_lastRowMat : Continuous (lastRowMat : (Fin (n + 1) → k) → _) := by
  unfold GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowMat
  exact continuous_const.matrix_updateRow (Fin.last n) continuous_id

theorem continuousAt_rowInv : ContinuousAt (fun x : GL (Fin (n + 1)) k => rowInv (invRow x)) 1 := by
  have hv : Continuous (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow : GL (Fin (n + 1)) k → _) := GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.continuous_invRow
  have hl : ContinuousAt (fun x : GL (Fin (n + 1)) k => (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow x (Fin.last n))⁻¹) 1 :=
    ((continuous_apply (Fin.last n)).comp hv).continuousAt.inv₀
      (show GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow (1 : GL (Fin (n + 1)) k) (Fin.last n) ≠ 0 by
        rw [GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow_one]; exact one_ne_zero)
  refine continuousAt_pi.2 fun j => ?_
  by_cases hj : j = Fin.last n
  · simp only [GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.rowInv, if_pos hj]
    exact hl
  · simp only [GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.rowInv, if_neg hj]
    exact (((continuous_apply j).comp hv).continuousAt.neg).mul hl

theorem exists_nhd {V : Set (GL (Fin (n + 1)) k)} (hV : V ∈ 𝓝 (1 : GL (Fin (n + 1)) k)) :
    ∃ N ∈ 𝓝 (1 : GL (Fin (n + 1)) k), ∀ x ∈ N, ∃ hr : invRow x (Fin.last n) ≠ 0,
      lastRowGL (invRow x) hr * x ∈ V := by
  have h1 : GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow (1 : GL (Fin (n + 1)) k) (Fin.last n) ≠ 0 := by
    rw [GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow_one]; exact one_ne_zero
  have hv1 : GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow (1 : GL (Fin (n + 1)) k) =
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) := by
    funext j; simp [GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow]
  have hg1 : GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowGL (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow (1 : GL (Fin (n + 1)) k)) h1 = 1 := by
    apply Units.ext
    show GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowMat (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow (1 : GL (Fin (n + 1)) k)) = 1
    rw [hv1]
    exact Matrix.updateRow_eq_self _ _
  let ψ : GL (Fin (n + 1)) k →
      Matrix (Fin (n + 1)) (Fin (n + 1)) k × (Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵐᵒᵖ :=
    fun x => (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowMat (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow x) * (x : Matrix (Fin (n + 1)) (Fin (n + 1)) k),
      MulOpposite.op (((x⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *
        GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowMat (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.rowInv (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow x))))
  have hψ : ∀ x (hr : GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow x (Fin.last n) ≠ 0),
      Units.embedProduct (Matrix (Fin (n + 1)) (Fin (n + 1)) k)
        (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowGL (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow x) hr * x) = ψ x := fun x hr => by
    first
    | rfl
    | (rw [Units.embedProduct_apply]; rfl)
  have hfst : ContinuousAt (fun x : GL (Fin (n + 1)) k =>
      GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowMat (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow x) * (x : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) 1 := by
    first
    | exact ((GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.continuous_lastRowMat.comp GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.continuous_invRow).mul
        Units.continuous_val).continuousAt
    | exact ((GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.continuous_lastRowMat.comp GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.continuous_invRow).matrix_mul
        Units.continuous_val).continuousAt
  have hsnd : ContinuousAt (fun x : GL (Fin (n + 1)) k =>
      MulOpposite.op (((x⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *
        GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowMat (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.rowInv (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow x)))) 1 :=
    MulOpposite.continuous_op.continuousAt.comp
      ((Units.continuous_coe_inv (M := Matrix (Fin (n + 1)) (Fin (n + 1)) k)).continuousAt.mul
        (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.continuous_lastRowMat.continuousAt.comp
          GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.continuousAt_rowInv))
  have hψc : ContinuousAt ψ 1 := hfst.prodMk hsnd
  have hψ1 : ψ 1 = Units.embedProduct (Matrix (Fin (n + 1)) (Fin (n + 1)) k) 1 := by
    rw [← hψ 1 h1, hg1, mul_one]
  obtain ⟨U, hU, hUV⟩ : ∃ U ∈ 𝓝 (Units.embedProduct (Matrix (Fin (n + 1)) (Fin (n + 1)) k) 1),
      Units.embedProduct (Matrix (Fin (n + 1)) (Fin (n + 1)) k) ⁻¹' U ⊆ V := by
    rw [Units.isEmbedding_embedProduct.toIsInducing.nhds_eq_comap] at hV
    exact Filter.mem_comap.1 hV
  have hne : ∀ᶠ x in 𝓝 (1 : GL (Fin (n + 1)) k), GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow x (Fin.last n) ≠ 0 :=
    ((continuous_apply (Fin.last n)).comp GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.continuous_invRow).continuousAt.eventually_ne h1
  refine ⟨ψ ⁻¹' U ∩ {x | GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow x (Fin.last n) ≠ 0},
    Filter.inter_mem (hψc.preimage_mem_nhds (by rw [hψ1]; exact hU)) hne, ?_⟩
  rintro x ⟨hxU, hx⟩
  refine ⟨hx, hUV ?_⟩
  show Units.embedProduct (Matrix (Fin (n + 1)) (Fin (n + 1)) k)
    (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowGL (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow x) hx * x) ∈ U
  rw [hψ x hx]
  exact hxU

end Top

theorem row_replacement (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (S : Subgroup (GL (Fin (n + 1)) k))
    (hS : ∀ (r : Fin (n + 1) → k), r (Fin.last n) ≠ 0 → ∀ g : GL (Fin (n + 1)) k,
      (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k).updateRow (Fin.last n) r → g ∈ S)
    (O : Set (Mir k n)) (hO : O ∈ 𝓝 (1 : Mir k n)) :
    ∃ N ∈ 𝓝 (1 : GL (Fin (n + 1)) k), ∀ p ∈ S, ∀ x ∈ N, ∀ m : Mir k n, (m : GL (Fin (n + 1)) k) = p * x →
      ∃ a : Mir k n, (a : GL (Fin (n + 1)) k) ∈ S ∧ ∃ x' ∈ O, m = a * x' := by
  obtain ⟨V, hV, hVO⟩ := (mem_nhds_subtype _ _ _).1 hO
  obtain ⟨N, hN, hNV⟩ := GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.exists_nhd (k := k) (n := n) hV
  refine ⟨N, hN, fun p hp x hx m hm => ?_⟩
  obtain ⟨hr, hgx⟩ := hNV x hx
  have hgS : GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowGL (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow x) hr ∈ S := hS _ hr _ rfl
  have hmir : GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowGL (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow x) hr * x ∈ GlobalTheory.BZMir.Mir k n :=
    GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.vecMul_eLast x
  refine ⟨m * ⟨GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowGL (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow x) hr * x, hmir⟩⁻¹, ?_,
    ⟨GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowGL (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow x) hr * x, hmir⟩, hVO hgx, (inv_mul_cancel_right _ _).symm⟩
  show (m : GL (Fin (n + 1)) k) * (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowGL (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow x) hr * x)⁻¹ ∈ S
  rw [hm, _root_.mul_inv_rev, ← mul_assoc, mul_inv_cancel_right]
  exact S.mul_mem hp (S.inv_mem hgS)

end GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviIrreducibleTensorDecompositionStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_irreducible_tensor_decomposition : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {s : ℕ} (d : Fin s → ℕ) (τ : IrrRep (Levi k fun a => Fin (d a))), ∃ σ : ∀ a, IrrCl (GL (Fin (d a)) k), Nonempty (τ.ρ.Equiv (piTensor fun a => (σ a).rep.ρ)) := by
  first | exact @GlobalTheory.CompanionTheory.LeviTensor.nonempty_equiv_piTensor | exact GlobalTheory.CompanionTheory.LeviTensor.nonempty_equiv_piTensor | (intros; apply GlobalTheory.CompanionTheory.LeviTensor.nonempty_equiv_piTensor <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviMatrixMapBaseChange
section
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.KFin

theorem leviMat_map {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}
    (A A' : Type) [CommRing A] [Algebra F A] [CommRing A'] [Algebra F A'] (φ : A →ₐ[F] A')
    (M : Matrix (Fin n) (Fin n) (A ⊗[F] E)) :
    leviMat σ J A' X Y (M.map (Algebra.TensorProduct.map φ (AlgHom.id F E))) =
      (leviMat σ J A X Y M).map (Algebra.TensorProduct.map φ (AlgHom.id F E)) := by
  let f : (A ⊗[F] E) →+* (A' ⊗[F] E) := (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom
  have hf : ∀ e : E, f (inclR (F := F) A e) = inclR (F := F) A' e := fun e => by
    simp [f, inclR]
  have hZ : ∀ {a b : ℕ} (Z : Matrix (Fin a) (Fin b) E),
      (Z.map (inclR (F := F) A)).map f = Z.map (inclR (F := F) A') := fun Z => by
    ext i j
    simp [hf]
  have hmul : ∀ {a b c : ℕ} (P : Matrix (Fin a) (Fin b) (A ⊗[F] E)) (Q : Matrix (Fin b) (Fin c) (A ⊗[F] E)),
      (P * Q).map f = P.map f * Q.map f := fun P Q => Matrix.map_mul
  have hadd : ∀ P Q : Matrix (Fin n) (Fin n) (A ⊗[F] E), (P + Q).map f = P.map f + Q.map f :=
    fun P Q => Matrix.map_add f (map_add f) P Q
  have hsub : ∀ P Q : Matrix (Fin n) (Fin n) (A ⊗[F] E), (P - Q).map f = P.map f - Q.map f :=
    fun P Q => Matrix.map_sub f (map_sub f) P Q
  have hone : (1 : Matrix (Fin n) (Fin n) (A ⊗[F] E)).map f = 1 :=
    Matrix.map_one f (map_zero f) (map_one f)
  have hdiag : ∀ d : Fin r → A ⊗[F] E, (diagonal d).map f = diagonal (fun i => f (d i)) := fun d => by
    ext i j
    by_cases h : i = j <;> simp [diagonal, h]
  change leviMat σ J A' X Y (M.map f) = (leviMat σ J A X Y M).map f
  have hentry : ∀ (P : Matrix (Fin r) (Fin r) (A ⊗[F] E)) (i : Fin r), f (P i i) = (P.map f) i i :=
    fun _ _ => rfl
  simp only [leviMat, hadd, hsub, hmul, hone, hdiag, hentry, hZ]

end GlobalTheory.CompanionTheory.KFin
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviMatrixOne
section
noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.KFin.LeviOne

theorem sum_parts {S : Type} [Ring S] {n r : ℕ} {a b : Matrix (Fin n) (Fin r) S} {c d : Matrix (Fin r) (Fin n) S}
    (ca : c * a = 0) (db : d * b = 0) (cb : c * b = 1) (da : d * a = 1) :
    a * Matrix.diagonal (fun i => (d * (1 : Matrix (Fin n) (Fin n) S) * a) i i) * d +
      b * Matrix.diagonal (fun i => (c * (1 : Matrix (Fin n) (Fin n) S) * b) i i) * c +
      (1 - a * d - b * c) * (1 : Matrix (Fin n) (Fin n) S) * (1 - a * d - b * c) = 1 := by
  have hd : ∀ m : Matrix (Fin r) (Fin r) S, m = 1 → Matrix.diagonal (fun i => m i i) = 1 := by
    intro m hm
    subst hm
    simp
  have hPa : (1 - a * d - b * c) * a = 0 := by
    rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, da, Matrix.mul_assoc, ca, Matrix.mul_one,
      Matrix.mul_zero]
    simp
  have hPb : (1 - a * d - b * c) * b = 0 := by
    rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, db, Matrix.mul_assoc, cb, Matrix.mul_one,
      Matrix.mul_zero]
    simp
  have hPP : (1 - a * d - b * c) * (1 - a * d - b * c) = 1 - a * d - b * c := by
    conv_lhs => rw [Matrix.mul_sub (1 - a * d - b * c) (1 - a * d) (b * c), Matrix.mul_sub (1 - a * d - b * c) 1 (a * d)]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPa, hPb, Matrix.zero_mul, Matrix.zero_mul, Matrix.mul_one]
    simp
  rw [Matrix.mul_one, Matrix.mul_one, Matrix.mul_one, hPP, hd _ da, hd _ cb, Matrix.mul_one, Matrix.mul_one]
  abel

theorem leviMat_one : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ (A : Type) [CommRing A] [Algebra F A], leviMat σ J A X Y (1 : Matrix (Fin n) (Fin n) (A ⊗[F] E)) = 1 := by
  intro F E _ _ _ _ _ σ n J r X Y h hJ hW A _ _
  have hX : cT (σ : E →+* E) (cT (σ : E →+* E) X) = X := by
    ext i j
    simp [cT, cm_conj_conj h]
  have hJJ : cT (σ : E →+* E) J = J := by
    ext i j
    simpa [cT] using hJ.1 i j
  have yx : cT (σ : E →+* E) Y * J * X = 1 := by
    have e := congrArg (cT (σ : E →+* E)) hW.xy
    rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul, hX, hJJ, Formalism.UG.cT_one, ← Matrix.mul_assoc] at e
    exact e
  have m0 : ∀ {M : Matrix (Fin r) (Fin n) E} {N : Matrix (Fin n) (Fin r) E}, M * N = 0 →
      M.map (inclR (F := F) A) * N.map (inclR (F := F) A) = 0 := by
    intro M N e
    rw [← Matrix.map_mul, e, Matrix.map_zero _ (map_zero _)]
  have m1 : ∀ {M : Matrix (Fin r) (Fin n) E} {N : Matrix (Fin n) (Fin r) E}, M * N = 1 →
      M.map (inclR (F := F) A) * N.map (inclR (F := F) A) = 1 := by
    intro M N e
    rw [← Matrix.map_mul, e, Matrix.map_one _ (map_zero _) (map_one _)]
  exact sum_parts (m0 hW.xx) (m0 hW.yy) (m1 hW.xy) (m1 yx)

end GlobalTheory.CompanionTheory.KFin.LeviOne

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalBridgeLubinTateFieldStatement
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical
open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open scoped GroundTheory.PAdicHodge.CyclNorms

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_bridge_lubin_tate_field : ∀ {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω (Dec (F := E) A) O), GlobalTheory.Pst.Induces Bw →
    ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [Algebra F (Om l)] [ValuativeExtension F (Om l)] [IsSepClosure F (Om l)]
    (σ : ↥(Dec (F := E) A)), (σ : G E Ω) ∈ Ine (F := E) A → ∀ g : Om l ≃ₐ[F] Om l,
    (∀ y, g y = ((Bw.e σ : ↥(GK Bw.Kw)) : GQ l) y) → unramifiedDegree F (Om l) g = 1 := by
  first | exact @GlobalTheory.CompanionTheory.LTLink.unramifiedDegree_eq_one_of_mem_inertia | exact GlobalTheory.CompanionTheory.LTLink.unramifiedDegree_eq_one_of_mem_inertia | (intros; apply GlobalTheory.CompanionTheory.LTLink.unramifiedDegree_eq_one_of_mem_inertia <;> assumption)
end
end

