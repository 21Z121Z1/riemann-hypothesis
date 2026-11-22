import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0008
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0554
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0574
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BilinearVacuumNonzeroCuspForm
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilRepresentationContinuous
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0301
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0190
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0253
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0258
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0015
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0565
import Formalism.LocalToGlobal.InertKernelTheory.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0577
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0512
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0563
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0572
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0569
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0575
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1459
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0576

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsStandardAuxiliaryFramesAllRowGrids
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFin

section Gen

variable {D : D7} {A B : HSp D} {c σ : ℕ}

theorem isAuxiliaryVectorWittDec_evenFourierJacobiRescale (d : HermitianOrthogonalExtensionData A B c (-1)) (h : c = 2 * σ) :
    IsAuxiliaryVectorWittDec d (GlobalTheory.AscInh.rescale (GlobalTheory.RowUnf.jacDec d h) (fun p => (-D.host.xi0) ^ (p.1 + 1))
      fun _ => GlobalTheory.AscInh.xiPow_ne D _) := by
  refine ⟨by omega, ?_, fun p => (star ((-D.host.xi0) ^ (p.1 + 1)))⁻¹, ?_⟩
  · ext i p
    simp only [GlobalTheory.AscInh.rescale, GlobalTheory.RowUnf.jacDec, HermitianOrthogonalExtensionData.iso, colsOf, Matrix.mul_diagonal, Matrix.submatrix_apply, id]
    exact mul_comm _ _
  · ext i p
    simp only [GlobalTheory.AscInh.rescale, GlobalTheory.RowUnf.jacDec, colsOf, Matrix.mul_diagonal, Matrix.submatrix_apply, id]
    exact mul_comm _ _

theorem isAuxiliaryVectorWittDec_oddBesselRescale (d : HermitianOrthogonalExtensionData A B c (-1)) (h : c = 2 * σ + 1) :
    IsAuxiliaryVectorWittDec d (GlobalTheory.AscInh.rescale (GlobalTheory.RowUnf.besDec d h) (fun p => (-D.host.xi0) ^ (p.1 + 1))
      fun _ => GlobalTheory.AscInh.xiPow_ne D _) := by
  refine ⟨by omega, ?_, fun p => (star ((-D.host.xi0) ^ (p.1 + 1)))⁻¹, ?_⟩
  · ext i p
    simp only [GlobalTheory.AscInh.rescale, GlobalTheory.RowUnf.besDec, HermitianOrthogonalExtensionData.iso, colsOf, Matrix.mul_diagonal, Matrix.submatrix_apply, id]
    exact mul_comm _ _
  · ext i p
    simp only [GlobalTheory.AscInh.rescale, GlobalTheory.RowUnf.besDec, colsOf, Matrix.mul_diagonal, Matrix.submatrix_apply, id]
    exact mul_comm _ _

theorem coreMat_iA (d : HermitianOrthogonalExtensionData A B c (-1)) (h : c = 2 * σ + 1) :
    GlobalTheory.RowUnf.coreMat d h * (GlobalTheory.OrthSumExists.orthDecHsum D A (GlobalTheory.SeeSaw.Model.nLine D)).iA = frameMat B A d.ι := by
  change (Matrix.fromCols (frameMat B A d.ι) (GlobalTheory.RowUnf.midCol d h)).submatrix id (finSumFinEquiv (m := A.rank) (n := 1)).symm *
    (Matrix.fromRows (1 : Matrix (Fin A.rank) (Fin A.rank) D.host.E) (0 : Matrix (Fin 1) (Fin A.rank) D.host.E)).submatrix
      finSumFinEquiv.symm id = _
  rw [Matrix.submatrix_mul_equiv, Matrix.fromCols_mul_fromRows, Matrix.mul_one, Matrix.mul_zero, add_zero, Matrix.submatrix_id_id]

theorem coreMat_iB (d : HermitianOrthogonalExtensionData A B c (-1)) (h : c = 2 * σ + 1) :
    (GlobalTheory.RowUnf.coreMat d h * (GlobalTheory.OrthSumExists.orthDecHsum D A (GlobalTheory.SeeSaw.Model.nLine D)).iB) *ᵥ
      (fun _ => (-D.host.xi0) ^ 0) = fun i => d.a i ⟨σ, by omega⟩ := by
  have e : GlobalTheory.RowUnf.coreMat d h * (GlobalTheory.OrthSumExists.orthDecHsum D A (GlobalTheory.SeeSaw.Model.nLine D)).iB = GlobalTheory.RowUnf.midCol d h := by
    change (Matrix.fromCols (frameMat B A d.ι) (GlobalTheory.RowUnf.midCol d h)).submatrix id (finSumFinEquiv (m := A.rank) (n := 1)).symm *
      (Matrix.fromRows (0 : Matrix (Fin A.rank) (Fin 1) D.host.E) (1 : Matrix (Fin 1) (Fin 1) D.host.E)).submatrix
        finSumFinEquiv.symm id = _
    rw [Matrix.submatrix_mul_equiv, Matrix.fromCols_mul_fromRows, Matrix.mul_one, Matrix.mul_zero, zero_add,
      Matrix.submatrix_id_id]
  rw [e]
  funext i
  change ∑ j : Fin 1, GlobalTheory.RowUnf.midCol d h i j * (-D.host.xi0) ^ 0 = _
  rw [Fin.sum_univ_one, pow_zero, mul_one]
  rfl

end Gen

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc)

theorem auxiliaryFrames_standard : Std (GlobalTheory.AscInh.auxiliaryFrames G) where
  zA := rfl
  zB := by
    funext i
    simp only [GlobalTheory.AscInh.auxiliaryFrames, GlobalTheory.AscInh.lineDec, Matrix.mulVec, dotProduct, pow_zero, mul_one]
    exact Fin.sum_univ_one _
  ζ ρ := by
    funext i
    show (-D.host.xi0) ^ ρ = (-D.host.xi0) ^ ρ * (-D.host.xi0) ^ 0
    rw [pow_zero, mul_one]
  hB ρ h := isAuxiliaryVectorWittDec_oddBesselRescale _ _
  aB ρ h := coreMat_iA _ _
  zB' ρ h := coreMat_iB _ _
  hJ ρ h := isAuxiliaryVectorWittDec_evenFourierJacobiRescale _ _
  aJ ρ h := rfl

theorem exists_std_frames : All fun {_} _ _ _ {G} _ _ => ∃ F : Frames G, Std F :=
  fun _ _ _ _ _ _ _ G _ _ _ => ⟨_, auxiliaryFrames_standard G⟩

end GlobalTheory.AscFin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaLiftRealCentreAverageEigenvector
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.CenAvgOne

open scoped ContDiff

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

def avg1 {K : Type} [MeasurableSpace K] (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (μ : Measure K)
    (j : K → GA D S) (c : K → ℂ) (Φ : WO S T → ℂ) : WO S T → ℂ :=
  fun w => ∫ k, c k * om (j k, 1) Φ w ∂μ

theorem continuous_fam (hom : IsWeilDatumO ψ S T χS χT om) {Φ : WO S T → ℂ} (hΦ : IsThetaFunO ψ S T Φ) {K : Type}
    [TopologicalSpace K] {p : K → GA D S × GA D T} (hp : Continuous p) :
    Continuous fun q : K × WO S T => om (p q.1) Φ q.2 :=
  (GlobalTheory.ThetaJointCont.continuous_om_oriented hom hΦ).comp ((hp.comp continuous_fst).prodMk continuous_snd)

variable {K : Type} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K)
  [IsFiniteMeasure μ] {j : K → GA D S} {c : K → ℂ} {Φ : WO S T → ℂ}

theorem isThetaFunction_average_compactFamily_weilTranslates (hom : IsWeilDatumO ψ S T χS χT om) (hjc : Continuous j) (hj : ∀ k, j k ∈ GinfC S)
    (hc : Continuous c) (hΦ : IsThetaFunO ψ S T Φ) : IsThetaFunO ψ S T (avg1 om μ j c Φ) := by
  have hψ := hom.std
  have hp : Continuous fun k => (j k, (1 : GA D T)) := hjc.prodMk continuous_const
  refine ⟨fun γ w => ?_, ?_, ?_, ?_⟩
  · simp only [avg1]
    rw [← integral_const_mul]
    congr 1
    funext k
    rw [(hom.om_pres _ _ hΦ).quasi]
    ring
  · obtain ⟨U, hU, h⟩ := hΦ.level
    refine ⟨U, hU, fun u hu hu0 => ?_⟩
    funext w
    simp only [heisO, avg1]
    rw [← integral_const_mul]
    congr 1
    funext k
    have := congrFun (hom.om_heis (j k) 1 u Φ hΦ) w
    rw [h u hu hu0, GlobalTheory.FrComb.actO_real (hj k) (GinfC T).one_mem hu0] at this
    rw [this, heisO]
    ring
  · exact GlobalTheory.AvgFam.continuous_avg μ (F := fun k w => c k * om (j k, 1) Φ w)
      ((hc.comp continuous_fst).mul (continuous_fam hom hΦ hp))
  · let gen : Set (K → WO S T → ℂ) := {F | ∃ (c : K → ℂ) (G : WO S T → ℂ), Continuous c ∧ IsThetaFunO ψ S T G ∧
      F = fun k => c k • om (j k, 1) G}
    have h1 : ∀ F ∈ Submodule.span ℂ gen, Continuous fun q : K × WO S T => F q.1 q.2 := by
      intro F hF
      induction hF using Submodule.span_induction with
      | mem F h =>
        obtain ⟨c, G, hc, hG, rfl⟩ := h
        exact (hc.comp continuous_fst).mul (continuous_fam hom hG hp)
      | zero => exact continuous_const
      | add F F' _ _ h h' => exact h.add h'
      | smul a F _ h => exact h.const_smul a
    have h2 : ∀ F ∈ Submodule.span ℂ gen, ∀ k, IsThetaFunO ψ S T (F k) := by
      intro F hF
      induction hF using Submodule.span_induction with
      | mem F h =>
        obtain ⟨c, G, hc, hG, rfl⟩ := h
        exact fun k => GlobalTheory.WeilVacMove.isTheta_smul _ (hom.om_pres _ _ hG)
      | zero => exact fun _ => GlobalTheory.WeilVacMove.isTheta_zero
      | add F F' _ _ h h' => exact fun k => GlobalTheory.WeilVacMove.isTheta_add (h k) (h' k)
      | smul a F _ h => exact fun k => GlobalTheory.WeilVacMove.isTheta_smul a (h k)
    have h3 : ∀ F ∈ Submodule.span ℂ gen, ∀ M : ℝ →+ WO S T, Continuous M → (∀ s, (M s).map (finPart D) = 0) →
        (fun k => GlobalTheory.WeilVacMove.dLine ψ S T M (F k)) ∈ Submodule.span ℂ gen := by
      intro F hF M hM hM0
      induction hF using Submodule.span_induction with
      | mem F h =>
        obtain ⟨c, G, hc, hG, rfl⟩ := h
        obtain ⟨m, N, e, hN, hN0, he, hexp⟩ := GlobalTheory.HeisLineComb.dLine_om_comb D ψ S T χS χT om hom M hM hM0
        have key : (fun k => GlobalTheory.WeilVacMove.dLine ψ S T M (c k • om (j k, 1) G)) =
            ∑ i, fun k => (c k * e i (j k, 1)) • om (j k, 1) (GlobalTheory.WeilVacMove.dLine ψ S T (N i) G) := by
          funext k
          rw [GlobalTheory.CenAvg.dLine_smul, hexp _ _ hG, Finset.smul_sum, Finset.sum_apply]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [smul_smul]
        rw [key]
        exact Submodule.sum_mem _ fun i _ => Submodule.subset_span
          ⟨_, _, hc.mul ((he i).comp hp), (GlobalTheory.WeilVacMove.hasDerivAt_zero_and_isTheta hψ (hN i) (hN0 i) hG).2, rfl⟩
      | zero =>
        have : (fun k : K => GlobalTheory.WeilVacMove.dLine ψ S T M ((0 : K → WO S T → ℂ) k)) = 0 := by
          funext k x
          simp [GlobalTheory.WeilVacMove.dLine, heisO]
        rw [this]
        exact Submodule.zero_mem _
      | add F F' hF hF' h h' =>
        have : (fun k => GlobalTheory.WeilVacMove.dLine ψ S T M ((F + F') k)) =
            (fun k => GlobalTheory.WeilVacMove.dLine ψ S T M (F k)) + fun k => GlobalTheory.WeilVacMove.dLine ψ S T M (F' k) :=
          funext fun k => GlobalTheory.CenAvg.dLine_add hψ hM hM0 (h2 F hF k) (h2 F' hF' k)
        rw [this]
        exact Submodule.add_mem _ h h'
      | smul a F _ h =>
        have : (fun k => GlobalTheory.WeilVacMove.dLine ψ S T M ((a • F) k)) = a • fun k => GlobalTheory.WeilVacMove.dLine ψ S T M (F k) :=
          funext fun k => GlobalTheory.CenAvg.dLine_smul M a (F k)
        rw [this]
        exact Submodule.smul_mem _ a h
    intro n L hL hL0 w
    have := GlobalTheory.ThetaAvgSmooth.avg_smooth D ψ hψ S T K μ (Submodule.span ℂ gen : Set _) h1 h2 h3 _
      (Submodule.subset_span (show _ ∈ gen from ⟨c, Φ, hc, hΦ, rfl⟩)) n L hL hL0 w
    simpa only [avg1, Pi.smul_apply, smul_eq_mul] using this

theorem weilOperator_average_eq_average_translated [SecondCountableTopology K] [IsTopologicalGroup (GA D S)] [IsTopologicalGroup (GA D T)]
    (hom : IsWeilDatumO ψ S T χS χT om) (hjc : Continuous j) (hj : ∀ k, j k ∈ GinfC S)
    (hc : Continuous c) (hΦ : IsThetaFunO ψ S T Φ) (p : GA D S × GA D T) (x : WO S T) :
    om p (avg1 om μ j c Φ) x = ∫ k, c k * om (p * (j k, 1)) Φ x ∂μ := by
  have hp : Continuous fun k => (j k, (1 : GA D T)) := hjc.prodMk continuous_const
  have hm : ∀ k, om p (om (j k, 1) Φ) = om (p * (j k, 1)) Φ := fun k => by
    rw [map_mul, Module.End.mul_apply]
  have := GlobalTheory.CenAvg.om_integral μ hom hc (F := fun k => om (j k, 1) Φ) p (fun k => hom.om_pres _ _ hΦ)
    (continuous_fam hom hΦ hp) (by simp only [hm]; exact continuous_fam hom hΦ (continuous_const.mul hp))
    (isThetaFunction_average_compactFamily_weilTranslates μ hom hjc hj hc hΦ) x
  simp only [hm] at this
  exact this

end GlobalTheory.CenAvgOne

namespace GlobalTheory.CenAvgOne

theorem exists_central_average_one : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → S.SigOK → S.IsDefinite → ∀ (ν : Measure (GA D S)) (fd : Set (GA D S)), ν.IsHaarMeasure → IsFundamentalDomain (GQ S) fd ν → ∀ (χ φ : GA D S → ℂ), GlobalTheory.SeeSaw.HasCen S χ φ → GlobalTheory.Unf.IsContAut S φ → ∀ Φ, IsThetaFunO ψ S T Φ → (∀ h, IntegrableOn (fun g => thetaKO om g h Φ * φ g) fd ν) → ∃ Φ', IsThetaFunO ψ S T Φ' ∧ (∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) → om (z, 1) Φ' = (χ z)⁻¹ • Φ') ∧ ∀ h, ∫ g in fd, thetaKO om g h Φ * φ g ∂ν = ∫ g in fd, thetaKO om g h Φ' * φ g ∂ν := by
  intro D ψ S T χS χT om hom hsig hdef ν fd hν hfd χ φ hcen hφ Φ hΦ hint
  by_cases hz : φ = 0
  · subst hz
    exact ⟨0, GlobalTheory.WeilVacMove.isTheta_zero, fun z _ _ => by simp, fun h => by simp⟩
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D S
  obtain ⟨j1, -, -, -, -, -⟩ := GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D T
  let Z : Subgroup (GA D S) := GinfC S ⊓ Subgroup.center (GA D S)
  have hcl : IsClosed (Subgroup.center (GA D S) : Set (GA D S)) := by
    have : (Subgroup.center (GA D S) : Set (GA D S)) = ⋂ g, {a | g * a = a * g} := by
      ext a
      simp only [SetLike.mem_coe, Subgroup.mem_center_iff, Set.mem_iInter, Set.mem_setOf_eq]
    rw [this]
    exact isClosed_iInter fun g => isClosed_eq (continuous_const.mul continuous_id) (continuous_id.mul continuous_const)
  haveI : CompactSpace Z :=
    isCompact_iff_compactSpace.mp ((Formalism.IndefR.Eqv.isCompact_GinfC hsig hdef).inter_right hcl)
  let m : Measure Z := GlobalTheory.haarProb Z
  obtain ⟨h₀, hh₀⟩ := Function.ne_iff.1 hz
  have hh : φ h₀ ≠ 0 := hh₀
  have hmul : ∀ a b : Z, χ (a * b : Z) = χ a * χ b := by
    intro a b
    apply mul_right_cancel₀ hh
    rw [← hcen _ (a * b).2.1 (a * b).2.2, Subgroup.coe_mul, ← mul_assoc, hcen _ b.2.1 b.2.2, hcen _ a.2.1 a.2.2]
    ring
  have hone : χ 1 = 1 := by
    apply mul_right_cancel₀ hh
    rw [← hcen _ (one_mem _) (one_mem _), mul_one, one_mul]
  have hcont : Continuous fun a : Z => χ a := by
    have : (fun a : Z => χ a) = fun a : Z => φ (h₀ * a) / φ h₀ := by
      funext a
      rw [hcen _ a.2.1 a.2.2, mul_div_cancel_right₀ _ hh]
    rw [this]
    exact (hφ.2.comp (continuous_const.mul continuous_subtype_val)).div_const _
  have hj : ∀ a : Z, (a : GA D S) ∈ GinfC S := fun a => a.2.1
  refine ⟨avg1 om m Subtype.val (fun a => χ a) Φ, isThetaFunction_average_compactFamily_weilTranslates m hom continuous_subtype_val hj hcont hΦ,
    fun a ha1 ha2 => ?_, fun h => ?_⟩
  · let a' : Z := ⟨a, ha1, ha2⟩
    have hne : χ a ≠ 0 := by
      intro h0
      have := hmul a'⁻¹ a'
      rw [inv_mul_cancel, OneMemClass.coe_one, hone] at this
      change 1 = χ (a'⁻¹ : Z) * χ a at this
      rw [h0, mul_zero] at this
      exact one_ne_zero this
    funext u
    rw [weilOperator_average_eq_average_translated m hom continuous_subtype_val hj hcont hΦ]
    simp only [Pi.smul_apply, smul_eq_mul, avg1]
    rw [← integral_mul_left_eq_self (μ := m) (fun b : Z => χ b * om ((b : GA D S), 1) Φ u) a', ← integral_const_mul]
    congr 1
    funext b
    rw [hmul a' b]
    change _ = (χ a)⁻¹ * (χ a * χ b * om ((a * b : GA D S), 1) Φ u)
    rw [Prod.mk_mul_mk, mul_one]
    field_simp
  · haveI : Countable (GQ S) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig S.gram
    haveI : ν.IsMulRightInvariant := Formalism.IndefR.Eqv.unimodGA_holds S ν hν
    have hF_inv : ∀ γ ∈ GQ S, ∀ g, thetaKO om (γ * g) h Φ * φ (γ * g) = thetaKO om g h Φ * φ g := by
      intro γ hγ g
      have : om (γ * g, h) Φ 0 = om (g, h) Φ 0 := by
        rw [show ((γ * g, h) : GA D S × GA D T) = (γ, 1) * (g, h) by rw [Prod.mk_mul_mk, one_mul], map_mul,
          Module.End.mul_apply, hom.om_aut γ hγ 1 (one_mem _) _ (hom.om_pres _ _ hΦ)]
      simp only [thetaKO, this, hφ.1 γ hγ g]
    have hF_cont : Continuous fun g => thetaKO om g h Φ * φ g :=
      ((hom.om_cont Φ hΦ 0).comp (continuous_id.prodMk continuous_const)).mul hφ.2
    have key : ∀ g, thetaKO om g h (avg1 om m Subtype.val (fun a => χ a) Φ) * φ g =
        ∫ k : Z, thetaKO om (g * k) h Φ * φ (g * k) ∂m := by
      intro g
      unfold thetaKO
      rw [weilOperator_average_eq_average_translated m hom continuous_subtype_val hj hcont hΦ, ← integral_mul_const]
      congr 1
      funext k
      rw [Prod.mk_mul_mk, mul_one, hcen _ k.2.1 k.2.2]
      ring
    simp_rw [key]
    exact (GlobalTheory.Chain.IoLift.AvgLift.setIntegral_average (GQ S) ν hfd m continuous_subtype_val
      (Φ := fun g => thetaKO om g h Φ * φ g) hF_inv hF_cont (hint h)).symm

end GlobalTheory.CenAvgOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryCoordinateOfRationalPointDefiniteVe
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open GlobalTheory.RatMoveJets

namespace GlobalTheory.RatMoveJets

theorem exists_unitary_ratCoord {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {W : G.Weil}
    (S : GridChoice W Set.univ) (X : Node) (hX : DefNode D.R.m X) (r : FinPt G X) (hr : GlobalTheory.MovedKappaEx.RatFin (G.V X) r) :
    ∃ U : Matrix.unitaryGroup (Fin (G.V X).rank) D.host.E, GlobalTheory.RatMoveJets.RatCoord (G.V X) (S.N.fr X) r U := by
  obtain ⟨γ, hγ, hf⟩ := hr
  obtain ⟨γ', h1, h2⟩ := id hγ
  have hG : star γ'.1 * (G.V X).gram * γ'.1 = (G.V X).gram := h1
  have hmt : Formalism.L2.Theta.mt (G.V X) γ = γ'.1.map (incA D) := congrArg Units.val h2.symm
  set F := (S.N.fr X).1 with hFdef
  set Fi := ((S.N.fr X)⁻¹ : GL (Fin (G.V X).rank) D.host.E).1 with hFidef
  have hF : star F * (G.V X).gram * F = 1 := S.N.fr_on X hX
  have e1 : Fi * F = 1 := by rw [hFdef, hFidef]; exact Units.inv_mul _
  have e2 : F * Fi = 1 := by rw [hFdef, hFidef]; exact Units.mul_inv _
  have hGram : star Fi * Fi = (G.V X).gram := by
    have : star Fi * (star F * (G.V X).gram * F) * Fi = (G.V X).gram := by
      calc star Fi * (star F * (G.V X).gram * F) * Fi = star (F * Fi) * (G.V X).gram * (F * Fi) := by
            rw [star_mul]; simp only [Matrix.mul_assoc]
        _ = (G.V X).gram := by rw [e2, star_one, Matrix.one_mul, Matrix.mul_one]
    rw [hF, Matrix.mul_one] at this
    exact this
  have hU : star (Fi * γ'.1 * F) * (Fi * γ'.1 * F) = 1 := by
    calc star (Fi * γ'.1 * F) * (Fi * γ'.1 * F) = star F * (star γ'.1 * (star Fi * Fi) * γ'.1) * F := by
          simp only [star_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hGram, hG]; exact hF
  refine ⟨⟨Fi * γ'.1 * F, Matrix.mem_unitaryGroup_iff'.2 hU⟩, γ, hγ, hf, ?_⟩
  rw [hmt]
  congr 1
  change γ'.1 = F * (Fi * γ'.1 * F) * Fi
  simp only [← Matrix.mul_assoc, e2, Matrix.one_mul]
  rw [Matrix.mul_assoc, e2, Matrix.mul_one]

end GlobalTheory.RatMoveJets
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstRowArgumentConjugateMoveLeftMulInvComponent
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.FirstRowCoord

open GlobalTheory.RowMoveAt

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem actO_chi_small (i : ℕ) (M : GA D (G.V (.grid i D.R.m)))
    (x : WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))) :
    actO _ _ (G.toPair (.chi i D.R.m) M 1).1⁻¹ (G.toPair (.chi i D.R.m) M 1).2⁻¹ x =
      mt (G.V (.grid i D.R.m)) M⁻¹ * (x : Matrix _ _ (AE D)) := by
  simp only [actO, GridData.toPair, inv_inv, map_one, inv_one]
  rw [show mt (G.pS (.chi i D.R.m : Pair T)) 1 = 1 from rfl, Matrix.mul_one]

theorem rowAt_first_move : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T},
    t ∈ U → ∀ w ∈ locPl G t, ∀ (k : FinPt G (.grid 0 D.R.m))
      (ys : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))),
      S.rowAt t w (Function.update ys (GlobalTheory.FirstRowVertex.firstIx D) (actO (G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T))
        (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).1⁻¹
        (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).2⁻¹ (ys (GlobalTheory.FirstRowVertex.firstIx D)))) =
      Function.update (S.rowAt t w ys) 0 (((GlobalTheory.FirstRowTermLaw.kapAt S t w k)⁻¹ : GL (Fin ((locGrid G t w).rank (0, (locGrid G t w).m))) (Kw w)).val * S.rowAt t w ys 0) := by
  intro D T L sc G W U S t ht w hw k ys
  have hX : DefNode D.R.m (.grid 0 D.R.m) := ⟨Nat.zero_le _, rfl⟩
  obtain ⟨P, e, he, hsupp, hoff⟩ := S.N.u_supp _ hX
  have hn := notOff S ht hw
  have hu := map_mt_eq_one hn he hoff hsupp
  have hu' := map_mt_eq_one hn he hoff (GlobalTheory.StdHalfLat.suppAt_inv' hsupp)
  have hM' : (mt _ ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1⁻¹).map ((cpt w).comp (toEAf D)) =
      (loc w (finG (G.V (.grid 0 D.R.m)) k⁻¹)).val := by
    rw [show mt _ ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1⁻¹ =
        mt _ (S.N.u (.grid 0 D.R.m)).1⁻¹ * mt _ k.1⁻¹ * mt _ (S.N.u (.grid 0 D.R.m)).1 from by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv, mul_assoc]; rfl,
      Matrix.map_mul, Matrix.map_mul, hu, hu', Matrix.one_mul, Matrix.mul_one]
    rfl
  have h0 : 0 < D.R.m := (GlobalTheory.FirstRowVertex.firstIx D).2
  funext i
  by_cases h1 : i = 0
  · subst h1
    rw [Function.update_self]
    simp only [GridChoice.rowAt, dif_pos h0, Frames.coord]
    erw [Function.update_self, actO_chi_small 0, Matrix.map_mul, hM']
    erw [Matrix.transpose_transpose, Matrix.transpose_transpose]
    rw [GlobalTheory.FirstRowTermLaw.kapAt]
    erw [← map_inv (inBasis _ (S.B.β 0 D.R.m) w)]
    rw [map_inv (finG (G.V (Node.grid 0 D.R.m))) k]
    erw [inBasis_val, mul_sub_cast]
    rfl
  · rw [Function.update_of_ne h1]
    simp only [GridChoice.rowAt]
    by_cases hi : i < D.R.m
    · rw [dif_pos hi, dif_pos hi, Function.update_of_ne (fun h => h1 (congrArg Fin.val h))]
    · rw [dif_neg hi, dif_neg hi]

end GlobalTheory.FirstRowCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatIntegrandFlippedTensorLocallyConstantCompactStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatIntegrand_flippedTensor_locallyConstant_compactSupport : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A) (CF b : ℝ), HidaSetting large₂ R F → ch.Is → ch.AtScale CF b → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ch.S.SumOK t Φ → ∀ β ∈ ch.S.supp t Φ, ∀ (w : locPl ch.G t) X Y, IsLocallyConstant (flatIntegrand one_le_sLen (psiAt ch.W w.1) (moved (locGrid ch.G t w) (keepAt ch.G w) ((repsAt ch.G t w).elt (β w)) (Tflip ch.W ch.S.B t Φ w)) X Y) ∧ HasCompactSupport (flatIntegrand one_le_sLen (psiAt ch.W w.1) (moved (locGrid ch.G t w) (keepAt ch.G w) ((repsAt ch.G t w).elt (β w)) (Tflip ch.W ch.S.B t Φ w)) X Y) := by
  first | exact @GlobalTheory.FlipIntegrand.flatIntegrand_lc_cpt | exact GlobalTheory.FlipIntegrand.flatIntegrand_lc_cpt | (intros; apply GlobalTheory.FlipIntegrand.flatIntegrand_lc_cpt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockGaussianJetsAtOriginEqFockVectorsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fock_gaussian_jets_at_origin_eq_fock_vectors : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), IsStdChar D ψ (-1) → GlobalTheory.FockCompare.Chart θ σ → ∀ (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T), ∃ C : (FVar D T.rank S.rank →₀ ℕ) → ℂ, ∀ f : WO S T → ℂ, GlobalTheory.ChainFr.IsVacF ψ θ A B f → ∀ (x : WO S T) (m : FVar D T.rank S.rank →₀ ℕ), derivAt0 (rd ψ σ A B f x) m = C m * GlobalTheory.ChainFr.ptF ψ θ A B f (MvPolynomial.monomial m 1) x := by
  first | exact @GlobalTheory.FockTransl.Jet.jet_eq_fock | exact GlobalTheory.FockTransl.Jet.jet_eq_fock | (intros; apply GlobalTheory.FockTransl.Jet.jet_eq_fock <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVacuaSpanFiniteDimensionalStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockVacua_span_finiteDimensional : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' →
    FiniteDimensional ℂ (Submodule.span ℂ {f₀ : SInf F (Fin n × Fin d) | M.IsGauss B.ψ B.emb f₀}) := by
  first | exact @GlobalTheory.FockVac.span_finiteDimensional | exact GlobalTheory.FockVac.span_finiteDimensional | (intros; apply GlobalTheory.FockVac.span_finiteDimensional <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiStepBasePointColumnsPrimitiveStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierJacobiStep_basePoint_columns_primitive : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∀ v ∉ G.pl.S0, ColsAt (F.dJ (σ + 1) h) (xFB F σ h') (G.Λ (.grid (2 * σ + 3) 0)) (G.Λ (.grid (2 * σ + 2) 0)) v := by
  first | exact @GlobalTheory.ColsFB.cols_fb | exact GlobalTheory.ColsFB.cols_fb | (intros; apply GlobalTheory.ColsFB.cols_fb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridTopVertexFormFunctionContinuousLeftInvariantStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gridTopVertexFormFunction_continuous_left_invariant : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ t y, Continuous (formTop ch t y) ∧
    ∀ γ ∈ GQ (ch.G.V (.grid 0 D.R.m)), ∀ g, formTop ch t y (γ * g) = formTop ch t y g := by
  first | exact @GlobalTheory.FormTopAut.formTop_cont_left | exact GlobalTheory.FormTopAut.formTop_cont_left | (intros; apply GlobalTheory.FormTopAut.formTop_cont_left <;> assumption)
end

