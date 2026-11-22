import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0825
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0080
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0074
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0943
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0936
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0901
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0928
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleEquivalenceSchemeOfStrictlyHenselianStalks
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0347
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0018
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0945
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0456
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0481
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PiTensorLiftCompSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0188
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalRingCardinality.Bundle0007
import Formalism.LocalRingCardinality.Bundle0003

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableFockVacuumGaussianDefinitePair
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.VacRealForm

open GlobalTheory.FockCompare GlobalTheory.VacUnique

variable {D : D7}

def entryR {m n : ℕ} (τ : D.what₂.Tau) (a : Fin m) (b : Fin n) : (D.what₂.Tau → Fin m → Fin n → ℂ) →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) b).comp
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) a).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : D.what₂.Tau => Fin m → Fin n → ℂ) τ))

theorem entryR_apply {m n : ℕ} (τ : D.what₂.Tau) (a : Fin m) (b : Fin n) (Z : D.what₂.Tau → Fin m → Fin n → ℂ) :
    entryR τ a b Z = Z τ a b := rfl

def dSq {m n : ℕ} (Z : D.what₂.Tau → Fin m → Fin n → ℂ) : (D.what₂.Tau → Fin m → Fin n → ℂ) →L[ℝ] ℝ :=
  ∑ τ, ∑ a, ∑ b, (2 : ℕ) • (innerSL ℝ (Z τ a b)).comp (entryR τ a b)

theorem dSq_apply {m n : ℕ} (Z V : D.what₂.Tau → Fin m → Fin n → ℂ) :
    dSq Z V = ∑ τ, ∑ a, ∑ b, 2 * (V τ a b * starRingEnd ℂ (Z τ a b)).re := by
  simp [dSq, ContinuousLinearMap.sum_apply, entryR_apply, Complex.inner, two_mul]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem hasFDerivAt_sqSum {m n : ℕ} (Z : D.what₂.Tau → Fin m → Fin n → ℂ) :
    HasFDerivAt (fun Z : D.what₂.Tau → Fin m → Fin n → ℂ => sqSum Z) (dSq Z) Z := by
  unfold sqSum dSq
  refine HasFDerivAt.fun_sum (𝕜 := ℝ) (u := Finset.univ) (A := fun τ (Z : D.what₂.Tau → Fin m → Fin n → ℂ) => ∑ a, ∑ b, ‖Z τ a b‖ ^ 2)
    fun τ _ => ?_
  refine HasFDerivAt.fun_sum (𝕜 := ℝ) (u := Finset.univ) (A := fun a (Z : D.what₂.Tau → Fin m → Fin n → ℂ) => ∑ b, ‖Z τ a b‖ ^ 2)
    fun a _ => ?_
  refine HasFDerivAt.fun_sum (𝕜 := ℝ) (u := Finset.univ) (A := fun b (Z : D.what₂.Tau → Fin m → Fin n → ℂ) => ‖Z τ a b‖ ^ 2)
    fun b _ => ?_
  exact (entryR τ a b).hasFDerivAt.norm_sq

def frL {m n : ℕ} (B : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (B' : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) :
    (D.what₂.Tau → Fin m → Fin n → ℂ) →L[ℂ] (D.what₂.Tau → Fin m → Fin n → ℂ) :=
  let l : (D.what₂.Tau → Fin m → Fin n → ℂ) →ₗ[ℂ] (D.what₂.Tau → Fin m → Fin n → ℂ) :=
    { toFun := frPt B B'
      map_add' := fun x y => by
        funext τ
        show B' τ * Matrix.of (x τ + y τ) * (B τ)⁻¹ = B' τ * Matrix.of (x τ) * (B τ)⁻¹ + B' τ * Matrix.of (y τ) * (B τ)⁻¹
        rw [show Matrix.of (x τ + y τ) = Matrix.of (x τ) + Matrix.of (y τ) from rfl, Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c x => by
        funext τ
        show B' τ * Matrix.of (c • x τ) * (B τ)⁻¹ = c • (B' τ * Matrix.of (x τ) * (B τ)⁻¹)
        rw [show Matrix.of (c • x τ) = c • Matrix.of (x τ) from rfl, Matrix.mul_smul, Matrix.smul_mul] }
  ⟨l, LinearMap.continuous_of_finiteDimensional l⟩

theorem frL_apply {m n : ℕ} (B : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (B' : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ)
    (Z : D.what₂.Tau → Fin m → Fin n → ℂ) : frL B B' Z = frPt B B' Z := rfl

def toCLin {m n : ℕ} (L : (D.what₂.Tau → Fin m → Fin n → ℂ) →L[ℝ] ℂ)
    (hL : ∀ v, L (Complex.I • v) = Complex.I * L v) : (D.what₂.Tau → Fin m → Fin n → ℂ) →L[ℂ] ℂ :=
  let l : (D.what₂.Tau → Fin m → Fin n → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := L
      map_add' := L.map_add
      map_smul' := fun c v => by
        have e : c • v = c.re • v + c.im • (Complex.I • v) := by
          funext τ a b
          simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Complex.real_smul]
          conv_lhs => rw [← Complex.re_add_im c]
          ring
        rw [e, L.map_add, L.map_smul, L.map_smul, hL, RingHom.id_apply, Complex.real_smul, Complex.real_smul]
        conv_rhs => rw [← Complex.re_add_im c]
        ring }
  ⟨l, LinearMap.continuous_of_finiteDimensional l⟩

theorem toCLin_restrict {m n : ℕ} (L : (D.what₂.Tau → Fin m → Fin n → ℂ) →L[ℝ] ℂ)
    (hL : ∀ v, L (Complex.I • v) = Complex.I * L v) : (toCLin L hL).restrictScalars ℝ = L := by
  ext v; rfl

end GlobalTheory.VacRealForm

namespace GlobalTheory.VacRealForm

open GlobalTheory.FockCompare GlobalTheory.VacUnique

variable {D : D7}

theorem realPlace_cmTrace_zero_element_eq_I_mul_abs (τ : D.what₂.Tau) : tauE D τ D.host.xi0 = ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * Complex.I := by
  have hre := GlobalTheory.RealSymplForm.realPlace_imaginaryGenerator_re_eq_zero D τ
  have him := Formalism.L2.Theta.xi_zero_im_pos D τ
  have hn := ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatB.norm_embedding_hostFormConstant_eq D (tauE D τ)
  have e : tauE D τ D.host.xi0 = (((tauE D τ D.host.xi0).im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hre]
  rw [e, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos him] at hn
  rw [e, hn]

theorem hAt_frame {S T : HSp D} (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E)
    (hS : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1)
    (hT : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1) (τ : D.what₂.Tau)
    (Z V : Fin T.rank → Fin S.rank → ℂ) :
    hAt S T τ (GlobalTheory.FockPos.frAt frT τ * Matrix.of Z * (GlobalTheory.FockPos.frAt frS τ)⁻¹)
      (GlobalTheory.FockPos.frAt frT τ * Matrix.of V * (GlobalTheory.FockPos.frAt frS τ)⁻¹) =
      ∑ a, ∑ b, starRingEnd ℂ (V a b) * Z a b := by
  set B := GlobalTheory.FockPos.frAt frS τ
  set B' := GlobalTheory.FockPos.frAt frT τ
  have h1 : Bᴴ * gramAt D S τ * B = 1 := GlobalTheory.FockPos.frAt_on frS hS τ
  have h2 : B'ᴴ * gramAt D T τ * B' = 1 := GlobalTheory.FockPos.frAt_on frT hT τ
  have hBd : IsUnit B.det := isUnit_iff_ne_zero.2 (GlobalTheory.FockPos.frAt_det_ne frS τ)
  have hGi : (gramAt D S τ)⁻¹ = B * Bᴴ := by
    apply Matrix.inv_eq_right_inv
    have e1 : Bᴴ * (gramAt D S τ * B) = 1 := by rw [← Matrix.mul_assoc]; exact h1
    rw [← Matrix.mul_assoc]
    exact mul_eq_one_comm.1 e1
  have hBB : Bᴴ * (B⁻¹)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Matrix.nonsing_inv_mul _ hBd, Matrix.conjTranspose_one]
  have e : (gramAt D S τ)⁻¹ * (B' * Matrix.of V * B⁻¹)ᴴ * gramAt D T τ * (B' * Matrix.of Z * B⁻¹) =
      B * ((Matrix.of V)ᴴ * Matrix.of Z * B⁻¹) := by
    rw [hGi]
    calc B * Bᴴ * (B' * Matrix.of V * B⁻¹)ᴴ * gramAt D T τ * (B' * Matrix.of Z * B⁻¹)
        = B * ((Bᴴ * (B⁻¹)ᴴ) * (Matrix.of V)ᴴ * (B'ᴴ * gramAt D T τ * B') * Matrix.of Z * B⁻¹) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = B * ((Matrix.of V)ᴴ * Matrix.of Z * B⁻¹) := by
          rw [hBB, h2, Matrix.one_mul, Matrix.mul_one]
  unfold hAt
  rw [e, Matrix.trace_mul_comm, Matrix.nonsing_inv_mul_cancel_right _ _ hBd]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, RCLike.star_def]
  exact Finset.sum_comm

end GlobalTheory.VacRealForm

namespace GlobalTheory.VacRealForm

open GlobalTheory.FockCompare GlobalTheory.VacUnique

variable {D : D7}

theorem omO_frame {S T : HSp D} (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E)
    (hS : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1)
    (hT : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1) (Z V : RW T S) :
    omO S T (frPt (fun τ => GlobalTheory.FockPos.frAt frS τ) (fun τ => GlobalTheory.FockPos.frAt frT τ) Z)
      (frPt (fun τ => GlobalTheory.FockPos.frAt frS τ) (fun τ => GlobalTheory.FockPos.frAt frT τ) V) =
      ∑ τ, ∑ a, ∑ b, 2 * (((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * Complex.I * (starRingEnd ℂ (V τ a b) * Z τ a b)).re := by
  rw [omO_apply]
  refine Finset.sum_congr rfl fun τ _ => ?_
  unfold GlobalTheory.VacUnique.omAt
  rw [frPt, frPt, hAt_frame frS frT hS hT τ (Z τ) (V τ), realPlace_cmTrace_zero_element_eq_I_mul_abs]
  simp only [Finset.mul_sum, Complex.re_sum]

theorem differentiable_gZ_of_frames {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : Chart θ σ)
    {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (frS : GL (Fin S.rank) D.host.E)
    (frT : GL (Fin T.rank) D.host.E)
    (hS : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1)
    (hT : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (hcS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (hcT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) (f : WO S T → ℂ)
    (hf : IsThetaFunO ψ S T f) (hfock : ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) :
    Differentiable ℂ (gZ σ S T (fun τ => (frS.1).map (tauE D τ)) (fun τ => (frT.1).map (tauE D τ)) f) := by
  obtain rfl := GlobalTheory.FockPos.cart_one frS hS hcS
  obtain rfl := GlobalTheory.FockPos.cart_one frT hT hcT
  obtain ⟨hd, hann⟩ := GlobalTheory.T.fockVacuum_annihilation_equation_real_coordinates D θ σ h ψ hψ S T _ _ f hf hfock
  have hJ : ∀ z : RW T S, jO S T (fun _ => (1 : Matrix (Fin S.rank) (Fin S.rank) ℂ))
      (fun _ => (1 : Matrix (Fin T.rank) (Fin T.rank) ℂ)) z = Complex.I • z := fun z => by
    funext τ i k
    simp [jO_apply, cplxO, Matrix.mul_apply, Matrix.one_apply, Pi.mul_apply, Pi.one_apply]
    first
      | exact congrFun (congrFun (Matrix.one_mul (M := (z τ : Matrix (Fin T.rank) (Fin S.rank) ℂ))) i) k
      | (erw [Matrix.mul_apply]; simp [Matrix.one_apply])
      | (rw [Matrix.one_mul])
  set F : RW T S → ℂ := fun z => f (iotaW σ T S z) with hF
  set Φ := frL (fun τ => GlobalTheory.FockPos.frAt frS τ) (fun τ => GlobalTheory.FockPos.frAt frT τ) with hΦ
  intro Z
  have h1 : HasFDerivAt (fun Z => F (Φ Z)) ((fderiv ℝ F (Φ Z)).comp (Φ.restrictScalars ℝ)) Z :=
    (hd (Φ Z)).hasFDerivAt.comp Z (Φ.restrictScalars ℝ).hasFDerivAt
  have h2 : HasFDerivAt (fun Z : RW T S => Complex.exp ((Real.pi * Formalism.L2.Pj.xiR D * sqSum Z : ℝ) : ℂ))
      (Complex.exp ((Real.pi * Formalism.L2.Pj.xiR D * sqSum Z : ℝ) : ℂ) •
        Complex.ofRealCLM.comp ((Real.pi * Formalism.L2.Pj.xiR D) • dSq Z)) Z :=
    (Complex.ofRealCLM.hasFDerivAt.comp Z ((hasFDerivAt_sqSum Z).const_mul (Real.pi * Formalism.L2.Pj.xiR D))).cexp
  have h3 := h1.mul h2
  refine (hasFDerivAt_of_restrictScalars ℝ h3 (toCLin_restrict _ ?_)).differentiableAt
  intro v
  have hω1 : omO S T (Φ Z) (Φ v) = -(Formalism.L2.Pj.xiR D * dSq Z (Complex.I • v)) := by
    rw [hΦ, frL_apply, frL_apply, omO_frame frS frT hS hT, dSq_apply]
    simp only [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    simp [Complex.mul_re, Complex.mul_im]
    ring
  have hω2 : omO S T (Φ Z) (Complex.I • Φ v) = Formalism.L2.Pj.xiR D * dSq Z v := by
    rw [← map_smul, hΦ, frL_apply, frL_apply, omO_frame frS frT hS hT, dSq_apply]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    simp [Complex.mul_re, Complex.mul_im]
    ring
  have ha := hann (Φ Z) (Φ v)
  rw [hJ, hω1, hω2, show f (iotaW σ T S (Φ Z)) = F (Φ Z) from rfl] at ha
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', map_smul, Complex.ofRealCLM_apply, smul_eq_mul]
  push_cast at ha ⊢
  generalize Complex.exp ((Real.pi : ℂ) * (Formalism.L2.Pj.xiR D : ℂ) * (sqSum Z : ℂ)) = E
  generalize (fderiv ℝ F (Φ Z)) (Complex.I • Φ v) = b at ha ⊢
  generalize (fderiv ℝ F (Φ Z)) (Φ v) = a at ha ⊢
  linear_combination (-Complex.I * E) * ha + (F (Φ Z) * E * Real.pi * Formalism.L2.Pj.xiR D * ((dSq Z (Complex.I • v) : ℝ) : ℂ) +
    E * b - Complex.I * F (Φ Z) * E * Real.pi * Formalism.L2.Pj.xiR D * ((dSq Z v : ℝ) : ℂ)) * Complex.I_sq

end GlobalTheory.VacRealForm

namespace GlobalTheory.VacRealForm

theorem differentiable_gZ_top : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (W : G.Weil) {U : Set T} (N : GlobalTheory.FunObj.Std G U) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart W.θ σ → ∀ (t : T) (j : ℕ), j + 1 ≤ D.R.m → ∀ f, IsVacO W.ψ W.θ _ _ (G.cartS W.cart (.top t j)) (G.onT W.cart (.top t j)) (N.latS (.top t j) : Set _) (N.latT (.top t j) : Set _) f → Differentiable ℂ (GlobalTheory.VacRealForm.gZ σ (G.pS (.top t j)) (G.pT (.top t j)) (N.frC (.top j)) (N.frC (.top (j + 1))) f) := by
  intro D T L sc G W U N σ hσ t j hj f hf
  exact differentiable_gZ_of_frames hσ hf.1 _ _ (N.fr (.top j)) (N.fr (.top (j + 1)))
    (N.fr_on (.top j) (show j ≤ D.R.m by omega)) (N.fr_on (.top (j + 1)) (show j + 1 ≤ D.R.m from hj)) _ _
    (W.cart_is (.top j) (show j ≤ D.R.m by omega)) (W.cart_is (.top (j + 1)) (show j + 1 ≤ D.R.m from hj)) f
    hf.2.theta hf.2.fock

end GlobalTheory.VacRealForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOnDoubleCosetOfEqOnArchimedeanSliceStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_on_doubleCoset_of_eq_on_archimedeanSlice : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (b W : GA E (m + 1) → ℂ) (V : Subgroup (GL (Fin (m + 1)) (Af E))) (q : GA E (m + 1)), q ∈ GlobalTheory.JSW.mirS E S m → GeneralLinearGroup.map (pInf E) q = 1 → (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) → (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) → (∀ u ∈ V, ∀ g, b (g * finGL E (m + 1) u) = b g) → (∀ u ∈ V, ∀ g, W (g * finGL E (m + 1) u) = W g) → (∀ y : GL (Fin (m + 1)) (Cinf E), q * infGL E (m + 1) y ∈ GlobalTheory.JSW.mirS E S m → W (q * infGL E (m + 1) y) = b (q * infGL E (m + 1) y)) → ∀ p ∈ GlobalTheory.JSW.mirS E S m, p ∈ GlobalTheory.JSW.MirPatch.cell V q → W p = b p := by
  first | exact @GlobalTheory.JSW.MirPatch.eq_on_cell_of_eq_on_slice | exact GlobalTheory.JSW.MirPatch.eq_on_cell_of_eq_on_slice | (intros; apply GlobalTheory.JSW.MirPatch.eq_on_cell_of_eq_on_slice <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleEquivalenceSchemeOfStrictlyHenselianStalksStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleEquivalence_scheme_of_strictlyHenselian_stalks : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (Y X S : Scheme.{0}) (f : Y ⟶ X) (p : X ⟶ S) [QuasiCompact p] [QuasiSeparated p] [QuasiCompact f] [QuasiSeparated f], (∀ (O : Type) [CommRing O] (s : Spec (CommRingCat.of O) ⟶ S), IsStalk O s → Eqv R (sch.map (pullback.map (f ≫ p) s p s f (𝟙 _) (𝟙 _) (by simp) (by simp))) F) → Eqv R (sch.map f) F := by
  first
  | exact @GlobalTheory.EtC.eqv_sch_of_stalks
  | exact GlobalTheory.EtC.eqv_sch_of_stalks
  | (intros; apply GlobalTheory.EtC.eqv_sch_of_stalks <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvarianceCechDescentIntegral
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC.CechDescHInv

theorem yoneda_spec_widePullback (A B T : Type) [CommRing A] [CommRing B] [CommRing T] (a : A →+* B) (k : ℕ)
    (ι : Fin (k + 1) → (B →+* T)) (hι : ∀ j, (ι j).comp a = (ι 0).comp a)
    (hu : ∀ (R : Type) [CommRing R] (g : Fin (k + 1) → (B →+* R)), (∀ j, (g j).comp a = (g 0).comp a) →
      ∃! φ : T →+* R, ∀ j, φ.comp (ι j) = g j) :
    ∃ e : yoneda.obj (Spec (CommRingCat.of T)) ≅ widePullback (yoneda.obj (Spec (CommRingCat.of A)))
        (fun _ : Fin (k + 1) => yoneda.obj (Spec (CommRingCat.of B))) (fun _ => yoneda.map (Spec.map (CommRingCat.ofHom a))),
      ∀ j, e.hom ≫ WidePullback.π _ j = yoneda.map (Spec.map (CommRingCat.ofHom (ι j))) :=
  GlobalTheory.T.spec_widePushout_iso_widePullback_yoneda A B T a k ι hι hu

theorem tensor_univ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (k : ℕ) (R : Type) [CommRing R]
    (g : Fin (k + 1) → (B →+* R)) (hg : ∀ j, (g j).comp (algebraMap A B) = (g 0).comp (algebraMap A B)) :
    ∃! φ : PiTensorProduct A (fun _ : Fin (k + 1) => B) →+* R,
      ∀ j, φ.comp (PiTensorProduct.singleAlgHom (R := A) (A := fun _ : Fin (k + 1) => B) j).toRingHom = g j := by
  classical
  letI : Algebra A R := ((g 0).comp (algebraMap A B)).toAlgebra
  let g' : Fin (k + 1) → (B →ₐ[A] R) := fun j => ⟨g j, fun r => RingHom.congr_fun (hg j) r⟩
  refine ⟨(GlobalTheory.piTensorLift g').toRingHom, fun j => ?_, fun ψ hψ => ?_⟩
  · ext x
    exact GlobalTheory.piTensorLift_single g' j x
  · have hc : ∀ r : A, ψ (algebraMap A (PiTensorProduct A fun _ : Fin (k + 1) => B) r) = algebraMap A R r := by
      intro r
      have h1 : algebraMap A (PiTensorProduct A fun _ : Fin (k + 1) => B) r =
          PiTensorProduct.singleAlgHom (R := A) (A := fun _ : Fin (k + 1) => B) 0 (algebraMap A B r) :=
        ((PiTensorProduct.singleAlgHom (R := A) (A := fun _ : Fin (k + 1) => B) 0).commutes r).symm
      rw [h1]
      exact RingHom.congr_fun (hψ 0) (algebraMap A B r)
    let ψ' : PiTensorProduct A (fun _ : Fin (k + 1) => B) →ₐ[A] R := ⟨ψ, hc⟩
    have : ψ' = GlobalTheory.piTensorLift g' := PiTensorProduct.algHom_ext fun j => by
      ext x
      change ψ _ = _
      rw [AlgHom.comp_apply, GlobalTheory.piTensorLift_single]
      exact RingHom.congr_fun (hψ j) x
    exact congrArg AlgHom.toRingHom this

theorem poly_univ (A B T : Type) [CommRing A] [CommRing B] [CommRing T] (a : A →+* B) (k : ℕ)
    (ι : Fin (k + 1) → (B →+* T))
    (hu : ∀ (R : Type) [CommRing R] (g : Fin (k + 1) → (B →+* R)), (∀ j, (g j).comp a = (g 0).comp a) →
      ∃! φ : T →+* R, ∀ j, φ.comp (ι j) = g j)
    (R : Type) [CommRing R] (g : Fin (k + 1) → (Polynomial B →+* R))
    (hg : ∀ j, (g j).comp (Polynomial.mapRingHom a) = (g 0).comp (Polynomial.mapRingHom a)) :
    ∃! φ : Polynomial T →+* R, ∀ j, φ.comp (Polynomial.mapRingHom (ι j)) = g j := by
  have hX : ∀ j, g j Polynomial.X = g 0 Polynomial.X := fun j => by
    have := RingHom.congr_fun (hg j) Polynomial.X
    simpa using this
  obtain ⟨ψ, hψ, hψu⟩ := hu R (fun j => (g j).comp Polynomial.C) (fun j => by
    ext x
    have := RingHom.congr_fun (hg j) (Polynomial.C x)
    simpa using this)
  refine ⟨Polynomial.eval₂RingHom ψ (g 0 Polynomial.X), fun j => ?_, fun φ hφ => ?_⟩
  · apply Polynomial.ringHom_ext
    · intro b
      simpa using RingHom.congr_fun (hψ j) b
    · simp [hX j]
  · have hC : φ.comp Polynomial.C = ψ := hψu _ (fun j => by
      ext b
      simpa using RingHom.congr_fun (hφ j) (Polynomial.C b))
    apply Polynomial.ringHom_ext
    · intro t
      simpa using RingHom.congr_fun hC t
    · simpa using RingHom.congr_fun (hφ 0) Polynomial.X

theorem spec_integral_surj (A B : Type) [CommRing A] [CommRing B] (φ : A →+* B) (hi : φ.IsIntegral)
    (hk : RingHom.ker φ ≤ nilradical A) :
    IsIntegralHom (Spec.map (CommRingCat.ofHom φ)) ∧ Surjective (Spec.map (CommRingCat.ofHom φ)) := by
  refine ⟨IsIntegralHom.SpecMap_iff.2 hi, ⟨fun (x : PrimeSpectrum A) => ?_⟩⟩
  letI := φ.toAlgebra
  haveI : Algebra.IsIntegral A B := ⟨hi⟩
  have hle : (⊥ : Ideal B).comap (algebraMap A B) ≤ x.asIdeal := by
    rw [← RingHom.ker_eq_comap_bot]
    exact hk.trans (nilradical_le_prime x.asIdeal)
  obtain ⟨Q, -, hQ, hQx⟩ := Ideal.exists_ideal_over_prime_of_isIntegral x.asIdeal ⊥ hle
  have : x ∈ Set.range (PrimeSpectrum.comap φ) := ⟨⟨Q, hQ⟩, PrimeSpectrum.ext hQx⟩
  exact this

theorem poly_isIntegral (A B : Type) [CommRing A] [CommRing B] (φ : A →+* B) (hi : φ.IsIntegral) :
    (Polynomial.mapRingHom φ).IsIntegral := by
  letI := (Polynomial.mapRingHom φ).toAlgebra
  have hC : ∀ b : B, IsIntegral (Polynomial A) (Polynomial.C b) := by
    intro b
    obtain ⟨f, hf, hfb⟩ := hi b
    refine ⟨f.map Polynomial.C, hf.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have e : (algebraMap (Polynomial A) (Polynomial B)).comp Polynomial.C = Polynomial.C.comp φ := by
      ext x <;> simp [RingHom.algebraMap_toAlgebra]
    rw [e, ← Polynomial.hom_eval₂, hfb, map_zero]
  have hXi : IsIntegral (Polynomial A) (Polynomial.X : Polynomial B) := by
    have : (Polynomial.X : Polynomial B) = algebraMap (Polynomial A) (Polynomial B) Polynomial.X := by
      simp [RingHom.algebraMap_toAlgebra]
    rw [this]; exact isIntegral_algebraMap
  intro p
  change IsIntegral (Polynomial A) p
  induction p using Polynomial.induction_on with
  | C b => exact hC b
  | add p r hp hr => exact hp.add hr
  | monomial n b _ => exact (hC b).mul (hXi.pow _)

theorem poly_ker (A B : Type) [CommRing A] [CommRing B] (φ : A →+* B) (hk : RingHom.ker φ ≤ nilradical A) :
    RingHom.ker (Polynomial.mapRingHom φ) ≤ nilradical (Polynomial A) := by
  intro p hp
  rw [mem_nilradical, Polynomial.isNilpotent_iff]
  intro n
  rw [← mem_nilradical]
  apply hk
  rw [RingHom.mem_ker] at hp ⊢
  have := congrArg (fun r => Polynomial.coeff r n) hp
  simpa using this

theorem isUnit_gamma (q : ℕ) (A : Type) [CommRing A] (hq : IsUnit (q : A)) :
    IsUnit (q : Γ(Spec (CommRingCat.of A), ⊤)) := by
  have := hq.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  simpa using this

theorem hInv_of_integral (q : ℕ) [NeZero q] (A B : Type) [CommRing A] [CommRing B] [Algebra A B] :
    Algebra.IsIntegral A B → RingHom.ker (algebraMap A B) ≤ nilradical A → IsUnit (q : A) →
    (∀ k : ℕ, HInv q (PiTensorProduct A (fun _ : Fin (k + 1) => B))) → HInv q A := by
  intro hint hker hq hT i
  have hi : (algebraMap A B).IsIntegral := fun x => hint.isIntegral x
  obtain ⟨hf1, hf2⟩ := spec_integral_surj A B (algebraMap A B) hi hker
  obtain ⟨hf1', hf2'⟩ := spec_integral_surj _ _ (Polynomial.mapRingHom (algebraMap A B))
    (poly_isIntegral A B _ hi) (poly_ker A B _ hker)
  have hq' : IsUnit (q : Polynomial A) := by simpa using hq.map (Polynomial.C : A →+* Polynomial A)
  have E := GlobalTheory.T.etaleCohomologyEquivalence_basic_properties (ZMod q) (tw q i)
  have h1 := GlobalTheory.EtC.b4 q (Spec.map (CommRingCat.ofHom (algebraMap A B))) (isUnit_gamma q A hq) i
  have h1' := GlobalTheory.EtC.b4 q (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap A B))))
    (isUnit_gamma q _ hq') i
  let F : Arrow.mk (yoneda.map (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap A B))))) ⟶
      Arrow.mk (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A B)))) :=
    Arrow.homMk (yoneda.map (Spec.map (CommRingCat.ofHom (Polynomial.C : B →+* Polynomial B))))
      (yoneda.map (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)))) (by
        simp only [Arrow.mk_hom, ← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
        congr 3
        ext x <;> simp)
  let m : cech (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap A B)))) ⟶
      cech (Spec.map (CommRingCat.ofHom (algebraMap A B))) := Arrow.mapCechNerve F
  have hsq : m ≫ cechAug (Spec.map (CommRingCat.ofHom (algebraMap A B))) =
      cechAug (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap A B)))) ≫
        spMap (Polynomial.C : A →+* Polynomial A) := by
    clear E h1 h1' hT hf1 hf2 hf1' hf2' hint hker hq hq' hi
    refine NatTrans.ext (funext fun n => ?_)
    change WidePullback.lift _ _ _ ≫ WidePullback.base _ = WidePullback.base _ ≫ yoneda.map (Spec.map _)
    apply WidePullback.lift_base
  have hm : Eqv _ m (tw q i) := by
    refine GlobalTheory.T.levelwiseEquivalence_isEquivalence _ m _ (fun n => ?_)
    clear h1 h1' hf1 hf2 hf1' hf2' hint hker hq hq' hi hsq
    set k := n.unop.len
    let T := PiTensorProduct A (fun _ : Fin (k + 1) => B)
    let ι : Fin (k + 1) → (B →+* T) := fun j =>
      (PiTensorProduct.singleAlgHom (R := A) (A := fun _ : Fin (k + 1) => B) j).toRingHom
    have hι : ∀ j, (ι j).comp (algebraMap A B) = (ι 0).comp (algebraMap A B) := by
      intro j; ext x; simp [ι]
    have hu := tensor_univ A B k
    obtain ⟨e, he⟩ := yoneda_spec_widePullback A B T (algebraMap A B) k ι hι hu
    have hι' : ∀ j, (Polynomial.mapRingHom (ι j)).comp (Polynomial.mapRingHom (algebraMap A B)) =
        (Polynomial.mapRingHom (ι 0)).comp (Polynomial.mapRingHom (algebraMap A B)) := by
      intro j; rw [Polynomial.mapRingHom_comp, Polynomial.mapRingHom_comp, hι j]
    obtain ⟨e', he'⟩ := yoneda_spec_widePullback (Polynomial A) (Polynomial B) (Polynomial T)
      (Polynomial.mapRingHom (algebraMap A B)) k (fun j => Polynomial.mapRingHom (ι j)) hι'
      (poly_univ A B T (algebraMap A B) k ι (fun R _ g hg => hu R g hg))
    let mn : widePullback (yoneda.obj (Spec (CommRingCat.of (Polynomial A))))
        (fun _ : Fin (k + 1) => yoneda.obj (Spec (CommRingCat.of (Polynomial B))))
        (fun _ => yoneda.map (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap A B))))) ⟶
        widePullback (yoneda.obj (Spec (CommRingCat.of A)))
        (fun _ : Fin (k + 1) => yoneda.obj (Spec (CommRingCat.of B)))
        (fun _ => yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A B)))) :=
      WidePullback.lift (WidePullback.base _ ≫ yoneda.map (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))))
        (fun j => WidePullback.π _ j ≫ yoneda.map (Spec.map (CommRingCat.ofHom (Polynomial.C : B →+* Polynomial B))))
        (fun j => by
          rw [Category.assoc, ← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
            ← WidePullback.π_arrow _ j, Category.assoc, ← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
          congr 4
          ext x <;> simp)
    have hmn : m.app n = mn := rfl
    have hπ : ∀ j, (e'.hom ≫ mn) ≫ WidePullback.π _ j =
        (yoneda.map (Spec.map (CommRingCat.ofHom (Polynomial.C : T →+* Polynomial T))) ≫ e.hom) ≫ WidePullback.π _ j := by
      intro j
      rw [Category.assoc, WidePullback.lift_π, ← Category.assoc, he' j, Category.assoc, he j,
        ← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Functor.map_comp, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp]
      congr 3
      ext x <;> simp
    have key : e'.hom ≫ mn = yoneda.map (Spec.map (CommRingCat.ofHom (Polynomial.C : T →+* Polynomial T))) ≫ e.hom := by
      apply WidePullback.hom_ext
      · exact hπ
      · rw [← WidePullback.π_arrow _ 0, ← Category.assoc, ← Category.assoc, hπ 0]
    have h3 : Eqv _ (disc.map e'.hom ≫ disc.map mn) (tw q i) := by
      rw [← Functor.map_comp, key, Functor.map_comp]
      exact (E.2.1 _ _ _ _ _).1 (hT k i) (E.1 _ _ _ (disc.mapIso e).isIso_hom)
    rw [hmn]
    exact (E.2.1 _ _ _ _ _).2.1 (E.1 _ _ _ (disc.mapIso e').isIso_hom) h3
  have h2 : Eqv _ (cechAug (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap A B)))) ≫
      spMap (Polynomial.C : A →+* Polynomial A)) (tw q i) := by
    rw [← hsq]; exact (E.2.1 _ _ _ _ _).1 hm h1
  exact (E.2.1 _ _ _ _ _).2.1 h1' h2

end GlobalTheory.EtC.CechDescHInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSideOfModels
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdelicSide

theorem adForms_eq_of_reps {Gr Γ : Type} [Group Gr] [Group Γ] (ι : Γ →* Gr) {Wc : Type} [NormedAddCommGroup Wc]
    [InnerProductSpace ℂ Wc] (ρ : Γ →* Module.End ℂ Wc) {J J' : Subgroup Gr} (χ : J →* ℂˣ) (hle : J' ≤ J) {I : Type}
    {y : I → Gr} (hy : Bridge.IsReps ι J' y) {f f' : Gr → Wc} (h1 : f ∈ Bridge.AdForms ι ρ J χ)
    (h2 : f' ∈ Bridge.AdForms ι ρ J χ) (h : ∀ k, f (y k) = f' (y k)) : f = f' := by
  funext g
  obtain ⟨k, ⟨γ, u, rfl⟩, -⟩ := hy g
  have m1 := h1 γ (y k) ⟨u, hle u.2⟩
  have m2 := h2 γ (y k) ⟨u, hle u.2⟩
  rw [h k] at m1
  exact m1.trans m2.symm

set_option maxHeartbeats 1000000 in

theorem exists_thAd_of_models : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.IsModels → ∀ (i : Fin D.R.m) (t : T0) (K' : Type) [Field K'] (σ' : K' →+* ℂ) (c0' : VsV D i K' →ₛₗ[σ'] (R.cV i).W) (Cl : Type) (h : Cl → GA D (Vc D i)) (J' : Subgroup (Bridge.Gf (Vc D i))), J' ≤ levJ R i t → Bridge.IsReps (Bridge.ratF (Vc D i)) J' (fun k => FWT.fin _ (h k)) → ∀ v₀ : (R.MW i (sg0 D A)).Vec, ∃ thAd, ThAdIs R i t h c0' v₀ thAd := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hR i t K' _ σ' c0' Cl h J' hle hr v₀
  classical
  obtain ⟨hinj, hrange, -⟩ := hR.HV i t
  have huniq : ∀ y y' x, Place R i t h c0' y x → Place R i t h c0' y' x → y = y' := fun y y' x h1 h2 =>
    hinj (adForms_eq_of_reps _ _ _ hle hr (hrange.le (LinearMap.mem_range_self _ y))
      (hrange.le (LinearMap.mem_range_self _ y')) fun k => (h1 k).trans (h2 k).symm)
  refine ⟨fun x => if hx : ∃ y, Place R i t h c0' y x then onQ (Wc D i) (R.thF i t hx.choose v₀) else 0, fun y x hy => ?_⟩
  have hx : ∃ y, Place R i t h c0' y x := ⟨y, hy⟩
  simp only [dif_pos hx]
  rw [huniq _ _ _ hx.choose_spec hy]

end GlobalTheory.AdelicSide
end

