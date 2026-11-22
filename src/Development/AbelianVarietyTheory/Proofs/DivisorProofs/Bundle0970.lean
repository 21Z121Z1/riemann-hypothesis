import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0943
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0079
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0074
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne
import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle0018
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0125
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0767
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0957
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingFormsIffProportionalPullbacks
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0941
import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridTopVertexFramePointTransportLattice
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacuumRealRestrictionGaussianEntire
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockPos

theorem differentiable_mul_of_cr {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (G E : V → ℂ) (c : V → V → ℂ)
    (hG : Differentiable ℝ G) (hE : Differentiable ℝ E)
    (hGc : ∀ Z Y, fderiv ℝ G Z Y + Complex.I * fderiv ℝ G Z (Complex.I • Y) = -(c Z Y * G Z))
    (hEc : ∀ Z Y, fderiv ℝ E Z Y + Complex.I * fderiv ℝ E Z (Complex.I • Y) = c Z Y * E Z) :
    Differentiable ℂ (fun Z => G Z * E Z) := by
  intro Z
  have hL := (hG Z).hasFDerivAt.mul (hE Z).hasFDerivAt
  set L : V →L[ℝ] ℂ := G Z • fderiv ℝ E Z + E Z • fderiv ℝ G Z with hLdef
  have hI : ∀ Y, L (Complex.I • Y) = Complex.I * L Y := fun Y => by
    have h1 := hGc Z Y
    have h2 := hEc Z Y
    simp only [hLdef, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    linear_combination (-(Complex.I * E Z)) * h1 + (-(Complex.I * G Z)) * h2 +
      (E Z * fderiv ℝ G Z (Complex.I • Y) + G Z * fderiv ℝ E Z (Complex.I • Y)) * Complex.I_sq
  have hsm : ∀ (a : ℂ) (Y : V), L (a • Y) = a * L Y := fun a Y => by
    have e : a • Y = a.re • Y + a.im • (Complex.I • Y) := by
      rw [← Complex.coe_smul, ← Complex.coe_smul, smul_smul, ← add_smul]
      congr 1
      exact (Complex.re_add_im a).symm
    rw [e, L.map_add, L.map_smul, L.map_smul, hI, Complex.real_smul, Complex.real_smul]
    conv_rhs => rw [← Complex.re_add_im a]
    ring
  let g : V →L[ℂ] ℂ :=
    { toFun := fun Y => L Y
      map_add' := fun Y Y' => L.map_add Y Y'
      map_smul' := fun a Y => hsm a Y
      cont := L.continuous }
  exact (differentiableAt_iff_restrictScalars ℝ hL.differentiableAt).2 ⟨g, by rw [hL.fderiv]; ext Y; rfl⟩

theorem gauss_cr {ι : Type} [Fintype ι] {m n : ℕ} (r : ℝ) :
    Differentiable ℝ (fun Z : ι → Fin m → Fin n → ℂ =>
      Complex.exp ((Real.pi * r * ∑ τ, ∑ a, ∑ b, ‖Z τ a b‖ ^ 2 : ℝ) : ℂ)) ∧
    ∀ Z Y : ι → Fin m → Fin n → ℂ,
      fderiv ℝ (fun Z : ι → Fin m → Fin n → ℂ =>
          Complex.exp ((Real.pi * r * ∑ τ, ∑ a, ∑ b, ‖Z τ a b‖ ^ 2 : ℝ) : ℂ)) Z Y +
        Complex.I * fderiv ℝ (fun Z : ι → Fin m → Fin n → ℂ =>
          Complex.exp ((Real.pi * r * ∑ τ, ∑ a, ∑ b, ‖Z τ a b‖ ^ 2 : ℝ) : ℂ)) Z (Complex.I • Y) =
      (2 * Real.pi * r * ∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y τ a b) : ℂ) *
        Complex.exp ((Real.pi * r * ∑ τ, ∑ a, ∑ b, ‖Z τ a b‖ ^ 2 : ℝ) : ℂ) := by
  let P : ι → Fin m → Fin n → ((ι → Fin m → Fin n → ℂ) →L[ℝ] ℂ) := fun τ a b =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) b).comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) a).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => Fin m → Fin n → ℂ) τ))
  have hP : ∀ τ a b (Z : ι → Fin m → Fin n → ℂ), P τ a b Z = Z τ a b := fun _ _ _ _ => rfl
  have hq : ∀ Z : ι → Fin m → Fin n → ℂ, HasFDerivAt (fun Z : ι → Fin m → Fin n → ℂ => ∑ τ, ∑ a, ∑ b, ‖Z τ a b‖ ^ 2)
      (∑ τ, ∑ a, ∑ b, (2 : ℕ) • (innerSL ℝ (Z τ a b)).comp (P τ a b)) Z := fun Z => by
    refine HasFDerivAt.fun_sum fun τ _ => HasFDerivAt.fun_sum fun a _ => HasFDerivAt.fun_sum fun b _ => ?_
    exact (P τ a b).hasFDerivAt.norm_sq
  have hE : ∀ Z : ι → Fin m → Fin n → ℂ, HasFDerivAt (fun Z : ι → Fin m → Fin n → ℂ =>
      Complex.exp ((Real.pi * r * ∑ τ, ∑ a, ∑ b, ‖Z τ a b‖ ^ 2 : ℝ) : ℂ))
      (Complex.exp ((Real.pi * r * ∑ τ, ∑ a, ∑ b, ‖Z τ a b‖ ^ 2 : ℝ) : ℂ) •
        Complex.ofRealCLM.comp ((Real.pi * r) • ∑ τ, ∑ a, ∑ b, (2 : ℕ) • (innerSL ℝ (Z τ a b)).comp (P τ a b))) Z :=
    fun Z => (Complex.ofRealCLM.hasFDerivAt.comp Z ((hq Z).const_mul (Real.pi * r))).cexp
  refine ⟨fun Z => (hE Z).differentiableAt, fun Z Y => ?_⟩
  rw [(hE Z).fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_sum',
    Finset.sum_apply, smul_eq_mul, Complex.ofRealCLM_apply, innerSL_apply_apply, hP, Pi.smul_apply,
    ContinuousLinearMap.smul_apply, nsmul_eq_mul]
  have key : ∀ z y : ℂ, z * starRingEnd ℂ y =
      ((inner ℝ z y : ℝ) : ℂ) + Complex.I * ((inner ℝ z (Complex.I * y) : ℝ) : ℂ) := by
    intro z y
    rw [Complex.inner, Complex.inner]
    apply Complex.ext <;> simp <;> ring
  simp_rw [key]
  push_cast
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

theorem trace_frames {m n : ℕ} (GS B : Matrix (Fin n) (Fin n) ℂ) (GT B' : Matrix (Fin m) (Fin m) ℂ)
    (hB : Bᴴ * GS * B = 1) (hB' : B'ᴴ * GT * B' = 1) (Z Y : Matrix (Fin m) (Fin n) ℂ) :
    (GS⁻¹ * (B' * Y * B⁻¹)ᴴ * GT * (B' * Z * B⁻¹)).trace = ∑ a, ∑ b, Z a b * starRingEnd ℂ (Y a b) := by
  have e : GS⁻¹ * (B' * Y * B⁻¹)ᴴ * GT * (B' * Z * B⁻¹) = (GS⁻¹ * (B⁻¹)ᴴ) * (Yᴴ * Z) * B⁻¹ := by
    calc _ = GS⁻¹ * (B⁻¹)ᴴ * Yᴴ * (B'ᴴ * GT * B') * Z * B⁻¹ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hB', Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have e2 : B⁻¹ * (GS⁻¹ * (B⁻¹)ᴴ) = 1 := by
    rw [Matrix.conjTranspose_nonsing_inv, ← Matrix.mul_inv_rev, ← Matrix.mul_inv_rev, hB, inv_one]
  rw [e, Matrix.trace_mul_comm, ← Matrix.mul_assoc, e2, Matrix.one_mul]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _

end GlobalTheory.FockPos

open GlobalTheory.FockCompare GlobalTheory.VacUnique

noncomputable section

namespace GlobalTheory.FockPos

variable {D : D7}

def frLin {S T : HSp D} (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E) :
    Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank →L[ℂ] RW T S :=
  LinearMap.toContinuousLinearMap
    { toFun := fun Z τ => (frAt frT τ * Matrix.of (Z τ) * (frAt frS τ)⁻¹ : Matrix (Fin T.rank) (Fin S.rank) ℂ)
      map_add' := fun Y Z => by
        funext τ
        show (frAt frT τ * (Matrix.of (Y τ) + Matrix.of (Z τ)) * (frAt frS τ)⁻¹ : Matrix (Fin T.rank) (Fin S.rank) ℂ) = _ + _
        rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c Z => by
        funext τ
        show (frAt frT τ * (c • Matrix.of (Z τ)) * (frAt frS τ)⁻¹ : Matrix (Fin T.rank) (Fin S.rank) ℂ) = c • _
        rw [Matrix.mul_smul, Matrix.smul_mul] }

theorem frLin_apply {S T : HSp D} (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E)
    (Z : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank) (τ : D.what₂.Tau) :
    frLin frS frT Z τ = (frAt frT τ * Matrix.of (Z τ) * (frAt frS τ)⁻¹ : Matrix (Fin T.rank) (Fin S.rank) ℂ) := rfl

theorem norm_embedding_xi0_eq (D : D7) (τ : D.host.E →+* ℂ) : ‖τ D.host.xi0‖ = Formalism.L2.Pj.xiR D := by
  have hs : ∀ τ : D.host.E →+* ℂ, ‖τ D.host.sqrtMinusD‖ = Real.sqrt D.host.d := by
    intro τ
    have h0 : (τ D.host.sqrtMinusD) ^ 2 = -(D.host.d : ℂ) := by
      rw [← map_pow, Formalism.BasicNotions.Host.sqrtMinusD_sq D.host, map_neg, map_natCast]
    rw [← Real.sqrt_sq (norm_nonneg (τ D.host.sqrtMinusD)), ← norm_pow, h0, norm_neg, Complex.norm_natCast]
  unfold Formalism.L2.Pj.xiR Host.xi0
  simp only [map_div₀, map_neg, map_one, map_mul, map_natCast, norm_div, norm_neg, norm_one, norm_mul,
    Complex.norm_natCast, hs]

theorem xi_zero_eq_host (τ : D.what₂.Tau) : tauE D τ D.host.xi0 = Complex.I * (Formalism.L2.Pj.xiR D : ℂ) := by
  have h1 := GlobalTheory.RealSymplForm.realPlace_imaginaryGenerator_re_eq_zero D τ
  have h2 := Formalism.L2.Theta.xi_zero_im_pos D τ
  have h3 : ‖tauE D τ D.host.xi0‖ = Formalism.L2.Pj.xiR D := norm_embedding_xi0_eq D (tauE D τ)
  have h4 : (tauE D τ D.host.xi0).im = Formalism.L2.Pj.xiR D := by
    rw [← h3, Complex.norm_def, Complex.normSq_apply, h1, zero_mul, zero_add, Real.sqrt_mul_self_eq_abs,
      abs_of_pos h2]
  apply Complex.ext <;> simp [h1, h4]

theorem vacuum_real_entire : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1 → ∀ f : WO S T → ℂ, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) LS LT f → ∃ Φ : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ, Differentiable ℂ Φ ∧ ∀ w : WO S T, w.map (finPart D) = 0 → f w = GlobalTheory.FockPos.gaussO θ frS frT w * Φ (GlobalTheory.FockPos.zCo θ frS frT w) := by
  intro D ψ θ S T frS frT LS LT hS hT f hf
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hf.2.inf
  obtain ⟨hF, hann⟩ := GlobalTheory.VacUnique.Ann.vacuum_annihilation D θ σ hσ ψ hf.1 S T (fun _ => 1) (fun _ => 1) f
    hf.2.theta hf.2.fock
  set F : RW T S → ℂ := fun z => f (iotaW σ T S z) with hFdef
  set X := frLin frS frT with hX
  set r := Formalism.L2.Pj.xiR D with hr
  set E : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ := fun Z =>
    Complex.exp ((Real.pi * r * ∑ τ, ∑ a, ∑ b, ‖Z τ a b‖ ^ 2 : ℝ) : ℂ) with hE
  have hU : ∀ {k : ℕ} (fr : GL (Fin k) D.host.E) τ, IsUnit (frAt fr τ).det := fun fr τ =>
    isUnit_iff_ne_zero.2 (frAt_det_ne fr τ)
  have hG : Differentiable ℝ (fun Z => F (X Z)) := hF.comp (X.restrictScalars ℝ).differentiable
  have hdG : ∀ Z Y, fderiv ℝ (fun Z => F (X Z)) Z Y = fderiv ℝ F (X Z) (X Y) := fun Z Y => by
    have h : HasFDerivAt (fun Z => F (X Z)) ((fderiv ℝ F (X Z)).comp (X.restrictScalars ℝ)) Z :=
      (hF (X Z)).hasFDerivAt.comp Z (X.restrictScalars ℝ).hasFDerivAt
    rw [h.fderiv]
    rfl
  refine ⟨fun Z => F (X Z) * E Z,
    differentiable_mul_of_cr (fun Z => F (X Z)) E
      (fun Z Y => (2 * Real.pi * r * ∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y τ a b) : ℂ))
      hG (gauss_cr r).1 (fun Z Y => ?_) (gauss_cr r).2, fun w hw => ?_⟩
  · rw [hdG, hdG]
    have hj : jO S T (fun _ => 1) (fun _ => 1) (X Y) = X (Complex.I • Y) := by
      rw [X.map_smul]
      funext τ
      rw [jO_apply]
      change Complex.I • ((1 : Matrix (Fin T.rank) (Fin T.rank) ℂ) * Matrix.of (X Y τ) *
        (1 : Matrix (Fin S.rank) (Fin S.rank) ℂ)) = _
      rw [Matrix.one_mul, Matrix.mul_one]
      rfl
    have h := hann (X Z) (X Y)
    rw [hj] at h
    have hom : ∀ Y' : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank, omO S T (X Z) (X Y') =
        ∑ τ, 2 * (Complex.I * (r : ℂ) * ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y' τ a b)).re := by
      intro Y'
      rw [omO_apply]
      refine Finset.sum_congr rfl fun τ _ => ?_
      show 2 * (tauE D τ D.host.xi0 * hAt S T τ (X Z τ) (X Y' τ)).re = _
      unfold hAt
      rw [hX, frLin_apply, frLin_apply, trace_frames _ _ _ _ (frAt_on frS hS τ) (frAt_on frT hT τ), xi_zero_eq_host τ]
      rfl
    rw [hom, hom] at h
    have hs2 : ∀ τ, (∑ a, ∑ b, Z τ a b * starRingEnd ℂ ((Complex.I • Y) τ a b)) =
        -Complex.I * ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y τ a b) := fun τ => by
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_I, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    simp only [hs2] at h
    have key : ((∑ τ, 2 * (Complex.I * (r : ℂ) * ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y τ a b)).re : ℝ) : ℂ) +
        Complex.I * ((∑ τ, 2 * (Complex.I * (r : ℂ) * (-Complex.I * ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y τ a b))).re : ℝ) : ℂ) =
        2 * Complex.I * r * ∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y τ a b) := by
      push_cast
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun τ _ => ?_
      set s := ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y τ a b)
      apply Complex.ext <;> simp <;> ring
    show _ = -((2 * Real.pi * r * ∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y τ a b) : ℂ) * F (X Z))
    have h' : fderiv ℝ F (X Z) (X Y) - Real.pi * Complex.I * ((∑ τ, 2 * (Complex.I * (r : ℂ) * ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y τ a b)).re : ℝ) : ℂ) * F (X Z) +
      Complex.I * (fderiv ℝ F (X Z) (X (Complex.I • Y)) - Real.pi * Complex.I * ((∑ τ, 2 * (Complex.I * (r : ℂ) * (-Complex.I * ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y τ a b))).re : ℝ) : ℂ) * F (X Z)) = 0 := h
    linear_combination h' + Real.pi * Complex.I * F (X Z) * key +
      2 * Real.pi * r * (∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (Y τ a b)) * F (X Z) * Complex.I_sq
  · have e1 : X (zCo θ frS frT w) = piW θ T S w := by
      funext τ
      rw [hX, frLin_apply]
      change frAt frT τ * ((frAt frT τ)⁻¹ * compAt θ τ w * frAt frS τ) * (frAt frS τ)⁻¹ = _
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hU _ τ), Matrix.one_mul, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ (hU _ τ), Matrix.mul_one]
      rfl
    show f w = gaussO θ frS frT w * (f (iotaW σ T S (X (zCo θ frS frT w))) * E (zCo θ frS frT w))
    rw [e1, hσ.iota_pi hw, ← mul_assoc, mul_comm _ (f w), mul_assoc, hE, gaussO, ← Complex.exp_add]
    have e2 : -((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖zCo θ frS frT w τ a b‖ ^ 2 : ℝ) : ℂ) +
        ((Real.pi * r * ∑ τ, ∑ a, ∑ b, ‖zCo θ frS frT w τ a b‖ ^ 2 : ℝ) : ℂ) = 0 := by
      rw [hr]; push_cast; ring
    rw [e2, Complex.exp_zero, mul_one]

end GlobalTheory.FockPos

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusPowRootOfUnity
section
noncomputable section

open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct

namespace GlobalTheory.LKRes.ResSplit

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem dvd_mul_div_gcd (f r : ℕ) : r ∣ f * (r / Nat.gcd f r) := by
  refine ⟨f / Nat.gcd f r, ?_⟩
  rw [← Nat.mul_div_assoc f (Nat.gcd_dvd_right f r), ← Nat.mul_div_assoc r (Nat.gcd_dvd_left f r), mul_comm]

theorem Qr_le_Kn {f : ℕ} (hq : qK p K = p ^ f) (r : ℕ) : Qr p r ≤ Kn p K (r / Nat.gcd f r) := by
  apply UnramifiedExtensions.Kn_le (Q0 p) bot_le
  intro ζ hζ
  apply UnramifiedExtensions.mem_Kn_of_pow K
  rw [residue_cardinality_base_field] at hζ
  obtain ⟨t, ht⟩ := dvd_mul_div_gcd f r
  obtain ⟨c, hc⟩ : p ^ r - 1 ∣ (p ^ r) ^ t - 1 := by simpa using Nat.sub_dvd_pow_sub_pow (p ^ r) 1 t
  rw [hq, ← pow_mul, ht, pow_mul, hc, pow_mul, hζ, one_pow]

def incQ {f : ℕ} (hq : qK p K = p ^ f) (r : ℕ) : Qr p r →ₐ[ℚ_[p]] Kn p K (r / Nat.gcd f r) :=
  IntermediateField.inclusion (Qr_le_Kn p K hq r)

def incK (n : ℕ) : K →ₐ[ℚ_[p]] Kn p K n := IntermediateField.inclusion (UnramifiedExtensions.le_Kn K n)

def comp {f : ℕ} (hq : qK p K = p ^ f) (r i : ℕ) : KQ p K r →ₐ[ℚ_[p]] Kn p K (r / Nat.gcd f r) :=
  Algebra.TensorProduct.productMap (incK p K _) ((incQ p K hq r).comp ((frobQ p r) ^ i))

def eMap {f : ℕ} (hq : qK p K = p ^ f) (r : ℕ) :
    KQ p K r →ₐ[ℚ_[p]] (Fin (Nat.gcd f r) → Kn p K (r / Nat.gcd f r)) :=
  Pi.algHom _ _ fun i => comp p K hq r i

theorem eMap_apply {f : ℕ} (hq : qK p K = p ^ f) (r : ℕ) (x : KQ p K r) (i : Fin (Nat.gcd f r)) :
    eMap p K hq r x i = comp p K hq r i x := rfl

theorem coe_incQ {f : ℕ} (hq : qK p K = p ^ f) (r : ℕ) (b : Qr p r) :
    ((incQ p K hq r b : Kn p K (r / Nat.gcd f r)) : PadicAlgCl p) = b :=
  IntermediateField.coe_inclusion _ _

theorem coe_incK (n : ℕ) (a : K) : ((incK p K n a : Kn p K n) : PadicAlgCl p) = a :=
  IntermediateField.coe_inclusion _ _

theorem coe_frobQ (r : ℕ) (b : Qr p r) :
    ((frobQ p r b : Qr p r) : PadicAlgCl p) = frobK p (Q0 p) (b : PadicAlgCl p) := rfl

theorem coe_frobQ_pow (r i : ℕ) (b : Qr p r) :
    (((frobQ p r ^ i) b : Qr p r) : PadicAlgCl p) = (frobK p (Q0 p) ^ i) (b : PadicAlgCl p) := by
  induction i generalizing b with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, AlgHom.mul_apply, ih, pow_succ, AlgEquiv.mul_apply, coe_frobQ]

theorem comp_tmul {f : ℕ} (hq : qK p K = p ^ f) (r i : ℕ) (a : K) (b : Qr p r) :
    ((comp p K hq r i (a ⊗ₜ[ℚ_[p]] b : K ⊗[ℚ_[p]] Qr p r) : Kn p K (r / Nat.gcd f r)) : PadicAlgCl p) =
      (a : PadicAlgCl p) * (frobK p (Q0 p) ^ i) (b : PadicAlgCl p) := by
  have h : comp p K hq r i (a ⊗ₜ[ℚ_[p]] b : K ⊗[ℚ_[p]] Qr p r) =
      incK p K _ a * incQ p K hq r ((frobQ p r ^ i) b) :=
    Algebra.TensorProduct.productMap_apply_tmul _ _ a b
  rw [h, MulMemClass.coe_mul, coe_incK, coe_incQ, coe_frobQ_pow]

theorem comp_sigKQ {f : ℕ} (hq : qK p K = p ^ f) (r i : ℕ) (x : KQ p K r) :
    comp p K hq r i (sigKQ p K r x) = comp p K hq r (i + 1) x := by
  have h : ∀ y : K ⊗[ℚ_[p]] Qr p r, comp p K hq r i (sigKQ p K r y) = comp p K hq r (i + 1) y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => exact (congrArg _ (map_zero _)).trans ((map_zero _).trans (map_zero _).symm)
    | tmul a b =>
      have h1 : sigKQ p K r (a ⊗ₜ[ℚ_[p]] b : K ⊗[ℚ_[p]] Qr p r) = (a ⊗ₜ[ℚ_[p]] frobQ p r b : K ⊗[ℚ_[p]] Qr p r) :=
        Algebra.TensorProduct.map_tmul _ _ a b
      rw [h1]
      apply Subtype.ext
      rw [comp_tmul, comp_tmul, coe_frobQ, pow_succ, AlgEquiv.mul_apply]
    | add y z hy hz =>
      have e1 : sigKQ p K r (y + z) = sigKQ p K r y + sigKQ p K r z := map_add _ _ _
      have e2 : comp p K hq r (i + 1) (y + z) = comp p K hq r (i + 1) y + comp p K hq r (i + 1) z := map_add _ _ _
      rw [e1, map_add, e2, hy, hz]
  exact h x

theorem comp_inclK {f : ℕ} (hq : qK p K = p ^ f) (r i : ℕ) (a : K) :
    ((comp p K hq r i (inclK p K r a) : Kn p K (r / Nat.gcd f r)) : PadicAlgCl p) = a := by
  have h : inclK p K r a = (a ⊗ₜ[ℚ_[p]] (1 : Qr p r) : K ⊗[ℚ_[p]] Qr p r) := rfl
  rw [h, comp_tmul, IntermediateField.coe_one, map_one, mul_one]

theorem comp_inclQ {f : ℕ} (hq : qK p K = p ^ f) (r i : ℕ) (b : Qr p r) :
    ((comp p K hq r i (inclQ p K r b) : Kn p K (r / Nat.gcd f r)) : PadicAlgCl p) =
      (frobK p (Q0 p) ^ i) (b : PadicAlgCl p) := by
  have h : inclQ p K r b = ((1 : K) ⊗ₜ[ℚ_[p]] b : K ⊗[ℚ_[p]] Qr p r) := rfl
  rw [h, comp_tmul, IntermediateField.coe_one, one_mul]

theorem frobenius_pow_root_of_unity {N : ℕ} (hN : ¬ p ∣ N) {ζ : PadicAlgCl p} (hζ : ζ ^ N = 1) (i : ℕ) :
    (frobK p (Q0 p) ^ i) ζ = ζ ^ p ^ i := by
  have hfd : FiniteDimensional ℚ_[p] (Q0 p) := inferInstance
  induction i with
  | zero => simp
  | succ n ih =>
    have h1 : (ζ ^ p ^ n) ^ N = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
    rw [pow_succ', AlgEquiv.mul_apply, ih, (isFrob_iff hfd _).1 (isFrob_frobK hfd) _ N hN h1, residue_cardinality_base_field,
      ← pow_mul, pow_succ]

end GlobalTheory.LKRes.ResSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainMeasureFinite
section
open NumberField MeasureTheory GlobalTheory.CuspRep

noncomputable section

namespace GlobalTheory.HCFct

theorem exists_interp {K : Type} (W : Submodule ℂ (K → ℂ)) (hW : FiniteDimensional ℂ W) :
    ∃ (s : Finset K) (b : s → W), ∀ w ∈ W, ∀ k, w k = ∑ i : s, w i.1 * (b i).1 k := by
  classical
  obtain ⟨s, hs⟩ := GlobalTheory.finiteDim_functions_detected_by_finset K W hW
  let ev : W →ₗ[ℂ] (s → ℂ) := LinearMap.pi fun i =>
    (LinearMap.proj (R := ℂ) (φ := fun _ : K => ℂ) i.1).comp W.subtype
  have hev : LinearMap.ker ev = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro w hw
    exact Subtype.ext (hs w.1 w.2 fun k hk => congrFun hw ⟨k, hk⟩)
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_leftInverse_of_injective ev hev
  refine ⟨s, fun i => ψ (fun j => if i = j then 1 else 0), fun w hw k => ?_⟩
  have e1 : (⟨w, hw⟩ : W) = ψ (ev ⟨w, hw⟩) := (LinearMap.congr_fun hψ _).symm
  rw [LinearMap.pi_apply_eq_sum_univ ψ (ev ⟨w, hw⟩)] at e1
  have e2 := congrArg (fun u : W => u.1 k) e1
  simpa only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, ev,
    LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.proj_apply, Submodule.subtype_apply] using e2

theorem constTerm_cptTranslate_mem : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))) (W : Submodule ℂ (Kinf E a → ℂ)), FiniteDimensional ℂ W → ∀ (X : Set (Module.End ℂ (Sm E a) → ℂ)) (N r : ℕ) [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 → ∀ φ ∈ Submodule.span ℂ (GlobalTheory.HCF.formsGL E a L W X N), ∀ g : GA E a, (fun k : Kinf E a => ∫ x in 𝓕, φ.1 (unip x * (g * infGL E a (Unitary.toUnits k))) ∂μ) ∈ W := by
  intro E _ _ _ a L W hW X N r _ _ μ 𝓕 hμ h𝓕 _ φ hφ g
  have hP : Continuous φ.1 ∧ (∀ γ h, φ.1 (ratGL E a γ * h) = φ.1 h) ∧
      ∀ h, (fun k : Kinf E a => φ.1 (h * infGL E a (Unitary.toUnits k))) ∈ W := by
    induction hφ using Submodule.span_induction with
    | mem x hx => exact ⟨ContAut.continuous_of_isOpen_stab E a x hx.1.level, hx.1.left, fun h => hx.2.2.1 h⟩
    | zero => exact ⟨continuous_const, fun _ _ => rfl, fun _ => W.zero_mem⟩
    | add x y _ _ hx hy =>
      exact ⟨hx.1.add hy.1, fun γ h => congrArg₂ (· + ·) (hx.2.1 γ h) (hy.2.1 γ h),
        fun h => W.add_mem (hx.2.2 h) (hy.2.2 h)⟩
    | smul c x _ hx =>
      exact ⟨hx.1.const_smul c, fun γ h => congrArg (c * ·) (hx.2.1 γ h), fun h => W.smul_mem c (hx.2.2 h)⟩
  obtain ⟨hc, hl, hK⟩ := hP
  obtain ⟨s, b, hb⟩ := exists_interp W hW
  haveI := hμ
  have hint : ∀ h, IntegrableOn (fun x => φ.1 (unip x * h)) 𝓕 μ := fun h =>
    CuspidalL2GL.integrableOn_unip hc hl μ h𝓕 h
  have hpt : ∀ k (x : BlockIx a r → Ad E), φ.1 (unip x * (g * infGL E a (Unitary.toUnits k))) =
      ∑ i : s, φ.1 (unip x * (g * infGL E a (Unitary.toUnits i.1))) * (b i).1 k := fun k x => by
    have := hb _ (hK (unip x * g)) k
    simpa only [mul_assoc] using this
  have e : (fun k : Kinf E a => ∫ x in 𝓕, φ.1 (unip x * (g * infGL E a (Unitary.toUnits k))) ∂μ) =
      ∑ i : s, (∫ x in 𝓕, φ.1 (unip x * (g * infGL E a (Unitary.toUnits i.1))) ∂μ) • (b i).1 := by
    funext k
    simp only [hpt k]
    rw [integral_finsetSum _ fun i _ => (hint _).mul_const _]
    simp only [integral_mul_const, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [e]
  exact W.sum_mem fun i _ => W.smul_mem _ (b i).2

end GlobalTheory.HCFct

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermFormPulledBackCombinationsExpandMonomials
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.FormsLocus

theorem eval₂_expand {Rg S : Type} [CommRing Rg] [CommRing S] (mA mB : ℕ)
    (ψ : MvPolynomial (Fin (mA * mB)) Rg →+* S) (β : Fin mA → S) (F : MvPolynomial (Fin mB) Rg) :
    MvPolynomial.eval₂Hom (ψ.comp MvPolynomial.C)
        (fun j => ∑ i, ψ (MvPolynomial.X (finProdFinEquiv (i, j))) * β i) F =
      MvPolynomial.eval₂Hom ψ β (expand mA mB F) := by
  rw [expand, ← MvPolynomial.coe_eval₂Hom (MvPolynomial.C.comp MvPolynomial.C), ← RingHom.comp_apply,
    MvPolynomial.comp_eval₂Hom]
  congr 1
  ext r <;> simp

theorem expand_isHomogeneous {Rg : Type} [CommRing Rg] (mA mB : ℕ) {F : MvPolynomial (Fin mB) Rg} {d : ℕ}
    (hF : F.IsHomogeneous d) : (expand mA mB F).IsHomogeneous d := by
  have h := hF.eval₂ (τ := Fin mA)
    (MvPolynomial.C.comp MvPolynomial.C : Rg →+* MvPolynomial (Fin mA) (MvPolynomial (Fin (mA * mB)) Rg))
    (fun j => ∑ i : Fin mA, MvPolynomial.C (MvPolynomial.X (finProdFinEquiv (i, j))) * MvPolynomial.X i)
    (fun r => MvPolynomial.isHomogeneous_C _ _)
    (fun j => MvPolynomial.IsHomogeneous.sum _ _ _ fun i _ => MvPolynomial.isHomogeneous_C_mul_X _ _)
  simpa [expand] using h

theorem germ_eval_comb : ∀ (Rg : Type) [CommRing Rg] (A₀ T X : Scheme.{0}) (f : A₀ ⟶ Sp Rg) (N : LB A₀) (mA mB : ℕ) (a : Fin mA → LB.Sec N) (g : T ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)) (φ : X ⟶ A₀) (p : X ⟶ T), φ ≫ f = p ≫ g ≫ affπ Rg (mA * mB) → ∀ (d : ℕ) (F : MvPolynomial (Fin mB) Rg), F.IsHomogeneous d → ∀ (z : X) (q : N.ι), φ z ∈ N.U q → MvPolynomial.eval₂Hom (gc (p ≫ g ≫ affπ Rg (mA * mB)) z) (comb a φ p (matOf g) z q) F = ∑ ν ∈ (GlobalTheory.FormsLocus.expand mA mB F).support, gs p z ⊤ (GlobalTheory.FormsLocus.ringOf g ((GlobalTheory.FormsLocus.expand mA mB F).coeff ν)) * gs φ z (N.U q) ((GlobalTheory.FormsLocus.monSec a d ν).f q) := by
  intro Rg _ A₀ T X f N mA mB a g φ p _ d F hF z q hq
  have hT : p z ∈ (⊤ : T.Opens) := trivial
  let ψ : MvPolynomial (Fin (mA * mB)) Rg →+* X.presheaf.stalk z :=
    (MapIff.gsH p z ⊤ hT).comp (ringOf g)
  have hC : ψ.comp MvPolynomial.C = gc (p ≫ g ≫ affπ Rg (mA * mB)) z := by
    ext r
    have n2 : (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin (mA * mB)) Rg))).inv (MvPolynomial.C r) =
        (affπ Rg (mA * mB)).appTop ((Scheme.ΓSpecIso (CommRingCat.of Rg)).inv r) := by
      rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]; rfl
    simp only [ψ, RingHom.comp_apply, ringOf, gc, MapIff.gsH, RingHom.coe_comp, Function.comp_apply]
    rw [n2, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop]
    rfl
  have hcomb : comb a φ p (matOf g) z q =
      fun j => ∑ i, ψ (MvPolynomial.X (finProdFinEquiv (i, j))) * gs φ z (N.U q) ((a i).f q) := by
    funext j
    simp only [comb, ψ, RingHom.comp_apply, ringOf_X, matOf]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [MapIff.gsH_apply]
  rw [← hC, hcomb, eval₂_expand, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq']
  refine Finset.sum_congr rfl fun ν hν => ?_
  have hd : ∑ i, ν i = d := by
    have := expand_isHomogeneous mA mB hF (MvPolynomial.mem_support_iff.1 hν)
    rw [← this, Finsupp.weight_apply]
    simp [Finsupp.sum_fintype]
  have hp : gs φ z (N.U q) (∏ i, (a i).f q ^ ν i) = ∏ i, gs φ z (N.U q) ((a i).f q) ^ ν i := by
    rw [← MapIff.gsH_apply φ z _ hq, map_prod]
    simp only [map_pow, MapIff.gsH_apply]
  simp only [ψ, RingHom.comp_apply, monSec, if_pos hd]
  rw [MapIff.gsH_apply]
  exact congrArg (fun x => gs p z ⊤ (ringOf g (MvPolynomial.coeff ν (expand mA mB F))) * x) hp.symm

end GlobalTheory.FormsLocus
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridFirstColumnSpaceRankSignatureSelfDualStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links GlobalTheory.ChiGrid
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gridFirstColumnSpace_rank_signature_selfDual : ∀ (D : D7) (T : Type) (L : LevCh D T) (μ0 : T), L.Is μ0 → ∀ j, j ≤ D.R.m → (columnBlock L j).IsV (rankV D 0 j) ((D.R.m - j) / 2) := by
  first | exact @GlobalTheory.ChiGrid.colY_isV | exact GlobalTheory.ChiGrid.colY_isV | (intros; apply GlobalTheory.ChiGrid.colY_isV <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridTopVertexFramePointTransportLatticeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gridTopVertex_frame_point_transport_lattice : ∀ (D : D7) (T : Type) (L : LevCh D T) (sc : Consts) (G : GridData L sc) (S : Finset ℕ)
    (fr₀ : GL (Fin (G.V (.grid D.R.m D.R.m)).rank) D.host.E) (u₀ : FinPt G (.grid D.R.m D.R.m)),
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr₀.1 * (G.V (.grid D.R.m D.R.m)).gram * fr₀.1 = 1 →
    (∃ (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P ∧ SuppAt e _ u₀.1 ∧ ∀ w ∈ P, Off S w) →
    (∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr₀) ↔
        (Formalism.IndefR.Lev.finE (G.V (.grid D.R.m D.R.m)) u₀.1).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.grid D.R.m D.R.m))) →
    ∃ (fr : GL (Fin (G.V (.top D.R.m)).rank) D.host.E) (u : FinPt G (.top D.R.m)),
      Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 * (G.V (.top D.R.m)).gram * fr.1 = 1 ∧
      (∃ (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P ∧ SuppAt e _ u.1 ∧ ∀ w ∈ P, Off S w) ∧
      (∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) ↔
        (Formalism.IndefR.Lev.finE (G.V (.top D.R.m)) u.1).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.top D.R.m))) ∧
      (∀ i (k : Fin (G.V (.grid D.R.m D.R.m)).rank), fr.1 i (Formalism.L2.Col.Br.iC G.sp.topDec.rank.symm k) =
        (frameMat _ _ G.sp.topDec.ι * fr₀.1) i k) ∧
      (∀ i, fr.1 i (Formalism.L2.Col.Br.iL G.sp.topDec.rank.symm) = G.sp.topDec.a i 0) ∧
      HMul.hMul (mt (G.V (.top D.R.m)) u.1) (topEmb G) = HMul.hMul (topEmb G) (mt (G.V (.grid D.R.m D.R.m)) u₀.1) ∧
      mt (G.V (.top D.R.m)) u.1 *ᵥ topVec G = topVec G := by
  first | exact @GlobalTheory.FunObj.top_transport | exact GlobalTheory.FunObj.top_transport | (intros; apply GlobalTheory.FunObj.top_transport <;> assumption)
end

