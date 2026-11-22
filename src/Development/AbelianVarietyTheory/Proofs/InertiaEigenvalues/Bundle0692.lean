import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0685
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0064
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0319
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0454
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0679
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0360
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0359
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0363
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0361
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0358
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0355
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0681
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0956
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixedVectorCoefficientLeftInvariantLevelGroup
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Classical

noncomputable section

namespace GlobalTheory.RawLift.CoefLeft

theorem ip_eq_of_sq {X : Type} [MeasurableSpace X] (ν : Measure X) (a b c d : X → ℂ)
    (ha : MemLp a 2 ν) (hb : MemLp b 2 ν) (hc : MemLp c 2 ν) (hd : MemLp d 2 ν)
    (h : ∀ z : ℂ, ∫⁻ x, ‖c x + z * d x‖ₑ ^ 2 ∂ν = ∫⁻ x, ‖a x + z * b x‖ₑ ^ 2 ∂ν) :
    ∫ x, star (c x) * d x ∂ν = ∫ x, star (a x) * b x ∂ν := by
  have pt : ∀ p q : ℂ, star p * q = (1/4 : ℂ) * ((((‖p + 1 * q‖ ^ 2 : ℝ)) : ℂ) - ((‖p + (-1) * q‖ ^ 2 : ℝ) : ℂ)
      + Complex.I * ((‖p + (-Complex.I) * q‖ ^ 2 : ℝ) : ℂ) - Complex.I * ((‖p + Complex.I * q‖ ^ 2 : ℝ) : ℂ)) := by
    intro p q
    have e : ∀ w : ℂ, ((‖w‖ ^ 2 : ℝ) : ℂ) = w * (starRingEnd ℂ) w := by
      intro w; rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp only [e, map_add, map_mul, map_neg, map_one, Complex.conj_I]
    show (starRingEnd ℂ) p * q = _
    ring_nf
    try (simp only [Complex.I_sq]; ring)
  have mem : ∀ (f g : X → ℂ), MemLp f 2 ν → MemLp g 2 ν → ∀ z : ℂ,
      Integrable (fun x => (((‖f x + z * g x‖ ^ 2 : ℝ)) : ℂ)) ν := by
    intro f g hf hg z
    have h2 : MemLp (fun x => f x + z * g x) 2 ν := hf.add (hg.const_mul z)
    have : Integrable (fun x => ‖f x + z * g x‖ ^ 2) ν := by
      have := h2.integrable_norm_pow (p := 2) (by norm_num)
      simpa using this
    exact this.ofReal
  have Q : ∀ (f g : X → ℂ), MemLp f 2 ν → MemLp g 2 ν → ∀ z : ℂ,
      ∫ x, (((‖f x + z * g x‖ ^ 2 : ℝ)) : ℂ) ∂ν = (((∫⁻ x, ‖f x + z * g x‖ₑ ^ 2 ∂ν).toReal : ℝ) : ℂ) := by
    intro f g hf hg z
    rw [integral_complex_ofReal]
    congr 1
    have hm : AEStronglyMeasurable (fun x => f x + z * g x) ν :=
      (hf.add (hg.const_mul z)).aestronglyMeasurable
    rw [integral_eq_lintegral_of_nonneg_ae (f := fun x => ‖f x + z * g x‖ ^ 2)
      (Filter.Eventually.of_forall fun x => by simp only [Pi.zero_apply]; positivity) (hm.norm.pow 2)]
    congr 1
    refine lintegral_congr fun x => ?_
    rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]
  have expand : ∀ (f g : X → ℂ), MemLp f 2 ν → MemLp g 2 ν →
      ∫ x, star (f x) * g x ∂ν = (1/4 : ℂ) * ((((∫⁻ x, ‖f x + 1 * g x‖ₑ ^ 2 ∂ν).toReal : ℝ) : ℂ)
        - (((∫⁻ x, ‖f x + (-1) * g x‖ₑ ^ 2 ∂ν).toReal : ℝ) : ℂ)
        + Complex.I * (((∫⁻ x, ‖f x + (-Complex.I) * g x‖ₑ ^ 2 ∂ν).toReal : ℝ) : ℂ)
        - Complex.I * (((∫⁻ x, ‖f x + Complex.I * g x‖ₑ ^ 2 ∂ν).toReal : ℝ) : ℂ)) := by
    intro f g hf hg
    simp_rw [pt (f _) (g _)]
    rw [integral_const_mul, integral_sub, integral_add, integral_sub, integral_const_mul, integral_const_mul,
      Q f g hf hg, Q f g hf hg, Q f g hf hg, Q f g hf hg]
    · exact mem f g hf hg 1
    · exact mem f g hf hg (-1)
    · exact (mem f g hf hg 1).sub (mem f g hf hg (-1))
    · exact (mem f g hf hg (-Complex.I)).const_mul _
    · exact ((mem f g hf hg 1).sub (mem f g hf hg (-1))).add ((mem f g hf hg (-Complex.I)).const_mul _)
    · exact (mem f g hf hg Complex.I).const_mul _
  rw [expand c d hc hd, expand a b ha hb, h 1, h (-1), h (-Complex.I), h Complex.I]

end GlobalTheory.RawLift.CoefLeft

namespace GlobalTheory.RawLift.CoefLeft

variable {D : D7}

theorem isThetaFunO_add_smul {S T' : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {f g : WO S T' → ℂ}
    (hf : IsThetaFunO ψ S T' f) (hg : IsThetaFunO ψ S T' g) (z : ℂ) : IsThetaFunO ψ S T' (f + z • g) where
  quasi γ w := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hf.quasi, hg.quasi]; ring
  level := by
    obtain ⟨U₁, hU₁, h₁⟩ := hf.level
    obtain ⟨U₂, hU₂, h₂⟩ := hg.level
    refine ⟨U₁ ⊓ U₂, by rw [AddSubgroup.coe_inf]; exact hU₁.inter hU₂, fun u hu hu0 => ?_⟩
    have e1 := h₁ u hu.1 hu0
    have e2 := h₂ u hu.2 hu0
    funext w
    have e1' := congrFun e1 w
    have e2' := congrFun e2 w
    simp only [heisO, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e1' e2' ⊢
    rw [← e1', ← e2']; ring_nf
  cont := hf.cont.add (hg.cont.const_smul z)
  smooth k L hL hL0 w := by
    have := (hf.smooth k L hL hL0 w).add ((hg.smooth k L hL hL0 w).const_smul z)
    simpa only [Pi.add_apply, Pi.smul_apply] using this

theorem memLp_two_of_lintegral {X : Type} [MeasurableSpace X] {ν : Measure X} {f : X → ℂ}
    (hm : AEStronglyMeasurable f ν) (h : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂ν < ⊤) : MemLp f 2 ν := by
  rw [memLp_two_iff_integrable_sq_norm hm]
  refine ⟨hm.norm.pow 2, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  simpa [enorm_pow] using h

end GlobalTheory.RawLift.CoefLeft

namespace GlobalTheory.RawLift.CoefLeft

theorem aesm_of_theta {D : D7} {S T' : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {f : WO S T' → ℂ} (ν : Measure (WO S T'))
    (hf : IsThetaFunO ψ S T' f) : AEStronglyMeasurable f ν := by
  haveI : OpensMeasurableSpace (WO S T') := ⟨le_rfl⟩
  exact hf.cont.aestronglyMeasurable

theorem thetaInner_weilRep {D : D7} {S T' : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T' →* Module.End ℂ (WO S T' → ℂ)} (hW : IsWeilDatumO ψ S T' χS χT om)
    {μ : Measure (WO S T')} {𝓕 : Set (WO S T')} (hμ : IsCovolOne (ratL T' S) μ 𝓕) (p : GA D S × GA D T')
    {u v : WO S T' → ℂ} (hu : IsThetaFunO ψ S T' u) (hv : IsThetaFunO ψ S T' v)
    (hu2 : ∫⁻ w in 𝓕, ‖u w‖ₑ ^ 2 ∂μ < ⊤) (hv2 : ∫⁻ w in 𝓕, ‖v w‖ₑ ^ 2 ∂μ < ⊤) :
    thetaIP μ 𝓕 (om p u) (om p v) = thetaIP μ 𝓕 u v := by
  have un := fun f (hf : IsThetaFunO ψ S T' f) => hW.om_unit μ 𝓕 hμ.1 hμ.2.1 p f hf
  unfold thetaIP
  refine ip_eq_of_sq (μ.restrict 𝓕) u v (om p u) (om p v)
    (memLp_two_of_lintegral (aesm_of_theta _ hu) hu2) (memLp_two_of_lintegral (aesm_of_theta _ hv) hv2)
    (memLp_two_of_lintegral (aesm_of_theta _ (hW.om_pres p u hu)) (by rw [un u hu]; exact hu2))
    (memLp_two_of_lintegral (aesm_of_theta _ (hW.om_pres p v hv)) (by rw [un v hv]; exact hv2)) (fun z => ?_)
  have := un (u + z • v) (isThetaFunO_add_smul hu hv z)
  simpa only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using this

theorem thetaIP₂ {D : D7} {S T' : HSp D} {μ : Measure (WO S T')} {𝓕 : Set (WO S T')}
    {v : WO S T' → ℂ} (h : thetaIP μ 𝓕 v v ≠ 0) : ∫⁻ w in 𝓕, ‖v w‖ₑ ^ 2 ∂μ < ⊤ := by
  have hi : Integrable (fun w => star (v w) * v w) (μ.restrict 𝓕) := by
    by_contra hn
    exact h (integral_undef hn)
  have := hi.hasFiniteIntegral
  rw [hasFiniteIntegral_iff_enorm] at this
  simpa [enorm_mul, sq] using this

end GlobalTheory.RawLift.CoefLeft

namespace GlobalTheory.RawLift.CoefLeft

set_option maxHeartbeats 1000000 in

theorem coef_lev_mul : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ i t, LevFix R i t → ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∀ k ∈ levW R i, ∀ g, coef R i t μ 𝓕 (k * g) = coef R i t μ 𝓕 g := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL i t hfix μ 𝓕 hμ k hk g
  have hW := hL.thP.ωP i t
  have hv1 : R.ωP i t (1, k) (R.vP i t) = R.vP i t := by
    have := hfix k hk 1
    rwa [Model.pureTensor_one] at this
  have hvθ : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) := by
    have := hL.thP.pt_theta i t 1
    rwa [Model.pureTensor_one] at this
  unfold coef
  by_cases h0 : thetaIP μ 𝓕 (R.vP i t) (R.vP i t) = 0
  · rw [h0, div_zero, div_zero]
  congr 1
  have e : R.ωP i t (1, k * g) = R.ωP i t (1, k) * R.ωP i t (1, g) := by rw [← map_mul]; simp
  rw [e, Module.End.mul_apply]
  have hv2 := thetaIP₂ h0
  have huθ := hW.om_pres (1, g) _ hvθ
  have hu2 : ∫⁻ w in 𝓕, ‖R.ωP i t (1, g) (R.vP i t) w‖ₑ ^ 2 ∂μ < ⊤ := by
    rw [hW.om_unit μ 𝓕 hμ.1 hμ.2.1 (1, g) _ hvθ]; exact hv2
  have key := thetaInner_weilRep hW hμ (1, k) huθ hvθ hu2 hv2
  rwa [hv1] at key

end GlobalTheory.RawLift.CoefLeft

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockMinorProductEqSignDualWeylExtremalVector
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ExportSeries.DeltaExtremal

noncomputable def lead {n : ℕ} (y : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) : ℂ :=
  if h : k ≤ n then (y.submatrix (Fin.castLE h) (Fin.castLE h)).det else 1

theorem lead_zero {n : ℕ} (y : Matrix (Fin n) (Fin n) ℂ) : lead y 0 = 1 := by
  simp [lead]

theorem lead_self {n : ℕ} (y : Matrix (Fin n) (Fin n) ℂ) : lead y n = y.det := by
  simp [lead]

theorem det_inv_rev {n k : ℕ} (hk : k ≤ n) (y : GL (Fin n) ℂ) :
    (Matrix.of fun a b : Fin k => (y⁻¹).val (Fin.rev (Fin.castLE hk a)) (Fin.rev (Fin.castLE hk b))).det =
      lead y.val (n - k) * (y.val.det)⁻¹ := by
  obtain ⟨e, hl, hr⟩ := GlobalTheory.ValCmp.exists_equiv_castLE_rev hk
  have hj := GlobalTheory.ValCmp.jacobi_blocks_of_mul (y.val.submatrix e e) ((y⁻¹).val.submatrix e e) 1 (by
    rw [Matrix.submatrix_mul_equiv, Units.mul_inv, one_smul, Matrix.submatrix_one_equiv])
  have e1 : (y.val.submatrix e e).toBlocks₁₁ =
      y.val.submatrix (Fin.castLE (Nat.sub_le n k)) (Fin.castLE (Nat.sub_le n k)) := by
    ext a b
    simp [Matrix.toBlocks₁₁, hl]
  have e2 : ((y⁻¹).val.submatrix e e).toBlocks₂₂ =
      Matrix.of fun a b : Fin k => (y⁻¹).val (Fin.rev (Fin.castLE hk a)) (Fin.rev (Fin.castLE hk b)) := by
    ext a b
    simp only [Matrix.toBlocks₂₂, hr, Matrix.of_apply, Matrix.submatrix_apply]
  rw [e1, e2, one_pow, one_mul, Matrix.det_submatrix_equiv_self] at hj
  rw [← hj, lead, dif_pos (Nat.sub_le n k), Matrix.coe_units_inv, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']

variable {D : D7} {m n : ℕ}

theorem aeval_minorPlus (p : D.what₂.Tau → ℕ) (y : GLR D n) (τ : D.what₂.Tau) {k : ℕ} (hk : k ≤ p τ) (hm : k ≤ m) (hn : k ≤ n) :
    MvPolynomial.aeval (fockPt p y) (minorPlus τ k : PolF D m n) = lead (y τ).val k := by
  rw [minorPlus, AlgHom.map_det, lead, dif_pos hn]
  congr 1
  ext a b
  have ha := a.isLt
  have hb := b.isLt
  have h1 : b.val < m ∧ a.val < n := ⟨by omega, by omega⟩
  have h2 : b.val < p τ := by omega
  have h3 : b.val < n := by omega
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, varF, dif_pos h1, MvPolynomial.aeval_X, fockPt,
    if_pos h2, dif_pos h3, Matrix.submatrix_apply]
  rfl

theorem aeval_minorMinus (p : D.what₂.Tau → ℕ) (y : GLR D n) (τ : D.what₂.Tau) {k : ℕ} (hm : p τ + k ≤ m) (hn : k ≤ n) :
    MvPolynomial.aeval (fockPt p y) (minorMinus τ (p τ) k : PolF D m n) =
      ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin k)) : ℤ) : ℂ) * (lead (y τ).val (n - k) * ((y τ).val.det)⁻¹) := by
  rw [minorMinus, AlgHom.map_det, ← det_inv_rev hn, ← Matrix.det_permute', ← Matrix.det_transpose]
  congr 1
  ext b a
  have ha := a.isLt
  have hb := b.isLt
  have h1 : p τ + b.val < m ∧ n - k + a.val < n := ⟨by omega, by omega⟩
  have h2 : ¬ p τ + b.val < p τ := by omega
  have h3 : p τ + b.val - p τ < n := by omega
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, varF, dif_pos h1, MvPolynomial.aeval_X, fockPt,
    if_neg h2, dif_pos h3, Matrix.submatrix_apply, Matrix.transpose_apply, id]
  refine congrArg₂ _ (congrArg Fin.rev (Fin.ext ?_)) (Fin.ext ?_)
  · simp
  · simp only [Fin.revPerm_apply, Fin.val_rev, Fin.val_castLE]
    omega

theorem sum_drops (q : ℕ) (a : ℕ → ℕ) (h : ∀ i, i + 1 < q → a (i + 1) ≤ a i) :
    ∑ i ∈ Finset.range q, (a i - if i + 1 < q then a (i + 1) else 0) = if 0 < q then a 0 else 0 := by
  have := Finset.sum_range_sub' (fun i => if i < q then (a i : ℤ) else 0) q
  simp only [lt_irrefl, if_false, sub_zero] at this
  refine Nat.cast_injective (R := ℤ) ?_
  rw [Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, ← this]
  refine Finset.sum_congr rfl fun i hi => ?_
  have := Finset.mem_range.1 hi
  have := h i
  split_ifs <;> omega

theorem prod_exponents {n p q : ℕ} (ap am : ℕ → ℕ) (c : ℤ) (lam : DomWeight n) (hle : p + q ≤ n)
    (hl : ∀ i : Fin n, lam.w i = (if i.val < p then (ap i : ℤ) else if n - q ≤ i.val then -(am (n - 1 - i) : ℤ) else 0) + c)
    (L : ℕ → ℂ) (h0 : L 0 = 1) (hd : L n ≠ 0) :
    L n ^ c * ((∏ i ∈ Finset.range p, L (i + 1) ^ (ap i - if i + 1 < p then ap (i + 1) else 0)) *
      ∏ i ∈ Finset.range q, (L (n - (i + 1)) * (L n)⁻¹) ^ (am i - if i + 1 < q then am (i + 1) else 0)) =
    L n ^ lam.detShift * ∏ s : Fin n, L (s + 1) ^ (lam.natW s - Formalism.GradedWeylDivisibility.nuNext lam.natW s) := by
  rcases n with _ | k
  · obtain rfl : p = 0 := by omega
    obtain rfl : q = 0 := by omega
    simp [h0]
  have hanti : ∀ i j (hi : i < k + 1) (hj : j < k + 1), i ≤ j → lam.w ⟨j, hj⟩ ≤ lam.w ⟨i, hi⟩ :=
    fun i j hi hj h => lam.anti (show (⟨i, hi⟩ : Fin (k + 1)) ≤ ⟨j, hj⟩ from h)
  have ham : ∀ i, i + 1 < q → am (i + 1) ≤ am i := by
    intro i hi
    have := hanti (k - (i + 1)) (k - i) (by omega) (by omega) (by omega)
    rw [hl, hl] at this
    dsimp only at this
    rw [show k + 1 - 1 - (k - i) = i by omega, show k + 1 - 1 - (k - (i + 1)) = i + 1 by omega] at this
    split_ifs at this <;> omega
  have hshift : lam.detShift = lam.w ⟨k, Nat.lt_succ_self k⟩ := by
    simp [DomWeight.detShift]
  set A : ℕ → ℕ := fun i => if i < p then ap i - if i + 1 < p then ap (i + 1) else 0 else 0 with hA
  set B : ℕ → ℕ := fun i => if i < q then am i - if i + 1 < q then am (i + 1) else 0 else 0 with hB
  have eA : (∏ i ∈ Finset.range p, L (i + 1) ^ (ap i - if i + 1 < p then ap (i + 1) else 0)) =
      (∏ i ∈ Finset.range k, L (i + 1) ^ A i) * L (k + 1) ^ A k := by
    rw [← Finset.prod_range_succ (fun i => L (i + 1) ^ A i),
      ← Finset.prod_subset (Finset.range_subset_range.2 (show p ≤ k + 1 by omega))
        (fun i _ hi => by rw [hA]; dsimp only; rw [if_neg (fun h => hi (Finset.mem_range.2 h)), pow_zero])]
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [hA]; dsimp only; rw [if_pos (Finset.mem_range.1 hi)]
  have eB : (∏ i ∈ Finset.range q, L (k + 1 - (i + 1)) ^ (am i - if i + 1 < q then am (i + 1) else 0)) =
      ∏ i ∈ Finset.range k, L (i + 1) ^ B (k - 1 - i) := by
    have : ∏ i ∈ Finset.range (k + 1), L (k + 1 - (i + 1)) ^ B i = ∏ i ∈ Finset.range k, L (i + 1) ^ B (k - 1 - i) := by
      rw [Finset.prod_range_succ, Nat.sub_self, h0, one_pow, mul_one, ← Finset.prod_range_reflect]
      refine Finset.prod_congr rfl fun i hi => ?_
      have := Finset.mem_range.1 hi
      rw [show k + 1 - (k - 1 - i + 1) = i + 1 by omega]
    rw [← this, ← Finset.prod_subset (Finset.range_subset_range.2 (show q ≤ k + 1 by omega))
        (fun i _ hi => by rw [hB]; dsimp only; rw [if_neg (fun h => hi (Finset.mem_range.2 h)), pow_zero])]
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [hB]; dsimp only; rw [if_pos (Finset.mem_range.1 hi)]
  have eR : ∏ s : Fin (k + 1), L (s + 1) ^ (lam.natW s - Formalism.GradedWeylDivisibility.nuNext lam.natW s) =
      ∏ i ∈ Finset.range k, L (i + 1) ^ (A i + B (k - 1 - i)) := by
    rw [Fin.prod_univ_castSucc, show lam.natW (Fin.last k) = 0 by
      rw [DomWeight.natW, hshift]; simp [Fin.last], Nat.zero_sub, pow_zero, mul_one,
      ← Fin.prod_univ_eq_prod_range (fun i => L (i + 1) ^ (A i + B (k - 1 - i)))]
    refine Finset.prod_congr rfl fun s _ => ?_
    obtain ⟨s, hs⟩ := s
    have hs' : s + 1 < k + 1 := by omega
    simp only [Fin.castSucc_mk, Formalism.GradedWeylDivisibility.nuNext, dif_pos hs', DomWeight.natW, hshift]
    congr 1
    have a1 := hanti s (s + 1) (by omega) hs' (by omega)
    have a2 := hanti (s + 1) k hs' (by omega) (by omega)
    have b1 := hl ⟨s, by omega⟩
    have b2 := hl ⟨s + 1, hs'⟩
    dsimp only at b1 b2
    rw [show k + 1 - 1 - s = k - 1 - s + 1 by omega] at b1
    rw [show k + 1 - 1 - (s + 1) = k - 1 - s by omega] at b2
    rw [hA, hB]
    dsimp only
    split_ifs at b1 b2 ⊢ <;> omega
  have eS : lam.detShift = c + (A k : ℤ) - ((if 0 < q then am 0 else 0 : ℕ) : ℤ) := by
    rw [hshift, hl, hA]
    dsimp only
    rw [show k + 1 - 1 - k = 0 by omega]
    split_ifs <;> omega
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [eA, eB, eR, eS, sum_drops q am ham, zpow_sub₀ hd, zpow_add₀ hd, zpow_natCast, zpow_natCast]
  simp only [pow_add, Finset.prod_mul_distrib, inv_pow]
  ring

theorem eval_extremal (lam : D.what₂.Tau → DomWeight n) (y : GLR D n) (τ : D.what₂.Tau) :
    MvPolynomial.eval₂Hom (RingHom.id ℂ) (fun v : D.what₂.Tau × Fin n × Fin n => (y v.1).val v.2.1 v.2.2)
      (Formalism.GradedWeylDivisibility.blockEmb ℂ τ (extremal ℂ n (lam τ))) =
    ∏ s : Fin n, lead (y τ).val (s + 1) ^ ((lam τ).natW s - Formalism.GradedWeylDivisibility.nuNext (lam τ).natW s) := by
  rw [extremal, Formalism.GradedWeylDivisibility.hw, map_prod, map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_pow, map_pow, Formalism.GradedWeylDivisibility.lpMinor, AlgHom.map_det, RingHom.map_det, lead, dif_pos (Nat.succ_le_of_lt s.isLt)]
  congr 2
  ext a b
  simp [Formalism.GradedWeylDivisibility.blockEmb]

theorem harmFn_delta : ∀ (D : D7) (m n : ℕ) (w : Weight D n) (B : GLR D n), w.Good → (∀ τ, w.p τ + w.q τ ≤ m) → ∃ s : ℤˣ, ∀ x, harmFn m w B (w.delta m) x = ((s : ℤ) : ℂ) * coefFn (RingHom.id ℂ) w.lam (ten fun τ => extremal ℂ n (w.lam τ)) (B⁻¹ * x) := by
  intro D m n w B hw hm
  refine ⟨∏ τ, ∏ i ∈ Finset.range (w.q τ), Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (i + 1))) ^
    (w.am τ i - if i + 1 < w.q τ then w.am τ (i + 1) else 0), fun x => ?_⟩
  rw [harmFn_apply, coefFn, ten]
  generalize B⁻¹ * x = y
  rw [Weight.delta, Datum.delta, map_prod, map_prod]
  simp only [detFam, MonoidHom.coe_mk, OneHom.coe_mk, Units.coe_prod, Units.val_zpow_eq_zpow_val,
    GeneralLinearGroup.val_det_apply, Int.cast_prod, Units.val_pow_eq_pow_val, Int.cast_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have h1 := hw.le τ
  have h2 := hm τ
  have hd : lead (y τ).val n ≠ 0 := by
    rw [lead_self]; exact (GeneralLinearGroup.det (y τ)).ne_zero
  rw [eval_extremal, ← lead_self, ← prod_exponents (w.ap τ) (w.am τ) (w.c τ) (w.lam τ) h1 (hw.lam_eq τ) _ (lead_zero _) hd,
    deltaAt, map_mul, map_prod, map_prod,
    Finset.prod_congr rfl fun i hi => by
      have := Finset.mem_range.1 hi
      rw [map_pow, aeval_minorPlus w.p y τ (by omega) (by omega) (by omega)],
    Finset.prod_congr (s₁ := Finset.range (w.q τ)) rfl fun i hi => by
      have := Finset.mem_range.1 hi
      rw [map_pow, aeval_minorMinus w.p y τ (by omega) (by omega), mul_pow, ← lead_self],
    Finset.prod_mul_distrib]
  ring

end GlobalTheory.ExportSeries.DeltaExtremal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FundamentalLemmaLatticeFrobFixedForallDegree
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PMon.ResR TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem flAt_all : ∀ r : ℕ, FLAt r := by
  intro r l _ P AI T n _ _ U x y hxy hU hc
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact x.1.elim0
  obtain ⟨E, ω, -, -, -, hω, hlin, hspan, hdet⟩ := GlobalTheory.T.unramifiedExt_fixedField_frobeniusPow_degree l r hr
  have hdet' : (frobMat ω).det ≠ 0 := hdet
  have hxy' : ((0 : Fin 1), ((x.2, x.1) : n × Fin r)) ≠ (0, (y.2, y.1)) := by
    intro h
    apply hxy
    simp only [Prod.mk.injEq, true_and] at h
    exact Prod.ext h.2 h.1
  obtain ⟨A₀, hA₀, hW⟩ := GlobalTheory.T.fundamentalLemmaLattice_degreeOne l P AI T (n × Fin r) (fun _ => U0 P ω hdet' U) _ _ hxy'
    (fun _ => GlobalTheory.T.isBdRPlusUnitMatrix_restrictionLatticeMatrix l P r ω hdet' n U hU) (GlobalTheory.T.linearIndependent_restrictionLattice_column l P r ω hω hdet' n U x hc)
  obtain ⟨W₀, hW₀, heq⟩ := hW 0
  have he : ∀ j : n × Fin r, eps ((0 : Fin 1), ((x.2, x.1) : n × Fin r)) (0, (y.2, y.1)) (0, j) = eps x y (j.2, j.1) := by
    intro j
    simp only [eps, Prod.mk.injEq, true_and, Prod.ext_iff]
    grind
  have heq' : (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B).map (ev P 0) = (U0 P ω hdet' U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) *
      Matrix.diagonal (fun j : n × Fin r => tz P (eps x y (j.2, j.1))) * (W₀ : Matrix (n × Fin r) (n × Fin r) P.R.BdR) := by
    simpa [he] using heq
  have hA₀' : ∀ i j, P.φB ((A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) i j) = (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) i j :=
    fun i j => by simpa using hA₀ i j
  have h3 := GlobalTheory.T.restrictionLattice_columns_condition_linearIndependent l P r ω hω hdet' n U x y A₀ hA₀' W₀ hW₀ heq'
  obtain ⟨a, -, -, hsp⟩ := GlobalTheory.T.exists_frobeniusFixed_unramified_tower_basis l r ω hω hlin hspan (n → P.R.B) n (colv P ω A₀) h3.2
    (fun e he c => GlobalTheory.T.mem_span_restrictionLattice_columns l P r hr ω hω hdet' n U x y A₀ hA₀' W₀ hW₀ heq' _ (GlobalTheory.T.frobFixedLatticeCondition_smul_of_frobenius_fixed l P r n U x y _ e he (h3.1 c)))
  exact GlobalTheory.T.exists_frobeniusFixed_matrix_units_of_lattice_basis l P r ω hω hdet' n U x y hU A₀ hA₀' W₀ hW₀ heq' a hsp

end GlobalTheory.PMon

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegrableOnDownwardThetaLiftIntegrand
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite

noncomputable section

open scoped ComplexOrder

namespace GlobalTheory.DownLift.GenFinite

theorem thetaKO_smul {D : D7} {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (h : GA D S)
    (g : GA D T) (c : ℂ) (f : WO S T → ℂ) : thetaKO om h g (c • f) = c * thetaKO om h g f := by
  simp only [thetaKO, map_smul, Pi.smul_apply, smul_eq_mul]

theorem integrableOn_downIntegrand : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type)
    (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP →
    ∀ (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (f : WO (Vc D i) (Wc D i) → ℂ) (l : (R.cV i).W →ₗ[ℂ] ℂ)
      (g : GA D (Wc D i)), IsThetaFunO R.ψ (Vc D i) (Wc D i) f →
      IntegrableOn (fun h => thetaKO (R.ωP i t) h g f * l (R.extV i t y h)) (R.fdV i t) (R.νV i t) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG hP i t y f l g hf
  have hm := hG.core.models
  have hom := (hP i t).datum
  have hx := (hm.HV i t).2.1.le (LinearMap.mem_range_self _ y)
  have hpos : ∀ τ, (gramAt D (Vc D i) τ).PosDef := fun τ => by
    have := D.sp.V_sig ((i : ℕ) + 1) (tauE D τ)
    rw [hm.vpos i] at this
    exact GlobalTheory.DefiniteQuotient.posDef_of_signature this
  have hcont : Continuous fun h => l (R.extV i t y h) :=
    (LinearMap.continuous_of_finiteDimensional l).comp
      (GlobalTheory.ThetaIntegrand.ext_continuous (R.cV i) (hm.cV i) (R.βV i) (R.datVt i t) hx)
  have hinv : ∀ γ ∈ GQ (Vc D i), ∀ h, l (R.extV i t y (γ * h)) = l (R.extV i t y h) := fun γ hγ h =>
    congrArg l (GlobalTheory.ThetaIntegrand.ext_invariant (R.cV i) hx γ hγ h)
  have key := GlobalTheory.DefiniteQuotient.integrableOn_theta D R.ψ hom.std (Vc D i) (Wc D i) _ _ (R.ωP i t) hom hpos ℂ
    (LinearMap.smulRight (LinearMap.id : ℂ →ₗ[ℂ] ℂ) f) (fun x => theta_smul x hf) (fun h => l (R.extV i t y h)) hcont hinv
    (R.νV i t) (R.fdV i t) (hm.νV i t).1.1 (hm.νV i t).2 g
  have e : (fun h => thetaKO (R.ωP i t) h g (LinearMap.smulRight (LinearMap.id : ℂ →ₗ[ℂ] ℂ) f (l (R.extV i t y h)))) =
      fun h => thetaKO (R.ωP i t) h g f * l (R.extV i t y h) := by
    funext h
    exact (thetaKO_smul (R.ωP i t) h g _ f).trans (mul_comm _ _)
  rw [e] at key
  exact key

end GlobalTheory.DownLift.GenFinite

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IrreducibleGL1IsCharacter
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands.DegreeOne

theorem classOfDegreeOne_eq_ofChar : BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (x : IrrGL k), x.1 = 1 →
    ∃ (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ), x = IrrGL.ofChar χ hχ := by
  intro _ k _ _ _ _ _ x hx
  obtain ⟨n, c⟩ := x
  obtain rfl : n = 1 := hx
  obtain ⟨θ, hθ, ⟨e⟩⟩ := RankLeOne.exists_equiv_detRep k (Fin 1) _ c.rep.ρ c.rep.smooth c.rep.irr
  exact ⟨θ, hθ, congrArg (Sigma.mk 1) (c.cl_rep.symm.trans (IrrRep.cl_eq_iff.2 ⟨e⟩))⟩

end GlobalTheory.LocLanglands.DegreeOne
end

