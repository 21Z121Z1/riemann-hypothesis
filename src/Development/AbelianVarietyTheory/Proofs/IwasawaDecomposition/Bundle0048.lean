import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOscillatorActionUnitaryGroupHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOscillatorActionOfGaussianPairings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0159
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0008
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0043
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0042
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0033
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FderivCompress
section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology

namespace GlobalTheory.Mem.Lift.VacBd

section General

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
  {om : V → V → ℝ} {ρ : V → B →L[ℂ] B}

theorem orbit_lip (h : IsHeis om ρ) {f : B} (hf : Sm ρ f) : ∃ C : ℝ, ∀ z, ‖ρ z f - f‖ ≤ C * ‖z‖ := by
  have hd := (ContDiff.differentiable hf (by simp) 0).hasFDerivAt.isBigO_sub
  obtain ⟨C, hC0, hC⟩ := hd.exists_pos
  obtain ⟨δ, hδ, hC⟩ := Metric.eventually_nhds_iff.1 hC.bound
  refine ⟨C + 2 * ‖f‖ / δ, fun z => ?_⟩
  have h0 : 0 ≤ 2 * ‖f‖ / δ * ‖z‖ := by positivity
  have h1 : 0 ≤ C * ‖z‖ := by positivity
  rw [add_mul]
  by_cases hz : ‖z‖ < δ
  · have := hC (y := z) (by simpa using hz)
    simp only [h.1, sub_zero] at this
    linarith
  · have h2 : ‖ρ z f - f‖ ≤ 2 * ‖f‖ := by
      have := norm_sub_le (ρ z f) f
      rw [h.2.2.1] at this
      linarith
    have h3 : 2 * ‖f‖ ≤ 2 * ‖f‖ / δ * ‖z‖ := by
      calc 2 * ‖f‖ = 2 * ‖f‖ / δ * δ := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left (not_lt.1 hz) (by positivity)
    linarith

theorem dH_bound [CompleteSpace B] (h : IsHeis om ρ) (T : B →L[ℂ] B) (hT : ∀ x, Sm ρ (T x)) :
    ∃ C : ℝ, ∀ z x, ‖dH ρ z (T x)‖ ≤ C * ‖z‖ * ‖x‖ := by
  obtain ⟨C, hC⟩ := banach_steinhaus (g := fun z : V => ((‖z‖ : ℂ)⁻¹) • ((ρ z).comp T - T)) (fun x => by
    obtain ⟨C, hC⟩ := orbit_lip h (hT x)
    refine ⟨max C 0, fun z => ?_⟩
    by_cases hz : z = 0
    · simp [hz]
    · have hz' : 0 < ‖z‖ := norm_pos_iff.2 hz
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
        norm_smul, norm_inv, Complex.norm_real, norm_norm]
      rw [inv_mul_le_iff₀ hz', mul_comm]
      exact (hC z).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hz'.le))
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  refine ⟨C, fun z x => ?_⟩
  have h1 : ‖fderiv ℝ (fun u => ρ u (T x)) 0‖ ≤ C * ‖x‖ := by
    refine (ContDiff.differentiable (hT x) (by simp) 0).hasFDerivAt.le_of_lip' (by positivity)
      (Filter.Eventually.of_forall fun w => ?_)
    by_cases hz : w = 0
    · simp [hz]
    · have hz' : 0 < ‖w‖ := norm_pos_iff.2 hz
      have := ContinuousLinearMap.le_of_opNorm_le _ (hC w) x
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
        norm_smul, norm_inv, Complex.norm_real, norm_norm] at this
      rw [inv_mul_le_iff₀ hz', mul_comm] at this
      simpa only [h.1, sub_zero] using this
  have := ContinuousLinearMap.le_of_opNorm_le _ h1 z
  unfold dH
  linarith [mul_right_comm C ‖x‖ ‖z‖]

end General

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] {J : V ≃ₗᵢ[ℝ] V}
  {ρ : V → B →L[ℂ] B}

set_option linter.unusedSectionVars false

theorem heis_dH (h : IsHeis (omJ J) ρ) {f : B} (hf : Sm ρ f) (v w : V) :
    ρ w (dH ρ v f) = (π * I * (omJ J w v : ℂ)) • ρ w f + fderiv ℝ (fun u => ρ u f) w v := by
  have h1 := ((ρ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_dH v hf)
  have h2 : HasDerivAt (fun t : ℝ => w + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add w
  have h3 : HasDerivAt (fun t : ℝ => ρ (w + t • v) f) (fderiv ℝ (fun u => ρ u f) w v) 0 :=
    (ContDiff.differentiable hf (by simp) w).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) h2 (by simp)
  have h4 : HasDerivAt (fun t : ℝ => cexp ((π * I * (omJ J w v : ℂ)) * (t : ℂ))) (π * I * (omJ J w v : ℂ)) 0 := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := 0)).const_mul (π * I * (omJ J w v : ℂ))).cexp
  have h5 := h4.smul h3
  have e : ((ρ w).restrictScalars ℝ) ∘ (fun t : ℝ => ρ (t • v) f) =
      (fun t : ℝ => cexp ((π * I * (omJ J w v : ℂ)) * (t : ℂ))) • fun t : ℝ => ρ (w + t • v) f := by
    funext t
    simp only [Function.comp, ContinuousLinearMap.coe_restrictScalars', h.2.1, Pi.smul_apply', omJ, map_smul,
      real_inner_smul_right]
    congr 2
    push_cast
    ring
  rw [e] at h1
  have := h1.unique h5
  simpa [add_comm] using this

theorem contDiff_omJ (v : V) : ContDiff ℝ ∞ fun w : V => (π * I * (omJ J w v : ℂ)) := by
  unfold omJ
  exact contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_id.inner ℝ contDiff_const))

theorem sm_dH (h : IsHeis (omJ J) ρ) {f : B} (hf : Sm ρ f) (v : V) : Sm ρ (dH ρ v f) := by
  unfold Sm
  simp only [heis_dH h hf]
  exact ((contDiff_omJ v).smul hf).add
    ((ContDiff.fderiv_right (m := ∞) hf (by simp)).clm_apply contDiff_const)

theorem fderiv_compress (P : B →L[ℂ] B) {g y : B} (hg : Sm ρ g) {φ : V → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (e : ∀ w, P (ρ w g) = φ w • y) (w v : V) : P (fderiv ℝ (fun u => ρ u g) w v) = fderiv ℝ φ w v • y := by
  have h1 := (P.restrictScalars ℝ).hasFDerivAt.comp w (ContDiff.differentiable hg (by simp) w).hasFDerivAt
  have h2 := (hφ.differentiable (by simp) w).hasFDerivAt.smul_const y
  have e' : (P.restrictScalars ℝ) ∘ (fun u => ρ u g) = fun u => φ u • y := funext e
  rw [e'] at h1
  simpa using DFunLike.congr_fun (h1.unique h2) v

theorem vacuum_bound : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (J : V ≃ₗᵢ[ℝ] V) (ρ : V → B →L[ℂ] B), (∀ x, J (J x) = -x) → ∀ h : IsHeis (omJ J) ρ, (∃ C : ℝ, ∀ z x, ‖dH ρ z (proj h x)‖ ≤ C * ‖z‖ * ‖x‖) ∧ (∀ u v, ∃ C : ℝ, ∀ x, ‖dH ρ u (dH ρ v (proj h x))‖ ≤ C * ‖x‖) ∧ ∀ u v, ∃ lam : ℂ, ∀ x, proj h (dH ρ u (dH ρ v (proj h x))) = lam • proj h x := by
  intro V _ _ _ _ _ B _ _ _ J ρ hJ h
  have hs : ∀ x, Sm ρ (proj h x) := fun x => (Osc.good_proj hJ h x).sm hJ
  obtain ⟨C, hC⟩ := dH_bound h (proj h) hs
  refine ⟨⟨C, hC⟩, fun u v => ?_, fun u v => ?_⟩
  · let T : B →L[ℂ] B := LinearMap.mkContinuous
      { toFun := fun x => dH ρ v (proj h x)
        map_add' := fun x y => by rw [map_add, dH_add v (hs x) (hs y)]
        map_smul' := fun a x => by rw [map_smul, dH_smul v a (hs x), RingHom.id_apply] } (C * ‖v‖) (hC v)
    obtain ⟨D, hD⟩ := dH_bound h T fun x => sm_dH h (hs x) v
    exact ⟨D * ‖u‖, hD u⟩
  · have hg : ContDiff ℝ ∞ (gau : V → ℂ) := contDiff_gau
    have hφ : ContDiff ℝ ∞ fun w : V => (π * I * (omJ J w v : ℂ)) * gau w + fderiv ℝ gau w v :=
      ((contDiff_omJ v).mul hg).add ((ContDiff.fderiv_right (m := ∞) hg (by simp)).clm_apply contDiff_const)
    refine ⟨_, fun x => fderiv_compress (proj h) (sm_dH h (hs x) v) hφ (fun w => ?_) 0 u⟩
    rw [heis_dH h (hs x), map_add, map_smul, proj_heis_proj hJ h,
      fderiv_compress (proj h) (hs x) hg (fun w => proj_heis_proj hJ h w x), add_smul, mul_smul _ (gau w)]

end GlobalTheory.Mem.Lift.VacBd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedVectorOfMemIsotypicComponentStatement
section
open Formalism.L2 Formalism.AUTREP ReciprocityTheory.Aut NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixed_vector_of_mem_isotypic_component : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GQ L n) W) (S : Submodule ℂ (GAf L n → W)) (K : Set (GAf L n)), NG.IsIrrRep ρ S → ∀ f ∈ NG.isoTyp ρ S, f ≠ 0 → (∀ κ ∈ K, NG.rt L n κ f = f) → ∃ f' ∈ S, f' ≠ 0 ∧ ∀ κ ∈ K, NG.rt L n κ f' = f' := by
  first | exact @GlobalTheory.IsoFix.fixed_of_isoTyp | exact GlobalTheory.IsoFix.fixed_of_isoTyp | (intros; apply GlobalTheory.IsoFix.fixed_of_isoTyp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusInvMulMemInertiaStatement
section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_inv_mul_mem_inertia : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (v : HeightOneSpectrum (𝓞 E))
    (A : ValuationSubring Ω), IsPlaceOver A v → ∀ τ τ' : G E Ω, IsFrob (F := E) A (normV v) τ →
    IsFrob (F := E) A (normV v) τ' → τ'⁻¹ * τ ∈ Ine (F := E) A := by
  first | exact @GlobalTheory.frob_inv_mul_mem_inertia | exact GlobalTheory.frob_inv_mul_mem_inertia | (intros; apply GlobalTheory.frob_inv_mul_mem_inertia <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusRatioPiCongrTameUnitStatement
section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_ratio_pi_congr_tame_unit : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (v : HeightOneSpectrum (𝓞 E))
    (A : ValuationSubring Ω), IsPlaceOver A v → ∀ u : 𝓞 E, u ∉ v.asIdeal → ∀ π t : Ω, π ≠ 0 →
    t ^ (normV v - 1) = algebraMap E Ω (u : E) → ∀ τ τ' : G E Ω, IsFrob (F := E) A (normV v) τ →
    IsFrob (F := E) A (normV v) τ' → τ π = π → τ' (π * t) = π * t →
    A.valuation ((τ'⁻¹ * τ) π / π - algebraMap E Ω (u : E)) < 1 := by
  first | exact @GlobalTheory.TameRatio.ratio_cong | exact GlobalTheory.TameRatio.ratio_cong | (intros; apply GlobalTheory.TameRatio.ratio_cong <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusRestrictScalarsPowModInertia
section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat

noncomputable section

namespace GlobalTheory.FrobRestrict

open scoped Pointwise

open NumberField IsDedekindDomain in
open scoped Pointwise in
theorem _root_.GlobalTheory.FrobRestrict.isFrob_pow {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    {A : ValuationSubring Ω} {q : ℕ} {φ : _root_.Formalism.ConjugateSelfDual.G F Ω} (hφ : _root_.Formalism.ConjugateSelfDual.IsFrob A q φ) (n : ℕ) :
    _root_.Formalism.ConjugateSelfDual.IsFrob A (q ^ n) (φ ^ n) := by
  have hdec : φ ∈ ValuationSubring.decompositionSubgroup F A := hφ.1
  induction n with
  | zero => exact ⟨one_mem _, fun x _ => by simp⟩
  | succ n ih =>
    refine ⟨Subgroup.pow_mem _ hdec _, fun x hx => ?_⟩
    have hxq : A.valuation (x ^ q) ≤ 1 := by rw [map_pow]; exact pow_le_one' hx q
    have e : (φ ^ (n + 1)) x - x ^ q ^ (n + 1)
        = ((φ ^ n) (x ^ q) - (x ^ q) ^ q ^ n) + (φ ^ n) (φ x - x ^ q) := by
      rw [pow_succ, AlgEquiv.mul_apply, map_sub, pow_succ', pow_mul]
      ring
    rw [e]
    refine Valuation.map_add_lt _ (ih.2 _ hxq) ?_
    rw [_root_.ReciprocityTheory.Gal.valuation_apply_lt_one_iff (Subgroup.pow_mem _ hdec n)]
    exact hφ.2 x hx

open NumberField IsDedekindDomain in
open scoped Pointwise in
private lemma restrictScalars_mem_decompositionSubgroup {E Ω : Type} [Field E] [Field Ω]
    [Algebra E Ω] {K : IntermediateField E Ω} {A : ValuationSubring Ω} {ι : _root_.Formalism.ConjugateSelfDual.G K Ω}
    (h : ι ∈ ValuationSubring.decompositionSubgroup K A) :
    ι.restrictScalars E ∈ ValuationSubring.decompositionSubgroup E A := by
  simp only [ValuationSubring.decompositionSubgroup, MulAction.mem_stabilizer_iff] at h ⊢
  exact h

open NumberField IsDedekindDomain in
open scoped Pointwise in
theorem _root_.GlobalTheory.FrobRestrict.frob_restrict : ∀ (E Ω : Type) [Field E] [NumberField E]
    [Field Ω] [Algebra E Ω] (K : IntermediateField E Ω) [FiniteDimensional E K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 K)),
    w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal → ∀ A : ValuationSubring Ω,
    _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w → _root_.Formalism.ConjugateSelfDual.IsPlaceOver A v ∧ _root_.Formalism.ConjugateSelfDual.normV w = _root_.Formalism.ConjugateSelfDual.normV v ^ w.asIdeal.inertiaDeg (𝓞 E) ∧
    (∀ ι ∈ _root_.ReciprocityTheory.Gal.Ine (F := K) A, ι.restrictScalars E ∈ _root_.ReciprocityTheory.Gal.Ine (F := E) A) ∧
    ∀ (σ : _root_.Formalism.ConjugateSelfDual.G K Ω) (φ : _root_.Formalism.ConjugateSelfDual.G E Ω), _root_.Formalism.ConjugateSelfDual.IsFrob A (_root_.Formalism.ConjugateSelfDual.normV w) σ → _root_.Formalism.ConjugateSelfDual.IsFrob A (_root_.Formalism.ConjugateSelfDual.normV v) φ →
    σ.restrictScalars E * (φ ^ w.asIdeal.inertiaDeg (𝓞 E))⁻¹ ∈ _root_.ReciprocityTheory.Gal.Ine (F := E) A := by
  intro E Ω _ _ _ _ K _ _ v w h A hw
  have hnorm : _root_.Formalism.ConjugateSelfDual.normV w = _root_.Formalism.ConjugateSelfDual.normV v ^ w.asIdeal.inertiaDeg (𝓞 E) := by
    haveI : w.asIdeal.LiesOver v.asIdeal := ⟨h.symm⟩
    haveI := v.isMaximal
    haveI := w.isMaximal
    rw [Ideal.inertiaDeg_eq_of_isMaximal v.asIdeal w.asIdeal]
    unfold _root_.Formalism.ConjugateSelfDual.normV
    letI := Ideal.Quotient.field v.asIdeal
    exact Module.natCard_eq_pow_finrank (K := 𝓞 E ⧸ v.asIdeal) (V := 𝓞 K ⧸ w.asIdeal)
  refine ⟨fun x => ?_, hnorm, fun ι hι => ?_, fun σ φ hσ hφ => ?_⟩
  · have e : (algebraMap K Ω) ((algebraMap (𝓞 E) (𝓞 K) x : 𝓞 K) : K)
        = algebraMap E Ω (x : E) := by
      rw [IsScalarTower.algebraMap_apply E K Ω]
      rfl
    rw [← e, hw, ← h, Ideal.mem_comap]
  · rw [_root_.ReciprocityTheory.Gal.mem_Ine] at hι ⊢
    exact ⟨restrictScalars_mem_decompositionSubgroup hι.1, hι.2⟩
  · have hσ' : _root_.Formalism.ConjugateSelfDual.IsFrob A (_root_.Formalism.ConjugateSelfDual.normV v ^ w.asIdeal.inertiaDeg (𝓞 E)) (σ.restrictScalars E) := by
      rw [← hnorm]
      exact ⟨restrictScalars_mem_decompositionSubgroup hσ.1, hσ.2⟩
    have hφf := _root_.GlobalTheory.FrobRestrict.isFrob_pow hφ (w.asIdeal.inertiaDeg (𝓞 E))
    have h1 := _root_.ReciprocityTheory.Gal.inv_mul_mem_Ine_of_isFrob hφf hσ'
    have h2 := _root_.ReciprocityTheory.Gal.conj_mem_Ine (g := φ ^ w.asIdeal.inertiaDeg (𝓞 E)) hφf.1 h1
    rwa [mul_inv_cancel_left] at h2

end GlobalTheory.FrobRestrict
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlRelOfCanonicalCommutationRelations
section
open Matrix GlobalTheory.Mem.Lift

namespace GlobalTheory.Mem.Lift

theorem IsCCR.comm_monomial {A : Type} [Ring A] {κ : Type} [DecidableEq κ] {x d : κ → A} (h : IsCCR x d)
    (k l k' l' : κ) : x k * d l * (x k' * d l') - x k' * d l' * (x k * d l) =
      (if k' = l then x k * d l' else 0) - (if k = l' then x k' * d l else 0) := by
  obtain ⟨hx, hd, hc⟩ := h
  have e1 : x k * d l * (x k' * d l') = x k * (d l * x k' - x k' * d l) * d l' + x k * x k' * (d l * d l') := by
    noncomm_ring
  have e2 : x k' * d l' * (x k * d l) = x k' * (d l' * x k - x k * d l') * d l + x k' * x k * (d l' * d l) := by
    noncomm_ring
  rw [e1, e2, hc, hc, hx k' k, hd l' l]
  split_ifs <;> simp

theorem glRel_of_isCCR (A : Type) [Ring A] (n m : ℕ) (x d : Fin n × Fin m → A) (h : IsCCR x d) :
    Formalism.REAL.GlRel (fun i j : Fin n => ∑ a, x (i, a) * d (j, a)) ∧
      Formalism.REAL.GlRel (fun a b : Fin m => -∑ i, x (i, b) * d (i, a)) := by
  refine ⟨fun i j k l => ?_, fun a b c e => ?_⟩
  · beta_reduce
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_comm (f := fun s t => x (k, s) * d (l, s) * (x (i, t) * d (j, t))),
      ← Finset.sum_sub_distrib]
    simp_rw [← Finset.sum_sub_distrib, h.comm_monomial, Finset.sum_sub_distrib, Prod.mk.injEq]
    congr 1
    · by_cases hjk : j = k
      · simp [hjk]
      · simp [hjk, Ne.symm hjk]
    · by_cases hli : l = i
      · simp [hli]
      · simp [hli, Ne.symm hli]
  · beta_reduce
    rw [neg_mul_neg, neg_mul_neg, Finset.sum_mul_sum, Finset.sum_mul_sum,
      Finset.sum_comm (f := fun s t => x (s, e) * d (s, c) * (x (t, b) * d (t, a))), ← Finset.sum_sub_distrib]
    simp_rw [← Finset.sum_sub_distrib, h.comm_monomial, Finset.sum_sub_distrib, Prod.mk.injEq]
    by_cases hbc : b = c <;> by_cases hea : e = a <;> simp [hbc, hea, sub_eq_neg_add, add_comm]

end GlobalTheory.Mem.Lift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasDerivAtLineDH
section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology

namespace GlobalTheory.Mem.Lift

theorem hasDerivAt_line_dH {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : Type} [NormedAddCommGroup B]
    [NormedSpace ℂ B] (om : V →L[ℝ] V →L[ℝ] ℝ) {ρ : V → B →L[ℂ] B} (h0 : ∀ x, om x x = 0)
    (h : IsHeis (fun x y => om x y) ρ) (v : V) {f : B} (hf : Sm ρ f) (s : ℝ) :
    HasDerivAt (fun t : ℝ => ρ (t • v) f) (ρ (s • v) (dH ρ v f)) s := by
  have e : (fun t : ℝ => ρ (t • v) f) = fun t : ℝ => ρ (s • v) (ρ ((t - s) • v) f) := by
    funext t
    rw [h.2.1, ← add_smul]
    simp [h0]
  have h1 : HasDerivAt (fun t : ℝ => ρ ((t - s) • v) f) (dH ρ v f) s := by
    have h2 : HasDerivAt (fun t : ℝ => ρ (t • v) f) (dH ρ v f) (s - s) := by
      rw [sub_self]; exact hasDerivAt_dH v hf
    exact h2.comp_sub_const s s
  rw [e]
  exact ((ρ (s • v)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s h1

theorem dH_integral : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (om : V →L[ℝ] V →L[ℝ] ℝ) (ρ : V → B →L[ℂ] B), (∀ x, om x x = 0) → IsHeis (fun x y => om x y) ρ → ∀ (Y : Type) [MeasurableSpace Y] (ν : Measure Y) (F : Y → B), (∀ y, Sm ρ (F y)) → Integrable F ν → Sm ρ (∫ y, F y ∂ν) → ∀ v, Integrable (fun y => dH ρ v (F y)) ν → dH ρ v (∫ y, F y ∂ν) = ∫ y, dH ρ v (F y) ∂ν := by
  intro V _ _ B _ _ _ om ρ h0 h Y _ ν F hF hFi hS v hd
  have key := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν) (𝕜 := ℝ) (x₀ := (0 : ℝ)) (s := Set.univ)
    (F := fun (t : ℝ) y => ρ (t • v) (F y)) (F' := fun (t : ℝ) y => ρ (t • v) (dH ρ v (F y)))
    (bound := fun y => ‖dH ρ v (F y)‖) Filter.univ_mem
    (Filter.Eventually.of_forall fun t => ((ρ (t • v)).integrable_comp hFi).aestronglyMeasurable)
    ((ρ _).integrable_comp hFi) ((ρ _).integrable_comp hd).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y t _ => (h.2.2.1 _ _).le) hd.norm
    (Filter.Eventually.of_forall fun y t _ => hasDerivAt_line_dH om h0 h v (hF y) t)).2
  simp only [zero_smul, h.1, ContinuousLinearMap.integral_comp_comm _ hFi] at key
  exact (hasDerivAt_dH v hS).unique key

end GlobalTheory.Mem.Lift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeisenbergSmoothVectorDerivativeCalculusStatement
section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergSmoothVector_derivative_calculus : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] (om : V →L[ℝ] V →L[ℝ] ℝ) (ρ : V → B →L[ℂ] B), (∀ x, om x x = 0) → IsHeis (fun x y => om x y) ρ → ∀ f, Sm ρ f → (∀ v, Sm ρ (dH ρ v f)) ∧ (∀ w, Sm ρ (ρ w f)) ∧ (∀ w y, fderiv ℝ (fun u => ρ u f) w y = ρ w (dH ρ y f) - (π * I * (om w y : ℂ)) • ρ w f) ∧ (∀ v w, dH ρ v (ρ w f) = ρ w (dH ρ v f) + (2 * π * I * (om v w : ℂ)) • ρ w f) ∧ ∀ u v, dH ρ u (dH ρ v f) - dH ρ v (dH ρ u f) = (2 * π * I * (om u v : ℂ)) • f := by
  first | exact @GlobalTheory.Mem.Lift.DCalc.dH_calculus | exact GlobalTheory.Mem.Lift.DCalc.dH_calculus | (intros; apply GlobalTheory.Mem.Lift.DCalc.dH_calculus <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertiaPowResidueCardSubOneApplyOfPowMemStatement
section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertia_pow_residueCard_sub_one_apply_of_pow_mem : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (v : HeightOneSpectrum (𝓞 E))
    (A : ValuationSubring Ω), IsPlaceOver A v → ∀ (w : E) (π : Ω), π ^ (normV v - 1) = algebraMap E Ω w →
    ∀ ρ ∈ Ine (F := E) A, (ρ ^ (normV v - 1)) π = π := by
  first | exact @GlobalTheory.ine_pow_normV_sub_one_apply_of_pow_mem | exact GlobalTheory.ine_pow_normV_sub_one_apply_of_pow_mem | (intros; apply GlobalTheory.ine_pow_normV_sub_one_apply_of_pow_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNilpotentZpowSubOne
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilDeligne.FrobSemisimpleUnique

theorem isNilpotent_zpow_sub_one {R : Type*} [Ring R] (u : Rˣ) (hu : IsNilpotent ((u : R) - 1))
    (d : ℤ) : IsNilpotent (((u ^ d : Rˣ) : R) - 1) := by
  have hnat : ∀ n : ℕ, IsNilpotent (((u ^ n : Rˣ) : R) - 1) := by
    intro n
    rw [Units.val_pow_eq_pow_val, ← geom_sum_mul]
    refine Commute.isNilpotent_mul_left ?_ hu
    refine Commute.sum_left _ _ _ fun i _ => ?_
    exact ((Commute.refl (u : R)).sub_right (Commute.one_right _)).pow_left i
  obtain ⟨n, rfl | rfl⟩ := d.eq_nat_or_neg
  · rw [zpow_natCast]; exact hnat n
  · rw [zpow_neg, zpow_natCast]
    have h1 := hnat n
    generalize u ^ n = v at h1
    have h2 : ((v⁻¹ : Rˣ) : R) - 1 = -(((v⁻¹ : Rˣ) : R) * ((v : R) - 1)) := by
      rw [mul_sub, Units.inv_mul, mul_one, neg_sub]
    rw [h2]
    refine (Commute.isNilpotent_mul_left ?_ h1).neg
    exact ((Commute.refl v).inv_left.units_val).sub_right (Commute.one_right _)

theorem nilpotent_part {R : Type*} [Ring R] {f s : R} (v : Rˣ) (hv : IsNilpotent ((v : R) - 1))
    (hc : Commute (v : R) f) (hf : f = s * v) : IsNilpotent (f - s) ∧ Commute (f - s) s := by
  have hs : s = f * ((v⁻¹ : Rˣ) : R) := by rw [hf, Units.mul_inv_cancel_right]
  have hvs : Commute (v : R) s := by
    rw [hs]
    exact hc.mul_right (Commute.refl v).inv_right.units_val
  have h1 : f - s = s * ((v : R) - 1) := by rw [hf, mul_sub, mul_one]
  have h2 : Commute s ((v : R) - 1) := hvs.symm.sub_right (Commute.one_right _)
  rw [h1]
  exact ⟨h2.isNilpotent_mul_left hv, (Commute.refl s).mul_left h2.symm⟩

end GlobalTheory.WeilDeligne.FrobSemisimpleUnique
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPurePairIffMonodromyFiltration
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilDeligne

section Graded

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {U : ℤ → Submodule K V}
  {N : End K V}

theorem exists_proj_of_iSupIndep (hi : iSupIndep U) (ht : ⨆ i, U i = ⊤) :
    ∃ p : ℤ → End K V, (∀ d v, p d v ∈ U d) ∧ (∀ d, ∀ v ∈ U d, p d v = v) ∧
      (∀ d e, e ≠ d → ∀ v ∈ U e, p d v = 0) ∧
      ∀ (S : Submodule K V) (v : V), (∀ d, p d v ∈ S) → v ∈ S := by
  classical
  let := (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hi ht).chooseDecomposition
  refine ⟨fun d => (U d).subtype ∘ₗ DirectSum.component K ℤ (fun i => U i) d ∘ₗ
    (DirectSum.decomposeLinearEquiv U).toLinearMap, fun d v => Subtype.coe_prop _,
    fun d v hv => DirectSum.decompose_of_mem_same U hv,
    fun d e hed v hv => DirectSum.decompose_of_mem_ne U hv hed, fun S v hv => ?_⟩
  rw [← DirectSum.sum_support_decompose U v]
  exact S.sum_mem fun d _ => hv d

theorem pow_mem_of_degree_two (hN : ∀ d, ∀ v ∈ U d, N v ∈ U (d + 2)) (m : ℕ) {d e : ℤ}
    (he : e = d + 2 * m) {v : V} (hv : v ∈ U d) : (N ^ m) v ∈ U e := by
  subst he
  induction m with
  | zero => simpa using hv
  | succ m ih =>
    rw [pow_succ', End.mul_apply]
    have := hN _ _ ih
    rwa [show d + 2 * (m : ℤ) + 2 = d + 2 * ((m + 1 : ℕ) : ℤ) by push_cast; ring] at this

theorem eq_zero_of_pow_eq_zero (hb : ∀ i : ℕ, Set.BijOn (N ^ i) (U (-i)) (U i)) {m : ℕ} {d : ℤ}
    (hd : d + m ≤ 0) {v : V} (hv : v ∈ U d) (h0 : (N ^ m) v = 0) : v = 0 := by
  obtain ⟨c, hc⟩ : ∃ c : ℕ, d = -((c + m : ℕ) : ℤ) := ⟨(-d - m).toNat, by omega⟩
  subst hc
  refine (hb (c + m)).2.1 hv (zero_mem _) ?_
  rw [pow_add, End.mul_apply, h0, map_zero, map_zero]

theorem exists_pow_eq (hN : ∀ d, ∀ v ∈ U d, N v ∈ U (d + 2))
    (hb : ∀ i : ℕ, Set.BijOn (N ^ i) (U (-i)) (U i)) {m : ℕ} {d e : ℤ}
    (hd : (m : ℤ) ≤ d) (he : d = e + 2 * m) {v : V} (hv : v ∈ U d) :
    ∃ u ∈ U e, (N ^ m) u = v := by
  obtain ⟨c, hc⟩ : ∃ c : ℕ, d = ((m + c : ℕ) : ℤ) := ⟨(d - m).toNat, by omega⟩
  rw [hc] at hv
  obtain ⟨u, hu, rfl⟩ := (hb (m + c)).2.2 hv
  refine ⟨(N ^ c) u, pow_mem_of_degree_two hN c (by omega) hu, ?_⟩
  rw [pow_add, End.mul_apply]

end Graded

theorem iSupIndep_absSpace {V ι : Type*} [AddCommGroup V] [Module ℂ V] (f : End ℂ V) {r : ι → ℝ}
    (hr : Function.Injective r) : iSupIndep fun i => absSpace f (r i) := by
  intro i
  refine ((End.eigenspaces_iSupIndep f).disjoint_biSup_biSup (s := {α | ‖α‖ = r i})
    (t := {α | ‖α‖ ≠ r i}) disjoint_compl_right).mono_right ?_
  refine iSup₂_le fun j hj => iSup₂_le fun α hα => le_iSup₂_of_le α ?_ le_rfl
  exact fun h => hj (hr (hα.symm.trans h))

end GlobalTheory.WeilDeligne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsTorusWeightOfPolyRepCompSwap
section
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

namespace GlobalTheory

theorem isWt_comp_swap : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ),
    IsPolyRep Φ → ∀ μ : Fin n → ℤ, IsWt Φ μ → ∀ i j : Fin n, IsWt Φ (μ ∘ Equiv.swap i j) := by
  intro n ι _ _ Φ hΦ μ ⟨w, hw0, hw⟩ i j
  set σ : Equiv.Perm (Fin n) := Equiv.swap i j with hσ
  set P : Matrix (Fin n) (Fin n) ℂ := σ.toPEquiv.toMatrix with hP
  have hσσ : ∀ k, σ (σ k) = k := fun k => Equiv.swap_apply_self _ _ _
  have hPP : P * P = 1 := by
    rw [hP, ← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]
    have : σ.trans σ = Equiv.refl _ := by ext k; simp [hσσ]
    rw [this, Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
  let p : GL (Fin n) ℂ := ⟨P, P, hPP, hPP⟩
  have hpp : p * p = 1 := Units.ext hPP
  refine ⟨Φ p *ᵥ w, ?_, ?_⟩
  · intro h
    apply hw0
    have : Φ p *ᵥ (Φ p *ᵥ w) = 0 := by rw [h]; simp
    rwa [mulVec_mulVec, ← hΦ.mul, hpp, hΦ.one, one_mulVec] at this
  · intro D hD
    have hent : ∀ a b, (p * D * p).val a b = D.val (σ a) (σ b) := by
      intro a b
      show (P * D.val * P) a b = _
      rw [hP, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
      simp [hσ, Equiv.symm_swap]
    have hD' : (p * D * p).val.IsDiag := by
      intro a b hab
      rw [hent]
      exact hD (fun h => hab (σ.injective h))
    have key : Φ D * Φ p = Φ p * Φ (p * D * p) := by
      rw [← hΦ.mul, ← hΦ.mul]
      congr 1
      rw [← mul_assoc, ← mul_assoc, hpp, one_mul]
    have hprod : (∏ k, (p * D * p).val k k ^ μ k) = ∏ k, D.val k k ^ (μ ∘ σ) k := by
      simp only [hent, Function.comp]
      rw [← Equiv.prod_comp σ (fun k => D.val k k ^ μ (σ k))]
      simp [hσσ]
    rw [mulVec_mulVec, key, ← mulVec_mulVec, hw _ hD', hprod, mulVec_smul]
end GlobalTheory
end

