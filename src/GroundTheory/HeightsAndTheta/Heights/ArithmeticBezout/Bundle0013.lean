import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle0003

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PHolomorphicImplicitGraph
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Module Function

noncomputable section

namespace HolomorphicImplicitGraph

theorem exists_coordSplitting {n m : ℕ} (L : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] (Fin (n - m) → ℂ))
    (hL : finrank ℂ (LinearMap.ker L) = m) :
    ∃ e : Fin n ≃ Fin m ⊕ Fin (n - m), ∀ v : EuclideanSpace ℂ (Fin n),
      (∀ j k, e j = Sum.inl k → v j = 0) → L v = 0 → v = 0 := by
  classical
  have hmn : m ≤ n := by
    have := Submodule.finrank_le (LinearMap.ker L)
    simpa [hL] using this
  have hrange : LinearMap.range L = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have := LinearMap.finrank_range_add_finrank_ker L
    simp only [finrank_euclideanSpace_fin, hL] at this
    simp only [Module.finrank_fin_fun]
    omega
  let w : Fin n → (Fin (n - m) → ℂ) := fun j => L (EuclideanSpace.single j 1)
  have hw : Submodule.span ℂ (Set.range w) = ⊤ := by
    rw [← hrange, LinearMap.range_eq_map, ← (EuclideanSpace.basisFun (Fin n) ℂ).toBasis.span_eq,
      Submodule.map_span, ← Set.range_comp]
    congr 2
    ext j
    simp [w]
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' ℂ w
  have : Finite κ := Finite.of_injective a ha
  let : Fintype κ := Fintype.ofFinite κ
  have hcardκ : Fintype.card κ = n - m := by
    have := finrank_span_eq_card hli
    rw [hsp, hw, finrank_top, Module.finrank_fin_fun] at this
    exact this.symm
  let s : Set (Fin n) := Set.range a
  have hcs : Fintype.card s = n - m := by
    rw [← hcardκ]
    exact Fintype.card_congr (Equiv.ofInjective a ha).symm
  have hcc : Fintype.card (sᶜ : Set (Fin n)) = m := by
    rw [Fintype.card_compl_set, hcs, Fintype.card_fin]
    omega
  let eS : s ≃ Fin (n - m) := Fintype.equivFinOfCardEq hcs
  let eM : (sᶜ : Set (Fin n)) ≃ Fin m := Fintype.equivFinOfCardEq hcc
  let e : Fin n ≃ Fin m ⊕ Fin (n - m) :=
    (Equiv.Set.sumCompl s).symm.trans ((Equiv.sumComm _ _).trans (Equiv.sumCongr eM eS))
  refine ⟨e, fun v hv hLv => ?_⟩
  have hout : ∀ j ∉ s, v j = 0 := fun j hj =>
    hv j (eM ⟨j, hj⟩) (by simp [e, Equiv.Set.sumCompl_symm_apply_of_notMem hj])
  have hv' : L v = ∑ j, v j • w j := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) ℂ).sum_repr v]
    simp [w, map_sum, map_smul]
  have hsum : ∑ c, v (a c) • w (a c) = 0 := by
    rw [Fintype.sum_of_injective a ha (fun c => v (a c) • w (a c)) (fun j => v j • w j)
      (fun j hj => by rw [hout j hj, zero_smul]) (fun c => rfl), ← hv', hLv]
  have hin : ∀ c, v (a c) = 0 := Fintype.linearIndependent_iff.1 hli (fun c => v (a c)) hsum
  refine PiLp.ext fun j => ?_
  by_cases hj : j ∈ s
  · obtain ⟨c, rfl⟩ := hj
    simpa using hin c
  · simpa using hout j hj

end HolomorphicImplicitGraph

theorem HolomorphicImplicitGraph.proof : HolomorphicImplicitGraph.Statement := by
  classical
  intro n m f y V hf hV hyV hfy hK

  let L : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] (Fin (n - m) → ℂ) :=
    LinearMap.pi fun i => (fderiv ℂ (f i) y : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] ℂ)
  obtain ⟨e, he⟩ := exists_coordSplitting L (by rw [LinearMap.ker_pi]; exact hK)

  let F : EuclideanSpace ℂ (Fin n) → (Fin n → ℂ) := fun z j =>
    Sum.elim (fun _ => z j) (fun i => f i z) (e j)
  let D : EuclideanSpace ℂ (Fin n) → (EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin n → ℂ)) := fun z =>
    ContinuousLinearMap.pi fun j =>
      Sum.elim (fun _ => EuclideanSpace.proj j) (fun i => fderiv ℂ (f i) z) (e j)
  have hFd : ∀ z, HasFDerivAt F (D z) z := by
    intro z
    refine hasFDerivAt_pi.2 fun j => ?_
    rcases h : e j with k | i
    · simp only [Sum.elim_inl]
      exact (EuclideanSpace.proj (𝕜 := ℂ) j).hasFDerivAt
    · simp only [Sum.elim_inr]
      exact ((hf i).differentiable one_ne_zero z).hasFDerivAt
  have hFc : ContDiff ℂ 1 F := by
    refine contDiff_pi.2 fun j => ?_
    rcases h : e j with k | i
    · simp only [F, h, Sum.elim_inl]
      exact (EuclideanSpace.proj (𝕜 := ℂ) j).contDiff
    · simp only [F, h, Sum.elim_inr]
      exact hf i

  have hDy : Injective (D y) := by
    refine (injective_iff_map_eq_zero (D y)).2 fun v hv => he v (fun j k hj => ?_) ?_
    · have := congr_fun hv j
      simpa [D, hj] using this
    · funext i
      have := congr_fun hv (e.symm (Sum.inr i))
      simpa [D, L] using this
  let A : EuclideanSpace ℂ (Fin n) ≃L[ℂ] (Fin n → ℂ) :=
    (LinearEquiv.ofInjectiveOfFinrankEq (D y : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] (Fin n → ℂ)) hDy
      (by simp)).toContinuousLinearEquiv
  have hA : (A : EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin n → ℂ)) = D y := by
    ext1 v
    rfl
  let P := hFc.contDiffAt.toOpenPartialHomeomorph F (f' := A) (by rw [hA]; exact hFd y) one_ne_zero

  let W : Set (EuclideanSpace ℂ (Fin n)) := (fun z => fderiv ℂ F z) ⁻¹'
    Set.range ((↑) : (EuclideanSpace ℂ (Fin n) ≃L[ℂ] (Fin n → ℂ)) → _)
  have hW : IsOpen W := ContinuousLinearEquiv.isOpen.preimage (hFc.continuous_fderiv one_ne_zero)
  have hyW : y ∈ W := ⟨A, by rw [hA]; exact (hFd y).fderiv.symm⟩
  have hWinj : ∀ z ∈ W, Injective (D z) := by
    rintro z ⟨A', hA'⟩
    have hA'' : (A' : EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin n → ℂ)) = fderiv ℂ F z := hA'
    rw [← (hFd z).fderiv, ← hA'']
    exact A'.injective
  let U := P.source ∩ V ∩ W
  have hU : IsOpen U := (P.open_source.inter hV).inter hW
  have hyU : y ∈ U := ⟨⟨ContDiffAt.mem_toOpenPartialHomeomorph_source _ _ _, hyV⟩, hyW⟩

  let ι : EuclideanSpace ℂ (Fin m) →L[ℂ] (Fin n → ℂ) := ContinuousLinearMap.pi fun j =>
    Sum.elim (fun k => EuclideanSpace.proj k) (fun _ => (0 : EuclideanSpace ℂ (Fin m) →L[ℂ] ℂ)) (e j)
  let g := P.symm
  let Φ : EuclideanSpace ℂ (Fin m) → EuclideanSpace ℂ (Fin (n - m)) := fun x =>
    WithLp.toLp 2 fun i => g (ι x) (e.symm (Sum.inr i))
  let Ω : Set (EuclideanSpace ℂ (Fin m)) := ι ⁻¹' (P.target ∩ g ⁻¹' U)
  have hΩ : IsOpen Ω := (P.isOpen_inter_preimage_symm hU).preimage ι.continuous
  have hG : ∀ x, ι x ∈ P.target → graphPt e Φ x = g (ι x) := by
    intro x hx
    have hFg : F (g (ι x)) = ι x := P.right_inv hx
    refine PiLp.ext fun j => ?_
    have hj := congr_fun hFg j
    rcases h : e j with k | i
    · simp [graphPt, F, ι, h] at hj ⊢
      exact hj.symm
    · have hs : e.symm (Sum.inr i) = j := e.symm_apply_eq.2 h.symm
      simp [graphPt, Φ, h, hs]
  have hzero : ∀ x, ι x ∈ P.target → ∀ i, f i (g (ι x)) = 0 := by
    intro x hx i
    have := congr_fun (P.right_inv hx) (e.symm (Sum.inr i))
    simpa [P, F, ι] using this
  let pin : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin m) := fun z =>
    WithLp.toLp 2 fun k => z (e.symm (Sum.inl k))
  have hFpin : ∀ z, (∀ i, f i z = 0) → F z = ι (pin z) := by
    intro z hz
    funext j
    rcases h : e j with k | i
    · have hs : e.symm (Sum.inl k) = j := e.symm_apply_eq.2 h.symm
      simp [F, ι, pin, h, hs]
    · simp [F, ι, h, hz i]
  have hgdiff : ∀ x ∈ Ω, DifferentiableAt ℂ g (ι x) := by
    intro x hx
    obtain ⟨A', hA'⟩ := hx.2.2
    have h1 : HasFDerivAt P (A' : EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin n → ℂ)) (P.symm (ι x)) := by
      rw [hA']
      exact (hFd _).differentiableAt.hasFDerivAt
    exact (P.contDiffAt_symm hx.1 h1 hFc.contDiffAt).differentiableAt one_ne_zero
  refine ⟨e, Ω, Φ, U, hU, hyU, fun z hz => hz.1.2, hΩ, ?_, ?_, ?_⟩
  · intro x hx
    refine (differentiableAt_euclidean.2 fun i => ?_).differentiableWithinAt
    show DifferentiableAt ℂ (fun x => g (ι x) (e.symm (Sum.inr i))) x
    exact (EuclideanSpace.proj (𝕜 := ℂ) (e.symm (Sum.inr i))).differentiableAt.comp x
      ((hgdiff x hx).comp x ι.differentiableAt)
  · ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hG x hx.1]
      exact ⟨hx.2, hzero x hx.1⟩
    · rintro ⟨hzU, hz0⟩
      have hFz := hFpin z hz0
      have ht : ι (pin z) ∈ P.target := by
        rw [← hFz]
        exact P.map_source hzU.1.1
      have hgz : g (ι (pin z)) = z := by
        rw [← hFz]
        exact P.left_inv hzU.1.1
      refine ⟨pin z, ⟨ht, ?_⟩, by rw [hG _ ht, hgz]⟩
      show g (ι (pin z)) ∈ U
      rw [hgz]
      exact hzU
  · intro x hx
    have hgx := hgdiff x hx
    let g' := fderiv ℂ g (ι x)
    have hGd : HasFDerivAt (graphPt e Φ) (g'.comp ι) x := by
      have h1 : HasFDerivAt (fun x => g (ι x)) (g'.comp ι) x :=
        hgx.hasFDerivAt.comp x ι.hasFDerivAt
      refine h1.congr_of_eventuallyEq ?_
      filter_upwards [hΩ.mem_nhds hx] with x' hx' using hG x' hx'.1
    have hDg : ∀ w, D (g (ι x)) (g' w) = w := by
      have h1 : HasFDerivAt (fun w => F (g w)) ((D (g (ι x))).comp g') (ι x) :=
        (hFd _).comp (ι x) hgx.hasFDerivAt
      have h2 : HasFDerivAt (fun w => F (g w)) (ContinuousLinearMap.id ℂ (Fin n → ℂ)) (ι x) := by
        refine (hasFDerivAt_id (ι x)).congr_of_eventuallyEq ?_
        filter_upwards [P.open_target.mem_nhds hx.1] with w hw using P.right_inv hw
      intro w
      have := congr_arg (fun T => T w) (h1.unique h2)
      simpa using this
    rw [hGd.fderiv, hG x hx.1]
    ext u
    simp only [LinearMap.mem_range, Submodule.mem_iInf, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
    constructor
    · rintro ⟨v, rfl⟩ i
      have := congr_fun (hDg (ι v)) (e.symm (Sum.inr i))
      simpa [D, ι] using this
    · intro hu
      refine ⟨pin u, ?_⟩
      show g' (ι (pin u)) = u
      apply hWinj _ hx.2.2
      rw [hDg]
      funext j
      rcases h : e j with k | i
      · have hs : e.symm (Sum.inl k) = j := e.symm_apply_eq.2 h.symm
        simp [D, ι, pin, h, hs]
      · have h2 : D (g (ι x)) u j = 0 := by
          simp only [D, ContinuousLinearMap.pi_apply, h, Sum.elim_inr]
          exact hu i
        rw [h2]
        simp [ι, h]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PPolyLocalGeneratorsDiff
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Module

noncomputable section

variable {n : ℕ}

def polyDiff (p : Fin n → ℂ) : MvPolynomial (Fin n) ℂ →ₗ[ℂ] (Fin n → ℂ) where
  toFun f j := eval p (pderiv j f)
  map_add' f g := by ext j; simp
  map_smul' c f := by ext j; simp

theorem polyDiff_apply (p : Fin n → ℂ) (f : MvPolynomial (Fin n) ℂ) (j : Fin n) :
    polyDiff p f j = eval p (pderiv j f) := rfl

def dotForm : (Fin n → ℂ) →ₗ[ℂ] Module.Dual ℂ (Fin n → ℂ) :=
  LinearMap.mk₂ ℂ (fun w v => ∑ j, w j * v j)
    (fun w w' v => by simp [add_mul, Finset.sum_add_distrib])
    (fun c w v => by simp [mul_assoc, Finset.mul_sum])
    (fun w v v' => by simp [mul_add, Finset.sum_add_distrib])
    (fun c w v => by simp [mul_left_comm, Finset.mul_sum])

theorem dotForm_apply (w v : Fin n → ℂ) : dotForm w v = ∑ j, w j * v j := rfl

theorem mem_polyTangent_iff (S : Set (MvPolynomial (Fin n) ℂ)) (p v : Fin n → ℂ) :
    v ∈ polyTangent S p ↔ ∀ q ∈ S, dotForm (polyDiff p q) v = 0 := Iff.rfl

theorem polyTangent_eq_of_subset (S T : Set (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ)
    (hST : S ⊆ T) (h : ∀ f ∈ T, polyDiff p f ∈ Submodule.span ℂ (polyDiff p '' S)) :
    polyTangent S p = polyTangent T p := by
  ext v
  rw [mem_polyTangent_iff, mem_polyTangent_iff]
  refine ⟨fun hv f hf => ?_, fun hv f hf => hv f (hST hf)⟩
  have hle : Submodule.span ℂ (polyDiff p '' S) ≤ LinearMap.ker (dotForm.flip v) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, hg, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.flip_apply]
    exact hv g hg
  have := hle (h f hf)
  simpa only [LinearMap.mem_ker, LinearMap.flip_apply] using this

def tanLinPoly (p w : Fin n → ℂ) : MvPolynomial (Fin n) ℂ := ∑ j, C (w j) * (X j - C (p j))

theorem eval_tanLinPoly (p w : Fin n → ℂ) : eval p (tanLinPoly p w) = 0 := by
  simp [tanLinPoly]

theorem tanLinPoly_add (p w w' : Fin n → ℂ) : tanLinPoly p (w + w') = tanLinPoly p w + tanLinPoly p w' := by
  simp only [tanLinPoly, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem tanLinPoly_smul (p w : Fin n → ℂ) (c : ℂ) : tanLinPoly p (c • w) = C c * tanLinPoly p w := by
  simp only [tanLinPoly, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]

theorem tanLinPoly_zero (p : Fin n → ℂ) : tanLinPoly p 0 = 0 := by
  simp [tanLinPoly]

theorem tanLinPoly_single (p : Fin n → ℂ) (i : Fin n) :
    tanLinPoly p (Pi.single i 1) = X i - C (p i) := by
  classical
  simp only [tanLinPoly, Pi.single_apply]
  simp

theorem polyDiff_tanLinPoly (p w : Fin n → ℂ) : polyDiff p (tanLinPoly p w) = w := by
  classical
  ext i
  simp [polyDiff_apply, tanLinPoly, Pi.single_apply]

theorem X_sub_C_mem_ker (p : Fin n → ℂ) (j : Fin n) :
    X j - C (p j) ∈ RingHom.ker (eval p) := by
  simp [RingHom.mem_ker]

theorem sub_tanLinPoly_mem_sq (p : Fin n → ℂ) (f : MvPolynomial (Fin n) ℂ) :
    f - C (eval p f) - tanLinPoly p (polyDiff p f) ∈ RingHom.ker (eval p) ^ 2 := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a =>
    have h : polyDiff p (C a) = 0 := by ext j; simp [polyDiff_apply]
    simp [h, tanLinPoly_zero]
  | add f g hf hg =>
    have e : f + g - C (eval p (f + g)) - tanLinPoly p (polyDiff p (f + g)) =
        (f - C (eval p f) - tanLinPoly p (polyDiff p f)) +
          (g - C (eval p g) - tanLinPoly p (polyDiff p g)) := by
      rw [map_add, map_add, map_add, tanLinPoly_add]; ring
    rw [e]
    exact add_mem hf hg
  | mul_X f i hf =>
    have hd : polyDiff p (f * X i) = p i • polyDiff p f + eval p f • Pi.single i 1 := by
      ext j
      simp only [polyDiff_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Derivation.leibniz,
        pderiv_X, map_add]
      by_cases hij : i = j
      · subst hij
        simp only [Pi.single_eq_same, mul_one, map_mul, eval_X]
        ring
      · simp only [Pi.single_eq_of_ne hij, Pi.single_eq_of_ne (Ne.symm hij), mul_zero, map_zero,
          map_mul, eval_X, zero_add, add_zero]
    have e : f * X i - C (eval p (f * X i)) - tanLinPoly p (polyDiff p (f * X i)) =
        C (p i) * (f - C (eval p f) - tanLinPoly p (polyDiff p f)) +
          (f - C (eval p f)) * (X i - C (p i)) := by
      rw [hd, tanLinPoly_add, tanLinPoly_smul, tanLinPoly_smul, tanLinPoly_single, map_mul, eval_X, map_mul]
      ring
    rw [e]
    refine add_mem (Ideal.mul_mem_left _ _ hf) ?_
    rw [pow_two]
    refine Ideal.mul_mem_mul ?_ (X_sub_C_mem_ker p i)
    simp [RingHom.mem_ker]

theorem mem_sq_of_polyDiff_eq_zero (p : Fin n → ℂ) {f : MvPolynomial (Fin n) ℂ}
    (h0 : eval p f = 0) (h1 : polyDiff p f = 0) : f ∈ RingHom.ker (eval p) ^ 2 := by
  simpa [h0, h1, tanLinPoly_zero] using sub_tanLinPoly_mem_sq p f

theorem mem_span_sup_sq_of_polyDiff_mem (p : Fin n → ℂ) {ι : Type*} [Fintype ι]
    (h : ι → MvPolynomial (Fin n) ℂ) (hh : ∀ i, eval p (h i) = 0) {f : MvPolynomial (Fin n) ℂ}
    (hf : eval p f = 0) (hd : polyDiff p f ∈ Submodule.span ℂ (Set.range (polyDiff p ∘ h))) :
    f ∈ Ideal.span (Set.range h) ⊔ RingHom.ker (eval p) ^ 2 := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hd
  have hg0 : eval p (f - ∑ i, C (c i) * h i) = 0 := by simp [hf, hh]
  have hg1 : polyDiff p (f - ∑ i, C (c i) * h i) = 0 := by
    simp only [map_sub, map_sum, C_mul', map_smul]
    rw [← hc]
    simp
  have hsum : ∑ i, C (c i) * h i ∈ Ideal.span (Set.range h) :=
    sum_mem fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  have e : f = (f - ∑ i, C (c i) * h i) + ∑ i, C (c i) * h i := by ring
  rw [e]
  exact add_mem (Ideal.mem_sup_right (mem_sq_of_polyDiff_eq_zero p hg0 hg1))
    (Ideal.mem_sup_left hsum)

theorem maximalIdeal_le_span_of_le_sup_sq {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (T : Set R)
    (h : IsLocalRing.maximalIdeal R ≤ Ideal.span T ⊔ IsLocalRing.maximalIdeal R ^ 2) :
    IsLocalRing.maximalIdeal R ≤ Ideal.span T := by
  apply Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _)
    (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  rwa [Ideal.smul_eq_mul, ← pow_two]

theorem exists_polyDiff_basis (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ) :
    ∃ q : Fin (n - finrank ℂ (polyTangent (J : Set (MvPolynomial (Fin n) ℂ)) p)) →
        MvPolynomial (Fin n) ℂ,
      (∀ i, q i ∈ J) ∧ LinearIndependent ℂ (polyDiff p ∘ q) ∧
        ∀ f ∈ J, polyDiff p f ∈ Submodule.span ℂ (Set.range (polyDiff p ∘ q)) := by
  set D : Submodule ℂ (Fin n → ℂ) := (J.restrictScalars ℂ).map (polyDiff p) with hDdef
  have hinj : Function.Injective (dotForm : (Fin n → ℂ) →ₗ[ℂ] Module.Dual ℂ (Fin n → ℂ)) := by
    intro w w' hww
    ext j
    have := LinearMap.congr_fun hww (Pi.single j 1)
    classical
    simpa [dotForm_apply, Pi.single_apply] using this
  set W := D.map (dotForm : (Fin n → ℂ) →ₗ[ℂ] Module.Dual ℂ (Fin n → ℂ))
  have hW : finrank ℂ W = finrank ℂ D :=
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj D)).symm
  have hco : W.dualCoannihilator = polyTangent (J : Set (MvPolynomial (Fin n) ℂ)) p := by
    ext v
    rw [Submodule.mem_dualCoannihilator, mem_polyTangent_iff]
    constructor
    · intro h q hq
      exact h _ (Submodule.mem_map_of_mem (Submodule.mem_map_of_mem (p := J.restrictScalars ℂ) hq))
    · rintro h _ ⟨w, ⟨q, hq, rfl⟩, rfl⟩
      exact h q hq
  have hsum := Subspace.finrank_add_finrank_dualCoannihilator_eq W
  rw [hco, hW, Module.finrank_fin_fun] at hsum
  have hD : finrank ℂ D = n - finrank ℂ (polyTangent (J : Set (MvPolynomial (Fin n) ℂ)) p) := by
    omega
  let b := Module.finBasisOfFinrankEq ℂ D hD
  have hb : ∀ i, ∃ q ∈ J, polyDiff p q = (b i : Fin n → ℂ) := by
    intro i
    obtain ⟨q, hq, e⟩ := Submodule.mem_map.1 (b i).2
    exact ⟨q, hq, e⟩
  choose q hqJ hq using hb
  have hcomp : polyDiff p ∘ q = D.subtype ∘ b := funext hq
  refine ⟨q, hqJ, ?_, ?_⟩
  · rw [hcomp]
    exact b.linearIndependent.map' D.subtype (Submodule.ker_subtype D)
  · intro f hf
    have hspan : Submodule.span ℂ (Set.range (polyDiff p ∘ q)) = D := by
      rw [hcomp, Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
    rw [hspan]
    exact Submodule.mem_map_of_mem (p := J.restrictScalars ℂ) hf

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChowDegreeSection
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial

def ChowDegreeSection.Statement : Prop :=
  ∀ (F : Type) [Field F] [PerfectField F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F)) (u : Fin n → F),
    IsProjPrime I → ringKrullDim (MvPolynomial (Fin n) F ⧸ I) = ((e + 2 : ℕ) : WithBot ℕ∞) →
      linForm u ∉ I →
        chowDegree I (e + 2) = (divCycle I u).sum fun W m => m * chowDegree W (e + 1)

end ObjectsChow

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChowFormBirationalAlgClosed
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def ChowFormBirationalAlgClosed.Statement : Prop :=
  ∀ (F : Type) [Field F] [IsAlgClosed F] (n k : ℕ) (P : Ideal (MvPolynomial (Fin n) F))
    (g : MvPolynomial (Fin (k + 1) × Fin n) F) (c : Fin n → FractionRing (MvPolynomial (Fin n) F ⧸ P)),
    IsProjPrime P → IsChowForm P (k + 1) g → ∑ j, c j * genPt P j = 1 →
      ∃ t : Fin n → F, (∑ l, C (t l) * pderiv (0, l) g) ∉ incIdeal P (k + 1) ∧
        ∀ m, aeval (genSubst (genPt P) c) (pderiv (0, m) g) *
              C (∑ l, algebraMap F (FractionRing (MvPolynomial (Fin n) F ⧸ P)) (t l) * genPt P l) =
            aeval (genSubst (genPt P) c) (∑ l, C (t l) * pderiv (0, l) g) * C (genPt P m)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChowFormSectionAlgClosed
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

def ChowFormSectionAlgClosed.Statement : Prop :=
  ∀ (F : Type) [Field F] [IsAlgClosed F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (u : Fin n → F),
    IsProjPrime I → IsChowForm I (e + 1) f → linForm u ∉ I →
      IsChowFormCycle (divCycle I u) e (specFirst f u)

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsProjChowNonzero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def ProjChowNonzero.Statement : Prop :=
  ∀ (n e : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)) (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ)
    (A : Matrix (Fin (e + 1)) (Fin n) ℂ),
    IsProjPrime W → IsChowForm W (e + 1) f → ComplexSets.IsFiniteProjection W A →
      eval (fun j => projPar A (.inr j))
        (Vertical.specRest (algebraMap ℂ (FractionRing (MvPolynomial (Fin (e + 1)) ℂ))) f (projPar A)) ≠ 0

end

end GroundTheory.Heights₂.Heights
end

