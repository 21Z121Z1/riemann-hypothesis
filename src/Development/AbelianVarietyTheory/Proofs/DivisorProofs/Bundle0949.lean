import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
import Development.AbelianVarietyTheory.Definitions.Divisors.IrreducibleOfIrreducibleMap
import ReciprocityTheory.SemistableReduction.Bundle0025
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0901
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0928
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0863
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PtCoeffSingleSubst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.TangentEqLcZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0926
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0903

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinSubstLinSubst
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField GlobalTheory.ChowHt GlobalTheory.Adelic MvPolynomial ReciprocityTheory.MultiplicativeHeights

namespace GlobalTheory.HeightUnique

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial in
set_option autoImplicit false in

theorem _root_.GlobalTheory.HeightUnique.linSubst_linSubst {R : Type} [CommRing R] {B N n m : ℕ} (M : Matrix (Fin N) (Fin n) R)
    (P : Matrix (Fin n) (Fin m) R) (f : MvPolynomial (Fin B × Fin N) R) :
    _root_.GlobalTheory.ChowHt.linSubst P (_root_.GlobalTheory.ChowHt.linSubst M f) = _root_.GlobalTheory.ChowHt.linSubst (M * P) f := by
  unfold _root_.GlobalTheory.ChowHt.linSubst
  rw [← AlgHom.comp_apply]
  congr 1
  apply MvPolynomial.algHom_ext
  intro p
  simp only [AlgHom.comp_apply, aeval_X, map_sum, map_mul, aeval_C, algebraMap_eq, Matrix.mul_apply,
    Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial in
set_option autoImplicit false in

theorem _root_.GlobalTheory.HeightUnique.linSubst_one {R : Type} [CommRing R] {B N : ℕ} (f : MvPolynomial (Fin B × Fin N) R) :
    _root_.GlobalTheory.ChowHt.linSubst (1 : Matrix (Fin N) (Fin N) R) f = f := by
  unfold _root_.GlobalTheory.ChowHt.linSubst
  have hX : (fun p : Fin B × Fin N => ∑ k, C ((1 : Matrix (Fin N) (Fin N) R) p.2 k) * X (p.1, k)) = X := by
    funext p
    simp [Matrix.one_apply, apply_ite C, ite_mul]
  rw [hX, aeval_X_left_apply]

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial in
set_option autoImplicit false in

theorem _root_.GlobalTheory.HeightUnique.linSubst_ne_zero {R : Type} [CommRing R] {B N n : ℕ} {M : Matrix (Fin N) (Fin n) R}
    {P : Matrix (Fin n) (Fin N) R} (h : M * P = 1) {f : MvPolynomial (Fin B × Fin N) R} (hf : f ≠ 0) :
    _root_.GlobalTheory.ChowHt.linSubst M f ≠ 0 := by
  intro h0
  apply hf
  have key := _root_.GlobalTheory.HeightUnique.linSubst_linSubst M P f
  rw [h0, h, _root_.GlobalTheory.HeightUnique.linSubst_one] at key
  rw [← key]
  simp [_root_.GlobalTheory.ChowHt.linSubst]

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial in
set_option autoImplicit false in

theorem _root_.GlobalTheory.HeightUnique.linSubst_C_mul {R : Type} [CommRing R] {B N n : ℕ} (M : Matrix (Fin N) (Fin n) R) (c : R)
    (f : MvPolynomial (Fin B × Fin N) R) :
    _root_.GlobalTheory.ChowHt.linSubst M (C c * f) = C c * _root_.GlobalTheory.ChowHt.linSubst M f := by
  simp [_root_.GlobalTheory.ChowHt.linSubst]

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial in
set_option autoImplicit false in

theorem _root_.GlobalTheory.HeightUnique.exists_right_inv {F : Type} [Field F] {N n : ℕ} {w : Matrix (Fin N) (Fin n) F}
    (hw : Submodule.span F (Set.range w.col) = ⊤) : ∃ P : Matrix (Fin n) (Fin N) F, w * P = 1 := by
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective w.mulVecLin
    (by rw [Matrix.range_mulVecLin, hw])
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have key := congrArg LinearMap.toMatrix' hg
  have hw' : LinearMap.toMatrix' w.mulVecLin = w := (LinearEquiv.eq_symm_apply LinearMap.toMatrix').mp rfl
  rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id, hw'] at key

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial in
set_option autoImplicit false in
private lemma isWeightedHomogeneous_aeval_of_isWeightedHomogeneous {R M σ τ : Type*} [CommSemiring R] [AddCommMonoid M]
    {w : σ → M} {w' : τ → M} {g : σ → MvPolynomial τ R} (hg : ∀ i, IsWeightedHomogeneous w' (g i) (w i))
    {f : MvPolynomial σ R} {m : M} (hf : IsWeightedHomogeneous w f m) :
    IsWeightedHomogeneous w' (aeval g f) m := by
  rw [f.as_sum, map_sum]
  apply IsWeightedHomogeneous.sum
  intro d hd
  rw [aeval_monomial, algebraMap_eq, ← hf (mem_support_iff.mp hd), Finsupp.weight_apply,
    ← zero_add (d.sum fun i c => c • w i)]
  exact (isWeightedHomogeneous_C w' _).mul
    (IsWeightedHomogeneous.prod _ _ _ fun i _ => (hg i).pow (d i))

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial in
set_option autoImplicit false in

theorem _root_.GlobalTheory.HeightUnique.linSubst_homog {R : Type} [Field R] {B N n : ℕ} (M : Matrix (Fin N) (Fin n) R)
    {a : Fin B → ℕ} {f : MvPolynomial (Fin B × Fin N) R} (hf : _root_.ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous a f) :
    _root_.ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous a (_root_.GlobalTheory.ChowHt.linSubst M f) := by
  rw [_root_.GlobalTheory.ChowHt.isMultiHomogeneous_iff_block] at hf ⊢
  unfold _root_.GlobalTheory.Chow.IsBlockHomogeneous at hf ⊢
  unfold _root_.GlobalTheory.ChowHt.linSubst
  refine isWeightedHomogeneous_aeval_of_isWeightedHomogeneous (fun p => ?_) hf
  apply IsWeightedHomogeneous.sum
  intro k _
  have hw : _root_.GlobalTheory.Chow.blockWeight p = _root_.GlobalTheory.Chow.blockWeight ((p.1, k) : Fin B × Fin n) := by
    simp [_root_.GlobalTheory.Chow.blockWeight]
  rw [hw, ← zero_add (_root_.GlobalTheory.Chow.blockWeight ((p.1, k) : Fin B × Fin n))]
  exact (isWeightedHomogeneous_C _ _).mul (isWeightedHomogeneous_X _ _ _)

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial in
set_option autoImplicit false in

theorem _root_.GlobalTheory.HeightUnique.gaussAbs_C {K σ : Type} [Field K] [NumberField K] (w : FinitePlace K) (c : K) :
    _root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs w (C c : MvPolynomial σ K) = w c := by
  classical
  unfold _root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs
  by_cases hc : c = 0
  · subst hc
    simp
  · rw [C_apply, support_monomial, if_neg hc]
    simp [Real.coe_toNNReal _ (apply_nonneg w c)]

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial in
set_option autoImplicit false in
private lemma gaussAbs_C_mul_of_ne_zero {K σ : Type} [Field K] [NumberField K] (w : FinitePlace K) {c : K}
    (hc : c ≠ 0) (g : MvPolynomial σ K) : _root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs w (C c * g) = w c * _root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs w g := by
  unfold _root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs
  have hs : (C c * g).support = g.support := by
    ext s
    simp [coeff_C_mul, hc]
  rw [hs]
  simp_rw [coeff_C_mul, map_mul, Real.toNNReal_mul (apply_nonneg w c)]
  rw [← NNReal.mul_finset_sup, NNReal.coe_mul, Real.coe_toNNReal _ (apply_nonneg w c)]

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial in
set_option autoImplicit false in
private lemma gaussAbs_pos_of_ne_zero {K σ : Type} [Field K] [NumberField K] (w : FinitePlace K)
    {g : MvPolynomial σ K} (hg : g ≠ 0) : 0 < _root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs w g := by
  obtain ⟨s, hs⟩ := exists_coeff_ne_zero hg
  unfold _root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs
  have h1 : (w (coeff s g)).toNNReal ≤ g.support.sup fun t => (w (coeff t g)).toNNReal :=
    Finset.le_sup (f := fun t => (w (coeff t g)).toNNReal) (mem_support_iff.mpr hs)
  have h2 : 0 < w (coeff s g) := w.pos_iff.mpr hs
  exact_mod_cast lt_of_lt_of_le (Real.toNNReal_pos.mpr h2) h1

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial in
set_option autoImplicit false in
private lemma finsum_log_finitePlace_add_sum_log_norm_embedding {K : Type} [Field K] [NumberField K] {c : K}
    (hc : c ≠ 0) : ∑ᶠ v : FinitePlace K, Real.log (v c) + ∑ σ : K →+* ℂ, Real.log ‖σ c‖ = 0 := by
  rw [_root_.ReciprocityTheory.MultiplicativeHeights.sum_log_norm_embedding_eq c hc, ← Real.log_finprod (fun v => v.pos_iff.mpr hc), FinitePlace.prod_eq_inv_abs_norm hc]
  push_cast
  rw [Real.log_inv]
  ring

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial in
set_option autoImplicit false in

theorem _root_.GlobalTheory.HeightUnique.formHeight_C_mul {F : Type} [Field F] [NumberField F] {B N n : ℕ} (hN : 0 < N) (δ : ℕ)
    {w : Matrix (Fin N) (Fin n) F} (hw : Submodule.span F (Set.range w.col) = ⊤)
    {A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ} (hA : ∀ σ, (A σ).det ≠ 0) {a : Fin B → ℕ}
    {f : MvPolynomial (Fin B × Fin N) F} (hf : f ≠ 0) (ha : _root_.ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous a f) {c : F} (hc : c ≠ 0) :
    _root_.GlobalTheory.ChowHt.formHeight δ w A (C c * f) = _root_.GlobalTheory.ChowHt.formHeight δ w A f := by
  obtain ⟨P, hP⟩ := _root_.GlobalTheory.HeightUnique.exists_right_inv hw
  have hLf : _root_.GlobalTheory.ChowHt.linSubst w f ≠ 0 := _root_.GlobalTheory.HeightUnique.linSubst_ne_zero hP hf
  have hfin : ∀ v : FinitePlace F, Real.log (_root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs v (_root_.GlobalTheory.ChowHt.linSubst w (C c * f))) =
      Real.log (v c) + Real.log (_root_.ReciprocityTheory.MultiplicativeHeights.gaussAbs v (_root_.GlobalTheory.ChowHt.linSubst w f)) := by
    intro v
    rw [_root_.GlobalTheory.HeightUnique.linSubst_C_mul, gaussAbs_C_mul_of_ne_zero v hc,
      Real.log_mul (v.pos_iff.mpr hc).ne' (gaussAbs_pos_of_ne_zero v hLf).ne']
  have harch : ∀ σ : F →+* ℂ, _root_.ReciprocityTheory.MultiplicativeHeights.blockSphereMean B N (_root_.GlobalTheory.ChowHt.linSubst (A σ) (map σ (C c * f))) =
      Real.log ‖σ c‖ + _root_.ReciprocityTheory.MultiplicativeHeights.blockSphereMean B N (_root_.GlobalTheory.ChowHt.linSubst (A σ) (map σ f)) := by
    intro σ
    have hQ : A σ * (A σ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hA σ))
    have hmf : map σ f ≠ 0 := fun h0 => hf (map_injective σ σ.injective (by rw [h0, map_zero]))
    have hg := _root_.GlobalTheory.HeightUnique.linSubst_ne_zero hQ hmf
    have hgh := _root_.GlobalTheory.HeightUnique.linSubst_homog (A σ) (_root_.ReciprocityTheory.MultiplicativeHeights.isMultiHomogeneous_map_ring a f ha σ)
    have hσc : σ c ≠ 0 := (map_ne_zero σ).mpr hc
    have hC : (C (σ c) : MvPolynomial (Fin B × Fin N) ℂ) ≠ 0 := by simpa using hσc
    have hCh : _root_.ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => 0) (C (σ c) : MvPolynomial (Fin B × Fin N) ℂ) :=
      (_root_.ReciprocityTheory.MultiplicativeHeights.isMultiHomogeneous_iff_forall_weighted_lh0BlockWt _ _).mpr fun _ => isWeightedHomogeneous_C _ _
    rw [map_mul, map_C, _root_.GlobalTheory.HeightUnique.linSubst_C_mul,
      _root_.ReciprocityTheory.MultiplicativeHeights.sphere_mean_mul_multihomogeneous _root_.ReciprocityTheory.MultiplicativeHeights.Closed.sphereLogIntegrable B N (fun _ => 0) a _ _ hC hg hCh hgh]
    congr 1
    haveI := _root_.ReciprocityTheory.MultiplicativeHeights.blockSphereMeasure_isProbability (B := B) hN
    unfold _root_.ReciprocityTheory.MultiplicativeHeights.blockSphereMean
    simp [eval_C]
  have hsuppc : (Function.support fun v : FinitePlace F => Real.log (v c)).Finite := by
    simpa [_root_.GlobalTheory.HeightUnique.gaussAbs_C] using _root_.ReciprocityTheory.MultiplicativeHeights.gauss_abs_log_support_finite (C c : MvPolynomial Unit F) (by simpa using hc)
  unfold _root_.GlobalTheory.ChowHt.formHeight
  congr 1
  simp_rw [hfin, harch]
  rw [finsum_add_distrib hsuppc (_root_.ReciprocityTheory.MultiplicativeHeights.gauss_abs_log_support_finite _ hLf)]
  simp only [Finset.sum_add_distrib]
  linarith [finsum_log_finitePlace_add_sum_log_norm_embedding hc]

end GlobalTheory.HeightUnique
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCutOperatorTransferAdelicWhittaker
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

noncomputable section

namespace GlobalTheory.JSW.CutTransfer

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem proj_finGL_locGL (w : HeightOneSpectrum (𝓞 E)) (g : GL (Fin n) (w.adicCompletion E)) :
    GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) (finGL E n (locGL E n w g)) = g := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h1 := congrArg (fun z => (GeneralLinearGroup.map (pLoc E w) z).val i j) (pFin_finGL (E := E) (locGL E n w g))
  simp only [pLoc_locGL] at h1
  exact h1

theorem gl_ext_pLoc {x y : GL (Fin n) (Af E)}
    (h : ∀ v, GeneralLinearGroup.map (pLoc E v) x = GeneralLinearGroup.map (pLoc E v) y) : x = y :=
  Units.ext (Matrix.ext fun i k => IsDedekindDomain.FiniteAdeleRing.ext _ fun v =>
    congrArg (fun x : GL (Fin n) (v.adicCompletion E) => x.val i k) (h v))

variable [IsTotallyComplex E]

theorem comm_of_proj_eq_one (w : HeightOneSpectrum (𝓞 E)) {x : GA E n}
    (hx : GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) x = 1) (g : GL (Fin n) (w.adicCompletion E)) :
    x * finGL E n (locGL E n w g) = finGL E n (locGL E n w g) * x := by
  have hxw : GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) x) = 1 := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    exact congrArg (fun z : GL (Fin n) (w.adicCompletion E) => z.val i j) hx
  refine ga_ext ?_ ?_
  · simp only [map_mul, pInf_finGL, mul_one, one_mul]
  · simp only [map_mul, pFin_finGL]
    refine gl_ext_pLoc fun v => ?_
    simp only [map_mul]
    by_cases hv : v = w
    · subst hv
      rw [hxw, one_mul, mul_one]
    · rw [pLoc_locGL_of_ne hv, one_mul, mul_one]

theorem superDiag_finGL_locGL (w : HeightOneSpectrum (𝓞 E)) (u : GL (Fin n) (w.adicCompletion E)) :
    GlobalTheory.Whittaker.superDiag (finGL E n (locGL E n w u)) = sFin E (sLoc E w (GlobalTheory.Whittaker.superDiag u)) := by
  unfold GlobalTheory.Whittaker.superDiag
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hij : i ≠ j := by
    intro h
    subst h
    simp at hj
  change (1 : Matrix (Fin n) (Fin n) (Ad E)) i j - sFin E ((1 : Matrix (Fin n) (Fin n) (Af E)) i j) +
    sFin E ((1 : Matrix (Fin n) (Fin n) (Af E)) i j - sLoc E w ((1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) +
      sLoc E w ((u : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j)) = _
  simp [Matrix.one_apply_ne hij]

theorem psiN_finGL_locGL (w : HeightOneSpectrum (𝓞 E)) (u : GL (Fin n) (w.adicCompletion E)) :
    psiN (finGL E n (locGL E n w u)) = psiLoc w (GlobalTheory.Whittaker.superDiag u) := by
  unfold psiN psiLoc
  rw [superDiag_finGL_locGL]

theorem finGL_locGL_mem_NA' (w : HeightOneSpectrum (𝓞 E)) {u : GL (Fin n) (w.adicCompletion E)}
    (hu : u ∈ GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin n)) : finGL E n (locGL E n w u) ∈ NA E n := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB _).1 hu
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · change (1 : Matrix (Fin n) (Fin n) (Ad E)) i j - sFin E ((1 : Matrix (Fin n) (Fin n) (Af E)) i j) +
      sFin E ((1 : Matrix (Fin n) (Fin n) (Af E)) i j - sLoc E w ((1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) +
        sLoc E w ((u : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j)) = 0
    simp [Matrix.one_apply_ne hij.ne', h1 i j hij]
  · change (1 : Matrix (Fin n) (Fin n) (Ad E)) i i - sFin E ((1 : Matrix (Fin n) (Fin n) (Af E)) i i) +
      sFin E ((1 : Matrix (Fin n) (Fin n) (Af E)) i i - sLoc E w ((1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i i) +
        sLoc E w ((u : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i i)) = 1
    simp [h2 i]

end GlobalTheory.JSW.CutTransfer

namespace GlobalTheory.JSW.CutTransfer

theorem transfer : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (w : HeightOneSpectrum (𝓞 E)) (ψ : AddChar (w.adicCompletion E) ℂ), (∀ x, ψ x = GlobalTheory.JSW.psiLoc w x) → ∀ (K : Subgroup (GL (Fin (m + 1)) (Af E))) (U : Subgroup (GL (Fin (m + 1)) (w.adicCompletion E))), (∀ u ∈ U, locGL E (m + 1) w u ∈ K) → ∀ X A : Set (GL (Fin (m + 1)) (w.adicCompletion E)), GlobalTheory.JSW.Cut.Cuts ψ (U : Set (GL (Fin (m + 1)) (w.adicCompletion E))) X A → ∃ T : GA E (m + 1) →₀ ℂ, (∀ k ∈ T.support, ∃ g, k = finGL E (m + 1) (locGL E (m + 1) w g)) ∧ ∀ W : GA E (m + 1) → ℂ, (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) → (∀ u ∈ K, ∀ g, W (g * finGL E (m + 1) u) = W g) → ∀ y : GA E (m + 1), GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) y ∈ A → GlobalTheory.JSW.Cut.act T W y = {x : GA E (m + 1) | GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) x ∈ X}.indicator W y := by
  intro E _ _ _ m w ψ hψ K U hU X A hcut
  classical
  obtain ⟨T₀, hT₀⟩ := hcut
  let Φ : GL (Fin (m + 1)) (w.adicCompletion E) →* GA E (m + 1) := (finGL E (m + 1)).comp (locGL E (m + 1) w)
  have hΦ : ∀ g, Φ g = finGL E (m + 1) (locGL E (m + 1) w g) := fun _ => rfl
  refine ⟨T₀.mapDomain Φ, ?_, ?_⟩
  · intro k hk
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hk)
    exact ⟨g, rfl⟩
  · intro W hN hK y hy
    set yw := GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) y with hyw
    set x := y * (Φ yw)⁻¹ with hxdef
    have hx : GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) x = 1 := by
      rw [hxdef, map_mul, map_inv, hΦ, proj_finGL_locGL, ← hyw, mul_inv_cancel]
    have hcomm : ∀ g, x * Φ g = Φ g * x := fun g => comm_of_proj_eq_one w hx g
    have hxy : ∀ g, x * Φ (yw * g) = y * Φ g := by
      intro g
      rw [map_mul, hxdef, mul_assoc, ← mul_assoc (Φ yw)⁻¹, inv_mul_cancel, one_mul]
    let f : GL (Fin (m + 1)) (w.adicCompletion E) → ℂ := fun g => W (x * Φ g)
    have hf1 : GlobalTheory.JSW.KirFin.Eqv ψ f := by
      intro u hu g
      show W (x * Φ (u * g)) = ψ (GlobalTheory.Whittaker.superDiag u) * W (x * Φ g)
      rw [map_mul, ← mul_assoc, hcomm u, mul_assoc, hΦ u, hN _ (finGL_locGL_mem_NA' w hu), psiN_finGL_locGL, hψ]
    have hf2 : ∀ u ∈ (U : Set (GL (Fin (m + 1)) (w.adicCompletion E))), ∀ g, f (g * u) = f g := by
      intro u hu g
      show W (x * Φ (g * u)) = W (x * Φ g)
      rw [map_mul, ← mul_assoc, hΦ u, hK _ (hU u hu)]
    have key := hT₀ f hf1 hf2 yw hy
    have hact : GlobalTheory.JSW.Cut.act (T₀.mapDomain Φ) W y = GlobalTheory.JSW.Cut.act T₀ f yw := by
      unfold GlobalTheory.JSW.Cut.act
      rw [Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
      refine Finset.sum_congr rfl fun k _ => ?_
      show _ * W (y * Φ k) = _ * W (x * Φ (yw * k))
      rw [hxy]
    rw [hact, key]
    by_cases h : yw ∈ X
    · have h' : y ∈ {z : GA E (m + 1) | GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) z ∈ X} := h
      rw [Set.indicator_of_mem h, Set.indicator_of_mem h']
      show W (x * Φ yw) = W y
      rw [hxdef, mul_assoc, inv_mul_cancel, mul_one]
    · have h' : y ∉ {z : GA E (m + 1) | GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) z ∈ X} := h
      rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h']

end GlobalTheory.JSW.CutTransfer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogIntegralUnitsSubgroupExpHomProof
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoTriv

open MvPowerSeries ReciprocityTheory.PGsh

section Unit

variable {C : Type} [Field C] [CharZero C] {σ : Type}

theorem expU_add (s t : MvPowerSeries σ C) (hs : constantCoeff s = 0) (ht : constantCoeff t = 0) :
    PowerSeries.subst (s + t) (PowerSeries.exp C) =
      PowerSeries.subst s (PowerSeries.exp C) * PowerSeries.subst t (PowerSeries.exp C) := by
  have hst : MvPowerSeries.HasSubst ![s, t] :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (by intro i; fin_cases i <;> simp [hs, ht])
  have comp : ∀ p : MvPowerSeries (Fin 2) C, constantCoeff p = 0 →
      MvPowerSeries.subst ![s, t] (PowerSeries.subst p (PowerSeries.exp C)) =
        PowerSeries.subst (MvPowerSeries.subst ![s, t] p) (PowerSeries.exp C) := by
    intro p hp
    unfold PowerSeries.subst
    rw [MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero hp).const hst]
  have H := congrArg (MvPowerSeries.subst ![s, t]) (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_subst_add_two_vars C)
  rw [MvPowerSeries.subst_mul hst, comp _ (by simp), comp _ (by simp), comp _ (by simp),
    MvPowerSeries.subst_add hst, MvPowerSeries.subst_X hst, MvPowerSeries.subst_X hst] at H
  simpa using H

theorem cc_expU (s : MvPowerSeries σ C) (hs : constantCoeff s = 0) :
    constantCoeff (PowerSeries.subst s (PowerSeries.exp C)) = 1 := by
  rw [PowerSeries.constantCoeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hs), finsum_eq_single _ 0]
  · simp
  · intro e he
    simp [map_pow, hs, zero_pow he]

theorem expU_zero : PowerSeries.subst (0 : MvPowerSeries σ C) (PowerSeries.exp C) = 1 := by
  have h := expU_add (0 : MvPowerSeries σ C) 0 (by simp) (by simp)
  rw [add_zero] at h
  have hu : IsUnit (PowerSeries.subst (0 : MvPowerSeries σ C) (PowerSeries.exp C)) := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff, cc_expU _ (by simp)]
    exact isUnit_one
  exact hu.mul_left_cancel (by rw [mul_one]; exact h.symm)

omit [CharZero C] in
theorem inv_int (v : AddValuation C (WithTop ℝ)) (U : MvPowerSeries σ C) (hU : MvIsInt v U)
    (h1 : constantCoeff U = 1) : ∃ U', MvIsInt v U' ∧ U * U' = 1 := by
  set S := ReciprocityTheory.ChartRestriction.G.Sh.PTb.intRing v
  let U' : MvPowerSeries σ S := fun α => ⟨coeff α U, hU α⟩
  have hU' : map S.subtype U' = U := by ext α; rfl
  have hc : constantCoeff U' = ((1 : Sˣ) : S) := by
    apply Subtype.ext
    change coeff 0 U = 1
    rw [coeff_zero_eq_constantCoeff_apply, h1]
  refine ⟨map S.subtype (invOfUnit U' 1), fun α => ?_, ?_⟩
  · rw [coeff_map]; exact (coeff α (invOfUnit U' 1)).2
  · rw [← hU', ← map_mul, mul_invOfUnit U' 1 hc, map_one]

theorem unitSt : UnitSt := by
  intro C _ _ v σ _
  have hexp0 := expU_zero (C := C) (σ := σ)
  refine ⟨⟨by simp, ?_⟩, ?_, ?_, fun s t hs ht => expU_add s t hs ht, fun s hs => cc_expU s hs,
    fun U hU h1 => inv_int v U hU h1⟩
  · rw [hexp0]; exact Subring.one_mem (ReciprocityTheory.ChartRestriction.G.Sh.ptIntSer v σ)
  · rintro s t ⟨hs0, hs⟩ ⟨ht0, ht⟩
    refine ⟨by simp [hs0, ht0], ?_⟩
    rw [expU_add s t hs0 ht0]
    exact Subring.mul_mem (ReciprocityTheory.ChartRestriction.G.Sh.ptIntSer v σ) hs ht
  · rintro s ⟨hs0, hs⟩
    have hn0 : constantCoeff (-s) = 0 := by simp [hs0]
    refine ⟨hn0, ?_⟩
    obtain ⟨U', hU', hm⟩ := inv_int v _ hs (cc_expU s hs0)
    have e : PowerSeries.subst (-s) (PowerSeries.exp C) * PowerSeries.subst s (PowerSeries.exp C) = 1 := by
      rw [← expU_add _ _ hn0 hs0, neg_add_cancel, hexp0]
    have : PowerSeries.subst (-s) (PowerSeries.exp C) = U' := by
      calc PowerSeries.subst (-s) (PowerSeries.exp C)
          = PowerSeries.subst (-s) (PowerSeries.exp C) * (PowerSeries.subst s (PowerSeries.exp C) * U') := by
            rw [hm, mul_one]
        _ = U' := by rw [← mul_assoc, e, one_mul]
    rw [this]; exact hU'

end Unit

end GlobalTheory.IsoTriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogarithmSumIntegralAdditive
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoTriv

open MvPowerSeries ReciprocityTheory.PGsh GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.LawLog

theorem exp_point_zero {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ} (G : LogFGL v d)
    (σ : Type) : expPt G (0 : Fin d → MvPowerSeries σ C) = 0 := by
  funext i
  have h0 : ∀ j, constantCoeff ((0 : Fin d → MvPowerSeries σ C) j) = 0 := fun _ => by simp
  have hs : HasSubst (0 : Fin d → MvPowerSeries σ C) := hasSubst_of_constantCoeff_zero h0
  ext e
  simp only [expPt, Pi.zero_apply]
  rw [coeff_subst hs, map_zero]
  apply finsum_eq_zero_of_forall_eq_zero
  intro m
  by_cases hm : m = 0
  · subst hm
    simp [coeff_zero_eq_constantCoeff_apply, (isExp_expOf G).1 i]
  · obtain ⟨s, hsm⟩ : ∃ s, m s ≠ 0 := by
      by_contra hc; push_neg at hc; exact hm (Finsupp.ext hc)
    have : (m.prod fun s n => ((0 : Fin d → MvPowerSeries σ C) s) ^ n) = 0 := by
      rw [Finsupp.prod]
      apply Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hsm)
      simp [zero_pow hsm]
    rw [this, map_zero, smul_zero]

theorem log_sum_additive_preserves_integrality : AddSt := by
  intro C _ v d G σ _
  have hadd : ∀ w w' : Fin d → MvPowerSeries σ C, (∀ i, constantCoeff (w i) = 0) →
      (∀ i, constantCoeff (w' i) = 0) →
      expPt G (w + w') = fun i => subst (Sum.elim (expPt G w) (expPt G w')) (G.F i) := by
    intro w w' hw hw'
    set a : Fin d ⊕ Fin d → MvPowerSeries σ C := Sum.elim (expPt G w) (expPt G w') with ha_def
    have ha0 : ∀ s, constantCoeff (a s) = 0 := by
      rintro (b | b)
      · exact cc_expPt G hw b
      · exact cc_expPt G hw' b
    have ha : HasSubst a := hasSubst_of_constantCoeff_zero ha0
    have hF : HasSubst G.F := hasSubst_of_constantCoeff_zero G.F_const
    set y : Fin d → MvPowerSeries σ C := fun i => subst a (G.F i) with hy_def
    have hy0 : ∀ i, constantCoeff (y i) = 0 := fun i =>
      constantCoeff_subst_eq_zero ha ha0 (G.F_const i)
    have hlg : lgPt G y = w + w' := by
      funext i
      have h1 := subst_comp_subst_apply hF ha (G.lg i)
      have hXl : HasSubst (fun b : Fin d => (X (Sum.inl b) : MvPowerSeries (Fin d ⊕ Fin d) C)) :=
        hasSubst_of_constantCoeff_zero (fun b => by simp)
      have hXr : HasSubst (fun b : Fin d => (X (Sum.inr b) : MvPowerSeries (Fin d ⊕ Fin d) C)) :=
        hasSubst_of_constantCoeff_zero (fun b => by simp)
      rw [G.lg_F, subst_add ha, subst_comp_subst_apply hXl ha, subst_comp_subst_apply hXr ha] at h1
      have hl : (fun s : Fin d => subst a (X (Sum.inl s) : MvPowerSeries (Fin d ⊕ Fin d) C)) = expPt G w := by
        funext s; rw [subst_X ha]; rfl
      have hr : (fun s : Fin d => subst a (X (Sum.inr s) : MvPowerSeries (Fin d ⊕ Fin d) C)) = expPt G w' := by
        funext s; rw [subst_X ha]; rfl
      rw [hl, hr] at h1
      have e1 : subst (expPt G w) (G.lg i) = w i := by
        have := congrFun (lgPt_expPt G hw) i; exact this
      have e2 : subst (expPt G w') (G.lg i) = w' i := by
        have := congrFun (lgPt_expPt G hw') i; exact this
      show subst y (G.lg i) = w i + w' i
      rw [hy_def, ← h1, e1, e2]
    rw [← hlg, expPt_lgPt G hy0]
  refine ⟨⟨fun i => by simp, fun i => ?_⟩, hadd, ?_⟩
  · rw [exp_point_zero G σ]; intro α; simp [IsIntV]
  · intro w w' hw hw'
    refine ⟨fun i => by simp [hw.1 i, hw'.1 i], fun i => ?_⟩
    rw [hadd w w' hw.1 hw'.1]
    refine ReciprocityTheory.ChartRestriction.G.Sh.PTb.mvIsInt_subst v (G.F_int i) ?_ ?_
    · rintro (b | b)
      · exact hw.2 b
      · exact hw'.2 b
    · rintro (b | b)
      · exact cc_expPt G hw.1 b
      · exact cc_expPt G hw'.1 b

end GlobalTheory.IsoTriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetricScalarPoincareWeightEqTwoMulPotentialStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst GlobalTheory.ScalarPoin MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.metric_scalarPoincareWeight_eq_two_mul_potential : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ (k : ℕ) (z : ReciprocityTheory.L2DbarEstimates.V (nd X)), z ∈ OmF X x0 → phla X (laS X k) (cpt X x0 z) = 2 * (k : ℝ) * rhF X x0 z := by
  first | exact @GlobalTheory.ScalarPoin.phla_laS_cpt | exact GlobalTheory.ScalarPoin.phla_laS_cpt | (intros; apply GlobalTheory.ScalarPoin.phla_laS_cpt <;> assumption)
end

