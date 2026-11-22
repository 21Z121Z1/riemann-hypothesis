import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0025
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSerreConditions
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0021
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0020

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.DetEqZeroOfMulVecEqZero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Matrix

noncomputable section

def analyticAtSubring {σ : Type} [Fintype σ] (p : σ → ℂ) : Subring ((σ → ℂ) → ℂ) where
  carrier := {g | AnalyticAt ℂ g p}
  mul_mem' ha hb := AnalyticAt.mul ha hb
  one_mem' := analyticAt_const
  add_mem' ha hb := AnalyticAt.add ha hb
  zero_mem' := analyticAt_const
  neg_mem' ha := AnalyticAt.neg ha

theorem mem_analyticAtSubring {σ : Type} [Fintype σ] {p : σ → ℂ} {g : (σ → ℂ) → ℂ} :
    g ∈ analyticAtSubring p ↔ AnalyticAt ℂ g p :=
  Iff.rfl

def analyticAtComp {σ τ : Type} [Fintype σ] [Fintype τ] (x : σ → ℂ) (L : (σ → ℂ) →L[ℂ] (τ → ℂ)) :
    analyticAtSubring (L x) →+* analyticAtSubring x where
  toFun g := ⟨fun z => (g : (τ → ℂ) → ℂ) (L z), AnalyticAt.comp g.2 (L.analyticAt x)⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem analyticAtComp_apply {σ τ : Type} [Fintype σ] [Fintype τ] (x : σ → ℂ)
    (L : (σ → ℂ) →L[ℂ] (τ → ℂ)) (g : analyticAtSubring (L x)) (z : σ → ℂ) :
    (analyticAtComp x L g : (σ → ℂ) → ℂ) z = (g : (τ → ℂ) → ℂ) (L z) :=
  rfl

def analyticAtEval {σ : Type} [Fintype σ] (p y : σ → ℂ) : analyticAtSubring p →+* ℂ :=
  (Pi.evalRingHom (fun _ : σ → ℂ => ℂ) y).comp (analyticAtSubring p).subtype

@[simp] theorem analyticAtEval_apply {σ : Type} [Fintype σ] (p y : σ → ℂ) (g : analyticAtSubring p) :
    analyticAtEval p y g = (g : (σ → ℂ) → ℂ) y :=
  rfl

def analyticAtGerm {σ : Type} [Fintype σ] (p : σ → ℂ) : analyticAtSubring p →+* holGerms p :=
  ((Germ.coeRingHom (𝓝 p)).comp (analyticAtSubring p).subtype).codRestrict (holGerms p)
    fun g => ⟨g, g.2, rfl⟩

theorem analyticAtGerm_eq_iff {σ : Type} [Fintype σ] {p : σ → ℂ} (a b : analyticAtSubring p) :
    analyticAtGerm p a = analyticAtGerm p b ↔ (a : (σ → ℂ) → ℂ) =ᶠ[𝓝 p] b := by
  rw [Subtype.ext_iff]
  exact Germ.coe_eq

theorem analyticAtGerm_surjective {σ : Type} [Fintype σ] (p : σ → ℂ) :
    Function.Surjective (analyticAtGerm p) := by
  rintro ⟨φ, g, hg, rfl⟩
  exact ⟨⟨g, hg⟩, rfl⟩

theorem det_eq_zero_of_mulVec_eq_zero {Q : Type*} [CommRing Q] {n : ℕ} (A : Matrix (Fin n) (Fin n) Q)
    (e β : Fin n → Q) (hA : A *ᵥ e = 0) (h1 : ∑ m, β m * e m = 1) : A.det = 0 := by
  have he : (A.adjugate * A) *ᵥ e = 0 := by
    rw [← Matrix.mulVec_mulVec, hA, Matrix.mulVec_zero]
  rw [Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec] at he
  calc A.det = A.det * ∑ m, β m * e m := by rw [h1, mul_one]
    _ = ∑ m, β m * (A.det * e m) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => by ring
    _ = 0 := Finset.sum_eq_zero fun m _ => by
      have := congrFun he m
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
      rw [this, mul_zero]

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Imports
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def SerreNormalOfRegularDepth.Statement : Prop :=
  ∀ (A : Type) [CommRing A], IsNoetherianRing A → SerreR A 1 → SerreS A 2 → NormalRing A

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PAreaLinear
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Module

noncomputable section

theorem AreaLinear.sqrt_det_adjoint_comp_eq_normDet {k m : ℕ}
    (L : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) :
    √(LinearMap.det (LinearMap.adjoint L ∘ₗ L)) = L.normDet := by
  rw [← LinearMap.normDet_sq L]
  push_cast
  exact Real.sqrt_sq (LinearMap.normDet_nonneg L)

theorem AreaLinear.proof : AreaLinear.Statement := by
  intro k m L _ A
  have h := LinearMap.hausdorffMeasure_image L A
  rw [finrank_euclideanSpace_fin] at h
  rw [h, AreaLinear.sqrt_det_adjoint_comp_eq_normDet]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCauchyBinetMinors
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Finset

namespace CauchyBinetMinorsAlt

theorem det_one_add_eq_sum {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n R) :
    (1 + X).det = ∑ s : Finset n, (X.submatrix ((↑) : s → n) ((↑) : s → n)).det := by
  rw [add_comm]
  change detRowAlternating (fun i => X i + (1 : Matrix n n R) i) = _
  rw [show (fun i => X i + (1 : Matrix n n R) i) =
      (fun i => X i) + (fun i => (1 : Matrix n n R) i) from rfl, AlternatingMap.map_add_univ]
  refine Finset.sum_congr rfl fun s _ => ?_
  exact det_piecewise_one_eq_submatrix_det X s

theorem minor_reindex {R : Type*} [CommRing R] {n k : ℕ} (X : Matrix (Fin n) (Fin n) R)
    (s : Finset (Fin n)) (hk : s.card = k) :
    (X.submatrix ((↑) : s → Fin n) ((↑) : s → Fin n)).det =
      (X.submatrix (s.orderEmbOfFin hk) (s.orderEmbOfFin hk)).det := by
  rw [← det_submatrix_equiv_self (s.orderIsoOfFin hk).toEquiv]
  congr 1

theorem sum_finset_by_card {n : ℕ} {β : Type*} [AddCommMonoid β] (f : Finset (Fin n) → β) :
    ∑ s : Finset (Fin n), f s =
      ∑ k ∈ range (n + 1), ∑ S : {S : Finset (Fin n) // S.card = k}, f S.1 := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := Finset.card) (t := range (n + 1)) (fun s _ => by
    have := card_le_univ s
    simp only [Fintype.card_fin] at this
    exact mem_range.2 (by omega))]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact Finset.sum_subtype _ (fun s => by simp) _

theorem sum_strictMono {n k : ℕ} {β : Type*} [AddCommMonoid β]
    [DecidablePred (fun b : Fin k → Fin n => StrictMono b)] (g : (Fin k → Fin n) → β) :
    ∑ b ∈ univ.filter (fun b : Fin k → Fin n => StrictMono b), g b =
      ∑ S : {S : Finset (Fin n) // S.card = k}, g (S.1.orderEmbOfFin S.2) := by
  symm
  refine Finset.sum_bij (fun S _ => (S.1.orderEmbOfFin S.2 : Fin k → Fin n)) ?_ ?_ ?_ ?_
  · intro S _
    simpa using (S.1.orderEmbOfFin S.2).strictMono
  · intro S _ T _ h
    apply Subtype.ext
    have h' := congrArg Set.range h
    simp only [range_orderEmbOfFin] at h'
    exact_mod_cast h'
  · intro b hb
    simp only [mem_filter, mem_univ, true_and] at hb
    have hc : (univ.image b).card = k := by
      rw [card_image_of_injective _ hb.injective, card_univ, Fintype.card_fin]
    exact ⟨⟨univ.image b, hc⟩, mem_univ _,
      (orderEmbOfFin_unique hc (fun x => mem_image_of_mem b (mem_univ x)) hb).symm⟩
  · intro _ _
    rfl

theorem principal_minor {p q k : ℕ} (M : Matrix (Fin p) (Fin q) ℂ)
    (S : {S : Finset (Fin q) // S.card = k}) :
    ((Mᴴ * M).submatrix (S.1.orderEmbOfFin S.2) (S.1.orderEmbOfFin S.2)).det =
      ∑ T : {T : Finset (Fin p) // T.card = k},
        ((‖(M.submatrix (T.1.orderEmbOfFin T.2) (S.1.orderEmbOfFin S.2)).det‖ ^ 2 : ℝ) : ℂ) := by
  rw [Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, CauchyBinet.proof]
  refine Finset.sum_congr rfl fun T _ => ?_
  have h1 : colsOf (Mᴴ.submatrix (S.1.orderEmbOfFin S.2) id) T =
      (M.submatrix (T.1.orderEmbOfFin T.2) (S.1.orderEmbOfFin S.2))ᴴ := by
    ext i j
    simp [colsOf, conjTranspose_apply]
  have h2 : rowsOf (M.submatrix id (S.1.orderEmbOfFin S.2)) T =
      M.submatrix (T.1.orderEmbOfFin T.2) (S.1.orderEmbOfFin S.2) := by
    ext i j
    simp [rowsOf]
  rw [h1, h2, det_conjTranspose, Complex.star_def, Complex.conj_mul']
  push_cast
  rfl

end CauchyBinetMinorsAlt

open CauchyBinetMinorsAlt in

theorem CauchyBinetMinors.proof : CauchyBinetMinors.Statement := by
  intro p q M
  let G : (k : ℕ) → {T : Finset (Fin p) // T.card = k} → {S : Finset (Fin q) // S.card = k} → ℂ :=
    fun k T S => ((‖(M.submatrix (T.1.orderEmbOfFin T.2) (S.1.orderEmbOfFin S.2)).det‖ ^ 2 : ℝ) : ℂ)
  have hL : (1 + Mᴴ * M).det = ∑ k ∈ range (p + q + 1), ∑ T, ∑ S, G k T S := by
    rw [det_one_add_eq_sum, sum_finset_by_card]
    have hk : ∀ k, ∑ S : {S : Finset (Fin q) // S.card = k},
        ((Mᴴ * M).submatrix ((↑) : S.1 → Fin q) ((↑) : S.1 → Fin q)).det = ∑ T, ∑ S, G k T S := by
      intro k
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun S _ => ?_
      rw [minor_reindex _ S.1 S.2, principal_minor]
    simp only [hk]
    have hsub : range (q + 1) ⊆ range (p + q + 1) := range_subset_range.2 (by omega)
    exact Finset.sum_subset hsub (f := fun k => ∑ T, ∑ S, G k T S) (fun k _ hk => by
      have : IsEmpty {S : Finset (Fin q) // S.card = k} := ⟨fun S => by
        have := card_le_univ S.1
        rw [Fintype.card_fin, S.2] at this
        simp only [mem_range] at hk
        omega⟩
      exact Finset.sum_eq_zero fun T _ => Fintype.sum_empty _)
  have hR : ((∑ k ∈ range (p + 1),
        ∑ a ∈ univ.filter (fun a : Fin k → Fin p => StrictMono a),
          ∑ b ∈ univ.filter (fun b : Fin k → Fin q => StrictMono b),
            ‖(M.submatrix a b).det‖ ^ 2 : ℝ) : ℂ) =
      ∑ k ∈ range (p + q + 1), ∑ T, ∑ S, G k T S := by
    simp only [Complex.ofReal_sum]
    have hk : ∀ k, (∑ a ∈ univ.filter (fun a : Fin k → Fin p => StrictMono a),
          ∑ b ∈ univ.filter (fun b : Fin k → Fin q => StrictMono b),
            ((‖(M.submatrix a b).det‖ ^ 2 : ℝ) : ℂ)) = ∑ T, ∑ S, G k T S := by
      intro k
      rw [sum_strictMono]
      refine Finset.sum_congr rfl fun T _ => ?_
      rw [sum_strictMono]
    simp only [hk]
    have hsub : range (p + 1) ⊆ range (p + q + 1) := range_subset_range.2 (by omega)
    exact Finset.sum_subset hsub (f := fun k => ∑ T, ∑ S, G k T S) (fun k _ hk => by
      have : IsEmpty {T : Finset (Fin p) // T.card = k} := ⟨fun T => by
        have := card_le_univ T.1
        rw [Fintype.card_fin, T.2] at this
        simp only [mem_range] at hk
        omega⟩
      exact Fintype.sum_empty _)
  rw [hL, hR]

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PComplexJacobian
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

theorem realForm_mul {p q r : ℕ} (A : Matrix (Fin p) (Fin q) ℂ) (B : Matrix (Fin q) (Fin r) ℂ) :
    realForm (A * B) = realForm A * realForm B := by
  ext ⟨i, a⟩ ⟨k, c⟩
  simp only [realForm, Matrix.mul_apply, Matrix.of_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    Complex.re_sum, Complex.im_sum]
  fin_cases a <;> fin_cases c <;>
    simp only [Complex.mul_re, Complex.mul_im, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_neg_distrib, Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons] <;>
    refine Finset.sum_congr rfl fun j _ => by ring

theorem realForm_add {p q : ℕ} (A B : Matrix (Fin p) (Fin q) ℂ) :
    realForm (A + B) = realForm A + realForm B := by
  ext ⟨i, a⟩ ⟨k, c⟩
  fin_cases a <;> fin_cases c <;> simp [realForm] <;> ring

theorem realForm_one {q : ℕ} : realForm (1 : Matrix (Fin q) (Fin q) ℂ) = 1 := by
  ext ⟨i, a⟩ ⟨k, c⟩
  by_cases h : i = k <;> fin_cases a <;> fin_cases c <;> simp [realForm, Matrix.one_apply, h]

theorem realForm_conjTranspose {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℂ) :
    realForm Aᴴ = (realForm A)ᵀ := by
  ext ⟨i, a⟩ ⟨k, c⟩
  fin_cases a <;> fin_cases c <;> simp [realForm]

theorem det_realForm {q : ℕ} (A : Matrix (Fin q) (Fin q) ℂ) :
    (realForm A).det = Complex.normSq A.det := by
  let B : Module.Basis (Fin q × Fin 2) ℝ (Fin q → ℂ) :=
    Complex.basisOneI.smulTower' (Pi.basisFun ℂ (Fin q))
  have hM : LinearMap.toMatrix B B ((Matrix.toLin' A).restrictScalars ℝ) = realForm A := by
    ext ⟨i, a⟩ ⟨j, b⟩
    rw [LinearMap.toMatrix_apply]
    simp only [B, Module.Basis.smulTower'_repr_mk, Module.Basis.smulTower'_apply,
      LinearMap.restrictScalars_apply, Pi.basisFun_repr, Pi.basisFun_apply]
    fin_cases a <;> fin_cases b <;>
      simp [realForm, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [← hM, LinearMap.det_toMatrix, LinearMap.det_restrictScalars, LinearMap.det_toLin',
    Algebra.norm_complex_apply]

theorem ComplexJacobian.proof : ComplexJacobian.Statement := by
  intro p q M
  have hR : 1 + (realForm M)ᵀ * realForm M = realForm (1 + Mᴴ * M) := by
    rw [realForm_add, realForm_one, realForm_mul, realForm_conjTranspose]
  set z := (1 + Mᴴ * M).det with hz
  have hstar : star z = z := by
    rw [hz, ← Matrix.det_conjTranspose, Matrix.conjTranspose_add, Matrix.conjTranspose_one,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have him : z.im = 0 := by
    have := congrArg Complex.im hstar
    simp only [Complex.star_def, Complex.conj_im] at this
    linarith
  rw [hR, det_realForm, Complex.normSq_apply, him]
  apply Complex.ext <;> simp [sq, him, ← hz]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDiscrAdjoin
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open Polynomial

theorem DiscrAdjoin.proof : DiscrAdjoin.Statement := by
  intro R K L _ _ _ _ _ _ _ _ _ _ _ _ ℓ hℓ hadj
  have hK : IsIntegral K ℓ := Algebra.IsIntegral.isIntegral ℓ
  have hFK : minpoly K ℓ = (minpoly R ℓ).map (algebraMap R K) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' K hℓ
  have hFm : (minpoly R ℓ).Monic := minpoly.monic hℓ
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hdegK : (minpoly K ℓ).natDegree = (minpoly R ℓ).natDegree := by
    rw [hFK, natDegree_map_eq_of_injective hinj]
  have hdeg : (minpoly R ℓ).natDegree = Module.finrank K L := by
    have h1 := IntermediateField.adjoin.finrank hK
    rw [hadj, IntermediateField.finrank_top', hdegK] at h1
    exact h1.symm
  have hpos : 0 < (minpoly R ℓ).natDegree := minpoly.natDegree_pos hℓ
  have hF'deg : (derivative (minpoly R ℓ)).natDegree ≤ (minpoly R ℓ).natDegree - 1 :=
    natDegree_derivative_le _
  have hres := resultant_deriv (f := minpoly R ℓ) (natDegree_pos_iff_degree_pos.mp hpos)
  rw [hFm.leadingCoeff, mul_one] at hres
  have hdisc : (minpoly R ℓ).discr = (-1) ^ ((minpoly R ℓ).natDegree *
      ((minpoly R ℓ).natDegree - 1) / 2) * resultant (minpoly R ℓ) (derivative (minpoly R ℓ))
        (minpoly R ℓ).natDegree ((minpoly R ℓ).natDegree - 1) := by
    rw [hres, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]
  refine ⟨hdeg, ?_, ?_⟩
  · intro h0
    have hR : resultant (minpoly R ℓ) (derivative (minpoly R ℓ)) (minpoly R ℓ).natDegree
        ((minpoly R ℓ).natDegree - 1) = 0 := by rw [hres, h0, mul_zero]
    have hRK := congrArg (algebraMap R K) hR
    rw [← resultant_map_map, map_zero, ← derivative_map, ← hFK, ← hdegK] at hRK
    have hsep : (minpoly K ℓ).Separable := Algebra.IsSeparable.isSeparable K ℓ
    have hle : (derivative (minpoly K ℓ)).natDegree ≤ (minpoly K ℓ).natDegree - 1 :=
      natDegree_derivative_le _
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
    rw [hk, resultant_add_right_deg _ _ _ _ k le_rfl, coeff_natDegree, (minpoly.monic hK).leadingCoeff,
      one_pow, one_mul] at hRK
    exact resultant_ne_zero _ _ hsep hRK
  · intro z hz
    obtain ⟨p, q, -, -, hpq⟩ := exists_mul_add_mul_eq_C_resultant (minpoly R ℓ)
      (derivative (minpoly R ℓ)) le_rfl hF'deg (Or.inl hpos.ne')
    have hev := congrArg (aeval ℓ) hpq
    simp only [map_add, map_mul, minpoly.aeval, zero_mul, zero_add, aeval_C] at hev
    have hadjK : Algebra.adjoin K {ℓ} = ⊤ := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hK.isAlgebraic, hadj,
        IntermediateField.top_toSubalgebra]
    have hzmem : z ∈ (Algebra.traceForm K L).dualSubmodule
        (Subalgebra.toSubmodule (Algebra.adjoin R {ℓ})) := by
      rw [LinearMap.BilinForm.mem_dualSubmodule]
      intro y hy
      rw [Submodule.mem_one]
      have hyint : IsIntegral R y := adjoin_le_integralClosure hℓ hy
      have htr : IsIntegral R (Algebra.trace K L (z * y)) := Algebra.isIntegral_trace (hz.mul hyint)
      obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.mp htr
      exact ⟨r, by simpa [Algebra.traceForm_apply] using hr⟩
    rw [traceForm_dualSubmodule_adjoin R K hadjK hℓ] at hzmem
    obtain ⟨w, hw, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hzmem
    have hd : aeval ℓ (derivative (minpoly K ℓ)) = aeval ℓ (derivative (minpoly R ℓ)) := by
      rw [hFK, derivative_map, aeval_map_algebraMap]
    rw [hd]
    have hq : aeval ℓ q ∈ Algebra.adjoin R {ℓ} := aeval_mem_adjoin_singleton R ℓ
    have hw' : w ∈ Algebra.adjoin R {ℓ} := hw
    have key : (minpoly R ℓ).discr • ((aeval ℓ (derivative (minpoly R ℓ)))⁻¹ • w) =
        ((-1 : L) ^ ((minpoly R ℓ).natDegree * ((minpoly R ℓ).natDegree - 1) / 2) * aeval ℓ q * w) *
          (aeval ℓ (derivative (minpoly R ℓ)) * (aeval ℓ (derivative (minpoly R ℓ)))⁻¹) := by
      rw [hdisc, Algebra.smul_def, smul_eq_mul, map_mul, ← hev, map_pow, map_neg, map_one]
      ring
    rw [key]
    by_cases hd0 : aeval ℓ (derivative (minpoly R ℓ)) = 0
    · rw [hd0, zero_mul, mul_zero]
      exact zero_mem _
    · rw [mul_inv_cancel₀ hd0, mul_one]
      exact mul_mem (mul_mem (pow_mem (neg_mem (one_mem _)) _) hq) hw'

end GroundTheory.Heights₂.Heights.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDiscriminantCover
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

theorem DiscriminantCover.proof (hP : PrimitiveElementFibres.Statement) :
    DiscriminantCover.Statement := by
  intro n d J A hJ hdim hA
  obtain ⟨c, m, Δ, Q, hmon, hdeg, hΔ, hgood⟩ := hP n d J A hJ hdim hA
  set ℓ : (Fin n → ℂ) → ℂ := fun x => ∑ j, c j * x j with hℓ

  have hdet : ∀ w, eval w Δ ≠ 0 → ∀ x ∈ fibre J A w,
      x = fun j => ((Q j).map (eval w)).eval (ℓ x) / eval w Δ := by
    intro w hw x hx
    funext j
    rw [eq_div_iff hw, mul_comm]
    exact ((hgood w hw).2.1 x hx).2 j
  refine ⟨Δ, hΔ, fun y hy => ?_⟩
  obtain ⟨hsep, hfib, hsurj⟩ := hgood y hy
  have hm0 : m.map (eval y) ≠ 0 := (hmon.map _).ne_zero
  have hinj : Set.InjOn ℓ (fibre J A y) := fun x hx x' hx' h => by
    rw [hdet y hy x hx, hdet y hy x' hx', h]
  have himg : ℓ '' fibre J A y = ↑(m.map (eval y)).roots.toFinset := by
    ext τ
    simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hm0]
    exact ⟨fun ⟨x, hx, hτ⟩ => hτ ▸ (hfib x hx).1, fun h => hsurj τ h⟩
  have hfin : (fibre J A y).Finite :=
    Set.Finite.of_finite_image (by rw [himg]; exact Finset.finite_toSet _) hinj
  refine ⟨hfin, ?_, fun x hx => ?_⟩
  · rw [← hinj.ncard_image, himg, Set.ncard_coe_finset,
      Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hsep),
      IsAlgClosed.card_roots_eq_natDegree, hmon.natDegree_map, hdeg]

  have hroot : (m.map (eval y)).IsRoot (ℓ x) := (hfib x hx).1
  have hder : (m.map (eval y)).derivative.eval (ℓ x) ≠ 0 := by
    have := hsep.aeval_derivative_ne_zero (x := ℓ x) (by simpa [Polynomial.aeval_def] using hroot)
    simpa [Polynomial.aeval_def] using this
  obtain ⟨U₀, B, ψ, hU₀o, hyU₀, hBo, hτB, hψd, hψy, hψ⟩ := SimpleRootBranch.proof d m y (ℓ x) hroot hder
  set U : Set (Fin d → ℂ) := U₀ ∩ {w | eval w Δ ≠ 0} with hU
  have hUo : IsOpen U := hU₀o.inter (isOpen_ne_fun (MvPolynomial.continuous_eval Δ) continuous_const)
  set g : (Fin d → ℂ) → (Fin n → ℂ) :=
    fun w j => ((Q j).map (eval w)).eval (ψ w) / eval w Δ with hg

  have hkey : ∀ w ∈ U, g w ∈ fibre J A w ∧ ℓ (g w) = ψ w := by
    intro w hw
    have hr : (m.map (eval w)).IsRoot (ψ w) := ((hψ w hw.1).2 (ψ w) (hψ w hw.1).1).mpr rfl
    obtain ⟨x', hx', hℓx'⟩ := (hgood w hw.2).2.2 (ψ w) hr
    have hℓx'' : ℓ x' = ψ w := hℓx'
    have he : x' = g w := by rw [hdet w hw.2 x' hx']; simp only [hg]; rw [hℓx'']
    exact ⟨he ▸ hx', he ▸ hℓx'⟩
  have hℓc : Continuous ℓ := by simp only [hℓ]; fun_prop
  have hAc : Continuous fun z : Fin n → ℂ => A.mulVec z := continuous_const.matrix_mulVec continuous_id
  refine ⟨U, {z | A.mulVec z ∈ U ∧ ℓ z ∈ B}, g, hUo, ⟨hyU₀, hy⟩,
    (hUo.preimage hAc).inter (hBo.preimage hℓc), ⟨by rw [hx.2]; exact ⟨hyU₀, hy⟩, hτB⟩,
    fun w hw => ?_, ?_, fun w hw => (hkey w hw).1.2, ?_⟩
  ·
    have hψw : DifferentiableAt ℂ ψ w := (hψd w hw.1).differentiableAt (hU₀o.mem_nhds hw.1)
    refine DifferentiableAt.differentiableWithinAt (differentiableAt_pi.2 fun j => ?_)
    have hΔd : DifferentiableAt ℂ (fun w => eval w Δ) w :=
      (AnalyticOnNhd.eval_mvPolynomial Δ w trivial).differentiableAt
    have hF : DifferentiableAt ℂ (fun v : (Fin d → ℂ) × ℂ => ((Q j).map (eval v.1)).eval v.2) (w, ψ w) :=
      (analyticAt_eval_map (Q j) (w, ψ w)).differentiableAt
    have hQd : DifferentiableAt ℂ (fun w => ((Q j).map (eval w)).eval (ψ w)) w :=
      DifferentiableAt.comp (g := fun v : (Fin d → ℂ) × ℂ => ((Q j).map (eval v.1)).eval v.2)
        (f := fun v => (v, ψ v)) w hF (differentiableAt_fun_id.prodMk hψw)
    have hfun : (fun w => g w j) = fun w => ((Q j).map (eval w)).eval (ψ w) * (eval w Δ)⁻¹ := by
      funext v; simp only [hg, div_eq_mul_inv]
    rw [hfun]
    exact hQd.mul (hΔd.inv hw.2)
  · funext j
    rw [congrFun (hdet y hy x hx) j]
    simp only [hg, hψy]
  · ext z
    constructor
    · rintro ⟨hz, hzU, hzB⟩
      have hzf : z ∈ fibre J A (A.mulVec z) := ⟨hz, rfl⟩
      have hr := ((hgood _ hzU.2).2.1 z hzf).1
      have hℓz : ℓ z = ψ (A.mulVec z) := ((hψ _ hzU.1).2 (ℓ z) hzB).mp hr
      refine ⟨A.mulVec z, hzU, ?_⟩
      funext j
      rw [congrFun (hdet _ hzU.2 z hzf) j]
      simp only [hg]
      rw [hℓz]
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨hf, hℓg⟩ := hkey w hw
      exact ⟨hf.1, by rw [hf.2]; exact hw, by rw [hℓg]; exact (hψ w hw.1).1⟩

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StHolGermsIntegrallyClosed
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def HolGermsIntegrallyClosed.Statement : Prop :=
  ∀ (d : ℕ) (y : Fin d → ℂ), IsDomain (holGerms y) ∧ IsIntegrallyClosed (holGerms y)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

