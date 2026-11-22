import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0057
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0009
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0003

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjoinRootEquivMk
section
noncomputable section

namespace GlobalTheory.LKCent

section Equiv

variable {F : Type} [Field F] {B : Type} [Ring B] [Algebra F B]

def gen (γ : B) : Algebra.adjoin F ({γ} : Set B) := ⟨γ, Algebra.self_mem_adjoin_singleton F γ⟩

theorem aeval_gen (γ : B) (p : Polynomial F) :
    ((Polynomial.aeval (gen (F := F) γ) p : Algebra.adjoin F ({γ} : Set B)) : B) = Polynomial.aeval γ p :=
  Polynomial.aeval_subalgebra_coe p _ _

def adjoinRootEquiv (γ : B) : AdjoinRoot (minpoly F γ) ≃ₐ[F] Algebra.adjoin F ({γ} : Set B) :=
  AlgEquiv.ofBijective (AdjoinRoot.liftAlgHom (minpoly F γ) (Algebra.ofId F _) (gen γ) (by
      show Polynomial.aeval (gen γ) (minpoly F γ) = 0
      apply Subtype.ext
      rw [aeval_gen, minpoly.aeval]
      rfl)) (by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro a ha
      induction a using AdjoinRoot.induction_on with
      | ih p =>
        rw [AdjoinRoot.liftAlgHom_mk] at ha
        have h0 : Polynomial.aeval γ p = 0 := by
          have := congrArg Subtype.val ha
          rw [← aeval_gen (F := F) γ p]
          exact this
        exact (AdjoinRoot.mk_eq_zero).2 (minpoly.dvd F γ h0)
    · rintro ⟨y, hy⟩
      rw [Algebra.adjoin_singleton_eq_range_aeval] at hy
      obtain ⟨p, rfl⟩ := hy
      refine ⟨AdjoinRoot.mk _ p, ?_⟩
      rw [AdjoinRoot.liftAlgHom_mk]
      apply Subtype.ext
      exact aeval_gen γ p)

end Equiv

section Star

variable (k : Type) [Field k] {F : Type} [Field F] [Algebra k F] {B : Type} [Ring B] [StarRing B]
  [Algebra F B] [Algebra k B] [IsScalarTower k F B] (γ : B)

def starL (hk : ∀ t : k, star (algebraMap k B t) = algebraMap k B t)
    (hs : ∀ x ∈ Algebra.adjoin F ({γ} : Set B), star x ∈ Algebra.adjoin F ({γ} : Set B)) :
    Algebra.adjoin F ({γ} : Set B) →ₐ[k] Algebra.adjoin F ({γ} : Set B) where
  toFun x := ⟨star (x : B), hs _ x.2⟩
  map_one' := by ext; simp
  map_mul' x y := by
    have h := mul_comm (⟨star (y : B), hs _ y.2⟩ : Algebra.adjoin F ({γ} : Set B)) ⟨star (x : B), hs _ x.2⟩
    ext
    simpa [star_mul] using congrArg Subtype.val h
  map_zero' := by ext; simp
  map_add' x y := by ext; simp
  commutes' t := by
    ext
    simp only [Subalgebra.coe_algebraMap]
    exact hk t

@[simp]
theorem coe_starL (hk : ∀ t : k, star (algebraMap k B t) = algebraMap k B t)
    (hs : ∀ x ∈ Algebra.adjoin F ({γ} : Set B), star x ∈ Algebra.adjoin F ({γ} : Set B))
    (x : Algebra.adjoin F ({γ} : Set B)) : ((starL k γ hk hs x : Algebra.adjoin F ({γ} : Set B)) : B) =
      star (x : B) := rfl

end Star

end GlobalTheory.LKCent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjoinRootMapComplexLinearIndependentStatement
section
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjoinRoot_complex_map_linearIndependent : ∀ (D : ℕ) (P : Polynomial (MvPolynomial (Fin D) ℚ)), P.Monic → ∃ τ : AdjoinRoot P →+* AdjoinRoot (P.map (MvPolynomial.map (algebraMap ℚ ℂ))), (∀ i, τ (AdjoinRoot.of P (MvPolynomial.X i)) = AdjoinRoot.of _ (MvPolynomial.X i)) ∧ (∀ (q : ℚ) u, τ (q • u) = (q : ℂ) • τ u) ∧ ∀ (J : Type) (e : J → AdjoinRoot P), LinearIndependent ℚ e → LinearIndependent ℂ (fun j => τ (e j)) := by
  first | exact @GlobalTheory.adjoinRoot_map_complex_linearIndependent | exact GlobalTheory.adjoinRoot_map_complex_linearIndependent | (intros; apply GlobalTheory.adjoinRoot_map_complex_linearIndependent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjoinRootUniformiserIsDVRStatement
section
open IsLocalRing
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDVR_adjoinRoot_X_pow_sub_C_of_irreducible : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (π : R) (e : ℕ), Irreducible π → 0 < e → ∀ [IsDomain (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π : Polynomial R))], IsDiscreteValuationRing (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π : Polynomial R)) := by
  first | (exact @GlobalTheory.adjoinRoot_uniformiser_isDVR) | (exact GlobalTheory.adjoinRoot_uniformiser_isDVR) | (intros; apply GlobalTheory.adjoinRoot_uniformiser_isDVR  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjoinRootXPowSubUniformizerIsDomainStatement
section
open IsLocalRing
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjoinRoot_X_pow_sub_uniformizer_isDomain : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (π : R) (e : ℕ), Irreducible π → 0 < e → IsDomain (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π : Polynomial R)) := by
  first | (exact @GlobalTheory.adjoinRoot_X_pow_sub_C_uniformizer_isDomain) | (exact GlobalTheory.adjoinRoot_X_pow_sub_C_uniformizer_isDomain) | (intros; apply GlobalTheory.adjoinRoot_X_pow_sub_C_uniformizer_isDomain  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjugateGramSymm
section
namespace GlobalTheory.CasimirOrder

open Matrix

variable {O : Type} [Ring O]

def form (s : O →+ O) (φ : O →+ ℤ) : LinearMap.BilinForm ℤ O :=
  LinearMap.mk₂ ℤ (fun u v => φ (s u * v))
    (fun u₁ u₂ v => by simp [map_add, add_mul])
    (fun c u v => by rw [map_zsmul, smul_mul_assoc, map_zsmul])
    (fun u v₁ v₂ => by simp [mul_add, map_add])
    (fun c u v => by rw [mul_smul_comm, map_zsmul])

@[simp] theorem form_apply (s : O →+ O) (φ : O →+ ℤ) (u v : O) : form s φ u v = φ (s u * v) := rfl

variable {r : ℕ}

def gram (x : Fin r → O) (s : O →+ O) (φ : O →+ ℤ) : Matrix (Fin r) (Fin r) ℤ :=
  Matrix.of fun i j => φ (s (x i) * x j)

def casimir (x : Fin r → O) (s : O →+ O) (φ : O →+ ℤ) : O :=
  ∑ i, ∑ j, (gram x s φ).adjugate i j • (s (x i) * x j)

theorem det_smul_eq_sum (x : Module.Basis (Fin r) ℤ O) (b : LinearMap.BilinForm ℤ O)
    (hb : ∀ u v, b u v = b v u) (v : O) :
    (Matrix.of fun i j => b (x i) (x j)).det • v =
      ∑ i, ∑ j, ((Matrix.of fun i j => b (x i) (x j)).adjugate i j * b (x i) v) • x j := by
  classical
  set G : Matrix (Fin r) (Fin r) ℤ := Matrix.of fun i j => b (x i) (x j) with hG
  have hGt : Gᵀ = G := by ext i j; simp [hG, hb]
  have hA : ∀ i j, G.adjugate i j = G.adjugate j i := by
    intro i j
    have h := congrArg (fun M : Matrix (Fin r) (Fin r) ℤ => M i j) (adjugate_transpose G)
    rw [hGt] at h
    simpa using h.symm
  have hv : v = ∑ k, x.repr v k • x k := (x.sum_repr v).symm
  have hb' : ∀ i, b (x i) v = ∑ k, G i k * x.repr v k := by
    intro i; conv_lhs => rw [hv]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [LinearMap.map_smul, smul_eq_mul, mul_comm]; rfl
  have key : ∀ j, ∑ i, G.adjugate i j * b (x i) v = G.det * x.repr v j := by
    intro j
    have e : ∑ i, G.adjugate i j * b (x i) v = ∑ k, (G.adjugate * G) j k * x.repr v k := by
      simp_rw [hb', Finset.mul_sum, mul_apply, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
      rw [hA]; ring
    rw [e, adjugate_mul]
    simp [Matrix.smul_apply, one_apply]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, key]
  conv_lhs => rw [hv]
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [smul_smul]

open scoped MatrixOrder in

theorem trace_mul_pos_real {n : ℕ} {P H : Matrix (Fin n) (Fin n) ℝ} (hP : P.PosDef) (hH : H.PosSemidef)
    (h0 : H ≠ 0) : 0 < (P * H).trace := by
  obtain ⟨C, hC, rfl⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp hP.isStrictlyPositive
  have e : (star C * C * H).trace = (C * H * Cᴴ).trace := by
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm]; rfl
  have hs := hH.mul_mul_conjTranspose_same C
  rw [e]
  refine hs.trace_nonneg.lt_of_ne fun h => h0 ?_
  have h1 := hs.trace_eq_zero_iff.1 h.symm
  rwa [show Cᴴ = star C from rfl, hC.star.mul_left_eq_zero, hC.mul_right_eq_zero] at h1

theorem posDef_of_int {n : ℕ} (G : Matrix (Fin n) (Fin n) ℤ) (hs : Gᵀ = G)
    (hp : ∀ v : Fin n → ℤ, v ≠ 0 → 0 < v ⬝ᵥ G *ᵥ v) : (G.map (Int.cast : ℤ → ℝ)).PosDef := by
  classical
  have hsym : ∀ y z, Matrix.toBilin' G y z = Matrix.toBilin' G z y := by
    intro y z
    rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply', Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hs,
      dotProduct_comm]
  have hnn : ∀ y, 0 ≤ Matrix.toBilin' G y y := by
    intro y
    by_cases hy : y = 0
    · simp [hy]
    · rw [Matrix.toBilin'_apply']; exact (hp y hy).le
  have hpsd : (G.map (Int.cast : ℤ → ℝ)).PosSemidef := by
    have h := GlobalTheory.gram_posSemidef_of_int_form (Matrix.toBilin' G) hsym hnn (fun u => Pi.single u 1)
    convert h using 1
    ext u v
    simp [Matrix.toBilin'_apply']
  rw [hpsd.posDef_iff_isUnit, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, ← Int.cast_det]
  intro h
  obtain ⟨z, hz, hGz⟩ := Matrix.exists_mulVec_eq_zero_iff.2 (by exact_mod_cast h)
  have h1 := hp z hz
  rw [hGz, dotProduct_zero] at h1
  exact lt_irrefl _ h1

theorem adjugate_posDef {n : ℕ} {P : Matrix (Fin n) (Fin n) ℝ} (hP : P.PosDef) : P.adjugate.PosDef := by
  have hd := hP.det_pos
  have e : P.adjugate = P.det • P⁻¹ := by
    rw [Matrix.inv_def, smul_smul, Ring.inverse_eq_inv', mul_inv_cancel₀ hd.ne', one_smul]
  rw [e]
  exact hP.inv.smul hd

theorem form_symm {s : O →+ O} {φ : O →+ ℤ} (hs : ∀ a b, s (a * b) = s b * s a) (hss : ∀ a, s (s a) = a)
    (hφs : ∀ a, φ (s a) = φ a) (u v : O) : form s φ u v = form s φ v u := by
  simp only [form_apply]
  rw [← hφs (s u * v), hs, hss]

theorem gram_eq (x : Fin r → O) (s : O →+ O) (φ : O →+ ℤ) :
    gram x s φ = Matrix.of fun i j => form s φ (x i) (x j) := rfl

theorem gram_transpose {x : Fin r → O} {s : O →+ O} {φ : O →+ ℤ} (hs : ∀ a b, s (a * b) = s b * s a)
    (hss : ∀ a, s (s a) = a) (hφs : ∀ a, φ (s a) = φ a) : (gram x s φ)ᵀ = gram x s φ := by
  ext i j
  simp only [transpose_apply, gram_eq, of_apply]
  exact form_symm hs hss hφs _ _

theorem adjugate_gram_symm {x : Fin r → O} {s : O →+ O} {φ : O →+ ℤ} (hs : ∀ a b, s (a * b) = s b * s a)
    (hss : ∀ a, s (s a) = a) (hφs : ∀ a, φ (s a) = φ a) (i j : Fin r) :
    (gram x s φ).adjugate i j = (gram x s φ).adjugate j i := by
  have h := congrArg (fun M : Matrix (Fin r) (Fin r) ℤ => M i j) (adjugate_transpose (gram x s φ))
  rw [gram_transpose hs hss hφs] at h
  simpa using h.symm

theorem casimir_star {x : Fin r → O} {s : O →+ O} {φ : O →+ ℤ} (hs : ∀ a b, s (a * b) = s b * s a)
    (hss : ∀ a, s (s a) = a) (hφs : ∀ a, φ (s a) = φ a) : s (casimir x s φ) = casimir x s φ := by
  unfold casimir
  simp only [map_sum, map_zsmul, hs, hss]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    rw [adjugate_gram_symm hs hss hφs]

theorem quad_eq (x : Fin r → O) (b : LinearMap.BilinForm ℤ O) (v : Fin r → ℤ) :
    v ⬝ᵥ (Matrix.of fun i j => b (x i) (x j)) *ᵥ v = b (∑ i, v i • x i) (∑ j, v j • x j) := by
  simp only [dotProduct, mulVec, of_apply, map_sum, LinearMap.sum_apply, LinearMap.map_smul,
    LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem posDef_gram (x : Module.Basis (Fin r) ℤ O) (b : LinearMap.BilinForm ℤ O) (hb : ∀ u v, b u v = b v u)
    (hpos : ∀ w, w ≠ 0 → 0 < b w w) :
    ((Matrix.of fun i j => b (x i) (x j)).map (Int.cast : ℤ → ℝ)).PosDef := by
  refine posDef_of_int _ (by ext i j; simp [hb]) fun v hv => ?_
  rw [quad_eq]
  refine hpos _ fun h => hv ?_
  have := (Fintype.linearIndependent_iff.1 x.linearIndependent) v h
  exact funext this

end GlobalTheory.CasimirOrder
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AeMeasureSmulPreimageFundamentalDomainEq
section
open MeasureTheory
open scoped ENNReal Pointwise

namespace GlobalTheory.CovolIndep

theorem ae_measure_slice_eq (S X : Type) [Group S] [MeasurableSpace S] [MeasurableSpace X]
    [MulAction S X] [MeasurableSMul₂ S X] [MeasurableMul₂ S] [MeasurableInv S] (ν : Measure S)
    [SFinite ν] [ν.IsMulLeftInvariant] (μ : Measure X) [SFinite μ] [SMulInvariantMeasure S X μ]
    (Γ : Subgroup S) [Countable Γ] (D : Set X) (hD : MeasurableSet D)
    (hDf : IsFundamentalDomain Γ D μ) (E : Set S) (hE : IsFundamentalDomain Γ E ν) :
    ∀ᵐ y ∂μ, ν {s | s • y ∈ D} = ν E := by
  set W₀ : Set X := {x | ¬ ∃ g : Γ, g • x ∈ D} with hW₀
  have hW₀0 : μ W₀ = 0 := ae_iff.1 hDf.ae_covers
  have h0 := ae_measure_setOf_smul_mem_eq_zero ν μ hW₀0
  have h1 : ∀ᵐ y ∂μ, ∀ p : Γ × Γ, p.1 ≠ p.2 →
      ν {s | s • y ∈ (p.1 • D ∩ p.2 • D : Set X)} = 0 := by
    rw [ae_all_iff]
    intro p
    by_cases hp : p.1 = p.2
    · exact Filter.Eventually.of_forall fun y h => absurd hp h
    · filter_upwards [ae_measure_setOf_smul_mem_eq_zero ν μ (hDf.aedisjoint hp)] with y hy
      exact fun _ => hy
  filter_upwards [h0, h1] with y hy0 hy1
  have hU : IsFundamentalDomain Γ {s : S | s • y ∈ D} ν := by
    refine ⟨(hD.preimage (measurable_smul_const y)).nullMeasurableSet, ?_, ?_⟩
    · rw [ae_iff]
      refine measure_mono_null (fun s hs => ?_) hy0
      simp only [Set.mem_setOf_eq, not_exists] at hs ⊢
      rintro ⟨g, hg⟩
      refine hs g ?_
      simpa [Subgroup.smul_def, mul_smul] using hg
    · intro a b hab
      have key : ∀ c : Γ, ∀ s : S, s ∈ (c • {s : S | s • y ∈ D} : Set S) ↔ s • y ∈ (c • D : Set X) := by
        intro c s
        rw [Set.mem_smul_set_iff_inv_smul_mem, Set.mem_smul_set_iff_inv_smul_mem]
        simp [Subgroup.smul_def, mul_smul]
      change ν _ = 0
      refine measure_mono_null (fun s hs => ?_) (hy1 (a, b) hab)
      exact ⟨(key a s).1 hs.1, (key b s).1 hs.2⟩
  exact hU.measure_eq hE

end GlobalTheory.CovolIndep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineBaseChangeOverFieldExtensionStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affine_base_change_over_field_extension : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (X X' : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of k)) (f' : X' ⟶ Spec (CommRingCat.of K)) (π : X' ⟶ X), IsPullback π f' f (Spec.map (CommRingCat.ofHom (algebraMap k K))) → ∀ V : X.Opens, IsAffineOpen V → letI : Algebra k Γ(X, V) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appLE ⊤ V le_top).hom.toAlgebra; IsAffineOpen (π ⁻¹ᵁ V) ∧ ∃ e : K ⊗[k] Γ(X, V) ≃+* Γ(X', π ⁻¹ᵁ V), (∀ a, e (1 ⊗ₜ a) = (π.app V).hom a) ∧ ∀ c : K, e (c ⊗ₜ 1) = ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f'.appLE ⊤ (π ⁻¹ᵁ V) le_top).hom c := by
  first | exact @GlobalTheory.isAffineOpen_preimage_and_tensor_equiv_of_isPullback | exact GlobalTheory.isAffineOpen_preimage_and_tensor_equiv_of_isPullback | (intros; apply GlobalTheory.isAffineOpen_preimage_and_tensor_equiv_of_isPullback <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertRepresentingUniversalSubscheme
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace GlobalTheory.HilbAff

variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B]

theorem sigma_inv (r : ℕ) {T : Scheme.{0}} {g₀ g : T ⟶ Spec (CommRingCat.of A)}
    {I₀ : (pullback (str A B) g₀).IdealSheafData} {I : (pullback (str A B) g).IdealSheafData}
    {h₀ : Good A B r g₀ I₀} {h₁ : Good A B r g I}
    (e : (⟨g₀, ⟨I₀, h₀⟩⟩ : Σ g : T ⟶ Spec (CommRingCat.of A),
      {I : (pullback (str A B) g).IdealSheafData // Good A B r g I}) = ⟨g, ⟨I, h₁⟩⟩) :
    ∃ h : g₀ = g, I = I₀.comap
      (pullback.map (str A B) g (str A B) g₀ (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp [h])) := by
  obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.mp e
  refine ⟨rfl, ?_⟩
  have : pullback.map (str A B) g₀ (str A B) g₀ (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp) = 𝟙 _ := by
    ext <;> simp
  rw [this, Scheme.IdealSheafData.comap_id]
  exact (congrArg Subtype.val (eq_of_heq h2)).symm

theorem good_ker (r : ℕ) {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A)) {V : Scheme.{0}}
    (v : V ⟶ pullback (str A B) g) [IsClosedImmersion v] (h1 : IsFinite (v ≫ pullback.snd _ g))
    (h2 : Flat (v ≫ pullback.snd _ g)) (h3 : ∀ y, (v ≫ pullback.snd _ g).finrank y = r) :
    Good A B r g v.ker := by
  let φ := IsClosedImmersion.lift v v.ker.subschemeι (by rw [Scheme.IdealSheafData.ker_subschemeι])
  have hφ : φ ≫ v = v.ker.subschemeι := IsClosedImmersion.lift_fac _ _ _
  haveI : IsIso φ := IsClosedImmersion.isIso_of_ker_eq v.ker.subschemeι v φ hφ
    (Scheme.IdealSheafData.ker_subschemeι _)
  have e : v.ker.subschemeι ≫ pullback.snd _ g = φ ≫ (v ≫ pullback.snd _ g) := by
    rw [← Category.assoc, hφ]
  refine ⟨?_, ?_, fun y => ?_⟩
  · rw [e]; infer_instance
  · rw [e]; infer_instance
  · rw [e, Scheme.Hom.finrank_comp_left_of_isIso, h3]

end GlobalTheory.HilbAff

theorem GlobalTheory.HilbAff.universal : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (r : ℕ) (H : Scheme.{0}) (R : (GlobalTheory.HilbAff.functor A B r).RepresentableBy H), ∃ (U : Scheme.{0}) (u : U ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap A B))) (R.homEquiv (𝟙 H)).1), IsClosedImmersion u ∧ IsFinite (u ≫ pullback.snd _ (R.homEquiv (𝟙 H)).1) ∧ Flat (u ≫ pullback.snd _ (R.homEquiv (𝟙 H)).1) ∧ (∀ y, (u ≫ pullback.snd _ (R.homEquiv (𝟙 H)).1).finrank y = r) ∧ ∀ (T : Scheme.{0}) (g : T ⟶ Spec (CommRingCat.of A)) (V : Scheme.{0}) (v : V ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap A B))) g), IsClosedImmersion v → IsFinite (v ≫ pullback.snd _ g) → Flat (v ≫ pullback.snd _ g) → (∀ y, (v ≫ pullback.snd _ g).finrank y = r) → ∃! f : T ⟶ H, ∃ hf : f ≫ (R.homEquiv (𝟙 H)).1 = g, ∃ w : V ⟶ U, IsPullback v w (pullback.map _ g _ (R.homEquiv (𝟙 H)).1 (𝟙 _) f (𝟙 _) (by simp) (by rw [Category.comp_id, hf])) u := by
  intro A B _ _ _ r H R
  have key : ∀ {T : Scheme.{0}} (f : T ⟶ H), R.homEquiv f =
      ⟨f ≫ (R.homEquiv (𝟙 H)).1, ⟨(R.homEquiv (𝟙 H)).2.1.comap
        (GlobalTheory.HilbAff.bc A B (R.homEquiv (𝟙 H)).1 f), GlobalTheory.HilbAff.good_comap A B r _ f _
          (R.homEquiv (𝟙 H)).2.2⟩⟩ := fun f => by
    have := R.homEquiv_comp f (𝟙 H)
    rw [Category.comp_id] at this
    rw [this]; rfl
  refine ⟨(R.homEquiv (𝟙 H)).2.1.subscheme, (R.homEquiv (𝟙 H)).2.1.subschemeι, inferInstance,
    (R.homEquiv (𝟙 H)).2.2.1, (R.homEquiv (𝟙 H)).2.2.2.1, (R.homEquiv (𝟙 H)).2.2.2.2, ?_⟩
  intro T g V v hv h1 h2 h3
  have hG := GlobalTheory.HilbAff.good_ker A B r g v h1 h2 h3
  let y : (GlobalTheory.HilbAff.functor A B r).obj (op T) := ⟨g, ⟨v.ker, hG⟩⟩

  have cmp : ∀ (f : T ⟶ H) (hf : f ≫ (R.homEquiv (𝟙 H)).1 = g),
      pullback.map (GlobalTheory.HilbAff.str A B) g (GlobalTheory.HilbAff.str A B) (f ≫ (R.homEquiv (𝟙 H)).1)
          (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp [hf]) ≫
        GlobalTheory.HilbAff.bc A B (R.homEquiv (𝟙 H)).1 f =
      pullback.map _ g _ (R.homEquiv (𝟙 H)).1 (𝟙 _) f (𝟙 _) (by simp)
        (by rw [Category.comp_id, hf]) := by
    intro f hf
    apply pullback.hom_ext <;>
      simp only [GlobalTheory.HilbAff.bc, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.id_comp]
  have cmp' : ∀ (f : T ⟶ H) (hf : f ≫ (R.homEquiv (𝟙 H)).1 = g),
      pullback.map (GlobalTheory.HilbAff.str A B) (f ≫ (R.homEquiv (𝟙 H)).1) (GlobalTheory.HilbAff.str A B) g
          (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp [hf]) ≫
        pullback.map _ g _ (R.homEquiv (𝟙 H)).1 (𝟙 _) f (𝟙 _) (by simp)
          (by rw [Category.comp_id, hf]) =
      GlobalTheory.HilbAff.bc A B (R.homEquiv (𝟙 H)).1 f := by
    intro f hf
    apply pullback.hom_ext <;>
      simp only [GlobalTheory.HilbAff.bc, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.id_comp]
  let f := R.homEquiv.symm y
  have hfy : R.homEquiv f = y := Equiv.apply_symm_apply _ _
  rw [key] at hfy
  obtain ⟨hf, hI⟩ := GlobalTheory.HilbAff.sigma_inv A B r hfy
  have hcomap : (R.homEquiv (𝟙 H)).2.1.comap (pullback.map _ g _ (R.homEquiv (𝟙 H)).1 (𝟙 _) f
      (𝟙 _) (by simp) (by rw [Category.comp_id, hf])) = v.ker := by
    rw [hI, ← Scheme.IdealSheafData.comap_comp, cmp f hf]
  refine ⟨f, ⟨hf, ?_⟩, ?_⟩
  · have hle : ((R.homEquiv (𝟙 H)).2.1.subschemeι).ker ≤ (v ≫ pullback.map _ g _
        (R.homEquiv (𝟙 H)).1 (𝟙 _) f (𝟙 _) (by simp) (by rw [Category.comp_id, hf])).ker := by
      rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.Hom.ker_comp,
        Scheme.IdealSheafData.le_map_iff_comap_le, hcomap]
    refine ⟨IsClosedImmersion.lift _ _ hle, ?_⟩
    exact isPullback_of_isClosedImmersion _ _ _ _ (IsClosedImmersion.lift_fac _ _ hle).symm
      (by rw [Scheme.IdealSheafData.ker_subschemeι, hcomap])
  · rintro f' ⟨hf', w', hpb⟩
    have hv : v.ker = (R.homEquiv (𝟙 H)).2.1.comap (pullback.map _ g _ (R.homEquiv (𝟙 H)).1 (𝟙 _)
        f' (𝟙 _) (by simp) (by rw [Category.comp_id, hf'])) := by
      rw [← hpb.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
        Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, Scheme.IdealSheafData.ker_subschemeι]
    have h' : R.homEquiv f' = y := by
      rw [key]
      refine GlobalTheory.HilbAff.sigma_eq A B r hf' ?_ _ _
      rw [hv, ← Scheme.IdealSheafData.comap_comp, cmp' f' hf']
    apply R.homEquiv.injective
    rw [h']
    exact (Equiv.apply_symm_apply R.homEquiv y).symm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineInterFiniteBasicOpenCoverStatement
section
open AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_basicOpen_cover_inf_of_isAffineOpen : ∀ (X : Scheme.{0}), IsNoetherian X → ∀ (W V : X.Opens), IsAffineOpen W → IsAffineOpen V → ∃ s : Finset Γ(X, W), (∀ h ∈ s, ∃ r : Γ(X, V), X.basicOpen h = X.basicOpen r) ∧ ((W ⊓ V : X.Opens) : Set X) ⊆ ⋃ h ∈ s, (X.basicOpen h : Set X) := by
  first | exact @GlobalTheory.affine_inter_finite_basicOpen_cover | exact GlobalTheory.affine_inter_finite_basicOpen_cover | (intros; apply GlobalTheory.affine_inter_finite_basicOpen_cover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineOpenExistsFieldPointBasicOpenCommonDenomAlStatement
section
open AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ringHom_field_common_denom_of_mem_isAffineOpen : ∀ {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (p : X), p ∈ U → ∃ (K : Type) (_ : Field K) (ψ : Γ(X, U) →+* K), (∀ g, ψ g ≠ 0 → p ∈ X.basicOpen g) ∧ ∀ (ι : Type) [Fintype ι] (m : ι → K), ∃ (a : ι → Γ(X, U)) (t : Γ(X, U)), ψ t ≠ 0 ∧ ∀ i, m i * ψ t = ψ (a i) := by
  first | exact @GlobalTheory.affineOpen_exists_field_point_basicOpen_commonDenom | exact GlobalTheory.affineOpen_exists_field_point_basicOpen_commonDenom | (intros; apply GlobalTheory.affineOpen_exists_field_point_basicOpen_commonDenom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineSpaceSmoothNormal
section
open CategoryTheory AlgebraicGeometry

namespace GlobalTheory

theorem smooth_affineSpace_over_of_isAffine (S : Scheme.{0}) [IsAffine S] (ι : Type) [Finite ι] :
    Smooth (𝔸(ι; S) ↘ S) := by
  have e : (𝔸(ι; S) ↘ S) = (AffineSpace.isoOfIsAffine ι S).hom ≫
      Spec.map (CommRingCat.ofHom MvPolynomial.C) ≫ S.isoSpec.inv := by
    rw [← AffineSpace.isoOfIsAffine_inv_over (n := ι) (S := S), Iso.hom_inv_id_assoc]
  rw [e]
  haveI : Algebra.Smooth Γ(S, ⊤) (MvPolynomial ι Γ(S, ⊤)) := ⟨inferInstance, inferInstance⟩
  have : Smooth (Spec.map (CommRingCat.ofHom (MvPolynomial.C (R := Γ(S, ⊤)) (σ := ι)))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
    exact RingHom.smooth_algebraMap.mpr inferInstance
  infer_instance

theorem isIntegrallyClosed_stalk_spec_field (K : Type) [Field K] (x : Spec (.of K)) :
    IsIntegrallyClosed ((Spec (.of K)).presheaf.stalk x) := by
  have hU := isAffineOpen_top (Spec (.of K))
  letI := (Spec (.of K)).presheaf.algebra_section_stalk (⟨x, trivial⟩ : (⊤ : (Spec (.of K)).Opens))
  have h1 := hU.isLocalization_stalk ⟨x, trivial⟩
  have : IsIntegrallyClosed Γ(Spec (.of K), ⊤) :=
    IsIntegrallyClosed.of_equiv (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv
  exact (isDomain_and_isIntegrallyClosed_atPrime_of_isDomain (hU.primeIdealOf ⟨x, trivial⟩).asIdeal
    ((Spec (.of K)).presheaf.stalk x)).2

theorem affineSpace_over_integral_affine_open_smooth_integral_normal :
    ∀ (X : Scheme.{0}) (K : Type) [Field K] (s : X ⟶ Spec (.of K)), Smooth s →
    ∀ (V : X.Opens), IsAffineOpen V → IsIntegral V.toScheme → ∀ (ι : Type) [Finite ι],
    Smooth ((𝔸(ι; V.toScheme) ↘ V.toScheme) ≫ V.ι) ∧
    LocallyOfFiniteType ((𝔸(ι; V.toScheme) ↘ V.toScheme) ≫ V.ι) ∧
    IsIntegral 𝔸(ι; V.toScheme) ∧
    ∀ t : 𝔸(ι; V.toScheme), IsIntegrallyClosed (𝔸(ι; V.toScheme).presheaf.stalk t) := by
  intro X K _ s hs V hV hint ι _
  have : IsAffine V.toScheme := hV
  have : Smooth (𝔸(ι; V.toScheme) ↘ V.toScheme) := smooth_affineSpace_over_of_isAffine _ ι
  have h1 : Smooth ((𝔸(ι; V.toScheme) ↘ V.toScheme) ≫ V.ι) := inferInstance
  refine ⟨h1, inferInstance, inferInstance, fun t ↦ ?_⟩
  have : Smooth (((𝔸(ι; V.toScheme) ↘ V.toScheme) ≫ V.ι) ≫ s) := inferInstance
  exact (forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth
    (((𝔸(ι; V.toScheme) ↘ V.toScheme) ≫ V.ι) ≫ s)
    (fun y ↦ ⟨inferInstance, isIntegrallyClosed_stalk_spec_field K y⟩) t).2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgEquivMatrixGlueCrtStatement
section
open scoped TensorProduct
open Function
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algEquiv_matrix_glue_crt : ∀ (A Λ : Type) [CommRing A] [Ring Λ] [Algebra A Λ] (ι : Type) [Fintype ι] (I : ι → Ideal A), Pairwise (IsCoprime on I) → ⨅ i, I i = ⊥ → ∀ (n : ℕ), (∀ i, Nonempty ((A ⧸ I i) ⊗[A] Λ ≃ₐ[A ⧸ I i] Matrix (Fin n) (Fin n) (A ⧸ I i))) → Nonempty (Λ ≃ₐ[A] Matrix (Fin n) (Fin n) A) := by
  first | (exact @GlobalTheory.matrix_glue_crt) | (exact GlobalTheory.matrix_glue_crt) | (intros; apply GlobalTheory.matrix_glue_crt  <;> assumption)
end

