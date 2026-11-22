import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import GroundTheory.AutomorphicForms.StableConjCyclic
import GroundTheory.Brauer.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0563
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0581
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0597
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0607

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsUnitMemOfSpanBaseChange
section
namespace GlobalTheory.LKInv

open Module Polynomial TensorProduct

theorem isUnit_of_isUnit_mulLeft {k A : Type} [Field k] [Ring A] [Algebra k A] (x : A)
    (h : IsUnit (LinearMap.mulLeft k x)) : IsUnit x := by
  set u := h.unit with hu
  set y : A := ((u⁻¹ : (Module.End k A)ˣ) : Module.End k A) 1 with hy
  have hxy : x * y = 1 := by
    change LinearMap.mulLeft k x (((u⁻¹ : (Module.End k A)ˣ) : Module.End k A) 1) = 1
    rw [← Module.End.mul_apply]
    have : LinearMap.mulLeft k x = (u : Module.End k A) := rfl
    rw [this, Units.mul_inv, Module.End.one_apply]
  have hly : LinearMap.mulLeft k y = ((u⁻¹ : (Module.End k A)ˣ) : Module.End k A) := by
    have e : (u : Module.End k A) * LinearMap.mulLeft k y = 1 := by
      change LinearMap.mulLeft k x * LinearMap.mulLeft k y = 1
      ext z
      simp [← mul_assoc, hxy]
    calc LinearMap.mulLeft k y = ((u⁻¹ : (Module.End k A)ˣ) : Module.End k A) *
          ((u : Module.End k A) * LinearMap.mulLeft k y) := by rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = _ := by rw [e, mul_one]
  have hyx : y * x = 1 := by
    have := congrArg (fun f : Module.End k A => f 1) (Units.inv_mul u)
    simp only [← hly] at this
    change y * (x * 1) = 1 at this
    rwa [mul_one] at this
  exact ⟨⟨x, y, hxy, hyx⟩, rfl⟩

theorem baseChange_mulLeft {k A K : Type} [Field k] [Ring A] [Algebra k A] [Field K] [Algebra k K]
    (a : A) : (LinearMap.mulLeft k a).baseChange K = LinearMap.mulLeft K ((1 : K) ⊗ₜ[k] a) := by
  ext x
  simp [Algebra.TensorProduct.tmul_mul_tmul]

theorem exists_isUnit_mem_of_span_baseChange {k A K : Type} [Field k] [Infinite k] [Ring A]
    [Algebra k A] [FiniteDimensional k A] [Field K] [Algebra k K] (V : Submodule k A) (u : K ⊗[k] A)
    (hu : u ∈ Submodule.span K ((fun a : A => (1 : K) ⊗ₜ[k] a) '' (V : Set A))) (hunit : IsUnit u) :
    ∃ x ∈ V, IsUnit x := by
  classical
  set r := finrank k V
  let b : Basis (Fin r) k V := Module.finBasis k V
  set m := finrank k A
  let bA : Basis (Fin m) k A := Module.finBasis k A
  let M : Fin r → Matrix (Fin m) (Fin m) k := fun i => LinearMap.toMatrix bA bA (LinearMap.mulLeft k (b i : A))
  set D : MvPolynomial (Fin r) k := (∑ i, (MvPolynomial.X i : MvPolynomial (Fin r) k) •
      (M i).map (MvPolynomial.C : k →+* MvPolynomial (Fin r) k)).det with hD
  have key : ∀ {T : Type} [CommRing T] (ψ : MvPolynomial (Fin r) k →+* T),
      ψ D = (∑ i, ψ (MvPolynomial.X i) • (M i).map (ψ.comp (MvPolynomial.C : k →+* MvPolynomial (Fin r) k))).det := by
    intro T _ ψ
    rw [hD, RingHom.map_det, RingHom.mapMatrix_apply]
    congr 1
    ext p q
    simp [Matrix.sum_apply]

  have hlin : ∀ t : Fin r → k, ∑ i, t i • M i =
      LinearMap.toMatrix bA bA (LinearMap.mulLeft k (∑ i, t i • (b i : A))) := by
    intro t
    have : LinearMap.mulLeft k (∑ i, t i • (b i : A)) = ∑ i, t i • LinearMap.mulLeft k (b i : A) := by
      ext z; simp [Finset.sum_mul]
    rw [this, map_sum]
    simp [M, map_smul]

  have hD0 : D ≠ 0 := by
    have hspan : Submodule.span K ((fun a : A => (1 : K) ⊗ₜ[k] a) '' (V : Set A)) ≤
        Submodule.span K (Set.range fun i => (1 : K) ⊗ₜ[k] (b i : A)) := by
      rw [Submodule.span_le]
      rintro _ ⟨a, ha, rfl⟩
      have hrep := b.sum_repr ⟨a, ha⟩
      have : (1 : K) ⊗ₜ[k] a = ∑ i, (algebraMap k K (b.repr ⟨a, ha⟩ i)) • ((1 : K) ⊗ₜ[k] (b i : A)) := by
        conv_lhs => rw [show a = ((⟨a, ha⟩ : V) : A) from rfl, ← hrep]
        simp only [Submodule.coe_sum, Submodule.coe_smul, TensorProduct.tmul_sum, TensorProduct.tmul_smul,
          algebraMap_smul]
      show (1 : K) ⊗ₜ[k] a ∈ Submodule.span K (Set.range fun i => (1 : K) ⊗ₜ[k] (b i : A))
      rw [this]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    obtain ⟨s, hs⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 (hspan hu)
    intro h0
    have h1 := key (MvPolynomial.eval₂Hom (algebraMap k K) s)
    rw [h0, map_zero] at h1
    have hmat : ∑ i, (MvPolynomial.eval₂Hom (algebraMap k K) s) (MvPolynomial.X i) •
        (M i).map ((MvPolynomial.eval₂Hom (algebraMap k K) s).comp MvPolynomial.C) =
        LinearMap.toMatrix (Algebra.TensorProduct.basis K bA) (Algebra.TensorProduct.basis K bA)
          (LinearMap.mulLeft K u) := by
      rw [← hs]
      have : LinearMap.mulLeft K (∑ i, s i • (1 : K) ⊗ₜ[k] (b i : A)) =
          ∑ i, s i • LinearMap.mulLeft K ((1 : K) ⊗ₜ[k] (b i : A)) := by
        ext z; simp [Finset.sum_mul]
      rw [this, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, ← baseChange_mulLeft, LinearMap.toMatrix_baseChange]
      simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
      rw [MvPolynomial.eval₂Hom_comp_C]
    rw [hmat, LinearMap.det_toMatrix] at h1
    have hu' : IsUnit (LinearMap.mulLeft K u) := by
      obtain ⟨w, rfl⟩ := hunit
      refine ⟨⟨LinearMap.mulLeft K (w : K ⊗[k] A), LinearMap.mulLeft K ((w⁻¹ : (K ⊗[k] A)ˣ) : K ⊗[k] A),
        ?_, ?_⟩, rfl⟩ <;> ext z <;> simp [← mul_assoc]
    have := (LinearMap.isUnit_iff_isUnit_det _).1 hu'
    rw [← h1] at this
    exact not_isUnit_zero this

  obtain ⟨t, ht⟩ : ∃ t : Fin r → k, MvPolynomial.eval t D ≠ 0 := by
    by_contra hne
    push_neg at hne
    exact hD0 (MvPolynomial.funext fun x => by rw [hne x, map_zero])
  refine ⟨∑ i, t i • (b i : A), Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (b i).2, ?_⟩
  apply isUnit_of_isUnit_mulLeft (k := k)
  rw [LinearMap.isUnit_iff_isUnit_det, ← LinearMap.det_toMatrix bA, ← hlin, isUnit_iff_ne_zero]
  rw [key] at ht
  convert ht using 2
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval_X]
  congr 1
  ext p q
  simp

end GlobalTheory.LKInv

namespace GlobalTheory.LKInv

open Module Polynomial TensorProduct

theorem exists_unit_conj_of_baseChange {k A K : Type} [Field k] [Infinite k] [Ring A] [Algebra k A]
    [FiniteDimensional k A] [Field K] [Algebra k K] (x₀ x : A) (w : (K ⊗[k] A)ˣ)
    (hw : (w : K ⊗[k] A) * ((1 : K) ⊗ₜ[k] x₀) = ((1 : K) ⊗ₜ[k] x) * w) :
    ∃ g : Aˣ, (g : A) * x₀ = x * g := by
  let a : A →ₗ[k] A := LinearMap.mulRight k x₀ - LinearMap.mulLeft k x
  let a' : K ⊗[k] A →ₗ[K] K ⊗[k] A :=
    LinearMap.mulRight K ((1 : K) ⊗ₜ[k] x₀) - LinearMap.mulLeft K ((1 : K) ⊗ₜ[k] x)
  have hbc := (GlobalTheory.BadCount.finrank_iInf_ker_baseChange k K A (K ⊗[k] A) Unit
    (TensorProduct.mk k K A 1) (TensorProduct.isBaseChange k A K) (fun _ => a) (fun _ => a')
    (fun _ v => by simp [a, a', Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.tmul_sub])).2
  rw [_root_.iInf_const, _root_.iInf_const] at hbc
  have hwmem : (w : K ⊗[k] A) ∈ LinearMap.ker a' := by
    rw [LinearMap.mem_ker]
    simp [a', hw]
  rw [hbc] at hwmem
  obtain ⟨y, hyV, hyu⟩ := exists_isUnit_mem_of_span_baseChange (K := K) (LinearMap.ker a)
    (w : K ⊗[k] A) hwmem w.isUnit
  refine ⟨hyu.unit, ?_⟩
  rw [LinearMap.mem_ker] at hyV
  simpa [a, sub_eq_zero] using hyV

theorem charpoly_eq_map_minpoly {F B : Type} [Field F] [Ring B] [Algebra F B] [FiniteDimensional F B]
    {n : ℕ} (e : AlgebraicClosure F ⊗[F] B ≃ₐ[AlgebraicClosure F] Matrix (Fin n) (Fin n) (AlgebraicClosure F))
    (y : B) (hsep : (minpoly F y).Separable) (hdeg : (minpoly F y).natDegree = n) :
    (e ((1 : AlgebraicClosure F) ⊗ₜ[F] y)).charpoly = (minpoly F y).map (algebraMap F (AlgebraicClosure F)) := by
  set K := AlgebraicClosure F
  set z : K ⊗[F] B := (1 : K) ⊗ₜ[F] y with hz
  have hzi : IsIntegral K z := IsIntegral.of_finite K z
  have hyi : IsIntegral F y := IsIntegral.of_finite F y
  have hzr : z = Algebra.TensorProduct.includeRight y := rfl
  have hdvd : minpoly K z ∣ (minpoly F y).map (algebraMap F K) := by
    apply minpoly.dvd
    rw [aeval_map_algebraMap, hzr, aeval_algHom_apply, minpoly.aeval, map_zero]
  have hge := GlobalTheory.CentSep.natDegree_minpoly_le_baseChange K y hzi
  have hmap0 : (minpoly F y).map (algebraMap F K) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap F K).injective).mpr (minpoly.ne_zero hyi)
  have hzdeg : (minpoly K z).natDegree = n := by
    refine le_antisymm ?_ (hdeg ▸ hge)
    calc (minpoly K z).natDegree ≤ ((minpoly F y).map (algebraMap F K)).natDegree :=
          natDegree_le_of_dvd hdvd hmap0
      _ = n := by rw [natDegree_map, hdeg]
  have hzeq : minpoly K z = (minpoly F y).map (algebraMap F K) := by
    have := eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le (minpoly.monic hzi) hdvd
      (by rw [natDegree_map, hdeg, hzdeg])
    rw [this, ((minpoly.monic hyi).map _).leadingCoeff, C_1, one_mul]
  set N := e z with hN
  have hmN : minpoly K N = minpoly K z := minpoly.algEquiv_eq e z
  have hd : minpoly K N ∣ N.charpoly := minpoly.dvd K N (Matrix.aeval_self_charpoly N)
  rw [hmN] at hd
  have := eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le (minpoly.monic hzi) hd
    (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin, hzdeg])
  rw [this, (Matrix.charpoly_monic N).leadingCoeff, C_1, one_mul, hzeq]

theorem exists_unit_conj_of_minpoly_eq (F B : Type) [Field F] [Infinite F] [Ring B] [Algebra F B]
    [Algebra.IsCentral F B] [IsSimpleRing B] [FiniteDimensional F B] (n : ℕ)
    (hn : Module.finrank F B = n ^ 2) (x₀ x : B) (hsep : (minpoly F x₀).Separable)
    (hdeg : (minpoly F x₀).natDegree = n) (hmin : minpoly F x = minpoly F x₀) :
    ∃ g : Bˣ, (g : B) * x₀ = x * g := by
  classical
  obtain ⟨m, hm0, hmB, ⟨e⟩⟩ := GroundTheory.Brauer.exists_algEquiv_matrix_algebraicClosure F B
  have hmn : m = n := Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) (hmB.symm.trans hn)
  subst hmn
  set K := AlgebraicClosure F
  set N₀ := e ((1 : K) ⊗ₜ[F] x₀) with hN₀
  set N := e ((1 : K) ⊗ₜ[F] x) with hN
  have hc₀ := charpoly_eq_map_minpoly e x₀ hsep hdeg
  have hc := charpoly_eq_map_minpoly e x (hmin ▸ hsep) (hmin ▸ hdeg)
  rw [hmin] at hc
  have hsepK : (Matrix.toLin' N₀).charpoly.Separable := by
    rw [Matrix.charpoly_toLin', hc₀]; exact hsep.map
  obtain ⟨e', he'⟩ := GroundTheory.Automorphic.exists_conj_of_charpoly_eq hsepK
    (f' := Matrix.toLin' N) (by rw [Matrix.charpoly_toLin', Matrix.charpoly_toLin', hc₀, hc])
  set P := LinearMap.toMatrix' (e' : (Fin m → K) →ₗ[K] (Fin m → K)) with hP
  set Q := LinearMap.toMatrix' (e'.symm : (Fin m → K) →ₗ[K] (Fin m → K)) with hQ
  have hPQ : P * Q = 1 := by
    rw [hP, hQ, ← LinearMap.toMatrix'_comp]
    have : (e' : (Fin m → K) →ₗ[K] (Fin m → K)) ∘ₗ (e'.symm : (Fin m → K) →ₗ[K] (Fin m → K)) =
        LinearMap.id := by ext v; simp
    rw [this, LinearMap.toMatrix'_id]
  have hQP : Q * P = 1 := by
    rw [hP, hQ, ← LinearMap.toMatrix'_comp]
    have : (e'.symm : (Fin m → K) →ₗ[K] (Fin m → K)) ∘ₗ (e' : (Fin m → K) →ₗ[K] (Fin m → K)) =
        LinearMap.id := by ext v; simp
    rw [this, LinearMap.toMatrix'_id]
  have hPN : P * N₀ = N * P := by
    have : (e' : (Fin m → K) →ₗ[K] (Fin m → K)) ∘ₗ Matrix.toLin' N₀ =
        Matrix.toLin' N ∘ₗ (e' : (Fin m → K) →ₗ[K] (Fin m → K)) :=
      LinearMap.ext fun v => he' v
    have h2 := congrArg LinearMap.toMatrix' this
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin',
      LinearMap.toMatrix'_toLin'] at h2

  set w : (K ⊗[F] B)ˣ := ⟨e.symm P, e.symm Q, by rw [← map_mul, hPQ, map_one],
    by rw [← map_mul, hQP, map_one]⟩ with hw
  refine exists_unit_conj_of_baseChange x₀ x w ?_
  apply e.injective
  rw [map_mul, map_mul]
  simp only [hw, Units.val_mk, AlgEquiv.apply_symm_apply]
  rw [← hN₀, ← hN, hPN]

end GlobalTheory.LKInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieAlgebraExpGenerators
section
noncomputable section

open Filter Topology
open scoped ContDiff

namespace GlobalTheory.ClosedMonoid

open GlobalTheory.ClosedMatGroup

theorem contDiff_ofFn_prod {𝔸 E : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ∀ (n : ℕ) (g : Fin n → E → 𝔸), (∀ i, ContDiff ℝ ∞ (g i)) →
      ContDiff ℝ ∞ (fun z => (List.ofFn fun i => g i z).prod) := by
  intro n
  induction n with
  | zero => intro g _; simpa using contDiff_const
  | succ n ih =>
    intro g hg
    simp only [List.ofFn_succ, List.prod_cons]
    exact (hg 0).mul (ih _ fun i => hg _)

theorem coords_second_kind_of_spanning : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (S : Set 𝔸), IsClosed S → (1 : 𝔸) ∈ S →
    (∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) → (∀ Z : 𝔸, NormedSpace.exp Z ∈ S → NormedSpace.exp (-Z) ∈ S) →
    ∀ (d : ℕ) (Z : Fin d → 𝔸), (∀ (i : Fin d) (t : ℝ), NormedSpace.exp (t • Z i) ∈ S) →
    (∀ Y : 𝔸, (∀ t : ℝ, NormedSpace.exp (t • Y) ∈ S) → Y ∈ Submodule.span ℝ (Set.range Z)) →
    ∃ s : 𝔸 → Fin d → ℝ, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) s 1 ∧
      ∀ᶠ X in nhds (1 : 𝔸), X ∈ S → X = (List.ofFn fun i => NormedSpace.exp (s X i • Z i)).prod := by
  intro 𝔸 _ _ _ _ S hc h1 hm hi d Z hZ hspan
  let _ : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  let L := lieSub S hc h1 hm
  obtain ⟨W, hW⟩ := L.exists_isCompl
  let F : (Fin d → ℝ) →ₗ[ℝ] 𝔸 := Fintype.linearCombination ℝ Z
  have hF : ∀ v, F v = ∑ i, v i • Z i := fun v => Fintype.linearCombination_apply ℝ Z v
  have hLF : L ≤ LinearMap.range F := by
    intro x hx
    rw [Fintype.range_linearCombination]
    exact hspan x hx
  obtain ⟨g, hg⟩ := F.rangeRestrict.exists_rightInverse_of_surjective (LinearMap.range_rangeRestrict F)
  let c : 𝔸 →L[ℝ] (Fin d → ℝ) := LinearMap.toContinuousLinearMap
    (g ∘ₗ (Submodule.inclusion hLF) ∘ₗ L.projectionOnto W hW)
  let p : 𝔸 →L[ℝ] 𝔸 := LinearMap.toContinuousLinearMap (L.projection W hW)
  have hpc : ∀ z, ∑ i, c z i • Z i = p z := by
    intro z
    rw [← hF]
    have e := congrArg Subtype.val (LinearMap.congr_fun hg (Submodule.inclusion hLF (L.projectionOnto W hW z)))
    exact e
  have hqW : ∀ z, z - p z ∈ W := fun z => by
    have h := Submodule.projection_add_projection_eq_self hW z
    have e : z - p z = W.projection _ hW.symm z := by
      rw [sub_eq_iff_eq_add']; exact h.symm
    rw [e]; exact Submodule.projection_apply_mem hW.symm z
  let Φ : 𝔸 → 𝔸 := fun z => (List.ofFn fun i => NormedSpace.exp (c z i • Z i)).prod * NormedSpace.exp (z - p z)
  have hexpS : ContDiff ℝ ∞ (NormedSpace.exp : 𝔸 → 𝔸) :=
    contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
  have hΦs : ContDiff ℝ ∞ Φ := by
    refine (contDiff_ofFn_prod d (fun i z => NormedSpace.exp (c z i • Z i)) fun i => ?_).mul ?_
    · exact hexpS.comp ((((ContinuousLinearMap.proj i).comp c).smulRight (Z i)).contDiff)
    · exact hexpS.comp ((ContinuousLinearMap.id ℝ 𝔸 - p).contDiff)
  have hexp : HasStrictFDerivAt NormedSpace.exp (1 : 𝔸 →L[ℝ] 𝔸) (0 : 𝔸) := hasStrictFDerivAt_exp_zero
  have hf : ∀ i, HasStrictFDerivAt (fun z => NormedSpace.exp (c z i • Z i))
      ((1 : 𝔸 →L[ℝ] 𝔸).comp (((ContinuousLinearMap.proj i).comp c).smulRight (Z i))) 0 := fun i =>
    HasStrictFDerivAt.comp (0 : 𝔸) (g := NormedSpace.exp) (by rw [map_zero, Pi.zero_apply, zero_smul]; exact hexp)
      (((ContinuousLinearMap.proj i).comp c).smulRight (Z i)).hasStrictFDerivAt
  have hP := hasStrictFDerivAt_ofFn_prod d (fun i z => NormedSpace.exp (c z i • Z i)) _ 0
    (fun i => by simp) hf
  have h2 : HasStrictFDerivAt (fun z => NormedSpace.exp (z - p z))
      ((1 : 𝔸 →L[ℝ] 𝔸).comp (ContinuousLinearMap.id ℝ 𝔸 - p)) 0 :=
    HasStrictFDerivAt.comp (0 : 𝔸) (f := fun z => z - p z) (by rw [map_zero, sub_zero]; exact hexp)
      (ContinuousLinearMap.id ℝ 𝔸 - p).hasStrictFDerivAt
  have h4 : HasStrictFDerivAt Φ ((ContinuousLinearEquiv.refl ℝ 𝔸 : 𝔸 ≃L[ℝ] 𝔸) : 𝔸 →L[ℝ] 𝔸) 0 := by
    refine (hP.mul' h2).congr_fderiv ?_
    ext1 z
    have e1 : (List.ofFn fun i => NormedSpace.exp ((0 : Fin d → ℝ) i • Z i)).prod = 1 := by simp
    simp [e1, hpc]
  have hΦ0 : Φ 0 = 1 := by
    show (List.ofFn fun i => NormedSpace.exp (c 0 i • Z i)).prod * NormedSpace.exp (0 - p 0) = 1
    simp
  have hn : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hΦa : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ 0 := hΦs.contDiffAt
  let Ψ := hΦa.localInverse h4.hasFDerivAt hn
  have hΨs : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ 1 := by
    have h := hΦa.to_localInverse h4.hasFDerivAt hn
    rw [hΦ0] at h
    exact h
  have h4' := hΦa.hasStrictFDerivAt' h4.hasFDerivAt hn
  have hΨ : Tendsto Ψ (𝓝 1) (𝓝 0) := by
    have h := h4'.localInverse_tendsto
    rw [hΦ0] at h
    exact h
  have hR : ∀ᶠ X in 𝓝 (1 : 𝔸), Φ (Ψ X) = X := by
    have h := h4'.eventually_right_inverse
    rw [hΦ0] at h
    exact h
  have hp0 : Tendsto p (𝓝 0) (𝓝 0) := by simpa using p.continuous.tendsto 0
  have hq0 : Tendsto (fun z => z - p z) (𝓝 0) (𝓝 (0 : 𝔸)) := by
    simpa using (tendsto_id (x := 𝓝 (0 : 𝔸))).sub hp0
  refine ⟨fun X => c (Ψ X), c.contDiff.contDiffAt.comp 1 hΨs, ?_⟩
  filter_upwards [hR, hΨ.eventually (hq0.eventually (eventually_eq_zero hc h1 hm hi hW.disjoint))]
    with X hX1 hX2 hXS
  obtain ⟨Q, hQ, hQe⟩ := exists_left_inv_ofFn_prod h1 hm d (fun i => c (Ψ X) i • Z i)
    (fun i => by rw [← neg_smul]; exact hZ i _)
  have hE : NormedSpace.exp (Ψ X - p (Ψ X)) = Q * X := by
    conv_rhs => rw [← hX1]
    show _ = Q * ((List.ofFn fun i => NormedSpace.exp (c (Ψ X) i • Z i)).prod * NormedSpace.exp (Ψ X - p (Ψ X)))
    rw [← mul_assoc, hQe, one_mul]
  have hw := hX2 (hqW _) (by rw [hE]; exact hm _ hQ _ hXS)
  calc X = Φ (Ψ X) := hX1.symm
    _ = _ := by
      show (List.ofFn fun i => NormedSpace.exp (c (Ψ X) i • Z i)).prod * NormedSpace.exp (Ψ X - p (Ψ X)) = _
      rw [hw, NormedSpace.exp_zero, mul_one]

end GlobalTheory.ClosedMonoid
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundlePowerIsoReindexedCharts
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat

namespace GlobalTheory.PowIsoRe

theorem res_res {X : Scheme.{0}} {U V W : X.Opens} (e1 : W ≤ V) (e2 : V ≤ U) (x : Γ(X, U)ˣ) :
    res e1 (res e2 x) = res (e1.trans e2) x := by
  ext1
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem preimage_comp_le {X Y Z : Scheme.{0}} (h : X ⟶ Y) (φ : Y ⟶ Z) {W : Z.Opens} {V : Y.Opens}
    (e : V ≤ φ ⁻¹ᵁ W) : h ⁻¹ᵁ V ≤ (h ≫ φ) ⁻¹ᵁ W := by
  intro x hx
  exact e hx

theorem pullU_res_pullU {X Y Z : Scheme.{0}} (h : X ⟶ Y) (φ : Y ⟶ Z) {W : Z.Opens} {V : Y.Opens}
    (e : V ≤ φ ⁻¹ᵁ W) (u : Γ(Z, W)ˣ) :
    pullU h V (res e (pullU φ W u)) = res (preimage_comp_le h φ e) (pullU (h ≫ φ) W u) := by
  have key : φ.app W ≫ Y.presheaf.map (homOfLE e).op ≫ h.app V =
      (h ≫ φ).app W ≫ X.presheaf.map (homOfLE (preimage_comp_le h φ e)).op := by
    rw [Scheme.Hom.naturality, Scheme.Hom.comp_app]
    rfl
  ext1
  simp only [res, pullU, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, key]

end GlobalTheory.PowIsoRe

namespace GlobalTheory.PowIsoRe

theorem res_pull_comp {X Y Z : Scheme.{0}} (h : X ⟶ Y) (m : Y ⟶ Z) {W : Z.Opens} {V1 : Y.Opens}
    {V2 V3 T : X.Opens} (u : Γ(Z, W)ˣ) (e1 : V1 ≤ m ⁻¹ᵁ W) (e2 : V2 ≤ h ⁻¹ᵁ V1) (e3 : T ≤ V2)
    (e4 : V3 ≤ (h ≫ m) ⁻¹ᵁ W) (e5 : T ≤ V3) :
    res e3 (res e2 (pullU h V1 (res e1 (pullU m W u)))) = res e5 (res e4 (pullU (h ≫ m) W u)) := by
  rw [pullU_res_pullU, res_res, res_res, res_res]

theorem res_res' {X : Scheme.{0}} {U V V' W : X.Opens} (x : Γ(X, U)ˣ) (e1 : W ≤ V) (e2 : V ≤ U)
    (e3 : W ≤ V') (e4 : V' ≤ U) : res e1 (res e2 x) = res e3 (res e4 x) := by
  rw [res_res, res_res]

end GlobalTheory.PowIsoRe

namespace GlobalTheory.PowIsoRe

theorem wchart_le_M {X Y Z : Scheme.{0}} (M : LB Z) (h : X ⟶ Y) (m : Y ⟶ Z) (j : Fin 1 → M.ι) :
    LB.wchart M (fun _ : Fin 1 => h ≫ m) j ≤
      LB.wchart (M.pull m) (fun _ : PUnit => h) (fun _ _ => j 0) := by
  intro x hx
  have hx0 := Set.mem_iInter.1 hx 0
  refine Set.mem_iInter.2 fun _ => ?_
  refine Set.mem_iInter.2 fun _ => ?_
  simpa using hx0

theorem wchart_le_L {X Z : Scheme.{0}} (L : LB Z) (f : X ⟶ Z) (j : Fin 1 → L.ι) :
    LB.wchart L (fun _ : Fin 1 => f) j ≤ LB.wchart L (fun _ : PUnit => f) (fun _ => j 0) := by
  intro x hx
  exact Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hx 0

theorem exists_powIso {X Y Z₁ Z₂ : Scheme.{0}} (L : LB Z₁) (M : LB Z₂) (f : X ⟶ Z₁) (h : X ⟶ Y) (m : Y ⟶ Z₂)
    (k : ℕ) (w : LB.Gen (LB.div ((M.pull m).pull h) (L.pull f))) (hw : w.IsGen) :
    ∃ α : LB.Gen (LB.div (powPull M (h ≫ m) (k : ℤ)) (powPull L f (k : ℤ))), α.IsGen := by
  dsimp only [LB.Gen.IsGen, LB.div, LB.LinComb, LB.pull, powPull] at w hw ⊢
  have hle : ∀ p : (Fin 1 → M.ι) × (Fin 1 → L.ι),
      LB.wchart M (fun _ : Fin 1 => h ≫ m) p.1 ⊓ LB.wchart L (fun _ : Fin 1 => f) p.2 ≤
        LB.wchart (M.pull m) (fun _ : PUnit => h) (fun _ _ => p.1 0) ⊓
          LB.wchart L (fun _ : PUnit => f) (fun _ => p.2 0) := fun p =>
    inf_le_inf (wchart_le_M M h m p.1) (wchart_le_L L f p.2)
  dsimp only [LB.pull, LB.LinComb] at hle
  refine ⟨⟨fun p => (res (hle p) (w.s (fun _ _ => p.1 0, fun _ => p.2 0))) ^ k⟩, ?_⟩
  dsimp only
  intro p p'
  have e := congrArg (fun x => (res (inf_le_inf (hle p) (hle p')) x) ^ k)
    (hw (fun _ _ => p.1 0, fun _ => p.2 0) (fun _ _ => p'.1 0, fun _ => p'.2 0))
  simp only [map_mul, map_inv, map_pow, map_zpow, map_prod, res_res, pullU_res_pullU,
    Fin.prod_univ_one, Fintype.prod_unique, Fin.default_eq_zero, zpow_one, zpow_natCast, mul_pow, inv_pow] at e ⊢
  convert e using 5
  · exact (res_pull_comp h m (W := M.U (p.1 0) ⊓ M.U (p'.1 0))
      (V1 := LB.wchart M (fun _ : PUnit.{1} => m) (fun _ => p.1 0) ⊓ LB.wchart M (fun _ : PUnit.{1} => m) (fun _ => p'.1 0))
      (M.g (p.1 0) (p'.1 0)) _ _ _ _ _).symm
  · rfl
  · exact res_res' (U := f ⁻¹ᵁ (L.U (p.2 0) ⊓ L.U (p'.2 0))) (pullU f _ (L.g (p.2 0) (p'.2 0))) _ _ _ _

end GlobalTheory.PowIsoRe
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundlePowerPullbackSectionPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat
noncomputable section

namespace GlobalTheory.HomFixMat

theorem appLE_res_pull {X Y Z : Scheme.{0}} (φ : Y ⟶ Z) (h : X ⟶ Y) (U : Z.Opens) (V : Y.Opens) (W : X.Opens)
    (e₁ : V ≤ φ ⁻¹ᵁ U) (e₂ : W ≤ h ⁻¹ᵁ V) (e₃ : W ≤ (h ≫ φ) ⁻¹ᵁ U) (u : Γ(Z, U)) :
    (h.appLE V W e₂).hom ((Y.presheaf.map (homOfLE e₁).op).hom ((φ.app U).hom u)) =
      (X.presheaf.map (homOfLE e₃).op).hom (((h ≫ φ).app U).hom u) := by
  simp only [← CommRingCat.comp_apply]
  congr 1
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map, Scheme.Hom.appLE_map,
    Scheme.Hom.appLE_comp_appLE]

theorem appLE_restrict {X Y : Scheme.{0}} (h : X ⟶ Y) (V V' : Y.Opens) (W W' : X.Opens) (eV : V' ≤ V)
    (eW : W' ≤ W) (e : W ≤ h ⁻¹ᵁ V) (e' : W' ≤ h ⁻¹ᵁ V') (x : Γ(Y, V)) :
    (X.presheaf.map (homOfLE eW).op).hom ((h.appLE V W e).hom x) =
      (h.appLE V' W' e').hom ((Y.presheaf.map (homOfLE eV).op).hom x) := by
  simp only [← CommRingCat.comp_apply]
  congr 1
  rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]

theorem pullSec_exists : ∀ {X Y Z : Scheme.{0}} (L : LB Z) (φ : Y ⟶ Z) (h : X ⟶ Y) (a : ℤ)
    (s : LB.Sec (powPull L φ a)), ∃ s' : LB.Sec (powPull L (h ≫ φ) a), ∀ q : Fin 1 → L.ι,
      s'.f q = (h.appLE (LB.wchart L (fun _ : Fin 1 => φ) q) (LB.wchart L (fun _ : Fin 1 => h ≫ φ) q)
        (GlobalTheory.HomFixMat.wchart_comp_le L h φ q)).hom (s.f q) := by
  intro X Y Z L φ h a s
  refine ⟨⟨fun q => (h.appLE _ _ (GlobalTheory.HomFixMat.wchart_comp_le L h φ q)).hom (s.f q), ?_⟩, fun q => rfl⟩
  intro (q : Fin 1 → L.ι) (q' : Fin 1 → L.ι)
  have e0 : LB.wchart L (fun _ : Fin 1 => h ≫ φ) q ⊓ LB.wchart L (fun _ : Fin 1 => h ≫ φ) q' ≤
      h ⁻¹ᵁ (LB.wchart L (fun _ : Fin 1 => φ) q ⊓ LB.wchart L (fun _ : Fin 1 => φ) q') :=
    fun x hx => ⟨GlobalTheory.HomFixMat.wchart_comp_le L h φ q hx.1, GlobalTheory.HomFixMat.wchart_comp_le L h φ q' hx.2⟩
  refine (appLE_restrict h _ _ _ _ inf_le_left inf_le_left _ e0 _).trans ?_
  refine (congrArg _ (s.compat q q')).trans ?_
  refine (map_mul _ _ _).trans ?_
  congr 1
  · have hg : ((powPull L (h ≫ φ) a).g q q') =
        Units.map (h.appLE _ _ e0).hom.toMonoidHom ((powPull L φ a).g q q') := by
      show (∏ k : Fin 1, _) = Units.map _ (∏ k : Fin 1, _)
      rw [map_prod]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [map_zpow]
      congr 1
      ext
      exact (appLE_res_pull φ h (L.U (q 0) ⊓ L.U (q' 0))
        (LB.wchart L (fun _ : Fin 1 => φ) q ⊓ LB.wchart L (fun _ : Fin 1 => φ) q')
        (LB.wchart L (fun _ : Fin 1 => h ≫ φ) q ⊓ LB.wchart L (fun _ : Fin 1 => h ≫ φ) q') _ e0 _
        (L.g (q 0) (q' 0) : Γ(Z, L.U (q 0) ⊓ L.U (q' 0)))).symm
    rw [hg]
    rfl
  · exact (appLE_restrict h _ _ _ _ inf_le_right inf_le_right _ e0 _).symm

end GlobalTheory.HomFixMat
end
end

