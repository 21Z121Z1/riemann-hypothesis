import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1395
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBoundedUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0255
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1052
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1053
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1081
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1375
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1067
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1026
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1113
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1027
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1064
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.Bundle0025
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0949
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1346
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1322
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1386
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1388
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1361
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1241
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1298
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1368
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1304
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1296
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1290
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1378
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLieElementsGenerateOneParamLines

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemL2OfContinuousAutomorphic
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefiniteSqInt

theorem memL2_of_continuous_definite : ∀ {D : D7} (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)),
    GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsDefiniteSpace V → GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsOpenCompactLevel V K → Links.IsMeasDef V K μ 𝓕 →
    ∀ u : GA D V → ℂ, Continuous u → (∀ γ ∈ GQ V, ∀ h, u (γ * h) = u h) → GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (GQ V) μ u := by
  intro D V K μ 𝓕 hV _ hμ u hu hinv
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := hT.2.2.2.2.2.2
  have := hμ.1.1
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.Mem.AnisoQuotient.exists_compact D V
    (GlobalTheory.BesselConvDefinite.isAniso_of_isDefinite V hV.1 hV.2)
  have hcov' : ∀ g : GA D V, ∃ γ ∈ GQ V, γ * g ∈ C := fun g => by
    obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov g
    exact ⟨γ⁻¹, inv_mem hγ, by rwa [inv_mul_cancel_left]⟩
  refine (GlobalTheory.AutomorphicL2Unitary.memL2_iff_fundamental_domain hμ.2).2 ⟨hinv, (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).2 ?_⟩
  simpa only [← _root_.norm_pow] using (GlobalTheory.integrableOn_fundamentalDomain_of_cocompact _ (GQ V) C hC hcov' μ
    inferInstance 𝓕 hμ.2 (fun g => u g ^ 2) (hu.pow 2) fun γ hγ g => by rw [hinv γ hγ]).norm

end GlobalTheory.DefiniteSqInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MoveMarkOfIrreducible
section
noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid.MoveMark

section Field

variable {F M : Type} [Field F] [Field M] [Algebra F M]

theorem exists_emb (pb : PowerBasis F M) (τ : F →+* ℂ) (z : ℂ) (hz : (minpoly F pb.gen).eval₂ τ z = 0) :
    ∃ e : M →+* ℂ, (∀ x, e (algebraMap F M x) = τ x) ∧ e pb.gen = z := by
  letI : Algebra F ℂ := τ.toAlgebra
  have h : Polynomial.aeval z (minpoly F pb.gen) = 0 := hz
  exact ⟨(pb.lift z h : M →ₐ[F] ℂ), fun x => (pb.lift z h).commutes x, pb.lift_gen z h⟩

theorem gen_ind (pb : PowerBasis F M) (q : M → Prop) (h0 : q pb.gen) (h1 : ∀ x, q (algebraMap F M x))
    (h2 : ∀ x y, q x → q y → q (x + y)) (h3 : ∀ x y, q x → q y → q (x * y)) (y : M) : q y := by
  have hy : y ∈ Algebra.adjoin F {pb.gen} := by rw [pb.adjoin_gen_eq_top]; trivial
  induction hy using Algebra.adjoin_induction with
  | mem x hx => rw [Set.mem_singleton_iff.1 hx]; exact h0
  | algebraMap r => exact h1 r
  | add x y _ _ hx hy => exact h2 x y hx hy
  | mul x y _ _ hx hy => exact h3 x y hx hy

theorem emb_ext (pb : PowerBasis F M) (e e' : M →+* ℂ) (h1 : ∀ x, e (algebraMap F M x) = e' (algebraMap F M x))
    (h0 : e pb.gen = e' pb.gen) : e = e' :=
  RingHom.ext (gen_ind pb (fun y => e y = e' y) h0 h1 (fun x y hx hy => by simp only [map_add, hx, hy])
    (fun x y hx hy => by simp only [map_mul, hx, hy]))

theorem emb_root (pb : PowerBasis F M) (e : M →+* ℂ) :
    (minpoly F pb.gen).eval₂ (e.comp (algebraMap F M)) (e pb.gen) = 0 := by
  rw [← Polynomial.hom_eval₂, ← Polynomial.aeval_def, minpoly.aeval, map_zero]

variable [NumberField F] [IsCMField F]

theorem ne_conj (τ : F →+* ℂ) (e e' : M →+* ℂ) (h : ∀ x, e (algebraMap F M x) = τ x)
    (h' : ∀ x, e' (algebraMap F M x) = τ x) : e ≠ ComplexEmbedding.conjugate e' := by
  intro he
  apply IsCMField.complexConj_ne_one F
  ext x
  apply τ.injective
  rw [IsCMField.complexEmbedding_complexConj, ← h' x]
  have := DFunLike.congr_fun he (algebraMap F M x)
  rw [ComplexEmbedding.conjugate_coe_eq] at this
  rw [← this, h]
  rfl

omit [NumberField F] [IsCMField F] in
theorem place_eq (v w : InfinitePlace F) (e e' : M →+* ℂ) (h : ∀ x, e (algebraMap F M x) = w.embedding x)
    (h' : ∀ x, e' (algebraMap F M x) = v.embedding x) (he : e = e' ∨ e = ComplexEmbedding.conjugate e') : w = v := by
  rw [← w.mk_embedding, ← v.mk_embedding]
  rcases he with he | he
  · congr 1
    ext x
    rw [← h, ← h', he]
  · rw [← InfinitePlace.mk_conjugate_eq v.embedding]
    congr 1
    ext x
    rw [← h, he, ComplexEmbedding.conjugate_coe_eq, ComplexEmbedding.conjugate_coe_eq, h']

end Field

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p}

theorem sh_mul (x y : G.C) : sh G (x * y) = sh G y * sh G x := by
  simp only [sh, map_mul, MulOpposite.unop_mul]

theorem sh_add (x y : G.C) : sh G (x + y) = sh G x + sh G y := by
  simp only [sh, map_add, MulOpposite.unop_add]

variable {M : Type} [Field M] [NumberField M] [Algebra G.F M]

theorem conj_law (P : Pair G) (pb : PowerBasis G.F M) (j : M →ₐ[G.F] G.C) (hj : j pb.gen = P.γ) (σ : M →+* M)
    (hσ : ∀ x : G.F, σ (algebraMap G.F M x) = algebraMap G.F M (IsCMField.complexConj G.F x))
    (hπ : σ pb.gen * pb.gen = ((P.c : ℚ) : M)) (y : M) : (P.β : G.C) * sh G (j y) = j (σ y) * P.β := by
  refine gen_ind pb (fun y => (P.β : G.C) * sh G (j y) = j (σ y) * P.β) ?_ ?_ ?_ ?_ y
  · have h1 : (P.γ : G.C) * j (σ pb.gen) = algebraMap ℚ G.C P.c := by
      rw [← hj, ← map_mul, mul_comm, hπ, IsScalarTower.algebraMap_apply ℚ G.F G.C, ← j.commutes]
      congr 1
      simp
    show (P.β : G.C) * sh G (j pb.gen) = j (σ pb.gen) * P.β
    apply P.γ.isUnit.mul_left_cancel
    rw [hj, ← mul_assoc, P.sim, ← mul_assoc, h1]
  · intro x
    show (P.β : G.C) * sh G (j (algebraMap G.F M x)) = j (σ (algebraMap G.F M x)) * P.β
    rw [hσ, j.commutes, j.commutes, sh, G.star_F, Algebra.commutes]
  · intro x y hx hy
    show (P.β : G.C) * sh G (j (x + y)) = j (σ (x + y)) * P.β
    rw [map_add, sh_add, mul_add, hx, hy, map_add, map_add, add_mul]
  · intro x y hx hy
    show (P.β : G.C) * sh G (j (x * y)) = j (σ (x * y)) * P.β
    rw [map_mul, sh_mul, ← mul_assoc, hy, mul_assoc, hx, ← mul_assoc, ← map_mul, ← map_mul, mul_comm y x]

omit [NumberField M] in
theorem comm_law (γ : G.C) (pb : PowerBasis G.F M) (j : M →ₐ[G.F] G.C) (hj : j pb.gen = γ) (y : G.C)
    (hy : y * γ = γ * y) (m : M) : y * j m = j m * y := by
  refine gen_ind pb (fun m => y * j m = j m * y) ?_ ?_ ?_ ?_ m
  · show y * j pb.gen = j pb.gen * y
    rw [hj, hy]
  · intro x
    show y * j (algebraMap G.F M x) = j (algebraMap G.F M x) * y
    rw [j.commutes, Algebra.commutes]
  · intro a b ha hb
    show y * j (a + b) = j (a + b) * y
    rw [map_add, mul_add, add_mul, ha, hb]
  · intro a b ha hb
    show y * j (a * b) = j (a * b) * y
    rw [map_mul, ← mul_assoc, ha, mul_assoc, hb, mul_assoc]

theorem triv_mul_inv (R : Type) [CommRing R] [Algebra ℚ R] (β β' : G.C) (x U : (R ⊗[ℚ] G.C)ˣ) (t : Rˣ)
    (hU : (U : R ⊗[ℚ] G.C) * inC G R β * (starT G.star R U).unop = inC G R β') (hx : Triv G R β x t) :
    Triv G R β' (x * U⁻¹) t := by
  unfold Triv at hx ⊢
  have h1 : (starT G.star R U).unop * (starT G.star R ((U⁻¹ : (R ⊗[ℚ] G.C)ˣ) : R ⊗[ℚ] G.C)).unop = 1 := by
    rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
  rw [← hx, ← hU, Units.val_mul, map_mul, MulOpposite.unop_mul]
  calc _ = (x : R ⊗[ℚ] G.C) * (((U⁻¹ : (R ⊗[ℚ] G.C)ˣ) : R ⊗[ℚ] G.C) * U) * inC G R β *
        ((starT G.star R U).unop * (starT G.star R ((U⁻¹ : (R ⊗[ℚ] G.C)ˣ) : R ⊗[ℚ] G.C)).unop) *
        (starT G.star R x).unop := by simp only [mul_assoc]
    _ = _ := by rw [h1, Units.inv_mul, mul_one, mul_one]

omit [NumberField M] in

theorem exists_basis (ha : G.a = 1) (P : Pair G) (μ : ℂ) (hm : P.Mark μ) (pb : PowerBasis G.F M)
    (hpol : P.pol = minpoly G.F pb.gen) (j : M →ₐ[G.F] G.C) (hj : j pb.gen = P.γ) (w : InfinitePlace G.F) :
    ∃ (Z : GL (Fin G.n) ℂ) (d : Fin G.n → ℝ) (e : Fin G.n → (M →+* ℂ)),
      (∀ i x, e i (algebraMap G.F M x) = w.embedding x) ∧ Function.Injective (fun i => e i pb.gen) ∧
      (∀ z : ℂ, P.pol.eval₂ w.embedding z = 0 → ∃ i, e i pb.gen = z) ∧
      (∀ y, G.psi w (j y) * (Z : Matrix (Fin G.n) (Fin G.n) ℂ) =
        (Z : Matrix (Fin G.n) (Fin G.n) ℂ) * Matrix.diagonal (fun i => e i y)) ∧ (∀ i, d i ≠ 0) ∧
      (Z : Matrix (Fin G.n) (Fin G.n) ℂ)ᴴ * (G.gram w * G.psi w ((P.β⁻¹ : G.Cˣ) : G.C)) *
        (Z : Matrix (Fin G.n) (Fin G.n) ℂ) = Matrix.diagonal (fun i => (d i : ℂ)) := by
  obtain ⟨Z, lam, hinj, hroot, hZ⟩ := GlobalTheory.T.exists_eigenbasis_psi_infinitePlace_distinct_roots p G P w
  have hr : ∀ i, P.pol.eval₂ w.embedding (lam i) = 0 := fun i => (hroot _).2 ⟨i, rfl⟩
  choose e he he' using fun i => exists_emb pb w.embedding (lam i) (hpol ▸ hr i)
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.similitudePair_hermitianForm_invertible_similitude p G P w
  obtain ⟨d, hd, hD⟩ := GlobalTheory.T.exists_diagonal_congr_of_similitude_distinct_eigenvalues _ (G.psi w P.γ) ((P.c : ℚ) : ℝ) Z lam h1 h2
    (by exact_mod_cast P.c.ne_zero) (by rw [h3]; simp) hinj
    (fun i => GlobalTheory.T.marked_similitude_pair_minpoly_roots_normSq_eq p G P μ ha hm _ _ (hr i)) hZ
  have hl : (fun i => e i pb.gen) = lam := funext he'
  refine ⟨Z, d, e, he, hl ▸ hinj, fun z hz => ?_, fun y => ?_, hd, hD⟩
  · obtain ⟨i, hi⟩ := (hroot z).1 hz
    exact ⟨i, (he' i).trans hi⟩
  · refine gen_ind pb (fun y => G.psi w (j y) * (Z : Matrix (Fin G.n) (Fin G.n) ℂ) =
        (Z : Matrix (Fin G.n) (Fin G.n) ℂ) * Matrix.diagonal (fun i => e i y)) ?_ ?_ ?_ ?_ y
    · show G.psi w (j pb.gen) * _ = _
      rw [hj, hl, hZ]
    · intro x
      show G.psi w (j (algebraMap G.F M x)) * _ = _
      simp only [he]
      rw [j.commutes, G.psi_F]
      exact (Matrix.scalar_commute _ (fun _ => Commute.all _ _) _).eq
    · intro a b h h'
      show G.psi w (j (a + b)) * _ = _
      simp only [map_add]
      rw [Matrix.add_mul, h, h', ← Matrix.mul_add, Matrix.diagonal_add]
    · intro a b h h'
      show G.psi w (j (a * b)) * _ = _
      simp only [map_mul]
      rw [Matrix.mul_assoc, h', ← Matrix.mul_assoc, h, Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]

end GlobalTheory.LKMid.MoveMark

namespace GlobalTheory.LKMid

end GlobalTheory.LKMid
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiformHeightLowerBound
section
set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.HtLowProof

theorem eval_blockScale_multi {B N : ℕ} {a : Fin B → ℕ} {h : MvPolynomial (Fin B × Fin N) ℂ}
    (hh : IsMultiHomogeneous a h) (r : Fin B → ℂ) (v : Fin B × Fin N → ℂ) :
    eval (fun q => r q.1 * v q) h = (∏ i, r i ^ a i) * eval v h := by
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hr : ∏ q : Fin B × Fin N, r q.1 ^ s q = ∏ i, r i ^ a i := by
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun i _ => ?_
    show ∏ y, r i ^ s (i, y) = _
    rw [Finset.prod_pow_eq_pow_sum, hh s hs i]
  simp_rw [mul_pow, Finset.prod_mul_distrib, hr]
  ring

theorem frameNorm_sum_le {N n : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (c : Fin n → ℂ) (u : Fin n → Fin N → ℂ)
    (Λ : ℝ) (hc : ∀ k, ‖c k‖ ≤ 1) (hu : ∀ k, frameNorm A (u k) ≤ Λ) :
    frameNorm A (∑ k, c k • u k) ≤ n * Λ := by
  let T : (Fin N → ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin N) :=
    (WithLp.linearEquiv 2 ℂ (Fin N → ℂ)).symm.toLinearMap ∘ₗ A⁻¹.mulVecLin
  have hT : ∀ z, frameNorm A z = ‖T z‖ := fun z => by
    rw [frameNorm, EuclideanSpace.norm_eq]; rfl
  rw [hT, map_sum]
  refine (norm_sum_le _ _).trans ?_
  calc _ ≤ ∑ _k : Fin n, Λ := Finset.sum_le_sum fun k _ => by
        rw [map_smul, norm_smul, ← hT]
        exact (mul_le_of_le_one_left (GlobalTheory.MaxPoint.frameNorm_nonneg' _ _) (hc k)).trans (hu k)
    _ = n * Λ := by simp

theorem norm_eval_le {B N : ℕ} {a : Fin B → ℕ} {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.det ≠ 0) (hN : 0 < N)
    {h : MvPolynomial (Fin B × Fin N) ℂ} (hh : IsMultiHomogeneous a h) (R : ℝ) (hR : 0 ≤ R)
    (u : Fin B × Fin N → ℂ) (hu : ∀ i, frameNorm A (fun j => u (i, j)) ≤ R) :
    ‖eval u h‖ ≤ Real.exp (blockSphereMean B N (linSubst A h) + (∑ i, (a i : ℝ)) * (harmonic (N - 1) : ℝ) / 2) *
      R ^ (∑ i, a i) := by
  set r : Fin B → ℝ := fun i => frameNorm A (fun j => u (i, j)) with hr
  have hr0 : ∀ i, 0 ≤ r i := fun i => GlobalTheory.MaxPoint.frameNorm_nonneg' _ _
  set e : Fin N → ℂ := A.mulVec (Pi.single ⟨0, hN⟩ 1) with he'
  have he : frameNorm A e = 1 := by
    rw [he', GlobalTheory.MaxPoint.frameNorm_mulVec hA]
    rw [Finset.sum_eq_single (⟨0, hN⟩ : Fin N) (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp)]
    simp
  let p : Fin B × Fin N → ℂ := fun q => if r q.1 = 0 then e q.2 else ((r q.1)⁻¹ : ℂ) * u q
  have hp : ∀ i, frameNorm A (fun j => p (i, j)) = 1 := fun i => by
    by_cases h0 : r i = 0
    · have : (fun j => p (i, j)) = e := by funext j; simp [p, h0]
      rw [this, he]
    · have : (fun j => p (i, j)) = ((r i)⁻¹ : ℂ) • (fun j => u (i, j)) := by
        funext j; simp [p, h0]
      rw [this, GlobalTheory.MaxPoint.frameNorm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (hr0 i)]
      exact inv_mul_cancel₀ h0
  have hup : u = fun q => ((r q.1 : ℝ) : ℂ) * p q := by
    funext q
    by_cases h0 : r q.1 = 0
    · have hz : (fun j => u (q.1, j)) = 0 := GlobalTheory.MaxPoint.eq_zero_of_frameNorm_eq_zero hA h0
      have := congrFun hz q.2
      simp only [Pi.zero_apply] at this
      simp [h0, this]
    · simp only [p, if_neg h0]
      rw [← mul_assoc, ← Complex.ofReal_inv, ← Complex.ofReal_mul, mul_inv_cancel₀ h0, Complex.ofReal_one, one_mul]
  have hval : ‖eval u h‖ = (∏ i, r i ^ a i) * ‖eval p h‖ := by
    rw [hup, eval_blockScale_multi hh (fun i => ((r i : ℝ) : ℂ)) p, norm_mul, norm_prod]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg (hr0 i)]
  have hprod : ∏ i, r i ^ a i ≤ R ^ (∑ i, a i) := by
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_le_prod (fun i _ => pow_nonneg (hr0 i) _) fun i _ => pow_le_pow_left₀ (hr0 i) (hu i) _
  rw [hval]
  by_cases hz : eval p h = 0
  · rw [hz, norm_zero, mul_zero]
    exact mul_nonneg (Real.exp_pos _).le (pow_nonneg hR _)
  · have harch := GlobalTheory.T.log_eval_sub_le_blockSphereMean_multidegree B N a A h hA hh p hp hz
    have hle : ‖eval p h‖ ≤ Real.exp (blockSphereMean B N (linSubst A h) +
        (∑ i, (a i : ℝ)) * (harmonic (N - 1) : ℝ) / 2) := by
      rw [← Real.exp_log (norm_pos_iff.2 hz)]
      exact Real.exp_le_exp.2 (by linarith)
    rw [mul_comm]
    exact mul_le_mul hle hprod (Finset.prod_nonneg fun i _ => pow_nonneg (hr0 i) _) (Real.exp_pos _).le

theorem eval₂_linSubst {F : Type} [Field F] {B N n : ℕ} (s : F →+* ℂ) (w : Matrix (Fin N) (Fin n) F)
    (G : MvPolynomial (Fin B × Fin N) F) (z : Fin B × Fin n → ℂ) :
    eval₂ s z (linSubst w G) = eval (fun q => ∑ k, z (q.1, k) * s (w q.2 k)) (MvPolynomial.map s G) := by
  have e : ((eval₂Hom s z).comp (aeval (fun p : Fin B × Fin N => ∑ k, C (w p.2 k) * X (p.1, k)) :
      MvPolynomial (Fin B × Fin N) F →ₐ[F] MvPolynomial (Fin B × Fin n) F).toRingHom) =
      (eval (fun q => ∑ k, z (q.1, k) * s (w q.2 k))).comp (MvPolynomial.map s) := by
    refine MvPolynomial.ringHom_ext (fun c => by simp) (fun q => ?_)
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X, map_sum, map_mul,
      coe_eval₂Hom, eval₂_C, eval₂_X, map_X, eval_X]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  exact RingHom.congr_fun e G

theorem htLow : HtLow := by
  intro F _ _ B N n w A Λ hL a G hG ha
  obtain ⟨P, hP⟩ := GlobalTheory.HeightUnique.exists_right_inv hL.spans
  have hk : linSubst w G ≠ 0 := GlobalTheory.HeightUnique.linSubst_ne_zero hP hG
  have hNn : N ≤ n := by
    have h1 := finrank_range_le_card (R := F) w.col
    unfold Set.finrank at h1
    rw [hL.spans, finrank_top, Module.finrank_fin_fun, Fintype.card_fin] at h1
    exact h1
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (hL.pos.trans_le hNn)
  have hnΛ : (0 : ℝ) < n * Λ := mul_pos (by linarith) (by linarith [hL.one_le])
  set deg : ℝ := ∑ b, (a b : ℝ) with hdeg
  set H : ℝ := (harmonic (N - 1) : ℝ) with hH
  set m : (F →+* ℂ) → ℝ := fun σ => blockSphereMean B N (linSubst (A σ) (MvPolynomial.map σ G)) with hm
  have key := GlobalTheory.HSFloor.floor F (Fin B × Fin n) (linSubst w G)
    (fun s => Real.exp (m s + deg * H / 2) * ((n : ℝ) * Λ) ^ (∑ b, a b)) hk (fun s z hz => by
      rw [eval₂_linSubst]
      refine norm_eval_le (hL.det s) hL.pos (isMultiHomogeneous_map_ring a G ha s) _ hnΛ.le _ fun i => ?_
      have e : (fun j => ∑ k, z (i, k) * s (w j k)) = ∑ k, z (i, k) • (fun j => s (w j k)) := by
        funext j; simp [Finset.sum_apply]
      rw [e]
      exact frameNorm_sum_le _ _ _ Λ (fun k => hz _) fun k => hL.le k s)
  have hd : (0 : ℝ) < Module.finrank ℚ F := Nat.cast_pos.2 Module.finrank_pos
  have hcard : (Fintype.card (F →+* ℂ) : ℝ) = Module.finrank ℚ F := by
    rw [NumberField.Embeddings.card]
  have hlog : ∀ s, Real.log (Real.exp (m s + deg * H / 2) * ((n : ℝ) * Λ) ^ (∑ b, a b)) =
      m s + (deg * H / 2 + deg * Real.log (n * Λ)) := fun s => by
    rw [Real.log_mul (Real.exp_pos _).ne' (pow_pos hnΛ _).ne', Real.log_exp, Real.log_pow, hdeg]
    push_cast
    ring
  have hmean : mean F (fun s => Real.log (Real.exp (m s + deg * H / 2) * ((n : ℝ) * Λ) ^ (∑ b, a b))) =
      mean F m + (deg * H / 2 + deg * Real.log (n * Λ)) := by
    simp only [hlog, mean, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
    field_simp
  have hht : ht w A G = finPart (linSubst w G) + mean F m := by
    simp only [ht, formHeight, finPart, mean, hm]
    simp only [Nat.cast_zero, mul_zero, zero_mul, zero_div, add_zero]
    rw [add_div]
  have hHle : H ≤ Real.log n + 1 := by
    have h1 : H ≤ 1 + Real.log ((N - 1 : ℕ) : ℝ) := by
      rw [hH]; exact_mod_cast harmonic_le_one_add_log (N - 1)
    have h2 : Real.log ((N - 1 : ℕ) : ℝ) ≤ Real.log n := by
      rcases Nat.eq_zero_or_pos (N - 1) with h0 | h0
      · rw [h0, Nat.cast_zero, Real.log_zero]; exact Real.log_nonneg hn1
      · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast (by omega : N - 1 ≤ n))
    linarith
  have hdeg0 : 0 ≤ deg := Finset.sum_nonneg fun b _ => Nat.cast_nonneg _
  rw [hmean] at key
  rw [hht, cst]
  nlinarith [mul_le_mul_of_nonneg_left hHle hdeg0]

end GlobalTheory.HtLowProof
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicityOneStatement
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multOne' : GlobalTheory.RealLift.MultOne := by
  first | exact @GlobalTheory.SteepMult.multOne | exact GlobalTheory.SteepMult.multOne | (intros; apply GlobalTheory.SteepMult.multOne <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonsplitUnitaryGroupIsoGlStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.EulerTw
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonsplit_unitary_group_iso_gl : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (u : Pl E), ¬ IsSplitAt u → ∃ e : GlobalTheory.EulerTw.Gam E n u ≃ₜ* GLw n u, ∀ g, e g = GeneralLinearGroup.map (pLoc E u) g.1 := by
  first | exact @GlobalTheory.EulerTw.GamInert.main | exact GlobalTheory.EulerTw.GamInert.main | (intros; apply GlobalTheory.EulerTw.GamInert.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedMatrixIntegralCompLinearEquivDet
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open MeasureTheory

theorem GlobalTheory.LeviDesc.hint_comp_linear : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (a b : ℕ) (L : Matrix (Fin a) (Fin b) (w.adicCompletion E) →ₗ[w.adicCompletion E] Matrix (Fin a) (Fin b) (w.adicCompletion E)) (φ : Matrix (Fin a) (Fin b) (w.adicCompletion E) → ℂ), LinearMap.det L ≠ 0 → (∃ U : AddSubgroup (Matrix (Fin a) (Fin b) (w.adicCompletion E)), IsOpen (U : Set (Matrix (Fin a) (Fin b) (w.adicCompletion E))) ∧ ∀ x, ∀ y ∈ U, φ (x + y) = φ x) → HasCompactSupport φ → hint (intMat a b w) (fun X => φ (L (Multiplicative.toAdd X))) = (absHalf w (LinearMap.det L) ^ 2)⁻¹ * hint (intMat a b w) (fun X => φ (Multiplicative.toAdd X)) := by
  intro E _ _ w a b L φ hL hU hc
  obtain ⟨Λ, hΛo, hΛc, hΛ⟩ := GlobalTheory.T.exists_open_compact_integralMatrixAddSubgroup E w a b
  obtain ⟨hU', hc', hlc⟩ := GlobalTheory.T.comp_linearAut_locallyConstant_compactSupport_matrix E w a b L φ hL hU hc
  letI : MeasurableSpace (Matrix (Fin a) (Fin b) (w.adicCompletion E)) := borel _
  haveI : BorelSpace (Matrix (Fin a) (Fin b) (w.adicCompletion E)) := ⟨rfl⟩
  let μ : Measure (Matrix (Fin a) (Fin b) (w.adicCompletion E)) := Measure.addHaar
  have hμ : μ.IsAddHaarMeasure := inferInstance
  rw [hΛ, GlobalTheory.T.haarIntegralNormalizedOpenCompact_eq_integral_div _ μ hμ Λ hΛo hΛc _ hU' hc', GlobalTheory.T.haarIntegralNormalizedOpenCompact_eq_integral_div _ μ hμ Λ hΛo hΛc _ hU hc,
    GlobalTheory.T.integral_comp_linearMap_matrix_nonarchLocalField _ a b L hL φ μ hμ, GlobalTheory.T.adicCompletion_distribHaarChar_eq_absHalf_sq E w _ hL]
  ring
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneParamSubgroupGeneratorsExistStatement
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oneParamSubgroup_generators_exist : GlobalTheory.RealLift.GenEx := by
  first | exact @GlobalTheory.RealLiftGen.genEx | exact GlobalTheory.RealLiftGen.genEx | (intros; apply GlobalTheory.RealLiftGen.genEx <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalIntegralTestFunctionFirst
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
theorem _root_.GlobalTheory.T.orbital_integral_test_function_first : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ v : InfinitePlace G.F, sigPosH (G.gram_herm v) = 1 → ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), (∀ (y : grp G β) (h : G.GAf), f (h⁻¹ * toAfF G β x t hx y * h) ≠ 0 → (∃ z : Fin G.n → ℂ, 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re ∧ FixL G v β y z) → (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n ∧ (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable) → sh G β = β → (∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) → ∀ P : Polynomial G.F, ∃ Y : Finset (grp G β), ∀ y : grp G β, minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = P → (∃ a : Dat G v β, FixL G v β y a.2.1 ∧ f (a.1.1⁻¹ * toAfF G β x t hx y * a.1.1) * f' (a.1.2⁻¹ * toP1 G β y * a.1.2) ≠ 0) → ∃ y₀ ∈ Y, ∃ γ : grp G β, y = γ * y₀ * γ⁻¹ := by
  first | exact @GlobalTheory.LKCx.ClsReg.classes_finite | exact GlobalTheory.LKCx.ClsReg.classes_finite
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialLTrivialRepTwistEqProdHeckeL
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.RallisEuler

open GlobalTheory.LFun in

theorem trivPar_euler : ∀ {D : D7} (χ : (AE D)ˣ →* Circle) (Sf : Finset (FinPl D)) (n : ℕ), GlobalTheory.LFun.UnrOff χ (Sf : Set (FinPl D)) → EqRight (fun s => ∏ i ∈ Finset.range n, GlobalTheory.LFun.charL χ⁻¹ (Sf : Set (FinPl D)) (s + (n : ℂ) / 2 - i)) (fun s => GlobalTheory.LFun.LSD D Sf (GlobalTheory.BottomRallis.trivPar n) χ (s + 1 / 2)) := by
  intro D χ Sf n hU
  refine ⟨(n : ℝ) / 2 + 1, fun s hs => ?_⟩
  have hs' : (n : ℝ) / 2 + 1 < s.re := hs
  set T := above D.host.E (Sf : Set (FinPl D)) with hT

  have hc : ∀ i ∈ Finset.range n, HasProd (fun w : {w // w ∉ T} => locL (charFam χ⁻¹) w.1 (s + (n : ℂ) / 2 - i))
      (charL χ⁻¹ (Sf : Set (FinPl D)) (s + (n : ℂ) / 2 - i)) := by
    intro i hi
    have hi' : (i : ℝ) + 1 ≤ n := by exact_mod_cast Finset.mem_range.1 hi
    refine (converges_charFam T χ⁻¹ ?_).hasProd
    simp
    linarith
  have hp := hasProd_prod hc
  show (∏ i ∈ Finset.range n, charL χ⁻¹ (Sf : Set (FinPl D)) (s + (n : ℂ) / 2 - i)) =
    LSD D Sf (GlobalTheory.BottomRallis.trivPar n) χ (s + 1 / 2)
  rw [← hp.tprod_eq]
  unfold LSD LSTw LS eulerProd
  refine tprod_congr fun w => ?_
  have hw : UnrAt χ⁻¹ w.1 := (hU w.1 w.2).inv
  rw [GlobalTheory.BottomRallis.trivPar, twist_segFam, locL_segFam']
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [locL, locL, charFam_of_unrAt hw, val_inv]
  congr 2
  · simp
  · congr 1
    push_cast
    ring

end GlobalTheory.RallisEuler
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLieElementsGenerateOneParamLinesStatement
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryLieElements_generate_oneParamLines : GlobalTheory.RealLift.LineEx := by
  first | exact @GlobalTheory.RealLift.exists_line_of_upq | exact GlobalTheory.RealLift.exists_line_of_upq | (intros; apply GlobalTheory.RealLift.exists_line_of_upq <;> assumption)
end

