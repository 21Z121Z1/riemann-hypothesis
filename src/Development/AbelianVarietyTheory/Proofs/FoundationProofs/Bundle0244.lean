import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0013
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
import Formalism.GradedWeylDivisibility.StatementE
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.Bundle0001
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0012
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0227
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0230

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MonomialDerivCauchyBoundGaussianGrowth
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.GaussCauchy

theorem factor_le (A B : ℝ) (hA : 0 < A) (n : ℕ) (hn : (n : ℝ) ≤ 2 * B) :
    ((n.factorial : ℝ)) ^ 2 * Real.exp n / (A * n / Real.pi) ^ n
      ≤ (2 * Real.exp 1 * Real.pi * B / A) ^ n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  have hn0 : (0 : ℝ) < n := by exact_mod_cast h
  have hpi := Real.pi_pos
  rw [div_le_iff₀ (by positivity), ← mul_pow]
  have h1 : 2 * Real.exp 1 * Real.pi * B / A * (A * n / Real.pi) = (2 * B) * n * Real.exp 1 := by
    field_simp
  have h2 : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
  have h3 : (n : ℝ) ^ n ≤ (2 * B) ^ n := pow_le_pow_left₀ hn0.le hn n
  rw [h1, mul_pow, mul_pow (2 * B), ← Real.exp_nat_mul, mul_one, sq]
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  exact mul_le_mul (h2.trans h3) h2 (by positivity) ((by positivity : (0 : ℝ) ≤ (n : ℝ) ^ n).trans h3)

theorem pderivIter_sq_le {ι : Type*} [DecidableEq ι] [Fintype ι] (F : (ι → ℂ) → ℂ) (S A B : ℝ)
    (hA : 0 < A) (hS : 0 ≤ S) (hF : Differentiable ℂ F)
    (hb : ∀ z, ‖F z‖ ^ 2 ≤ S * Real.exp (Real.pi * (∑ k, ‖z k‖ ^ 2) / A))
    (α : ι →₀ ℕ) (hα : ∀ k, (α k : ℝ) ≤ 2 * B) :
    ‖pderivIter α F 0‖ ^ 2 ≤ S * (2 * Real.exp 1 * Real.pi * B / A) ^ (∑ k, α k) := by
  have hpi := Real.pi_pos
  have hsq : ∀ k, Real.sqrt (A * α k / Real.pi) ^ 2 = A * α k / Real.pi := fun k =>
    Real.sq_sqrt (by positivity)
  have h := norm_pderivIter_le_of_differentiable (F := F) (a := 0)
    (r := fun k => Real.sqrt (A * α k / Real.pi))
    (M := Real.sqrt (S * Real.exp (∑ k, (α k : ℝ)))) α (fun k => Real.sqrt_nonneg _)
    (fun k hk => by
      have : (0 : ℝ) < α k := by exact_mod_cast Nat.pos_of_ne_zero hk
      exact Real.sqrt_pos.mpr (by positivity)) hF
    (fun z hz => by
      apply Real.le_sqrt_of_sq_le
      refine (hb z).trans (le_of_eq ?_)
      congr 2
      simp only [Pi.zero_apply, sub_zero] at hz
      simp only [hz, hsq, Finset.mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun k _ => ?_
      field_simp)
  refine (pow_le_pow_left₀ (norm_nonneg _) h 2).trans ?_
  rw [div_pow, mul_pow, Real.sq_sqrt (by positivity), ← Finset.prod_pow, ← Finset.prod_pow,
    Real.exp_sum, ← Finset.prod_pow_eq_pow_sum, mul_left_comm, mul_div_assoc,
    ← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
  refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun k _ => by positivity) fun k _ => ?_) hS
  rw [← pow_mul, mul_comm (α k) 2, pow_mul, hsq]
  exact factor_le A B hA _ (hα k)

noncomputable def curry (D : D7) (N N' : ℕ) :
    (D.what₂.Tau × Fin N' × Fin N → ℂ) →ₗ[ℂ] VC D N N' where
  toFun w := fun τ i j => w (τ, i, j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem curry_single (D : D7) (N N' : ℕ) (k : D.what₂.Tau × Fin N' × Fin N) :
    curry D N N' (Pi.single k 1) = coordV D k := by
  funext τ i j
  obtain ⟨a, b, c⟩ := k
  simp [curry, coordV, Pi.single_apply, Prod.ext_iff]

theorem factorial_mul_taylor (D : D7) (N N' : ℕ) (G : VC D N N' → ℂ) (hG : Differentiable ℂ G)
    (α : Mono D N N') :
    (α.prod fun _ n => (n.factorial : ℂ)) * taylor D G α
      = pderivIter α (fun w => G (curry D N N' w)) 0 := by
  have hne : (α.prod fun _ n => (n.factorial : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have han : AnalyticAt ℂ G 0 := SCV.analyticOnNhd_of_differentiable hG Set.univ 0 (Set.mem_univ _)
  rw [taylor, mul_div_cancel₀ _ hne, pderivIter, pderivList, lineDerivList_comp_linearMap,
    ← lineDerivList_ofFn han]
  simp only [map_zero, List.map_map]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [curry_single]

theorem monomial_deriv_bound : ∀ (D : D7) (N N' : ℕ) (G : VC D N N' → ℂ) (S A B : ℝ), 0 < A → 1 ≤ B → 0 ≤ S → Differentiable ℂ G → (∀ z, ‖G z‖ ^ 2 ≤ S * Real.exp (Real.pi * (∑ τ, ∑ i, ∑ j, ‖z τ i j‖ ^ 2) / A)) → ∀ α : Mono D N N', (∀ k, (α k : ℝ) ≤ 2 * B) → ‖(α.prod fun _ n => (n.factorial : ℂ)) * taylor D G α‖ ^ 2 ≤ S * (2 * Real.exp 1 * Real.pi * B / A) ^ (α.sum fun _ n => n) := by
  intro D N N' G S A B hA _ hS hG hb α hα
  rw [factorial_mul_taylor D N N' G hG, Finsupp.sum_fintype _ _ (fun _ => rfl)]
  refine pderivIter_sq_le _ S A B hA hS
    (hG.comp (LinearMap.toContinuousLinearMap (curry D N N')).differentiable) (fun z => ?_) α hα
  simp only [Fintype.sum_prod_type]
  exact hb (curry D N N' z)

end GlobalTheory.GaussCauchy
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVSubRight
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Matrix

noncomputable section

namespace GlobalTheory.RatEqui

variable (D : D7) {N N' : ℕ}

theorem embT_conj (τ : D.what₂.Tau) (x : D.host.E) :
    embT D τ (D.host.conj x) = (starRingEnd ℂ) (embT D τ x) :=
  Formalism.HC.HostAx.conjE_apply D.host.toHostAx _ _

def adj {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E :=
  (M.map D.host.conj).transpose

theorem adj_map {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E) (τ : D.what₂.Tau) :
    (adj D M).map (embT D τ) = (M.map (embT D τ))ᴴ := by
  ext i j
  simp [adj, embT_conj]

def mulV (M' : Matrix (Fin N') (Fin N') D.host.E) (M : Matrix (Fin N) (Fin N) D.host.E) :
    VC D N N' →ₗ[ℂ] VC D N N' where
  toFun z := fun τ => (M'.map (embT D τ) * Matrix.of (z τ) * M.map (embT D τ) : Matrix _ _ ℂ)
  map_add' z w := by
    funext τ
    change M'.map (embT D τ) * (Matrix.of (z τ) + Matrix.of (w τ)) * M.map (embT D τ) = _
    rw [Matrix.mul_add, Matrix.add_mul]; rfl
  map_smul' c z := by
    funext τ
    change M'.map (embT D τ) * (c • Matrix.of (z τ)) * M.map (embT D τ) = _
    rw [Matrix.mul_smul, Matrix.smul_mul]; rfl

theorem mulV_apply (M' : Matrix (Fin N') (Fin N') D.host.E) (M : Matrix (Fin N) (Fin N) D.host.E)
    (z : VC D N N') (τ : D.what₂.Tau) :
    mulV D M' M z τ = (M'.map (embT D τ) * Matrix.of (z τ) * M.map (embT D τ) : Matrix _ _ ℂ) := rfl

theorem mulV_mulV (M₁' M₂' : Matrix (Fin N') (Fin N') D.host.E) (M₁ M₂ : Matrix (Fin N) (Fin N) D.host.E)
    (z : VC D N N') : mulV D M₁' M₁ (mulV D M₂' M₂ z) = mulV D (M₁' * M₂') (M₂ * M₁) z := by
  funext τ
  change M₁'.map (embT D τ) * (M₂'.map (embT D τ) * Matrix.of (z τ) * M₂.map (embT D τ)) * M₁.map (embT D τ) =
    (M₁' * M₂').map (embT D τ) * Matrix.of (z τ) * (M₂ * M₁).map (embT D τ)
  simp only [Matrix.map_mul, Matrix.mul_assoc]

theorem mulV_one (z : VC D N N') : mulV D 1 1 z = z := by
  funext τ
  rw [mulV_apply, Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.one_mul, Matrix.mul_one]
  rfl

theorem mulV_sub_left (M₁' M₂' : Matrix (Fin N') (Fin N') D.host.E) (M : Matrix (Fin N) (Fin N) D.host.E)
    (z : VC D N N') : mulV D (M₁' - M₂') M z = mulV D M₁' M z - mulV D M₂' M z := by
  funext τ
  change (M₁' - M₂').map (embT D τ) * Matrix.of (z τ) * M.map (embT D τ) =
    M₁'.map (embT D τ) * Matrix.of (z τ) * M.map (embT D τ) - M₂'.map (embT D τ) * Matrix.of (z τ) * M.map (embT D τ)
  rw [Matrix.map_sub _ (map_sub _), Matrix.sub_mul, Matrix.sub_mul]

theorem mulV_sub_right (M' : Matrix (Fin N') (Fin N') D.host.E) (M₁ M₂ : Matrix (Fin N) (Fin N) D.host.E)
    (z : VC D N N') : mulV D M' (M₁ - M₂) z = mulV D M' M₁ z - mulV D M' M₂ z := by
  funext τ
  change M'.map (embT D τ) * Matrix.of (z τ) * (M₁ - M₂).map (embT D τ) =
    M'.map (embT D τ) * Matrix.of (z τ) * M₁.map (embT D τ) - M'.map (embT D τ) * Matrix.of (z τ) * M₂.map (embT D τ)
  rw [Matrix.map_sub _ (map_sub _), Matrix.mul_sub]

theorem Hf_eq_trace (T : Tor D) (z w : VC D N N') :
    Hf D T z w = (∑ τ, Matrix.trace (Matrix.of (z τ) * (Matrix.of (w τ))ᴴ)) / (area T.abelian₂ : ℂ) := by
  simp [Hf, Matrix.trace, Matrix.mul_apply]

theorem Hf_mulV (T : Tor D) (M' : Matrix (Fin N') (Fin N') D.host.E) (M : Matrix (Fin N) (Fin N) D.host.E)
    (z w : VC D N N') : Hf D T (mulV D M' M z) w = Hf D T z (mulV D (adj D M') (adj D M) w) := by
  rw [Hf_eq_trace, Hf_eq_trace]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  change Matrix.trace (M'.map (embT D τ) * Matrix.of (z τ) * M.map (embT D τ) * (Matrix.of (w τ))ᴴ) =
    Matrix.trace (Matrix.of (z τ) * ((adj D M').map (embT D τ) * Matrix.of (w τ) * (adj D M).map (embT D τ))ᴴ)
  rw [adj_map, adj_map, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem pull_eq (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (γ : Matrix (Fin N) (Fin N) D.host.E)
    (γ' : Matrix (Fin N') (Fin N') D.host.E) (G : VC D N N' → ℂ) :
    pull D (tor0 D cc δ) γ γ' G = fun z => G (mulV D (adj D γ') γ z) := by
  funext z
  unfold pull
  congr 1
  funext τ
  rw [mulV_apply, adj_map]
  rfl

theorem mulV_pt (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M' : Matrix (Fin N') (Fin N') D.host.E)
    (M : Matrix (Fin N) (Fin N) D.host.E) (z : Matrix (Fin N') (Fin N) D.host.E) :
    mulV D M' M (pt D (tor0 D cc δ) δ z) = pt D (tor0 D cc δ) δ (M' * z * M) := by
  unfold pt
  rw [map_smul]
  congr 1
  funext τ
  change M'.map (embT D τ) * z.map (embT D τ) * M.map (embT D τ) = (M' * z * M).map (embT D τ)
  simp only [Matrix.map_mul]

theorem adj_mul {n : ℕ} (M₁ M₂ : Matrix (Fin n) (Fin n) D.host.E) : adj D (M₁ * M₂) = adj D M₂ * adj D M₁ := by
  unfold adj
  rw [← Matrix.transpose_mul]
  congr 1
  exact Matrix.map_mul (f := (D.host.conj : D.host.E →+* D.host.E))

theorem adj_one {n : ℕ} : adj D (1 : Matrix (Fin n) (Fin n) D.host.E) = 1 := by
  unfold adj
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]

end GlobalTheory.RatEqui
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NegRankMulLogLeLogCovolumeHermitian
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.LcvSub

theorem cnorm_sq_eq {ι : Type} [Fintype ι] (u : ι → ℂ) :
    ((∑ i, ‖u i‖ ^ 2 : ℝ) : ℂ) = star u ⬝ᵥ u := by
  simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul']
  push_cast
  rfl

theorem cnorm_mulVec_eq {m n k : Type} [Fintype m] [Fintype n] [Fintype k]
    (A : Matrix m k ℂ) (B : Matrix n k ℂ) (h : Aᴴ * A = Bᴴ * B) (u : k → ℂ) :
    Formalism.HermitianLatticesTheory.cnorm (A *ᵥ u) = Formalism.HermitianLatticesTheory.cnorm (B *ᵥ u) := by
  unfold Formalism.HermitianLatticesTheory.cnorm
  congr 1
  apply Complex.ofReal_injective
  rw [cnorm_sq_eq, cnorm_sq_eq, Matrix.star_mulVec, Matrix.star_mulVec,
    ← Matrix.dotProduct_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, h]

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem fcoord_std {d : ℕ} (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (v : InfinitePlace K)
    (x : Fin d → K) :
    Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K (Fin d)) X v x = (X v)⁻¹ *ᵥ (fun i => v.embedding (x i)) := by
  unfold Formalism.HermitianLatticesTheory.fcoord
  congr 1

theorem gram_eq {d j : ℕ} (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (v : InfinitePlace K)
    (e : Fin j → Fin d → K) :
    gram X v e = ((X v)⁻¹ * ((Matrix.of e)ᵀ.map v.embedding))ᴴ *
      ((X v)⁻¹ * ((Matrix.of e)ᵀ.map v.embedding)) := by
  ext a b
  simp only [gram, Formalism.HN.gramPl, Formalism.HermitianLatticesTheory.majAt, fcoord_std, Matrix.of_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.mulVec, dotProduct, Matrix.map_apply,
    Matrix.transpose_apply]

theorem gram_single {d : ℕ} (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (v : InfinitePlace K) :
    gram X v (fun i => (Pi.single i 1 : Fin d → K)) = ((X v)⁻¹)ᴴ * (X v)⁻¹ := by
  have h : (Matrix.of (fun i => (Pi.single i 1 : Fin d → K)))ᵀ.map v.embedding = 1 := by
    ext a b
    by_cases hab : a = b
    · subst hab; simp
    · simp [hab, Matrix.one_apply]
  rw [gram_eq, h, Matrix.mul_one]

end GlobalTheory.LcvSub

open GlobalTheory.LcvSub in

theorem GlobalTheory.neg_rank_mul_log_le_lcv : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (v₀ : InfinitePlace K), IsConjAt v₀ → ∀ (d : ℕ) (H : Matrix (Fin d) (Fin d) K) (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ), IsRatHerm (cmMax K) H X → ∀ (s : ℕ), 0 < s → ∀ L : Submodule (𝓞 K) (Fin d → K), L.FG → (∀ x ∈ L, ∀ y ∈ L, (s : K) * (star x ⬝ᵥ H *ᵥ y) ∈ (algebraMap (𝓞 K) K).range) → -((Formalism.HN.rkK L : ℝ) * Real.log s) ≤ lcv X L := by
  intro K _ _ _ _ v₀ hv₀ d H X hH s hs L hL hint
  classical
  set j := Formalism.HN.rkK L with hj
  let W : Submodule K (Fin d → K) := Submodule.span K (L : Set (Fin d → K))
  let b : Module.Basis (Fin j) K W := Module.finBasis K W
  let e : Fin j → Fin d → K := fun a => (b a : Fin d → K)
  have he : LinearIndependent K e := b.linearIndependent.map' W.subtype W.ker_subtype
  let ψ : (Fin j → K) →ₗ[K] (Fin d → K) := W.subtype ∘ₗ b.equivFun.symm.toLinearMap
  have hψ : Function.Injective ψ := W.injective_subtype.comp b.equivFun.symm.injective
  have hψE : ∀ x, ψ x = (Matrix.of e)ᵀ *ᵥ x := by
    intro x
    ext i
    simp [ψ, e, Matrix.mulVec, dotProduct, mul_comm]
  have hrange : LinearMap.range ψ = W := by
    simp [ψ, LinearMap.range_comp]
  obtain ⟨hne, hpos⟩ := GlobalTheory.TestLat.gramR_ne_zero_and_gram_posDef K v₀ hv₀ d j H X hH.2 e he
  choose X' hX' hX'g using fun v => GlobalTheory.posDef_exists_frame j _ (hpos v)
  let L' : Submodule (𝓞 K) (Fin j → K) := L.comap (ψ.restrictScalars (𝓞 K))
  have hmap : L'.map (ψ.restrictScalars (𝓞 K)) = L := by
    apply Submodule.map_comap_eq_self
    intro x hx
    have : x ∈ LinearMap.range ψ := by
      rw [hrange]; exact Submodule.subset_span hx
    exact this
  have hfg : L'.FG :=
    Submodule.fg_of_fg_map_injective (ψ.restrictScalars (𝓞 K)) hψ (by rw [hmap]; exact hL)
  have hlat : Submodule.IsLattice K L' := by
    refine ⟨hfg, ?_⟩
    apply Submodule.map_injective_of_injective hψ
    rw [← Submodule.span_image, Submodule.map_top, hrange]
    have : ψ '' (L' : Set (Fin j → K)) = (L : Set (Fin d → K)) := by
      rw [← hmap]; rfl
    rw [this]
  have hnorm : ∀ v x, Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin d)) X v (ψ x) =
      Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin j)) X' v x := by
    intro v x
    unfold Formalism.HermitianLatticesTheory.normAt
    rw [fcoord_std, fcoord_std,
      cnorm_mulVec_eq (X' v)⁻¹ ((X v)⁻¹ * ((Matrix.of e)ᵀ.map v.embedding))
        (by rw [hX'g, gram_eq]), ← Matrix.mulVec_mulVec]
    congr 2
    ext i
    rw [hψE]
    simp [Matrix.mulVec, dotProduct]
  have hht := (Formalism.HN.rerealize K (Fin j → K) (Fin j) (Fin d → K) (Fin d) (Pi.basisFun K (Fin j)) X'
    (Pi.basisFun K (Fin d)) X ψ hX' (fun v => (hH.2 v).1) hψ hnorm L' hfg).1
  rw [hmap] at hht
  have hlcv : lcv X L = lcv X' L' := by
    unfold lcv; rw [hht]
  rw [hlcv]
  refine GlobalTheory.TestLat.neg_log_le_lcv_of_integral_form K j X' hX' (Matrix.of fun a c => star (e a) ⬝ᵥ H *ᵥ (e c)) s hs hne ?_ L' hlat ?_
  · have h := GlobalTheory.GramMean.prod_norm_gramR_le K d j H X hH e
    simp only [gram_single, hX'g]
    exact h
  · intro x hx y hy
    have h := hint (ψ x) hx (ψ y) hy
    have hG : (Matrix.of fun a c => star (e a) ⬝ᵥ H *ᵥ (e c)) =
        ((Matrix.of e)ᵀ)ᴴ * (H * (Matrix.of e)ᵀ) := by
      ext a c
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rw [hψE, hψE, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, Matrix.mul_assoc] at h
    rw [hG]
    exact h
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormJetExpNegMulLe
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ExpJets

open PowerSeries

variable {p : ℕ} [Fact p.Prime]

theorem expPS_eq_subst (F : PowerSeries ℂ_[p]) (hF : constantCoeff F = 0) :
    expPS F = (PowerSeries.exp ℂ_[p]).subst F := by
  ext n
  rw [PowerSeries.coeff_subst' (HasSubst.of_constantCoeff_zero' hF), expPS, coeff_mk,
    finsum_eq_sum_of_support_subset (s := Finset.range (n + 1))]
  · refine Finset.sum_congr rfl fun k _ => ?_
    simp [PowerSeries.coeff_exp, div_eq_inv_mul]
  · intro k hk
    by_contra h
    apply hk
    have hlt : n < k := by simpa using h
    have h0 : coeff n (F ^ k) = 0 := by
      have : (X : PowerSeries ℂ_[p]) ^ k ∣ F ^ k := pow_dvd_pow_of_dvd (X_dvd_iff.2 hF) k
      exact X_pow_dvd_iff.1 this n hlt
    simp [h0]

theorem derivative_expPS (F : PowerSeries ℂ_[p]) (hF : constantCoeff F = 0) :
    d⁄dX ℂ_[p] (expPS F) = expPS F * d⁄dX ℂ_[p] F := by
  rw [expPS_eq_subst F hF, PowerSeries.derivative_subst (HasSubst.of_constantCoeff_zero' hF),
    PowerSeries.derivative_exp]

theorem norm_jet_mul_le (A B : PowerSeries ℂ_[p]) (n : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ i j, i + j = n →
      ‖(i.factorial : ℂ_[p]) * coeff i A‖ * ‖(j.factorial : ℂ_[p]) * coeff j B‖ ≤ C) :
    ‖(n.factorial : ℂ_[p]) * coeff n (A * B)‖ ≤ C := by
  rw [coeff_mul, Finset.mul_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC fun x hx => ?_
  obtain ⟨i, j⟩ := x
  have hij : i + j = n := by simpa using hx
  have e : (n.factorial : ℂ_[p]) * (coeff i A * coeff j B) =
      (((i + j).choose j : ℕ) : ℂ_[p]) *
        (((i.factorial : ℂ_[p]) * coeff i A) * ((j.factorial : ℂ_[p]) * coeff j B)) := by
    rw [← hij, ← Nat.add_choose_mul_factorial_mul_factorial i j]
    push_cast
    ring
  simp only
  rw [e, norm_mul, norm_mul]
  have h1 : ‖(((i + j).choose j : ℕ) : ℂ_[p])‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ _
  calc _ ≤ 1 * C := mul_le_mul h1 (h i j hij) (by positivity) zero_le_one
    _ = C := one_mul C

theorem jet_derivative (A : PowerSeries ℂ_[p]) (n : ℕ) :
    (n.factorial : ℂ_[p]) * coeff n (d⁄dX ℂ_[p] A) =
      ((n + 1).factorial : ℂ_[p]) * coeff (n + 1) A := by
  rw [PowerSeries.coeff_derivative, Nat.factorial_succ]
  push_cast
  ring

theorem norm_jet_expPS_le (F : PowerSeries ℂ_[p]) (hF : constantCoeff F = 0) (s : ℝ)
    (hs : 0 ≤ s) (h : ∀ n : ℕ, ‖(n.factorial : ℂ_[p]) * coeff n F‖ ≤ s ^ n) (n : ℕ) :
    ‖(n.factorial : ℂ_[p]) * coeff n (expPS F)‖ ≤ s ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => simp [expPS]
    | succ n =>
      rw [← jet_derivative, derivative_expPS F hF]
      refine norm_jet_mul_le _ _ n _ (by positivity) fun i j hij => ?_
      rw [jet_derivative, ← hij, add_assoc, pow_add]
      exact mul_le_mul (ih i (by omega)) (h (j + 1)) (norm_nonneg _) (by positivity)

theorem norm_jet_exp_neg_mul_le : ∀ (p : ℕ) [Fact p.Prime] (ph : PowerSeries ℂ_[p]) (s : ℝ), 1 ≤ s → PowerSeries.constantCoeff ph = 0 → (∀ i, i ≠ 2 → ‖(i.factorial : ℂ_[p]) * PowerSeries.coeff i ph‖ ≤ 1) → ‖(2 : ℂ_[p]) * PowerSeries.coeff 2 ph‖ ≤ s ^ 2 → ∀ (f : PowerSeries ℂ_[p]), (∀ n : ℕ, ‖(n.factorial : ℂ_[p]) * PowerSeries.coeff n f‖ ≤ 1) → ∀ n : ℕ, ‖(n.factorial : ℂ_[p]) * PowerSeries.coeff n (expPS (-ph) * f)‖ ≤ s ^ n := by
  intro p _ ph s hs h0 h1 h2 f hf n
  have hs0 : 0 ≤ s := zero_le_one.trans hs
  have hE := norm_jet_expPS_le (-ph) (by simp [h0]) s hs0 fun m => by
    rw [map_neg, mul_neg, norm_neg]
    by_cases hm : m = 2
    · subst hm
      simpa using h2
    · exact (h1 m hm).trans (one_le_pow₀ hs)
  refine norm_jet_mul_le _ _ n _ (by positivity) fun i j hij => ?_
  rw [← hij, pow_add]
  exact mul_le_mul (hE i) ((hf j).trans (one_le_pow₀ hs)) (norm_nonneg _) (by positivity)

end GlobalTheory.ExpJets
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RatOfImEqZero
section
namespace GlobalTheory.RationalOfReal

open IntermediateField

theorem exists_coords {E : Type*} [Field E] [CharZero E] [Algebra ℚ E] (β : E) (d : ℚ)
    (hβ : β * β = -(d : E)) (y : E) (hy : y ∈ ℚ⟮β⟯) : ∃ u v : ℚ, y = (u : E) + (v : E) * β := by
  have hint : IsIntegral ℚ β := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    have : β ^ 2 = algebraMap ℚ E (-d) := by rw [pow_two, hβ]; simp
    rw [this]
    exact isIntegral_algebraMap
  have hy' : y ∈ Algebra.adjoin ℚ ({β} : Set E) := by
    rw [← adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
    exact hy
  clear hy
  induction hy' using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    exact ⟨0, 1, by simp [hx]⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨u, v, rfl⟩ := hx
    obtain ⟨u', v', rfl⟩ := hy
    exact ⟨u + u', v + v', by push_cast; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨u, v, rfl⟩ := hx
    obtain ⟨u', v', rfl⟩ := hy
    refine ⟨u * u' - d * v * v', u * v' + v * u', ?_⟩
    push_cast
    linear_combination (v : E) * (v' : E) * hβ

theorem rat_of_im_eq_zero {E : Type*} [Field E] [CharZero E] [Algebra ℚ E] (φ : E →+* ℂ) (β : E)
    (d : ℕ) (hd : 0 < d) (hφ : φ β = Complex.I * (Real.sqrt d : ℂ)) (y : E) (hy : y ∈ ℚ⟮β⟯)
    (him : (φ y).im = 0) : ∃ a : ℚ, y = (a : E) := by
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
  have hβ : β * β = -(((d : ℚ)) : E) := by
    apply φ.injective
    have h2 : (Real.sqrt d : ℂ) * (Real.sqrt d : ℂ) = (d : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg d)]
      simp
    rw [map_mul, hφ, map_neg, map_ratCast]
    push_cast
    linear_combination (Real.sqrt d : ℂ) * (Real.sqrt d : ℂ) * Complex.I_mul_I - h2
  obtain ⟨u, v, rfl⟩ := exists_coords β d hβ y hy
  rw [map_add, map_mul, map_ratCast, map_ratCast, hφ] at him
  have hv : (v : ℝ) * Real.sqrt d = 0 := by simpa using him
  have hv0 : v = 0 := by
    have := (mul_eq_zero.1 hv).resolve_right hs.ne'
    exact_mod_cast this
  exact ⟨u, by simp [hv0]⟩

theorem rat_of_real (D : Formalism.BasicNotions.D7) (x : D.host.K)
    (hx : (D.host.φ₀ (x : D.host.E)).im = 0) : ∃ a : ℚ, x = (a : D.host.K) := by
  obtain ⟨a, ha⟩ := rat_of_im_eq_zero D.host.φ₀ (D.host.sqd) D.host.d
    D.host.hyp.2.1.pos D.host.φ₀_mem (x : D.host.E) x.2 hx
  exact ⟨a, Subtype.ext (by simpa using ha)⟩

end GlobalTheory.RationalOfReal
end

