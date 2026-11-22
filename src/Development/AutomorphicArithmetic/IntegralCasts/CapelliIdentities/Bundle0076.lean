import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsIsomFrame
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0002
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0005
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0001
import GroundTheory.PAdicHodge.BdRAlg
import GroundTheory.PAdicHodge.FactorizationFactorialLe
import GroundTheory.PAdicHodge.PerfectoidField
import GroundTheory.PAdicHodge.KerFontaineThetaCompFrobeniusEquivSymmPow

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjEmbeddingRt
section
theorem UpperTheory.Reformulated.B.Gc4.conj_embedding_rt :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E]
    [inst_2 : NumberField.IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (τ : E →+* ℂ),
    (starRingEnd ℂ : ℂ → ℂ) ((τ : E → ℂ) (↑H.rt : E)) =
      -(τ : E → ℂ)
          (↑H.rt :
            E) := by
  intro E _ _ _ H τ
  have h1 : (H.rt : E) ^ 2 = -(H.d : E) := by
    simpa using congrArg (algebraMap (NumberField.RingOfIntegers E) E) H.rt_sq
  have h2 : (τ (H.rt : E)) ^ 2 = -(H.d : ℂ) := by
    rw [← map_pow, h1, map_neg, map_natCast]
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  generalize τ (H.rt : E) = z at h2 ⊢
  have hre : z.re * z.re - z.im * z.im = -(H.d : ℝ) := by simpa [sq] using congrArg Complex.re h2
  have him : z.re * z.im + z.im * z.re = 0 := by simpa [sq] using congrArg Complex.im h2
  have hz : z.im ≠ 0 := fun h => by rw [h] at hre; nlinarith [mul_self_nonneg z.re]
  have h0 : z.re = 0 := mul_right_cancel₀ hz (by linarith)
  apply Complex.ext <;> simp [h0]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjugateRootZero
section
theorem UpperTheory.Reformulated.B.ComplexConjugateRootEqNeg.rt0_conj_neg_ne_zero :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsCMField E]
      (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), (starRingEnd ℂ : ℂ → ℂ) H.rt0 = -H.rt0 := by
  intro E _ _ _ H
  have h := H.sqrt_neg_disc_sq
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.natCast_re, Complex.natCast_im, neg_zero] at hre him
  have h0 : H.rt0.re * H.rt0.im = 0 := by linarith
  have hr : H.rt0.re = 0 := by
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact h1
    · exfalso
      rw [h1] at hre
      nlinarith [mul_self_nonneg H.rt0.re]
  apply Complex.ext
  · rw [Complex.conj_re, Complex.neg_re, hr, neg_zero]
  · rw [Complex.conj_im, Complex.neg_im]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjugateRootZeroSecond
section
theorem UpperTheory.Reformulated.B.ConjugateRootZeroSecond.rt0_conj_neg_ne_zero :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsCMField E]
      (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), (starRingEnd ℂ : ℂ → ℂ) H.rt0 = -H.rt0 := by
  intro E _ _ _ H
  have h := H.sqrt_neg_disc_sq
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [pow_two] at hre him
  have h0 : H.rt0.re = 0 := by
    by_contra hne
    have him0 : H.rt0.im = 0 := by
      have hm : H.rt0.re * H.rt0.im = 0 := by linarith
      exact (mul_eq_zero.mp hm).resolve_left hne
    rw [him0] at hre
    nlinarith [mul_self_nonneg H.rt0.re]
  apply Complex.ext <;> simp [h0]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjugateRootZeroThird
section
theorem UpperTheory.Reformulated.B.StarRingEndRootEqNeg.rt0_conj_neg_ne_zero :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsCMField E]
      (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), (starRingEnd ℂ : ℂ → ℂ) H.rt0 = -H.rt0 := by
  intro E _ _ _ H
  have hd : (0 : ℝ) < (H.d : ℝ) := by exact_mod_cast H.d_prime.pos
  have h := H.sqrt_neg_disc_sq
  have hre : H.rt0.re * H.rt0.re - H.rt0.im * H.rt0.im = -(H.d : ℝ) := by
    simpa [pow_two, Complex.mul_re] using congrArg Complex.re h
  have him : H.rt0.re * H.rt0.im + H.rt0.im * H.rt0.re = 0 := by
    simpa [pow_two, Complex.mul_im] using congrArg Complex.im h
  have ha : H.rt0.re = 0 := by
    by_contra ha
    have hm : H.rt0.re * H.rt0.im = 0 := by linarith
    have hb : H.rt0.im = 0 := (mul_eq_zero.mp hm).resolve_left ha
    rw [hb] at hre
    nlinarith [mul_self_nonneg H.rt0.re]
  apply Complex.ext
  · simp [ha]
  · simp
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CubicCharpolyDiscriminant
section
open Matrix Polynomial UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

namespace UpperTheory.Reformulated.B.CubicCharpolyDiscriminant

private lemma charpoly_three {R : Type} [CommRing R] (M : Matrix (Fin 3) (Fin 3) R) :
    M.charpoly = X ^ 3 - C M.trace * X ^ 2 + C M.adjugate.trace * X - C M.det := by
  simp [Matrix.charpoly, Matrix.det_fin_three, Matrix.trace_fin_three, Matrix.adjugate_fin_three,
    Matrix.charmatrix_apply_eq, Matrix.charmatrix_apply_ne]
  ring

private lemma charpoly_tw {R : Type} [CommRing R] [StarRing R] (A M : Matrix (Fin 3) (Fin 3) R)
    (hA : A * star A = 1) (hM : M * star M = 1) (h : M = A * A.map star) :
    star M.trace = M.trace ∧ M.charpoly = (X - 1) * (X ^ 2 - C (M.trace - 1) * X + 1) := by
  have h1 : star M.trace = M.trace := by
    subst h
    simp only [Matrix.trace_fin_three, Matrix.mul_apply, Fin.sum_univ_three, Matrix.map_apply,
      star_add, star_mul', star_star]
    ring
  have h2 : M.det = 1 := by
    have e : A.map star = (star A)ᵀ := by
      ext i j
      simp [Matrix.star_apply]
    rw [h, det_mul, e, det_transpose, ← det_mul, hA, det_one]
  have h3 : M.adjugate = star M := by
    calc M.adjugate = M.adjugate * (M * star M) := by rw [hM, Matrix.mul_one]
      _ = star M := by rw [← Matrix.mul_assoc, adjugate_mul, h2, one_smul, Matrix.one_mul]
  refine ⟨h1, ?_⟩
  rw [charpoly_three, h3, h2, star_eq_conjTranspose, trace_conjTranspose, h1]
  simp only [map_sub, map_one]
  ring

open scoped Matrix.Norms.L2Operator in
private lemma disc_nonpos (M : Matrix (Fin 3) (Fin 3) ℂ) (hM : M ∈ unitary (Matrix (Fin 3) (Fin 3) ℂ)) (t : ℝ)
    (h : M.charpoly = (X - 1) * (X ^ 2 - C (t : ℂ) * X + 1)) : t ^ 2 - 4 ≤ 0 := by
  by_contra hc
  push Not at hc
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s ^ 2 = t ^ 2 - 4 := ⟨√(t ^ 2 - 4), Real.sq_sqrt hc.le⟩
  set r : ℝ := (t + s) / 2 with hr
  have e : r ^ 2 - t * r + 1 = 0 := by rw [hr]; linarith
  have hroot : (r : ℂ) ∈ spectrum ℂ M := by
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly, h]
    have e' : (r : ℂ) ^ 2 - t * r + 1 = 0 := by exact_mod_cast e
    simp [e']
  have hn := spectrum.norm_eq_one_of_unitary hM hroot
  rw [Complex.norm_real, Real.norm_eq_abs] at hn
  have h2 : r ^ 2 = 1 := by rw [← sq_abs, hn]; norm_num
  have h3 : t * r = 2 := by linarith
  have h4 : t ^ 2 = 4 := by
    calc t ^ 2 = (t * r) ^ 2 := by rw [mul_pow, h2, mul_one]
      _ = 4 := by rw [h3]; norm_num
  linarith

private lemma exists_emb {F : Type} [Field F] (Δ : F) (σ : F →+* ℝ) (h : σ Δ < 0) :
    ∃ φ : Lsq F Δ →+* ℂ, (∀ x, φ (star x) = star (φ x)) ∧ ∀ a, φ (algebraMap F _ a) = σ a := by
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s * s = -σ Δ := ⟨√(-σ Δ), Real.mul_self_sqrt (by linarith)⟩
  refine ⟨{ toFun := fun x => ⟨σ x.re, σ x.im * s⟩
            map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, ?_, ?_⟩
  · apply Complex.ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  · intro x y
    apply Complex.ext
    · simp
      linear_combination (σ x.im * σ y.im) * hs
    · simp
      ring
  · apply Complex.ext <;> simp
  · intro x y
    apply Complex.ext
    · simp
    · simp
      ring
  · intro x
    apply Complex.ext <;> simp
  · intro a
    apply Complex.ext <;> simp

end UpperTheory.Reformulated.B.CubicCharpolyDiscriminant

theorem UpperTheory.Reformulated.B.CubicCharpolyDiscriminant.tauEx :
    UpperTheory.V.Z.Sym.Glob.TauEx := by
  intro F _ _ Δ D hD δ
  set M : U3 Δ := δ * theta Δ δ with hMdef
  obtain ⟨h1, h2⟩ := charpoly_tw (δ : Matrix (Fin 3) (Fin 3) (Lsq F Δ)) (M : Matrix (Fin 3) (Fin 3) (Lsq F Δ))
    δ.2.2 M.2.2 rfl
  have him : (M : Matrix (Fin 3) (Fin 3) (Lsq F Δ)).trace.im = 0 := by
    have := congrArg QuadraticAlgebra.im h1
    rw [QuadraticAlgebra.im_star] at this
    linear_combination (-1 / 2 : F) * this
  have hτ : algebraMap F (Lsq F Δ) ((M : Matrix (Fin 3) (Fin 3) (Lsq F Δ)).trace.re - 1) =
      (M : Matrix (Fin 3) (Fin 3) (Lsq F Δ)).trace - 1 := by
    ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, him]
  rw [← hτ] at h2
  generalize (M : Matrix (Fin 3) (Fin 3) (Lsq F Δ)).trace.re - 1 = τ at h2
  refine ⟨τ, h2, fun hne σ => ?_⟩
  obtain ⟨φ, hφ, hφa⟩ := exists_emb Δ σ (hD.neg σ)
  have hs : star ((M : Matrix (Fin 3) (Fin 3) (Lsq F Δ)).map φ) = (star (M : Matrix (Fin 3) (Fin 3) (Lsq F Δ))).map φ := by
    ext i j
    simp only [Matrix.star_apply, Matrix.map_apply, hφ]
  have hu : (M : Matrix (Fin 3) (Fin 3) (Lsq F Δ)).map φ ∈ unitary (Matrix (Fin 3) (Fin 3) ℂ) := by
    constructor
    · rw [hs, ← Matrix.map_mul, M.2.1, Matrix.map_one _ (map_zero φ) (map_one φ)]
    · rw [hs, ← Matrix.map_mul, M.2.2, Matrix.map_one _ (map_zero φ) (map_one φ)]
  have hle := disc_nonpos _ hu (σ τ) (by
    rw [Matrix.charpoly_map, h2]
    simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_one, Polynomial.map_C, hφa])
  have hne' : σ (τ ^ 2 - 4) ≠ 0 := (map_ne_zero σ).2 hne
  have e : σ (τ ^ 2 - 4) = σ τ ^ 2 - 4 := by
    rw [map_sub, map_pow, map_ofNat]
  exact lt_of_le_of_ne (e ▸ hle) hne'
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsCoordinate
section
open scoped IntermediateField Algebra TensorProduct Matrix Pointwise NumberField Topology ContDiff NNReal ENNReal Polynomial DirectSum BigOperators InnerProductSpace Manifold

theorem UpperTheory.Reformulated.B.ExistsCoordinate.exists_coord :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E]
    [inst_2 : NumberField.IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) {y : E},
    y ∈ ℚ[(↑H.rt : E)] →
      ∃ (u : ℚ) (v : ℚ),
        y =
          (↑u : E) +
            (↑v : E) *
              (↑H.rt :
                E) := by
  intro E _ _ _ H y hy
  have hsq : (H.rt : E) * (H.rt : E) = -(H.d : E) := by
    have h := congrArg (fun z : NumberField.RingOfIntegers E => (z : E)) H.rt_sq
    simpa [sq] using h
  induction hy using Algebra.adjoin_induction with
  | mem x hx => exact ⟨0, 1, by rw [Set.mem_singleton_iff.mp hx]; simp⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add x z _ _ hx hz =>
    obtain ⟨⟨a, b, rfl⟩, c, e, rfl⟩ := And.intro hx hz
    exact ⟨a + c, b + e, by push_cast; ring⟩
  | mul x z _ _ hx hz =>
    obtain ⟨⟨a, b, rfl⟩, c, e, rfl⟩ := And.intro hx hz
    exact ⟨a * c - b * e * H.d, a * e + b * c, by push_cast; linear_combination (b * e : E) * hsq⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsOrthogonalUnitVector
section
noncomputable def UpperTheory.Reformulated.B.ExistsOrthogonalBasisWithUnitNorms.PairUnit :
    {K V : Type} →
      [inst : Field K] →
        [inst_1 : StarRing K] →
          [inst_2 : AddCommGroup V] → [inst_3 : _root_.Module K V] → Subring K → (V →ₗ⋆[K] V →ₗ[K] K) → Prop :=
    fun {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [_root_.Module K V] (S : Subring K) (h : V →ₗ⋆[K] V →ₗ[K] K) ↦
      ∀ (w y : V),
        ((h : V → V →ₗ[K] K) y : V → K) w = (1 : K) →
          ((h : V → V →ₗ[K] K) w : V → K) w ∈ S →
            ((h : V → V →ₗ[K] K) y : V → K) y ∈ S →
              ∃ c ∈ S,
                ∃ d ∈ S, Formalism.HermitianLattices.Ext.L3.WA.IsUnitIn S (((h : V → V →ₗ[K] K) (c • w + d • y) : V → K) (c • w + d • y))

open Formalism.HermitianLattices.Ext.L3.WA in

private theorem UpperTheory.Reformulated.B.ExistsOrthogonalBasisWithUnitNorms.exists_primitive {K V : Type} [Field K] [StarRing K] [AddCommGroup V]
    [Module K V] {S : Subring K} {h : V →ₗ⋆[K] V →ₗ[K] K} (hS : IsHermSemilocal S)
    (hn : h.Nondegenerate) {L : AddSubgroup V} (hL : IsSelfDualMod S h L) {v : V} (hv : v ≠ 0) :
    ∃ a : K, a • v ∈ L ∧ ∃ w ∈ L, h w (a • v) = 1 := by
  let A : AddSubgroup K :=
    { carrier := {a | ∃ m ∈ L, h m v = a}
      zero_mem' := ⟨0, L.zero_mem, by simp⟩
      add_mem' := by
        rintro _ _ ⟨m, hm, rfl⟩ ⟨m', hm', rfl⟩
        exact ⟨m + m', L.add_mem hm hm', by simp⟩
      neg_mem' := by
        rintro _ ⟨m, hm, rfl⟩
        exact ⟨-m, L.neg_mem hm, by simp⟩ }
  have hmul : ∀ s ∈ S, ∀ a ∈ A, s * a ∈ A := by
    rintro s hs _ ⟨m, hm, rfl⟩
    exact ⟨star s • m, hL.smul_mem _ (hS.star_mem s hs) _ hm, by
      rw [map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply, star_star, smul_eq_mul]⟩
  have hne : ∃ a ∈ A, a ≠ 0 := by
    have hu : ∃ u, h u v ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hv (hn.2 v hc)
    obtain ⟨u, hu⟩ := hu
    obtain ⟨t, ht, htu⟩ := hL.span u
    refine ⟨_, ⟨t • u, htu, rfl⟩, ?_⟩
    simp [map_smulₛₗ, ht, hu]
  have hbd : ∃ t : K, t ≠ 0 ∧ ∀ a ∈ A, t * a ∈ S := by
    obtain ⟨t, ht, htv⟩ := hL.span v
    refine ⟨t, ht, ?_⟩
    rintro _ ⟨m, hm, rfl⟩
    simpa using hL.int m hm _ htv
  obtain ⟨α, ⟨w, hw, hα⟩, hα0, hdiv⟩ := hS.principal A hmul hne hbd
  refine ⟨α⁻¹, hL.dual _ fun m hm => ?_, w, hw, ?_⟩
  · simpa [mul_comm] using hdiv _ ⟨m, hm, rfl⟩
  · rw [map_smul, hα, smul_eq_mul, inv_mul_cancel₀ hα0]

open Formalism.HermitianLattices.Ext.L3.WA in

private theorem UpperTheory.Reformulated.B.ExistsOrthogonalBasisWithUnitNorms.exists_extend {K V : Type} [Field K] [StarRing K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {S : Subring K} {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hS : IsHermSemilocal S) (hs : h.IsSymm) (hn : h.Nondegenerate)
    (hp : UpperTheory.Reformulated.B.ExistsOrthogonalBasisWithUnitNorms.PairUnit S h) {L : AddSubgroup V} (hL : IsSelfDualMod S h L)
    {k : ℕ} (hk : k < Module.finrank K V) (x : Fin k → V) (hxL : ∀ i, x i ∈ L)
    (hxo : ∀ i j, i ≠ j → h (x i) (x j) = 0) (hxu : ∀ i, IsUnitIn S (h (x i) (x i))) :
    ∃ z ∈ L, (∀ i, h (x i) z = 0) ∧ IsUnitIn S (h z z) := by
  have hsym : ∀ u v, star (h u v) = h v u := fun u v => hs.eq u v
  let φ : V →ₗ[K] (Fin k → K) := LinearMap.pi fun i => h (x i)
  have hker : LinearMap.ker φ ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by simpa using hk)
  obtain ⟨v, hvk, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hxv : ∀ i, h (x i) v = 0 := fun i => congrFun (LinearMap.mem_ker.mp hvk) i
  obtain ⟨a, hyL, w₀, hw₀, hwy⟩ := UpperTheory.Reformulated.B.ExistsOrthogonalBasisWithUnitNorms.exists_primitive hS hn hL hv0
  have hxy : ∀ i, h (x i) (a • v) = 0 := fun i => by rw [map_smul, hxv, smul_zero]
  generalize a • v = y at hyL hwy hxy
  have hyx : ∀ i, h y (x i) = 0 := fun i => by rw [← hsym, hxy, star_zero]
  have hyw₀ : h y w₀ = 1 := by rw [← hsym, hwy, star_one]
  let w : V := w₀ - ∑ i, ((h (x i) (x i))⁻¹ * h (x i) w₀) • x i
  have hwL : w ∈ L :=
    L.sub_mem hw₀ (L.sum_mem fun i _ =>
      hL.smul_mem _ (S.mul_mem (hxu i).2.2 (hL.int _ (hxL i) _ hw₀)) _ (hxL i))
  have hyw : h y w = 1 := by
    simp [w, map_sub, map_sum, hyx, hyw₀]
  have hxw : ∀ j, h (x j) w = 0 := by
    intro j
    have hj := (hxu j).1
    simp only [w, map_sub, map_sum, map_smul, smul_eq_mul]
    rw [Finset.sum_eq_single j]
    · field_simp
      ring
    · intro i _ hij
      rw [hxo j i hij.symm, mul_zero]
    · simp
  obtain ⟨c, hc, d, hd, hu⟩ := hp w y hyw (hL.int _ hwL _ hwL) (hL.int _ hyL _ hyL)
  refine ⟨c • w + d • y, L.add_mem (hL.smul_mem _ hc _ hwL) (hL.smul_mem _ hd _ hyL), fun i => ?_, hu⟩
  rw [map_add, map_smul, map_smul, hxw, hxy, smul_zero, smul_zero, add_zero]

theorem UpperTheory.Reformulated.B.ExistsOrthogonalBasisWithUnitNorms.exists_ortho_unit :
    ∀ {K V : Type} [inst : Field K] [inst_1 : StarRing K] [inst_2 : AddCommGroup V] [inst_3 : _root_.Module K V]
      {S : Subring K} {h : V →ₗ⋆[K] V →ₗ[K] K} [FiniteDimensional K V],
      Formalism.HermitianLattices.Ext.L3.WA.IsHermSemilocal S →
        h.IsSymm →
          h.Nondegenerate →
            UpperTheory.Reformulated.B.ExistsOrthogonalBasisWithUnitNorms.PairUnit S h →
              ∀ {L : AddSubgroup V},
                Formalism.HermitianLattices.Ext.L3.WA.IsSelfDualMod S h L →
                  ∃ (x : Fin (Module.finrank K V) → V),
                    (∀ (i : Fin (Module.finrank K V)), x i ∈ L) ∧
                      (∀ (i j : Fin (Module.finrank K V)), i ≠ j → ((h : V → V →ₗ[K] K) (x i) : V → K) (x j) = (0 : K)) ∧
                        ∀ (i : Fin (Module.finrank K V)),
                          Formalism.HermitianLattices.Ext.L3.WA.IsUnitIn S (((h : V → V →ₗ[K] K) (x i) : V → K) (x i)) := by
  intro K V _ _ _ _ S h _ hS hs hn hp L hL
  have key : ∀ k : ℕ, k ≤ Module.finrank K V → ∃ x : Fin k → V, (∀ i, x i ∈ L) ∧
      (∀ i j, i ≠ j → h (x i) (x j) = 0) ∧
        ∀ i, Formalism.HermitianLattices.Ext.L3.WA.IsUnitIn S (h (x i) (x i)) := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
    | succ k ih =>
      intro hk
      obtain ⟨x, hxL, hxo, hxu⟩ := ih (by omega)
      obtain ⟨z, hzL, hxz, hzu⟩ :=
        UpperTheory.Reformulated.B.ExistsOrthogonalBasisWithUnitNorms.exists_extend hS hs hn hp hL (by omega) x hxL hxo hxu
      have hzx : ∀ i, h z (x i) = 0 := fun i => by
        rw [← hs.eq, hxz, map_zero]
      refine ⟨Fin.cons z x, fun i => ?_, fun i j hij => ?_, fun i => ?_⟩
      · refine Fin.cases ?_ (fun i => ?_) i
        · simpa using hzL
        · simpa using hxL i
      · induction i using Fin.cases with
        | zero =>
          induction j using Fin.cases with
          | zero => exact absurd rfl hij
          | succ j => simpa using hzx j
        | succ i =>
          induction j using Fin.cases with
          | zero => simpa using hxz i
          | succ j => simpa using hxo i j fun e => hij (by rw [e])
      · refine Fin.cases ?_ (fun i => ?_) i
        · simpa using hzu
        · simpa using hxu i
  exact key _ le_rfl
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FinitelyGeneratedHomology
section
theorem UpperTheory.Reformulated.B.FinitelyGeneratedHomology.omHT_fg :
    ∀ {A K : Type} [inst : CommRing A] [inst_1 : Field K] [inst_2 : Algebra A K] {E : Type} [inst_3 : Field E]
      [inst_4 : NumberField E] {c : E ≃+* E} {p R N : ℕ} {Ω : Type} [inst_5 : AddCommGroup Ω] [inst_6 : _root_.Module K Ω]
      [inst_7 : _root_.Module A Ω] [inst_8 : IsScalarTower A K Ω] (D : GlobalTheory.CompanionTheory.Ar.HT.HTChart A K c p R N Ω) (σ : E →+* K),
      (D.omHT σ).FG := by
  intro A K _ _ _ E _ _ c p R N Ω _ _ _ _ D σ
  have hZ : (LinearMap.range D.h.toIntLinearMap).FG := Submodule.fg_range _
  have hA : (Submodule.span A (Set.range D.h)).FG := by
    obtain ⟨S, hS⟩ := hZ
    refine ⟨S, ?_⟩
    have h1 : Set.range D.h = (Submodule.span ℤ (S : Set Ω) : Set Ω) := by
      rw [hS]; rfl
    rw [h1, Submodule.span_span_of_tower]
  exact (hA.sup (D.om_lat.fg.map _)).map _
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LocPairValLinear
section
theorem UpperTheory.Reformulated.B.Qp9.locPair_val_linear :
    ∀ (O : Type) [inst : CommRing O] [inst_1 : IsDomain O]
    [inst_2 : IsDiscreteValuationRing O] (K : Type) [Fintype K] [inst_4 : DecidableEq K] (ι : K → Type)
    [(k : K) → Fintype (ι k)] (σ : Type) [inst_6 : Fintype σ] (T : GlobalTheory.CompanionTheory.Ar.Num.LocPair ι O σ)
    (P : Ideal (GroundTheory.Heights₂.Heights.NumbersDVR.MRing ι O)),
    (∀ (Gs Hs : σ → MvPolynomial (σ ⊕ σ) ℝ), T.val P (Gs + Hs) = T.val P Gs + T.val P Hs) ∧
      (∀ (c : ℝ) (Gs : σ → MvPolynomial (σ ⊕ σ) ℝ),
          (T.val P fun (i : σ) ↦ (MvPolynomial.C : ℝ → MvPolynomial (σ ⊕ σ) ℝ) c * Gs i) = c * T.val P Gs) ∧
        ∀ (α : Type) (s : Finset α) (Gs : α → σ → MvPolynomial (σ ⊕ σ) ℝ),
          (T.val P fun (i : σ) ↦ ∑ a ∈ s, Gs a i) =
            ∑ a ∈ s,
              T.val P
                (Gs
                  a) := by
  intro O _ _ _ K _ _ ι _ σ _ T P
  have key : ∀ Gs : σ → MvPolynomial (σ ⊕ σ) ℝ, T.val P Gs = ∑ i, Finsupp.linearCombination ℝ
      (fun μ => (GlobalTheory.CompanionTheory.Ar.Num.cycList (GroundTheory.Heights₂.Heights.NumbersDVR.ratDiv P (T.f i) (T.g i))
        (GroundTheory.Heights₂.Heights.NumbersDVR.classList (Sum.elim T.x T.x') μ ++ []) : ℝ))
      (MvPolynomial.basisMonomials (σ ⊕ σ) ℝ |>.repr (Gs i)) := fun Gs => rfl
  refine ⟨fun Gs Hs => ?_, fun c Gs => ?_, fun α s Gs => ?_⟩
  · simp only [key, Pi.add_apply, map_add, Finset.sum_add_distrib]
  · simp only [key, MvPolynomial.C_mul', map_smul, smul_eq_mul, Finset.mul_sum]
  · simp only [key, map_sum]
    exact Finset.sum_comm
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Rt0ConjNegNeZero
section
theorem UpperTheory.Reformulated.B.Ga10.rt0_conj_neg_ne_zero :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E]
    [inst_2 : NumberField.IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    (starRingEnd ℂ : ℂ → ℂ) H.rt0 =
      -H.rt0 := by
  intro E _ _ _ H
  have h := H.sqrt_neg_disc_sq
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp [sq] at h1 h2
  have hre : H.rt0.re = 0 := by
    by_contra hne
    have him : H.rt0.im = 0 := mul_left_cancel₀ hne (by linarith)
    rw [him] at h1
    nlinarith [mul_self_nonneg H.rt0.re]
  apply Complex.ext <;> simp [hre]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ZASmul
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qi53.Acris :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ GroundTheory.PAdicHodge.ACris.ACris ℂ_[l] l

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qi53.Ainf :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ GroundTheory.PAdicHodge.AInf ℂ_[l] l

noncomputable def UpperTheory.Reformulated.B.Qi53.zA :
    (l : ℕ) → [inst : Fact (Nat.Prime l)] → ℤ_[l] →+* UpperTheory.Reformulated.B.Qi53.Acris l :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦
      (Algebra.algebraMap (UpperTheory.Reformulated.B.Qi53.Ainf l) (UpperTheory.Reformulated.B.Qi53.Acris l)).comp
        (GroundTheory.PAdicHodge.IsPerfectoidField.padicIntToWitt l)

theorem UpperTheory.Reformulated.B.Qi53.zA_smul.{u_1} :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] {N : Type u_1} [inst_1 : AddCommGroup N]
      [inst_2 : _root_.Module (UpperTheory.Reformulated.B.Qi53.Acris l) N] (n : ℕ),
      (∀ (y : N), (↑l : UpperTheory.Reformulated.B.Qi53.Acris l) ^ n • y = (0 : N)) →
        ∀ (z : ℤ_[l]) (y : N),
          (UpperTheory.Reformulated.B.Qi53.zA l : ℤ_[l] → UpperTheory.Reformulated.B.Qi53.Acris l) z • y =
            ((PadicInt.toZModPow n : ℤ_[l] → ZMod (l ^ n)) z).val • y := by
  intro l _ N _ _ n h z y
  have hz : z - (((PadicInt.toZModPow n z).val : ℕ) : ℤ_[l]) ∈ RingHom.ker (PadicInt.toZModPow n : ℤ_[l] →+* ZMod (l ^ n)) := by
    haveI : NeZero (l ^ n) := ⟨pow_ne_zero n (Fact.out : Nat.Prime l).ne_zero⟩
    rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hz
  obtain ⟨w, hw⟩ := hz
  have hz' : z = (((PadicInt.toZModPow n z).val : ℕ) : ℤ_[l]) + (l : ℤ_[l]) ^ n * w := by
    rw [← hw]; ring
  generalize (PadicInt.toZModPow n z).val = m at hz' ⊢
  rw [hz', map_add, map_mul, map_pow, map_natCast, map_natCast, add_smul, mul_smul, h, add_zero,
    Nat.cast_smul_eq_nsmul]
end

