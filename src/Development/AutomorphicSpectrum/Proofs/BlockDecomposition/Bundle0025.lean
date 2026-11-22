import Mathlib

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorSumAnnihilator
section
open Polynomial

namespace GlobalTheory.CompanionTheory.KillSum

theorem prod_map_add_eq {R α : Type*} [CommRing R] (P : Multiset α) (f : α → R) (w : R) :
    ∃ q, (P.map fun a => f a + w).prod = (P.map f).prod + w * q := by
  induction P using Multiset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | cons a s ih =>
    obtain ⟨q, hq⟩ := ih
    refine ⟨(s.map f).prod + f a * q + w * q, ?_⟩
    simp only [Multiset.map_cons, Multiset.prod_cons, hq]
    ring

theorem add_killed {R : Type*} [CommRing R] [Algebra ℂ R] (x y : R) (P Q : Multiset ℂ)
    (hP : (P.map fun c => x - algebraMap ℂ R c).prod = 0)
    (hQ : (Q.map fun c => y - algebraMap ℂ R c).prod = 0) :
    ((Q.bind fun b => P.map fun a => a + b).map fun c => (x + y) - algebraMap ℂ R c).prod = 0 := by
  have key : ∀ b : ℂ, ∃ q, (P.map fun a => (x + y) - algebraMap ℂ R (a + b)).prod
      = (y - algebraMap ℂ R b) * q := by
    intro b
    obtain ⟨q, hq⟩ := prod_map_add_eq P (fun c => x - algebraMap ℂ R c) (y - algebraMap ℂ R b)
    refine ⟨q, ?_⟩
    rw [hP, zero_add] at hq
    rw [← hq]
    congr 1
    apply Multiset.map_congr rfl
    intro a _
    simp only [map_add]
    ring
  choose q hq using key
  rw [Multiset.map_bind, Multiset.prod_bind]
  simp only [Multiset.map_map, Function.comp_def]
  simp only [hq]
  rw [Multiset.prod_map_mul, hQ, zero_mul]

theorem sum_killed {ι : Type} (T : Finset ι) (l : ι → Multiset ℂ) :
    ∃ l' : Multiset ℂ, Multiset.card l' = ∏ τ ∈ T, Multiset.card (l τ) ∧
  ∀ (R : Type) [CommRing R] [Algebra ℂ R] (h : ι → R), (∀ τ ∈ T, ((l τ).map fun c => h τ - algebraMap ℂ R c).prod = 0) →
    (l'.map fun c => ∑ τ ∈ T, h τ - algebraMap ℂ R c).prod = 0 := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨{0}, by simp, fun R _ _ h _ => by simp⟩
  | insert τ s hτ ih =>
    obtain ⟨l0, hc, hk⟩ := ih
    refine ⟨l0.bind fun b => (l τ).map fun a => a + b, ?_, ?_⟩
    · rw [Finset.prod_insert hτ, ← hc]
      simp [Multiset.card_bind, mul_comm]
    · intro R _ _ h hh
      rw [Finset.sum_insert hτ]
      exact add_killed _ _ _ _ (hh τ (Finset.mem_insert_self _ _))
        (hk R h fun t ht => hh t (Finset.mem_insert_of_mem ht))

end GlobalTheory.CompanionTheory.KillSum
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceDualDenominatorBounded
section
open NumberField

namespace GlobalTheory.CompanionTheory.SiegelND.Integ

theorem traceDual_clear_by_integer : ∀ (F : Type) [Field F] [NumberField F], ∃ D : ℕ, 0 < D ∧ ∀ f : F,
    (∀ r : 𝓞 F, ∃ m : ℤ, Algebra.trace ℚ F (f * (r : F)) = m) → ∃ o : 𝓞 F, (o : F) = (D : F) * f := by
  intro F _ _
  obtain ⟨a, ha, hint⟩ := (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)).isFractional
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  refine ⟨Ideal.absNorm (Ideal.span {a}), ?_, ?_⟩
  · rw [Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact ha0
  · intro f hf
    have hmem : f ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
      rw [FractionalIdeal.mem_dual (one_ne_zero' (FractionalIdeal (nonZeroDivisors (𝓞 F)) F))]
      intro x hx
      obtain ⟨r, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
      obtain ⟨m, hm⟩ := hf r
      refine ⟨m, ?_⟩
      rw [Algebra.traceForm_apply, eq_intCast]
      exact hm.symm
    obtain ⟨o, ho⟩ := hint f hmem
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {a}))
    refine ⟨c * o, ?_⟩
    rw [Algebra.smul_def] at ho
    show algebraMap (𝓞 F) F (c * o) = _
    rw [map_mul, ho, ← mul_assoc, ← map_mul, hc, map_natCast]

end GlobalTheory.CompanionTheory.SiegelND.Integ
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformLowerBoundNearInjective
section
open MeasureTheory
open scoped ENNReal NNReal Topology

namespace GlobalTheory.CompanionTheory.RealCoordinates

theorem eventually_lower_bound_of_tendsto_injective
    (X P : Type) [AddCommGroup X] [TopologicalSpace X] [TopologicalSpace P] (N : ℕ)
    (e : X ≃+ (Fin N → ℝ)) (he : Continuous e) (hes : Continuous e.symm) (c : P)
    (A : P → X →+ X) (hA : ∀ s, Continuous (A s))
    (hlim : ∀ x, Filter.Tendsto (fun s => A s x) (nhds c) (nhds (A c x)))
    (hinj : Function.Injective (A c)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ s in nhds c, ∀ x, δ * ‖e x‖ ≤ ‖e (A s x)‖ := by
  classical

  let f : P → (Fin N → ℝ) →+ (Fin N → ℝ) := fun s =>
    e.toAddMonoidHom.comp ((A s).comp e.symm.toAddMonoidHom)
  have hf : ∀ s, Continuous (f s) := fun s => he.comp ((hA s).comp hes)
  let L : P → (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) := fun s => (f s).toRealLinearMap (hf s)
  have hL : ∀ s x, e (A s x) = L s (e x) := by
    intro s x
    simp [L, f]
  have hLc : Function.Injective (L c) := by
    intro y z h
    have h' : A c (e.symm y) = A c (e.symm z) := by
      apply e.injective
      simpa [L, f] using h
    simpa using congrArg e (hinj h')

  obtain ⟨K, hK, hKL⟩ := (L c : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ)).exists_antilipschitzWith
    (LinearMap.ker_eq_bot.mpr hLc)
  have hKpos : (0 : ℝ) < K := hK
  set δ : ℝ := 1 / (2 * K) with hδ
  have hδpos : 0 < δ := by positivity
  have hlow : ∀ y, 2 * δ * ‖y‖ ≤ ‖L c y‖ := by
    intro y
    have h1 := hKL.le_mul_dist y 0
    simp only [dist_zero_right, map_zero, ContinuousLinearMap.coe_coe] at h1
    have h2 : 2 * δ = (K : ℝ)⁻¹ := by
      rw [hδ]
      field_simp
    rw [h2, inv_mul_le_iff₀ hKpos]
    exact h1

  let b : Fin N → Fin N → ℝ := fun i j => if i = j then 1 else 0
  set ε : ℝ := δ / (N + 1) with hε
  have hεpos : 0 < ε := by positivity
  have hev : ∀ᶠ s in nhds c, ∀ i : Fin N, ‖L s (b i) - L c (b i)‖ < ε := by
    rw [Filter.eventually_all]
    intro i
    have ht : Filter.Tendsto (fun s => L s (b i)) (nhds c) (nhds (L c (b i))) := by
      have := (he.tendsto _).comp (hlim (e.symm (b i)))
      simpa [L, f, Function.comp_def] using this
    exact (Metric.tendsto_nhds.mp ht ε hεpos).mono fun s hs => by rwa [dist_eq_norm] at hs
  have hNε : (N : ℝ) * ε ≤ δ := by
    rw [hε, mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  refine ⟨δ, hδpos, hev.mono fun s hs x => ?_⟩
  rw [hL]
  have hdiff : ‖L s (e x) - L c (e x)‖ ≤ δ * ‖e x‖ := by
    have hy : L s (e x) - L c (e x) = ∑ i, (e x) i • (L s (b i) - L c (b i)) := by
      conv_lhs => rw [pi_eq_sum_univ (e x)]
      simp only [map_sum, map_smul, smul_sub, Finset.sum_sub_distrib]
      rfl
    rw [hy]
    calc ‖∑ i, (e x) i • (L s (b i) - L c (b i))‖
        ≤ ∑ i, ‖(e x) i • (L s (b i) - L c (b i))‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin N, ‖e x‖ * ε := by
          apply Finset.sum_le_sum
          intro i _
          rw [norm_smul]
          exact mul_le_mul (norm_le_pi_norm (e x) i) (hs i).le (norm_nonneg _) (norm_nonneg _)
      _ = (N : ℝ) * ε * ‖e x‖ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
      _ ≤ δ * ‖e x‖ := mul_le_mul_of_nonneg_right hNε (norm_nonneg _)
  have hc := hlow (e x)
  have htri : ‖L c (e x)‖ ≤ ‖L s (e x)‖ + ‖L s (e x) - L c (e x)‖ := by
    calc ‖L c (e x)‖ = ‖L s (e x) - (L s (e x) - L c (e x))‖ := by rw [sub_sub_cancel]
      _ ≤ ‖L s (e x)‖ + ‖L s (e x) - L c (e x)‖ := norm_sub_le _ _
  nlinarith [norm_nonneg (e x)]

end GlobalTheory.CompanionTheory.RealCoordinates
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryExtensionOfBlock
section
open Matrix

namespace GlobalTheory.CompanionTheory.WittFrame

abbrev FrameIdx (D m : ℕ) := Fin D ⊕ₗ (Fin m ⊕ₗ (Fin D)ᵒᵈ)

def frameEquiv (D m : ℕ) : FrameIdx D m ≃ Fin D ⊕ (Fin m ⊕ Fin D) :=
  ofLex.trans (Equiv.sumCongr (Equiv.refl _)
    (ofLex.trans (Equiv.sumCongr (Equiv.refl _) OrderDual.ofDual)))

theorem block_zero {D m : ℕ} (b b' : Matrix (Fin D) (Fin D) ℂ) (t : Matrix (Fin m) (Fin m) ℂ)
    (hb : b.BlockTriangular id) (ht : t.BlockTriangular id)
    (hb' : ∀ x y, x < y → b' x y = 0) (p q : FrameIdx D m) (hqp : q < p) :
    (fromBlocks b 0 0 (fromBlocks t 0 0 b')) (frameEquiv D m p) (frameEquiv D m q) = 0 := by
  obtain ⟨p, rfl⟩ := toLex.surjective p
  obtain ⟨q, rfl⟩ := toLex.surjective q
  rcases p with a | u <;> rcases q with c | v
  · have h : c < a := Sum.Lex.inl_lt_inl_iff.1 hqp
    simpa [frameEquiv] using hb h
  · exact absurd hqp Sum.Lex.not_inr_lt_inl
  · simp [frameEquiv]
  · have h : v < u := Sum.Lex.inr_lt_inr_iff.1 hqp
    obtain ⟨u, rfl⟩ := toLex.surjective u
    obtain ⟨v, rfl⟩ := toLex.surjective v
    rcases u with a | u <;> rcases v with c | v
    · have h' : c < a := Sum.Lex.inl_lt_inl_iff.1 h
      simpa [frameEquiv] using ht h'
    · exact absurd h Sum.Lex.not_inr_lt_inl
    · simp [frameEquiv]
    · have h' : v < u := Sum.Lex.inr_lt_inr_iff.1 h
      have h'' : OrderDual.ofDual u < OrderDual.ofDual v := h'
      simpa [frameEquiv] using hb' _ _ h''

theorem unitary_of_blocks {n D m : ℕ} (C H : Matrix (Fin n) (Fin D) ℂ)
    (G : Matrix (Fin n) (Fin m) ℂ)
    (hCC : Cᴴ * C = 1) (hCG : Cᴴ * G = 0) (hCH : Cᴴ * H = 0) (hGG : Gᴴ * G = 1)
    (hGH : Gᴴ * H = 0) (hHH : Hᴴ * H = 1) (hcard : D + (m + D) = n) :
    ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ (s : Matrix (Fin n) (Fin n) ℂ)
      (b b' : Matrix (Fin D) (Fin D) ℂ) (t : Matrix (Fin m) (Fin m) ℂ),
      s * C = C * b → s * G = G * t → s * H = H * b' → b.BlockTriangular id →
      t.BlockTriangular id → (∀ x y, x < y → b' x y = 0) → (Uᴴ * s * U).BlockTriangular id := by
  have hGC : Gᴴ * C = 0 := by
    have := congrArg conjTranspose hCG
    simpa [conjTranspose_mul] using this
  have hHC : Hᴴ * C = 0 := by
    have := congrArg conjTranspose hCH
    simpa [conjTranspose_mul] using this
  have hHG : Hᴴ * G = 0 := by
    have := congrArg conjTranspose hGH
    simpa [conjTranspose_mul] using this
  set E : Matrix (Fin n) (Fin D ⊕ (Fin m ⊕ Fin D)) ℂ := fromCols C (fromCols G H) with hEdef
  have hE : Eᴴ * E = 1 := by
    rw [hEdef, conjTranspose_fromCols_eq_fromRows_conjTranspose,
      conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul_fromCols, fromRows_mul,
      fromRows_mul, mul_fromCols, mul_fromCols, mul_fromCols, fromRows_fromCols_eq_fromBlocks,
      hCC, hCG, hCH, hGC, hGG, hGH, hHC, hHG, hHH, fromCols_zero, fromRows_zero, fromBlocks_one,
      fromBlocks_one]
  have hT : Fintype.card (FrameIdx D m) = n := by
    rw [← hcard]
    simp [Fintype.card_congr (frameEquiv D m)]
  let g : Fin n ≃ Fin D ⊕ (Fin m ⊕ Fin D) :=
    (Fintype.orderIsoFinOfCardEq (FrameIdx D m) hT).toEquiv.trans (frameEquiv D m)
  refine ⟨E.submatrix id g, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff']
    show (E.submatrix id g)ᴴ * E.submatrix id g = 1
    rw [conjTranspose_submatrix, ← submatrix_mul _ _ g id g Function.bijective_id, hE,
      submatrix_one_equiv]
  · intro s b b' t h1 h2 h3 hb ht hb'
    have hs : s * E = E * fromBlocks b 0 0 (fromBlocks t 0 0 b') := by
      rw [hEdef, mul_fromCols, mul_fromCols, h1, h2, h3, fromCols_mul_fromBlocks,
        fromCols_mul_fromBlocks]
      simp
    have hΔ : Eᴴ * s * E = fromBlocks b 0 0 (fromBlocks t 0 0 b') := by
      rw [Matrix.mul_assoc, hs, ← Matrix.mul_assoc, hE, Matrix.one_mul]
    have hM : (E.submatrix id g)ᴴ * s * E.submatrix id g =
        (fromBlocks b 0 0 (fromBlocks t 0 0 b')).submatrix g g := by
      rw [← hΔ, submatrix_mul _ _ g id g Function.bijective_id,
        submatrix_mul _ _ g id id Function.bijective_id, submatrix_id_id,
        conjTranspose_submatrix]
    rw [hM]
    intro x y hxy
    exact block_zero b b' t hb ht hb' _ _ ((Fintype.orderIsoFinOfCardEq (FrameIdx D m) hT).lt_iff_lt.2 hxy)

theorem unitary_adapted_triangularises : ∀ {n D m : ℕ} (J : Matrix (Fin n) (Fin n) ℂ)
    (J' : Matrix (Fin m) (Fin m) ℂ) (C : Matrix (Fin n) (Fin D) ℂ) (R : Matrix (Fin n) (Fin m) ℂ),
    J * J = 1 → Jᴴ = J → Cᴴ * C = 1 → Cᴴ * J * C = 0 → Rᴴ * R = 1 → J * R = R * J' →
    Cᴴ * R = 0 → C * Cᴴ + J * C * Cᴴ * J + R * Rᴴ = 1 →
    ∀ U₀ ∈ Matrix.unitaryGroup (Fin m) ℂ, ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ,
      ∀ (s : Matrix (Fin n) (Fin n) ℂ) (b b' : Matrix (Fin D) (Fin D) ℂ)
        (t : Matrix (Fin m) (Fin m) ℂ),
        s * C = C * b → s * (R * U₀) = (R * U₀) * t → s * (J * C) = (J * C) * b' →
        b.BlockTriangular id → t.BlockTriangular id → (∀ x y, x < y → b' x y = 0) →
        (Uᴴ * s * U).BlockTriangular id := by
  intro n D m J J' C R hJJ hJh hCC hCJC hRR hJR hCR hsum U₀ hU₀
  have hU : U₀ᴴ * U₀ = 1 := (Matrix.mem_unitaryGroup_iff').1 hU₀
  have hRC : Rᴴ * C = 0 := by
    have := congrArg conjTranspose hCR
    simpa [conjTranspose_mul] using this
  have hRJ : Rᴴ * J = J'ᴴ * Rᴴ := by
    have := congrArg conjTranspose hJR
    simpa [conjTranspose_mul, hJh] using this
  have t1 : trace (C * Cᴴ) = (D : ℂ) := by
    rw [trace_mul_comm, hCC, trace_one]; simp
  have t2 : trace (J * C * Cᴴ * J) = (D : ℂ) := by
    rw [trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hJJ, Matrix.one_mul, t1]
  have t3 : trace (R * Rᴴ) = (m : ℂ) := by
    rw [trace_mul_comm, hRR, trace_one]; simp
  have hcard : D + (m + D) = n := by
    have h := congrArg trace hsum
    rw [trace_add, trace_add, t1, t2, t3, trace_one] at h
    simp only [Fintype.card_fin] at h
    have h' : ((D + D + m : ℕ) : ℂ) = (n : ℂ) := by push_cast; exact h
    have h'' : D + D + m = n := by exact_mod_cast h'
    omega
  refine unitary_of_blocks C (J * C) (R * U₀) hCC ?_ ?_ ?_ ?_ ?_ hcard
  · rw [← Matrix.mul_assoc, hCR, Matrix.zero_mul]
  · rw [← Matrix.mul_assoc, hCJC]
  · rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Rᴴ, hRR, Matrix.one_mul, hU]
  · rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Rᴴ, hRJ, Matrix.mul_assoc, hRC]
    simp
  · rw [conjTranspose_mul, hJh, Matrix.mul_assoc, ← Matrix.mul_assoc J, hJJ, Matrix.one_mul, hCC]

end GlobalTheory.CompanionTheory.WittFrame
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryFramesPreserveNormSqSum
section
open Matrix

namespace GlobalTheory.CompanionTheory.UnitFrame

theorem normSq_eq_scalar_mul_form {m : ℕ} (J : Matrix (Fin m) (Fin m) ℂ) (fr : GL (Fin m) ℂ)
    (ζ : ℂ) (s : ℤˣ)
    (h : ζ • (fr.1ᵀ * J * fr.1.map star) = ((s : ℤ) : ℂ) • 1) (v : Fin m → ℂ) :
    ((∑ a, ‖((fr⁻¹).1 *ᵥ v) a‖ ^ 2 : ℝ) : ℂ) =
      (((s : ℤ) : ℂ) * star ζ) * (star v ⬝ᵥ (J.map star *ᵥ v)) := by
  obtain ⟨w, hw, hv⟩ : ∃ w, (fr⁻¹).1 *ᵥ v = w ∧ v = fr.1 *ᵥ w :=
    ⟨_, rfl, by rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]⟩
  rw [hw]
  subst hv
  have hc : ((s : ℤ) : ℂ) * ((s : ℤ) : ℂ) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have hB : star ζ • (fr.1ᵀ * J * fr.1.map star).map star =
      ((s : ℤ) : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ) := by
    ext i j
    have h1 := congrArg star (congrFun (congrFun h i) j)
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, star_mul'] at h1 ⊢
    rw [h1]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have hX : (fr.1ᵀ * J * fr.1.map star).map star = fr.1ᴴ * J.map star * fr.1 := by
    ext i j
    simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply,
      star_sum, star_mul', star_star]
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, ← hX, mul_assoc,
    ← smul_eq_mul (star ζ), ← dotProduct_smul, ← smul_mulVec, hB, smul_mulVec, one_mulVec, dotProduct_smul,
    smul_eq_mul, ← mul_assoc, hc, one_mul]
  simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.star_def, Complex.conj_mul']

theorem normSq_pos {m : ℕ} (hm : 1 ≤ m) (fr : GL (Fin m) ℂ) :
    0 < ∑ a, ‖((fr⁻¹).1 *ᵥ (Pi.single (⟨0, hm⟩ : Fin m) (1 : ℂ))) a‖ ^ 2 := by
  have hne : (fr⁻¹).1 *ᵥ (Pi.single (⟨0, hm⟩ : Fin m) (1 : ℂ)) ≠ 0 := by
    intro h0
    have h1 := congrArg (fun u => fr.1 *ᵥ u) h0
    simp only [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec,
      mulVec_zero] at h1
    exact one_ne_zero (Pi.single_eq_zero_iff.mp h1)
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hne
  exact Finset.sum_pos' (fun i _ => by positivity)
    ⟨a, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr ha) 2⟩

theorem normSq_eq_of_unit_frames : ∀ (m : ℕ), 1 ≤ m → ∀ (J : Matrix (Fin m) (Fin m) ℂ) (fr fr' : GL (Fin m) ℂ) (ζ ζ' : ℂ) (s s' : ℤˣ), (ζ = 1 ∨ ζ = Complex.I) → (ζ' = 1 ∨ ζ' = Complex.I) → ζ • (fr.1ᵀ * J * fr.1.map star) = ((s : ℤ) : ℂ) • 1 → ζ' • (fr'.1ᵀ * J * fr'.1.map star) = ((s' : ℤ) : ℂ) • 1 → ∀ v : Fin m → ℂ, ∑ a, ‖((fr⁻¹).1 *ᵥ v) a‖ ^ 2 = ∑ a, ‖((fr'⁻¹).1 *ᵥ v) a‖ ^ 2 := by
  intro m hm J fr fr' ζ ζ' s s' hζ hζ' h h' v
  have key := normSq_eq_scalar_mul_form J fr ζ s h
  have key' := normSq_eq_scalar_mul_form J fr' ζ' s' h'
  have hα : ((s : ℤ) : ℂ) * star ζ = ((s' : ℤ) : ℂ) * star ζ' := by
    have k0 := key (Pi.single (⟨0, hm⟩ : Fin m) (1 : ℂ))
    have k0' := key' (Pi.single (⟨0, hm⟩ : Fin m) (1 : ℂ))
    have hr := normSq_pos hm fr
    have hr' := normSq_pos hm fr'
    generalize (∑ a, ‖((fr⁻¹).1 *ᵥ (Pi.single (⟨0, hm⟩ : Fin m) (1 : ℂ))) a‖ ^ 2) = r at k0 hr
    generalize (∑ a, ‖((fr'⁻¹).1 *ᵥ (Pi.single (⟨0, hm⟩ : Fin m) (1 : ℂ))) a‖ ^ 2) = r' at k0' hr'
    generalize (star (Pi.single (⟨0, hm⟩ : Fin m) (1 : ℂ)) ⬝ᵥ
      (J.map star *ᵥ (Pi.single (⟨0, hm⟩ : Fin m) (1 : ℂ)))) = Q at k0 k0'
    rcases hζ with rfl | rfl <;> rcases hζ' with rfl | rfl <;>
      rcases Int.units_eq_one_or s with rfl | rfl <;>
      rcases Int.units_eq_one_or s' with rfl | rfl <;>
      simp [Complex.ext_iff] at k0 k0' ⊢ <;> linarith
  apply Complex.ofReal_injective
  rw [key v, key' v, hα]

end GlobalTheory.CompanionTheory.UnitFrame
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryLiftCommutingInvolution
section
open Matrix

namespace GlobalTheory.CompanionTheory.UnitaryAssembly

theorem exists_unitary_assemble : ∀ {n D m : ℕ} (J : Matrix (Fin n) (Fin n) ℂ) (J' : Matrix (Fin m) (Fin m) ℂ) (C : Matrix (Fin n) (Fin D) ℂ) (R : Matrix (Fin n) (Fin m) ℂ), J * J = 1 → Jᴴ = J → Cᴴ * C = 1 → Cᴴ * J * C = 0 → Rᴴ * R = 1 → J * R = R * J' → Cᴴ * R = 0 → C * Cᴴ + J * C * Cᴴ * J + R * Rᴴ = 1 → ∀ k₀ ∈ Matrix.unitaryGroup (Fin D) ℂ, ∀ kR ∈ Matrix.unitaryGroup (Fin m) ℂ, kR * J' = J' * kR → ∃ k ∈ Matrix.unitaryGroup (Fin n) ℂ, k * J = J * k ∧ k * C = C * k₀ ∧ kᴴ * C = C * k₀ᴴ ∧ kᴴ * R = R * kRᴴ ∧ kᴴ * (J * C) = (J * C) * k₀ᴴ := by
  intro n D m J J' C R hJJ hJh hCC hCJC hRR hJR hCR hsum k₀ hk₀ kR hkR hkRJ
  rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose] at hk₀ hkR
  have hRC : Rᴴ * C = 0 := by
    have h := congrArg conjTranspose hCR
    simpa [conjTranspose_mul] using h
  have hJ'h : J'ᴴ = J' := by
    have h1 : J' = Rᴴ * (J * R) := by
      rw [hJR, ← Matrix.mul_assoc, hRR, Matrix.one_mul]
    rw [h1]
    simp [conjTranspose_mul, hJh, Matrix.mul_assoc]
  have hRJ : Rᴴ * J = J' * Rᴴ := by
    have h := congrArg conjTranspose hJR
    simpa only [conjTranspose_mul, hJh, hJ'h] using h
  have c2 : Cᴴ * (J * C) = 0 := by rw [← Matrix.mul_assoc]; exact hCJC
  have a1 : ∀ {p : Type} (X : Matrix (Fin D) p ℂ), Cᴴ * (C * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hCC, Matrix.one_mul]
  have a2 : ∀ {p : Type} (X : Matrix (Fin D) p ℂ), Cᴴ * (J * (C * X)) = 0 := fun X => by
    rw [← Matrix.mul_assoc J C X, ← Matrix.mul_assoc, c2, Matrix.zero_mul]
  have a3 : ∀ {p : Type} (X : Matrix (Fin m) p ℂ), Cᴴ * (R * X) = 0 := fun X => by
    rw [← Matrix.mul_assoc, hCR, Matrix.zero_mul]
  have a4 : ∀ {p : Type} (X : Matrix (Fin m) p ℂ), Rᴴ * (R * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hRR, Matrix.one_mul]
  have a5 : ∀ {p : Type} (X : Matrix (Fin D) p ℂ), Rᴴ * (C * X) = 0 := fun X => by
    rw [← Matrix.mul_assoc, hRC, Matrix.zero_mul]
  have a6 : ∀ {p : Type} (X : Matrix (Fin n) p ℂ), J * (J * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  have a7 : ∀ {p : Type} (X : Matrix (Fin m) p ℂ), J * (R * X) = R * (J' * X) := fun X => by
    rw [← Matrix.mul_assoc, hJR, Matrix.mul_assoc]
  have a8 : ∀ {p : Type} (X : Matrix (Fin n) p ℂ), Rᴴ * (J * X) = J' * (Rᴴ * X) := fun X => by
    rw [← Matrix.mul_assoc, hRJ, Matrix.mul_assoc]
  have a9 : ∀ {p : Type} (X : Matrix (Fin D) p ℂ), k₀ * (k₀ᴴ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hk₀, Matrix.one_mul]
  have a10 : ∀ {p : Type} (X : Matrix (Fin m) p ℂ), kR * (kRᴴ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hkR, Matrix.one_mul]
  have a11 : ∀ {p : Type} (X : Matrix (Fin m) p ℂ), kR * (J' * X) = J' * (kR * X) := fun X => by
    rw [← Matrix.mul_assoc, hkRJ, Matrix.mul_assoc]
  have hs : C * Cᴴ + J * (C * (Cᴴ * J)) + R * Rᴴ = 1 := by
    simpa only [Matrix.mul_assoc] using hsum
  refine ⟨C * k₀ * Cᴴ + J * C * k₀ * Cᴴ * J + R * kR * Rᴴ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose]
    simp only [Matrix.add_mul, Matrix.mul_add, conjTranspose_add, conjTranspose_mul,
      conjTranspose_conjTranspose, hJh, Matrix.mul_assoc, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10,
      hCC, c2, hCR, hRR, hRC, hJJ, hJR, hRJ, hk₀, hkR, Matrix.mul_zero, Matrix.zero_mul,
      add_zero, zero_add, Matrix.mul_one, Matrix.one_mul]
    rw [← hs]
  all_goals
    simp only [Matrix.add_mul, Matrix.mul_add, conjTranspose_add, conjTranspose_mul,
      conjTranspose_conjTranspose, hJh, Matrix.mul_assoc, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10,
      a11, hCC, c2, hCR, hRR, hRC, hJJ, hJR, hRJ, hk₀, hkR, hkRJ, Matrix.mul_zero, Matrix.zero_mul,
      add_zero, zero_add, Matrix.mul_one, Matrix.one_mul]
    try abel

end GlobalTheory.CompanionTheory.UnitaryAssembly
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VandermondeSeparation
section
namespace GlobalTheory.CompanionTheory.ExpSums

open Matrix in

theorem vandermonde_separation (r : ℕ) (α : Fin r → ℂ) (hα : Function.Injective α) :
    ∃ C : ℝ, ∀ (c : Fin r → ℂ) (i : Fin r),
      ‖c i‖ ≤ C * ∑ s : Fin r, ‖∑ k, c k * α k ^ (s : ℕ)‖ := by
  classical
  obtain ⟨V, hV⟩ : ∃ V : Matrix (Fin r) (Fin r) ℂ, V = Matrix.vandermonde α := ⟨_, rfl⟩
  have hdet : IsUnit V.det := by
    rw [isUnit_iff_ne_zero, hV]
    exact Matrix.det_vandermonde_ne_zero_iff.mpr hα
  refine ⟨∑ s : Fin r, ∑ j : Fin r, ‖V⁻¹ s j‖, ?_⟩
  intro c i
  have hsum : ∀ s : Fin r, Matrix.vecMul c V s = ∑ k, c k * α k ^ (s : ℕ) := by
    intro s
    simp [Matrix.vecMul, dotProduct, hV, Matrix.vandermonde_apply]
  have hc : c = Matrix.vecMul (Matrix.vecMul c V) V⁻¹ := by
    rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hdet, Matrix.vecMul_one]
  have hC : ∀ s : Fin r, ‖V⁻¹ s i‖ ≤ ∑ s : Fin r, ∑ j : Fin r, ‖V⁻¹ s j‖ := fun s =>
    (Finset.single_le_sum (f := fun j => ‖V⁻¹ s j‖) (fun j _ => norm_nonneg _)
      (Finset.mem_univ i)).trans
    (Finset.single_le_sum (f := fun s => ∑ j, ‖V⁻¹ s j‖)
      (fun s _ => Finset.sum_nonneg fun j _ => norm_nonneg _) (Finset.mem_univ s))
  calc ‖c i‖ = ‖Matrix.vecMul (Matrix.vecMul c V) V⁻¹ i‖ := by rw [← hc]
    _ = ‖∑ s, Matrix.vecMul c V s * V⁻¹ s i‖ := rfl
    _ ≤ ∑ s, ‖Matrix.vecMul c V s * V⁻¹ s i‖ := norm_sum_le _ _
    _ = ∑ s, ‖Matrix.vecMul c V s‖ * ‖V⁻¹ s i‖ := by simp_rw [norm_mul]
    _ ≤ ∑ s, ‖Matrix.vecMul c V s‖ * ∑ s : Fin r, ∑ j : Fin r, ‖V⁻¹ s j‖ :=
      Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hC s) (norm_nonneg _)
    _ = (∑ s : Fin r, ∑ j : Fin r, ‖V⁻¹ s j‖) * ∑ s : Fin r, ‖∑ k, c k * α k ^ (s : ℕ)‖ := by
      rw [← Finset.sum_mul, mul_comm]
      congr 1
      exact Finset.sum_congr rfl fun s _ => by rw [hsum]

end GlobalTheory.CompanionTheory.ExpSums
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightedAntitoneLastNonpos
section
namespace GlobalTheory.CompanionTheory.Inequalities

theorem weighted_antitone_last_nonpos : ∀ (h : ℕ) (d e : Fin h → ℝ), 2 ≤ h → (∀ i, 0 < d i) →
    Antitone e → ∑ i, d i * e i = 0 →
    ∃ j : Fin h, 0 < j.val ∧ ∑ i ∈ Finset.univ.filter (fun i => j ≤ i), d i * e i ≤ 0 := by
  intro h d e hh hd he hs
  obtain ⟨n, rfl⟩ : ∃ n, h = n + 2 := ⟨h - 2, by omega⟩
  refine ⟨Fin.last (n + 1), by simp, ?_⟩
  have hf : Finset.univ.filter (fun i : Fin (n + 2) => Fin.last (n + 1) ≤ i)
      = {Fin.last (n + 1)} := by
    ext i
    simp [Fin.last_le_iff]
  rw [hf, Finset.sum_singleton]
  have hle : (∑ i, d i) * e (Fin.last (n + 1)) ≤ 0 := by
    rw [Finset.sum_mul, ← hs]
    exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (he (Fin.le_last i)) (hd i).le
  have hpos : 0 < ∑ i, d i :=
    Finset.sum_pos (fun i _ => hd i) ⟨Fin.last _, Finset.mem_univ _⟩
  have hel : e (Fin.last (n + 1)) ≤ 0 := by
    by_contra hc
    exact absurd (mul_pos hpos (not_le.mp hc)) (not_lt.mpr hle)
  exact mul_nonpos_of_nonneg_of_nonpos (hd _).le hel

end GlobalTheory.CompanionTheory.Inequalities
end

