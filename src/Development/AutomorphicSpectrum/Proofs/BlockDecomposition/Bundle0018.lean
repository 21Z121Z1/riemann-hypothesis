import Mathlib

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieAlgebraFunctionCalculus
section
open Matrix Topology Filter

namespace GlobalTheory.CompanionTheory.AdProj

noncomputable def entryMul {n : ℕ} (h : Fin n → ℝ) (g : ℝ → ℝ)
    (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => (g (h i - h j) : ℂ) * X i j

theorem diagonal_commutator {n : ℕ} (h : Fin n → ℝ) (X : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.diagonal (fun i => (h i : ℂ)) * X - X * Matrix.diagonal (fun i => (h i : ℂ))
      = entryMul h (fun t => t) X := by
  ext i j
  simp only [entryMul, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.of_apply]
  push_cast
  ring

theorem entryMul_pow_mem {n : ℕ} (𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (h : Fin n → ℝ)
    (hD : Matrix.diagonal (fun i => (h i : ℂ)) ∈ 𝔤)
    (hbr : ∀ X ∈ 𝔤, ∀ Y ∈ 𝔤, X * Y - Y * X ∈ 𝔤)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ 𝔤) (k : ℕ) :
    entryMul h (fun t => t ^ k) X ∈ 𝔤 := by
  induction k with
  | zero =>
    have h0 : entryMul h (fun t => t ^ 0) X = X := by
      ext i j
      simp [entryMul]
    rw [h0]
    exact hX
  | succ k ih =>
    have hs : entryMul h (fun t => t ^ (k + 1)) X =
        Matrix.diagonal (fun i => (h i : ℂ)) * entryMul h (fun t => t ^ k) X -
          entryMul h (fun t => t ^ k) X * Matrix.diagonal (fun i => (h i : ℂ)) := by
      rw [diagonal_commutator]
      ext i j
      simp only [entryMul, Matrix.of_apply]
      push_cast
      ring
    rw [hs]
    exact hbr _ hD _ ih

theorem entryMul_poly_mem {n : ℕ} (𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (h : Fin n → ℝ)
    (hD : Matrix.diagonal (fun i => (h i : ℂ)) ∈ 𝔤)
    (hbr : ∀ X ∈ 𝔤, ∀ Y ∈ 𝔤, X * Y - Y * X ∈ 𝔤)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ 𝔤) (p : Polynomial ℝ) :
    entryMul h (fun t => p.eval t) X ∈ 𝔤 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    have hs : entryMul h (fun t => (p + q).eval t) X =
        entryMul h (fun t => p.eval t) X + entryMul h (fun t => q.eval t) X := by
      ext i j
      simp only [entryMul, Matrix.of_apply, Matrix.add_apply, Polynomial.eval_add]
      push_cast
      ring
    rw [hs]
    exact 𝔤.add_mem hp hq
  | monomial m a =>
    have hs : entryMul h (fun t => (Polynomial.monomial m a).eval t) X =
        a • entryMul h (fun t => t ^ m) X := by
      ext i j
      simp only [entryMul, Matrix.of_apply, Matrix.smul_apply, Polynomial.eval_monomial,
        Complex.real_smul]
      push_cast
      ring
    rw [hs]
    exact 𝔤.smul_mem a (entryMul_pow_mem 𝔤 h hD hbr hX m)

theorem mem_of_entrywise {n : ℕ} (𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (h : Fin n → ℝ) :
    Matrix.diagonal (fun i => (h i : ℂ)) ∈ 𝔤 → (∀ X ∈ 𝔤, ∀ Y ∈ 𝔤, X * Y - Y * X ∈ 𝔤) →
      ∀ (f : ℝ → ℝ), ∀ X ∈ 𝔤, (Matrix.of fun i j => (f (h i - h j) : ℂ) * X i j) ∈ 𝔤 := by
  intro hD hbr f X hX
  obtain ⟨S, hS⟩ : ∃ S : Finset ℝ, ∀ i j, h i - h j ∈ S :=
    ⟨Finset.univ.image (fun q : Fin n × Fin n => h q.1 - h q.2),
      fun i j => Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩⟩
  have key : ∀ x ∈ S, (Lagrange.interpolate S id f).eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (v := id) (s := S) (r := f) Function.injective_id.injOn hx
  obtain ⟨p, hp⟩ : ∃ p : Polynomial ℝ, ∀ i j, p.eval (h i - h j) = f (h i - h j) :=
    ⟨Lagrange.interpolate S id f, fun i j => key _ (hS i j)⟩
  have heq : (Matrix.of fun i j => (f (h i - h j) : ℂ) * X i j) = entryMul h (fun t => p.eval t) X := by
    ext i j
    simp only [entryMul, Matrix.of_apply, hp]
  rw [heq]
  exact entryMul_poly_mem 𝔤 h hD hbr hX p

end GlobalTheory.CompanionTheory.AdProj
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieAlgebraStarClosedBracket
section
open Matrix

namespace GlobalTheory.CompanionTheory.UnitaryBlock

theorem block_diagonal_of_keeps_frame : ∀ {n D m : ℕ} (J : Matrix (Fin n) (Fin n) ℂ)
    (J' : Matrix (Fin m) (Fin m) ℂ) (C : Matrix (Fin n) (Fin D) ℂ)
    (R : Matrix (Fin n) (Fin m) ℂ), J * J = 1 → Jᴴ = J → Cᴴ * C = 1 → Rᴴ * R = 1 →
    J * R = R * J' → Cᴴ * R = 0 → C * Cᴴ + J * C * Cᴴ * J + R * Rᴴ = 1 →
    ∀ (g : Matrix (Fin n) (Fin n) ℂ) (h : Matrix (Fin D) (Fin D) ℂ), gᴴ * J * g = J →
    g * C = C * h → gᴴ * C = C * hᴴ →
    IsUnit h ∧ g * (J * C) = (J * C) * (hᴴ)⁻¹ ∧ g * R = R * (Rᴴ * g * R) ∧
      (Rᴴ * g * R)ᴴ * J' * (Rᴴ * g * R) = J' := by
  intro n D m J J' C R hJJ hJh hC hR hJR hCR hsum g h hg hgC hgHC
  have hl : (J * gᴴ * J) * g = 1 := by
    calc (J * gᴴ * J) * g = J * (gᴴ * J * g) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg, hJJ]
  have hr : g * (J * gᴴ * J) = 1 := mul_eq_one_comm.mp hl
  have hgJ : g * J * gᴴ = J := by
    calc g * J * gᴴ = g * (J * gᴴ * J) * J := by
          simp only [Matrix.mul_assoc, hJJ, Matrix.mul_one]
      _ = J := by rw [hr, Matrix.one_mul]

  obtain ⟨k, hkdef⟩ : ∃ k, k = Cᴴ * (J * gᴴ * J) * C := ⟨_, rfl⟩
  have hk : k * h = 1 := by
    calc k * h = Cᴴ * (J * gᴴ * J) * (C * h) := by
          rw [hkdef]; simp only [Matrix.mul_assoc]
      _ = Cᴴ * ((J * gᴴ * J) * g) * C := by
          rw [← hgC]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hl, Matrix.mul_one, hC]
  have hk' : h * k = 1 := mul_eq_one_comm.mp hk
  have hunit : IsUnit h := ⟨⟨h, k, hk', hk⟩, rfl⟩
  have hdet : IsUnit hᴴ.det := by
    have : IsUnit hᴴ := by
      refine ⟨⟨hᴴ, kᴴ, ?_, ?_⟩, rfl⟩
      · rw [← Matrix.conjTranspose_mul, hk, Matrix.conjTranspose_one]
      · rw [← Matrix.conjTranspose_mul, hk', Matrix.conjTranspose_one]
    exact (Matrix.isUnit_iff_isUnit_det _).mp this
  have hJC : g * (J * C) * hᴴ = J * C := by
    calc g * (J * C) * hᴴ = g * J * (C * hᴴ) := by simp only [Matrix.mul_assoc]
      _ = g * J * gᴴ * C := by rw [← hgHC]; simp only [Matrix.mul_assoc]
      _ = J * C := by rw [hgJ]
  have hsecond : g * (J * C) = (J * C) * (hᴴ)⁻¹ := by
    calc g * (J * C) = g * (J * C) * (hᴴ * (hᴴ)⁻¹) := by
          rw [Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
      _ = (g * (J * C) * hᴴ) * (hᴴ)⁻¹ := by simp only [Matrix.mul_assoc]
      _ = (J * C) * (hᴴ)⁻¹ := by rw [hJC]

  have hgpC : (J * gᴴ * J) * C = C * k := by
    calc (J * gᴴ * J) * C = (J * gᴴ * J) * C * (h * k) := by rw [hk', Matrix.mul_one]
      _ = (J * gᴴ * J) * (C * h) * k := by simp only [Matrix.mul_assoc]
      _ = ((J * gᴴ * J) * g) * C * k := by rw [← hgC]; simp only [Matrix.mul_assoc]
      _ = C * k := by rw [hl, Matrix.one_mul]
  have hCgR : Cᴴ * (g * R) = 0 := by
    have hadj : Cᴴ * g = h * Cᴴ := by
      have := congrArg Matrix.conjTranspose hgHC
      simpa [Matrix.conjTranspose_mul] using this
    calc Cᴴ * (g * R) = (Cᴴ * g) * R := by simp only [Matrix.mul_assoc]
      _ = h * (Cᴴ * R) := by rw [hadj, Matrix.mul_assoc]
      _ = 0 := by rw [hCR, Matrix.mul_zero]
  have hgHJC : gᴴ * J * C = J * C * k := by
    calc gᴴ * J * C = (J * J) * (gᴴ * J * C) := by rw [hJJ, Matrix.one_mul]
      _ = J * ((J * gᴴ * J) * C) := by simp only [Matrix.mul_assoc]
      _ = J * C * k := by rw [hgpC, Matrix.mul_assoc]
  have hCJg : Cᴴ * J * g = kᴴ * Cᴴ * J := by
    have := congrArg Matrix.conjTranspose hgHJC
    simpa [Matrix.conjTranspose_mul, hJh, Matrix.mul_assoc] using this
  have hCJgR : Cᴴ * J * (g * R) = 0 := by
    calc Cᴴ * J * (g * R) = (Cᴴ * J * g) * R := by simp only [Matrix.mul_assoc]
      _ = kᴴ * Cᴴ * (J * R) := by rw [hCJg]; simp only [Matrix.mul_assoc]
      _ = kᴴ * (Cᴴ * R) * J' := by rw [hJR]; simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hCR, Matrix.mul_zero, Matrix.zero_mul]
  have hthird : g * R = R * (Rᴴ * g * R) := by
    calc g * R = (C * Cᴴ + J * C * Cᴴ * J + R * Rᴴ) * (g * R) := by rw [hsum, Matrix.one_mul]
      _ = C * (Cᴴ * (g * R)) + J * C * (Cᴴ * J * (g * R)) + R * (Rᴴ * g * R) := by
          simp only [Matrix.add_mul, Matrix.mul_assoc]
      _ = R * (Rᴴ * g * R) := by rw [hCgR, hCJgR]; simp
  refine ⟨hunit, hsecond, hthird, ?_⟩
  have hRJ : R * J' = J * R := hJR.symm
  have hRhJR : Rᴴ * J * R = J' := by
    calc Rᴴ * J * R = Rᴴ * (J * R) := by rw [Matrix.mul_assoc]
      _ = Rᴴ * R * J' := by rw [hJR, Matrix.mul_assoc]
      _ = J' := by rw [hR, Matrix.one_mul]
  calc (Rᴴ * g * R)ᴴ * J' * (Rᴴ * g * R)
      = Rᴴ * gᴴ * (R * J') * (Rᴴ * g * R) := by
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    _ = Rᴴ * gᴴ * J * (R * (Rᴴ * g * R)) := by rw [hRJ]; simp only [Matrix.mul_assoc]
    _ = Rᴴ * (gᴴ * J * g) * R := by rw [← hthird]; simp only [Matrix.mul_assoc]
    _ = J' := by rw [hg, hRhJR]

end GlobalTheory.CompanionTheory.UnitaryBlock
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearMapZeroOfInjectiveFullRank
section
open TensorProduct

namespace GlobalTheory.CompanionTheory.Perf

theorem map_eq_zero_of_comp_injective_of_finrank_eq :
    ∀ (A W N : Type) [CommRing A] [Nontrivial A] [AddCommGroup W] [Module A W] [AddCommGroup N]
      [Module A N] [Module.Free A W] [Module.Finite A W] [Module.Free A N] (g : ℕ)
      (φ : (Fin g → A) →ₗ[A] W) (f : W →ₗ[A] N),
      Module.finrank A W = g → Function.Injective φ → f ∘ₗ φ = 0 → f = 0 := by
  intro A W N _ _ _ _ _ _ _ _ _ g φ f hg hφ hf
  classical
  let e : W ≃ₗ[A] (Fin g → A) := (Module.finBasisOfFinrankEq A W hg).equivFun
  let M : Matrix (Fin g) (Fin g) A := LinearMap.toMatrix' (e.toLinearMap ∘ₗ φ)
  have hM : ∀ v, Matrix.mulVec M v = e (φ v) := fun v => by
    change Matrix.toLin' M v = _
    rw [Matrix.toLin'_toMatrix']
    rfl
  have hinj : Function.Injective M.mulVec := by
    intro v v' h
    rw [hM, hM] at h
    exact hφ (e.injective h)
  have hdet : M.det ∈ nonZeroDivisors A :=
    Matrix.nonsingular_iff_det_mem_nonZeroDivisors.mp
      (Matrix.Nonsingular.of_linearIndependent_col (Matrix.mulVec_injective_iff.mp hinj))
  have hkill : ∀ w, M.det • f w = 0 := by
    intro w
    have h1 : φ (M.cramer (e w)) = M.det • w := by
      apply e.injective
      rw [← hM, Matrix.mulVec_cramer, map_smul]
    rw [← map_smul, ← h1]
    exact LinearMap.congr_fun hf _
  ext w
  apply (Module.Free.chooseBasis A N).repr.injective
  ext i
  have h2 := congrArg (fun n => (Module.Free.chooseBasis A N).repr n i) (hkill w)
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.coe_zero,
    Pi.zero_apply] at h2
  simpa using (mul_left_mem_nonZeroDivisors_eq_zero_iff hdet).mp h2

end GlobalTheory.CompanionTheory.Perf
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralUniformNearParameter
section
open MeasureTheory
open scoped ENNReal NNReal Topology

namespace GlobalTheory.CompanionTheory.FibSch

theorem weight_le_of_one_add_le {a b M : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ)
    (h : 1 + a ≤ M * (1 + b)) :
    (1 + b) ^ (-(n : ℝ)) ≤ M ^ n * (1 + a) ^ (-(n : ℝ)) := by
  have ha' : 0 < 1 + a := by linarith
  have hb' : 0 < 1 + b := by linarith
  rw [Real.rpow_neg ha'.le, Real.rpow_neg hb'.le, Real.rpow_natCast, Real.rpow_natCast,
    ← div_eq_mul_inv, le_div_iff₀ (pow_pos ha' n), inv_mul_le_iff₀ (pow_pos hb' n), ← mul_pow]
  rw [mul_comm (1 + b) M]
  exact pow_le_pow_left₀ ha'.le h n

theorem integral_comp_additive_continuousAt :
    ∀ (X P : Type) [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
      [TopologicalSpace P] [FirstCountableTopology P] (N : ℕ) (e : X ≃+ (Fin N → ℝ)),
      Continuous e → ∀ (c : P) (m0 : Measure X) (A : P → X →+ X), (∀ s, Continuous (A s)) →
      (∀ x, Filter.Tendsto (fun s => A s x) (nhds c) (nhds (A c x))) → ∀ δ : ℝ, 0 < δ →
      (∀ᶠ s in nhds c, ∀ x, δ * ‖e x‖ ≤ ‖e (A s x)‖) →
      ∫⁻ x, ENNReal.ofReal ((1 + ‖e x‖) ^ (-((N + 1 : ℕ) : ℝ))) ∂m0 ≠ ⊤ →
      ∀ (u : (Fin N → ℝ) → ℂ) (C : ℝ), Continuous u →
      (∀ y, ‖u y‖ ≤ C * (1 + ‖y‖) ^ (-((N + 1 : ℕ) : ℝ))) →
      (∀ᶠ s in nhds c, Integrable (fun x => u (e (A s x))) m0) ∧
        ContinuousAt (fun s => ∫ x, u (e (A s x)) ∂m0) c := by
  intro X P _ _ _ _ _ _ N e he c m0 A hA hlim δ hδ hev hfin u C hu hub
  have hw_cont : Continuous fun x => (1 + ‖e x‖) ^ (-((N + 1 : ℕ) : ℝ)) :=
    (continuous_const.add he.norm).rpow_const (fun x => Or.inl (by positivity : (0 : ℝ) < 1 + ‖e x‖).ne')
  have hw_nonneg : ∀ x, 0 ≤ (1 + ‖e x‖) ^ (-((N + 1 : ℕ) : ℝ)) :=
    fun x => Real.rpow_nonneg (by positivity) _
  have hw_int : Integrable (fun x => (1 + ‖e x‖) ^ (-((N + 1 : ℕ) : ℝ))) m0 := by
    refine ⟨hw_cont.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hw_nonneg)]
    exact lt_top_iff_ne_top.mpr hfin
  have hM : ∀ a b : ℝ, 0 ≤ a → δ * a ≤ b → 1 + a ≤ max 1 (1 / δ) * (1 + b) := by
    intro a b ha hab
    have h1 : (1 : ℝ) ≤ max 1 (1 / δ) := le_max_left _ _
    have h2 : 1 / δ ≤ max 1 (1 / δ) := le_max_right _ _
    have hb : 0 ≤ b := le_trans (mul_nonneg hδ.le ha) hab
    have h3 : a ≤ 1 / δ * b := by
      rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hδ, mul_comm]
      exact hab
    have h4 : a ≤ max 1 (1 / δ) * b := h3.trans (mul_le_mul_of_nonneg_right h2 hb)
    rw [mul_add, mul_one]
    linarith
  have hbound : ∀ᶠ s in nhds c, ∀ x, ‖u (e (A s x))‖ ≤
      |C| * max 1 (1 / δ) ^ (N + 1) * (1 + ‖e x‖) ^ (-((N + 1 : ℕ) : ℝ)) := by
    filter_upwards [hev] with s hs x
    have hb := GlobalTheory.CompanionTheory.FibSch.weight_le_of_one_add_le (norm_nonneg (e x))
      (norm_nonneg (e (A s x))) (N + 1) (hM _ _ (norm_nonneg _) (hs x))
    calc ‖u (e (A s x))‖ ≤ C * (1 + ‖e (A s x)‖) ^ (-((N + 1 : ℕ) : ℝ)) := hub _
      _ ≤ |C| * (1 + ‖e (A s x)‖) ^ (-((N + 1 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg (by positivity) _)
      _ ≤ |C| * (max 1 (1 / δ) ^ (N + 1) * (1 + ‖e x‖) ^ (-((N + 1 : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_left hb (abs_nonneg C)
      _ = |C| * max 1 (1 / δ) ^ (N + 1) * (1 + ‖e x‖) ^ (-((N + 1 : ℕ) : ℝ)) := by
          rw [mul_assoc]
  have hg_int := hw_int.const_mul (|C| * max 1 (1 / δ) ^ (N + 1))
  have hmeas : ∀ s, AEStronglyMeasurable (fun x => u (e (A s x))) m0 :=
    fun s => (hu.comp (he.comp (hA s))).aestronglyMeasurable
  refine ⟨?_, ?_⟩
  · filter_upwards [hbound] with s hs
    exact hg_int.mono' (hmeas s) (Filter.Eventually.of_forall hs)
  · exact tendsto_integral_filter_of_dominated_convergence _
      (Filter.Eventually.of_forall hmeas) (hbound.mono fun s hs => Filter.Eventually.of_forall hs)
      hg_int (Filter.Eventually.of_forall fun x => (hu.comp he).continuousAt.tendsto.comp (hlim x))

end GlobalTheory.CompanionTheory.FibSch
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalContinuousSectionVecMulOrbit
section
open Matrix
open scoped Topology

namespace GlobalTheory.CompanionTheory.OrbitSection

section Shear

variable {k : Type} [Field k] {n : ℕ}

noncomputable def shear (j : Fin n) (c : k) (ζ ξ : Fin n → k) : Matrix (Fin n) (Fin n) k :=
  1 + c • vecMulVec (Pi.single j 1) (ξ - ζ)

theorem shear_mul_shear (j : Fin n) (ζ ξ : Fin n → k) (h0 : ζ j ≠ 0) (h1 : ξ j ≠ 0) :
    shear j (ζ j)⁻¹ ζ ξ * shear j (-(ξ j)⁻¹) ζ ξ = 1 := by
  have hE : vecMulVec (Pi.single j (1 : k)) (ξ - ζ) * vecMulVec (Pi.single j 1) (ξ - ζ)
      = (ξ j - ζ j) • vecMulVec (Pi.single j (1 : k)) (ξ - ζ) := by
    rw [vecMulVec_mul_vecMulVec, vecMulVec_smul]
    simp
  have hc : (ζ j)⁻¹ + -(ξ j)⁻¹ + (ζ j)⁻¹ * -(ξ j)⁻¹ * (ξ j - ζ j) = 0 := by
    field_simp
    ring
  have key : ∀ E : Matrix (Fin n) (Fin n) k, E * E = (ξ j - ζ j) • E →
      (1 + (ζ j)⁻¹ • E) * (1 + (-(ξ j)⁻¹) • E) = 1 := by
    intro E hEE
    have : (1 + (ζ j)⁻¹ • E) * (1 + (-(ξ j)⁻¹) • E)
        = 1 + ((ζ j)⁻¹ + -(ξ j)⁻¹ + (ζ j)⁻¹ * -(ξ j)⁻¹ * (ξ j - ζ j)) • E := by
      simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, hEE]
      module
    rw [this, hc, zero_smul, add_zero]
  exact key _ hE

theorem vecMul_shear (j : Fin n) (ζ ξ : Fin n → k) (h0 : ζ j ≠ 0) :
    ζ ᵥ* shear j (ζ j)⁻¹ ζ ξ = ξ := by
  have : ζ ᵥ* vecMulVec (Pi.single j (1 : k)) (ξ - ζ) = (ζ j) • (ξ - ζ) := by
    rw [vecMul_vecMulVec]
    simp
  rw [shear, vecMul_add, vecMul_one, vecMul_smul, this, smul_smul, inv_mul_cancel₀ h0, one_smul]
  abel

theorem shear_self (j : Fin n) (c : k) (ζ : Fin n → k) : shear j c ζ ζ = 1 := by
  simp [shear]

open Classical in

noncomputable def orbitSection (j : Fin n) (ζ ξ : Fin n → k) : GL (Fin n) k :=
  if h : ζ j ≠ 0 ∧ ξ j ≠ 0 then
    ⟨shear j (ζ j)⁻¹ ζ ξ, shear j (-(ξ j)⁻¹) ζ ξ, shear_mul_shear j ζ ξ h.1 h.2,
      mul_eq_one_comm.mp (shear_mul_shear j ζ ξ h.1 h.2)⟩
  else 1

theorem coe_orbitSection (j : Fin n) (ζ ξ : Fin n → k) (h0 : ζ j ≠ 0) (h1 : ξ j ≠ 0) :
    (orbitSection j ζ ξ : Matrix (Fin n) (Fin n) k) = shear j (ζ j)⁻¹ ζ ξ := by
  rw [orbitSection, dif_pos ⟨h0, h1⟩]

theorem coe_orbitSection_inv (j : Fin n) (ζ ξ : Fin n → k) (h0 : ζ j ≠ 0) (h1 : ξ j ≠ 0) :
    ((orbitSection j ζ ξ)⁻¹ : (Matrix (Fin n) (Fin n) k)ˣ).val = shear j (-(ξ j)⁻¹) ζ ξ := by
  rw [orbitSection, dif_pos ⟨h0, h1⟩]
  rfl

end Shear

section Top

variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalDivisionRing k] {n : ℕ}

theorem continuousOn_shear (j : Fin n) (ζ : Fin n → k) {N : Set (Fin n → k)} {c : (Fin n → k) → k}
    (hc : ContinuousOn c N) : ContinuousOn (fun ξ => shear j (c ξ) ζ ξ) N := by
  refine continuousOn_pi.2 fun a => continuousOn_pi.2 fun b => ?_
  simp only [shear, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, Pi.sub_apply, smul_eq_mul]
  refine continuousOn_const.add (hc.mul (continuousOn_const.mul ?_))
  exact ((continuous_apply b).sub continuous_const).continuousOn

theorem continuousOn_orbitSection (j : Fin n) (ζ : Fin n → k) (h0 : ζ j ≠ 0) :
    ContinuousOn (orbitSection j ζ) {ξ | ξ j ≠ 0} := by
  have hinv : ContinuousOn (fun ξ : Fin n → k => -(ξ j)⁻¹) {ξ | ξ j ≠ 0} :=
    (((continuous_apply j).continuousOn).inv₀ fun ξ h => h).neg
  rw [continuousOn_iff_continuous_restrict, Units.continuous_iff]
  refine ⟨(continuousOn_iff_continuous_restrict.1
      (continuousOn_shear j ζ (c := fun _ => (ζ j)⁻¹) continuousOn_const)).congr fun ξ => ?_,
    (continuousOn_iff_continuous_restrict.1 (continuousOn_shear j ζ hinv)).congr fun ξ => ?_⟩
  · exact (coe_orbitSection j ζ ξ.1 h0 ξ.2).symm
  · exact (coe_orbitSection_inv j ζ ξ.1 h0 ξ.2).symm

end Top

theorem exists_local_section : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ζ : Fin n → k), ζ ≠ 0 → ∃ N : Set (Fin n → k), IsOpen N ∧ ζ ∈ N ∧ ∃ f : (Fin n → k) → GL (Fin n) k, ContinuousOn f N ∧ f ζ = 1 ∧ ∀ ξ ∈ N, ζ ᵥ* (f ξ : Matrix (Fin n) (Fin n) k) = ξ := by
  intro k _ _ _ _ n ζ hζ
  haveI : T2Space k := by
    letI := IsTopologicalAddGroup.rightUniformSpace k
    haveI := isUniformAddGroup_of_addCommGroup (G := k)
    infer_instance
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hζ
  have hj' : ζ j ≠ 0 := hj
  refine ⟨{ξ | ξ j ≠ 0}, isOpen_ne.preimage (continuous_apply j), hj', orbitSection j ζ,
    continuousOn_orbitSection j ζ hj', ?_, fun ξ hξ => ?_⟩
  · apply Units.ext
    rw [coe_orbitSection j ζ ζ hj' hj', shear_self]
    rfl
  · rw [coe_orbitSection j ζ ξ hj' hξ, vecMul_shear j ζ ξ hj']

end GlobalTheory.CompanionTheory.OrbitSection
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalSplittingKernelBaseChange
section
open TensorProduct

namespace GlobalTheory.CompanionTheory.RegularLocal

theorem regular_of_regular_at_maximal : ∀ (R Q P : Type) [CommRing R] [AddCommGroup Q] [Module R Q] [AddCommGroup P] [Module R P] [Module.Finite R Q] [Module.Projective R Q] [Module.Finite R P] [Module.Projective R P] (d : Q →ₗ[R] P), (∀ (p : Ideal R) [p.IsMaximal], ∃ r : Localization.AtPrime p ⊗[R] P →ₗ[Localization.AtPrime p] Localization.AtPrime p ⊗[R] Q, d.baseChange (Localization.AtPrime p) ∘ₗ r ∘ₗ d.baseChange (Localization.AtPrime p) = d.baseChange (Localization.AtPrime p)) → ∃ r : P →ₗ[R] Q, d ∘ₗ r ∘ₗ d = d := by
  intro R Q P _ _ _ _ _ _ _ _ _ d h
  have hex : Function.Exact d (LinearMap.range d).mkQ := LinearMap.exact_map_mkQ_range d
  have hsurj : Function.Surjective (LinearMap.range d).mkQ := Submodule.mkQ_surjective _

  have hloc : ∀ (p : Ideal R) [p.IsMaximal], Module.Flat (Localization.AtPrime p)
      (Localization.AtPrime p ⊗[R] (P ⧸ LinearMap.range d)) := by
    intro p _
    obtain ⟨r, hr⟩ := h p
    set A := Localization.AtPrime p
    set dA := d.baseChange A with hdA
    set πA := (LinearMap.range d).mkQ.baseChange A with hπA
    have hexA : Function.Exact dA πA := by
      have := lTensor_exact A hex hsurj
      simpa [hdA, hπA, LinearMap.baseChange_eq_ltensor] using this
    have hsA : Function.Surjective πA := by
      have := LinearMap.lTensor_surjective A hsurj
      simpa [hπA, LinearMap.baseChange_eq_ltensor] using this
    let e : A ⊗[R] P →ₗ[A] A ⊗[R] P := LinearMap.id - dA ∘ₗ r
    have he : ∀ x ∈ LinearMap.range dA, e x = 0 := by
      rintro _ ⟨y, rfl⟩
      have := LinearMap.congr_fun hr y
      simp only [LinearMap.comp_apply] at this
      simp [e, this]
    let s : A ⊗[R] (P ⧸ LinearMap.range d) →ₗ[A] A ⊗[R] P :=
      ((LinearMap.range dA).liftQ e (fun x hx => he x hx)) ∘ₗ
        (hexA.linearEquivOfSurjective hsA).symm.toLinearMap
    have hs : ∀ x, s (πA x) = e x := by
      intro x
      have : (hexA.linearEquivOfSurjective hsA).symm (πA x) = (LinearMap.range dA).mkQ x := by
        rw [LinearEquiv.symm_apply_eq]
        rfl
      simp only [s, LinearMap.comp_apply, LinearEquiv.coe_coe, this]
      rfl
    have hsec : πA ∘ₗ s = LinearMap.id := by
      refine LinearMap.ext fun z => ?_
      obtain ⟨x, rfl⟩ := hsA z
      rw [LinearMap.comp_apply, hs, LinearMap.id_apply]
      have h0 : πA (dA (r x)) = 0 := hexA.apply_apply_eq_zero (r x)
      simp [e, h0]
    exact Module.Flat.of_retract s πA hsec
  have hflat : Module.Flat R (P ⧸ LinearMap.range d) :=
    Module.flat_of_isLocalized_maximal R (P ⧸ LinearMap.range d)
      (fun p _ => Localization.AtPrime p ⊗[R] (P ⧸ LinearMap.range d))
      (fun p _ => TensorProduct.mk R (Localization.AtPrime p) (P ⧸ LinearMap.range d) 1)
      (fun p _ => by
        have := hloc p
        exact Module.Flat.trans R (Localization.AtPrime p) _)
  have hfp : Module.FinitePresentation R (P ⧸ LinearMap.range d) := by
    have : Module.FinitePresentation R P := Module.finitePresentation_of_projective R P
    refine Module.finitePresentation_of_surjective (LinearMap.range d).mkQ hsurj ?_
    rw [Submodule.ker_mkQ]
    exact Module.Finite.iff_fg.mp inferInstance
  have hproj : Module.Projective R (P ⧸ LinearMap.range d) :=
    Module.Flat.projective_of_finitePresentation
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (LinearMap.range d).mkQ LinearMap.id hsurj
  let f : P →ₗ[R] P := LinearMap.id - s ∘ₗ (LinearMap.range d).mkQ
  have hf : ∀ x, f x ∈ LinearMap.range d := by
    intro x
    rw [← Submodule.ker_mkQ (LinearMap.range d), LinearMap.mem_ker]
    have := LinearMap.congr_fun hs ((LinearMap.range d).mkQ x)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    simp only [f, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub, this,
      sub_self]
  let g : P →ₗ[R] LinearMap.range d := f.codRestrict _ hf
  have hg : ∀ y : LinearMap.range d, f y = y := by
    rintro ⟨_, y, rfl⟩
    have h0 : (LinearMap.range d).mkQ (d y) = 0 := hex.apply_apply_eq_zero y
    simp only [f, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, h0, map_zero,
      sub_zero]
  have hrp : Module.Projective R (LinearMap.range d) :=
    Module.Projective.of_split (LinearMap.range d).subtype g (by
      ext y
      simpa [g] using hg y)
  obtain ⟨t, ht⟩ := Module.projective_lifting_property d.rangeRestrict LinearMap.id
    d.surjective_rangeRestrict
  refine ⟨t ∘ₗ g, ?_⟩
  ext y
  have h1 : g (d y) = d.rangeRestrict y := by
    apply Subtype.ext
    simpa [g] using hg (d.rangeRestrict y)
  have h2 := LinearMap.congr_fun ht (d.rangeRestrict y)
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at h2
  have h3 : d (t (d.rangeRestrict y)) = d y := by
    have := congrArg Subtype.val h2
    simpa using this
  simp [h1, h3]

end GlobalTheory.CompanionTheory.RegularLocal
end

