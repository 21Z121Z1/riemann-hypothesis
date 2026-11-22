import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramDetNeZeroOfKerOrth
section
open Matrix Polynomial

theorem GlobalTheory.gram_det_ne_zero_of_ker_orth {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (A : Matrix (Fin n) (Fin n) K) {ι : Type} [Fintype ι] [DecidableEq ι] (u : ι → Fin n → K) (hli : LinearIndependent K u) (hsp : Submodule.span K (Set.range u) = LinearMap.ker (Matrix.toLin' A)) (horth : ∀ x z, A *ᵥ x = 0 → ∑ k, σ ((A *ᵥ z) k) * x k = 0) (hdec : ∀ v, ∃ z y, A *ᵥ y = 0 ∧ v = A *ᵥ z + y) : (Matrix.of fun i j => ∑ k, σ (u i k) * u j k).det ≠ 0 := by
  intro hdet
  obtain ⟨c, hc0, hGc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  set x : Fin n → K := ∑ j, c j • u j with hxdef
  have hx0 : x ≠ 0 := by
    intro hx
    apply hc0
    funext j
    exact Fintype.linearIndependent_iff.mp hli c hx j
  have hxspan : x ∈ Submodule.span K (Set.range u) :=
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hAx : A *ᵥ x = 0 := by
    rw [hsp, LinearMap.mem_ker, Matrix.toLin'_apply] at hxspan
    exact hxspan
  have hu : ∀ i, ∑ k, σ (u i k) * x k = 0 := by
    intro i
    have := congrFun hGc i
    rw [Matrix.mulVec, dotProduct] at this
    simp only [Matrix.of_apply, Pi.zero_apply] at this
    rw [← this]
    simp only [hxdef, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  have hy : ∀ y ∈ LinearMap.ker (Matrix.toLin' A), ∑ k, σ (y k) * x k = 0 := by
    intro y hy
    rw [← hsp] at hy
    obtain ⟨d, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hy
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    have : ∀ i, ∑ k, σ (d i) * σ (u i k) * x k = σ (d i) * ∑ k, σ (u i k) * x k := by
      intro i; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    simp [this, hu]
  have hall : ∀ v : Fin n → K, ∑ k, σ (v k) * x k = 0 := by
    intro v
    obtain ⟨z, y, hAy, rfl⟩ := hdec v
    have h1 := horth x z hAx
    have h2 := hy y (by rw [LinearMap.mem_ker, Matrix.toLin'_apply]; exact hAy)
    simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib, h1, h2, add_zero]
  apply hx0
  funext k
  have := hall (Pi.single k 1)
  simpa [Pi.single_apply] using this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramFiberMeasuresUniqueAe
section
namespace GlobalTheory

theorem unitsMod_away_of_unique_prime (B D : Type) [CommRing B] [CommRing D] [Algebra B D]
    (f : B) (P : Ideal B) (Q : Ideal D) (g : D)
    (hQP : Q.comap (algebraMap B D) = P)
    (huniq : ∀ Q' : Ideal D, Q'.IsPrime → algebraMap B D f ∈ Q' → g ∉ Q' → Q' = Q) :
    ∀ s : B, s ∉ P → ∃ t : Localization.Away g,
      algebraMap B (Localization.Away g) s * t - 1 ∈
        Ideal.span {algebraMap B (Localization.Away g) f} := by
  intro s hs
  set A := Localization.Away g
  by_cases hI : Ideal.span {algebraMap B A s, algebraMap B A f} = ⊤
  · have h1 : (1 : A) ∈ Ideal.span {algebraMap B A s, algebraMap B A f} := by
      rw [hI]; exact Submodule.mem_top
    obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp h1
    refine ⟨a, ?_⟩
    have : algebraMap B A s * a - 1 = (-b) * algebraMap B A f := by
      rw [← hab]; ring
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  · exfalso
    obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal _ hI
    have hMp : (M.comap (algebraMap D A)).IsPrime := Ideal.comap_isPrime _ _
    have hf : algebraMap B D f ∈ M.comap (algebraMap D A) := by
      rw [Ideal.mem_comap, ← IsScalarTower.algebraMap_apply]
      exact hIM (Ideal.subset_span (by simp))
    have hg : g ∉ M.comap (algebraMap D A) := by
      intro hgM
      rw [Ideal.mem_comap] at hgM
      exact hM.ne_top (Ideal.eq_top_of_isUnit_mem _ hgM
        (IsLocalization.Away.algebraMap_isUnit g))
    have hEq := huniq _ hMp hf hg
    apply hs
    rw [← hQP, Ideal.mem_comap, ← hEq, Ideal.mem_comap, ← IsScalarTower.algebraMap_apply]
    exact hIM (Ideal.subset_span (by simp))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramPosSemidefOfIntForm
section
namespace GlobalTheory

open Matrix

theorem gram_posSemidef_of_int_form {X : Type} [AddCommGroup X] {r : ℕ}
    (b : LinearMap.BilinForm ℤ X) (hsymm : ∀ y z, b y z = b z y) (hpos : ∀ y, 0 ≤ b y y)
    (v : Fin r → X) : (Matrix.of fun i j => (b (v i) (v j) : ℝ)).PosSemidef := by
  set G : Matrix (Fin r) (Fin r) ℝ := Matrix.of fun i j => (b (v i) (v j) : ℝ) with hG
  have hint : ∀ m : Fin r → ℤ, 0 ≤ ∑ i, ∑ j, (m i : ℝ) * (m j : ℝ) * G i j := by
    intro m
    have key : (∑ i, ∑ j, m i * m j * b (v i) (v j) : ℤ)
        = b (∑ i, m i • v i) (∑ j, m j • v j) := by
      simp only [map_sum, LinearMap.sum_apply, map_zsmul, LinearMap.smul_apply, smul_eq_mul,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hsymm (v i) (v j)]; ring
    have h0 : (0:ℝ) ≤ ((∑ i, ∑ j, m i * m j * b (v i) (v j) : ℤ) : ℝ) := by
      rw [key]; exact_mod_cast hpos _
    simpa [hG] using h0
  have hrat : ∀ c : Fin r → ℚ, 0 ≤ ∑ i, ∑ j, (c i : ℝ) * (c j : ℝ) * G i j := by
    intro c
    set N : ℕ := ∏ i, (c i).den with hN
    have hNpos : (0:ℝ) < N := by
      have : 0 < N := Finset.prod_pos (fun i _ => (c i).den_pos)
      exact_mod_cast this
    have hm : ∀ i, ∃ k : ℤ, (k : ℝ) = N * (c i : ℝ) := by
      intro i
      obtain ⟨t, ht⟩ : (c i).den ∣ N := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
      refine ⟨(c i).num * t, ?_⟩
      have h1 : ((c i).num : ℚ) = c i * (c i).den := (Rat.mul_den_eq_num (c i)).symm
      have h2 : ((c i).num : ℝ) = (c i : ℝ) * (c i).den := by exact_mod_cast h1
      rw [ht]; push_cast
      rw [h2]; ring
    choose m hm using hm
    have h3 := hint m
    simp_rw [hm] at h3
    have e : ∑ i, ∑ j, ((N:ℝ) * c i) * (N * c j) * G i j
        = (N:ℝ) ^ 2 * ∑ i, ∑ j, (c i : ℝ) * (c j : ℝ) * G i j := by
      simp_rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [e] at h3
    exact (mul_nonneg_iff_of_pos_left (by positivity)).mp h3
  have hreal : ∀ x : Fin r → ℝ, 0 ≤ ∑ i, ∑ j, x i * x j * G i j := by
    intro x
    have hd : DenseRange (Pi.map fun (_ : Fin r) (q : ℚ) => (q : ℝ)) :=
      DenseRange.piMap fun _ => Rat.denseRange_cast
    refine hd.induction_on (p := fun x : Fin r → ℝ => 0 ≤ ∑ i, ∑ j, x i * x j * G i j) x ?_ ?_
    · exact isClosed_le continuous_const (by fun_prop)
    · intro c
      simpa [Pi.map] using hrat c
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · ext i j
    simp [hG, Matrix.conjTranspose_apply, hsymm]
  · intro x
    have e : star x ⬝ᵥ (G *ᵥ x) = ∑ i, ∑ j, x i * x j * G i j := by
      simp only [dotProduct, mulVec, star_trivial, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [e]; exact hreal x

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HPolyAddTwo
section
set_option autoImplicit false

noncomputable section

open MeasureTheory MvPolynomial

namespace GlobalTheory.FibLine

def fsDens (x : ℂ) : ℝ := 1 / (Real.pi * (1 + ‖x‖ ^ 2) ^ 2)

def lineVec (x : ℂ) : Fin 2 → ℂ := ![1, x]

def qCoef (x : ℂ) (ab : Fin 2 × Fin 2) : ℂ :=
  lineVec x ab.2 * starRingEnd ℂ (lineVec x ab.1) / ((1 + ‖x‖ ^ 2 : ℝ) : ℂ)

def entries {R : Type} (H : Matrix (Fin 2) (Fin 2) R) : Fin 2 × Fin 2 → R := fun ab => H ab.1 ab.2

def qMat {R : Type} [CommRing R] [Algebra ℂ R] (H : Matrix (Fin 2) (Fin 2) R) (x : ℂ) : R :=
  ∑ ab : Fin 2 × Fin 2, qCoef x ab • entries H ab

def fibPow (k : ℕ) : MvPolynomial (Fin 2 × Fin 2) ℂ :=
  ∑ f : Fin k → Fin 2 × Fin 2, C (∫ x : ℂ, (∏ i, qCoef x (f i)) * (fsDens x : ℂ)) * ∏ i, X (f i)

def hPoly (k : ℕ) : MvPolynomial (Fin 2) ℂ :=
  (Nat.rec (motive := fun _ => MvPolynomial (Fin 2) ℂ × MvPolynomial (Fin 2) ℂ) (1, X 0)
    (fun _ p => (p.2, X 0 * p.2 - X 1 * p.1)) k).1

theorem hPoly_zero : hPoly 0 = 1 := rfl

theorem hPoly_one : hPoly 1 = X 0 := rfl

theorem hPoly_add_two (k : ℕ) : hPoly (k + 2) = X 0 * hPoly (k + 1) - X 1 * hPoly k := rfl

def trDet : Fin 2 → MvPolynomial (Fin 2 × Fin 2) ℂ :=
  ![X (0, 0) + X (1, 1), X (0, 0) * X (1, 1) - X (0, 1) * X (1, 0)]

end GlobalTheory.FibLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HTChartExistsHolds
section
open scoped TensorProduct

namespace GlobalTheory

theorem exists_order_integers_mul_finite_index (F B : Type) [Field F] [NumberField F] [Ring B]
    [Algebra F B] [Algebra ℚ B] [IsScalarTower ℚ F B] (OB : Subring B) (hfin : Module.Finite ℤ OB)
    (hsat : ∀ b : B, ∃ m : ℕ, 0 < m ∧ (m : B) * b ∈ OB) :
    ∃ Λ : Subring B, OB ≤ Λ ∧ (∀ a : NumberField.RingOfIntegers F, algebraMap F B (a : F) ∈ Λ) ∧
      Module.Finite ℤ Λ ∧ ∃ N : ℕ, 0 < N ∧ ∀ x ∈ Λ, (N : B) * x ∈ OB := by
  classical
  let f : NumberField.RingOfIntegers F →ₐ[ℤ] B :=
    ((algebraMap F B).comp (algebraMap (NumberField.RingOfIntegers F) F)).toIntAlgHom
  let g : OB →ₐ[ℤ] B := OB.subtype.toIntAlgHom
  have hc : ∀ a b, Commute (f a) (g b) := fun a b => Algebra.commutes _ _
  let L := Algebra.TensorProduct.lift f g hc
  have hL : ∀ a b, L (a ⊗ₜ b) = f a * g b := fun a b => Algebra.TensorProduct.lift_tmul f g hc a b

  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ (NumberField.RingOfIntegers F)).FG)
  choose m hm0 hm using fun a : NumberField.RingOfIntegers F => hsat (f a)
  let N : ℕ := ∏ a ∈ s, m a
  have hN0 : 0 < N := Finset.prod_pos fun a _ => hm0 a
  have hnat : ∀ (k : ℕ) (y : B), y ∈ OB → (k : B) * y ∈ OB := fun k y hy =>
    OB.mul_mem (natCast_mem OB k) hy
  let P : Submodule ℤ (NumberField.RingOfIntegers F) :=
    { carrier := {a | (N : B) * f a ∈ OB}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, map_add, mul_add] at *
        exact OB.add_mem ha hb
      zero_mem' := by simp
      smul_mem' := by
        intro n a ha
        simp only [Set.mem_setOf_eq, map_zsmul, mul_smul_comm] at *
        exact OB.zsmul_mem ha n }
  have hsP : (s : Set (NumberField.RingOfIntegers F)) ⊆ SetLike.coe P := by
    intro a ha
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem m ha
    show (N : B) * f a ∈ OB
    have : (N : B) = (k : B) * (m a : B) := by
      rw [show N = m a * k from hk, Nat.cast_mul, (Nat.cast_commute _ _).eq]
    rw [this, mul_assoc]
    exact hnat k _ (hm a)
  have hP : ∀ a, (N : B) * f a ∈ OB := by
    intro a
    have : a ∈ Submodule.span ℤ (s : Set _) := by rw [hs]; trivial
    exact (Submodule.span_le.mpr hsP) this
  refine ⟨L.toRingHom.range, ?_, ?_, ?_, N, hN0, ?_⟩
  · intro b hb
    refine ⟨1 ⊗ₜ ⟨b, hb⟩, ?_⟩
    show L _ = b
    rw [hL]; simp [f, g]
  · intro a
    refine ⟨a ⊗ₜ 1, ?_⟩
    show L _ = _
    rw [hL]; simp [f, g]
  · haveI : Module.Finite ℤ OB := hfin
    haveI : Module.Finite ℤ (NumberField.RingOfIntegers F ⊗[ℤ] OB) := Module.Finite.tensorProduct _ _ _
    exact Module.Finite.of_surjective (L.toRingHom.rangeRestrict.toIntAlgHom.toLinearMap)
      (RingHom.rangeRestrict_surjective _)
  · rintro x ⟨t, rfl⟩
    show (N : B) * L t ∈ OB
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      rw [hL, ← mul_assoc]
      exact OB.mul_mem (hP a) b.2
    | add t u ht hu =>
      rw [map_add, mul_add]
      exact OB.add_mem ht hu

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtLinearMapEvalAlgebraMap
section
open Filter Topology

namespace GlobalTheory

open Polynomial in

theorem hasDerivAt_linearMap_eval_algebraMap {A : Type*} [CommRing A] [Algebra ℝ A]
    (Φ : A →ₗ[ℝ] ℝ) (R : Polynomial A) (τ : ℝ) :
    HasDerivAt (fun t : ℝ => Φ (R.eval (algebraMap ℝ A t)))
      (Φ ((derivative R).eval (algebraMap ℝ A τ))) τ := by
  induction R using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [eval_add, map_add, derivative_add]
    exact hp.add hq
  | monomial n a =>
    simp only [eval_monomial, derivative_monomial]
    have h1 : ∀ (m : ℕ) (t : ℝ), Φ (a * (algebraMap ℝ A t) ^ m) = t ^ m * Φ a := by
      intro m t
      rw [← map_pow, mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul]
    have h2 : Φ (a * (n : A) * (algebraMap ℝ A τ) ^ (n - 1)) = (n : ℝ) * τ ^ (n - 1) * Φ a := by
      have : a * (n : A) * (algebraMap ℝ A τ) ^ (n - 1) = n • (a * (algebraMap ℝ A τ) ^ (n - 1)) := by
        rw [nsmul_eq_mul]; ring
      rw [this, map_nsmul, h1, nsmul_eq_mul]; ring
    have h3 : (fun t : ℝ => Φ (a * (algebraMap ℝ A t) ^ n)) = fun t => t ^ n * Φ a := funext (h1 n)
    rw [h3, h2]
    exact (hasDerivAt_pow n τ).mul_const (Φ a)

theorem monotone_form_along_segment : ∀ (D : ℕ) (Φ : MvPolynomial (Fin 2) ℝ →ₗ[ℝ] ℝ),
    (∀ x y : ℕ, 0 ≤ Φ ((MvPolynomial.X 0 - MvPolynomial.X 1) *
      (MvPolynomial.C (x : ℝ) * MvPolynomial.X 0 + MvPolynomial.C (y : ℝ) * MvPolynomial.X 1) ^ D)) →
    Φ (MvPolynomial.X 1 ^ (D + 1)) ≤ Φ (MvPolynomial.X 0 ^ (D + 1)) := by
  intro D Φ hyp
  have hΦC : ∀ (r : ℝ) (q : MvPolynomial (Fin 2) ℝ), Φ (MvPolynomial.C r * q) = r * Φ q := by
    intro r q; rw [MvPolynomial.C_mul', map_smul, smul_eq_mul]
  set a : MvPolynomial (Fin 2) ℝ := MvPolynomial.X 1 with ha
  set b : MvPolynomial (Fin 2) ℝ := MvPolynomial.X 0 - MvPolynomial.X 1 with hb
  set Q : Polynomial (MvPolynomial (Fin 2) ℝ) :=
    (Polynomial.C a + Polynomial.X * Polynomial.C b) ^ (D + 1) with hQ
  set R : Polynomial (MvPolynomial (Fin 2) ℝ) :=
    Polynomial.C b * (Polynomial.C a + Polynomial.X * Polynomial.C b) ^ D with hR
  set g : ℝ → ℝ := fun t => Φ (Q.eval (algebraMap ℝ _ t)) with hg
  set f : ℝ → ℝ := fun t => Φ (R.eval (algebraMap ℝ _ t)) with hf
  have hgd : ∀ τ, HasDerivAt g (((D : ℝ) + 1) * f τ) τ := by
    intro τ
    convert hasDerivAt_linearMap_eval_algebraMap Φ Q τ using 1
    simp [hf, hQ, hR, Polynomial.derivative_pow]
    have hc : ((D : MvPolynomial (Fin 2) ℝ) + 1) = MvPolynomial.C ((D : ℝ) + 1) := by simp
    rw [hc, mul_assoc, hΦC]
    congr 2
    ring
  have hfc : Continuous f := by
    rw [continuous_iff_continuousAt]
    intro τ
    exact (hasDerivAt_linearMap_eval_algebraMap Φ R τ).continuousAt
  have hfrat : ∀ x n : ℕ, 0 < n → x ≤ n → 0 ≤ f ((x : ℝ) / n) := by
    intro x n hn hxn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have e : a + MvPolynomial.C ((x : ℝ) / n) * b = MvPolynomial.C (1 / (n : ℝ)) *
        (MvPolynomial.C (x : ℝ) * MvPolynomial.X 0 + MvPolynomial.C (((n - x : ℕ)) : ℝ) * a) := by
      rw [Nat.cast_sub hxn]
      have h1 : MvPolynomial.C (1 / (n : ℝ)) * MvPolynomial.C (x : ℝ) =
          (MvPolynomial.C ((x : ℝ) / n) : MvPolynomial (Fin 2) ℝ) := by
        rw [← map_mul]; congr 1; ring
      have h2 : MvPolynomial.C (1 / (n : ℝ)) * MvPolynomial.C ((n : ℝ) - x) =
          (1 - MvPolynomial.C ((x : ℝ) / n) : MvPolynomial (Fin 2) ℝ) := by
        rw [← map_mul, ← map_one MvPolynomial.C, ← map_sub]; congr 1; field_simp
      rw [ha, hb]
      linear_combination (-(MvPolynomial.X 0 : MvPolynomial (Fin 2) ℝ)) * h1 - (MvPolynomial.X 1) * h2
    have hfx : f ((x : ℝ) / n) = (1 / (n : ℝ)) ^ D * Φ (b *
        (MvPolynomial.C (x : ℝ) * MvPolynomial.X 0 + MvPolynomial.C (((n - x : ℕ)) : ℝ) * a) ^ D) := by
      simp only [hf, hR, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_add,
        Polynomial.eval_X, MvPolynomial.algebraMap_eq]
      rw [e, mul_pow, ← map_pow, mul_left_comm, hΦC]
    rw [hfx]
    exact mul_nonneg (pow_nonneg (by positivity) _) (hyp _ _)
  have hfpos : ∀ τ ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ f τ := by
    intro τ hτ
    by_contra hneg
    push_neg at hneg
    have hev : ∀ᶠ t in 𝓝 τ, f t < 0 := hfc.continuousAt.eventually (Iio_mem_nhds hneg)
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show max 0 (τ - ε) < τ from
      max_lt hτ.1 (by linarith))
    have hq0 : (0 : ℝ) < q := lt_of_le_of_lt (le_max_left _ _) hq1
    have hqε : τ - ε < q := lt_of_le_of_lt (le_max_right _ _) hq1
    have hq0' : (0 : ℚ) < q := by exact_mod_cast hq0
    have hnum : 0 < q.num := Rat.num_pos.mpr hq0'
    have hx : ((q.num.toNat : ℕ) : ℝ) = (q.num : ℝ) := by
      have := Int.toNat_of_nonneg hnum.le
      exact_mod_cast this
    have hqdef : (q : ℝ) = (q.num.toNat : ℝ) / (q.den : ℝ) := by
      rw [hx]; exact_mod_cast (Rat.num_div_den q).symm
    have hden : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
    have hle : q.num.toNat ≤ q.den := by
      have h1 : (q : ℝ) < 1 := by linarith [hτ.2]
      rw [hqdef, div_lt_one hden] at h1
      exact_mod_cast h1.le
    have h0 := hfrat q.num.toNat q.den q.den_pos hle
    rw [← hqdef] at h0
    have hd : dist (q : ℝ) τ < ε := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith
    linarith [hball hd]
  have hgdiff : ∀ τ, DifferentiableAt ℝ g τ := fun τ => (hgd τ).differentiableAt
  have hmono : MonotoneOn g (Set.Icc 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
    · exact fun τ _ => (hgdiff τ).continuousAt.continuousWithinAt
    · exact fun τ _ => (hgdiff τ).differentiableWithinAt
    · intro τ hτ
      rw [interior_Icc] at hτ
      rw [(hgd τ).deriv]
      exact mul_nonneg (by positivity) (hfpos τ hτ)
  have h01 := hmono (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one) zero_le_one
  simpa [hg, hQ, ha, hb] using h01

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtOfContinuousOfMapAdd
section
namespace GlobalTheory.DerivativeOfAdditiveContinuous

theorem hasDerivAt_of_continuous_of_map_add (χ : ℝ → ℂ) (hc : Continuous χ)
    (hadd : ∀ s t : ℝ, χ (s + t) = χ s * χ t) (h0 : χ (0 : ℝ) = (1 : ℂ)) (s : ℝ) :
    HasDerivAt χ (deriv χ (0 : ℝ) * χ s) s := by
  obtain ⟨δ, hδ, hball⟩ := Metric.continuous_iff.mp hc 0 (1 / 2) (by norm_num)
  set η := δ / 2 with hη
  have hη0 : 0 < η := by positivity
  set c := ∫ t in (0 : ℝ)..η, χ t with hcdef
  have hc0 : c ≠ 0 := by
    have hsplit : c = (η : ℂ) + ∫ t in (0 : ℝ)..η, (χ t - 1) := by
      rw [hcdef, intervalIntegral.integral_sub (hc.intervalIntegrable _ _) intervalIntegrable_const]
      simp
    have hbound : ‖∫ t in (0 : ℝ)..η, (χ t - 1)‖ ≤ 1 / 2 * |η - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro t ht
      rw [Set.uIoc_of_le hη0.le] at ht
      have h1 : dist t 0 < δ := by
        rw [Real.dist_eq, sub_zero, abs_of_pos ht.1]
        linarith [ht.2]
      have h2 := hball t h1
      rw [dist_eq_norm, h0] at h2
      exact h2.le
    intro hzero
    rw [hsplit] at hzero
    have h3 : ‖∫ t in (0 : ℝ)..η, (χ t - 1)‖ = η := by
      rw [eq_neg_of_add_eq_zero_right hzero, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hη0]
    rw [h3, sub_zero, abs_of_pos hη0] at hbound
    linarith
  set F : ℝ → ℂ := fun x => ∫ t in (0 : ℝ)..x, χ t with hF
  have hFd : ∀ x, HasDerivAt F (χ x) x := fun x => (hc.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hrep : ∀ x, χ x * c = F (x + η) - F x := by
    intro x
    have h1 : ∫ t in (0 : ℝ)..η, χ (x + t) = χ x * c := by
      simp only [hadd]
      rw [intervalIntegral.integral_const_mul]
    have h2 : ∫ t in (0 : ℝ)..η, χ (x + t) = ∫ t in x..(x + η), χ t := by
      rw [intervalIntegral.integral_comp_add_left]
      simp
    rw [← h1, h2, hF]
    simp only
    rw [intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)]
  have hdiff : ∀ x, DifferentiableAt ℝ χ x := by
    intro x
    have hχ : χ = fun y => (F (y + η) - F y) / c := by
      funext y
      rw [← hrep y, mul_div_cancel_right₀ _ hc0]
    rw [hχ]
    exact (((hFd (x + η)).comp_add_const x η).sub (hFd x)).differentiableAt.div_const c
  have hd0 : HasDerivAt χ (deriv χ 0) (s - s) := by
    rw [sub_self]
    exact (hdiff 0).hasDerivAt
  have hcomp : HasDerivAt (fun y => χ (y - s)) (deriv χ 0) s := hd0.comp_sub_const s s
  have hmul := hcomp.const_mul (χ s)
  have hfun : (fun y => χ s * χ (y - s)) = χ := by
    funext y
    rw [← hadd]
    congr 1
    ring
  rw [hfun] at hmul
  rw [mul_comm]
  exact hmul

end GlobalTheory.DerivativeOfAdditiveContinuous
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTemperateGrowthElim
section
noncomputable section

namespace GlobalTheory.SliceSchwartz

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def inrL (κ κ' : Type) [Fintype κ] [Fintype κ'] : (κ' → V) →L[ℝ] (κ ⊕ κ' → V) :=
  ContinuousLinearMap.pi fun i =>
    Sum.elim (fun _ : κ => (0 : (κ' → V) →L[ℝ] V)) (fun j => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ' => V) j) i

theorem elim_eq_add {κ κ' : Type} [Fintype κ] [Fintype κ'] (x : κ → V) :
    (fun y : κ' → V => (Sum.elim x y : κ ⊕ κ' → V)) = fun y => Sum.elim x 0 + inrL κ κ' y := by
  funext y i
  cases i with
  | inl i => simp [inrL]
  | inr j => simp [inrL]

theorem hasTemperateGrowth_elim {κ κ' : Type} [Fintype κ] [Fintype κ'] (x : κ → V) :
    Function.HasTemperateGrowth (fun y : κ' → V => (Sum.elim x y : κ ⊕ κ' → V)) := by
  rw [elim_eq_add]
  exact (Function.HasTemperateGrowth.const _).add (ContinuousLinearMap.hasTemperateGrowth (inrL (V := V) κ κ'))

theorem norm_le_norm_elim {κ κ' : Type} [Fintype κ] [Fintype κ'] (x : κ → V) (y : κ' → V) :
    ‖y‖ ≤ ‖(Sum.elim x y : κ ⊕ κ' → V)‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => norm_le_pi_norm (Sum.elim x y : κ ⊕ κ' → V) (Sum.inr j)

theorem elim_upper {κ κ' : Type} [Fintype κ] [Fintype κ'] (x : κ → V) :
    ∃ (k : ℕ) (C : ℝ), ∀ y : κ' → V, ‖y‖ ≤ C * (1 + ‖(Sum.elim x y : κ ⊕ κ' → V)‖) ^ k :=
  ⟨1, 1, fun y => by rw [pow_one, one_mul]; linarith [norm_le_norm_elim x y]⟩

def sliceR {κ κ' : Type} [Fintype κ] [Fintype κ'] (f : SchwartzMap (κ ⊕ κ' → V) ℂ) (x : κ → V) :
    SchwartzMap (κ' → V) ℂ :=
  SchwartzMap.compCLM ℂ (hasTemperateGrowth_elim x) (elim_upper x) f

@[simp] theorem sliceR_apply {κ κ' : Type} [Fintype κ] [Fintype κ'] (f : SchwartzMap (κ ⊕ κ' → V) ℂ) (x : κ → V)
    (y : κ' → V) : sliceR f x y = f (Sum.elim x y) := rfl

def sliceRL {κ κ' : Type} [Fintype κ] [Fintype κ'] (x : κ → V) :
    SchwartzMap (κ ⊕ κ' → V) ℂ →L[ℂ] SchwartzMap (κ' → V) ℂ :=
  SchwartzMap.compCLM ℂ (hasTemperateGrowth_elim x) (elim_upper x)

theorem sliceRL_apply {κ κ' : Type} [Fintype κ] [Fintype κ'] (x : κ → V) (f : SchwartzMap (κ ⊕ κ' → V) ℂ) :
    sliceRL x f = sliceR f x := rfl

end GlobalTheory.SliceSchwartz
end
end

