import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0001
import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CapelliComplements.Bundle0001
import Lemmata.CofiniteContinuousBounds.LeOfCofinite
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0002

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CountPf
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up

namespace CountPf

theorem ratio (T c : ℕ) (hT : 0 < T) : ∀ k : ℕ,
    (1 - (k : ℝ) * c / T) * ((T + c + k).choose k : ℝ) ≤ ((T + k).choose k : ℝ) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have hTr : (0 : ℝ) < T := by exact_mod_cast hT
    have hA : ((T + (k + 1)).choose (k + 1) : ℝ) * (k + 1) = (T + k + 1) * ((T + k).choose k : ℝ) := by
      have h := Nat.add_one_mul_choose_eq (T + k) k
      rw [show T + (k + 1) = T + k + 1 by ring]
      have h' : ((T + k + 1) * (T + k).choose k : ℕ) = ((T + k + 1).choose (k + 1) * (k + 1) : ℕ) := h
      have := congrArg (fun t : ℕ => (t : ℝ)) h'
      push_cast at this
      linarith
    have hB : ((T + c + (k + 1)).choose (k + 1) : ℝ) * (k + 1) = (T + c + k + 1) * ((T + c + k).choose k : ℝ) := by
      have h := Nat.add_one_mul_choose_eq (T + c + k) k
      rw [show T + c + (k + 1) = T + c + k + 1 by ring]
      have h' : ((T + c + k + 1) * (T + c + k).choose k : ℕ) = ((T + c + k + 1).choose (k + 1) * (k + 1) : ℕ) := h
      have := congrArg (fun t : ℕ => (t : ℝ)) h'
      push_cast at this
      linarith
    have hk1 : (0 : ℝ) < k + 1 := by positivity
    have hBn : (0 : ℝ) ≤ ((T + c + k).choose k : ℝ) := Nat.cast_nonneg _
    have hAn : (0 : ℝ) ≤ ((T + k).choose k : ℝ) := Nat.cast_nonneg _
    have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg _
    push_cast
    rw [← mul_le_mul_iff_of_pos_right hk1, mul_assoc, hB, hA]
    by_cases hs : 1 - ((k : ℝ) + 1) * c / T ≤ 0
    · have : (1 - ((k : ℝ) + 1) * c / T) * ((T + c + k + 1) * ((T + c + k).choose k : ℝ)) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hs (by positivity)
      have : (0 : ℝ) ≤ (T + k + 1) * ((T + k).choose k : ℝ) := by positivity
      linarith
    · push_neg at hs
      set u := 1 - (k : ℝ) * c / T with hu
      have hu1 : u ≤ 1 := by
        have : 0 ≤ (k : ℝ) * c / T := by positivity
        rw [hu]; linarith
      have hcT : (c : ℝ) / T * T = c := by field_simp
      have e1 : 1 - ((k : ℝ) + 1) * c / T = u - c / T := by rw [hu]; ring
      rw [e1]
      have step : (u - c / T) * (T + c + k + 1) ≤ u * (T + k + 1) := by
        have : (u - c / T) * (T + c + k + 1) = u * (T + k + 1) + (u * c - c / T * T - c / T * (c + k + 1)) := by ring
        rw [this, hcT]
        have h1 : u * c ≤ c := by nlinarith
        have h2 : 0 ≤ (c : ℝ) / T * (c + k + 1) := by positivity
        linarith
      have hupos : 0 ≤ u - c / T := by linarith
      calc (u - c / T) * ((T + c + k + 1) * ((T + c + k).choose k : ℝ))
          = ((u - c / T) * (T + c + k + 1)) * ((T + c + k).choose k : ℝ) := by ring
        _ ≤ (u * (T + k + 1)) * ((T + c + k).choose k : ℝ) := mul_le_mul_of_nonneg_right step hBn
        _ = (T + k + 1) * (u * ((T + c + k).choose k : ℝ)) := by ring
        _ ≤ (T + k + 1) * ((T + k).choose k : ℝ) := mul_le_mul_of_nonneg_left ih (by positivity)

end CountPf

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.IntegralStatementPfA
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.IntPf

noncomputable section

section Cone

open MvPolynomial

variable {R E : Type*} [CommRing R] [CommRing E] [Algebra R E] {ι : Type*}

def cone (a : ι → E) : MvPolynomial ι R →ₐ[R] Polynomial E :=
  aeval fun i => Polynomial.C (a i) * Polynomial.X

theorem cone_homog (a : ι → E) {f : MvPolynomial ι R} {d : ℕ} (hf : f.IsHomogeneous d) :
    cone a f = Polynomial.monomial d (aeval a f) := by
  classical
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  rw [map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : ∑ i ∈ m.support, m i = d := by
    have := hf (mem_support_iff.mp hm)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  have hp : (m.prod fun i k => (Polynomial.C (a i) * Polynomial.X) ^ k) =
      Polynomial.C (m.prod fun i k => a i ^ k) * Polynomial.X ^ d := by
    simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, map_prod, map_pow,
      Finset.prod_pow_eq_pow_sum, hd]
  rw [cone, aeval_monomial, aeval_monomial, hp, Polynomial.algebraMap_apply, ← mul_assoc,
    ← Polynomial.C_mul, Polynomial.C_mul_X_pow_eq_monomial]

theorem coeff_cone (a : ι → E) (f : MvPolynomial ι R) (n : ℕ) :
    (cone a f).coeff n = aeval a (homogeneousComponent n f) := by
  classical
  conv_lhs => rw [← sum_homogeneousComponent f]
  rw [map_sum, Polynomial.finsetSum_coeff]
  simp_rw [cone_homog a (homogeneousComponent_isHomogeneous _ f), Polynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [homogeneousComponent_eq_zero _ _ (by simp at h; omega), map_zero]

theorem aeval_mul_homog (q : ι → E) (t : E) {G : MvPolynomial ι R} {m : ℕ} (hG : G.IsHomogeneous m) :
    aeval (fun i => q i * t) G = t ^ m * aeval q G := by
  have h := congrArg ((Polynomial.aeval t : Polynomial E →ₐ[E] E).restrictScalars R)
    (cone_homog (R := R) q hG)
  rw [cone, MvPolynomial.comp_aeval_apply] at h
  simp only [AlgHom.restrictScalars_apply, map_mul, Polynomial.aeval_C, Polynomial.aeval_X,
    Polynomial.aeval_monomial, Algebra.algebraMap_self, RingHom.id_apply] at h
  rw [h, mul_comm]

theorem eval_mul_homog {K : Type*} [CommRing K] (q : ι → K) (t : K) {G : MvPolynomial ι K} {m : ℕ}
    (hG : G.IsHomogeneous m) : eval (fun i => q i * t) G = t ^ m * eval q G := by
  simpa using aeval_mul_homog (R := K) q t hG

end Cone

open MvPolynomial in
theorem exists_cons_one_ne {K : Type*} [Field K] [Infinite K] {n m : ℕ}
    {G : MvPolynomial (Fin (n + 1)) K} (hG : G.IsHomogeneous m) (h0 : G ≠ 0) :
    ∃ c : Fin n → K, eval (Fin.cons 1 c) G ≠ 0 := by
  by_contra! h
  apply h0
  have hX : (X 0 * G : MvPolynomial (Fin (n + 1)) K) = 0 := by
    apply MvPolynomial.funext
    intro p
    rw [map_mul, eval_X, map_zero]
    by_cases hp : p 0 = 0
    · rw [hp, zero_mul]
    · have hq : p = fun i => (Fin.cons 1 (fun k => p k.succ / p 0) : Fin (n + 1) → K) i * p 0 := by
        funext i
        refine Fin.cases ?_ (fun k => ?_) i
        · simp
        · simp [div_mul_cancel₀ _ hp]
      have : eval p G = 0 := by
        rw [hq]
        rw [eval_mul_homog _ _ hG, h, mul_zero]
      rw [this, mul_zero]
  exact (mul_eq_zero.mp hX).resolve_left (X_ne_zero _)

section Int

open MvPolynomial

variable {R E : Type*} [CommRing R] [CommRing E] [Algebra R E] {ι : Type*}

end Int

section Homog

open Polynomial

theorem prod_pow_natDegree_coeff' {B : Type*} [CommRing B] {ι : Type*} (s : Finset ι)
    (v : ι → B[X]) (d : ι → ℕ) (hv : ∀ i, (v i).natDegree ≤ 1) :
    (∏ i ∈ s, v i ^ d i).natDegree ≤ ∑ i ∈ s, d i ∧
      (∏ i ∈ s, v i ^ d i).coeff (∑ i ∈ s, d i) = ∏ i ∈ s, (v i).coeff 1 ^ d i := by
  first | exact Bl.FirstLemmaA.goal1 .. | (apply Bl.FirstLemmaA.goal1 <;> assumption) | (intros; apply Bl.FirstLemmaA.goal1 <;> assumption) | (apply @Bl.FirstLemmaA.goal1 <;> assumption) | (intros; apply @Bl.FirstLemmaA.goal1 <;> assumption) | (apply @Bl.FirstLemmaA.goal1 <;> first | assumption | infer_instance)

end Homog

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.IntPf
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PolyGrowthStatementPfB
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PG

open MvPolynomial

variable {D : ℕ}

noncomputable def lineHom (a w : Fin D → ℂ) : MvPolynomial (Fin D) ℂ →ₐ[ℂ] Polynomial ℂ :=
  aeval fun i => Polynomial.C (a i) + Polynomial.C (w i) * Polynomial.X

theorem eval_lineHom (a w : Fin D → ℂ) (F : MvPolynomial (Fin D) ℂ) (s : ℂ) :
    (lineHom a w F).eval s = eval (fun i => a i + w i * s) F := by
  induction F using MvPolynomial.induction_on with
  | C c => simp [lineHom]
  | add p q hp hq => rw [map_add, Polynomial.eval_add, hp, hq, MvPolynomial.eval_add]
  | mul_X p i hp =>
    rw [map_mul, Polynomial.eval_mul, hp, MvPolynomial.eval_mul, MvPolynomial.eval_X]
    simp [lineHom]

end ReciprocityTheory.ChartRestriction.G.AR.Up.PG
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.SCoordStatementPfC
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.SCoC

open MvPolynomial Filter Topology ReciprocityTheory.ChartRestriction.G.AR.Up.SCoA

noncomputable section

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {ιB : Type} [Fintype ιB]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem eval₂Hom_comp (φ : Ω →+* ℂ) (y : ιB → Ω) :
    eval₂Hom (φ.comp (algebraMap K Ω)) (φ ∘ y) = φ.comp (aeval y : MvPolynomial ιB K →ₐ[K] Ω).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro k; simp
  · intro b; simp

def coef (y : ιB → Ω) (a : Ω) (P : Polynomial (MvPolynomial ιB K)) (b : ιB) : Ω :=
  -(xTerm (aeval y : MvPolynomial ιB K →ₐ[K] Ω).toRingHom a b P) /
    (Polynomial.derivative P).eval₂ (aeval y : MvPolynomial ιB K →ₐ[K] Ω).toRingHom a

theorem deriv_rel (φ : Ω →+* ℂ) {y : ιB → Ω} {a : Ω} (P : Polynomial (MvPolynomial ιB K))
    (hP' : (Polynomial.derivative P).eval₂ (aeval y : MvPolynomial ιB K →ₐ[K] Ω).toRingHom a ≠ 0)
    {h : V → ιB → ℂ} {g : V → ℂ} {Dh : ιB → V →L[ℂ] ℂ} {Dg : V →L[ℂ] ℂ}
    (hh : ∀ b, HasFDerivAt (fun z => h z b) (Dh b) 0) (hg : HasFDerivAt g Dg 0)
    (h0 : h 0 = φ ∘ y) (g0 : g 0 = φ a)
    (hrel : ∀ᶠ z in 𝓝 (0 : V), P.eval₂ (eval₂Hom (φ.comp (algebraMap K Ω)) (h z)) (g z) = 0) :
    Dg = ∑ b, φ (coef y a P b) • Dh b := by
  set σ := φ.comp (algebraMap K Ω)
  have hd := hasFDerivAt_eval₂ σ P hh hg
  have hz : HasFDerivAt (fun z => P.eval₂ (eval₂Hom σ (h z)) (g z)) (0 : V →L[ℂ] ℂ) 0 :=
    (hasFDerivAt_const (0 : ℂ) (0 : V)).congr_of_eventuallyEq (hrel.mono fun z hz => hz)
  have heq := hd.unique hz
  rw [h0, g0, eval₂Hom_comp] at heq
  simp only [← Polynomial.hom_eval₂, ← map_xTerm] at heq
  set E := (Polynomial.derivative P).eval₂ (aeval y : MvPolynomial ιB K →ₐ[K] Ω).toRingHom a
  have hE : φ E ≠ 0 := (map_ne_zero φ).mpr hP'
  apply smul_right_injective (V →L[ℂ] ℂ) hE
  simp only
  rw [eq_neg_of_add_eq_zero_left heq, Finset.smul_sum]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [smul_smul, coef, map_div₀, map_neg, mul_div_cancel₀ _ hE, neg_smul]

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.SCoC
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.SCoordStatementPfE
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.SCoE

open MvPolynomial

noncomputable section

def pdet {Ω : Type} [Field Ω] {n N : ℕ} {j0 : Fin (N + 1)} {B : Set {j // j ≠ j0}} (e : Fin n ≃ B)
    (a : {j // j ≠ j0} → B → Ω) : MvPolynomial (Fin n × {j // j ≠ j0}) Ω :=
  (Matrix.of fun i k : Fin n => ∑ j : {j // j ≠ j0}, X (i, j) * C (a j (e k))).det

theorem pdet_ne {Ω : Type} [Field Ω] {n N : ℕ} {j0 : Fin (N + 1)} {B : Set {j // j ≠ j0}} (e : Fin n ≃ B)
    (a : {j // j ≠ j0} → B → Ω) (ha : ∀ b : B, a b.1 = Pi.single b 1) : pdet e a ≠ 0 := by
  classical
  intro h0
  have h1 := congrArg (eval (fun q : Fin n × {j // j ≠ j0} => if q.2 = (e q.1).1 then (1 : Ω) else 0)) h0
  rw [map_zero, pdet, RingHom.map_det] at h1
  have h2 : (eval (fun q : Fin n × {j // j ≠ j0} => if q.2 = (e q.1).1 then (1 : Ω) else 0)).mapMatrix
      (Matrix.of fun i k : Fin n => ∑ j : {j // j ≠ j0}, X (i, j) * C (a j (e k))) = 1 := by
    ext i k
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, map_sum, map_mul,
      eval_X, eval_C, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, ha,
      Matrix.one_apply]
    rw [Pi.single_apply]
    simp [e.apply_eq_iff_eq, eq_comm]
  rw [h2, Matrix.det_one] at h1
  exact one_ne_zero h1

theorem eval_pdet {Ω : Type} [Field Ω] {n N : ℕ} {j0 : Fin (N + 1)} {B : Set {j // j ≠ j0}} (e : Fin n ≃ B)
    (a : {j // j ≠ j0} → B → Ω) (φ : Ω →+* ℂ) (t : Fin (n + 1) × Fin (N + 1) → ℂ) :
    eval₂ φ (fun q : Fin n × {j // j ≠ j0} => t (q.1.succ, q.2.1)) (pdet e a) =
      (Matrix.of fun i k : Fin n => ∑ j : {j // j ≠ j0}, t (i.succ, j.1) * φ (a j (e k))).det := by
  classical
  rw [pdet, ← coe_eval₂Hom, RingHom.map_det]
  congr 1
  ext i k
  simp [RingHom.mapMatrix_apply, Matrix.map_apply]

theorem det_ne {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {n N : ℕ} (sg : K →+* ℂ)
    (φ : Ω →+* ℂ) (hφ : φ.comp (algebraMap K Ω) = sg) (j0 : Fin (N + 1)) (u : Fin (N + 1) → Ω)
    (hu0 : u j0 = 1) (B : Set {j // j ≠ j0}) [Fintype B]
    (hy : IsTranscendenceBasis K (fun b : B => u b.1.1)) (e : Fin n ≃ B)
    (a : {j // j ≠ j0} → B → Ω) (ha : ∀ b : B, a b.1 = Pi.single b 1)
    (t : Fin (n + 1) × Fin (N + 1) → ℂ)
    (ht : ∀ Q : MvPolynomial (Fin (n + 1) × Fin (N + 1)) K, Q ≠ 0 → eval₂ sg t Q ≠ 0)
    (hrel : ∀ i : Fin n, ∑ j, t (i.succ, j) * φ (u j) = 0) :
    (Matrix.of fun i k : Fin n => ∑ j : {j // j ≠ j0}, t (i.succ, j.1) * φ (a j (e k))).det ≠ 0 := by
  classical
  have hcard : Fintype.card B ≤ Fintype.card (Fin n) := (Fintype.card_congr e).symm.le
  let f : Fin n × Fin (N + 1) → Fin (n + 1) × Fin (N + 1) := fun p => (p.1.succ, p.2)
  have hf : Function.Injective f := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    simp only [f, Prod.mk.injEq, Fin.succ_inj] at h
    rw [h.1, h.2]
  have ht' : ∀ Q : MvPolynomial (Fin n × Fin (N + 1)) K, Q ≠ 0 →
      eval₂ sg (fun p => (fun i j => t (i.succ, j)) p.1 p.2) Q ≠ 0 := by
    intro Q hQ
    have h1 := ht (rename f Q) (by simpa using (rename_injective f hf).ne hQ)
    rwa [eval₂_rename] at h1
  have hgen : ∀ p : MvPolynomial (Fin n × {j // j ≠ j0}) Ω, p ≠ 0 →
      eval₂ φ (fun q => t (q.1.succ, q.2.1)) p ≠ 0 :=
    SCoB.gen_indep (ιB := B) (R := Fin n) sg φ hφ hy j0 u hu0 (fun i j => t (i.succ, j)) ht' hrel hcard
  rw [← eval_pdet e a φ t]
  exact hgen _ (pdet_ne e a ha)

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.SCoE
end

