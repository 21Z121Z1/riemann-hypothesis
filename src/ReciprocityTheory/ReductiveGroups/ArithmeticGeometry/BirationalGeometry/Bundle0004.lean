import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0002
import Mathlib
import Lemmata.GeneralBFactMore.Imports
import Lemmata.FirstBlockLemmaA.Imports
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodB
section
namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial

noncomputable section

variable {σ : Type}

abbrev qmap : MvPolynomial σ ℤ →+* MvPolynomial σ ℚ := MvPolynomial.map (Int.castRingHom ℚ)

def qIdeal (P : Ideal (MvPolynomial σ ℤ)) : Ideal (MvPolynomial σ ℚ) := P.map qmap

theorem qmap_injective : Function.Injective (qmap : MvPolynomial σ ℤ → MvPolynomial σ ℚ) := MvPolynomial.map_injective _ Int.cast_injective

theorem exists_int_mul_eq_qmap (q : MvPolynomial σ ℚ) :
    ∃ D : ℤ, D ≠ 0 ∧ ∃ q' : MvPolynomial σ ℤ, (D : MvPolynomial σ ℚ) * q = qmap q' := by
  induction q using MvPolynomial.induction_on' with
  | monomial u a =>
    refine ⟨a.den, by exact_mod_cast a.den_nz, MvPolynomial.monomial u a.num, ?_⟩
    rw [show ((a.den : ℤ) : MvPolynomial σ ℚ) = C ((a.den : ℤ) : ℚ) from (map_intCast (C : ℚ →+* MvPolynomial σ ℚ) _).symm,
      C_mul_monomial, MvPolynomial.map_monomial]
    congr 1
    push_cast
    exact Rat.den_mul_eq_num a
  | add p q hp hq =>
    obtain ⟨D₁, hD₁, p', hp'⟩ := hp
    obtain ⟨D₂, hD₂, q', hq'⟩ := hq
    refine ⟨D₁ * D₂, mul_ne_zero hD₁ hD₂, (D₂ : MvPolynomial σ ℤ) * p' + (D₁ : MvPolynomial σ ℤ) * q', ?_⟩
    rw [map_add, map_mul, map_mul, map_intCast, map_intCast, ← hp', ← hq']
    push_cast
    ring

theorem exists_int_mul_mem_of_mem_qIdeal (P : Ideal (MvPolynomial σ ℤ)) {g : MvPolynomial σ ℚ}
    (hg : g ∈ qIdeal P) :
    ∃ N : ℤ, N ≠ 0 ∧ ∃ h ∈ P, (N : MvPolynomial σ ℚ) * g = qmap h := by
  have hg' : g ∈ Submodule.span (MvPolynomial σ ℚ) (qmap '' (P : Set (MvPolynomial σ ℤ))) := hg
  clear hg
  induction hg' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h, hh, rfl⟩ := hx
    exact ⟨1, one_ne_zero, h, hh, by simp⟩
  | zero => exact ⟨1, one_ne_zero, 0, P.zero_mem, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨N₁, hN₁, h₁, hh₁, e₁⟩ := hx
    obtain ⟨N₂, hN₂, h₂, hh₂, e₂⟩ := hy
    refine ⟨N₁ * N₂, mul_ne_zero hN₁ hN₂, (N₂ : MvPolynomial σ ℤ) * h₁ + (N₁ : MvPolynomial σ ℤ) * h₂,
      P.add_mem (P.mul_mem_left _ hh₁) (P.mul_mem_left _ hh₂), ?_⟩
    rw [map_add, map_mul, map_mul, map_intCast, map_intCast, ← e₁, ← e₂]
    push_cast
    ring
  | smul a x _ hx =>
    obtain ⟨N, hN, h, hh, e⟩ := hx
    obtain ⟨D, hD, a', ha'⟩ := exists_int_mul_eq_qmap a
    refine ⟨D * N, mul_ne_zero hD hN, a' * h, P.mul_mem_left _ hh, ?_⟩
    rw [map_mul, ← ha', ← e, smul_eq_mul]
    push_cast
    ring

theorem mem_of_qmap_mem_qIdeal (P : Ideal (MvPolynomial σ ℤ)) (hP : P.IsPrime)
    (hH : P.comap (C : ℤ →+* MvPolynomial σ ℤ) = ⊥) {f : MvPolynomial σ ℤ}
    (hf : qmap f ∈ qIdeal P) : f ∈ P := by
  obtain ⟨N, hN, h, hh, e⟩ := exists_int_mul_mem_of_mem_qIdeal P hf
  have hNf : (N : MvPolynomial σ ℤ) * f = h := by
    apply qmap_injective
    rw [map_mul, map_intCast, e]
  rw [← hNf, show (N : MvPolynomial σ ℤ) = C N from (map_intCast (C : ℤ →+* MvPolynomial σ ℤ) N).symm] at hh
  rcases hP.mem_or_mem hh with hC | hf'
  · have : N ∈ P.comap (C : ℤ →+* MvPolynomial σ ℤ) := hC
    rw [hH] at this
    exact absurd ((Submodule.mem_bot ℤ).mp this) hN
  · exact hf'

def ratHom (P : Ideal (MvPolynomial σ ℤ)) :
    MvPolynomial σ ℤ ⧸ P →+* MvPolynomial σ ℚ ⧸ qIdeal P :=
  Ideal.quotientMap (qIdeal P) qmap Ideal.le_comap_map

theorem ratHom_mk (P : Ideal (MvPolynomial σ ℤ)) (f : MvPolynomial σ ℤ) :
    ratHom P (Ideal.Quotient.mk P f) = Ideal.Quotient.mk (qIdeal P) (qmap f) := rfl

theorem ratHom_isLocalization (P : Ideal (MvPolynomial σ ℤ)) :
    letI := (ratHom P).toAlgebra
    IsLocalization (Algebra.algebraMapSubmonoid (MvPolynomial σ ℤ ⧸ P) (nonZeroDivisors ℤ))
      (MvPolynomial σ ℚ ⧸ qIdeal P) := by
  let _ := (ratHom P).toAlgebra
  have hcast : ∀ n : ℤ, algebraMap (MvPolynomial σ ℤ ⧸ P) (MvPolynomial σ ℚ ⧸ qIdeal P)
      (algebraMap ℤ (MvPolynomial σ ℤ ⧸ P) n) = algebraMap ℚ (MvPolynomial σ ℚ ⧸ qIdeal P) n := by
    intro n
    rw [eq_intCast, map_intCast, map_intCast]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨y, hy⟩
    obtain ⟨n, hn, rfl⟩ := Submonoid.mem_map.mp hy
    rw [hcast]
    exact (IsUnit.mk0 (n : ℚ) (by exact_mod_cast nonZeroDivisors.ne_zero hn)).map _
  · intro z
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨D, hD, q', hq'⟩ := exists_int_mul_eq_qmap q
    refine ⟨⟨Ideal.Quotient.mk P q', ⟨algebraMap ℤ _ D,
      Submonoid.mem_map.mpr ⟨D, mem_nonZeroDivisors_of_ne_zero hD, rfl⟩⟩⟩, ?_⟩
    change _ * algebraMap (MvPolynomial σ ℤ ⧸ P) _ (algebraMap ℤ _ D) = ratHom P (Ideal.Quotient.mk P q')
    rw [hcast, ratHom_mk, ← hq', mul_comm, map_mul]
    congr 1
  · intro x y hxy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    change ratHom P _ = ratHom P _ at hxy
    rw [ratHom_mk, ratHom_mk, Ideal.Quotient.eq, ← map_sub] at hxy
    obtain ⟨N, hN, h, hh, e⟩ := exists_int_mul_mem_of_mem_qIdeal P hxy
    have hNab : (N : MvPolynomial σ ℤ) * (a - b) = h := by
      apply qmap_injective
      rw [map_mul, map_intCast, e]
    refine ⟨⟨algebraMap ℤ _ N, Submonoid.mem_map.mpr ⟨N, mem_nonZeroDivisors_of_ne_zero hN, rfl⟩⟩, ?_⟩
    change algebraMap ℤ _ N * Ideal.Quotient.mk P a = algebraMap ℤ _ N * Ideal.Quotient.mk P b
    rw [← sub_eq_zero, ← mul_sub, ← map_sub, eq_intCast, ← map_intCast (Ideal.Quotient.mk P), ← map_mul,
      hNab, Ideal.Quotient.eq_zero_iff_mem]
    exact hh

theorem isDomain_qQuot (P : Ideal (MvPolynomial σ ℤ)) (hP : P.IsPrime)
    (hH : P.comap (C : ℤ →+* MvPolynomial σ ℤ) = ⊥) :
    IsDomain (MvPolynomial σ ℚ ⧸ qIdeal P) := by
  let _ := (ratHom P).toAlgebra
  have := ratHom_isLocalization P
  refine IsLocalization.isDomain_of_le_nonZeroDivisors (R := MvPolynomial σ ℤ ⧸ P)
    (M := Algebra.algebraMapSubmonoid (MvPolynomial σ ℤ ⧸ P) (nonZeroDivisors ℤ))
    (S := MvPolynomial σ ℚ ⧸ qIdeal P) ?_
  rintro _ ⟨n, hn, rfl⟩
  apply mem_nonZeroDivisors_of_ne_zero
  intro h0
  rw [eq_intCast, ← map_intCast (Ideal.Quotient.mk P), Ideal.Quotient.eq_zero_iff_mem,
    show (n : MvPolynomial σ ℤ) = C n from (map_intCast (C : ℤ →+* MvPolynomial σ ℤ) n).symm] at h0
  have : n ∈ P.comap (C : ℤ →+* MvPolynomial σ ℤ) := h0
  rw [hH] at this
  exact nonZeroDivisors.ne_zero hn ((Submodule.mem_bot ℤ).mp this)

end

end ReciprocityTheory.ChartRestriction.G.Geo
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodD
section
namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial

noncomputable section

variable {k : Type*} [Field k]

def substFun {r : ℕ} (lam : Fin r → k) : Fin (r + 1) → Polynomial (MvPolynomial (Fin r) k) :=
  Fin.cons Polynomial.X (fun i => Polynomial.C (C (lam i)) * Polynomial.X + Polynomial.C (X i))

def subst {r : ℕ} (lam : Fin r → k) :
    MvPolynomial (Fin (r + 1)) k →ₐ[k] Polynomial (MvPolynomial (Fin r) k) :=
  aeval (substFun lam)

theorem substFun_natDegree {r : ℕ} (lam : Fin r → k) (j : Fin (r + 1)) :
    (substFun lam j).natDegree ≤ 1 := by
  refine Fin.cases ?_ (fun i => ?_) j
  · simp [substFun]
  · simp only [substFun, Fin.cons_succ]
    exact Polynomial.natDegree_linear_le

theorem substFun_coeff_one {r : ℕ} (lam : Fin r → k) (j : Fin (r + 1)) :
    (substFun lam j).coeff 1 = C ((Fin.cons (1 : k) lam : Fin (r + 1) → k) j) := by
  refine Fin.cases ?_ (fun i => ?_) j
  · simp [substFun]
  · simp [substFun, Polynomial.coeff_C]

theorem prod_pow_natDegree_coeff {R ι : Type*} [CommRing R] (s : Finset ι) (p : ι → Polynomial R)
    (e : ι → ℕ) (hp : ∀ i, (p i).natDegree ≤ 1) :
    (∏ i ∈ s, p i ^ e i).natDegree ≤ ∑ i ∈ s, e i ∧
      (∏ i ∈ s, p i ^ e i).coeff (∑ i ∈ s, e i) = ∏ i ∈ s, (p i).coeff 1 ^ e i := by
  first | exact Bl.general_b_fact_more.goal1 .. | (apply Bl.general_b_fact_more.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_more.goal1 <;> assumption)

theorem subst_monomial {r : ℕ} (lam : Fin r → k) (m : Fin (r + 1) →₀ ℕ) (a : k) :
    (subst lam (monomial m a)).natDegree ≤ Finsupp.degree m ∧
      (subst lam (monomial m a)).coeff (Finsupp.degree m) =
        C (eval (Fin.cons (1 : k) lam) (monomial m a)) := by
  have h := prod_pow_natDegree_coeff m.support (substFun lam) m (substFun_natDegree lam)
  have hdeg : Finsupp.degree m = ∑ i ∈ m.support, m i := rfl
  simp only [subst, aeval_monomial, Finsupp.prod, eval_monomial]
  rw [hdeg, Polynomial.algebraMap_apply, algebraMap_eq]
  refine ⟨(Polynomial.natDegree_C_mul_le _ _).trans h.1, ?_⟩
  rw [Polynomial.coeff_C_mul, h.2]
  simp only [substFun_coeff_one, ← map_pow, ← map_prod, ← C_mul]

theorem subst_natDegree_le {r : ℕ} (lam : Fin r → k) (F : MvPolynomial (Fin (r + 1)) k) :
    (subst lam F).natDegree ≤ F.totalDegree := by
  conv_lhs => rw [F.as_sum, map_sum]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun m hm => ?_
  exact (subst_monomial lam m _).1.trans (le_totalDegree hm)

theorem subst_coeff_totalDegree {r : ℕ} (lam : Fin r → k) (F : MvPolynomial (Fin (r + 1)) k) :
    (subst lam F).coeff F.totalDegree =
      C (eval (Fin.cons (1 : k) lam) (homogeneousComponent F.totalDegree F)) := by
  classical
  rw [show subst lam F = ∑ v ∈ F.support, subst lam (monomial v (coeff v F)) by
    rw [← map_sum, ← F.as_sum]]
  rw [homogeneousComponent_apply, map_sum, map_sum, Polynomial.finsetSum_coeff,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hle : Finsupp.degree m ≤ F.totalDegree := le_totalDegree hm
  split_ifs with hd
  · rw [← hd]; exact (subst_monomial lam m _).2
  · have hlt : Finsupp.degree m < F.totalDegree := lt_of_le_of_ne hle hd
    exact Polynomial.coeff_eq_zero_of_natDegree_lt ((subst_monomial lam m _).1.trans_lt hlt)

theorem homogeneousComponent_totalDegree_ne_zero {σ : Type*} {F : MvPolynomial σ k} (hF : F ≠ 0) :
    homogeneousComponent F.totalDegree F ≠ 0 := by
  obtain ⟨m, hm, hmax⟩ := Finset.exists_mem_eq_sup F.support (support_nonempty.mpr hF)
    (fun s => s.sum fun _ e => e)
  intro h0
  have := congrArg (coeff m) h0
  rw [coeff_homogeneousComponent, if_pos (by rw [totalDegree, hmax]; rfl), coeff_zero] at this
  exact (mem_support_iff.mp hm) this

theorem eval_smul_of_degree {σ : Type*} [Fintype σ] (H : MvPolynomial σ k) (d : ℕ)
    (hH : ∀ m ∈ H.support, Finsupp.degree m = d) (c : k) (v : σ → k) :
    eval (c • v) H = c ^ d * eval v H := by
  first | exact Bl.FirstBlockLemmaA.goal1 .. | (apply Bl.FirstBlockLemmaA.goal1 <;> assumption) | (intros; apply Bl.FirstBlockLemmaA.goal1 <;> assumption)

theorem exists_eval_cons_one_ne_zero [Infinite k] {r : ℕ} (H : MvPolynomial (Fin (r + 1)) k)
    (d : ℕ) (hH : ∀ m ∈ H.support, Finsupp.degree m = d) (h0 : H ≠ 0) :
    ∃ lam : Fin r → k, eval (Fin.cons (1 : k) lam) H ≠ 0 := by
  by_contra hall
  push Not at hall
  apply h0
  have hX : H * X 0 = 0 := by
    apply MvPolynomial.funext
    intro y
    rw [map_mul, eval_X, map_zero]
    by_cases hy : y 0 = 0
    · rw [hy, mul_zero]
    · have hyeq : y = y 0 • (Fin.cons (1 : k) (fun i => (y 0)⁻¹ * y i.succ) : Fin (r + 1) → k) := by
        funext j
        refine Fin.cases ?_ (fun i => ?_) j
        · simp
        · simp [hy]
      rw [hyeq, eval_smul_of_degree H d hH, hall, mul_zero, zero_mul]
  rcases mul_eq_zero.mp hX with h | h
  · exact h
  · exact absurd h (X_ne_zero 0)

theorem eval₂_subst {R : Type*} [CommRing R] [Algebra k R] {r : ℕ} (lam : Fin r → k)
    (ℓ : Fin (r + 1) → R) (F : MvPolynomial (Fin (r + 1)) k) :
    Polynomial.eval₂ ((aeval (fun i => ℓ i.succ - lam i • ℓ 0) : MvPolynomial (Fin r) k →ₐ[k] R) :
      MvPolynomial (Fin r) k →+* R) (ℓ 0) (subst lam F) =
      aeval ℓ F := by
  induction F using MvPolynomial.induction_on with
  | C a =>
    simp [subst, Polynomial.eval₂_C, Polynomial.algebraMap_apply]
  | add p q hp hq => rw [map_add, Polynomial.eval₂_add, hp, hq, map_add]
  | mul_X p j hp =>
    rw [map_mul, Polynomial.eval₂_mul, hp, map_mul]
    congr 1
    simp only [subst, aeval_X]
    refine Fin.cases ?_ (fun i => ?_) j
    · simp [substFun]
    · simp [substFun, Algebra.smul_def]

def IntOver (k : Type*) [Field k] {R : Type*} [CommRing R] [Algebra k R] {r : ℕ} (ℓ : Fin r → R)
    (x : R) : Prop :=
  ((aeval ℓ : MvPolynomial (Fin r) k →ₐ[k] R) : MvPolynomial (Fin r) k →+* R).IsIntegralElem x

theorem exists_isIntegralElem_linear [Infinite k] {R : Type*} [CommRing R] [Algebra k R] {r : ℕ}
    (ℓ : Fin (r + 1) → R) (F : MvPolynomial (Fin (r + 1)) k) (hF : F ≠ 0) (h : aeval ℓ F = 0) :
    ∃ lam : Fin r → k, IntOver k (fun i => ℓ i.succ - lam i • ℓ 0) (ℓ 0) := by
  classical
  set d := F.totalDegree
  have hsupp : ∀ m ∈ (homogeneousComponent d F).support, Finsupp.degree m = d := by
    intro m hm
    rw [mem_support_iff, coeff_homogeneousComponent] at hm
    by_contra hne
    exact hm (if_neg hne)
  obtain ⟨lam, hlam⟩ := exists_eval_cons_one_ne_zero _ d hsupp
    (homogeneousComponent_totalDegree_ne_zero hF)
  set c := eval (Fin.cons (1 : k) lam) (homogeneousComponent d F)
  refine ⟨lam, Polynomial.C (C c⁻¹) * subst lam F, ?_, ?_⟩
  · refine Polynomial.monic_of_natDegree_le_of_coeff_eq_one d ?_ ?_
    · exact (Polynomial.natDegree_C_mul_le _ _).trans (subst_natDegree_le lam F)
    · rw [Polynomial.coeff_C_mul, subst_coeff_totalDegree, ← C_mul, inv_mul_cancel₀ hlam, C_1]
  · rw [Polynomial.eval₂_mul, eval₂_subst, h, mul_zero]

end

end ReciprocityTheory.ChartRestriction.G.Geo
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial MeasureTheory Filter Topology

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

section Algebra

abbrev MRingOver (R : Type*) [CommRing R] (ι : K → Type*) := MvPolynomial (Σ k, ι k) R

abbrev MRing (ι : K → Type*) := MRingOver ℤ ι

variable {R : Type*} [CommRing R]

def IsMultiHomog (s : MRingOver R ι) (a : K → ℕ) : Prop :=
  ∀ m ∈ s.support, ∀ k, ∑ i, m ⟨k, i⟩ = a k

def IsMultiHomogIdeal (P : Ideal (MRingOver R ι)) : Prop :=
  ∃ S : Set (MRingOver R ι), (∀ f ∈ S, ∃ a, IsMultiHomog f a) ∧ P = Ideal.span S

def IsRelevant (W : Ideal (MRingOver R ι)) : Prop :=
  ∀ k, ∃ i, (X ⟨k, i⟩ : MRingOver R ι) ∉ W

def IsMultiProjPrime (P : Ideal (MRingOver R ι)) : Prop :=
  P.IsPrime ∧ IsMultiHomogIdeal P ∧ IsRelevant P

def IsHorizontal (P : Ideal (MRing ι)) : Prop :=
  P.comap (C : ℤ →+* MRing ι) = ⊥

def IsArithVar (P : Ideal (MRing ι)) (d : ℕ) : Prop :=
  Nonempty K ∧ IsMultiProjPrime P ∧ IsHorizontal P ∧
    ringKrullDim (MRing ι ⧸ P) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞)

def divSupp (P : Ideal (MRingOver R ι)) (s : MRingOver R ι) : Set (Ideal (MRingOver R ι)) :=
  {W | W ∈ (P ⊔ Ideal.span {s}).minimalPrimes ∧ IsRelevant W}

open Classical in

def multAt (J W : Ideal (MRingOver R ι)) : ℕ :=
  if h : W.IsPrime then
    haveI := h
    (Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (MRingOver R ι ⧸ J))).toNat
  else 0

theorem divSupp_finite [IsNoetherianRing R] (P : Ideal (MRingOver R ι)) (s : MRingOver R ι) : (divSupp P s).Finite :=
  (Ideal.finite_minimalPrimes_of_isNoetherianRing _ (P ⊔ Ideal.span {s})).subset fun _ hW => hW.1

def divCycle [IsNoetherianRing R] (P : Ideal (MRingOver R ι)) (s : MRingOver R ι) :
    Ideal (MRingOver R ι) →₀ ℕ := by
  classical
  exact Finsupp.ofSupportFinite
    (fun W => if W ∈ divSupp P s then multAt (P ⊔ Ideal.span {s}) W else 0)
    ((divSupp_finite P s).subset fun W hW => by
      by_contra h
      exact hW (if_neg h))

def charOf (W : Ideal (MRing ι)) : ℕ :=
  (Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing ι))).natAbs

open Classical in

def geoNum : (n : ℕ) → Ideal (MRing ι) → (Fin n → K → ℤ) → ℤ
  | 0, V, _ =>
    if h : IsRelevant V then
      ((Module.length ℤ
        (MRing ι ⧸ (V ⊔ Ideal.span (Set.range fun k => (X ⟨k, (h k).choose⟩ : MRing ι) - 1)))).toNat : ℤ)
    else 0
  | n + 1, V, a =>
    if h : IsRelevant V then
      ∑ k, a (Fin.last n) k *
        ∑ᶠ W ∈ divSupp V (X ⟨k, (h k).choose⟩),
          (multAt (V ⊔ Ideal.span {(X ⟨k, (h k).choose⟩ : MRing ι)}) W : ℤ) * geoNum n W (Fin.init a)
    else 0

end Algebra

section Complex

def mcPts (P : Ideal (MRing ι)) : Set ((Σ k, ι k) → ℂ) :=
  {z | (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) ∧ ∀ f ∈ P, eval z (map (Int.castRingHom ℂ) f) = 0}

variable (ι) in

structure HermLine where

  a : K → ℤ

  h : ((Σ k, ι k) → ℂ) → ℝ
  pos : ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → 0 < h z
  smul : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) →
    h (fun p => c p.1 * z p) = (∏ k, ‖c k‖ ^ a k) * h z

def IsSmoothHerm (A : HermLine ι) : Prop :=
  ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A.h {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}

def HermLine.tensor (A B : HermLine ι) : HermLine ι where
  a := A.a + B.a
  h z := A.h z * B.h z
  pos z hz := mul_pos (A.pos z hz) (B.pos z hz)
  smul c z hc := by
    rw [A.smul c z hc, B.smul c z hc]
    have : ∀ k, ‖c k‖ ^ (A.a + B.a) k = ‖c k‖ ^ A.a k * ‖c k‖ ^ B.a k := fun k =>
      zpow_add₀ (norm_ne_zero_iff.mpr (hc k)) _ _
    simp only [this, Finset.prod_mul_distrib]
    ring

def segre (z : (Σ k, ι k) → ℂ) : ((k : K) → ι k) → ℂ :=
  fun i => ∏ k, z ⟨k, i k⟩

variable {e : ℕ}

def fibre (P : Ideal (MRing ι)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (y : Fin e → ℂ) : Set (((k : K) → ι k) → ℂ) :=
  {w | ∃ z ∈ mcPts P, segre z = w ∧ Ψ w = Fin.cons 1 y}

def IsSheet (P : Ideal (MRing ι)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (y : Fin e → ℂ) (w : ((k : K) → ι k) → ℂ) (γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ) : Prop :=
  segre (γ y) = w ∧ ∀ᶠ y' in 𝓝 y,
    DifferentiableAt ℂ γ y' ∧ γ y' ∈ mcPts P ∧ Ψ (segre (γ y')) = Fin.cons 1 y'

def sheetDensity (P : Ideal (MRing ι)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ) (y : Fin e → ℂ)
    (w : ((k : K) → ι k) → ℂ) : ℝ := by
  classical
  exact if hγ : ∃ γ, IsSheet P Ψ y w γ then
    g (hγ.choose y) * maDensity (fun j y' => φ j (hγ.choose y')) y
  else 0

def ptsIntegralAt (P : Ideal (MRing ι)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ) : ℝ :=
  ∫ y, ∑ᶠ w ∈ fibre P Ψ y, sheetDensity P Ψ φ g y w

def IsGoodProj (P : Ideal (MRing ι)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) : Prop :=
  ∀ z ∈ mcPts P, Ψ (segre z) ≠ 0

def ptsIntegral (P : Ideal (MRing ι)) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    (g : ((Σ k, ι k) → ℂ) → ℝ) : ℝ := by
  classical
  exact if hΨ : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj P Ψ then
    ptsIntegralAt P hΨ.choose φ g
  else 0

def logNorm (A : HermLine ι) (s : MRing ι) (z : (Σ k, ι k) → ℂ) : ℝ :=
  Real.log (‖eval z (map (Int.castRingHom ℂ) s)‖ / A.h z)

def arInt (P : Ideal (MRing ι)) (s : MRing ι) (A : HermLine ι) (L : Fin e → HermLine ι) : ℝ :=
  ptsIntegral P (fun j z => Real.log ((L j).h z)) (logNorm A s)

end Complex

section Constructors

def HermLine.ofMetrics (m : ∀ k, ConeMetric ℂ (ι k)) (a : K → ℤ) : HermLine ι where
  a := a
  h z := ∏ k, (m k).ρ (fun i => z ⟨k, i⟩) ^ a k
  pos z hz := Finset.prod_pos fun k _ => by
    obtain ⟨i, hi⟩ := hz k
    exact zpow_pos ((m k).pos _ fun h0 => hi (congrFun h0 i)) _
  smul c z hc := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    have : (fun i => c k * z ⟨k, i⟩) = c k • fun i => z ⟨k, i⟩ := rfl
    simp only [this, (m k).smul, mul_zpow]

def HermLine.ofWeight (u : ((Σ k, ι k) → ℂ) → ℝ)
    (hu : ∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) → u (fun p => c p.1 * z p) = u z) : HermLine ι where
  a := 0
  h z := Real.exp (-u z)
  pos _ _ := Real.exp_pos _
  smul c z hc := by simp [hu c z hc]

end Constructors

section Family

def recR (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι)) {n : ℕ}
    (L : Fin n → HermLine ι) (A : HermLine ι) (s : MRing ι) : ℝ := by
  classical
  exact (∑ᶠ W ∈ divSupp P s, (multAt (P ⊔ Ideal.span {s}) W : ℝ) *
      (if IsHorizontal W then I W n L
        else (geoNum n W (fun j => (L j).a) : ℝ) * Real.log (charOf W))) -
    arInt P s A L

def IsIntersectionFamily (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) : Prop :=
  (∀ P n (L : Fin n → HermLine ι) (σ : Equiv.Perm (Fin n)), IsArithVar P n →
      (∀ j, IsSmoothHerm (L j)) → I P n (L ∘ σ) = I P n L) ∧
  (∀ P n (L : Fin n → HermLine ι) (A B : HermLine ι), IsArithVar P (n + 1) →
      (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSmoothHerm B →
      I P (n + 1) (Fin.snoc L (A.tensor B)) =
        I P (n + 1) (Fin.snoc L A) + I P (n + 1) (Fin.snoc L B)) ∧
  (∀ P n (L : Fin n → HermLine ι) (A : HermLine ι) (s : MRing ι) (a : K → ℕ),
      IsArithVar P (n + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A →
      (∀ k, A.a k = a k) → IsMultiHomog s a → s ∉ P →
      I P (n + 1) (Fin.snoc L A) = recR I P L A s)

end Family

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

