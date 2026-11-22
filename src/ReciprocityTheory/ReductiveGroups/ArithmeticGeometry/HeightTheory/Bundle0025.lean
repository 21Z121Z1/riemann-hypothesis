import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0018
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ProdZpowEqZpowSum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.NormFactorizationClause
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.NormByPlaces

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.SupportFreeOfBlockSubstInvariant
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open MvPolynomial

section Comp

variable {K : Type} [Field K] {D N : ℕ}

def degB (b : Fin (D + 1)) (s : TVar D N →₀ ℕ) : ℕ := ∑ j, s (b, j)

noncomputable def compB (b : Fin (D + 1)) (k : ℕ) (p : MvPolynomial (TVar D N) K) :
    MvPolynomial (TVar D N) K :=
  ∑ s ∈ p.support.filter (fun s => degB b s = k), monomial s (coeff s p)

theorem coeff_compB (b : Fin (D + 1)) (k : ℕ) (p : MvPolynomial (TVar D N) K) (t : TVar D N →₀ ℕ) :
    coeff t (compB b k p) = if degB b t = k then coeff t p else 0 := by
  unfold compB
  rw [coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  by_cases h : degB b t = k
  · rw [if_pos h]
    by_cases ht : t ∈ p.support
    · have hm : t ∈ p.support.filter (fun s => degB b s = k) := Finset.mem_filter.mpr ⟨ht, h⟩
      rw [if_pos hm]
    · have hn : t ∉ p.support.filter (fun s => degB b s = k) := fun h' => ht (Finset.mem_filter.mp h').1
      rw [if_neg hn]
      exact (by simpa using ht : coeff t p = 0).symm
  · have hn : t ∉ p.support.filter (fun s => degB b s = k) := fun h' => h (Finset.mem_filter.mp h').2
    rw [if_neg h, if_neg hn]

theorem mem_support_compB {b : Fin (D + 1)} {k : ℕ} {p : MvPolynomial (TVar D N) K}
    {t : TVar D N →₀ ℕ} (ht : t ∈ (compB b k p).support) : t ∈ p.support ∧ degB b t = k := by
  rw [mem_support_iff, coeff_compB] at ht
  by_cases h : degB b t = k
  · rw [if_pos h] at ht
    exact ⟨mem_support_iff.mpr ht, h⟩
  · rw [if_neg h] at ht
    exact absurd rfl ht

private lemma sum_filter_block_eq_degB {D N : ℕ} (b : Fin (D + 1)) (s : TVar D N →₀ ℕ) :
    ∑ v ∈ Finset.univ.filter (fun v : TVar D N => v.1 = b), s v = degB b s := by
  rw [Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_eq_single b]
  · simp [degB]
  · intro i _ hi
    simp [hi]
  · intro h
    exact absurd (Finset.mem_univ b) h

theorem scaleBlock_eq_sum (b : Fin (D + 1)) (u : Kˣ) (p : MvPolynomial (TVar D N) K) (M : ℕ)
    (hM : ∀ s ∈ p.support, degB b s < M) :
    sigP b u p = ∑ k ∈ Finset.range M, C ((u : K) ^ k) * compB b k p := by
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  simp only [sigP, scaleEquiv_monomial, sum_filter_block_eq_degB]
  simp only [compB, Finset.mul_sum]
  rw [← Finset.sum_fiberwise_of_maps_to (fun s hs => Finset.mem_range.mpr (hM s hs))]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun s hs => ?_
  rw [(Finset.mem_filter.mp hs).2]

end Comp

section Pres

variable {K : Type} [Field K] [CharZero K] {D N : ℕ}

theorem sigF_alg (b : Fin (D + 1)) (u : Kˣ) (g : KTp K D N) :
    sigF (K := K) (D := D) (N := N) b u (algebraMap (KTp K D N) (KTf K D N) g) =
      algebraMap (KTp K D N) (KTf K D N) (sigP b u g) := by
  first
  | exact IsFractionRing.ringEquivOfRingEquiv_algebraMap _ _
  | simp [sigF, IsFractionRing.ringEquivOfRingEquiv_algebraMap]

theorem one_block (b : Fin (D + 1)) (z : KTf K D N)
    (hz : ∀ u : Kˣ, sigF (K := K) (D := D) (N := N) b u z = z)
    (p q : KTp K D N) (hq : q ≠ 0)
    (hpq : algebraMap (KTp K D N) (KTf K D N) p = z * algebraMap (KTp K D N) (KTf K D N) q) :
    ∃ k, compB b k q ≠ 0 ∧ algebraMap (KTp K D N) (KTf K D N) (compB b k p) =
      z * algebraMap (KTp K D N) (KTf K D N) (compB b k q) := by
  obtain ⟨M, hMp, hMq⟩ : ∃ M, (∀ s ∈ p.support, degB b s < M) ∧ (∀ s ∈ q.support, degB b s < M) :=
    ⟨(p.support ∪ q.support).sup (degB b) + 1,
      fun s hs => Nat.lt_succ_of_le (Finset.le_sup (f := degB b) (Finset.mem_union_left _ hs)),
      fun s hs => Nat.lt_succ_of_le (Finset.le_sup (f := degB b) (Finset.mem_union_right _ hs))⟩
  have hroot : ∀ u : Kˣ, ∑ k ∈ Finset.range M,
      (algebraMap (KTp K D N) (KTf K D N) (compB b k p) - z * algebraMap (KTp K D N) (KTf K D N) (compB b k q)) * (algebraMap (KTp K D N) (KTf K D N) (C (u : K))) ^ k = 0 := by
    intro u
    have h1 := congrArg (sigF (K := K) (D := D) (N := N) b u) hpq
    rw [map_mul, sigF_alg, sigF_alg, hz u, scaleBlock_eq_sum b u p M hMp, scaleBlock_eq_sum b u q M hMq,
      map_sum, map_sum, Finset.mul_sum] at h1
    have h2 := sub_eq_zero.mpr h1
    rw [← Finset.sum_sub_distrib] at h2
    refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) h2
    simp only [map_mul, map_pow]
    ring
  have hQ : (∑ k ∈ Finset.range M, Polynomial.monomial k
      (algebraMap (KTp K D N) (KTf K D N) (compB b k p) - z * algebraMap (KTp K D N) (KTf K D N) (compB b k q))) = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => algebraMap (KTp K D N) (KTf K D N) (C ((n : K) + 1))) ?_ ?_
    · intro n m hnm
      have h2 := IsFractionRing.injective (KTp K D N) (KTf K D N) hnm
      have h3 := MvPolynomial.C_injective (TVar D N) K h2
      exact_mod_cast add_right_cancel h3
    · intro n
      have hu := hroot (Units.mk0 ((n : K) + 1) (Nat.cast_add_one_ne_zero n))
      rw [Units.val_mk0] at hu
      show Polynomial.eval _ _ = 0
      rw [Polynomial.eval_finset_sum]
      simp only [Polynomial.eval_monomial]
      exact hu
  have hcoef : ∀ k < M, algebraMap (KTp K D N) (KTf K D N) (compB b k p) - z * algebraMap (KTp K D N) (KTf K D N) (compB b k q) = 0 := by
    intro k hk
    have h4 := congrArg (fun P => Polynomial.coeff P k) hQ
    simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_monomial, Polynomial.coeff_zero] at h4
    first
    | rwa [Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr hk)] at h4
    | rwa [Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr hk)] at h4
  have hqs : q = ∑ k ∈ Finset.range M, compB b k q := by
    ext t
    rw [MvPolynomial.coeff_sum]
    simp only [coeff_compB]
    rw [Finset.sum_ite_eq]
    split_ifs with h
    · rfl
    · by_contra hne
      exact h (Finset.mem_range.mpr (hMq t (MvPolynomial.mem_support_iff.mpr hne)))
  obtain ⟨k, hk, hqk⟩ : ∃ k ∈ Finset.range M, compB b k q ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply hq
    rw [hqs]
    exact Finset.sum_eq_zero hc
  exact ⟨k, hqk, sub_eq_zero.mp (hcoef k (Finset.mem_range.mp hk))⟩

private lemma aeval_block_zero_monomial (s : TVar D N →₀ ℕ) (a : K) :
    (aeval (fun v : TVar D N => if v.1 = 0 then C ((0 : Fin (N + 1) → K) v.2) else X v) :
      KTp K D N →ₐ[K] KTp K D N) (monomial s a) =
      if degB 0 s = 0 then monomial s a else 0 := by
  rw [aeval_monomial]
  split_ifs with h
  · have h' : ∑ j, s (0, j) = 0 := h
    have hz : ∀ v ∈ s.support, v.1 ≠ 0 := by
      intro v hv h0
      have hsum : s (0, v.2) = 0 := Finset.sum_eq_zero_iff.mp h' v.2 (Finset.mem_univ _)
      have hv' : v = (0, v.2) := Prod.ext h0 rfl
      rw [Finsupp.mem_support_iff, hv'] at hv
      exact hv hsum
    rw [Finsupp.prod_congr (g2 := fun i k => (X i : KTp K D N) ^ k) (fun i hi => by simp [hz i hi]),
      MvPolynomial.algebraMap_eq, ← monomial_eq]
  · have h' : ∃ j, s (0, j) ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact h (Finset.sum_eq_zero fun j _ => hc j)
    obtain ⟨j, hj⟩ := h'
    rw [Finsupp.prod, Finset.prod_eq_zero (i := ((0 : Fin (D + 1)), j))
      (Finsupp.mem_support_iff.mpr hj) (by simp [hj]), mul_zero]

theorem support_free_of_block_subst_invariant (P : KTp K D N)
    (hP : ∀ x : Fin (N + 1) → K, (aeval (fun v : TVar D N =>
      if v.1 = 0 then C (x v.2) else X v) : KTp K D N →ₐ[K] KTp K D N) P = P) :
    ∀ s ∈ P.support, degB 0 s = 0 := by
  have h0 := hP 0
  have hc : (aeval (fun v : TVar D N => if v.1 = 0 then C ((0 : Fin (N + 1) → K) v.2) else X v) :
      KTp K D N →ₐ[K] KTp K D N) P = compB 0 0 P := by
    conv_lhs => rw [P.as_sum]
    rw [map_sum]
    simp only [aeval_block_zero_monomial]
    unfold compB
    rw [Finset.sum_filter]
  have hPc : P = compB 0 0 P := h0.symm.trans hc
  intro s hs
  rw [hPc] at hs
  exact (mem_support_compB hs).2

theorem multi_pres (z : KTf K D N)
    (hz : ∀ (b : Fin (D + 1)) (u : Kˣ), sigF (K := K) (D := D) (N := N) b u z = z)
    (p q : KTp K D N) (hq : q ≠ 0)
    (hpq : algebraMap (KTp K D N) (KTf K D N) p = z * algebraMap (KTp K D N) (KTf K D N) q)
    (hp0 : ∀ s ∈ p.support, degB 0 s = 0) (hq0 : ∀ s ∈ q.support, degB 0 s = 0) :
    ∃ a b : KTp K D N, b ≠ 0 ∧
      algebraMap (KTp K D N) (KTf K D N) a = z * algebraMap (KTp K D N) (KTf K D N) b ∧
      ∃ m : Fin (D + 1) → ℕ, m 0 = 0 ∧ ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous m a ∧
        ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous m b := by
  classical
  have key : ∀ S : Finset (Fin (D + 1)), ∃ a b : KTp K D N, b ≠ 0 ∧
      algebraMap (KTp K D N) (KTf K D N) a = z * algebraMap (KTp K D N) (KTf K D N) b ∧
      (∀ s ∈ a.support, degB 0 s = 0) ∧ (∀ s ∈ b.support, degB 0 s = 0) ∧
      ∃ m : Fin (D + 1) → ℕ, ∀ i ∈ S,
        (∀ s ∈ a.support, degB i s = m i) ∧ (∀ s ∈ b.support, degB i s = m i) := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨p, q, hq, hpq, hp0, hq0, 0, by simp⟩
    | insert i S hi ih =>
      obtain ⟨a, b, hb, hab, ha0, hb0, m, hm⟩ := ih
      obtain ⟨k, hk0, hk⟩ := one_block i z (hz i) a b hb hab
      refine ⟨compB i k a, compB i k b, hk0, hk, fun s hs => ha0 s (mem_support_compB hs).1,
        fun s hs => hb0 s (mem_support_compB hs).1, Function.update m i k, ?_⟩
      intro i' hi'
      rcases Finset.mem_insert.mp hi' with rfl | hi'
      · simp only [Function.update_self]
        exact ⟨fun s hs => (mem_support_compB hs).2, fun s hs => (mem_support_compB hs).2⟩
      · have hne : i' ≠ i := fun h => hi (h ▸ hi')
        rw [Function.update_of_ne hne]
        exact ⟨fun s hs => (hm i' hi').1 s (mem_support_compB hs).1,
          fun s hs => (hm i' hi').2 s (mem_support_compB hs).1⟩
  obtain ⟨a, b, hb, hab, ha0, hb0, m, hm⟩ := key Finset.univ
  refine ⟨a, b, hb, hab, fun i => if i = 0 then 0 else m i, by simp, ?_, ?_⟩
  · intro s hs i
    by_cases hi : i = 0
    · subst hi
      simpa [degB] using ha0 s hs
    · simpa [hi, degB] using (hm i (Finset.mem_univ i)).1 s hs
  · intro s hs i
    by_cases hi : i = 0
    · subst hi
      simpa [degB] using hb0 s hs
    · simpa [hi, degB] using (hm i (Finset.mem_univ i)).2 s hs

end Pres

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.UnitAtIntAt
section
set_option linter.style.haveILetI false

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

namespace LocAt

variable {R F : Type*} [CommRing R] [IsDomain R] [Field F] [Algebra R F] [IsFractionRing R F]

def IntAt (p : Ideal R) (x : F) : Prop :=
  ∃ a s : R, s ∉ p ∧ x * algebraMap R F s = algebraMap R F a

def UnitAt (p : Ideal R) (x : F) : Prop :=
  ∃ a s : R, a ∉ p ∧ s ∉ p ∧ x * algebraMap R F s = algebraMap R F a

variable {p : Ideal R} [hP : p.IsPrime]
include hP

omit [IsDomain R] [IsFractionRing R F] in
theorem intAt_mul {x y : F} (hx : IntAt p x) (hy : IntAt p y) : IntAt p (x * y) := by
  obtain ⟨a, s, hs, hxs⟩ := hx
  obtain ⟨b, t, ht, hyt⟩ := hy
  refine ⟨a * b, s * t, fun h => (hP.mem_or_mem h).elim hs ht, ?_⟩
  rw [map_mul, map_mul, ← hxs, ← hyt]
  ring

omit [IsDomain R] [IsFractionRing R F] in
theorem unitAt_mul {x y : F} (hx : UnitAt p x) (hy : UnitAt p y) : UnitAt p (x * y) := by
  obtain ⟨a, s, ha, hs, hxs⟩ := hx
  obtain ⟨b, t, hb, ht, hyt⟩ := hy
  refine ⟨a * b, s * t, fun h => (hP.mem_or_mem h).elim ha hb,
    fun h => (hP.mem_or_mem h).elim hs ht, ?_⟩
  rw [map_mul, map_mul, ← hxs, ← hyt]
  ring

omit [IsDomain R] [IsFractionRing R F] in
theorem unitAt_one : UnitAt p (1 : F) := by
  have h1 : (1 : R) ∉ p := fun h => hP.ne_top ((Ideal.eq_top_iff_one p).mpr h)
  exact ⟨1, 1, h1, h1, by simp⟩

omit [IsDomain R] [IsFractionRing R F] in
theorem unitAt_intAt {x : F} (hx : UnitAt p x) : IntAt p x := by
  obtain ⟨a, s, _, hs, h⟩ := hx
  exact ⟨a, s, hs, h⟩

omit [IsDomain R] [IsFractionRing R F] in
theorem unitAt_alg {r : R} (hr : r ∉ p) : UnitAt p (algebraMap R F r) := by
  have h1 : (1 : R) ∉ p := fun h => hP.ne_top ((Ideal.eq_top_iff_one p).mpr h)
  exact ⟨r, 1, hr, h1, by simp⟩

theorem unitAt_inv {x : F} (hx : UnitAt p x) : UnitAt p x⁻¹ := by
  obtain ⟨a, s, ha, hs, h⟩ := hx
  refine ⟨s, a, hs, ha, ?_⟩
  have ha0 : algebraMap R F a ≠ 0 := by
    intro h0
    apply ha
    have h00 : a = 0 := IsFractionRing.injective R F (by rw [h0, map_zero])
    rw [h00]
    exact p.zero_mem
  have hx0 : x ≠ 0 := by
    rintro rfl
    apply ha0
    rw [← h, zero_mul]
  rw [← h, ← mul_assoc, inv_mul_cancel₀ hx0, one_mul]

omit [IsDomain R] [IsFractionRing R F] in
theorem unitAt_pow {x : F} (hx : UnitAt p x) (n : ℕ) : UnitAt p (x ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact unitAt_one
  | succ n ih => rw [pow_succ]; exact unitAt_mul ih hx

theorem unitAt_zpow {x : F} (hx : UnitAt p x) (n : ℤ) : UnitAt p (x ^ n) := by
  cases n with
  | ofNat n =>
    show UnitAt p (x ^ (n : ℤ))
    rw [zpow_natCast]
    exact unitAt_pow hx n
  | negSucc n =>
    rw [zpow_negSucc]
    exact unitAt_inv (unitAt_pow hx (n + 1))

omit [IsDomain R] [IsFractionRing R F] in
theorem unitAt_prod {κ : Type*} (s : Finset κ) (f : κ → F) (hf : ∀ i ∈ s, UnitAt p (f i)) :
    UnitAt p (∏ i ∈ s, f i) := by
  classical
  revert hf
  refine Finset.induction_on s ?_ ?_
  · intro _
    rw [Finset.prod_empty]
    exact unitAt_one
  · intro i s hi ih hf
    rw [Finset.prod_insert hi]
    exact unitAt_mul (hf i (Finset.mem_insert_self i s))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

end LocAt

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem gen_prime' {q : Ideal (KTp K d.D d.N)} (hq : q ∈ d.HtOne) : Prime (d.gen q) :=
  ValUFD.gen_prime (fun p hp hh => d.gen_span ⟨hp, hh⟩) hq

theorem gen_not_mem {p q : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne) (hq : q ∈ d.HtOne)
    (hqp : q ≠ p) : d.gen q ∉ p := by
  intro hm
  rw [d.gen_span hp, Ideal.mem_span_singleton] at hm
  have e := (ValUFD.gen_dvd_iff (fun p hp hh => d.gen_span ⟨hp, hh⟩) hp (d.gen_prime' hq)).mp hm
  exact hqp (by rw [e, ← d.gen_span hq])

theorem split_at (E : Ideal (KTp K d.D d.N) → ℤ) (hE : {q | q ∈ d.HtOne ∧ E q ≠ 0}.Finite)
    {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne) :
    ∃ V : KTf K d.D d.N, LocAt.UnitAt p V ∧
      (∏ᶠ (q : Ideal (KTp K d.D d.N)) (_ : q ∈ d.HtOne),
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen q) ^ E q) =
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ E p * V := by
  haveI := hp.1
  have hfin : ((d.HtOne \ {p}) ∩ Function.mulSupport
      (fun q => algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen q) ^ E q)).Finite := by
    refine hE.subset ?_
    rintro q ⟨⟨hq, _⟩, hq1⟩
    refine ⟨hq, fun h0 => (Function.mem_mulSupport.mp hq1) ?_⟩
    simp [h0]
  refine ⟨∏ᶠ (q : Ideal (KTp K d.D d.N)) (_ : q ∈ d.HtOne \ {p}), algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen q) ^ E q, ?_, ?_⟩
  · rw [← finprod_mem_inter_mulSupport, finprod_mem_eq_finite_toFinset_prod _ hfin]
    apply LocAt.unitAt_prod
    intro q hq
    rw [Set.Finite.mem_toFinset] at hq
    obtain ⟨⟨hq1, hq2⟩, _⟩ := hq
    exact LocAt.unitAt_zpow
      (LocAt.unitAt_alg (d.gen_not_mem hp hq1 (fun h => hq2 (Set.mem_singleton_iff.mpr h)))) _
  · have hins : d.HtOne = insert p (d.HtOne \ {p}) := by
      ext x
      by_cases hx : x = p
      · subst hx
        simp [hp]
      · simp [hx]
    conv_lhs => rw [hins]
    rw [finprod_mem_insert' _ (fun h => h.2 (Set.mem_singleton p)) hfin]

theorem b_mem_p (hd : d.AxH 𝒜) (h : d.S1) {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne)
    (k : Fin d.del) (c : ι) (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ))
    (hw : w ∈ d.GoodP c p) :
    0 ≤ w (d.bvecG hd.sel hd.a4.choose k c) +
      ((d.ord c (d.Wres c w) d.wF (hd.a4.choose c) : ℤ) : WithTop ℤ) := by
  classical
  obtain ⟨he, -, -⟩ := hd.a4.choose_spec
  obtain ⟨heF, he0⟩ := he c
  have hadm := d.good_adm hd h c hp hw
  have hthpF : d.thp (hd.sel k) c ∈ 𝒜 c d.wF := hd.thp_mem _ c
  obtain ⟨a, ha⟩ : ∃ a : Ω c, d.thp (hd.sel k) c = a • hd.a4.choose c := by
    have he0' : (⟨hd.a4.choose c, heF⟩ : 𝒜 c d.wF) ≠ 0 := by
      intro h0; exact he0 (congrArg Subtype.val h0)
    obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' _ he0').mp (hd.finrank_one c d.wF)
      ⟨_, hthpF⟩
    exact ⟨a, (congrArg Subtype.val ha).symm⟩
  have hb : d.bvecG hd.sel hd.a4.choose k c = algebraMap (Ω c) (OmS (Ω c) d.D d.N) a := by
    simp only [bvecG]
    rw [ValuationResidueLemmas.ratio_eq he0 ha]
  rw [hb]
  change 0 ≤ d.Wres c w a + _
  by_cases ha0 : a = 0
  · rw [ha0, AddValuation.map_zero, top_add]
    exact le_top
  have hth0 : d.thp (hd.sel k) c ≠ 0 := by
    rw [ha]; exact smul_ne_zero ha0 he0
  rw [← hd.ord_smul c _ hadm a heF he0 ha0, ← ha]
  have hmem : d.thp (hd.sel k) ∈ d.Thp := by
    rw [hd.Thp_span]; exact Submodule.subset_span ⟨_, rfl⟩
  exact_mod_cast hd.ord_nonneg_Thp c _ hadm _ hmem hth0

theorem de_local (hd : d.AxH 𝒜) (h : d.S1) {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne) :
    LocAt.IntAt p (d.De hd h * algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^
      (2 * ∑ c, d.nP h c d.wF (hd.a4.choose c) p)) := by
  classical
  letI : ∀ c, Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := fun c => (d.KTtoS h c).toAlgebra
  haveI : ∀ c, FiniteDimensional (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := fun c =>
    (d.omS_finite hd h c).1
  haveI : CharZero (KTf K d.D d.N) :=
    charZero_of_injective_algebraMap (algebraMap K (KTf K d.D d.N)).injective
  haveI : ∀ c, Algebra.IsSeparable (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := fun c =>
    Algebra.IsSeparable.of_integral _ _
  haveI := hp.1
  have hsH : ∀ c x, d.sH c x = algebraMap (KTf K d.D d.N) (OmS (Ω c) d.D d.N)
      (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) x) := fun c x =>
    (IsFractionRing.lift_algebraMap (A := KTp K d.D d.N) (g := (d.sH c).toRingHom) (h c) x).symm
  have hOver : ∀ c, d.OverP c p =
      HNm.OverR (KTp K d.D d.N) (KTf K d.D d.N) (OmS (Ω c) d.D d.N) p := by
    intro c; ext w; simp only [OverP, HNm.OverR, Set.mem_ofPred_eq, hsH]
  let n : ∀ c, AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ) → ℤ := fun c w =>
    if w ∈ d.GoodP c p then d.ord c (d.Wres c w) d.wF (hd.a4.choose c) else 0
  have hb : ∀ k c, ∀ w ∈ HNm.OverR (KTp K d.D d.N) (KTf K d.D d.N) (OmS (Ω c) d.D d.N) p,
      0 ≤ w (d.bvecG hd.sel hd.a4.choose k c) + (n c w : WithTop ℤ) := by
    intro k c w hw
    rw [← hOver c] at hw
    by_cases hg : w ∈ d.GoodP c p
    · simp only [n, if_pos hg]
      exact d.b_mem_p hd h hp k c w hg
    · simp only [n, if_neg hg, WithTop.coe_zero, add_zero]
      have hz : ∀ a : Ω c, a ≠ 0 → d.Wres c w a = 0 := fun a ha =>
        by_contra fun hne => hg ⟨hw, a, ha, hne⟩
      change 0 ≤ d.Wres c w _
      by_cases hr : ratio (Ω := Ω c) (d.thp (hd.sel k) c) (hd.a4.choose c) = 0
      · rw [hr, AddValuation.map_zero]; exact le_top
      · rw [hz _ hr]
  have hexp : ∀ c, (∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ))
      (_ : w ∈ HNm.OverR (KTp K d.D d.N) (KTf K d.D d.N) (OmS (Ω c) d.D d.N) p),
        (HNm.fz (KTf K d.D d.N) w : ℤ) * n c w) = d.nP h c d.wF (hd.a4.choose c) p := by
    intro c
    rw [← hOver c]
    simp only [nP]
    rw [finsum_mem_def, finsum_mem_def]
    refine finsum_congr fun w => ?_
    simp only [Set.indicator_apply, n]
    by_cases hg : w ∈ d.GoodP c p
    · have hg1 : w ∈ d.OverP c p := hg.1
      simp only [hg, hg1, if_true]
      rfl
    · simp only [hg, if_false, mul_zero, ite_self]
  obtain ⟨a, s, hs, he⟩ := HDiscOmL.disc_local (R := KTp K d.D d.N) (F := KTf K d.D d.N)
    (L := fun c => OmS (Ω c) d.D d.N) p hp.2 (d.gen p) (d.gen_span hp) n (d.del_eq hd h)
    (d.bvecG hd.sel hd.a4.choose) (d.b_linIndep hd h) hb
  refine ⟨a, s, hs, ?_⟩
  rw [← he]
  simp only [hexp]
  rfl

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

