import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.Bundle0003
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.Bundle0004
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.Bundle0002
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.EulerIndependenceOfOrder
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.Bundle0004
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.Bundle0003
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.Bundle0001

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ExistsNotInP
section
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

namespace UpperTheory.V.Alg.M.GradedPrimePointLifting

section

variable {B A : Type} [CommRing B] [CommRing A] [Algebra B A] {k : ℕ} {N : Fin k → Submodule B A}

private def InP (p : Ideal (rees N)) (i : Fin k) (n : ℕ) (t : A) : Prop :=
  ∃ q ∈ p, q.1 = MvPolynomial.monomial (Finsupp.single i n) t

private theorem lat_single_pow (i : Fin k) (n : ℕ) : lat N (Finsupp.single i n) = N i ^ n := by
  rw [lat, Finset.prod_eq_single i] <;> simp +contextual [Finsupp.single_apply, eq_comm]

variable {p : Ideal (rees N)} {i : Fin k}

private theorem InP.zero (n : ℕ) : InP p i n 0 := ⟨0, p.zero_mem, by simp⟩

private theorem InP.add {n : ℕ} {t u : A} (ht : InP p i n t) (hu : InP p i n u) : InP p i n (t + u) := by
  obtain ⟨q, hq, e1⟩ := ht
  obtain ⟨q', hq', e2⟩ := hu
  exact ⟨q + q', p.add_mem hq hq', by rw [Subalgebra.coe_add, e1, e2, map_add]⟩

private theorem InP.mul {n m : ℕ} {t u : A} (ht : InP p i n t) (hu : u ∈ N i ^ m) : InP p i (n + m) (t * u) := by
  obtain ⟨q, hq, e1⟩ := ht
  refine ⟨q * mono N (Finsupp.single i m) u ((lat_single_pow (N := N) i m).symm ▸ hu), p.mul_mem_right _ hq, ?_⟩
  rw [Subalgebra.coe_mul, e1, Finsupp.single_add, ← MvPolynomial.monomial_mul]
  rfl

private theorem InP.of_mul (hp : p.IsPrime) {n m : ℕ} {t u : A} (ht : t ∈ N i ^ n) (hu : u ∈ N i ^ m)
    (h : InP p i (n + m) (t * u)) : InP p i n t ∨ InP p i m u := by
  obtain ⟨q, hq, e1⟩ := h
  have : q = mono N (Finsupp.single i n) t ((lat_single_pow (N := N) i n).symm ▸ ht) *
      mono N (Finsupp.single i m) u ((lat_single_pow (N := N) i m).symm ▸ hu) := by
    apply Subtype.ext
    rw [Subalgebra.coe_mul, e1, Finsupp.single_add, ← MvPolynomial.monomial_mul]
    rfl
  rw [this] at hq
  exact (hp.mem_or_mem hq).imp (fun h => ⟨_, h, rfl⟩) (fun h => ⟨_, h, rfl⟩)

private theorem inP_zero_iff (b : B) : InP p i 0 (algebraMap B A b) ↔ algebraMap B (rees N) b ∈ p := by
  have e0 : (algebraMap B (rees N) b).1 = MvPolynomial.monomial (Finsupp.single i 0) (algebraMap B A b) := by
    rw [Finsupp.single_zero, Subalgebra.coe_algebraMap, MvPolynomial.algebraMap_apply]
    rfl
  constructor
  · rintro ⟨q, hq, e1⟩
    rwa [show algebraMap B (rees N) b = q from Subtype.ext (e0.trans e1.symm)]
  · exact fun h => ⟨_, h, e0⟩

private theorem not_inP_pow (hp : p.IsPrime) {f : A} (hf : f ∈ N i) (h : ¬ InP p i 1 f) {b : B}
    (hb : algebraMap B (rees N) b ∉ p) (n : ℕ) : ¬ InP p i n (algebraMap B A b * f ^ n) := by
  induction n with
  | zero => simpa [inP_zero_iff] using hb
  | succ n ih =>
    intro h1
    rw [pow_succ, ← mul_assoc] at h1
    refine (InP.of_mul hp ?_ (by rwa [pow_one]) h1).elim ih h
    rw [← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.pow_mem_pow _ hf n)

private theorem exists_not_inP (h : ¬ Irr (reesGr N) ≤ p) (i : Fin k) : ∃ f ∈ N i, ¬ InP p i 1 f := by
  classical
  by_contra hc
  push Not at hc
  apply h
  refine le_trans (Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_univ i))) (Ideal.span_le.2 fun q hq => ?_)
  obtain ⟨q', hq', e1⟩ := hc _ (lat_single N i ▸ q.2 (Finsupp.single i 1))
  have he : e i = toDeg (Finsupp.single i 1) := by
    funext j; simp [e, toDeg, Pi.single_apply, Finsupp.single_apply, eq_comm]
  have : q = q' := by
    apply Subtype.ext
    rw [e1]
    ext m
    rw [MvPolynomial.coeff_monomial]
    split_ifs with hm
    · rw [hm]
    · exact hq m fun h2 => hm (toDeg_injective (he.symm.trans h2.symm))
  rw [this]
  exact hq'

end

section

variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {𝒜 : ℤ → Submodule O A} [GradedAlgebra 𝒜]
  {k : ℕ} {N : Fin k → Submodule (𝒜 0) A}

private def idJ (p : Ideal (rees N)) (i : Fin k) : Ideal A where
  carrier := {t | ∀ (h : A) (n : ℕ), InP p i (n + 1) (DirectSum.decompose 𝒜 (h * t) (2 * ((n + 1 : ℕ) : ℤ)) : A)}
  add_mem' {a b} ha hb h n := by
    rw [mul_add, DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add]
    exact (ha h n).add (hb h n)
  zero_mem' h n := by
    rw [mul_zero, DirectSum.decompose_zero]
    exact InP.zero _
  smul_mem' c t ht h n := by
    rw [smul_eq_mul, ← mul_assoc]
    exact ht _ n

variable {p : Ideal (rees N)} {i : Fin k}

private theorem mem_idJ {j : ℤ} {t : A} (ht : t ∈ 𝒜 j)
    (H : ∀ (n : ℕ), ∀ h ∈ 𝒜 (2 * ((n + 1 : ℕ) : ℤ) - j), InP p i (n + 1) (h * t)) : t ∈ idJ p i := by
  intro h n
  have := DirectSum.coe_decompose_mul_add_of_right_mem 𝒜 (a := h) (i := 2 * ((n + 1 : ℕ) : ℤ) - j) ht
  rw [sub_add_cancel] at this
  rw [this]
  exact H n _ (Subtype.property _)

private theorem mul_mem' {a b c : ℤ} {t u : A} (ht : t ∈ 𝒜 a) (hu : u ∈ 𝒜 b) (h : a + b = c) : t * u ∈ 𝒜 c :=
  h ▸ SetLike.GradedMul.mul_mem ht hu

private theorem inP_neg (hpos : ∀ n : ℕ, oz 𝒜 (2 * n) = N i ^ n) (hneg : ∀ n : ℕ, oz 𝒜 (-(2 * n)) = oz 𝒜 (-2) ^ n)
    (hD : (idD 𝒜).map (algebraMap (𝒜 0) (rees N)) ≤ p) (l m : ℕ) {a b : A} (ha : a ∈ 𝒜 (-(2 * ((l + 1 : ℕ) : ℤ))))
    (hb : b ∈ 𝒜 (2 * ((m + l + 1 : ℕ) : ℤ))) : InP p i m (a * b) := by
  have h2 : oz 𝒜 2 = N i := by simpa using hpos 1
  have L1 : ∀ c ∈ 𝒜 (-2), ∀ u ∈ 𝒜 (2 * ((m + 1 : ℕ) : ℤ)), InP p i m (c * u) := by
    intro c hc u hu
    rw [← mem_oz, hpos, pow_succ] at hu
    refine Submodule.mul_induction_on hu (fun v hv w hw => ?_) (fun v w hv hw => ?_)
    · rw [← h2, mem_oz] at hw
      have h0 : InP p i 0 (algebraMap (𝒜 0) A ⟨c * w, mul_mem' hc hw (by norm_num)⟩) :=
        (inP_zero_iff _).2 (hD (Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨c, hc, w, hw, rfl⟩)))
      have h1 := h0.mul hv
      rw [zero_add] at h1
      have e1 : c * (v * w) = c * w * v := by ring
      rw [e1]
      exact h1
    · rw [mul_add]; exact hv.add hw
  rw [← mem_oz, hneg, pow_succ, ← hneg] at ha
  refine Submodule.mul_induction_on ha (fun v hv w hw => ?_) (fun v w hv hw => ?_)
  · have e1 : v * w * b = w * (v * b) := by ring
    rw [e1]
    exact L1 w hw _ (mul_mem' hv hb (by push_cast; ring))
  · rw [add_mul]; exact hv.add hw

private theorem neg_mem_idJ (hp : p.IsPrime) (hpos : ∀ n : ℕ, oz 𝒜 (2 * n) = N i ^ n)
    (hneg : ∀ n : ℕ, oz 𝒜 (-(2 * n)) = oz 𝒜 (-2) ^ n)
    (hD : (idD 𝒜).map (algebraMap (𝒜 0) (rees N)) ≤ p) {j : ℤ} (hj : j < 0) {g : A} (hg : g ∈ 𝒜 j) :
    g ∈ idJ p i := by
  refine mem_idJ hg fun n h hh => ?_
  obtain ⟨l, rfl⟩ : ∃ l : ℕ, j = -((l + 1 : ℕ) : ℤ) := ⟨(-j - 1).toNat, by omega⟩
  have hm : h * g ∈ N i ^ (n + 1) := by
    rw [← hpos, mem_oz]; exact mul_mem' hh hg (by ring)
  refine (InP.of_mul hp hm hm ?_).elim id id
  have e1 : h * g * (h * g) = (g * g) * (h * h) := by ring
  rw [e1]
  exact inP_neg hpos hneg hD l _ (mul_mem' hg hg (by ring)) (mul_mem' hh hh (by push_cast; ring))

private theorem two_mem_idJ (hpos : ∀ n : ℕ, oz 𝒜 (2 * n) = N i ^ n) {g : A} (hg : g ∈ 𝒜 2) (H : InP p i 1 g) :
    g ∈ idJ p i := by
  refine mem_idJ hg fun n h hh => ?_
  have hm : h ∈ N i ^ n := by
    rw [← hpos, mem_oz]; convert hh using 2; push_cast; ring
  rw [mul_comm, add_comm]
  exact H.mul hm

private theorem one_mem_idJ (hp : p.IsPrime) (hpos : ∀ n : ℕ, oz 𝒜 (2 * n) = N i ^ n) {g : A} (hg : g ∈ 𝒜 1)
    (H : InP p i 1 (g ^ 2)) : g ∈ idJ p i := by
  refine mem_idJ hg fun n h hh => ?_
  have hm : h * g ∈ N i ^ (n + 1) := by
    rw [← hpos, mem_oz]; exact mul_mem' hh hg (by ring)
  refine (InP.of_mul hp hm hm ?_).elim id id
  have h2 : h * h ∈ N i ^ (2 * n + 1) := by
    rw [← hpos, mem_oz]; exact mul_mem' hh hh (by push_cast; ring)
  have e1 : h * g * (h * g) = g ^ 2 * (h * h) := by ring
  have e2 : n + 1 + (n + 1) = 1 + (2 * n + 1) := by ring
  rw [e1, e2]
  exact H.mul h2

private theorem zero_mem_idJ (hpos : ∀ n : ℕ, oz 𝒜 (2 * n) = N i ^ n) {b : 𝒜 0}
    (H : algebraMap (𝒜 0) (rees N) b ∈ p) : algebraMap (𝒜 0) A b ∈ idJ p i := by
  refine mem_idJ (j := 0) b.2 fun n h hh => ?_
  have hm : h ∈ N i ^ (n + 1) := by
    rw [← hpos, mem_oz]; rwa [sub_zero] at hh
  have := ((inP_zero_iff b).2 H).mul hm
  rwa [zero_add, mul_comm] at this

private theorem not_mem_idJ (hp : p.IsPrime) (hpos : ∀ n : ℕ, oz 𝒜 (2 * n) = N i ^ n) {f : A} (hf : f ∈ N i)
    (h : ¬ InP p i 1 f) {b : 𝒜 0} (hb : algebraMap (𝒜 0) (rees N) b ∉ p) (n : ℕ) :
    algebraMap (𝒜 0) A b * f ^ n ∉ idJ p i := by
  intro H
  apply not_inP_pow hp hf h hb (n + 1)
  have h1 := H f n
  have e1 : f * (algebraMap (𝒜 0) A b * f ^ n) = algebraMap (𝒜 0) A b * f ^ (n + 1) := by ring
  have hm : algebraMap (𝒜 0) A b * f ^ (n + 1) ∈ 𝒜 (2 * ((n + 1 : ℕ) : ℤ)) := by
    rw [← mem_oz, hpos, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.pow_mem_pow _ hf _)
  rwa [e1, DirectSum.decompose_of_mem_same 𝒜 hm] at h1

end

end UpperTheory.V.Alg.M.GradedPrimePointLifting

open UpperTheory.V.Alg.M.GradedPrimePointLifting in
theorem UpperTheory.V.Alg.M.zp_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ (r s r' s' m : ℕ) (Q : Eqns 𝒜 x r s r' s' m),
    ∀ p : Ideal (mR Q), p.IsPrime → ¬ Irr (mGr Q) ≤ p → secs (ts Q) ≤ p → (∀ i, algebraMap (𝒜 0) (mR Q) ⟨Q.Z i, (Q.hZ i).1⟩ ∈ p) →
      (idD 𝒜).map (algebraMap (𝒜 0) (mR Q)) ≤ p → ∀ σ : 𝒜 0 →ₐ[O] K, RingHom.ker σ = p.comap (algebraMap (𝒜 0) (mR Q)) →
      ∃ ξ : A →ₐ[O] K, OnS Q.ideal ξ ∧ NegZero 𝒜 ξ ∧ ¬ PosZero 𝒜 ξ ∧ res0 𝒜 ξ = σ := by
  intro O _ _ _ _ _ K _ _ _ _ A _ _ 𝒜 _ _ x hW r s r' s' m Q p hp hI hs hZ hD σ hσ
  have hpos : ∀ n : ℕ, oz 𝒜 (2 * n) = mN 𝒜 (Q.F (Fin.last r)) 1 ^ n := fun n => (oz_two_mul_eq_pow O A 𝒜 x hW n).2
  have hneg : ∀ n : ℕ, oz 𝒜 (-(2 * n)) = oz 𝒜 (-2) ^ n := fun n => (oz_two_mul_eq_pow O A 𝒜 x hW n).1
  have hk : ∀ b, σ b = 0 ↔ algebraMap (𝒜 0) (mR Q) b ∈ p := fun b => by
    rw [← RingHom.mem_ker, hσ, Ideal.mem_comap]
  obtain ⟨f, hf, hfp⟩ := exists_not_inP hI 1
  haveI := (ft_holds O A 𝒜 x hW).1
  obtain ⟨ξ, h0, hJ, hξ⟩ := ns_holds O (𝒜 0) A K σ (idJ p 1) f (fun b hb => zero_mem_idJ hpos ((hk b).1 hb))
    (fun b n hb => not_mem_idJ hp hpos hf hfp (fun h => hb ((hk b).2 h)) n)
  have hN : NegZero 𝒜 ξ := fun j hj g hg => hJ _ (neg_mem_idJ hp hpos hneg hD hj hg)
  refine ⟨ξ, ?_, hN, fun h => hξ (h 2 (by norm_num) f hf), AlgHom.ext fun b => h0 b⟩
  intro g hg
  refine (Ideal.span_le.2 ?_ : Q.ideal ≤ RingHom.ker ξ) hg
  rintro _ ((((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩)
  · exact hN _ (by norm_num) _ (Q.hF i)
  · exact hN _ (by norm_num) _ (Q.hG i)
  · refine hJ _ (one_mem_idJ hp hpos (Q.hE i)
      ⟨sec _ 1 (Q.E i ^ 2) (sq_mem_pos 𝒜 (Q.hE i)), hs (Ideal.subset_span ⟨e 1, ?_⟩), rfl⟩)
    simp only [ts, tsR, List.mem_append, List.mem_ofFn]
    exact Or.inr (Or.inl (Or.inl (Or.inr ⟨i, rfl⟩)))
  · refine hJ _ (two_mem_idJ hpos (Q.hE' i)
      ⟨sec _ 1 (Q.E' i) (Q.hE' i), hs (Ideal.subset_span ⟨e 1, ?_⟩), rfl⟩)
    simp only [ts, tsR, List.mem_append, List.mem_ofFn]
    exact Or.inr (Or.inl (Or.inr ⟨i, rfl⟩))
  · exact hJ _ (zero_mem_idJ hpos (hZ i))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.FixHolds
section
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

theorem UpperTheory.V.Alg.M.fix_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ (r s r' s' m : ℕ) (Q : Eqns 𝒜 x r s r' s' m),
    ∀ σ : 𝒜 0 →ₐ[O] K, idD 𝒜 ≤ RingHom.ker σ → (∀ b : 𝒜 0, (b : A) ∈ Q.ideal → σ b = 0) →
      ∃ ξ : A →ₐ[O] K, OnS Q.ideal ξ ∧ NegZero 𝒜 ξ ∧ PosZero 𝒜 ξ ∧ res0 𝒜 ξ = σ := by
  intro O _ _ _ _ _ K _ _ _ _ A _ _ 𝒜 _ _ x hW r s r' s' m Q σ hid hQ
  have hcoe : ∀ z (hz : z ∈ 𝒜 0), DirectSum.decompose 𝒜 z 0 = ⟨z, hz⟩ :=
    fun z hz => Subtype.ext (DirectSum.decompose_of_mem_same 𝒜 hz)
  have dmul : ∀ (i : ℤ) (z : A), z ∈ 𝒜 i → ∀ b : A,
      (DirectSum.decompose 𝒜 (z * b) 0 : A) = z * (DirectSum.decompose 𝒜 b (-i) : A) := by
    intro i z hz b
    have h := DirectSum.coe_decompose_mul_add_of_left_mem 𝒜 (j := -i) hz (b := b)
    rwa [add_neg_cancel] at h
  have kill : ∀ c : 𝒜 0, ∀ f ∈ 𝒜 (-2), ∀ g ∈ 𝒜 2, (c : A) = f * g → σ c = 0 := by
    intro c f hf g hg h
    exact (RingHom.mem_ker).1 (hid (Ideal.subset_span ⟨f, hf, g, hg, h⟩))
  have kill1 : ∀ c : 𝒜 0, ∀ f ∈ 𝒜 (-1), ∀ g ∈ 𝒜 1, (c : A) = f * g → σ c = 0 := by
    intro c f hf g hg h
    have hff : f * f ∈ 𝒜 (-2) := by
      convert SetLike.mul_mem_graded hf hf using 2
      norm_num
    have hgg : g * g ∈ 𝒜 2 := by
      convert SetLike.mul_mem_graded hg hg using 2
      norm_num
    have h2 : σ (c * c) = 0 := kill (c * c) (f * f) hff (g * g) hgg (by
      rw [SetLike.GradeZero.coe_mul, h]
      ring)
    rw [map_mul] at h2
    exact mul_self_eq_zero.1 h2
  obtain ⟨S, hS, hgen⟩ := hW.gen
  have key : ∀ z ∈ S, ∀ b : A, σ (DirectSum.decompose 𝒜 (z * b) 0) = 0 := by
    intro z hz b
    rcases hS z hz with h | h | h | h
    · refine kill _ z h _ (DirectSum.decompose 𝒜 b 2).2 ?_
      rw [dmul _ z h b, neg_neg]
    · refine kill1 _ z h _ (DirectSum.decompose 𝒜 b 1).2 ?_
      rw [dmul _ z h b, neg_neg]
    · refine kill1 _ _ (DirectSum.decompose 𝒜 b (-1)).2 z h ?_
      rw [dmul _ z h b, mul_comm]
    · refine kill _ _ (DirectSum.decompose 𝒜 b (-2)).2 z h ?_
      rw [dmul _ z h b, mul_comm]
  have h0 : ∀ z ∈ 𝒜 0, ∀ b : A, σ (DirectSum.decompose 𝒜 (z * b) 0) =
      σ (DirectSum.decompose 𝒜 z 0) * σ (DirectSum.decompose 𝒜 b 0) := by
    intro z hz b
    have h1 : DirectSum.decompose 𝒜 (z * b) 0 = ⟨z, hz⟩ * DirectSum.decompose 𝒜 b 0 := by
      apply Subtype.ext
      rw [SetLike.GradeZero.coe_mul]
      have h := DirectSum.coe_decompose_mul_add_of_left_mem 𝒜 (j := 0) hz (b := b)
      rw [add_zero] at h
      exact h
    rw [h1, hcoe z hz, map_mul]
  have hmul : ∀ a b : A, σ (DirectSum.decompose 𝒜 (a * b) 0) =
      σ (DirectSum.decompose 𝒜 a 0) * σ (DirectSum.decompose 𝒜 b 0) := by
    intro a b
    have ha : a ∈ Algebra.adjoin O ((𝒜 0 : Set A) ∪ S) := by
      rw [hgen]
      trivial
    induction ha using Algebra.adjoin_induction generalizing b with
    | mem z hz =>
      rcases hz with hz | hz
      · exact h0 z hz b
      · have hz0 : DirectSum.decompose 𝒜 z 0 = 0 := by
          apply Subtype.ext
          rcases hS z hz with h | h | h | h <;>
            (rw [DirectSum.decompose_of_mem_ne 𝒜 h (by norm_num)]; rfl)
        rw [key z hz b, hz0, map_zero, zero_mul]
    | algebraMap c => exact h0 _ (SetLike.algebraMap_mem_graded 𝒜 c) b
    | add a a' _ _ iha iha' =>
      rw [add_mul, DirectSum.decompose_add, DirectSum.add_apply, map_add, iha, iha',
        DirectSum.decompose_add, DirectSum.add_apply, map_add, add_mul]
    | mul a a' _ _ iha iha' =>
      rw [mul_assoc, iha (a' * b), iha' b, iha a']
      ring
  let ξ : A →ₐ[O] K :=
    { toFun := fun a => σ (DirectSum.decompose 𝒜 a 0)
      map_one' := by
        show σ (DirectSum.decompose 𝒜 1 0) = 1
        rw [show DirectSum.decompose 𝒜 (1 : A) 0 = 1 from Subtype.ext (by
          rw [DirectSum.decompose_of_mem_same 𝒜 (SetLike.one_mem_graded 𝒜),
            SetLike.GradeZero.coe_one]), map_one]
      map_mul' := hmul
      map_zero' := by simp
      map_add' := by
        intro a b
        show σ (DirectSum.decompose 𝒜 (a + b) 0) =
          σ (DirectSum.decompose 𝒜 a 0) + σ (DirectSum.decompose 𝒜 b 0)
        rw [DirectSum.decompose_add, DirectSum.add_apply, map_add]
      commutes' := by
        intro c
        show σ (DirectSum.decompose 𝒜 (algebraMap O A c) 0) = algebraMap O K c
        rw [hcoe _ (SetLike.algebraMap_mem_graded 𝒜 c)]
        rw [show (⟨algebraMap O A c, SetLike.algebraMap_mem_graded 𝒜 c⟩ : 𝒜 0) =
          algebraMap O (𝒜 0) c from Subtype.ext (SetLike.GradeZero.coe_algebraMap 𝒜 c).symm]
        exact σ.commutes c }
  have hξ : ∀ a, ξ a = σ (DirectSum.decompose 𝒜 a 0) := fun a => rfl
  have hne : ∀ j : ℤ, j ≠ 0 → ∀ f ∈ 𝒜 j, ξ f = 0 := by
    intro j hj f hf
    rw [hξ, show DirectSum.decompose 𝒜 f 0 = 0 from Subtype.ext (by
      rw [DirectSum.decompose_of_mem_ne 𝒜 hf hj]; rfl), map_zero]
  refine ⟨ξ, ?_, ?_, ?_, ?_⟩
  · intro f hf
    have hle : Q.ideal ≤ RingHom.ker ξ := by
      unfold Eqns.ideal
      rw [Ideal.span_le]
      intro y hy
      rw [SetLike.mem_coe, RingHom.mem_ker]
      rcases hy with ((((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩)
      · exact hne (-1) (by norm_num) _ (Q.hF i)
      · exact hne (-2) (by norm_num) _ (Q.hG i)
      · exact hne 1 (by norm_num) _ (Q.hE i)
      · exact hne 2 (by norm_num) _ (Q.hE' i)
      · rw [hξ, hcoe _ (Q.hZ i).1]
        exact hQ ⟨Q.Z i, (Q.hZ i).1⟩ (Ideal.subset_span (Set.mem_union_right _ ⟨i, rfl⟩))
    exact (RingHom.mem_ker).1 (hle hf)
  · intro j hj f hf
    exact hne j (by omega) f hf
  · intro j hj f hf
    exact hne j (by omega) f hf
  · refine AlgHom.ext fun b => ?_
    show σ (DirectSum.decompose 𝒜 ((b : 𝒜 0) : A) 0) = σ b
    rw [DirectSum.decompose_coe, DirectSum.of_eq_same]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.LaDifPerm
section
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem la_dif_perm {k : ℕ} {l l' : List (Deg k)} (h : l.Perm l') (f : Deg k → ℤ) :
    ∀ m, dif l f m = dif l' f m := by
  induction h with
  | nil => intro m; rfl
  | cons a _ ih => intro m; simp only [dif, ih]
  | swap a b l =>
    intro m
    simp only [dif]
    rw [sub_right_comm m a b]
    ring
  | trans _ _ ih1 ih2 => intro m; rw [ih1, ih2]

private theorem la_hdiff {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R]
    (ts : List (Deg k × R)) (G : GMod B R k) :
    ∀ m, Sm.hdiff ts G m = dif (ts.map Prod.fst) (hilb G) m := by
  induction ts with
  | nil => intro m; rw [Sm.hdiff_nil]; rfl
  | cons p ts ih =>
    obtain ⟨d, s⟩ := p
    intro m
    rw [Sm.hdiff_cons, ih, ih]
    rfl

private theorem la_adm {k : ℕ} (X : HidaSetting k) (J : Ideal X.R) (d : Deg k) (a y : X.R)
    (ts : List (Deg k × X.R)) (h : admitted X.𝒜 ((d, a * y) :: ts) J) : admitted X.𝒜 ((d, y) :: ts) J := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, hN.trans (sup_le_sup_left ?_ _)⟩
  rw [secs, Ideal.span_le]
  rintro x ⟨e, he⟩
  rcases List.mem_cons.1 he with h | h
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, List.mem_cons_self⟩)
  · exact Ideal.subset_span ⟨e, List.mem_cons_of_mem _ h⟩

private theorem la_mem {k : ℕ} (X : HidaSetting k) (β : X.B) (c : ℕ) {d : Deg k} {y : X.R} (hy : y ∈ X.𝒜 d) :
    algebraMap X.B X.R β ^ c * y ∈ X.𝒜 d := by
  rw [← map_pow, ← Algebra.smul_def]
  exact Submodule.smul_mem _ _ hy

private theorem la_peel {k : ℕ} (X : HidaSetting k) (F : X.Mod) (hF : F.IsGr X.𝒜) (β : X.B)
    (hβ : ∀ y : F.M, algebraMap X.B X.R β • y = 0 → y = 0)
    (hA : admitted X.𝒜 [] (F.quot (algebraMap X.B X.R β)).Ann) (d : Deg k) (hd : 0 ≤ d) (y : X.R)
    (hy : y ∈ X.𝒜 d) (ts : List (Deg k × X.R)) (hV : Valid X.𝒜 ts) (c : ℕ) :
    admitted X.𝒜 ((d, algebraMap X.B X.R β ^ c * y) :: ts) F.Ann →
    ∀ᶠ m in atTop, chi ((d, algebraMap X.B X.R β ^ c * y) :: ts) F m =
      (c : ℤ) * dif (ts.map Prod.fst) (hilb (F.quot (algebraMap X.B X.R β))) m + chi ((d, y) :: ts) F m := by
  have hb : algebraMap X.B X.R β ∈ X.𝒜 0 := by
    rw [X.std.zero]; exact ⟨β, rfl⟩
  have hs := ruleSmall k X ts _ hV ((ruleGr k X F hF).2.2 0 _ hb).1 hA
  induction c with
  | zero => intro _; simp
  | succ c ih =>
    intro h
    rw [pow_succ', mul_assoc] at h ⊢
    have hV' : Valid X.𝒜 ((0, algebraMap X.B X.R β) :: (d, algebraMap X.B X.R β ^ c * y) :: ts) := by
      intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact ⟨le_rfl, hb⟩
      rcases List.mem_cons.1 hp with rfl | hp
      · exact ⟨hd, la_mem X β c hy⟩
      · exact hV p hp
    filter_upwards [euler_rule_product_zero k X ts F d _ _ hV' hF h, ih (la_adm X _ d _ _ ts h), hs] with m h1 h2 h3
    have h4 : chi ts (F.quot (algebraMap X.B X.R β)) m = _ := h3.trans (la_hdiff ts _ m)
    rw [h1, h2, ruleNzd k X ts F 0 _ hβ m, h4]
    push_cast
    ring

theorem UpperTheory.V.Alg.M.la_holds :
    ∀ (k : ℕ) (X : HidaSetting k) (F : X.Mod), F.IsGr X.𝒜 → ∀ β : X.B, (∀ y : F.M, algebraMap X.B X.R β • y = 0 → y = 0) →
      admitted X.𝒜 [] (F.quot (algebraMap X.B X.R β)).Ann → ∀ (d : Deg k), 0 ≤ d → ∀ (n : ℕ) (y : Fin n → X.R) (c : Fin n → ℕ),
      (∀ i, y i ∈ X.𝒜 d) → ∀ us : List (Deg k × X.R), Valid X.𝒜 us →
      admitted X.𝒜 ((List.ofFn fun i => (d, algebraMap X.B X.R β ^ c i * y i)) ++ us) F.Ann →
      ∀ᶠ m in atTop, ((∑ i, c i : ℕ) : ℤ) * dif (List.replicate (n - 1) d ++ us.map Prod.fst) (hilb (F.quot (algebraMap X.B X.R β))) m ≤
        chi ((List.ofFn fun i => (d, algebraMap X.B X.R β ^ c i * y i)) ++ us) F m := by
  intro k X F hF β hβ hA d hd n
  induction n with
  | zero =>
    intro y c _ us hV h
    simpa using rulePos k X us F hV hF (by simpa using h)
  | succ n ih =>
    intro y c hy us hV h
    rw [List.ofFn_succ, List.cons_append] at h ⊢
    set L := (List.ofFn fun i : Fin n => (d, algebraMap X.B X.R β ^ c i.succ * y i.succ)) with hL
    have hVL : Valid X.𝒜 (L ++ us) := by
      intro p hp
      rcases List.mem_append.1 hp with hp | hp
      · obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hp
        exact ⟨hd, la_mem X β _ (hy _)⟩
      · exact hV p hp
    have hc : ∀ l, Valid X.𝒜 l → Valid X.𝒜 ((d, y 0) :: l) := by
      intro l hl p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact ⟨hd, hy 0⟩
      · exact hl p hp
    have hP : ((d, y 0) :: (L ++ us)).Perm (L ++ (d, y 0) :: us) := List.perm_middle.symm
    have h' := la_adm X _ d _ _ _ h
    have h'' : admitted X.𝒜 (L ++ (d, y 0) :: us) F.Ann := by
      unfold admitted at h' ⊢
      rwa [← E2.secs_perm hP]
    have hfst : (L ++ us).map Prod.fst = List.replicate n d ++ us.map Prod.fst := by
      rw [List.map_append, hL, List.map_ofFn]
      congr 1
      exact List.ofFn_const n d
    filter_upwards [la_peel X F hF β hβ hA d hd (y 0) (hy 0) _ hVL (c 0) h,
      euler_rule_two_of_graded_finite_iso ruleGr ruleFin ruleIso (euler_additivity_of_rules ruleGr ruleFin ruleIso) k X _ _ F (hc _ hVL) hP hF h',
      ih (fun i => y i.succ) (fun i => c i.succ) (fun i => hy _) _ (hc _ hV) h''] with m h1 h2 h3
    rw [h1, h2, hfst, Fin.sum_univ_succ, Nat.add_sub_cancel, Nat.cast_add, add_mul]
    refine add_le_add le_rfl (le_trans (le_of_eq ?_) h3)
    cases n with
    | zero => simp
    | succ n =>
      congr 1
      refine la_dif_perm ?_ _ m
      rw [Nat.add_sub_cancel, List.replicate_succ, List.map_cons, List.cons_append]
      exact List.perm_middle.symm
end

