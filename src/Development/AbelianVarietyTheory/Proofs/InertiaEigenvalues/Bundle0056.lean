import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0020
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0021
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0018
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0022

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniqueIntegralAdditiveSystemFrobeniusPower
section
open GlobalTheory.PMonE Finset

namespace GlobalTheory.PMonE

theorem gsum_sub_of_charP {F : Type*} [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] {m : Type*} [Fintype m]
    (e D : ℕ) (M : ℕ → Matrix m m F) (x y : m → F) :
    gsum (p ^ e) D M (x - y) = gsum (p ^ e) D M x - gsum (p ^ e) D M y := by
  unfold gsum
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← Matrix.mulVec_sub]
  congr 1
  funext i
  simp only [Pi.sub_apply, ← pow_mul]
  exact sub_pow_char_pow _ _ _

theorem norm_gsum_le_of_small {F : Type*} [NormedField F] [IsUltrametricDist F] {m : Type*} [Fintype m]
    (q D : ℕ) (hq : 0 < q) (M : ℕ → Matrix m m F) (δ : ℝ) (hδ : 0 ≤ δ)
    (hM : ∀ n, n ≤ D → ∀ i j, ‖M n i j‖ ≤ δ) (z : m → F) (hz : ‖z‖ ≤ 1) :
    ‖gsum q D M z‖ ≤ δ * ‖z‖ := by
  have h0 : 0 ≤ δ * ‖z‖ := mul_nonneg hδ (norm_nonneg _)
  rw [pi_norm_le_iff_of_nonneg h0]
  intro i
  unfold gsum
  rw [Finset.sum_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg h0 fun n hn => ?_
  simp only [Matrix.mulVec, dotProduct]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg h0 fun j _ => ?_
  rw [norm_mul, norm_pow]
  have hj : ‖z j‖ ≤ ‖z‖ := norm_le_pi_norm z j
  refine mul_le_mul (hM n (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)) i j) ?_ (by positivity) hδ
  exact (pow_le_of_le_one (norm_nonneg _) (hj.trans hz) (pow_pos hq n).ne').trans hj

theorem gsum_eq_add_gsum_update {F : Type*} [NormedField F] {m : Type*} [Fintype m] [DecidableEq m]
    (q D : ℕ) (U : ℕ → Matrix m m F) (y : m → F) :
    gsum q D U y = y + gsum q D (fun n => if n = 0 then U 0 - 1 else U n) y := by
  unfold gsum
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  simp [Matrix.sub_mulVec]
  abel

theorem existsUnique_integral_gsum_eq (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F]
    (p : ℕ) [Fact p.Prime] [CharP F p] (m : Type) [Fintype m] [DecidableEq m] (e D : ℕ) (_he : 0 < e)
    (U : ℕ → Matrix m m F) (h0 : ∀ i j, ‖(U 0 - 1) i j‖ < 1) (h1 : ∀ n, 1 ≤ n → ∀ i j, ‖U n i j‖ < 1)
    (b : m → F) (hb : Integral b) : ∃! y : m → F, Integral y ∧ gsum (p ^ e) D U y = b := by
  set V : ℕ → Matrix m m F := fun n => if n = 0 then U 0 - 1 else U n with hV
  have hVs : ∀ n i j, ‖V n i j‖ < 1 := by
    intro n i j
    by_cases hn : n = 0
    · simpa [hV, hn] using h0 i j
    · simpa [hV, hn] using h1 n (Nat.one_le_iff_ne_zero.mpr hn) i j
  obtain ⟨δ, hδ1, hδ⟩ : ∃ δ : NNReal, δ < 1 ∧ ∀ n, n ≤ D → ∀ i j, ‖V n i j‖ ≤ δ := by
    refine ⟨((range (D + 1)) ×ˢ (univ : Finset (m × m))).sup fun t => ‖V t.1 t.2.1 t.2.2‖₊, ?_, ?_⟩
    · rw [Finset.sup_lt_iff (by simp)]
      intro t _
      exact_mod_cast hVs t.1 t.2.1 t.2.2
    · intro n hn i j
      have := Finset.le_sup (f := fun t : ℕ × m × m => ‖V t.1 t.2.1 t.2.2‖₊)
        (s := (range (D + 1)) ×ˢ (univ : Finset (m × m))) (b := (n, i, j))
        (by simp [Nat.lt_succ_iff, hn])
      exact_mod_cast this
  have hq : 0 < p ^ e := pow_pos (Fact.out : p.Prime).pos e
  have hint : ∀ y : m → F, Integral y ↔ ‖y‖ ≤ 1 := fun y => (pi_norm_le_iff_of_nonneg zero_le_one).symm
  have hbound := norm_gsum_le_of_small (p ^ e) D hq V δ δ.2 hδ
  have hδ1' : (δ : ℝ) < 1 := by exact_mod_cast hδ1
  have hsub : ∀ x y : m → F, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 → ‖x - y‖ ≤ 1 := by
    intro x y hx hy
    rw [← hint] at *
    intro i
    rw [Pi.sub_apply, sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hx i) ?_)
    rw [norm_neg]; exact hy i
  let T : (m → F) → (m → F) := fun y => b - gsum (p ^ e) D V y
  let S : Set (m → F) := Metric.closedBall 0 1
  have hS : ∀ y, y ∈ S ↔ ‖y‖ ≤ 1 := fun y => mem_closedBall_zero_iff
  have hT : ∀ x y : m → F, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 → ‖T x - T y‖ ≤ δ * ‖x - y‖ := by
    intro x y hx hy
    have : T x - T y = - gsum (p ^ e) D V (x - y) := by
      rw [gsum_sub_of_charP]; simp only [T]; abel
    rw [this, norm_neg]
    exact hbound _ (hsub x y hx hy)
  have hmaps : Set.MapsTo T S S := by
    intro y hy
    rw [hS] at hy ⊢
    refine hsub _ _ ((hint b).mp hb) ((hbound y hy).trans ?_)
    exact mul_le_one₀ hδ1'.le (norm_nonneg _) hy
  have hc : ContractingWith δ (hmaps.restrict T S S) := by
    refine ⟨hδ1, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
    exact hT x y ((hS _).mp x.2) ((hS _).mp y.2)
  have hfix : ∀ y, gsum (p ^ e) D U y = b ↔ T y = y := by
    intro y
    rw [gsum_eq_add_gsum_update]
    simp only [T]
    constructor
    · intro h; rw [← h]; simp [hV]
    · intro h; rw [sub_eq_iff_eq_add] at h; exact h.symm
  obtain ⟨y, hyS, hy, -⟩ := hc.exists_fixedPoint' Metric.isClosed_closedBall.isComplete hmaps
    (x := 0) ((hS 0).mpr (by simp)) (edist_ne_top _ _)
  refine ⟨y, ⟨(hint y).mpr ((hS y).mp hyS), (hfix y).mpr hy⟩, ?_⟩
  rintro x ⟨hx, hx'⟩
  have h := hT x y ((hint x).mp hx) ((hS y).mp hyS)
  rw [(hfix x).mp hx', show T y = y from hy] at h
  have hn := norm_nonneg (x - y)
  have : ‖x - y‖ = 0 := by nlinarith
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

end GlobalTheory.PMonE
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitBasePointAdjoinTwistedSigma
section
noncomputable section

namespace GlobalTheory.UnitLemma.UnitBase

open GlobalTheory.UnitLemma Polynomial

theorem mem_adjoin_of_mul_eq_one' {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {s t : A}
    (h : s * t = 1) (ht : IsIntegral O t) : t ∈ Algebra.adjoin O {s} := by
  obtain ⟨p, hp, hpt⟩ := ht
  have e : aeval t p = 0 := hpt
  rw [aeval_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, one_smul] at e
  rcases Nat.eq_zero_or_pos p.natDegree with h0 | hpos
  · rw [h0] at e
    simp at e
    have : t = 0 := by simpa using congrArg (t * ·) e
    rw [this]; exact Subalgebra.zero_mem _
  obtain ⟨k, hk⟩ : ∃ k, p.natDegree = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
  rw [hk] at e
  have hts : t * s = 1 := by rw [mul_comm]; exact h
  have h1 : t ^ (k + 1) * s ^ k = t := by
    rw [pow_succ', mul_assoc, ← mul_pow, hts, one_pow, mul_one]
  have h2 : ∀ i ∈ Finset.range (k + 1), p.coeff i • t ^ i * s ^ k = p.coeff i • s ^ (k - i) := by
    intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    rw [smul_mul_assoc]
    congr 1
    rw [show s ^ k = s ^ i * s ^ (k - i) by rw [← pow_add, Nat.add_sub_cancel' hik], ← mul_assoc,
      ← mul_pow, hts, one_pow, one_mul]
  have e2 := congrArg (· * s ^ k) e
  simp only [add_mul, zero_mul, Finset.sum_mul] at e2
  rw [Finset.sum_congr rfl h2, h1] at e2
  have key : t = -∑ i ∈ Finset.range (k + 1), p.coeff i • s ^ (k - i) := by
    linear_combination e2
  rw [key]
  exact Subalgebra.neg_mem _ (Subalgebra.sum_mem _ fun i _ =>
    Subalgebra.smul_mem _ (Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton O s) _) _)

theorem exists_isUnit_add_mul_twist {R : Type} [CommRing R] (τ : R ≃+* R) (hτ : ∀ y, τ (τ y) = y)
    (a : R) (ha : IsUnit a) (hfin : {M : Ideal R | M.IsMaximal}.Finite)
    (x : R) (hx : IsUnit (τ x - x)) : ∃ y : R, IsUnit (y + a * τ y) := by
  classical
  haveI : Finite {M : Ideal R // M.IsMaximal} := hfin.to_subtype
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin {M : Ideal R // M.IsMaximal}
  let pt : {M : Ideal R // M.IsMaximal} → {M : Ideal R // M.IsMaximal} := fun M =>
    ⟨M.1.comap (τ : R →+* R), by haveI := M.2; exact Ideal.comap_isMaximal_of_surjective _ τ.surjective⟩
  have mem_pt : ∀ M z, z ∈ (pt M).1 ↔ τ z ∈ M.1 := fun M z => Iff.rfl
  have pt_pt : ∀ M, pt (pt M) = M := by
    intro M; apply Subtype.ext; ext z; rw [mem_pt, mem_pt, hτ]
  let t : {M : Ideal R // M.IsMaximal} → R := fun M =>
    if pt M = M then (if 1 + a ∈ M.1 then x else 1) else if e M < e (pt M) then 1 else 0
  have hcop : Pairwise (Function.onFun IsCoprime fun M : {M : Ideal R // M.IsMaximal} => M.1) := by
    intro M N hne
    haveI := M.2; haveI := N.2
    exact Ideal.isCoprime_of_isMaximal (fun h => hne (Subtype.ext h))
  obtain ⟨q, hq⟩ := Ideal.quotientInfToPiQuotient_surj hcop (fun M => Ideal.Quotient.mk M.1 (t M))
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
  have hy : ∀ M : {M : Ideal R // M.IsMaximal}, y - t M ∈ M.1 := by
    intro M
    have := congrFun hq M
    rw [Ideal.quotientInfToPiQuotient_mk'] at this
    exact Ideal.Quotient.eq.1 this
  refine ⟨y, ?_⟩
  by_contra hnu
  obtain ⟨M0, hM0, hyM⟩ := exists_max_ideal_of_mem_nonunits hnu
  set M : {M : Ideal R // M.IsMaximal} := ⟨M0, hM0⟩ with hMdef
  have hyM' : y + a * τ y ∈ M.1 := hyM
  have hne1 : (1 : R) ∉ M.1 := fun h => hM0.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have hunit : ∀ {u : R}, IsUnit u → u ∉ M.1 := fun hu h => hM0.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)
  by_cases hfix : pt M = M
  · have hτM : ∀ z, z ∈ M.1 → τ z ∈ M.1 := by
      intro z hz; rw [← mem_pt, hfix]; exact hz
    have hd := hy M
    have ht : t M + a * τ (t M) ∈ M.1 := by
      have : t M + a * τ (t M) = (y + a * τ y) - (y - t M) - a * τ (y - t M) := by
        rw [map_sub]; ring
      rw [this]
      exact M.1.sub_mem (M.1.sub_mem hyM' hd) (M.1.mul_mem_left _ (hτM _ hd))
    by_cases h1a : 1 + a ∈ M.1
    · have htx : t M = x := by simp only [t, if_pos hfix, if_pos h1a]
      rw [htx] at ht
      have : a * (τ x - x) ∈ M.1 := by
        have : a * (τ x - x) = (x + a * τ x) - x * (1 + a) := by ring
        rw [this]; exact M.1.sub_mem ht (M.1.mul_mem_left _ h1a)
      exact hunit (ha.mul hx) this
    · have ht1 : t M = 1 := by simp only [t, if_pos hfix, if_neg h1a]
      rw [ht1, map_one, mul_one, add_comm] at ht
      exact h1a (by rwa [add_comm])
  · have hfix' : pt (pt M) ≠ pt M := by rw [pt_pt]; exact Ne.symm hfix
    by_cases hlt : e M < e (pt M)
    · have ht1 : t M = 1 := by simp only [t, if_neg hfix, if_pos hlt]
      have hlt' : ¬ e (pt M) < e (pt (pt M)) := by rw [pt_pt]; exact not_lt.2 hlt.le
      have ht0 : t (pt M) = 0 := by simp only [t, if_neg hfix', if_neg hlt']
      have h1 := hy M
      have h2 := hy (pt M)
      rw [ht1] at h1
      rw [ht0, sub_zero, mem_pt] at h2
      have : (1 : R) = (y + a * τ y) - (y - 1) - a * τ y := by ring
      exact hne1 (this ▸ M.1.sub_mem (M.1.sub_mem hyM' h1) (M.1.mul_mem_left _ h2))
    · have ht0 : t M = 0 := by simp only [t, if_neg hfix, if_neg hlt]
      have hne : e (pt M) ≠ e M := fun h => hfix (e.injective h)
      have hlt' : e (pt M) < e (pt (pt M)) := by
        rw [pt_pt]; exact lt_of_le_of_ne (not_lt.1 hlt) hne
      have ht1 : t (pt M) = 1 := by simp only [t, if_neg hfix', if_pos hlt']
      have h1 := hy M
      have h2 := hy (pt M)
      rw [ht0, sub_zero] at h1
      rw [ht1, mem_pt, map_sub, map_one] at h2
      have : a = (y + a * τ y) - y - a * (τ y - 1) := by ring
      exact hunit ha (this ▸ M.1.sub_mem (M.1.sub_mem hyM' h1) (M.1.mul_mem_left _ h2))

def cO (K : UQ) : K.O →+* K.O where
  toFun x := Classical.choose (K.c_int x)
  map_one' := by
    apply IsFractionRing.injective K.O K.E
    rw [← Classical.choose_spec (K.c_int 1)]; simp
  map_mul' x y := by
    apply IsFractionRing.injective K.O K.E
    rw [← Classical.choose_spec (K.c_int (x * y)), map_mul, map_mul, map_mul,
      ← Classical.choose_spec (K.c_int x), ← Classical.choose_spec (K.c_int y)]
  map_zero' := by
    apply IsFractionRing.injective K.O K.E
    rw [← Classical.choose_spec (K.c_int 0)]; simp
  map_add' x y := by
    apply IsFractionRing.injective K.O K.E
    rw [← Classical.choose_spec (K.c_int (x + y)), map_add, map_add, map_add,
      ← Classical.choose_spec (K.c_int x), ← Classical.choose_spec (K.c_int y)]

theorem algebraMap_cO (K : UQ) (x : K.O) : algebraMap K.O K.E (cO K x) = K.c (algebraMap K.O K.E x) :=
  (Classical.choose_spec (K.c_int x)).symm

theorem σ_algebraMap_O {K : UQ} (B : InvAlg K) (x : K.O) :
    B.σ (algebraMap K.O B.A x) = algebraMap K.O B.A (cO K x) := by
  rw [IsScalarTower.algebraMap_apply K.O K.E B.A, B.σ_alg, ← algebraMap_cO,
    ← IsScalarTower.algebraMap_apply]

theorem isIntegral_σ {K : UQ} (B : InvAlg K) {y : B.A} (hy : IsIntegral K.O y) : IsIntegral K.O (B.σ y) := by
  obtain ⟨p, hp, hpy⟩ := hy
  refine ⟨p.map (cO K), hp.map _, ?_⟩
  have hc : (B.σ : B.A →+* B.A).comp (algebraMap K.O B.A) = (algebraMap K.O B.A).comp (cO K) := by
    ext x; exact σ_algebraMap_O B x
  have := congrArg (B.σ : B.A →+* B.A) hpy
  rw [map_zero, Polynomial.hom_eval₂, hc] at this
  rw [Polynomial.eval₂_map]; exact this

theorem σ_mem_adjoin {K : UQ} (B : InvAlg K) (hg : B.g * B.σ B.g = 1) (hint : IsIntegral K.O B.g)
    {y : B.A} (hy : y ∈ Algebra.adjoin K.O {B.g}) : B.σ y ∈ Algebra.adjoin K.O {B.g} := by
  induction hy using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx; subst hx
    exact mem_adjoin_of_mul_eq_one' hg (isIntegral_σ B hint)
  | algebraMap r => rw [σ_algebraMap_O]; exact Subalgebra.algebraMap_mem _ _
  | add x z _ _ hx hz => rw [map_add]; exact Subalgebra.add_mem _ hx hz
  | mul x z _ _ hx hz => rw [map_mul]; exact Subalgebra.mul_mem _ hx hz

theorem maximal_finite {K : UQ} (B : InvAlg K) (hint : IsIntegral K.O B.g) :
    {M : Ideal (Algebra.adjoin K.O {B.g}) | M.IsMaximal}.Finite := by
  haveI : Module.Finite K.O (Algebra.adjoin K.O {B.g}) := Module.Finite.iff_fg.mpr hint.fg_adjoin_singleton
  refine (Algebra.QuasiFinite.finite_primesOver (IsLocalRing.maximalIdeal K.O)).subset ?_
  intro M hM
  have hM' : M.IsMaximal := hM
  have hc : (M.comap (algebraMap K.O (Algebra.adjoin K.O {B.g}))).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M
  exact ⟨hM'.isPrime, ⟨(IsLocalRing.eq_maximalIdeal hc).symm⟩⟩

theorem exists_unit_base : ∀ (K : UQ) (B : InvAlg K), B.g * B.σ B.g = 1 → B.P.Separable → IsIntegral K.O B.g →
    ∀ (ε : B.A), (ε = 1 ∨ ε = -1) → ∃ β₀ : B.Aˣ, B.σ (β₀ : B.A) = β₀ * (ε * B.g) ∧
      (β₀ : B.A) ∈ Algebra.adjoin K.O {B.g} ∧ ((β₀⁻¹ : B.Aˣ) : B.A) ∈ Algebra.adjoin K.O {B.g} := by
  intro K B hg _ hint ε hε
  set R := Algebra.adjoin K.O {B.g} with hR
  have hσR : ∀ y : R, B.σ (y : B.A) ∈ R := fun y => σ_mem_adjoin B hg hint y.2
  let τ : R ≃+* R :=
    { toFun := fun y => ⟨B.σ (y : B.A), hσR y⟩
      invFun := fun y => ⟨B.σ (y : B.A), hσR y⟩
      left_inv := fun y => Subtype.ext (B.σ_σ (y : B.A))
      right_inv := fun y => Subtype.ext (B.σ_σ (y : B.A))
      map_mul' := fun x y => Subtype.ext (map_mul B.σ (x : B.A) (y : B.A))
      map_add' := fun x y => Subtype.ext (map_add B.σ (x : B.A) (y : B.A)) }
  have hτc : ∀ y : R, ((τ y : R) : B.A) = B.σ y := fun y => rfl
  have hτ : ∀ y, τ (τ y) = y := fun y => Subtype.ext (B.σ_σ (y : B.A))

  obtain ⟨ε', hε'c, hε'u, hεε, hσε⟩ : ∃ ε' : R, (ε' : B.A) = ε ∧ IsUnit ε' ∧ ε * ε = 1 ∧ B.σ ε = ε := by
    rcases hε with rfl | rfl
    · exact ⟨1, by simp, isUnit_one, by simp, by simp⟩
    · exact ⟨-1, by simp, isUnit_one.neg, by simp, by simp⟩

  let g' : R := ⟨B.g, Algebra.self_mem_adjoin_singleton K.O B.g⟩
  let h' : R := τ g'
  have hgh : g' * h' = 1 := Subtype.ext hg
  have hh'u : IsUnit h' := ⟨⟨h', g', by rw [mul_comm]; exact hgh, hgh⟩, rfl⟩

  obtain ⟨x0, y0, hxy, hxy0⟩ := K.c_res
  have hcx : cO K x0 = y0 := IsFractionRing.injective K.O K.E (by rw [algebraMap_cO, hxy])
  have hx : IsUnit (τ (algebraMap K.O R x0) - algebraMap K.O R x0) := by
    have hu : IsUnit (y0 - x0) := by
      have : IsUnit (x0 - y0) := by
        by_contra hn; exact hxy0 ((IsLocalRing.mem_maximalIdeal _).2 hn)
      simpa [neg_sub] using this.neg
    have : τ (algebraMap K.O R x0) - algebraMap K.O R x0 = algebraMap K.O R (y0 - x0) := by
      apply Subtype.ext
      simp only [hτc, Subalgebra.coe_sub, Subalgebra.coe_algebraMap, σ_algebraMap_O, hcx, map_sub]
    rw [this]; exact hu.map _
  obtain ⟨y, hy⟩ := exists_isUnit_add_mul_twist τ hτ (ε' * h') (hε'u.mul hh'u) (maximal_finite B hint) _ hx
  refine ⟨Units.map (R.val : R →* B.A) hy.unit, ?_, ?_, ?_⟩
  · have hc : ((Units.map (R.val : R →* B.A) hy.unit : B.Aˣ) : B.A) = (y : B.A) + ε * B.σ B.g * B.σ y := by
      simp [Units.coe_map, IsUnit.unit_spec, hε'c, hτc, h', g', mul_assoc]
    rw [hc, map_add, map_mul, map_mul, hσε, B.σ_σ, B.σ_σ]
    linear_combination (-(B.σ (y : B.A)) * ε * ε) * hg - B.σ (y : B.A) * hεε
  · simp only [Units.coe_map]; exact (hy.unit : R).2
  · rw [← map_inv]; simp only [Units.coe_map]; exact ((hy.unit⁻¹ : Rˣ) : R).2

end GlobalTheory.UnitLemma.UnitBase
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWindowRadii
section
namespace GlobalTheory.PMonE

open Finset in

theorem _root_.GlobalTheory.PMonE.exists_window_radii : ∀ (F : Type) [NontriviallyNormedField F]
    [IsUltrametricDist F] [IsAlgClosed F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]
    (k : ℕ) (ϖ : F), ‖ϖ‖ = (p : ℝ)⁻¹ → ∀ lam : Fin (k + 1) → F, (∀ j, lam j ≠ 0) →
    Antitone (fun j => ‖lam j‖) → (∀ i j, ‖lam i‖ < p * ‖lam j‖) →
    ∃ π : Fin (k + 1) → F, (∀ j, π j ≠ 0 ∧ ‖π j‖ < 1) ∧
      (∀ j : Fin k, ‖lam j.succ‖ * ‖π j.succ‖ ^ p ^ (j : ℕ) =
        ‖lam j.castSucc‖ * ‖π j.castSucc‖ ^ p ^ (j : ℕ)) ∧
      (‖lam 0‖ / p) ^ p * ‖π 0‖ = (‖lam (Fin.last k)‖ * ‖π (Fin.last k)‖ ^ p ^ k) ^ p := by
  intro F _ _ _ p _ _ _ k ϖ hϖ lam hlam hanti hclose
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hpR : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hl : ∀ j, 0 < ‖lam j‖ := fun j => norm_pos_iff.mpr (hlam j)
  have hρ : ∀ j : Fin k, ∃ y : F, y ^ p ^ (j : ℕ) = lam j.castSucc / lam j.succ :=
    fun j => IsAlgClosed.exists_pow_nat_eq _ (pow_pos (by omega) _)
  choose ρ hρ using hρ
  have hρn : ∀ j : Fin k, ‖ρ j‖ ^ p ^ (j : ℕ) = ‖lam j.castSucc‖ / ‖lam j.succ‖ := fun j => by
    rw [← norm_pow, hρ, norm_div]
  have hρ1 : ∀ j : Fin k, 1 ≤ ‖ρ j‖ := fun j => by
    rw [← one_le_pow_iff_of_nonneg (norm_nonneg _) (pow_pos (by omega : 0 < p) (j : ℕ)).ne', hρn,
      one_le_div (hl _)]
    exact hanti (Fin.castSucc_le_succ j)
  set ρ' : ℕ → F := fun n => if h : n < k then ρ ⟨n, h⟩ else 1 with hρ'
  have hρ'1 : ∀ n, 1 ≤ ‖ρ' n‖ := fun n => by
    simp only [hρ']; split_ifs with h
    · exact hρ1 _
    · simp
  have hρ'ne : ∀ n, ρ' n ≠ 0 := fun n h0 => by
    have := hρ'1 n; rw [h0, norm_zero] at this; linarith
  set P : ℕ → F := fun j => ∏ n ∈ range j, ρ' n with hP
  have hPne : ∀ j, P j ≠ 0 := fun j => prod_ne_zero_iff.mpr fun n _ => hρ'ne n
  have hPsucc : ∀ j, P (j + 1) = P j * ρ' j := fun j => prod_range_succ _ _
  have hPmono : Monotone fun j => ‖P j‖ := by
    refine monotone_nat_of_le_succ fun j => ?_
    simp only [hPsucc, norm_mul]
    exact le_mul_of_one_le_right (norm_nonneg _) (hρ'1 j)
  have hP0 : P 0 = 1 := by simp [hP]
  have hc1 : 1 ≤ ‖P k‖ := by
    have := hPmono (Nat.zero_le k); simpa [hP0] using this
  set c := ‖P k‖ with hc
  have hcpos : 0 < c := by linarith
  set N := p ^ (k + 1) - 1 with hN
  have hpk : 2 ≤ p ^ (k + 1) := le_trans (by omega) (Nat.le_self_pow (by omega) p)
  have hNpos : 0 < N := by omega
  have hN1 : p ^ (k + 1) = N + 1 := by omega
  set w : F := (lam 0 * ϖ) ^ p / ((lam (Fin.last k)) ^ p * P k ^ p ^ (k + 1)) with hw
  have hwn : ‖w‖ = (‖lam 0‖ / p) ^ p / (‖lam (Fin.last k)‖ ^ p * c ^ (N + 1)) := by
    rw [hw]
    simp only [norm_div, norm_mul, norm_pow, hϖ, ← hN1]
    ring
  have hwne : w ≠ 0 := by
    rw [hw]
    exact div_ne_zero (pow_ne_zero _ (mul_ne_zero (hlam 0) (by
      intro h0; rw [h0, norm_zero] at hϖ; exact (inv_pos.mpr hpR).ne' hϖ.symm)))
      (mul_ne_zero (pow_ne_zero _ (hlam _)) (pow_ne_zero _ (hPne k)))
  obtain ⟨π0, hπ0⟩ := IsAlgClosed.exists_pow_nat_eq w hNpos
  have hπ0ne : π0 ≠ 0 := by
    intro h0; rw [h0, zero_pow hNpos.ne'] at hπ0; exact hwne hπ0.symm
  set s := ‖π0‖ with hs
  have hspos : 0 < s := norm_pos_iff.mpr hπ0ne
  have hsN : s ^ N = ‖w‖ := by rw [hs, ← norm_pow, hπ0]
  have hl0 : ‖lam 0‖ / p < ‖lam (Fin.last k)‖ := by
    rw [div_lt_iff₀ hpR, mul_comm]; exact hclose 0 (Fin.last k)
  have hsc : s * c < 1 := by
    have key : (s * c) ^ N < 1 := by
      have hwc : ‖w‖ * c ^ N = (‖lam 0‖ / p) ^ p / (‖lam (Fin.last k)‖ ^ p * c) := by
        rw [hwn, pow_succ]
        field_simp
      rw [mul_pow, hsN, hwc, div_lt_one (by have := hl (Fin.last k); positivity)]
      calc (‖lam 0‖ / p) ^ p < ‖lam (Fin.last k)‖ ^ p :=
            pow_lt_pow_left₀ hl0 (by positivity) (by omega)
        _ ≤ ‖lam (Fin.last k)‖ ^ p * c :=
            le_mul_of_one_le_right (by have := hl (Fin.last k); positivity) hc1
    exact (pow_lt_one_iff_of_nonneg (by positivity) hNpos.ne').mp key
  refine ⟨fun j => π0 * P j, fun j => ⟨mul_ne_zero hπ0ne (hPne _), ?_⟩, fun j => ?_, ?_⟩
  · rw [norm_mul, ← hs]
    calc s * ‖P j‖ ≤ s * c := mul_le_mul_of_nonneg_left (hPmono (Nat.lt_succ_iff.mp j.isLt)) hspos.le
      _ < 1 := hsc
  · simp only [Fin.val_succ, Fin.coe_castSucc, hPsucc, norm_mul, mul_pow]
    have : ρ' j = ρ j := by simp [hρ', j.isLt]
    rw [this, hρn]
    have := hl j.succ
    field_simp
  · simp only [Fin.val_zero, Fin.val_last, hP0, mul_one, norm_mul, ← hs, ← hc, mul_pow, ← pow_mul]
    rw [← pow_succ, hN1, pow_succ s N, hsN, hwn]
    have := hl (Fin.last k)
    field_simp

end GlobalTheory.PMonE
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWittVectorGhostEqFrobeniusIterateStatement
section
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_wittVector_ghost_eq_frobenius_iterate : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (φ : A →+* A), (∀ a, ((l : ℕ) : A) ∣ φ a - a ^ l) → ∀ a : A, ∃ w : WittVector l A, ∀ n, WittVector.ghostComponent n w = φ^[n] a := by
  first | exact @GlobalTheory.DworkGhost.exists_witt_ghost_iterate | exact GlobalTheory.DworkGhost.exists_witt_ghost_iterate | (intros; apply GlobalTheory.DworkGhost.exists_witt_ghost_iterate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExpIntegralEntireRealPosStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exp_integral_differentiable_real_re_pos : ∀ {X : Type} [MeasurableSpace X] (ν : Measure X) (f t : X → ℝ), Measurable f → Measurable t → (∀ y, 0 ≤ f y) →
    Integrable f ν → (∃ R : ℝ, ∀ y, f y ≠ 0 → |t y| ≤ R) →
    Differentiable ℂ (fun s : ℂ => ∫ y, (f y : ℂ) * Complex.exp (s * t y) ∂ν) ∧
    ∀ r : ℝ, (∫ y, (f y : ℂ) * Complex.exp (r * t y) ∂ν).im = 0 ∧
      (0 < ∫ y, f y ∂ν → 0 < (∫ y, (f y : ℂ) * Complex.exp (r * t y) ∂ν).re) := by
  first | exact @GlobalTheory.exp_integral_entire_real_pos | exact GlobalTheory.exp_integral_entire_real_pos | (intros; apply GlobalTheory.exp_integral_entire_real_pos <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FgInfSupOfIsComplStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fg_inf_sup_of_isCompl' : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (A : Submodule (𝓞 K) V) (U U' : Submodule K V), A.FG → IsCompl U U' → (U.restrictScalars (𝓞 K) ⊓ (A ⊔ U'.restrictScalars (𝓞 K))).FG := by
  first | exact @GlobalTheory.fg_inf_sup_of_isCompl | exact GlobalTheory.fg_inf_sup_of_isCompl | (intros; apply GlobalTheory.fg_inf_sup_of_isCompl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteClassesModUniformizerPowMatricesStatement
section
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_classes_mod_uniformizer_pow_matrices : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r t : ℕ) (ϖ : O), Irreducible ϖ → ∀ N : ℕ, ∃ T : Finset (Matrix (Fin r ⊕ Fin t) (Fin r) K), ∀ (x : Matrix (Fin r ⊕ Fin t) (Fin r) K) (z : Matrix (Fin r ⊕ Fin t) (Fin r) O), algebraMap O K (ϖ ^ N) • x = z.map (algebraMap O K) → ∃ y ∈ T, ∃ z' : Matrix (Fin r ⊕ Fin t) (Fin r) O, x = y + (ϖ ^ N • z').map (algebraMap O K) := by
  first | exact @GlobalTheory.GenUnr.finite_classes_mod_pow | exact GlobalTheory.GenUnr.finite_classes_mod_pow | (intros; apply GlobalTheory.GenUnr.finite_classes_mod_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteFieldExistsGeneratorMinpolyStatement
section
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_separable_generator_card_eq_pow_natDegree : ∀ (l : ℕ) [Fact l.Prime] (K : Type) [Field K] [Finite K] [Algebra (ZMod l) K], ∃ (a : K) (p : (ZMod l)[X]), p.Monic ∧ Irreducible p ∧ aeval a p = 0 ∧ aeval a (derivative p) ≠ 0 ∧ (∀ y : K, ∃ q : (ZMod l)[X], aeval a q = y) ∧ Nat.card K = l ^ p.natDegree := by
  first | exact @GlobalTheory.finiteField_exists_generator_minpoly | exact GlobalTheory.finiteField_exists_generator_minpoly | (intros; apply GlobalTheory.finiteField_exists_generator_minpoly <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteFreeModuleCompactAdicDvrStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_free_module_compact_adic_dvr : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O], IsAdic (IsLocalRing.maximalIdeal O) → ∀ {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul O M] [T2Space M] [Module.Free O M] [Module.Finite O M] (ϖ : O), Irreducible ϖ → CompactSpace M ∧ IsOpen (LinearMap.range (LinearMap.lsmul O M ϖ) : Set M) ∧ Topology.IsClosedEmbedding (fun m : M => ϖ • m) := by
  first | exact @GlobalTheory.finite_free_compact_adic_dvr | exact GlobalTheory.finite_free_compact_adic_dvr | (intros; apply GlobalTheory.finite_free_compact_adic_dvr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteOfPerfectPairingZmodStatement
section
open Function
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_of_bijective_pairing_zmod : ∀ (n : ℕ) [NeZero n] (A B C : Type) [AddCommGroup A] [Module (ZMod n) A] [AddCommGroup B] [Module (ZMod n) B] [AddCommGroup C] [Module (ZMod n) C] [Finite C] (b : A →ₗ[ZMod n] B →ₗ[ZMod n] C), Nonempty (C ≃ₗ[ZMod n] ZMod n) → Bijective b → Bijective b.flip → Finite A ∧ Finite B := by
  first | exact @GlobalTheory.finite_of_perfect_pairing_zmod | exact GlobalTheory.finite_of_perfect_pairing_zmod | (intros; apply GlobalTheory.finite_of_perfect_pairing_zmod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteQuotientOfCompleteNakayamaStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.module_finite_quotient_of_complete_of_span_mod_range : ∀ {R : Type} [CommRing R] (ϖ : R), (∀ x : ℕ → R, ∃ a : R, ∀ n : ℕ, ∃ b : R, a - ∑ j ∈ Finset.range n, ϖ ^ j * x j = ϖ ^ n * b) → ∀ {T Z : Type} [AddCommGroup T] [Module R T] [AddCommGroup Z] [Module R Z], (∀ x : ℕ → T, ∃ y : T, ∀ n : ℕ, ∃ z : T, y - ∑ j ∈ Finset.range n, ϖ ^ j • x j = ϖ ^ n • z) → (∀ c : Z, (∀ n : ℕ, ∃ z : Z, c = ϖ ^ n • z) → c = 0) → ∀ (d : T →ₗ[R] Z) (N : Submodule R Z), LinearMap.range d ≤ N → ∀ s : Finset Z, (∀ c : Z, ∃ (a : Z → R) (c' : Z) (x : T), c = ∑ i ∈ s, a i • i + ϖ • c' + d x) → Module.Finite R (Z ⧸ N) := by
  first | exact @GlobalTheory.finite_quotient_of_complete_nakayama | exact GlobalTheory.finite_quotient_of_complete_nakayama | (intros; apply GlobalTheory.finite_quotient_of_complete_nakayama <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteSqEqOneOfFiniteAlgebraStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_setOf_sq_eq_one_of_finite_charZero : ∀ (k : Type) [Field k] [CharZero k] (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A], Set.Finite {x : A | x ^ 2 = 1} := by
  first | exact @GlobalTheory.finite_sq_eq_one_of_finite_algebra | exact GlobalTheory.finite_sq_eq_one_of_finite_algebra | (intros; apply GlobalTheory.finite_sq_eq_one_of_finite_algebra <;> assumption)
end

