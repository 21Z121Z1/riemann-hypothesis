import Formalism.CyclotomicNorms.Bundle0001

-- bundled from Formalism.CyclotomicNorms.NonsquarefreeBounds.Central
section
open Finset

noncomputable section

namespace Formalism.CyclotomicNorms

namespace CentralScalarSequence

variable {G : Type} [Group G]

def insN (i : ℕ) (a : G) (y : ℕ → G) : ℕ → G :=
  fun k => if k < i then y k else if k = i then a else y (k - 1)

def contrN (j : ℕ) (y : ℕ → G) : ℕ → G :=
  fun k => if k < j then y k else if k = j then y k * y (k + 1) else y (k + 1)

def extN {m : ℕ} (x : Fin m → G) : ℕ → G := fun k => if h : k < m then x ⟨k, h⟩ else 1

lemma extN_agree {m : ℕ} (x : Fin m → G) : ∀ k : Fin m, x k = extN x k := by
  intro k; simp [extN, k.isLt]

lemma ins_agree {m : ℕ} (i : Fin (m + 1)) (a : G) (x : Fin m → G) (y : ℕ → G)
    (hx : ∀ k : Fin m, x k = y k) :
    ∀ k : Fin (m + 1), Fin.insertNth (α := fun _ => G) i a x k = insN i a y k := by
  intro k
  rcases lt_trichotomy k i with h | h | h
  · rw [Fin.insertNth_apply_below h, eq_rec_constant, hx]
    have h' : (k : ℕ) < i := h
    simp [insN, h']
  · subst h; simp [insN]
  · rw [Fin.insertNth_apply_above h, eq_rec_constant, hx]
    have h' : (i : ℕ) < k := h
    simp [insN, not_lt.mpr h'.le, h'.ne']

lemma contr_agree {m : ℕ} (j : Fin (m + 1)) (x : Fin (m + 1) → G) (y : ℕ → G)
    (hx : ∀ k : Fin (m + 1), x k = y k) :
    ∀ k : Fin m, Fin.contractNth j (· * ·) x k = contrN j y k := by
  intro k
  simp only [Fin.contractNth, contrN, hx, Fin.val_castSucc, Fin.val_succ]

section seq

variable (a : G) (y : ℕ → G)

lemma seq_a (M j : ℕ) (h : j < M) : contrN j (insN (M + 1) a y) = insN M a (contrN j y) := by
  funext k
  simp only [insN, contrN]
  split_ifs <;> first | rfl | omega | (congr <;> omega)

lemma seq_b (hz : ∀ g, a * g = g * a) (M : ℕ) :
    contrN M (insN (M + 1) a y) = contrN M (insN M a y) := by
  funext k
  simp only [insN, contrN]
  split_ifs <;> first | rfl | omega | (congr <;> omega) | (subst_vars; exact (hz _).symm)

lemma seq_c (M i : ℕ) (h : i ≤ M) : contrN (M + 1) (insN i a y) = insN i a (contrN M y) := by
  funext k
  simp only [insN, contrN]
  split_ifs <;> first | rfl | omega | (congr <;> omega)

lemma seq_d (i : ℕ) : insN (i + 1) a y 0 = y 0 := by simp [insN]

lemma seq_e (i : ℕ) : (fun k => insN (i + 1) a y (k + 1)) = insN i a (fun k => y (k + 1)) := by
  funext k
  simp only [insN]
  split_ifs <;> first | rfl | omega | (congr <;> omega)

lemma seq_f : insN 0 a y 0 = a := by simp [insN]

lemma seq_g : (fun k => insN 0 a y (k + 1)) = y := by
  funext k; simp [insN]

lemma seq_h (n k : ℕ) (hk : k < n + 1) : contrN (n + 1) (insN (n + 1) a y) k = y k := by
  simp [insN, contrN, hk]

end seq

lemma abstract {W : Type} [AddCommGroup W] (T S : ℕ → ℕ → W)
    (h1 : ∀ M j, j < M → T (M + 1) j = - S M j) (h2 : ∀ M, T (M + 1) M = - T M M)
    (h3 : ∀ M i, i ≤ M → T i (M + 1) = - S i M) (N : ℕ) :
    (∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1), T i j) +
      (∑ i ∈ range N, ∑ j ∈ range N, S i j) = T N N := by
  induction N with
  | zero => simp
  | succ N ih =>
    have eT : ∑ i ∈ range (N + 1 + 1), ∑ j ∈ range (N + 1 + 1), T i j =
        (∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1), T i j) + (∑ i ∈ range (N + 1), T i (N + 1))
        + ((∑ j ∈ range N, T (N + 1) j) + T (N + 1) N) + T (N + 1) (N + 1) := by
      rw [sum_range_succ _ (N + 1)]
      simp only [sum_range_succ _ (N + 1), sum_add_distrib]
      rw [← sum_range_succ (fun j => T (N + 1) j) N]
      abel
    have eS : ∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1), S i j =
        (∑ i ∈ range N, ∑ j ∈ range N, S i j) + (∑ i ∈ range N, S i N) +
        (∑ j ∈ range N, S N j) + S N N := by
      rw [sum_range_succ _ N]
      simp only [sum_range_succ _ N, sum_add_distrib]
      abel
    have e1 : ∑ j ∈ range N, T (N + 1) j = - ∑ j ∈ range N, S N j := by
      rw [← sum_neg_distrib]; exact sum_congr rfl fun j hj => h1 N j (mem_range.mp hj)
    have e2 : ∑ i ∈ range (N + 1), T i (N + 1) = - ((∑ i ∈ range N, S i N) + S N N) := by
      rw [← sum_range_succ (fun i => S i N) N, ← sum_neg_distrib]
      exact sum_congr rfl fun i hi => h3 N i (Nat.lt_succ_iff.mp (mem_range.mp hi))
    rw [eT, eS, e1, e2, h2 N]
    have ih' := eq_sub_of_add_eq ih
    rw [ih']
    abel

variable {R W : Type} [CommRing R] [AddCommGroup W] [Module R W]

lemma sgn_succ (k : ℕ) : (-1 : R) ^ (k + 1) = - (-1 : R) ^ k := by
  rw [pow_succ, mul_neg_one]

lemma sgn_diag (i : ℕ) : (-1 : R) ^ (i + (i + 1)) = -1 := by
  rw [show i + (i + 1) = 2 * i + 1 by ring, pow_succ, pow_mul]; simp

lemma nat_identity (ρ : Representation R G W) (z : G) (hz : ∀ g, z * g = g * z) (n : ℕ)
    (φ : (ℕ → G) → W) (hφ : ∀ u v : ℕ → G, (∀ k < n + 1, u k = v k) → φ u = φ v) (y : ℕ → G)
    (hcoc : ∀ i < n + 2, ρ (insN i z y 0) (φ (fun k => insN i z y (k + 1))) +
      ∑ j ∈ range (n + 2), (-1 : R) ^ (j + 1) • φ (contrN j (insN i z y)) = 0) :
    ρ (y 0) (∑ i ∈ range (n + 1), (-1 : R) ^ i • φ (insN i z (fun k => y (k + 1)))) +
      ∑ j ∈ range (n + 1), (-1 : R) ^ (j + 1) •
        ∑ i ∈ range (n + 1), (-1 : R) ^ i • φ (insN i z (contrN j y))
      = ρ z (φ y) - φ y := by
  have h0 : (∑ i ∈ range (n + 2), (-1 : R) ^ i • ρ (insN i z y 0) (φ (fun k => insN i z y (k + 1))))
      + ∑ i ∈ range (n + 2), ∑ j ∈ range (n + 2),
          (-1 : R) ^ (i + (j + 1)) • φ (contrN j (insN i z y)) = 0 := by
    rw [← sum_add_distrib]
    refine sum_eq_zero fun i hi => ?_
    have := congrArg (fun w => (-1 : R) ^ i • w) (hcoc i (mem_range.mp hi))
    simp only [smul_add, smul_sum, smul_smul, ← pow_add, smul_zero] at this
    exact this
  have hA : ∑ i ∈ range (n + 2), (-1 : R) ^ i • ρ (insN i z y 0) (φ (fun k => insN i z y (k + 1)))
      = ρ z (φ y) - ρ (y 0) (∑ i ∈ range (n + 1), (-1 : R) ^ i • φ (insN i z (fun k => y (k + 1)))) := by
    rw [sum_range_succ']
    simp only [seq_d, seq_e, seq_f, seq_g, pow_zero, one_smul, map_sum, map_smul, sgn_succ,
      neg_smul, sum_neg_distrib]
    abel
  have hK := abstract (fun i j => (-1 : R) ^ (i + (j + 1)) • φ (contrN j (insN i z y)))
      (fun i j => (-1 : R) ^ (i + (j + 1)) • φ (insN i z (contrN j y)))
      (fun M j h => by
        rw [seq_a z y M j h, show M + 1 + (j + 1) = M + (j + 1) + 1 by omega, sgn_succ, neg_smul])
      (fun M => by
        rw [seq_b z y hz M, show M + 1 + (M + 1) = M + (M + 1) + 1 by omega, sgn_succ, neg_smul])
      (fun M i h => by
        rw [seq_c z y M i h, show i + (M + 1 + 1) = i + (M + 1) + 1 by omega, sgn_succ, neg_smul])
      (n + 1)
  rw [sgn_diag, neg_one_smul, hφ _ y (seq_h z y n)] at hK
  have hB : ∑ j ∈ range (n + 1), (-1 : R) ^ (j + 1) •
        ∑ i ∈ range (n + 1), (-1 : R) ^ i • φ (insN i z (contrN j y)) =
      ∑ i ∈ range (n + 1), ∑ j ∈ range (n + 1), (-1 : R) ^ (i + (j + 1)) • φ (insN i z (contrN j y)) := by
    simp only [smul_sum, smul_smul, ← pow_add]
    rw [sum_comm]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    rw [show j + 1 + i = i + (j + 1) by omega]
  rw [hA, eq_sub_of_add_eq hK] at h0
  rw [hB]
  rw [← sub_eq_zero, ← neg_eq_zero, ← h0]
  abel

def prism (R : Type) [CommRing R] [Module R W] {n : ℕ} (z : G) (f : (Fin (n + 1) → G) → W)
    (x : Fin n → G) : W :=
  ∑ i : Fin (n + 1), (-1 : R) ^ (i : ℕ) • f (Fin.insertNth (α := fun _ => G) i z x)

lemma prism_eq {n : ℕ} (z : G) (f : (Fin (n + 1) → G) → W) (x : Fin n → G) (v : ℕ → G)
    (hx : ∀ k : Fin n, x k = v k) :
    prism R z f x = ∑ i ∈ range (n + 1), (-1 : R) ^ i • f (fun k => insN i z v k) := by
  unfold prism
  rw [← Fin.sum_univ_eq_sum_range (fun i => (-1 : R) ^ i • f (fun k => insN i z v k)) (n + 1)]
  refine sum_congr rfl fun i _ => ?_
  congr 2
  funext k
  exact ins_agree i z x v hx k

lemma prism_continuous [TopologicalSpace G] [TopologicalSpace W] [DiscreteTopology W] {n : ℕ}
    (z : G) (f : (Fin (n + 1) → G) → W) (hf : Continuous f) : Continuous (prism R z f) := by
  have hV : Continuous fun x : Fin n → G => fun i : Fin (n + 1) =>
      f (Fin.insertNth (α := fun _ => G) i z x) :=
    continuous_pi fun i => hf.comp (continuous_const.finInsertNth i continuous_id)
  exact (continuous_of_discreteTopology
    (f := fun v : Fin (n + 1) → W => ∑ i : Fin (n + 1), (-1 : R) ^ (i : ℕ) • v i)).comp hV

end CentralScalarSequence

open CentralScalarSequence in
theorem central_scalar_holds : CentralScalar := by
  intro G R W _ _ _ _ _ _ _ ρ z c hz hc hρz
  have hzc : ∀ g, z * g = g * z := fun g => (Subgroup.mem_center_iff.mp hz g).symm
  obtain ⟨u, hu⟩ := hc
  refine ⟨?_, ?_⟩
  · intro w hw
    have h1 : (c - 1) • w = 0 := by rw [sub_smul, one_smul, ← hρz, hw, sub_self]
    calc w = ((↑u⁻¹ : R) * ↑u) • w := by simp
      _ = (↑u⁻¹ : R) • ((c - 1) • w) := by rw [mul_smul, hu]
      _ = 0 := by rw [h1, smul_zero]
  · intro n f hf hcoc
    refine ⟨fun x => (↑u⁻¹ : R) • prism R z f x,
      (continuous_of_discreteTopology (f := fun w : W => (↑u⁻¹ : R) • w)).comp
        (prism_continuous z f hf), ?_⟩
    funext g
    have key : coboundary ρ n (prism R z f) g = (c - 1) • f g := by
      set y := extN g with hy
      have hg := extN_agree g
      rw [← hy] at hg
      simp only [coboundary]
      rw [prism_eq z f (fun i => g i.succ) (fun k => y (k + 1)) (fun k => by simp [hg])]
      have hsum : ∑ j : Fin (n + 1), (-1 : R) ^ ((j : ℕ) + 1) • prism R z f (Fin.contractNth j (· * ·) g)
          = ∑ j ∈ range (n + 1), (-1 : R) ^ (j + 1) •
            ∑ i ∈ range (n + 1), (-1 : R) ^ i • f (fun k => insN i z (contrN j y) k) := by
        rw [← Fin.sum_univ_eq_sum_range (fun j => (-1 : R) ^ (j + 1) •
          ∑ i ∈ range (n + 1), (-1 : R) ^ i • f (fun k => insN i z (contrN j y) k)) (n + 1)]
        refine sum_congr rfl fun j _ => ?_
        rw [prism_eq z f _ (contrN j y) (contr_agree j g y hg)]
      rw [hsum]
      rw [show f g = f (fun k => y k) from congrArg f (funext hg), sub_smul, one_smul, ← hρz,
        hg 0, Fin.val_zero]
      refine nat_identity ρ z hzc n (fun v => f (fun k => v k)) ?_ y ?_
      · intro u v huv
        exact congrArg f (funext fun k => huv k k.isLt)
      · intro i hi
        have := congrFun hcoc (fun k : Fin (n + 2) => insN i z y k)
        simp only [coboundary, Pi.zero_apply] at this
        have hsum : ∑ j : Fin (n + 2), (-1 : R) ^ ((j : ℕ) + 1) •
            f (Fin.contractNth j (· * ·) (fun k : Fin (n + 2) => insN i z y k)) =
            ∑ j ∈ range (n + 2), (-1 : R) ^ (j + 1) • f (fun k => contrN j (insN i z y) k) := by
          rw [← Fin.sum_univ_eq_sum_range (fun j => (-1 : R) ^ (j + 1) •
            f (fun k => contrN j (insN i z y) k)) (n + 2)]
          refine sum_congr rfl fun j _ => ?_
          rw [show Fin.contractNth j (· * ·) (fun k : Fin (n + 2) => insN i z y k) =
            fun k : Fin (n + 1) => contrN j (insN i z y) k from
              funext (contr_agree j _ _ fun _ => rfl)]
        rw [hsum] at this
        simpa using this
    have lin : coboundary ρ n (fun x => (↑u⁻¹ : R) • prism R z f x) g =
        (↑u⁻¹ : R) • coboundary ρ n (prism R z f) g := by
      simp only [coboundary, map_smul, smul_add, smul_sum]
      congr 1
      exact sum_congr rfl fun j _ => smul_comm _ _ _
    rw [lin, key, ← hu, smul_smul, Units.inv_mul, one_smul]

end Formalism.CyclotomicNorms
end
end

-- bundled from Formalism.CyclotomicNorms.NonsquarefreeBounds.Cycles
section
open Module

noncomputable section

namespace Formalism.CyclotomicNorms

namespace CycleChains

universe u

variable {k : Type*} [Field k]

def resR {G V : Type*} [Group G] [AddCommGroup V] [Module k V] (ρ : Representation k G V)
    (W : Submodule k V) (hW : ∀ g, ∀ x ∈ W, ρ g x ∈ W) (g : G) : W →ₗ[k] W :=
  (ρ g).restrict (hW g)

theorem chi_mul {G V : Type*} [Group G] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V) (N : ℕ) (I : Subgroup G) (χ : Fin N → G → k)
    (flag : Fin (N + 1) → Submodule k V)
    (hdim : ∀ i : Fin (N + 1), finrank k (flag i) = i)
    (hmono : ∀ i : Fin N, flag i.castSucc ≤ flag i.succ)
    (hstab : ∀ i, ∀ x ∈ flag i, ∀ y ∈ I, ρ y x ∈ flag i)
    (hchi : ∀ i : Fin N, ∀ x ∈ flag i.succ, ∀ y ∈ I, ρ y x - χ i y • x ∈ flag i.castSucc)
    (i : Fin N) : χ i 1 = 1 ∧ ∀ y ∈ I, ∀ z ∈ I, χ i (y * z) = χ i y * χ i z := by
  have hlt : flag i.castSucc < flag i.succ := by
    refine lt_of_le_of_ne (hmono i) fun h => ?_
    have := congrArg (fun S : Submodule k V => finrank k S) h
    simp only [hdim, Fin.val_castSucc, Fin.val_succ] at this
    omega
  obtain ⟨x, hx, hxn⟩ := SetLike.exists_of_lt hlt
  have hz : ∀ a : k, a • x ∈ flag i.castSucc → a = 0 := by
    intro a ha
    by_contra hne
    exact hxn ((Submodule.smul_mem_iff _ hne).mp ha)
  refine ⟨?_, ?_⟩
  · have h := hchi i x hx 1 I.one_mem
    simp only [map_one, Module.End.one_apply] at h
    have : (1 - χ i 1) • x ∈ flag i.castSucc := by rwa [sub_smul, one_smul]
    have := hz _ this
    rw [sub_eq_zero] at this
    exact this.symm
  · intro y hy z hz'
    have h1 := hchi i x hx (y * z) (I.mul_mem hy hz')
    have h2 := hchi i x hx y hy
    have h3 := hchi i x hx z hz'
    have h4 := hstab i.castSucc _ h3 y hy
    have key : (χ i (y * z) - χ i y * χ i z) • x =
        (ρ y (ρ z x - χ i z • x) + χ i z • (ρ y x - χ i y • x)) -
          (ρ (y * z) x - χ i (y * z) • x) := by
      rw [map_mul, Module.End.mul_apply, map_sub, map_smul]
      module
    have hm : (χ i (y * z) - χ i y * χ i z) • x ∈ flag i.castSucc := by
      rw [key]
      exact Submodule.sub_mem _ (Submodule.add_mem _ h4 (Submodule.smul_mem _ _ h2)) h1
    have := hz _ hm
    rwa [sub_eq_zero] at this

end CycleChains

end Formalism.CyclotomicNorms
end
end

-- bundled from Formalism.CyclotomicNorms.NonsquarefreeBounds.LowDegreePowerSeries
section
open PowerSeries

noncomputable section

namespace Formalism.CyclotomicNorms

theorem low_key {R : Type*} [CommRing R] (x p D' y : R) (U : Rˣ) (m n : ℕ)
    (hp : p ^ n = 0) (hD : (x ^ m * U + p * D') * y = 0) : x ^ (m * n) * y = 0 := by
  have hU : (U : R) * ↑U⁻¹ = 1 := U.mul_inv
  have h1 : x ^ m * y = (-(p * D' * ↑U⁻¹)) * y := by
    linear_combination (↑U⁻¹ : R) * hD - (x ^ m * y) * hU
  have h2 : ∀ k : ℕ, x ^ (m * k) * y = (-(p * D' * ↑U⁻¹)) ^ k * y := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc x ^ (m * (k + 1)) * y = x ^ (m * k) * (x ^ m * y) := by ring
        _ = (-(p * D' * ↑U⁻¹)) * (x ^ (m * k) * y) := by rw [h1]; ring
        _ = (-(p * D' * ↑U⁻¹)) ^ (k + 1) * y := by rw [ih]; ring
  rw [h2 n]
  have : (-(p * D' * ↑U⁻¹)) ^ n = (-(D' * ↑U⁻¹)) ^ n * p ^ n := by ring
  rw [this, hp]
  simp

theorem low_coeff_dvd {O : Type*} [CommRing O] (a : O) (M : ℕ) (f : PowerSeries O)
    (hf : f ∈ Ideal.span {PowerSeries.C a, (PowerSeries.X : PowerSeries O) ^ (M + 1)})
    (k : ℕ) (hk : k ≤ M) : a ∣ coeff k f := by
  obtain ⟨u, v, rfl⟩ := Ideal.mem_span_pair.mp hf
  rw [map_add, mul_comm u, coeff_C_mul, mul_comm v, coeff_X_pow_mul', if_neg (by omega), add_zero]
  exact dvd_mul_right a _

theorem low_divide {O : Type*} [CommRing O] (a : O) (f : PowerSeries O)
    (h : ∀ k, a ∣ coeff k f) : ∃ f', f = C a * f' := by
  refine ⟨mk fun k => (h k).choose, ?_⟩
  ext k
  rw [coeff_C_mul, coeff_mk]
  exact (h k).choose_spec

theorem low_degree_power_series : LowPowerSeries := by
  intro O _ _ _ ϖ n m₀ D g hϖ hord hg hmem
  set Db := PowerSeries.map (IsLocalRing.residue O) D with hDb
  have hne : Db ≠ 0 := by
    intro h
    rw [h, order_zero] at hord
    exact absurd hord (by simp)
  set m := Db.order.toNat with hm
  have hmm : m ≤ m₀ := by
    have := coe_toNat_order hne
    rw [← this] at hord
    exact_mod_cast hord
  set U : PowerSeries O := mk fun k => coeff (m + k) D with hU
  have hUunit : IsUnit U := by
    rw [isUnit_iff_constantCoeff, ← coeff_zero_eq_constantCoeff_apply, hU, coeff_mk, add_zero,
      ← IsLocalRing.residue_ne_zero_iff_isUnit]
    have := coeff_order hne
    rwa [hDb, coeff_map] at this
  have hdiv : ∀ k, ϖ ∣ coeff k (D - X ^ m * U) := by
    intro k
    rw [map_sub, coeff_X_pow_mul']
    split_ifs with hk
    · rw [hU, coeff_mk, Nat.add_sub_cancel' hk, sub_self]
      exact dvd_zero _
    · rw [sub_zero, ← Ideal.mem_span_singleton,
        ← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ,
        ← IsLocalRing.residue_eq_zero_iff, ← coeff_map]
      exact coeff_of_lt_order_toNat (φ := Db) k (by omega)
  obtain ⟨D', hD'⟩ := low_divide ϖ _ hdiv
  have hDeq : D = X ^ m * U + C ϖ * D' := by rw [← hD']; ring
  set I := Ideal.span {PowerSeries.C (ϖ ^ n), (PowerSeries.X : PowerSeries O) ^ (n * m₀ + 1)}
    with hI
  let q := Ideal.Quotient.mk I
  have hp : (q (C ϖ)) ^ n = 0 := by
    rw [← map_pow, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (Set.mem_insert _ _)
  have h0 : (q X ^ m * ↑((hUunit.map q).unit) + q (C ϖ) * q D') * q g = 0 := by
    have h := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    rw [hDeq] at h
    simpa [map_mul, map_add, map_pow] using h
  have h3 := low_key _ _ _ _ _ m n hp h0
  rw [← map_pow, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at h3
  have hmn : m * n ≤ n * m₀ := by
    rw [mul_comm]
    exact Nat.mul_le_mul_left n hmm
  have := low_coeff_dvd (ϖ ^ n) (n * m₀) _ h3 (m * n) hmn
  rw [coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, coeff_zero_eq_constantCoeff_apply] at this
  exact hg (Ideal.mem_span_singleton.mpr this)

end Formalism.CyclotomicNorms
end
end

-- bundled from Formalism.CyclotomicNorms.NonsquarefreeBounds.NonsquarefreeMonicBoundHolds
section
open Finset Polynomial

noncomputable section

namespace Formalism.CyclotomicNorms

namespace Sqf

variable {K : Type} [Field K]

lemma coeff_monicOf_lt {N : ℕ} (a : Fin N → K) (i : Fin N) :
    (monicOf a).coeff (i : ℕ) = a i := by
  unfold monicOf
  rw [coeff_add, coeff_X_pow, if_neg (Nat.ne_of_lt i.2), zero_add, finset_sum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single i (fun j _ hj => if_neg (fun h => hj (Fin.ext h).symm)) (by simp)]
  simp

lemma coeff_monicOf_ge {N : ℕ} (a : Fin N → K) (k : ℕ) (hk : N ≤ k) :
    (monicOf a).coeff k = if k = N then 1 else 0 := by
  unfold monicOf
  rw [coeff_add, coeff_X_pow, finset_sum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_eq_zero (fun j _ => if_neg (by have := j.2; omega)), add_zero]

lemma natDegree_monicOf {N : ℕ} (a : Fin N → K) : (monicOf a).natDegree = N := by
  unfold monicOf
  rw [natDegree_add_eq_left_of_degree_lt (by rw [degree_X_pow]; exact degree_sum_fin_lt a), natDegree_X_pow]

lemma monic_monicOf {N : ℕ} (a : Fin N → K) : (monicOf a).Monic := by
  unfold monicOf
  exact monic_X_pow_add (degree_sum_fin_lt a)

lemma monicOf_coeffs (p : K[X]) (hp : p.Monic) {m : ℕ} (hd : p.natDegree = m) :
    monicOf (fun i : Fin m => p.coeff i) = p := by
  ext n
  rcases lt_or_ge n m with h | h
  · exact coeff_monicOf_lt (fun i : Fin m => p.coeff i) ⟨n, h⟩
  · rw [coeff_monicOf_ge _ n h]
    split_ifs with hn
    · subst hn
      rw [← hd]
      exact hp.coeff_natDegree.symm
    · exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm

lemma decomp (f : K[X]) (hf : f.Monic) (h0 : f.coeff 0 ≠ 0) (hsq : ¬ Squarefree f) :
    ∃ P h : K[X], P.Monic ∧ h.Monic ∧ 1 ≤ P.natDegree ∧ P.coeff 0 ≠ 0 ∧ f = P * P * h := by
  unfold Squarefree at hsq
  push_neg at hsq
  obtain ⟨x, ⟨g, hg⟩, hx⟩ := hsq
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hf.ne_zero (by simpa using hg)
  have hc : x.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hx0
  have hP : (x * C x.leadingCoeff⁻¹).Monic := monic_mul_leadingCoeff_inv hx0
  have hu : C x.leadingCoeff⁻¹ * C x.leadingCoeff = (1 : K[X]) := by
    rw [← C_mul, inv_mul_cancel₀ hc, C_1]
  have key : f = (x * C x.leadingCoeff⁻¹) * (x * C x.leadingCoeff⁻¹) *
      (C x.leadingCoeff * C x.leadingCoeff * g) := by
    rw [hg]
    linear_combination (-(x * x * g * (C x.leadingCoeff⁻¹ * C x.leadingCoeff + 1))) * hu
  refine ⟨x * C x.leadingCoeff⁻¹, C x.leadingCoeff * C x.leadingCoeff * g, hP,
    Monic.of_mul_monic_left (hP.mul hP) (by rw [← key]; exact hf), ?_, ?_, key⟩
  · by_contra hlt
    push_neg at hlt
    have h1 : x * C x.leadingCoeff⁻¹ = 1 := (Monic.natDegree_eq_zero hP).mp (by omega)
    exact hx (isUnit_iff_exists_inv.mpr ⟨_, h1⟩)
  · intro hz
    apply h0
    rw [key, mul_coeff_zero, mul_coeff_zero, hz]
    simp

lemma geo (q : ℕ) (hq : 2 ≤ q) (N : ℕ) :
    ∀ k, k < N → (∑ d ∈ Icc 1 k, q ^ (N - d)) + 2 * q ^ (N - 1 - k) ≤ 2 * q ^ (N - 1) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have ih' := ih (by omega)
    rw [Finset.sum_Icc_succ_top (by omega)]
    have e1 : N - 1 - k = (N - 1 - (k + 1)) + 1 := by omega
    have e2 : N - (k + 1) = N - 1 - k := by omega
    rw [e2]
    rw [e1] at ih' ⊢
    rw [pow_succ] at ih' ⊢
    have hm := Nat.mul_le_mul_left (q ^ (N - 1 - (k + 1))) hq
    linarith

end Sqf

end Formalism.CyclotomicNorms
end
end

