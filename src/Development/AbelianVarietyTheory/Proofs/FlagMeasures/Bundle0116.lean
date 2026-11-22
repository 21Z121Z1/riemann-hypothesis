import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Formalism.HarderNarasimhan.ShiftInvariance

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LayerProdCountMulDensityLeTwo
section
open GlobalTheory.Count Finset

namespace GlobalTheory.Count

theorem layerProd_mul_layerProd (n f : ℕ) {a : ℕ} (j : Fin a → ℕ) (τ : Fin a → ℝ) (G H : ℝ → ℝ) :
    layerProd n f j τ G * layerProd n f j τ H = layerProd n f j τ (fun la => G la * H la) := by
  simp only [layerProd, mul_pow, Finset.prod_mul_distrib]
  ring

private theorem layerProd_const_eq_pow (n f : ℕ) {a : ℕ} (j : Fin a → ℕ) (τ : Fin a → ℝ) (c : ℝ) :
    layerProd n f j τ (fun _ => c) = c ^ (∑ i, ∑ k ∈ univ.filter (fun k => i < k),
      (2 * j i * j k * f + 2 * j i * j k * f) + ∑ i, (2 * j i * (n - 2 * ∑ l, j l) * f + j i ^ 2 * f)) := by
  simp only [layerProd, ← pow_add, Finset.prod_pow_eq_pow_sum]

private theorem layerProd_exponent_le_three_mul_sum_mul (n f : ℕ) {a : ℕ} (j : Fin a → ℕ) (hn : 2 * ∑ i, j i ≤ n) :
    ∑ i, ∑ k ∈ univ.filter (fun k => i < k), (2 * j i * j k * f + 2 * j i * j k * f) +
      ∑ i, (2 * j i * (n - 2 * ∑ l, j l) * f + j i ^ 2 * f) ≤ 3 * (∑ i, j i) * n * f := by
  obtain ⟨S, hS⟩ : ∃ S, S = ∑ i, j i := ⟨_, rfl⟩
  rw [← hS] at hn ⊢
  have h1 : ∑ i, ∑ k ∈ univ.filter (fun k => i < k), j i * j k ≤ S * S := by
    calc ∑ i, ∑ k ∈ univ.filter (fun k => i < k), j i * j k ≤ ∑ i, ∑ k, j i * j k :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ = S * S := by rw [hS, Finset.sum_mul_sum]
  have h2 : ∑ i, j i ^ 2 ≤ S * S := by
    calc ∑ i, j i ^ 2 ≤ ∑ i, j i * S := Finset.sum_le_sum fun i _ => by
          rw [sq, hS]
          exact Nat.mul_le_mul_left _ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
      _ = S * S := by rw [← Finset.sum_mul, hS]
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 * S + m := ⟨n - 2 * S, by omega⟩
  have hm : 2 * S + m - 2 * S = m := by omega
  have e1 : ∑ i, ∑ k ∈ univ.filter (fun k => i < k), (2 * j i * j k * f + 2 * j i * j k * f) =
      4 * f * ∑ i, ∑ k ∈ univ.filter (fun k => i < k), j i * j k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have e2 : ∑ i, (2 * j i * m * f + j i ^ 2 * f) = 2 * m * f * S + f * ∑ i, j i ^ 2 := by
    rw [hS, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hm, e1, e2]
  nlinarith [Nat.mul_le_mul_left f h1, Nat.mul_le_mul_left f h2, Nat.zero_le (S * m * f)]

theorem layerProd_le_exp (n f : ℕ) {a : ℕ} (j : Fin a → ℕ) (τ : Fin a → ℝ) (G : ℝ → ℝ) (x : ℝ)
    (hx : 0 ≤ x) (hn : 2 * ∑ i, j i ≤ n) (hτ : StrictMono τ) (h01 : ∀ i, 0 < τ i ∧ τ i < 1)
    (hG : ∀ la, 0 < la → la < 1 → 0 ≤ G la ∧ G la ≤ Real.exp x) :
    layerProd n f j τ G ≤ Real.exp (((3 * (∑ i, j i) * n * f : ℕ) : ℝ) * x) := by
  have hpos : ∀ i, 0 < τ i := fun i => (h01 i).1
  have hlt : ∀ i, τ i < 1 := fun i => (h01 i).2
  have hb : ∀ la, 0 < la → la < 1 → ∀ e : ℕ, 0 ≤ G la ^ e ∧ G la ^ e ≤ Real.exp x ^ e :=
    fun la h0 h1 e => ⟨pow_nonneg (hG la h0 h1).1 e, pow_le_pow_left₀ (hG la h0 h1).1 (hG la h0 h1).2 e⟩
  have hr : ∀ i k, i < k → 0 < τ i / τ k ∧ τ i / τ k < 1 :=
    fun i k hik => ⟨div_pos (hpos i) (hpos k), (div_lt_one (hpos k)).2 (hτ hik)⟩
  have hp : ∀ i k, 0 < τ i * τ k ∧ τ i * τ k < 1 := fun i k =>
    ⟨mul_pos (hpos i) (hpos k), by nlinarith [hpos i, hpos k, hlt i, hlt k]⟩
  have hs : ∀ i, 0 < τ i ^ 2 ∧ τ i ^ 2 < 1 := fun i => ⟨pow_pos (hpos i) 2, by nlinarith [hpos i, hlt i]⟩
  have hex : 0 ≤ Real.exp x := (Real.exp_pos x).le
  have key : layerProd n f j τ G ≤ layerProd n f j τ (fun _ => Real.exp x) := by
    simp only [layerProd]
    apply mul_le_mul
    · apply Finset.prod_le_prod
      · intro i _
        apply Finset.prod_nonneg
        intro k hk
        have hik := (Finset.mem_filter.1 hk).2
        exact mul_nonneg (hb _ (hr i k hik).1 (hr i k hik).2 _).1 (hb _ (hp i k).1 (hp i k).2 _).1
      · intro i _
        apply Finset.prod_le_prod
        · intro k hk
          have hik := (Finset.mem_filter.1 hk).2
          exact mul_nonneg (hb _ (hr i k hik).1 (hr i k hik).2 _).1 (hb _ (hp i k).1 (hp i k).2 _).1
        · intro k hk
          have hik := (Finset.mem_filter.1 hk).2
          exact mul_le_mul (hb _ (hr i k hik).1 (hr i k hik).2 _).2 (hb _ (hp i k).1 (hp i k).2 _).2
            (hb _ (hp i k).1 (hp i k).2 _).1 (pow_nonneg hex _)
    · apply Finset.prod_le_prod
      · intro i _
        exact mul_nonneg (hb _ (hpos i) (hlt i) _).1 (hb _ (hs i).1 (hs i).2 _).1
      · intro i _
        exact mul_le_mul (hb _ (hpos i) (hlt i) _).2 (hb _ (hs i).1 (hs i).2 _).2
          (hb _ (hs i).1 (hs i).2 _).1 (pow_nonneg hex _)
    · apply Finset.prod_nonneg
      intro i _
      exact mul_nonneg (hb _ (hpos i) (hlt i) _).1 (hb _ (hs i).1 (hs i).2 _).1
    · apply Finset.prod_nonneg
      intro i _
      apply Finset.prod_nonneg
      intro k _
      positivity
  refine key.trans ?_
  rw [layerProd_const_eq_pow, ← Real.exp_nat_mul]
  apply Real.exp_le_exp.2
  apply mul_le_mul_of_nonneg_right _ hx
  exact_mod_cast layerProd_exponent_le_three_mul_sum_mul n f j hn

private theorem mul_prod_mul_le_prod_of_le_one {a : ℕ} (X : ℝ) (u v : Fin a → ℝ) (hX0 : 0 ≤ X) (hX1 : X ≤ 1)
    (hu : ∀ i, 0 ≤ u i) (hv0 : ∀ i, 0 ≤ v i) (hv1 : ∀ i, v i ≤ 1) :
    X * ∏ i, u i * v i ≤ ∏ i, u i := by
  rw [Finset.prod_mul_distrib]
  have hA : 0 ≤ ∏ i, u i := Finset.prod_nonneg fun i _ => hu i
  have hB0 : 0 ≤ ∏ i, v i := Finset.prod_nonneg fun i _ => hv0 i
  have hB1 : ∏ i, v i ≤ 1 := Finset.prod_le_one (fun i _ => hv0 i) (fun i _ => hv1 i)
  calc X * ((∏ i, u i) * ∏ i, v i) ≤ 1 * ((∏ i, u i) * ∏ i, v i) :=
        mul_le_mul_of_nonneg_right hX1 (mul_nonneg hA hB0)
    _ ≤ ∏ i, u i := by rw [one_mul]; exact mul_le_of_le_one_right hA hB1

theorem layerProd_count_mul_density_le_two :
    ∀ (n f q a : ℕ) (j : Fin a → ℕ) (τ : Fin a → ℝ) (de : ℝ), ∑ i, j i ≤ q → 2 * q ≤ n → StrictMono τ →
      (∀ i, 0 < τ i ∧ τ i < 1 / 2) → 0 ≤ de → de * q * n * f ≤ 1 / 100 →
      layerProd n f j τ (fun la => 1 + 12 * de / la) * layerProd n f j τ (fun la => la) ≤ 2 ∧
      layerProd n f j τ (fun la => la) ≤ ∏ i, τ i ^ (2 * j i * (n - 2 * ∑ l, j l) * f) := by
  intro n f q a j τ de hq hqn hτ h01 hde hsmall
  have hS2 : 2 * ∑ i, j i ≤ n := by omega
  have hpos : ∀ i, 0 < τ i := fun i => (h01 i).1
  have hlt : ∀ i, τ i < 1 := fun i => by linarith [(h01 i).2]
  constructor
  · rw [layerProd_mul_layerProd]
    have hb := layerProd_le_exp n f j τ (fun la => (1 + 12 * de / la) * la) (12 * de) (by positivity)
      hS2 hτ (fun i => ⟨hpos i, hlt i⟩) (fun la h0 h1 => by
        show 0 ≤ (1 + 12 * de / la) * la ∧ (1 + 12 * de / la) * la ≤ Real.exp (12 * de)
        rw [add_mul, div_mul_cancel₀ _ h0.ne', one_mul]
        exact ⟨by linarith, by linarith [Real.add_one_le_exp (12 * de)]⟩)
    refine hb.trans ?_
    have hnat : 3 * (∑ i, j i) * n * f ≤ 3 * q * n * f := by gcongr
    have hcast : ((3 * (∑ i, j i) * n * f : ℕ) : ℝ) ≤ 3 * q * n * f := by exact_mod_cast hnat
    have hexp : ((3 * (∑ i, j i) * n * f : ℕ) : ℝ) * (12 * de) ≤ 36 / 100 := by
      calc ((3 * (∑ i, j i) * n * f : ℕ) : ℝ) * (12 * de) ≤ (3 * q * n * f : ℝ) * (12 * de) :=
            mul_le_mul_of_nonneg_right hcast (by positivity)
        _ = 36 * (de * q * n * f) := by ring
        _ ≤ 36 / 100 := by linarith
    calc Real.exp (((3 * (∑ i, j i) * n * f : ℕ) : ℝ) * (12 * de)) ≤ Real.exp (36 / 100) :=
          Real.exp_le_exp.2 hexp
      _ ≤ Real.exp (Real.log 2) := Real.exp_le_exp.2 (by linarith [Real.log_two_gt_d9])
      _ = 2 := Real.exp_log (by norm_num)
  · unfold layerProd
    refine mul_prod_mul_le_prod_of_le_one _ (fun i => τ i ^ (2 * j i * (n - 2 * ∑ l, j l) * f))
      (fun i => (τ i ^ 2) ^ (j i ^ 2 * f)) ?_ ?_ (fun i => pow_nonneg (hpos i).le _)
      (fun i => pow_nonneg (pow_pos (hpos i) 2).le _) ?_
    · apply Finset.prod_nonneg
      intro i _
      apply Finset.prod_nonneg
      intro k _
      exact mul_nonneg (pow_nonneg (div_pos (hpos i) (hpos k)).le _) (pow_nonneg (mul_pos (hpos i) (hpos k)).le _)
    · apply Finset.prod_le_one
      · intro i _
        apply Finset.prod_nonneg
        intro k _
        exact mul_nonneg (pow_nonneg (div_pos (hpos i) (hpos k)).le _) (pow_nonneg (mul_pos (hpos i) (hpos k)).le _)
      · intro i _
        apply Finset.prod_le_one
        · intro k _
          exact mul_nonneg (pow_nonneg (div_pos (hpos i) (hpos k)).le _) (pow_nonneg (mul_pos (hpos i) (hpos k)).le _)
        · intro k hk
          have hik := (Finset.mem_filter.1 hk).2
          have hq1 : τ i / τ k ≤ 1 := ((div_lt_one (hpos k)).2 (hτ hik)).le
          have hp1 : τ i * τ k ≤ 1 := by nlinarith [hpos i, hpos k, hlt i, hlt k]
          exact mul_le_one₀ (pow_le_one₀ (div_pos (hpos i) (hpos k)).le hq1)
            (pow_nonneg (mul_pos (hpos i) (hpos k)).le _) (pow_le_one₀ (mul_pos (hpos i) (hpos k)).le hp1)
    · intro i
      have : τ i ^ 2 ≤ 1 := by nlinarith [hpos i, hlt i]
      exact pow_le_one₀ (pow_pos (hpos i) 2).le this

end GlobalTheory.Count
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetNotGG
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.WUnfold

variable {k r : ℕ}

theorem mul_mem_GG_iff {s x : Mat k r} (hs : s ∈ GG k r) : s * x ∈ GG k r ↔ x ∈ GG k r := by
  have hs' : sᴴ * Hpk k r * s = Hpk k r := hs
  have : (s * x)ᴴ * Hpk k r * (s * x) = xᴴ * Hpk k r * x := by
    rw [Matrix.conjTranspose_mul]
    calc xᴴ * sᴴ * Hpk k r * (s * x) = xᴴ * (sᴴ * Hpk k r * s) * x := by
          simp only [Matrix.mul_assoc]
      _ = xᴴ * Hpk k r * x := by rw [hs']
  show (s * x)ᴴ * Hpk k r * (s * x) = Hpk k r ↔ xᴴ * Hpk k r * x = Hpk k r
  rw [this]

theorem Sset_subset (z : Fin (2 * r + k + 1) → ℂ) : Sset k r z ⊆ GG k r := by
  rintro s ⟨h, hh, m, hm, rfl⟩
  exact (mul_mem_GG_iff hh.1).2 hm.1

theorem measurableSet_not_GG : MeasurableSet {x : Mt k r | Matrix.of x ∉ GG k r} := by
  have hc : IsClosed {x : Mat k r | xᴴ * Hpk k r * x = Hpk k r} :=
    isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
      continuous_id) continuous_const
  have hc' : IsClosed {x : Mt k r | Matrix.of x ∈ GG k r} := hc
  exact hc'.measurableSet.compl

theorem ae_mem_GG {z : Fin (2 * r + k + 1) → ℂ} {μG μS ν : Measure (Mt k r)}
    (hG : IsHaarOn (GG k r) μG) (hS : IsHaarOn (Sset k r z) μS) (hq : IsQuotMeas μG μS ν) :
    ∀ᵐ x ∂ν, Matrix.of x ∈ GG k r := by
  set U : Set (Mt k r) := {x | Matrix.of x ∉ GG k r} with hU
  have hUm : MeasurableSet U := measurableSet_not_GG
  have haeS : ∀ᵐ s ∂μS, Matrix.of s ∈ Sset k r z := hS.2.2.1
  have h1 := hq (U.indicator 1) (measurable_const.indicator hUm)
  rw [lintegral_indicator_one hUm, hG.2.2.1] at h1
  have h2 : ∫⁻ x, U.indicator (fun _ => μS Set.univ) x ∂ν ≤ 0 := by
    rw [h1]
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ U
    · rw [Set.indicator_of_mem hx, ← lintegral_one]
      refine lintegral_mono_ae (haeS.mono fun s hs => ?_)
      have : (fun i j => (Matrix.of s * Matrix.of x) i j : Mt k r) ∈ U := fun h =>
        hx ((mul_mem_GG_iff (Sset_subset z hs)).1 h)
      rw [Set.indicator_of_mem this]; rfl
    · rw [Set.indicator_of_notMem hx]; exact zero_le
  rw [lintegral_indicator_const hUm, nonpos_iff_eq_zero, mul_eq_zero] at h2
  rcases h2 with h | h
  · exact absurd (Measure.measure_univ_eq_zero.1 h) hS.2.1
  · exact h

end GlobalTheory.SgInf.WUnfold
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingAffine
section
noncomputable section

open MeasureTheory Matrix Formalism.MainNotions.S GlobalTheory.LoopV
open scoped Classical

namespace GlobalTheory.LoopVol

theorem measurePreserving_affine {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (hM : M.det = 1) (b : ι → ℂ) :
    MeasurePreserving (fun c : ι → ℂ => M *ᵥ c + b) volume volume := by
  let f : (ι → ℂ) →ₗ[ℝ] (ι → ℂ) := (Matrix.toLin' M).restrictScalars ℝ
  have hdet : LinearMap.det f = 1 := by
    simp only [f, LinearMap.det_restrictScalars, LinearMap.det_toLin', hM, map_one]
  have hfun : (f : (ι → ℂ) → ι → ℂ) = fun c => M *ᵥ c := by
    funext c
    simp [f, Matrix.toLin'_apply]
  have hlin : MeasurePreserving (fun c : ι → ℂ => M *ᵥ c) volume volume := by
    rw [← hfun]
    refine ⟨(LinearMap.continuous_of_finiteDimensional f).measurable, ?_⟩
    rw [Measure.map_linearMap_addHaar_eq_smul_addHaar _ (by rw [hdet]; exact one_ne_zero), hdet]
    simp
  exact (measurePreserving_add_right volume b).comp hlin

variable {N : ℕ}

theorem ofRoots_eq (R : Finset (Fin N × Fin N)) (hR : ∀ q ∈ R, q.1 < q.2) (c : R → ℂ) (i j : Fin N) :
    ofRoots R c i j = (1 : Matrix (Fin N) (Fin N) ℂ) i j + ∑ q : R, if q.1 = (i, j) then c q else 0 := by
  simp only [ofRoots]
  by_cases h : (i, j) ∈ R
  · rw [dif_pos h, Matrix.one_apply_ne (hR _ h).ne, zero_add, Finset.sum_eq_single ⟨(i, j), h⟩]
    · simp
    · intro q _ hq
      rw [if_neg]
      intro h'
      exact hq (Subtype.ext h')
    · intro h'
      exact absurd (Finset.mem_univ _) h'
  · rw [dif_neg h, Finset.sum_eq_zero, add_zero, Matrix.one_apply]
    intro q _
    rw [if_neg]
    intro h'
    apply h
    rw [← h']
    exact q.2

theorem det_two_sided (R : Finset (Fin N × Fin N)) (a b : Matrix (Fin N) (Fin N) ℂ) (ha : IsUpUni a)
    (hb : IsUpUni b) : (Matrix.of fun q q' : R => a q.1.1 q'.1.1 * b q'.1.2 q.1.2).det = 1 := by
  let key : R → Fin N ×ₗ (Fin N)ᵒᵈ := fun q => toLex (q.1.1, OrderDual.toDual q.1.2)
  have hinj : Function.Injective key := by
    intro x y h
    simp only [key, toLex_inj, Prod.mk.injEq, OrderDual.toDual_inj] at h
    exact Subtype.ext (Prod.ext h.1 h.2)
  let e := Equiv.ofInjective key hinj
  rw [← Matrix.det_reindex_self e, Matrix.det_of_isUpperTriangular]
  · refine Finset.prod_eq_one fun i _ => ?_
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply, (ha _ _).2 rfl,
      (hb _ _).2 rfl, mul_one]
  · intro i j hlt
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply]
    have hk : key (e.symm j) < key (e.symm i) := by
      simp only [e, Equiv.apply_ofInjective_symm]
      exact hlt
    simp only [key, Prod.Lex.toLex_lt_toLex, OrderDual.toDual_lt_toDual] at hk
    rcases hk with h1 | ⟨-, h2⟩
    · rw [(ha _ _).1 h1, zero_mul]
    · rw [(hb _ _).1 h2, mul_zero]

theorem measurePreserving_mul (R : Finset (Fin N × Fin N)) (hR : ∀ q ∈ R, q.1 < q.2)
    (a b : Matrix (Fin N) (Fin N) ℂ) (ha : IsUpUni a) (hb : IsUpUni b) :
    MeasurePreserving (fun (c : R → ℂ) (q : R) => (a * ofRoots R c * b) q.1.1 q.1.2) volume volume := by
  have hent : ∀ (c : R → ℂ) (x y : Fin N),
      (a * ofRoots R c * b) x y = ∑ q : R, a x q.1.1 * b q.1.2 y * c q + (a * b) x y := by
    intro c x y
    have hO : ofRoots R c = 1 + ∑ q : R, c q • Matrix.of (fun i j => if q.1 = (i, j) then (1 : ℂ) else 0) := by
      ext i j
      rw [ofRoots_eq R hR c i j, Matrix.add_apply, Matrix.sum_apply]
      congr 1
      refine Finset.sum_congr rfl fun q _ => ?_
      simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [hO, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.add_apply, add_comm, Finset.mul_sum,
      Finset.sum_mul, Matrix.sum_apply]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, mul_comm (c q)]
    congr 1
    simp [Matrix.mul_apply, Prod.ext_iff, ite_and]
  have h := measurePreserving_affine (Matrix.of fun q q' : R => a q.1.1 q'.1.1 * b q'.1.2 q.1.2)
    (det_two_sided R a b ha hb) (fun q : R => (a * b) q.1.1 q.1.2)
  convert h using 1
  funext c q
  simp only [hent, Pi.add_apply, Matrix.mulVec, dotProduct, Matrix.of_apply]

theorem measurePreserving_mul_pi {ι : Type*} [Fintype ι] (R : Finset (Fin N × Fin N)) (hR : ∀ q ∈ R, q.1 < q.2)
    (a b : ι → Matrix (Fin N) (Fin N) ℂ) (ha : ∀ v, IsUpUni (a v)) (hb : ∀ v, IsUpUni (b v)) :
    MeasurePreserving (fun (c : ι → R → ℂ) (v : ι) (q : R) => (a v * ofRoots R (c v) * b v) q.1.1 q.1.2)
      volume volume :=
  measurePreserving_pi (fun _ => volume) (fun _ => volume) fun v =>
    measurePreserving_mul R hR (a v) (b v) (ha v) (hb v)

end GlobalTheory.LoopVol

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormLowerLe
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.LduBound

theorem norm_det_le {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (B : ℝ)
    (h : ∀ i j, ‖A i j‖ ≤ B) : ‖A.det‖ ≤ (Fintype.card ι).factorial * B ^ Fintype.card ι := by
  have := Matrix.det_le (A := A) (abv := NormedField.toAbsoluteValue ℂ) (x := B) h
  rw [nsmul_eq_mul] at this
  exact this

theorem det_minor {n : ℕ} (L R : Matrix (Fin n) (Fin n) ℂ) (hL : IsLoUni L)
    (hR : ∀ a b, b < a → R a b = 0) (i j : Fin n) :
    ((L * R).submatrix (fun a : {k : Fin n // k ≤ j} => if a.1 = j then i else a.1)
      (fun a : {k : Fin n // k ≤ j} => a.1)).det = L i j * ∏ k ∈ Finset.Iic j, R k k := by
  have hf : (L * R).submatrix (fun a : {k : Fin n // k ≤ j} => if a.1 = j then i else a.1)
      (fun a : {k : Fin n // k ≤ j} => a.1) =
      L.submatrix (fun a : {k : Fin n // k ≤ j} => if a.1 = j then i else a.1)
      (fun a : {k : Fin n // k ≤ j} => a.1) * R.submatrix (fun a : {k : Fin n // k ≤ j} => a.1)
      (fun a : {k : Fin n // k ≤ j} => a.1) := by
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.mul_apply]
    rw [← Fintype.sum_subtype_add_sum_subtype (fun k : Fin n => k ≤ j)]
    have : ∑ k : {k : Fin n // ¬ k ≤ j}, L (if a.1 = j then i else a.1) k.1 * R k.1 b.1 = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [hR k.1 b.1 (lt_of_le_of_lt b.2 (not_le.1 k.2)), mul_zero]
    rw [this, add_zero]
  rw [hf, Matrix.det_mul]
  congr 1
  · rw [Matrix.det_of_lowerTriangular]
    · rw [Finset.prod_eq_single (⟨j, le_rfl⟩ : {k : Fin n // k ≤ j})]
      · simp
      · intro b _ hb
        have : b.1 ≠ j := fun h => hb (Subtype.ext h)
        simp only [Matrix.submatrix_apply, if_neg this]
        exact (hL _ _).2 rfl
      · simp
    · intro a b hab
      have hab' : a.1 < b.1 := hab
      have : a.1 ≠ j := ne_of_lt (lt_of_lt_of_le hab' b.2)
      simp only [Matrix.submatrix_apply, if_neg this]
      exact (hL _ _).1 hab'
  · rw [Matrix.det_of_upperTriangular]
    · simp only [Matrix.submatrix_apply]
      exact (Finset.prod_subtype (Finset.Iic j) (fun k => Finset.mem_Iic) (fun k => R k k)).symm
    · intro a b hab
      exact hR _ _ hab

theorem norm_lower_le {n : ℕ} (L U : Matrix (Fin n) (Fin n) ℂ) (t : Fin n → ℂ) (B δ : ℝ)
    (hL : IsLoUni L) (hU : IsUpUni U) (hB : 1 ≤ B) (hδ : 0 < δ)
    (ht : ∀ l : Fin n, δ ≤ ‖∏ i ∈ Finset.Iic l, t i‖)
    (hZ : ∀ i j, ‖(L * Matrix.diagonal t * U) i j‖ ≤ B) (i j : Fin n) :
    ‖L i j‖ ≤ n.factorial * B ^ n / δ := by
  have h1 := det_minor L (Matrix.diagonal t * U) hL
    (fun a b hab => by rw [Matrix.diagonal_mul, (hU a b).1 hab, mul_zero]) i j
  have h2 : ∏ k ∈ Finset.Iic j, (Matrix.diagonal t * U) k k = ∏ k ∈ Finset.Iic j, t k :=
    Finset.prod_congr rfl fun k _ => by rw [Matrix.diagonal_mul, (hU k k).2 rfl, mul_one]
  rw [h2, ← Matrix.mul_assoc] at h1
  have h3 := norm_det_le ((L * Matrix.diagonal t * U).submatrix
    (fun a : {k : Fin n // k ≤ j} => if a.1 = j then i else a.1)
      (fun a : {k : Fin n // k ≤ j} => a.1)) B (fun a b => hZ _ _)
  rw [h1, norm_mul] at h3
  have hc : Fintype.card {k : Fin n // k ≤ j} ≤ n := by
    simpa using Fintype.card_subtype_le (fun k : Fin n => k ≤ j)
  have h4 : ((Fintype.card {k : Fin n // k ≤ j}).factorial : ℝ) * B ^ Fintype.card {k : Fin n // k ≤ j}
      ≤ n.factorial * B ^ n :=
    mul_le_mul (by exact_mod_cast Nat.factorial_le hc) (pow_le_pow_right₀ hB hc) (by positivity)
      (by positivity)
  rw [le_div_iff₀ hδ]
  exact (mul_le_mul_of_nonneg_left (ht j) (norm_nonneg _)).trans (h3.trans h4)

theorem norm_inv_le {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (hA : A.det = 1) (x : ℝ)
    (h : ∀ i j, ‖A i j‖ ≤ x) (i j : Fin (m + 1)) : ‖A⁻¹ i j‖ ≤ m.factorial * x ^ m := by
  rw [Matrix.inv_def, hA, Ring.inverse_one, one_smul, Matrix.adjugate_fin_succ_eq_det_submatrix,
    norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  simpa using norm_det_le (A.submatrix j.succAbove i.succAbove) x (fun a b => h _ _)

theorem ldu_bound (m : ℕ) : ∃ c : ℝ, 0 < c ∧ ∀ (L U : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (t : Fin (m + 1) → ℂ) (B δ : ℝ), IsLoUni L → IsUpUni U → 1 ≤ B → 0 < δ → δ ≤ 1 →
    (∀ l : Fin (m + 1), δ ≤ ‖∏ i ∈ Finset.Iic l, t i‖) →
    (∀ i j, ‖(L * Matrix.diagonal t * U) i j‖ ≤ B) →
    ∀ i j, ‖L i j‖ ≤ c * B ^ (m + 1) / δ ∧ ‖U i j‖ ≤ c * B ^ (m + 1) / δ ∧
      ‖L⁻¹ i j‖ ≤ c * (B ^ (m + 1) / δ) ^ m ∧ ‖U⁻¹ i j‖ ≤ c * (B ^ (m + 1) / δ) ^ m := by
  refine ⟨(m + 1).factorial + m.factorial * ((m + 1).factorial : ℝ) ^ m, by positivity, ?_⟩
  intro L U t B δ hL hU hB hδ _ ht hZ
  have hB0 : 0 < B := by linarith
  have h1 := norm_lower_le L U t B δ hL hU hB hδ ht hZ
  have h2 : ∀ i j, ‖U i j‖ ≤ (m + 1).factorial * B ^ (m + 1) / δ := fun i j =>
    norm_lower_le Uᵀ Lᵀ t B δ (fun a b => ⟨(hU b a).1, fun h => (hU b a).2 h.symm⟩)
      (fun a b => ⟨(hL b a).1, fun h => (hL b a).2 h.symm⟩) hB hδ ht
      (fun a b => by
        have : Uᵀ * Matrix.diagonal t * Lᵀ = (L * Matrix.diagonal t * U)ᵀ := by
          simp [Matrix.transpose_mul, Matrix.mul_assoc]
        rw [this]; exact hZ b a) j i
  have dL : L.det = 1 := by
    rw [Matrix.det_of_lowerTriangular L (fun a b hab => (hL a b).1 hab)]
    exact Finset.prod_eq_one fun k _ => (hL k k).2 rfl
  have dU : U.det = 1 := by
    rw [Matrix.det_of_upperTriangular (M := U) (fun a b hab => (hU a b).1 hab)]
    exact Finset.prod_eq_one fun k _ => (hU k k).2 rfl
  have e1 : ((m + 1).factorial : ℝ) * B ^ (m + 1) / δ ≤
      ((m + 1).factorial + m.factorial * ((m + 1).factorial : ℝ) ^ m) * B ^ (m + 1) / δ := by
    gcongr
    exact le_add_of_nonneg_right (by positivity)
  have e2 : (m.factorial : ℝ) * (((m + 1).factorial : ℝ) * B ^ (m + 1) / δ) ^ m ≤
      ((m + 1).factorial + m.factorial * ((m + 1).factorial : ℝ) ^ m) * (B ^ (m + 1) / δ) ^ m := by
    rw [mul_div_assoc, mul_pow, ← mul_assoc]
    gcongr
    exact le_add_of_nonneg_left (by positivity)
  exact fun i j => ⟨(h1 i j).trans e1, (h2 i j).trans e1, (norm_inv_le L dL _ h1 i j).trans e2,
    (norm_inv_le U dU _ h2 i j).trans e2⟩

end GlobalTheory.SgInf.LduBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsAutIdemElementary
section
open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset
open scoped InnerProductSpace ComplexOrder

namespace GlobalTheory

theorem rowsAut_idem_elementary : ∀ B : RowsAut,
    (B.e 1).im = 0 ∧ 0 ≤ (B.e 1).re ∧ (∀ y, ‖B.e y‖ ≤ (B.e 1).re) ∧ Continuous B.e := by
  intro B
  obtain ⟨hlc, -, hstar, hpos, -⟩ := B.e_adm

  have him : (B.e 1).im = 0 := by
    have h := congrArg Complex.im (hstar 1)
    rw [inv_one, Complex.star_def, Complex.conj_im] at h
    linarith

  have hre : 0 ≤ (B.e 1).re := by
    have h := hpos 1 (fun _ => 1) (fun _ => 1)
    simp only [Fin.sum_univ_one, star_one, one_mul, inv_one] at h
    exact (Complex.nonneg_iff.mp h).1
  refine ⟨him, hre, ?_, hlc.continuous⟩
  intro y
  set a := (B.e 1).re with ha
  have h1 : B.e 1 = (a : ℂ) := Complex.ext (by simp [ha]) (by simp [him])
  set b := B.e y with hb
  have hyi : B.e y⁻¹ = star b := hstar y
  have key : star b * b = ((‖b‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_mul']
    push_cast
    ring
  have hs : star ((‖b‖ : ℝ) : ℂ) = ((‖b‖ : ℝ) : ℂ) := Complex.conj_ofReal _

  have h := hpos 2 ![1, y] ![b, -((‖b‖ : ℝ) : ℂ)]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    inv_one, one_mul, mul_one, inv_mul_cancel, hyi, h1, star_neg, hs] at h
  have hE : star b * b * (a : ℂ) + star b * -((‖b‖ : ℝ) : ℂ) * b +
      (-((‖b‖ : ℝ) : ℂ) * b * star b + -((‖b‖ : ℝ) : ℂ) * -((‖b‖ : ℝ) : ℂ) * (a : ℂ)) =
      ((2 * ‖b‖ ^ 2 * (a - ‖b‖) : ℝ) : ℂ) := by
    push_cast at key ⊢
    linear_combination ((a : ℂ) - 2 * ((‖b‖ : ℝ) : ℂ)) * key
  rw [hE, Complex.zero_le_real] at h
  refine le_of_not_gt fun hlt => ?_
  have hb0 : 0 < ‖b‖ := lt_of_le_of_lt hre hlt
  have hneg : 2 * ‖b‖ ^ 2 * (a - ‖b‖) < 0 := mul_neg_of_pos_of_neg (by positivity) (by linarith)
  linarith

end GlobalTheory
end

