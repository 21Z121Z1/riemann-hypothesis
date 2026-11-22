import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.MulConjTransposeEqOneOfOrthonormal
section
open Matrix

namespace GlobalTheory

section Ring

variable {R : Type*} [CommRing R]

abbrev subsetEnum {n : Type*} [LinearOrder n] {i : ℕ} (S : Set.powersetCard n i) : Fin i → n :=
  S.1.orderEmbOfFin S.2

theorem range_subsetEnum {n : Type*} [LinearOrder n] {i : ℕ} (S : Set.powersetCard n i) :
    Set.range (subsetEnum S) = (S.1 : Set n) :=
  Finset.range_orderEmbOfFin _ _

theorem subsetEnum_injective {n : Type*} [LinearOrder n] {i : ℕ} (S : Set.powersetCard n i) :
    Function.Injective (subsetEnum S) :=
  (S.1.orderEmbOfFin S.2).injective

theorem alternatingMap_apply_eq_sum_minors {n : Type*} [Fintype n] [LinearOrder n] {i : ℕ}
    {M : Type*} [AddCommGroup M] [Module R M] (f : (n → R) [⋀^Fin i]→ₗ[R] M)
    (A : Fin i → n → R) :
    f A = ∑ S : Set.powersetCard n i,
      ((Matrix.of A).submatrix id (subsetEnum S)).det • f (fun a => Pi.single (subsetEnum S a) 1) := by
  classical
  let b := Pi.basisFun R n
  have h := (b.exteriorPower i).sum_repr (exteriorPower.ιMulti R i A)
  rw [← exteriorPower.alternatingMapLinearEquiv_apply_ιMulti f A, ← h, map_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [map_smul, exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti,
    exteriorPower.basis_apply, exteriorPower.ιMulti_family,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  congr 2
  funext a
  simp only [b, Function.comp_apply, Pi.basisFun_apply]
  rfl

theorem det_mul_eq_sum_minors {n : Type*} [Fintype n] [LinearOrder n] {i : ℕ}
    (A : Matrix (Fin i) n R) (B : Matrix n (Fin i) R) :
    (A * B).det = ∑ S : Set.powersetCard n i,
      (A.submatrix id (subsetEnum S)).det * (B.submatrix (subsetEnum S) id).det := by
  classical
  have h := alternatingMap_apply_eq_sum_minors
    ((Matrix.detRowAlternating (n := Fin i) (R := R)).compLinearMap B.vecMulLinear) A
  have h0 : (A * B).det =
      ((Matrix.detRowAlternating (n := Fin i) (R := R)).compLinearMap B.vecMulLinear) A := rfl
  rw [h0, h]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [smul_eq_mul]
  congr 1
  rw [AlternatingMap.compLinearMap_apply]
  change Matrix.det _ = _
  congr 1
  ext a c
  simp [Matrix.vecMulLinear_apply, Matrix.single_one_vecMul]

theorem det_mul_det_eq_of_range_eq {m k n : Type*} [Fintype m] [DecidableEq m] [Fintype k]
    [DecidableEq k] (A : Matrix m n R) (B : Matrix n m R) (φ : k ≃ m) (e : m → n) (g : k → n)
    (hg : Function.Injective g) (h : Set.range e = Set.range g) :
    (A.submatrix id e).det * (B.submatrix e id).det =
      (A.submatrix φ g).det * (B.submatrix g φ).det := by
  have h1 : ∀ a : k, ∃ c : m, e c = g a := fun a => by
    have : g a ∈ Set.range e := h ▸ Set.mem_range_self a
    exact this
  choose s hs using h1
  have hinj : Function.Injective (φ.symm ∘ s) := by
    intro a a' haa
    have : s a = s a' := φ.symm.injective haa
    exact hg (by rw [← hs a, ← hs a', this])
  let σ : Equiv.Perm k := Equiv.ofBijective _ (Finite.injective_iff_bijective.mp hinj)
  have hσ : ∀ a, e (φ (σ a)) = g a := fun a => by simp [σ, hs]
  have hA : A.submatrix φ g = ((A.submatrix id e).submatrix φ φ).submatrix id σ := by
    ext a c; simp [hσ]
  have hB : B.submatrix g φ = ((B.submatrix e id).submatrix φ φ).submatrix σ id := by
    ext a c; simp [hσ]
  rw [hA, hB, det_permute, det_permute', det_submatrix_equiv_self, det_submatrix_equiv_self]
  have : ((Equiv.Perm.sign σ : ℤ) : R) * ((Equiv.Perm.sign σ : ℤ) : R) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]; simp
  linear_combination (-(A.submatrix id e).det * (B.submatrix e id).det) * this

theorem det_mul_eq_sum_minors_of_enum {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]
    (e : Set.powersetCard n (Fintype.card m) → m → n)
    (he : ∀ S, Set.range (e S) = (S.1 : Set n)) (A : Matrix m n R) (B : Matrix n m R) :
    (A * B).det = ∑ S : Set.powersetCard n (Fintype.card m),
      (A.submatrix id (e S)).det * (B.submatrix (e S) id).det := by
  classical
  letI : LinearOrder n := linearOrderOfSTO WellOrderingRel
  let φ : Fin (Fintype.card m) ≃ m := (Fintype.equivFin m).symm
  rw [← det_submatrix_equiv_self φ (A * B), submatrix_mul A B φ id φ Function.bijective_id,
    det_mul_eq_sum_minors]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [det_mul_det_eq_of_range_eq A B φ (e S) (subsetEnum S) (subsetEnum_injective S)
    ((he S).trans (range_subsetEnum S).symm)]
  rfl

theorem det_submatrix_mul_eq_sum_minors {l n o : Type*} [Fintype n] [LinearOrder n] {i : ℕ}
    (A : Matrix l n R) (B : Matrix n o R) (r : Fin i → l) (c : Fin i → o) :
    ((A * B).submatrix r c).det = ∑ S : Set.powersetCard n i,
      (A.submatrix r (subsetEnum S)).det * (B.submatrix (subsetEnum S) c).det := by
  rw [submatrix_mul A B r id c Function.bijective_id, det_mul_eq_sum_minors]
  rfl

theorem det_mul_diagonal_mul_eq_sum_minors {n : Type*} [Fintype n] [LinearOrder n] {i : ℕ}
    (A : Matrix (Fin i) n R) (d : n → R) (B : Matrix n (Fin i) R) :
    (A * diagonal d * B).det = ∑ S : Set.powersetCard n i,
      (∏ s ∈ S.1, d s) *
        ((A.submatrix id (subsetEnum S)).det * (B.submatrix (subsetEnum S) id).det) := by
  rw [det_mul_eq_sum_minors]
  refine Finset.sum_congr rfl fun S _ => ?_
  have h1 : (A * diagonal d).submatrix id (subsetEnum S) =
      A.submatrix id (subsetEnum S) * diagonal (d ∘ subsetEnum S) := by
    ext a c; simp
  have h2 : ∏ a, d (subsetEnum S a) = ∏ s ∈ S.1, d s := by
    refine Finset.prod_bij (fun a _ => subsetEnum S a) (fun a _ => Finset.orderEmbOfFin_mem _ _ _)
      (fun a _ b _ h => subsetEnum_injective S h) (fun s hs => ?_) (fun _ _ => rfl)
    have : s ∈ Set.range (subsetEnum S) := by rw [range_subsetEnum]; exact hs
    obtain ⟨a, ha⟩ := this
    exact ⟨a, Finset.mem_univ _, ha⟩
  rw [h1, det_mul, det_diagonal, ← h2]
  simp only [Function.comp_apply]
  ring

end Ring

section Normed

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [LinearOrder n] {i : ℕ}

theorem det_mul_conjTranspose_eq_sum_norm_sq (A : Matrix (Fin i) n 𝕜) :
    (A * Aᴴ).det =
      ((∑ S : Set.powersetCard n i, ‖(A.submatrix id (subsetEnum S)).det‖ ^ 2 : ℝ) : 𝕜) := by
  rw [det_mul_eq_sum_minors]
  push_cast
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [← conjTranspose_submatrix, det_conjTranspose, RCLike.star_def, RCLike.mul_conj]

theorem sum_norm_sq_minors_eq_one (A : Matrix (Fin i) n 𝕜) (hA : A * Aᴴ = 1) :
    ∑ S : Set.powersetCard n i, ‖(A.submatrix id (subsetEnum S)).det‖ ^ 2 = 1 := by
  have h := det_mul_conjTranspose_eq_sum_norm_sq A
  rw [hA, det_one] at h
  exact_mod_cast h.symm

theorem two_rpow_neg_half_le_choose_rpow {i N r : ℕ} (hi : i ≤ N) (hr : N ≤ r) :
    (2 : ℝ) ^ (-(r : ℝ) / 2) ≤ (N.choose i : ℝ) ^ (-(1 : ℝ) / 2) := by
  have hpos : (0 : ℝ) < N.choose i := by exact_mod_cast Nat.choose_pos hi
  have hle : (N.choose i : ℝ) ≤ (2 : ℝ) ^ (r : ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast (Nat.choose_le_two_pow N i).trans (Nat.pow_le_pow_right two_pos hr)
  calc (2 : ℝ) ^ (-(r : ℝ) / 2) = ((2 : ℝ) ^ (r : ℝ)) ^ (-(1 : ℝ) / 2) := by
        rw [← Real.rpow_mul zero_le_two]; congr 1; ring
    _ ≤ _ := Real.rpow_le_rpow_of_nonpos hpos hle (by norm_num)

theorem exists_choose_rpow_le_norm_minor (A : Matrix (Fin i) n 𝕜) (hA : A * Aᴴ = 1) :
    i ≤ Fintype.card n ∧ ∃ S : Set.powersetCard n i,
      ((Fintype.card n).choose i : ℝ) ^ (-(1 : ℝ) / 2) ≤
        ‖(A.submatrix id (subsetEnum S)).det‖ := by
  have h := sum_norm_sq_minors_eq_one A hA
  have hne : (Finset.univ : Finset (Set.powersetCard n i)).Nonempty := by
    rcases (Finset.univ : Finset (Set.powersetCard n i)).eq_empty_or_nonempty with h0 | h0
    · rw [h0] at h; simp at h
    · exact h0
  have hi : i ≤ Fintype.card n := by
    obtain ⟨S, -⟩ := hne
    exact S.2 ▸ Finset.card_le_univ S.1
  have hcard : Fintype.card (Set.powersetCard n i) = (Fintype.card n).choose i := by
    rw [Fintype.card_eq_nat_card, Set.powersetCard.card, Nat.card_eq_fintype_card]
  have hpos : (0 : ℝ) < (Fintype.card n).choose i := by exact_mod_cast Nat.choose_pos hi
  refine ⟨hi, ?_⟩
  obtain ⟨S, -, hS⟩ := Finset.exists_le_of_sum_le hne
    (f := fun _ => (((Fintype.card n).choose i : ℝ))⁻¹)
    (g := fun S => ‖(A.submatrix id (subsetEnum S)).det‖ ^ 2) (by
      rw [h, Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul, mul_inv_cancel₀ hpos.ne'])
  refine ⟨S, (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp ?_⟩
  refine le_of_eq_of_le ?_ hS
  rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le, ← Real.rpow_neg_one]
  norm_num

theorem exists_two_rpow_le_norm_minor (A : Matrix (Fin i) n 𝕜) (hA : A * Aᴴ = 1) {r : ℕ}
    (hr : Fintype.card n ≤ r) :
    ∃ S : Set.powersetCard n i,
      (2 : ℝ) ^ (-(r : ℝ) / 2) ≤ ‖(A.submatrix id (subsetEnum S)).det‖ := by
  obtain ⟨hi, S, hS⟩ := exists_choose_rpow_le_norm_minor A hA
  exact ⟨S, (two_rpow_neg_half_le_choose_rpow hi hr).trans hS⟩

end Normed

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.NatCastMulCoeffOfPderivEq
section
namespace GlobalTheory.FormalCalc

open MvPowerSeries Finsupp

section Chain

variable {σ τ R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

theorem subst_zero' {a : σ → MvPowerSeries τ S} (ha : HasSubst a) :
    subst a (0 : MvPowerSeries σ R) = 0 := by
  rw [← substAlgHom_apply ha, map_zero]

theorem subst_one' {a : σ → MvPowerSeries τ S} (ha : HasSubst a) :
    subst a (1 : MvPowerSeries σ R) = 1 := by
  rw [← substAlgHom_apply ha, map_one]

theorem subst_neg' {a : σ → MvPowerSeries τ S} (ha : HasSubst a) (f : MvPowerSeries σ R) :
    subst a (-f) = -subst a f := by
  rw [← substAlgHom_apply ha, map_neg, substAlgHom_apply]

theorem subst_sum' {κ : Type*} {a : σ → MvPowerSeries τ S} (ha : HasSubst a) (s : Finset κ)
    (f : κ → MvPowerSeries σ R) : subst a (∑ k ∈ s, f k) = ∑ k ∈ s, subst a (f k) := by
  rw [← substAlgHom_apply ha, map_sum]
  simp only [substAlgHom_apply]

theorem subst_C' {a : σ → MvPowerSeries τ S} (ha : HasSubst a) (r : R) :
    subst a (C r : MvPowerSeries σ R) = C (algebraMap R S r) := by
  rw [← substAlgHom_apply ha, show (C r : MvPowerSeries σ R) = algebraMap R _ r from rfl,
    AlgHom.commutes, MvPowerSeries.algebraMap_apply]

open MvPowerSeries.WithPiTopology in

theorem continuous_pderiv [TopologicalSpace R] [DiscreteTopology R] (i : σ) :
    Continuous (pderiv R i : MvPowerSeries σ R → MvPowerSeries σ R) := by
  refine continuous_iff_continuousAt.mpr fun f => ?_
  rw [ContinuousAt, tendsto_iff_coeff_tendsto]
  intro d
  simp only [coeff_pderiv]
  exact ((continuous_coeff R (d + single i 1)).mul continuous_const).continuousAt

theorem pderiv_comm (i j : σ) (f : MvPowerSeries σ R) :
    pderiv R i (pderiv R j f) = pderiv R j (pderiv R i f) := by
  classical
  by_cases h : i = j
  · rw [h]
  ext d
  simp only [coeff_pderiv, Finsupp.add_apply, single_eq_of_ne h, single_eq_of_ne (Ne.symm h),
    add_zero]
  rw [add_right_comm]
  ring

open MvPowerSeries.WithPiTopology in

theorem pderiv_subst [Fintype σ] {a : σ → MvPowerSeries τ S} (ha : HasSubst a)
    (f : MvPowerSeries σ R) (j : τ) :
    pderiv S j (subst a f) = ∑ i, subst a (pderiv R i f) * pderiv S j (a i) := by
  classical
  letI : UniformSpace R := ⊥
  letI : UniformSpace S := ⊥
  have hc := continuous_subst (R := R) ha
  refine congr_fun (DenseRange.equalizer (denseRange_toMvPowerSeries (σ := σ) (R := R))
    (g := fun f => pderiv S j (subst a f))
    (h := fun f => ∑ i, subst a (pderiv R i f) * pderiv S j (a i))
    ((continuous_pderiv j).comp hc)
    (continuous_finset_sum _ fun i _ => (hc.comp (continuous_pderiv i)).mul continuous_const)
    ?_) f
  funext p
  simp only [Function.comp_apply]
  induction p using MvPolynomial.induction_on with
  | C r =>
    simp [MvPolynomial.coe_C, pderiv_C, subst_C' ha, subst_zero' ha]
  | add p q hp hq =>
    simp only [MvPolynomial.coe_add, subst_add ha, map_add, hp, hq, add_mul,
      Finset.sum_add_distrib]
  | mul_X p n hp =>
    simp only [MvPolynomial.coe_mul, MvPolynomial.coe_X, subst_mul ha, Derivation.leibniz, hp,
      smul_eq_mul, subst_add ha, subst_X ha, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    · rw [Finset.sum_eq_single n]
      · simp [subst_one' ha]
      · intro b _ hb
        simp [pderiv_X_of_ne (Ne.symm hb), subst_zero' ha]
      · simp
    · exact Finset.sum_congr rfl fun i _ => by ring

theorem pderiv_powerSeries_subst {a : MvPowerSeries τ S} (ha : PowerSeries.HasSubst a)
    (f : PowerSeries R) (j : τ) :
    pderiv S j (PowerSeries.subst a f) =
      PowerSeries.subst a (PowerSeries.derivative R f) * pderiv S j a := by
  have h := pderiv_subst (σ := Unit) (a := fun _ => a) ha.const f j
  simpa [PowerSeries.subst, PowerSeries.derivative] using h

theorem constantCoeff_subst_of_zero {a : σ → MvPowerSeries τ S} (ha : HasSubst a)
    (ha0 : ∀ i, constantCoeff (a i) = 0) (f : MvPowerSeries σ R) :
    constantCoeff (subst a f) = algebraMap R S (constantCoeff f) := by
  have h : f = C (constantCoeff f) + (f - C (constantCoeff f)) := by simp
  have h' : constantCoeff (subst a (f - C (constantCoeff f))) = 0 :=
    constantCoeff_subst_eq_zero ha ha0 (by simp)
  conv_lhs => rw [h, subst_add ha, map_add, h', subst_C' ha]
  simp

theorem pderiv_map {T : Type*} [CommRing T] (φ : R →+* T) (i : σ) (f : MvPowerSeries σ R) :
    pderiv T i (map φ f) = map φ (pderiv R i f) := by
  ext d
  simp [coeff_pderiv]

end Chain

section Poincare

variable {σ ι A : Type*} [CommRing A]

theorem natCast_mul_coeff_of_pderiv_eq {f a : MvPowerSeries σ A} {s : σ}
    (h : pderiv A s f = a) {α : σ →₀ ℕ} (hα : α s ≠ 0) :
    (α s : A) * coeff α f = coeff (α - single s 1) a := by
  have hle : single s 1 ≤ α := single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hα)
  rw [← h, coeff_pderiv, tsub_add_cancel_of_le hle, coe_tsub, Pi.sub_apply, single_eq_same,
    Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hα), Nat.cast_one, sub_add_cancel, mul_comm]

theorem ext_of_pderiv_of_coeff [IsAddTorsionFree A] (e : ι → σ) {f g : MvPowerSeries σ A}
    (hD : ∀ i, pderiv A (e i) f = pderiv A (e i) g)
    (h0 : ∀ α : σ →₀ ℕ, (∀ i, α (e i) = 0) → coeff α f = coeff α g) : f = g := by
  ext α
  by_cases h : ∀ i, α (e i) = 0
  · exact h0 α h
  push Not at h
  obtain ⟨i, hi⟩ := h
  have h1 := natCast_mul_coeff_of_pderiv_eq (hD i) hi
  have h2 := natCast_mul_coeff_of_pderiv_eq (rfl : pderiv A (e i) g = _) hi
  rw [← h2, ← nsmul_eq_mul, ← nsmul_eq_mul] at h1
  exact (smul_right_inj hi).mp h1

variable [Algebra ℚ A]

theorem existsUnique_primitive_param {e : ι → σ} (he : Function.Injective e)
    (a : ι → MvPowerSeries σ A) (ha : ∀ i j, pderiv A (e i) (a j) = pderiv A (e j) (a i)) :
    ∃! f : MvPowerSeries σ A, (∀ α : σ →₀ ℕ, (∀ i, α (e i) = 0) → coeff α f = 0) ∧
      ∀ i, pderiv A (e i) f = a i := by
  classical
  haveI : IsAddTorsionFree A := .of_module_rat A
  have key : ∀ (α : σ →₀ ℕ) (i j : ι), α (e i) ≠ 0 → α (e j) ≠ 0 →
      (α (e j) : A) * coeff (α - single (e i) 1) (a i) =
        (α (e i) : A) * coeff (α - single (e j) 1) (a j) := by
    intro α i j hi hj
    by_cases hij : i = j
    · rw [hij]
    have hne : e i ≠ e j := fun h => hij (he h)
    have e1 : (α - single (e i) 1 : σ →₀ ℕ) (e j) = α (e j) := by
      simp [single_eq_of_ne (Ne.symm hne)]
    have e2 : (α - single (e j) 1 : σ →₀ ℕ) (e i) = α (e i) := by
      simp [single_eq_of_ne hne]
    have h1 := natCast_mul_coeff_of_pderiv_eq (rfl : pderiv A (e j) (a i) = _) (e1 ▸ hj)
    have h2 := natCast_mul_coeff_of_pderiv_eq (rfl : pderiv A (e i) (a j) = _) (e2 ▸ hi)
    rw [e1] at h1
    rw [e2] at h2
    rw [h1, h2, ha, tsub_right_comm]
  let f : MvPowerSeries σ A := fun α =>
    if h : ∃ i, α (e i) ≠ 0 then
      ((α (e h.choose) : ℚ)⁻¹) • coeff (α - single (e h.choose) 1) (a h.choose) else 0
  have hf : ∀ α, coeff α f = if h : ∃ i, α (e i) ≠ 0 then
      ((α (e h.choose) : ℚ)⁻¹) • coeff (α - single (e h.choose) 1) (a h.choose) else 0 :=
    fun _ => rfl
  have hf0 : ∀ α : σ →₀ ℕ, (∀ i, α (e i) = 0) → coeff α f = 0 := by
    intro α h
    rw [hf, dif_neg]
    push Not
    exact h
  have hf1 : ∀ i, pderiv A (e i) f = a i := by
    intro i
    ext n
    have hi : (n + single (e i) 1 : σ →₀ ℕ) (e i) ≠ 0 := by simp
    have hex : ∃ j, (n + single (e i) 1 : σ →₀ ℕ) (e j) ≠ 0 := ⟨i, hi⟩
    have hk := key _ hex.choose i hex.choose_spec hi
    have hq : (((n + single (e i) 1 : σ →₀ ℕ) (e hex.choose) : ℕ) : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr hex.choose_spec
    rw [add_tsub_cancel_right] at hk
    rw [coeff_pderiv, hf, dif_pos hex, smul_mul_assoc, mul_comm]
    have : ((n (e i) : A) + 1) = (((n + single (e i) 1 : σ →₀ ℕ) (e i) : ℕ) : A) := by simp
    rw [this, hk, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ hq,
      one_smul]
  refine ⟨f, ⟨hf0, hf1⟩, fun g hg => ?_⟩
  exact ext_of_pderiv_of_coeff e (fun i => by rw [hg.2, hf1]) fun α h => by rw [hg.1 α h, hf0 α h]

end Poincare

end GlobalTheory.FormalCalc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.SummablePiProd
section
namespace GlobalTheory.SummablePiProd

universe u_1 u_2

theorem summable_pi_prod {ι : Type u_1} [inst : Fintype ι] {J : ι → Type u_2}
    {u : (i : ι) → J i → ℝ} (h0 : ∀ (i : ι) (j : J i), (0 : ℝ) ≤ u i j)
    (hs : ∀ (i : ι), Summable (u i)) :
    Summable fun (t : (i : ι) → J i) ↦ ∏ i : ι, u i (t i) := by
  classical
  refine summable_of_sum_le (c := ∏ i, ∑' j, u i j)
    (fun t => Finset.prod_nonneg fun i _ => h0 i (t i)) ?_
  intro s
  calc ∑ t ∈ s, ∏ i, u i (t i)
      ≤ ∑ t ∈ Fintype.piFinset (fun i => s.image (fun t => t i)), ∏ i, u i (t i) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_
          (fun t _ _ => Finset.prod_nonneg fun i _ => h0 i (t i))
        intro t ht
        exact Fintype.mem_piFinset.2 fun i => Finset.mem_image_of_mem _ ht
    _ = ∏ i, ∑ j ∈ s.image (fun t => t i), u i j := (Finset.prod_univ_sum _ _).symm
    _ ≤ ∏ i, ∑' j, u i j := by
        refine Finset.prod_le_prod (fun i _ => Finset.sum_nonneg fun j _ => h0 i j) ?_
        intro i _
        exact (hs i).sum_le_tsum _ (fun j _ => h0 i j)

end GlobalTheory.SummablePiProd
end

