import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MonomialCountAndBinomialEstimates
section
namespace GlobalTheory

open Finset

theorem setOf_degree_eq_coe_finsuppAntidiag (σ : Type*) [Fintype σ] [DecidableEq σ] (a : ℕ) :
    {α : σ →₀ ℕ | α.degree = a} = ↑(finsuppAntidiag (univ : Finset σ) a) := by
  ext α
  simp [Finset.mem_finsuppAntidiag, Finsupp.degree_eq_sum]

theorem ncard_degree_eq (σ : Type*) [Fintype σ] (a : ℕ) :
    {α : σ →₀ ℕ | α.degree = a}.ncard = (a + Fintype.card σ - 1).choose a := by
  classical
  rw [setOf_degree_eq_coe_finsuppAntidiag, Set.ncard_coe_finset,
    Finset.card_finsuppAntidiag_nat_eq_choose, Finset.card_univ, Nat.add_comm]

theorem ncard_degree_le (σ : Type*) [Fintype σ] (k : ℕ) :
    {α : σ →₀ ℕ | α.degree ≤ k}.ncard = (k + Fintype.card σ).choose (Fintype.card σ) := by
  classical
  have hset : {α : σ →₀ ℕ | α.degree ≤ k} =
      ↑((range (k + 1)).biUnion fun a => finsuppAntidiag (univ : Finset σ) a) := by
    ext α
    simp [Finset.mem_finsuppAntidiag, Finsupp.degree_eq_sum]
  rw [hset, Set.ncard_coe_finset, Finset.card_biUnion]
  · simp_rw [Finset.card_finsuppAntidiag_nat_eq_choose, Finset.card_univ, ← Nat.multichoose_eq]
    exact Nat.sum_range_multichoose k _
  · intro a _ b _ hab
    exact Finset.disjoint_left.2 fun α h1 h2 =>
      hab ((Finset.mem_finsuppAntidiag.1 h1).1.symm.trans (Finset.mem_finsuppAntidiag.1 h2).1)

theorem natCard_degree_eq (σ : Type*) [Fintype σ] (a : ℕ) :
    Nat.card {α : σ →₀ ℕ // α.degree = a} = (a + Fintype.card σ - 1).choose a := by
  have h := ncard_degree_eq σ a
  rw [← Nat.card_coe_set_eq] at h
  exact h

theorem natCard_degree_le (σ : Type*) [Fintype σ] (k : ℕ) :
    Nat.card {α : σ →₀ ℕ // α.degree ≤ k} = (k + Fintype.card σ).choose (Fintype.card σ) := by
  have h := ncard_degree_le σ k
  rw [← Nat.card_coe_set_eq] at h
  exact h

theorem fintypeCard_degree_le (σ : Type*) [Fintype σ] (k : ℕ)
    [Fintype {α : σ →₀ ℕ // α.degree ≤ k}] :
    Fintype.card {α : σ →₀ ℕ // α.degree ≤ k} =
      (k + Fintype.card σ).choose (Fintype.card σ) := by
  rw [← Nat.card_eq_fintype_card]
  exact natCard_degree_le σ k

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.OneSubSmulPeirceCut
section
namespace GlobalTheory.PeirceDecompositionCut

variable {R : Type*} [CommRing R] (A : Type*) [Ring A] [Algebra R A]

def peirceCut (e : R) (he : IsIdempotentElem e) : A →* A where
  toFun x := e • x + (1 - e) • (1 : A)
  map_one' := by rw [← add_smul, add_sub_cancel, one_smul]
  map_mul' x y := by
    have h1 : e * e = e := he
    have h2 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, h1, sub_self]
    have h3 : (1 - e) * e = 0 := by rw [mul_comm, h2]
    have h4 : (1 - e) * (1 - e) = 1 - e := he.one_sub
    simp only [add_mul, mul_add, smul_mul_smul_comm, h1, h2, h3, h4, zero_smul, add_zero,
      zero_add, mul_one]

variable {A}

@[simp] theorem peirceProjection_apply (e : R) (he : IsIdempotentElem e) (x : A) :
    peirceCut A e he x = e • x + (1 - e) • (1 : A) := rfl

end GlobalTheory.PeirceDecompositionCut
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SigmaSplitSymmInl
section
namespace GlobalTheory.InnerAutomorphism

section Inner

variable {A : Type*} (R : Type*) [CommSemiring R] [Semiring A] [Algebra R A]

def innerAut (u : Aˣ) : A ≃ₐ[R] A where
  toFun x := (u : A) * x * ((u⁻¹ : Aˣ) : A)
  invFun x := ((u⁻¹ : Aˣ) : A) * x * (u : A)
  left_inv x := by simp [mul_assoc]
  right_inv x := by simp [mul_assoc]
  map_mul' x y := by simp [mul_assoc]
  map_add' x y := by simp [mul_add, add_mul]
  commutes' r := by rw [← Algebra.commutes, mul_assoc, Units.mul_inv, mul_one]

@[simp] theorem innerAut_apply (u : Aˣ) (x : A) :
    innerAut R u x = (u : A) * x * ((u⁻¹ : Aˣ) : A) := rfl

end Inner

section Bounded

variable {K n : Type*} [NormedField K]

def EntriesBounded (M : Matrix n n K) (c : ℝ) : Prop :=
  ∀ i j, ‖M i j‖ ≤ c

theorem EntriesBounded.mono {M : Matrix n n K} {c d : ℝ} (h : EntriesBounded M c)
    (hcd : c ≤ d) : EntriesBounded M d :=
  fun i j => (h i j).trans hcd

theorem EntriesBounded.mul [IsUltrametricDist K] [Fintype n] {M N : Matrix n n K} {c d : ℝ}
    (hM : EntriesBounded M c) (hN : EntriesBounded N d) :
    EntriesBounded (M * N) (c * d) := by
  intro i j
  have hc : 0 ≤ c := (norm_nonneg _).trans (hM i j)
  have hd : 0 ≤ d := (norm_nonneg _).trans (hN i j)
  rw [Matrix.mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hc hd) ?_
  intro k _
  rw [norm_mul]
  exact mul_le_mul (hM i k) (hN k j) (norm_nonneg _) hc

end Bounded

section DropLast

variable (K : Type*) [Semiring K] (d : ℕ)

def dropLast : (Fin (d + 1) → K) →ₗ[K] (Fin d → K) where
  toFun x i := x i.castSucc
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem dropLast_apply (x : Fin (d + 1) → K) (i : Fin d) :
    dropLast K d x i = x i.castSucc := rfl

end DropLast

section Split

variable {ι : Type*} [DecidableEq ι] (F : ι → Type*)

def sigmaSplit (j : ι) : (Σ i, F i) ≃ F j ⊕ (Σ i : {i // i ≠ j}, F i.1) where
  toFun p := if h : p.1 = j then Sum.inl (h ▸ p.2) else Sum.inr ⟨⟨p.1, h⟩, p.2⟩
  invFun s := Sum.elim (fun x => ⟨j, x⟩) (fun q => ⟨q.1.1, q.2⟩) s
  left_inv := by
    rintro ⟨i, x⟩
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  right_inv := by
    rintro (x | ⟨⟨i, hi⟩, x⟩)
    · simp
    · simp [show ¬ i = j from hi]

theorem sigmaSplit_self (j : ι) (x : F j) : sigmaSplit F j ⟨j, x⟩ = Sum.inl x :=
  (Equiv.apply_eq_iff_eq_symm_apply _).2 rfl

theorem sigmaSplit_of_ne {i j : ι} (h : i ≠ j) (x : F i) :
    sigmaSplit F j ⟨i, x⟩ = Sum.inr ⟨⟨i, h⟩, x⟩ :=
  (Equiv.apply_eq_iff_eq_symm_apply _).2 rfl

end Split

end GlobalTheory.InnerAutomorphism
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SubalgebraEqBotOfIsIntegralOfIsIntegrallyClosed
section
open scoped PowerSeries TensorProduct

namespace GlobalTheory

open scoped PowerSeries TensorProduct in

theorem _root_.GlobalTheory.integralClosure_restrictScalars_of_isIntegral (A A' B : Type*) [CommRing A] [CommRing A']
    [CommRing B] [Algebra A A'] [Algebra A' B] [Algebra A B] [IsScalarTower A A' B]
    [Algebra.IsIntegral A A'] :
    (integralClosure A' B).restrictScalars A = integralClosure A B := by
  ext x
  simp only [Subalgebra.mem_restrictScalars, mem_integralClosure_iff]
  exact ⟨fun h => isIntegral_trans x h, fun h => h.tower_top⟩

section Contraction

variable {A : Type*} [CommRing A] (M : Submonoid A) {S : Type*} [CommRing S] [Algebra A S]
  [IsLocalization M S]

end Contraction

section PowerSeries

open PowerSeries IsLocalRing

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

section Away

variable {ϖ : O} (hϖ : Irreducible ϖ) (S : Type*) [CommRing S] [Algebra O⟦X⟧ S]
  [IsLocalization.Away (C ϖ : O⟦X⟧) S]

include hϖ

variable (𝔭 : Ideal S) [𝔭.IsPrime] (h𝔭 : 𝔭 = Ideal.span {algebraMap O⟦X⟧ S X})
  (V : Type*) [CommRing V] [Algebra S V] [IsLocalization.AtPrime V 𝔭]

include h𝔭

end Away

end PowerSeries

universe u

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SummableNormBoundedSeries
section
namespace GlobalTheory.BoundedPowerSeriesDisc

open PowerSeries

section General

variable {K : Type*} [NormedField K]

theorem summable_norm_of_bounded {a : ℕ → K} {B : ℝ} (ha : ∀ n, ‖a n‖ ≤ B) {t : K}
    (ht : ‖t‖ < 1) : Summable fun n => ‖a n * t ^ n‖ := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    ((summable_geometric_of_lt_one (norm_nonneg t) ht).mul_left B)
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_right (ha n) (pow_nonneg (norm_nonneg t) n)

theorem tsum_coeff_mul [CompleteSpace K] (f g : K⟦X⟧) (t : K)
    (hf : Summable fun n => ‖coeff n f * t ^ n‖) (hg : Summable fun n => ‖coeff n g * t ^ n‖) :
    ∑' n, coeff n (f * g) * t ^ n = (∑' n, coeff n f * t ^ n) * ∑' n, coeff n g * t ^ n := by
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg]
  refine tsum_congr fun n => ?_
  rw [coeff_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  obtain rfl : p.1 + p.2 = n := by simpa using hp
  rw [pow_add]
  ring

theorem tsum_coeff_C (c t : K) : ∑' n, coeff n (C c : K⟦X⟧) * t ^ n = c := by
  rw [tsum_eq_single 0]
  · simp
  · intro n hn
    simp [coeff_C, hn]

theorem tsum_coeff_X (t : K) : ∑' n, coeff n (X : K⟦X⟧) * t ^ n = t := by
  rw [tsum_eq_single 1]
  · simp
  · intro n hn
    simp [coeff_X, hn]

end General

section Integral

variable {O : Type*} [Semiring O] {K : Type*} [NormedField K] [CompleteSpace K]

noncomputable def evalDisc (i : O →+* K) (hi : ∀ a, ‖i a‖ ≤ 1) (t : K) (ht : ‖t‖ < 1) :
    O⟦X⟧ →+* K where
  toFun f := ∑' n, i (coeff n f) * t ^ n
  map_one' := by
    have := tsum_coeff_C (1 : K) t
    rw [map_one, ← map_one (PowerSeries.map i)] at this
    simpa only [coeff_map] using this
  map_mul' f g := by
    have := tsum_coeff_mul (PowerSeries.map i f) (PowerSeries.map i g) t
      (by simpa only [coeff_map] using summable_norm_of_bounded (fun n => hi (coeff n f)) ht)
      (by simpa only [coeff_map] using summable_norm_of_bounded (fun n => hi (coeff n g)) ht)
    rw [← map_mul] at this
    simpa only [coeff_map] using this
  map_zero' := by simp
  map_add' f g := by
    rw [← (summable_norm_of_bounded (fun n => hi (coeff n f)) ht).of_norm.tsum_add
      (summable_norm_of_bounded (fun n => hi (coeff n g)) ht).of_norm]
    simp only [map_add, add_mul]

variable (i : O →+* K) (hi : ∀ a, ‖i a‖ ≤ 1) (t : K) (ht : ‖t‖ < 1)

theorem evalDisc_apply (f : O⟦X⟧) : evalDisc i hi t ht f = ∑' n, i (coeff n f) * t ^ n := rfl

@[simp] theorem evalDisc_C (a : O) : evalDisc i hi t ht (C a) = i a := by
  rw [evalDisc_apply, tsum_eq_single 0]
  · simp
  · intro n hn
    simp [coeff_C, hn]

@[simp] theorem evalDisc_X : evalDisc i hi t ht X = t := by
  rw [evalDisc_apply, tsum_eq_single 1]
  · simp
  · intro n hn
    simp [coeff_X, hn]

end Integral

section Bounded

def boundedSeries (F : Type*) [NormedField F] [IsUltrametricDist F] : Subring F⟦X⟧ where
  carrier := {f | ∃ B : ℝ, ∀ n, ‖coeff n f‖ ≤ B}
  mul_mem' := by
    rintro f g ⟨A, hA⟩ ⟨B, hB⟩
    have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
    refine ⟨A * B, fun n => ?_⟩
    rw [coeff_mul]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hA0 hB0)
      fun p _ => ?_
    rw [norm_mul]
    exact mul_le_mul (hA _) (hB _) (norm_nonneg _) hA0
  one_mem' := ⟨1, fun n => by rw [coeff_one]; split_ifs <;> simp⟩
  add_mem' := by
    rintro f g ⟨A, hA⟩ ⟨B, hB⟩
    refine ⟨A + B, fun n => ?_⟩
    rw [map_add]
    exact (norm_add_le _ _).trans (add_le_add (hA n) (hB n))
  zero_mem' := ⟨0, fun n => by simp⟩
  neg_mem' := by
    rintro f ⟨A, hA⟩
    exact ⟨A, fun n => by simpa using hA n⟩

variable {F : Type*} [NormedField F] [IsUltrametricDist F]

theorem mem_boundedSeries {f : F⟦X⟧} :
    f ∈ boundedSeries F ↔ ∃ B : ℝ, ∀ n, ‖coeff n f‖ ≤ B := by exact Iff.rfl

theorem C_mem_boundedSeries (c : F) : (C c : F⟦X⟧) ∈ boundedSeries F := by
  refine mem_boundedSeries.2 ⟨‖c‖, fun n => ?_⟩
  rw [coeff_C]
  split_ifs <;> simp

theorem X_mem_boundedSeries : (X : F⟦X⟧) ∈ boundedSeries F := by
  refine mem_boundedSeries.2 ⟨1, fun n => ?_⟩
  rw [coeff_X]
  split_ifs <;> simp

theorem summable_norm_boundedSeries (f : boundedSeries F) {π : F} (hπ : ‖π‖ < 1) :
    Summable fun n => ‖coeff n (f : F⟦X⟧) * π ^ n‖ := by
  obtain ⟨B, hB⟩ := mem_boundedSeries.1 f.2
  exact summable_norm_of_bounded hB hπ

variable [CompleteSpace F]

noncomputable def evalBounded (π : F) (hπ : ‖π‖ < 1) : boundedSeries F →+* F where
  toFun f := ∑' n, coeff n (f : F⟦X⟧) * π ^ n
  map_one' := by simpa only [map_one, OneMemClass.coe_one] using tsum_coeff_C (1 : F) π
  map_mul' f g := tsum_coeff_mul (f : F⟦X⟧) g π (summable_norm_boundedSeries f hπ)
    (summable_norm_boundedSeries g hπ)
  map_zero' := by simp
  map_add' f g := by
    rw [← (summable_norm_boundedSeries f hπ).of_norm.tsum_add
      (summable_norm_boundedSeries g hπ).of_norm]
    simp only [Subring.coe_add, map_add, add_mul]

variable (π : F) (hπ : ‖π‖ < 1)

theorem evalBounded_apply (f : boundedSeries F) :
    evalBounded π hπ f = ∑' n, coeff n (f : F⟦X⟧) * π ^ n := rfl

@[simp] theorem evalBounded_C (c : F) :
    evalBounded π hπ ⟨C c, C_mem_boundedSeries c⟩ = c := by
  rw [evalBounded_apply]
  exact tsum_coeff_C c π

@[simp] theorem evalBounded_X : evalBounded π hπ ⟨X, X_mem_boundedSeries⟩ = π := by
  rw [evalBounded_apply]
  exact tsum_coeff_X π

end Bounded

end GlobalTheory.BoundedPowerSeriesDisc
end

