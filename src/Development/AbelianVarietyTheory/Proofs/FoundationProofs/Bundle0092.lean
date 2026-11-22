import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0078
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0074
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0042
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSymplecticBasisToMatrixOffDiagDvd
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0053

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardPermExistsStableSubsetLe
section
open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.StableSubset

open Finset Equiv

theorem mem_iff_of_map_eq {N : ℕ} (σ : Perm (Fin N)) (A : Finset (Fin N))
    (h : A.map σ.toEmbedding = A) (x : Fin N) : σ x ∈ A ↔ x ∈ A := by
  conv_lhs => rw [← h]
  exact Finset.mem_map' σ.toEmbedding

theorem map_eq_of_mem_iff {N : ℕ} (σ : Perm (Fin N)) (A : Finset (Fin N))
    (h : ∀ x, x ∈ A → σ x ∈ A) : A.map σ.toEmbedding = A := by
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 hy
    exact h x hx
  · simp

theorem card_stab_le {N : ℕ} (A : Finset (Fin N)) :
    (univ.filter fun σ : Perm (Fin N) => A.map σ.toEmbedding = A).card ≤
      A.card.factorial * (N - A.card).factorial := by
  have hsub : (univ.filter fun σ : Perm (Fin N) => A.map σ.toEmbedding = A) ⊆
      (univ : Finset (Perm {x // x ∈ A} × Perm {x // x ∉ A})).image
        (fun p => Perm.subtypeCongr p.1 p.2) := by
    intro σ hσ
    have h := mem_iff_of_map_eq σ A (Finset.mem_filter.1 hσ).2
    refine Finset.mem_image.2 ⟨(σ.subtypePerm h, σ.subtypePerm (fun x => not_congr (h x))),
      Finset.mem_univ _, ?_⟩
    ext x
    by_cases hx : x ∈ A
    · simp [Perm.subtypeCongr.left_apply _ _ hx]
    · simp [Perm.subtypeCongr.right_apply _ _ hx]
  refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
  simp [Fintype.card_perm, Fintype.card_subtype_compl]

theorem card_fix_ge {N : ℕ} (A : Finset (Fin N)) (h0 : 0 < A.card) (hN : A.card < N) :
    A.card.factorial * (N - A.card).factorial ≤
      4 * (univ.filter fun σ : Perm (Fin N) => A.map σ.toEmbedding = A ∧
        (∃ i ∈ A, σ i = i) ∧ ∃ j ∉ A, σ j = j).card := by
  have c1 : Fintype.card {x // x ∈ A} = A.card := by simp
  have c2 : Fintype.card {x // x ∉ A} = N - A.card := by simp [Fintype.card_subtype_compl]
  have h1 := GlobalTheory.T.factorial_le_two_mul_card_perm_with_fixedPoint {x // x ∈ A} (Fintype.card_pos_iff.1 (by omega))
  have h2 := GlobalTheory.T.factorial_le_two_mul_card_perm_with_fixedPoint {x // x ∉ A} (Fintype.card_pos_iff.1 (by omega))
  rw [c1] at h1
  rw [c2] at h2
  refine (Nat.mul_le_mul h1 h2).trans ?_
  rw [mul_mul_mul_comm, ← Finset.card_product]
  refine Nat.mul_le_mul le_rfl ?_
  refine Finset.card_le_card_of_injOn (fun p => Perm.subtypeCongr p.1 p.2) ?_ ?_
  · rintro ⟨e, f⟩ hp
    simp only [Finset.coe_product, Set.mem_prod, Finset.coe_filter, Finset.mem_univ, true_and,
      Set.mem_setOf_eq] at hp ⊢
    obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := hp
    refine ⟨map_eq_of_mem_iff _ _ ?_, ⟨i, i.2, ?_⟩, ⟨j, j.2, ?_⟩⟩
    · intro x hx
      rw [Perm.subtypeCongr.left_apply _ _ hx]
      exact (e ⟨x, hx⟩).2
    · rw [Perm.subtypeCongr.left_apply_subtype, hi]
    · rw [Perm.subtypeCongr.right_apply_subtype, hj]
  · rintro ⟨e, f⟩ - ⟨e', f'⟩ - h
    have h' : Perm.subtypeCongr e f = Perm.subtypeCongr e' f' := h
    refine Prod.ext ?_ ?_
    · ext x : 2
      have := congrArg (fun s : Perm (Fin N) => s x) h'
      simpa only [Perm.subtypeCongr.left_apply_subtype] using this
    · ext x : 2
      have := congrArg (fun s : Perm (Fin N) => s x) h'
      simpa only [Perm.subtypeCongr.right_apply_subtype] using this

noncomputable def wt {N : ℕ} (A : Finset (Fin N)) (σ : Perm (Fin N)) : ℕ :=
  if A.map σ.toEmbedding = A then
    (if (∃ i ∈ A, σ i = i) ∧ ∃ j ∉ A, σ j = j then 4 else 8) else 0

theorem sum_wt_le {N : ℕ} (A : Finset (Fin N)) (h0 : 0 < A.card) (hN : A.card < N) :
    ∑ σ, wt A σ ≤ 7 * (A.card.factorial * (N - A.card).factorial) := by
  have h1 := card_stab_le A
  have h2 := card_fix_ge A h0 hN
  have h3 : ∑ σ, wt A σ + 4 * (univ.filter fun σ : Perm (Fin N) => A.map σ.toEmbedding = A ∧
        (∃ i ∈ A, σ i = i) ∧ ∃ j ∉ A, σ j = j).card =
      8 * (univ.filter fun σ : Perm (Fin N) => A.map σ.toEmbedding = A).card := by
    rw [Finset.card_filter, Finset.card_filter, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    unfold wt
    by_cases ha : A.map σ.toEmbedding = A <;>
      by_cases hb : (∃ i ∈ A, σ i = i) ∧ ∃ j ∉ A, σ j = j <;> simp only [ha, hb] <;> simp
  omega

theorem four_le_wt {N : ℕ} (A : Finset (Fin N)) (σ : Perm (Fin N))
    (h : A.map σ.toEmbedding = A) : 4 ≤ wt A σ := by
  unfold wt
  rw [if_pos h]
  split_ifs <;> omega

theorem eight_le_sum_wt {N a : ℕ} (σ : Perm (Fin N)) (A : Finset (Fin N)) (hA : A.card = a)
    (h : A.map σ.toEmbedding = A) : 8 ≤ ∑ B ∈ powersetCard a (univ : Finset (Fin N)), wt B σ := by
  have hAm : A ∈ powersetCard a (univ : Finset (Fin N)) := by simp [hA]
  by_cases hb : (∃ i ∈ A, σ i = i) ∧ ∃ j ∉ A, σ j = j
  · obtain ⟨⟨i, hi, hσi⟩, ⟨j, hj, hσj⟩⟩ := hb
    set B := insert j (A.erase i) with hB
    have hjB : j ∈ B := Finset.mem_insert_self _ _
    have hne : A ≠ B := fun e => hj (e ▸ hjB)
    have hBc : B.card = a := by
      rw [hB, Finset.card_insert_of_notMem (fun hh => hj (Finset.mem_of_mem_erase hh)),
        Finset.card_erase_add_one hi, hA]
    have hBm : B ∈ powersetCard a (univ : Finset (Fin N)) := by simp [hBc]
    have hBs : B.map σ.toEmbedding = B := by
      apply map_eq_of_mem_iff
      intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · rw [hσj]; exact hjB
      · refine Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨?_, ?_⟩)
        · intro e
          exact (Finset.mem_erase.1 hx).1 (σ.injective (e.trans hσi.symm))
        · exact (mem_iff_of_map_eq σ A h x).2 (Finset.mem_erase.1 hx).2
    have hs : ({A, B} : Finset _) ⊆ powersetCard a (univ : Finset (Fin N)) := by
      intro C hC
      rcases Finset.mem_insert.1 hC with rfl | hC
      · exact hAm
      · rw [Finset.mem_singleton.1 hC]; exact hBm
    have := Finset.sum_le_sum_of_subset (f := fun B => wt B σ) hs
    rw [Finset.sum_pair hne] at this
    have h1 := four_le_wt A σ h
    have h2 := four_le_wt B σ hBs
    omega
  · have : wt A σ = 8 := by unfold wt; rw [if_pos h, if_neg hb]
    rw [← this]
    exact Finset.single_le_sum (f := fun B => wt B σ) (fun _ _ => Nat.zero_le _) hAm

theorem card_exists_stable_subset_le : ∀ N a : ℕ, 0 < a → a < N →
    8 * (Finset.univ.filter fun σ : Equiv.Perm (Fin N) =>
      ∃ A : Finset (Fin N), A.card = a ∧ A.map σ.toEmbedding = A).card ≤ 7 * N.factorial := by
  intro N a h0 hN
  calc _ ≤ ∑ σ : Perm (Fin N), ∑ B ∈ powersetCard a (univ : Finset (Fin N)), wt B σ := by
        rw [Finset.card_filter, Finset.mul_sum]
        refine Finset.sum_le_sum fun σ _ => ?_
        split_ifs with h
        · obtain ⟨A, hA, h⟩ := h
          exact eight_le_sum_wt σ A hA h
        · simp
    _ = ∑ B ∈ powersetCard a (univ : Finset (Fin N)), ∑ σ : Perm (Fin N), wt B σ :=
        Finset.sum_comm
    _ ≤ ∑ B ∈ powersetCard a (univ : Finset (Fin N)),
          7 * (a.factorial * (N - a).factorial) := by
        refine Finset.sum_le_sum fun B hB => ?_
        have hB' : B.card = a := (Finset.mem_powersetCard.1 hB).2
        have := sum_wt_le B (by omega) (by omega)
        rwa [hB'] at this
    _ = 7 * N.factorial := by
        rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
          smul_eq_mul, ← Nat.choose_mul_factorial_mul_factorial hN.le]
        ring

end GlobalTheory.StableSubset
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharacterAverageTwistedSpanEqZeroStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_average_twistedSpan_eq_zero : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∀ (H : Set G) (θ : G → ℂ), Datum H θ → ∀ u ∈ aug π H θ, ∃ R : Finset G, (1 : G) ∈ R ∧ (∀ j ∈ R, j ∈ H) ∧ ∑ j ∈ R, (θ j)⁻¹ • π j u = 0 := by
  first | exact @GlobalTheory.PsType.aug_avg_zero | exact GlobalTheory.PsType.aug_avg_zero | (intros; apply GlobalTheory.PsType.aug_avg_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CocycleIsCoboundaryOfNegCentralElementStatement
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocycle_isCoboundary_of_neg_central_element : ∀ (G : Type) [Group G] (R : Type) [CommRing R] (V : Type) [AddCommGroup V] [Module R V] (ρ : G → V →ₗ[R] V), (∀ g h v, ρ (g * h) v = ρ h (ρ g v)) → (∀ v, ρ 1 v = v) → IsUnit (2 : R) → ∀ (S : Submodule R V), (∀ g, ∀ v ∈ S, ρ g v ∈ S) → ∀ (Δ : Subgroup G), Δ.Normal → (∀ δ ∈ Δ, ∀ v, ρ δ v = v) → ∀ c : G, (∀ v ∈ S, ρ c v = -v) → (∀ g, c * g * c⁻¹ * g⁻¹ ∈ Δ) → ∀ z : G → V, (∀ g, z g ∈ S) → (∀ g h, z (g * h) = ρ h (z g) + z h) → (∀ δ ∈ Δ, z δ = 0) → ∃ p ∈ S, ∀ g, z g = ρ g p - p := by
  first | exact @GlobalTheory.KZ.H3.cocycle_isCoboundary_of_neg_central | exact GlobalTheory.KZ.H3.cocycle_isCoboundary_of_neg_central | (intros; apply GlobalTheory.KZ.H3.cocycle_isCoboundary_of_neg_central <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompactSubgroupSmoothCharacterDatumMonotoneStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactSubgroupSmoothCharacterDatum_monotone : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ) (r : ℕ) (ϖ : k), (∀ i, IsSmoothChar (ψ i)) → ϖ ≠ 0 → valuation k ϖ < 1 → (∀ x : k, valuation k x < 1 → valuation k x ≤ valuation k ϖ) → (∀ m, Datum (strip ψ r ϖ m) (fun _ => 1)) ∧ Monotone (strip ψ r ϖ) := by
  first | exact @GlobalTheory.StripGrp.strip_datum_monotone | exact GlobalTheory.StripGrp.strip_datum_monotone | (intros; apply GlobalTheory.StripGrp.strip_datum_monotone <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompletedLaurentIsDVRStatementStatement
section
open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completed_laurent_isDVR_statement : ∀ (p : ℕ) [Fact p.Prime], ∃ _ : IsDomain (O0 p), IsDiscreteValuationRing (O0 p) ∧ Irreducible (p : O0 p) := by
  first | exact @GlobalTheory.K5.completed_laurent_isDVR | exact GlobalTheory.K5.completed_laurent_isDVR | (intros; apply GlobalTheory.K5.completed_laurent_isDVR <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConstOfSlTwoIntInvariantBoundedUpperHalfPlaneStatement
section
open scoped MatrixGroups
open GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.const_of_slTwoInt_invariant_bounded_upperHalfPlane : ∀ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs → (∀ γ : SL(2, ℤ), ∀ z ∈ Hs, φ (mob (ofSL γ) z) = φ z) → (∃ M t : ℝ, ∀ z ∈ Hs, t < z.im → ‖φ z‖ ≤ M) → ∃ c : ℂ, ∀ z ∈ Hs, φ z = c := by
  first | exact @GlobalTheory.KZ.LevelOne.const_of_invariant_bounded | exact GlobalTheory.KZ.LevelOne.const_of_invariant_bounded | (intros; apply GlobalTheory.KZ.LevelOne.const_of_invariant_bounded <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspidalOfEichlerPeriodSubConjMemCoboundaries
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices.Par

noncomputable def lam (w : ℕ) (x y : ℂ) : ℂ[X] →ₗ[ℂ] ℂ :=
  ∑ i ∈ Finset.range (w + 1), (x ^ i * y ^ (w - i)) • lcoeff ℂ i

lemma lam_apply (w : ℕ) (x y : ℂ) (p : ℂ[X]) :
    lam w x y p = ∑ i ∈ Finset.range (w + 1), p.coeff i * (x ^ i * y ^ (w - i)) := by
  simp [lam, LinearMap.sum_apply, mul_comm]

lemma lam_eq (w : ℕ) (x y : ℂ) (p : ℂ[X]) :
    lam w x y p = MvPolynomial.eval ![x, y] (p.homogenize w) := by
  rw [lam_apply, Polynomial.homogenize, map_sum, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (by simp)]
  simp

lemma lam_mul (m n : ℕ) (x y : ℂ) (p q : ℂ[X]) (hp : p.natDegree ≤ m) (hq : q.natDegree ≤ n) :
    lam (m + n) x y (p * q) = lam m x y p * lam n x y q := by
  simp only [lam_eq, homogenize_mul p q hp hq, map_mul]

lemma natDegree_lin_pow (a b : ℂ) (i : ℕ) : ((C a * X + C b) ^ i).natDegree ≤ i := by
  refine natDegree_pow_le.trans ?_
  have : (C a * X + C b).natDegree ≤ 1 := natDegree_linear_le
  simpa using Nat.mul_le_mul_left i this

lemma lam_lin_pow (a b x y : ℂ) (i : ℕ) : lam i x y ((C a * X + C b) ^ i) = (a * x + b * y) ^ i := by
  induction i with
  | zero => simp [lam_apply]
  | succ i ih =>
    rw [pow_succ, lam_mul i 1 x y _ _ (natDegree_lin_pow a b i) natDegree_linear_le, ih, pow_succ]
    congr 1
    simp [lam_apply, Finset.sum_range_succ, coeff_X, coeff_C]
    ring

lemma polySlash_sum (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) :
    slP w g p = ∑ i ∈ Finset.range (w + 1), p.coeff i •
      ((C ((g 0 0 : ℤ) : ℂ) * X + C ((g 0 1 : ℤ) : ℂ)) ^ i *
        (C ((g 1 0 : ℤ) : ℂ) * X + C ((g 1 1 : ℤ) : ℂ)) ^ (w - i)) := by
  simp only [slP, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply, lcoeff_apply]

lemma lam_slP (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (x y : ℂ) (p : ℂ[X]) :
    lam w x y (slP w g p) =
      lam w ((g 0 0 : ℤ) * x + (g 0 1 : ℤ) * y) ((g 1 0 : ℤ) * x + (g 1 1 : ℤ) * y) p := by
  rw [polySlash_sum, map_sum, lam_apply w _ _ p]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ w := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [map_smul, smul_eq_mul]
  congr 1
  have := lam_mul i (w - i) x y _ _ (natDegree_lin_pow ((g 0 0 : ℤ) : ℂ) ((g 0 1 : ℤ) : ℂ) i)
    (natDegree_lin_pow ((g 1 0 : ℤ) : ℂ) ((g 1 1 : ℤ) : ℂ) (w - i))
  rw [Nat.add_sub_cancel' hi', lam_lin_pow, lam_lin_pow] at this
  exact this

lemma lam_one_zero (w : ℕ) (p : ℂ[X]) : lam w 1 0 p = p.coeff w := by
  rw [lam_apply, Finset.sum_eq_single w]
  · simp
  · intro b hb hbw
    have : w - b ≠ 0 := by have := Finset.mem_range.mp hb; omega
    simp [this]
  · simp

lemma lam_conj (w : ℕ) (a c : ℤ) (p : ℂ[X]) :
    lam w a c (p.map (starRingEnd ℂ)) = starRingEnd ℂ (lam w a c p) := by
  simp [lam_apply, map_sum]

lemma coeff_eichler (w : ℕ) (f : ℍ → ℂ) (τ : ℍ) :
    (eichler w f τ).coeff w = ∫ t in (0 : ℝ)..1,
      (f ∘ ofComplex) (Complex.I + t * ((τ : ℂ) - Complex.I)) * ((τ : ℂ) - Complex.I) := by
  rw [eichler, finsetSum_coeff, Finset.sum_eq_single w]
  · rw [coeff_C_mul_X_pow]
    simp
  · intro b _ hbw
    rw [coeff_C_mul_X_pow, if_neg hbw.symm]
  · simp

lemma coeff_eichler_period (w n : ℕ) (hn : 0 < n) (g : ℍ → ℂ) (hper : Function.Periodic (g ∘ ofComplex) (n : ℝ))
    (hhol : MDiff g) (hbdd : IsBoundedAtImInfty g) :
    (eichler w g (((n : ℤ) : ℝ) +ᵥ UpperHalfPlane.I)).coeff w = n * valueAtInfty g := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h0 := qExpansion_coeff_zero hn' (analyticAt_cuspFunction_zero hn' hper hhol hbdd) hper
  rw [qExpansion_coeff_eq_intervalIntegral hn' hper hhol hbdd 0 one_pos] at h0
  rw [coeff_eichler, ← h0]
  have hτ : (((((n : ℤ) : ℝ) +ᵥ UpperHalfPlane.I : ℍ) : ℂ) - Complex.I) = (n : ℝ) := by
    simp
  rw [hτ, intervalIntegral.integral_mul_const]
  have h1 := intervalIntegral.smul_integral_comp_mul_right (a := 0) (b := 1)
    (fun u : ℝ => (g ∘ ofComplex) (Complex.I + u)) (n : ℝ)
  simp only [zero_mul, one_mul, Complex.real_smul, Complex.ofReal_mul] at h1
  rw [mul_comm, h1]
  have hn'' : ((n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [← mul_assoc, show (n : ℂ) * (1 / ((n : ℝ) : ℂ)) = 1 from by
    rw [Complex.ofReal_natCast] at hn'' ⊢; field_simp, one_mul]
  refine intervalIntegral.integral_congr fun u _ => ?_
  have hu : 0 < (Complex.I + (u : ℂ)).im := by simp
  simp only [Function.comp_apply, ofComplex_apply_of_im_pos hu, pow_zero, div_one, one_mul]
  congr 1
  ext
  simp [add_comm]

lemma periodic_slash {Γ : Subgroup SL(2, ℤ)} {k : ℤ} (f : ModularForm Γ k) (σ γ : SL(2, ℤ)) (n : ℤ)
    (hγ : γ ∈ Γ) (h : γ * σ = σ * ModularGroup.T ^ n) :
    Function.Periodic (((f : ℍ → ℂ) ∣[k] σ) ∘ ofComplex) ((n : ℝ) : ℂ) := by
  have h1 : (f : ℍ → ℂ) ∣[k] γ = f := by
    rw [ModularForm.SL_slash]
    exact SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hγ)
  have h2 : ((f : ℍ → ℂ) ∣[k] σ) ∣[k] (ModularGroup.T ^ n) = (f : ℍ → ℂ) ∣[k] σ := by
    rw [← SlashAction.slash_mul, ← h, SlashAction.slash_mul, h1]
  have h3 : ∀ z : ℍ, ((f : ℍ → ℂ) ∣[k] σ) ((n : ℝ) +ᵥ z) = ((f : ℍ → ℂ) ∣[k] σ) z := by
    intro z
    have := (ModularForm.slash_action_eq'_iff k _ (ModularGroup.T ^ n) z).mp (congrFun h2 z)
    rw [modular_T_zpow_smul, ModularGroup.coe_T_zpow] at this
    simpa using this
  intro w
  by_cases! hw : 0 < w.im
  · have : 0 < (w + (n : ℝ)).im := by simp [hw]
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos this, ofComplex_apply_of_im_pos hw]
    rw [← h3 ⟨w, hw⟩]
    refine congrArg _ (UpperHalfPlane.ext ?_)
    simp [add_comm]
  · have : (w + (n : ℝ)).im ≤ 0 := by simpa using hw
    simp only [Function.comp_apply, ofComplex_apply_of_im_nonpos this, ofComplex_apply_of_im_nonpos hw]

lemma lambda_slParabolic (w : ℕ) (σ γ : SL(2, ℤ)) (n : ℤ) (h : γ * σ = σ * ModularGroup.T ^ n) (p : ℂ[X]) :
    lam w (mat σ 0 0 : ℤ) (mat σ 1 0 : ℤ) (slP w (mat γ) p) = lam w (mat σ 0 0 : ℤ) (mat σ 1 0 : ℤ) p := by
  have h' : mat γ * mat σ = mat σ * !![1, n; 0, 1] := by
    rw [← ModularGroup.coe_T_zpow]
    exact congrArg Subtype.val h
  have h0 := congrFun (congrFun h' 0) 0
  have h1 := congrFun (congrFun h' 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_one, mul_zero, add_zero] at h0 h1
  rw [lam_slP]
  congr 2
  · exact_mod_cast h0
  · exact_mod_cast h1

lemma lam_per {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {k : ℕ} (hk : 2 ≤ k) (f : ModularForm Γ (k : ℤ))
    (σ : SL(2, ℤ)) (γ : Γ) (n : ℕ) (hn : 0 < n) (h : γ * σ = σ * ModularGroup.T ^ (n : ℤ)) :
    lam (k - 2) (mat σ 0 0 : ℤ) (mat σ 1 0 : ℤ) (per Γ (k - 2) f γ) =
      n * valueAtInfty ((f : ℍ → ℂ) ∣[(k : ℤ)] σ) := by
  obtain ⟨c, hc⟩ := GlobalTheory.T.eichlerIntegralFromI_slash_change_of_variables k hk f f.holo' σ
  have key : ∀ τ : ℍ, lam (k - 2) (mat σ 0 0 : ℤ) (mat σ 1 0 : ℤ) (eichler (k - 2) f (σ • τ)) =
      (eichler (k - 2) ((f : ℍ → ℂ) ∣[(k : ℤ)] σ) τ).coeff (k - 2) + c.coeff (k - 2) := by
    intro τ
    rw [← coeff_add, ← hc τ, ← lam_one_zero, lam_slP]
    simp
  rw [(GlobalTheory.T.eichlerPeriodCocycle_mem_cocycles_and_eq Γ k hk f).2 γ (σ • UpperHalfPlane.I), map_sub, lambda_slParabolic _ σ γ n h, ← mul_smul, h,
    mul_smul, key, key, modular_T_zpow_smul, coeff_eichler_period _ n hn, coeff_eichler]
  · simp
  · simpa using periodic_slash f σ γ n γ.2 h
  · rw [ModularForm.SL_slash]
    exact MDifferentiable.slash f.holo' _ _
  · exact ModularFormClass.bdd_at_infty_slash f σ

end GlobalTheory.HeckeFamilyMatrices.Par

open GlobalTheory.HeckeFamilyMatrices.Par in

theorem GlobalTheory.HeckeFamilyMatrices.cuspidal_of_per_sub_cj_mem : ∀ (N : ℕ) (Γ : Subgroup SL(2, ℤ)) (k : ℕ), 5 ≤ N → Γ ≤ CongruenceSubgroup.Gamma1 N → Γ.FiniteIndex → 3 ≤ k → ∀ (f : ModularForm Γ (k : ℤ)) (h : CuspForm Γ (k : ℤ)), per Γ (k - 2) ⇑f - cj (per Γ (k - 2) ⇑h) ∈ B1 Γ (k - 2) → ∃ f' : CuspForm Γ (k : ℤ), ⇑f' = ⇑f := by
  intro N Γ k _ _ hΓ hk f h hB
  have hk2 : 2 ≤ k := by omega
  obtain ⟨p, hp⟩ := hB
  have hall : ∀ σ : SL(2, ℤ), IsZeroAtImInfty ((f : ℍ → ℂ) ∣[(k : ℤ)] σ) := by
    intro σ
    obtain ⟨n, hn, -, hmem⟩ := Subgroup.exists_pow_mem_of_index_ne_zero hΓ.index_ne_zero
      (σ * ModularGroup.T * σ⁻¹)
    have hγ : ((⟨_, hmem⟩ : Γ) : SL(2, ℤ)) * σ = σ * ModularGroup.T ^ (n : ℤ) := by
      simp [conj_pow]
    set γ : Γ := ⟨_, hmem⟩
    have hf := lam_per hk2 f σ γ n hn hγ
    have hh := lam_per hk2 (ModularFormClass.modularForm h) σ γ n hn hγ
    have hcoe : ((ModularFormClass.modularForm h : ModularForm Γ (k : ℤ)) : ℍ → ℂ) = h := rfl
    rw [hcoe, (CuspFormClass.zero_at_infty_slash h σ).valueAtInfty_eq_zero, mul_zero] at hh
    have h1 := congrArg (lam (k - 2) (mat σ 0 0 : ℤ) (mat σ 1 0 : ℤ)) (congrFun hp γ)
    simp only [LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply, map_sub,
      Pi.sub_apply, cj] at h1
    rw [lambda_slParabolic _ σ γ n hγ, sub_self, lam_conj, hh, hf, map_zero, sub_zero] at h1
    have hv : valueAtInfty ((f : ℍ → ℂ) ∣[(k : ℤ)] σ) = 0 :=
      (mul_eq_zero.mp h1.symm).resolve_left (by exact_mod_cast hn.ne')
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hper : Function.Periodic (((f : ℍ → ℂ) ∣[(k : ℤ)] σ) ∘ ofComplex) ((n : ℝ) : ℂ) := by
      simpa using periodic_slash f σ γ n γ.2 hγ
    have hhol : MDiff ((f : ℍ → ℂ) ∣[(k : ℤ)] σ) := by
      rw [ModularForm.SL_slash]
      exact MDifferentiable.slash f.holo' _ _
    have han := analyticAt_cuspFunction_zero hn' hper hhol (ModularFormClass.bdd_at_infty_slash f σ)
    have h2 : (cuspFunction n ((f : ℍ → ℂ) ∣[(k : ℤ)] σ) ∘ fun τ : ℍ => Function.Periodic.qParam n τ : ℍ → ℂ) =
        (f : ℍ → ℂ) ∣[(k : ℤ)] σ := by
      funext τ
      exact eq_cuspFunction τ hn'.ne' hper
    have h3 := han.continuousAt.tendsto.comp (qParam_tendsto_atImInfty hn')
    rw [cuspFunction_apply_zero hn' han hper, hv, h2] at h3
    exact h3
  refine ⟨⟨f.toSlashInvariantForm, f.holo', ?_⟩, rfl⟩
  intro c hc
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
  rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
  intro γ _
  exact hall γ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagOneUnitConjLiftsSl2IntReductionMod
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem exists_redGL_eq {N : ℕ} (g : GL (Fin 2) (ZMod N))
    (hg : Matrix.det (g : Matrix (Fin 2) (Fin 2) (ZMod N)) = 1) : ∃ γ : SL(2, ℤ), redGL N γ = g := by
  obtain ⟨γ, hγ⟩ := GlobalTheory.specialLinearGroup_map_zmod_surjective (Fin 2) N ⟨(g : Matrix (Fin 2) (Fin 2) (ZMod N)), hg⟩
  refine ⟨γ, Units.ext ?_⟩
  show ((Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ) : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) = g
  rw [hγ]; rfl

theorem dg_conj_lift : ∀ (N : ℕ) [NeZero N] (u : (ZMod N)ˣ), (∀ γ : SL(2, ℤ), ∃ γ' : SL(2, ℤ), dg u * redGL N γ' = redGL N γ * dg u) ∧ ∀ γ' : SL(2, ℤ), ∃ γ : SL(2, ℤ), dg u * redGL N γ' = redGL N γ * dg u := by
  intro N _ u
  have hdet : ∀ γ : SL(2, ℤ), Matrix.det ((redGL N γ : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) = 1 := by
    intro γ
    exact (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ).2
  have hconj : ∀ (a g : GL (Fin 2) (ZMod N)), Matrix.det ((g : Matrix (Fin 2) (Fin 2) (ZMod N))) = 1 →
      Matrix.det (((a⁻¹ * g * a : GL (Fin 2) (ZMod N))) : Matrix (Fin 2) (Fin 2) (ZMod N)) = 1 := by
    intro a g hg
    simp only [Units.val_mul, Matrix.det_mul]
    rw [hg, mul_one, ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
  refine ⟨fun γ => ?_, fun γ' => ?_⟩
  · obtain ⟨γ', h⟩ := exists_redGL_eq _ (hconj (dg u) (redGL N γ) (hdet γ))
    refine ⟨γ', ?_⟩
    rw [h]; group
  · obtain ⟨γ, h⟩ := exists_redGL_eq _ (hconj (dg u)⁻¹ (redGL N γ') (hdet γ'))
    refine ⟨γ, ?_⟩
    rw [h]; group

end GlobalTheory.FN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiamondOperatorOfMatrixCompMul
section
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem isDia_mul {N l : ℕ} {d e : ℤ} {σ τ : SL(2, ℤ)} (hσ : IsDia N l d σ) (hτ : IsDia N l e τ) :
    IsDia N l (d * e) (σ * τ) := by
  obtain ⟨hσ0, hσ1⟩ := hσ
  obtain ⟨hτ0, hτ1⟩ := hτ
  have hσ0' : ((σ 1 0 : ℤ) : ZMod N) = 0 := by
    have := congrArg (ZMod.castHom (Dvd.intro l rfl : N ∣ N * l) (ZMod N)) hσ0
    simpa using this
  constructor
  · simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    push_cast
    rw [hσ0, hτ0]; ring
  · simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    push_cast
    rw [hσ0', hσ1, hτ1]; ring

theorem dia_mul : ∀ (N l : ℕ) (k d e : ℤ) (σ τ ρ : SL(2, ℤ)), 0 < N → GlobalTheory.Hk.IsDia N l d σ →
    GlobalTheory.Hk.IsDia N l e τ → GlobalTheory.Hk.IsDia N l (d * e) ρ → ∀ f : ModularForm (GlobalTheory.Hk.lev N l) k,
    GlobalTheory.Hk.dia k τ (GlobalTheory.Hk.dia k σ ⇑f) = GlobalTheory.Hk.dia k ρ ⇑f := by
  intro N l k d e σ τ ρ hN hσ hτ hρ f
  have h := GlobalTheory.T.diamondOperatorOfMatrix_congr N l k (d * e) (σ * τ) ρ hN (isDia_mul hσ hτ) hρ f
  rw [← h]
  simp only [dia]
  rw [SlashAction.slash_mul]

end GlobalTheory.Hk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerPeriodPolynomialLimitAtCuspStatement
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eichlerPeriodPolynomial_limit_at_cusp : ∀ (k : ℕ) (f h : ℍ → ℂ) (p : ℂ[X]) (σ : SL(2, ℤ)) (Cf cf Ch ch : ℝ), 2 ≤ k → 0 < cf → 0 < ch → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f ∣[(k : ℤ)] σ) → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (h ∣[(k : ℤ)] σ) → (∀ τ : ℍ, 1 ≤ τ.im → ‖(f ∣[(k : ℤ)] σ) τ‖ ≤ Cf * Real.exp (-cf * τ.im)) → (∀ τ : ℍ, 1 ≤ τ.im → ‖(h ∣[(k : ℤ)] σ) τ‖ ≤ Ch * Real.exp (-ch * τ.im)) → p ∈ degreeLT ℂ (k - 1) → ∃ (Q : ℂ[X]) (C' c : ℝ), Q ∈ degreeLT ℂ (k - 2 + 1) ∧ 0 < c ∧ ∀ τ : ℍ, 1 ≤ τ.im → ∀ j ≤ k - 2, ‖(slP (k - 2) (mat σ) (eichler (k - 2) f (σ • τ) - (eichler (k - 2) h (σ • τ)).map (starRingEnd ℂ) - p) - Q).coeff j‖ ≤ C' * Real.exp (-c * τ.im) * (1 + ‖(τ : ℂ)‖) ^ (k - 2) := by
  first | exact @GlobalTheory.EichlerLimit.polySlash_eichler_limit | exact GlobalTheory.EichlerLimit.polySlash_eichler_limit | (intros; apply GlobalTheory.EichlerLimit.polySlash_eichler_limit <;> assumption)
end

