import Formalism.TruncatedSeriesCounting.RamifiedValuationInequality
import Formalism.WindowSums.PowerSeriesRelationList
import Formalism.TruncatedSeriesCounting.LemmaDetPoly
import Formalism.CharacterColumnKernels.IdempotentNormalForms.LengthQuotSmulRangeFree

-- bundled from Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.LemmaGVal
section
namespace Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains

open Finset

private lemma sum_shift_val (ℓ : ℕ) (j₀ : ℤ) (T : Finset ℤ) :
    ∑ j ∈ T, padicValInt ℓ (j₀ - j) = ∑ i ∈ T.image (fun j => j₀ - j), padicValInt ℓ i := by
  rw [Finset.sum_image]
  intro a _ b _ h
  simp only at h
  omega

theorem g_coeff_valuation_statement : LemmaGVal := by
  intro ℓ _ h η S b a S₂ hb hbS hS₂ j₀ hj₀
  rw [Finset.mem_Icc] at hj₀
  obtain ⟨hj1, hj2⟩ := hj₀
  have hℓ : (2 : ℝ) ≤ ℓ := by exact_mod_cast (Fact.out : ℓ.Prime).two_le
  have hmem : ∀ j ∈ S₂, ((b : ℤ) + 1 ≤ j ∧ j ≤ (b : ℤ) + S + a) ∨
      (1 - (η : ℤ) ≤ j ∧ j ≤ (η : ℤ) + a) := by
    intro j hj
    have := hS₂ hj
    simpa only [Finset.mem_union, Finset.mem_Icc] using this
  set T₁ : Finset ℤ := (Finset.Icc ((b : ℤ) - a + 1) b).erase j₀ ∪
    S₂.filter (fun j => (b : ℤ) < j) with hT₁
  set T₂ : Finset ℤ := S₂.filter (fun j => ¬ (b : ℤ) < j) with hT₂
  have hsplit : (∑ j ∈ (Finset.Icc ((b : ℤ) - a + 1) (b : ℤ)).erase j₀, padicValInt ℓ (j₀ - j)) +
      ∑ j ∈ S₂, padicValInt ℓ (j₀ - j) =
      ∑ j ∈ T₁, padicValInt ℓ (j₀ - j) + ∑ j ∈ T₂, padicValInt ℓ (j₀ - j) := by
    rw [← Finset.sum_filter_add_sum_filter_not S₂ (fun j => (b : ℤ) < j), ← add_assoc, hT₁,
      hT₂, Finset.sum_union]
    rw [Finset.disjoint_left]
    intro x hx hx'
    have h1 := (Finset.mem_Icc.mp (Finset.mem_of_mem_erase hx)).2
    have h2 := (Finset.mem_filter.mp hx').2
    omega
  rw [hsplit, sum_shift_val, sum_shift_val]
  have c1 : T₁.image (fun j => j₀ - j) ⊆
      Finset.Ico (j₀ - b - S - a) (j₀ - b - S - a + ((2 * a + S : ℕ) : ℤ)) := by
    intro i hi
    rw [Finset.mem_image] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    rw [Finset.mem_Ico]
    push_cast
    rw [hT₁, Finset.mem_union] at hj
    rcases hj with hj | hj
    · have := Finset.mem_Icc.mp (Finset.mem_of_mem_erase hj)
      omega
    · have h1 := (Finset.mem_filter.mp hj).2
      have h2 := hmem j (Finset.mem_filter.mp hj).1
      omega
  have c2 : (0 : ℤ) ∉ T₁.image (fun j => j₀ - j) := by
    intro hi
    rw [Finset.mem_image] at hi
    obtain ⟨j, hj, hj0⟩ := hi
    rw [hT₁, Finset.mem_union] at hj
    rcases hj with hj | hj
    · have := Finset.ne_of_mem_erase hj
      omega
    · have h1 := (Finset.mem_filter.mp hj).2
      omega
  have c3 : ∀ i ∈ T₁.image (fun j => j₀ - j), |i| ≤ ((2 * (h + η) : ℕ) : ℤ) := by
    intro i hi
    rw [Finset.mem_image] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    push_cast
    rw [hT₁, Finset.mem_union] at hj
    rw [abs_le]
    rcases hj with hj | hj
    · have := Finset.mem_Icc.mp (Finset.mem_of_mem_erase hj)
      constructor <;> omega
    · have h1 := (Finset.mem_filter.mp hj).2
      have h2 := hmem j (Finset.mem_filter.mp hj).1
      constructor <;> omega
  have d1 : T₂.image (fun j => j₀ - j) ⊆
      Finset.Ico (j₀ - η - a) (j₀ - η - a + ((2 * η + a : ℕ) : ℤ)) := by
    intro i hi
    rw [Finset.mem_image] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    rw [Finset.mem_Ico]
    push_cast
    have h1 := (Finset.mem_filter.mp hj).2
    have h2 := hmem j (Finset.mem_filter.mp hj).1
    omega
  have d2 : (0 : ℤ) ∉ T₂.image (fun j => j₀ - j) := by
    intro hi
    rw [Finset.mem_image] at hi
    obtain ⟨j, hj, hj0⟩ := hi
    have h1 := (Finset.mem_filter.mp hj).2
    have h2 := hmem j (Finset.mem_filter.mp hj).1
    omega
  have d3 : ∀ i ∈ T₂.image (fun j => j₀ - j), |i| ≤ ((2 * (h + η) : ℕ) : ℤ) := by
    intro i hi
    rw [Finset.mem_image] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    push_cast
    rw [abs_le]
    have h1 := (Finset.mem_filter.mp hj).2
    have h2 := hmem j (Finset.mem_filter.mp hj).1
    constructor <;> omega
  have w1 := Formalism.WindowSums.arc_WindowSum ℓ (j₀ - b - S - a) (2 * a + S) (2 * (h + η)) _ c1 c2 c3
  have w2 := Formalism.WindowSums.arc_WindowSum ℓ (j₀ - η - a) (2 * η + a) (2 * (h + η)) _ d1 d2 d3
  have hDpos : (1 : ℝ) ≤ ((2 * (h + η) : ℕ) : ℝ) := by
    have : 1 ≤ 2 * (h + η) := by omega
    exact_mod_cast this
  have hlog : 0 ≤ Real.logb ℓ ((2 * (h + η) : ℕ) : ℝ) := Real.logb_nonneg (by linarith) hDpos
  have hlam : lam ℓ (h + η) = Real.logb ℓ ((2 * (h + η) : ℕ) : ℝ) + 1 := by
    simp only [lam]
    push_cast
    ring_nf
  have hsum : ((2 * a + S : ℕ) : ℝ) / ((ℓ : ℝ) - 1) + ((2 * η + a : ℕ) : ℝ) / ((ℓ : ℝ) - 1) =
      (3 * (a : ℝ) + (S : ℝ) + 2 * (η : ℝ)) / ((ℓ : ℝ) - 1) := by
    rw [← add_div]
    push_cast
    ring_nf
  rw [hlam]
  push_cast at w1 w2 hlog hsum ⊢
  linarith

end Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains
end

-- bundled from Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.PropEta
section
open Formalism.NG Formalism.NG.QuotientPowerLengths Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities Module IsDiscreteValuationRing

noncomputable section

universe u v w

namespace Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities.EtaCongruenceSeparation

section
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X : Type*} [Finite X]
  {T : Subalgebra O (X → O)} {V : Type*} [AddCommGroup V] [Module (FractionRing O) V]
  [Module O V] [IsScalarTower O (FractionRing O) V] [FiniteDimensional (FractionRing O) V]
  {act : T →+* Module.End (FractionRing O) V}

lemma exists_sep (hs : ∀ x y : X, x ≠ y → ∃ f ∈ T, f x ≠ f y) (S : Set X) :
    ∃ u ∈ T, (∀ x ∈ S, u x = 0) ∧ ∀ y ∉ S, u y ≠ 0 := by
  classical
  have := Fintype.ofFinite X
  choose f hfT hf using hs
  let F : X → X → (X → O) := fun y x =>
    if h : y = x then 1 else f y x h - algebraMap O (X → O) (f y x h x)
  have hFT : ∀ y x, F y x ∈ T := by
    intro y x
    simp only [F]
    split_ifs with h
    · exact one_mem _
    · exact sub_mem (hfT y x h) (T.algebraMap_mem _)
  let e : X → (X → O) := fun y => ∏ x, F y x
  have heT : ∀ y, e y ∈ T := fun y => prod_mem fun x _ => hFT y x
  have he_self : ∀ y, e y y ≠ 0 := by
    intro y
    simp only [e, Finset.prod_apply]
    rw [Finset.prod_ne_zero_iff]
    intro x _
    simp only [F]
    split_ifs with h
    · simp
    · simp only [Pi.sub_apply, Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
      exact sub_ne_zero.mpr (fun h' => hf y x h h')
  have he_other : ∀ y z, y ≠ z → e y z = 0 := by
    intro y z hyz
    simp only [e, Finset.prod_apply]
    refine Finset.prod_eq_zero (Finset.mem_univ z) ?_
    simp only [F, dif_neg hyz, Pi.sub_apply, Pi.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply, sub_self]
  refine ⟨∑ y ∈ Finset.univ.filter (· ∉ S), e y, sum_mem fun y _ => heT y, ?_, ?_⟩
  · intro x hx
    rw [Finset.sum_apply]
    refine Finset.sum_eq_zero fun y hy => he_other y x ?_
    rintro rfl
    exact (Finset.mem_filter.mp hy).2 hx
  · intro y hy
    rw [Finset.sum_apply, Finset.sum_eq_single y]
    · exact he_self y
    · intro b _ hb
      exact he_other b y hb
    · intro h
      exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ y, hy⟩) h

lemma disj (hs : ∀ x y : X, x ≠ y → ∃ f ∈ T, f x ≠ f y) (S : Set X) :
    Disjoint (VS T act S) (VS T act Sᶜ) := by
  obtain ⟨u, hu, hu0, hu1⟩ := exists_sep hs S
  let g : Module.End (FractionRing O) V := act ⟨u, hu⟩
  have hV : ∀ x, Vx T act x ≤ Module.End.eigenspace g (algebraMap O (FractionRing O) (u x)) := by
    intro x v hv
    rw [Module.End.mem_eigenspace_iff]
    rw [mem_Vx.mp hv ⟨u, hu⟩, algebraMap_smul]
  have h1 : VS T act S ≤ Module.End.eigenspace g 0 := by
    refine iSup₂_le fun x hx => ?_
    have := hV x
    rwa [hu0 x hx, map_zero] at this
  have h2 : VS T act Sᶜ ≤ ⨆ μ ∈ ({0}ᶜ : Set (FractionRing O)), Module.End.eigenspace g μ := by
    refine iSup₂_le fun x hx => (hV x).trans ?_
    refine le_iSup₂ (f := fun μ (_ : μ ∈ ({0}ᶜ : Set (FractionRing O))) => Module.End.eigenspace g μ)
      _ ?_
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact (map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).mpr (hu1 x hx)
  exact ((Module.End.eigenspaces_iSupIndep g).disjoint_biSup (by simp)).mono h1 h2

end

end Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities.EtaCongruenceSeparation

namespace Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

end Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities
end
end

