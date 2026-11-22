import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.IntegrableOnFundamentalDomainOfCocompact
section
open NumberField IsDedekindDomain MeasureTheory

namespace GlobalTheory

open Pointwise in

theorem integrableOn_fundamentalDomain_of_cocompact : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ] (K : Set G), IsCompact K → (∀ g : G, ∃ γ ∈ Γ, γ * g ∈ K) → ∀ (μ : Measure G), μ.IsHaarMeasure → ∀ (𝓕 : Set G), IsFundamentalDomain Γ 𝓕 μ → ∀ (f : G → ℂ), Continuous f → (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) → IntegrableOn f 𝓕 μ := by
  intro G _ _ _ _ _ Γ _ K hK hcov μ hμ 𝓕 h𝓕 f hf hinv
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  have hbound : ∀ g, ‖f g‖ ≤ C := by
    intro g
    obtain ⟨γ, hγ, hγg⟩ := hcov g
    rw [← hinv γ hγ g]
    exact hC _ hγg
  have hcover : 𝓕 ⊆ ⋃ γ : Γ, (γ • K ∩ 𝓕) := by
    intro x hx
    obtain ⟨γ, hγ, hγx⟩ := hcov x
    refine Set.mem_iUnion.mpr ⟨(⟨γ, hγ⟩ : Γ)⁻¹, ?_, hx⟩
    rw [Set.mem_inv_smul_set_iff]
    exact hγx
  have hle : μ 𝓕 ≤ μ K :=
    calc μ 𝓕 ≤ μ (⋃ γ : Γ, (γ • K ∩ 𝓕)) := measure_mono hcover
      _ ≤ ∑' γ : Γ, μ (γ • K ∩ 𝓕) := measure_iUnion_le _
      _ = μ K := (h𝓕.measure_eq_tsum K).symm
  exact Measure.integrableOn_of_bounded (hle.trans_lt hK.measure_lt_top).ne
    hf.aestronglyMeasurable (M := C) (ae_of_all _ hbound)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.MulApply
section
namespace GlobalTheory.OrbitGrowth

variable {M : Type} [AddCommGroup M] [Module ℂ M]

def orb (A : Subalgebra ℂ (Module.End ℂ M)) (x : M) : Submodule ℂ M :=
  Submodule.span ℂ {y | ∃ a ∈ A, y = (a : M → M) x}

lemma orb_le {A : Subalgebra ℂ (Module.End ℂ M)} {x : M} {U : Submodule ℂ M} :
    orb A x ≤ U ↔ ∀ a ∈ A, (a : M → M) x ∈ U := by
  unfold orb
  rw [Submodule.span_le]
  constructor
  · intro h a ha; exact h ⟨a, ha, rfl⟩
  · rintro h y ⟨a, ha, rfl⟩; exact h a ha

lemma mem_orb {A : Subalgebra ℂ (Module.End ℂ M)} {x : M} {a : Module.End ℂ M} (ha : a ∈ A) :
    (a : M → M) x ∈ orb A x := Submodule.subset_span ⟨a, ha, rfl⟩

lemma mul_apply' (a b : Module.End ℂ M) (y : M) : (a * b) y = a (b y) := rfl

def good (A : Subalgebra ℂ (Module.End ℂ M)) : Submodule ℂ M where
  carrier := {x | FiniteDimensional ℂ (orb A x)}
  zero_mem' := by
    show FiniteDimensional ℂ (orb A 0)
    have : orb A 0 ≤ ⊥ := orb_le.mpr (fun a _ => by simp)
    exact Submodule.finiteDimensional_of_le this
  add_mem' := by
    intro x y hx hy
    haveI : FiniteDimensional ℂ (orb A x) := hx
    haveI : FiniteDimensional ℂ (orb A y) := hy
    show FiniteDimensional ℂ (orb A (x + y))
    have : orb A (x + y) ≤ orb A x ⊔ orb A y := orb_le.mpr (fun a ha => by
      rw [map_add]
      exact Submodule.add_mem_sup (mem_orb ha) (mem_orb ha))
    exact Submodule.finiteDimensional_of_le this
  smul_mem' := by
    intro c x hx
    haveI : FiniteDimensional ℂ (orb A x) := hx
    show FiniteDimensional ℂ (orb A (c • x))
    have : orb A (c • x) ≤ orb A x := orb_le.mpr (fun a ha => by
      rw [map_smul]
      exact Submodule.smul_mem _ c (mem_orb ha))
    exact Submodule.finiteDimensional_of_le this

lemma mem_good {A : Subalgebra ℂ (Module.End ℂ M)} {x : M} :
    x ∈ good A ↔ FiniteDimensional ℂ (orb A x) := Iff.rfl

def grow (A : Subalgebra ℂ (Module.End ℂ M)) (W : Submodule ℂ M) : Submodule ℂ M :=
  Submodule.span ℂ {y | ∃ a ∈ A, ∃ x ∈ W, y = (a : M → M) x}

lemma grow_le {A : Subalgebra ℂ (Module.End ℂ M)} {W U : Submodule ℂ M} :
    grow A W ≤ U ↔ ∀ a ∈ A, ∀ x ∈ W, (a : M → M) x ∈ U := by
  unfold grow
  rw [Submodule.span_le]
  constructor
  · intro h a ha x hx; exact h ⟨a, ha, x, hx, rfl⟩
  · rintro h y ⟨a, ha, x, hx, rfl⟩; exact h a ha x hx

lemma mem_grow {A : Subalgebra ℂ (Module.End ℂ M)} {W : Submodule ℂ M} {a : Module.End ℂ M}
    (ha : a ∈ A) {x : M} (hx : x ∈ W) : (a : M → M) x ∈ grow A W :=
  Submodule.subset_span ⟨a, ha, x, hx, rfl⟩

lemma le_grow (A : Subalgebra ℂ (Module.End ℂ M)) (W : Submodule ℂ M) : W ≤ grow A W := by
  intro x hx
  have := mem_grow A.one_mem hx
  simpa using this

lemma grow_inv {A : Subalgebra ℂ (Module.End ℂ M)} {W : Submodule ℂ M} {a : Module.End ℂ M}
    (ha : a ∈ A) {x : M} (hx : x ∈ grow A W) : (a : M → M) x ∈ grow A W := by
  have h : grow A W ≤ (grow A W).comap a := grow_le.mpr (fun b hb y hy => by
    show a (b y) ∈ grow A W
    rw [← mul_apply']
    exact mem_grow (A.mul_mem ha hb) hy)
  exact h hx

lemma grow_inv' {A : Subalgebra ℂ (Module.End ℂ M)} {W : Submodule ℂ M} {c : Module.End ℂ M}
    (hc : ∀ x ∈ W, c x ∈ W) (hcomm : ∀ a ∈ A, c * a = a * c) {x : M} (hx : x ∈ grow A W) :
    c x ∈ grow A W := by
  have h : grow A W ≤ (grow A W).comap c := grow_le.mpr (fun b hb y hy => by
    show c (b y) ∈ grow A W
    rw [← mul_apply', hcomm b hb, mul_apply']
    exact mem_grow hb (hc y hy))
  exact h hx

lemma grow_fd {A : Subalgebra ℂ (Module.End ℂ M)} {W : Submodule ℂ M} [FiniteDimensional ℂ W]
    (hW : W ≤ good A) : FiniteDimensional ℂ (grow A W) := by
  obtain ⟨s, hs⟩ : W.FG := (Submodule.fg_iff_finiteDimensional W).mpr inferInstance
  haveI : ∀ y : s, FiniteDimensional ℂ (orb A (y : M)) := fun y => by
    have hy : (y : M) ∈ W := by rw [← hs]; exact Submodule.subset_span y.2
    exact mem_good.mp (hW hy)
  have hle : grow A W ≤ ⨆ y : s, orb A (y : M) := grow_le.mpr (fun a ha x hx => by
    have h2 : W ≤ (⨆ y : s, orb A (y : M)).comap a := by
      rw [← hs, Submodule.span_le]
      intro y hy
      exact Submodule.mem_iSup_of_mem (⟨y, hy⟩ : s) (mem_orb ha)
    exact h2 hx)
  exact Submodule.finiteDimensional_of_le hle

lemma grow_good {A B : Subalgebra ℂ (Module.End ℂ M)} {W : Submodule ℂ M} (hW : W ≤ good B)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : grow A W ≤ good B :=
  grow_le.mpr (fun a ha x hx => by
    haveI : FiniteDimensional ℂ (orb B x) := mem_good.mp (hW hx)
    have hle : orb B (a x) ≤ (orb B x).map a := orb_le.mpr (fun b hb => by
      have e : b (a x) = a (b x) := by
        rw [← mul_apply', ← mul_apply', hcomm a ha b hb]
      rw [e]
      exact Submodule.mem_map_of_mem (mem_orb hb))
    exact mem_good.mpr (Submodule.finiteDimensional_of_le hle))

theorem main : ∀ (M : Type) [inst : AddCommGroup M] [inst_1 : Module ℂ M] (ι : Type) [Finite ι]
    (A : ι → Subalgebra ℂ (Module.End ℂ M)),
    (∀ (i j : ι), i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, a * b = b * a) → ∀ (m : M),
    (∀ (i : ι), FiniteDimensional ℂ ↥(Submodule.span ℂ {x : M | ∃ a ∈ A i, x = (a : M → M) m})) →
    ∃ (W : Submodule ℂ M), FiniteDimensional ℂ ↥W ∧ m ∈ W ∧
      ∀ (i : ι), ∀ a ∈ A i, ∀ x ∈ W, (a : M → M) x ∈ W := by
  intro M _ _ ι _ A hcomm m hfin
  classical
  haveI := Fintype.ofFinite ι
  have key : ∀ S : Finset ι, ∃ W : Submodule ℂ M, FiniteDimensional ℂ W ∧ m ∈ W ∧
      (∀ i ∈ S, ∀ a ∈ A i, ∀ x ∈ W, a x ∈ W) ∧ (∀ j, j ∉ S → W ≤ good (A j)) := by
    intro S
    refine Finset.induction_on S ?_ ?_
    · refine ⟨Submodule.span ℂ {m}, inferInstance, Submodule.mem_span_singleton_self m,
        by simp, ?_⟩
      intro j _
      rw [Submodule.span_le, Set.singleton_subset_iff]
      exact mem_good.mpr (hfin j)
    · intro j S hj ih
      obtain ⟨W, hWfd, hmW, hinv, hgood⟩ := ih
      refine ⟨grow (A j) W, grow_fd (hgood j hj), le_grow _ _ hmW, ?_, ?_⟩
      · intro i hi a ha x hx
        rcases Finset.mem_insert.mp hi with rfl | hiS
        · exact grow_inv ha hx
        · have hij : i ≠ j := fun h => hj (h ▸ hiS)
          exact grow_inv' (hinv i hiS a ha) (fun b hb => hcomm i j hij a ha b hb) hx
      · intro k hk
        have hkj : k ≠ j := fun h => hk (h ▸ Finset.mem_insert_self j S)
        have hkS : k ∉ S := fun h => hk (Finset.mem_insert_of_mem h)
        exact grow_good (hgood k hkS) (fun a ha b hb => (hcomm k j hkj b hb a ha).symm)
  obtain ⟨W, h1, h2, h3, -⟩ := key Finset.univ
  exact ⟨W, h1, h2, fun i a ha x hx => h3 i (Finset.mem_univ i) a ha x hx⟩

end GlobalTheory.OrbitGrowth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.SumSizesLeRingPolynomial
section
open Real

namespace GlobalTheory

theorem sum_sizes_le_ring_polynomial :
    ∀ (f r m L lE lh lG : ℝ), 8 ≤ f → 62 ≤ r → 2 * m ≤ r → 0 ≤ m → 4 ≤ L → lE ≤ 2 * L → 0 ≤ lE →
      log f ≤ L → lh ≤ f * lE + 2 * f * log (1 + f * lE) → lG ≤ f * r ^ 2 * (18 * L + 2) →
      lG + (m + 5) * lh + (4 * f + 20) * (21 * L) + 100 * L
        ≤ 19 * f * r ^ 2 * L + 198 * f ^ 2 * L := by
  intro f r m L lE lh lG hf hr hm hm0 hL hE hE0 hlog hlh hlG
  have hf0 : 0 < f := by linarith
  have hL0 : 0 < L := by linarith
  have hfE0 : 0 ≤ f * lE := mul_nonneg hf0.le hE0
  have hfE : f * lE ≤ f * (2 * L) := mul_le_mul_of_nonneg_left hE hf0.le
  have hfL : 32 ≤ f * L := by nlinarith
  have h1 : log (1 + f * lE) ≤ log (f * (3 * L)) :=
    log_le_log (by linarith) (by nlinarith)
  have h2 : log (f * (3 * L)) = log f + log (3 * L) :=
    log_mul hf0.ne' (by positivity)
  have h3 : log (3 * L) ≤ 3 * L - 1 := log_le_sub_one_of_pos (by positivity)
  have h4 : log (1 + f * lE) ≤ 4 * L := by linarith
  have h5 : 2 * f * log (1 + f * lE) ≤ 2 * f * (4 * L) :=
    mul_le_mul_of_nonneg_left h4 (by positivity)
  have h6 : lh ≤ 10 * (f * L) := by nlinarith
  have h7 : (m + 5) * lh ≤ (m + 5) * (10 * (f * L)) :=
    mul_le_mul_of_nonneg_left h6 (by linarith)
  have h8 : (m + 5) * (10 * (f * L)) ≤ (r / 2 + 5) * (10 * (f * L)) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have h9 : f * r ^ 2 * 4 ≤ f * r ^ 2 * L :=
    mul_le_mul_of_nonneg_left hL (by positivity)
  have h10 : 8 * L ≤ f * L := mul_le_mul_of_nonneg_right hf hL0.le
  have h11 : 5 * r + 200 ≤ r ^ 2 / 2 := by nlinarith
  have h12 : (5 * r + 200) * (f * L) ≤ r ^ 2 / 2 * (f * L) :=
    mul_le_mul_of_nonneg_right h11 (by linarith)
  have h13 : 0 ≤ f ^ 2 * L := by positivity
  nlinarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ThreeDistinctRoots
section
namespace GlobalTheory.ThreeDistinctRoots

open Polynomial

theorem three_distinct_roots :
    ∀ {K : Type} [inst : Field K] [IsAlgClosed K] (g₂ g₃ : K), (2 : K) ≠ (0 : K) →
      g₂ ^ (3 : ℕ) - (27 : K) * g₃ ^ (2 : ℕ) ≠ (0 : K) →
      ∃ (x : K) (y : K) (z : K), x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
        (4 : K) * x ^ (3 : ℕ) - g₂ * x - g₃ = (0 : K) ∧
        (4 : K) * y ^ (3 : ℕ) - g₂ * y - g₃ = (0 : K) ∧
        (4 : K) * z ^ (3 : ℕ) - g₂ * z - g₃ = (0 : K) := by
  intro K _ _ g₂ g₃ h2 hΔ
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2

  obtain ⟨x, hx⟩ : ∃ x : K, (4 : K) * x ^ 3 - g₂ * x - g₃ = 0 := by
    have hdeg : (C (4 : K) * X ^ 3 - C g₂ * X - C g₃).degree ≠ 0 := by
      have : (C (4 : K) * X ^ 3 - C g₂ * X - C g₃).degree = 3 := by
        compute_degree!
      rw [this]; decide
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_root _ hdeg
    refine ⟨x, ?_⟩
    simpa using hx

  obtain ⟨s, hs⟩ := IsAlgClosed.exists_eq_mul_self (g₂ - 3 * x ^ 2)
  obtain ⟨y, hy⟩ : ∃ y : K, 2 * y = s - x := ⟨(s - x) / 2, by field_simp⟩
  have hq : 4 * y ^ 2 + 4 * x * y + 4 * x ^ 2 - g₂ = 0 := by
    linear_combination (2 * y + x + s) * hy - hs
  have hg₂ : g₂ = 4 * (x ^ 2 + x * y + y ^ 2) := by linear_combination -hq
  have hg₃ : g₃ = -4 * x * y * (x + y) := by
    linear_combination -hx + x * hq
  refine ⟨x, y, -x - y, ?_⟩
  have key : g₂ ^ 3 - 27 * g₃ ^ 2 = 16 * ((x - y) * (y - (-x - y)) * ((-x - y) - x)) ^ 2 := by
    rw [hg₂, hg₃]; ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; apply hΔ; rw [key, sub_eq_zero.mpr h]; ring
  · intro h; apply hΔ
    rw [key, show (-x - y) - x = -(x - (-x - y)) by ring, sub_eq_zero.mpr h]; ring
  · intro h; apply hΔ
    rw [key, sub_eq_zero.mpr h]; ring
  · exact hx
  · rw [hg₂, hg₃]; ring
  · rw [hg₂, hg₃]; ring

end GlobalTheory.ThreeDistinctRoots
end

