import Mathlib

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.JetApproximation
section
set_option autoImplicit false

namespace ReciprocityTheory.ChartRestriction.G.H1.JetApproximation

variable {F R : Type*} [Field F] [CommRing R] [Algebra F R]

theorem pow_le_pow_of_le {V W : Submodule F R} (h : V ≤ W) : ∀ n : ℕ, V ^ n ≤ W ^ n
  | 0 => le_rfl
  | n + 1 => by
    rw [pow_succ, pow_succ]
    exact mul_le_mul' (pow_le_pow_of_le h n) h

theorem one_le_pow {V : Submodule F R} (h1 : 1 ≤ V) : ∀ n : ℕ, 1 ≤ V ^ n
  | 0 => by rw [pow_zero]
  | n + 1 => by
    rw [pow_succ]
    calc (1 : Submodule F R) = 1 * 1 := (mul_one 1).symm
      _ ≤ V ^ n * V := mul_le_mul' (one_le_pow h1 n) h1

theorem pow_mono {V : Submodule F R} (h1 : 1 ≤ V) {a b : ℕ} (hab : a ≤ b) : V ^ a ≤ V ^ b := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [pow_add]
  calc V ^ a = V ^ a * 1 := (mul_one _).symm
    _ ≤ V ^ a * V ^ c := mul_le_mul' le_rfl (one_le_pow h1 c)

theorem pow_le_ideal_pow {W : Submodule F R} {m : Ideal R} (h : W ≤ m.restrictScalars F) :
    ∀ k : ℕ, W ^ k ≤ (m ^ k).restrictScalars F
  | 0 => by
    intro x _
    simp [Ideal.one_eq_top]
  | k + 1 => by
    rw [pow_succ]
    refine Submodule.mul_le.2 fun a ha b hb => ?_
    rw [Submodule.restrictScalars_mem, pow_succ]
    exact Ideal.mul_mem_mul (pow_le_ideal_pow h k ha) (h hb)

theorem pow_le_sup {V : Submodule F R} (h1 : 1 ≤ V) {m : Ideal R}
    (hres : ∀ f : R, ∃ c : F, f - algebraMap F R c ∈ m) (D : ℕ) (n : ℕ) :
    V ^ n ≤ V ^ D ⊔ (m ^ (D + 1)).restrictScalars F := by
  set W : Submodule F R := V ⊓ m.restrictScalars F
  have hVW : V ≤ 1 ⊔ W := by
    intro v hv
    obtain ⟨c, hc⟩ := hres v
    refine Submodule.mem_sup.2 ⟨algebraMap F R c, Submodule.algebraMap_mem c, v - algebraMap F R c,
      ⟨V.sub_mem hv (h1 (Submodule.algebraMap_mem c)), hc⟩, add_sub_cancel _ _⟩
  have hWm : W ≤ m.restrictScalars F := inf_le_right
  have key : ∀ n k : ℕ, W ^ k * V ^ n ≤ V ^ D ⊔ (m ^ (D + 1)).restrictScalars F := by
    intro n
    induction n with
    | zero =>
      intro k
      rw [pow_zero, mul_one]
      rcases le_or_gt k D with hk | hk
      · exact le_sup_of_le_left ((pow_le_pow_of_le inf_le_left k).trans (pow_mono h1 hk))
      · refine le_sup_of_le_right ((pow_le_ideal_pow hWm k).trans ?_)
        intro x hx
        exact Ideal.pow_le_pow_right hk hx
    | succ n ih =>
      intro k
      calc W ^ k * V ^ (n + 1) = W ^ k * (V ^ n * V) := by rw [pow_succ]
        _ ≤ W ^ k * (V ^ n * (1 ⊔ W)) := mul_le_mul' le_rfl (mul_le_mul' le_rfl hVW)
        _ = W ^ k * V ^ n ⊔ W ^ (k + 1) * V ^ n := by
          rw [Submodule.mul_sup, mul_one, Submodule.mul_sup, ← mul_assoc, pow_succ, mul_right_comm (W ^ k) W]
        _ ≤ _ := sup_le (ih k) (ih (k + 1))
  simpa using key n 0

theorem inv_approx {V : Submodule F R} (h1 : 1 ≤ V) {m : Ideal R} (hm : ∀ x ∈ m, ¬ IsUnit x)
    (hres : ∀ f : R, ∃ c : F, f - algebraMap F R c ∈ m) (D n : ℕ) (u : Rˣ) (hu : (u : R) ∈ V ^ n) :
    ∃ w ∈ V ^ (n * D), ((u⁻¹ : Rˣ) : R) - w ∈ m ^ (D + 1) := by
  obtain ⟨c, hc⟩ := hres u
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero, sub_zero] at hc
    exact hm _ hc u.isUnit
  set a : R := algebraMap F R c⁻¹
  have ha : a * algebraMap F R c = 1 := by rw [← map_mul, inv_mul_cancel₀ hc0, map_one]
  set x : R := -(a * u - 1)
  have hxm : x ∈ m := by
    have : a * u - 1 = a * ((u : R) - algebraMap F R c) := by rw [mul_sub, ha]
    rw [show x = -(a * u - 1) from rfl, this]
    exact m.neg_mem (m.mul_mem_left a hc)
  have hxV : x ∈ V ^ n := by
    refine (V ^ n).neg_mem ((V ^ n).sub_mem ?_ (Submodule.one_le.1 (one_le_pow h1 n)))
    rw [show a * (u : R) = c⁻¹ • (u : R) from (Algebra.smul_def _ _).symm]
    exact (V ^ n).smul_mem _ hu
  refine ⟨a * ∑ e ∈ Finset.range (D + 1), x ^ e, ?_, ?_⟩
  · rw [show a * ∑ e ∈ Finset.range (D + 1), x ^ e = c⁻¹ • ∑ e ∈ Finset.range (D + 1), x ^ e from
      (Algebra.smul_def _ _).symm]
    refine (V ^ (n * D)).smul_mem _ (Submodule.sum_mem _ fun e he => ?_)
    have hx := Submodule.pow_mem_pow (V ^ n) hxV e
    rw [← pow_mul] at hx
    exact pow_mono h1 (Nat.mul_le_mul_left n (Nat.lt_succ_iff.1 (Finset.mem_range.1 he))) hx
  · have hau : a * u = 1 - x := by rw [show x = -(a * u - 1) from rfl]; ring
    have hgeom : (u : R) * (a * ∑ e ∈ Finset.range (D + 1), x ^ e) = 1 - x ^ (D + 1) := by
      rw [← mul_assoc, mul_comm (u : R) a, hau, mul_neg_geom_sum]
    have : ((u⁻¹ : Rˣ) : R) - a * ∑ e ∈ Finset.range (D + 1), x ^ e = ((u⁻¹ : Rˣ) : R) * x ^ (D + 1) := by
      have e1 : ((u⁻¹ : Rˣ) : R) * u = 1 := u.inv_mul
      calc ((u⁻¹ : Rˣ) : R) - a * ∑ e ∈ Finset.range (D + 1), x ^ e
          = ((u⁻¹ : Rˣ) : R) * (1 - (u : R) * (a * ∑ e ∈ Finset.range (D + 1), x ^ e)) := by
            rw [mul_sub, mul_one, ← mul_assoc, e1, one_mul]
        _ = _ := by rw [hgeom]; ring
    rw [this]
    exact (m ^ (D + 1)).mul_mem_left _ (Ideal.pow_mem_pow hxm _)

theorem jets {V : Submodule F R} (h1 : 1 ≤ V) {m : Ideal R} (hm : ∀ x ∈ m, ¬ IsUnit x)
    (hres : ∀ f : R, ∃ c : F, f - algebraMap F R c ∈ m)
    (hfrac : ∀ f : R, ∃ (n : ℕ) (G G' : R), G ∈ V ^ n ∧ G' ∈ V ^ n ∧ IsUnit G' ∧ f * G' = G)
    (D : ℕ) (f : R) : ∃ v ∈ V ^ D, f - v ∈ m ^ (D + 1) := by
  obtain ⟨n, G, G', hG, hG', ⟨u, rfl⟩, hf⟩ := hfrac f
  obtain ⟨w, hw, hw'⟩ := inv_approx h1 hm hres D n u hG'
  have hGw : G * w ∈ V ^ D ⊔ (m ^ (D + 1)).restrictScalars F := by
    refine pow_le_sup h1 hres D (n + n * D) ?_
    rw [pow_add]
    exact Submodule.mul_mem_mul hG hw
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hGw
  refine ⟨y, hy, ?_⟩
  have hfG : f = G * ((u⁻¹ : Rˣ) : R) := by rw [← hf, mul_assoc, u.mul_inv, mul_one]
  have : f - y = G * (((u⁻¹ : Rˣ) : R) - w) + z := by
    rw [hfG]
    have : y = G * w - z := by rw [← hyz]; ring
    rw [this]; ring
  rw [this]
  exact (m ^ (D + 1)).add_mem ((m ^ (D + 1)).mul_mem_left _ hw') hz

end ReciprocityTheory.ChartRestriction.G.H1.JetApproximation
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.ReducedBasisStatement
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.H1

open Module Matrix
open scoped ComplexOrder

def diagForm {ι : Type} [Fintype ι] {m : ι → ℕ}
    (H : (τ : ι) → Matrix (Fin (m τ)) (Fin (m τ)) ℂ) (x : (τ : ι) → Fin (m τ) → ℂ) : ℝ :=
  ∑ τ, (star (x τ) ⬝ᵥ (H τ *ᵥ x τ)).re

def ScaleBoundStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (H : (τ : ι) → Matrix (Fin (m τ)) (Fin (m τ)) ℂ),
    (∀ τ, (H τ).PosSemidef) → ∀ (c : ι → ℂ) (C : ℝ), (∀ τ, ‖c τ‖ ^ 2 ≤ C) →
    ∀ x : (τ : ι) → Fin (m τ) → ℂ, diagForm H (fun τ => c τ • x τ) ≤ C * diagForm H x

def ReducedBasisStatement : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (X : Submodule ℤ E) [DiscreteTopology X] [IsZLattice ℝ X] (M : ℝ)
    (v : Fin (finrank ℝ E) → E), LinearIndependent ℝ v → (∀ i, v i ∈ X) →
    (∀ i, ‖v i‖ ^ 2 / 2 ≤ M) →
    ∃ b : Basis (Fin (finrank ℝ E)) ℤ X,
      (∀ j, ‖(b j : E)‖ ^ 2 / 2 ≤ (finrank ℝ E : ℝ) * M) ∧
      ∀ j, ∀ z ∈ X, |inner ℝ (b j : E) z| ≤ 2 * Real.sqrt (finrank ℝ E) * (‖z‖ ^ 2 / 2)

def SpanShortStatement : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (J κ : Type) [Finite J] [Finite κ] (A : J → V →ₗ[ℝ] V) (x : κ → V) (K M : ℝ),
    0 ≤ K → (∀ j y, ‖A j y‖ ^ 2 ≤ K * ‖y‖ ^ 2) → (∀ k, ‖x k‖ ^ 2 / 2 ≤ M) →
    Submodule.span ℝ (Set.range fun p : J × κ => A p.1 (x p.2)) = ⊤ →
    ∃ v : Fin (finrank ℝ V) → J × κ,
      LinearIndependent ℝ (fun i => A (v i).1 (x (v i).2)) ∧
        ∀ i, ‖A (v i).1 (x (v i).2)‖ ^ 2 / 2 ≤ K * M

def PrimeLogSumStatement : Prop :=
  ∀ x : ℝ, 1 ≤ x →
    ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime, Real.log p / ((p : ℝ) - 1) ≤ Real.log x + 2.2

def PrimeTotalStatement : Prop :=
  ∀ (D : ℕ) (L abelian₂ : ℝ) (T : Finset ℕ) (b c : ℕ → ℝ) (g₁ g₂ : ℕ),
    1 ≤ D → Real.log D ≤ 2 * L → 0 ≤ abelian₂ → (∀ l ∈ T, l.Prime) → (∀ l, 0 ≤ c l) →
    ∑ l ∈ T, c l * Real.log l ≤ ((D : ℝ) / 2 + 1) * abelian₂ →
    g₁.Prime → g₂.Prime → 3 ≤ g₁ → 3 ≤ g₂ →
    (∀ l ∈ T, l ≠ g₁ → l ≠ g₂ → l ≤ D → b l ≤ (D : ℝ) / ((l : ℝ) - 1) + c l) →
    (∀ l ∈ T, l ≠ g₁ → l ≠ g₂ → D < l → b l ≤ c l) →
    (∀ l ∈ T, (l = g₁ ∨ l = g₂) → b l ≤ (D : ℝ) / ((l : ℝ) - 1)) →
    ∑ l ∈ T, b l * Real.log l ≤ (2 * L + abelian₂ + 4) * ((D : ℝ) + 2)

def ThirdDiffStatement : Prop :=
  ∀ (G : Type) [AddCommGroup G] (F : G → ℝ), (∃ C : ℝ, ∀ x, |F x| ≤ C) →
    (∀ x y z, F (x + y + z) - F (x + y) - F (x + z) - F (y + z) + F x + F y + F z - F 0 = 0) →
    ∀ x, F x = F 0

def NakayamaCharStatement : Prop :=
  ∀ (R : Type) [CommRing R] [IsLocalRing R] (M : Type) [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] (ι : Type) [Fintype ι] (Γ : Type)
    (T : Γ → M →ₗ[R] M) (χ : ι → Γ → R) (s : ι → M),
    Fintype.card ι = finrank R M →
    (∀ i, s i ∉ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)) →
    (∀ i γ, T γ (s i) - χ i γ • s i ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)) →
    (∀ i j, i ≠ j → ∃ γ, χ i γ - χ j γ ∉ IsLocalRing.maximalIdeal R) →
    Submodule.span R (Set.range s) = ⊤

end ReciprocityTheory.ChartRestriction.G.H1
end
end

