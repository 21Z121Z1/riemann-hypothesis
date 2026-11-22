import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0021
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0022
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0027
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0025
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0026

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.CardRealEmbeddingsEqFinrankStatement
section
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_real_embeddings_eq_finrank : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], Finite (F →+* ℝ) ∧ Nat.card (F →+* ℝ) = Module.finrank ℚ F := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.EmbCard.finite_and_card_realEmbeddings | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.EmbCard.finite_and_card_realEmbeddings | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.EmbCard.finite_and_card_realEmbeddings <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConeSeriesDerivativeGrowthBoundStatement
section
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cone_series_derivative_growth_bound : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ), (∀ j i, 0 < a j i) → (∀ j, 0 < b j) → ∀ (B R : ℕ) (β : ι → ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, ‖s‖ ≤ R → -(B : ℝ) ≤ s.re →
  ∀ x : Fin r → ℝ, (∀ i, 0 ≤ x i) →
    ‖Fr a b s β x‖ ≤ C * sizeE x ^ ((Fintype.card ι : ℤ) * (B : ℤ) - ∑ j, (β j : ℤ)) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.baseBound | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.baseBound | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.baseBound <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConeSeriesDifferentiableLeftStrip
section
set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.OneVar

theorem goodAt_smul {r l : ℕ} {k : Fin r} {v : (Fin r → ℕ) → ℚ} (s : ℚ) (h : GoodAt l k v) :
    GoodAt l k (fun m => s * v m) := by
  refine ⟨fun m => by simp only [h.1 m], fun m => ?_⟩
  rw [← Finset.mul_sum, h.2 m, mul_zero]

theorem bddW_sign {r : ℕ} {v : (Fin r → ℕ) → ℚ} (c : ℕ) (h : BddW v) :
    BddW (fun m => (-1 : ℚ) ^ c * v m) := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C, fun m => ?_⟩
  have : |(((-1 : ℚ) ^ c * v m : ℚ) : ℝ)| = |(v m : ℝ)| := by
    push_cast
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  rw [this]
  exact hC m

theorem iterate_good_bdd {r l : ℕ} {i : Fin r} {v : (Fin r → ℕ) → ℚ} (hl : 0 < l)
    (hg : GoodAt l i v) (hb : BddW v) (c : ℕ) :
    GoodAt l i ((Aop l i)^[c] v) ∧ BddW ((Aop l i)^[c] v) := by
  induction c with
  | zero => exact ⟨hg, hb⟩
  | succ c ih =>
    rw [Function.iterate_succ_apply']
    have := @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.aop_props r l i _ hl ih.1 ih.2
    exact ⟨this.2.2, this.1⟩

theorem iterate_good_other {r l : ℕ} {i k : Fin r} {v : (Fin r → ℕ) → ℚ} (hk : k ≠ i)
    (hg : GoodAt l k v) (c : ℕ) : GoodAt l k ((Aop l i)^[c] v) := by
  induction c with
  | zero => exact hg
  | succ c ih =>
    rw [Function.iterate_succ_apply']
    exact (((@GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.OtherVar.otherVar_main r l i k _ hk).1 ih).1)

theorem iterate_supp_other {r l : ℕ} {i k : Fin r} {v : (Fin r → ℕ) → ℚ} (hk : k ≠ i)
    (hs : ∀ m, m k ≠ 0 → v m = 0) (c : ℕ) : ∀ m, m k ≠ 0 → (Aop l i)^[c] v m = 0 := by
  induction c with
  | zero => exact hs
  | succ c ih =>
    rw [Function.iterate_succ_apply']
    exact (((@GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.OtherVar.otherVar_main r l i k _ hk).2 ih).1)

theorem DL_replicate_succ {r : ℕ} (i : Fin r) (c : ℕ) (g : (Fin r → ℕ) → ℂ) :
    DL (List.replicate (c + 1) i) g = fd i (DL (List.replicate c i) g) := by
  simp [DL, List.replicate_succ]

theorem tsum_iterate {r l : ℕ} {i : Fin r} {v : (Fin r → ℕ) → ℚ} (hl : 0 < l)
    (hg : GoodAt l i v) (hb : BddW v) {g : (Fin r → ℕ) → ℂ} (hs : Summable g) (N : ℕ) :
    ∑' m, (v m : ℂ) * g m =
      ∑ c ∈ Finset.range N, (-1 : ℂ) ^ c *
          ∑' m, (Bop l i ((Aop l i)^[c] v) m : ℂ) * DL (List.replicate c i) g m +
        (-1 : ℂ) ^ N * ∑' m, ((Aop l i)^[N] v m : ℂ) * DL (List.replicate N i) g m := by
  induction N with
  | zero => simp [DL]
  | succ N ih =>
    have hN := iterate_good_bdd hl hg hb N
    have key := @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.StepIdentity.stepIdentity r l i ((Aop l i)^[N] v) (DL (List.replicate N i) g) hl hN.1 hN.2
      (@GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.summable_DL r _ g hs)
    rw [ih, key, Finset.sum_range_succ, Function.iterate_succ_apply', DL_replicate_succ, pow_succ]
    ring

def uW {r : ℕ} (l N : ℕ) (i : Fin r) (v : (Fin r → ℕ) → ℚ) (c : ℕ) : (Fin r → ℕ) → ℚ :=
  if c < N then fun m => (-1 : ℚ) ^ c * Bop l i ((Aop l i)^[c] v) m
  else fun m => (-1 : ℚ) ^ N * (Aop l i)^[N] v m

theorem abel_oneVar : ∀ (r l N : ℕ) (i : Fin r) (v : (Fin r → ℕ) → ℚ), 0 < l → GoodAt l i v → BddW v →
  ∃ u : Fin (N + 1) → (Fin r → ℕ) → ℚ, (∀ c, BddW (u c)) ∧
    (∀ c : Fin (N + 1), (c : ℕ) = N ∨ ∀ m, m i ≠ 0 → u c m = 0) ∧
    (∀ c k, k ≠ i → GoodAt l k v → GoodAt l k (u c)) ∧
    (∀ c k, k ≠ i → (∀ m, m k ≠ 0 → v m = 0) → ∀ m, m k ≠ 0 → u c m = 0) ∧
    ∀ g : (Fin r → ℕ) → ℂ, Summable g →
      ∑' m, (v m : ℂ) * g m = ∑ c, ∑' m, (u c m : ℂ) * DL (List.replicate (c : ℕ) i) g m := by
  intro r l N i v hl hg hb
  refine ⟨fun c => uW l N i v c, fun c => ?_, fun c => ?_, fun c k hk hgk => ?_,
    fun c k hk hsk => ?_, fun g hs => ?_⟩
  · unfold uW
    beta_reduce
    split_ifs with h
    · have hc := iterate_good_bdd hl hg hb c
      exact bddW_sign _ (@GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.aop_props r l i _ hl hc.1 hc.2).2.1
    · exact bddW_sign _ (iterate_good_bdd hl hg hb N).2
  · by_cases h : (c : ℕ) < N
    · refine Or.inr fun m hm => ?_
      simp [uW, h, Bop, hm]
    · exact Or.inl (by have := c.isLt; omega)
  · unfold uW
    beta_reduce
    split_ifs with h
    · exact goodAt_smul _ ((@GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.OtherVar.otherVar_main r l i k _ hk).1 (iterate_good_other hk hgk c)).2
    · exact goodAt_smul _ (iterate_good_other hk hgk N)
  · intro m hm
    unfold uW
    beta_reduce
    split_ifs with h
    · simp [((@GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.OtherVar.otherVar_main r l i k _ hk).2 (iterate_supp_other hk hsk c)).2 m hm]
    · simp [iterate_supp_other hk hsk N m hm]
  · rw [tsum_iterate hl hg hb hs N, Fin.sum_univ_castSucc, Finset.sum_range]
    congr 1
    · refine Finset.sum_congr rfl fun c _ => ?_
      have hc : (c : ℕ) < N := c.isLt
      rw [← tsum_mul_left]
      refine tsum_congr fun m => ?_
      simp [uW, hc, mul_assoc]
    · rw [← tsum_mul_left]
      refine tsum_congr fun m => ?_
      simp [uW, mul_assoc]

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.OneVar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConeSeriesRealDerivativeFormulaStatement
section
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cone_series_real_derivative_formula : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ), (∀ j i, 0 < a j i) → (∀ j, 0 < b j) →
  ∀ (s : ℂ) (β : ι → ℕ) (cs : List (Fin r)) (i : Fin r) (x : Fin r → ℝ) (τ : ℝ), (∀ k, 0 ≤ x k) → 0 ≤ τ →
    HasDerivAt (fun t : ℝ => DLR cs (Fr a b s β) (x + t • (Pi.single i 1 : Fin r → ℝ)))
      (∑ j, (-s - (β j : ℂ)) * (a j i : ℂ) *
        DLR cs (Fr a b s (β + Pi.single j 1)) (x + τ • (Pi.single i 1 : Fin r → ℝ))) τ := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DerivDLR.hasDerivAt_DLR_Fr | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DerivDLR.hasDerivAt_DLR_Fr | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DerivDLR.hasDerivAt_DLR_Fr <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConeSeriesSummableRightHalfPlaneStatement
section
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cone_series_summable_right_half_plane : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ), r ≤ Fintype.card ι → (∀ j i, 0 < a j i) → (∀ j, 0 < b j) → ∀ s : ℂ, 1 < s.re → Summable (coneTerm a b s) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.coneTerm_summable | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.coneTerm_summable | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.coneTerm_summable <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConeTilingBySignRegionsStatement
section
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cone_values_negative_integer_rational : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ) (p : ℕ), (∀ m : Fin r → ℕ, ∃ q : ℚ, ∏ j, (b j + ∑ i, a j i * (m i : ℝ)) ^ p = (q : ℝ)) →
  ∀ cs : List (Fin r), ∃ ρ : (Fin r → ℕ) → ℚ, ∀ m, DL cs (coneTerm a b (-(p : ℂ))) m = (ρ m : ℂ) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DL_coneTerm_neg_nat_rational | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DL_coneTerm_neg_nat_rational | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DL_coneTerm_neg_nat_rational <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConeValuesNegativeIntegerRationalStatement
section
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.high_difference_vanishes_negative_integer : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ) (cs : List (Fin r)) (i : Fin r) (N p : ℕ), cs.count i = N → Fintype.card ι * p < N →
  ∀ m, DL cs (coneTerm a b (-(p : ℂ))) m = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DL_coneTerm_neg_natCast_eq_zero | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DL_coneTerm_neg_natCast_eq_zero | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DL_coneTerm_neg_natCast_eq_zero <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsUnitPowerInCongruenceStatement
section
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_power_in_congruence : ∀ (F : Type) [Field F] [NumberField F] (𝔣 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ → ∃ e : ℕ, 0 < e ∧ ∀ u : (𝓞 F)ˣ, u ^ e ∈ congUnits 𝔣 := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.exists_pow_mem_congUnits | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.exists_pow_mem_congUnits | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.exists_pow_mem_congUnits <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteDifferenceConeTermEqStatement
section
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_difference_cone_term_eq : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ) (s : ℂ) (cs : List (Fin r)) (m : Fin r → ℕ),
  DL cs (coneTerm a b s) m = DLR cs (Fr a b s 0) (fun i => (m i : ℝ)) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DL_coneTerm_eq_DLR | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DL_coneTerm_eq_DLR | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DL_coneTerm_eq_DLR <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteUnitsBoundedEmbeddingRatioStatement
section
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_units_bounded_embedding_ratio : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (R : ℝ),
    {u : (𝓞 F)ˣ | TotPos F ((u : 𝓞 F) : F) ∧ ∀ σ τ : F →+* ℝ, σ ((u : 𝓞 F) : F) ≤ R * τ ((u : 𝓞 F) : F)}.Finite := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.finite_totPos_units_bounded_ratio | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.finite_totPos_units_bounded_ratio | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.finite_totPos_units_bounded_ratio <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.HighDifferenceVanishesNegativeIntegerStatement
section
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_difference_cone_term_differentiable : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ), (∀ j i, 0 < a j i) → (∀ j, 0 < b j) → ∀ (cs : List (Fin r)) (m : Fin r → ℕ), Differentiable ℂ (fun s => DL cs (coneTerm a b s) m) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DL_coneTerm_differentiable | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DL_coneTerm_differentiable | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DL_coneTerm_differentiable <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.PeriodicWeightBoundedStatement
section
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodic_weight_bounded : ∀ (r l : ℕ) (v : (Fin r → ℕ) → ℚ), 0 < l → (∀ i, ∀ m, v (m + (Pi.single i l : Fin r → ℕ)) = v m) → BddW v := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.GoodBdd.bddW_of_periodic | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.GoodBdd.bddW_of_periodic | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.GoodBdd.bddW_of_periodic <;> assumption)
end

