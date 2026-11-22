import Mathlib
import Formalism.GL3MeanSquares.Bundle0001
import Formalism.GL3MeanSquares.HookFormulaTorsion.GlobalBoundRefinements
import Formalism.SharpRestriction.InertJacobiLevels.Bundle0007
import Formalism.CyclotomicNorms.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0040
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0010
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0129
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0120
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0125
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0119

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormPrimesShortIntervalLower
section
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.NormPrimes

open Formalism.HermitianLattices.GL2PrimeSums

theorem err_le_rhoErr {CA c₃ Q B Y : ℝ} (hCA : 0 < CA) (hc : 0 < c₃) (hQ : 1 < Q) (hQB : Q ≤ B)
    (hY : 1 ≤ Y) :
    CA * (Real.exp (-c₃ * Real.log Y / Real.log Q) + Real.exp (-Real.sqrt (c₃ * Real.log Y / 2))) ≤
      rhoErr CA (min c₃ (Real.sqrt (c₃ / 2))) B Y := by
  have hL : 0 ≤ Real.log Y := Real.log_nonneg hY
  have hlQ : 0 < Real.log Q := Real.log_pos hQ
  have hlQB : Real.log Q ≤ Real.log B := Real.log_le_log (by linarith) hQB
  have hm0 : 0 ≤ min c₃ (Real.sqrt (c₃ / 2)) := le_min hc.le (Real.sqrt_nonneg _)
  unfold rhoErr
  rw [mul_add]
  refine add_le_add (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hCA.le)
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hCA.le)
  · rw [neg_mul, neg_mul, neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div₀ (mul_nonneg hc.le hL) (mul_le_mul_of_nonneg_right (min_le_left _ _) hL)
      hlQ hlQB
  · rw [neg_mul, neg_le_neg_iff, show c₃ * Real.log Y / 2 = c₃ / 2 * Real.log Y by ring,
      Real.sqrt_mul (by positivity)]
    exact mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.sqrt_nonneg _)

theorem exceptional_bounds {cS Q B β : ℝ} (hc : 0 < cS) (hQ : 4 ≤ Q) (hQB : Q ≤ B)
    (h1 : 1 - 1 / (8 * Real.log Q) < β) (h2 : cS / (Q ^ 2 * Real.log Q) ≤ 1 - β) :
    1 / 2 ≤ β ∧ β < 1 ∧ cS / (B ^ 2 * Real.log B) ≤ 1 - β := by
  have hl1 : 1 ≤ Real.log Q := by
    have h1 : Real.log 4 ≤ Real.log Q := Real.log_le_log (by norm_num) hQ
    have h2 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    have h3 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    linarith
  have hlQB : Real.log Q ≤ Real.log B := Real.log_le_log (by linarith) hQB
  have hQ0 : 0 < Q := by linarith
  have hp : 0 < Q ^ 2 * Real.log Q := mul_pos (by positivity) (by linarith)
  refine ⟨?_, ?_, ?_⟩
  · have : 1 / (8 * Real.log Q) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  · have := div_pos hc hp
    linarith
  · refine le_trans (div_le_div_of_nonneg_left hc.le hp ?_) h2
    exact mul_le_mul (pow_le_pow_left₀ hQ0.le hQB 2) hlQB (by linarith) (by positivity)

theorem normOne_of_generator {K : Type} [Field K] [NumberField K] {d M : ℕ} {ω : 𝓞 K}
    (hgen : ∀ z : 𝓞 K, ∃ a b : ℤ, z = a + b * ω)
    (hnorm : ∀ a b : ℤ,
      Algebra.norm ℤ ((a : 𝓞 K) + b * ω) * 4 = (2 * a + b) ^ 2 + d * b ^ 2)
    {π : 𝓞 K} (hπ : π - 1 ∈ Ideal.span {(M : 𝓞 K)}) :
    NormOne d M (Ideal.absNorm (Ideal.span {π})) := by
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hπ
  obtain ⟨a, b, rfl⟩ := hgen z
  have e : π = ((1 + M * a : ℤ) : 𝓞 K) + ((M * b : ℤ) : 𝓞 K) * ω := by
    push_cast
    linear_combination -hz
  have hn := hnorm (1 + M * a) (M * b)
  rw [← e] at hn
  have h0 : 0 ≤ Algebra.norm ℤ π := by
    have : 0 ≤ (2 * (1 + (M : ℤ) * a) + M * b) ^ 2 + d * ((M : ℤ) * b) ^ 2 := by positivity
    linarith
  refine ⟨2 * (1 + M * a) + M * b, M * b, ?_, Dvd.intro _ rfl, ⟨a, by ring⟩⟩
  rw [Ideal.absNorm_span_singleton, Int.natAbs_of_nonneg h0]
  linarith

theorem ncard_le_two_mul_card {α : Type} {T : Set α} (hT : T.Finite) (f : α → ℕ) (F : Finset ℕ)
    (hF : ∀ v ∈ T, f v ∈ F) (h2 : ∀ p ∈ F, {v ∈ T | f v = p}.ncard ≤ 2) :
    T.ncard ≤ 2 * F.card := by
  classical
  rw [Set.ncard_eq_toFinset_card T hT]
  refine Finset.card_le_mul_card_image_of_maps_to (f := f) (fun v hv => hF v (by simpa using hv)) 2
    (fun p hp => ?_)
  refine le_trans (le_of_eq ?_) (h2 p hp)
  rw [← Set.ncard_coe_finset]
  congr 1
  ext v
  simp

theorem normPrimes_short_interval : GlobalTheory.Mem.An.QuadraticHeckeZeroEstimates → ∃ C₀ Cr cr c : ℝ, 0 < C₀ ∧ 0 < Cr ∧ 0 < cr ∧ 0 < c ∧ ∀ d M : ℕ, d.Prime → d % 4 = 3 → 100 ≤ d → 1 ≤ M → ∀ X h : ℝ, (4 * (d : ℝ) * (M : ℝ) ^ 2) ^ C₀ ≤ X → h ≤ 1 → Formalism.HermitianLattices.GL2PrimeSums.rhoErr Cr cr (4 * (d : ℝ) * (M : ℝ) ^ 2) X ≤ h / 100 → (4 * (d : ℝ) * (M : ℝ) ^ 2) ^ (7 : ℝ) ≤ h * X ^ ((1 : ℝ) / 3) → c * h * (4 * (d : ℝ) * (M : ℝ) ^ 2) ^ (-6 : ℝ) * X / Real.log X ≤ ((normPrimes d M X (X * (1 + h))).card : ℝ) := by
  rintro ⟨c₂, c₃, CA, cS, hc₂, hc₃, hCA, hcS, HT⟩
  have hcr : 0 < min c₃ (Real.sqrt (c₃ / 2)) := lt_min hc₃ (Real.sqrt_pos.2 (by positivity))
  obtain ⟨C₀, c, hC₀, hc, H⟩ := Formalism.HermitianLattices.GlobalBoundRefinements.shortIntervalLowerBound c₂ CA _ cS hc₂ hCA hcr hcS
  refine ⟨C₀, CA, _, c / 2, by linarith, hCA, hcr, by positivity, ?_⟩
  intro d M hdp hd4 hd100 hM X h hX hh1 hρ hB7
  obtain ⟨K, _, _, ω, hK, h2, hD, -, hgen, hnorm⟩ :=
    GlobalTheory.Mem.ImagQuad.exists_imagQuad_integers d hdp hd4
  set B : ℝ := 4 * (d : ℝ) * (M : ℝ) ^ 2 with hB
  set 𝔮 : Ideal (𝓞 K) := Ideal.span {(M : 𝓞 K)} with h𝔮
  have hq0 : 𝔮 ≠ ⊥ := by
    rw [h𝔮, Ne, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.2 (by omega)
  have hNq : (Ideal.absNorm 𝔮 : ℝ) = (M : ℝ) ^ 2 := by
    rw [h𝔮, Ideal.absNorm_span_natCast, RingOfIntegers.rank, h2]
    push_cast; rfl
  have hDR : |(discr K : ℝ)| = d := by
    rw [hD]; push_cast; rw [abs_neg, abs_of_nonneg (Nat.cast_nonneg d)]
  have hdR : (100 : ℝ) ≤ d := by exact_mod_cast hd100
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hM2 : (1 : ℝ) ≤ (M : ℝ) ^ 2 := one_le_pow₀ hMR
  obtain ⟨Q, β, θ, S, hQ1, hQ2, hθ, hβ, hS, hmain⟩ := HT K hK h2 𝔮 hq0
  rw [hDR] at hQ1 hQ2
  rw [hNq] at hQ2
  have hQB : Q ≤ B := hQ2
  have hQ4 : 4 ≤ Q := by linarith
  have hB4 : 4 ≤ B := by linarith
  obtain ⟨hfin, hfib, hdiv⟩ := GlobalTheory.T.prime_ideals_counting_bounds K hK h2
  obtain ⟨hG1, hG2, -⟩ := GlobalTheory.T.ray_class_number_bounds K 𝔮 hq0
  have hcl := GlobalTheory.classNumber_le_four_mul_abs_discr K h2
  rw [hDR] at hcl
  have hGB : (rayNo 𝔮 : ℝ) ≤ B := by
    have h1 : (rayNo 𝔮 : ℝ) ≤ (classNumber K : ℝ) * (Ideal.absNorm 𝔮 : ℝ) := by
      exact_mod_cast hG2
    rw [hNq] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right hcl (by positivity))
  have hrfin : ∀ Y : ℝ, 1 ≤ Y → (rayPrimes 𝔮 Y).Finite := fun Y hY =>
    (hfin Y hY).1.subset (fun v hv => hv.2.1)
  let P₁ : ℝ → Set (HeightOneSpectrum (𝓞 K)) := fun Y =>
    {v ∈ rayPrimes 𝔮 Y | (Ideal.absNorm v.asIdeal).Prime}
  let P₂ : ℝ → Set (HeightOneSpectrum (𝓞 K)) := fun Y =>
    {v ∈ rayPrimes 𝔮 Y | ¬ (Ideal.absNorm v.asIdeal).Prime}
  have hsplit : ∀ Y : ℝ, 1 ≤ Y → (rayPrimes 𝔮 Y).ncard = (P₁ Y).ncard + (P₂ Y).ncard := by
    intro Y hY
    rw [← Set.ncard_union_eq ?_ ((hrfin Y hY).subset (fun v hv => hv.1))
      ((hrfin Y hY).subset (fun v hv => hv.1))]
    · congr 1
      ext v
      simp only [P₁, P₂, Set.mem_union, Set.mem_setOf_eq]
      tauto
    · exact Set.disjoint_left.2 (fun v hv hv' => hv'.2 hv.2)
  have hdfin : {v : HeightOneSpectrum (𝓞 K) | v.asIdeal ∣ 𝔮}.Finite :=
    Ideal.finite_factors hq0
  have hX1 : 1 ≤ X := le_trans (Real.one_le_rpow (by linarith) (by linarith)) hX
  have key := (H B (rayNo 𝔮) β θ (fun Y => (P₁ Y).ncard) (fun Y => (P₂ Y).ncard)
    (fun Y => ({v ∈ S | (Ideal.absNorm v.asIdeal : ℝ) ≤ Y}.ncard : ℝ)) hB4
    (by exact_mod_cast hG1) hGB (by rcases hθ with h | h <;> simp [h])
    (fun h0 => by
      obtain ⟨a, b⟩ := hβ (by omega)
      exact exceptional_bounds hcS hQ4 hQB a b)
    (fun Y hY => by
      have h1 : (P₂ Y).ncard ≤ {v : HeightOneSpectrum (𝓞 K) |
          (Ideal.absNorm v.asIdeal : ℝ) ≤ Y ∧ ¬ (Ideal.absNorm v.asIdeal).Prime}.ncard :=
        Set.ncard_le_ncard (fun v hv => ⟨hv.1.2.1, hv.2⟩)
          ((hfin Y hY).1.subset (fun v hv => hv.1))
      have h2 : ((P₂ Y).ncard : ℝ) ≤ _ := Nat.cast_le.2 h1
      have := (hfin Y hY).2
      have := Real.sqrt_nonneg Y
      linarith)
    (fun Y => by
      refine ⟨Nat.cast_nonneg _, ?_⟩
      have h1 : {v ∈ S | (Ideal.absNorm v.asIdeal : ℝ) ≤ Y}.ncard ≤
          {v : HeightOneSpectrum (𝓞 K) | v.asIdeal ∣ 𝔮}.ncard :=
        Set.ncard_le_ncard (fun v hv => hS v hv.1) hdfin
      have h2 : ({v ∈ S | (Ideal.absNorm v.asIdeal : ℝ) ≤ Y}.ncard : ℝ) ≤ _ := Nat.cast_le.2 h1
      have h3 := hdiv 𝔮 hq0
      rw [hNq] at h3
      have h4 : Real.log (4 * (M : ℝ) ^ 2) ≤ Real.log B :=
        Real.log_le_log (by positivity) (by rw [hB]; nlinarith)
      linarith)
    (fun Y hY => by
      have hY1 : 1 ≤ Y := le_trans (Real.one_le_rpow (by linarith) hc₂.le) hY
      have h1 := hmain Y (le_trans (Real.rpow_le_rpow (by linarith) hQB hc₂.le) hY)
      rw [hsplit Y hY1] at h1
      push_cast at h1
      have hE : 0 ≤ Emain θ β Y :=
        nonneg_of_mul_nonneg_right (le_trans (abs_nonneg _) h1) (by positivity)
      exact h1.trans (mul_le_mul_of_nonneg_right
        (err_le_rhoErr hCA hc₃ (by linarith) hQB hY1) hE))
    X hX).2 h hh1 hρ hB7
  have hρ0 : 0 < rhoErr CA (min c₃ (Real.sqrt (c₃ / 2))) B X := by unfold rhoErr; positivity
  have hh0 : 0 < h := by linarith
  have hX' : 1 ≤ X * (1 + h) := by nlinarith
  have hP1 : (P₁ (X * (1 + h))).Finite := (hrfin _ hX').subset (fun v hv => hv.1)
  have hP0 : (P₁ X).Finite := (hrfin _ hX1).subset (fun v hv => hv.1)
  have hcount : (P₁ (X * (1 + h)) \ P₁ X).ncard ≤ 2 * (normPrimes d M X (X * (1 + h))).card := by
    refine ncard_le_two_mul_card (hP1.subset Set.diff_subset)
      (fun v => Ideal.absNorm v.asIdeal) _ ?_ ?_
    · rintro v ⟨⟨hv, hp⟩, hn⟩
      have hlt : X < (Ideal.absNorm v.asIdeal : ℝ) := by
        by_contra hle
        exact hn ⟨⟨hv.1, not_lt.1 hle, hv.2.2⟩, hp⟩
      obtain ⟨π, hπ1, hπ2⟩ := GlobalTheory.T.ray_primes_principal_generator K 𝔮 hq0 _ v hv
      have hN := normOne_of_generator hgen hnorm hπ2
      rw [← hπ1] at hN
      unfold normPrimes
      simp only [Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨⟨(Nat.floor_lt (by linarith)).2 hlt, Nat.le_floor hv.2.1⟩, hp, hN⟩
    · intro p hp
      have hpp : p.Prime := by
        unfold normPrimes at hp
        simp only [Finset.mem_filter] at hp
        exact hp.2.1
      refine le_trans (Set.ncard_le_ncard (fun v hv => hv.2) ?_) (hfib p hpp)
      refine (hfin p (by exact_mod_cast hpp.one_lt.le)).1.subset (fun v hv => ?_)
      have : Ideal.absNorm v.asIdeal = p := hv
      simp [this]
  have hle : (P₁ (X * (1 + h))).ncard ≤ (P₁ (X * (1 + h)) \ P₁ X).ncard + (P₁ X).ncard :=
    Set.ncard_le_ncard_diff_add_ncard _ _ hP0
  have hR : ((P₁ (X * (1 + h))).ncard : ℝ) ≤
      2 * ((normPrimes d M X (X * (1 + h))).card : ℝ) + (P₁ X).ncard := by
    exact_mod_cast hle.trans (Nat.add_le_add_right hcount _)
  have e : c / 2 * h * B ^ (-6 : ℝ) * X / Real.log X
      = (c * h * B ^ (-6 : ℝ) * X / Real.log X) / 2 := by ring
  rw [e]
  linarith

end GlobalTheory.Mem.NormPrimes
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrimeLevelStructureDataRanksModPrime
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.Col2.LRank

open scoped TensorProduct in

theorem natCard_quot {R N : Type} [CommRing R] [IsDomain R] [AddCommGroup N] [Module R N]
    [Module.Finite R N] [Module.Projective R N] (I : Ideal R) [Finite (R ⧸ I)] :
    Nat.card (N ⧸ (I • ⊤ : Submodule R N)) = Nat.card (R ⧸ I) ^ Module.finrank R N := by
  have : IsArtinianRing (R ⧸ I) := isArtinian_of_finite
  obtain ⟨b⟩ := Module.nonempty_basis_of_flat_of_finrank_eq (R ⧸ I) ((R ⧸ I) ⊗[R] N) (Module.finrank R N)
    (fun P => by
      have := P.isMaximal
      let : Field ((R ⧸ I) ⧸ P.asIdeal) := Ideal.Quotient.field _
      rw [(TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ I) ((R ⧸ I) ⧸ P.asIdeal)
        ((R ⧸ I) ⧸ P.asIdeal) N).finrank_eq]
      have h1 := Module.rankAtStalk_baseChange (R := R) (M := N) (S := (R ⧸ I) ⧸ P.asIdeal) ⊥
      rw [Module.rankAtStalk_eq_finrank_of_free, Module.rankAtStalk_eq, Ideal.finrank_fiber_eq_finrank] at h1
      exact h1)
  rw [← Nat.card_congr (TensorProduct.quotTensorEquivQuotSMul N I).toEquiv, Nat.card_congr b.equivFun.toEquiv,
    Nat.card_fun, Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin]

theorem finrank_of_span_top {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (p : Submodule (𝓞 K) V)
    (h : Submodule.span K (p : Set V) = ⊤) : Module.finrank (𝓞 K) p = Module.finrank K V := by
  have : IsLocalizedModule (nonZeroDivisors (𝓞 K)) p.subtype := by
    refine ⟨fun s => ?_, fun y => ?_, fun {a b} hab => ⟨1, by simpa using hab⟩⟩
    · have := isLocalizedModule_id (nonZeroDivisors (𝓞 K)) V K
      exact IsLocalizedModule.map_units (S := nonZeroDivisors (𝓞 K)) (LinearMap.id : V →ₗ[𝓞 K] V) s
    · have hy : y ∈ Submodule.span K (p : Set V) := h ▸ Submodule.mem_top
      obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 K)) K _ y hy
      rw [Submodule.span_eq] at ht
      exact ⟨(⟨_, ht⟩, t), rfl⟩
  rw [← IsLocalizedModule.finrank_eq (nonZeroDivisors (𝓞 K)) p.subtype le_rfl,
    IsFractionRing.finrank_right_eq (𝓞 K) K V]

theorem finrank_of_card {F V : Type} [Field F] [Finite F] [AddCommGroup V] [Module F V] {n : ℕ}
    (h : Nat.card V = Nat.card F ^ n) : Module.finrank F V = n := by
  have h1 : 1 < Nat.card F := Finite.one_lt_card
  have : Finite V := Nat.finite_of_card_ne_zero (by rw [h]; positivity)
  have : Module.Finite F V := Module.Finite.of_finite
  have h2 := Module.natCard_eq_pow_finrank (K := F) (V := V)
  rw [h] at h2
  exact (Nat.pow_right_injective h1 h2).symm

set_option maxHeartbeats 800000 in

theorem finrank_red {E : Type} [Field E] [NumberField E] {n : ℕ} (N : Submodule (𝓞 E) (Fin n → E))
    (hN : Submodule.IsLattice E N) (P : HeightOneSpectrum (𝓞 E)) :
    Module.finrank (Res P) (TDat.Red N P) = n := by
  have : Module.Finite (𝓞 E) N := Module.Finite.iff_fg.2 (Submodule.IsLattice.fg (self := hN))
  have : Module.FinitePresentation (𝓞 E) N := Module.finitePresentation_of_finite _ _
  have : Module.Flat (𝓞 E) N := inferInstance
  have : Module.Projective (𝓞 E) N := Module.Flat.projective_of_finitePresentation
  have : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  have hr : Module.finrank (𝓞 E) N = n := by
    simpa using finrank_of_span_top N hN.span_eq_top
  have h := natCard_quot (R := 𝓞 E) (N := N) P.asIdeal
  rw [hr] at h
  exact finrank_of_card (F := Res P) h

set_option maxHeartbeats 1600000 in

theorem ranks : ∀ {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {S : GStep E K n} {ST : Finset (HeightOneSpectrum (𝓞 E))} (A : TDat S ST) (T : ℕ), S.Ok → A.Ok T → (∀ P c, Module.finrank (Res P.1) (A.lv P c) = n) ∧ ∀ P c, Module.finrank (Res P.1) (A.lk P c) = n := by
  intro E K _ _ _ _ n S ST A T _ h
  exact ⟨fun P c => finrank_red _ (h.N_lat _ _) P.1, fun P c => finrank_red _ (h.dnN_lat _ _ P) P.1⟩

end GlobalTheory.Mem.Col2.LRank
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Psi0TruncatedExplicitFormula
section
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.An.ExplUsed

theorem zsumR_inv_norm_nonneg {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    0 ≤ zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖) := by
  unfold zsumR
  refine finsum_nonneg fun ρ => finsum_nonneg fun _ => ?_
  positivity

theorem zsum_inv_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) :
    zsum χ⁻¹ 0 1 (fun ρ => 1 / (1 - ρ)) = zsum χ 0 1 (fun ρ => 1 / ρ) := by
  unfold zsum
  symm
  refine finsum_mem_eq_of_bijOn (fun ρ => 1 - ρ) ⟨?_, ?_, ?_⟩ ?_
  · rintro ρ ⟨h0, h1, h2, h3⟩
    refine ⟨by simp; linarith, by simp; linarith, by simpa using h2, ?_⟩
    exact (GlobalTheory.T.dirichlet_L_zero_symmetry q χ hχ ρ h0 h1).1.1 h3
  · intro a _ b _ h
    simpa using h
  · rintro ρ ⟨h0, h1, h2, h3⟩
    have a0 : 0 < (1 - ρ).re := by simp; linarith
    have a1 : (1 - ρ).re < 1 := by simp; linarith
    refine ⟨1 - ρ, ⟨a0, a1, by simpa using h2, ?_⟩, by simp⟩
    exact (GlobalTheory.T.dirichlet_L_zero_symmetry q χ hχ _ a0 a1).1.2 (by simpa using h3)
  · rintro ρ ⟨h0, h1, h2, h3⟩
    rw [(GlobalTheory.T.dirichlet_L_zero_symmetry q χ hχ ρ h0 h1).2]
    simp

theorem norm_zsum_inv_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ‖zsum χ 0 1 (fun ρ => 1 / ρ)‖ ≤ zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖) := by
  unfold zsum zsumR
  have hf := (GlobalTheory.T.dirichletLZerosInWindow_finite_and_pos_order q χ 0 1).1
  rw [finsum_mem_eq_finite_toFinset_sum _ hf, finsum_mem_eq_finite_toFinset_sum _ hf]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun ρ _ => ?_
  simp

theorem log_two_pi_bounds : 0 ≤ Real.log (2 * Real.pi) ∧ Real.log (2 * Real.pi) ≤ 7 := by
  have h3 := Real.pi_gt_three
  have h4 := Real.pi_le_four
  refine ⟨Real.log_nonneg (by linarith), ?_⟩
  have := Real.log_le_sub_one_of_pos (x := 2 * Real.pi) (by linarith)
  linarith

theorem half_le_log {u : ℝ} (hu : 2 ≤ u) : 1 / 2 ≤ Real.log u := by
  have h1 := Real.log_le_log (by norm_num) hu
  have h2 := Real.log_two_gt_d9
  linarith

theorem zeta_const_bound {u : ℝ} (hu : 2 ≤ u) :
    |Real.log (2 * Real.pi) + Real.log (1 - 1 / u ^ 2) / 2| ≤ 16 * Real.log u := by
  have h1 := log_two_pi_bounds
  have h2 := half_le_log hu
  have h3 : 1 / u ^ 2 ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) (by nlinarith)
  have h4 : 0 < 1 / u ^ 2 := by positivity
  have h5 : Real.log (1 - 1 / u ^ 2) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  have h6 : Real.log (1 / 2) ≤ Real.log (1 - 1 / u ^ 2) := Real.log_le_log (by norm_num) (by linarith)
  have h7 : Real.log (1 / 2) = - Real.log 2 := by rw [one_div, Real.log_inv]
  have h8 := Real.log_two_lt_d9
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2]

theorem explicit_formula_used : GlobalTheory.Mem.An.ExplZeta → GlobalTheory.Mem.An.ExplChi → GlobalTheory.Mem.An.LogDerOne → ∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ u T : ℝ, 2 ≤ T → T ≤ u → ‖GlobalTheoryTheory.psi0 χ u + zsum χ 0 T (fun ρ => (u : ℂ) ^ ρ / ρ)‖ ≤ C * (u * Real.log (q * u * T) ^ 2 / T + Real.log (q * u) + zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖)) := by
  rintro ⟨C₁, h₁⟩ ⟨C₂, h₂⟩ ⟨C₃, h₃⟩
  refine ⟨|C₁| + |C₂| + 4 * |C₃| + 20, fun q _ χ hχ u T hT hTu => ?_⟩
  have hu : 2 ≤ u := hT.trans hTu
  have hL := half_le_log hu
  have hS := zsumR_inv_norm_nonneg χ
  have hq0 : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq0
  have hlq : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hqu : Real.log (q * u) = Real.log q + Real.log u :=
    Real.log_mul (by positivity) (by positivity)
  have hE : u * Real.log (q * u * T) ^ 2 / T = u / T * Real.log (q * u * T) ^ 2 := by ring
  have hE0 : 0 ≤ u / T * Real.log (q * u * T) ^ 2 := by positivity
  have a1 := abs_nonneg C₁
  have a2 := abs_nonneg C₂
  have a3 := abs_nonneg C₃
  rw [hE, hqu]
  rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hq0) with hq | hq
  · have hq' : q = 1 := hq.symm
    subst hq'
    have hχ1 : χ = 1 := DirichletCharacter.level_one χ
    subst hχ1
    have h := h₁ u T hu hT
    have hA := zeta_const_bound hu
    simp only [Nat.cast_one, one_mul, Real.log_one, zero_add] at hE0 ⊢
    set E := u / T * Real.log (u * T) ^ 2
    set S := zsumR (1 : DirichletCharacter ℂ 1) 0 1 (fun ρ => 1 / ‖ρ‖)
    set A := Real.log (2 * Real.pi) + Real.log (1 - 1 / u ^ 2) / 2
    set Z := zsum (1 : DirichletCharacter ℂ 1) 0 T (fun ρ => (u : ℂ) ^ ρ / ρ)
    have e : GlobalTheoryTheory.psi0 (1 : DirichletCharacter ℂ 1) u + Z =
        (psiChi (1 : DirichletCharacter ℂ 1) u - (u : ℂ) + Z + (A : ℂ)) - (A : ℂ) := by
      simp only [GlobalTheoryTheory.psi0, psiChi, if_true]
      ring
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
    have h' : C₁ * (Real.log u + E) ≤ |C₁| * (Real.log u + E) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
    have hL0 : 0 ≤ Real.log u := by linarith
    nlinarith [mul_nonneg a1 hS, mul_nonneg a2 hS, mul_nonneg a3 hS, mul_nonneg a2 hE0, mul_nonneg a3 hE0,
      mul_nonneg a2 hL0, mul_nonneg a3 hL0]
  · have hq' : 1 < q := hq
    have hne : χ ≠ 1 := by
      rintro rfl
      have := hχ
      rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_one] at this
      omega
    have hχ' : χ⁻¹.IsPrimitive := by
      rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]
      exact hχ
    have h := h₂ q χ hq' hχ u T hu hT
    have g := h₃ q χ⁻¹ hq' hχ'
    rw [zsum_inv_eq χ hχ] at g
    have gz := norm_zsum_inv_le χ
    set E := u / T * Real.log (q * u * T) ^ 2
    set S := zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖)
    set Z := zsum χ 0 T (fun ρ => (u : ℂ) ^ ρ / ρ)
    set Y := zsum χ 0 1 (fun ρ => 1 / ρ)
    set D := deriv (DirichletCharacter.LFunction χ⁻¹) 1 / DirichletCharacter.LFunction χ⁻¹ 1
    set a : ℂ := ((Real.log (u - 1) / 2 : ℝ) : ℂ) with ha
    set b : ℂ := χ (-1) / 2 * ((Real.log (u + 1) : ℝ) : ℂ) with hb
    set c : ℂ := ((Real.log (q / (2 * Real.pi)) - Real.eulerMascheroniConstant : ℝ) : ℂ) with hc
    have hL0 : 0 ≤ Real.log u := by linarith
    have na : ‖a‖ ≤ Real.log u := by
      rw [ha, Complex.norm_real, Real.norm_eq_abs, abs_le]
      have b1 : 0 ≤ Real.log (u - 1) := Real.log_nonneg (by linarith)
      have b2 : Real.log (u - 1) ≤ Real.log u := Real.log_le_log (by linarith) (by linarith)
      constructor <;> linarith
    have nb : ‖b‖ ≤ Real.log u := by
      have b1 : 0 ≤ Real.log (u + 1) := Real.log_nonneg (by linarith)
      have b2 : Real.log (u + 1) ≤ Real.log (u ^ 2) := Real.log_le_log (by linarith) (by nlinarith)
      rw [Real.log_pow] at b2
      have b3 := χ.norm_le_one (-1)
      rw [hb, norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg b1]
      simp only [Complex.norm_ofNat]
      push_cast at b2
      nlinarith
    have nc : ‖c‖ ≤ Real.log q + 16 * Real.log u := by
      have b1 := log_two_pi_bounds
      have b2 := Real.one_half_lt_eulerMascheroniConstant
      have b3 := Real.eulerMascheroniConstant_lt_two_thirds
      rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_le,
        Real.log_div (by positivity) (by positivity)]
      constructor <;> linarith [b1.1, b1.2]
    have n3 : Real.log (3 * q) ≤ 4 * (Real.log q + Real.log u) := by
      rw [Real.log_mul (by positivity) (by positivity)]
      have := Real.log_le_sub_one_of_pos (x := 3) (by norm_num)
      linarith
    have n30 : 0 ≤ Real.log (3 * q) := Real.log_nonneg (by linarith)
    have g' : ‖D - Y‖ ≤ |C₃| * (4 * (Real.log q + Real.log u)) :=
      g.trans ((mul_le_mul_of_nonneg_right (le_abs_self _) n30).trans (mul_le_mul_of_nonneg_left n3 a3))
    have h' : C₂ * (Real.log u + E) ≤ |C₂| * (Real.log u + E) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
    have e : GlobalTheoryTheory.psi0 χ u + Z =
        (psiChi χ u + Z + a + b - (D + c)) - a - b + (D - Y) + Y + c := by
      simp only [GlobalTheoryTheory.psi0, psiChi, if_neg hne]
      ring
    rw [e]
    have t : ∀ w : ℂ, ‖w - a - b + (D - Y) + Y + c‖ ≤ ‖w‖ + ‖a‖ + ‖b‖ + ‖D - Y‖ + ‖Y‖ + ‖c‖ := by
      intro w
      have t1 := norm_add_le (w - a - b + (D - Y) + Y) c
      have t2 := norm_add_le (w - a - b + (D - Y)) Y
      have t3 := norm_add_le (w - a - b) (D - Y)
      have t4 := norm_sub_le (w - a) b
      have t5 := norm_sub_le w a
      linarith
    refine (t _).trans ?_
    nlinarith [mul_nonneg a1 hS, mul_nonneg a2 hS, mul_nonneg a3 hS, mul_nonneg a1 hE0, mul_nonneg a3 hE0,
      mul_nonneg a1 hL0, mul_nonneg a1 hlq, mul_nonneg a2 hlq]

end GlobalTheory.Mem.An.ExplUsed
end

