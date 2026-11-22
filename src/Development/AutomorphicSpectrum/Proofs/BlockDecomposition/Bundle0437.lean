import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0417
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0408
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0694
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0024
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0396
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0415
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0410
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0397
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0401
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0419
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
import Formalism.RealPlaceAnalysis.Bundle0004
import Formalism.PeriodIntegrals.Bundle0022
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0132
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0225
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0420
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.TemperednessTransfer
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SignAntisymmetric
section
noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.RealMult.Short

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open Formalism.REAL (dot nsq)

variable {n : ℕ}

theorem dL_add (u v w : Fin n → ℝ) : dot (u + v) w = dot u w + dot v w := by
  simp [dot, add_mul, sum_add_distrib]

theorem dL_sub (u v w : Fin n → ℝ) : dot (u - v) w = dot u w - dot v w := by
  simp [dot, sub_mul, sum_sub_distrib]

theorem dL_smul (c : ℝ) (u w : Fin n → ℝ) : dot (c • u) w = c * dot u w := by
  simp [dot, mul_sum, mul_assoc]

theorem d_comm (u v : Fin n → ℝ) : dot u v = dot v u := by
  simp [dot, mul_comm]

theorem dR_add (u v w : Fin n → ℝ) : dot u (v + w) = dot u v + dot u w := by
  simp [dot, mul_add, sum_add_distrib]

theorem dR_sub (u v w : Fin n → ℝ) : dot u (v - w) = dot u v - dot u w := by
  simp [dot, mul_sub, sum_sub_distrib]

theorem dR_smul (c : ℝ) (u w : Fin n → ℝ) : dot u (c • w) = c * dot u w := by
  rw [d_comm, dL_smul, d_comm]

theorem d_perm (u v : Fin n → ℝ) (w : Equiv.Perm (Fin n)) : dot (u ∘ w) (v ∘ w) = dot u v := by
  simpa [dot] using Equiv.sum_comp w (fun a => u a * v a)

theorem d_self_nonneg (u : Fin n → ℝ) : 0 ≤ dot u u :=
  sum_nonneg fun a _ => mul_self_nonneg _

theorem rho_sub (a b : Fin n) : rhoV n a - rhoV n b = (b : ℕ) - (a : ℕ) := by
  simp only [rhoV]; ring

theorem rho_anti : StrictAnti (rhoV n) := by
  intro a b h
  have h' : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast h
  have := rho_sub a b
  linarith

theorem rearr (u : Fin n → ℝ) (hu : Antitone u) (σ : Equiv.Perm (Fin n)) :
    dot u (rhoV n ∘ σ) ≤ dot u (rhoV n) :=
  Monovary.sum_mul_comp_perm_le_sum_mul (hu.monovary rho_anti.antitone)

def s0 (a b : Fin n) : ℝ := if a < b then 1 else if b < a then -1 else 0

def mB (B : Finset (Fin n × Fin n)) (a b : Fin n) : ℝ := if (a, b) ∈ B then 1 else 0

def sg (B : Finset (Fin n × Fin n)) (a b : Fin n) : ℝ := s0 a b - 2 * mB B a b + 2 * mB B b a

theorem sign_antisymmetric_alt (a b : Fin n) : s0 b a = -s0 a b := by
  unfold s0
  rcases lt_trichotomy a b with h | h | h
  · simp [h, asymm h]
  · simp [h]
  · simp [h, asymm h]

theorem sg_anti (B : Finset (Fin n × Fin n)) (a b : Fin n) : sg B b a = -sg B a b := by
  unfold sg; rw [sign_antisymmetric_alt a b]; ring

theorem sign_self_eq_zero (a : Fin n) : s0 a a = 0 := by simp [s0]

theorem sum_sign_eq_two_rho (a : Fin n) : ∑ b, s0 a b = 2 * rhoV n a := by
  have h : ∀ b, s0 a b = (if a < b then (1 : ℝ) else 0) - (if b < a then (1 : ℝ) else 0) := by
    intro b
    unfold s0
    rcases lt_trichotomy a b with h | h | h
    · simp [h, asymm h]
    · simp [h]
    · simp [h, asymm h]
  simp only [h, sum_sub_distrib, sum_boole]
  rw [Finset.filter_lt_eq_Ioi, Finset.filter_gt_eq_Iio, Fin.card_Ioi, Fin.card_Iio]
  have ha := a.2
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  simp [rhoV]
  ring

theorem sum_row_count (B : Finset (Fin n × Fin n)) (a : Fin n) :
    ∑ b, mB B a b = ((B.filter fun p => p.1 = a).card : ℝ) := by
  have : B.filter (fun p => p.1 = a) = (univ.filter fun b => (a, b) ∈ B).image (fun b => (a, b)) := by
    ext ⟨x, y⟩
    simp only [mem_filter, mem_image, mem_univ, true_and, Prod.mk.injEq]
    constructor
    · rintro ⟨h, rfl⟩; exact ⟨y, h, rfl, rfl⟩
    · rintro ⟨c, h, rfl, rfl⟩; exact ⟨h, rfl⟩
  rw [this, card_image_of_injective _ (fun x y h => (Prod.mk.inj h).2)]
  simp [mB]

theorem sum_column_count (B : Finset (Fin n × Fin n)) (a : Fin n) :
    ∑ b, mB B b a = ((B.filter fun p => p.2 = a).card : ℝ) := by
  have : B.filter (fun p => p.2 = a) = (univ.filter fun b => (b, a) ∈ B).image (fun b => (b, a)) := by
    ext ⟨x, y⟩
    simp only [mem_filter, mem_image, mem_univ, true_and, Prod.mk.injEq]
    constructor
    · rintro ⟨h, rfl⟩; exact ⟨x, h, rfl, rfl⟩
    · rintro ⟨c, h, rfl, rfl⟩; exact ⟨h, rfl⟩
  rw [this, card_image_of_injective _ (fun x y h => (Prod.mk.inj h).1)]
  simp [mB]

theorem sum_sg (B : Finset (Fin n × Fin n)) (a : Fin n) :
    ∑ b, sg B a b = 2 * (rhoV n a - wtB B a) := by
  simp only [sg, sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_sign_eq_two_rho, sum_row_count, sum_column_count, wtB]
  ring

theorem sg_val (B : Finset (Fin n × Fin n)) (hB : ∀ p ∈ B, p.1 < p.2) {a b : Fin n} (hab : a ≠ b) :
    sg B a b = 1 ∨ sg B a b = -1 := by
  have key : ∀ a b : Fin n, a < b → sg B a b = 1 ∨ sg B a b = -1 := by
    intro a b h
    have h1 : (b, a) ∉ B := fun hm => asymm h (hB _ hm)
    by_cases hm : (a, b) ∈ B
    · right; simp [sg, s0, mB, h, h1, hm]; norm_num
    · left; simp [sg, s0, mB, h, h1, hm]
  rcases lt_or_gt_of_ne hab with h | h
  · exact key a b h
  · rw [sg_anti B b a]
    rcases key b a h with h' | h' <;> simp [h']

theorem cyc (f : Fin n → Fin n → Fin n → ℝ) : ∑ a, ∑ b, ∑ c, f b c a = ∑ a, ∑ b, ∑ c, f a b c := by
  rw [sum_comm]
  refine sum_congr rfl fun b _ => ?_
  rw [sum_comm]

end GlobalTheory.CompanionTheory.RealMult.Short

namespace GlobalTheory.CompanionTheory.RealMult

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open Formalism.REAL (dot nsq)
open Short

end GlobalTheory.CompanionTheory.RealMult
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimpleLoweringPowMemIdeal
section
set_option maxSynthPendingDepth 1

noncomputable section

open GroundTheory.Automorphic.HarishChandra

namespace GlobalTheory.CompanionTheory.PresRho

variable {n : ℕ}

def adL (F u : U n) : U n := F * u - u * F

theorem adL_zero (F : U n) : adL F 0 = 0 := by simp [adL]

theorem adL_sub (F u v : U n) : adL F (u - v) = adL F u - adL F v := by
  simp only [adL, mul_sub, sub_mul]; abel

theorem adL_neg (F u : U n) : adL F (-u) = - adL F u := by
  simp only [adL, mul_neg, neg_mul]; abel

theorem adL_e (i j c d : Fin n) :
    adL (e (j, i)) (e (c, d)) =
      (if i = c then e (j, d) else 0) - (if d = j then e (c, i) else 0) :=
  e_mul_sub_mul (j, i) (c, d)

theorem adL_iter_e {i j : Fin n} (hij : i ≠ j) (a : Fin n × Fin n) :
    (adL (e (j, i)))^[3] (e a) = 0 := by
  obtain ⟨c, d⟩ := a
  show adL (e (j, i)) (adL (e (j, i)) (adL (e (j, i)) (e (c, d)))) = 0
  have hji : j ≠ i := hij.symm
  by_cases h1 : i = c <;> by_cases h2 : d = j
  · subst h1; subst h2
    simp [adL_e, adL_sub, adL_neg, adL_zero, hij, hji]
  · subst h1
    simp [adL_e, adL_sub, adL_neg, adL_zero, hij, hji, h2]
  · subst h2
    simp [adL_e, adL_sub, adL_neg, adL_zero, hij, hji, h1]
  · simp [adL_e, adL_sub, adL_neg, adL_zero, h1, h2]

theorem pow_mul_mem_Jp_of_le {F w : U n} {N N' : ℕ} (h : N ≤ N') (hw : F ^ N * w ∈ Jp n) :
    F ^ N' * w ∈ Jp n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' h
  rw [pow_add, mul_assoc]
  exact mul_mem_Jp _ hw

theorem exists_pow_mul_mul_mem (F : U n) (s : ℕ) :
    ∀ (r M : ℕ) (u y : U n), r + M = s → (adL F)^[r] u = 0 → F ^ M * y ∈ Jp n →
      ∃ N : ℕ, F ^ N * (u * y) ∈ Jp n := by
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro r M u y hs hu hy
    rcases M with _ | M
    · refine ⟨0, ?_⟩
      rw [pow_zero, one_mul] at hy ⊢
      exact mul_mem_Jp u hy
    rcases r with _ | r
    · refine ⟨0, ?_⟩
      have : u = 0 := hu
      simp [this]
    obtain ⟨N₁, h₁⟩ := ih (r + 1 + M) (by omega) (r + 1) M u (F * y) rfl hu
      (by rw [← mul_assoc, ← pow_succ]; exact hy)
    obtain ⟨N₂, h₂⟩ := ih (r + (M + 1)) (by omega) r (M + 1) (adL F u) y rfl
      (by rw [← Function.iterate_succ_apply]; exact hu) hy
    refine ⟨max N₁ N₂ + 1, ?_⟩
    have key : F ^ (max N₁ N₂ + 1) * (u * y) =
        F ^ max N₁ N₂ * (u * (F * y)) + F ^ max N₁ N₂ * (adL F u * y) := by
      rw [pow_succ, ← mul_add, mul_assoc]
      congr 1
      simp only [adL, sub_mul, mul_assoc]
      abel
    rw [key]
    exact Submodule.add_mem _ (pow_mul_mem_Jp_of_le (le_max_left _ _) h₁)
      (pow_mul_mem_Jp_of_le (le_max_right _ _) h₂)

theorem lower_locally_nilpotent {n : ℕ} (i j : Fin n) (x : U n) (hij : (j : ℕ) = i + 1) :
    ∃ N : ℕ, e (j, i) ^ N * x ∈ Jp n := by
  have hne : i ≠ j := by
    intro h
    rw [h] at hij
    omega
  have step : ∀ v : U n, ∀ y : U n, (∃ N : ℕ, e (j, i) ^ N * y ∈ Jp n) →
      ∃ N : ℕ, e (j, i) ^ N * (v * y) ∈ Jp n := by
    intro v
    induction v using U.induction with
    | halg r =>
      rintro y ⟨N, hN⟩
      refine ⟨N, ?_⟩
      rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, mul_smul_comm]
      exact Submodule.smul_mem _ r hN
    | hι X =>
      intro y hy
      obtain ⟨M, hM⟩ := hy
      have hsum : ∀ t : Finset (Fin n × Fin n), ∃ N : ℕ, e (j, i) ^ N *
          ((∑ a ∈ t, X a.1 a.2 • e (n := n) a) * y) ∈ Jp n := by
        intro t
        induction t using Finset.induction_on with
        | empty => exact ⟨0, by simp⟩
        | insert a t ha ih =>
          obtain ⟨N₁, h₁⟩ := ih
          obtain ⟨N₂, h₂⟩ := exists_pow_mul_mul_mem (e (j, i)) (3 + M) 3 M (e a) y rfl
            (adL_iter_e hne a) hM
          refine ⟨max N₁ N₂, ?_⟩
          rw [Finset.sum_insert ha, add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
          exact Submodule.add_mem _
            (Submodule.smul_mem _ _ (pow_mul_mem_Jp_of_le (le_max_right _ _) h₂))
            (pow_mul_mem_Jp_of_le (le_max_left _ _) h₁)
      rw [ι_eq_sum_e]
      exact hsum Finset.univ
    | hmul a b ha hb =>
      intro y hy
      rw [mul_assoc]
      exact ha _ (hb _ hy)
    | hadd a b ha hb =>
      intro y hy
      obtain ⟨N₁, h₁⟩ := ha y hy
      obtain ⟨N₂, h₂⟩ := hb y hy
      refine ⟨max N₁ N₂, ?_⟩
      rw [add_mul, mul_add]
      exact Submodule.add_mem _ (pow_mul_mem_Jp_of_le (le_max_left _ _) h₁)
        (pow_mul_mem_Jp_of_le (le_max_right _ _) h₂)
  have h1 : ∃ N : ℕ, e (j, i) ^ N * (1 : U n) ∈ Jp n :=
    ⟨2, by simpa using mul_sq_mem_Jp (1 : U n) hij⟩
  simpa using step x 1 h1

end GlobalTheory.CompanionTheory.PresRho
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SquareIntegrableOfHeckeSpectral
section
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.SqIntHecke

theorem lintegral_sq_lt_top_of_cover {X ι κ : Type*} [MeasurableSpace X] (μ : Measure X) (F : X → ℝ) [Finite ι]
    [Countable κ] (A : ι → κ → Set X) (hcov : ∀ x, ∃ i j, x ∈ A i j) (b w : ι → κ → ℝ) (hw : ∀ i j, 0 ≤ w i j)
    (E : ENNReal) (hE : E < ⊤) (hF : ∀ i j, ∀ x ∈ A i j, ‖F x‖ ≤ b i j)
    (hμ : ∀ i j, μ (A i j) ≤ ENNReal.ofReal (w i j) * E)
    (hsum : ∀ i, Summable fun j => b i j ^ 2 * w i j) :
    ∫⁻ x, ‖F x‖ₑ ^ (2 : ℝ) ∂μ < ⊤ := by
  classical
  have := Fintype.ofFinite ι
  have hu : (⋃ p : ι × κ, A p.1 p.2) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨i, j, h⟩ := hcov x
    exact ⟨(i, j), h⟩
  have h1 : ∫⁻ x, ‖F x‖ₑ ^ (2 : ℝ) ∂μ ≤ ∑' p : ι × κ, ∫⁻ x in A p.1 p.2, ‖F x‖ₑ ^ (2 : ℝ) ∂μ := by
    conv_lhs => rw [← setLIntegral_univ, ← hu]
    exact lintegral_iUnion_le _ _
  have h2 : ∀ p : ι × κ, ∫⁻ x in A p.1 p.2, ‖F x‖ₑ ^ (2 : ℝ) ∂μ ≤
      ENNReal.ofReal (b p.1 p.2 ^ 2 * w p.1 p.2) * E := by
    rintro ⟨i, j⟩
    have h3 : ∫⁻ x in A i j, ‖F x‖ₑ ^ (2 : ℝ) ∂μ ≤ ∫⁻ x in A i j, ENNReal.ofReal (b i j ^ 2) ∂μ := by
      refine setLIntegral_mono measurable_const fun x hx => ?_
      rw [ENNReal.rpow_two, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (hF i j x hx) 2)
    refine h3.trans ?_
    rw [setLIntegral_const, ENNReal.ofReal_mul (sq_nonneg _), mul_assoc]
    gcongr
    exact hμ i j
  refine (h1.trans (ENNReal.tsum_le_tsum h2)).trans_lt ?_
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_prod (f := fun i j => ENNReal.ofReal (b i j ^ 2 * w i j))]
  refine ENNReal.mul_lt_top ?_ hE
  rw [tsum_fintype]
  refine ENNReal.sum_lt_top.2 fun i _ => ?_
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg (sq_nonneg _) (hw i j)) (hsum i)]
  exact ENNReal.ofReal_lt_top

theorem sq_mul_pow_eq {r : ℕ} (q : ℝ) (e g : Fin r → ℕ) (ρ : Fin r → ℝ) (C : ℝ) :
    (C * ∏ j, ρ j ^ g j) ^ 2 * q ^ (∑ j, g j * e j) = C ^ 2 * ∏ j, (q ^ e j * ρ j ^ 2) ^ g j := by
  have h1 : ∏ j, (q ^ e j) ^ g j = q ^ (∑ j, g j * e j) := by
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_congr rfl fun j _ => by rw [← pow_mul, mul_comm]
  have h2 : ∏ j, (ρ j ^ 2) ^ g j = (∏ j, ρ j ^ g j) ^ 2 := by
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl fun j _ => by rw [← pow_mul, ← pow_mul, mul_comm]
  simp only [mul_pow _ _ (g _)]
  rw [Finset.prod_mul_distrib, h1, h2, mul_pow C, mul_assoc, mul_comm (q ^ _)]

theorem isSqIntCoeff_of_heckeSpectral : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → π.IsIrreducible → IsAdmissible π → Zls.UnitaryCentral π →
    Zls.HeckeSpectral π → IsSqIntCoeff π := by
  intro k _ _ _ _ N V _ _ π hs hi ha hu hH
  unfold IsSqIntCoeff CoeffLp
  intro _ _ μ hμ v l hl
  have hcen : ∀ z ∈ Subgroup.center (GL (Fin N) k), ∀ w, ‖l (π z w)‖ = ‖l w‖ := by
    intro z hz w
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz
    obtain ⟨t, rfl⟩ := hz
    obtain ⟨c, hc⟩ := GlobalTheory.T.admissible_irreducible_central_scalar k N V π hs hi ha t
    rw [hc, map_smul, norm_smul, hu t c hc, one_mul]
  have hF : ∀ g : GL (Fin N) k, ‖l (π (QuotientGroup.mk g : AdGL k N).out v)‖ = ‖l (π g v)‖ := by
    intro g
    obtain ⟨z, hz⟩ := QuotientGroup.mk_out_eq_mul (Subgroup.center (GL (Fin N) k)) g
    rw [hz, Subgroup.mem_center_iff.1 z.2 g, map_mul, Module.End.mul_apply, hcen _ z.2]
  refine ⟨fun q => ‖l (π q.out v)‖, hF, ?_, ?_⟩
  · refine Continuous.aestronglyMeasurable ((QuotientGroup.isQuotientMap_mk _).continuous_iff.2 ?_)
    rw [show (fun q : AdGL k N => ‖l (π q.out v)‖) ∘ QuotientGroup.mk = fun g => ‖l (π g v)‖ from funext hF]
    exact ((SqIntBridge.isLocallyConstant_orbit hs v).comp fun w => ‖l w‖).continuous
  rw [show ENNReal.ofReal 2 = 2 by simp, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have : Subsingleton (GL (Fin 0) k) := inferInstance
    have h1 : Subsingleton (AdGL k 0) := inferInstance
    have h2 : μ Set.univ < ⊤ := isCompact_univ.measure_lt_top
    refine lintegral_sq_lt_top_of_cover μ _ (fun _ _ : Unit => Set.univ) (fun _ => ⟨(), (), trivial⟩)
      (fun _ _ => ‖l (π (1 : AdGL k 0).out v)‖) (fun _ _ => 1) (fun _ _ => zero_le_one) _ h2 ?_ (by simp)
      (fun _ => (hasSum_fintype _).summable)
    intro _ _ x _
    rw [Subsingleton.elim x 1, norm_norm]
  obtain ⟨m1, hm1, hK1⟩ := GlobalTheory.T.congruence_subgroup_basis_nhds k N _ (hs v) (by simp)
  obtain ⟨m2, hm2, hK2⟩ := GlobalTheory.T.congruence_subgroup_basis_nhds k N _ hl (by simp [Module.End.one_eq_id])
  have hm : 1 ≤ max m1 m2 := hm1.trans (le_max_left _ _)
  obtain ⟨m, hmm⟩ : ∃ m, m = max m1 m2 := ⟨_, rfl⟩
  rw [← hmm] at hm
  have hv : v ∈ fixed π (Zls.Km k N m) := by
    rintro ⟨x, hx⟩
    have : π x v = v := hK1 (GlobalTheory.T.congruence_subgroup_antitone k N m1 m (hmm ▸ le_max_left _ _) hx)
    simpa using this
  have hlK : ∀ x ∈ Zls.Km k N m, l ∘ₗ π x = l := fun x hx =>
    hK2 (GlobalTheory.T.congruence_subgroup_antitone k N m2 m (hmm ▸ le_max_right _ _) hx)
  obtain ⟨s, hsK, hcov⟩ := GlobalTheory.T.cartan_decomposition_congruence k N m hm hN
  have key : ∀ p : s, ∃ (C : ℝ) (ρ : Fin (N - 1) → ℝ), (∀ j, 0 ≤ ρ j) ∧
      (∀ j : Fin (N - 1), (Nat.card 𝓀[k] : ℝ) ^ (((j : ℕ) + 1) * (N - ((j : ℕ) + 1))) * ρ j ^ 2 < 1) ∧
      ∀ g : Fin (N - 1) → ℕ, ∀ x ∈ Zls.Km k N m, ∀ y ∈ Zls.Km k N m,
        ‖l (π (p.1.1 * x * Zls.diagPow k N (Zls.lamOf g) * y * p.1.2) v)‖ ≤ C * ∏ j, ρ j ^ g j := by
    rintro ⟨p, hp⟩
    obtain ⟨h1, h2⟩ := hsK p hp
    obtain ⟨hf, hli, heq⟩ := GlobalTheory.T.matrix_coefficient_cartan_translate k N V π m v hv l hlK p.1 p.2 h1 h2
    obtain ⟨C, ρ, hρ0, hρ1, hb⟩ := GlobalTheory.T.matrix_coefficient_hecke_decay k N V π hs ha hH m hm (π p.2 v) hf (l ∘ₗ π p.1) hli
    refine ⟨C, ρ, hρ0, hρ1, fun g x hx y hy => ?_⟩
    rw [heq _ x hx y hy]
    exact hb g
  choose C ρ hρ0 hρ1 hbound using key
  refine lintegral_sq_lt_top_of_cover μ _
    (fun (p : s) (g : Fin (N - 1) → ℕ) => (QuotientGroup.mk : GL (Fin N) k → AdGL k N) ''
      {h | ∃ x ∈ Zls.Km k N m, ∃ y ∈ Zls.Km k N m, h = p.1.1 * x * Zls.diagPow k N (Zls.lamOf g) * y * p.1.2})
    ?_ (fun p g => C p * ∏ j, ρ p j ^ g j)
    (fun _ g => (Nat.card 𝓀[k] : ℝ) ^ (∑ j : Fin (N - 1), g j * (((j : ℕ) + 1) * (N - ((j : ℕ) + 1)))))
    (fun _ _ => by positivity)
    (μ ((QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' (Zls.Km k N m : Set (GL (Fin N) k))))
    (GlobalTheory.T.congruence_subgroup_finite_volume k N μ hμ m) ?_ ?_ ?_
  · intro x
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨p, hp, g, a, ha', b, hb, z, hz, rfl⟩ := hcov h
    exact ⟨⟨p, hp⟩, g, _, ⟨a, ha', b, hb, rfl⟩, (QuotientGroup.mk_mul_of_mem _ hz).symm⟩
  · rintro p g _ ⟨h, ⟨a, ha', b, hb, rfl⟩, rfl⟩
    show ‖‖l (π (QuotientGroup.mk _ : AdGL k N).out v)‖‖ ≤ _
    rw [norm_norm, hF]
    exact hbound p g a ha' b hb
  · intro p g
    obtain ⟨h1, h2⟩ := hsK p.1 p.2
    refine (GlobalTheory.T.double_coset_volume_le k N μ hμ m hm p.1.1 p.1.2 h1 h2 g).trans_eq ?_
    rw [ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  · intro p
    have h := GlobalTheory.CompanionTheory.Summability.summable_prod_pow_multiIndex (N - 1)
      (fun j => (Nat.card 𝓀[k] : ℝ) ^ (((j : ℕ) + 1) * (N - ((j : ℕ) + 1))) * ρ p j ^ 2)
      (fun j => by positivity) (hρ1 p)
    exact (h.mul_left (C p ^ 2)).congr fun g => (sq_mul_pow_eq _ _ g _ _).symm

end GlobalTheory.CompanionTheory.SqIntHecke
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubquotientRealisedBySubrepsStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subquotient_realised_by_subreps : ∀ {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (π : Representation ℂ G W), IsSubquotient π ρ → ∃ A B : Subrepresentation ρ, B ≤ A ∧ Nonempty (π.Equiv (subQuot A B)) := by
  first | exact @GlobalTheory.CompanionTheory.SubquotPres.exists_equiv_subQuot | exact GlobalTheory.CompanionTheory.SubquotPres.exists_equiv_subQuot | (intros; apply GlobalTheory.CompanionTheory.SubquotPres.exists_equiv_subQuot <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumCycWordEqEtr
section
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.CycWordTrace

theorem sum_cycWord_eq_etr : ∀ (B : Type) [Ring B] (n m : ℕ) (X : Fin n → Fin n → B),
    ∑ a : Fin (m + 1) → Fin n, ((GlobalTheory.Dec.cycWord a).map fun p => X p.1 p.2).prod
      = Formalism.REAL.etr X (m + 1) := by
  intro B _ n m X
  exact (GlobalTheory.TraceCycWord.etr_succ_eq_sum_cycWord X m).symm

end GlobalTheory.CompanionTheory.CycWordTrace
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SupEqOfIrreducibleSubquotientStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sup_eq_of_irreducible_subquotient : ∀ {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (A B E : Subrepresentation ρ), B ≤ A → (subQuot A B).IsIrreducible → E ≤ A → ¬ E ≤ B → E ⊔ B = A := by
  first | exact @GlobalTheory.CompanionTheory.GenCore.sup_eq_of_isIrreducible_subQuot | exact GlobalTheory.CompanionTheory.GenCore.sup_eq_of_isIrreducible_subQuot | (intros; apply GlobalTheory.CompanionTheory.GenCore.sup_eq_of_isIrreducible_subQuot <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperedRestrictionStatement
section
open LocalGlobalAboveLAlt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tempered_restriction : TempRes := by
  first | exact @GlobalTheory.CompanionTheory.TempRes.tempRes | exact GlobalTheory.CompanionTheory.TempRes.tempRes | (intros; apply GlobalTheory.CompanionTheory.TempRes.tempRes <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorProductRankLeOneStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_product_rank_le_one : ∀ {α : Type} [Fintype α] (M : α → Type) [∀ a, AddCommGroup (M a)] [∀ a, Module ℂ (M a)], (∀ a, Module.rank ℂ (M a) ≤ 1) → Module.rank ℂ (⨂[ℂ] a, M a) ≤ 1 := by
  first | exact @GlobalTheory.CompanionTheory.TensorRank.rank_piTensorProduct_le_one | exact GlobalTheory.CompanionTheory.TensorRank.rank_piTensorProduct_le_one | (intros; apply GlobalTheory.CompanionTheory.TensorRank.rank_piTensorProduct_le_one <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedJacquetIteratedPhiEquiv
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

namespace GlobalTheory.CompanionTheory.BZMir

theorem iterPhi_twJacquet_equiv (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (n j : ℕ) (τ : MRep k (n + j)) :
    Nonempty (TwJacquet (iterPhi k ψ j τ).ρ (MirUin k n) 1 ≃ₗ[ℂ]
      TwJacquet τ.ρ (derUnipM k (n + j) n) (derCharM k ψ (n + j) n)) := by
  induction j with
  | zero =>
    exact ⟨Submodule.quotEquivOfEq _ _ (GlobalTheory.T.mirabolic_twisted_kernel_derivative_zero k ψ n τ.V τ.ρ)⟩
  | succ j ih =>
    obtain ⟨e₁⟩ := ih (MRep.phiM k ψ τ)
    obtain ⟨e₂⟩ := GlobalTheory.T.twisted_jacquet_phi_minus_equiv k ψ (n + j) n (Nat.le_add_right n j) τ.V τ.ρ
    exact ⟨e₁.trans e₂⟩

end GlobalTheory.CompanionTheory.BZMir
end

