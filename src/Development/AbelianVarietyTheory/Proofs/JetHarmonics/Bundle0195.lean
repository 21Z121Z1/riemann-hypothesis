import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0194
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0003
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
import Formalism.SharpRestriction.CuspSpanNormBounds.OnePlaceEstimates
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0187
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0469
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0115
import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0033
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0027
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GramSpace
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0026
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0037
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0041
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0039
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroSplitOfLocalAndSum
import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0306
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0305
import Formalism.HermitianCurvature.Bundle0004
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0029
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0027
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0163
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0108
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0190
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0186
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0002
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0208
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0164
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0004

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.AllGoodPrimeDepthDataExistProofStatement
section
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.allGoodPrimeDepthDataExist_proof : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], PkgSt Xo c := by
  first | exact @GlobalTheory.goodPrime_packages | exact GlobalTheory.goodPrime_packages | (intros; apply GlobalTheory.goodPrime_packages <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BpFormsOfThmBpDS
section
open BpJoin Formalism.FourierDecayAlt Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.QuantumDeterminants GlobalTheory.ThA

namespace GlobalTheory

theorem bpNear_thresholds (k r : ℕ) (hk : 1 ≤ k) :
    2 * ThreeDimData.Mexp r * (ThreeDimData.AS k r + ThreeDimData.AG k r) + ThreeDimData.AG k r + 3 ≤
        31 * (((r : ℝ) + 1) ^ 4 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3) ∧
      9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + 3 * ThreeDimData.AG k r + 3 ≤
        24 * (((r : ℝ) + 1) ^ 4 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3) ∧
      ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1) ≤
        2 * (((r : ℝ) + 1) ^ 4 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3) ∧
      1 ≤ ((r : ℝ) + 1) ^ 4 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 := by
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hn : ((2 * r + k + 1 : ℕ) : ℝ) = 2 * r + k + 1 := by push_cast; ring
  set n : ℝ := ((2 * r + k + 1 : ℕ) : ℝ) with hndef
  set s : ℝ := (r : ℝ) + 1 with hs
  have hs1 : 1 ≤ s := by linarith
  have hn1 : 1 ≤ n := by linarith
  have key : ∀ i j : ℕ, i ≤ 4 → j ≤ 3 → s ^ i * n ^ j ≤ s ^ 4 * n ^ 3 := fun i j hi hj =>
    mul_le_mul (pow_le_pow_right₀ hs1 hi) (pow_le_pow_right₀ hn1 hj) (by positivity) (by positivity)
  have hM : ThreeDimData.Mexp r ≤ 2 * s ^ 2 := by unfold ThreeDimData.Mexp; rw [hs]; nlinarith
  have hM0 : 0 ≤ ThreeDimData.Mexp r := by unfold ThreeDimData.Mexp; positivity
  have hG : ThreeDimData.AG k r ≤ 4 * n * s := by
    unfold ThreeDimData.AG; rw [← hs]
    have : (k : ℝ) + r ≤ n := by linarith
    nlinarith
  have hG0 : 0 ≤ ThreeDimData.AG k r := by unfold ThreeDimData.AG; positivity
  have hd : ThreeDimData.dN k r ≤ 2 * s * n := by unfold ThreeDimData.dN; rw [hs, hn]; nlinarith [mul_nonneg hr hr]
  have hd0 : 0 ≤ ThreeDimData.dN k r := by unfold ThreeDimData.dN; nlinarith [mul_nonneg hr hr, mul_nonneg hr (by linarith : (0 : ℝ) ≤ k)]
  have hS : ThreeDimData.AS k r ≤ n * (2 * s * n) := by
    unfold ThreeDimData.AS
    refine mul_le_mul ?_ hd hd0 (by linarith)
    rw [hn]; push_cast; linarith
  have hS0 : 0 ≤ ThreeDimData.AS k r := by unfold ThreeDimData.AS; positivity
  have hP : ThreeDimData.Mexp r * (ThreeDimData.AS k r + ThreeDimData.AG k r) ≤ 2 * s ^ 2 * (n * (2 * s * n) + 4 * n * s) :=
    mul_le_mul hM (by linarith) (by linarith) (by positivity)
  have k32 := key 3 2 (by omega) (by omega)
  have k31 := key 3 1 (by omega) (by omega)
  have k11 := key 1 1 (by omega) (by omega)
  have k12 := key 1 2 (by omega) (by omega)
  have k20 := key 2 0 (by omega) (by omega)
  have k00 := key 0 0 (by omega) (by omega)
  have hrn : s ^ 2 * (r * n) ≤ s ^ 3 * n ^ 1 := by
    have : (r : ℝ) * n ≤ s * n := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    calc s ^ 2 * (r * n) ≤ s ^ 2 * (s * n) := mul_le_mul_of_nonneg_left this (by positivity)
      _ = s ^ 3 * n ^ 1 := by ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · nlinarith
  · simpa using k00

theorem bpNear_gapOK (k r : ℕ) (hk : 1 ≤ k) (c Cg : ℝ) (hC : 240 + 2 * |c| ≤ Cg) :
    ThreeDimData.GapOK k r (Cg * ((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
      (((3 * (r + 1) : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + ((2 * r + k + 1 : ℕ) : ℝ) ^ 3) / 2) ∧
    c * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1) ≤
      ThreeDimData.aOf r (Cg * ((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
        (((3 * (r + 1) : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + ((2 * r + k + 1 : ℕ) : ℝ) ^ 3) / 2) - 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := bpNear_thresholds k r hk
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hc : 0 ≤ |c| := abs_nonneg c
  have hm : ((2 * r + 2 : ℕ) : ℝ) = 2 * ((r : ℝ) + 1) := by push_cast; ring
  have hn0 : (0 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hN0 : (0 : ℝ) ≤ ((3 * (r + 1) : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [hm]
  set n : ℝ := ((2 * r + k + 1 : ℕ) : ℝ) with hndef
  set N : ℝ := ((3 * (r + 1) : ℕ) : ℝ)
  have hs1 : (1 : ℝ) ≤ 2 * ((r : ℝ) + 1) := by linarith
  have hpos : (0 : ℝ) < 2 * ((r : ℝ) + 1) := by linarith
  have hsq : 0 < Real.sqrt (2 * ((r : ℝ) + 1)) := Real.sqrt_pos.2 hpos
  have hpow : (2 * ((r : ℝ) + 1)) ^ ((9 : ℝ) / 2) =
      (2 * ((r : ℝ) + 1)) ^ 4 * Real.sqrt (2 * ((r : ℝ) + 1)) := by
    rw [Real.sqrt_eq_rpow, show (9 : ℝ) / 2 = (4 : ℕ) + 1 / 2 by norm_num, Real.rpow_add hpos, Real.rpow_natCast]
  have hge : 1 ≤ (2 * ((r : ℝ) + 1)) ^ ((9 : ℝ) / 2) := Real.one_le_rpow hs1 (by norm_num)
  have hZ : n ^ 3 ≤ N * n ^ 2 + n ^ 3 := by have : 0 ≤ N * n ^ 2 := by positivity
                                            linarith
  have hCg : 0 ≤ Cg := by linarith
  have ha : Cg * (((r : ℝ) + 1) ^ 4 * n ^ 3) ≤
      ThreeDimData.aOf r (Cg * (2 * ((r : ℝ) + 1)) ^ ((9 : ℝ) / 2) * (N * n ^ 2 + n ^ 3) / 2) := by
    have e : ThreeDimData.aOf r (Cg * (2 * ((r : ℝ) + 1)) ^ ((9 : ℝ) / 2) * (N * n ^ 2 + n ^ 3) / 2) =
        Cg * (((r : ℝ) + 1) ^ 4 * (N * n ^ 2 + n ^ 3)) := by
      unfold ThreeDimData.aOf; rw [hpow]; field_simp; ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hZ (by positivity)) hCg
  set Y : ℝ := ((r : ℝ) + 1) ^ 4 * n ^ 3 with hY
  have hCY : (240 + 2 * |c|) * Y ≤ Cg * Y := mul_le_mul_of_nonneg_right hC (by linarith)
  have hcY : 0 ≤ |c| * Y := mul_nonneg hc (by linarith)
  refine ⟨⟨hk, ?_, by linarith, by linarith⟩, ?_⟩
  · have e1 : 240 * 1 ≤ Cg * (2 * ((r : ℝ) + 1)) ^ ((9 : ℝ) / 2) :=
      mul_le_mul (by linarith) hge (by norm_num) hCg
    have e2 : 240 * 1 * n ^ 3 ≤ Cg * (2 * ((r : ℝ) + 1)) ^ ((9 : ℝ) / 2) * (N * n ^ 2 + n ^ 3) :=
      mul_le_mul e1 hZ (by positivity) (by positivity)
    linarith
  · have e0 : 0 ≤ ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * n + 1) := by positivity
    have e1 : c * (((r : ℝ) + 1) ^ 2 * ((r : ℝ) * n + 1)) ≤ |c| * (2 * Y) :=
      mul_le_mul (le_abs_self c) h3 e0 hc
    nlinarith

theorem bpNear_gapAtLeast {n : ℕ} (ε : Fin n → Bool) (lam lam0 : Fin n → ℝ) (h : ℝ) (h0 : GapAtLeast ε lam0 h)
    (hg : AllGaps lam0 (200 * l1 lam lam0)) : GapAtLeast ε lam (h / 2) := by
  intro a b hab
  have hne : a ≠ b := fun e => hab (by rw [e])
  have h1 := h0 a b hab
  have h2 := hg a b hne
  have hd : ∀ s, |lam s - lam0 s| ≤ l1 lam lam0 := fun s =>
    Finset.single_le_sum (f := fun a => |lam a - lam0 a|) (fun _ _ => abs_nonneg _) (Finset.mem_univ s)
  have h3 : |lam0 a - lam0 b| ≤ |lam a - lam b| + |lam a - lam0 a| + |lam b - lam0 b| := by
    have e : lam0 a - lam0 b = (lam a - lam b) - (lam a - lam0 a) + (lam b - lam0 b) := by ring
    rw [e]
    exact (abs_add_le _ _).trans (by linarith [abs_sub (lam a - lam b) (lam a - lam0 a)])
  linarith [hd a, hd b, abs_nonneg (lam0 a - lam0 b)]

theorem bp_forms_of_thmBpDS : BranchingSupport.Hyps → ThmBpDS → ∀ Ch : ℝ, ∃ Cb Cg₀ : ℝ, ∀ Cg : ℝ, Cg₀ ≤ Cg → (∀ (D : D7) (L : LocBessel D.R.k D.R.rS) (lam0 : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (f : B.Mat D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)) (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) (ka b : ℝ), LocOk D Ch Cg L lam0 ka b 1 → AllGaps lam0 (200 * l1 L.lam lam0) → IsKFinCoefH L.σ f → IsSection D.R.k D.R.rS L.z L.z' μsec → ∀ γ : Point ℂ (D.R.rS + 1), Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ ≠ 0 → BpIneq D Cb L f μsec b γ) ∧ (∀ D : D7, Formalism.MainNotions.OnePlaceEstimates.TheoremBPrimePointwise D Ch Cg Cb) ∧ ∀ (D : D7) (Cu Cg' : ℝ), 200 * Cu ≤ Cg' → Formalism.MainNotions.OnePlaceEstimates.UniformityTheoremBPrime D Ch Cu Cg Cg' Cb := by
  intro hH hT Ch
  obtain ⟨C₄, G₀, hC₄, hloc⟩ := GlobalTheory.T.exists_local_section_bounds hT Ch
  obtain ⟨c₃, hdict⟩ := GlobalTheory.T.standard_bessel_scale_bound
  refine ⟨max (C₄ + 1) 10, max G₀ (240 + 2 * |c₃|), fun Cg hCg => ?_⟩
  have hG₀ : G₀ ≤ Cg := (le_max_left _ _).trans hCg
  have hG₁ : 240 + 2 * |c₃| ≤ Cg := (le_max_right _ _).trans hCg
  have main : ∀ (D : D7) (L : LocBessel D.R.k D.R.rS) (lam0 : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (f : B.Mat D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)) (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) (ka b : ℝ), LocOk D Ch Cg L lam0 ka b 1 → AllGaps lam0 (200 * l1 L.lam lam0) → IsKFinCoefH L.σ f → IsSection D.R.k D.R.rS L.z L.z' μsec → ∀ γ : Point ℂ (D.R.rS + 1), Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ ≠ 0 → BpIneq D (max (C₄ + 1) 10) L f μsec b γ := by
    intro D L lam0 f μsec ka b hL hg hf hsec
    obtain ⟨U, U', p, n₀, hstd, hn₀, hB⟩ := hloc Cg hG₀ D L lam0 f μsec ka b hL hg hf hsec
    obtain ⟨hk, -, hc, hκ0, hκ, hS, -⟩ := hL
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hb, -, -, hall, hgap, -⟩ := hS
    obtain ⟨hOK, hA⟩ := bpNear_gapOK D.R.k D.R.rS hk c₃ Cg hG₁
    obtain ⟨v1, v2, -⟩ := GlobalTheory.upqRep_vocabulary_agree D.R.k D.R.rS L.Hs L.σ L.ε L.lam
    have hone : (1 : B.Mat D.R.k D.R.rS) ∈ UH (Hpk D.R.k D.R.rS) := by simp [UH]
    have hE := GlobalTheory.T.capelli_eigen_gap_coef hH D.R.k D.R.rS L.ε L.lam _ ⟨L.Hs, L.σ⟩ L.Wp L.Wq f ⟨L.hlam, v1.1 L.hσ⟩
      (bpNear_gapAtLeast _ _ _ _ hgap hg) hOK (by
        obtain ⟨P, Q, hQ, hP, he⟩ := hf
        exact ⟨1, hone, 1, hone, P, Q, fun w => (v2 _).1 (hQ w), fun x => (v2 _).1 (hP x), fun g => by
          simpa using he g⟩)
    have hr : (0 : ℝ) ≤ D.R.rS := Nat.cast_nonneg _
    have hm : ((2 * D.R.rS + 2 : ℕ) : ℝ) = 2 * ((D.R.rS : ℝ) + 1) := by push_cast; ring
    have hb3 : 3 ≤ b := by
      have h1 := hall ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp)
      have h2 := abs_sub (lam0 ⟨0, by omega⟩) (lam0 ⟨1, by omega⟩)
      have h3 : (1 : ℝ) ≤ ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 := one_le_pow₀ (by rw [hm]; linarith)
      have h4 : 240 * 1 ≤ Cg * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 :=
        mul_le_mul (by linarith [abs_nonneg c₃]) h3 (by norm_num) (by linarith [abs_nonneg c₃])
      linarith [hb ⟨0, by omega⟩, hb ⟨1, by omega⟩]
    refine hdict D L μsec U U' p f _ b C₄ _ n₀ _ hstd (hc.trans Formalism.MainNotions.OnePlaceEstimates.cOfDpsi_one) hκ0.ne' hκ hA (hE.2.1 1)
      hb3 (le_max_left _ _) ?_ hB
    have h1 : (n₀ : ℝ) ≤ 30 * ((D.R.rS : ℝ) + 1) ^ 2 + 6 := by exact_mod_cast hn₀
    have h2 : 10 * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2 ≤ max (C₄ + 1) 10 * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    refine le_trans ?_ h2
    rw [hm]; push_cast; nlinarith
  refine ⟨main, ?_, ?_⟩
  · intro D L f μsec ka b hL hf hsec
    exact main D L L.lam f μsec ka b hL (fun s s' _ => by simp [l1]) hf hsec
  · intro D Cu Cg' hCu L lam0 f μsec ka b hL hR hf hsec _
    refine main D L lam0 f μsec ka b hL (fun s s' hs => le_trans ?_ (hR.1 s s' hs)) hf hsec
    have h1 := hR.2
    have h2 : 200 * Cu * ((D.R.k : ℝ) * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3) ≤
        Cg' * ((D.R.k : ℝ) * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3) := mul_le_mul_of_nonneg_right hCu (by positivity)
    nlinarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CombinedValuationBoundAlgebraicPointsStatement
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.combinedValuationBound_algebraicPoints : (∀ (p : ℕ) [Fact p.Prime], Pdiv.ChartF.HTFSt p) → ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (w : WeightFamilies.Wt D j) (c : ℝ), Oriented T EX → RunNum D w c → ∀ (ka wF : WeightFamilies.Wt D j) (S : WeightAlgebra.Scal (recB h.toLawsCore)) (G : GlobalFamilyData (recPJ h j hj) ka w wF), S.sW = sWt (recB h.toLawsCore) hinj EX w → (j < D.R.m → 0 < G.iet ∧ EtVal h j hj G.iet G.et) → CombBound G S c (nusOf (recB h.toLawsCore) w (nuWt T w)) := by
  first | exact @GlobalTheory.PtTie.combBound_alg | exact GlobalTheory.PtTie.combBound_alg | (intros; apply GlobalTheory.PtTie.combBound_alg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.GridsAtPlaceLongCutNormaliserPositive
section
open BpJoin Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Formalism.QuantumDeterminants

namespace GlobalTheory.GridAtPlace

theorem pow_absorb (C b : ℝ) (r : ℕ) (hb : 3 ≤ b) :
    (b ^ ((6 + C) * ((2 * r + 2 : ℕ) : ℝ))) ^ 2 * (5 / 4 : ℝ) ^ (3 * (r + 1)) ≤
      (b ^ ((7 + C) * ((2 * r + 2 : ℕ) : ℝ))) ^ 2 := by
  have hb0 : 0 < b := by linarith
  have e : b ^ ((7 + C) * ((2 * r + 2 : ℕ) : ℝ)) =
      b ^ ((6 + C) * ((2 * r + 2 : ℕ) : ℝ)) * b ^ (2 * r + 2) := by
    rw [← Real.rpow_natCast b (2 * r + 2), ← Real.rpow_add hb0]
    congr 1
    ring
  rw [e, mul_pow]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  rw [← pow_mul]
  calc (5 / 4 : ℝ) ^ (3 * (r + 1)) ≤ b ^ (3 * (r + 1)) :=
        pow_le_pow_left₀ (by norm_num) (by linarith) _
    _ ≤ b ^ ((2 * r + 2) * 2) := pow_le_pow_right₀ (by linarith) (by omega)

theorem main : ∀ (C b c : ℝ) (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ), 0 ≤ C → GridNum C b c P p.l0 lam → ((30 * (P.r + 1) ^ 2 + 6 : ℕ) : ℝ) ≤ |P.u p.l0 - P.u' p.l0| → (∀ y, 0 < Pst lam c y) ∧ 1 ≤ b ^ ((7 + C) * ((2 * P.r + 2 : ℕ) : ℝ)) ∧ ∃ Y : Finset ℝ, TBBx5.WaveGrid p (Pst lam c) Y (b ^ ((7 + C) * ((2 * P.r + 2 : ℕ) : ℝ))) 3 (3 * (P.r + 1)) ∧ TBBx5.LiftGrid p (Pst lam c) Y (b ^ ((7 + C) * ((2 * P.r + 2 : ℕ) : ℝ))) 3 (3 * (P.r + 1)) := by
  intro C b c P Wp Wq _ _ _ _ _ _ p lam hC hG hcut
  obtain ⟨hc, hcb, hkb, hu, hu', hlam, hgap, hint, hint', hT, hT'⟩ := hG
  have hb3 : 3 ≤ b := by linarith
  have hpos : ∀ y, 0 < Pst lam c y := fun y =>
    Finset.prod_pos (fun s _ => by have := abs_nonneg (y + lam s); linarith)
  have hone : 1 ≤ b ^ ((7 + C) * ((2 * P.r + 2 : ℕ) : ℝ)) :=
    Real.one_le_rpow (by linarith) (by positivity)
  refine ⟨hpos, hone, ?_⟩
  obtain ⟨Y, hcard, hsep, hon⟩ := GlobalTheory.exists_grid_five_apart_on_cut.1 P.u P.u' p.l0
    (3 * (P.r + 1) * (2 * P.r + 1)) (le_trans (by
      exact_mod_cast GlobalTheory.exists_grid_five_apart_on_cut.2 P.r) hcut)
  have hNQ := GlobalTheory.NormaliserCutBound.main C b c P p.l0 lam (Pst lam c) Y p.hP.1 hC p.hl.1 p.hl.2.1 hc hcb hkb
    hu hu' hlam (fun s t hst _ => hgap s t (by rw [Fin.lt_def]; omega)) hint hint' hT hT'
    (fun y => ⟨(hpos y).le, le_rfl⟩) (fun y hy => (hon y hy).1)
  exact ⟨Y, GlobalTheory.T.waveGrid_liftGrid_of_layout_normaliserBound P Wp Wq p (Pst lam c) Y _ _ 3 (3 * (P.r + 1)) hpos ⟨hsep, hcard, hon⟩ hNQ
    (by linarith) (pow_absorb C b P.r hb3)⟩

end GlobalTheory.GridAtPlace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroLimitOfXiExists
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Formalism.QuantumDeterminants
open Filter Topology

namespace GlobalTheory.PointwiseBoundDecay

theorem levelZero_limit_of_xiExists (hΞ : B.XiExists) (Cb : ℝ) : ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
    [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ)
    (ε A : ℝ) (N : ℕ) (nn : ℝ → ℝ) (Y : Finset ℝ),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → 0 < ε → B.CkOn ⊤ (B.GV P.k P.r) f →
    (∀ m : ℕ, B.InCC A m f) →
    Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A →
    LimZeroN p nn (D.cutF p.T.base χ f ε) Y N := by
  obtain ⟨Cc, hCc⟩ := GlobalTheory.GivenXi.levelForm_cutoff_tendsto hΞ Cb
  refine ⟨Cc, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f χ ε A N nn Y hDD hχ hε hf hfA hA
  have hFL := (hCc Wp Wq P p f χ ε A N (cutN P.k P.r) hDD hχ hε hf hfA hA (fun _ _ => rfl)).2
  intro w hw hN
  have hT := hFL 0 w hw.1 hN [] []
  have hre := (Complex.continuous_re.tendsto _).comp hT
  have e1 : ∀ n : ℕ, TBB.Ew p nn (apx (D.cutF p.T.base χ f ε) n) 0 w [] =
      (p.RR (fun g => cutN P.k P.r n g • D.cutF p.T.base χ f ε g) 0 w [] []).re / TBB.normC nn w :=
    fun n => Formalism.FourierDecayAlt.P.TBBx3.ew_zero_nil p nn _ w
  have e2 : TBB.Ew p nn (D.cutF p.T.base χ f ε) 0 w [] =
      (p.RR (D.cutF p.T.base χ f ε) 0 w [] []).re / TBB.normC nn w :=
    Formalism.FourierDecayAlt.P.TBBx3.ew_zero_nil p nn _ w
  simp only [e1, e2]
  exact hre.div_const _

theorem top_threshold_le (r k N : ℕ) :
    ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1) ≤
      ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) := by
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  push_cast
  set n : ℝ := 2 * (r : ℝ) + k + 1 with hn
  have h1 : 1 ≤ n := by linarith
  have h3 : n ≤ n ^ 3 := le_self_pow₀ h1 (by norm_num)
  have h4 : (r : ℝ) * n + 1 ≤ ((r : ℝ) + 1) * n := by nlinarith
  have h5 : ((r : ℝ) + 1) ≤ ((r : ℝ) + 1) ^ 2 := le_self_pow₀ (by linarith) (by norm_num)
  have h6 : n ≤ (N : ℝ) * n ^ 2 + n ^ 3 := by
    have : 0 ≤ (N : ℝ) * n ^ 2 := by positivity
    linarith
  have h7 : ((r : ℝ) + 1) * n ≤ ((r : ℝ) + 1) ^ 2 * ((N : ℝ) * n ^ 2 + n ^ 3) :=
    mul_le_mul h5 h6 (by linarith) (by positivity)
  calc ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * n + 1)
      ≤ ((r : ℝ) + 1) ^ 2 * (((r : ℝ) + 1) ^ 2 * ((N : ℝ) * n ^ 2 + n ^ 3)) :=
        mul_le_mul_of_nonneg_left (h4.trans h7) (by positivity)
    _ = _ := by ring

open GlobalTheory.PointwiseBound in

theorem ptBound_of_xiExists (hXi : B.XiExists) (hA : P5.ThmPActualCpt) : ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Λ κ₀ : ℝ) (χ nn : ℝ → ℝ) (Y : Finset ℝ) (K N : ℕ) (Cb : ℝ), 1 ≤ Λ → 0 < κ₀ → 3 ≤ K → (P.r + 1) * K ≤ N → C6.IsCut0 χ → (∀ y, 0 < nn y) → KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → B.CkOn ⊤ (B.GV P.k P.r) F → TBBx5.WaveGrid p nn Y Λ K N → TBBx5.LiftGrid p nn Y Λ K N → (∀ ε : ℝ, 0 < ε → ∀ n : ℕ, TBB.BlockGrowthBound p nn (apx (D.cutF p.T.base χ F ε) n) Y K N) → (∀ ε : ℝ, 0 < ε → LimTopN p nn (D.cutF p.T.base χ F ε)) → (∀ ε : ℝ, 0 < ε → LimZeroN p nn (D.cutF p.T.base χ F ε) Y N) → LimE p nn χ F Y N → LemB p F κ₀ → TBB.PtBound p F (κ₀ * (C₂ * Λ ^ 2) ^ (P.r + 1)) := by
  have hRad := GlobalTheory.WeightedFormPos.radialModuleForm_of_xiExists hXi
  have hSS := GlobalTheory.ListDuality.listDuality_cpt hRad
  have hVI := waveIsometry_of_radial hRad
  have hFP := GlobalTheory.WeightedFormPos.formPosCpt_of_xiExists hXi
  have hI4 := GlobalTheory.LiftBoundCpt.liftBound_of_xiExists hXi hA hSS hFP
  obtain ⟨C₂, hC₂, hLS⟩ := Formalism.FourierDecayAlt.P.lemma_s_of_parts Formalism.FourierDecayAlt.P.lemma_s_induction_base
    Formalism.FourierDecayAlt.P.lemma_s_induction_up
  refine ⟨C₂, hC₂, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p F Λ κ₀ χ nn Y K N Cb hΛ hκ hK hKN hχ hnn hCb hF hWG hLG hI5 hTN hZN hE hB
  refine Formalism.FourierDecayAlt.P.point_bound_of_corollary_s Wp Wq P p nn χ F Y Λ K N C₂ κ₀ hC₂.le hκ hnn
    ⟨1, one_pos, fun ε hε _ => ?_⟩ (Formalism.FourierDecayAlt.P.vector_truncation_at_place p χ F hχ.2.2)
    (Formalism.FourierDecayAlt.P.limit_zero_at_place p nn χ F Y N κ₀ hE hB)
  refine corS_of_apx p nn _ Y Λ K N C₂ (fun n => ?_) (hTN ε hε) (hZN ε hε)
  have hG := cptCoef_apx P p.T.base hχ hF hε n
  have hPos := GlobalTheory.WeightedFormPos.posAt_of_cptCoef_of_xiExists hXi hA Wp Wq P p nn _ Y N (fun y => (hnn y).le) hG
  exact Formalism.FourierDecayAlt.P.corSOfLemmaS_statement Wp Wq P p nn _ Y Λ K N C₂ hKN hC₂.le hPos
    (hLS Wp Wq P p nn _ Y Λ K N hK hΛ hPos (extension_at_zero hXi hA p nn _ Y N Cb hCb hG)
      (GlobalTheory.planeWave_bound_of_xiExists hXi hA hVI hSS hFP Wp Wq P p nn _ Y Λ K N Cb hCb hG hnn hWG)
      (hI4 Wp Wq P p nn _ Y Λ K N hG hnn hLG) (hI5 ε hε n))

theorem main : P5.ThmPActualCpt → ∀ Cb : ℝ, ∃ C₂ Cc : ℝ, 0 < C₂ ∧ ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Λ A : ℝ) (χ nn : ℝ → ℝ) (Y : Finset ℝ) (K N : ℕ), 1 ≤ Λ → 3 ≤ K → (P.r + 1) * K ≤ N → C6.IsCut0 χ → (∀ y, 0 < nn y) → KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → B.CkOn ⊤ (B.GV P.k P.r) F → (∀ m : ℕ, B.InCC A m F) → Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A → TBBx5.WaveGrid p nn Y Λ K N → TBBx5.LiftGrid p nn Y Λ K N → (∀ ε : ℝ, 0 < ε → ∀ n : ℕ, TBB.BlockGrowthBound p nn (apx (D.cutF p.T.base χ F ε) n) Y K N) → LimEvT p χ F Y N → LimBd p nn F Y N → TBB.PtBound p F (1 * (C₂ * Λ ^ 2) ^ (P.r + 1)) := by
  intro hA Cb
  have hXi : B.XiExists := Formalism.FourierDecayAlt.P.exists_auxiliary_xi
  obtain ⟨C₂, hC₂, hPt⟩ := ptBound_of_xiExists hXi hA
  obtain ⟨c₃, hc₃⟩ := limTopN_cut_of_inCC
  obtain ⟨Ca, hCa⟩ := levelZero_limit_of_xiExists hXi Cb
  obtain ⟨Ce, hE⟩ := GlobalTheory.LevelZeroLimit.limE_of_limEvT_of_xiExists hXi hA Cb
  refine ⟨C₂, max (max 0 c₃) (max Ca Ce), hC₂, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P q F Λ A χ nn Y K N hΛ hK hKN hχ hnn hCb hF hFA hth hWG hLG hI5 hLim hBd
  set C : ℝ := max (max 0 c₃) (max Ca Ce) with hC
  have hC0 : 0 ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have hC3 : c₃ ≤ C := (le_max_right _ _).trans (le_max_left _ _)
  have hCa' : Ca ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCe' : Ce ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  have hmono : ∀ c : ℝ, c ≤ C → c * ((P.r : ℝ) + 1) ^ 4 *
      ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A := fun c hc =>
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by positivity)) (by positivity)).trans hth
  have hth1 : c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤ A := by
    refine le_trans ?_ hth
    rw [mul_assoc, mul_assoc]
    exact (mul_le_mul_of_nonneg_right hC3 (by positivity)).trans
      (mul_le_mul_of_nonneg_left (top_threshold_le P.r P.k N) hC0)
  exact hPt Wp Wq P q F Λ 1 χ nn Y K N Cb hΛ one_pos hK hKN hχ hnn hCb hF hWG hLG hI5
    (hc₃ Wp Wq P q nn χ F A hth1 hχ hFA hF)
    (fun ε hε => hCa Wp Wq P q F χ ε A N nn Y hCb hχ hε hF hFA (hmono _ hCa'))
    (hE Wp Wq P q F χ nn A N Y hCb hχ (fun y => (hnn y).le) hF hFA (hmono _ hCe') hLim hBd)
    (lemB_one q F)

end GlobalTheory.PointwiseBoundDecay
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroPairingEqIntegralInnerTopVectors
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.TopVec Filter Topology MeasureTheory

namespace GlobalTheory

theorem beta_word_cutF_eq_integral_inner_tv :
    P5.ThmPActualCpt → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (A : ℝ) (N : ℕ) (w : List C.Letter), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A m f) → Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A → KB.CutWord P p.l0 w → w.length ≤ N → ∀ ε₁ ε₂ : ℝ, 0 < ε₁ → 0 < ε₂ → B.beta p.T.base (List.foldr (fun (a : Bool × ℝ) G => M.sgn P p.l0 • Q.CV P.k P.r (a.2 : ℂ) G) ((D.cutF p.T.base χ f ε₁)) w) (D.cutF p.T.base χ f ε₂) = ∫ c, inner ℂ (tv p (D.cutF p.T.base χ f ε₂) w c) (tv p (D.cutF p.T.base χ f ε₁) w c) := by
  intro hA Cb
  obtain ⟨C₁, h₁⟩ := GlobalTheory.T.levelZeroPairing_compactApproximants_cauchy_bound
  obtain ⟨C₂, h₂⟩ := GlobalTheory.T.tv_approx_tendsto_L2_cutoff hA Cb
  refine ⟨max C₁ C₂, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f χ A N w hD hχ hf hCC hth hw hlen ε₁ ε₂ hε₁ hε₂
  have hmono : ∀ Cc : ℝ, Cc ≤ max C₁ C₂ →
      Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A := by
    intro Cc hC
    refine le_trans ?_ hth
    gcongr
  have hL := (h₁ P.k P.r Wp Wq p.T.base (M.sgn P p.l0) w χ f A N hχ hf hCC (hmono _ (le_max_left _ _)) hlen
    ε₁ ε₂ hε₁ hε₂).1
  obtain ⟨a₁, b₁, c₁⟩ := h₂ Wp Wq P p f χ A N w hD hχ hf hCC (hmono _ (le_max_right _ _)) hw hlen ε₁ hε₁
  obtain ⟨a₂, b₂, c₂⟩ := h₂ Wp Wq P p f χ A N w hD hχ hf hCC (hmono _ (le_max_right _ _)) hw hlen ε₂ hε₂
  have hR := tendsto_integral_inner_of_tendsto_eLpNorm_two _ _ _ _ _ _ _ a₁ a₂ b₁ b₂ c₁ c₂
  refine tendsto_nhds_unique hL (hR.congr fun n => ?_)
  have hc : ∀ ε : ℝ, 0 < ε → KB.CptCoef p.T.base (fun g : B.Mat P.k P.r =>
      ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) •
        D.cutF p.T.base χ f ε g) := fun ε hε =>
    Formalism.FourierDecayAlt.P.PBE.cutCpt P p.T.base f χ ε
      (fun (n : ℕ) (g : B.Mat P.k P.r) =>
        ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ))
      hχ hε hf (fun _ _ => rfl) n
  exact (GlobalTheory.T.levelZeroPairing_eq_bigCell_integral_topVectors hA Wp Wq P p Cb _ _ w hD (hc ε₁ hε₁) (hc ε₂ hε₂) hw).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TopDensityCutoffDominatedOfHCXiStatement
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topDensity_cutoff_dominated_of_HC_xi : GlobalTheory.HCXi.BesselXiIntegrable → Formalism.FourierDecayAlt.P.CutBP.NFTopDomAll := by
  first | exact @GlobalTheory.HatNF.topDensity_cut_dominated_all | exact GlobalTheory.HatNF.topDensity_cut_dominated_all | (intros; apply GlobalTheory.HatNF.topDensity_cut_dominated_all <;> assumption)
end

