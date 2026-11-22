import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0022
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0086
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0092
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0096
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AevalNeZeroOfMemCellMon
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PChartSecGen
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0071
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ChartRingOverOneBlockBase
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0069

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Imports
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def FujitaVanishingPrime.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (I : IFamily F ι) (P : Ideal (MRingOver F ι)),
    IsFieldIntersection I → IsMultiProjPrime P →
    (∀ W : Ideal (MRingOver F ι), P < W →
      ∀ (M : Type) [AddCommGroup M] [Module (MRingOver F ι) M] [Module F M]
        [IsScalarTower F (MRingOver F ι) M] (𝓜 : (K → ℤ) → Submodule F M),
        Module.Finite (MRingOver F ι) M → KH.IsMGraded F ι 𝓜 → W ≤ Module.annihilator (MRingOver F ι) M →
        ∀ e : K → ℤ, ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ N : K → ℤ, KH.NefOnF I P N → ∀ i : ℕ, 1 ≤ i →
          Subsingleton (KH.cechHc ι 𝓜 (e + ((fun _ => (m : ℤ)) + N)) i)) →
    (∀ e : K → ℤ, ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ N : K → ℤ, KH.NefOnF I P N → ∀ i : ℕ, 2 ≤ i →
      Subsingleton (KH.cechHc ι (KH.quotPart F P) (e + ((fun _ => (m : ℤ)) + N)) i)) →
    ∀ e : K → ℤ, ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ N : K → ℤ, KH.NefOnF I P N →
      Subsingleton (KH.cechHc ι (KH.quotPart F P) (e + ((fun _ => (m : ℤ)) + N)) 1)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PFibreNormPullbackX
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

namespace FibreNormPullback

theorem proof_dehom (hG : PullFormsGeneric.Statement) (hC : FibreNormDehomCharpoly.Statement)
    (hI : FibreNormDehomIntegral.Statement) (hR : FibreNormDehomRoots.Statement) :
    FibreNormPullback.Statement := by
  intro K _ ι _ Ω _ y D e L q hV hBir he hL hL0
  classical
  have : CharZero Ω := charZero_of_isArithVar hV
  obtain ⟨j, hj⟩ : ∃ j, aeval y (L j) ≠ 0 := by
    by_contra h
    push Not at h
    have h0 := hG K ι Ω y D e L hV hBir he hL hL0 1 (X 0) (isHomogeneous_X ℚ 0) (by rw [aeval_X]; exact h 0)
    exact X_ne_zero _ h0
  obtain ⟨hfin, hC'⟩ := hC K ι Ω y D e L q hV hBir he hL hL0
  obtain ⟨M₀, hM₀, hI'⟩ := hI K ι Ω y D e L q hV hBir he hL hL0
  have hR' := hR K ι Ω y D e L q hV hBir he hL hL0
  have hP : IsMultiHomogIdeal (mCoordIdeal y) := hV.2.1.2.1
  set n := Module.finrank (pullField y L) Ω
  have hn1 : 1 ≤ n := Module.finrank_pos
  refine ⟨n, M₀, hn1, by exact_mod_cast hM₀, fun τ s hs hs0 => ?_⟩
  obtain ⟨c, hc, hcn⟩ := hC' τ s hs j hj
  obtain ⟨F, hF⟩ := hI' τ s hs j c hc
  have hRc := hR' τ s hs j c hc
  obtain ⟨-, _, hc0, hch, -⟩ := hc
  have hM₀q : ((M₀ : ℚ) ^ τ) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (show M₀ ≠ 0 by omega))
  refine ⟨F, ?_, ?_, fun ζ hζ S hS M hM hrep => ?_⟩
  · rintro rfl
    rw [map_zero, eq_comm, smul_eq_zero] at hF
    exact hF.elim hM₀q (hcn hs0)
  · apply isHomogeneous_of_map
    rw [hF, smul_eq_C_mul, show n * q * τ = 0 + n * (q * τ) by ring]
    exact (isHomogeneous_C _ _).mul (hch n le_rfl)

  have hmapF : eval ζ (map (Int.castRingHom ℂ) F) = (M₀ : ℂ) ^ τ * eval ζ (map (algebraMap ℚ ℂ) (c n)) := by
    have h1 : map (Int.castRingHom ℂ) F = map (algebraMap ℚ ℂ) (map (Int.castRingHom ℚ) F) := by
      rw [map_map]
      congr 1
    rw [h1, hF, smul_eq_C_mul, map_mul, map_C, eval_mul, eval_C]
    simp
  set B := M * ‖ζ‖ ^ (q * τ) with hBdef
  have hB0 : 0 ≤ B := mul_nonneg hM (pow_nonneg (norm_nonneg _) _)
  have hroot : ∀ w : ℂ, ∑ i ∈ Finset.range (n + 1), eval ζ (map (algebraMap ℚ ℂ) (c i)) * w ^ (n - i) = 0 →
      ‖w‖ ≤ B := by
    intro w hw
    obtain ⟨z, hz, t, ht0, hLz, hval⟩ := hRc ζ hζ w hw
    obtain ⟨z', hz'S, r, hr0, rfl⟩ := hS z hz ⟨t, hLz⟩
    have hz'm : z' ∈ mcPts (mCoordIdeal y) := by
      have h1 := mcPts_smul hP (fun k => (r k)⁻¹) (fun k => inv_ne_zero (hr0 k)) hz
      convert h1 using 1
      funext p
      simp [hr0 p.1]
    obtain ⟨dg, dh, g, h, hg, hh, hd, hgh, hz'0, hle⟩ := hrep z' hz'S hz'm
    have hgz := eval_smul_homog g dg hg r z'
    have hhz := eval_smul_homog h dh hh r z'
    have hhz0 : eval (fun p => r p.1 * z' p) (map (Int.castRingHom ℂ) h) ≠ 0 := by
      rw [hhz]
      exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hr0 k)) hz'0
    have hv := hval dg dh g h hg hh hd hgh hhz0
    have hRg : (∏ k, r k ^ dg k) = (∏ k, r k ^ dh k) * (∏ k, r k ^ e k) ^ (q * τ) := by
      rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [hd k, ← pow_mul, ← pow_add]
      ring
    have hnormL : ‖∏ k, r k ^ e k‖ * ‖fun j => eval z' (map (Int.castRingHom ℂ) (L j))‖ = ‖t‖ * ‖ζ‖ := by
      have h1 : (∏ k, r k ^ e k) • (fun j => eval z' (map (Int.castRingHom ℂ) (L j))) = t • ζ := by
        funext j
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [← eval_smul_homog (L j) e (hL j) r z', hLz j]
      rw [← norm_smul, h1, norm_smul]
    have hpos : 0 < ‖t‖ ^ (q * τ) * ‖eval (fun p => r p.1 * z' p) (map (Int.castRingHom ℂ) h)‖ :=
      mul_pos (pow_pos (norm_pos_iff.mpr ht0) _) (norm_pos_iff.mpr hhz0)
    refine le_of_mul_le_mul_right ?_ hpos
    calc ‖w‖ * (‖t‖ ^ (q * τ) * ‖eval (fun p => r p.1 * z' p) (map (Int.castRingHom ℂ) h)‖)
        = ‖eval (fun p => r p.1 * z' p) (map (Int.castRingHom ℂ) g)‖ := by
          rw [hv, norm_mul, norm_mul, norm_pow]; ring
      _ = ‖∏ k, r k ^ dg k‖ * ‖eval z' (map (Int.castRingHom ℂ) g)‖ := by rw [hgz, norm_mul]
      _ ≤ ‖∏ k, r k ^ dg k‖ * (M * ‖fun j => eval z' (map (Int.castRingHom ℂ) (L j))‖ ^ (q * τ) *
            ‖eval z' (map (Int.castRingHom ℂ) h)‖) := mul_le_mul_of_nonneg_left hle (norm_nonneg _)
      _ = M * (‖∏ k, r k ^ e k‖ * ‖fun j => eval z' (map (Int.castRingHom ℂ) (L j))‖) ^ (q * τ) *
            (‖∏ k, r k ^ dh k‖ * ‖eval z' (map (Int.castRingHom ℂ) h)‖) := by
          rw [hRg, norm_mul, norm_pow]; ring
      _ = B * (‖t‖ ^ (q * τ) * ‖eval (fun p => r p.1 * z' p) (map (Int.castRingHom ℂ) h)‖) := by
          rw [hnormL, hhz, norm_mul, hBdef]; ring
  have key := norm_last_le (fun i => eval ζ (map (algebraMap ℚ ℂ) (c i))) (by simp [hc0]) hB0 hroot
  rw [hmapF, norm_mul, norm_pow, Complex.norm_natCast]
  calc (M₀ : ℝ) ^ τ * ‖eval ζ (map (algebraMap ℚ ℂ) (c n))‖ ≤ (M₀ : ℝ) ^ τ * B ^ n :=
        mul_le_mul_of_nonneg_left key (pow_nonneg (Nat.cast_nonneg _) _)
    _ = (M₀ : ℝ) ^ τ * ‖ζ‖ ^ (n * q * τ) * M ^ n := by
        rw [hBdef, mul_pow, ← pow_mul, show q * τ * n = n * q * τ by ring]
        ring

end FibreNormPullback

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PRowLocCoverX
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

theorem RowLocCover.closed : RowLocCover.Statement :=
  RowLocCover.proof ChartSecGen.full (ChartSecMul.proof BundleOfDeg.full) RowSub.proof
    RowChartAct.proof

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

