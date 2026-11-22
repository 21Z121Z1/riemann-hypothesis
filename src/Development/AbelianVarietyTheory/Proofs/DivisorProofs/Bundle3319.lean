import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3240
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3252
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3284
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3301
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3186
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3203
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3194
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3207
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3208
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1191
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1267
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3280
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3192
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3306
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3046
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3283
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3136
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3282
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3138
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3129
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatTranslateOfPrime
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0736
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2159
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3089
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3308
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2219
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2197
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2137

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsEqSumAevalBoundedIntCoeffAmple
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HSRep

open MvPolynomial

theorem aeval_smul_of_hom {σ K : Type} [CommRing K] {d : ℕ} {P : MvPolynomial σ ℤ} (hP : P.IsHomogeneous d)
    (c : K) (y : σ → K) : aeval (c • y) P = c ^ d * aeval y P := by
  rw [aeval_def, aeval_def, eval₂_eq, eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have : a.degree = d := by rw [Finsupp.degree_eq_weight_one]; exact hP (mem_support_iff.1 ha)
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [← this, Finsupp.degree_apply, mul_left_comm]

theorem rep_of_trace {K : Type} [Field K] [CharZero K] {D : ℕ} (x : Fin (D + 1) → K) (hx0 : x 0 ≠ 0)
    [FiniteDimensional (ratF x) K] (g : Fin (Module.finrank (ratF x) K) → K) (hg : LinearIndependent (ratF x) g) :
    ∃ w : Fin (Module.finrank (ratF x) K) → K, ∀ (N : ℕ) (f : K)
      (T : Fin (Module.finrank (ratF x) K) → MvPolynomial (Fin (D + 1)) ℤ), (∀ i, (T i).IsHomogeneous N) →
      (∀ i, (Algebra.trace (ratF x) K (f * g i / x 0 ^ N) : K) = aeval (fun l => x l / x 0) (T i)) →
      f = ∑ i, aeval x (T i) * w i := by
  classical
  haveI : Nonempty (Fin (Module.finrank (ratF x) K)) := ⟨⟨0, Module.finrank_pos⟩⟩
  let b := basisOfLinearIndependentOfCardEqFinrank hg (by simp)
  have hB : (Algebra.traceForm (ratF x) K).Nondegenerate := traceForm_nondegenerate _ _
  refine ⟨fun i => (Algebra.traceForm (ratF x) K).dualBasis hB b i, ?_⟩
  intro N f T hT htr
  have key := ((Algebra.traceForm (ratF x) K).dualBasis hB b).sum_repr (f / x 0 ^ N)
  simp_rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply] at key
  have hxN : x 0 ^ N ≠ 0 := pow_ne_zero _ hx0
  have hf : f = (f / x 0 ^ N) * x 0 ^ N := by field_simp
  rw [hf, ← key, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hbi : b i = g i := by simp [b]
  have hx : x = x 0 • fun l => x l / x 0 := by
    funext l; simp [smul_eq_mul, mul_div_cancel₀ _ hx0]
  rw [Algebra.smul_def, hbi, div_mul_eq_mul_div, show (algebraMap (ratF x) K) (Algebra.trace (ratF x) K (f * g i / x 0 ^ N)) = _ from htr i]
  have hT' : aeval x (T i) = x 0 ^ N * aeval (fun l => x l / x 0) (T i) := by
    conv_lhs => rw [hx]
    exact aeval_smul_of_hom (hT i) _ _
  rw [hT']
  ring

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem nu_nonneg (P : Pair p) (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField) : 0 ≤ P.nu a b σ y f := by
  rw [← norm_val]; exact norm_nonneg _

theorem sections_eq_sum_aeval_bounded : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → ∀ a b : ℤ, ∃ (c : ℕ) (w : Fin (Module.finrank (ratF x) X.functionField) → X.functionField) (C : ℝ), 0 < C ∧ ∀ (q : ℕ), ∀ f ∈ P.H (e * q + a) b, ∃ T : Fin (Module.finrank (ratF x) X.functionField) → MvPolynomial (Fin (D + 1)) ℤ, (∀ i, (T i).IsHomogeneous (q + c)) ∧ f = ∑ i, MvPolynomial.aeval x (T i) * w i ∧ ∀ R κ : ℝ, 0 < κ → (∀ (σ : k →+* ℂ) (y : CxPts p σ), ∃ l, κ ≤ P.nu e 0 σ y (x l)) → (∀ (σ : k →+* ℂ) (y : CxPts p σ), P.nu (e * q + a) b σ y f ≤ R) → ∀ i α, |((MvPolynomial.coeff α (T i) : ℤ) : ℝ)| ≤ C * R / κ ^ (q + c) := by
  intro k _ X _ p D hV P hA e x hG a b
  classical
  obtain ⟨hx0s, hai, hfd⟩ := GlobalTheory.T.sectionQuotients_transcendenceBasis_basepointFree k X p D hV P hA e x hG
  haveI := hfd
  obtain ⟨hch, -⟩ := GlobalTheory.T.projArith_functionField_charZero_trdeg k X p D hV
  haveI := hch
  set n' := Module.finrank (ratF x) X.functionField with hn'
  obtain ⟨c0, g0, hg0, hli0⟩ := GlobalTheory.T.exists_functionField_basis_of_sections k X p D hV P hA e x hG (-a) (-b)

  have hli : LinearIndependent (ratF x) (fun i => g0 i * x 0) := by
    have hk : LinearMap.ker (LinearMap.mulRight (ratF x) (x 0)) = ⊥ :=
      LinearMap.ker_eq_bot.2 (mul_left_injective₀ (hx0s 0))
    have := hli0.map' (LinearMap.mulRight (ratF x) (x 0)) hk
    exact this
  have hgH : ∀ i, (fun j => g0 j * x 0) i ∈ P.H (e * c0 + -a + e) (-b + 0) := fun i =>
    (NuMul.mul_mem_H_and_nu_mul k X p P _ _ _ _ _ _ (hg0 i) (hG.mem 0)).1
  generalize hgdef : (fun j => g0 j * x 0) = g at hli hgH
  obtain ⟨w, hw⟩ := rep_of_trace x (hx0s 0) g hli

  have hbd : ∀ i, ∃ Ci : ℝ, ∀ (σ : k →+* ℂ) (y : CxPts p σ), P.nu (e * c0 + -a + e) (-b + 0) σ y (g i) ≤ Ci :=
    fun i => ((GlobalTheory.T.continuous_hermSectionValue_mul_conj_and_norm_bounded k X p D hV P _ _).2 _ (hgH i)).2
  choose Ci hCi using hbd
  set Cg : ℝ := ∑ i, |Ci i| + 1 with hCg
  have hCg1 : 1 ≤ Cg := by
    have : 0 ≤ ∑ i, |Ci i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    linarith
  have hCgi : ∀ i σ y, P.nu (e * c0 + -a + e) (-b + 0) σ y (g i) ≤ Cg := fun i σ y => by
    have h1 : Ci i ≤ |Ci i| := le_abs_self _
    have h2 : |Ci i| ≤ ∑ j, |Ci j| := Finset.single_le_sum (f := fun j => |Ci j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    linarith [hCi i σ y]
  have hn'pos : (0 : ℝ) < n' := by exact_mod_cast Module.finrank_pos
  refine ⟨c0 + 1, w, n' * Cg, by positivity, ?_⟩
  intro q f hf
  set N := q + (c0 + 1) with hNdef
  have hN1 : 1 ≤ N := by omega
  have hidx : ((e : ℤ) * q + a) + (e * c0 + -a + e) = (N : ℤ) * e := by rw [hNdef]; push_cast; ring
  have hidx2 : b + (-b + 0) = (N : ℤ) * 0 := by ring
  have hu : ∀ i, f * g i ∈ P.H ((N : ℤ) * e) ((N : ℤ) * 0) ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ),
      P.nu ((N : ℤ) * e) ((N : ℤ) * 0) σ y (f * g i) =
        P.nu (e * q + a) b σ y f * P.nu (e * c0 + -a + e) (-b + 0) σ y (g i) := fun i => by
    have := NuMul.mul_mem_H_and_nu_mul k X p P _ _ _ _ f (g i) hf (hgH i)
    rw [hidx, hidx2] at this
    exact this
  have hxpow : ∀ l, x l ^ N ∈ P.H ((N : ℤ) * e) ((N : ℤ) * 0) ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ),
      P.nu ((N : ℤ) * e) ((N : ℤ) * 0) σ y (x l ^ N) = P.nu e 0 σ y (x l) ^ N := fun l =>
    NuPow.pow_mem_H_and_nu_pow k X p P _ _ (x l) (hG.mem l) N
  have hnv : ∀ l, NV P ((N : ℤ) * e) ((N : ℤ) * 0) (x l ^ N) = NV P e 0 (x l) := fun l =>
    (GlobalTheory.T.regularNonvanishingLocusSection_properties k X p P e 0 (x l) (hG.mem l)).2.2.1 N hN1
  have hreg : ∀ i l, ∀ z ∈ NV P e 0 (x l), RegAt z (f * g i / x l ^ N) := fun i l z hz =>
    ((GlobalTheory.T.regularNonvanishingLocusSection_properties k X p P _ _ (x l ^ N) (hxpow l).1).2.2.2.1 _ (hu i).1 z (by rw [hnv l]; exact hz)).1
  have hintg : ∀ i l, IsIntegral (ratR x l) (f * g i / x l ^ N) := fun i l =>
    GlobalTheory.T.isIntegral_quotientRing_sectionTuple_locus k X p D hV P e x hG l _ (hx0s l) (hreg i l)
  have hTex : ∀ i, ∃ T : MvPolynomial (Fin (D + 1)) ℤ, T.IsHomogeneous N ∧
      (Algebra.trace (ratF x) X.functionField (f * g i / x 0 ^ N) : X.functionField) = aeval (fun l => x l / x 0) T :=
    fun i => GlobalTheory.T.exists_homogeneous_int_trace_sectionTuple X.functionField D x hx0s hai hfd N (f * g i) (hintg i)
  choose T hT htr using hTex
  refine ⟨T, hT, hw N f T hT htr, ?_⟩
  intro R κ hκ hcov hR i α
  obtain ⟨U, hgen, hU, -, hregU, -, -, hpts⟩ := GlobalTheory.T.nonvanishingLocus_ample_section_isAffine_model k X p D hV P hA e (x 0) hG.pos (hG.mem 0) (hx0s 0)
  have hB : ∀ l, x l / x 0 ∈ (fnOf U hgen).range := fun l => (hregU _).1 fun z hz =>
    ((GlobalTheory.T.regularNonvanishingLocusSection_properties k X p P e 0 (x 0) (hG.mem 0)).2.2.2.1 _ (hG.mem l) z (by rw [← hU]; exact hz)).1
  have hBint : ∀ b' ∈ (fnOf U hgen).range, IsIntegral (ratR x 0) b' := fun b' hb =>
    GlobalTheory.T.isIntegral_quotientRing_sectionTuple_locus k X p D hV P e x hG 0 b' (hx0s 0) fun z hz => (hregU b').2 hb z (show z ∈ (U : Set X) by rw [hU]; exact hz)
  have hwB : f * g i / x 0 ^ N ∈ (fnOf U hgen).range := (hregU _).1 fun z hz => hreg i 0 z (by rw [← hU]; exact hz)
  have key := GlobalTheory.T.norm_aeval_traceForm_le_fibreValues X.functionField D x hx0s hai hfd (fnOf U hgen).range hB hBint ⟨_, hwB⟩ (T i) (htr i)
  have hcoef := GlobalTheory.T.abs_coeff_le_of_homogeneous_torus_bound D N (T i) (n' * (R * Cg / κ ^ N)) (hT i) ?_ α
  · exact le_of_le_of_eq hcoef (by ring)
  intro z hz0 hz1
  refine key z _ hz0 fun φ hφ => ?_
  obtain ⟨σ, y, hyU, hval⟩ := hpts φ
  have hyNV : under y ∈ NV P e 0 (x 0) := by rw [← hU]; exact hyU
  obtain ⟨l, hl⟩ := hcov σ y
  have h5 := (GlobalTheory.T.regularNonvanishingLocusSection_properties k X p P e 0 (x 0) (hG.mem 0)).2.2.2.2 (x l) (hG.mem l) σ y hyNV
  have hzl : ‖ratVal (x l / x 0) y‖ = 1 := by
    have := hval ⟨_, hB l⟩
    simp only at this
    rw [this, hφ l, hz1 l]
  have hx0κ : κ ≤ P.nu e 0 σ y (x 0) := by rw [h5.1, hzl, one_mul] at hl; exact hl
  have hyN : under y ∈ NV P ((N : ℤ) * e) ((N : ℤ) * 0) (x 0 ^ N) := by rw [hnv 0]; exact hyNV
  have h6 := (GlobalTheory.T.regularNonvanishingLocusSection_properties k X p P _ _ (x 0 ^ N) (hxpow 0).1).2.2.2.2 (f * g i) (hu i).1 σ y hyN
  rw [(hu i).2, (hxpow 0).2] at h6
  have hv := hval ⟨_, hwB⟩
  simp only at hv
  rw [← hv, le_div_iff₀ (pow_pos hκ N)]
  calc ‖ratVal (f * g i / x 0 ^ N) y‖ * κ ^ N ≤ ‖ratVal (f * g i / x 0 ^ N) y‖ * P.nu e 0 σ y (x 0) ^ N :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hκ.le hx0κ N) (norm_nonneg _)
    _ = P.nu (e * q + a) b σ y f * P.nu (e * c0 + -a + e) (-b + 0) σ y (g i) := h6.1.symm
    _ ≤ R * Cg := mul_le_mul (hR σ y) (hCgi i σ y) (nu_nonneg _ _ _ _ _ _) (le_trans (nu_nonneg _ _ _ _ _ _) (hR σ y))

end GlobalTheory.HSRep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupNormBallCountAsymptoticGramDeterminant
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem eventually_poly_mul_pow_le_exp (c C t : ℝ) (n : ℕ) (hC : 1 ≤ C) (ht : Real.log C < t) :
    ∀ᶠ m : ℕ in atTop, c * (m : ℝ) ^ n * C ^ m ≤ Real.exp (t * m) := by
  have hδ : 0 < t - Real.log C := sub_pos.2 ht
  have hc1 : 0 < |c| + 1 := by positivity
  have h1 := (isLittleO_pow_exp_pos_mul_atTop n hδ).bound (c := 1 / (|c| + 1)) (by positivity)
  have h2 := tendsto_natCast_atTop_atTop.eventually h1
  filter_upwards [h2] with m hm
  have hCpos : 0 < C := by linarith
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (Real.exp_pos _).le] at hm
  have hexp : Real.exp (t * m) = Real.exp ((t - Real.log C) * m) * C ^ m := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hCpos, ← Real.exp_add]; ring_nf
  rw [hexp]
  have hmn : (0 : ℝ) ≤ (m : ℝ) ^ n := by positivity
  have hle : c * (m : ℝ) ^ n ≤ Real.exp ((t - Real.log C) * m) := by
    calc c * (m : ℝ) ^ n ≤ (|c| + 1) * (m : ℝ) ^ n :=
          mul_le_mul_of_nonneg_right (by linarith [le_abs_self c]) hmn
      _ ≤ (|c| + 1) * (1 / (|c| + 1) * Real.exp ((t - Real.log C) * m)) :=
          mul_le_mul_of_nonneg_left hm hc1.le
      _ = _ := by field_simp
  exact mul_le_mul_of_nonneg_right hle (by positivity)

theorem count_ball_asymp : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ (P : Pair p), P.L.SemiPos D → ∀ (ω : ∀ σ, VolDens p σ D) (r : ℕ → ℕ) (f : ∀ m, Fin (r m) → X.functionField), (∀ (m : ℕ) i, f m i ∈ P.H m 1) → (∀ m, LinearIndependent ℤ (f m)) → ∀ g : ℝ, Tendsto (fun m : ℕ => (r m : ℝ) / (m : ℝ) ^ D) atTop (𝓝 g) → ∀ C : ℝ, 1 ≤ C → (∀ m : ℕ, 1 ≤ m → AddSubgroup.closure (Set.range (f m)) ≤ AddSubgroup.closure (ballIn P (AddSubgroup.closure (Set.range (f m))) m 1 (C ^ m))) → ∀ t : ℝ, Real.log C < t → Tendsto (fun m : ℕ => (Real.log ((ballIn P (AddSubgroup.closure (Set.range (f m))) m 1 (Real.exp (t * m))).ncard : ℝ) - (r m * (t * m) - Real.log (gram (fun σ => (ω σ).meas) (vals P m 1 (f m))).det.re / 2 + Real.log (volume {x : Fin (r m) → ℝ | ∑ i, x i ^ 2 ≤ 1}).toReal)) / (m : ℝ) ^ (D + 1)) atTop (𝓝 0) := by
  intro k _ X _ p D hX hS P hP ω r f hf hli g hg C hC hball t ht
  haveI := hX.finite_emb
  letI := Fintype.ofFinite (k →+* ℂ)
  have hρ := fun σ => GlobalTheory.T.exists_chernTopPower_volumeDensity_ratio k X p D hX hS P.L hP σ (ω σ)
  choose ρ hρr hρ0 _ using hρ
  have hbd : ∀ σ, ∃ b : ℝ, ∀ y, ρ σ y ≤ b := fun σ => by
    haveI := hX.compactSpace σ
    obtain ⟨b, hb⟩ := (isCompact_range (hρr σ).1).bddAbove
    exact ⟨b, fun y => hb ⟨y, rfl⟩⟩
  choose b hb using hbd
  set B : ℝ := ∑ σ, |b σ| with hBdef
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hρB : ∀ σ y, ρ σ y ≤ B := fun σ y => (hb σ y).trans ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun σ => |b σ|) (fun _ _ => abs_nonneg _) (Finset.mem_univ σ)))
  set K : ℝ := B / D.factorial + 1 with hKdef
  have hK : 1 ≤ K := by
    have : 0 ≤ B / D.factorial := by positivity
    linarith
  set V : ℝ := max 1 (∑ᶠ σ, ((ω σ).meas Set.univ).toReal) with hVdef
  have hV : 1 ≤ V := le_max_left _ _
  have hmorse := GlobalTheory.T.holomorphicMorse_sections_mL_add_A_uniform k X p D hX hS P hP ω ρ hρr 1 one_pos
  have hr : ∀ᶠ m : ℕ in atTop, (r m : ℝ) ≤ (g + 1) * (m : ℝ) ^ D := by
    filter_upwards [hg.eventually (gt_mem_nhds (lt_add_one g)), eventually_ge_atTop 1] with m hm h1
    have h0 : (0 : ℝ) < (m : ℝ) ^ D := pow_pos (by exact_mod_cast h1) D
    exact ((div_lt_iff₀ h0).1 hm).le
  have hexp := eventually_poly_mul_pow_le_exp (2 * (g + 1) * K * V) C t (2 * D) hC ht
  refine squeeze_zero_norm' (a := fun m : ℕ =>
    2 * ((r m : ℝ) / (m : ℝ) ^ D) * ((Real.log (2 * K * V) + D * Real.log m) / m)) ?_ ?_
  · filter_upwards [hmorse, hr, hexp, eventually_ge_atTop 1] with m hm hrm hem h1
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast h1
    have hm0 : (0 : ℝ) < m := by linarith
    have hmD : (0 : ℝ) < (m : ℝ) ^ D := pow_pos hm0 D
    have hM : 1 ≤ K * (m : ℝ) ^ D := one_le_mul_of_one_le_of_one_le hK (one_le_pow₀ hm1)
    have hcmb : ∀ (c : Fin (r m) → ℂ) σ y, cmb (vals P m 1 (f m)) c σ y ≤
        K * (m : ℝ) ^ D * l2 (fun σ => (ω σ).meas) (vals P m 1 (f m)) c := by
      intro c σ y
      have h := hm (Fin (r m)) (f m) (hf m) c σ y
      have hl2 : 0 ≤ l2 (fun σ => (ω σ).meas) (vals P m 1 (f m)) c :=
        finsum_nonneg fun σ => integral_nonneg fun y => by unfold cmb; positivity
      refine h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hmD.le) hl2)
      have : ρ σ y / D.factorial ≤ B / D.factorial :=
        div_le_div_of_nonneg_right (hρB σ y) (by positivity)
      linarith
    have hR : 2 * (r m : ℝ) * C ^ m * (K * (m : ℝ) ^ D * V) ≤ Real.exp (t * m) := by
      calc 2 * (r m : ℝ) * C ^ m * (K * (m : ℝ) ^ D * V)
          ≤ 2 * ((g + 1) * (m : ℝ) ^ D) * C ^ m * (K * (m : ℝ) ^ D * V) := by
            have : 0 ≤ C ^ m * (K * (m : ℝ) ^ D * V) := by
              have : 0 ≤ C := by linarith
              positivity
            nlinarith
        _ = 2 * (g + 1) * K * V * (m : ℝ) ^ (2 * D) * C ^ m := by ring
        _ ≤ _ := hem
    have key := GlobalTheory.T.abs_log_card_ballIn_sub_gramVolume_le k X p D hX hS P ω (m : ℤ) 1 (r m) (f m) (hf m) (hli m) (K * (m : ℝ) ^ D) V (C ^ m)
      (Real.exp (t * m)) hM hV (le_max_right _ _) (by positivity) (Real.exp_pos _) hcmb (hball m h1) hR
    rw [Real.log_exp] at key
    have hlog : Real.log (2 * (K * (m : ℝ) ^ D * V)) = Real.log (2 * K * V) + D * Real.log m := by
      have e : 2 * (K * (m : ℝ) ^ D * V) = (2 * K * V) * (m : ℝ) ^ D := by ring
      rw [e, Real.log_mul (by positivity) hmD.ne', Real.log_pow]
    have hmD1 : (0 : ℝ) < (m : ℝ) ^ (D + 1) := pow_pos hm0 _
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hmD1, div_le_iff₀ hmD1]
    refine key.trans (le_of_eq ?_)
    rw [hlog, pow_succ]
    field_simp
  · have h1 : Tendsto (fun m : ℕ => 2 * ((r m : ℝ) / (m : ℝ) ^ D)) atTop (𝓝 (2 * g)) := hg.const_mul 2
    have hl : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    have h2 : Tendsto (fun m : ℕ => (Real.log (2 * K * V) + D * Real.log m) / m) atTop (𝓝 0) := by
      have := ((tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (Real.log (2 * K * V))).add
        ((hl.comp tendsto_natCast_atTop_atTop).const_mul (D : ℝ))
      simp only [mul_zero, add_zero] at this
      refine this.congr fun m => ?_
      simp only [Function.comp_apply]
      ring
    simpa using h1.mul h2

end GlobalTheory.HSAmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoRegularisedLogNormMixedMeasureDivisors
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mix.LogLim

theorem compactSpace_of_proj {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R}
    (h : IsProjOver f) : CompactSpace X := by
  obtain ⟨m, i, hi, rfl⟩ := h
  have := isProper_str R m
  have : IsProper (i ≫ PSpace.str R m) := inferInstance
  exact QuasiCompact.compactSpace_of_compactSpace (i ≫ PSpace.str R m)

theorem nsq_nonneg {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
    (N : MLine p σ) (t : N.B.Sec) (y : CxPts p σ) : 0 ≤ N.φ.nsq (secVal p σ t) y := by
  unfold Weight.nsq; positivity

theorem continuous_nsq {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
    (N : MLine p σ) (t : N.B.Sec) : Continuous (N.φ.nsq (secVal p σ t)) :=
  continuous_iff_continuousAt.2 fun y => ((GlobalTheory.T.smoothWeightedLineBundle_logSectionNorm_properties k X p σ N t).2.2.1 y).continuousAt

theorem exists_nsq_le {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
    (hp : IsProjOver p) (N : MLine p σ) (t : N.B.Sec) : ∃ C : ℝ, ∀ y, N.φ.nsq (secVal p σ t) y ≤ C := by
  haveI : CompactSpace (CxPts p σ) := CxPts.compactSpace σ hp
  obtain ⟨C, hC⟩ := (isCompact_univ.image (continuous_nsq N t)).bddAbove
  exact ⟨C, fun y => hC ⟨y, Set.mem_univ _, rfl⟩⟩

end GlobalTheory.Mix.LogLim

open GlobalTheory.Mix.LogLim in

theorem GlobalTheory.Mix.tendsto_logReg : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → ∀ (N : MLine p σ) (t : N.B.Sec), (genericPoint X ∈ nonzeroLocus t → ∀ L : Fin (e + 1) → MLine p σ, Tendsto (fun n : ℕ => Mix.int L fun y => Real.log (N.φ.nsq (secVal p σ t) y + 1 / ((n : ℝ) + 1))) atTop (𝓝 (2 * Mix.int L (N.logSec t)))) ∧ ∀ (L : Fin e → MLine p σ) (Δ : CartierDiv X), (∀ z, Δ.mult z ≠ 0 → z ∈ nonzeroLocus t) → Tendsto (fun n : ℕ => ∑ᶠ z, (Δ.mult z : ℝ) * cycInt L (fun y => Real.log (N.φ.nsq (secVal p σ t) y + 1 / ((n : ℝ) + 1))) z) atTop (𝓝 (2 * ∑ᶠ z, (Δ.mult z : ℝ) * cycInt L (N.logSec t) z)) := by
  intro hP F _ X _ _ p σ e hp hdim N t
  set w := N.φ.nsq (secVal p σ t) with hw_def
  have hbasic := GlobalTheory.T.smoothWeightedLineBundle_logSectionNorm_properties F X p σ N t
  have hcont : Continuous w := continuous_nsq N t
  obtain ⟨C, hC⟩ := exists_nsq_le hp N t
  have hwC : ∀ y, 0 ≤ w y ∧ w y ≤ C := fun y => ⟨nsq_nonneg N t y, hC y⟩
  refine ⟨fun hgen L => ?_, fun L Δ hΔ => ?_⟩
  · have hfin := (GlobalTheory.T.mixedChernMeasure_finite_integrable_projective hP F X p σ (e + 1) hp hdim L).1
    have hint := GlobalTheory.T.log_norm_section_integrable_mixedChern_projective hP F X p σ (e + 1) hp hdim L N t hgen
    have one (ε : ℤˣ) (hi : Integrable (N.logSec t) (part L ε)) :
        Tendsto (fun n : ℕ => ∫ y, Real.log (w y + 1 / ((n : ℝ) + 1)) ∂part L ε) atTop
          (𝓝 (2 * ∫ y, Real.log (w y) / 2 ∂part L ε)) := by
      haveI := hfin ε
      have hnull := GlobalTheory.T.mixedChernFormSignedPartMeasure_compl_open_genericPoint_eq_zero F X p σ σ.injective hp (e + 1) L ε (nonzeroLocus t) hgen
      refine GlobalTheory.T.tendsto_integral_log_add_inv_succ _ (part L ε) w C hcont.measurable hwC ?_ hi
      refine ae_iff.2 (measure_mono_null (fun y hy => ?_) hnull)
      exact fun h => hy ((hbasic.2.1 y).2 h)
    have h1 := one 1 hint.1
    have h2 := one (-1) hint.2
    simp only [Mix.int, MLine.logSec, mul_sub]
    exact h1.sub h2
  · haveI : CompactSpace X := compactSpace_of_proj hp
    have hS := Δ.finite_support_mult
    have hsub (f : X → ℝ) : Function.support (fun z => (Δ.mult z : ℝ) * f z) ⊆ ↑hS.toFinset := by
      intro z hz
      simp only [Set.Finite.coe_toFinset, Function.mem_support]
      intro h0; apply hz; simp [h0]
    have hrw : (fun n : ℕ => ∑ᶠ z, (Δ.mult z : ℝ) * cycInt L (fun y => Real.log (w y + 1 / ((n : ℝ) + 1))) z) =
        fun n : ℕ => ∑ z ∈ hS.toFinset, (Δ.mult z : ℝ) * cycInt L (fun y => Real.log (w y + 1 / ((n : ℝ) + 1))) z :=
      funext fun n => finsum_eq_sum_of_support_subset _ (hsub _)
    rw [hrw, finsum_eq_sum_of_support_subset _ (hsub _), Finset.mul_sum]
    refine tendsto_finset_sum _ fun z hz => ?_
    have hz0 : Δ.mult z ≠ 0 := by simpa using hz
    have hcoh := CartierDiv.coheight_eq_one_of_mult_ne_zero hz0
    have hdz := (GlobalTheory.T.coheight_eq_one_iff_closure_dim_projective F X p e hp hdim z).1 hcoh
    obtain ⟨hfin, -, hnull, hlog⟩ := GlobalTheory.T.mixedChernForm_finite_integrable_pointClosure hP F X p σ hp e L z hdz
    have hzt := hΔ z hz0
    have hint := hlog N t hzt
    set π := ptMap (closι z) rfl σ with hπ
    have hπc : Continuous π := continuous_of_comp (f := closι z) fun _ => rfl
    have one (ε : ℤˣ) (hi : Integrable (fun y => N.logSec t (π y)) (part (fun i => (L i).pull (closι z) rfl) ε)) :
        Tendsto (fun n : ℕ => ∫ y, Real.log (w (π y) + 1 / ((n : ℝ) + 1)) ∂part (fun i => (L i).pull (closι z) rfl) ε)
          atTop (𝓝 (2 * ∫ y, Real.log (w (π y)) / 2 ∂part (fun i => (L i).pull (closι z) rfl) ε)) := by
      haveI := hfin ε
      refine GlobalTheory.T.tendsto_integral_log_add_inv_succ _ _ (fun y => w (π y)) C (hcont.comp hπc).measurable (fun y => hwC (π y)) ?_ hi
      refine ae_iff.2 (measure_mono_null (fun y hy => ?_) (hnull (nonzeroLocus t) hzt ε))
      exact fun h => hy ((hbasic.2.1 (π y)).2 h)
    have h1 := one 1 hint.1
    have h2 := one (-1) hint.2
    have := (h1.sub h2).const_mul (Δ.mult z : ℝ)
    simp only [cycInt, Mix.int, MLine.logSec] at this ⊢
    convert this using 2
    ring
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistUpperBound
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.ConjTwist (BaseOf UnitOff ser)
open GlobalTheory.FlatVecSum (princ)
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open Formalism.L2.Host (embLL0)
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp

namespace GlobalTheory.BigOn.Exp.TupLe

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem baseOf_of_pin {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type}
    {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd}
    (hL : Rl.toLevCh.Is A3.A.μ0) {ρ : Setup D.ntw} (hρ : ρ.Good) (hp : RealPin Rl cG ρ) (i : D.ntw.Tw)
    (j : Fin D.R.m) (b : Bool) : BaseOf Rl.toRealDat j (ρ.B i j b) := by
  have hB := hρ.base i j b
  have hlam := GlobalTheory.BaseLiftWeight.lam_eq D _ Rl.toLevCh A3.A.μ0 j (ρ.B i j b) hL hB (hp.mu0 i j b) (hp.ap i j b) (hp.am i j b)
  have hc : ∀ τ, (ρ.B i j b).w.c τ = GlobalTheory.ConjTwist.liftC D j τ := fun τ => GlobalTheory.BaseLiftWeight.c_eq hL hB (hp.mu0 i j b) τ
  have hP : (ρ.B i j b).w.p = GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.pS D j := funext fun τ => congrArg Prod.fst (hB.sig τ)
  have hQ : (ρ.B i j b).w.q = GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.qS D j := funext fun τ => congrArg Prod.snd (hB.sig τ)
  have hAP : (ρ.B i j b).w.ap = GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.aP D j := funext fun τ => hp.ap i j b τ
  have hAM : (ρ.B i j b).w.am = GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.aM D j := funext fun τ => hp.am i j b τ
  refine
    { ψ := hp.psi i j b, θ := hp.inf i j b, sT := hp.cartT i j b, BS := hp.onbS i j b, BT := hp.onbT i j b,
      ΛS := hp.latS i j b, ΛT := hp.latT i j b, βS := hp.frS i j b, βT := hp.frT i j b, vac := hp.vac i j b,
      Pg := hp.Pg i j b, mu0 := hp.mu0 i j b, eta := hp.eta i j b, lam := hlam, delta := ?_, p := hP, q := hQ,
      c := funext hc }
  rw [← GlobalTheory.ConjTwist.liftWeight_delta, Weight.delta, Weight.delta, hP, hQ, hAP, hAM]
  rfl

theorem twLe : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → TwAdm → TwChr → TwLe := by
  intro _ _ _ hA hX
  refine AtTw.imp (AtTw.and hA hX) fun Fm x hx i p hr hm w hw j ⟨a, c⟩ ρ hρ ν rd hf hc => ?_
  have hL := GlobalTheory.T.second_link_of_weight_rows _ _ _ _ _ _ _ _ _ _ p hr hm.1
  have h0 := baseOf_of_pin (cG := p.cG) p.charW.base.lev hρ hf.pin ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)
  obtain ⟨c1, c2⟩ := c ρ hρ hf.adapted
  obtain ⟨-, e, h1, h2⟩ := hf.adapted
  exact realTw_le GlobalTheory.T.places_bound_tuple GlobalTheory.T.flat_bound_tuple GlobalTheory.T.trace_bound_tuple GlobalTheory.T.coefficient_bound_tuple GlobalTheory.T.small_bound_tuple hr hm hL hw a.1 hρ hf.pin hf.level
    { h0 with } e h1 h2 c1 c2 hf.norm hf.rat hc

end GlobalTheory.BigOn.Exp.TupLe

end
end

