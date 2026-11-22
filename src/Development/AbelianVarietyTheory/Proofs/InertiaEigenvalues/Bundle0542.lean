import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0207
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0212
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0336
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0370
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0210
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0203
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0196
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0489
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0194
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0452
import Formalism.LocalRingCardinality.HostCls
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0014
import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.Bundle0003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0447
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0492
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0518
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0018
import Formalism.SharpRestriction.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0519
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0476
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0520
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0481
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormLeOneOfMemOL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0061
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0069
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0495
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0516
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0485

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RootCancelPowEqSelfAcrisGaussNorm
section
noncomputable section

open scoped Formalism.Per

namespace GlobalTheory.PMon.Gauss

theorem rootCancel_radius (l : ℕ) [Fact l.Prime] {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    (l : ℝ)⁻¹ ≤ (l : ℝ) ^ (-r) ∧ (l : ℝ) ^ (-r) < 1 := by
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  constructor
  · rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hl.le (by linarith)
  · exact Real.rpow_lt_one_of_one_lt_of_neg hl (by linarith)

theorem vr_iterate_φc (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Acris l) (hx : x ≠ 0) :
    ∀ k : ℕ, ∀ r ∈ Set.Ioc (0 : ℝ) 1,
      (φc l)^[k] x ≠ 0 ∧ vr l r ((φc l)^[k] x) = (l : ℝ) ^ k * vr l (r / (l : ℝ) ^ k) x := by
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  intro k
  induction k with
  | zero => intro r _; simp [hx]
  | succ k ih =>
    intro r hr
    have hrl : r / l ∈ Set.Ioc (0 : ℝ) 1 :=
      ⟨div_pos hr.1 (by linarith), (div_le_one (by linarith)).2 (by linarith [hr.2])⟩
    obtain ⟨h1, h2⟩ := ih (r / l) hrl
    have V := (GlobalTheory.T.acrisValuation_radius_laws l r hr.1 hr.2).2.1 _ h1
    refine ⟨by rw [Function.iterate_succ_apply']; exact V.1, ?_⟩
    rw [Function.iterate_succ_apply', V.2, h2, div_div, pow_succ, mul_comm ((l : ℝ) ^ k) (l : ℝ)]
    ring

theorem vr_prod_range (l : ℕ) [Fact l.Prime] (x : ℕ → Formalism.Per.Acris l) (hx : ∀ i, x i ≠ 0)
    (h10 : (1 : Formalism.Per.Acris l) ≠ 0) :
    ∀ n : ℕ, (∏ i ∈ Finset.range n, x i) ≠ 0 ∧
      ∀ r ∈ Set.Ioc (0 : ℝ) 1, vr l r (∏ i ∈ Finset.range n, x i) = ∑ i ∈ Finset.range n, vr l r (x i) := by
  intro n
  induction n with
  | zero =>
    refine ⟨by simpa using h10, fun r hr => ?_⟩
    have hρ := rootCancel_radius l hr.1 hr.2
    simp [vr, (gC_basic_values l _ hρ.1 hρ.2).1]
  | succ n ih =>
    have hne : (∏ i ∈ Finset.range (n + 1), x i) ≠ 0 := by
      rw [Finset.prod_range_succ]
      intro h0
      rcases GlobalTheory.T.acris_eq_zero_or_eq_zero_of_mul_eq_zero l _ _ h0 with h | h
      · exact ih.1 h
      · exact hx n h
    refine ⟨hne, fun r hr => ?_⟩
    rw [Finset.prod_range_succ, Finset.sum_range_succ, (GlobalTheory.T.acrisValuation_radius_laws l r hr.1 hr.2).1 _ _ ih.1 (hx n),
      ih.2 r hr]

theorem root_cancel_pow_eq_self : ∀ (l : ℕ) [Fact l.Prime] (h s : ℕ), s < h → ∀ (w w' : Formalism.Per.Acris l) (ζ : Formalism.Per.Fl l) (o : ℕ) (ρ₀ : ℝ), (φc l)^[h] w' = (l : Formalism.Per.Acris l) ^ s * w' → w' ≠ 0 → φc l w * w' = w * φc l w' → (∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ w = gC l ρ w') → 0 < o → ζ ^ (l ^ o) = ζ → ζ ≠ 0 → (l : ℝ)⁻¹ ≤ ρ₀ → ρ₀ < 1 → gC l ρ₀ (w - tc l ζ * w') < gC l ρ₀ w' → ζ ^ l = ζ := by
  intro l _ h s hsh w w' ζ o ρ₀ hh hw' hφ hnorm ho hζo hζ0 hρ₀1 hρ₀2 hlt
  classical
  have hlN : 1 < l := (Fact.out : l.Prime).one_lt
  have hl : (1 : ℝ) < l := by exact_mod_cast hlN
  have hl0 : (0 : ℝ) < l := by linarith
  set F : Formalism.Per.Fl l → Formalism.Per.Fl l := fun y => y ^ l with hF
  have hFit : ∀ i, F^[i] ζ = ζ ^ (l ^ i) := by
    intro i
    induction i with
    | zero => simp
    | succ i ih => rw [Function.iterate_succ_apply', ih, hF, pow_succ, pow_mul]
  have hper : Function.IsPeriodicPt F o ζ := by
    show F^[o] ζ = ζ
    rw [hFit]; exact hζo
  set o' := Function.minimalPeriod F ζ with ho'
  have ho'pos : 0 < o' := Function.IsPeriodicPt.minimalPeriod_pos ho hper
  have hz_eq : ∀ i j, F^[i] ζ = F^[j] ζ → i % o' = j % o' := by
    intro i j hij
    rw [← Function.iterate_mod_minimalPeriod_eq (n := i), ← Function.iterate_mod_minimalPeriod_eq (n := j)] at hij
    exact (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod (Nat.mod_lt _ ho'pos) (Nat.mod_lt _ ho'pos)).1 hij
  have hmod1 : ∀ i, (i + 1) % o' = i % o' → o' = 1 := by
    intro i hi
    have hmod : (i + 1) % o' = (i + 0) % o' := by rw [add_zero]; exact hi
    have h10 : 1 ≡ 0 [MOD o'] := Nat.ModEq.add_left_cancel' i hmod
    exact Nat.dvd_one.mp (Nat.modEq_zero_iff_dvd.mp h10)
  suffices hsuff : o' = 1 by
    have := Function.iterate_minimalPeriod (f := F) (x := ζ)
    rw [← ho', hsuff] at this
    simpa [hF] using this

  have hz0 : ∀ i, F^[i] ζ ≠ 0 := fun i => by rw [hFit]; exact pow_ne_zero _ hζ0
  have hzfix : ∀ i, (F^[i] ζ) ^ (l ^ o) = F^[i] ζ := by
    intro i
    rw [hFit, ← pow_mul, mul_comm, pow_mul, hζo]
  have hzsucc : ∀ i, F^[i + 1] ζ = (F^[i] ζ) ^ l := fun i => Function.iterate_succ_apply' _ _ _
  have hzper : F^[o'] ζ = F^[0] ζ := Function.iterate_minimalPeriod

  have hG : ∀ ρ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → IsGauss l ρ (gC l ρ) := fun ρ h0 h1 => isGauss_gC_target l ρ h0 h1
  have htc1 : ∀ ρ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → ∀ i, gC l ρ (tc l (F^[i] ζ)) = 1 := by
    intro ρ h0 h1 i
    rw [(gC_basic_values l ρ h0 h1).2.2.2.1]
    have h00 : (0 : Formalism.Per.Fl l) ^ (l ^ o) = 0 := zero_pow (pow_ne_zero _ (by omega))
    have := GlobalTheory.TiltAbs.norm_untilt_sub_eq_one_of_pow_fixed l o _ 0 ho (hzfix i) h00 (hz0 i)
    simpa using this
  set x : ℕ → Formalism.Per.Acris l := fun i => w - tc l (F^[i] ζ) * w' with hx
  have hfrob : ∀ i, φc l (x i) * w' = x (i + 1) * φc l w' := by
    intro i
    simp only [hx, map_sub, map_mul, frob_teich, hzsucc]
    linear_combination hφ

  by_cases hA : ∃ i, x i = 0
  · obtain ⟨i, hi⟩ := hA
    have hwi : w = tc l (F^[i] ζ) * w' := sub_eq_zero.1 hi
    rw [hwi] at hφ
    have hfix := GlobalTheory.T.teichmuller_pow_eq_of_frobenius_ratio l w' (F^[i] ζ) hw' hφ
    apply hmod1 i
    apply hz_eq
    rw [hzsucc]; exact hfix
  push_neg at hA

  have h10 : (1 : Formalism.Per.Acris l) ≠ 0 := fun h1 => hw' (by rw [← one_mul w', h1, zero_mul])
  have hrad := fun r (hr : r ∈ Set.Ioc (0 : ℝ) 1) => rootCancel_radius l hr.1 hr.2
  have hpos : ∀ y : Formalism.Per.Acris l, y ≠ 0 → ∀ r ∈ Set.Ioc (0 : ℝ) 1, 0 < gC l ((l : ℝ) ^ (-r)) y :=
    fun y hy r hr => GlobalTheory.T.gaussNormAcrisRadius_pos_definite l y hy _ (hrad r hr).1 (hrad r hr).2
  have hmulw : ∀ r ∈ Set.Ioc (0 : ℝ) 1, ∀ i,
      gC l ((l : ℝ) ^ (-r)) (tc l (F^[i] ζ) * w') = gC l ((l : ℝ) ^ (-r)) w' := by
    intro r hr i
    rw [(hG _ (hrad r hr).1 (hrad r hr).2).2.2.2.1, htc1 _ (hrad r hr).1 (hrad r hr).2, one_mul]
  have hxle : ∀ r ∈ Set.Ioc (0 : ℝ) 1, ∀ i, gC l ((l : ℝ) ^ (-r)) (x i) ≤ gC l ((l : ℝ) ^ (-r)) w' := by
    intro r hr i
    have hGr := hG _ (hrad r hr).1 (hrad r hr).2
    have := hGr.2.1 w (-(tc l (F^[i] ζ) * w'))
    rw [← sub_eq_add_neg, hGr.2.2.1, hmulw r hr i, hnorm _ (hrad r hr).1 (hrad r hr).2, max_self] at this
    exact this
  set fv : ℕ → ℝ → ℝ := fun i r => vr l r (x i) - vr l r w' with hfv
  have hfv_pos : ∀ r ∈ Set.Ioc (0 : ℝ) 1, ∀ i,
      0 < fv i r ↔ gC l ((l : ℝ) ^ (-r)) (x i) < gC l ((l : ℝ) ^ (-r)) w' := by
    intro r hr i
    simp only [hfv, vr, sub_pos, neg_lt_neg_iff]
    exact Real.logb_lt_logb_iff hl (hpos _ (hA i) r hr) (hpos _ hw' r hr)
  have hfv_nonneg : ∀ i, ∀ r ∈ Set.Ioc (0 : ℝ) 1, 0 ≤ fv i r := by
    intro i r hr
    simp only [hfv, vr, sub_nonneg, neg_le_neg_iff]
    exact Real.logb_le_logb_of_le hl (hpos _ (hA i) r hr) (hxle r hr i)
  have hfv_cont : ∀ i, ContinuousOn (fv i) (Set.Ioc 0 1) := fun i =>
    ((GlobalTheory.T.acrisValuationAtRadius_concave_cont_slope l _ (hA i)).2.1).sub (GlobalTheory.T.acrisValuationAtRadius_concave_cont_slope l _ hw').2.1
  have hfv_class : ∀ i j, ∀ r ∈ Set.Ioc (0 : ℝ) 1, 0 < fv i r → 0 < fv j r → i % o' = j % o' := by
    intro i j r hr hi hj
    by_cases hzz : F^[i] ζ = F^[j] ζ
    · exact hz_eq _ _ hzz
    exfalso
    have hGr := hG _ (hrad r hr).1 (hrad r hr).2
    have hd : x j - x i = (tc l (F^[i] ζ) - tc l (F^[j] ζ)) * w' := by simp only [hx]; ring
    have hsep := GlobalTheory.TiltAbs.norm_untilt_sub_eq_one_of_pow_fixed l o _ _ ho (hzfix i) (hzfix j) hzz
    have h1 := GlobalTheory.T.gaussNormAcris_teichmuller_tilt_sub_eq_one l _ _ hsep _ (hrad r hr).1 (hrad r hr).2
    have hle := hGr.2.1 (x j) (-(x i))
    rw [← sub_eq_add_neg, hGr.2.2.1, hd, hGr.2.2.2.1, h1, one_mul] at hle
    have := (hfv_pos r hr i).1 hi
    have := (hfv_pos r hr j).1 hj
    have := le_max_iff.1 hle
    rcases this with h | h <;> linarith
  have hfv_shift : ∀ i r, 0 < r → r ≤ 1 / (l : ℝ) → fv (i + 1) ((l : ℝ) * r) = (l : ℝ) * fv i r := by
    intro i r hr0 hr1
    have hlr : (l : ℝ) * r ∈ Set.Ioc (0 : ℝ) 1 :=
      ⟨by positivity, by rw [le_div_iff₀ hl0] at hr1; linarith⟩
    have V := GlobalTheory.T.acrisValuation_radius_laws l _ hlr.1 hlr.2
    have hrr : (l : ℝ) * r / l = r := by field_simp
    have e := congrArg (vr l ((l : ℝ) * r)) (hfrob i)
    rw [V.1 _ _ (V.2.1 _ (hA i)).1 hw', V.1 _ _ (hA (i + 1)) (V.2.1 _ hw').1, (V.2.1 _ (hA i)).2,
      (V.2.1 _ hw').2, hrr] at e
    simp only [hfv]
    linarith

  have hper_x : x o' = x 0 := by simp only [hx, hzper]
  obtain ⟨hWne, hWvr⟩ := vr_prod_range l x hA h10 o'
  set W := ∏ i ∈ Finset.range o', x i with hW
  have hsum : ∀ r ∈ Set.Ioc (0 : ℝ) 1, vr l r W - (o' : ℝ) * vr l r w' = ∑ i ∈ Finset.range o', fv i r := by
    intro r hr
    simp only [hfv, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, hWvr r hr]
  have hB : ∀ r ∈ Set.Ioc (0 : ℝ) 1, (l : ℝ) ^ h * vr l (r / (l : ℝ) ^ h) w' = vr l r w' + s * r := by
    intro r hr
    have e := (vr_iterate_φc l w' hw' h r hr).2
    rw [hh, (GlobalTheory.T.acrisValuation_radius_laws l r hr.1 hr.2).2.2.1 w' s hw'] at e
    linarith
  have hAB : ∀ r ∈ Set.Ioc (0 : ℝ) (1 / l), vr l ((l : ℝ) * r) W - (o' : ℝ) * vr l ((l : ℝ) * r) w' =
      (l : ℝ) * (vr l r W - (o' : ℝ) * vr l r w') := by
    intro r hr
    have hr1 : r ∈ Set.Ioc (0 : ℝ) 1 :=
      ⟨hr.1, hr.2.trans (by rw [div_le_one hl0]; exact hl.le)⟩
    have hlr : (l : ℝ) * r ∈ Set.Ioc (0 : ℝ) 1 :=
      ⟨mul_pos hl0 hr.1, by have := hr.2; rw [le_div_iff₀ hl0] at this; linarith⟩
    rw [hsum _ hlr, hsum _ hr1, Finset.mul_sum]
    have hcyc : ∑ i ∈ Finset.range o', fv i ((l : ℝ) * r) = ∑ i ∈ Finset.range o', fv (i + 1) ((l : ℝ) * r) := by
      have e1 := Finset.sum_range_succ (fun i => fv i ((l : ℝ) * r)) o'
      have e2 := Finset.sum_range_succ' (fun i => fv i ((l : ℝ) * r)) o'
      have e3 : fv o' ((l : ℝ) * r) = fv 0 ((l : ℝ) * r) := by simp only [hfv, hper_x]
      linarith
    rw [hcyc]
    exact Finset.sum_congr rfl (fun i _ => hfv_shift i r hr.1 hr.2)
  obtain ⟨n, hn⟩ := GlobalTheory.T.exists_int_sub_mul_eq_int_mul_of_homogeneous l h s o' hlN hsh ho'pos (fun r => vr l r W) (fun r => vr l r w')
    (GlobalTheory.T.acrisValuationAtRadius_concave_cont_slope l _ hWne).1 (GlobalTheory.T.acrisValuationAtRadius_concave_cont_slope l _ hw').1 (GlobalTheory.T.acrisValuationAtRadius_concave_cont_slope l _ hWne).2.1 (GlobalTheory.T.acrisValuationAtRadius_concave_cont_slope l _ hw').2.1
    (GlobalTheory.T.acrisValuationAtRadius_concave_cont_slope l _ hWne).2.2 (GlobalTheory.T.acrisValuationAtRadius_concave_cont_slope l _ hw').2.2 hB hAB

  set r₀ := -Real.logb l ρ₀ with hr₀
  have hρ₀pos : 0 < ρ₀ := lt_of_lt_of_le (inv_pos.2 hl0) hρ₀1
  have hr₀ρ : (l : ℝ) ^ (-r₀) = ρ₀ := by rw [hr₀, neg_neg, Real.rpow_logb hl0 hl.ne' hρ₀pos]
  have hr₀mem : r₀ ∈ Set.Ioc (0 : ℝ) 1 := by
    constructor
    · rw [hr₀, neg_pos]; exact Real.logb_neg hl hρ₀pos hρ₀2
    · rw [hr₀, neg_le]
      have := Real.logb_le_logb_of_le hl (inv_pos.2 hl0) hρ₀1
      rwa [Real.logb_inv, Real.logb_self_eq_one hl] at this
  have hf0 : 0 < fv 0 r₀ := by
    rw [hfv_pos r₀ hr₀mem 0, hr₀ρ]
    simpa [hx] using hlt
  have hnpos : (0 : ℝ) < n := by
    have hs := hsum r₀ hr₀mem
    rw [hn r₀ hr₀mem] at hs
    have : fv 0 r₀ ≤ ∑ i ∈ Finset.range o', fv i r₀ :=
      Finset.single_le_sum (fun i _ => hfv_nonneg i r₀ hr₀mem) (Finset.mem_range.2 ho'pos)
    nlinarith [hr₀mem.1]
  have hcover : ∀ r ∈ Set.Ioc (0 : ℝ) 1, ∃ i, 0 < fv i r := by
    intro r hr
    by_contra H
    push_neg at H
    have hs := hsum r hr
    rw [hn r hr] at hs
    have : ∑ i ∈ Finset.range o', fv i r ≤ 0 := Finset.sum_nonpos (fun i _ => H i)
    nlinarith [hr.1]
  exact GlobalTheory.orbit_class_trivial o' (l : ℝ) fv ho'pos hl hfv_cont hfv_nonneg hfv_class hcover
    (fun i r hr0 hr1 hi => by rw [hfv_shift i r hr0 hr1]; positivity)

end GlobalTheory.PMon.Gauss

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitRowAt
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.FrobeniusOrbits GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes

namespace GlobalTheory.SplitRowAll

theorem splitRow_at : ∀ D : D7, SplitRow_at D := by
  intro D
  refine ⟨fun l hl => GlobalTheory.T.split_prime_implies_places_split D.host l hl, fun i hi => ⟨?_, ?_, ?_, ?_⟩⟩
  · intro w hw
    have h2 : D.nd.l i ∉ D.host.small := ((primeClass_eq_splitK_iff _).1 hi.2.2.2.2.2).1
    exact (GlobalTheory.T.K0_eq_and_good_of_ne D i h2 hi.2.2.1 hi.2.2.2.1 w hw).1
  · rintro w hw τ ⟨h1, h2⟩
    rcases GlobalTheory.SplitRowProbe.embIn_xor D i w hw τ with h | h
    · exact h.2 h2
    · exact h.2 h1
  · exact GlobalTheory.T.splitPrime_place_cmType_conjugate D i hi
  · exact GlobalTheory.T.cmHalfTypePlaces_meet_conjugatePairs_and_count D i hi

end GlobalTheory.SplitRowAll
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StarInequalityRowsADOfGlobalTheoremsStatement
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.starInequality_rowsAD_of_global_theorems : ∀ (D : D7) (L : SizeData₂ D) (HW : HWOf D.loc) (X : KillingConditions.HubData D) (R : KillingConditions.RowK), KillingConditions.DataAD L HW X R → KillingConditions.StepAD L X → TruncatedSeriesCountingIdentities.IntegralityFromMetric D → (∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i) (ep : Bool) (e' : ℕ) (c0 : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ), EmbeddingTypes.admitted i r ρ π dc ep e' c0 cB → (D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.admG2 i r ρ π) → EmbeddingTypes.aux₃ i r ρ π dc ep e' c0 cB) → (∀ i, D.nd.l i ∉ TwistedPlaces.gset D → ∀ π ∈ D.nd.Zgood i, TruncatedSeriesCountingIdentities.admG2 i (X.r i) (X.ρ i) π) → KillingConditions.KillAt X.ρ → TwistedPlaces.ShaFinOdd D → KillingConditions.StarAD L X := by
  first | exact @GlobalTheory.NLink.starAD_of_global | exact GlobalTheory.NLink.starAD_of_global | (intros; apply GlobalTheory.NLink.starAD_of_global <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameAnyAtPlaceStatement
section
open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tame_any_at_place : ∀ D : D7, GalAway D → FrobDense D → ∀ (i : D.nd.Loc) (π : D.naut.CG D.R.r) (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)), D.naut.csd π → D.naut.ralg π → FullLab D [⟨D.R.r, π, 1⟩] → IsRepOfSig D.nd D.naut i [⟨D.R.r, π, 1⟩] ρ → ∀ k : Fin 2, D.nd.l i ≠ D.host.g k → ∀ v : D.nd.PlG k, TameAnyAt D i [⟨D.R.r, π, 1⟩] ρ k (D.naut.plGw k v) := by
  first | exact @GlobalTheory.TypeLeaf.tameAnyAt_fixed | exact GlobalTheory.TypeLeaf.tameAnyAt_fixed | (intros; apply GlobalTheory.TypeLeaf.tameAnyAt_fixed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameFixedAwayStatement
section
open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tame_fixed_away : ∀ D : D7, WildOne D → GalAway D → FrobDense D → ∀ (i : D.nd.Loc) (π : D.naut.CG D.R.r) (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)), D.naut.csd π → D.naut.ralg π → FullLab D [⟨D.R.r, π, 1⟩] → IsRepOfSig D.nd D.naut i [⟨D.R.r, π, 1⟩] ρ → ∀ k : Fin 2, D.nd.l i ≠ D.host.g k → TameFixed D i [⟨D.R.r, π, 1⟩] ρ k := by
  first | exact @GlobalTheory.TypeLeaf.tameFixed_of_cuspidal | exact GlobalTheory.TypeLeaf.tameFixed_of_cuspidal | (intros; apply GlobalTheory.TypeLeaf.tameFixed_of_cuspidal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateDualDeRhamAndFilZeroDimAllStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateDual_deRham_and_filZero_dim_all : ∀ D : D7, Formalism.MainNotions.LocalSituation.adm8 D := by
  first | exact @GlobalTheory.TateDualFil.main | exact GlobalTheory.TateDualFil.main | (intros; apply GlobalTheory.TateDualFil.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateDualTwistedSumSummandIsDeRhamStatement
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateDual_twistedSumSummand_isDeRham : ∀ (D : D7), FontaineAtPlacesOverL (D := D) → PotDRL D.loc → ∀ (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r →
    ∀ (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (n : ℕ),
      PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) n →
    ∀ X : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw), IsSummandTw i w hw r Xs X →
    ∀ (X' : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw))
      (PX : X.V →ₗ[Br.LL D.nbr i w hw] X'.V →ₗ[Br.LL D.nbr i w hw] Br.LL D.nbr i w hw),
      IsDual1 (Br.PD D.loc D.nbr i w hw) X.ρ X'.ρ PX → IsDR (Br.PD D.loc D.nbr i w hw) X'.ρ := by
  first | exact @GlobalTheory.SummandDualDR.main | exact GlobalTheory.SummandDualDR.main | (intros; apply GlobalTheory.SummandDualDR.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TaylorShiftFrobeniusMemDividedTwoVariableGeneratStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.taylorShift_frobenius_mem_dividedTwoVariableGeneratorSet : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative K)^[i] f) → ∀ x : (Wq l a)⟦X⟧, shP a sh (inclS t K (frobS l a x)) ∈ PPSet t K e ∧ ∃ B ∈ PPSet t K e, shP a sh (inclS t K (frobS l a x)) - constP a K (inclS t K (frobS l a x)) = (l : ZMod a → K⟦X⟧⟦X⟧) * B := by
  first | exact @GlobalTheory.CrysPrism.ShMem.shP_frob_mem | exact GlobalTheory.CrysPrism.ShMem.shP_frob_mem | (intros; apply GlobalTheory.CrysPrism.ShMem.shP_frob_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerSubOneAinfPropertiesCompatibleRoots
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.MuOfEps

variable {l : ℕ} [hl : Fact l.Prime]

theorem root_eq {ε δ : OCb l} (h : δ ^ l = ε) : δ = (frobeniusEquiv (OCb l) l).symm ε := by
  apply (frobeniusEquiv (OCb l) l).injective
  rw [RingEquiv.apply_symm_apply, ← h]
  rfl

theorem coeff_zero_muOf (x : OCb l) : (muOf x).coeff 0 = x - 1 := by
  change WittVector.constantCoeff (WittVector.teichmuller l x - 1) = x - 1
  rw [map_sub, map_one, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]

theorem frob_iterate_muOf (x : OCb l) (n : ℕ) :
    WittVector.frobenius^[n] (muOf x) = muOf (x ^ (l ^ n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, muOf, muOf, map_sub, map_one,
      WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, ← pow_mul, pow_succ]

theorem theta_muOf (x : OCb l) : Per.θ l (muOf x) = x.untilt - 1 := by
  rw [muOf, map_sub, map_one, WittVector.fontaineTheta_teichmuller]

variable (l) in

def kerAll : Ideal (Ainf l) := ⨅ n : ℕ, RingHom.ker ((Per.θ l).comp (WittVector.frobenius ^ n))

theorem mem_kerAll (a : Ainf l) : a ∈ kerAll l ↔ ∀ n : ℕ, Per.θ l (WittVector.frobenius^[n] a) = 0 := by
  simp only [kerAll, Ideal.mem_iInf, RingHom.mem_ker, RingHom.comp_apply, RingHom.coe_pow]

theorem muOf_mem_kerAll {x : OCb l} (hx : x.untilt = 1) : muOf x ∈ kerAll l := by
  rw [mem_kerAll]
  intro n
  rw [frob_iterate_muOf, theta_muOf, map_pow, hx, one_pow, sub_self]

theorem kerAll_sat (a : Ainf l) (h : (l : Ainf l) * a ∈ kerAll l) : a ∈ kerAll l := by
  rw [mem_kerAll] at h ⊢
  intro n
  have h1 := h n
  rw [← RingHom.coe_pow, map_mul, map_natCast, map_mul, map_natCast, RingHom.coe_pow] at h1
  exact (mul_eq_zero.1 h1).resolve_left (Nat.cast_ne_zero.2 hl.out.ne_zero)

theorem isEps_mem {ε : OCb l} (hε : IsEps ε) :
    GlobalTheory.MemLoc.IsEps ε := by
  obtain ⟨h1, δ, hδ, hδ1⟩ := hε
  exact ⟨h1, by rw [← root_eq hδ]; exact hδ1⟩

theorem ne_one {ε : OCb l} (hε : IsEps ε) : ε ≠ 1 := by
  obtain ⟨-, δ, hδ, hδ1⟩ := hε
  rintro rfl
  have : δ = 1 := by rw [root_eq hδ, map_one]
  exact hδ1 (by rw [this, map_one])

theorem muOf_dvd {ε : OCb l} (hε : IsEps ε) {x : OCb l} (hx : x.untilt = 1) : muOf ε ∣ muOf x :=
  GlobalTheory.T.wittVector_dvd_of_mem_saturated_ideal l (OCb l) (kerAll l) (muOf ε) (muOf_mem_kerAll hε.1) kerAll_sat
    (fun a ha => by rw [coeff_zero_muOf]; exact GlobalTheory.T.epsilon_sub_one_dvd_ainf_coeff_zero_of_theta_vanishing l ε hε a ((mem_kerAll a).1 ha)) _ (muOf_mem_kerAll hx)

theorem muOf_ne_zero {ε : OCb l} (hε : IsEps ε) : muOf ε ≠ 0 := fun h => by
  have := congrArg (fun y : Ainf l => y.coeff 0) h
  simp only [coeff_zero_muOf, WittVector.zero_coeff] at this
  exact ne_one hε (sub_eq_zero.1 this)

theorem σA_muOf (g : GQ l) (x : OCb l) : Per.σA g (muOf x) = muOf (Per.σF g x) := by
  rw [muOf, muOf, map_sub, map_one, GlobalTheory.RingIface.sigA_teich]

theorem untilt_σF_eq {x : OCb l} (hx : x.untilt = 1) (g : GQ l) : (Per.σF g x).untilt = 1 := by
  rw [GlobalTheory.RingBasics.untilt_σF, hx, map_one]

end GlobalTheory.MuOfEps

namespace GlobalTheory.MuOfEps

variable {l : ℕ} [hl : Fact l.Prime]

theorem exists_isEps (l : ℕ) [Fact l.Prime] : ∃ ε : OCb l, IsEps ε := by
  obtain ⟨ζ, e, h0, -, h1, hr⟩ := GlobalTheory.MemLoc.exists_zeta_eps l
  have he : e.untilt = 1 := Subtype.ext (by
    have := hr 0
    rw [h0, map_one] at this
    exact this)
  have hE : GlobalTheory.MemLoc.IsEps e := ⟨he, fun hh => h1 (by
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← hr 1, map_one]
    exact congrArg Subtype.val hh)⟩
  exact ⟨e, he, _, frobeniusEquiv_symm_pow_p (OCb l) l e, hE.2⟩

theorem units_σA {ε : OCb l} (hε : IsEps ε) (g : GQ l) :
    ∃ u : (Ainf l)ˣ, Per.σA g (muOf ε) = u * muOf ε := by
  obtain ⟨a, ha⟩ := muOf_dvd hε (untilt_σF_eq hε.1 g)
  obtain ⟨b, hb⟩ := muOf_dvd hε (untilt_σF_eq hε.1 g⁻¹)
  rw [← σA_muOf] at ha hb
  have h : muOf ε = Per.σA g b * a * muOf ε := by
    have := congrArg (Per.σA g) hb
    rw [← GlobalTheory.RingBasics.σA_mul, mul_inv_cancel, GlobalTheory.RingBasics.σA_one, map_mul, ha] at this
    linear_combination this
  have h1 : Per.σA g b * a = 1 := by
    have h2 : (Per.σA g b * a - 1) * muOf ε = 0 := by linear_combination -h
    exact sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_right (muOf_ne_zero hε))
  refine ⟨⟨a, Per.σA g b, by rw [mul_comm]; exact h1, h1⟩, ?_⟩
  rw [ha, mul_comm]

theorem main : ∀ (l : ℕ) [Fact l.Prime], (∃ ε : OCb l, IsEps ε) ∧ ∀ ε δ : OCb l, IsEps ε → δ ^ l = ε → (∃ ξ : Ainf l, Ideal.span {ξ} = RingHom.ker (Per.θ l) ∧ muOf ε = ξ * muOf δ) ∧ WittVector.frobenius (muOf δ) = muOf ε ∧ Per.θ l (muOf δ) ≠ 0 ∧ IsUnit (acrisToBcris l (ainfToAcris l (muOf ε))) ∧ IsUnit (inclW l (muOf ε)) ∧ (∀ g : GQ l, ∃ u : (Ainf l)ˣ, Per.σA g (muOf ε) = u * muOf ε) ∧ ∀ x : OCb l, x.untilt = 1 → muOf ε ∣ muOf x := by
  intro l _
  refine ⟨exists_isEps l, fun ε δ hε hδ => ?_⟩
  have hr := root_eq hδ
  have hE := isEps_mem hε
  refine ⟨⟨GlobalTheory.MemLoc.xi ε, (GlobalTheory.MemLoc.ker_theta_eq_span_xi hE).symm, ?_⟩, ?_, ?_, ?_, ?_, units_σA hε,
    fun x hx => muOf_dvd hε hx⟩
  · rw [GlobalTheory.MemLoc.xi, ← hr, muOf, muOf, geom_sum_mul, ← map_pow, hδ]
  · rw [muOf, muOf, map_sub, map_one, WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller,
      frobenius_def, hδ]
  · rw [theta_muOf, sub_ne_zero]
    obtain ⟨-, δ', hδ', hδ'1⟩ := hε
    rwa [root_eq hδ', ← hr] at hδ'1
  · exact GlobalTheory.CrisLoc.unit_of_root l ε hε.1 (ne_one hε)
  · refine WittVector.isUnit_of_coeff_zero_ne_zero _ fun h => ?_
    have h0 : (muOf ε).coeff 0 = 0 :=
      IsFractionRing.injective (OCb l) (Cb l) (h.trans (map_zero _).symm)
    rw [coeff_zero_muOf] at h0
    exact ne_one hε (sub_eq_zero.1 h0)

end GlobalTheory.MuOfEps

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TensorBcrisFrobeniusValueEqSumCoordinatesStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix GlobalTheory.BKGal.XiFil
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorBcris_frobenius_value_eq_sum_coordinates : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (w : Vec K a ι) (hwS : ∀ τ j, w τ j ∈ invL l (S O K e)) (hw : P.xiExt w ∈ P.MMl) (hd : ∀ j, P.xi (fun _ => Pi.single j 1) ∈ P.MMl), toBcris t ϖ P ⟨P.xiExt w, hw⟩ = ∑ j, ϖ.iB t K (fun τ => ⟨w τ j, hwS τ j⟩) • toBcris t ϖ P ⟨P.xi (fun _ => Pi.single j 1), hd j⟩ := by
  first | exact @GlobalTheory.XiDecomp.toBcris_xiExt_eq_sum | exact GlobalTheory.XiDecomp.toBcris_xiExt_eq_sum | (intros; apply GlobalTheory.XiDecomp.toBcris_xiExt_eq_sum <;> assumption)
end

