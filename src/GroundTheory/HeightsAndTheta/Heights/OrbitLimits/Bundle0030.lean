import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsLiftBlockDatum
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionBounded
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0079
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0023
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0076
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0026
import GroundTheory.HeightsAndTheta.Heights.Intersections.PRFormula
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0025
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0017
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0019
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0018
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0022
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0028
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0021

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.LiftBlockSections
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

namespace LiftBlockSections

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem chartLat_smul_one (y : (Σ k, ι k) → Ω) (m : ℕ) (b : K → ℤ) :
    chartLat y (m • b) 1 = chartLat y b m := by
  ext s
  show (∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
      s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * (m • b) k)) ∈ chartRingZ y c) ↔
    (∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → s * ∏ k, y ⟨k, c k⟩ ^ (-((m : ℤ) * b k)) ∈ chartRingZ y c)
  simp only [Pi.smul_apply, nsmul_eq_mul, Nat.cast_one, one_mul]

theorem secM_le_chartLat [DecidableEq K] {r : ℕ} (y : (Σ k, ι k) → Ω) (v : Fin r → Ω) (b : K → ℤ)
    (hv : ∀ j, v j ∈ chartLat y b 1) (n : ℕ) :
    secM (addBlock y v) (blockDeg (none : Option K) n) ≤ chartLat y (n • b) 1 := by
  classical
  intro s hs
  have hle : Submodule.span ℤ {s | ∃ g : MRing (addIdx ι r), IsMultiHomog g (blockDeg (none : Option K) n) ∧
      aeval (addBlock y v) g = s} ≤ (chartLat y (n • b) 1).toIntSubmodule := by
    rw [Submodule.span_le]
    rintro _ ⟨g, hg, rfl⟩
    show aeval (addBlock y v) g ∈ chartLat y (n • b) 1
    rw [g.as_sum, map_sum]
    refine AddSubgroup.sum_mem _ fun m hm => ?_
    have hold : ∀ (k : K) (i : ι k), m ⟨some k, i⟩ = 0 := by
      intro k i
      have h := hg m hm (some k)
      simp only [blockDeg, reduceCtorEq, if_false] at h
      exact Finset.sum_eq_zero_iff.mp h i (Finset.mem_univ _)
    have htot : ∑ p ∈ m.support, m p = n := by
      rw [Finset.sum_subset (Finset.subset_univ _) (fun p _ hp => Finsupp.notMem_support_iff.mp hp),
        Fintype.sum_sigma, Fintype.sum_option]
      have h0 := hg m hm none
      simp only [blockDeg, if_true] at h0
      have h1 : ∑ k : K, ∑ i : addIdx ι r (some k), m ⟨some k, i⟩ = 0 :=
        Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun i _ => hold k i
      rw [h0, h1, add_zero]
    have hprod : m.prod (fun p e => addBlock y v p ^ e) ∈ chartLat y (n • b) 1 := by
      have h := LiftBirationalAmple.chartLat_prod (y := y) m.support (fun p => addBlock y v p ^ m p)
        (fun p => m p • b) (fun p _ => by
          rcases p with ⟨_ | k, i⟩
          · exact LiftBirationalAmple.chartLat_pow (hv i) _
          · simp only [hold k i, pow_zero, zero_smul]
            exact LiftBirationalAmple.chartLat_one_mem)
      rwa [← Finset.sum_smul, htot] at h
    rw [aeval_monomial, algebraMap_int_eq, eq_intCast, ← zsmul_eq_mul]
    exact AddSubgroup.zsmul_mem _ hprod _
  exact hle hs

def oldEmb (r : ℕ) : (Σ k, ι k) → (Σ k, addIdx ι r k) := fun p => ⟨some p.1, p.2⟩

theorem oldEmb_injective (r : ℕ) : Function.Injective (oldEmb (ι := ι) r) := by
  rintro ⟨k, i⟩ ⟨k', i'⟩ h
  cases h
  rfl

theorem homog_rename_old (r : ℕ) {g : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d) :
    IsMultiHomog (rename (oldEmb (ι := ι) r) g) (fun o => Option.elim o 0 d) := by
  classical
  intro m' hm' o
  rw [support_rename_of_injective (oldEmb_injective r)] at hm'
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hm'
  rcases o with _ | k
  · refine Finset.sum_eq_zero fun j _ => Finsupp.mapDomain_of_notMem_range _ _ ?_
    rintro ⟨p, hp⟩
    exact Option.some_ne_none _ (congrArg Sigma.fst hp)
  · have h := hg m hm k
    simp only [Option.elim_some]
    rw [← h]
    exact Finset.sum_congr rfl fun i _ => Finsupp.mapDomain_apply (oldEmb_injective r) m ⟨k, i⟩

theorem addBlock_comp_oldEmb {r : ℕ} (y : (Σ k, ι k) → Ω) (v : Fin r → Ω) : addBlock y v ∘ oldEmb r = y := by
  funext p
  rfl

theorem eval_rename_old {r : ℕ} (z : (Σ k, addIdx ι r k) → ℂ) (g : MRing ι) :
    eval z (map (Int.castRingHom ℂ) (rename (oldEmb r) g)) = eval (basePart₂ z) (map (Int.castRingHom ℂ) g) := by
  rw [map_rename, eval_rename]
  rfl

theorem isSmallH_of_lift [DecidableEq K] {r : ℕ} {y : (Σ k, ι k) → Ω} {v : Fin r → Ω} {N : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {a : ℕ}
    {B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine (addIdx ι r)} (hB : B.a = unitDeg (none : Option K))
    (hv : ∀ j, v j ∈ chartLat y N.a a)
    (hmet : ∀ z ∈ mcPts (mCoordIdeal (addBlock y v)), ∀ j,
      secNormAt y N a (v j) (basePart₂ z) * B.h z = ‖z ⟨none, j⟩‖)
    (hlift : ∀ w ∈ mcPts (mCoordIdeal y), ∃ z ∈ mcPts (mCoordIdeal (addBlock y v)), basePart₂ z = w)
    {n : ℕ} {s : Ω} (hs : IsSmallH (mCoordIdeal (addBlock y v)) (addBlock y v) B n s) :
    IsSmallH (mCoordIdeal y) y N (a * n) s := by
  classical
  intro dg dh g h w hg hh hdeg he hw
  obtain ⟨z, hz, rfl⟩ := hlift w hw
  obtain ⟨j, hj⟩ := hz.1 none
  choose c hc using hw.1
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k h0 => hc k (by
    have := SectionBounded.vanish hw (SectionBounded.homog_X (ι := ι) ⟨k, c k⟩) (by rw [aeval_X]; exact h0)
    simpa using this)

  obtain ⟨δ, e, he_h, he_v⟩ := SectionBounded.exists_form_of_mem_chartRingZ y c hyc (hv j c hyc)
  set t : K → ℤ := fun k => (a : ℤ) * N.a k with ht
  set β : K → ℕ := fun k => δ k + (-t k).toNat with hβ
  set γ : K → ℕ := fun k => (t k).toNat with hγ
  set q₁ := SectionBounded.chartMon c β with hq₁
  set r₁ := e * SectionBounded.chartMon c γ with hr₁
  have hq₁h : IsMultiHomog q₁ β := SectionBounded.homog_chartMon c β
  have hr₁h : IsMultiHomog r₁ (δ + γ) := SectionBounded.homog_mul he_h (SectionBounded.homog_chartMon c γ)
  have hdeg₁ : ∀ k, (((δ + γ) k : ℕ) : ℤ) = β k + t k := by
    intro k
    simp only [Pi.add_apply, hβ, hγ]
    omega
  have hval₁ : aeval y r₁ = v j * aeval y q₁ := by
    rw [hr₁, hq₁, map_mul, SectionBounded.aeval_chartMon, SectionBounded.aeval_chartMon, he_v]
    have hk : ∀ k, y ⟨k, c k⟩ ^ β k =
        y ⟨k, c k⟩ ^ (-((a : ℤ) * N.a k)) * y ⟨k, c k⟩ ^ δ k * y ⟨k, c k⟩ ^ γ k := by
      intro k
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hyc k), ← zpow_add₀ (hyc k)]
      congr 1
      simp only [hβ, hγ, ht]
      omega
    rw [Finset.prod_congr rfl fun k _ => hk k, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    ring

  set w := basePart₂ z with hw_def
  set σ := secNormAt y N a (v j) w with hσ
  have hBpos : 0 < B.h z := B.pos z hz.1
  have hZ : 0 < ‖z ⟨none, j⟩‖ := norm_pos_iff.mpr hj
  have hσB : σ * B.h z = ‖z ⟨none, j⟩‖ := hmet z hz j
  have hσpos : 0 < σ := by
    by_contra hle
    push Not at hle
    nlinarith
  have hQ : 0 < ‖eval w (map (Int.castRingHom ℂ) q₁)‖ := by
    rw [hq₁, SectionBounded.eval_chartMon]
    exact norm_pos_iff.mpr (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k))
  have hM : 0 < N.h w ^ a := pow_pos (N.pos w hw.1) _
  have hR : ‖eval w (map (Int.castRingHom ℂ) r₁)‖ ≤ σ * (‖eval w (map (Int.castRingHom ℂ) q₁)‖ * N.h w ^ a) := by
    have hS : {c' : ℝ | 0 ≤ c' ∧ IsBoundedAt y N a c' (v j) w}.Nonempty := by
      by_contra hne
      rw [Set.not_nonempty_iff_eq_empty] at hne
      have : σ = 0 := by rw [hσ, secNormAt, hne, Real.sInf_empty]
      linarith
    rw [← div_le_iff₀ (mul_pos hQ hM)]
    refine le_csInf hS fun c' ⟨_, hc'⟩ => ?_
    rw [div_le_iff₀ (mul_pos hQ hM)]
    have := hc' (δ + γ) β r₁ q₁ hr₁h hq₁h (fun k => hdeg₁ k) hval₁
    linarith

  set G := rename (oldEmb r) g * rename (oldEmb r) (q₁ ^ n) * (X ⟨none, j⟩ : MRing (addIdx ι r)) ^ n with hG
  set H := rename (oldEmb r) h * rename (oldEmb r) (r₁ ^ n) with hH
  set dG : Option K → ℕ := (fun o => Option.elim o 0 dg) + (fun o => Option.elim o 0 (n • β)) +
      n • Pi.single (none : Option K) 1 with hdG
  set dH : Option K → ℕ := (fun o => Option.elim o 0 dh) + (fun o => Option.elim o 0 (n • (δ + γ))) with hdH
  have hGh : IsMultiHomog G dG :=
    SectionBounded.homog_mul (SectionBounded.homog_mul (homog_rename_old r hg)
      (homog_rename_old r (SectionBounded.homog_pow hq₁h n)))
      (SectionBounded.homog_pow (SectionBounded.homog_X (ι := addIdx ι r) ⟨none, j⟩) n)
  have hHh : IsMultiHomog H dH :=
    SectionBounded.homog_mul (homog_rename_old r hh) (homog_rename_old r (SectionBounded.homog_pow hr₁h n))
  have hdegGH : ∀ o, (dG o : ℤ) = dH o + n * B.a o := by
    intro o
    rw [hB, hdG, hdH]
    rcases o with _ | k
    · simp [unitDeg]
    · have h1 := hdeg k
      have h2 := hdeg₁ k
      simp only [Pi.add_apply, Pi.smul_apply, Option.elim_some, smul_eq_mul, Pi.single_apply, reduceCtorEq,
        if_false, mul_zero, add_zero, unitDeg] at h2 ⊢
      push_cast at h1 h2 ⊢
      simp only [ht] at h2
      linear_combination h1 - (n : ℤ) * h2
  have hvalGH : aeval (addBlock y v) G = s * aeval (addBlock y v) H := by
    have e1 : aeval (addBlock y v) G = aeval y g * aeval y q₁ ^ n * v j ^ n := by
      simp only [hG, map_mul, map_pow, aeval_rename, addBlock_comp_oldEmb, aeval_X]
      rfl
    have e2 : aeval (addBlock y v) H = aeval y h * aeval y r₁ ^ n := by
      simp only [hH, map_mul, map_pow, aeval_rename, addBlock_comp_oldEmb]
    rw [e1, e2, hval₁, he]
    ring
  have hsm := hs _ _ G H z hGh hHh hdegGH hvalGH hz
  simp only [hG, hH, map_mul, map_pow, eval_rename_old, map_X, eval_X, norm_mul, norm_pow] at hsm
  rw [← hw_def] at hsm

  set Gw := ‖eval w (map (Int.castRingHom ℂ) g)‖
  set Hw := ‖eval w (map (Int.castRingHom ℂ) h)‖
  set Q := ‖eval w (map (Int.castRingHom ℂ) q₁)‖
  set R := ‖eval w (map (Int.castRingHom ℂ) r₁)‖
  set M := N.h w ^ a
  have hb := B.h z
  have h1 : Gw * (Q * σ) ^ n * B.h z ^ n ≤ Hw * R ^ n * B.h z ^ n := by
    have e1 : Gw * (Q * σ) ^ n * B.h z ^ n = Gw * Q ^ n * ‖z ⟨none, j⟩‖ ^ n := by
      rw [← hσB]
      ring
    rw [e1]
    exact hsm
  have h2 : Gw * (Q * σ) ^ n ≤ Hw * R ^ n := le_of_mul_le_mul_right h1 (pow_pos hBpos n)
  have h3 : R ^ n ≤ (σ * (Q * M)) ^ n := pow_le_pow_left₀ (norm_nonneg _) hR n
  have h4 : Gw * (Q * σ) ^ n ≤ Hw * M ^ n * (Q * σ) ^ n := by
    calc Gw * (Q * σ) ^ n ≤ Hw * R ^ n := h2
      _ ≤ Hw * (σ * (Q * M)) ^ n := mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
      _ = Hw * M ^ n * (Q * σ) ^ n := by ring
  have h5 := le_of_mul_le_mul_right h4 (pow_pos (mul_pos hQ hσpos) n)
  rw [pow_mul]
  exact h5

theorem smallSectionCount_mono {P P' : ℕ → Ω → Prop} {La La' : ℕ → AddSubgroup Ω} {τ τ' : ℕ}
    (h : ∀ s ∈ La τ, P τ s → s ∈ La' τ' ∧ P' τ' s) (hfin : {s : La' τ' | P' τ' (s : Ω)}.Finite) :
    smallSectionCount P La τ ≤ smallSectionCount P' La' τ' := by
  unfold smallSectionCount
  have : Finite {s : La' τ' // P' τ' (s : Ω)} := hfin.to_subtype
  have hcard : Nat.card {s : La τ // P τ (s : Ω)} ≤ Nat.card {s : La' τ' // P' τ' (s : Ω)} :=
    Nat.card_le_card_of_injective (fun s => ⟨⟨s.1.1, (h s.1.1 s.1.2 s.2).1⟩, (h s.1.1 s.1.2 s.2).2⟩) fun s t hst => by
      simp only [Subtype.mk.injEq] at hst
      exact Subtype.ext (Subtype.ext hst)
  rcases Nat.eq_zero_or_pos (Nat.card {s : La τ // P τ (s : Ω)}) with h0 | hpos
  · rw [h0, Nat.cast_zero, Real.log_zero]
    exact Real.log_natCast_nonneg _
  · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hcard)

end LiftBlockSections

end

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveFormNonvanishing
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace CurveFormNonvanishing

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem eval₂_multiHomog {L : Type*} [Field L] (f : ℤ →+* L) {g : MRing ι} {d : K → ℕ}
    (hg : IsMultiHomog g d) (c : ∀ k, ι k) (w : (Σ k, ι k) → L) (hw : ∀ k, w ⟨k, c k⟩ ≠ 0) :
    eval₂ f w g = (∏ k, w ⟨k, c k⟩ ^ d k) * eval₂ f (fun p ↦ w p / w ⟨p.1, c p.1⟩) g := by
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  rw [eval₂_sum, eval₂_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  rw [eval₂_monomial, eval₂_monomial, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _),
    Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _)]
  have h1 : ∏ p, (w p / w ⟨p.1, c p.1⟩) ^ m p = (∏ p, w p ^ m p) / ∏ k, w ⟨k, c k⟩ ^ d k := by
    simp only [div_pow, Finset.prod_div_distrib]
    congr 1
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    rw [← hg m hm k]
    exact Finset.prod_pow_eq_pow_sum Finset.univ (fun i ↦ m ⟨k, i⟩) (w ⟨k, c k⟩)
  have h3 : ∏ k, w ⟨k, c k⟩ ^ d k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hw k)
  rw [h1]
  field_simp

end CurveFormNonvanishing

theorem CurveFormNonvanishing.proof : CurveFormNonvanishing.Statement := by
  intro K _ ι _ Ω _ y d g hP hg hgy z hz
  have := HilbertSamuel.BigIffGenDeg.charZero_of_isArithVar hP
  choose c hc using HilbertSamuel.BigIffGenDeg.coord_ne_zero_of_isArithVar hP
  obtain ⟨φ, hφ, hzc⟩ := IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.exists_ptOf hP hc hz

  have hF : eval₂ (Int.castRingHom _) (IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.ratioF y c) g ≠ 0 := by
    intro h0
    have h := congrArg (algebraMap (blockFnField y) Ω) h0
    rw [map_zero, eval₂_comp_left] at h
    have hy := CurveFormNonvanishing.eval₂_multiHomog (Int.castRingHom Ω) hg c y hc
    have e : eval₂ ((algebraMap (blockFnField y) Ω).comp (Int.castRingHom _))
        (algebraMap _ Ω ∘ IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.ratioF y c) g =
        eval₂ (Int.castRingHom Ω) (fun p ↦ y p / y ⟨p.1, c p.1⟩) g := by
      congr 1
    rw [e] at h
    rw [h, mul_zero] at hy
    exact hgy (by rw [aeval_def, algebraMap_int_eq, hy])

  have hpt : eval₂ (Int.castRingHom ℂ) (IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.ptOf y c φ) g ≠ 0 := by
    have h := (map_ne_zero_iff (φ : blockFnField y →+* ℂ) φ.toRingHom.injective).mpr hF
    rw [eval₂_comp_left] at h
    convert h using 2
    · exact RingHom.ext_int _ _
    · rfl
  rw [eval_map, CurveFormNonvanishing.eval₂_multiHomog (Int.castRingHom ℂ) hg c z hzc]
  refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hzc k)) ?_
  have e : (fun p ↦ z p / z ⟨p.1, c p.1⟩) = IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.ptOf y c φ := by
    rw [hφ]
    funext p
    rw [div_eq_inv_mul]
  rw [e]
  exact hpt

end

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PLelongChartLimit
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial Filter Topology
open scoped ContDiff
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar IsSectionOn ptsIntegral pot segre mcPts
  isOpen_blockNonzero)
open GroundTheory.Heights₂.Heights (segreChartSet segreChartComponents mem_segreChartComponents chartLift
  contDiff_chartLift chartLift_blockNonzero segre_chartLift chart_coord_eq_one)

theorem LelongChartLimit.proof (hInt : SegreChartIntegral.Statement) (hDim : SegreChartDim.Statement)
    (hNot : ChartSectionNotMem.Statement) (hLel : LelongPolyLimit.Statement)
    (hDiv : ChartDivisorCompare.Statement) : LelongChartLimit.Statement := by
  classical
  intro K _ _ ι _ P n L A s g i δ hP hL hA hs hg hδ hsupp
  obtain ⟨a, ha, hsa, -⟩ := id hs
  let σ := (Fintype.equivFin ((k : K) → ι k)).symm
  let lam := chartLift σ i
  let χ : ContDiffBump (0 : Fin (Fintype.card ((k : K) → ι k)) → ℂ) :=
    ⟨1 / δ + 1, 1 / δ + 2, by positivity, by linarith⟩
  let G := fun x => χ x * g (lam x)
  let Φ : Fin n → _ := fun j x => pot L j (lam x)
  let kk := fun x => A.h (lam x)
  let F := fun (ε : ℝ) x => Real.log (‖eval x (chartSection σ i s)‖ ^ 2 + ε * kk x ^ 2) / 2
  have hlam : ContDiff ℝ ∞ lam := contDiff_chartLift σ i
  let Ω := lam ⁻¹' {z | ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0}
  have hΩ : IsOpen Ω := isOpen_blockNonzero.preimage hlam.continuous
  have hsm : ∀ f : ((Σ k, ι k) → ℂ) → ℝ, ContDiffOn ℝ ∞ f {z | ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0} →
      ContDiffOn ℝ ∞ (f ∘ lam) Ω := fun f hf => hf.comp hlam.contDiffOn fun _ hx => hx
  have hpot : ∀ j, ContDiffOn ℝ ∞ (pot L j) {z | ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0} := fun j =>
    (hL j).log fun z hz => ((L j).pos z hz).ne'
  have hxΩ : ∀ x ∈ segreChartSet P σ i, x ∈ Ω := by
    rintro _ ⟨z, -, hzi, rfl⟩
    exact chartLift_blockNonzero σ i (by simp [σ, hzi])

  have key : ∀ x ∈ segreChartSet P σ i, G =ᶠ[𝓝 x] g ∘ lam := by
    rintro _ ⟨z, -, hzi, rfl⟩
    by_cases hr : ‖fun a => segre z (σ a)‖ < 1 / δ + 1
    · filter_upwards [Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hr)] with y hy
      simp [G, χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)]
    · have hle : ‖fun a => segre z (σ a)‖ ≤ ‖segre z‖ :=
        (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun a => norm_le_pi_norm (segre z) (σ a)
      have hcont : Continuous fun y => segre (lam y) :=
        continuous_pi fun i' => continuous_finsetProd _ fun k _ =>
          (continuous_apply (⟨k, i' k⟩ : Σ k, ι k)).comp hlam.continuous
      have hO : IsOpen {y | ‖segre (lam y) i‖ < δ * ‖segre (lam y)‖} :=
        isOpen_lt ((continuous_apply i).comp hcont).norm (continuous_const.mul hcont.norm)
      have hx : ‖segre (lam fun a => segre z (σ a)) i‖ < δ * ‖segre (lam fun a => segre z (σ a))‖ := by
        rw [segre_chartLift σ i z hzi, hzi, norm_one]
        have h1 : 1 / δ < ‖segre z‖ := by linarith
        calc (1 : ℝ) = δ * (1 / δ) := by field_simp
          _ < δ * ‖segre z‖ := mul_lt_mul_of_pos_left h1 hδ
      filter_upwards [hO.mem_nhds hx] with y hy
      simp [G, hsupp _ hy]
  have hJ : ∀ J ∈ segreChartComponents P σ i, ComplexSets.zeroSet J ⊆ Ω := fun J hJ x hx =>
    chartLift_blockNonzero σ i (chart_coord_eq_one hJ hx)

  have hlim := tendsto_finsetSum (segreChartComponents P σ i) fun J hJs =>
    hLel _ n J (chartSection σ i s) G kk Φ (mem_segreChartComponents.1 hJs).1.1
      (hDim K ι P (n + 1) _ σ i hP J hJs) (hNot K ι P (n + 1) _ σ i A s hP hs J hJs)
      ⟨Ω, hΩ, hJ J hJs, (χ.contDiff.contDiffOn).mul (hsm g hg.1)⟩ χ.hasCompactSupport.mul_right
      (fun j => ⟨Ω, hΩ, hJ J hJs, hsm _ (hpot j)⟩) ⟨Ω, hΩ, hJ J hJs, hsm _ hA⟩
      fun x hx => A.pos _ (hJ J hJs hx)
  rw [hDiv K ι P n _ σ i L A s g δ G Φ hP hL hs hg hδ hsupp
    fun x hx => ⟨key x hx, fun j => EventuallyEq.rfl⟩] at hlim
  refine hlim.congr' (eventually_nhdsWithin_of_forall fun ε (hε : 0 < ε) => ?_)

  set M := (regLine A s ε ha hsa).tensor A
  have hML : ∀ j, IsSmoothHerm ((Fin.cons M L : Fin (n + 1) → HermLine ι) j) :=
    fun j => Fin.cases ((isSmoothHerm_regLine hA hε ha hsa).mul hA) (fun i => hL i) j
  have hcongr : ptsIntegral P
      (Fin.cons (fun z => Real.log (‖eval z (map (Int.castRingHom ℂ) s)‖ ^ 2 + ε * A.h z ^ 2) / 2)
        (pot L)) g = ptsIntegral P (pot (Fin.cons M L)) g := by
    rw [Inter.PtsAddFirst.pot_cons]
    refine Inter.DiagRAux.ptsIntegral_congr_mcPts P (fun j => ?_) (fun _ _ => rfl)
    refine Fin.cases ?_ (fun i => ?_) j
    · intro z hz
      simp only [Fin.cons_zero]
      exact (log_regLine_tensor A s hε ha hsa z hz.1).symm
    · intro z _
      simp only [Fin.cons_succ]
  beta_reduce
  rw [hcongr]
  refine (hInt K ι P n _ σ i (Fin.cons M L) g δ G (Matrix.vecCons (F ε) Φ) hP hML hg hδ (Or.inl hsupp)
    fun x hx => ⟨key x hx, fun j => ?_⟩).symm
  refine Fin.cases ?_ (fun j => EventuallyEq.rfl) j
  filter_upwards [hΩ.mem_nhds (hxΩ x hx)] with y hy
  simp only [Matrix.cons_val_zero, Function.comp_apply, Inter.PtsAddFirst.pot_cons, Fin.cons_zero, F, kk,
    eval_chartSection]
  exact (log_regLine_tensor A s hε ha hsa (lam y) hy).symm

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StChartSheetNoRatNull
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix

def ChartSheetNoRatNull.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (p : Fin d → MvPolynomial (Fin n) ℂ) (q : MvPolynomial (Fin n) ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → ComplexSets.IsFiniteProjection J A →
    q ∉ J → (∀ y, (RatChart.ratFibre J p q y).Finite) →
      volume ((fun x => A *ᵥ x) ''
        {x | x ∈ ComplexSets.zeroSet J ∧ (∃ s, IsSheetAt J A x s) ∧
          ¬ ∃ s', RatChart.IsRatSheetAt J p q x s'}) = 0

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StGoodChartZeroSet
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomogIdeal PBlk)
open ComplexSets

def GoodChartZeroSet.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e m : ℕ)
    (σ : Fin m ≃ ((k : K) → ι k)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsMultiHomogIdeal P → zeroSet (projChartIdeal P σ Ψ) = projChartSet P σ Ψ

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StPtsChartDim
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def PtsChartDim.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (i : (k : K) → ι k),
    IsArithVar P (e + 1) → ∀ J ∈ (PtsSegreChart.ideal P i).minimalPrimes,
      ringKrullDim (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ ⧸ J) = (e : ℕ)

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StPtsChartMapFinite
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def PtsChartMapFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (i : (k : K) → ι k) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsArithVar P (e + 1) → IsGoodProj P Ψ → ∀ J ∈ (PtsSegreChart.ideal P i).minimalPrimes,
      PtsSegreChart.chartDen Ψ ∉ J ∧
        ∀ y, (RatChart.ratFibre J (PtsSegreChart.chartNum Ψ) (PtsSegreChart.chartDen Ψ) y).Finite

end GroundTheory.Heights₂.Heights
end
end

