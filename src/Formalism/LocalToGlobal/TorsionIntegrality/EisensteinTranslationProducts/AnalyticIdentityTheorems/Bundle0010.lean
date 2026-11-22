import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.HkRowIntegral
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EisensteinS2LimitFormula
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.Bundle0008
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.TaylorWp
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.Bundle0009
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.WeierstrassNumeratorDenominator

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.EisensteinS2LimitFormulaOfHkLimit
section
noncomputable section
open scoped BigOperators ComplexConjugate
open Filter Topology

namespace Formalism.L2.Th1.F

namespace Hk4

lemma hk_zero (w : ℂ) : hk 0 w = 1 / w ^ 2 := by simp [hk]

def cellOff (τ : ℂ) (s : ℝ) (p : ℤ × ℤ) : ℂ := if p.2 = 0 then 0 else hkCell τ s p

lemma cellOff_norm_le {τ : ℂ} {b : ℤ × ℤ → ℝ}
    (hbd : ∀ (s : ℝ) (p : ℤ × ℤ), 0 ≤ s → s ≤ 1 → p.2 ≠ 0 → ‖hkCell τ s p‖ ≤ b p)
    {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) (p : ℤ × ℤ) : ‖cellOff τ s p‖ ≤ |b p| := by
  unfold cellOff
  split_ifs with hp
  · simp
  · exact (hbd s p h0 h1 hp).trans (le_abs_self _)

lemma split (h2 : HkRowIntegral) {τ : ℂ} (hτ : τ.im ≠ 0) {b : ℤ × ℤ → ℝ} (hb : Summable b)
    (hbd : ∀ (s : ℝ) (p : ℤ × ℤ), 0 ≤ s → s ≤ 1 → p.2 ≠ 0 → ‖hkCell τ s p‖ ≤ b p)
    {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1)
    (hI : Summable (fun n : ℤ => if n = 0 then 0 else hkInt τ s n)) :
    ∑' n : ℤ, ∑' m : ℤ, hk s ((m : ℂ) + (n : ℂ) * τ)
      = ∑' m : ℤ, hk s (m : ℂ) + ∑' p : ℤ × ℤ, cellOff τ s p
        + ∑' n : ℤ, (if n = 0 then 0 else hkInt τ s n) := by
  have hC : Summable (cellOff τ s) :=
    Summable.of_norm_bounded hb.abs (cellOff_norm_le hbd h0 h1)
  have hC' : Summable (fun q : ℤ × ℤ => cellOff τ s (q.2, q.1)) :=
    (Equiv.prodComm ℤ ℤ).summable_iff.mpr hC
  have hCsum : ∑' p : ℤ × ℤ, cellOff τ s p = ∑' n : ℤ, ∑' m : ℤ, cellOff τ s (m, n) := by
    rw [← (Equiv.prodComm ℤ ℤ).tsum_eq (cellOff τ s)]
    exact hC'.tsum_prod
  have hG : Summable (fun n : ℤ => ∑' m : ℤ, cellOff τ s (m, n)) := hC'.prod
  have hrow : ∀ n : ℤ, ∑' m : ℤ, hk s ((m : ℂ) + (n : ℂ) * τ)
      = (if n = 0 then ∑' m : ℤ, hk s (m : ℂ) else 0) + ∑' m : ℤ, cellOff τ s (m, n)
        + (if n = 0 then 0 else hkInt τ s n) := by
    intro n
    by_cases hn : n = 0
    · subst hn
      simp [cellOff]
    · have hs1 : Summable (fun m : ℤ => cellOff τ s (m, n)) := hC'.prod_factor n
      have hs2 := (h2 τ s n hτ h0 hn).2
      have := hs1.hasSum.add hs2
      have he : (fun m : ℤ => cellOff τ s (m, n)
          + ∫ x in (0 : ℝ)..1, hk s ((m : ℂ) + (x : ℂ) + (n : ℂ) * τ))
          = fun m : ℤ => hk s ((m : ℂ) + (n : ℂ) * τ) := by
        funext m
        simp [cellOff, hkCell, hn]
      rw [he] at this
      rw [this.tsum_eq]
      simp [hn]
  have hR : Summable (fun n : ℤ => if n = 0 then ∑' m : ℤ, hk s (m : ℂ) else 0) :=
    (hasSum_ite_eq (0 : ℤ) _).summable
  rw [tsum_congr hrow, (hR.add hG).tsum_add hI, hR.tsum_add hG, tsum_ite_eq, hCsum]

end Hk4

open Hk4 in
theorem hkLimit_of (h1 : HkSummable) (h2 : HkRowIntegral) (h3 : HkCellBound) (h4 : HkCellCont)
    (h5 : HkIntZero) (h6 : HkRowZero) (h7 : HkIntLimit) : HkLimit := by
  intro τ hτ
  obtain ⟨b, hb, hbd⟩ := h3 τ hτ
  have hmem : Set.Ioc (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := Ioc_mem_nhdsGT one_pos

  have hcell : Tendsto (fun s : ℝ => ∑' p : ℤ × ℤ, cellOff τ s p) (𝓝[>] 0)
      (𝓝 (∑' p : ℤ × ℤ, cellOff τ 0 p)) := by
    refine tendsto_tsum_of_dominated_convergence hb.abs ?_ ?_
    · intro p
      by_cases hp : p.2 = 0
      · simp [cellOff, hp]
      · simpa [cellOff, hp] using h4 τ p hτ hp
    · filter_upwards [hmem] with s hs p
      exact cellOff_norm_le hbd hs.1.le hs.2 p

  have hI0 : (fun n : ℤ => if n = 0 then (0 : ℂ) else hkInt τ 0 n) = fun _ => 0 := by
    funext n
    by_cases hn : n = 0
    · simp [hn]
    · simp [hn, h5 τ n hτ hn]
  have hzero := split h2 hτ hb hbd le_rfl zero_le_one (by rw [hI0]; exact summable_zero)
  rw [hI0, tsum_zero, add_zero] at hzero
  simp only [hk_zero] at hzero
  rw [hzero]
  have hlim := (h6.add hcell).add (h7 τ hτ).2
  rw [← sub_eq_add_neg] at hlim
  refine hlim.congr' ?_
  filter_upwards [hmem] with s hs
  rw [← split h2 hτ hb hbd hs.1.le hs.2 ((h7 τ hτ).1 s hs.1)]
  have hS := h1 τ s hτ hs.1
  have hS' : Summable (fun q : ℤ × ℤ => hk s ((q.2 : ℂ) + (q.1 : ℂ) * τ)) :=
    (Equiv.prodComm ℤ ℤ).summable_iff.mpr hS
  rw [← (Equiv.prodComm ℤ ℤ).tsum_eq (fun p : ℤ × ℤ => hk s ((p.1 : ℂ) + (p.2 : ℂ) * τ))]
  exact hS'.tsum_prod.symm

namespace Hk4

lemma hk_mul (s : ℝ) (u w : ℂ) :
    hk s (u * w) = (u ^ 2)⁻¹ * ((‖u‖ ^ (-(2 * s)) : ℝ) : ℂ) * hk s w := by
  unfold hk
  rw [norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _), mul_pow, mul_inv]
  push_cast
  ring

end Hk4

open Hk4 PeriodAreaSignLemmas in
theorem eisensteinS2LimitFormula_of_hkLimit (h : HkLimit) : EisensteinS2LimitFormula := by
  intro L
  set u := L.ω₁ with hu_def
  have hu : u ≠ 0 := ω₁_ne_zero L
  set τ := L.ω₂ / u with hτ_def
  have hN : 0 < Complex.normSq u := Complex.normSq_pos.mpr hu
  have him : τ.im = det L / Complex.normSq u := div_im L
  have hτ : τ.im ≠ 0 := by
    rw [him]; exact div_ne_zero (det_ne_zero L) hN.ne'
  have hlin : ∀ m n : ℤ, (m : ℂ) * u + (n : ℂ) * L.ω₂ = u * ((m : ℂ) + (n : ℂ) * τ) := by
    intro m n
    rw [hτ_def]; field_simp
  have hsum : ∀ s : ℝ, ∑' ω : L.lattice, ((ω : ℂ) ^ 2)⁻¹ * ((‖(ω : ℂ)‖ ^ (-(2 * s)) : ℝ) : ℂ)
      = (u ^ 2)⁻¹ * ((‖u‖ ^ (-(2 * s)) : ℝ) : ℂ) * ∑' p : ℤ × ℤ, hk s ((p.1 : ℂ) + (p.2 : ℂ) * τ) := by
    intro s
    rw [← L.latticeEquivProd.symm.toEquiv.tsum_eq, ← tsum_mul_left]
    refine tsum_congr fun p => ?_
    rw [← hk_mul, ← hlin]
    simp only [LinearEquiv.coe_toEquiv, L.latticeEquiv_symm_apply, hk]
    rfl
  simp only [hsum]
  have hc : Tendsto (fun s : ℝ => (u ^ 2)⁻¹ * ((‖u‖ ^ (-(2 * s)) : ℝ) : ℂ)) (𝓝[>] 0)
      (𝓝 ((u ^ 2)⁻¹ * 1)) := by
    refine Tendsto.const_mul _ ?_
    have h1 : ContinuousAt (fun s : ℝ => ‖u‖ ^ (-(2 * s))) 0 := by
      have : ContinuousAt (fun x : ℝ => ‖u‖ ^ x) (-(2 * (0 : ℝ))) :=
        Real.continuousAt_const_rpow (norm_ne_zero_iff.mpr hu)
      exact ContinuousAt.comp (f := fun s : ℝ => -(2 * s)) this (by fun_prop)
    have h2 : Tendsto (fun s : ℝ => ‖u‖ ^ (-(2 * s))) (𝓝[>] 0) (𝓝 1) := by
      have := h1.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
      simpa using this
    have := (Complex.continuous_ofReal.tendsto 1).comp h2
    simpa [Function.comp_def] using this
  have hmain := hc.mul (h τ hτ)
  convert hmain using 2

  have hE := (etaEisenstein L).1
  have hSp := etaSplit L u
  have hT : ∑' n : ℤ, ∑' m : ℤ, 1 / ((m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂) ^ 2
      = (u ^ 2)⁻¹ * ∑' n : ℤ, ∑' m : ℤ, 1 / ((m : ℂ) + (n : ℂ) * τ) ^ 2 := by
    simp_rw [← tsum_mul_left]
    refine tsum_congr fun n => tsum_congr fun m => ?_
    rw [hlin, mul_pow]
    field_simp
  rw [hT, ← hu_def] at hE
  have hA : (area L : ℂ) ≠ 0 := by exact_mod_cast (area_pos L).ne'
  have habs : |τ.im| = area L / Complex.normSq u := by
    rw [him, abs_div, abs_of_pos hN, area_eq]
  have hNc : ((Complex.normSq u : ℝ) : ℂ) = u * conj u := (Complex.mul_conj u).symm
  have hcu : conj u ≠ 0 := by simpa using hu
  rw [habs]
  push_cast
  rw [hNc]
  rw [hE] at hSp
  have hs : s2 L = (u * ((u ^ 2)⁻¹ * ∑' n : ℤ, ∑' m : ℤ, 1 / ((m : ℂ) + (n : ℂ) * τ) ^ 2)
      - ((Real.pi : ℂ) / (area L : ℂ)) * conj u) / u := by
    rw [hSp]; field_simp; ring
  rw [hs]
  generalize (∑' n : ℤ, ∑' m : ℤ, 1 / ((m : ℂ) + (n : ℂ) * τ) ^ 2) = T
  field_simp

end Formalism.L2.Th1.F
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.GoodModelLatticeGen
section
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism.L2.Th1.CM (wpNum wpDen uSer IsGoodModel)

namespace Formalism.L2.Th1.F

open PowerSeries TaylorWp

namespace USer

def num (L : PeriodPair) (z : ℂ) : ℂ := 1 + z ^ 2 * L.weierstrassPExcept 0 z

def den (L : PeriodPair) (z : ℂ) : ℂ := 1 + -(1 / 2) * z ^ 3 * deriv (L.weierstrassPExcept 0) z

theorem T_num (hr : TaylorRing) (L : PeriodPair) : T (num L) (1 + X ^ 2 * pSeries L) := by
  obtain ⟨hadd, hC, hX, -⟩ := hr
  have hP := TaylorSigmaUniqueness.analyticAt_pExcept L
  have hz : AnalyticAt ℂ (fun z : ℂ => z) 0 := analyticAt_id
  have hz2 : AnalyticAt ℂ (fun z : ℂ => z * z) 0 := hz.mul hz
  have hprod : AnalyticAt ℂ (fun z => z * z * L.weierstrassPExcept 0 z) 0 := hz2.mul hP
  have e : num L = fun z => (fun _ : ℂ => (1 : ℂ)) z + (fun z => z * z * L.weierstrassPExcept 0 z) z := by
    funext z
    simp only [num]
    ring
  refine ⟨by rw [e]; exact analyticAt_const.add hprod, ?_⟩
  have h1 : taylor0 (num L) = taylor0 (fun _ : ℂ => (1 : ℂ)) +
      taylor0 (fun z => z * z * L.weierstrassPExcept 0 z) := by
    rw [e]
    exact (hadd _ _ analyticAt_const hprod).1
  have h2 : taylor0 (fun z => z * z * L.weierstrassPExcept 0 z) =
      taylor0 (fun z : ℂ => z * z) * taylor0 (L.weierstrassPExcept 0) :=
    (hadd (fun z : ℂ => z * z) (L.weierstrassPExcept 0) hz2 hP).2
  have h3 : taylor0 (fun z : ℂ => z * z) = taylor0 (fun z : ℂ => z) * taylor0 (fun z : ℂ => z) :=
    (hadd (fun z : ℂ => z) (fun z : ℂ => z) hz hz).2
  rw [h1, h2, h3, hC, hX, map_one, sq]
  rfl

theorem T_den (hr : TaylorRing) (hd : TaylorDeriv) (L : PeriodPair) :
    T (den L) (1 - C (1 / 2 : ℂ) * X ^ 3 * derivative ℂ (pSeries L)) := by
  obtain ⟨hadd, hC, hX, -⟩ := hr
  have hP := TaylorSigmaUniqueness.analyticAt_pExcept L
  have hPd : AnalyticAt ℂ (deriv (L.weierstrassPExcept 0)) 0 := hP.deriv
  have hz : AnalyticAt ℂ (fun z : ℂ => z) 0 := analyticAt_id
  have hz2 : AnalyticAt ℂ (fun z : ℂ => z * z) 0 := hz.mul hz
  have hz3 : AnalyticAt ℂ (fun z : ℂ => z * z * z) 0 := hz2.mul hz
  have hc3 : AnalyticAt ℂ (fun z : ℂ => -(1 / 2 : ℂ) * (z * z * z)) 0 := analyticAt_const.mul hz3
  have hprod : AnalyticAt ℂ (fun z => -(1 / 2 : ℂ) * (z * z * z) * deriv (L.weierstrassPExcept 0) z) 0 :=
    hc3.mul hPd
  have e : den L = fun z => (fun _ : ℂ => (1 : ℂ)) z +
      (fun z => -(1 / 2 : ℂ) * (z * z * z) * deriv (L.weierstrassPExcept 0) z) z := by
    funext z
    simp only [den]
    ring
  refine ⟨by rw [e]; exact analyticAt_const.add hprod, ?_⟩
  have h1 : taylor0 (den L) = taylor0 (fun _ : ℂ => (1 : ℂ)) +
      taylor0 (fun z => -(1 / 2 : ℂ) * (z * z * z) * deriv (L.weierstrassPExcept 0) z) := by
    rw [e]
    exact (hadd _ _ analyticAt_const hprod).1
  have h2 : taylor0 (fun z => -(1 / 2 : ℂ) * (z * z * z) * deriv (L.weierstrassPExcept 0) z) =
      taylor0 (fun z : ℂ => -(1 / 2 : ℂ) * (z * z * z)) * taylor0 (deriv (L.weierstrassPExcept 0)) :=
    (hadd (fun z : ℂ => -(1 / 2 : ℂ) * (z * z * z)) (deriv (L.weierstrassPExcept 0)) hc3 hPd).2
  have h3 : taylor0 (fun z : ℂ => -(1 / 2 : ℂ) * (z * z * z)) =
      taylor0 (fun _ : ℂ => -(1 / 2 : ℂ)) * taylor0 (fun z : ℂ => z * z * z) :=
    (hadd (fun _ : ℂ => -(1 / 2 : ℂ)) (fun z : ℂ => z * z * z) analyticAt_const hz3).2
  have h4 : taylor0 (fun z : ℂ => z * z * z) = taylor0 (fun z : ℂ => z * z) * taylor0 (fun z : ℂ => z) :=
    (hadd (fun z : ℂ => z * z) (fun z : ℂ => z) hz2 hz).2
  have h5 : taylor0 (fun z : ℂ => z * z) = taylor0 (fun z : ℂ => z) * taylor0 (fun z : ℂ => z) :=
    (hadd (fun z : ℂ => z) (fun z : ℂ => z) hz hz).2
  rw [h1, h2, h3, h4, h5, hC, hC, hX, hd.1 _ hP, map_one, map_neg]
  show _ = 1 - PowerSeries.C (1 / 2 : ℂ) * PowerSeries.X ^ 3 * PowerSeries.derivative ℂ (taylor0 (L.weierstrassPExcept 0))
  ring

theorem den_zero (L : PeriodPair) : den L 0 = 1 := by
  simp [den]

theorem u_eventuallyEq (L : PeriodPair) :
    (fun z => -2 * L.weierstrassP z / L.derivWeierstrassP z)
      =ᶠ[nhds 0] fun z => z * num L z / den L z := by
  have hPl : L.weierstrassP = fun w => L.weierstrassPExcept 0 w + 1 / w ^ 2 := funext fun w => by
    have := Formalism.L2.Th1.F.IsogenyPAux.P_local L 0 (zero_mem _) w
    simpa using this
  have hev := (TaylorSigmaUniqueness.analyticAt_pExcept L).eventually_analyticAt
  filter_upwards [hev] with z hz
  by_cases hz0 : z = 0
  · subst hz0
    simp [hPl, PeriodPair.weierstrassPExcept_zero]
  · have hd : L.derivWeierstrassP z = deriv (L.weierstrassPExcept 0) z - 2 / z ^ 3 := by
      rw [← L.deriv_weierstrassP, hPl]
      have h1 : HasDerivAt (fun w => L.weierstrassPExcept 0 w) (deriv (L.weierstrassPExcept 0) z) z :=
        hz.differentiableAt.hasDerivAt
      have h2 : HasDerivAt (fun w : ℂ => 1 / w ^ 2) (-2 / z ^ 3) z := by
        have h3 := (hasDerivAt_pow 2 z).inv (pow_ne_zero 2 hz0)
        have e : (fun w : ℂ => 1 / w ^ 2) = fun w => (w ^ 2)⁻¹ := funext fun w => one_div _
        rw [e]
        refine h3.congr_deriv ?_
        have e2 : (2 : ℕ) - 1 = 1 := rfl
        rw [e2]
        push_cast
        field_simp
      have h4 := (h1.add h2).deriv
      rw [show (fun w => L.weierstrassPExcept 0 w + 1 / w ^ 2) =
        ((fun w => L.weierstrassPExcept 0 w) + fun w : ℂ => 1 / w ^ 2) from rfl, h4]
      ring
    rw [hd, hPl]
    simp only [num, den]
    by_cases hD : (1 + -(1 / 2 : ℂ) * z ^ 3 * deriv (L.weierstrassPExcept 0) z) = 0
    · have hD' : deriv (L.weierstrassPExcept 0) z - 2 / z ^ 3 = 0 := by
        have e : deriv (L.weierstrassPExcept 0) z - 2 / z ^ 3 =
            (-2 / z ^ 3) * (1 + -(1 / 2 : ℂ) * z ^ 3 * deriv (L.weierstrassPExcept 0) z) := by
          field_simp
          ring
        rw [e, hD, mul_zero]
      rw [hD, hD', div_zero, div_zero]
    · have hD' : deriv (L.weierstrassPExcept 0) z - 2 / z ^ 3 ≠ 0 := by
        intro h
        apply hD
        have e : 1 + -(1 / 2 : ℂ) * z ^ 3 * deriv (L.weierstrassPExcept 0) z =
            (-(z ^ 3) / 2) * (deriv (L.weierstrassPExcept 0) z - 2 / z ^ 3) := by
          field_simp
          ring
        rw [e, h, mul_zero]
      rw [div_eq_div_iff hD' hD]
      field_simp
      ring

theorem uSerLattice_gen (hr : TaylorRing) (hd : TaylorDeriv) (hp : POfLattice) (hn : WpNumDen) :
    USerLattice := by
  intro L
  have hN := T_num hr L
  have hD := T_den hr hd L
  have hden0 : den L 0 = 1 := den_zero L
  have hev := u_eventuallyEq L
  have hne : den L 0 ≠ 0 := by rw [hden0]; exact one_ne_zero
  have hzN : AnalyticAt ℂ (fun z => z * num L z) 0 := analyticAt_id.mul hN.1
  have hinv : AnalyticAt ℂ (fun z => (den L z)⁻¹) 0 := hD.1.inv hne
  have hquot : AnalyticAt ℂ (fun z => z * num L z / den L z) 0 := hzN.div hD.1 hne
  refine ⟨hquot.congr hev.symm, ?_⟩
  have h0 : taylor0 (fun z => -2 * L.weierstrassP z / L.derivWeierstrassP z) =
      taylor0 (fun z => z * num L z / den L z) := hr.2.2.2 _ _ hev
  have h1 : taylor0 (fun z => z * num L z / den L z) =
      taylor0 (fun z => z * num L z) * taylor0 (fun z => (den L z)⁻¹) := by
    have e : (fun z => z * num L z / den L z) = fun z => (z * num L z) * (den L z)⁻¹ := by
      funext z
      rw [div_eq_mul_inv]
    rw [e]
    exact (hr.1 (fun z => z * num L z) (fun z => (den L z)⁻¹) hzN hinv).2
  have h2 : taylor0 (fun z => z * num L z) = taylor0 (fun z : ℂ => z) * taylor0 (num L) :=
    (hr.1 (fun z : ℂ => z) (num L) analyticAt_id hN.1).2
  have hmul : taylor0 (fun z => (den L z)⁻¹) * taylor0 (den L) = 1 := by
    have e1 : taylor0 (fun z => (den L z)⁻¹ * den L z) =
        taylor0 (fun z => (den L z)⁻¹) * taylor0 (den L) :=
      (hr.1 (fun z => (den L z)⁻¹) (den L) hinv hD.1).2
    have hc := hD.1.continuousAt.eventually_ne hne
    have e2 : taylor0 (fun z => (den L z)⁻¹ * den L z) = taylor0 (fun _ : ℂ => (1 : ℂ)) := by
      refine hr.2.2.2 _ _ ?_
      filter_upwards [hc] with z hz
      exact inv_mul_cancel₀ hz
    rw [← e1, e2, hr.2.1, map_one]
  have hc0 : PowerSeries.constantCoeff (taylor0 (den L)) ≠ 0 := by
    rw [hD.2]
    simp
  have hinv2 : taylor0 (fun z => (den L z)⁻¹) = (taylor0 (den L))⁻¹ :=
    (PowerSeries.eq_inv_iff_mul_eq_one hc0).mpr hmul
  rw [h0, h1, h2, hinv2, hr.2.2.1, hN.2, hD.2]
  unfold uSer
  rw [(hn ℂ L.g₂ L.g₃).1, (hn ℂ L.g₂ L.g₃).2, ← hp L]

theorem goodModelLattice_gen (hh : Homogeneity) (hp : POfLattice) (hm : SeriesMap) (hs : TaylorSigma)
    (hst : TaylorSgStar) (hu : USerLattice) : GoodModelLattice := by
  intro l _ L ι g2 g3 hG
  obtain ⟨-, -, -, -, -, lam, hlam, h2, h3⟩ := hG
  obtain ⟨c, hιc⟩ : ∃ c : ℂ, ι c = lam⁻¹ := ⟨ι.symm lam⁻¹, ι.apply_symm_apply _⟩
  have hc : c ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hιc
    exact inv_ne_zero hlam hιc.symm
  refine ⟨c, hc, ?_⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, hg2, hg3⟩ := hh L c hc
  have e2 : ι (scalePair L c hc).g₂ = g2 := by
    rw [hg2, map_mul, map_inv₀, map_pow, hιc, inv_pow, inv_inv]
    exact h2.symm
  have e3 : ι (scalePair L c hc).g₃ = g3 := by
    rw [hg3, map_mul, map_inv₀, map_pow, hιc, inv_pow, inv_inv]
    exact h3.symm
  obtain ⟨-, -, hMp, hMu, hMs, hMst⟩ := hm ℂ ℂ_[l] (ι : ℂ →+* ℂ_[l]) (scalePair L c hc).g₂
    (scalePair L c hc).g₃ (s2 (scalePair L c hc)) (pSeries (scalePair L c hc))
  have e4 : PowerSeries.map (ι : ℂ →+* ℂ_[l]) (pSeries (scalePair L c hc)) = pOf g2 g3 := by
    rw [hp (scalePair L c hc), hMp]
    exact congrArg₂ pOf e2 e3
  refine ⟨e2.symm, e3.symm, e4, ?_, ?_, ?_⟩
  · rw [hs (scalePair L c hc), hMs, e4]
  · rw [hst (scalePair L c hc), hMst, e4]
    rfl
  · rw [(hu (scalePair L c hc)).2, hMu]
    exact congrArg₂ uSer e2 e3

end USer

theorem uSerLattice_of (hp : POfLattice) (hn : WpNumDen) : USerLattice := USer.uSerLattice_gen taylor_ring taylor_deriv hp hn

theorem goodModelLattice_of (hp : POfLattice) (hn : WpNumDen) : GoodModelLattice := USer.goodModelLattice_gen homogeneity_thm hp series_map
    (taylorSigma_of taylor_ring taylor_deriv)
    (taylorSgStar_of (taylorSigma_of taylor_ring taylor_deriv) taylor_ring taylor_exp
      sigmaEntire)
    (uSerLattice_of hp hn)

theorem u_series_lattice : USerLattice := uSerLattice_of weierstrass_p_of_lattice weierstrass_numerator_denominator

theorem good_model_lattice : GoodModelLattice := goodModelLattice_of weierstrass_p_of_lattice weierstrass_numerator_denominator

end Formalism.L2.Th1.F
end
end

