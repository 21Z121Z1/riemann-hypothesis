import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0022
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0026
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0023
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0006
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0016
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0019
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0073
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0004
import ReciprocityTheory.AnalyticForms.AnalyticCharts.MaDensCompEqZeroOfRankLt
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import ReciprocityTheory.AnalyticForms.PotentialTheory.PushAFinsumInter
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0024

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PChartDivisorLength
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar IsSectionOn divSupp IsHorizontal multAt mcPts)
open GroundTheory.Heights₂.Heights (segreChartSet segreChartIdeal segreChartComponents localMult mem_segreChartComponents)

variable {K : Type*} [Fintype K] {ι : K → Type*}

theorem segreChartIdeal_isRadical (P : Ideal (MRing ι)) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) :
    (segreChartIdeal P σ i).IsRadical := by
  rintro f ⟨e, he⟩
  rw [segreChartIdeal, MvPolynomial.mem_vanishingIdeal_iff] at he ⊢
  intro x hx
  have h := he x hx
  rw [map_pow] at h
  exact eq_zero_of_pow_eq_zero h

theorem segreChartIdeal_mono {P W : Ideal (MRing ι)} (h : P ≤ W) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (i : (k : K) → ι k) : segreChartIdeal P σ i ≤ segreChartIdeal W σ i := by
  apply MvPolynomial.vanishingIdeal_anti_mono
  rintro x ⟨z, ⟨hz0, hz⟩, hzi, rfl⟩
  exact ⟨z, ⟨hz0, fun f hf => hz f (h hf)⟩, hzi, rfl⟩

theorem ChartDivisorLength.proof (hNotMem : ChartSectionNotMem.Statement) (hComp : ChartDivisorComponents.Statement)
    (hLen : ChartSectionLength.Statement) : ChartDivisorLength.Statement := by
  intro K _ _ ι _ P n m σ i A s hP hs W hW hWh W' hW'
  have hcomp := (hComp K ι P n m σ i A s hP hs).1
  have hnot := hNotMem K ι P (n + 1) m σ i A s hP hs
  have hW'min : W' ∈ (segreChartIdeal W σ i).minimalPrimes := mem_segreChartComponents.1 hW'
  have hW'p : W'.IsPrime := hW'min.1.1
  have hIW' : segreChartIdeal P σ i ≤ W' :=
    (segreChartIdeal_mono (le_sup_left.trans hW.1.1.2) σ i).trans hW'min.1.2
  have hJW : ∀ J ∈ (segreChartIdeal P σ i).minimalPrimes, J ≤ W' →
      W' ∈ (J ⊔ Ideal.span {chartSection σ i s}).minimalPrimes := fun J hJ hJW' =>
    (hcomp J (mem_segreChartComponents.2 hJ) W').2 ⟨hJW', W, ⟨hW, hWh⟩, hW'⟩
  have hmin : W' ∈ (segreChartIdeal P σ i ⊔ Ideal.span {chartSection σ i s}).minimalPrimes := by
    refine ⟨⟨hW'p, sup_le hIW' ?_⟩, fun Q hQ hQW' => ?_⟩
    · obtain ⟨J, hJ, hJW'⟩ := Ideal.exists_minimalPrimes_le hIW'
      exact le_sup_right.trans (hJW J hJ hJW').1.2
    · have := hQ.1
      obtain ⟨J, hJ, hJQ⟩ := Ideal.exists_minimalPrimes_le (le_sup_left.trans hQ.2)
      exact (hJW J hJ (hJQ.trans hQW')).2 ⟨hQ.1, sup_le hJQ (le_sup_right.trans hQ.2)⟩ hQW'
  have key := GroundTheory.Heights₂.Heights.SectionLengthSum.proof
    (GroundTheory.Heights₂.Heights.LocalSectionLengthSum.proof GroundTheory.Heights₂.Heights.PiQuotCokerFiniteLength.proof)
    (MvPolynomial (Fin m) ℂ) (segreChartIdeal P σ i) W' (chartSection σ i s) (segreChartIdeal_isRadical P σ i)
    (fun J hJ => hnot J (mem_segreChartComponents.2 hJ)) hmin hJW
  rw [← hLen K ι P n m σ i A s hP hs W hW hWh W' hW', key]
  rfl

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PConeComplexBaseChange
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

namespace ConeComplexBaseChange

variable {σ : Type} [Fintype σ]

omit [Fintype σ] in

theorem map_int_complex_eq :
    (MvPolynomial.map (Int.castRingHom ℂ) : MvPolynomial σ ℤ →+* MvPolynomial σ ℂ) =
      (MvPolynomial.map (algebraMap ℚ ℂ)).comp (MvPolynomial.map (Int.castRingHom ℚ)) := by
  apply MvPolynomial.ringHom_ext <;> intro <;> simp

theorem comap_of_minimal (P : Ideal (MvPolynomial σ ℤ)) [P.IsPrime]
    (hP : P.comap (C : ℤ →+* MvPolynomial σ ℤ) = ⊥) (Q : Ideal (MvPolynomial σ ℂ))
    (hQ : Q ∈ (P.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes) :
    Q.comap (MvPolynomial.map (Int.castRingHom ℂ)) = P := by
  have hP' : ∀ m : ℤ, (C m : MvPolynomial σ ℤ) ∈ P → m = 0 := fun m hm => by
    have : m ∈ P.comap (C : ℤ →+* MvPolynomial σ ℤ) := hm
    rw [hP] at this
    exact this
  obtain ⟨hpr, hco, -⟩ := ReciprocityTheory.AnForm.R.extQ_spec P hP'
  have : (P.map (MvPolynomial.map (Int.castRingHom ℚ))).IsPrime := hpr
  rw [map_int_complex_eq, ← Ideal.map_map] at hQ
  have h := ReciprocityTheory.AnForm.R.BaseChangeC.comap_of_mem_minimalPrimes_map _ Q hQ
  rw [map_int_complex_eq, ← Ideal.comap_comap, h]
  exact hco

theorem dim_cancel_one {d : WithBot ℕ∞} {N : ℕ} (h : d + 1 = ((N + 1 : ℕ) : WithBot ℕ∞)) :
    d = (N : WithBot ℕ∞) := by
  refine ReciprocityTheory.AnForm.R.BaseChangeC.withBot_enat_cancel (h := 1) (N := N + 1) ?_ ?_
  · rw [add_comm]; exact_mod_cast h
  · push_cast; rw [add_comm]

end ConeComplexBaseChange

open ConeComplexBaseChange in

theorem ConeComplexBaseChange.proof : ConeComplexBaseChange.Statement := by
  intro K _ ι _ P n s W' Wa hV hs hW hWh hWa
  obtain ⟨-, ⟨hPp, -, -⟩, hPh, hdim⟩ := hV
  have hP' : ∀ m : ℤ, (C m : MRing ι) ∈ P → m = 0 := fun m hm => by
    have : m ∈ P.comap (C : ℤ →+* MRing ι) := hm
    rw [hPh] at this
    exact this
  obtain ⟨hQp, -, hQdim⟩ := ReciprocityTheory.AnForm.R.extQ_spec P hP'
  have hmapP : P.map (MvPolynomial.map (Int.castRingHom ℂ)) =
      (ReciprocityTheory.AnForm.R.extQ P).map (MvPolynomial.map (algebraMap ℚ ℂ)) := by
    rw [map_int_complex_eq, ← Ideal.map_map]; rfl
  have : W'.IsPrime := hW.1.1.1
  refine ⟨?_, fun Q hQ => ⟨?_, ?_⟩, ?_⟩
  · rw [hmapP]
    exact ReciprocityTheory.AnForm.R.BaseChangeC.isRadical_map _
  · have hQ' := hQ
    rw [hmapP] at hQ'
    rw [ReciprocityTheory.AnForm.R.BaseChangeC.ringKrullDim_of_mem_minimalPrimes_map _ Q hQ']
    rw [hdim, show n + 2 + Fintype.card K = (n + Fintype.card K + 1) + 1 by omega] at hQdim
    exact dim_cancel_one hQdim
  · intro hsQ
    apply hs
    rw [← comap_of_minimal P hPh Q hQ]
    exact hsQ
  · have hco : Wa.comap (MvPolynomial.map (Int.castRingHom ℂ)) = W' := comap_of_minimal W' hWh Wa hWa
    have hPW : P ⊔ Ideal.span {s} ≤ W' := hW.1.1.2
    refine ⟨⟨hWa.1.1, le_trans (Ideal.map_mono hPW) hWa.1.2⟩, ?_⟩
    rintro Q' ⟨hQ'p, hQ'le⟩ hQ'W
    have h1 : P ⊔ Ideal.span {s} ≤ Q'.comap (MvPolynomial.map (Int.castRingHom ℂ)) :=
      Ideal.map_le_iff_le_comap.mp hQ'le
    have h2 : Q'.comap (MvPolynomial.map (Int.castRingHom ℂ)) ≤ W' := hco ▸ Ideal.comap_mono hQ'W
    have h3 : W' ≤ Q'.comap (MvPolynomial.map (Int.castRingHom ℂ)) :=
      hW.1.2 ⟨Ideal.comap_isPrime _ _, h1⟩ h2
    exact hWa.2 ⟨hQ'p, Ideal.map_le_iff_le_comap.mpr h3⟩ hQ'W

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PNefCountUpper
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Topology
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

theorem NefCountUpper.proof (hApx : NefSmallApprox.Statement) (hCurve : NefCountUpperCurve.Statement)
    (h7 : G7.Statement) (hPack : PackingStatement) : NefCountUpper.Statement := by
  intro K _ ι _ Ω _ y D A P0 II hII har hb hP0 hs hc hnef hgen hht ε hε
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · filter_upwards [hCurve K ι Ω y A P0 II hII har hb hP0 hs hc hnef hgen hht ε hε] with n hn
    simpa using hn
  have : CharZero Ω := UpperNormalisation.charZero_of_isArithVar har
  set F : ℝ := ((D + 1).factorial : ℝ) with hF
  have hFpos : 0 < F := by rw [hF]; exact_mod_cast Nat.factorial_pos _
  set IA := II K ι (mCoordIdeal y) (D + 1) (fun _ => A) with hIA
  obtain ⟨q, B, P1, hq, hsg, hBc, htop, hev⟩ :=
    hApx K ι Ω y D A P0 II hD hII har hb hP0 hs hc hnef hgen hht (ε / 4) (by linarith)
  set IB := II K ι (mCoordIdeal y) (D + 1) (fun _ => B) with hIB
  set T : ℝ := IA + ε / 2 with hT
  have hq1 : (1 : ℝ) ≤ (q : ℝ) ^ (D + 1) := one_le_pow₀ (by exact_mod_cast hq)
  have hBT : IB + ε / 4 ≤ (q : ℝ) ^ (D + 1) * T := by
    have : ε / 4 ≤ (q : ℝ) ^ (D + 1) * (ε / 4) := le_mul_of_one_le_left (by linarith) hq1
    rw [hT]; nlinarith
  obtain ⟨hfin, Cp, hCp⟩ := hPack K ι Ω y D B (chartLat y B.a) har hb hsg.semipos.1
    (fun τ => Mono.chartLat_le_nm y B.a τ)
  have hG7 := h7 K ι Ω y D B P1 II hD hII har hb hsg hBc

  set v : ℕ → ℝ := fun N => smallSectionCount (IsSmallH (mCoordIdeal y) y B) (chartLat y B.a) N /
    ((N : ℝ) ^ (D + 1) / F) with hv
  have hv_bdd : ∀ N, v N ≤ |Cp| * F * 2 ^ (D + 1) := by
    intro N
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp only [hv, Nat.cast_zero, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true,
        zero_pow, zero_div, div_zero]
      positivity
    · have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
      have hNpos : (0 : ℝ) < (N : ℝ) ^ (D + 1) / F := by positivity
      simp only [hv]
      rw [div_le_iff₀ hNpos]
      have h1 := (hCp N).trans (mul_le_mul_of_nonneg_right (le_abs_self Cp) (by positivity))
      have h2 : ((N : ℝ) + 1) ^ (D + 1) ≤ (2 * N) ^ (D + 1) := pow_le_pow_left₀ (by positivity) (by linarith) _
      calc _ ≤ |Cp| * ((N : ℝ) + 1) ^ (D + 1) := h1
        _ ≤ |Cp| * (2 * N) ^ (D + 1) := mul_le_mul_of_nonneg_left h2 (abs_nonneg Cp)
        _ = |Cp| * F * 2 ^ (D + 1) * ((N : ℝ) ^ (D + 1) / F) := by rw [mul_pow]; field_simp
  have hev1 : ∀ᶠ N in atTop, v N < IB + ε / 4 :=
    eventually_lt_of_limsup_lt (lt_of_le_of_lt hG7 (by linarith)) (isBoundedUnder_of ⟨_, hv_bdd⟩)
  have hNq : Tendsto (fun n : ℕ => n / q + 1) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_succ _) (Nat.tendsto_div_const_atTop (Nat.one_le_iff_ne_zero.mp hq))
  have hlim : Tendsto (fun n : ℕ => T * (1 + (q : ℝ) / n) ^ (D + 1)) atTop (𝓝 T) := by
    have h0 : Tendsto (fun n : ℕ => (q : ℝ) / n) atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat _
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).add h0).pow (D + 1) |>.const_mul T
  filter_upwards [hNq.eventually hev1, hlim.eventually (gt_mem_nhds (show T < IA + ε by linarith)), hev,
    eventually_ge_atTop 1] with n h2 h3 ⟨t, ht0, hts⟩ hn1
  set N := n / q + 1 with hN
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hNpos : (0 : ℝ) < (N : ℝ) ^ (D + 1) / F := by
    have : (0 : ℝ) < N := by exact_mod_cast Nat.succ_pos _
    positivity

  have hcmp : smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) n ≤
      smallSectionCount (IsSmallH (mCoordIdeal y) y B) (chartLat y B.a) N :=
    Mono.smallSectionCount_le_of_injOn (Q := fun m => IsSmallH (mCoordIdeal y) y B (m / q + 1))
      (La' := fun m => chartLat y B.a (m / q + 1)) (fun s => s * t)
      (fun s _ u _ hsu => mul_right_cancel₀ ht0 hsu) (fun s hs hsm => hts s hs hsm) (hfin N)
  have hcount : smallSectionCount (IsSmallH (mCoordIdeal y) y B) (chartLat y B.a) N ≤
      (IB + ε / 4) * ((N : ℝ) ^ (D + 1) / F) := by
    have := h2
    simp only [hv] at this
    rw [div_lt_iff₀ hNpos] at this
    exact this.le

  have hlo : (n : ℝ) ≤ q * N := by
    have := Nat.lt_mul_div_succ n (show 0 < q by omega)
    exact_mod_cast this.le
  have hhi : (q : ℝ) * N ≤ n + q := by
    have : q * (n / q) ≤ n := Nat.mul_div_le n q
    have : q * N ≤ n + q := by rw [hN, mul_add, mul_one]; omega
    exact_mod_cast this
  set X : ℝ := ((q : ℝ) * N) ^ (D + 1) with hX
  have hX1 : (n : ℝ) ^ (D + 1) ≤ X := pow_le_pow_left₀ hnpos.le hlo _
  have hX2 : X ≤ ((n : ℝ) + q) ^ (D + 1) := pow_le_pow_left₀ (by positivity) hhi _
  have hratio : ((n : ℝ) + q) ^ (D + 1) = (1 + (q : ℝ) / n) ^ (D + 1) * (n : ℝ) ^ (D + 1) := by
    rw [← mul_pow]; congr 1; field_simp
  have hTX : T * X ≤ (IA + ε) * (n : ℝ) ^ (D + 1) := by
    rcases le_or_gt 0 T with hT0 | hT0
    · calc T * X ≤ T * ((n : ℝ) + q) ^ (D + 1) := mul_le_mul_of_nonneg_left hX2 hT0
        _ = (T * (1 + (q : ℝ) / n) ^ (D + 1)) * (n : ℝ) ^ (D + 1) := by rw [hratio]; ring
        _ ≤ (IA + ε) * (n : ℝ) ^ (D + 1) := mul_le_mul_of_nonneg_right h3.le (by positivity)
    · calc T * X ≤ T * (n : ℝ) ^ (D + 1) := mul_le_mul_of_nonpos_left hX1 hT0.le
        _ ≤ (IA + ε) * (n : ℝ) ^ (D + 1) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  calc smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) n
      ≤ (IB + ε / 4) * ((N : ℝ) ^ (D + 1) / F) := hcmp.trans hcount
    _ ≤ ((q : ℝ) ^ (D + 1) * T) * ((N : ℝ) ^ (D + 1) / F) := mul_le_mul_of_nonneg_right hBT hNpos.le
    _ = (T * X) / F := by rw [hX, mul_pow]; ring
    _ ≤ ((IA + ε) * (n : ℝ) ^ (D + 1)) / F := div_le_div_of_nonneg_right hTX hFpos.le
    _ = (IA + ε) * ((n : ℝ) ^ (D + 1) / F) := by ring

end

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PProjRankDropDens
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M Filter Topology
open scoped ContDiff

theorem hessC_congr_of_eventuallyEq {D : ℕ} {φ ψ : (Fin D → ℂ) → ℝ} {z : Fin D → ℂ}
    (h : φ =ᶠ[𝓝 z] ψ) : ReciprocityTheory.AnForm.hessC φ z = ReciprocityTheory.AnForm.hessC ψ z := by
  have h1 : fderiv ℝ φ =ᶠ[𝓝 z] fderiv ℝ ψ := h.fderiv
  unfold ReciprocityTheory.AnForm.hessC
  rw [h1.fderiv_eq]

theorem ProjRankDropDens.proof : ProjRankDropDens.Statement := by
  intro K _ ι _ P J n R L V BV hL hV j u hu p hp hrk
  set x : V := (BV.chart j).symm u with hx
  set G : (Fin n → ℂ) → (Σ k, ι k) → ℂ := fun y => R.lift x.1 ((BV.chart j).symm y).1 with hG
  set τ : (Fin n → ℂ) → (Σ k, ι k) → ℂ := fun y q => G y q / G y ⟨q.1, p q.1⟩ with hτ
  obtain ⟨k₀, hk₀⟩ := R.A.cover x.1
  have hGa : ∀ q, AnalyticAt ℂ (fun y => G y q) u := by
    intro q
    have h1 : AnalyticAt ℂ ((fun y => R.lift x.1 y q) ∘ (R.A.chart k₀).symm) (R.A.chart k₀ x.1) :=
      R.holo x.1 q k₀ _ ⟨(R.A.chart k₀).map_source hk₀, by
        simp only [Set.mem_preimage, (R.A.chart k₀).left_inv hk₀]; exact R.mem_U _⟩
    have h2 : AnalyticAt ℂ (R.A.chart k₀ ∘ Subtype.val ∘ (BV.chart j).symm) u :=
      hV.2 j k₀ u ⟨hu, hk₀⟩
    refine (h1.comp_of_eq h2 rfl).congr ?_
    filter_upwards [holoMap_preimage_mem_nhds hV j k₀ hu hk₀] with y hy
    simp only [Function.comp_apply, G, (R.A.chart k₀).left_inv hy.2]
  have hc : ∀ᶠ y in 𝓝 u, ∀ k, G y ⟨k, p k⟩ ≠ 0 :=
    eventually_all.2 fun k => (hGa ⟨k, p k⟩).continuousAt.eventually_ne (hp k)
  have hτa : AnalyticAt ℂ τ u := AnalyticAt.pi fun q => (hGa q).div (hGa ⟨q.1, p q.1⟩) (hp q.1)
  have hτ1 : ∀ y, (∀ k, G y ⟨k, p k⟩ ≠ 0) → ∀ k, τ y ⟨k, p k⟩ = 1 := fun y hy k => div_self (hy k)

  let E : ((Σ k, ι k) → ℂ) ≃L[ℂ] (Fin (Nat.card (Σ k, ι k)) → ℂ) :=
    (LinearEquiv.funCongrLeft ℂ ℂ (Finite.equivFin (Σ k, ι k)).symm).toContinuousLinearEquiv
  let φ' : Fin n → (Fin (Nat.card (Σ k, ι k)) → ℂ) → ℝ := fun i z => Real.log ((L i).h (E.symm z))
  let τ' : (Fin n → ℂ) → (Fin (Nat.card (Σ k, ι k)) → ℂ) := ⇑E ∘ τ
  have hτ'a : AnalyticAt ℂ τ' u := (E.toContinuousLinearMap.analyticAt _).comp hτa
  have hφ' : ∀ i, ContDiffAt ℝ 2 (φ' i) (τ' u) := by
    intro i
    have hS : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} ∈ 𝓝 (τ u) :=
      Filter.mem_of_superset (eventually_all.2 fun k =>
        (continuous_apply (⟨k, p k⟩ : Σ k, ι k)).continuousAt.eventually_ne
          (show τ u ⟨k, p k⟩ ≠ 0 by rw [hτ1 u hp k]; exact one_ne_zero))
        fun z hz k => ⟨p k, hz k⟩
    have hlog : ContDiffAt ℝ ∞ (fun z => Real.log ((L i).h z)) (E.symm (τ' u)) := by
      simp only [τ', Function.comp_apply, E.symm_apply_apply]
      exact ((hL i).contDiffAt hS).log ((L i).pos _ fun k => ⟨p k, by rw [hτ1 u hp k]; exact one_ne_zero⟩).ne'
    exact (hlog.comp _ ((E.symm.contDiff (n := ∞)).restrict_scalars ℝ).contDiffAt).of_le
      (by first | exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤) | simp | exact WithTop.coe_le_coe.2 le_top)

  let g : Fin n → (Fin n → ℂ) → ℂ := fun i y => ∏ k, G y ⟨k, p k⟩ ^ (L i).a k
  have hga : ∀ i, AnalyticAt ℂ (g i) u := fun i =>
    Finset.univ.analyticAt_fun_prod fun k _ => (hGa ⟨k, p k⟩).zpow (hp k)
  have hg0 : ∀ i, g i u ≠ 0 := fun i =>
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hp k)
  have hgerm : ∀ i, (fun y' => ((potOf R (L i)).pullback Subtype.val continuous_subtype_val).φ
      ((BV.chart j).symm u) ((BV.chart j).symm y')) =ᶠ[𝓝 u]
      fun y => (φ' i ∘ τ') y + Real.log ‖g i y‖ := by
    intro i
    filter_upwards [hc] with y hy
    show Real.log ((L i).h (G y)) = _
    have hGy : G y = fun q => G y ⟨q.1, p q.1⟩ * τ y q := by
      funext q
      simp only [τ]
      field_simp [hy q.1]
    have hs : (L i).h (G y) = (∏ k, ‖G y ⟨k, p k⟩‖ ^ (L i).a k) * (L i).h (τ y) := by
      conv_lhs => rw [hGy]
      exact (L i).smul (fun k => G y ⟨k, p k⟩) (τ y) hy
    have hpos : 0 < (L i).h (τ y) :=
      (L i).pos _ fun k => ⟨p k, by rw [hτ1 y hy k]; exact one_ne_zero⟩
    have hprod : 0 < ∏ k, ‖G y ⟨k, p k⟩‖ ^ (L i).a k :=
      Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.2 (hy k)) _
    simp only [Function.comp_apply, φ', τ', E.symm_apply_apply, g, norm_prod, norm_zpow]
    rw [hs, Real.log_mul hprod.ne' hpos.ne', add_comm]
  have hrk' : Module.finrank ℂ (LinearMap.range (fderiv ℂ τ' u).toLinearMap) < n := by
    have : LinearMap.range (fderiv ℂ τ' u).toLinearMap =
        (LinearMap.range (fderiv ℂ τ u).toLinearMap).map E.toLinearEquiv.toLinearMap := by
      rw [show τ' = ⇑E ∘ τ from rfl, E.comp_fderiv]
      exact LinearMap.range_comp (fderiv ℂ τ u).toLinearMap E.toLinearEquiv.toLinearMap
    rw [this, LinearEquiv.finrank_map_eq]
    exact hrk
  unfold locDens
  refine (maDens_congr_hessC _ (fun i => φ' i ∘ τ') u fun i => ?_).trans
    (ReciprocityTheory.AnForm.maDens_comp_eq_zero_of_rank_lt φ' τ' u hτ'a hφ' hrk')
  rw [hessC_congr_of_eventuallyEq (hgerm i)]
  exact ReciprocityTheory.AnForm.A.hessC_add_log_norm _ (g i) u
    ((hφ' i).comp u (hτ'a.contDiffAt.restrict_scalars ℝ)) (hga i) (hg0 i)

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PProjRegularFibre
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M Filter Topology

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}

omit [∀ k, Fintype (ι k)] in

theorem segre_of_sameOrbit {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    ∃ c : ℂ, c ≠ 0 ∧ segre z = c • (segre z' : ((k : K) → ι k) → ℂ) := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨∏ k, c k, Finset.prod_ne_zero_iff.mpr fun k _ => hc k, ?_⟩
  funext i
  simp [segre, Finset.prod_mul_distrib]

theorem segre_lift_eq_smul {e : ℕ} (R : AnLogRes P J e) (x₀ : R.X) {x : R.X} (hx : x ∈ R.U x₀) :
    ∃ c : ℂ, c ≠ 0 ∧ segre (R.lift x x) = c • (segre (R.lift x₀ x) : ((k : K) → ι k) → ℂ) :=
  segre_of_sameOrbit (R.compat x x₀ x ⟨R.mem_U x, hx⟩)

theorem continuousOn_segre_lift {e n : ℕ} (R : AnLogRes P J e)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (x₀ : R.X) :
    ContinuousOn (fun x => Ψ (segre (R.lift x₀ x))) (R.U x₀) := by
  have hl : ContinuousOn (fun x => R.lift x₀ x) (R.U x₀) :=
    continuousOn_pi.mpr fun p => continuousOn_lift R x₀ p
  have hs : Continuous (segre : ((Σ k, ι k) → ℂ) → ((k : K) → ι k) → ℂ) :=
    continuous_pi fun i => continuous_finsetProd Finset.univ fun k _ => continuous_apply _
  exact (LinearMap.continuous_of_finiteDimensional Ψ).comp_continuousOn (hs.comp_continuousOn hl)

theorem isClosed_projFibre {n : ℕ} (R : AnLogRes P J (n + 1))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) {V : Set R.X} (hV : IsClosed V)
    (hΨ : ∀ x ∈ V, Ψ (segre (R.lift x x)) ≠ 0) (y : Fin n → ℂ) :
    IsClosed {x | x ∈ V ∧ Ψ (segre (R.lift x x)) 0 ≠ 0 ∧ projCoord R Ψ x = y} := by
  refine isClosed_of_closure_subset fun x hx => ?_
  set F := {x | x ∈ V ∧ Ψ (segre (R.lift x x)) 0 ≠ 0 ∧ projCoord R Ψ x = y} with hFdef
  have hxV : x ∈ V := closure_minimal (fun z hz => hz.1) hV hx
  set w : R.X → Fin (n + 1) → ℂ := fun z => Ψ (segre (R.lift x z)) with hwdef
  have hw : ContinuousAt w x :=
    (continuousOn_segre_lift R Ψ x).continuousAt ((R.isOpen_U x).mem_nhds (R.mem_U x))
  set h : R.X → Fin n → ℂ := fun z i => w z i.succ - y i * w z 0 with hhdef
  have hh : ContinuousAt h x := continuousAt_pi.mpr fun i =>
    ((continuous_apply _).continuousAt.comp hw).sub
      (continuousAt_const.mul ((continuous_apply _).continuousAt.comp hw))

  have hev : ∀ᶠ z in 𝓝[F] x, h z = 0 := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds ((R.isOpen_U x).mem_nhds (R.mem_U x))] with z hz hzU
    obtain ⟨c, hc, hcz⟩ := segre_lift_eq_smul R x hzU
    have h0 : Ψ (segre (R.lift z z)) = c • w z := by simp [w, hcz]
    have hw0 : w z 0 ≠ 0 := fun h' => hz.2.1 (by rw [h0]; simp [h'])
    funext i
    have hi := congrFun hz.2.2 i
    simp only [projCoord, h0, Pi.smul_apply, smul_eq_mul] at hi
    rw [mul_div_mul_left _ _ hc, div_eq_iff hw0] at hi
    simp [h, hi]
  have : (𝓝[F] x).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hx
  have hlim : h x = 0 :=
    tendsto_nhds_unique (hh.tendsto.mono_left nhdsWithin_le_nhds)
      (tendsto_const_nhds.congr' (hev.mono fun z hz => hz.symm))
  have hi : ∀ i : Fin n, w x i.succ = y i * w x 0 := fun i => by
    have := congrFun hlim i
    simpa [h, sub_eq_zero] using this
  have hw0 : w x 0 ≠ 0 := by
    intro h0
    apply hΨ x hxV
    funext i
    cases i using Fin.cases with
    | zero => simpa [w] using h0
    | succ i => simpa [w, h0] using hi i
  refine ⟨hxV, hw0, funext fun i => ?_⟩
  show w x i.succ / w x 0 = y i
  rw [div_eq_iff hw0]
  exact hi i

theorem ProjRegularFibre.of_found (hReg : ProjRegular.Statement) : ProjRegularFibre.Statement := by
  intro K _ ι _ P J n R Ψ V BV hBV hV hΨ
  have hAn := (hReg K ι P J n R Ψ V BV hBV).2.1
  have : CompactSpace V := isCompact_iff_compactSpace.mp hV.isCompact
  set q : V → Fin n → ℂ := projCoord R Ψ ∘ Subtype.val with hqdef
  set f : Fin BV.n → (Fin n → ℂ) → Fin n → ℂ := fun j => q ∘ (BV.chart j).symm with hfdef

  set C : Fin BV.n → Set (Fin n → ℂ) := fun j => {u | u ∈ (BV.chart j).target ∧
      Ψ (segre (R.lift ((BV.chart j).symm u).1 ((BV.chart j).symm u).1)) 0 ≠ 0 ∧
      LinearMap.det (fderiv ℂ (f j) u : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = 0} with hCdef
  have hnull : ∀ j, volume (f j '' C j) = 0 := fun j => by
    refine addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
      (f' := fun u => (fderiv ℂ (f j) u).restrictScalars ℝ) (fun u hu => ?_) (fun u hu => ?_)
    · have ha := hAn _ hu.2.1 j ((BV.chart j).map_target hu.1)
      rw [(BV.chart j).right_inv hu.1] at ha
      exact (ha.differentiableAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
    · show LinearMap.det ((fderiv ℂ (f j) u : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)).restrictScalars ℝ) = 0
      rw [ReciprocityTheory.AnForm.A.det_restrictScalars_real, hu.2.2, map_zero]
  filter_upwards [compl_mem_ae_iff.mpr (measure_iUnion_null hnull)] with y hy
  set F : Set V := Subtype.val ⁻¹'
    {x | x ∈ V ∧ Ψ (segre (R.lift x x)) 0 ≠ 0 ∧ projCoord R Ψ x = y} with hFdef
  have hFc : IsCompact F :=
    ((isClosed_projFibre R Ψ hV hΨ y).preimage continuous_subtype_val).isCompact

  have hFreg : ∀ x ∈ F, x ∈ projRegular R Ψ BV := by
    intro x hx
    refine ⟨hx.2.1, fun j hj hd => hy (Set.mem_iUnion.mpr ⟨j, BV.chart j x,
      ⟨(BV.chart j).map_source hj, ?_, hd⟩, ?_⟩)⟩
    · rw [(BV.chart j).left_inv hj]; exact hx.2.1
    · show projCoord R Ψ ((BV.chart j).symm (BV.chart j x)).1 = y
      rw [(BV.chart j).left_inv hj]; exact hx.2.2

  have hloc : ∀ x ∈ F, ∃ N ∈ 𝓝 x, Set.InjOn q N := by
    intro x hx
    obtain ⟨j, hj⟩ := BV.cover x
    obtain ⟨W, hWo, hxW, hinj⟩ :=
      pushA_locInj (hAn x (hFreg x hx).1 j hj) ((hFreg x hx).2 j hj)
    refine ⟨(BV.chart j).source ∩ BV.chart j ⁻¹' W,
      ((BV.chart j).isOpen_inter_preimage hWo).mem_nhds ⟨hj, hxW⟩, fun a ha b hb hab => ?_⟩
    refine (BV.chart j).injOn ha.1 hb.1 (hinj ha.2 hb.2 ?_)
    show projCoord R Ψ ((BV.chart j).symm (BV.chart j a)).1 =
      projCoord R Ψ ((BV.chart j).symm (BV.chart j b)).1
    rw [(BV.chart j).left_inv ha.1, (BV.chart j).left_inv hb.1]
    exact hab
  choose! N hN hNinj using hloc
  obtain ⟨t, htF, hcov⟩ := hFc.elim_nhds_subcover N hN
  refine t.finite_toSet.subset fun z hz => ?_
  have hzy : projCoord R Ψ z.1 = y := hz.1
  have hzF : z ∈ F := ⟨z.2, hz.2.1, hzy⟩
  obtain ⟨x, hxt, hzx⟩ := Set.mem_iUnion₂.mp (hcov hzF)
  have hxF := htF x hxt
  have : z = x := hNinj x hxF hzx (mem_of_mem_nhds (hN x hxF)) (hzy.trans hxF.2.2.symm)
  exact this ▸ hxt

end GroundTheory.Heights₂.Heights.Targets
end
end

