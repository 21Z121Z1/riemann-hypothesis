import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0017
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0016
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0019
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0029
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0038
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0031
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0018
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PFCoord
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem PFCoord.of_found (hGD : GenDegStatement)
    (hR4 : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι)
    (hGF : GenFibreExistsStatement) (hFD : FibreDimStatement) (hCF : CoordFibreDeg.Statement) :
    ReciprocityTheory.ChartRestriction.G.AI.I4.PFCoordStatement := by
  intro I hI K _ ι _ K' _ ι' _ κ v Ω _ _ y d L L' hv hP' hP hL hLL'
  obtain ⟨G⟩ := hGF K ι K' ι' κ v (mCoordIdeal y) d hv hP'
  obtain ⟨J, hJ, -⟩ := hR4 G.Φ (FibreBlock κ) (fibreIdx ι' κ)
  have hV : IsProjVarF (fibreIdeal κ G) 0 := hFD K ι K' ι' κ v (mCoordIdeal y) d 0 G hv hP' hP
  choose i hi using hV.1.2.2
  have h0 := hJ.1 (fibreIdeal κ G) Fin.elim0 i hV hi
  rw [hGD I hI K ι K' ι' κ v (mCoordIdeal y) d G J L L' hv hP' hP hJ hL hLL', h0,
    hCF K ι K' ι' κ v Ω y d G i hv hP' hP hi, Int.cast_natCast]

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PMoriwakiBigCurve
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.Geo Filter

theorem chartLat_le_chartLatNm {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    (y : (Σ k, ι k) → Ω) (a : K → ℤ) (τ : ℕ) : chartLat y a τ ≤ chartLatNm y a τ := fun _ hs c hc =>
  (mem_integralClosure_iff _ _).mpr (isIntegral_algebraMap (R := chartRingZ y c) (A := Ω) (x := ⟨_, hs c hc⟩))

theorem MoriwakiBigCurve.proof (hL : CurveCountLower.Statement)
    (hPk : HilbertSamuel.SmallPacking.Statement) : MoriwakiBigCurve.Statement := by
  intro K _ ι _ Ω _ y A P0 II hII hP hB _ hS hC _ _
  set Q := IsSmallH (mCoordIdeal y) y A
  set La := chartLat y A.a
  set T := II K ι (mCoordIdeal y) (0 + 1) (fun _ => A)
  obtain ⟨C, hC⟩ := hL K ι Ω y A II hII hP hB hS.1 hC
  obtain ⟨C', hC'⟩ := (hPk K ι Ω y 0 A La hP hB hS.1 fun τ => chartLat_le_chartLatNm y A.a τ).2
  have h0 : ∀ τ, 0 ≤ smallSectionCount Q La τ := fun τ => Real.log_natCast_nonneg _
  have hf : (fun k : ℕ => smallSectionCount Q La (1 * k) / (((1 * k : ℕ) : ℝ) ^ (0 + 1) / ((0 + 1).factorial : ℝ))) =
      fun k : ℕ => smallSectionCount Q La k / k := by
    funext k
    simp
  unfold arVolP
  rw [hf]
  have hC'0 : 0 ≤ C' := by simpa using (h0 0).trans (hC' 0)
  have hbdd : IsBoundedUnder (· ≤ ·) atTop fun k : ℕ => smallSectionCount Q La k / k := by
    refine ⟨2 * C', eventually_map.mpr ((eventually_ge_atTop 1).mono fun k hk => ?_)⟩
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    show smallSectionCount Q La k / k ≤ 2 * C'
    rw [div_le_iff₀ (by linarith)]
    have h1 : smallSectionCount Q La k ≤ C' * ((k : ℝ) + 1) := by simpa using hC' k
    nlinarith
  refine le_of_forall_sub_le fun ε hε => le_limsup_of_frequently_le ?_ hbdd
  refine Eventually.frequently ((eventually_ge_atTop (⌈C / ε⌉₊ + 1)).mono fun k hk => ?_)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (Nat.le_add_left 1 _).trans hk
  have hkC : C ≤ ε * k := by
    have h1 : C / ε ≤ k := (Nat.le_ceil _).trans (by exact_mod_cast (Nat.le_succ _).trans hk)
    rwa [div_le_iff₀ hε, mul_comm] at h1
  have hτ : (k : ℝ) * T - C ≤ smallSectionCount Q La k := hC k ((Nat.le_add_left 1 _).trans hk)
  rw [le_div_iff₀ (by linarith)]
  show (T - ε) * k ≤ _
  nlinarith

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PNefCountLower
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

section Shift

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem smallSectionCount_le_shift {y : (Σ k, ι k) → Ω} {A : HermLine ι} {m d : ℕ} {t : Ω}
    (ht : t ∈ chartLat y A.a d) (ht0 : t ≠ 0) (hts : IsSmallH (mCoordIdeal y) y A d t)
    (hfin : {s : chartLat y A.a (m + d) | IsSmallH (mCoordIdeal y) y A (m + d) (s : Ω)}.Finite) :
    smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) m ≤
      smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) (m + d) := by
  unfold smallSectionCount
  have : Finite {s : chartLat y A.a (m + d) // IsSmallH (mCoordIdeal y) y A (m + d) (s : Ω)} :=
    hfin.to_subtype
  have hmap : ∀ s : {s : chartLat y A.a m // IsSmallH (mCoordIdeal y) y A m (s : Ω)},
      (s.1 : Ω) * t ∈ chartLat y A.a (m + d) ∧ IsSmallH (mCoordIdeal y) y A (m + d) ((s.1 : Ω) * t) := by
    intro s
    refine ⟨chartLat_mul s.1.2 ht, fun dg dh g h z hg hh hdeg he hz => ?_⟩
    have := SectionBoundedMul.proof K ι Ω y A m d 1 1 _ t s.1.2 ht (isBoundedH_one_of_isSmallH s.2)
      (isBoundedH_one_of_isSmallH hts) dg dh g h z hg hh hdeg he hz
    simpa only [one_mul] using this
  have hcard : Nat.card {s : chartLat y A.a m // IsSmallH (mCoordIdeal y) y A m (s : Ω)} ≤
      Nat.card {s : chartLat y A.a (m + d) // IsSmallH (mCoordIdeal y) y A (m + d) (s : Ω)} :=
    Nat.card_le_card_of_injective (fun s => ⟨⟨(s.1 : Ω) * t, (hmap s).1⟩, (hmap s).2⟩) fun s s' h => by
      simp only [Subtype.mk.injEq] at h
      exact Subtype.ext (Subtype.ext (mul_right_cancel₀ ht0 h))
  rcases Nat.eq_zero_or_pos (Nat.card {s : chartLat y A.a m // IsSmallH (mCoordIdeal y) y A m (s : Ω)})
    with h0 | hpos
  · rw [h0, Nat.cast_zero, Real.log_zero]
    exact Real.log_natCast_nonneg _
  · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hcard)

end Shift

theorem eventually_mul_pow_le_shift (D L : ℕ) {b c : ℝ} (hc : 0 < c) (hbc : b < c) :
    ∀ᶠ n : ℕ in atTop, b * (n : ℝ) ^ (D + 1) ≤ c * ((n : ℝ) - L) ^ (D + 1) := by
  have h1 : Tendsto (fun n : ℕ => (1 - (L : ℝ) / n) ^ (D + 1)) atTop (𝓝 1) := by
    simpa using ((tendsto_const_div_atTop_nhds_zero_nat (L : ℝ)).const_sub 1).pow (D + 1)
  filter_upwards [h1.eventually (lt_mem_nhds ((div_lt_one hc).2 hbc)), eventually_ge_atTop 1] with n hn hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have e : (n : ℝ) - L = n * (1 - L / n) := by field_simp
  have hp : 0 < (n : ℝ) ^ (D + 1) := by positivity
  rw [e, mul_pow]
  have := (div_lt_iff₀ hc).1 hn
  nlinarith

theorem NefCountLower.proof (hM : NefCountAlongMultiples.Statement) (hS : NefSmallSectionEventually.Statement)
    (hPk : PackingStatement) : NefCountLower.Statement := by
  intro K _ ι _ Ω _ y D A P0 II hII har hb hP0 hs hc hnef hgen hht ε hε
  set T := II K ι (mCoordIdeal y) (D + 1) (fun _ => A)
  have hfac : (0 : ℝ) < ((D + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  by_cases hT : T - ε ≤ 0
  · exact Eventually.of_forall fun n =>
      (mul_nonpos_of_nonpos_of_nonneg hT (by positivity)).trans (Real.log_natCast_nonneg _)
  rw [not_le] at hT
  obtain ⟨a, ha, hak⟩ := hM K ι Ω y D A P0 II hII har hb hP0 hs hc hnef hgen hht (ε / 2) (by linarith)
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 hak
  obtain ⟨n₀, hn₀⟩ :=
    eventually_atTop.1 (hS K ι Ω y D A P0 II hII har hb hP0 hs hc hnef hgen hht (by linarith))
  have hfin := (hPk K ι Ω y D A (chartLat y A.a) har hb hs.1
    (fun τ _ hs' c hc' => isIntegral_algebraMap (x := (⟨_, hs' c hc'⟩ : chartRingZ y c)))).1
  filter_upwards [eventually_mul_pow_le_shift D (n₀ + a) (b := T - ε) (c := T - ε / 2) (by linarith)
    (by linarith), eventually_ge_atTop (n₀ + a + a * k₀)] with n hn hge
  obtain ⟨k, r, hr, hnk⟩ : ∃ k r, r < a ∧ n = a * k + (n₀ + r) :=
    ⟨(n - n₀) / a, (n - n₀) % a, Nat.mod_lt _ ha, by have := Nat.div_add_mod (n - n₀) a; omega⟩
  have hkk : k₀ ≤ k := by
    by_contra hlt
    have : a * k + a ≤ a * k₀ := by nlinarith
    omega
  obtain ⟨t, ht, ht0, hts⟩ := hn₀ (n₀ + r) (by omega)
  have hL : (n : ℝ) - ((n₀ + a : ℕ) : ℝ) ≤ ((a * k : ℕ) : ℝ) := by
    have : (n : ℝ) ≤ ((a * k : ℕ) : ℝ) + ((n₀ + a : ℕ) : ℝ) := by exact_mod_cast (by omega : n ≤ a * k + (n₀ + a))
    linarith
  have hL0 : (0 : ℝ) ≤ (n : ℝ) - ((n₀ + a : ℕ) : ℝ) := by
    have : ((n₀ + a : ℕ) : ℝ) ≤ n := by exact_mod_cast (by omega : n₀ + a ≤ n)
    linarith
  have hpow := pow_le_pow_left₀ hL0 hL (D + 1)
  calc (T - ε) * ((n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ))
      = ((T - ε) * (n : ℝ) ^ (D + 1)) / ((D + 1).factorial : ℝ) := by ring
    _ ≤ ((T - ε / 2) * ((n : ℝ) - ((n₀ + a : ℕ) : ℝ)) ^ (D + 1)) / ((D + 1).factorial : ℝ) :=
        div_le_div_of_nonneg_right hn hfac.le
    _ ≤ ((T - ε / 2) * ((a * k : ℕ) : ℝ) ^ (D + 1)) / ((D + 1).factorial : ℝ) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by linarith)) hfac.le
    _ = (T - ε / 2) * (((a * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) := by ring
    _ ≤ smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) (a * k) := hk₀ k hkk
    _ ≤ smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) (a * k + (n₀ + r)) :=
        smallSectionCount_le_shift ht ht0 hts (hfin _)
    _ = smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) n := by rw [← hnk]

end

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PProjRegular
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M

namespace ProjRegular

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}
  {n : ℕ} {R : AnLogRes P J (n + 1)} (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))

theorem proj_segre_lift_eq {x y : R.X} (hy : y ∈ R.U x) :
    ∃ c : ℂ, c ≠ 0 ∧ Ψ (segre (R.lift y y)) = c • Ψ (segre (R.lift x y)) := by
  obtain ⟨c, hc, hz⟩ := R.compat y x y ⟨R.mem_U y, hy⟩
  refine ⟨∏ k, c k, Finset.prod_ne_zero_iff.mpr (fun k _ => hc k), ?_⟩
  rw [← map_smul]
  congr 1
  funext i
  simp only [segre, Pi.smul_apply, smul_eq_mul, hz, Finset.prod_mul_distrib]

theorem projCoord_eq {x y : R.X} (hy : y ∈ R.U x) :
    projCoord R Ψ y = fun i => Ψ (segre (R.lift x y)) i.succ / Ψ (segre (R.lift x y)) 0 := by
  obtain ⟨c, hc, h⟩ := proj_segre_lift_eq Ψ hy
  funext i
  simp only [projCoord, h, Pi.smul_apply, smul_eq_mul]
  exact mul_div_mul_left _ _ hc

theorem proj_ne_zero_iff {x y : R.X} (hy : y ∈ R.U x) :
    Ψ (segre (R.lift y y)) 0 ≠ 0 ↔ Ψ (segre (R.lift x y)) 0 ≠ 0 := by
  obtain ⟨c, hc, h⟩ := proj_segre_lift_eq Ψ hy
  simp [h, hc]

theorem lift_analyticAt {V : Set R.X} {BV : FinHolAtlas n V} (hB : HoloMap BV R.A Subtype.val)
    (x : V) {j : Fin BV.n} (hx : x ∈ (BV.chart j).source) :
    AnalyticAt ℂ (fun u => R.lift x.1 ((BV.chart j).symm u).1) (BV.chart j x) ∧
      ∀ᶠ u in 𝓝 (BV.chart j x), ((BV.chart j).symm u).1 ∈ R.U x.1 := by
  obtain ⟨k, hk⟩ : ∃ k, x.1 ∈ (R.A.chart k).source := R.A.cover x.1
  have hxt : BV.chart j x ∈ (BV.chart j).target := (BV.chart j).map_source hx
  have hsx : (BV.chart j).symm (BV.chart j x) = x := (BV.chart j).left_inv hx
  have hcont : ContinuousAt (fun u => ((BV.chart j).symm u).1) (BV.chart j x) :=
    continuous_subtype_val.continuousAt.comp ((BV.chart j).continuousAt_symm hxt)
  have hev : ∀ s : Set R.X, IsOpen s → x.1 ∈ s →
      ∀ᶠ u in 𝓝 (BV.chart j x), ((BV.chart j).symm u).1 ∈ s := fun s hs hxs =>
    hcont.preimage_mem_nhds (by
      show s ∈ 𝓝 ((BV.chart j).symm (BV.chart j x)).1
      rw [hsx]; exact hs.mem_nhds hxs)
  refine ⟨?_, hev _ (R.isOpen_U x.1) (R.mem_U x.1)⟩
  rw [analyticAt_pi_iff]
  intro p
  have h1 : AnalyticAt ℂ ((fun y => R.lift x.1 y p) ∘ (R.A.chart k).symm) (R.A.chart k x.1) :=
    R.holo x.1 p k _ ⟨(R.A.chart k).map_source hk, by
      show (R.A.chart k).symm (R.A.chart k x.1) ∈ R.U x.1
      rw [(R.A.chart k).left_inv hk]; exact R.mem_U x.1⟩
  have h2 : AnalyticAt ℂ (R.A.chart k ∘ Subtype.val ∘ (BV.chart j).symm) (BV.chart j x) :=
    hB.2 j k _ ⟨hxt, by
      show ((BV.chart j).symm (BV.chart j x)).1 ∈ (R.A.chart k).source
      rw [hsx]; exact hk⟩
  refine (h1.comp_of_eq h2 (by simp [hsx])).congr ?_
  filter_upwards [hev _ (R.A.chart k).open_source hk] with u hu
  simp [(R.A.chart k).left_inv hu]

theorem proj_analyticAt {V : Set R.X} {BV : FinHolAtlas n V} (hB : HoloMap BV R.A Subtype.val)
    (x : V) {j : Fin BV.n} (hx : x ∈ (BV.chart j).source) :
    AnalyticAt ℂ (fun u => Ψ (segre (R.lift x.1 ((BV.chart j).symm u).1))) (BV.chart j x) := by
  classical
  have hF := (lift_analyticAt hB x hx).1
  have hs : AnalyticAt ℂ (fun u => segre (R.lift x.1 ((BV.chart j).symm u).1))
      (BV.chart j x) := by
    rw [analyticAt_pi_iff]
    intro i
    exact Finset.univ.analyticAt_fun_prod (fun k _ => analyticAt_pi_iff.1 hF ⟨k, i k⟩)
  exact ((LinearMap.toContinuousLinearMap Ψ).analyticAt _).comp hs

theorem analyticAt_chart {V : Set R.X} {BV : FinHolAtlas n V} (hB : HoloMap BV R.A Subtype.val)
    (x : V) (h0 : Ψ (segre (R.lift x.1 x.1)) 0 ≠ 0) (j : Fin BV.n)
    (hx : x ∈ (BV.chart j).source) :
    AnalyticAt ℂ ((projCoord R Ψ ∘ Subtype.val) ∘ (BV.chart j).symm) (BV.chart j x) := by
  have hsx : (BV.chart j).symm (BV.chart j x) = x := (BV.chart j).left_inv hx
  have hc : ∀ i : Fin (n + 1), AnalyticAt ℂ
      (fun u => Ψ (segre (R.lift x.1 ((BV.chart j).symm u).1)) i) (BV.chart j x) :=
    fun i => analyticAt_pi_iff.1 (proj_analyticAt Ψ hB x hx) i
  have hG : AnalyticAt ℂ (fun u (i : Fin n) => Ψ (segre (R.lift x.1 ((BV.chart j).symm u).1)) i.succ /
      Ψ (segre (R.lift x.1 ((BV.chart j).symm u).1)) 0) (BV.chart j x) := by
    rw [analyticAt_pi_iff]
    intro i
    exact (hc i.succ).div (hc 0) (by simpa [hsx] using h0)
  refine hG.congr ?_
  filter_upwards [(lift_analyticAt hB x hx).2] with u hu
  exact (projCoord_eq Ψ hu).symm

theorem det_ne_zero_of_chart {V : Set R.X} {BV : FinHolAtlas n V}
    (hB : HoloMap BV R.A Subtype.val) (y : V) (h0 : Ψ (segre (R.lift y.1 y.1)) 0 ≠ 0)
    {j k : Fin BV.n} (hj : y ∈ (BV.chart j).source) (hk : y ∈ (BV.chart k).source)
    (hd : LinearMap.det (fderiv ℂ ((projCoord R Ψ ∘ Subtype.val) ∘ (BV.chart k).symm)
      (BV.chart k y) : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ≠ 0) :
    LinearMap.det (fderiv ℂ ((projCoord R Ψ ∘ Subtype.val) ∘ (BV.chart j).symm)
      (BV.chart j y) : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ≠ 0 := by
  have hu0 : BV.chart j y ∈ (BV.chart j).target := (BV.chart j).map_source hj
  have hv0 : BV.chart k y ∈ (BV.chart k).target := (BV.chart k).map_source hk
  have hsj : (BV.chart j).symm (BV.chart j y) = y := (BV.chart j).left_inv hj
  have hsk : (BV.chart k).symm (BV.chart k y) = y := (BV.chart k).left_inv hk
  have hτu : (BV.chart k ∘ (BV.chart j).symm) (BV.chart j y) = BV.chart k y := by simp [hsj]
  have hτ : AnalyticAt ℂ (BV.chart k ∘ (BV.chart j).symm) (BV.chart j y) :=
    BV.holo j k _ ⟨hu0, by
      show (BV.chart j).symm (BV.chart j y) ∈ (BV.chart k).source; rw [hsj]; exact hk⟩
  have hσ : AnalyticAt ℂ (BV.chart j ∘ (BV.chart k).symm)
      ((BV.chart k ∘ (BV.chart j).symm) (BV.chart j y)) := by
    rw [hτu]
    exact BV.holo k j _ ⟨hv0, by
      show (BV.chart k).symm (BV.chart k y) ∈ (BV.chart j).source; rw [hsk]; exact hj⟩
  have hev : ∀ᶠ u in 𝓝 (BV.chart j y), (BV.chart j).symm u ∈ (BV.chart k).source :=
    ((BV.chart j).continuousAt_symm hu0).preimage_mem_nhds (by
      show (BV.chart k).source ∈ 𝓝 ((BV.chart j).symm (BV.chart j y))
      rw [hsj]; exact (BV.chart k).open_source.mem_nhds hk)
  have hid : (BV.chart j ∘ (BV.chart k).symm) ∘ (BV.chart k ∘ (BV.chart j).symm)
      =ᶠ[𝓝 (BV.chart j y)] id := by
    filter_upwards [hev, (BV.chart j).open_target.mem_nhds hu0] with u hu hut
    simp [(BV.chart k).left_inv hu, (BV.chart j).right_inv hut]
  have hq : (projCoord R Ψ ∘ Subtype.val) ∘ (BV.chart j).symm =ᶠ[𝓝 (BV.chart j y)]
      ((projCoord R Ψ ∘ Subtype.val) ∘ (BV.chart k).symm) ∘ (BV.chart k ∘ (BV.chart j).symm) := by
    filter_upwards [hev] with u hu
    simp [(BV.chart k).left_inv hu]
  have hqk : DifferentiableAt ℂ ((projCoord R Ψ ∘ Subtype.val) ∘ (BV.chart k).symm)
      ((BV.chart k ∘ (BV.chart j).symm) (BV.chart j y)) := by
    rw [hτu]; exact (analyticAt_chart Ψ hB y h0 k hk).differentiableAt
  have hinv : (fderiv ℂ (BV.chart j ∘ (BV.chart k).symm)
      ((BV.chart k ∘ (BV.chart j).symm) (BV.chart j y))).comp
      (fderiv ℂ (BV.chart k ∘ (BV.chart j).symm) (BV.chart j y)) =
      ContinuousLinearMap.id ℂ (Fin n → ℂ) := by
    rw [← fderiv_comp _ hσ.differentiableAt hτ.differentiableAt, hid.fderiv_eq, fderiv_id]
  have hdetτ : LinearMap.det (fderiv ℂ (BV.chart k ∘ (BV.chart j).symm) (BV.chart j y) :
      (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ≠ 0 := by
    intro h
    have := congrArg (fun f : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) =>
      LinearMap.det (f : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))) hinv
    simp [LinearMap.det_comp, h] at this
  rw [hq.fderiv_eq, fderiv_comp _ hqk hτ.differentiableAt, ContinuousLinearMap.toLinearMap_comp,
    LinearMap.det_comp, hτu]
  exact mul_ne_zero hd hdetτ

theorem proof : ProjRegular.Statement := by
  intro K _ ι _ P J n R Ψ V BV hB
  refine ⟨?_, fun x h0 j hx => analyticAt_chart Ψ hB x h0 j hx, ?_⟩
  · rw [isOpen_iff_mem_nhds]
    rintro x ⟨h0, hdet⟩
    have hj : x ∈ (BV.chart (chartIdx BV x)).source := Classical.choose_spec (BV.cover x)
    have hsx : (BV.chart (chartIdx BV x)).symm (BV.chart (chartIdx BV x) x) = x :=
      (BV.chart _).left_inv hj
    have hg : BV.chart (chartIdx BV x) x ∈ goodT BV (projCoord R Ψ ∘ Subtype.val) (chartIdx BV x) :=
      ⟨(BV.chart _).map_source hj, analyticAt_chart Ψ hB x h0 _ hj, hdet _ hj⟩
    have hD : ∀ᶠ u in 𝓝 (BV.chart (chartIdx BV x) x),
        Ψ (segre (R.lift x.1 ((BV.chart (chartIdx BV x)).symm u).1)) 0 ≠ 0 :=
      (analyticAt_pi_iff.1 (proj_analyticAt Ψ hB x hj) 0).continuousAt.eventually_ne
        (by simpa [hsx] using h0)
    refine ((BV.chart _).eventually_nhds' (· ∈ projRegular R Ψ BV) hj).1 ?_
    filter_upwards [(isOpen_goodT BV _ _).mem_nhds hg, hD, (lift_analyticAt hB x hj).2]
      with u hu hDu hUu
    have h0u := (proj_ne_zero_iff Ψ hUu).2 hDu
    refine ⟨h0u, fun k hk => det_ne_zero_of_chart Ψ hB _ h0u hk ((BV.chart _).map_target hu.1) ?_⟩
    rw [(BV.chart _).right_inv hu.1]
    exact hu.2.2
  · intro x h0 hd
    exact ⟨h0, fun k hk => det_ne_zero_of_chart Ψ hB x h0 hk
      (Classical.choose_spec (BV.cover x)) hd⟩

end ProjRegular

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChart
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open Filter Topology
open scoped ContDiff
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar ptsIntegral pot segre isOpen_blockNonzero)

def expLine {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    (v : ((Σ k, ι k) → ℂ) → ℝ) (hv : IsDegZeroSmooth v) : HermLine ι :=
  HermLine.ofWeight (fun z => -v z) fun c z hc => by rw [hv.2 c z hc]

theorem pot_cons_expLine {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {n : ℕ}
    (v : ((Σ k, ι k) → ℂ) → ℝ) (hv : IsDegZeroSmooth v) (L : Fin n → HermLine ι) :
    pot (Fin.cons (expLine v hv) L : Fin (n + 1) → HermLine ι) = Fin.cons v (pot L) := by
  funext j z
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [pot, expLine, HermLine.ofWeight]
  · simp [pot]

theorem isSmoothHerm_cons_expLine {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {n : ℕ}
    (v : ((Σ k, ι k) → ℂ) → ℝ) (hv : IsDegZeroSmooth v) (L : Fin n → HermLine ι)
    (hL : ∀ j, IsSmoothHerm (L j)) :
    ∀ j, IsSmoothHerm ((Fin.cons (expLine v hv) L : Fin (n + 1) → HermLine ι) j) := by
  intro j
  refine Fin.cases ?_ (fun j => ?_) j
  · exact Real.contDiff_exp.comp_contDiffOn hv.1.neg.neg
  · simpa using hL j

theorem SegreChart.proof (hDim : SegreChartDim.Statement) (hInt : SegreChartIntegral.Statement) :
    SegreChart.Statement := by
  classical
  intro K _ _ ι _ P n L u v i δ hP hL hu hv hδ hsupp
  let σ := (Fintype.equivFin ((k : K) → ι k)).symm
  let lam := chartLift σ i
  let χ : ContDiffBump (0 : Fin (Fintype.card ((k : K) → ι k)) → ℂ) :=
    ⟨1 / δ + 1, 1 / δ + 2, by positivity, by linarith⟩
  let U := fun x => χ x * u (lam x)
  let V := fun x => v (lam x)
  let Φ : Fin n → _ := fun j x => pot L j (lam x)
  have hlam : ContDiff ℝ ∞ lam := contDiff_chartLift σ i

  let Ω := lam ⁻¹' {z | ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0}
  have hΩ : IsOpen Ω := isOpen_blockNonzero.preimage hlam.continuous
  have hsm : ∀ f : ((Σ k, ι k) → ℂ) → ℝ, ContDiffOn ℝ ∞ f {z | ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0} →
      ContDiffOn ℝ ∞ (f ∘ lam) Ω := fun f hf => hf.comp hlam.contDiffOn fun _ hx => hx
  have hpot : ∀ j, ContDiffOn ℝ ∞ (pot L j) {z | ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0} := fun j =>
    (hL j).log fun z hz => ((L j).pos z hz).ne'

  have key : ∀ x ∈ segreChartSet P σ i, U =ᶠ[𝓝 x] u ∘ lam := by
    rintro _ ⟨z, -, hzi, rfl⟩
    by_cases hr : ‖fun a => segre z (σ a)‖ < 1 / δ + 1
    · filter_upwards [Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hr)] with y hy
      simp [U, χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)]
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
      simp [U, hsupp _ hy]
  have hJ : ∀ J ∈ segreChartComponents P σ i, ComplexSets.zeroSet J ⊆ Ω := fun J hJ x hx =>
    chartLift_blockNonzero σ i (chart_coord_eq_one hJ hx)
  refine ⟨Fintype.card ((k : K) → ι k), segreChartComponents P σ i, U, V, Φ,
    fun J hJs => ⟨(mem_segreChartComponents.1 hJs).1.1,
      hDim K ι P (n + 1) _ σ i hP J hJs,
      ⟨Ω, hΩ, hJ J hJs, (χ.contDiff.contDiffOn).mul (hsm u hu.1)⟩,
      ⟨Ω, hΩ, hJ J hJs, hsm v hv.1⟩, fun j => ⟨Ω, hΩ, hJ J hJs, hsm _ (hpot j)⟩⟩,
    χ.hasCompactSupport.mul_right, ?_, ?_⟩
  · rw [← pot_cons_expLine v hv L]
    refine hInt K ι P n _ σ i _ u δ U _ hP (isSmoothHerm_cons_expLine v hv L hL) hu hδ (Or.inl hsupp)
      fun x hx => ⟨key x hx, fun j => EventuallyEq.of_eq ?_⟩
    refine Fin.cases ?_ (fun j => ?_) j
    · funext y; simp [V, lam, pot, expLine, HermLine.ofWeight]
    · rfl
  · rw [← pot_cons_expLine u hu L]
    refine hInt K ι P n _ σ i _ v δ V _ hP (isSmoothHerm_cons_expLine u hu L hL) hv hδ
      (Or.inr fun z hz => by rw [pot_cons_expLine u hu L]; exact hsupp z hz)
      fun x hx => ⟨EventuallyEq.rfl, fun j => ?_⟩
    refine Fin.cases ?_ (fun j => ?_) j
    · have h0 : pot (Fin.cons (expLine u hu) L : Fin (n + 1) → HermLine ι) 0 = u := by
        rw [pot_cons_expLine u hu L]; rfl
      simpa [h0] using key x hx
    · exact EventuallyEq.rfl

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PoincareLelongAlt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

theorem PoincareLelongAlt.of_found (hSt : StokesStatement) (hReg : PoincareLelongRegularised.Statement)
    (hLim : PoincareLelongLimit.Statement) : ReciprocityTheory.ChartRestriction.G.Geo.ArithmeticPoincareLelongFormula := by
  intro K _ ι _ P n L A B s hP hL hA hB hBa hs
  obtain ⟨a, ha, hsa, -⟩ := id hs
  have hS : ∀ ε ∈ Set.Ioi (0 : ℝ),
      ptsIntegral P (Fin.cons (regLog A s ε) (pot L)) (fun z => Real.log (B.h z)) =
        ptsIntegral P (Fin.cons (fun z => Real.log (B.h z)) (pot L)) (regLog A s ε) := by
    intro ε hε
    have h := hSt K ι P n L (regLine A s ε ha hsa) B hP hL (isSmoothHerm_regLine hA hε ha hsa) hB
      (regLine_a A s ε ha hsa) hBa
    rw [log_regLine] at h
    exact h.symm
  exact tendsto_nhds_unique (hReg K ι P n L A B s hP hL hA hB hBa hs)
    ((hLim K ι P n L A B s hP hL hA hB hBa hs).congr' (eventually_nhdsWithin_of_forall hS))

end GroundTheory.Heights₂.Heights.Targets
end

