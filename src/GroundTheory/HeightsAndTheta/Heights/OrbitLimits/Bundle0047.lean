import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0045
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PZeroCocycleSection
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0044
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0046
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0043
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0040
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PClosedPointUnitSection
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0015

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PChartLatFull
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace ChartLatFull

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

def ratSat [CharZero Ω] (R : Subalgebra ℤ Ω) : Subalgebra ℚ Ω where
  carrier := {t | ∃ n : ℕ, 0 < n ∧ (n : Ω) * t ∈ R}
  mul_mem' := by
    rintro t u ⟨n, hn, ht⟩ ⟨m, hm, hu⟩
    refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
    have : ((n * m : ℕ) : Ω) * (t * u) = ((n : Ω) * t) * ((m : Ω) * u) := by push_cast; ring
    rw [this]
    exact R.mul_mem ht hu
  one_mem' := ⟨1, one_pos, by simp⟩
  add_mem' := by
    rintro t u ⟨n, hn, ht⟩ ⟨m, hm, hu⟩
    refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
    have : ((n * m : ℕ) : Ω) * (t + u) = (m : Ω) * ((n : Ω) * t) + (n : Ω) * ((m : Ω) * u) := by push_cast; ring
    rw [this]
    exact R.add_mem (R.mul_mem (R.natCast_mem m) ht) (R.mul_mem (R.natCast_mem n) hu)
  zero_mem' := ⟨1, one_pos, by simp⟩
  algebraMap_mem' := by
    intro q
    refine ⟨q.den, q.den_pos, ?_⟩
    have hd : (q.den : Ω) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
    have : (q.den : Ω) * algebraMap ℚ Ω q = (q.num : Ω) := by
      rw [eq_ratCast, Rat.cast_def, mul_div_cancel₀ _ hd]
    rw [this]
    exact R.intCast_mem _

theorem exists_nat_mul_mem [NumberField Ω] {y : (Σ k, ι k) → Ω} (hy : Birational y) (c : ∀ k, ι k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (t : Ω) : ∃ n : ℕ, 0 < n ∧ (n : Ω) * t ∈ chartRingZ y c := by
  obtain ⟨d, g, h, hg, hh, hh0, hgt⟩ := hy t
  have hX : ∏ k, y ⟨k, c k⟩ ^ d k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
  have hG : aeval y g / ∏ k, y ⟨k, c k⟩ ^ d k ∈ ratSat (chartRingZ y c) :=
    ⟨1, one_pos, by simpa using HilbertSamuel.ZeroCocycleSection.aeval_div_mem y c hg⟩
  have hH : aeval y h / ∏ k, y ⟨k, c k⟩ ^ d k ∈ ratSat (chartRingZ y c) :=
    ⟨1, one_pos, by simpa using HilbertSamuel.ZeroCocycleSection.aeval_div_mem y c hh⟩
  have hinv : (aeval y h / ∏ k, y ⟨k, c k⟩ ^ d k)⁻¹ ∈ ratSat (chartRingZ y c) :=
    Subalgebra.inv_mem_of_algebraic (A := ratSat (chartRingZ y c)) (x := ⟨_, hH⟩)
      (Algebra.IsAlgebraic.isAlgebraic _)
  have ht : t = (aeval y g / ∏ k, y ⟨k, c k⟩ ^ d k) * (aeval y h / ∏ k, y ⟨k, c k⟩ ^ d k)⁻¹ := by
    rw [hgt, inv_div, div_mul_div_comm, mul_comm (∏ k, y ⟨k, c k⟩ ^ d k), mul_assoc,
      mul_div_assoc, div_self (mul_ne_zero hh0 hX), mul_one]
  have := (ratSat (chartRingZ y c)).mul_mem hG hinv
  rw [← ht] at this
  exact this

end ChartLatFull

theorem ChartLatFull.proof : ChartLatFull.Statement := by
  intro K _ ι _ Ω _ _ y hy a τ s
  classical
  let t : (∀ k, ι k) → Ω := fun c => s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k))
  let N : (∀ k, ι k) → ℕ := fun c =>
    if hc : ∀ k, y ⟨k, c k⟩ ≠ 0 then (ChartLatFull.exists_nat_mul_mem hy c hc (t c)).choose else 1
  have hNpos : ∀ c, 0 < N c := by
    intro c
    simp only [N]
    split_ifs with hc
    · exact (ChartLatFull.exists_nat_mul_mem hy c hc (t c)).choose_spec.1
    · exact one_pos
  refine ⟨∏ c, N c, Finset.prod_pos fun c _ => hNpos c, ?_⟩
  show ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → _
  intro c hc
  have hN : (N c : Ω) * t c ∈ chartRingZ y c := by
    simp only [N, dif_pos hc]
    exact (ChartLatFull.exists_nat_mul_mem hy c hc (t c)).choose_spec.2
  obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem N (Finset.mem_univ c)
  have : ((∏ c, N c : ℕ) : Ω) * s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k)) = (m : Ω) * ((N c : Ω) * t c) := by
    rw [hm]; push_cast; simp only [t]; ring
  rw [this]
  exact (chartRingZ y c).mul_mem ((chartRingZ y c).natCast_mem m) hN

end

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveBoxCount
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.Inter

theorem CurveBoxCount.proof (hS : CurveBoxSmall.Statement) (hL : CurveBoxLattice.Statement) :
    CurveBoxCount.Statement := by
  intro K _ ι _ Ω _ y A c R hP hB hA hc hR hRu
  obtain ⟨C, hC⟩ := hL K ι Ω y A c R hP hB hA hc hR hRu
  refine ⟨C, fun τ hτ => ?_⟩
  have e : smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) τ =
      Real.log (Nat.card {s : chartLat y A.a τ //
        ∀ σ : Ω →+* ℂ, ‖σ ((s : Ω) / chartUnit y c A.a τ)‖ ≤ chartRadius A c (fun p => σ (y p)) ^ τ}) := by
    unfold smallSectionCount
    rw [Nat.card_congr (Equiv.subtypeEquivRight (p := fun s : chartLat y A.a τ => IsSmallH (mCoordIdeal y) y A τ (s : Ω))
      fun s => hS K ι Ω y A c hP hB hc τ (s : Ω))]
  rw [e]
  exact hC τ hτ

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveBoxLattice
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.Inter

section Lemmas

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [∀ k, Fintype (ι k)] in

theorem chartRadius_smul (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (c : ∀ k, ι k) (d : K → ℂ) (hd : ∀ k, d k ≠ 0)
    (z : (Σ k, ι k) → ℂ) : chartRadius A c (fun p => d p.1 * z p) = chartRadius A c z := by
  unfold chartRadius
  rw [A.smul d z hd]
  have hX : (∏ k, ‖d k‖ ^ A.a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hd k))
  simp only [norm_mul, mul_zpow, Finset.prod_mul_distrib]
  rw [mul_div_mul_left _ _ hX]

omit [∀ k, Fintype (ι k)] in

theorem chartRadius_conj (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (hA : IsConjInvariantH A) (c : ∀ k, ι k)
    (z : (Σ k, ι k) → ℂ) : chartRadius A c (fun p => (starRingEnd ℂ) (z p)) = chartRadius A c z := by
  unfold chartRadius
  rw [hA z]
  simp only [Complex.norm_conj]

omit [∀ k, Fintype (ι k)] in

theorem chartRadius_pos (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (c : ∀ k, ι k) (z : (Σ k, ι k) → ℂ)
    (hz : ∀ k, z ⟨k, c k⟩ ≠ 0) : 0 < chartRadius A c z :=
  div_pos (A.pos z fun k => ⟨c k, hz k⟩)
    (Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.mpr (hz k)) _)

end Lemmas

theorem genIndex_map_addEquiv {G : Type*} [AddCommGroup G] (m : G ≃+ G) (A B : AddSubgroup G) :
    genIndex (A.map m.toAddMonoidHom) (B.map m.toAddMonoidHom) = genIndex A B := by
  unfold genIndex
  rw [AddSubgroup.relIndex_map_map_of_injective _ _ m.injective,
    AddSubgroup.relIndex_map_map_of_injective _ _ m.injective]

theorem addSubgroup_fg_map {G H : Type*} [AddCommGroup G] [AddCommGroup H] {A : AddSubgroup G} (hA : A.FG)
    (f : G →+ H) : (A.map f).FG := by
  classical
  obtain ⟨S, hS⟩ := hA
  exact ⟨S.image f, by rw [Finset.coe_image, ← AddMonoidHom.map_closure, hS]⟩

theorem CurveBoxLattice.proof (hF : CurveFieldNumber.Statement) (hE : CurveEmbedOrbit.Statement)
    (hL : ChartLatFull.Statement) (hN : NumberFieldBoxCount.Statement)
    (hG : HilbertSamuel.SectionLatticeFinite.Statement) : CurveBoxLattice.Statement := by
  intro K _ ι _ Ω _ y A c R hP hB hA hc hR hRu
  have : NumberField Ω := hF K ι Ω y hP hB
  obtain ⟨e, he⟩ := hE K ι Ω y R hP hB hR hRu
  have hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := fun k => ⟨c k, hc k⟩
  have hBeq : (curveRing y).toAddSubgroup = chartLat y 0 0 := by
    ext s
    simp [mem_curveRing, chartLat]
  have hBfg : (curveRing y).toAddSubgroup.FG := hBeq ▸ hG K ι Ω y 0 0 hy
  have hBfull : ∀ x : Ω, ∃ n : ℕ, 0 < n ∧ (n : Ω) * x ∈ (curveRing y).toAddSubgroup :=
    hBeq ▸ hL K ι Ω y hB 0 0
  obtain ⟨C, hC⟩ := hN Ω _ hBfg hBfull
  refine ⟨C, fun τ _ => ?_⟩
  have hu : chartUnit y c A.a τ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)
  set u := chartUnit y c A.a τ with hu_def
  let m : Ω ≃+ Ω :=
    { toFun := fun x => x / u
      invFun := fun x => x * u
      left_inv := fun x => div_mul_cancel₀ x hu
      right_inv := fun x => mul_div_cancel_right₀ x hu
      map_add' := fun x z => add_div x z u }
  set Λ := (chartLat y A.a τ).map m.toAddMonoidHom with hΛ
  have hΛfg : Λ.FG := addSubgroup_fg_map (hG K ι Ω y A.a τ hy) _
  have hΛfull : ∀ x : Ω, ∃ n : ℕ, 0 < n ∧ (n : Ω) * x ∈ Λ := by
    intro x
    obtain ⟨n, hn, hmem⟩ := hL K ι Ω y hB A.a τ (x * u)
    refine ⟨n, hn, ?_⟩
    have : (n : Ω) * x = m ((n : Ω) * (x * u)) := by
      show (n : Ω) * x = (n : Ω) * (x * u) / u
      rw [mul_div_assoc, mul_div_cancel_right₀ x hu]
    rw [this]
    exact AddSubgroup.mem_map_of_mem _ hmem
  have hBmap : (curveMul y u).map m.toAddMonoidHom = (curveRing y).toAddSubgroup := by
    rw [curveMul, AddSubgroup.map_map]
    convert AddSubgroup.map_id _ using 2
    ext x
    show u * x / u = x
    rw [mul_div_cancel_left₀ x hu]
  have hidx : genIndex Λ (curveRing y).toAddSubgroup = genIndex (chartLat y A.a τ) (curveMul y u) := by
    rw [← hBmap, hΛ, genIndex_map_addEquiv]
  let ρ : (Ω →+* ℂ) → ℝ := fun σ => chartRadius A c (fun p => σ (y p)) ^ τ
  have hρpos : ∀ σ, 0 < ρ σ := fun σ =>
    pow_pos (chartRadius_pos A c _ fun k => (map_ne_zero σ).mpr (hc k)) τ
  have hρconj : ∀ σ, ρ (NumberField.ComplexEmbedding.conjugate σ) = ρ σ := by
    intro σ
    simp only [ρ, NumberField.ComplexEmbedding.conjugate_coe_eq]
    rw [chartRadius_conj A hA c]
  have hcount := hC Λ hΛfg hΛfull ρ hρpos hρconj
  have hsum : ∑ t ∈ R, Real.log (chartRadius A c t) =
      ∑ σ : Ω →+* ℂ, Real.log (chartRadius A c (fun p => σ (y p))) := by
    rw [← Finset.sum_coe_sort R, ← Equiv.sum_comp e]
    refine Finset.sum_congr rfl fun t _ => ?_
    obtain ⟨d, hd, ht⟩ := he t
    rw [ht, chartRadius_smul A c d hd]
  have hρsum : ∑ σ : Ω →+* ℂ, Real.log (ρ σ) =
      (τ : ℝ) * ∑ σ : Ω →+* ℂ, Real.log (chartRadius A c (fun p => σ (y p))) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun σ _ => Real.log_pow _ _
  have hcard : Nat.card {s : chartLat y A.a τ //
        ∀ σ : Ω →+* ℂ, ‖σ ((s : Ω) / u)‖ ≤ chartRadius A c (fun p => σ (y p)) ^ τ} =
      Nat.card {x : Λ // ∀ σ : Ω →+* ℂ, ‖σ (x : Ω)‖ ≤ ρ σ} :=
    Nat.card_congr ((AddSubgroup.equivMapOfInjective _ m.toAddMonoidHom m.injective).toEquiv.subtypeEquiv
      fun s => Iff.rfl)
  rw [hcard, hsum, ← hρsum, chartIndexLog, ← hu_def, ← hidx]
  exact hcount

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveBoxSmall
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.Inter

theorem CurveBoxSmall.zpow_mul_toNat_neg {F : Type} [Field F] {t : F} (ht : t ≠ 0) (n : ℤ) :
    t ^ n * t ^ (-n).toNat = t ^ n.toNat :=
  calc t ^ n * t ^ (-n).toNat = t ^ ((n.toNat : ℤ) - ((-n).toNat : ℤ)) * t ^ (-n).toNat := by
        rw [Int.toNat_sub_toNat_neg]
    _ = t ^ n.toNat := by
        rw [zpow_sub₀ ht, zpow_natCast, zpow_natCast, div_mul_cancel₀ _ (pow_ne_zero _ ht)]

theorem CurveBoxSmall.proof : CurveBoxSmall.Statement := by
  intro K _ ι _ Ω _ y A c hP hB hc τ s
  classical
  have hU : ∀ σ : Ω →+* ℂ, ‖σ (chartUnit y c A.a τ)‖ = (∏ k, ‖σ (y ⟨k, c k⟩)‖ ^ A.a k) ^ τ := fun σ => by
    rw [chartUnit, map_prod, norm_prod, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [map_zpow₀, norm_zpow, ← zpow_natCast (_ ^ A.a k), ← zpow_mul, mul_comm (A.a k)]
  have hQ : ∀ σ : Ω →+* ℂ, 0 < (∏ k, ‖σ (y ⟨k, c k⟩)‖ ^ A.a k) ^ τ := fun σ =>
    pow_pos (Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.mpr ((map_ne_zero σ).mpr (hc k))) _) _
  constructor
  · intro hS σ
    obtain ⟨d, g, h, hg, hh, hh0, hgh⟩ := hB (s / chartUnit y c A.a τ)
    let ap : K → ℕ := fun k => ((τ : ℤ) * A.a k).toNat
    let am : K → ℕ := fun k => (-((τ : ℤ) * A.a k)).toNat
    have hU0 : chartUnit y c A.a τ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)
    have hu : chartUnit y c A.a τ * ∏ k, y ⟨k, c k⟩ ^ am k = ∏ k, y ⟨k, c k⟩ ^ ap k := by
      rw [chartUnit, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun k _ => CurveBoxSmall.zpow_mul_toNat_neg (hc k) _
    have hdeg : ∀ k, (((d + ap) k : ℕ) : ℤ) = ((d + am) k : ℕ) + τ * A.a k := fun k => by
      have := Int.toNat_sub_toNat_neg ((τ : ℤ) * A.a k)
      simp only [Pi.add_apply, Nat.cast_add, ap, am]
      omega
    have hval : aeval y (g * curveChartMono c ap) = s * aeval y (h * curveChartMono c am) := by
      simp only [map_mul, curveChartMono, map_prod, map_pow, aeval_X]
      rw [← hu, hgh]
      field_simp
    have hS' := hS _ _ _ _ _ (CurveOrbit.isMultiHomog_mul hg (isMultiHomog_curveChartMono c ap))
      (CurveOrbit.isMultiHomog_mul hh (isMultiHomog_curveChartMono c am)) hdeg hval (CurveOrbit.mem_mcPts σ y hc)
    rw [CurveOrbit.eval_comp, CurveOrbit.eval_comp] at hS'
    simp only [map_mul, curveChartMono, map_prod, map_pow, aeval_X, norm_mul, norm_prod, norm_pow] at hS'
    have hsu : s / chartUnit y c A.a τ = aeval y g / aeval y h := eq_div_of_mul_eq hh0 hgh.symm
    have hσh : 0 < ‖σ (aeval y h)‖ := norm_pos_iff.mpr ((map_ne_zero σ).mpr hh0)
    have ht : ∀ k, ‖σ (y ⟨k, c k⟩)‖ ≠ 0 := fun k => norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr (hc k))
    have hR : (∏ k, ‖σ (y ⟨k, c k⟩)‖ ^ A.a k) ^ τ * ∏ k, ‖σ (y ⟨k, c k⟩)‖ ^ am k =
        ∏ k, ‖σ (y ⟨k, c k⟩)‖ ^ ap k := by
      rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← zpow_natCast (_ ^ A.a k), ← zpow_mul, mul_comm (A.a k)]
      exact CurveBoxSmall.zpow_mul_toNat_neg (ht k) _
    have hRm : 0 < ∏ k, ‖σ (y ⟨k, c k⟩)‖ ^ am k :=
      Finset.prod_pos fun k _ => pow_pos (lt_of_le_of_ne (norm_nonneg _) (ht k).symm) _
    rw [hsu, map_div₀, norm_div, chartRadius, div_pow, div_le_div_iff₀ hσh (hQ σ)]
    refine le_of_mul_le_mul_right ?_ hRm
    calc ‖σ (aeval y g)‖ * (∏ k, ‖σ (y ⟨k, c k⟩)‖ ^ A.a k) ^ τ * ∏ k, ‖σ (y ⟨k, c k⟩)‖ ^ am k
        = ‖σ (aeval y g)‖ * ∏ k, ‖σ (y ⟨k, c k⟩)‖ ^ ap k := by rw [mul_assoc, hR]
      _ ≤ ‖σ (aeval y h)‖ * (∏ k, ‖σ (y ⟨k, c k⟩)‖ ^ am k) * A.h (fun p => σ (y p)) ^ τ := hS'
      _ = _ := by ring
  · intro hbox dg dh g h z hg hh hdeg hgs hz
    obtain ⟨σ, l, hl, rfl⟩ := CurveOrbit.exists_sameOrbit hP hB hz
    beta_reduce
    have hb := hbox σ
    rw [map_div₀, norm_div, chartRadius, div_pow, hU σ, div_le_div_iff_of_pos_right (hQ σ)] at hb
    have hlam : ‖∏ k, l k ^ dg k‖ = ‖∏ k, l k ^ dh k‖ * (∏ k, ‖l k‖ ^ A.a k) ^ τ := by
      rw [norm_prod, norm_prod, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      have hlk : ‖l k‖ ≠ 0 := norm_ne_zero_iff.mpr (hl k)
      rw [norm_pow, norm_pow, ← zpow_natCast (‖l k‖) (dg k), hdeg k, zpow_add₀ hlk, zpow_natCast,
        ← zpow_natCast (_ ^ A.a k), ← zpow_mul, mul_comm (A.a k)]
    rw [CurveOrbit.eval_smul _ l hg, CurveOrbit.eval_smul _ l hh, A.smul l _ hl, CurveOrbit.eval_comp,
      CurveOrbit.eval_comp, hgs, map_mul, norm_mul, norm_mul, norm_mul, hlam, mul_pow]
    calc ‖∏ k, l k ^ dh k‖ * (∏ k, ‖l k‖ ^ A.a k) ^ τ * (‖σ s‖ * ‖σ (aeval y h)‖)
        = (‖∏ k, l k ^ dh k‖ * (∏ k, ‖l k‖ ^ A.a k) ^ τ * ‖σ (aeval y h)‖) * ‖σ s‖ := by ring
      _ ≤ (‖∏ k, l k ^ dh k‖ * (∏ k, ‖l k‖ ^ A.a k) ^ τ * ‖σ (aeval y h)‖) * A.h (fun p => σ (y p)) ^ τ :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      _ = _ := by ring

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveClosedPointChart
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

set_option linter.unusedSectionVars false

noncomputable section

namespace CurveClosedPointChartAlt

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  [CharZero Ω] (y : (Σ k, ι k) → Ω) (f : ∀ k, ι k)

abbrev fld : IntermediateField ℚ Ω :=
  CoordinateConeArithVar.ratioField (SegreChart.segre y) (fun _ ↦ f)

def pt : (Σ _ : Unit, ∀ k, ι k) → fld y f :=
  CoordinateConeArithVar.ratioPtL (SegreChart.segre y) (fun _ ↦ f)

theorem coe_pt (q : Σ _ : Unit, ∀ k, ι k) :
    ((pt y f q : fld y f) : Ω) = SegreChart.segre y q / SegreChart.segre y ⟨(), f⟩ := rfl

variable {y f}

theorem numberField (hP : IsArithVar (mCoordIdeal y) 1) (hf : ∀ k, y ⟨k, f k⟩ ≠ 0) : NumberField (fld y f) := by
  have : Finite (coneRatios (SegreChart.segre y) fun _ ↦ f) := (Set.finite_range _).to_subtype
  have : FiniteDimensional ℚ (fld y f) := IntermediateField.finiteDimensional_adjoin (by
    rintro _ ⟨⟨⟨⟩, g⟩, rfl⟩
    exact (SegreChart.isAlgebraic_segre_ratio hP f hf g).isIntegral)
  exact {}

theorem isArithVar_pt (hP : IsArithVar (mCoordIdeal y) 1) (hf : ∀ k, y ⟨k, f k⟩ ≠ 0) :
    IsArithVar (mCoordIdeal (pt y f)) 1 := by
  rw [pt, CoordinateConeArithVar.mCoordIdeal_ratioPtL _ _ fun _ ↦ (SegreChart.segre_ne_zero_iff y f).mpr hf]
  exact SegreChart.isArithVar_segre hP f hf

theorem pt_ne_zero_iff (hf : ∀ k, y ⟨k, f k⟩ ≠ 0) (g : ∀ k, ι k) :
    pt y f ⟨(), g⟩ ≠ 0 ↔ ∀ k, y ⟨k, g k⟩ ≠ 0 := by
  rw [← SegreChart.segre_ne_zero_iff, ne_eq, ← ZeroMemClass.coe_eq_zero, coe_pt, div_eq_zero_iff, not_or,
    and_iff_left ((SegreChart.segre_ne_zero_iff y f).mpr hf)]

theorem coe_pt_ratio (hf : ∀ k, y ⟨k, f k⟩ ≠ 0) (g h : ∀ k, ι k) :
    ((pt y f ⟨(), h⟩ / pt y f ⟨(), g⟩ : fld y f) : Ω) =
      SegreChart.segre y ⟨(), h⟩ / SegreChart.segre y ⟨(), g⟩ := by
  rw [IntermediateField.coe_div, coe_pt, coe_pt,
    div_div_div_cancel_right₀ ((SegreChart.segre_ne_zero_iff y f).mpr hf)]

theorem map_chartRingZ (hf : ∀ k, y ⟨k, f k⟩ ≠ 0) (g : ∀ k, ι k) (hg : ∀ k, y ⟨k, g k⟩ ≠ 0) :
    (chartRingZ (pt y f) (fun _ ↦ g)).map (algebraMap (fld y f) Ω).toIntAlgHom = chartRingZ y g := by
  rw [chartRingZ, ← Algebra.adjoin_image, ← Set.range_comp, ← SegreChart.chartRingZ_segre y g hg, chartRingZ]
  congr 2
  funext q
  obtain ⟨⟨⟩, h⟩ := q
  exact coe_pt_ratio hf g h

theorem mem_chartRingZ_iff (hf : ∀ k, y ⟨k, f k⟩ ≠ 0) (g : ∀ k, ι k) (hg : ∀ k, y ⟨k, g k⟩ ≠ 0)
    (x : fld y f) : x ∈ chartRingZ (pt y f) (fun _ ↦ g) ↔ (x : Ω) ∈ chartRingZ y g := by
  rw [← map_chartRingZ hf g hg, Subalgebra.mem_map]
  refine ⟨fun h ↦ ⟨x, h, rfl⟩, ?_⟩
  rintro ⟨x', hx', he⟩
  rwa [show x' = x from Subtype.ext he] at hx'

theorem mem_curveRing_iff (hf : ∀ k, y ⟨k, f k⟩ ≠ 0) (x : fld y f) :
    x ∈ curveRing (pt y f) ↔ (x : Ω) ∈ curveRing y := by
  rw [mem_curveRing, mem_curveRing]
  refine ⟨fun h g hg ↦ (mem_chartRingZ_iff hf g hg x).1 (h _ fun _ ↦ (pt_ne_zero_iff hf g).2 hg),
    fun h c hc ↦ ?_⟩
  have hc' := (pt_ne_zero_iff hf (c ())).1 (hc ())
  exact (mem_chartRingZ_iff hf (c ()) hc' x).2 (h _ hc')

theorem exists_of_mem_curveRing (hf : ∀ k, y ⟨k, f k⟩ ≠ 0) {b : Ω} (hb : b ∈ curveRing y) :
    ∃ x : fld y f, (x : Ω) = b := by
  have h := mem_curveRing.mp hb f hf
  rw [← map_chartRingZ hf f hf, Subalgebra.mem_map] at h
  obtain ⟨x, -, hx⟩ := h
  exact ⟨x, hx⟩

end CurveClosedPointChartAlt

open CurveClosedPointChartAlt in

theorem CurveClosedPointChart.proof : CurveClosedPointChart.Statement := by
  classical
  intro K _ ι _ Ω _ y hP m hm
  have := SegreChart.charZero_of_isArithVar hP
  obtain ⟨f, hf⟩ := SegreChart.exists_chart hP
  have := numberField hP hf
  let φ : curveRing (pt y f) →+* curveRing y :=
    RingHom.codRestrict ((algebraMap (fld y f) Ω).comp (curveRing (pt y f)).subtype) (curveRing y)
      fun x ↦ (mem_curveRing_iff hf x).1 x.2
  have hφ : Function.Surjective φ := by
    rintro ⟨b, hb⟩
    obtain ⟨x, rfl⟩ := exists_of_mem_curveRing hf hb
    exact ⟨⟨x, (mem_curveRing_iff hf x).2 hb⟩, rfl⟩
  have hm' : (m.comap φ).IsMaximal := Ideal.comap_isMaximal_of_surjective φ hφ
  obtain ⟨t, ht, hrat⟩ := ClosedPointChart.proof ClosedPointUnitSection.proof (∀ k, ι k) (fld y f) (pt y f)
    (isArithVar_pt hP hf) (m.comap φ) hm'
  have hyt := (pt_ne_zero_iff hf t).1 ht
  refine ⟨t, hyt, fun p ↦ ?_⟩
  obtain ⟨a, b, hb, hab⟩ := hrat (Function.update t p.1 p.2)
  refine ⟨φ a, φ b, hb, ?_⟩
  have h1 := congrArg (fun x : fld y f ↦ (x : Ω)) hab
  simp only [IntermediateField.coe_mul] at h1
  rw [coe_pt_ratio hf, SegreChart.segre_ratio, SegreChart.prod_ratio_update y t hyt p] at h1
  exact h1

end

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StChartDehomIdeal
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomogIdeal IsMultiProjPrime PBlk)
open GroundTheory.Heights₂.Heights (segreChartIdeal)

def ChartDehomIdeal.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (m : ℕ)
    (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k),
    IsMultiHomogIdeal P →
      segreChartIdeal P σ i =
        (((P.map (MvPolynomial.map (Int.castRingHom ℂ))).map (dehom i)).radical).comap (segreDehom σ i)

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StConeRingLaurent
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial

def ConeRingLaurent.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) (i : (k : K) → ι k),
    (ratioMap i).Flat ∧ ∀ 𝔮 : Ideal (DehomRing i), 𝔮.IsPrime → (𝔮.map (ratioMap i)).IsPrime

def evalOnesDehom {K : Type} [Fintype K] {ι : K → Type} (i : (k : K) → ι k) : DehomRing i →+* ℂ :=
  Ideal.Quotient.lift (dehomIdeal i) (eval fun _ => (1 : ℂ)) (by
    have hle : dehomIdeal i ≤ RingHom.ker (eval fun _ => (1 : ℂ) : MvPolynomial (Σ k, ι k) ℂ →+* ℂ) := by
      rw [dehomIdeal, Ideal.span_le]
      rintro _ ⟨k, rfl⟩
      simp
    exact fun a ha => hle ha)

end GroundTheory.Heights₂.Heights.Targets
end
end

