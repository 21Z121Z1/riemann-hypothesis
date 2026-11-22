import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.UnfoldAbs

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.HenselCountHolds
section
noncomputable section

namespace PI.VolStabW

open MeasureTheory Topology

section Hensel

variable {V X : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [BorelSpace V] [AddCommGroup X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [MeasurableSpace X] [BorelSpace X]

def hlev (Λ0 : AddSubgroup V) (H : AddSubgroup X) (G : V → X) (y : V) (h : X) : Set V :=
  {Z | Z ∈ Λ0 ∧ G (y + Z) - h ∈ H}

theorem hensel_main (μ : Measure V) (ν : Measure X) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    (Λ : ℕ → AddSubgroup V) (H : ℕ → AddSubgroup X) (hΛo : ∀ n, IsOpen (Λ n : Set V))
    (hΛa : Antitone Λ) (hHo : ∀ n, IsOpen (H n : Set X)) (hHc : ∀ n, IsCompact (H n : Set X))
    (D : V →+ X) (hD : ∀ n, (Λ n).map D = H n) (G : V → X) (y : V)
    (hG : ∀ n, ∀ Z ∈ Λ 0, ∀ W ∈ Λ n, G (y + Z + W) - G (y + Z) - D W ∈ H (n + 1))
    (h : X) (hh : h - G y ∈ H 0) (n : ℕ) :
    μ (hlev (Λ 0) (H n) G y h) * ν (H 0) = μ (Λ 0) * ν (H n) := by
  have hHa : ∀ n, H (n + 1) ≤ H n := by
    intro n
    rw [← hD, ← hD]
    exact AddSubgroup.map_mono (hΛa (Nat.le_succ n))
  have hDW : ∀ n W, W ∈ Λ n → D W ∈ H n := fun n W hW => hD n ▸ AddSubgroup.mem_map_of_mem D hW
  have hΛ0 : ∀ n W, W ∈ Λ n → W ∈ Λ 0 := fun n W hW => hΛa (Nat.zero_le n) hW

  have hopen : ∀ m h', IsOpen (hlev (Λ 0) (H m) G y h') := by
    intro m h'
    rw [isOpen_iff_forall_mem_open]
    rintro Z ⟨hZ0, hZh⟩
    refine ⟨{x | x - Z ∈ Λ m}, ?_, (hΛo m).preimage (continuous_id.sub continuous_const),
      by simp [(Λ m).zero_mem]⟩
    intro x hx
    have hx : x - Z ∈ Λ m := hx
    have hx' : x = Z + (x - Z) := by abel
    refine ⟨?_, ?_⟩
    · rw [hx']
      exact (Λ 0).add_mem hZ0 (hΛ0 m _ hx)
    · have h1 := hG m Z hZ0 (x - Z) hx
      have h2 := hDW m _ hx
      have e : G (y + x) - h' = (G (y + Z + (x - Z)) - G (y + Z) - D (x - Z)) + D (x - Z) +
          (G (y + Z) - h') := by
        rw [show y + Z + (x - Z) = y + x by abel]
        abel
      rw [e]
      exact (H m).add_mem ((H m).add_mem (hHa m h1) h2) hZh

  have htr : ∀ n h' W, W ∈ Λ n →
      μ (hlev (Λ 0) (H (n + 1)) G y (h' + D W)) = μ (hlev (Λ 0) (H (n + 1)) G y h') := by
    intro n h' W hW
    have hW0 := hΛ0 n W hW
    have e : hlev (Λ 0) (H (n + 1)) G y (h' + D W) =
        (fun Z => -W + Z) ⁻¹' hlev (Λ 0) (H (n + 1)) G y h' := by
      ext Z
      simp only [hlev, Set.mem_preimage, Set.mem_setOf_eq]
      constructor
      · rintro ⟨hZ, hZh⟩
        have hZ' : -W + Z ∈ Λ 0 := (Λ 0).add_mem ((Λ 0).neg_mem hW0) hZ
        refine ⟨hZ', ?_⟩
        have h1 := hG n (-W + Z) hZ' W hW
        rw [show y + (-W + Z) + W = y + Z by abel] at h1
        have e2 : G (y + (-W + Z)) - h' =
            (G (y + Z) - (h' + D W)) - (G (y + Z) - G (y + (-W + Z)) - D W) := by abel
        rw [e2]
        exact (H (n + 1)).sub_mem hZh h1
      · rintro ⟨hZ', hZh⟩
        have hZ : Z ∈ Λ 0 := by
          have := (Λ 0).add_mem hW0 hZ'
          rwa [add_neg_cancel_left] at this
        refine ⟨hZ, ?_⟩
        have h1 := hG n (-W + Z) hZ' W hW
        rw [show y + (-W + Z) + W = y + Z by abel] at h1
        have e2 : G (y + Z) - (h' + D W) =
            (G (y + Z) - G (y + (-W + Z)) - D W) + (G (y + (-W + Z)) - h') := by abel
        rw [e2]
        exact (H (n + 1)).add_mem h1 hZh
    rw [e, measure_preimage_add]

  have hstep : ∀ n, ∃ k : ℕ, k ≠ 0 ∧
      μ (hlev (Λ 0) (H n) G y h) = k * μ (hlev (Λ 0) (H (n + 1)) G y h) ∧
      ν (H n) = k * ν (H (n + 1)) := by
    intro n
    have : DiscreteTopology (X ⧸ H (n + 1)) := QuotientAddGroup.discreteTopology (hHo (n + 1))
    let q : X → X ⧸ H (n + 1) := QuotientAddGroup.mk
    have hq : Continuous q := continuous_quot_mk
    have hfin : (q '' (H n : Set X)).Finite := ((hHc n).image hq).finite_of_discrete
    set T := hfin.toFinset with hT
    have hqeq : ∀ a b, q a = q b ↔ a - b ∈ H (n + 1) := fun a b => QuotientAddGroup.eq_iff_sub_mem
    have hmemT : ∀ p, p ∈ T ↔ ∃ u ∈ H n, q u = p := by
      intro p
      simp [hT, q]
    let piece : X ⧸ H (n + 1) → Set V := fun p => {Z | Z ∈ Λ 0 ∧ q (G (y + Z) - h) = p}
    have hpiece : ∀ u, piece (q u) = hlev (Λ 0) (H (n + 1)) G y (h + u) := by
      intro u
      ext Z
      simp only [piece, hlev, Set.mem_setOf_eq, hqeq, sub_sub]
    have hA : hlev (Λ 0) (H n) G y h = ⋃ p ∈ T, piece p := by
      ext Z
      simp only [Set.mem_iUnion, exists_prop]
      constructor
      · rintro ⟨hZ, hZh⟩
        exact ⟨q (G (y + Z) - h), (hmemT _).2 ⟨_, hZh, rfl⟩, hZ, rfl⟩
      · rintro ⟨p, hp, hZ, hZp⟩
        obtain ⟨u, hu, rfl⟩ := (hmemT p).1 hp
        refine ⟨hZ, ?_⟩
        have h1 := (hqeq _ _).1 hZp
        have e : G (y + Z) - h = (G (y + Z) - h - u) + u := by abel
        rw [e]
        exact (H n).add_mem (hHa n h1) hu
    have hdisj : Set.PairwiseDisjoint (↑T : Set (X ⧸ H (n + 1))) piece := by
      intro p _ p' _ hne
      refine Set.disjoint_left.2 fun Z hZ hZ' => hne ?_
      exact hZ.2.symm.trans hZ'.2
    have hmeasP : ∀ p ∈ T, MeasurableSet (piece p) := by
      intro p hp
      obtain ⟨u, _, rfl⟩ := (hmemT p).1 hp
      rw [hpiece]
      exact (hopen _ _).measurableSet
    have hvalP : ∀ p ∈ T, μ (piece p) = μ (hlev (Λ 0) (H (n + 1)) G y h) := by
      intro p hp
      obtain ⟨u, hu, rfl⟩ := (hmemT p).1 hp
      rw [hpiece]
      rw [← hD n] at hu
      obtain ⟨W, hW, rfl⟩ := AddSubgroup.mem_map.1 hu
      exact htr n h W hW
    have hH : (H n : Set X) = ⋃ p ∈ T, q ⁻¹' {p} := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff, exists_prop]
      constructor
      · intro hx
        exact ⟨q x, (hmemT _).2 ⟨x, hx, rfl⟩, rfl⟩
      · rintro ⟨p, hp, hxp⟩
        obtain ⟨u, hu, rfl⟩ := (hmemT p).1 hp
        have h1 := (hqeq _ _).1 hxp
        have e : x = (x - u) + u := by abel
        rw [e]
        exact (H n).add_mem (hHa n h1) hu
    have hdisjH : Set.PairwiseDisjoint (↑T : Set (X ⧸ H (n + 1))) (fun p => q ⁻¹' {p}) :=
      fun p _ p' _ hne => (Set.disjoint_singleton.2 hne).preimage q
    have hmeasH : ∀ p ∈ T, MeasurableSet (q ⁻¹' {p}) := fun p _ =>
      ((isOpen_discrete ({p} : Set (X ⧸ H (n + 1)))).preimage hq).measurableSet
    have hvalH : ∀ p ∈ T, ν (q ⁻¹' {p}) = ν (H (n + 1)) := by
      intro p hp
      obtain ⟨u, _, rfl⟩ := (hmemT p).1 hp
      have e : q ⁻¹' {q u} = (fun z => -u + z) ⁻¹' (H (n + 1) : Set X) := by
        ext z
        simp only [Set.mem_preimage, Set.mem_singleton_iff, hqeq, SetLike.mem_coe]
        rw [show z - u = -u + z by abel]
      rw [e, measure_preimage_add]
    refine ⟨T.card, ?_, ?_, ?_⟩
    · refine Finset.card_ne_zero.2 ⟨q 0, (hmemT _).2 ⟨0, (H n).zero_mem, rfl⟩⟩
    · rw [hA, measure_biUnion_finset hdisj hmeasP, Finset.sum_congr rfl hvalP, Finset.sum_const,
        nsmul_eq_mul]
    · rw [hH, measure_biUnion_finset hdisjH hmeasH, Finset.sum_congr rfl hvalH, Finset.sum_const,
        nsmul_eq_mul]
  induction n with
  | zero =>
    have e : hlev (Λ 0) (H 0) G y h = (Λ 0 : Set V) := by
      ext Z
      simp only [hlev, Set.mem_setOf_eq, SetLike.mem_coe, and_iff_left_iff_imp]
      intro hZ
      have h1 := hG 0 0 (Λ 0).zero_mem Z hZ
      simp only [add_zero] at h1
      have e2 : G (y + Z) - h = (G (y + Z) - G y - D Z) + D Z - (h - G y) := by abel
      rw [e2]
      exact (H 0).sub_mem ((H 0).add_mem (hHa 0 h1) (hDW 0 Z hZ)) hh
    rw [e, mul_comm]
  | succ n ih =>
    obtain ⟨k, hk, hμ, hν⟩ := hstep n
    have hk0 : (k : ENNReal) ≠ 0 := Nat.cast_ne_zero.2 hk
    have key : (k : ENNReal) * (μ (hlev (Λ 0) (H (n + 1)) G y h) * ν (H 0)) =
        k * (μ (Λ 0) * ν (H (n + 1))) := by
      rw [← mul_assoc, ← hμ, ih, hν]
      ring
    exact (ENNReal.mul_right_inj hk0 (ENNReal.natCast_ne_top k)).1 key

end Hensel

theorem henselCount_holds : HenselCount := by
  intro V X _ _ _ _ _ _ _ _ _ _ μ ν hμ hν Λ H hΛo _ hΛa hHo hHc D hD G y hG n h hh
  exact hensel_main μ ν Λ H hΛo hΛa hHo hHc D hD G y hG h hh n

end PI.VolStabW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.LintFibre
section
noncomputable section

namespace PI.VolStabW

open MeasureTheory Set
open scoped ENNReal Pointwise

section Abs2

variable {G Y : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableInv G]
  [MulAction G Y]

theorem lint_fibre {Γ H : Subgroup G} [Countable Γ] (μ' : Measure H) [μ'.IsMulLeftInvariant]
    [μ'.IsInvInvariant] (y0 : Y) (hH : ∀ k : G, k ∈ H ↔ k • y0 = y0) [Countable (orbS Γ y0)]
    {A : Set G} (hA : MeasurableSet A)
    (𝓕' : Set H) (h𝓕' : IsFundamentalDomain ((Γ ⊓ H).subgroupOf H) 𝓕' μ')
    (ρ : G → ℝ≥0∞) (hρ : Measurable ρ) (hρi : ∀ γ ∈ Γ, ∀ g, ρ (γ * g) = ρ g) (s : G) :
    ∫⁻ k, cfun Γ A y0 (s * (k : G)) * ρ ((s * (k : G))⁻¹) ∂μ' =
      ∫⁻ k in 𝓕', cntN Γ A ((k : G) * s⁻¹) * ρ ((k : G) * s⁻¹) ∂μ' := by
  haveI : Countable ((Γ ⊓ H).subgroupOf H) := countable_subgroupOf
  have memΓ : ∀ δ : (Γ ⊓ H).subgroupOf H, ((δ : H) : G) ∈ Γ := fun δ =>
    (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 δ.2)).1
  have h1 : ∀ (δ : (Γ ⊓ H).subgroupOf H) (k : H),
      cfun Γ A y0 (s * (((δ • k)⁻¹ : H) : G)) * ρ ((s * (((δ • k)⁻¹ : H) : G))⁻¹) =
        (∑' x : orbS Γ y0, A.indicator (fun _ => (1 : ℝ≥0∞))
          (repO Γ y0 x * ((δ : H) : G) * ((k : G) * s⁻¹))) * ρ ((k : G) * s⁻¹) := by
    intro δ k
    have e : (((δ • k)⁻¹ : H) : G) = (k : G)⁻¹ * ((δ : H) : G)⁻¹ := by
      show ((((δ : H) * k)⁻¹ : H) : G) = _
      rw [Subgroup.coe_inv, Subgroup.coe_mul, mul_inv_rev]
    rw [e]
    have eρ : ρ ((s * ((k : G)⁻¹ * ((δ : H) : G)⁻¹))⁻¹) = ρ ((k : G) * s⁻¹) := by
      rw [show (s * ((k : G)⁻¹ * ((δ : H) : G)⁻¹))⁻¹ = ((δ : H) : G) * ((k : G) * s⁻¹) by group]
      exact hρi _ (memΓ δ) _
    rw [eρ]
    congr 1
    unfold cfun
    refine tsum_congr fun x => ?_
    congr 1
    group
  have hm : ∀ δ : (Γ ⊓ H).subgroupOf H, Measurable fun k : H =>
      (∑' x : orbS Γ y0, A.indicator (fun _ => (1 : ℝ≥0∞))
          (repO Γ y0 x * ((δ : H) : G) * ((k : G) * s⁻¹))) * ρ ((k : G) * s⁻¹) := fun δ =>
    (Measurable.ennreal_tsum fun _ => (measurable_const.indicator hA).comp
      ((measurable_const_mul _).comp ((measurable_mul_const _).comp measurable_subtype_coe))).mul
      (hρ.comp ((measurable_mul_const _).comp measurable_subtype_coe))
  calc ∫⁻ k, cfun Γ A y0 (s * (k : G)) * ρ ((s * (k : G))⁻¹) ∂μ'
      = ∫⁻ k, cfun Γ A y0 (s * ((k⁻¹ : H) : G)) * ρ ((s * ((k⁻¹ : H) : G))⁻¹) ∂μ' :=
        (lintegral_inv_eq_self
          (fun k : H => cfun Γ A y0 (s * (k : G)) * ρ ((s * (k : G))⁻¹))).symm
    _ = ∑' δ : (Γ ⊓ H).subgroupOf H, ∫⁻ k in 𝓕',
          cfun Γ A y0 (s * (((δ • k)⁻¹ : H) : G)) * ρ ((s * (((δ • k)⁻¹ : H) : G))⁻¹) ∂μ' :=
        h𝓕'.lintegral_eq_tsum'' _
    _ = ∑' δ : (Γ ⊓ H).subgroupOf H, ∫⁻ k in 𝓕',
          (∑' x : orbS Γ y0, A.indicator (fun _ => (1 : ℝ≥0∞))
            (repO Γ y0 x * ((δ : H) : G) * ((k : G) * s⁻¹))) * ρ ((k : G) * s⁻¹) ∂μ' :=
        tsum_congr fun δ => lintegral_congr fun k => h1 δ k
    _ = ∫⁻ k in 𝓕', ∑' δ : (Γ ⊓ H).subgroupOf H,
          (∑' x : orbS Γ y0, A.indicator (fun _ => (1 : ℝ≥0∞))
            (repO Γ y0 x * ((δ : H) : G) * ((k : G) * s⁻¹))) * ρ ((k : G) * s⁻¹) ∂μ' :=
        (lintegral_tsum fun δ => (hm δ).aemeasurable).symm
    _ = ∫⁻ k in 𝓕', cntN Γ A ((k : G) * s⁻¹) * ρ ((k : G) * s⁻¹) ∂μ' := by
        refine lintegral_congr fun k => ?_
        rw [ENNReal.tsum_mul_right, ENNReal.tsum_comm]
        congr 1
        exact sum_rep_eq y0 hH (fun g => A.indicator (fun _ => (1 : ℝ≥0∞)) (g * ((k : G) * s⁻¹)))

end Abs2

end PI.VolStabW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.LocDensChLift
section
noncomputable section

open NumberField Complex

namespace PI.VolStabW

namespace ChLiftW

theorem int_valued_zero {Y : Type*} [TopologicalSpace Y] [PreconnectedSpace Y] (ψ : Y → ℝ)
    (hψ : Continuous ψ) (hint : ∀ p, ∃ n : ℤ, ψ p = n) (a : Y) (ha : ψ a = 0) (p : Y) :
    ψ p = 0 := by
  obtain ⟨n, hn⟩ := hint p
  have key : ∀ t : ℝ, t ∈ Set.uIcc (0 : ℝ) (n : ℝ) → ∃ m : ℤ, t = m := by
    intro t ht
    rcases le_total (0 : ℝ) n with h | h
    · rw [Set.uIcc_of_le h] at ht
      obtain ⟨q, hq⟩ := intermediate_value_univ a p hψ (by rw [ha, hn]; exact ht)
      obtain ⟨m, hm⟩ := hint q
      exact ⟨m, by rw [← hq, hm]⟩
    · rw [Set.uIcc_of_ge h] at ht
      obtain ⟨q, hq⟩ := intermediate_value_univ p a hψ (by rw [ha, hn]; exact ht)
      obtain ⟨m, hm⟩ := hint q
      exact ⟨m, by rw [← hq, hm]⟩
  rw [hn]
  by_contra hne
  have hn0 : n ≠ 0 := fun h => hne (by simp [h])
  rcases lt_or_gt_of_ne hn0 with h | h
  · have hn1 : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
    obtain ⟨m, hm⟩ := key (-1 / 2) (by
      rw [Set.uIcc_of_ge (by linarith)]
      constructor <;> linarith)
    have h2 : ((2 * m : ℤ) : ℝ) = -1 := by push_cast; linarith
    have h3 : 2 * m = -1 := by exact_mod_cast h2
    omega
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    obtain ⟨m, hm⟩ := key (1 / 2) (by
      rw [Set.uIcc_of_le (by linarith)]
      constructor <;> linarith)
    have h2 : ((2 * m : ℤ) : ℝ) = 1 := by push_cast; linarith
    have h3 : 2 * m = 1 := by exact_mod_cast h2
    omega

theorem lift_normed {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] (χ : W → ℂ)
    (hc : Continuous χ) (hadd : ∀ x y, χ (x + y) = χ x * χ y) (h0 : χ 0 = 1) :
    ∃ ℓ : W →+ ℂ, Continuous ℓ ∧ ∀ x, χ x = exp (ℓ x) := by
  have hne : ∀ x, χ x ≠ 0 := fun x h => by
    have := hadd x (-x)
    rw [add_neg_cancel, h0, h, zero_mul] at this
    exact one_ne_zero this
  let f : C(W, {z : ℂ // z ≠ 0}) := ⟨fun x => ⟨χ x, hne x⟩, hc.subtype_mk _⟩
  obtain ⟨g, ⟨hg0, hgl⟩, -⟩ := Complex.isCoveringMap_exp.existsUnique_continuousMap_lifts f 0 0
    (by ext; simp [f, h0])
  have hge : ∀ x, exp (g x) = χ x := fun x => congrArg Subtype.val (congrFun hgl x)
  have h2 : (2 * Real.pi * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  let D : W × W → ℂ := fun p => g (p.1 + p.2) - g p.1 - g p.2
  have hDc : Continuous D := by
    have := g.continuous
    fun_prop
  have hDint : ∀ p, ∃ n : ℤ, D p = n * (2 * Real.pi * I) := fun p => by
    rw [← Complex.exp_eq_one_iff]
    simp only [D, Complex.exp_sub, hge, hadd]
    field_simp [hne p.1, hne p.2]
  let ψ : W × W → ℝ := fun p => (D p / (2 * Real.pi * I)).re
  have hψint : ∀ p, ∃ n : ℤ, ψ p = n := fun p => by
    obtain ⟨n, hn⟩ := hDint p
    refine ⟨n, ?_⟩
    simp only [ψ, hn, mul_div_assoc, div_self h2, mul_one]
    simp
  have hψ : ∀ p, D p = ψ p * (2 * Real.pi * I) := fun p => by
    obtain ⟨n, hn⟩ := hDint p
    have : ψ p = n := by simp only [ψ, hn, mul_div_assoc, div_self h2, mul_one]; simp
    rw [this, hn]; push_cast; ring
  have hψc : Continuous ψ := by
    simp only [ψ]
    fun_prop
  have hψ0 : ψ (0, 0) = 0 := by simp [ψ, D, hg0]
  have hD0 : ∀ p, D p = 0 := fun p => by
    rw [hψ p, int_valued_zero ψ hψc hψint (0, 0) hψ0 p]; simp
  refine ⟨{ toFun := g, map_zero' := hg0, map_add' := fun x y => ?_ }, g.continuous,
    fun x => (hge x).symm⟩
  have := hD0 (x, y)
  simp only [D] at this
  linear_combination this

theorem lift_homeo {X W : Type*} [AddCommGroup X] [TopologicalSpace X] [NormedAddCommGroup W]
    [NormedSpace ℝ W] (e : X ≃ₜ W) (he : ∀ x y, e (x + y) = e x + e y) (χ : X → ℂ)
    (hc : Continuous χ) (hadd : ∀ x y, χ (x + y) = χ x * χ y) (h0 : χ 0 = 1) :
    ∃ ℓ : X →+ ℂ, Continuous ℓ ∧ ∀ x, χ x = exp (ℓ x) := by
  have hes : ∀ a b, e.symm (a + b) = e.symm a + e.symm b := fun a b => by
    apply e.injective
    rw [he]; simp
  have he0 : e.symm 0 = 0 := by
    have := hes 0 0
    rw [add_zero] at this
    exact left_eq_add.mp this
  obtain ⟨ℓ', hℓc, hℓ⟩ := lift_normed (χ ∘ e.symm) (hc.comp e.symm.continuous)
    (fun a b => by simp only [Function.comp, hes, hadd]) (by simp [he0, h0])
  refine ⟨ℓ'.comp (AddMonoidHom.mk' e he), hℓc.comp e.continuous, fun x => ?_⟩
  have := hℓ (e x)
  simpa using this

theorem lift_place {F : Type} [Field F] (v : InfinitePlace F) (χ : v.Completion → ℂ)
    (hc : Continuous χ) (hadd : ∀ x y, χ (x + y) = χ x * χ y) (h0 : χ 0 = 1) :
    ∃ ℓ : v.Completion →+ ℂ, Continuous ℓ ∧ ∀ x, χ x = exp (ℓ x) := by
  by_cases hv : v.IsReal
  · exact lift_homeo (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).toHomeomorph
      (fun x y => (InfinitePlace.Completion.ringEquivRealOfIsReal hv).map_add x y) χ hc hadd h0
  · have hv' : v.IsComplex := InfinitePlace.not_isReal_iff_isComplex.1 hv
    exact lift_homeo (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv').toHomeomorph
      (fun x y => (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv').map_add x y) χ hc hadd h0

theorem addChar_sum {ι A : Type*} [AddCommMonoid A] (χ : AddChar A ℂ) (s : Finset ι) (f : ι → A) :
    χ (∑ i ∈ s, f i) = ∏ i ∈ s, χ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [AddChar.map_zero_eq_one]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

end ChLiftW

open Classical in

def sgl {F : Type} [Field F] (v : InfinitePlace F) (t : v.Completion) : InfiniteAdeleRing F :=
  Pi.single v t

open Classical in
theorem sgl_add {F : Type} [Field F] (v : InfinitePlace F) (x y : v.Completion) :
    sgl v (x + y) = sgl v x + sgl v y :=
  Pi.single_add v x y

open Classical in
theorem sgl_zero {F : Type} [Field F] (v : InfinitePlace F) : sgl v (0 : v.Completion) = 0 :=
  Pi.single_zero v

open Classical in
theorem continuous_sgl {F : Type} [Field F] (v : InfinitePlace F) : Continuous (sgl v) :=
  continuous_single (A := fun w : InfinitePlace F => w.Completion) v

open Classical in
theorem sum_sgl {F : Type} [Field F] [NumberField F] (x : InfiniteAdeleRing F) :
    ∑ v, sgl v (x v) = x :=
  Finset.univ_sum_single (M := fun w : InfinitePlace F => w.Completion) x

open ChLiftW in
theorem chLift_holds : ChLift := by
  intro F _ _ χ hχ
  have hloc : ∀ v : InfinitePlace F, ∃ ℓ : v.Completion →+ ℂ, Continuous ℓ ∧
      ∀ t, χ (sgl v t) = exp (ℓ t) := fun v =>
    lift_place v (fun t => χ (sgl v t)) (hχ.comp (continuous_sgl v))
      (fun x y => by simp only [sgl_add, AddChar.map_add_eq_mul])
      (by simp only [sgl_zero, AddChar.map_zero_eq_one])
  choose ℓv hℓc hℓ using hloc
  let ℓ : InfiniteAdeleRing F →+ ℂ := AddMonoidHom.mk' (fun x => ∑ v, ℓv v (x v)) (fun a b => by
    show ∑ v, ℓv v (a v + b v) = _
    simp [map_add, Finset.sum_add_distrib])
  refine ⟨ℓ, ?_, fun x => ?_⟩
  · show Continuous (fun x : InfiniteAdeleRing F => ∑ v, ℓv v (x v))
    exact continuous_finsetSum _ fun v _ => (hℓc v).comp (continuous_apply v)
  · conv_lhs => rw [← sum_sgl x]
    rw [addChar_sum]
    show _ = exp (∑ v, ℓv v (x v))
    rw [Complex.exp_sum]
    exact Finset.prod_congr rfl fun v _ => hℓ v (x v)

end PI.VolStabW
end
end

