import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0011
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.LocalizeBundleSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.LocalizeSubvarSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0018

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PGraphClosedLocal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

namespace GraphClosedAlt

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem chartRing_subset_ampleChart (H : SubSystem S x Ω) (h : Ω) (I : Chart x) {a : Ω}
    (ha : a ∈ chartRing S x I) : a ∈ ampleChart H 1 h I := by
  refine ⟨0, ?_⟩
  rw [pow_zero, mul_one, mul_zero]
  change a ∈ twistMod S x 0 I
  obtain ⟨i, hi⟩ := I.2.1
  rw [twistMod_eq_span 0 I hi, zpow_zero]
  have : a = (⟨a, ha⟩ : chartRing S x I) • (1 : Ω) := by rw [chartRing_smul_def, mul_one]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)

theorem ampleChart_mul (H : SubSystem S x Ω) (h : Ω) (I : Chart x) {a b : Ω}
    (ha : a ∈ ampleChart H 1 h I) (hb : b ∈ ampleChart H 1 h I) : a * b ∈ ampleChart H 1 h I := by
  obtain ⟨n, hn⟩ := ha
  obtain ⟨m, hm⟩ := hb
  refine ⟨n + m, ?_⟩
  rw [one_mul] at hn hm ⊢
  rw [SubSystem.pow_sub] at hn hm ⊢
  rw [pow_add, pow_add]
  have : a * b * (h ^ n * h ^ m) = (a * h ^ n) * (b * h ^ m) := by ring
  rw [this]
  exact Submodule.mul_mem_mul hn hm

theorem ampleChart_pow (H : SubSystem S x Ω) (h : Ω) (I : Chart x) {a : Ω}
    (ha : a ∈ ampleChart H 1 h I) (e : ℕ) : a ^ e ∈ ampleChart H 1 h I := by
  induction e with
  | zero => rw [pow_zero]; exact chartRing_subset_ampleChart H h I (one_mem _)
  | succ e ih => rw [pow_succ]; exact ampleChart_mul H h I ih ha

def chartUnion (I J : Chart x) : Chart x :=
  ⟨I.1 ∪ J.1, I.2.1.mono Finset.subset_union_left, Finset.union_subset I.2.2 J.2.2⟩

theorem xProd_ne_zero (I : Chart x) : xProd I ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ hi => (mem_support x).mp (I.2.2 hi)

theorem div_mem_chartRing (I : Chart x) (j : Fin (N + 1)) {i : Fin (N + 1)} (hi : i ∈ I.1) :
    x j / x i ∈ chartRing S x I :=
  ⟨X j, X i, 1, X_mem_monos hi, isHomogeneous_X S j, isHomogeneous_X S i, by simp⟩

theorem exists_pow_mul_ratio_mem (I J : Chart x) {i₀ : Fin (N + 1)} (hi₀ : i₀ ∈ I.1)
    {i : Fin (N + 1)} (hi : i ∈ I.1 ∪ J.1) : ∃ e : ℕ,
    (xProd J ^ I.1.card / xProd I ^ J.1.card) ^ e * (x i₀ / x i) ∈ chartRing S x I := by
  by_cases hiI : i ∈ I.1
  · exact ⟨0, by rw [pow_zero, one_mul]; exact div_mem_chartRing I i₀ hiI⟩
  have hiJ : i ∈ J.1 := (Finset.mem_union.mp hi).resolve_left hiI
  refine ⟨1, ?_⟩
  have hw : x i₀ ≠ 0 := (mem_support x).mp (I.2.2 hi₀)
  have hxi : x i ≠ 0 := (mem_support x).mp (J.2.2 hiJ)
  have hQ : xProd I ≠ 0 := xProd_ne_zero I
  obtain ⟨m, hm⟩ : ∃ m, I.1.card = m + 1 := ⟨I.1.card - 1, (Nat.succ_pred_eq_of_pos I.2.1.card_pos).symm⟩
  obtain ⟨c, hc⟩ : ∃ c, J.1.card = c + 1 := ⟨J.1.card - 1, (Nat.succ_pred_eq_of_pos J.2.1.card_pos).symm⟩
  have hce : (J.1.erase i).card = c := by rw [Finset.card_erase_of_mem hiJ, hc]; rfl
  set P := ∏ j ∈ J.1.erase i, x j with hP
  have hJP : xProd J = x i * P := (Finset.mul_prod_erase J.1 x hiJ).symm
  have hprodI : ∏ i' ∈ I.1, (x i₀ / x i') = x i₀ ^ (m + 1) / xProd I := by
    rw [Finset.prod_div_distrib, Finset.prod_const, hm]; rfl
  have hprodJ : ∏ j ∈ J.1.erase i, (x j / x i₀) = P / x i₀ ^ c := by
    rw [Finset.prod_div_distrib, Finset.prod_const, hce]
  have key : (xProd J ^ I.1.card / xProd I ^ J.1.card) ^ 1 * (x i₀ / x i) =
      (x i / x i₀) ^ m * (∏ j ∈ J.1.erase i, (x j / x i₀)) ^ (m + 1) *
        (∏ i' ∈ I.1, (x i₀ / x i')) ^ (c + 1) := by
    rw [hprodI, hprodJ, hJP, hm, hc, pow_one]
    simp only [div_pow, mul_pow, ← pow_mul]
    field_simp
    ring
  rw [key]
  refine mul_mem (mul_mem (pow_mem (div_mem_chartRing I i hi₀) m)
    (pow_mem (prod_mem fun j _ => div_mem_chartRing I j hi₀) _))
    (pow_mem (prod_mem fun i' hi' => div_mem_chartRing I i₀ hi') _)

theorem exists_pow_mul_mem_chartRing (I J : Chart x) {z : Ω}
    (hz : z ∈ chartRing S x (chartUnion I J)) : ∃ e : ℕ,
    (xProd J ^ I.1.card / xProd I ^ J.1.card) ^ e * z ∈ chartRing S x I := by
  set σ := xProd J ^ I.1.card / xProd I ^ J.1.card
  obtain ⟨i₀, hi₀⟩ := I.2.1
  have hw : x i₀ ≠ 0 := (mem_support x).mp (I.2.2 hi₀)
  have hmon : ∀ s ∈ monos (S := S) (I.1 ∪ J.1), ∃ (e d : ℕ), s.IsHomogeneous d ∧
      σ ^ e * (x i₀ ^ d / aeval x s) ∈ chartRing S x I := by
    intro s hs
    induction hs using Submonoid.closure_induction with
    | mem a ha =>
      obtain ⟨i, hi, rfl⟩ := ha
      obtain ⟨e, he⟩ := exists_pow_mul_ratio_mem (S := S) I J hi₀ (i := i) (by exact_mod_cast hi)
      exact ⟨e, 1, isHomogeneous_X S i, by rw [pow_one, aeval_X]; exact he⟩
    | one => exact ⟨0, 0, isHomogeneous_one _ _, by simp⟩
    | mul a b _ _ ha hb =>
      obtain ⟨e₁, d₁, had, hae⟩ := ha
      obtain ⟨e₂, d₂, hbd, hbe⟩ := hb
      refine ⟨e₁ + e₂, d₁ + d₂, had.mul hbd, ?_⟩
      have : σ ^ (e₁ + e₂) * (x i₀ ^ (d₁ + d₂) / aeval x (a * b)) =
          (σ ^ e₁ * (x i₀ ^ d₁ / aeval x a)) * (σ ^ e₂ * (x i₀ ^ d₂ / aeval x b)) := by
        rw [map_mul, pow_add, pow_add]; ring
      rw [this]
      exact mul_mem hae hbe
  obtain ⟨f, s, d, hs, hf, hsd, rfl⟩ := hz
  obtain ⟨e, d', hsd', hmem⟩ := hmon s hs
  have hs0 : aeval x s ≠ 0 := eval_ne_zero_of_mem_monos (chartUnion I J) hs
  have hsne : s ≠ 0 := fun h => hs0 (by rw [h, map_zero])
  have hdd : d' = d := hsd'.inj_right hsd hsne
  subst hdd
  have hf' : aeval x f / x i₀ ^ d' ∈ chartRing S x I :=
    ⟨f, X i₀ ^ d', d', pow_mem (X_mem_monos hi₀) d', hf, isHomogeneous_X_pow i₀ d', by simp⟩
  refine ⟨e, ?_⟩
  have : σ ^ e * (aeval x f / aeval x s) = (aeval x f / x i₀ ^ d') * (σ ^ e * (x i₀ ^ d' / aeval x s)) := by
    field_simp
  rw [this]
  exact mul_mem hf' hmem

theorem exists_pow_mul_mem_ampleRing (H : SubSystem S x Ω) (h b : Ω) (J : Chart x)
    (hb : b ∈ ampleRing H 1 h)
    (hbJ : ∀ I : Chart x, ∃ e : ℕ,
      b ^ e * (xProd I ^ J.1.card / xProd J ^ I.1.card) ∈ ampleChart H 1 h I)
    {c : Ω} (hc : c ∈ chartRing S x J) : ∃ e : ℕ, b ^ e * c ∈ ampleRing H 1 h := by
  classical
  have hloc : ∀ I : Chart x, ∃ e : ℕ, b ^ e * c ∈ ampleChart H 1 h I := by
    intro I
    obtain ⟨e₀, he₀⟩ := hbJ I
    have hcU : c ∈ chartRing S x (chartUnion I J) := chartRing_mono Finset.subset_union_right hc
    obtain ⟨e₁, he₁⟩ := exists_pow_mul_mem_chartRing I J hcU
    refine ⟨e₀ * e₁, ?_⟩
    have hρσ : (xProd I ^ J.1.card / xProd J ^ I.1.card) *
        (xProd J ^ I.1.card / xProd I ^ J.1.card) = 1 := by
      have := xProd_ne_zero I
      have := xProd_ne_zero J
      field_simp
    have : b ^ (e₀ * e₁) * c = (b ^ e₀ * (xProd I ^ J.1.card / xProd J ^ I.1.card)) ^ e₁ *
        ((xProd J ^ I.1.card / xProd I ^ J.1.card) ^ e₁ * c) := by
      calc b ^ (e₀ * e₁) * c = (b ^ e₀) ^ e₁ * ((xProd I ^ J.1.card / xProd J ^ I.1.card) *
          (xProd J ^ I.1.card / xProd I ^ J.1.card)) ^ e₁ * c := by
            rw [hρσ, one_pow, mul_one, pow_mul]
        _ = _ := by ring
    rw [this]
    exact ampleChart_mul H h I (ampleChart_pow H h I he₀ e₁)
      (chartRing_subset_ampleChart H h I he₁)
  choose f hf using hloc
  refine ⟨∑ I, f I, Set.mem_iInter.mpr fun I => ?_⟩
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le
    (Finset.single_le_sum (fun I _ => Nat.zero_le (f I)) (Finset.mem_univ I))
  have : b ^ (f I + k) * c = (b ^ f I * c) * b ^ k := by ring
  rw [hk, this]
  exact ampleChart_mul H h I (hf I) (ampleChart_pow H h I (Set.mem_iInter.mp hb I) k)

end GraphClosedAlt

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PInterNumPoint
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

section InterNumPointLemmas

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}

theorem interNumPoint_restrLen_eq_finrank (y : Fin (N + 1) → Ω) {j : Fin (N + 1)} (hyj : y j ≠ 0)
    (F : SubSystem k y Ω) : restrLen (primeOf (S := k) y) F = Module.finrank k F.secs := by
  have hid : ∀ I : Chart y, idealMod (x := y) (primeOf (S := k) y) I = ⊥ := by
    intro I
    refine Submodule.span_eq_bot.mpr ?_
    rintro _ ⟨f, s, e, hf, _, hfe, _, rfl⟩
    rw [(mem_primeOf_of_isHomogeneous y hfe).mp hf, zero_div]
  have hbot : ∀ I : Chart y, (F.twist (idealSys y (primeOf (S := k) y))).sub I = ⊥ := by
    intro I
    refine Submodule.span_eq_bot.mpr ?_
    rintro _ ⟨q, hq, z, _, rfl⟩
    have hq' : q ∈ idealMod (x := y) (primeOf (S := k) y) I := hq
    rw [hid I, Submodule.mem_bot] at hq'
    rw [hq', zero_smul]
  have hsecs : (F.twist (idealSys y (primeOf (S := k) y))).secs = ⊥ := by
    refine eq_bot_iff.mpr fun z hz => ?_
    have h1 := (Submodule.mem_iInf _).mp hz (singleChart hyj)
    rw [Submodule.restrictScalars_mem, hbot] at h1
    exact h1
  unfold restrLen
  rw [hsecs, Submodule.comap_bot, Submodule.ker_subtype,
    (Submodule.quotEquivOfEqBot (⊥ : Submodule k F.secs) rfl).length_eq, Module.length_eq_rank]
  rfl

theorem interNumPoint_interSum_eq (y : Fin (N + 1) → Ω) {j : Fin (N + 1)} (hyj : y j ≠ 0)
    (L : Fin 0 → SubSystem k y Ω) (c : ℕ) :
    interSum (primeOf (S := k) y) L c = Module.finrank k (twistSys k y (c : ℤ)).secs := by
  have huniv : (Finset.univ : Finset (Finset (Fin 0))) = {∅} := by decide
  have h0 : tensorSub L ∅ = twistSys k y 0 := rfl
  rw [interSum, huniv, Finset.sum_singleton, h0, twistSys_zero_twist,
    interNumPoint_restrLen_eq_finrank y hyj]
  simp

end InterNumPointLemmas

theorem InterNumPoint.proof (hHP : HilbertPoint.Statement.{u, w}) : InterNumPoint.Statement.{u, w} := by
  intro k _ Ω _ _ N y hsub L
  obtain ⟨_, hdim, hsecs⟩ := hHP k Ω N y hsub
  obtain ⟨j, hj⟩ := hsub.relevant
  have hyj : y j ≠ 0 := by
    intro h
    apply hj
    rw [mem_primeOf_of_isHomogeneous y (isHomogeneous_X k j), aeval_X]
    exact h
  have hev : (fun _ : ℕ => (Module.finrank k (funField (k := k) y) : ℤ)) =ᶠ[atTop]
      interSum (primeOf (S := k) y) L := by
    filter_upwards [hdim, hsecs] with n hn hs
    rw [interNumPoint_interSum_eq y hyj, hs, hn]
  exact (tendsto_const_nhds.congr' hev).limUnder_eq

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PLocalizeBundle
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial

noncomputable section

universe u u' w

section BaseChange

variable {S : Type u} [CommRing S] {O : Type u'} [CommRing O] [Algebra S O]
  {Ω : Type w} [Field Ω] [Algebra S Ω] [Algebra O Ω] [IsScalarTower S O Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem map_mem_monos_base {I : Finset (Fin (N + 1))} {s : Poly S N} (hs : s ∈ monos I) :
    map (algebraMap S O) s ∈ monos (S := O) I := by
  induction hs using Submonoid.closure_induction with
  | mem a ha =>
    obtain ⟨i, hi, rfl⟩ := ha
    rw [map_X]
    exact Submonoid.subset_closure ⟨i, hi, rfl⟩
  | one => rw [map_one]; exact one_mem _
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb

theorem mem_chartRing_base {I : Chart x} {a : Ω} (ha : a ∈ chartRing S x I) :
    a ∈ chartRing O x I := by
  obtain ⟨f, s, e, hs, hf, hse, rfl⟩ := ha
  exact ⟨map (algebraMap S O) f, map (algebraMap S O) s, e, map_mem_monos_base hs, hf.map _,
    hse.map _, by rw [aeval_map_algebraMap, aeval_map_algebraMap]⟩

theorem smul_mem_span_base {I : Chart x} (P : Set Ω) (a : chartRing S x I) {y : Ω}
    (hy : y ∈ Submodule.span (chartRing O x I) P) : a • y ∈ Submodule.span (chartRing O x I) P := by
  have : a • y = (⟨(a : Ω), mem_chartRing_base a.2⟩ : chartRing O x I) • y := by
    rw [chartRing_smul_def, chartRing_smul_def]
  rw [this]
  exact Submodule.smul_mem _ _ hy

theorem span_base_span (I : Chart x) (P : Set Ω) :
    Submodule.span (chartRing O x I) (Submodule.span (chartRing S x I) P : Set Ω) =
      Submodule.span (chartRing O x I) P := by
  apply le_antisymm
  · refine Submodule.span_le.mpr fun y hy => ?_
    refine Submodule.span_induction
      (p := fun y _ => y ∈ Submodule.span (chartRing O x I) P) ?_ ?_ ?_ ?_ hy
    · intro z hz; exact Submodule.subset_span hz
    · exact Submodule.zero_mem _
    · intro a b _ _ ha hb; exact Submodule.add_mem _ ha hb
    · intro a z _ hz; exact smul_mem_span_base P a hz
  · exact Submodule.span_mono Submodule.subset_span

theorem isUnit_base {I J : Chart x} (h : I.1 ⊆ J.1) {a : chartRing S x I}
    (ha : IsUnit (chartIncl h a)) :
    IsUnit (chartIncl h (⟨(a : Ω), mem_chartRing_base a.2⟩ : chartRing O x I)) := by
  obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp ha
  refine isUnit_iff_exists_inv.mpr ⟨⟨(v : Ω), mem_chartRing_base v.2⟩, Subtype.ext ?_⟩
  have := congrArg Subtype.val hv
  change (a : Ω) * (v : Ω) = 1 at this
  change (a : Ω) * (v : Ω) = 1
  exact this

theorem LocalizeBundle.mem_iff_baseChange (M : LineBundle S x) (I J : Chart x) (h : I.1 ⊆ J.1)
    (y : Ω) :
    y ∈ (M.toSubSystem.baseChange O).sub J ↔
      ∃ a : chartRing O x I, IsUnit (chartIncl h a) ∧
        (a : Ω) • y ∈ (M.toSubSystem.baseChange O).sub I := by
  constructor
  · intro hy
    change y ∈ Submodule.span (chartRing O x J) (M.sub J : Set Ω) at hy
    let T : Submodule (chartRing O x J) Ω :=
      { carrier := {y | ∃ a : chartRing O x I, IsUnit (chartIncl h a) ∧
          (a : Ω) • y ∈ Submodule.span (chartRing O x I) (M.sub I : Set Ω)}
        add_mem' := by
          rintro y₁ y₂ ⟨a₁, ha₁, h₁⟩ ⟨a₂, ha₂, h₂⟩
          refine ⟨a₁ * a₂, by rw [map_mul]; exact ha₁.mul ha₂, ?_⟩
          have : ((a₁ * a₂ : chartRing O x I) : Ω) • (y₁ + y₂) =
              a₂ • ((a₁ : Ω) • y₁) + a₁ • ((a₂ : Ω) • y₂) := by
            change (a₁ : Ω) * a₂ * (y₁ + y₂) = (a₂ : Ω) * ((a₁ : Ω) * y₁) + (a₁ : Ω) * ((a₂ : Ω) * y₂)
            ring
          rw [this]
          exact Submodule.add_mem _ (Submodule.smul_mem _ _ h₁) (Submodule.smul_mem _ _ h₂)
        zero_mem' := ⟨1, by rw [map_one]; exact isUnit_one, by
          rw [smul_zero]; exact Submodule.zero_mem _⟩
        smul_mem' := by
          rintro b y ⟨a, ha, hay⟩
          obtain ⟨c, hc, hcb⟩ := exists_isUnit_mul_mem (S := O) h b
          refine ⟨c * a, by rw [map_mul]; exact hc.mul ha, ?_⟩
          have : ((c * a : chartRing O x I) : Ω) • (b • y) =
              (⟨(c : Ω) * b, hcb⟩ : chartRing O x I) • ((a : Ω) • y) := by
            change (c : Ω) * a * ((b : Ω) * y) = (c : Ω) * b * ((a : Ω) * y)
            ring
          rw [this]
          exact Submodule.smul_mem _ _ hay }
    have hle : Submodule.span (chartRing O x J) (M.sub J : Set Ω) ≤ T := by
      refine Submodule.span_le.mpr fun m hm => ?_
      obtain ⟨a, ha, ham⟩ := (M.mem_iff I J h m).mp hm
      exact ⟨⟨(a : Ω), mem_chartRing_base a.2⟩, isUnit_base h ha, Submodule.subset_span ham⟩
    exact hle hy
  · rintro ⟨a, ⟨u, hu⟩, hay⟩
    have hJ := (M.toSubSystem.baseChange O).mono I J h _ hay
    have hinv : ((↑u⁻¹ : chartRing O x J) : Ω) * (a : Ω) = 1 := by
      have := congrArg Subtype.val (Units.inv_mul u)
      rw [hu] at this
      exact this
    have hy : y = (↑u⁻¹ : chartRing O x J) • ((a : Ω) • y) := by
      rw [chartRing_smul_def, smul_eq_mul, ← mul_assoc, hinv, one_mul]
    rw [hy]
    exact Submodule.smul_mem _ _ hJ

theorem LocalizeBundle.fg_baseChange (M : LineBundle S x) (I : Chart x) :
    ((M.toSubSystem.baseChange O).sub I).FG := by
  obtain ⟨s, hs⟩ := M.fg I
  refine ⟨s, ?_⟩
  change Submodule.span (chartRing O x I) (s : Set Ω) =
    Submodule.span (chartRing O x I) (M.sub I : Set Ω)
  rw [← hs, span_base_span]

theorem LocalizeBundle.invertible_baseChange (M : LineBundle S x) (I : Chart x) :
    ∃ Q' : Submodule (chartRing O x I) Ω, (M.toSubSystem.baseChange O).sub I * Q' = 1 := by
  obtain ⟨Q', hQ⟩ := M.invertible I
  refine ⟨Submodule.span (chartRing O x I) (Q' : Set Ω), ?_⟩
  change Submodule.span (chartRing O x I) (M.sub I : Set Ω) *
    Submodule.span (chartRing O x I) (Q' : Set Ω) = 1
  rw [Submodule.span_mul_span, ← span_base_span (S := S) (O := O) I,
    ← Submodule.mul_eq_span_mul_set, hQ, Submodule.one_eq_span (R := chartRing S x I),
    span_base_span]
  exact (Submodule.one_eq_span).symm

def LocalizeBundle.lineBundleBaseChange (M : LineBundle S x) : LineBundle O x :=
  { M.toSubSystem.baseChange O with
    mem_iff := LocalizeBundle.mem_iff_baseChange M
    fg := LocalizeBundle.fg_baseChange M
    invertible := LocalizeBundle.invertible_baseChange M }

end BaseChange

theorem LocalizeBundle.proof : LocalizeBundle.Statement := by
  intro S _ 𝔪 _ O _ _ _ Ω _ _ _ _ N x M
  exact ⟨LocalizeBundle.lineBundleBaseChange M, rfl⟩

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PLocalizeSubvar
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial

theorem LocalizeSubvar.homogeneousComponent_map {R A σ : Type*} [CommSemiring R] [CommSemiring A]
    (f : R →+* A) (d : ℕ) (g : MvPolynomial σ R) :
    homogeneousComponent d (map f g) = map f (homogeneousComponent d g) := by
  ext m
  simp only [coeff_homogeneousComponent, coeff_map]
  split_ifs <;> simp

theorem LocalizeSubvar.quotientMap_surjective (S : Type) [CommRing S] (𝔪 : Ideal S) [𝔪.IsMaximal]
    (O : Type) [CommRing O] [Algebra S O] [IsLocalization.AtPrime O 𝔪] (N : ℕ)
    (pp' : Ideal (Kleiman.Poly O N))
    (hle : (𝔪.map (algebraMap S O)).map (C : O →+* Kleiman.Poly O N) ≤ pp') :
    Function.Surjective (Ideal.quotientMap pp'
      (MvPolynomial.map (algebraMap S O) : Kleiman.Poly S N →+* Kleiman.Poly O N) le_rfl) := by
  set φ := Ideal.quotientMap pp'
    (MvPolynomial.map (algebraMap S O) : Kleiman.Poly S N →+* Kleiman.Poly O N) le_rfl with hφ
  have key : ∀ q : Kleiman.Poly O N, Ideal.Quotient.mk pp' q ∈ φ.range := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C o =>
      obtain ⟨⟨s, t⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔪.primeCompl o
      obtain ⟨y, i, hi, hyi⟩ := Ideal.IsMaximal.exists_inv (inferInstance : 𝔪.IsMaximal) t.2
      refine ⟨Ideal.Quotient.mk _ (C (s * y)), ?_⟩
      rw [Ideal.quotientMap_mk, map_C, Ideal.Quotient.eq]
      set v : O := IsLocalization.mk' O (1 : S) t
      have h1 : algebraMap S O t * v = 1 := by rw [IsLocalization.mk'_spec', map_one]
      have h2 : algebraMap S O y * algebraMap S O t + algebraMap S O i = 1 := by
        rw [← map_mul, ← map_add, hyi, map_one]
      have ho : IsLocalization.mk' O s t = algebraMap S O s * v := IsLocalization.mk'_eq_mul_mk'_one s t
      have hd : algebraMap S O (s * y) - IsLocalization.mk' O s t =
          -(algebraMap S O i * (algebraMap S O s * v)) := by
        rw [ho, map_mul]
        linear_combination (-(algebraMap S O y * algebraMap S O s)) * h1 +
          (algebraMap S O s * v) * h2
      rw [← map_sub, hd, map_neg, map_mul]
      refine neg_mem (Ideal.mul_mem_right _ _ (hle ?_))
      exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hi)
    | add p q hp hq => rw [map_add]; exact Subring.add_mem _ hp hq
    | mul_X p j hp =>
      rw [map_mul]
      refine Subring.mul_mem _ hp ⟨Ideal.Quotient.mk _ (X j), ?_⟩
      rw [Ideal.quotientMap_mk, map_X]
  intro z
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact key q

theorem LocalizeSubvar.proof : LocalizeSubvar.Statement := by
  intro S _ 𝔪 _ O _ _ _ Ω _ _ _ _ N x pp' e hle h
  have := h.isPrime
  refine
    { isPrime := Ideal.comap_isPrime _ _
      homog := ?_
      le := ?_
      relevant := ?_
      dim := ?_ }
  · intro g hg d
    rw [Ideal.mem_comap, ← LocalizeSubvar.homogeneousComponent_map]
    exact h.homog _ hg d
  · intro g hg
    rw [Kleiman.primeOf_eq, RingHom.mem_ker] at hg
    rw [Ideal.mem_comap]
    apply h.le
    rw [Kleiman.primeOf_eq, RingHom.mem_ker, Kleiman.cone_eq, Kleiman.coneGen, aeval_map_algebraMap]
    rw [Kleiman.cone_eq, Kleiman.coneGen] at hg
    exact hg
  · obtain ⟨i, hi⟩ := h.relevant
    exact ⟨i, by rw [Ideal.mem_comap, map_X]; exact hi⟩
  · rw [← h.dim]
    exact ringKrullDim_eq_of_ringEquiv (RingEquiv.ofBijective _
      ⟨Ideal.quotientMap_injective, LocalizeSubvar.quotientMap_surjective S 𝔪 O N pp' hle⟩)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTwistAlg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

theorem twistMul_twist_twistMul {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
    {x : Fin (N + 1) → Ω} (M : SubSystem S x Ω) (a a' : ℕ) (c c' : ℤ) :
    (twistMul M a c).twist (twistMul M a' c') = twistMul M (a + a') (c + c') := by
  refine SubSystem.ext_sub fun I => ?_
  rw [SubSystem.twist_sub_eq_mul_of_line, twistMul_sub, twistMul_sub, twistMul_sub, pow_add,
    ← twistSys_sub_mul]
  ring

theorem TwistAlg.proof : TwistAlg.Statement.{u, w} := by
  intro S _ Ω _ _ N x M p q m m' b₁ b₂ h
  rw [pow_twistMul, pow_twistMul, pow_twistMul, twistMul_twist_twistMul]
  congr 1
  · ring
  · push_cast
    linear_combination (b₁ : ℤ) * h

end

end GroundTheory.Heights₂.Heights.Kleiman
end

