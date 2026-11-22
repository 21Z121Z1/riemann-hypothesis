import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0063
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ChartRingOverOneBlockEqChartRing
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0058
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0062
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0052
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0057
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0018

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SpanSecsMemLocInSelf
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver)

noncomputable section

section Local

variable {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω]

theorem spanSecs_mem_locIn_self {A : Subalgebra F Ω} {p : Ideal A} [hp : p.IsPrime] {a : Ω} (ha : a ∈ A) :
    a ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn A p :=
  mem_locIn.mpr ⟨⟨a, ha⟩, 1, one_not_mem_of_prime hp, by simp⟩

theorem spanSecs_mul_step {B : Subalgebra F Ω} {q : Ideal B} [hq : q.IsPrime] {T : Set Ω} {u g : Ω}
    (hg : g ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn B q) (hu : ∃ b : B, b ∉ q ∧ (b : Ω) * u ∈ Submodule.span B T) :
    ∃ b : B, b ∉ q ∧ (b : Ω) * (g * u) ∈ Submodule.span B T := by
  obtain ⟨b, hb, hbu⟩ := hu
  obtain ⟨a, b', hb', rfl⟩ := mem_locIn.mp hg
  refine ⟨b' * b, fun h => (hq.mem_or_mem h).elim hb' hb, ?_⟩
  have h0 := coe_ne_zero_of_not_mem hb'
  have e : ((b' * b : B) : Ω) * ((a : Ω) / b' * u) = a • ((b : Ω) * u) := by
    rw [Subalgebra.smul_def, smul_eq_mul, Subalgebra.coe_mul]
    field_simp
  rw [e]
  exact Submodule.smul_mem _ _ hbu

theorem spanSecs_exists_mul_mem (B C : Subalgebra F Ω) (q : Ideal B) [hq : q.IsPrime]
    (hC : ∀ a ∈ C, a ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn B q) (T : Set Ω) {u : Ω} (hu : u ∈ Submodule.span C T) :
    ∃ b : B, b ∉ q ∧ (b : Ω) * u ∈ Submodule.span B T := by
  induction hu using Submodule.span_induction with
  | mem z hz => exact ⟨1, one_not_mem_of_prime hq, by simpa using Submodule.subset_span hz⟩
  | zero => exact ⟨1, one_not_mem_of_prime hq, by simp⟩
  | add z w _ _ hz hw =>
    obtain ⟨b₁, hb₁, h₁⟩ := hz
    obtain ⟨b₂, hb₂, h₂⟩ := hw
    refine ⟨b₁ * b₂, fun h => (hq.mem_or_mem h).elim hb₁ hb₂, ?_⟩
    have e : ((b₁ * b₂ : B) : Ω) * (z + w) = b₂ • ((b₁ : Ω) * z) + b₁ • ((b₂ : Ω) * w) := by
      rw [Subalgebra.smul_def, Subalgebra.smul_def, smul_eq_mul, smul_eq_mul, Subalgebra.coe_mul]
      ring
    rw [e]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ h₁) (Submodule.smul_mem _ _ h₂)
  | smul a z _ hz =>
    rw [Subalgebra.smul_def, smul_eq_mul]
    exact spanSecs_mul_step (hC _ a.2) hz

theorem spanSecs_mem_of_local (B : Subalgebra F Ω) (T : Set Ω) (u : Ω)
    (h : ∀ q : Ideal B, q.IsMaximal → ∃ b : B, b ∉ q ∧ (b : Ω) * u ∈ Submodule.span B T) :
    u ∈ Submodule.span B T := by
  let J : Ideal B := (Submodule.span B T).comap (LinearMap.toSpanSingleton B Ω u)
  have hJ : ∀ b : B, b ∈ J ↔ (b : Ω) * u ∈ Submodule.span B T := fun b => Iff.rfl
  by_cases hJt : J = ⊤
  · have h1 : (1 : B) ∈ J := hJt ▸ Submodule.mem_top
    simpa using (hJ 1).mp h1
  · obtain ⟨q, hq, hJq⟩ := Ideal.exists_le_maximal J hJt
    obtain ⟨b, hb, hbu⟩ := h q hq
    exact absurd (hJq ((hJ b).mpr hbu)) hb

end Local

theorem SpanSecs.proof : SpanSecs.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y k₀ N e x hx hmod T d s
  have hxv : ∀ i, x i = y ⟨k₀, e.symm i⟩ := fun i => by rw [hx]; rfl

  let B : ι k₀ → Subalgebra F Ω := fun i' =>
    chartRingOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) (fun _ => i')
  have hB : ∀ (i : Fin (N + 1)) (hi : x i ≠ 0), Kleiman.chartRing F x (Kleiman.singleChart hi) = B (e.symm i) := by
    intro i hi
    rw [← chartRingOver_oneBlock_eq_chartRing (S := F) x (fun _ => i) hi]
    unfold B chartRingOver
    congr 1
    ext z
    constructor
    · rintro ⟨⟨_, l⟩, rfl⟩
      exact ⟨⟨(), e.symm l⟩, by simp [IndefiniteRowSideFullHecke.Kleiman2.oneBlock, IndefiniteRowSideFullHecke.Kleiman2.blockVec, hxv]⟩
    · rintro ⟨⟨_, l⟩, rfl⟩
      exact ⟨⟨(), e l⟩, by simp [IndefiniteRowSideFullHecke.Kleiman2.oneBlock, IndefiniteRowSideFullHecke.Kleiman2.blockVec, hxv]⟩

  have hBc : ∀ c : ∀ k, ι k, B (c k₀) ≤ chartRingOver F y c := by
    intro c
    refine Algebra.adjoin_le ?_
    rintro _ ⟨⟨_, l⟩, rfl⟩
    exact Algebra.subset_adjoin ⟨⟨k₀, l⟩, rfl⟩
  constructor
  · intro hs c hc
    have hi : x (e (c k₀)) ≠ 0 := by rw [hxv, Equiv.symm_apply_apply]; exact hc k₀
    set A := Kleiman.chartRing F x (Kleiman.singleChart hi) with hA
    have hAc : A ≤ chartRingOver F y c := by
      rw [hA, hB, Equiv.symm_apply_apply]; exact hBc c
    have hs' := Submodule.mem_iInf _ |>.mp hs (Kleiman.singleChart hi)
    rw [Submodule.restrictScalars_mem,
      Kleiman.twistMod_eq_span d _ (Finset.mem_singleton_self (e (c k₀)))] at hs'
    have hv : y ⟨k₀, c k₀⟩ = x (e (c k₀)) := by rw [hxv, Equiv.symm_apply_apply]
    rw [hv]
    refine Submodule.mul_induction_on hs' ?_ ?_
    · intro m hm n hn
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hn
      have e1 : m * (a • x (e (c k₀)) ^ d) * x (e (c k₀)) ^ (-d) = (⟨a, hAc a.2⟩ : chartRingOver F y c) • m := by
        rw [Subalgebra.smul_def, Subalgebra.smul_def, smul_eq_mul, smul_eq_mul, zpow_neg]
        field_simp
      rw [e1]
      exact Submodule.smul_mem _ _ (span_subset_span hAc T hm)
    · intro a b ha hb
      rw [add_mul]
      exact Submodule.add_mem _ ha hb
  · intro h
    refine Submodule.mem_iInf _ |>.mpr fun I => ?_
    rw [Submodule.restrictScalars_mem]
    obtain ⟨i, hiI⟩ := I.2.1
    have hi : x i ≠ 0 := (Kleiman.mem_support x).1 (I.2.2 hiI)
    rw [Kleiman.twistMod_eq_span d I hiI]
    have hle : Kleiman.chartRing F x (Kleiman.singleChart hi) ≤ Kleiman.chartRing F x I :=
      Kleiman.chartRing_mono (Finset.singleton_subset_iff.mpr hiI)

    suffices key : s * x i ^ (-d) ∈ Submodule.span (Kleiman.chartRing F x (Kleiman.singleChart hi)) T by
      have e1 : s = s * x i ^ (-d) * x i ^ d := by
        rw [zpow_neg, mul_assoc, inv_mul_cancel₀ (zpow_ne_zero d hi), mul_one]
      rw [e1]
      exact Submodule.mul_mem_mul (span_subset_span hle T key) (Submodule.subset_span rfl)
    rw [hB i hi]
    have hxi' : y ⟨k₀, e.symm i⟩ ≠ 0 := by rw [← hxv]; exact hi
    refine spanSecs_mem_of_local _ T _ fun q hq => ?_
    have := hq.isPrime

    have hz : IndefiniteRowSideFullHecke.Kleiman2.locIn (B (e.symm i)) q ∈
        IndefiniteRowSideFullHecke.Kleiman2.modelPts F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) :=
      ⟨fun _ => e.symm i, fun _ => hxi', q, hq.isPrime, rfl⟩
    rw [← hmod.2] at hz
    obtain ⟨c, hc, p, hp, hzp⟩ := hz
    have := hp
    have hCz : ∀ a ∈ chartRingOver F y c, a ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn (B (e.symm i)) q := by
      intro a ha
      rw [hzp]
      exact spanSecs_mem_locIn_self ha

    set w := y ⟨k₀, c k₀⟩ with hw
    set v := y ⟨k₀, e.symm i⟩ with hvdef
    have hw0 : w ≠ 0 := hc k₀
    have h1 : w / v ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn (B (e.symm i)) q :=
      spanSecs_mem_locIn_self (Algebra.subset_adjoin ⟨⟨(), c k₀⟩, rfl⟩)
    have h2 : v / w ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn (B (e.symm i)) q :=
      hCz _ (Algebra.subset_adjoin ⟨⟨k₀, e.symm i⟩, rfl⟩)
    have hg : (w / v) ^ d ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn (B (e.symm i)) q := by
      obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg d
      · rw [zpow_natCast]; exact pow_mem h1 n
      · rw [zpow_neg, zpow_natCast, ← inv_pow, inv_div]; exact pow_mem h2 n
    have e2 : s * x i ^ (-d) = (w / v) ^ d * (s * w ^ (-d)) := by
      rw [hxv, ← hvdef, div_zpow, zpow_neg, zpow_neg]
      field_simp
    rw [e2]
    exact spanSecs_mul_step hg (spanSecs_exists_mul_mem _ _ q hCz T (h c hc))

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistModNatMul
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open scoped Pointwise
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver)

section Charts

variable {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem PowRealises.twist_sub (G Q : Kleiman.SubSystem F x Ω) (I : Kleiman.Chart x) :
    (G.twist Q).sub I = Q.sub I * G.sub I := by
  rw [Submodule.mul_eq_span_mul_set]
  show Submodule.span _ _ = _
  congr 1
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_mul, SetLike.mem_coe, smul_eq_mul]
  constructor
  · rintro ⟨q, hq, g, hg, rfl⟩; exact ⟨q, hq, g, hg, rfl⟩
  · rintro ⟨q, hq, g, hg, rfl⟩; exact ⟨q, hq, g, hg, rfl⟩

theorem PowRealises.twistSys_sub (c : ℤ) (I : Kleiman.Chart x) :
    (Kleiman.twistSys F x c).sub I = Kleiman.twistMod F x c I := rfl

theorem PowRealises.twistMod_mul (a b : ℤ) (I : Kleiman.Chart x) :
    Kleiman.twistMod F x a I * Kleiman.twistMod F x b I = Kleiman.twistMod F x (a + b) I := by
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (Kleiman.mem_support x).mp (I.2.2 hi)
  rw [Kleiman.twistMod_eq_span a I hi, Kleiman.twistMod_eq_span b I hi, Kleiman.twistMod_eq_span (a + b) I hi,
    Submodule.span_mul_span, Set.singleton_mul_singleton, ← zpow_add₀ hxi]

theorem PowRealises.twistMod_zero (I : Kleiman.Chart x) : Kleiman.twistMod F x 0 I = 1 := by
  obtain ⟨i, hi⟩ := I.2.1
  rw [Kleiman.twistMod_eq_span 0 I hi, zpow_zero, Submodule.one_eq_span]

theorem PowRealises.twistMod_nat_mul (c : ℤ) (I : Kleiman.Chart x) :
    ∀ p : ℕ, Kleiman.twistMod F x ((p : ℤ) * c) I = Kleiman.twistMod F x c I ^ p
  | 0 => by rw [Nat.cast_zero, zero_mul, pow_zero]; exact PowRealises.twistMod_zero I
  | p + 1 => by
    rw [pow_succ', ← PowRealises.twistMod_nat_mul c I p, PowRealises.twistMod_mul]
    congr 1
    push_cast
    ring

theorem PowRealises.pow_sub (Q : Kleiman.SubSystem F x Ω) (I : Kleiman.Chart x) :
    ∀ p : ℕ, (Q.pow p).sub I = Q.sub I ^ p
  | 0 => by rw [pow_zero]; exact PowRealises.twistMod_zero I
  | p + 1 => by
    show ((Q.pow p).twist Q).sub I = _
    rw [PowRealises.twist_sub, PowRealises.pow_sub Q I p, pow_succ']

end Charts

section Model

variable {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω]

theorem PowRealises.mem_span_inv_iff (A : Subalgebra F Ω) {u z : Ω} (hu : u ≠ 0) :
    z ∈ Submodule.span A {u⁻¹} ↔ z * u ∈ A := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    rw [Subalgebra.smul_def, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hu, mul_one]
    exact a.2
  · intro h
    refine ⟨⟨z * u, h⟩, ?_⟩
    rw [Subalgebra.smul_def, smul_eq_mul]
    exact mul_inv_cancel_right₀ hu z

variable {K : Type} [Fintype K] {ι : K → Type}

theorem PowRealises.mem_secOver (y : (Σ k, ι k) → Ω) (n : K → ℤ) (s : Ω) :
    s ∈ secOver F y n ↔ ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
      s * ∏ k, y ⟨k, c k⟩ ^ (-n k) ∈ chartRingOver F y c := by
  simp only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply,
    Subalgebra.mem_toSubmodule]

theorem PowRealises.span_secOver_eq (y : (Σ k, ι k) → Ω) (n : K → ℤ) (hg : IndefiniteRowSideFullHecke.Kleiman2.IsGenerated F y n)
    (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    Submodule.span (chartRingOver F y c) (secOver F y n : Set Ω) =
      Submodule.span (chartRingOver F y c) {(∏ k, y ⟨k, c k⟩ ^ (-n k))⁻¹} := by
  have hu : (∏ k, y ⟨k, c k⟩ ^ (-n k)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)
  apply le_antisymm
  · rw [Submodule.span_le]
    intro t ht
    exact (PowRealises.mem_span_inv_iff _ hu).mpr ((PowRealises.mem_secOver y n t).mp ht c hc)
  · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
    obtain ⟨m, s, hs, hgen⟩ := hg
    obtain ⟨u, hu', hsum⟩ := hgen c hc
    have key : (∏ k, y ⟨k, c k⟩ ^ (-n k))⁻¹ =
        ∑ j, (⟨u j, hu' j⟩ : chartRingOver F y c) • s j := by
      rw [← one_mul (_⁻¹), ← hsum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Subalgebra.smul_def, smul_eq_mul, mul_assoc, mul_inv_cancel_right₀ hu]
    rw [key]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span (hs j))

theorem PowRealises.prod_exp [DecidableEq K] (y : (Σ k, ι k) → Ω) (k₀ : K) (β : K → ℤ) (p : ℕ) (c d : ℤ)
    (cc : ∀ k, ι k) (hc : ∀ k, y ⟨k, cc k⟩ ≠ 0) :
    y ⟨k₀, cc k₀⟩ ^ (-d) * (∏ k, y ⟨k, cc k⟩ ^ (-(β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k)) ^ p =
      ∏ k, y ⟨k, cc k⟩ ^ (-(p • β + ((p : ℤ) * c + d) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k) := by
  have h0 : y ⟨k₀, cc k₀⟩ ^ (-d) = ∏ k, y ⟨k, cc k⟩ ^ (-(d • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k) := by
    rw [Finset.prod_eq_single k₀]
    · simp [IndefiniteRowSideFullHecke.Kleiman2.baseDeg]
    · intro k _ hk
      simp [IndefiniteRowSideFullHecke.Kleiman2.baseDeg, hk]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [h0, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_natCast, ← zpow_mul, ← zpow_add₀ (hc k)]
  congr 1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply]
  ring

end Model

theorem PowRealises.proof (hG : ModelGenerated.Statement) (hS : SpanSecs.Statement) : PowRealises.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y k₀ N e x hx hmod Q β hQ p ct
  obtain ⟨c₀, hc₀⟩ := Kleiman.Generated.full F Ω N x Q
  obtain ⟨c₁, hc₁⟩ := hG F K ι Ω y k₀ hmod β
  obtain ⟨c, hc0, hc1⟩ : ∃ c, c₀ ≤ c ∧ c₁ ≤ c := ⟨max c₀ c₁, le_max_left _ _, le_max_right _ _⟩
  have hgenQ := hc₀ c hc0
  have hgenY := hc₁ c hc1
  obtain ⟨d, rfl⟩ : ∃ d, ct = (p : ℤ) * c + d := ⟨ct - (p : ℤ) * c, by ring⟩
  have hchart : ∀ I : Kleiman.Chart x, (Kleiman.twistMul Q.toSubSystem p ((p : ℤ) * c + d)).sub I =
      Submodule.span (Kleiman.chartRing F x I)
          ((secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) : Set Ω) ^ p) * Kleiman.twistMod F x d I := by
    intro I
    have h1 : (Q.toSubSystem.twist (Kleiman.twistSys F x c)).sub I =
        Submodule.span (Kleiman.chartRing F x I) (secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) : Set Ω) := by
      rw [← hgenQ I, hQ c]
    rw [PowRealises.twist_sub, PowRealises.twistSys_sub] at h1
    show ((Q.toSubSystem.pow p).twist (Kleiman.twistSys F x ((p : ℤ) * c + d))).sub I = _
    rw [PowRealises.twist_sub, PowRealises.twistSys_sub, PowRealises.pow_sub, ← PowRealises.twistMod_mul,
      PowRealises.twistMod_nat_mul, ← Submodule.span_pow, ← h1, mul_pow]
    ring
  have hsecs : (Kleiman.twistMul Q.toSubSystem p ((p : ℤ) * c + d)).secs = ⨅ I : Kleiman.Chart x,
      (Submodule.span (Kleiman.chartRing F x I)
          ((secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) : Set Ω) ^ p) *
        Kleiman.twistMod F x d I).restrictScalars F := by
    simp only [Kleiman.SubSystem.secs, hchart]
  ext s
  rw [hsecs, hS F K ι Ω y k₀ N e x hx hmod _ d s, PowRealises.mem_secOver]
  refine forall_congr' fun cc => forall_congr' fun hc => ?_
  have hu : (∏ k, y ⟨k, cc k⟩ ^ (-(β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)
  rw [← Submodule.span_pow, PowRealises.span_secOver_eq y _ hgenY cc hc, Submodule.span_pow, Set.singleton_pow,
    inv_pow, PowRealises.mem_span_inv_iff _ (pow_ne_zero _ hu), mul_assoc, PowRealises.prod_exp y k₀ β p c d cc hc]

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ZpowMemSubringOfInvMem
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver)

noncomputable section

section Base

variable {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω]

theorem mem_of_forall_mem_locIn (B : Subalgebra F Ω) {u : Ω}
    (h : ∀ p : Ideal B, p.IsMaximal → u ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn B p) : u ∈ B := by
  let I : Ideal B :=
    { carrier := {a | (a : Ω) * u ∈ B}
      add_mem' := fun {a b} ha hb => by
        show ((a : Ω) + b) * u ∈ B
        rw [add_mul]; exact B.add_mem ha hb
      zero_mem' := by show (0 : Ω) * u ∈ B; rw [zero_mul]; exact B.zero_mem
      smul_mem' := fun c a ha => by
        show ((c : Ω) * a) * u ∈ B
        rw [mul_assoc]; exact B.mul_mem c.2 ha }
  by_cases hI : I = ⊤
  · have h1 : (1 : B) ∈ I := hI ▸ Submodule.mem_top
    have h2 : ((1 : B) : Ω) * u ∈ B := h1
    simpa using h2
  · obtain ⟨p, hp, hIp⟩ := Ideal.exists_le_maximal I hI
    have := hp.isPrime
    obtain ⟨a, b, hb, hu⟩ := mem_locIn.mp (h p hp)
    have hb0 : (b : Ω) ≠ 0 := coe_ne_zero_of_not_mem hb
    refine absurd (hIp ?_) hb
    show (b : Ω) * u ∈ B
    rw [hu, mul_div_cancel₀ _ hb0]
    exact a.2

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}

omit [Fintype K] [DecidableEq K] in

theorem adjoin_base_le (y : (Σ k, ι k) → Ω) (k₀ : K) (c : ∀ k, ι k) :
    Algebra.adjoin F (Set.range fun i => IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ i / IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ (c k₀)) ≤
      chartRingOver F y c := by
  rw [Algebra.adjoin_le_iff]
  rintro _ ⟨i, rfl⟩
  exact Algebra.subset_adjoin ⟨⟨k₀, i⟩, rfl⟩

theorem prod_baseDeg (y : (Σ k, ι k) → Ω) (k₀ : K) (c : ∀ k, ι k) (m : ℤ) :
    (∏ k, y ⟨k, c k⟩ ^ (-(m • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k)) = y ⟨k₀, c k₀⟩ ^ (-m) := by
  rw [Finset.prod_eq_single k₀]
  · simp [IndefiniteRowSideFullHecke.Kleiman2.baseDeg]
  · intro k _ hk
    simp [IndefiniteRowSideFullHecke.Kleiman2.baseDeg, hk]
  · intro h; exact absurd (Finset.mem_univ k₀) h

theorem zpow_mem_subring_of_inv_mem (z : Subring Ω) {r : Ω} (hr : r ∈ z) (hr' : r⁻¹ ∈ z) (m : ℤ) : r ^ m ∈ z := by
  rcases Int.eq_nat_or_neg m with ⟨n, rfl | rfl⟩
  · rw [zpow_natCast]; exact z.pow_mem hr n
  · rw [zpow_neg, zpow_natCast, ← inv_pow]; exact z.pow_mem hr' n

theorem secOver_baseDeg_eq (y : (Σ k, ι k) → Ω) (k₀ : K) (hy : IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀) (m : ℤ) :
    secOver F y (m • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) =
      secOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) (fun _ => m) := by
  set x' := IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ with hx'
  have hmem : ∀ t, t ∈ secOver F y (m • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) ↔
      ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → t * y ⟨k₀, c k₀⟩ ^ (-m) ∈ chartRingOver F y c := by
    intro t
    simp only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply,
      Subalgebra.mem_toSubmodule, prod_baseDeg]
  ext t
  rw [hmem, mem_secOver_oneBlock]
  constructor
  · intro ht j hj
    apply mem_of_forall_mem_locIn
    intro p hp
    have hpp := hp.isPrime
    have hz : IndefiniteRowSideFullHecke.Kleiman2.locIn _ p ∈ IndefiniteRowSideFullHecke.Kleiman2.modelPts F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') := by
      refine ⟨fun _ => j, fun _ => hj, ?_⟩
      rw [chartRingOver_oneBlock_eq]
      exact ⟨p, hp.isPrime, rfl⟩
    rw [← hy.2] at hz
    obtain ⟨c, hc, q, hq, hzq⟩ := hz
    have hA : ∀ a ∈ chartRingOver F y c, a ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn _ p := fun a ha => by
      rw [hzq, mem_locIn]
      exact ⟨⟨a, ha⟩, 1, fun h => one_not_mem_of_prime hq h, by simp⟩
    have hB : ∀ a ∈ Algebra.adjoin F (Set.range fun i => x' i / x' j), a ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn _ p :=
      fun a ha => mem_locIn.mpr ⟨⟨a, ha⟩, 1, fun h => one_not_mem_of_prime hpp h, by simp⟩
    have hyc : y ⟨k₀, c k₀⟩ ≠ 0 := hc k₀
    have hr : y ⟨k₀, c k₀⟩ / x' j ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn _ p := hB _ (Algebra.subset_adjoin ⟨c k₀, rfl⟩)
    have hr' : (y ⟨k₀, c k₀⟩ / x' j)⁻¹ ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn _ p := by
      rw [inv_div]
      exact hA _ (Algebra.subset_adjoin ⟨⟨k₀, j⟩, rfl⟩)
    have e : t * x' j ^ (-m) = t * y ⟨k₀, c k₀⟩ ^ (-m) * (y ⟨k₀, c k₀⟩ / x' j) ^ m := by
      rw [div_zpow, zpow_neg, zpow_neg]
      field_simp
    rw [e]
    exact Subring.mul_mem _ (hA _ (ht c hc)) (zpow_mem_subring_of_inv_mem _ hr hr' m)
  · intro ht c hc
    exact adjoin_base_le y k₀ c (ht (c k₀) (hc k₀))

end Base

theorem BaseRealises.proof : BaseRealises.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y k₀ N e x hx hy b c
  rw [Kleiman.twistBundle_toSubSystem, Kleiman.twistSys_twist_twistSys, twistSys_secs_eq_secOver, ← add_smul,
    secOver_baseDeg_eq y k₀ hy, hx, secOver_oneBlock_comp]

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

