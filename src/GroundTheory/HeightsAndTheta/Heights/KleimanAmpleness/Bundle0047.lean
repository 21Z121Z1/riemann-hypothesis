import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0038
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0042
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPrimeFiltrationExists
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0039
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSectionCountDropFilt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistSplitCech
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0019
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0043
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0014

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCutNonempty
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section Chart

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem coe_aeval_ratio_mem_idealMod {pp : Ideal (Poly k N)}
    (hh : ∀ p ∈ pp, ∀ d : ℕ, homogeneousComponent d p ∈ pp) {j : Fin (N + 1)} (hj : x j ≠ 0)
    {p : Poly k N} (hp : p ∈ pp) :
    ((aeval (ratio (S := k) hj) p : chartRing k x (singleChart hj)) : Ω) ∈
      idealMod (x := x) pp (singleChart hj) := by
  rw [← sum_homogeneousComponent p]
  rw [map_sum, AddSubmonoidClass.coe_finsetSum]
  refine Submodule.sum_mem _ fun d _ => Submodule.subset_span ?_
  exact ⟨homogeneousComponent d p, X j ^ d, d, hh p hp d,
    pow_mem (X_mem_monos (Finset.mem_singleton_self j)) d, homogeneousComponent_isHomogeneous d p,
    isHomogeneous_X_pow j d, coe_aeval_ratio' hj (homogeneousComponent_isHomogeneous d p)⟩

theorem coe_aeval_ratio_mul_mem_span {L : SubSystem k x Ω} {s : Ω} {j : Fin (N + 1)} (hj : x j ≠ 0)
    {z : Poly k N} (hz : z ∈ zeroIdeal L s) {δ : Ω} (hδ : δ ∈ L.sub (singleChart hj)) :
    ((aeval (ratio (S := k) hj) z : chartRing k x (singleChart hj)) : Ω) * δ ∈
      Submodule.span (chartRing k x (singleChart hj)) {s} := by
  induction hz using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨c, hfc, hf⟩ := hf
    obtain ⟨o, ho, he⟩ := hf (singleChart hj) δ hδ
    rw [twistMod_eq_span _ _ (Finset.mem_singleton_self j), Submodule.mem_span_singleton] at ho
    obtain ⟨b, rfl⟩ := ho
    rw [Submodule.mem_span_singleton]
    refine ⟨b, ?_⟩
    rw [coe_aeval_ratio hj hfc, chartRing_smul_def, div_mul_eq_mul_div, he, chartRing_smul_def,
      zpow_natCast]
    field_simp
  | zero => simp
  | add a b _ _ ha hb =>
    rw [map_add, Subalgebra.coe_add, add_mul]
    exact Submodule.add_mem _ ha hb
  | smul g z _ hz =>
    rw [smul_eq_mul, map_mul, Subalgebra.coe_mul, mul_assoc]
    exact Submodule.smul_mem _ (aeval (ratio (S := k) hj) g) hz

theorem sub_le_twist_sup_span {pp : Ideal (Poly k N)}
    (hh : ∀ p ∈ pp, ∀ d : ℕ, homogeneousComponent d p ∈ pp) (L : LineBundle k x) (s : Ω)
    (hmin : ∀ qq ∈ (pp ⊔ zeroIdeal L.toSubSystem s).minimalPrimes, ∀ i, (X i : Poly k N) ∈ qq)
    (j : Fin (N + 1)) (hj : x j ≠ 0) :
    L.sub (singleChart hj) ≤ (L.twist (idealSys x pp)).sub (singleChart hj) ⊔
      Submodule.span (chartRing k x (singleChart hj)) {s} := by
  have hrad : (X j : Poly k N) ∈ (pp ⊔ zeroIdeal L.toSubSystem s).radical := by
    rw [← Ideal.sInf_minimalPrimes]
    exact Submodule.mem_sInf.mpr fun qq hq => hmin qq hq j
  obtain ⟨m, hm⟩ := hrad
  obtain ⟨p, hp, z, hz, hpz⟩ := Submodule.mem_sup.mp hm
  intro ℓ hℓ
  have h1 : ((aeval (ratio (S := k) hj) ((X j : Poly k N) ^ m) : chartRing k x (singleChart hj)) : Ω) = 1 := by
    rw [map_pow, aeval_X, SubmonoidClass.coe_pow]
    change (x j / x j) ^ m = 1
    rw [div_self hj, one_pow]
  have hsplit : ℓ = ((aeval (ratio (S := k) hj) p : chartRing k x (singleChart hj)) : Ω) * ℓ +
      ((aeval (ratio (S := k) hj) z : chartRing k x (singleChart hj)) : Ω) * ℓ := by
    rw [← add_mul, ← Subalgebra.coe_add, ← map_add, hpz, h1, one_mul]
  rw [hsplit]
  refine Submodule.add_mem_sup (Submodule.subset_span ?_) (coe_aeval_ratio_mul_mem_span hj hz hℓ)
  exact ⟨_, coe_aeval_ratio_mem_idealMod hh hj hp, ℓ, hℓ, rfl⟩

end Chart

theorem CutNonempty.proof (hO : CutOneGenerator.Statement.{u, w}) : CutNonempty.Statement.{u, w} := by
  intro k _ Ω _ _ N x n pp L s hW hL hs _
  by_contra hne
  push Not at hne
  exact hO k Ω N x n pp L s hW hL hs (sub_le_twist_sup_span hW.homog L s hne)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCutOneGenerator
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

namespace CutOneGenerator

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {K' : Type w} [Field K']
  [Algebra k K'] {N : ℕ} {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'}

theorem mem_sub_of_mem_secs {S : Type u} [CommRing S] {E : Type w} [Field E] [Algebra S E] {M : ℕ}
    {z : Fin (M + 1) → E} {H : SubSystem S z E} {t : E} (ht : t ∈ H.secs) (I : Chart z) :
    t ∈ H.sub I :=
  (Submodule.restrictScalars_mem S _ _).mp ((Submodule.mem_iInf _).mp ht I)

theorem mem_chartRing_of_mem_idealMod {pp : Ideal (Poly k N)} {I : Chart x} {a : Ω}
    (ha : a ∈ idealMod (x := x) pp I) : a ∈ chartRing k x I := by
  induction ha using Submodule.span_induction with
  | mem a ha => obtain ⟨f, s, e, -, hs, hf, hse, rfl⟩ := ha; exact ⟨f, s, e, hs, hf, hse, rfl⟩
  | zero => exact zero_mem _
  | add a b _ _ ha hb => exact add_mem ha hb
  | smul c a _ ha => exact mul_mem c.2 ha

variable {hxy : ∀ i, y i ≠ 0 → x i ≠ 0} {Q : SubSystem k x Ω} {Q' : SubSystem k y K'} {ρ : Ω → K'}

theorem restrict_zero (hR : RestrictData Q hxy Q' ρ) (J : Chart y) : ρ 0 = 0 := by
  have := hR.add J 0 (Q.sub _).zero_mem 0 (Q.sub _).zero_mem
  rw [add_zero] at this
  simpa using this

theorem exists_restrict_mul (hR : RestrictData Q hxy Q' ρ) (J : Chart y) {c q : Ω}
    (hc : c ∈ chartRing k x (liftChart hxy J)) (hq : q ∈ Q.sub (liftChart hxy J)) :
    ∃ b ∈ chartRing k y J, ρ (c * q) = b * ρ q := by
  obtain ⟨f, t, e, ht, hf, hte, rfl⟩ := hc
  exact ⟨_, ⟨f, t, e, ht, hf, hte, rfl⟩, hR.smul J q hq f t e ht hf hte⟩

theorem restrict_twist_eq_zero (hR : RestrictData Q hxy Q' ρ) {pp : Ideal (Poly k N)}
    (hpp : primeOf (S := k) y = pp) (J : Chart y) {z : Ω}
    (hz : z ∈ (Q.twist (idealSys x pp)).sub (liftChart hxy J)) :
    z ∈ Q.sub (liftChart hxy J) ∧ ρ z = 0 := by
  have hgen : ∀ w ∈ Q.sub (liftChart hxy J), ∀ q ∈ idealMod (x := x) pp (liftChart hxy J),
      q * w ∈ Q.sub (liftChart hxy J) ∧ ρ (q * w) = 0 := by
    intro w hw q hq
    have hmw : ∀ a ∈ idealMod (x := x) pp (liftChart hxy J), a * w ∈ Q.sub (liftChart hxy J) :=
      fun a ha => (Q.sub _).smul_mem
        ⟨a, mem_chartRing_of_mem_idealMod (pp := pp) (I := liftChart hxy J) ha⟩ hw
    refine ⟨hmw q hq, ?_⟩
    induction hq using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨f, t, e, hfp, ht, hf, hte, rfl⟩ := ha
      rw [hR.smul J w hw f t e ht hf hte,
        (mem_primeOf_of_isHomogeneous y hf).mp (hpp ▸ hfp), zero_div, zero_mul]
    | zero => rw [zero_mul]; exact restrict_zero hR J
    | add a b ha hb iha ihb =>
      rw [add_mul, hR.add J _ (hmw a ha) _ (hmw b hb), iha, ihb, add_zero]
    | smul c a ha iha =>
      obtain ⟨b, -, hb⟩ := exists_restrict_mul hR J c.2 (hmw a ha)
      rw [chartRing_smul_def, mul_assoc, hb, iha, mul_zero]
  induction hz using Submodule.span_induction with
  | mem z hz => obtain ⟨q, hq, w, hw, rfl⟩ := hz; exact hgen w hw q hq
  | zero => exact ⟨zero_mem _, restrict_zero hR J⟩
  | add a b _ _ ha hb => exact ⟨add_mem ha.1 hb.1, by rw [hR.add J a ha.1 b hb.1, ha.2, hb.2, add_zero]⟩
  | smul c a _ ha =>
    refine ⟨(Q.sub _).smul_mem c ha.1, ?_⟩
    obtain ⟨b, -, hb⟩ := exists_restrict_mul hR J c.2 ha.1
    rw [chartRing_smul_def]
    erw [hb]
    rw [ha.2, mul_zero]

theorem exists_eq_mul_of_le (hR : RestrictData Q hxy Q' ρ) {pp : Ideal (Poly k N)}
    (hpp : primeOf (S := k) y = pp) (J : Chart y) {s : Ω} (hs : s ∈ Q.sub (liftChart hxy J))
    (hle : Q.sub (liftChart hxy J) ≤ (Q.twist (idealSys x pp)).sub (liftChart hxy J) ⊔
      Submodule.span (chartRing k x (liftChart hxy J)) {s}) {t : K'} (ht : t ∈ Q'.sub J) :
    ∃ b ∈ chartRing k y J, t = b * ρ s := by
  rw [← hR.span J] at ht
  induction ht using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨q, hq, rfl⟩ := ht
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp (hle hq)
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
    obtain ⟨hu', hu0⟩ := restrict_twist_eq_zero hR hpp J hu
    obtain ⟨b, hb, he⟩ := exists_restrict_mul hR J a.2 hs
    refine ⟨b, hb, ?_⟩
    rw [hR.add J u hu' _ ((Q.sub _).smul_mem a hs), hu0, zero_add, chartRing_smul_def, he]
  | zero => exact ⟨0, zero_mem _, (zero_mul _).symm⟩
  | add t t' _ _ ht ht' =>
    obtain ⟨b, hb, rfl⟩ := ht
    obtain ⟨b', hb', rfl⟩ := ht'
    exact ⟨b + b', add_mem hb hb', (add_mul _ _ _).symm⟩
  | smul c t _ ht =>
    obtain ⟨b, hb, rfl⟩ := ht
    exact ⟨c * b, mul_mem c.2 hb, by rw [chartRing_smul_def, mul_assoc]⟩

theorem exists_algHom_ker_eq {R : Type w} [CommRing R] [Algebra k R] (P : Ideal R) [P.IsPrime] :
    ∃ (F : Type w) (_ : Field F) (_ : Algebra k F) (ψ : R →ₐ[k] F), RingHom.ker ψ = P := by
  refine ⟨FractionRing (R ⧸ P), inferInstance, inferInstance,
    (IsScalarTower.toAlgHom k (R ⧸ P) (FractionRing (R ⧸ P))).comp (Ideal.Quotient.mkₐ k P), ?_⟩
  ext a
  rw [RingHom.mem_ker]
  change algebraMap (R ⧸ P) (FractionRing (R ⧸ P)) (Ideal.Quotient.mk P a) = 0 ↔ _
  rw [IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]

end CutOneGenerator

open CutOneGenerator in

theorem CutOneGenerator.proof (hG : GlobalFunctionsIntegral.Statement.{u, w}) :
    CutOneGenerator.Statement.{u, w} := by
  intro k _ Ω _ _ N x n pp L s hW hL hs hgen
  obtain ⟨r, h, hV⟩ := hL
  obtain ⟨j, hXj⟩ := hW.relevant
  have hxj : x j ≠ 0 := by
    intro h0
    apply hXj
    apply hW.le
    rw [mem_primeOf_of_isHomogeneous x (isHomogeneous_X k j), aeval_X, h0]
  obtain ⟨hprime, hpt⟩ :=
    PrimeFiltration.Point.proof k Ω N x pp hW.isPrime hW.homog hW.le j hxj hXj
  obtain ⟨K', _, _, ψ, hker⟩ := @exists_algHom_ker_eq k _ _ _ _ (chartPrime pp hxj) hprime
  set y : Fin (N + 1) → K' := fun i => ψ (ratio hxj i) with hy
  have hpy : primeOf (S := k) y = pp := hpt K' ψ hker
  have hy0 : y j ≠ 0 := by
    have e : ratio (S := k) hxj j = 1 := Subtype.ext (div_self hxj)
    show ψ (ratio hxj j) ≠ 0
    rw [e, map_one]
    exact one_ne_zero
  have hxy : ∀ i, y i ≠ 0 → x i ≠ 0 := by
    intro i hyi hxi
    apply hyi
    have e : ratio (S := k) hxj i = 0 := Subtype.ext (by show x i / x j = 0; rw [hxi, zero_div])
    show ψ (ratio hxj i) = 0
    rw [e, map_zero]
  have hne : y ≠ 0 := Function.ne_iff.mpr ⟨j, hy0⟩
  obtain ⟨Q', ρ, hR, hV', hdim⟩ :=
    exists_restrictData_isVeryAmpleBy (by rw [hpy]; exact hW.le) hxy (singleChart hy0) L h hV
  have hWy : IsSubvar y (primeOf (S := k) y) (n + 1) := by
    rw [hpy]; exact ⟨hW.isPrime, hW.homog, hpy.le, hW.relevant, hW.dim⟩
  have hdy : dimCl k y = ((n + 1 : ℕ) : Cardinal) := (DimTie.proof k K' N y hne (n + 1)).mp hWy
  have hmul : ∀ t ∈ Q'.secs, ∀ i (hi : y i ≠ 0), ∃ b ∈ chartRing k y (singleChart hi), t = b * ρ s :=
    fun t ht i hi => exists_eq_mul_of_le hR hpy (singleChart hi) (mem_sub_of_mem_secs hs _)
      (hgen i (hxy i hi)) (mem_sub_of_mem_secs ht _)
  have hρs : ρ s ≠ 0 := by
    intro h0
    obtain ⟨Q'', hQ''⟩ := Q'.invertible (singleChart hy0)
    have hbot : Q'.sub (singleChart hy0) = ⊥ := (Submodule.eq_bot_iff _).mpr fun t ht => by
      obtain ⟨b, -, rfl⟩ := exists_eq_mul_of_le hR hpy (singleChart hy0) (mem_sub_of_mem_secs hs _)
        (hgen j (hxy j hy0)) ht
      rw [h0, mul_zero]
    rw [hbot, Submodule.bot_mul] at hQ''
    have h1 : (1 : K') ∈ (⊥ : Submodule (chartRing k y (singleChart hy0)) K') := by
      rw [hQ'']; exact Submodule.one_le.mp le_rfl
    exact one_ne_zero ((Submodule.mem_bot _).mp h1)
  have hint : ∀ l, IsIntegral k (ρ (h l) / ρ s) := fun l => hG k K' N y _ hne fun i hi => by
    obtain ⟨b, hb, he⟩ := hmul (ρ (h l)) (hV'.mem_secs l) i hi
    rw [he, mul_div_cancel_right₀ _ hρs]
    exact hb
  have halg : Algebra.IsAlgebraic k (funField (k := k) (ρ ∘ h)) := by
    apply IntermediateField.isAlgebraic_adjoin
    rintro _ ⟨i, l, -, rfl⟩
    have e : (ρ ∘ h) l / (ρ ∘ h) i = ρ (h l) / ρ s * (ρ (h i) / ρ s)⁻¹ := by
      rw [inv_div, div_mul_div_cancel₀ hρs]; rfl
    rw [e]
    exact (hint l).mul (hint i).inv
  have h0 : dimCl k (ρ ∘ h) = 0 := trdeg_eq_zero
  rw [← hdim, hdy] at h0
  exact Nat.succ_ne_zero n (Nat.cast_eq_zero.mp h0)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCycleSplitFilt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

universe u w

theorem CycleSplit.Filt.telescope : ∀ {n : ℕ} (a : Fin (n + 1) → ℤ) (b : Fin n → ℤ),
    (∀ l : Fin n, a l.castSucc = a l.succ + b l) → a 0 = a (Fin.last n) + ∑ l, b l
  | 0, a, b, _ => by simp
  | n + 1, a, b, h => by
    have ih := CycleSplit.Filt.telescope (fun m => a m.castSucc) (fun l => b l.castSucc)
      (fun l => by
        have := h l.castSucc
        simpa only [Fin.succ_castSucc] using this)
    have hl := h (Fin.last n)
    rw [Fin.succ_last] at hl
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.castSucc_zero] at ih
    linarith

open SectionCount.Drop.Filt in

theorem CycleSplit.Filt.proof (hS : CycleSplit.Filt.Step.Statement.{u, w}) :
    CycleSplit.Filt.Statement.{u, w} := by
  classical
  intro S _ _ Ω _ _ N x 𝔪 h𝔪 J hJhom hJx hJ𝔪

  have hkill : ∀ p ∈ primeOf (S := S) x, ∀ m : Poly S N ⧸ J, p • m = 0 := by
    intro p hp m
    obtain ⟨m, rfl⟩ := Ideal.Quotient.mk_surjective m
    change Ideal.Quotient.mk J (p * m) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (J.mul_mem_right m (hJx hp))
  obtain ⟨⟨Fl⟩, hcount⟩ := PrimeFiltration.Exists.proof.{u, u, w} S Ω N x (Poly S N ⧸ J)
    (quotGraded J hJhom) (finite_quot J) hkill
  rw [Ideal.annihilator_quotient] at hcount
  have hann : ∀ l, J ≤ Fl.prime l := fun l => by
    have := Fl.ann_le l; rwa [Ideal.annihilator_quotient] at this

  have hlift : ∀ l : Fin Fl.n, ∃ (g : Poly S N) (e : ℕ), g.IsHomogeneous e ∧
      Ideal.Quotient.mk J g = Fl.gen l := by
    intro l
    obtain ⟨g, hg, hgm⟩ := mem_quotGraded_piece.mp (Fl.gen_mem l)
    by_cases h0 : 0 ≤ Fl.deg l
    · refine ⟨g, (Fl.deg l).toNat, isHomogeneous_of_isWeightedHomogeneous_one ?_, hgm⟩
      rwa [Int.toNat_of_nonneg h0]
    · refine ⟨0, 0, isHomogeneous_zero _ _ _, ?_⟩
      have hg0 : g = 0 := by
        ext m
        by_contra hne
        have h1 := hg hne
        rw [weight_one_int] at h1
        omega
      rw [← hgm, hg0]
  choose g eK hgH hgm using hlift

  let Jk : Fin (Fl.n + 1) → Ideal (Poly S N) := fun l => (Fl.step l).comap J.mkQ
  have hJ0 : Jk 0 = J := by
    simp only [Jk, Fl.step_zero, Submodule.comap_bot, Submodule.ker_mkQ]
  have hJlast : Jk (Fin.last _) = ⊤ := by
    simp only [Jk, Fl.step_last, Submodule.comap_top]
  have hmkQ : ∀ (c : Poly S N) (l : Fin Fl.n), J.mkQ (c * g l) = c • Fl.gen l := by
    intro c l
    rw [← hgm l]
    rfl
  have hJsucc : ∀ l : Fin Fl.n, Jk l.succ = Jk l.castSucc ⊔ Ideal.span {g l} := by
    intro l
    ext f
    simp only [Jk, Fl.step_succ, Submodule.mem_comap]
    constructor
    · intro hf
      obtain ⟨a, ha, y, hy, hay⟩ := Submodule.mem_sup.mp hf
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
      have h1 : f - c * g l ∈ (Fl.step l.castSucc).comap J.mkQ := by
        rw [Submodule.mem_comap, map_sub, hmkQ, ← hay, add_sub_cancel_right]
        exact ha
      have h2 := Submodule.add_mem_sup h1 (Ideal.mul_mem_left _ c (Ideal.mem_span_singleton_self (g l)))
      rwa [sub_add_cancel] at h2
    · intro hf
      obtain ⟨a, ha, y, hy, rfl⟩ := Submodule.mem_sup.mp hf
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hy
      rw [map_add, hmkQ]
      exact Submodule.add_mem_sup ha (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
  have hJkp : ∀ (l : Fin Fl.n) (f : Poly S N), f ∈ Fl.prime l ↔ f * g l ∈ Jk l.castSucc := by
    intro l f
    rw [Fl.mem_prime, ← hgm l]
    exact Iff.rfl
  have hJk_ge : ∀ l, J ≤ Jk l := fun l f hf => by
    simp only [Jk, Submodule.mem_comap, Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero J).mpr hf, zero_mem]
  have hJk_hom : ∀ l, ∀ f ∈ Jk l, ∀ d : ℕ, homogeneousComponent d f ∈ Jk l := by
    intro l
    induction l using Fin.induction with
    | zero => rw [hJ0]; exact hJhom
    | succ l ih =>
      rw [hJsucc l]
      exact hom_sup ih (hom_span fun g' hg' => ⟨eK l, by rw [Set.mem_singleton_iff.mp hg']; exact hgH l⟩)
  refine ⟨Fl.n, Fl.prime, fun l => -((eK l : ℕ) : ℤ),
    fun l => ⟨Fl.isPrime l, Fl.isHomogeneous l, hann l⟩, fun G _ hG => hcount Fl G hG, fun Q => ?_⟩

  have hstep : ∀ l : Fin Fl.n, ∀ᶠ c : ℕ in atTop,
      restrLen (Jk l.castSucc) (Q.twist (twistSys S x (c : ℤ))) =
        restrLen (Jk l.succ) (Q.twist (twistSys S x (c : ℤ))) +
          restrLen (Fl.prime l) (Q.twist (twistSys S x ((c : ℤ) - (eK l : ℕ)))) := by
    intro l
    rw [hJsucc l]
    exact hS S Ω N x 𝔪 h𝔪 (Jk l.castSucc) (Fl.prime l) (g l) (eK l) (hJk_hom _)
      (hJx.trans (hJk_ge _)) (hJ𝔪.trans (hJk_ge _)) (hgH l) (Fl.isHomogeneous l) (hJkp l) Q
  filter_upwards [Filter.eventually_all.mpr hstep] with c hc
  have htel := CycleSplit.Filt.telescope
    (fun m => restrLen (Jk m) (Q.twist (twistSys S x (c : ℤ))))
    (fun l => restrLen (Fl.prime l) (Q.twist (twistSys S x ((c : ℤ) - (eK l : ℕ))))) hc
  simp only [hJ0, hJlast, restrLen_of_irrelevant ⊤ (fun i => Submodule.mem_top), zero_add] at htel
  rw [htel]
  simp only [sub_eq_add_neg]

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTwistSplit
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section Retract

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {r : ℕ} (η : Fin (r + 1) → Ω) (M₀ : FinGradedSub (S := S) (x := x) Ω) (n : ℕ) (c : ℤ)
  {G B : SubSystem S x Ω} (hG : ∀ I, M₀.tilde 0 I = G.sub I)
  (hB : ∀ I, Submodule.span (chartRing S x I) (Set.range η) = B.sub I)

include hG hB in

theorem twist_retract (i : ℕ) :
    ∃ (ι : ((G.twist (B.pow n)).twist (twistSys S x c)).H i →+ cohom (twGraded η M₀) i c)
      (π : cohom (twGraded η M₀) i c →+ ((G.twist (B.pow n)).twist (twistSys S x c)).H i),
      ∀ z, π (ι z) = z := by
  have hker : ∀ z : Cech.Cochain (fun K : Chart x => ↥(((G.twist (B.pow n)).twist (twistSys S x c)).sub K)) i,
      Cech.d _ ((G.twist (B.pow n)).twist (twistSys S x c)).res i z = 0 →
      Cech.d _ locResS i (Fmap η M₀ n c hG hB i z) = 0 := by
    intro z hz
    rw [← F_d, hz, Fmap_zero]
  have hker' : ∀ (s : Cech.Cochain (locSys (MvPolynomial (Fin (r + 1)) S) N (TwM η M₀)) i)
      (hs : s ∈ Cech.Cdeg (locSys (MvPolynomial (Fin (r + 1)) S) N (TwM η M₀)) (degLoc (twGraded η M₀) c) i),
      Cech.d _ locResS i s = 0 →
      Cech.d _ ((G.twist (B.pow n)).twist (twistSys S x c)).res i (Gm η M₀ n c hG hB i s hs) = 0 := by
    intro s hs h0
    rw [← Gm_d η M₀ n c hG hB i s hs (by rw [h0]; exact Submodule.zero_mem _)]
    funext K
    apply Subtype.ext
    change gm η M₀ n c (i + 1) (Cech.d _ locResS i s) K = 0
    rw [h0, gm_zero]
  let f : LinearMap.ker (Cech.d (fun K : Chart x => ↥(((G.twist (B.pow n)).twist (twistSys S x c)).sub K))
        ((G.twist (B.pow n)).twist (twistSys S x c)).res i) →+
      Cech.cocyDeg (locSys (MvPolynomial (Fin (r + 1)) S) N (TwM η M₀)) (degLoc (twGraded η M₀) c) locResS i :=
    { toFun := fun z => ⟨Fmap η M₀ n c hG hB i z.1, Submodule.mem_inf.mpr
        ⟨LinearMap.mem_ker.mpr (hker z.1 (LinearMap.mem_ker.mp z.2)), Fmap_mem η M₀ n c hG hB i z.1⟩⟩
      map_zero' := Subtype.ext (Fmap_zero η M₀ n c hG hB i)
      map_add' := fun a b => Subtype.ext (Fmap_add η M₀ n c hG hB i a.1 b.1) }
  let g : Cech.cocyDeg (locSys (MvPolynomial (Fin (r + 1)) S) N (TwM η M₀)) (degLoc (twGraded η M₀) c) locResS i →+
      LinearMap.ker (Cech.d (fun K : Chart x => ↥(((G.twist (B.pow n)).twist (twistSys S x c)).sub K))
        ((G.twist (B.pow n)).twist (twistSys S x c)).res i) :=
    { toFun := fun y => ⟨Gm η M₀ n c hG hB i y.1 (Submodule.mem_inf.mp y.2).2,
        LinearMap.mem_ker.mpr (hker' _ _ (LinearMap.mem_ker.mp (Submodule.mem_inf.mp y.2).1))⟩
      map_zero' := Subtype.ext (funext fun K => Subtype.ext (gm_zero η M₀ n c i K))
      map_add' := fun a b => Subtype.ext (funext fun K => Subtype.ext (gm_add η M₀ n c i a.1 b.1 K)) }
  refine quot_retract _ _ f g ?_ ?_ ?_
  · intro z hz
    exact F_bdry η M₀ n c hG hB i z.1 hz
  · intro y hy
    exact G_bdry η M₀ n c hG hB i y.1 (Submodule.mem_inf.mp y.2).2 hy
  · intro z
    apply Subtype.ext
    funext K
    apply Subtype.ext
    exact gm_Fmap η M₀ n c hG hB i z.1 K

end Retract

theorem TwistSplit.proof : TwistSplit.Statement := by
  intro S _ _ Ω _ _ N x M₀ G B r η hG _ hB
  refine ⟨TwM η M₀, inferInstance, inferInstance, inferInstance, inferInstance, twGraded η M₀, inferInstance, ?_⟩
  intro b c i
  exact twist_retract η M₀ b c hG hB i

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleEmbedNumbers
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u w

theorem VeryAmpleEmbed.Numbers.proof (hSecs : VeryAmpleSecs.Statement.{u, w})
    (hHilb : VeryAmpleHilbert.Statement.{u, w}) : VeryAmpleEmbed.Numbers.Statement.{u, w} := by
  intro k _ Ω _ _ N y Q r h hV n hZ
  exact ⟨VeryAmpleDim.proof k Ω N y n Q r h hZ hV,
    VeryAmpleDegree.proof VeryAmpleDim.proof hSecs hHilb k Ω N y n Q r h hZ hV⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
end

