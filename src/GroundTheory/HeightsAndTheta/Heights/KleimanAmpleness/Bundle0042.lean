import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.RestrictionBundle
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0029
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0036
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0024
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0032
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0023
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0027
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPrimeFiltrationRestrict
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PExtension

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PRestriction
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

theorem zero_mem_ampleChart {S : Type u} [CommRing S] {E : Type w} [Field E] [Algebra S E] {M : ℕ}
    {z : Fin (M + 1) → E} {H : SubSystem S z E} {σ : E} {I : Chart z} :
    (0 : E) ∈ ampleChart H 1 σ I :=
  ⟨0, by rw [zero_mul]; exact Submodule.zero_mem _⟩

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {K' : Type w} [Field K']
  [Algebra k K'] {N : ℕ} {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'}

theorem exists_restrictData_isVeryAmpleBy (hsp : primeOf (S := k) x ≤ primeOf (S := k) y)
    (hxy : ∀ i, y i ≠ 0 → x i ≠ 0) (I₀ : Chart y) (Nb : LineBundle k x) {r : ℕ}
    (h : Fin (r + 1) → Ω) (hV : IsVeryAmpleBy Nb.toSubSystem h) :
    ∃ (Q' : LineBundle k y) (ρ : Ω → K'), RestrictData Nb.toSubSystem hxy Q'.toSubSystem ρ ∧
      IsVeryAmpleBy Q'.toSubSystem (ρ ∘ h) ∧ dimCl k y = dimCl k (ρ ∘ h) := by
  classical
  obtain ⟨l₀, hg0, hgl, hg⟩ := exists_redGood hsp hxy hV I₀
  obtain ⟨Q', hQ⟩ := exists_lineBundle_redSys hsp hxy hV hg0 hg (mem_sub_of_isVeryAmpleBy hV l₀)
  set g := h l₀ with hgdef
  set ρ : Ω → K' := fun q => redAt k x y (q / g) with hρ
  have hloc : ∀ {j : Fin (r + 1)} (_ : redAt k x y (h j / g) ≠ 0) {c : Ω},
      c ∈ ampleRing Nb.toSubSystem 1 (h j) →
        c ∈ locAt k x y ∧ redAt k x y c ∈ ampleBase (S := k) (ρ ∘ h) j := fun {j} hr {c} hc =>
    redAt_mem_ampleBase hsp hg0 hgl hr (hV.closed j (ne_zero_of_redAt_div hsp (hgl j) hr) hc)
  have hvery : IsVeryAmpleBy Q'.toSubSystem (ρ ∘ h) := by
    refine ⟨fun l => ?_, fun I => ?_, fun j hj => ?_, fun j hj => ?_⟩
    · refine (Submodule.mem_iInf _).mpr fun I => ?_
      rw [Submodule.restrictScalars_mem, hQ]
      exact Submodule.subset_span ⟨h l, mem_sub_of_isVeryAmpleBy hV l _, rfl⟩
    · rw [hQ, redSys_sub_eq hsp hxy hV hg]; rfl
    ·
      have hσ := hgl j
      have hσr : redAt k x y (h j / g) ≠ 0 := hj
      obtain ⟨n, a', b', J, ha', hb', hsum, hbJ⟩ :=
        hV.affine j (ne_zero_of_redAt_div hsp hσ hσr)
      intro a ha
      have hE : ∀ kk, ∃ E : ℕ, redAt k x y (b' kk) ^ (E + 1) * a ∈ ampleBase (S := k) (ρ ∘ h) j := by
        intro kk
        by_cases hbr : redAt k x y (b' kk) = 0
        · refine ⟨0, ?_⟩
          rw [hbr, zero_pow (Nat.succ_ne_zero 0), zero_mul]; exact zero_mem _
        · have hbl := (hloc hσr (hb' kk)).1
          have hJ := subset_support_of_redAt_ne_zero hsp hxy hg hσ hσr I₀ hbl hbr (hbJ kk)
          let Jy : Chart y := ⟨(J kk).1, (J kk).2.1, hJ⟩
          obtain ⟨e, he, hea⟩ :=
            exists_lift_ampleChart hsp hxy hg Q' hQ hσ hσr Jy (Set.mem_iInter.mp ha Jy)
          have hel := (redAt_mem_ampleChart hsp hxy hg Q' hQ hσ hσr Jy he).1
          obtain ⟨E, hEm⟩ := res_exists_pow_mul_mem_ampleRing Nb (hb' kk) (hbJ kk) (J := J kk) he
          have hm := hloc hσr hEm
          rw [(locAt_mul hsp (locAt_pow hsp hbl E).1 hel).2, (locAt_pow hsp hbl E).2, hea] at hm
          refine ⟨E, ?_⟩
          have : redAt k x y (b' kk) ^ (E + 1) * a =
              redAt k x y (b' kk) * (redAt k x y (b' kk) ^ E * a) := by ring
          rw [this]
          exact mul_mem (hloc hσr (hb' kk)).2 hm.2
      choose E hE using hE
      let T := Finset.univ.sup E + 1
      let β : Fin n → ampleBase (S := k) (ρ ∘ h) j :=
        fun kk => ⟨redAt k x y (b' kk), (hloc hσr (hb' kk)).2⟩
      let α : Fin n → ampleBase (S := k) (ρ ∘ h) j :=
        fun kk => ⟨redAt k x y (a' kk), (hloc hσr (ha' kk)).2⟩
      have hsum' : ∑ kk, α kk * β kk = 1 := by
        apply Subtype.ext
        rw [AddSubmonoidClass.coe_finsetSum, OneMemClass.coe_one]
        have h2 := (locAt_sum hsp Finset.univ (fun kk => a' kk * b' kk) fun kk _ =>
          (locAt_mul hsp (hloc hσr (ha' kk)).1 (hloc hσr (hb' kk)).1).1).2
        rw [hsum, (locAt_one hsp).2] at h2
        refine Eq.trans (Finset.sum_congr rfl fun kk _ => ?_) h2.symm
        rw [(locAt_mul hsp (hloc hσr (ha' kk)).1 (hloc hσr (hb' kk)).1).2]
        rfl
      have hspan : Ideal.span (Set.range β) = ⊤ := by
        rw [Ideal.eq_top_iff_one, ← hsum']
        exact Ideal.sum_mem _ fun kk _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨kk, rfl⟩)
      have hT := Ideal.span_pow_eq_top (Set.range β) hspan T
      let 𝔞 : Ideal (ampleBase (S := k) (ρ ∘ h) j) :=
        { carrier := {c | (c : K') * a ∈ ampleBase (S := k) (ρ ∘ h) j}
          add_mem' := fun {u v} hu hv => by
            simp only [Set.mem_ofPred_eq, AddMemClass.coe_add, add_mul] at hu hv ⊢
            exact add_mem hu hv
          zero_mem' := by
            simp only [Set.mem_ofPred_eq, ZeroMemClass.coe_zero, zero_mul]; exact zero_mem _
          smul_mem' := fun c u hu => by
            simp only [Set.mem_ofPred_eq, smul_eq_mul, MulMemClass.coe_mul, mul_assoc] at hu ⊢
            exact mul_mem c.2 hu }
      have hle : Ideal.span ((fun c => c ^ T) '' Set.range β) ≤ 𝔞 := by
        rw [Ideal.span_le]
        rintro _ ⟨_, ⟨kk, rfl⟩, rfl⟩
        show ((β kk ^ T : ampleBase (S := k) (ρ ∘ h) j) : K') * a ∈ ampleBase (S := k) (ρ ∘ h) j
        have hk : E kk + 1 ≤ T := Nat.succ_le_succ (Finset.le_sup (Finset.mem_univ kk))
        rw [SubmonoidClass.coe_pow, ← Nat.sub_add_cancel hk, pow_add, mul_assoc]
        exact mul_mem (pow_mem (β kk).2 _) (hE kk)
      have h1 : (1 : ampleBase (S := k) (ρ ∘ h) j) ∈ 𝔞 := hle (by rw [hT]; exact Submodule.mem_top)
      have h1' : ((1 : ampleBase (S := k) (ρ ∘ h) j) : K') * a ∈ ampleBase (S := k) (ρ ∘ h) j := h1
      rwa [OneMemClass.coe_one, one_mul] at h1'
    ·
      have hσ := hgl j
      have hσr : redAt k x y (h j / g) ≠ 0 := hj
      obtain ⟨n, a', b', J, ha', hb', hsum, hbJ⟩ :=
        hV.affine j (ne_zero_of_redAt_div hsp hσ hσr)
      have hred : ∀ {c : Ω}, c ∈ ampleRing Nb.toSubSystem 1 (h j) →
          redAt k x y c ∈ ampleRing Q'.toSubSystem 1 ((ρ ∘ h) j) := fun hc =>
        Set.mem_iInter.mpr fun I => (redAt_mem_ampleChart hsp hxy hg Q' hQ hσ hσr I
          (Set.mem_iInter.mp hc (liftChart hxy I))).2
      have hsupp : ∀ kk, redAt k x y (b' kk) ≠ 0 → (J kk).1 ⊆ support y := fun kk hbr =>
        subset_support_of_redAt_ne_zero hsp hxy hg hσ hσr I₀ (hloc hσr (hb' kk)).1 hbr (hbJ kk)
      refine ⟨n, fun kk => redAt k x y (a' kk),
        fun kk => if redAt k x y (b' kk) = 0 then 0 else redAt k x y (b' kk),
        fun kk => if hb : redAt k x y (b' kk) = 0 then I₀ else ⟨(J kk).1, (J kk).2.1, hsupp kk hb⟩,
        fun kk => hred (ha' kk), fun kk => ?_, ?_, fun kk I => ?_⟩
      · dsimp only
        split_ifs with hb
        · exact Set.mem_iInter.mpr fun I => zero_mem_ampleChart
        · exact hred (hb' kk)
      · have h2 := (locAt_sum hsp Finset.univ (fun kk => a' kk * b' kk) fun kk _ =>
          (locAt_mul hsp (hloc hσr (ha' kk)).1 (hloc hσr (hb' kk)).1).1).2
        rw [hsum, (locAt_one hsp).2] at h2
        refine Eq.trans (Finset.sum_congr rfl fun kk _ => ?_) h2.symm
        rw [(locAt_mul hsp (hloc hσr (ha' kk)).1 (hloc hσr (hb' kk)).1).2]
        dsimp only
        split_ifs with hb
        · rw [hb, mul_zero]
        · rfl
      · dsimp only
        by_cases hb : redAt k x y (b' kk) = 0
        · rw [if_pos hb, dif_pos hb]
          exact ⟨1, by rw [pow_one, zero_mul]; exact zero_mem_ampleChart⟩
        · rw [if_neg hb, dif_neg hb]
          obtain ⟨e, he⟩ := hbJ kk (liftChart hxy I)
          have hbl := (hloc hσr (hb' kk)).1
          have hJ := hsupp kk hb
          have hf := (res_isHomogeneous_prod_X (S := k) I.1).pow (J kk).1.card
          have hs : ((∏ l ∈ (J kk).1, (X l : Poly k N)) ^ I.1.card).IsHomogeneous
              (I.1.card * (J kk).1.card) := by
            rw [mul_comm]; exact (res_isHomogeneous_prod_X (S := k) (J kk).1).pow I.1.card
          have hsy : aeval y ((∏ l ∈ (J kk).1, (X l : Poly k N)) ^ I.1.card) ≠ 0 := by
            rw [map_pow, res_aeval_prod_X]
            exact pow_ne_zero _ (Finset.prod_ne_zero_iff.mpr fun i hi => (mem_support y).mp (hJ hi))
          have ht : xProd (liftChart hxy I) ^ (J kk).1.card / xProd (J kk) ^ (liftChart hxy I).1.card =
              aeval x ((∏ l ∈ I.1, (X l : Poly k N)) ^ (J kk).1.card) /
                aeval x ((∏ l ∈ (J kk).1, (X l : Poly k N)) ^ I.1.card) := by
            rw [map_pow, map_pow, res_aeval_prod_X, res_aeval_prod_X]; rfl
          obtain ⟨-, h2⟩ := redAt_mem_ampleChart hsp hxy hg Q' hQ hσ hσr I he
          rw [ht, (locAt_mul hsp (locAt_pow hsp hbl e).1 (mem_locAt hf hs hsy)).2,
            (locAt_pow hsp hbl e).2, redAt_eq hsp hf hs hsy, map_pow, map_pow, res_aeval_prod_X,
            res_aeval_prod_X] at h2
          exact ⟨e, h2⟩

  have hdim : funField (k := k) y = funField (k := k) (ρ ∘ h) := by
    obtain ⟨i₀, hi₀⟩ := I₀.2.1
    have hy₀ : y i₀ ≠ 0 := (mem_support y).mp (I₀.2.2 hi₀)
    have haeval : ∀ p : Poly k N, aeval (fun l => y l / y i₀) p ∈ funField (k := k) y := fun p =>
      MvPolynomial.induction_on (motive := fun p => aeval (fun l => y l / y i₀) p ∈ funField (k := k) y) p
        (fun c => by rw [aeval_C]; exact IntermediateField.algebraMap_mem _ c)
        (fun p q hp hq => by rw [map_add]; exact add_mem hp hq)
        (fun p l hp => by
          rw [map_mul, aeval_X]
          exact mul_mem hp (IntermediateField.subset_adjoin _ _ ⟨i₀, l, hy₀, rfl⟩))
    have hredF : ∀ {c : Ω}, c ∈ locAt k x y → redAt k x y c ∈ funField (k := k) y := by
      rintro _ ⟨f, s, e, hf, hs, hsy, rfl⟩
      rw [redAt_eq hsp hf hs hsy, ← div_div_div_cancel_right₀ (pow_ne_zero e hy₀),
        ← aeval_div_of_isHomogeneous hf i₀, ← aeval_div_of_isHomogeneous hs i₀]
      exact div_mem (haeval f) (haeval s)
    apply le_antisymm
    · have hg1' : redAt k x y (g / g) ≠ 0 := by
        rw [div_self hg0, (locAt_one hsp).2]; exact one_ne_zero
      obtain ⟨n, a', b', J, ha', hb', hsum, hbJ⟩ := hV.affine l₀ hg0
      have h2 := (locAt_sum hsp Finset.univ (fun kk => a' kk * b' kk) fun kk _ =>
          (locAt_mul hsp (hloc hg1' (ha' kk)).1 (hloc hg1' (hb' kk)).1).1).2
      rw [hsum, (locAt_one hsp).2] at h2
      have hne : ∑ kk, redAt k x y (a' kk * b' kk) ≠ 0 := by rw [← h2]; exact one_ne_zero
      obtain ⟨kk, -, hkk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
      rw [(locAt_mul hsp (hloc hg1' (ha' kk)).1 (hloc hg1' (hb' kk)).1).2] at hkk
      have hbr : redAt k x y (b' kk) ≠ 0 := right_ne_zero_of_mul hkk
      have hbl := (hloc hg1' (hb' kk)).1
      have hJ := subset_support_of_redAt_ne_zero hsp hxy hg (hgl l₀) hg1' I₀ hbl hbr (hbJ kk)
      obtain ⟨c, hc⟩ := (J kk).2.1
      have hyc : y c ≠ 0 := (mem_support y).mp (hJ hc)
      have hBF : ampleBase (S := k) (ρ ∘ h) l₀ ≤ (funField (k := k) (ρ ∘ h)).toSubalgebra := by
        refine Algebra.adjoin_le ?_
        rintro _ ⟨l, rfl⟩
        exact IntermediateField.subset_adjoin _ _ ⟨l₀, l, hg1', rfl⟩
      have hbF : redAt k x y (b' kk) ∈ funField (k := k) (ρ ∘ h) := hBF (hloc hg1' (hb' kk)).2
      have hratio : ∀ m, y m / y c ∈ funField (k := k) (ρ ∘ h) := by
        intro m
        have hmc : x m / x c ∈ chartRing k x (J kk) :=
          ⟨X m, X c, 1, X_mem_monos hc, isHomogeneous_X k m, isHomogeneous_X k c, by simp⟩
        obtain ⟨E, hE⟩ := res_exists_pow_mul_mem_ampleRing Nb (hb' kk) (hbJ kk)
          (res_chartRing_sub_ampleChart hmc)
        have hm := hloc hg1' hE
        have hsy : aeval y (X c : Poly k N) ≠ 0 := by rw [aeval_X]; exact hyc
        have hmcl : x m / x c ∈ locAt k x y := by
          have := mem_locAt (x := x) (isHomogeneous_X k m) (isHomogeneous_X k c) hsy
          simpa only [aeval_X] using this
        have hmcr : redAt k x y (x m / x c) = y m / y c := by
          have := redAt_eq hsp (isHomogeneous_X k m) (isHomogeneous_X k c) hsy
          simpa only [aeval_X] using this
        rw [(locAt_mul hsp (locAt_pow hsp hbl E).1 hmcl).2, (locAt_pow hsp hbl E).2, hmcr] at hm
        have hF := hBF hm.2
        have hbE : redAt k x y (b' kk) ^ E ≠ 0 := pow_ne_zero _ hbr
        have : y m / y c = (redAt k x y (b' kk) ^ E * (y m / y c)) / redAt k x y (b' kk) ^ E := by
          field_simp
        rw [this]
        exact div_mem hF (pow_mem hbF E)
      rw [funField, IntermediateField.adjoin_le_iff]
      rintro _ ⟨i, i', hi, rfl⟩
      rw [← div_div_div_cancel_right₀ hyc (y i') (y i)]
      exact div_mem (hratio i') (hratio i)
    · rw [funField, IntermediateField.adjoin_le_iff]
      rintro _ ⟨i, i', -, rfl⟩
      exact div_mem (hredF (hgl i')) (hredF (hgl i))
  refine ⟨Q', ρ, restrictData_redSys hsp hxy hg Q' hQ, hvery, ?_⟩
  rw [dimCl, dimCl, hdim]

theorem Restriction.proof : Restriction.Statement.{u, w} := by
  intro k _ Ω _ _ N x Nb r h hV pp _ _ _ j hj _ K' _ _ ψ _ hxy
  have hsp := primeOf_le_primeOf_of_algHom hj ψ
  have hyj : (fun i => ψ (ratio hj i)) j ≠ 0 := by
    show ψ (ratio hj j) ≠ 0
    rw [algHom_ratio_self]; exact one_ne_zero
  exact exists_restrictData_isVeryAmpleBy hsp hxy (singleChart hyj) Nb h hV

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PStepThreeOnWGen
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

namespace StepThree.OnW.Gen

section Helpers

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem sub_le_twist_idealSys_of_mem (F : SubSystem S x Ω) {pp : Ideal (Poly S N)} (I : Chart x)
    {i : Fin (N + 1)} (hi : i ∈ I.1) (hX : (X i : Poly S N) ∈ pp) :
    F.sub I ≤ (F.twist (idealSys x pp)).sub I := by
  intro z hz
  have hx : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  have h1 : (1 : Ω) ∈ idealMod (x := x) pp I :=
    Submodule.subset_span ⟨X i, X i, 1, hX, X_mem_monos hi, isHomogeneous_X S i, isHomogeneous_X S i, by
      rw [aeval_X, div_self hx]⟩
  exact Submodule.subset_span ⟨1, h1, z, hz, (one_smul Ω z).symm⟩

theorem primeOf_le_zeroIdeal (D : SubSystem S x Ω) (s : Ω) : primeOf (S := S) x ≤ zeroIdeal D s := by
  intro f hf
  rw [← sum_homogeneousComponent f]
  refine Ideal.sum_mem _ fun d _ => Ideal.subset_span ⟨d, homogeneousComponent_isHomogeneous d f, ?_⟩
  intro I δ _
  refine ⟨0, Submodule.zero_mem _, ?_⟩
  rw [(mem_primeOf_of_isHomogeneous x (homogeneousComponent_isHomogeneous d f)).mp
    (homogeneousComponent_mem_primeOf x hf d), zero_mul, mul_zero]

attribute [local instance] MvPolynomial.gradedAlgebra in

theorem homog_of_mem_minimalPrimes (D : SubSystem S x Ω) (s : Ω) {pp : Ideal (Poly S N)}
    (hpp : pp ∈ (zeroIdeal D s).minimalPrimes) :
    ∀ p ∈ pp, ∀ d : ℕ, homogeneousComponent d p ∈ pp := by
  have hJ : (zeroIdeal D s).IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) S) :=
    Ideal.homogeneous_span _ _ fun f ⟨c, hf, _⟩ => ⟨c, (mem_homogeneousSubmodule c f).mpr hf⟩
  have hcore : (pp.homogeneousCore (homogeneousSubmodule (Fin (N + 1)) S)).toIdeal.IsPrime :=
    hpp.1.1.homogeneousCore
  have hle : zeroIdeal D s ≤ (pp.homogeneousCore (homogeneousSubmodule (Fin (N + 1)) S)).toIdeal :=
    hJ.toIdeal_homogeneousCore_eq_self.symm.trans_le (Ideal.homogeneousCore_mono _ hpp.1.2)
  have heq : (pp.homogeneousCore (homogeneousSubmodule (Fin (N + 1)) S)).toIdeal = pp :=
    le_antisymm (Ideal.toIdeal_homogeneousCore_le _ _)
      (hpp.2 ⟨hcore, hle⟩ (Ideal.toIdeal_homogeneousCore_le _ _))
  have hW : pp.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) S) := by
    rw [Ideal.IsHomogeneous.iff_eq]
    exact heq
  intro p hp d
  have h := hW d hp
  have hc : (DirectSum.decompose (homogeneousSubmodule (Fin (N + 1)) S) p d : Poly S N) =
      homogeneousComponent d p := decomposition.decompose'_apply p d
  rwa [hc] at h

variable {K' : Type w} [Field K'] [Algebra S K'] {y : Fin (N + 1) → K'}

theorem exists_restrict_powBundle (hxy : ∀ i, y i ≠ 0 → x i ≠ 0)
    (hle : primeOf (S := S) x ≤ primeOf (S := S) y) (M : LineBundle S x) (M' : LineBundle S y)
    (r : Ω → K') (h : RestrictData M.toSubSystem hxy M'.toSubSystem r) (n : ℕ) :
    ∃ r' : Ω → K', RestrictData (M.powBundle n).toSubSystem hxy (M'.powBundle n).toSubSystem r' := by
  induction n with
  | zero => exact RestrictTwist.proof.1 S Ω N x K' y hxy hle 0
  | succ n ih =>
    obtain ⟨r', hr'⟩ := ih
    exact RestrictTwist.proof.2 S Ω N x K' y hxy _ M _ M' r' r hr' h

def twistMulBundle (M : LineBundle S x) (p : ℕ) (m : ℤ) : LineBundle S x :=
  (M.powBundle p).tensorProd (twistBundle S x m)

theorem twistMulBundle_toSubSystem (M : LineBundle S x) (p : ℕ) (m : ℤ) :
    (twistMulBundle M p m).toSubSystem = twistMul M.toSubSystem p m := by
  change (M.powBundle p).toSubSystem.twist (twistSys S x m) = _
  rw [LineBundle.powBundle_toSubSystem]
  rfl

theorem exists_restrict_twistMulBundle (hxy : ∀ i, y i ≠ 0 → x i ≠ 0)
    (hle : primeOf (S := S) x ≤ primeOf (S := S) y) (M : LineBundle S x) (M' : LineBundle S y)
    (r : Ω → K') (h : RestrictData M.toSubSystem hxy M'.toSubSystem r) (p : ℕ) (m : ℤ) :
    ∃ r' : Ω → K', RestrictData (twistMulBundle M p m).toSubSystem hxy
      (twistMulBundle M' p m).toSubSystem r' := by
  obtain ⟨rP, hrP⟩ := exists_restrict_powBundle hxy hle M M' r h p
  obtain ⟨rc, hrc⟩ := RestrictTwist.proof.1 S Ω N x K' y hxy hle m
  exact RestrictTwist.proof.2 S Ω N x K' y hxy _ (twistBundle S x m) _ (twistBundle S y m) rP rc hrP hrc

end Helpers

end StepThree.OnW.Gen

open StepThree.OnW.Gen in

theorem StepThree.OnW.Gen.proof (hRL : RestrLenRestrict.Statement.{u, w})
    (hRG : RestrictGenerated.Statement.{u, w}) : StepThree.OnW.Gen.Statement.{u, w} := by
  intro k _ Ω _ _ N x T hK pp hpp
  have hpr : pp.IsPrime := hpp.1.1
  have hhom := homog_of_mem_minimalPrimes T.D T.si hpp
  have hle : primeOf (S := k) x ≤ pp := (primeOf_le_zeroIdeal T.D T.si).trans hpp.1.2
  by_cases hrel : ∃ j, (X j : Poly k N) ∉ pp
  swap
  · push Not at hrel
    refine ⟨0, fun b c _ _ I => ?_⟩
    obtain ⟨i, hi⟩ := I.2.1
    exact le_sup_of_le_right (sub_le_twist_idealSys_of_mem _ I hi (hrel i))
  obtain ⟨j, hjp⟩ := hrel
  have hj : x j ≠ 0 := fun h0 => hjp (hle ((mem_primeOf_of_isHomogeneous x (isHomogeneous_X k j)).mpr
    (by rw [aeval_X]; exact h0)))
  obtain ⟨hcp, hpt⟩ := PrimeFiltration.Point.proof k Ω N x pp hpr hhom hle j hj hjp

  have := hcp
  let A := chartRing k x (singleChart hj)
  let Ip : Ideal A := chartPrime pp hj
  let ψ : A →ₐ[k] Ip.ResidueField := IsScalarTower.toAlgHom k A Ip.ResidueField
  have hker : RingHom.ker ψ = Ip := Ideal.ker_algebraMap_residueField Ip
  have hxy : ∀ i, ψ (ratio hj i) ≠ 0 → x i ≠ 0 := by
    intro i h hx
    apply h
    have h0 : ratio (S := k) hj i = 0 := Subtype.ext (by change x i / x j = 0; rw [hx, zero_div])
    rw [h0, map_zero]
  have hpy : primeOf (S := k) (fun i => ψ (ratio hj i)) = pp := hpt _ ψ hker
  have hxy' : primeOf (S := k) x ≤ primeOf (S := k) (fun i => ψ (ratio hj i)) := hpy ▸ hle

  obtain ⟨f, e₀, hfJ, hfh, hfq⟩ := StepData.JProper.proof k Ω N x T
  obtain ⟨e, he, hsub⟩ :=
    SubvarDrop.proof k Ω N x T.d pp T.dim hpr hhom hle ⟨j, hjp⟩ ⟨f, hpp.1.2 hfJ, hfq⟩
  have hsubW : IsSubvar (fun i => ψ (ratio hj i)) (primeOf (S := k) (fun i => ψ (ratio hj i))) e := by
    rw [hpy]
    exact ⟨hsub.isPrime, hsub.homog, le_of_eq hpy, hsub.relevant, hsub.dim⟩

  obtain ⟨M', rM, hM'⟩ := PrimeFiltration.Restrict.proof k Ω N x pp hpr hhom hle j hj hjp _ ψ hker hxy T.M
  have hRM : RestrictData T.M.toSubSystem hxy M'.toSubSystem rM :=
    ⟨fun I => (hM' I).1, fun I => (hM' I).2.1, fun I => (hM' I).2.2.1, fun I => (hM' I).2.2.2⟩
  have hnef : Nef M'.toSubSystem :=
    NefRestrict.proof RestrictTwist.proof hRL k Ω N x _ _ hxy hxy' T.M M' rM hRM T.nef

  have hts : 0 < T.t - T.s' := by
    have hd : (1 : ℚ) ≤ (T.d : ℚ) + 1 := by
      have := (Nat.cast_nonneg T.d : (0 : ℚ) ≤ T.d); linarith
    have ht : 0 < T.t := by
      by_contra hneg'
      have hneg : T.t ≤ 0 := not_lt.mp hneg'
      have : T.t / ((T.d : ℚ) + 1) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hneg (by positivity)
      linarith [T.s'_pos, T.s'_lt]
    have : T.t / ((T.d : ℚ) + 1) ≤ T.t := div_le_self ht.le hd
    linarith [T.s'_lt]
  obtain ⟨q, m', hq, hm', hva⟩ := hK e he _ N _ M' hsubW hnef (T.t - T.s') hts
  obtain ⟨rr, h, hvb⟩ := hva
  have hqm : (q : ℤ) * T.m = T.p * m' := by
    have : (((q : ℤ) * T.m : ℤ) : ℚ) = ((T.p * m' : ℤ) : ℚ) := by
      push_cast; rw [T.m_eq, hm']; ring
    exact_mod_cast this

  have hBgen : (twistMul M'.toSubSystem q m').Generated := fun I => le_antisymm
    (Submodule.span_le.mpr fun z hz => KThm.mem_sub_of_mem_secs hz I)
    (by rw [← hvb.generates I]; exact Submodule.span_mono (Set.range_subset_iff.mpr hvb.mem_secs))

  have hv : ∀ b₂ : ℕ, ∃ c₀ : ℤ, ∀ c : ℤ, c₀ ≤ c →
      (((twistMul M'.toSubSystem T.p T.m).pow b₂).twist
        (twistSys k (fun i => ψ (ratio hj i)) c)).Generated := by
    intro b₂
    obtain ⟨c₀, hc₀⟩ := Generated.proof Extension.proof k _ N _ ((twistMulBundle M' T.p T.m).powBundle b₂)
    refine ⟨c₀, fun c hc => ?_⟩
    have hs := hc₀ c hc
    rwa [LineBundle.powBundle_toSubSystem, twistMulBundle_toSubSystem] at hs
  choose cv hcv using hv
  refine ⟨∑ b₂ ∈ Finset.range q, |cv b₂|, fun b c _ hc I => ?_⟩

  obtain ⟨rL, hrL⟩ := exists_restrict_twistMulBundle hxy hxy' T.M M' rM hRM T.p T.m
  obtain ⟨rb, hrb⟩ := exists_restrict_powBundle hxy hxy' _ _ rL hrL b
  obtain ⟨rc, hrc⟩ := RestrictTwist.proof.1 k Ω N x _ _ hxy hxy' c
  obtain ⟨r'', hr''⟩ := RestrictTwist.proof.2 k Ω N x _ _ hxy _ (twistBundle k x c) _
    (twistBundle k (fun i => ψ (ratio hj i)) c) rb rc hrb hrc
  have hQ : ((twistMulBundle T.M T.p T.m).powBundle b).toSubSystem.twist (twistSys k x c) =
      (T.L.pow b).twist (twistSys k x c) := by
    rw [LineBundle.powBundle_toSubSystem, twistMulBundle_toSubSystem]
    rfl
  have hlt : b % q < q := Nat.mod_lt b (by omega)
  have hcb : cv (b % q) ≤ c :=
    le_trans (le_abs_self _) (le_trans (Finset.single_le_sum (f := fun b₂ => |cv b₂|)
      (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr hlt)) hc)
  have hW : (twistMul M'.toSubSystem T.p T.m).pow b = ((twistMul M'.toSubSystem T.p T.m).pow (b % q)).twist
      ((twistMul M'.toSubSystem q m').pow (T.p * (b / q))) := by
    rw [← TwistAlg.proof k _ N _ M'.toSubSystem T.p q T.m m' (b / q) (b % q) hqm, Nat.div_add_mod b q]
  have hgen : (((twistMulBundle M' T.p T.m).powBundle b).tensorProd
      (twistBundle k (fun i => ψ (ratio hj i)) c)).toSubSystem.Generated := by
    change (((twistMulBundle M' T.p T.m).powBundle b).toSubSystem.twist
      (twistSys k (fun i => ψ (ratio hj i)) c)).Generated
    rw [LineBundle.powBundle_toSubSystem, twistMulBundle_toSubSystem, hW, SubSystem.twist_assoc,
      SubSystem.twist_comm ((twistMul M'.toSubSystem q m').pow (T.p * (b / q))), ← SubSystem.twist_assoc]
    exact KThm.generated_twist (hcv _ c hcb) (KThm.generated_pow hBgen _)
  have key := hRG k Ω N x _ _ hxy pp hle hpy (((twistMulBundle T.M T.p T.m).powBundle b).tensorProd
    (twistBundle k x c))
    (((twistMulBundle M' T.p T.m).powBundle b).tensorProd (twistBundle k (fun i => ψ (ratio hj i)) c)) r'' hr''
    hgen I
  have hQ' : (((twistMulBundle T.M T.p T.m).powBundle b).tensorProd (twistBundle k x c)).toSubSystem =
      (T.L.pow b).twist (twistSys k x c) := hQ
  rw [hQ'] at key
  exact key

end

end GroundTheory.Heights₂.Heights.Kleiman
end

