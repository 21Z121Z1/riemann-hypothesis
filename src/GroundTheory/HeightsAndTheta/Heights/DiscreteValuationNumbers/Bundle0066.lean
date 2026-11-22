import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0065
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0049
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpLocalChart
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.LiftFormNotMemBlowUpOf
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0060
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0063
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0050
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0046
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagCutSpecialize
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0052
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0013
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0056
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0051
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagConeAlg
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagCutTools
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0032
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0058

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpOverLocFamilyFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem prime_eq_or_eq_of_le_mem_minimalPrimes_sup_span {A : Type*} [CommRing A] [IsNoetherianRing A]
    {P W Q : Ideal A} (hP : P.IsPrime) (hQ : Q.IsPrime) {x : A}
    (hW : W ∈ (P ⊔ Ideal.span {x}).minimalPrimes) (hPQ : P ≤ Q) (hQW : Q ≤ W) : Q = P ∨ Q = W := by
  by_contra h
  rw [not_or] at h
  obtain ⟨hQP, hQW'⟩ := h
  have hWp : W.IsPrime := hW.1.1
  let f := Ideal.Quotient.mk P
  have hf : Function.Surjective f := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker f ≤ Q := by rw [Ideal.mk_ker]; exact hPQ
  have hkerW : RingHom.ker f ≤ W := hker.trans hQW
  have : (Q.map f).IsPrime := Ideal.map_isPrime_of_surjective hf hker
  have : (W.map f).IsPrime := Ideal.map_isPrime_of_surjective hf hkerW
  have : (⊥ : Ideal (A ⧸ P)).IsPrime := Ideal.isPrime_bot
  have h1 : (⊥ : Ideal (A ⧸ P)) < Q.map f := by
    refine bot_lt_iff_ne_bot.mpr fun h0 => hQP (le_antisymm (fun q hq => ?_) hPQ)
    have hq' : f q ∈ Q.map f := Ideal.mem_map_of_mem f hq
    rw [h0, Ideal.mem_bot] at hq'
    exact Ideal.Quotient.eq_zero_iff_mem.mp hq'
  have h2 : Q.map f < W.map f := by
    refine lt_of_le_of_ne (Ideal.map_mono hQW) fun e => hQW' ?_
    have e' := congrArg (Ideal.comap f) e
    rwa [Ideal.comap_map_of_surjective' f hf, Ideal.comap_map_of_surjective' f hf,
      sup_eq_left.mpr hker, sup_eq_left.mpr hkerW] at e'
  have e1 := Ideal.height_add_one_le_of_lt_of_isPrime h1
  have e2 := Ideal.height_add_one_le_of_lt_of_isPrime h2
  have e3 := Ideal.map_height_le_one_of_mem_minimalPrimes hW
  rw [Ideal.height_bot] at e1
  have e4 : (0 : ℕ∞) + 1 + 1 ≤ 1 := ((add_le_add e1 le_rfl).trans e2).trans e3
  norm_num at e4

theorem eq_blowUpOf_of_comap_liftForm_le {K : Type} [DecidableEq K] {ι : K → Type} {J : Type} {R : Type*}
    [CommRing R] {P : Ideal (MRing ι R)} {u : J → MRing ι R} {Q : Ideal (MRing (extIdx ι J) R)}
    (hQp : Q.IsPrime) (hQh : IsMultiHomogIdeal Q) (hle : blowUpOf P u ≤ Q) {j : J}
    (hj : (newVar j : MRing (extIdx ι J) R) ∉ Q)
    (hc : Q.comap (liftForm (ι := ι) (J := J) (R := R)) ≤ P) : Q = blowUpOf P u := by
  classical
  refine le_antisymm (fun F hF => ?_) hle
  have hcomp : ∀ b, weightedHomogeneousComponent (blockWeight (extIdx ι J)) b F ∈ blowUpOf P u := by
    intro b
    set G := weightedHomogeneousComponent (blockWeight (extIdx ι J)) b F
    have hG : IsMultiHomog G b := weightedHomogeneousComponent_isWeightedHomogeneous _ _
    have hGQ : G ∈ Q := hQh F hF b
    obtain ⟨f, hf⟩ := Ideal.Quotient.mk_surjective (blowUpEval P u G)
    have hrel : liftForm (u j) ^ (b none) * G - newVar j ^ (b none) * liftForm f ∈ blowUpOf P u := by
      rw [blowUpOf, RingHom.mem_ker, map_sub, map_mul, map_mul, map_pow, map_pow,
        aeval_blowUpSubst_of_isMultiHomog P u hG, aeval_blowUpSubst_liftForm, aeval_blowUpSubst_liftForm,
        aeval_blowUpSubst_newVar, ← hf]
      ring
    have h1 : newVar j ^ (b none) * liftForm f ∈ Q := by
      have h := Q.sub_mem (Q.mul_mem_left (liftForm (u j) ^ (b none)) hGQ) (hle hrel)
      rwa [sub_sub_cancel] at h
    have h2 : liftForm f ∈ Q :=
      (hQp.mem_or_mem h1).resolve_left fun h => hj (hQp.mem_of_pow_mem _ h)
    have h3 : f ∈ P := hc h2
    rw [blowUpOf, RingHom.mem_ker, aeval_blowUpSubst_of_isMultiHomog P u hG, ← hf,
      Ideal.Quotient.eq_zero_iff_mem.mpr h3, map_zero, zero_mul]
  rw [← sum_weightedHomogeneousComponent (blockWeight (extIdx ι J)) F]
  exact finsum_induction (· ∈ blowUpOf P u) (Submodule.zero_mem _) (fun _ _ => Submodule.add_mem _) hcomp

theorem BlowUpOverLocFamilyFinite.proof (h₁ : BlowUpOverLocFibreFinite.Statement.{u}) :
    BlowUpOverLocFamilyFinite.Statement.{u} := by
  intro O _ _ _ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP W hWmin hWrel
  have hPp : P.IsPrime := hP.multiProj.isPrime
  refine ((Set.finite_singleton (blowUpOf P u)).union
    (h₁ O K ι J P n hP N u hu hu' c x hx hxP W hWmin hWrel)).subset ?_
  rintro Q ⟨hQp, hQh, hQr, hQle, hQW⟩
  obtain ⟨hcp, hPc, -, j, hj⟩ := comap_liftForm_facts hQp hQle hQr
  rcases prime_eq_or_eq_of_le_mem_minimalPrimes_sup_span hPp hcp hWmin hPc hQW with h | h
  · exact Or.inl (eq_blowUpOf_of_comap_liftForm_le hQp hQh hQle hj h.le)
  · exact Or.inr ⟨hQp, hQh, hQr, hQle, h⟩

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpOverLocLocalization
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem BlowUpOverLocLocalization.proof (hfam : BlowUpOverLocFamilyFinite.Statement.{u}) :
    BlowUpOverLocLocalization.Statement.{u} := by
  intro O _ _ _ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP W hWmin hWrel
  have := hP.multiProj.isPrime
  intro W' hW'p hmh hW'rel hbl hW'W
  have hW'fam : W'.IsPrime ∧ IsMultiHomogIdeal W' ∧ IsRelevant W' ∧ blowUpOf P u ≤ W' ∧
      W'.comap (liftForm (ι := ι) (J := J) (R := O)) ≤ W := ⟨hW'p, hmh, hW'rel, hbl, hW'W⟩
  have hBR : blowUpOverLoc P W u ≤ blowUpLocRing P u W' := iInf₂_le W' hW'fam
  obtain ⟨e, L, hL, he, hLQ⟩ := MultiHomogPrimeAvoid.proof O (Option K) (extIdx ι J) _
    (hfam O K ι J P n hP N u hu hu' c x hx hxP W hWmin hWrel) (fun Q hQ => ⟨hQ.1, hQ.2.1, hQ.2.2.1⟩)
  have : (blowUpOf P u).IsPrime := RingHom.ker_isPrime _
  obtain ⟨φ, hφ⟩ := BlowUpLocRingIso.proof O K ι J P u W' hbl
  obtain ⟨hlocT, -⟩ :=
    HomLocRingIsLocal.proof HomLocRingMem.proof O (Option K) (extIdx ι J) (blowUpOf P u) W' hW'p hbl
  have : IsLocalRing (blowUpLocRing P u W') := φ.isLocalRing

  have hne : ∀ (d : Option K → ℕ) (H : MRing (extIdx ι J) O), IsMultiHomog H d → H ∉ W' →
      algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u H) ≠ 0 := by
    intro d H hH hHW h0
    have h1 := hφ d H H hH hH hHW
    rw [h0, div_zero] at h1
    have h2 : (⟨_, Subring.subset_closure ⟨d, H, H, hH, hH, hHW, rfl⟩⟩ :
        homLocRing (blowUpOf P u) W') = 1 := by
      apply Subtype.ext
      show _ / _ = (1 : FractionRing (MRing (extIdx ι J) O ⧸ blowUpOf P u))
      apply div_self
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]
      exact fun h => hHW (hbl h)
    rw [h2, map_one] at h1
    exact one_ne_zero h1

  have hgen : ∀ (b : Option K → ℕ) (F G : MRing (extIdx ι J) O), IsMultiHomog F b → IsMultiHomog G b →
      G ∉ W' → ∃ bb ∈ blowUpOverLoc P W u, ∃ s ∈ blowUpOverLoc P W u,
        (∃ t ∈ blowUpLocRing P u W', s * t = 1) ∧
        algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u F) /
          algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u G) * s = bb := by
    intro b F G hF hG hGW
    set k := ∑ o, b o with hk
    obtain ⟨M, hM, hMW⟩ := homLocRing_form_not_mem hW'p hW'rel (fun o => k * e o - b o)
    have hdeg : b + (fun o => k * e o - b o) = k • e := by
      funext o
      have : b o ≤ k * e o := le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ o)) (Nat.le_mul_of_pos_right _ (he o))
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      omega
    have hFM : IsMultiHomog (F * M) (k • e) := hdeg ▸ hF.mul hM
    have hGM : IsMultiHomog (G * M) (k • e) := hdeg ▸ hG.mul hM
    have hLk : IsMultiHomog (L ^ k) (k • e) := hL.pow k
    have hLkQ : ∀ Q : Ideal (MRing (extIdx ι J) O), Q.IsPrime ∧ IsMultiHomogIdeal Q ∧ IsRelevant Q ∧
        blowUpOf P u ≤ Q ∧ Q.comap (liftForm (ι := ι) (J := J) (R := O)) ≤ W → L ^ k ∉ Q :=
      fun Q hQ h => hLQ Q hQ (hQ.1.mem_of_pow_mem k h)
    have hmemB : ∀ H, IsMultiHomog H (k • e) →
        algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u H) /
          algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (blowUpEval P u (L ^ k)) ∈
          blowUpOverLoc P W u := fun H hH =>
      Subring.mem_iInf.mpr fun Q => Subring.mem_iInf.mpr fun hQ =>
        Subring.subset_closure ⟨k • e, H, L ^ k, hH, hLk, hLkQ Q hQ, rfl⟩
    have hGMW : G * M ∉ W' := fun h => (hW'p.mem_or_mem h).elim hGW hMW
    have hLkW : L ^ k ∉ W' := hLkQ W' hW'fam
    have hG0 := hne _ _ hG hGW
    have hGM0 := hne _ _ hGM hGMW
    have hLk0 := hne _ _ hLk hLkW
    refine ⟨_, hmemB _ hFM, _, hmemB _ hGM, ⟨_,
      Subring.subset_closure ⟨k • e, L ^ k, G * M, hLk, hGM, hGMW, rfl⟩, ?_⟩, ?_⟩
    · rw [div_mul_div_comm, mul_comm]
      exact div_self (mul_ne_zero hLk0 hGM0)
    · rw [map_mul, map_mul] at hGM0 ⊢
      rw [map_mul, map_mul]
      field_simp

  have hfrac : ∀ z ∈ blowUpLocRing P u W', ∃ b ∈ blowUpOverLoc P W u, ∃ s ∈ blowUpOverLoc P W u,
      (∃ t ∈ blowUpLocRing P u W', s * t = 1) ∧ z * s = b := by
    intro z hz
    induction hz using Subring.closure_induction with
    | mem z hz =>
      obtain ⟨b, F, G, hF, hG, hGW, rfl⟩ := hz
      exact hgen b F G hF hG hGW
    | zero => exact ⟨0, zero_mem _, 1, one_mem _, ⟨1, one_mem _, mul_one 1⟩, zero_mul 1⟩
    | one => exact ⟨1, one_mem _, 1, one_mem _, ⟨1, one_mem _, mul_one 1⟩, one_mul 1⟩
    | add x y _ _ h₁ h₂ =>
      obtain ⟨b₁, hb₁, s₁, hs₁, ⟨t₁, ht₁, hst₁⟩, hx₁⟩ := h₁
      obtain ⟨b₂, hb₂, s₂, hs₂, ⟨t₂, ht₂, hst₂⟩, hx₂⟩ := h₂
      refine ⟨b₁ * s₂ + b₂ * s₁, add_mem (mul_mem hb₁ hs₂) (mul_mem hb₂ hs₁), s₁ * s₂, mul_mem hs₁ hs₂,
        ⟨t₁ * t₂, mul_mem ht₁ ht₂, by rw [mul_mul_mul_comm, hst₁, hst₂, one_mul]⟩, ?_⟩
      rw [← hx₁, ← hx₂]
      ring
    | neg x _ h =>
      obtain ⟨b₁, hb₁, s₁, hs₁, ht, hx₁⟩ := h
      exact ⟨-b₁, neg_mem hb₁, s₁, hs₁, ht, by rw [← hx₁]; ring⟩
    | mul x y _ _ h₁ h₂ =>
      obtain ⟨b₁, hb₁, s₁, hs₁, ⟨t₁, ht₁, hst₁⟩, hx₁⟩ := h₁
      obtain ⟨b₂, hb₂, s₂, hs₂, ⟨t₂, ht₂, hst₂⟩, hx₂⟩ := h₂
      refine ⟨b₁ * b₂, mul_mem hb₁ hb₂, s₁ * s₂, mul_mem hs₁ hs₂,
        ⟨t₁ * t₂, mul_mem ht₁ ht₂, by rw [mul_mul_mul_comm, hst₁, hst₂, one_mul]⟩, ?_⟩
      rw [← hx₁, ← hx₂]
      ring

  let 𝔭 : Ideal (blowUpOverLoc P W u) :=
    (IsLocalRing.maximalIdeal (blowUpLocRing P u W')).comap (Subring.inclusion hBR)
  have h𝔭 : 𝔭.IsPrime := Ideal.comap_isPrime _ _
  refine ⟨hBR, 𝔭, h𝔭, ?_⟩
  letI := (Subring.inclusion hBR).toAlgebra
  refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨s, hs⟩
    by_contra h
    exact hs ((IsLocalRing.mem_maximalIdeal _).mpr h)
  · rintro ⟨z, hz⟩
    obtain ⟨b, hb, s, hs, ⟨t, ht, hst⟩, hzs⟩ := hfrac z hz
    refine ⟨(⟨b, hb⟩, ⟨⟨s, hs⟩, ?_⟩), Subtype.ext hzs⟩
    intro hm
    have hm' := (IsLocalRing.mem_maximalIdeal _).mp hm
    exact hm' (IsUnit.of_mul_eq_one (⟨t, ht⟩ : blowUpLocRing P u W') (Subtype.ext hst))
  · intro a a' h
    exact ⟨1, by rw [Subring.inclusion_injective hBR h]⟩

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagCutDivisor
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

open FlagBundleSectionDivProof GenericProjClosureDivisor in

theorem SegreFlagCutDivisor.proof (hSpec : SegreFlagCutSpecialize.Statement)
    (hChart : SegreFlagCutChart.Statement) : SegreFlagCutDivisor.Statement := by
  have hModel : SegreFlagClosureModel.Statement :=
    SegreFlagClosureModel.proof (SegreFlagClosureTrdeg.proof SegreFlagConeAlg.proof)
  have hSat : MultAtOfSaturated.Statement.{0} := MultAtOfSaturated.proof
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ'
    Φ _ _ _ _ e t ht k hk cs ch s h hs hh hdeg hsP hhP hval W hW
  classical
  have hPp : (pointIdeal O (flagClosurePt y w e φ φ' t (k + 1))).IsPrime := RingHom.ker_isPrime _
  have hQp : (pointIdeal O (flagClosurePt y w e φ φ' t k)).IsPrime := RingHom.ker_isPrime _
  obtain ⟨hPQ, hspec⟩ := hSpec O ϖ hϖ Ω K ι y d hV N E B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ'
    Φ e t ht k hk
  have hτ : flagLineCoord w' w e t (k + 1) ⟨k, hk⟩ ≠ 0 := by
    intro h0
    exact hsP (mem_of_homog hs (by rw [hval, h0, zero_mul]))
  by_cases hWc : W.IsPrime ∧ IsRelevant W ∧ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) ≤ W
  · obtain ⟨hWp, hWrel, hPW⟩ := hWc
    obtain ⟨cl, cm, l, μ, u, hl, hμ, hdl, hμW, huW, hlv, hl0, hsat⟩ :=
      hChart O ϖ hϖ Ω K ι y d hV N E B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht k hk W
        hWp hWrel hPW hW
    have hμP : μ ∉ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) := fun h' => hμW (hPW h')
    have hlP : l ∉ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) := by
      intro h'
      have h0 := aeval_eq_zero_of_mem h'
      rw [hlv] at h0
      exact hμP (mem_of_homog hμ ((mul_eq_zero.mp h0).resolve_left hτ))
    have huW' : ∀ n : ℕ, u ^ n ∉ W := fun n h' => huW (hWp.mem_of_pow_mem n h')
    have hdeg' : cs + cm = cl + ch := by
      funext o
      have h1 := congrFun hdeg o
      have h2 := congrFun hdl o
      simp only [Pi.add_apply] at h1 h2 ⊢
      omega
    have hdiff : s * μ - l * h ∈ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) := by
      have h2 := hl.mul hh
      rw [← hdeg'] at h2
      refine mem_of_homog (b := cs + cm) ((mem_weightedHomogeneousSubmodule _ _ _ _).mp
        (Submodule.sub_mem _ ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr (hs.mul hμ))
          ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr h2))) ?_
      rw [map_sub, map_mul, map_mul, hval, hlv]
      ring
    rw [ratDiv_eq_of_sub_mem hsP hhP hlP hμP hdiff]
    unfold ratDiv
    rw [divCycle_eq_zero_of_not_mem hμW, sub_zero]
    have hlQ : 0 < k → l ∈ pointIdeal O (flagClosurePt y w e φ φ' t k) := fun _ =>
      mem_of_homog hl (hspec l μ hlv)
    split_ifs with hc
    · obtain ⟨hkpos, rfl⟩ := hc
      obtain ⟨hmin, hmult⟩ := hSat O (Option (Option K)) (bundleIdx (bundleIdx ι M) M') _ _
        (sup_le hPQ ((Ideal.span_singleton_le_iff_mem _).mpr (hlQ hkpos)))
        (fun q hq => by
          obtain ⟨n, hn⟩ := hsat hkpos q hq
          exact ⟨_, huW' n, hn⟩)
      unfold divCycle
      rw [dif_pos ⟨hmin, hWrel⟩, hmult]
      rfl
    · by_contra hne
      have hmin : W ∈ (pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) ⊔ Ideal.span {l}).minimalPrimes := by
        unfold divCycle at hne
        split_ifs at hne with h'
        · exact h'.1
        · exact absurd rfl hne
      have hlW : l ∈ W := hmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self l))
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · exact hl0 hk0 hlW
      · have hQW : pointIdeal O (flagClosurePt y w e φ φ' t k) ≤ W := fun q hq => by
          obtain ⟨n, hn⟩ := hsat hkpos q hq
          exact (hWp.mem_or_mem (hmin.1.2 hn)).resolve_left (huW' n)
        have hPQ' : pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) <
            pointIdeal O (flagClosurePt y w e φ φ' t k) :=
          lt_of_le_of_ne hPQ (fun h' => hlP (by rw [h']; exact hlQ hkpos))
        exact hc ⟨hkpos, (eq_of_lt_of_le_of_mem_minimalPrimes hmin hPQ' hQW).symm⟩
  · have h0 : ∀ z, divCycle (pointIdeal O (flagClosurePt y w e φ φ' t (k + 1))) z W = 0 := fun z => by
      unfold divCycle
      rw [dif_neg]
      rintro ⟨h', hr⟩
      exact hWc ⟨h'.1.1, hr, le_sup_left.trans h'.1.2⟩
    have hWQ : ¬ (0 < k ∧ W = pointIdeal O (flagClosurePt y w e φ φ' t k)) := by
      rintro ⟨hkpos, rfl⟩
      exact hWc ⟨hQp, (hModel O ϖ hϖ Ω K ι y d hV N E B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ'
        Φ e t ht k hkpos hk.le).1.multiProj.relevant, hPQ⟩
    rw [if_neg hWQ]
    simp [ratDiv, h0]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagCutLiesOver
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace SegreFlagCutLiesOverProof

variable {κ : Type} [Fintype κ] [DecidableEq κ] {ικ : κ → Type} [∀ o, Fintype (ικ o)] {O : Type} [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] {Φ : Type} [Field Φ] [Algebra O Φ]

theorem le_comap_of_chart (pt : (Σ o, ικ o) → Φ) {A F : Type*} [CommRing A] [FunLike F A (MRing ικ O)]
    [RingHomClass F A (MRing ικ O)] (ρ : F) (Q : Ideal A) (u : MRing ικ O) (τ : Φ) {cs ch dl dm : κ → ℕ}
    {s h l μ : MRing ικ O} (hs : IsMultiHomog s cs) (hh : IsMultiHomog h ch) (hl : IsMultiHomog l dl)
    (hμ : IsMultiHomog μ dm) (hdeg : cs + dm = dl + ch) (hsP : s ∉ pointIdeal O pt)
    (hhP : h ∉ pointIdeal O pt) (hsv : aeval pt s = τ * aeval pt h) (hlv : aeval pt l = τ * aeval pt μ)
    (hsat : ∀ q ∈ Q, ∃ n : ℕ, u ^ n * ρ q ∈ pointIdeal O pt ⊔ Ideal.span {l})
    {W : Ideal (MRing ικ O)} (hμW : μ ∉ W) (huW : ∀ n : ℕ, u ^ n ∉ W)
    (hPW : pointIdeal O pt ≤ W) (hW : ratDiv (pointIdeal O pt) s h W ≠ 0) : Q ≤ W.comap ρ := by
  have : (pointIdeal O pt).IsPrime := RingHom.ker_isPrime _
  have hμP : μ ∉ pointIdeal O pt := fun h' => hμW (hPW h')
  have hsv0 : aeval pt s ≠ 0 := fun h0 => hsP (GenericProjClosureDivisor.mem_of_homog hs h0)
  have hτ : τ ≠ 0 := by
    rintro rfl
    exact hsv0 (by rw [hsv, zero_mul])
  have hμv : aeval pt μ ≠ 0 := fun h0 => hμP (GenericProjClosureDivisor.mem_of_homog hμ h0)
  have hlP : l ∉ pointIdeal O pt := fun h' =>
    mul_ne_zero hτ hμv (hlv ▸ GenericProjClosureDivisor.aeval_eq_zero_of_mem h')
  have hdiff : s * μ - l * h ∈ pointIdeal O pt := by
    have h2 := hl.mul hh
    rw [← hdeg] at h2
    have h1 : IsMultiHomog (s * μ - l * h) (cs + dm) :=
      (mem_weightedHomogeneousSubmodule _ _ _ _).mp (Submodule.sub_mem _
        ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr (hs.mul hμ))
        ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr h2))
    refine GenericProjClosureDivisor.mem_of_homog h1 ?_
    rw [map_sub, map_mul, map_mul, hsv, hlv]
    ring
  have hrat := congrFun (ratDiv_eq_of_sub_mem hsP hhP hlP hμP hdiff) W
  have hμ0 : divCycle (pointIdeal O pt) μ W = 0 := by
    unfold divCycle
    rw [dif_neg]
    rintro ⟨h', -⟩
    exact hμW (h'.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self μ)))
  have hl0 : divCycle (pointIdeal O pt) l W ≠ 0 := by
    rw [hrat] at hW
    unfold ratDiv at hW
    rwa [hμ0, sub_zero] at hW
  have hmin : W ∈ (pointIdeal O pt ⊔ Ideal.span {l}).minimalPrimes := by
    unfold divCycle at hl0
    split_ifs at hl0 with h'
    · exact h'.1
    · exact absurd rfl hl0
  have hWp : W.IsPrime := hmin.1.1
  intro q hq
  obtain ⟨n, hn⟩ := hsat q hq
  exact (hWp.mem_or_mem (hmin.1.2 hn)).resolve_left (huW n)

omit [Fintype κ] [DecidableEq κ] [∀ o, Fintype (ικ o)] [IsDomain O] [IsDiscreteValuationRing O] in

theorem support_ratDiv {P W : Ideal (MRing ικ O)} {s h : MRing ικ O} (hW : ratDiv P s h W ≠ 0) :
    W.IsPrime ∧ P ≤ W ∧ IsRelevant W := by
  have key : ∀ v, divCycle P v W ≠ 0 → W.IsPrime ∧ P ≤ W ∧ IsRelevant W := by
    intro v hv
    unfold divCycle at hv
    split_ifs at hv with h'
    · exact ⟨h'.1.1.1, le_sup_left.trans h'.1.1.2, h'.2⟩
    · exact absurd rfl hv
  by_cases h1 : divCycle P s W = 0
  · exact key h fun h2 => hW (by simp [ratDiv, h1, h2])
  · exact key s h1

end SegreFlagCutLiesOverProof

open SegreFlagCutLiesOverProof in

theorem SegreFlagCutLiesOver.proof (hChart : SegreFlagCutChartSection.Statement) :
    SegreFlagCutLiesOver.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hBB' w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ'
    Φ _ _ _ _ e t ht k hk
  have hchart : ∀ (s h : MRing (bundleIdx (bundleIdx ι M) M') O) (W : Ideal (MRing (bundleIdx (bundleIdx ι M) M') O)),
      ratDiv (pointIdeal O (flagClosurePt y w e φ φ' t (k + 1))) s h W ≠ 0 →
      ∃ c : ∀ j, ι j, segreVec y c ≠ 0 ∧ pointIdeal O (flagClosurePt y w e φ φ' t (k + 1)) ≤ W ∧
        ∀ m : K → ℕ, (∏ j, (X ⟨some (some j), c j⟩ : MRing (bundleIdx (bundleIdx ι M) M') O) ^ m j) ∉ W := by
    intro s h W hW
    obtain ⟨hWp, hPW, hWr⟩ := support_ratDiv hW
    choose c hc using fun j : K => hWr (some (some j))
    refine ⟨c, ?_, hPW, ?_⟩
    · unfold segreVec
      rw [Finset.prod_ne_zero_iff]
      intro j _ hj
      apply hc j (hPW ?_)
      refine GenericProjClosureDivisor.mem_of_homog (isWeightedHomogeneous_X O _ _) ?_
      rw [aeval_X]
      simp [flagClosurePt, pairProjCoord, projCoord, hj]
    · intro m hm
      obtain ⟨j, -, hj⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hWp)).mp hm
      exact hc j (hWp.mem_of_pow_mem _ hj)
  have hdeg : ∀ {cs ch dl dm : Option (Option K) → ℕ} {D : Option (Option K) → ℤ},
      (fun o => (cs o : ℤ) - ch o) = D → (fun o => (dl o : ℤ) - dm o) = D → cs + dm = dl + ch := by
    intro cs ch dl dm D h1 h2
    funext o
    have e1 := congrFun h1 o
    have e2 := congrFun h2 o
    simp only [Pi.add_apply] at e1 e2 ⊢
    omega
  refine ⟨fun cs ch s h hs hh hsh hsP hhP hsv W _ hW => ?_, fun cs ch s h hs hh hsh hsP hhP hsv W _ hW => ?_⟩
  · obtain ⟨c, hc, hPW, hmono⟩ := hchart s h W hW
    obtain ⟨⟨dl, dm, l, μ, m, hμ, hl, hμh, hdl, hlv, hsat⟩, -⟩ :=
      hChart O ϖ hϖ Ω K ι y d hV N E B B' hBB' w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht k hk c hc
    exact le_comap_of_chart _ _ _ _ _ hs hh hl hμh (hdeg hsh hdl) hsP hhP hsv hlv hsat (hμ ▸ hmono m)
      (fun n => by rw [← Finset.prod_pow]; exact hmono fun _ => n) hPW hW
  · obtain ⟨c, hc, hPW, hmono⟩ := hchart s h W hW
    obtain ⟨-, ⟨dl, dm, l, μ, m, hμ, hl, hμh, hdl, hlv, hsat⟩⟩ :=
      hChart O ϖ hϖ Ω K ι y d hV N E B B' hBB' w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht k hk c hc
    exact le_comap_of_chart _ _ _ _ _ hs hh hl hμh (hdeg hsh hdl) hsP hhP hsv hlv hsat (hμ ▸ hmono m)
      (fun n => by rw [← Finset.prod_pow]; exact hmono fun _ => n) hPW hW

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

