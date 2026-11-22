import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0017
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0155
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1098
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0163
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.SharpRestriction.Divisibility.KudlaSiegelWeil
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0172
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsNormCoprimeOfSup
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0149
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0132
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0127
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0152
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0166
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0169
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FourthPowerTheta
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0170
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightRegularOfExt
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0012
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0171
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ExistsIntegralMulOrderElement

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharacterisationPlacesPartsOfWeak
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoreThree

open Formalism.IndefR.Bridge in
theorem conj_ne_of_two {D : D7} (P : HeightOneSpectrum (𝓞 D.host.E)) (h2 : ((2 : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) :
    Formalism.DivisionValues.conjPl P ≠ P := by
  intro hP
  have hP' : P.asIdeal.map (Formalism.DivisionValues.cO D.host.E) = P.asIdeal := congrArg HeightOneSpectrum.asIdeal hP
  have hfix : ∀ x : 𝓞 D.host.E, Formalism.DivisionValues.cO D.host.E x ∈ P.asIdeal ↔ x ∈ P.asIdeal := fun x => by
    conv_lhs => rw [← hP']
    exact Ideal.apply_mem_of_equiv_iff
  refine Formalism.MainNotions.KudlaSiegelWeil.InertConditionsOfHost.not_fixed_ram D P 2 (Or.inl rfl) h2 (Ideal.ext fun x => ?_)
  rw [Ideal.mem_comap, ← hfix x]
  refine Eq.to_iff (congrArg (· ∈ P.asIdeal) (RingOfIntegers.ext ?_))
  exact (Formalism.BasicNotions.Examples₂.star_eq_conj D.host _).symm

theorem exists_two (D : D7) : ∃ P : HeightOneSpectrum (𝓞 D.host.E), ((2 : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
  haveI : (Ideal.span {(2 : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp Nat.prime_two).irreducible
  obtain ⟨Q, hQ, hc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 D.host.E) (Ideal.span {(2 : ℤ)}) (by
    intro x hx
    rw [RingHom.mem_ker] at hx
    have : x = 0 := by
      have := congrArg (fun y : 𝓞 D.host.E => ((y : D.host.E))) hx
      simpa using this
    rw [this]; exact zero_mem _)
  have h2 : ((2 : ℕ) : 𝓞 D.host.E) ∈ Q := by
    have : (2 : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 D.host.E)) := hc ▸ Ideal.mem_span_singleton_self _
    simpa using this
  refine ⟨⟨Q, hQ.isPrime, fun hb => ?_⟩, h2⟩
  rw [hb, Ideal.mem_bot] at h2
  have := congrArg (fun y : 𝓞 D.host.E => ((y : D.host.E))) h2
  norm_num at this

end GlobalTheory.CoreThree

namespace GlobalTheory.CoreThree

theorem heckeCharacterisation_places_parts_of_weak : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → (R.toRealDat.ExAt → Core R.toRealDat F.lv2) ∧ IsSF R.toRealDat R.SF ∧ (∀ t, ∀ Q ∈ A3.okI t, Good R.toRealDat t (R.plI Q) ∧ conjPl (R.plI Q) = R.plI Q) ∧ (∀ P, Good R.toRealDat A3.A.μ0 P → (conjPl P = P → ∃ Q ∈ A3.okI A3.A.μ0, R.plI Q = P) ∧ (conjPl P ≠ P → ∃ P0 ∈ A3.A.ok A3.A.μ0, R.pl P0 = P)) ∧ (∀ c, R.EEc c = EEc R.toRealDat R.SF c) ∧ (∀ i c, R.Wc' i c = Wcc R.toRealDat R.SF i c) ∧ (A3.A.ok A3.A.μ0).Nonempty := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F h
  have hL : R.toLevCh.Is A3.A.μ0 := h.base.lev
  obtain ⟨hQ0, -, -, -⟩ := GlobalTheory.GoodPrimes.good_primes R.toRealDat F.lv2 hL
  obtain ⟨_, _, _, ht⟩ := h.base.fam.tie
  have hSb : (R.Sb : Set (Pl D.host.E)) = R.Pg := by rw [h.allPl]
  have hon : ∀ P, Good R.toRealDat A3.A.μ0 P → (Formalism.DivisionValues.conjPl P = P → ∃ Q ∈ A3.okI A3.A.μ0, R.plI Q = P) ∧
      (Formalism.DivisionValues.conjPl P ≠ P → ∃ P0 ∈ A3.A.ok A3.A.μ0, R.pl P0 = P) := by
    intro P hP
    have hnS : P ∉ (R.Sb : Set (Pl D.host.E)) := by
      rw [hSb]; intro hm; exact (hP P (Or.inl hm)).1 rfl
    refine ⟨fun hf => ?_, fun hf => ?_⟩
    · have hio : Formalism.IndefR.Bridge.InertOff P (R.Sb : Set (Pl D.host.E)) := by
        refine ⟨?_, hnS⟩
        rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq, hf]
      obtain ⟨Q, hQ⟩ := h.inert.onto P hio
      refine ⟨Q, (h.inert.tie.okI A3.A.μ0 Q).2 ?_, hQ⟩
      rw [hQ0, Finset.coe_empty, Set.union_empty, hQ]
      exact hio
    · have hso : Formalism.IndefR.Bridge.SplitOff P (R.Sb : Set (Pl D.host.E)) := by
        refine ⟨?_, hnS, fun Q hQ he => ?_⟩
        · rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq]
          exact fun he => hf (HeightOneSpectrum.ext he)
        · rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq] at he
          have hQP : Q = Formalism.DivisionValues.conjPl P := HeightOneSpectrum.ext he
          rw [hSb] at hQ
          apply (hP Q (Or.inl hQ)).2
          have := GlobalTheory.SplitHeckeAdj.isConjPl_conj (Formalism.DivisionValues.conjPl P)
          rw [Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl] at this
          rw [hQP]; exact this
      obtain ⟨P0, hP0⟩ := h.base.fam.pl_onto P hso
      refine ⟨P0, (ht.ok A3.A.μ0 P0).2 ?_, hP0⟩
      rw [hQ0, Finset.coe_empty, Set.union_empty, hP0]
      exact hso
  refine ⟨fun e => (GlobalTheory.CoreOfWeak.core_of_weak R F h e).1, ?_, ?_, hon, fun c => rfl, fun i c => rfl, ?_⟩
  · intro v
    rw [h.inert.SF v, h.allPl]
  · intro t Q hQ
    obtain ⟨hfix, hoff⟩ := (h.inert.tie.okI t Q).1 hQ
    rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq] at hfix
    have hf : Formalism.DivisionValues.conjPl (R.plI Q) = R.plI Q := HeightOneSpectrum.ext hfix
    refine ⟨fun PP hPP => ⟨fun he => hoff ?_, fun hc => hoff ?_⟩, hf⟩
    · rcases hPP with hm | hm
      · exact Or.inl (by rw [hSb, ← he]; exact hm)
      · exact Or.inr (by rw [← he]; exact hm)
    · have e1 := GlobalTheory.SplitHeckeAdj.eq_conj_of_isConjPl hc
      have e2 : PP = R.plI Q := by
        rw [← Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl PP, ← e1, hf]
      rcases hPP with hm | hm
      · exact Or.inl (by rw [hSb, ← e2]; exact hm)
      · exact Or.inr (by rw [← e2]; exact hm)
  · obtain ⟨P, h2⟩ := exists_two D
    have hg : Good R.toRealDat A3.A.μ0 P := by
      intro PP hPP
      rw [hQ0] at hPP
      have hm : PP ∈ R.Pg := hPP.resolve_right (by simp)
      obtain ⟨k, hk⟩ := (hL.Pg PP).1 hm
      have hgk := GlobalTheory.LevelPlaces.mem_of_div _ k PP hk
      have hn : ((2 : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal :=
        GlobalTheory.LevelPlaces.not_mem_of_prime PP.isPrime.ne_top Nat.prime_two (D.host.g_prime k) (Formalism.L2.Pj.g_ne_two D k) hgk
      refine ⟨fun he => hn (he ▸ h2), fun hc => ?_⟩
      have hgP := GlobalTheory.LevelPlaces.natCast_mem_of_isConjPl hc hgk
      exact GlobalTheory.LevelPlaces.not_mem_of_prime P.isPrime.ne_top Nat.prime_two (D.host.g_prime k)
        (Formalism.L2.Pj.g_ne_two D k) hgP h2
    obtain ⟨P0, hP0, -⟩ := (hon P hg).2 (conj_ne_of_two P h2)
    exact ⟨P0, hP0⟩

end GlobalTheory.CoreThree
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HyperspecialFixesAllChainVacuaAtInertPrime
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.VacFixInert

open GlobalTheory.IdemSupport

variable {D : D7}

theorem parity_step {r t j : ℕ} (hr : Odd r) (ht : Odd t) :
    r + j * t ≠ r + (j + 1) * t ∧ (Even (r + j * t) ∨ Even (r + (j + 1) * t)) := by
  refine ⟨by rw [add_mul, one_mul]; have := ht.pos; omega, ?_⟩
  have hr' : ¬ Even r := Nat.not_even_iff_odd.2 hr
  have ht' : ¬ Even t := Nat.not_even_iff_odd.2 ht
  rcases Nat.even_or_odd j with hj | hj
  · right; simp [Nat.even_add, Nat.even_mul, Nat.even_add_one, hr', ht', hj]
  · left; simp [Nat.even_add, Nat.even_mul, hr', ht', Nat.not_even_iff_odd.2 hj]

theorem r_odd : Odd D.R.r := by
  obtain ⟨a, ha⟩ := D.R.k_even
  obtain ⟨b, hb⟩ := D.R.m_even
  have h2 := D.R.two_le_m
  exact ⟨a + b - 1, by simp only [Ranks.r]; omega⟩

theorem rank_Yc' {j : ℕ} (hj : j ≤ D.R.m) : (Yc D j).rank = D.R.r + j * D.R.t := by
  rw [D.sp.Y_rank _ (min_le_right _ _), min_eq_left hj]; rfl

theorem unrPl_mul_inv' {P : Pl D.host.E} {χ η : (AE D)ˣ →* Circle} (h : UnrPl P χ) (h' : UnrPl P η) :
    UnrPl P (χ * η⁻¹) := fun e f he x h1 h2 h3 => by
  show χ x * (η x)⁻¹ = 1
  rw [h e f he x h1 h2 h3, h' e f he x h1 h2 h3, inv_one, mul_one]

theorem unrPl_step' {P : Pl D.host.E} {μ : ℕ → (AE D)ˣ →* Circle} {η : (AE D)ˣ →* Circle} {j : ℕ} (h : UnrPl P (μ j))
    (h' : UnrPl P η) : UnrPl P (Lift.chrStep μ η j).1 ∧ UnrPl P (Lift.chrStep μ η j).2 := by
  unfold Lift.chrStep
  split_ifs
  · exact ⟨unrPl_mul_inv' h h', h⟩
  · exact ⟨h, unrPl_mul_inv' h h'⟩

theorem inert_data {P : Pl D.host.E} (hP : Formalism.DivisionValues.conjPl P = P) :
    ∃ ε, IsPlaceIdem D (P.under (𝓞 D.host.F)) ε ∧
      (¬ ∃ e : AE D, IsSplitIdem D e ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε) ∧ P = cP P ∧
      ∀ e f, IsPrimeIdem P e f → e = algebraMap (AF D.host.F) (AE D) ε ∧ f = algebraMap (AF D.host.F) (AE D) ε := by
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  have hc : P = cP P := by
    refine (isConjPl_iff P P).1 fun c hc => ⟨cO D c, ?_, rfl⟩
    have h1 : cO D c ∈ (Formalism.DivisionValues.conjPl P).asIdeal := Ideal.mem_map_of_mem _ hc
    rwa [hP] at h1
  obtain ⟨ε, hε⟩ := exists_placeIdem (D := D) (P.under (𝓞 D.host.F))
  obtain ⟨h0, h1, h2⟩ := place_comp hΦ hε
  have hd : IsDelta Φ P (algebraMap (AF D.host.F) (AE D) ε) :=
    ⟨h0, h1 P rfl, fun Q hQ => h2 Q fun h => (eq_or_eq_cP h).elim hQ fun h => hQ (h.trans hc.symm)⟩
  refine ⟨ε, hε, ?_, hc, fun e f h => ?_⟩
  · rintro ⟨e, ⟨e1, e2, -⟩, e3⟩
    have key : ∀ a : AE D, a * a = a → algebraMap (AF D.host.F) (AE D) ε * a = a → Φ a P ≠ 0 → IsDelta Φ P a :=
      fun a a1 a2 a3 => ⟨by rw [← a2, RingHom.map_mul, h0, zero_mul],
        mul_left_cancel₀ a3 (by rw [← ev_mul, a1, mul_one]),
        fun Q hQ => by rw [← a2, ev_mul, hd.2.2 Q hQ, zero_mul]⟩
    have e1' : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, e1]
    have hz : Φ e P * Φ (cA D e) P = 0 := by rw [← ev_mul, e2, ev_zero]
    have hs : Φ e P + Φ (cA D e) P = 1 := by rw [← ev_add, e3, hd.2.1]
    by_cases h : Φ e P = 0
    · have a := key (cA D e) e1' (by rw [← e3]; linear_combination e1' + e2)
        (by rw [h, zero_add] at hs; rw [hs]; exact one_ne_zero)
      have b := delta_conj hΦ a
      rw [cA_cA, ← hc] at b
      exact zero_ne_one (h.symm.trans b.2.1)
    · have a := key e e1 (by rw [← e3]; linear_combination e1 + e2) h
      have b := delta_conj hΦ a
      rw [← hc] at b
      rw [a.2.1, b.2.1, one_mul] at hz
      exact one_ne_zero hz
  · obtain ⟨k1, ε', k2, k3⟩ := of_isPrimeIdem hΦ h
    exact ⟨delta_unique hΦ k1 hd, by rw [k3, placeIdem_unique k2 hε]⟩

theorem split_mul_eq_zero {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε)
    (hns : ¬ ∃ e : AE D, IsSplitIdem D e ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε) :
    ∀ e, IsSplitIdem D e → e * algebraMap (AF D.host.F) (AE D) ε = 0 := by
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  rintro e ⟨he1, he2, v', ε', hε', hs⟩
  by_cases hv : v' = v
  · subst hv
    rw [placeIdem_unique hε' hε] at hs
    exact (hns ⟨e, ⟨he1, he2, v', ε, hε, hs⟩, hs⟩).elim
  · have h1 : e = e * algebraMap (AF D.host.F) (AE D) ε' := by rw [← hs, mul_add, he1, he2, add_zero]
    rw [h1, mul_assoc, place_orth hΦ hε' hε hv, mul_zero]

theorem two_not_mem {P : Pl D.host.E} (hc : P = cP P) : (2 : 𝓞 D.host.F) ∉ (P.under (𝓞 D.host.F)).asIdeal := by
  intro h2
  have h : ((2 : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
    have := Ideal.mem_comap.1 h2
    rw [map_ofNat] at this
    rw [Nat.cast_ofNat]
    exact this
  refine Formalism.MainNotions.KudlaSiegelWeil.InertConditionsOfHost.not_fixed_ram D P 2 (Or.inl rfl) h (Ideal.ext fun x => ?_)
  rw [Ideal.mem_comap]
  have : Formalism.MainNotions.KudlaSiegelWeil.InertConditionsOfHost.sgO D x = cO D x := by
    apply RingOfIntegers.ext
    rw [cO_coe]
    show D.host.conj (x : D.host.E) = _
    exact (Formalism.BasicNotions.Examples₂.star_eq_conj D.host _).symm
  rw [this, ← mem_cP, ← hc]

theorem unrAtV_of {P : Pl D.host.E} {ε : AF D.host.F} {χ : (AE D)ˣ →* Circle} {e f : AE D} (he : IsPrimeIdem P e f)
    (hf : f = algebraMap (AF D.host.F) (AE D) ε) (h : UnrPl P χ) : Formalism.IndefR.WeilFull.UnrAtV ε χ := by
  intro x hx a b
  refine h e f he x ?_ a b
  rw [hf]
  linear_combination (-1 : AE D) * hx

theorem isHalf_of_mem' {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) {u : WO S T}
    (hu : u ∈ latO S T LS LT fun w => w = v) : IsHalf (algebraMap (AF D.host.F) (AE D) ε) u := by
  obtain ⟨β, rfl, h1, h0⟩ := hε
  intro i j
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hw
    have hβα : β * α = α := FiniteAdeleRing.ext _ fun w => by
      change evalV D.host.F w (β * α) = evalV D.host.F w α
      rw [map_mul]
      by_cases hw : w = v
      · subst hw; rw [h1, one_mul]
      · rw [hP w hw, mul_zero]
    change (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 : D.host.E)) * (_ ⊗ₜ _) = _ ⊗ₜ _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    congr 1
    exact Prod.ext (mul_zero _) hβα
  | zero => exact mul_zero _
  | add x x' _ _ h h' => rw [Matrix.add_apply, mul_add, h, h']
  | neg x _ h => rw [Matrix.neg_apply, mul_neg, h]

theorem vacFix_of_inert (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (P : Pl D.host.E)
    (hI : Formalism.IndefR.WeilFull.SphInertAtO ψ S T χS χT om) (hrk : S.rank ≠ T.rank) (hev : Even S.rank ∨ Even T.rank)
    (hP : Formalism.DivisionValues.conjPl P = P) (uS : UnrPl P χS) (uT : UnrPl P χT) : VacFix ψ om P := by
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  obtain ⟨ε, hε, hns, hc, hpi⟩ := inert_data hP
  obtain ⟨e0, f0, h0⟩ := exists_isPrimeIdem hΦ P
  have eS : GlobalTheory.PlaceModel.latFrame S = GlobalTheory.LevSplit.L0sub S := SetLike.coe_injective (GlobalTheory.PlaceModel.coe_latFrame S)
  have eT : GlobalTheory.PlaceModel.latFrame T = GlobalTheory.LevSplit.L0sub T := SetLike.coe_injective (GlobalTheory.PlaceModel.coe_latFrame T)
  have hsS : IsSelfDualC S (GlobalTheory.LevSplit.L0sub S) := eS ▸ GlobalTheory.PlaceModel.isSelfDualC_latFrame S
  have hsT : IsSelfDualC T (GlobalTheory.LevSplit.L0sub T) := eT ▸ GlobalTheory.PlaceModel.isSelfDualC_latFrame T
  obtain ⟨βS, hβS⟩ := GlobalTheory.latticeFrame.exists_frame D.host.F D.host.E _ _ hsS.1
  obtain ⟨βT, hβT⟩ := GlobalTheory.latticeFrame.exists_frame D.host.F D.host.E _ _ hsT.1
  rintro f hf k ⟨hk, a, a', ha, sk⟩ k' ⟨hk', b, b', hb, sk'⟩
  rw [(hpi a a' ha).2] at sk
  rw [(hpi b b' hb).2] at sk'
  have key : ∀ u ∈ latO S T (GlobalTheory.LevSplit.L0sub S : Set (Fin S.rank → D.host.E))
      (GlobalTheory.LevSplit.L0sub T : Set (Fin T.rank → D.host.E)) (fun w => w = P.under (𝓞 D.host.F)),
      heisO ψ S T u f = f := fun u hu =>
    hf.2 e0 f0 h0 u (GlobalTheory.PlaceModel.latO_le_top _ hu) (Or.inl (by rw [(hpi e0 f0 h0).1]; exact isHalf_of_mem' hε hu))
  refine hI hrk hev _ _ hsS hsT βS βT hβS hβT _ ε hε (two_not_mem hc) (split_mul_eq_zero hε hns)
    (unrAtV_of h0 (hpi e0 f0 h0).2 uS) (unrAtV_of h0 (hpi e0 f0 h0).2 uT) k k' sk sk' ?_ ?_ f hf.1
    ⟨fun u hu => key _ (AddSubgroup.nsmul_mem _ hu 2), fun e _ u hu _ => key u hu⟩
  · exact (GlobalTheory.LevSplit.mem_St_iff βS _ hβS _).2 ((GlobalTheory.LevSplit.ksph_iff S k).1 hk).2
  · exact (GlobalTheory.LevSplit.mem_St_iff βT _ hβT _).2 ((GlobalTheory.LevSplit.ksph_iff T k').1 hk').2

end GlobalTheory.VacFixInert

namespace GlobalTheory.VacFixInert

theorem fixAll_inert : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → ∀ t P, Good R.toRealDat t P → Formalism.DivisionValues.conjPl P = P →
    FixAll R.toRealDat t P := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hC t P hG hP
  have hU := GlobalTheory.T.splittingCharacters_unramified_offLevels R.toRealDat F.lv2 hC.base.lev t P hG
  have hη := hU.1
  have hμ := hU.2
  have hr : Odd D.R.r := r_odd
  have ht : Odd D.R.t := D.R.t_odd
  have hm2 := D.R.two_le_m
  refine ⟨fun k hk => ?_, ?_, fun i => ?_⟩
  · have hW := hC.fullY t k hk
    have u := unrPl_step' (hμ (k + 1) (by omega) hk.le) hη
    have hp := parity_step (j := k) hr ht
    refine vacFix_of_inert _ _ P hW.inert ?_ ?_ hP u.1 u.2
    · rw [rank_Yc' (by omega), rank_Yc' (by omega)]; exact hp.1
    · rw [rank_Yc' (by omega), rank_Yc' (by omega)]; exact hp.2
  · have hW := hC.fullX t
    have u := unrPl_step' (hμ D.R.m (by omega) le_rfl) hη
    have hp := parity_step (j := D.R.m - 1) hr ht
    have hm : D.R.m - 1 + 1 = D.R.m := by omega
    rw [hm] at hp
    have hX : D.sp.X'.rank = D.R.r + D.R.m * D.R.t := D.sp.X'_rank
    refine vacFix_of_inert _ _ P hW.inert ?_ ?_ hP u.1 u.2
    · rw [rank_Yc' (by omega), hX]; exact hp.1
    · rw [rank_Yc' (by omega), hX]; exact hp.2
  · have hW := hC.fullP i t
    have u1 : UnrPl P (R.toLevCh.mu t ((i : ℕ) + 1)) := hμ ((i : ℕ) + 1) (by omega) i.2
    have hV : (Vc D i).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
    have hWr : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
    refine vacFix_of_inert _ _ P hW.inert ?_ ?_ hP u1 (unrPl_mul_inv' u1 hη)
    · rw [hV, hWr]; have := ht.pos; omega
    · left; rw [hV]; exact hr.add_odd ht

end GlobalTheory.VacFixInert
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralWittUnitaryModUniformizer
section
open Matrix

namespace GlobalTheory.Hk3.IntWittBase

open Formalism.UG GlobalTheory.Hk3.IntWitt

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem witt_mod_base : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → ∀ (n' : ℕ) (JT : GL (Fin n') L),
    JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ (ι : Type) [Fintype ι] (z z' : ι → Fin n' → L), (∀ i r, z i r ∈ Formalism.UG.intL L) → (∀ i r, z' i r ∈ Formalism.UG.intL L) →
    GlobalTheory.Hk3.IntWitt.IndepMod ϖ z → GlobalTheory.Hk3.IntWitt.IndepMod ϖ z' →
    (∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 (Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z' i) (z' j) - Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z i) (z j))) →
    ∃ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
      ∀ i r, GlobalTheory.Hk3.IntWitt.DvdPow ϖ 1 ((((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ z i) r - z' i r) := by
  intro L _ _ _ ϖ σ q hU hq n' JT hJ hJh ι _ z z' hz hz' hi hi' hgr
  classical
  obtain ⟨g₀, hg₀i, hg₀u, hg₀z⟩ := GlobalTheory.T.hermitian_integral_vectors_pairing L ϖ σ q hU hq n' JT hJ hJh ι z z' hz hz' hi hi' hgr
  have hstep := GlobalTheory.T.unitaryGroup_newton_lift_step L ϖ σ q hU hq n' JT hJ hJh
  obtain ⟨hσσ, hσv, hσϖ, hϖv, -, -, -⟩ := hU
  set J : Matrix (Fin n') (Fin n') L := (JT : Matrix (Fin n') (Fin n') L) with hJdef
  have hJi : ∀ i j, J i j ∈ intL L := by
    obtain ⟨k0, hk0⟩ := hJ
    intro i j; rw [hJdef, ← hk0]; exact ((k0 : Matrix (Fin n') (Fin n') (intL L)) i j).2

  let P : ℕ → Matrix (Fin n') (Fin n') L → Prop := fun k g =>
    (∀ i j, g i j ∈ intL L) ∧ ∀ i j, DvdPow ϖ (k + 1) ((cT σ g * J * g - J) i j)
  have hex : ∀ (k : ℕ) (g : Matrix (Fin n') (Fin n') L), ∃ g' : Matrix (Fin n') (Fin n') L,
      P k g → P (k + 1) g' ∧ ∀ i j, DvdPow ϖ (k + 1) (g' i j - g i j) := by
    intro k g
    by_cases hP : P k g
    · obtain ⟨g', h1, h2, h3⟩ := hstep k g hP.1 hP.2
      exact ⟨g', fun _ => ⟨⟨h1, h3⟩, h2⟩⟩
    · exact ⟨g, fun h => absurd h hP⟩
  choose F hF using hex
  let f : ℕ → Matrix (Fin n') (Fin n') L := fun k => Nat.rec g₀ (fun k g => F k g) k
  have hf0 : f 0 = g₀ := rfl
  have hfs : ∀ k, f (k + 1) = F k (f k) := fun k => rfl
  have hfP : ∀ k, P k (f k) := by
    intro k
    induction k with
    | zero => exact ⟨hg₀i, hg₀u⟩
    | succ k ih => rw [hfs]; exact (hF k (f k) ih).1
  have hclose : ∀ k i j, DvdPow ϖ (k + 1) (f (k + 1) i j - f k i j) := by
    intro k i j; rw [hfs]; exact (hF k (f k) (hfP k)).2 i j

  have hlim := fun i j => GlobalTheory.T.exists_limit_dvdUniformizerPow_cauchy L ϖ hϖv (fun k => f k i j) (fun k => hclose k i j)
  choose b hb using hlim
  let h : Matrix (Fin n') (Fin n') L := Matrix.of b
  have hhk : ∀ k i j, DvdPow ϖ (k + 1) ((h - f k) i j) := fun k i j => hb i j k
  have hϖi : ϖ ∈ intL L := by
    show Valued.v ϖ ≤ 1
    rw [hϖv]; exact WithZero.exp_le_exp.2 (by norm_num : (-1 : ℤ) ≤ 0)
  have hhi : ∀ i j, h i j ∈ intL L := by
    intro i j
    have e : h i j = (h - f 0) i j + f 0 i j := by simp
    rw [e]
    exact add_mem (dvdPow_zero_iff.1 (dvdPow_mono hϖi (Nat.zero_le 1) (hhk 0 i j))) ((hfP 0).1 i j)
  have hunit : cT σ h * J * h = J := by
    ext i j
    have hz0 : (cT σ h * J * h - J) i j = 0 := by
      refine eq_zero_of_forall_dvdPow hϖv fun k => ?_
      have e : cT σ h * J * h - J = (cT σ (h - f k) * J * h + cT σ (f k) * J * (h - f k)) +
          (cT σ (f k) * J * f k - J) := by
        rw [cT_sub]; simp only [sub_mul, mul_sub, Matrix.mul_assoc]; abel
      rw [e, Matrix.add_apply, Matrix.add_apply]
      refine dvdPow_add (dvdPow_add ?_ ?_) ((hfP k).2 i j)
      · exact mc_mul_right (mc_mul_right (mc_cT hσv hσϖ (hhk k)) hJi) hhi i j
      · rw [Matrix.mul_assoc]
        exact mc_mul_left (int_cT hσv (hfP k).1) (mc_mul_left hJi (hhk k)) i j
    rw [Matrix.sub_apply] at hz0
    exact sub_eq_zero.1 hz0

  set Ji : Matrix (Fin n') (Fin n') L := ((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) with hJidef
  have hJiJ : Ji * J = 1 := by rw [hJidef, hJdef, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hleft : (Ji * cT σ h * J) * h = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT σ h), hunit, hJiJ]
  have hright : h * (Ji * cT σ h * J) = 1 := mul_eq_one_comm.1 hleft
  let hG : GL (Fin n') L := ⟨h, Ji * cT σ h * J, hright, hleft⟩
  have hmem : hG ∈ UJ σ J := hunit
  refine ⟨⟨hG, hmem⟩, GlobalTheory.UnitarySwap.mem_GLint_of_unitary hσv hJ hmem hhi, fun i r => ?_⟩
  show DvdPow ϖ 1 ((h *ᵥ z i) r - z' i r)
  have e : (h *ᵥ z i) r - z' i r = ((h - g₀) *ᵥ z i) r + ((g₀ *ᵥ z i) r - z' i r) := by
    simp [Matrix.sub_mulVec]
  rw [e]
  refine dvdPow_add ?_ (hg₀z i r)
  simp only [Matrix.mulVec, dotProduct]
  refine dvdPow_sum _ _ fun s _ => ?_
  rw [mul_comm]
  exact dvdPow_mul_int (hhk 0 r s) (hz i s)

end GlobalTheory.Hk3.IntWittBase
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocJetsAll
section
namespace GlobalTheory.ThLoc

theorem locJets_all :
    Formalism.L2.Th1.GD.IntOpLoc ∧ Formalism.L2.Th1.GD.IntOpTwoLoc ∧
      (Formalism.L2.Th1.GD.EmbSep → Formalism.L2.Th1.GD.ShapeEigenLoc) :=
  ⟨LocJets.jetsOdd, LocJets.jetsTwo, LocJets.shape⟩

end GlobalTheory.ThLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalInvariantsMatchSemisimpleStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_invariants_match_semisimple : ∀ D : D7, Formalism.MainNotions.SumRepresentations.tie0 D → Formalism.MainNotions.SumRepresentations.adm2 D → Formalism.MainNotions.SumRepresentations.adm5 D → ∀ (i : D.nd.Loc) (a : ℕ), 1 ≤ a → ∀ (π : D.naut.CG a) (s : ℝ), D.naut.csd (D.naut.tw π D.naut.etaT) → D.naut.ralg (D.naut.tw π D.naut.etaT) → (∃ m : ℤ, s = (m : ℝ) + 1 / 2) → ∀ ρ : G D.host.E D.nd.Om →* GL (Fin a) (D.nd.O i), GlobalTheory.LocalInv.Cont D.nd i ρ → IsSSRep (mapRep (algebraMap (D.nd.O i) (Kf D.nd i)) ρ) → GlobalTheory.LocalInv.Matches D.nd D.naut i ρ π (s + (1 - (a : ℝ)) / 2) → ∀ w, GlobalTheory.LocalInv.wd D.nd D.naut i ρ w = D.naut.lpTw (D.naut.locG π w) (s + (1 - (a : ℝ)) / 2) ∧ (w ∈ placesOver D.host.E (D.nd.l i) → GlobalTheory.LocalInv.DeRham D.nd D.naut i ρ w) := by
  first | exact @GlobalTheory.TwistLG.localGlobal_twist | exact GlobalTheory.TwistLG.localGlobal_twist | (intros; apply GlobalTheory.TwistLG.localGlobal_twist <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemISupTypePartsOfGoodBaseFormsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_iSup_type_parts_of_good_base_forms : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), (R.toCx3 F).PartsW false → ∀ j (w : (R.HW j (sg0 D A3.A)).H), w ∈ R.toRealDat.WS F.lv2 false j (sg0 D A3.A) → w ∈ ⨆ p, R.Wp3 j p := by
  first | exact @GlobalTheory.TwParts.mem_iSup_Wp3_of_mem_WS | exact GlobalTheory.TwParts.mem_iSup_Wp3_of_mem_WS | (intros; apply GlobalTheory.TwParts.mem_iSup_Wp3_of_mem_WS <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemberBadPrimesNoConjugatePairStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms Formalism.L2.Col Formalism.L2.DIV Formalism.HermitianLatticesTheory NumberField IsDedekindDomain Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.memberBadPrimes_no_conjugatePair : ∀ {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S), X.Ok → Pr.Ok → IsSel X sel → ∀ u : Pr.Word, Pr.T u ∈ S → (∀ i, Pr.g i ∈ S) → ∀ P ∈ Sall sel mu u, conjPrime₂ P ∉ Sall sel mu u := by
  first | exact @GlobalTheory.BadNoConj.sall_noConj_ok | exact GlobalTheory.BadNoConj.sall_noConj_ok | (intros; apply GlobalTheory.BadNoConj.sall_noConj_ok <;> assumption)
end

