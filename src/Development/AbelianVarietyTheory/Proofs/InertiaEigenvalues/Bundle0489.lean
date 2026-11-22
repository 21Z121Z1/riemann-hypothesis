import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationBoundOfPrimePowDvdMuPowAcris
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0455
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JumpDictCrysAtOfWeights
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0018
import Formalism.SharpRestriction.Bundle0002
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0031
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0420
import Formalism.SharpRestriction.LevelLetterCocycles.ProdOneSubPrimitiveRoots
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0406
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0458
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0403
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscGaugeCompletionZeroOneProperties
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0457
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0456
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0014
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisLpowDvdBoundTeichmullerMonoid
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.AcrisMonBound

variable {l : ℕ} [hl : Fact l.Prime]

theorem exists_pow_bound {ϖ : OCb l} (hϖ : ϖ.untilt = (l : Per.OC l)) {c : OCb l} (hc : c ≠ 0) :
    ∃ K : ℕ, ∀ k : ℕ, ϖ ^ k ∣ c → k < K := by
  set a := ‖((c.untilt : Per.OC l) : ℂ_[l])‖
  set b := ‖((l : ℕ) : ℂ_[l])‖
  have ha : 0 < a := by
    refine norm_pos_iff.2 fun h => hc (GlobalTheory.TiltAbs.eq_zero_of_untilt c ?_)
    exact Subtype.ext (by simpa using h)
  have hb1 : b < 1 := GlobalTheory.RingBasics.norm_p_lt
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one ha hb1
  refine ⟨K, fun k hk => ?_⟩
  by_contra hkK
  obtain ⟨d, hd⟩ := map_dvd (PreTilt.untilt (O := Per.OC l) (p := l)) hk
  rw [map_pow, hϖ] at hd
  have h1 := congrArg (fun z : Per.OC l => ‖(z : ℂ_[l])‖) hd
  push_cast at h1
  rw [norm_mul, norm_pow] at h1
  have h2 : a ≤ b ^ k := by
    change ‖((c.untilt : Per.OC l) : ℂ_[l])‖ ≤ _
    rw [h1]
    exact mul_le_of_le_one_right (pow_nonneg (norm_nonneg _) _) (GlobalTheory.TiltAbs.norm_le_one d)
  have h3 : b ^ k ≤ b ^ K := pow_le_pow_of_le_one (norm_nonneg _) hb1.le (not_lt.1 hkK)
  linarith

end GlobalTheory.AcrisMonBound

namespace GlobalTheory.AcrisMonBound

theorem main : ∀ (l : ℕ) [Fact l.Prime] (y : Ainf l), WittVector.constantCoeff y ≠ 0 → ∃ C : ℕ, ∀ (z : ℤ_[l]) (N : ℕ), z ≠ 0 → (l : Per.Acris l) ^ N ∣ ainfToAcris l y * algebraMap ℤ_[l] (Per.Acris l) z → N ≤ z.valuation + C := by
  intro l hl y hy
  have hl2 : 2 ≤ l := hl.out.two_le
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.MemLoc.FundOnto.untilt_surjective l (l : Per.OC l)
  obtain ⟨K, hK⟩ := exists_pow_bound hϖ hy
  refine ⟨K, fun z N hz h => ?_⟩
  set u := PadicInt.unitCoeff hz
  set v := z.valuation
  rcases le_or_gt N v with hNv | hNv
  · omega
  obtain ⟨n', rfl⟩ := Nat.exists_eq_add_of_le hNv.le
  set y' := y * algebraMap ℤ_[l] (Ainf l) (u : ℤ_[l])
  have hza : algebraMap ℤ_[l] (Per.Acris l) z =
      (l : Per.Acris l) ^ v * algebraMap ℤ_[l] (Per.Acris l) (u : ℤ_[l]) := by
    conv_lhs => rw [PadicInt.unitCoeff_spec hz]
    rw [map_mul, map_pow, map_natCast, mul_comm]
  have hy' : ainfToAcris l y' = ainfToAcris l y * algebraMap ℤ_[l] (Per.Acris l) (u : ℤ_[l]) := by
    simp only [y', map_mul]
    congr 1
  have h2 : (l : Per.Acris l) ^ n' ∣ ainfToAcris l y' := by
    obtain ⟨w, hw⟩ := h
    refine ⟨w, ?_⟩
    have h3 : ((l ^ v : ℕ) : Per.Acris l) * (ainfToAcris l y' - (l : Per.Acris l) ^ n' * w) = 0 := by
      rw [hza] at hw
      rw [hy']
      push_cast
      rw [mul_sub]
      linear_combination hw
    exact sub_eq_zero.1 (acris_nat_cancel (pow_ne_zero _ hl.out.ne_zero) h3)
  have h4 := GlobalTheory.AcrisMuBound.pow_dvd_cc hl2 hϖ h2
  have hu : IsUnit (WittVector.constantCoeff (algebraMap ℤ_[l] (Ainf l) (u : ℤ_[l]))) :=
    (u.isUnit.map _).map _
  rw [show y' = y * algebraMap ℤ_[l] (Ainf l) (u : ℤ_[l]) from rfl, map_mul, hu.dvd_mul_right] at h4
  have h5 := hK _ h4
  have h6 : n' ≤ (l - 1) * n' := Nat.le_mul_of_pos_left n' (by omega)
  omega

end GlobalTheory.AcrisMonBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisValuationAtRadiusConcaveContSlopeStatement
section
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.acrisValuationAtRadius_concave_cont_slope : ∀ (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Acris l), x ≠ 0 → ConcaveOn ℝ (Set.Ioc 0 1) (fun r => vr l r x) ∧ ContinuousOn (fun r => vr l r x) (Set.Ioc 0 1) ∧ ∀ r ∈ Set.Ioo (0 : ℝ) 1, ∃ (k : ℤ) (δ : ℝ), 0 < δ ∧ r + δ ≤ 1 ∧ ∀ t ∈ Set.Icc r (r + δ), vr l t x = vr l r x + k * (t - r) := by
  first | exact @GlobalTheory.PMon.Gauss.vr_concave_cont_rightSlope | exact GlobalTheory.PMon.Gauss.vr_concave_cont_rightSlope | (intros; apply GlobalTheory.PMon.Gauss.vr_concave_cont_rightSlope <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleDictionaryOfParamsStatement
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissible_dictionary_of_params : GlobalTheory.TwSys.Cheb → ∀ D : D7, SumRepresentations.adm2 D → WeightParam D → BlockCharParam D → AdmissibleParameterJ.AdmDict D := by
  first | exact @GlobalTheory.BridgeAdmDict.main | exact GlobalTheory.BridgeAdmDict.main | (intros; apply GlobalTheory.BridgeAdmDict.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleTableOfLocalBounds
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

noncomputable section

namespace GlobalTheory.NLink.Adm4Tab

theorem placesOver_nonempty (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p.Prime) :
    (placesOver E p).Nonempty :=
  by apply _root_.UpperTheory.Reformulated.B.Qk8.exists_place <;> assumption

theorem sumOver_const (D : D7) (l : ℕ) (hl : l ≠ 0) (k : ℝ) :
    TwistedPlaces.sumOver D l (fun _ => k) = ((placesOver D.host.E l).ncard : ℝ) * k := by
  have hf := FamilyRepresentationConstants.placesOver_finite D.host.E l hl
  rw [TwistedPlaces.sumOver, finsum_mem_eq_finite_toFinset_sum _ hf, Finset.sum_const, Set.ncard_eq_toFinset_card _ hf,
    nsmul_eq_mul]

theorem sumOver_mono (D : D7) (l : ℕ) (hl : l ≠ 0) {f g : HeightOneSpectrum (𝓞 D.host.E) → ℝ}
    (h : ∀ lam, f lam ≤ g lam) : TwistedPlaces.sumOver D l f ≤ TwistedPlaces.sumOver D l g := by
  have hf := FamilyRepresentationConstants.placesOver_finite D.host.E l hl
  rw [TwistedPlaces.sumOver, TwistedPlaces.sumOver, finsum_mem_eq_finite_toFinset_sum _ hf, finsum_mem_eq_finite_toFinset_sum _ hf]
  exact Finset.sum_le_sum fun lam _ => h lam

theorem le_supZ {D : D7} (i : D.nd.Loc) (f : D.nd.X i → ℝ) {π : D.nd.X i} (hπ : π ∈ D.nd.Zgood i) :
    f π ≤ KillingConditions.supZ i f := by
  unfold KillingConditions.supZ
  rw [dif_pos ⟨π, hπ⟩]
  exact Finset.le_sup' f hπ

end GlobalTheory.NLink.Adm4Tab

open GlobalTheory.NLink.Adm4Tab in

theorem GlobalTheory.NLink.admissible_table_of_conclusion : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ) (tf : TwistedPlaces.Tab L),
    Concl L P X C → (∀ i, TwistedPlaces.TwLoc D i → (D.nd.l i ∈ D.host.small ∨ D.nd.l i = 3) → ∀ π ∈ D.nd.Zgood i,
      Bd X.ρ i π (TwistedPlaces.sumOver D (D.nd.l i) (tf.len i) + tf.BB i)) → TwistedPlaces.ArchimedeanSignatureMatching L (tab L X tf C) := by
  intro D L P X C tf hC h23 i hi hg π hπ
  have key : ∀ b, Bd X.ρ i π b → b ≤ TwistedPlaces.sumOver D (D.nd.l i) ((tab L X tf C).len i) + (tab L X tf C).BB i →
      (D.nd.vcc i π : ℝ) ≤ (tab L X tf C).s i π + TwistedPlaces.sumOver D (D.nd.l i) ((tab L X tf C).len i) +
        TwistedPlaces.VVr D (D.nd.l i) + TwistedPlaces.vhE D (D.nd.l i) + (tab L X tf C).BB i + TwistedPlaces.epsL (D.nd.l i) := by
    intro b hb hle
    unfold Bd at hb
    have hs : (tab L X tf C).s i π = (Br.sPi D.loc D.nbr i (X.ρ i) π : ℝ) := rfl
    rw [hs]
    linarith
  have hl0 : D.nd.l i ≠ 0 := (D.nd.lPrime i).out.ne_zero
  have hq3 : D.host.q ≠ 3 := D.host.q_ne_three
  have hd3 : D.host.d ≠ 3 := by have := D.host.hyp.2.2.2.1; omega
  have hzero : TwistedPlaces.sumOver D (D.nd.l i) (fun _ => (0 : ℝ)) = 0 := by
    rw [sumOver_const D _ hl0, mul_zero]
  by_cases h2 : D.nd.l i ∈ D.host.small
  · apply key _ (h23 i hi (Or.inl h2) π hπ)
    have hlen : (tab L X tf C).len i = fun _ => 0 := by
      funext lam
      simp only [tab, if_pos h2]
    have hBB : (tab L X tf C).BB i = TwistedPlaces.sumOver D (D.nd.l i) (tf.len i) + tf.BB i := by
      simp only [tab, if_pos h2]
    rw [hlen, hzero, hBB, zero_add]
  by_cases h3 : D.nd.l i = 3
  · apply key _ (h23 i hi (Or.inr h3) π hπ)
    have hBB : (tab L X tf C).BB i = 0 := by
      have hq : ¬ (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) := by
        rw [h3]; rintro (h | h) <;> [exact hq3 h.symm; exact hd3 h.symm]
      have hR : ¬ KillingConditions.RangeAD L X.exc (D.nd.l i) := fun h => h.1 (Or.inr h3)
      simp only [tab, if_neg h2, if_neg hq, if_neg hR]
    have hlen : (tab L X tf C).len i =
        fun _ => (TwistedPlaces.sumOver D 3 (tf.len i) + tf.BB i) / ((placesOver D.host.E 3).ncard : ℝ) := by
      funext lam
      simp only [tab, if_neg h2, if_pos h3]
    rw [hBB, hlen, h3, sumOver_const D 3 (by norm_num)]
    have hf3 := FamilyRepresentationConstants.placesOver_finite D.host.E 3 (by norm_num)
    have hpos : 0 < (placesOver D.host.E 3).ncard :=
      (Set.ncard_pos hf3).2 (placesOver_nonempty D.host.E 3 Nat.prime_three)
    have hpos' : ((placesOver D.host.E 3).ncard : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
    rw [mul_div_cancel₀ _ hpos', add_zero]
  by_cases hqd : D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d
  · apply key _ (hC.ram i hi hqd π hπ)
    have hR : ¬ KillingConditions.RangeAD L X.exc (D.nd.l i) := fun h => h.2.1 hqd
    have hlen : (tab L X tf C).len i = fun _ => 0 := by
      funext lam
      simp only [tab, if_neg h2, if_neg h3, if_neg hR]
    have hBB : (tab L X tf C).BB i = TwistedPlaces.midG L C (D.nd.l i) := by
      simp only [tab, if_neg h2, if_pos hqd]
    rw [hlen, hzero, hBB, zero_add]
  by_cases hR : KillingConditions.RangeAD L X.exc (D.nd.l i)
  · have hm := hC.mid i hi hg hR π hπ
    have hb : Bd X.ρ i π (TwistedPlaces.sumOver D (D.nd.l i) (X.len0 i π) + X.errorBoundHub i π) := by
      unfold Bd
      linarith
    apply key _ hb
    have hlen : (tab L X tf C).len i = KillingConditions.lenR X.len0 i := by
      funext lam
      simp only [tab, if_neg h2, if_neg h3, if_pos hR]
    have hBB : (tab L X tf C).BB i = KillingConditions.supZ i (X.errorBoundHub i) := by
      simp only [tab, if_neg h2, if_neg hqd, if_pos hR]
    rw [hlen, hBB]
    have h1 : TwistedPlaces.sumOver D (D.nd.l i) (X.len0 i π) ≤ TwistedPlaces.sumOver D (D.nd.l i) (KillingConditions.lenR X.len0 i) :=
      sumOver_mono D _ hl0 fun lam => le_supZ i (fun π => X.len0 i π lam) hπ
    have h2' : X.errorBoundHub i π ≤ KillingConditions.supZ i (X.errorBoundHub i) := le_supZ i (X.errorBoundHub i) hπ
    linarith
  · have hlt : TwistedPlaces.lStar L < (D.nd.l i : ℝ) ∧ D.nd.l i ∉ X.exc := by
      by_contra hc
      exact hR ⟨fun h => h.elim h2 h3, hqd, hc⟩
    apply key _ (hC.large i hi hlt.1 hg hlt.2 π hπ)
    have hlen : (tab L X tf C).len i = fun _ => 0 := by
      funext lam
      simp only [tab, if_neg h2, if_neg h3, if_neg hR]
    have hBB : (tab L X tf C).BB i = 0 := by
      simp only [tab, if_neg h2, if_neg hqd, if_neg hR]
    rw [hlen, hzero, hBB, add_zero]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AevalRootOfUnityMulKummerRootMinpolyStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.aeval_rootOfUnity_mul_kummer_root_minpoly : ∀ (l : ℕ) [Fact l.Prime] (M : ℕ), 0 < M → ∀ (ρ ξ : Om l), ρ ^ M = -(l : Om l) → ξ ^ M = 1 → Polynomial.aeval (ξ * ρ) (minpoly ↥(MaximalUnramifiedExtension l) ρ) = 0 := by
  first | exact @GlobalTheory.MinpolyKummerUr.aeval_mul_root | exact GlobalTheory.MinpolyKummerUr.aeval_mul_root | (intros; apply GlobalTheory.MinpolyKummerUr.aeval_mul_root <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfDvdOfClosedDiscDvdEisensteinPow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.DiscDvd

variable {l : ℕ} [Fact l.Prime] {K : FinExt l}

theorem ρ₀_pos_lt (bk : BK K) : 0 < bk.ρ₀ ∧ bk.ρ₀ < 1 := by
  have hl : (1 : ℝ≥0) < (l : ℝ≥0) := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have he : (0 : ℝ) < bk.Ep.natDegree := by exact_mod_cast bk.deg_pos
  refine ⟨NNReal.rpow_pos (by exact_mod_cast (Fact.out : l.Prime).pos), ?_⟩
  exact NNReal.rpow_lt_one_of_one_lt_of_neg hl (by rw [neg_lt_zero]; positivity)

theorem complete_max (bk : BK K) :
    IsAdicComplete (IsLocalRing.maximalIdeal (Wq l bk.a)) (Wq l bk.a) := by
  haveI : IsAdicComplete (Ideal.span {(l : Wq l bk.a)}) (Wq l bk.a) := WittVector.isAdicCompleteIdealSpanP
  have hsurj : Function.Surjective (WittVector.constantCoeff (p := l) (R := Fq l bk.a)) :=
    fun x => ⟨WittVector.teichmuller l x, by simp⟩
  have hm : IsLocalRing.maximalIdeal (Wq l bk.a) = Ideal.span {(l : Wq l bk.a)} := by
    rw [← WittVector.ker_constantCoeff]
    haveI := RingHom.ker_isMaximal_of_surjective _ hsurj
    exact (IsLocalRing.eq_maximalIdeal this).symm
  exact hm ▸ inferInstance

theorem dvd_E (bk : BK K) (s : bk.S) (h : toDisc l (X : bk.S) bk.ρ₀ bk.E ∣ toDisc l (X : bk.S) bk.ρ₀ s) :
    bk.E ∣ s := by
  haveI := complete_max bk
  have hg : PowerSeries.map (IsLocalRing.residue (Wq l bk.a)) bk.E ≠ 0 := by
    intro h0
    have h1 := congrArg (PowerSeries.coeff bk.Ep.natDegree) h0
    rw [PowerSeries.coeff_map, BK.E, Polynomial.coeff_coe, bk.monic.coeff_natDegree, map_one,
      map_zero] at h1
    exact one_ne_zero h1
  have e1 := s.eq_mul_weierstrassDiv_add_weierstrassMod hg
  set r := s %ʷ bk.E
  have e2 := Polynomial.modByMonic_add_div r bk.Ep
  have e3 : s = bk.E * (s /ʷ bk.E + ((r /ₘ bk.Ep : Polynomial (Wq l bk.a)) : bk.S)) +
      ((r %ₘ bk.Ep : Polynomial (Wq l bk.a)) : bk.S) := by
    conv_lhs => rw [e1, ← e2]
    rw [Polynomial.coe_add, Polynomial.coe_mul]
    simp only [BK.E]; ring
  have h3 : toDisc l (X : bk.S) bk.ρ₀ bk.E ∣ toDisc l (X : bk.S) bk.ρ₀ ((r %ₘ bk.Ep : Polynomial (Wq l bk.a)) : bk.S) := by
    have : ((r %ₘ bk.Ep : Polynomial (Wq l bk.a)) : bk.S) =
        s - bk.E * (s /ʷ bk.E + ((r /ₘ bk.Ep : Polynomial (Wq l bk.a)) : bk.S)) := by
      rw [eq_sub_iff_add_eq, add_comm, ← e3]
    rw [this, map_sub, map_mul]
    exact dvd_sub h (dvd_mul_right _ _)
  have h4 := GlobalTheory.BSP.DiscRem.eq_zero_of_dvd l K bk _ (Polynomial.degree_modByMonic_lt r bk.monic) h3
  rw [e3, h4, Polynomial.coe_zero, add_zero]
  exact dvd_mul_right _ _

theorem dvd_X (bk : BK K) (s : bk.S) (h : toDisc l (X : bk.S) bk.ρ₀ X ∣ toDisc l (X : bk.S) bk.ρ₀ s) :
    (X : bk.S) ∣ s := by
  rw [PowerSeries.X_dvd_iff]
  have hh : ‖toDisc l (0 : Wq l bk.a) 1 ((PowerSeries.constantCoeff : bk.S →+* Wq l bk.a) X)‖ ≤ bk.ρ₀ := by
    rw [PowerSeries.constantCoeff_X, map_zero, norm_zero]; exact NNReal.coe_nonneg _
  have hm := isDiscMap_map (l := l) (u := (X : bk.S)) (ρ := bk.ρ₀) (u' := (0 : Wq l bk.a)) (ρ' := 1)
    (PowerSeries.constantCoeff : bk.S →+* Wq l bk.a) hh
  obtain ⟨z, hz⟩ := h
  have h1 := congrArg (Disc.map (PowerSeries.constantCoeff : bk.S →+* Wq l bk.a) hh) hz
  rw [map_mul, hm.ext, hm.ext, PowerSeries.constantCoeff_X, map_zero, zero_mul] at h1
  exact (GlobalTheory.BSP.disc_zero_one l K bk).2.2.1 (h1.trans (map_zero _).symm)

theorem toDisc_inj (bk : BK K) : Function.Injective (toDisc l (X : bk.S) bk.ρ₀) := by
  haveI : IsAdicComplete bk.J bk.S := bk.complete
  exact (GlobalTheory.BSP.toDisc_injective_of_topBasis l K bk bk.S (RingHom.id bk.S) Unit (TopBasis.self bk.J) bk.ρ₀
    (ρ₀_pos_lt bk).1 (ρ₀_pos_lt bk).2).1

theorem mem_nzd (bk : BK K) {x : bk.DS bk.ρ₀} (hx : x ≠ 0) : x ∈ nonZeroDivisors (bk.DS bk.ρ₀) := by
  refine mem_nonZeroDivisors_iff.2 ⟨fun y hy => ?_, fun y hy => ?_⟩
  · have := GlobalTheory.BSP.GaussMul.norm_mul l K bk bk.ρ₀ (ρ₀_pos_lt bk).1 (ρ₀_pos_lt bk).2 x y
    rw [hy, norm_zero] at this
    exact norm_eq_zero.1 ((mul_eq_zero.1 this.symm).resolve_left (norm_ne_zero_iff.2 hx))
  · have := GlobalTheory.BSP.GaussMul.norm_mul l K bk bk.ρ₀ (ρ₀_pos_lt bk).1 (ρ₀_pos_lt bk).2 y x
    rw [hy, norm_zero] at this
    exact norm_eq_zero.1 ((mul_eq_zero.1 this.symm).resolve_right (norm_ne_zero_iff.2 hx))

theorem dvd_E_pow (bk : BK K) (m : ℕ) : ∀ s : bk.S,
    toDisc l (X : bk.S) bk.ρ₀ bk.E ^ m ∣ toDisc l (X : bk.S) bk.ρ₀ s → bk.E ^ m ∣ s := by
  induction m with
  | zero => intro s _; rw [pow_zero]; exact one_dvd _
  | succ m ih =>
    intro s h
    obtain ⟨s', rfl⟩ := dvd_E bk s ((dvd_pow_self _ (Nat.succ_ne_zero m)).trans h)
    obtain ⟨z, hz⟩ := h
    have hE : toDisc l (X : bk.S) bk.ρ₀ bk.E ≠ 0 := fun h0 =>
      bk.E_ne_zero (toDisc_inj bk (h0.trans (map_zero _).symm))
    rw [map_mul, pow_succ', mul_assoc] at hz
    have := (mul_cancel_left_mem_nonZeroDivisors (mem_nzd bk hE)).1 hz
    rw [pow_succ']
    exact mul_dvd_mul_left _ (ih s' ⟨z, this⟩)

end GlobalTheory.BSP.DiscDvd

namespace GlobalTheory.BSP.DiscDvd

variable {l : ℕ} [Fact l.Prime] {K : FinExt l}

theorem lift (bk : BK K) (g : bk.S) (hreg : toDisc l (X : bk.S) bk.ρ₀ g ∈ nonZeroDivisors (bk.DS bk.ρ₀))
    (hdiv : ∀ s : bk.S, toDisc l (X : bk.S) bk.ρ₀ g ∣ toDisc l (X : bk.S) bk.ρ₀ s → g ∣ s)
    (a : Ainf l) (h : bk.iS g ∣ bk.iA a) : bk.ev g ∣ a := by
  obtain ⟨ι, ⟨TB⟩⟩ := GlobalTheory.BSP.AinfTopBasis.main l K bk
  obtain ⟨h0, h1⟩ := ρ₀_pos_lt bk
  have hj : ‖toDisc l (bk.ev X) bk.ρ₀ (bk.ev X)‖ ≤ bk.ρ₀ := by
    simpa using norm_toDisc_pow_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) 1 h0
  have hjm := isDiscMap_map (l := l) (u := (X : bk.S)) (ρ := bk.ρ₀) (u' := bk.ev X) (ρ' := bk.ρ₀) bk.ev hj
  obtain ⟨cD, hc1, hc2, -, hc4, -⟩ :=
    GlobalTheory.BSP.disc_coefficients l K bk (Ainf l) bk.ev ι TB bk.ρ₀ h0 h1 _ hjm
  obtain ⟨y, hy⟩ := h
  have hiS : bk.iS g = Disc.map bk.ev hj (toDisc l (X : bk.S) bk.ρ₀ g) := (hjm.ext g).symm
  have hq : ∀ i, ∃ q : bk.S, TB.c i a = g * q ∧ toDisc l (X : bk.S) bk.ρ₀ q = cD i y := by
    intro i
    have e : toDisc l (X : bk.S) bk.ρ₀ (TB.c i a) = toDisc l (X : bk.S) bk.ρ₀ g * cD i y := by
      rw [← hc1, show toDisc l (bk.ev X) bk.ρ₀ a = bk.iA a from rfl, hy, hiS, hc2]
    obtain ⟨q, hq⟩ := hdiv _ ⟨_, e⟩
    refine ⟨q, hq, ?_⟩
    rw [hq, map_mul] at e
    exact (mul_cancel_left_mem_nonZeroDivisors hreg).1 e
  choose q hq1 hq2 using hq
  classical
  haveI : IsAdicComplete bk.J bk.S := bk.complete
  have hsmall := (GlobalTheory.BSP.toDisc_injective_of_topBasis l K bk bk.S (RingHom.id bk.S) Unit
    (TopBasis.self bk.J) bk.ρ₀ h0 h1).2.1
  have hfin : ∀ n, {i | q i ∉ bk.J ^ n}.Finite := by
    intro n
    obtain ⟨r, hr, hr'⟩ := hsmall n
    have hev : ∀ᶠ i in Filter.cofinite, ‖cD i y‖ < r :=
      (hc4 y).norm.eventually (gt_mem_nhds (by simpa using hr))
    refine (Filter.eventually_cofinite.1 hev).subset fun i hi hlt => hi ?_
    have h5 : ‖toDisc l (X : bk.S) bk.ρ₀ (q i)‖ ≤ r := by rw [hq2 i]; exact hlt.le
    have h6 := hr' (q i) h5
    rwa [Ideal.map_id] at h6
  let F : ℕ → Finset ι := fun n => (hfin n).toFinset
  have hF : ∀ n i, i ∉ F n → q i ∈ bk.J ^ n := fun n i hi => by
    simpa [F] using hi
  let I : Ideal (Ainf l) := bk.J.map bk.ev
  have key : ∀ n i, i ∉ F n → bk.ev (q i) ∈ I ^ n := fun n i hi => by
    rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ (hF n i hi)
  let f : ℕ → Ainf l := fun n => ∑ i ∈ F n, bk.ev (q i) * TB.b i
  have hmono : ∀ {m n : ℕ}, m ≤ n → F m ⊆ F n := fun {m n} hmn i hi => by
    simp only [F, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hi ⊢
    exact fun hn => hi (Ideal.pow_le_pow_right hmn hn)
  have hsm : ∀ n : ℕ, (I ^ n • (⊤ : Submodule (Ainf l) (Ainf l))) = I ^ n := fun n => by
    rw [smul_eq_mul, Ideal.mul_top]
  have hcauchy : ∀ {m n : ℕ}, m ≤ n → f m ≡ f n [SMOD I ^ m • (⊤ : Submodule (Ainf l) (Ainf l))] := by
    intro m n hmn
    rw [SModEq.sub_mem, hsm]
    have e : f m - f n = -∑ i ∈ F n \ F m, bk.ev (q i) * TB.b i := by
      simp only [f]
      rw [← Finset.sum_sdiff (hmono hmn)]; ring
    rw [e]
    refine neg_mem (Ideal.sum_mem _ fun i hi => Ideal.mul_mem_right _ _ (key m i ?_))
    exact (Finset.mem_sdiff.1 hi).2
  haveI : IsAdicComplete I (Ainf l) := TB.complete
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete I (Ainf l)) hcauchy
  refine ⟨L, ?_⟩
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (inferInstance : IsHausdorff I (Ainf l)) _ fun n => ?_
  rw [SModEq.sub_mem, sub_zero, hsm]
  have happ := TB.approx a n (F n) fun i hi => by rw [hq1 i]; exact Ideal.mul_mem_left _ _ (hF n i hi)
  rw [Ideal.map_pow] at happ
  have hs : ∑ i ∈ F n, bk.ev (TB.c i a) * TB.b i = bk.ev g * f n := by
    simp only [f, Finset.mul_sum, hq1, map_mul, mul_assoc]
  rw [hs] at happ
  have hLn := hL n
  rw [SModEq.sub_mem, hsm] at hLn
  have e : a - bk.ev g * L = (a - bk.ev g * f n) + bk.ev g * (f n - L) := by ring
  rw [e]
  exact add_mem happ (Ideal.mul_mem_left _ _ hLn)

end GlobalTheory.BSP.DiscDvd

namespace GlobalTheory.BSP

theorem ainf_dvd_of_disc_dvd : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (a : Ainf l),
    (∀ m : ℕ, bk.iS bk.E ^ m ∣ bk.iA a → bk.ev bk.E ^ m ∣ a) ∧ (bk.iS X ∣ bk.iA a → bk.ev X ∣ a) := by
  intro l _ K bk a
  have hE : toDisc l (X : bk.S) bk.ρ₀ bk.E ≠ 0 := fun h0 =>
    bk.E_ne_zero (DiscDvd.toDisc_inj bk (h0.trans (map_zero _).symm))
  have hX : toDisc l (X : bk.S) bk.ρ₀ X ≠ 0 := fun h0 =>
    PowerSeries.X_ne_zero (DiscDvd.toDisc_inj bk (h0.trans (map_zero _).symm))
  refine ⟨fun m h => ?_, fun h => DiscDvd.lift bk X (DiscDvd.mem_nzd bk hX) (DiscDvd.dvd_X bk) a h⟩
  rw [← map_pow] at h ⊢
  refine DiscDvd.lift bk (bk.E ^ m) ?_ (fun s hs => DiscDvd.dvd_E_pow bk m s ?_) a h
  · rw [map_pow]; exact pow_mem (DiscDvd.mem_nzd bk hE) m
  · rwa [map_pow] at hs

end GlobalTheory.BSP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AmbientJumpBlockOfAdmissibleDecompositionStatement
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ambientJumpBlock_of_admissibleDecomposition : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π → EmbeddingTypes.ambBlock (D := D) i r ρ π := by
  first | exact @GlobalTheory.AmbBlockDecomp.main | exact GlobalTheory.AmbBlockDecomp.main | (intros; apply GlobalTheory.AmbBlockDecomp.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ApproxRootSubUniformizerMemFilPStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.approxRoot_sub_uniformizer_mem_filP : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l) (n m : ℕ) (q : bk.S), bk.E ∣ q - (l : bk.S) ^ m * X → bk.E ^ n ∣ Polynomial.eval₂ PowerSeries.C q (bk.Ep.scaleRoots ((l : Wq l bk.a) ^ m)) → aDp l (bk.ev q) - (l : Per.BdRp l) ^ m * C.o (((bk.str.symm (Ideal.Quotient.mk _ X) : ↥(OL K)) : ↥K.1) : Om l) ∈ Per.FilP l n := by
  first | exact @GlobalTheory.BSP.approxRoot_sub_mem_fil | exact GlobalTheory.BSP.approxRoot_sub_mem_fil | (intros; apply GlobalTheory.BSP.approxRoot_sub_mem_fil <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisPeriodMatrixOverAcrisStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bcris_periodMatrix_over_acris : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (U U' : Matrix (Fin d) (Fin d) (Per.Bcris l)), U * U' = 1 → (∀ g : ↥(GK K), (ρ g).map (Per.zB l) * U.map (Per.σB (g : GQ l)) = U) → ∀ (c₁ : ℕ) (F : Matrix (Fin d) (Fin d) (Wq l bk.a)), (l : Per.Bcris l) ^ c₁ • U.map (Per.φB l) = U * F.map ((Per.aB l).comp (wA l bk.a).toRingHom) → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (X X' : Matrix (Fin d) (Fin d) (bk.S)), (∀ i j, (U.map C.ι * X.map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev))) i j ∈ Per.FilD l N) → (∀ i j, (X'.map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev)) * U'.map C.ι) i j ∈ Per.FilD l N) → ∃ Z Z' : Matrix (Fin d) (Fin d) (Per.Acris l), Z * Z' = C.t ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) ∧ (C.t ^ N * (l : Per.Acris l) ^ c₁) • Z.map (phiA l) = phiA l C.t ^ N • (Z * F.map (((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev).comp PowerSeries.C)) ∧ (∀ g : ↥(GK K), C.t ^ N • ((ρ g).map ((algebraMap (Ainf l) (Per.Acris l)).comp (algebraMap ℤ_[l] (Ainf l))) * Z.map (sigA (g : GQ l))) = sigA (g : GQ l) C.t ^ N • Z) ∧ (∀ i j, C.j ((Z * X.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)) i j) ∈ Per.FilP l (2 * N)) ∧ (∀ i j, C.j ((X'.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) * Z') i j) ∈ Per.FilP l (2 * N)) := by
  first | exact @GlobalTheory.CrisPeriods.periods_over_Acris | exact GlobalTheory.CrisPeriods.periods_over_Acris | (intros; apply GlobalTheory.CrisPeriods.periods_over_Acris <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BddCrisToODStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_mul_crisToOD_sub_toOD_dvd : ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (ϖ : PiSys l e) (m : ℕ), ∃ N : ℕ, ∀ z : OCr l O, ∃ y : OA l O, ϖ.iAl O K (EIn l e _) ^ m ∣ (l : OD l O) ^ N * crisToOD l O z - toOD l O y := by
  first | exact @GlobalTheory.BKReal.CrisBounded.bdd_crisToOD | exact GlobalTheory.BKReal.CrisBounded.bdd_crisToOD | (intros; apply GlobalTheory.BKReal.CrisBounded.bdd_crisToOD <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockDetMemHeckeAlgebraOfHeckeSpanStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockDet_mem_heckeAlgebra_of_heckeSpan : ∀ {Γ X O : Type} [Group Γ] [CommRing O] {n : ℕ} (T : Subalgebra O (X → O)) (rep : X → (Γ →* GL (Fin n) O)), CharPolyIn T rep → ∀ (g : ℕ) (Θ : Fin g → Fin g → X → Matrix (Fin n) (Fin n) O), (∀ p q, InRing T rep (Θ p q)) → (fun x => Matrix.det (Matrix.of fun (pa qb : Fin g × Fin n) => Θ pa.1 qb.1 x pa.2 qb.2)) ∈ T := by
  first | exact @GlobalTheory.SpanRing.blockDet_mem | exact GlobalTheory.SpanRing.blockDet_mem | (intros; apply GlobalTheory.SpanRing.blockDet_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinAinfDiscIsDomainNormBoundsStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_ainfDisc_isDomain_norm_bounds : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ : ℝ≥0), 0 < ρ → ρ < 1 → IsDomain (bk.DA ρ) ∧ (∀ x y : bk.DA ρ, (ρ : ℝ) ^ 2 * (‖x‖ * ‖y‖) ≤ ‖x * y‖) ∧ ∀ a : bk.DA ρ, a ≠ 0 → ∃ C : ℝ, ∀ y, ‖y‖ ≤ C * ‖a * y‖ := by
  first | exact @GlobalTheory.BSP.discAinf_isDomain | exact GlobalTheory.BSP.discAinf_isDomain | (intros; apply GlobalTheory.BSP.discAinf_isDomain <;> assumption)
end

