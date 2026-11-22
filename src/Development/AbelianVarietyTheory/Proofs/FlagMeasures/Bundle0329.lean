import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0093
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0106
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0097
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0073
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0309
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0191
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0131
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0058
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0143
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0321
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicUnitaryHaarBiInvariant
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0311
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0220
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0318
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0316
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0167
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.RightDerivativeZeroOutsideSupport

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.KappaBound
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.WedgeKappaL

theorem kappa_bound : Hyps → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (lb : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R lb dg → ∀ (l : ℕ) (hl : l ≤ r + 1) ν, n1 ν + (r + 1) * (r + 2) ≤ q0 → ∀ io pr ep, TensH (cmp l) (cmp l (Formalism.QuantumDeterminants.Hpk k r)) (R ν) (fun I : Sub (2 * r + k + 1) l => R (ν + eZ I.1)) io pr ep → NzOn (R ν) (lb ν) → ∀ (I : Sub (2 * r + k + 1) l) (κ₀ : ℂ), NzOn (R (ν + eZ I.1)) (lb (ν + eZ I.1)) → (∀ v ∈ (R ν).sm, lb (ν + eZ I.1) (∑ c, pr I c (tm (R ν) (wedge (fun a : Fin l => Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a))) v c)) = κ₀ • lb ν v) → ‖κ₀‖ ^ 2 * dg ν / dg (ν + eZ I.1) ≤ Hsq r (Formalism.QuantumDeterminants.Tz k r z) b ^ l := by
  intro hyp k r Wp _ _ _ _ lam u b bv ga h q0 z π μW μN μG νq R lb dg hS l hl ν hν io pr ep hT hnz I κ₀ hnzI hκ
  classical
  have hS' := hS
  obtain ⟨hNum, hFam, hG, hSF⟩ := hS'
  have hν0 : n1 ν ≤ q0 := by omega
  have hνJ : ∀ J : Sub (2 * r + k + 1) l, n1 (ν + eZ J.1) + (r + 1) ^ 2 ≤ q0 := by
    intro J
    have := GlobalTheory.WedgeKappa.n1_add_eZ_le_add_card ν J.1
    rw [J.2] at this
    nlinarith
  have hνJ0 : ∀ J : Sub (2 * r + k + 1) l, n1 (ν + eZ J.1) ≤ q0 := fun J =>
    le_trans (Nat.le_add_right _ _) (hνJ J)
  have hDS := hFam ν hν0
  have hDSJ := fun J : Sub (2 * r + k + 1) l => hFam (ν + eZ J.1) (hνJ0 J)
  have hF := GlobalTheory.WedgeFRep.isFRep_cmp k r l
  have hdual := fun J : Sub (2 * r + k + 1) l =>
    GlobalTheory.KappaDual.kappa_dual hyp k r _ _ _ _ _ (R ν) _ io pr ep _ _ _ Wp z π u μW μN μG νq
      (wedge (fun a : Fin l => Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a))) (lb ν) hDS hDSJ hF hT hG
      (fun s hs => (GlobalTheory.T.flagWedge_fixed_and_length_eq_prod_distances k r l hl z hG.1).1 s hs) (hSF ν hν0).1 hnz J
      (lb (ν + eZ J.1)) (hSF _ (hνJ0 J)).1
  have hex : ∀ J : Sub (2 * r + k + 1) l, ∃ c : ℂ, (J = I → c = κ₀) ∧
      ∀ y ∈ (R (ν + eZ J.1)).sm, lb ν (ev (cmp l (Formalism.QuantumDeterminants.Hpk k r)) (R ν) (wedge (fun a : Fin l => Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a)))
        (fun c => io J c y)) = ((ep J : ℂ) * star c) • lb (ν + eZ J.1) y := by
    intro J
    by_cases hJ : J = I
    · subst hJ
      exact ⟨κ₀, fun _ => rfl, (hdual J).2 κ₀ hκ⟩
    · obtain ⟨c, hc⟩ := (hdual J).1
      exact ⟨c, fun h => absurd h hJ, (hdual J).2 c hc⟩
  choose κ hκI hκd using hex
  have hd0 : 0 < dg ν := (hSF ν hν0).2.1
  have hdJ : ∀ J : Sub (2 * r + k + 1) l, 0 < dg (ν + eZ J.1) := fun J => (hSF _ (hνJ0 J)).2.1
  have hmass := GlobalTheory.MomMass.mom_mass hyp k r Wp lam u b bv ga h q0 z π μW μN μG νq R lb dg hS
  obtain ⟨w, hw, hw1, hint⟩ := GlobalTheory.T.mass_bound_low_types hyp k r Wp lam u b bv ga h q0 z π μW μN μG νq R lb dg hS l hl _ (hνJ I) hnzI
  have hinj : Function.Injective (fun (J : Sub (2 * r + k + 1) l) (a : Fin (2 * r + k + 1)) =>
      lam a + (((ν + eZ J.1) a : ℤ) : ℝ)) := by
    intro J J' hJ
    apply Subtype.ext
    apply GlobalTheory.WedgeKappa.eZ_injective
    funext a
    have := congrFun hJ a
    simp only [Pi.add_apply, add_right_inj, Int.cast_inj] at this
    exact this
  have h8 := GlobalTheory.MomLem8.moment_lemma_pieri hyp k r _ _ _ _ _ (R ν) _ io pr ep _ _ _ Wp z π u μW μN μG νq
    (wedge (fun a : Fin l => Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a))) (fun w => ((Real.sqrt (dg ν) : ℝ) : ℂ) • lb ν w)
    (fun J w => ((Real.sqrt (dg (ν + eZ J.1)) : ℝ) : ℂ) • lb (ν + eZ J.1) w)
    (fun J => if NzOn (R (ν + eZ J.1)) (lb (ν + eZ J.1)) then
      (ep J : ℂ) * star (κ J) * ((Real.sqrt (dg ν) : ℝ) : ℂ) / ((Real.sqrt (dg (ν + eZ J.1)) : ℝ) : ℂ) else 0)
    hDS hDSJ hinj hF hT hG ((hmass ν hν0).2 hnz).1
    (fun J => by
      by_cases hJ : NzOn (R (ν + eZ J.1)) (lb (ν + eZ J.1))
      · exact Or.inl ((hmass _ (hνJ0 J)).2 hJ).1
      · exact Or.inr (if_neg hJ))
    (fun J y hy => by
      rw [hκd J y hy]
      by_cases hJ : NzOn (R (ν + eZ J.1)) (lb (ν + eZ J.1))
      · rw [if_pos hJ, smul_smul, smul_smul]
        congr 1
        have : ((Real.sqrt (dg (ν + eZ J.1)) : ℝ) : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (hdJ J)).ne'
        field_simp
      · have : lb (ν + eZ J.1) y = 0 := by
          by_contra hne
          exact hJ ⟨y, hy, hne⟩
        rw [if_neg hJ, this]
        simp)
    I ((hmass _ (hνJ0 I)).2 hnzI).1 w hw
  have hae := (GlobalTheory.quotMeas_ae_mem_and_measurable hyp.1.2.2.1 k r _ _ (R ν) Wp z π u μW μN μG νq hDS hG).1
  rw [if_pos hnzI, hκI I rfl, hw1] at h8
  have h9 := h8.trans (le_trans (le_of_eq (lintegral_congr_ae ?_)) hint)
  · have hH : 0 ≤ Hsq r (Formalism.QuantumDeterminants.Tz k r z) b ^ l := by
      apply pow_nonneg
      unfold Hsq
      apply mul_nonneg (le_trans zero_le_one (le_max_left _ _))
      rw [show 20 * (r + 1) = 2 * (10 * (r + 1)) by ring, pow_mul]
      positivity
    rw [ENNReal.ofReal_le_ofReal_iff hH] at h9
    refine le_trans (le_of_eq ?_) h9
    have hep : ‖(ep I : ℂ)‖ = 1 := by
      rcases hT.ep_sq I with h | h <;> simp [h]
    rw [norm_div, norm_mul, norm_mul, hep, norm_star, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, div_pow, mul_pow, sq_abs, sq_abs, Real.sq_sqrt hd0.le, Real.sq_sqrt (hdJ I).le]
    ring
  · filter_upwards [hae] with x hx
    rw [(GlobalTheory.T.flagWedge_fixed_and_length_eq_prod_distances k r l hl z hG.1).2 _ hx, norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      sq_abs, Real.sq_sqrt (hdJ I).le]

end GlobalTheory.WedgeKappaL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeftQuotientCovolumeEqFundamentalDomainInter
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.CovolRat

theorem covol_eq_inter_fund : ∀ (I : AutInst) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure] (fund A : Set I.GA), I.IsFundDom (I.muA μf) fund → MeasurableSet A → (∀ γ ∈ I.GFset, ∀ x ∈ A, γ * x ∈ A) → covol I.GFset (I.muA μf) A = I.muA μf (A ∩ fund) ∧ 0 < I.muA μf fund := by
  intro I μf _ _ fund A hfund hA hinv
  obtain ⟨hleft, -, -, -, hopen⟩ := GlobalTheory.AdelicUnimod.adelic_unimodular I μf
  obtain ⟨⟨Γ, hΓ⟩, hcount, -⟩ := GlobalTheory.RatDiscrete.subgroup_countable_discrete I
  obtain ⟨hmeas, hcov, hdisj⟩ := hfund

  have hm : ∀ γ, γ ∈ Γ ↔ γ ∈ I.GFset := fun γ => by rw [← hΓ]; exact SetLike.mem_coe.symm
  refine ⟨?_, ?_⟩
  · have key := GlobalTheory.covol_eq_measure_inter_fund I.GA Γ (I.muA μf) fund A (by rw [hΓ]; exact hcount)
      (fun γ _ => hleft γ) hmeas
      (fun y => by obtain ⟨γ, hγ, h⟩ := hcov y; exact ⟨γ, (hm γ).2 hγ, h⟩)
      (fun γ hγ h1 => hdisj γ ((hm γ).1 hγ) h1) hA (fun γ hγ x hx => hinv γ ((hm γ).1 hγ) x hx)
    rw [hΓ] at key
    exact key
  ·
    rw [pos_iff_ne_zero]
    intro h0
    have hpre : ∀ γ : I.GA, I.muA μf ((fun y => γ * y) ⁻¹' fund) = 0 := by
      intro γ
      rw [← Measure.map_apply (measurable_const_mul γ) hmeas, hleft γ, h0]
    have hsub : (Set.univ : Set I.GA) ⊆ ⋃ γ ∈ I.GFset, (fun y => γ * y) ⁻¹' fund := by
      intro y _
      obtain ⟨γ, hγ, h⟩ := hcov y
      exact Set.mem_biUnion hγ h
    have hnull : I.muA μf Set.univ = 0 :=
      measure_mono_null hsub ((measure_biUnion_null_iff hcount).2 fun γ _ => hpre γ)
    have hpos := hopen Set.univ isOpen_univ ⟨1, trivial⟩
    rw [hnull] at hpos
    exact lt_irrefl _ hpos

end GlobalTheory.CovolRat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralTranslateLeMultiplicityFundamental
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.BoundedUnfold

theorem multiplicity_le (I : AutInst) (g : ℕ) (S : Set I.Ginf) (y z : I.GA) (hn : 1 ≤ I.n)
    (hS : ∀ a ∈ S, ∀ a' ∈ S, ∀ v, dOp (uMat ((a * a'⁻¹) v)) ≤ Real.log 2) :
    {γ : GlobalTheory.RatDiscrete.ratSub I | y⁻¹ * (γ.1 * z) ∈ S ×ˢ I.Kg g}.Finite ∧
    (({γ : GlobalTheory.RatDiscrete.ratSub I | y⁻¹ * (γ.1 * z) ∈ S ×ˢ I.Kg g}.ncard : ℕ) : ℝ) ≤
      (1 + 4 * Real.sqrt I.n / tau1 I y ^ 2) ^ (2 * (I.n ^ 2 * I.f)) := by
  classical
  have hτ : 0 < tau1 I y := GlobalTheory.RationalCount.truncatedLeastLatticeSize_pos I hn y
  rcases Set.eq_empty_or_nonempty
      {γ : GlobalTheory.RatDiscrete.ratSub I | y⁻¹ * (γ.1 * z) ∈ S ×ˢ I.Kg g} with h0 | ⟨γ0, hγ0⟩
  · rw [h0]
    refine ⟨Set.finite_empty, ?_⟩
    rw [Set.ncard_empty, Nat.cast_zero]
    positivity
  · obtain ⟨hCfin, hCcard⟩ :=
      GlobalTheory.RationalCount.count_le I y y (fun _ => Real.log 2) hn (fun _ => (Real.log_pos one_lt_two).le)

    have hf : ∀ γ ∈ {γ : GlobalTheory.RatDiscrete.ratSub I | y⁻¹ * (γ.1 * z) ∈ S ×ˢ I.Kg g},
        (fun γ : GlobalTheory.RatDiscrete.ratSub I => γ.1 * γ0.1⁻¹) γ ∈
          {a : I.GA | a ∈ I.GFset ∧ (y⁻¹ * a * y).2 ∈ I.Kset ∧
            ∀ v, dOp (uMat ((y⁻¹ * a * y).1 v)) ≤ (fun _ => Real.log 2) v} := by
      intro γ hγ
      have hγ' : y⁻¹ * (γ.1 * z) ∈ S ×ˢ I.Kg g := hγ
      have hγ0' : y⁻¹ * (γ0.1 * z) ∈ S ×ˢ I.Kg g := hγ0
      have key : y⁻¹ * (γ.1 * γ0.1⁻¹) * y = (y⁻¹ * (γ.1 * z)) * (y⁻¹ * (γ0.1 * z))⁻¹ := by
        group
      refine ⟨?_, ?_, ?_⟩
      · exact (GlobalTheory.RatDiscrete.ratSub I).mul_mem γ.2 ((GlobalTheory.RatDiscrete.ratSub I).inv_mem γ0.2)
      · rw [key]
        have h1 := hγ'.2.1
        have h2 := hγ0'.2.1
        simp only [AutInst.Kset, Set.mem_ofPred_eq] at h1 h2 ⊢
        rw [Prod.snd_mul, Prod.snd_inv]
        push_cast
        exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ h2)
      · intro v
        rw [key, Prod.fst_mul, Prod.fst_inv]
        exact hS _ hγ'.1 _ hγ0'.1 v
    have hinj : Set.InjOn (fun γ : GlobalTheory.RatDiscrete.ratSub I => γ.1 * γ0.1⁻¹)
        {γ : GlobalTheory.RatDiscrete.ratSub I | y⁻¹ * (γ.1 * z) ∈ S ×ˢ I.Kg g} :=
      fun a _ b _ hab => Subtype.ext (mul_right_cancel hab)
    have hAfin : {γ : GlobalTheory.RatDiscrete.ratSub I | y⁻¹ * (γ.1 * z) ∈ S ×ˢ I.Kg g}.Finite :=
      Set.Finite.of_finite_image (hCfin.subset (Set.image_subset_iff.2 hf)) hinj
    refine ⟨hAfin, ?_⟩
    refine le_trans (Nat.cast_le.2 (Set.ncard_le_ncard_of_injOn _ hf hinj hCfin)) (le_trans hCcard ?_)
    have hsum : (∑ v : InfinitePlace I.F, (fun _ => Real.log 2) v) = (I.f : ℝ) * Real.log 2 := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, GlobalTheory.RationalCount.card_places]
    have hE : Real.exp ((∑ v : InfinitePlace I.F, (fun _ => Real.log 2) v) / I.f) ≤ 2 := by
      rw [hsum]
      rcases Nat.eq_zero_or_pos I.f with hf0 | hfpos
      · rw [hf0]; norm_num
      · have : (I.f : ℝ) ≠ 0 := by exact_mod_cast hfpos.ne'
        rw [mul_div_cancel_left₀ _ this, Real.exp_log two_pos]
    apply pow_le_pow_left₀ (by positivity)
    have h2 : 2 * Real.sqrt I.n * Real.exp ((∑ v : InfinitePlace I.F, (fun _ => Real.log 2) v) / I.f) /
        (tau1 I y * tau1 I y) ≤ 2 * Real.sqrt I.n * 2 / (tau1 I y * tau1 I y) := by
      gcongr
    calc _ ≤ 1 + 2 * Real.sqrt I.n * 2 / (tau1 I y * tau1 I y) := by linarith
      _ = 1 + 4 * Real.sqrt I.n / tau1 I y ^ 2 := by ring

theorem lintegral_le_multiplicity : ∀ (B : RowsAut) (S : Set B.I.Ginf) (y : B.I.GA) (Φ : B.I.GA → ENNReal), 1 ≤ B.I.n → 1 ≤ B.g → MeasurableSet S → (∀ a ∈ S, ∀ a' ∈ S, ∀ v, dOp (uMat ((a * a'⁻¹) v)) ≤ Real.log 2) → Measurable Φ → (∀ γ ∈ B.I.GFset, ∀ z, Φ (γ * z) = Φ z) → (∀ k ∈ B.I.Kg B.g, ∀ z, Φ (z * (1, k)) = Φ z) → B.μf (B.I.Kg B.g) * ∫⁻ a in S, Φ (y * (a, 1)) ∂(muInf B.I) ≤ ENNReal.ofReal ((1 + 4 * Real.sqrt B.I.n / tau1 B.I y ^ 2) ^ (2 * (B.I.n ^ 2 * B.I.f))) * ∫⁻ z in B.fund, Φ z ∂(B.I.muA B.μf) := by
  intro B S y Φ hn hg hSm hS hΦ hΦl hΦr
  classical
  have hL : ∀ a : B.I.GA, Measurable (fun q : B.I.GA => a * q) := fun a =>
    (GlobalTheory.AdelicUnfold.measurePreserving_left B.I B.μf a).measurable
  have hKm : MeasurableSet (B.I.Kg B.g) :=
    ((GlobalTheory.CongTop.adelic_topology B.I).2.2.2.2.2.2 B.g hg).1.measurableSet
  have hUm : MeasurableSet (S ×ˢ B.I.Kg B.g) := hSm.prod hKm

  have step1 : B.μf (B.I.Kg B.g) * ∫⁻ a in S, Φ (y * (a, 1)) ∂(muInf B.I) =
      ∫⁻ p in S ×ˢ B.I.Kg B.g, Φ (y * p) ∂(B.I.muA B.μf) := by
    rw [AutInst.muA, ← Measure.prod_restrict, lintegral_prod (fun p => Φ (y * p)) (hΦ.comp (hL y)).aemeasurable]
    have inner : ∀ a : B.I.Ginf, ∫⁻ k in B.I.Kg B.g, Φ (y * (a, k)) ∂B.μf =
        Φ (y * (a, 1)) * B.μf (B.I.Kg B.g) := by
      intro a
      rw [← setLIntegral_const]
      refine setLIntegral_congr_fun hKm (fun k hk => ?_)
      have e : y * (a, k) = y * (a, 1) * (1, k) := by
        rw [mul_assoc]
        congr 1
        exact Prod.ext (mul_one a).symm (one_mul k).symm
      rw [e, hΦr k hk]
    simp_rw [inner]
    rw [lintegral_mul_const (f := fun a : B.I.Ginf => Φ (y * (a, 1))) _
      (hΦ.comp ((hL y).comp measurable_prodMk_right))]
    exact mul_comm _ _

  have hH : Measurable (fun q : B.I.GA => (S ×ˢ B.I.Kg B.g).indicator (fun p => Φ (y * p)) (y⁻¹ * q)) :=
    ((hΦ.comp (hL y)).indicator hUm).comp (hL y⁻¹)
  have step2 : ∫⁻ p in S ×ˢ B.I.Kg B.g, Φ (y * p) ∂(B.I.muA B.μf) =
      ∫⁻ q, (S ×ˢ B.I.Kg B.g).indicator (fun p => Φ (y * p)) (y⁻¹ * q) ∂(B.I.muA B.μf) := by
    rw [← lintegral_indicator hUm,
      ← (GlobalTheory.AdelicUnfold.measurePreserving_left B.I B.μf y).lintegral_comp hH]
    congr 1
    funext p
    simp only [inv_mul_cancel_left]

  have hfd := GlobalTheory.RatDiscrete.isFundamentalDomain B.I B.μf B.fund B.fund_spec
  have : Countable (GlobalTheory.RatDiscrete.ratSub B.I) :=
    Set.Countable.to_subtype (s := (GlobalTheory.RatDiscrete.ratSub B.I : Set B.I.GA))
      (GlobalTheory.RatDiscrete.countable_GFset B.I)
  have : MeasurableConstSMul (GlobalTheory.RatDiscrete.ratSub B.I) B.I.GA := ⟨fun c => hL c.1⟩
  have : SMulInvariantMeasure (GlobalTheory.RatDiscrete.ratSub B.I) B.I.GA (B.I.muA B.μf) :=
    ⟨fun c s hs => (GlobalTheory.AdelicUnfold.measurePreserving_left B.I B.μf c.1).measure_preimage
      hs.nullMeasurableSet⟩

  have hpt : ∀ z : B.I.GA, ∑' γ : GlobalTheory.RatDiscrete.ratSub B.I,
      (S ×ˢ B.I.Kg B.g).indicator (fun p => Φ (y * p)) (y⁻¹ * (γ.1 * z)) ≤
        ENNReal.ofReal ((1 + 4 * Real.sqrt B.I.n / tau1 B.I y ^ 2) ^ (2 * (B.I.n ^ 2 * B.I.f))) * Φ z := by
    intro z
    obtain ⟨hAf, hAc⟩ := multiplicity_le B.I B.g S y z hn hS
    have hHA : ∀ γ : GlobalTheory.RatDiscrete.ratSub B.I,
        (S ×ˢ B.I.Kg B.g).indicator (fun p => Φ (y * p)) (y⁻¹ * (γ.1 * z)) =
          {γ : GlobalTheory.RatDiscrete.ratSub B.I | y⁻¹ * (γ.1 * z) ∈ S ×ˢ B.I.Kg B.g}.indicator
            (fun _ => Φ z) γ := by
      intro γ
      by_cases h : y⁻¹ * (γ.1 * z) ∈ S ×ˢ B.I.Kg B.g
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show γ ∈ {γ : GlobalTheory.RatDiscrete.ratSub B.I |
          y⁻¹ * (γ.1 * z) ∈ S ×ˢ B.I.Kg B.g} from h)]
        show Φ (y * (y⁻¹ * (γ.1 * z))) = Φ z
        rw [mul_inv_cancel_left]
        exact hΦl γ.1 γ.2 z
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show γ ∉ {γ : GlobalTheory.RatDiscrete.ratSub B.I |
          y⁻¹ * (γ.1 * z) ∈ S ×ˢ B.I.Kg B.g} from h)]
    have hsum1 : ∑' γ : GlobalTheory.RatDiscrete.ratSub B.I,
        {γ : GlobalTheory.RatDiscrete.ratSub B.I | y⁻¹ * (γ.1 * z) ∈ S ×ˢ B.I.Kg B.g}.indicator (fun _ => Φ z) γ =
        ∑ γ ∈ hAf.toFinset,
          {γ : GlobalTheory.RatDiscrete.ratSub B.I | y⁻¹ * (γ.1 * z) ∈ S ×ˢ B.I.Kg B.g}.indicator (fun _ => Φ z) γ :=
      tsum_eq_sum (s := hAf.toFinset) (fun γ hγ => Set.indicator_of_notMem (by simpa using hγ) _)
    have hsum2 : ∑ γ ∈ hAf.toFinset,
          {γ : GlobalTheory.RatDiscrete.ratSub B.I | y⁻¹ * (γ.1 * z) ∈ S ×ˢ B.I.Kg B.g}.indicator (fun _ => Φ z) γ =
        ∑ γ ∈ hAf.toFinset, Φ z :=
      Finset.sum_congr rfl (fun γ hγ => Set.indicator_of_mem (by simpa using hγ) _)
    rw [tsum_congr hHA, hsum1, hsum2, Finset.sum_const, nsmul_eq_mul, ← Set.ncard_eq_toFinset_card _ hAf]
    gcongr
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hAc
  calc B.μf (B.I.Kg B.g) * ∫⁻ a in S, Φ (y * (a, 1)) ∂(muInf B.I)
      = ∫⁻ q, (S ×ˢ B.I.Kg B.g).indicator (fun p => Φ (y * p)) (y⁻¹ * q) ∂(B.I.muA B.μf) := by
        rw [step1, step2]
    _ = ∫⁻ z in B.fund, ∑' γ : GlobalTheory.RatDiscrete.ratSub B.I,
          (S ×ˢ B.I.Kg B.g).indicator (fun p => Φ (y * p)) (y⁻¹ * (γ.1 * z)) ∂(B.I.muA B.μf) := by
        rw [hfd.lintegral_eq_tsum''
          (fun q : B.I.GA => (S ×ˢ B.I.Kg B.g).indicator (fun p => Φ (y * p)) (y⁻¹ * q))]
        rw [lintegral_tsum (f := fun (γ : GlobalTheory.RatDiscrete.ratSub B.I) (z : B.I.GA) =>
            (S ×ˢ B.I.Kg B.g).indicator (fun p => Φ (y * p)) (y⁻¹ * (γ.1 * z)))
          (fun γ => (hH.comp (hL γ.1)).aemeasurable)]
        simp only [Subgroup.smul_def]
        rfl
    _ ≤ ∫⁻ z in B.fund, ENNReal.ofReal ((1 + 4 * Real.sqrt B.I.n / tau1 B.I y ^ 2) ^
          (2 * (B.I.n ^ 2 * B.I.f))) * Φ z ∂(B.I.muA B.μf) := lintegral_mono hpt
    _ = _ := lintegral_const_mul _ hΦ

end GlobalTheory.BoundedUnfold
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MapConjGaugeMeasureEqInvDetSmul
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.GaugeConjScale

open Topology Filter

theorem integral_comp_mulVec {d : ℕ} (L : Matrix (Fin d) (Fin d) ℝ) (hL : L.det ≠ 0)
    (φ : (Fin d → ℝ) → ℝ) (hφ : Continuous φ) :
    ∫ t, φ (L *ᵥ t) = |L.det|⁻¹ * ∫ t, φ t := by
  have hc : Continuous (Matrix.toLin' L) := LinearMap.continuous_of_finiteDimensional _
  have h := Real.map_matrix_volume_pi_eq_smul_volume_pi hL
  have h2 : ∫ t, φ t ∂(Measure.map (Matrix.toLin' L) volume) = ∫ t, φ (Matrix.toLin' L t) :=
    integral_map hc.measurable.aemeasurable hφ.aestronglyMeasurable
  rw [h, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _), abs_inv, smul_eq_mul] at h2
  simpa using h2.symm

theorem hasCompactSupport_comp_mulVec {d : ℕ} (L : Matrix (Fin d) (Fin d) ℝ) (hL : L.det ≠ 0)
    (φ : (Fin d → ℝ) → ℝ) (hφ : HasCompactSupport φ) : HasCompactSupport (fun t => φ (L *ᵥ t)) := by
  have hu : IsUnit L.det := isUnit_iff_ne_zero.2 hL
  let e : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ) :=
    (Matrix.toLinearEquiv' L (Matrix.invertibleOfIsUnitDet L hu)).toContinuousLinearEquiv
  exact hφ.comp_homeomorph e.toHomeomorph

theorem scalar_eq_inv_det {X : Type} [MeasurableSpace X] (μ : Measure X) (T : X → X) (hT : Measurable T)
    (h : X → ℝ) (hh : Measurable h) {d : ℕ} (t : X → Fin d → ℝ) (ht : Measurable t)
    (L : Matrix (Fin d) (Fin d) ℝ) (hL : L.det ≠ 0) (c : NNReal) (hc : μ.map T = (c : ENNReal) • μ)
    (hTt : ∀ᵐ g ∂μ, t (T g) = L *ᵥ t g) (C : ℝ) (hC : 1 ≤ C) (h1 : ∀ g, h (T g) ≤ C * h g)
    (h2 : ∀ g, h g ≤ C * h (T g)) (ρ : ℝ) (hρ : 0 < ρ) (hfin : μ {g | h g < ρ} ≠ ⊤)
    (hlim : ∀ r₁ : ℝ, 0 < r₁ → r₁ ≤ ρ → ∀ φ : (Fin d → ℝ) → ℝ, Continuous φ → HasCompactSupport φ →
      Tendsto (fun r : ℝ => (r ^ d)⁻¹ * ∫ g in {g | h g < r₁}, φ (fun i => t g i / r) ∂μ)
        (𝓝[>] 0) (𝓝 (∫ x, φ x))) :
    (c : ℝ) = |L.det|⁻¹ := by
  have hC0 : 0 < C := lt_of_lt_of_le one_pos hC
  let b : ContDiffBump (0 : Fin d → ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  let φ : (Fin d → ℝ) → ℝ := b
  have hφc : Continuous φ := b.continuous
  have hφs : HasCompactSupport φ := b.hasCompactSupport
  have hφp : 0 < ∫ x, φ x := b.integral_pos
  have hφ0 : ∀ x, 0 ≤ φ x := fun x => b.nonneg
  have hφ1 : ∀ x, φ x ≤ 1 := fun x => b.le_one
  let ψ : (Fin d → ℝ) → ℝ := fun x => φ (L *ᵥ x)
  have hψc : Continuous ψ := hφc.comp (continuous_const.matrix_mulVec continuous_id)
  have hψs : HasCompactSupport ψ := hasCompactSupport_comp_mulVec L hL φ hφs
  have hψi : ∫ x, ψ x = |L.det|⁻¹ * ∫ x, φ x := integral_comp_mulVec L hL φ hφc
  have hr1 : 0 < ρ / C := div_pos hρ hC0
  have hr1' : ρ / C ≤ ρ := div_le_self hρ.le hC
  have hr2 : 0 < ρ / C / C := div_pos hr1 hC0
  have hr2' : ρ / C / C ≤ ρ := (div_le_self hr1.le hC).trans hr1'
  have hB1 : MeasurableSet {g | h g < ρ / C} := measurableSet_lt hh measurable_const
  have hs1 : {g | h g < ρ / C / C} ⊆ T ⁻¹' {g | h g < ρ / C} := by
    intro g hg
    have hg : h g < ρ / C / C := hg
    rw [lt_div_iff₀ hC0] at hg
    have := h1 g
    show h (T g) < ρ / C
    linarith
  have hs2 : T ⁻¹' {g | h g < ρ / C} ⊆ {g | h g < ρ} := by
    intro g hg
    have hg : h (T g) < ρ / C := hg
    rw [lt_div_iff₀ hC0] at hg
    have := h2 g
    show h g < ρ
    linarith
  have hm : ∀ r : ℝ, Measurable (fun g => (fun i => t g i / r : Fin d → ℝ)) := fun r =>
    measurable_pi_lambda _ fun i => ((measurable_pi_apply i).comp ht).div_const r
  have hint : ∀ r : ℝ, IntegrableOn (fun g => ψ (fun i => t g i / r)) {g | h g < ρ} μ := by
    intro r
    refine Measure.integrableOn_of_bounded (M := 1) hfin (hψc.measurable.comp (hm r)).aestronglyMeasurable ?_
    refine Eventually.of_forall fun g => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hφ0 _)]
    exact hφ1 _
  have key : ∀ r : ℝ, (c : ℝ) * ∫ g in {g | h g < ρ / C}, φ (fun i => t g i / r) ∂μ
      = ∫ g in T ⁻¹' {g | h g < ρ / C}, ψ (fun i => t g i / r) ∂μ := by
    intro r
    have e1 := setIntegral_map (μ := μ) (g := T) (f := fun g => φ (fun i => t g i / r)) hB1
      (hφc.measurable.comp (hm r)).aestronglyMeasurable hT.aemeasurable
    rw [hc, Measure.restrict_smul, integral_smul_measure, ENNReal.coe_toReal, smul_eq_mul] at e1
    rw [e1]
    refine integral_congr_ae (ae_restrict_of_ae (hTt.mono fun g hg => ?_))
    have e2 : ∀ y : Fin d → ℝ, (fun i => y i / r) = r⁻¹ • y := fun y => by
      ext i; simp [div_eq_inv_mul]
    show φ (fun i => t (T g) i / r) = φ (L *ᵥ fun i => t g i / r)
    rw [e2, e2, hg, Matrix.mulVec_smul]
  have l1 := (hlim _ hr1 hr1' φ hφc hφs).const_mul (c : ℝ)
  have l2 := hlim _ hr2 hr2' ψ hψc hψs
  have l3 := hlim _ hρ le_rfl ψ hψc hψs
  have a1 : ∫ x, ψ x ≤ c * ∫ x, φ x := by
    refine le_of_tendsto_of_tendsto l2 l1 ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr : 0 < r := hr
    rw [mul_left_comm, key]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact setIntegral_mono_set ((hint r).mono_set hs2) (Eventually.of_forall fun g => hφ0 _) hs1.eventuallyLE
  have a2 : c * ∫ x, φ x ≤ ∫ x, ψ x := by
    refine le_of_tendsto_of_tendsto l1 l3 ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr : 0 < r := hr
    rw [mul_left_comm, key]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact setIntegral_mono_set (hint r) (Eventually.of_forall fun g => hφ0 _) hs2.eventuallyLE
  exact mul_right_cancel₀ hφp.ne' ((le_antisymm a2 a1).trans hψi)

theorem hs_conj_le {n : ℕ} {ε : Fin n → Bool} (m g : Formalism.REAL.UJ ε) :
    Formalism.REAL.hs (uMat (m * g * m⁻¹) - 1) ≤
      Formalism.REAL.hs (uMat m) * Formalism.REAL.hs (uMat m⁻¹) * Formalism.REAL.hs (uMat g - 1) := by
  have a : uMat (m * g * m⁻¹) = uMat m * uMat g * uMat m⁻¹ := rfl
  have b : uMat m * uMat m⁻¹ = 1 := by
    have : uMat m * uMat m⁻¹ = uMat (m * m⁻¹) := rfl
    rw [this, mul_inv_cancel]; rfl
  have e : uMat (m * g * m⁻¹) - 1 = uMat m * (uMat g - 1) * uMat m⁻¹ := by
    rw [a, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, b]
  rw [e]
  refine (Formalism.REAL.frobenius_mul_le _ _).trans ?_
  rw [mul_right_comm]
  exact mul_le_mul_of_nonneg_right (Formalism.REAL.frobenius_mul_le _ _) (Formalism.REAL.frobenius_nonneg _)

theorem map_conj_eq_inv_det_smul (n : ℕ) (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (d : ℕ)
    (E : Fin d → Matrix (Fin n) (Fin n) ℂ) (S : Subgroup (Formalism.REAL.UJ ε))
    (hA : ∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A)
    (hE : ∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0)
    (hsp : ∀ X, (X ∈ A ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E))
    (hS : ∀ g, g ∈ S ↔ uMat g - 1 ∈ A) (hcl : IsClosed (S : Set (Formalism.REAL.UJ ε)))
    (μ : Measure (Formalism.REAL.UJ ε)) (hμ : IsGaugeSub (S : Set (Formalism.REAL.UJ ε)) d μ)
    (m : Formalism.REAL.UJ ε) (L : Matrix (Fin d) (Fin d) ℝ) (hm : ∀ g, g ∈ S ↔ m * g * m⁻¹ ∈ S)
    (hmL : ∀ k, uMat m * E k * uMat m⁻¹ = ∑ i, L i k • E i) (hL : L.det ≠ 0) :
    μ.map (fun u => m * u * m⁻¹) = ENNReal.ofReal |L.det|⁻¹ • μ := by
  have hSe : (S : Set (Formalism.REAL.UJ ε)) = {g | uMat g - 1 ∈ A} := Set.ext hS
  obtain ⟨-, hK, -, r₀, hr₀, hlim⟩ := GlobalTheory.T.gaugeMeasure_matrixAlgebraSubgroup_local_asymptotics n ε A d E hA hE hsp μ (hSe ▸ hμ)
  obtain ⟨h1, h2, h3⟩ := hμ
  have hp : 0 < volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) := Metric.measure_ball_pos _ _ one_pos
  have hf : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) < ⊤ := measure_ball_lt_top
  obtain ⟨r, ⟨hr1, hr2⟩, hr⟩ :=
    (((h3.eventually (lt_mem_nhds hp)).and (h3.eventually (gt_mem_nhds hf))).and self_mem_nhdsWithin).exists
  have hr : 0 < r := hr
  have hcu : Continuous (fun g : Formalism.REAL.UJ ε => uMat g) :=
    Units.continuous_val.comp continuous_subtype_val
  have hc : Continuous (fun g : Formalism.REAL.UJ ε => Formalism.REAL.hs (uMat g - 1)) := by
    unfold Formalism.REAL.hs
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    exact (((hcu.sub continuous_const).matrix_elem i j).norm).pow 2
  have hne : μ ≠ 0 := by
    rintro rfl
    simp at hr1
  have hfin : μ {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r} ≠ ⊤ := by
    intro h
    rw [h, ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top] at hr2
    exact lt_irrefl _ hr2
  obtain ⟨c, hcμ⟩ := GlobalTheory.T.unitaryJ_map_conj_eq_smul_of_normalizing n ε S μ hcl h1 h2 hK hne m hm
  have hC0 : 0 ≤ Formalism.REAL.hs (uMat m) * Formalism.REAL.hs (uMat m⁻¹) :=
    mul_nonneg (Formalism.REAL.frobenius_nonneg _) (Formalism.REAL.frobenius_nonneg _)
  have hT : Continuous (fun u : Formalism.REAL.UJ ε => m * u * m⁻¹) := by fun_prop
  have ht : Continuous (fun (g : Formalism.REAL.UJ ε) (i : Fin d) => (((uMat g - 1) * (E i)ᴴ).trace).re) :=
    continuous_pi fun i => Complex.continuous_re.comp
      (((hcu.sub continuous_const).matrix_mul continuous_const).matrix_trace)
  have key := scalar_eq_inv_det μ (fun u => m * u * m⁻¹) hT.measurable _ hc.measurable _ ht.measurable L hL c hcμ
    ?_ (Formalism.REAL.hs (uMat m) * Formalism.REAL.hs (uMat m⁻¹) + 1) (by linarith) ?_ ?_ (min r₀ (r ^ 2))
    (lt_min hr₀ (by positivity)) ?_ (fun r₁ a b => hlim r₁ a (b.trans (min_le_left _ _)))
  · rw [hcμ, ← key, ENNReal.ofReal_coe_nnreal]
  · have : ∀ᵐ g ∂μ, g ∈ (S : Set (Formalism.REAL.UJ ε)) := h1
    filter_upwards [this] with g hg
    exact GlobalTheory.T.unitaryJ_lieCoords_conj_linear n ε A d E hE hsp g m L ((hS g).1 hg) ((hS _).1 (S.inv_mem hg)) hmL
  · intro g
    have := hs_conj_le m g
    have := Formalism.REAL.frobenius_nonneg (uMat g - 1)
    linarith
  · intro g
    have h4 := hs_conj_le m⁻¹ (m * g * m⁻¹)
    have e : m⁻¹ * (m * g * m⁻¹) * m⁻¹⁻¹ = g := by group
    rw [e, inv_inv] at h4
    have := Formalism.REAL.frobenius_nonneg (uMat (m * g * m⁻¹) - 1)
    linarith
  · refine ne_top_of_le_ne_top hfin (measure_mono fun g hg => ?_)
    have hg : Formalism.REAL.hs (uMat g - 1) < min r₀ (r ^ 2) := hg
    exact Real.sqrt_le_iff.2 ⟨hr.le, (hg.trans_le (min_le_right _ _)).le⟩

end GlobalTheory.GaugeConjScale
end

