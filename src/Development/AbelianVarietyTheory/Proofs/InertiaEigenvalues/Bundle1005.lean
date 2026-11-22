import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0603
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0988
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GenDirichletHasSumIteratedDeriv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0055
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0980
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle1002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0634
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0989
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0777
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0623
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle1001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0624
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRatScalarMulIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0856
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0977
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0981
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0947
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2130
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0013
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1986
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1004
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0990
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0992
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0993
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalAwayFromTypes
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0682
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0985
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle1003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaSeriesIntegralFormsEqSpanDedekindCoefRing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0983
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0016

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergPartialLTendstoNeZeroAtOne
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology Formalism.UG GlobalTheory.RSNonvan

namespace GlobalTheory.RSNonvan

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem analyticAt_dslope' {f : ℂ → ℂ} {ξ x : ℂ} (hx : AnalyticAt ℂ f x) : AnalyticAt ℂ (dslope f ξ) x := by
  by_cases h : x = ξ
  · subst h
    obtain ⟨p, hp⟩ := hx
    exact ⟨_, hp.has_fpower_series_dslope_fslope⟩
  · have h1 : AnalyticAt ℂ (fun t => (t - ξ)⁻¹ * (f t - f ξ)) x :=
      ((analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.2 h)).mul (hx.sub analyticAt_const)
    refine h1.congr ?_
    filter_upwards [dslope_eventuallyEq_slope_of_ne f h] with t ht
    rw [ht, slope_def_module, smul_eq_mul]

theorem hasProd_of_subset {ι : Type} [DecidableEq ι] (f : ι → ℂ) {T T' : Finset ι} (h : T ⊆ T') {b : ℂ}
    (hb : HasProd (fun w : {w // w ∉ T'} => f w.1) b) :
    HasProd (fun w : {w // w ∉ T} => f w.1) ((∏ w ∈ T' \ T, f w) * b) := by
  classical
  let s : Set {w // w ∉ T} := {w | w.1 ∈ T'}
  let e1 : (↑(T' \ T) : Set ι) ≃ s :=
    { toFun := fun w => ⟨⟨w.1, (Finset.mem_sdiff.1 (Finset.mem_coe.1 w.2)).2⟩, (Finset.mem_sdiff.1 (Finset.mem_coe.1 w.2)).1⟩
      invFun := fun w => ⟨w.1.1, Finset.mem_coe.2 (Finset.mem_sdiff.2 ⟨w.2, w.1.2⟩)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e2 : {w // w ∉ T'} ≃ (sᶜ : Set {w // w ∉ T}) :=
    { toFun := fun w => ⟨⟨w.1, fun hw => w.2 (h hw)⟩, w.2⟩
      invFun := fun w => ⟨w.1.1, w.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h1 : HasProd ((fun w : {w // w ∉ T} => f w.1) ∘ ((↑) : s → {w // w ∉ T})) (∏ w ∈ T' \ T, f w) :=
    (e1.hasProd_iff).1 (Finset.hasProd (T' \ T) f)
  have h2 : HasProd ((fun w : {w // w ∉ T} => f w.1) ∘ ((↑) : (sᶜ : Set {w // w ∉ T}) → {w // w ∉ T})) b :=
    (e2.hasProd_iff).1 hb
  exact h1.mul_compl h2

theorem sat_spec {a : ℕ} {π : CG E a} {w : HeightOneSpectrum (𝓞 E)} (h : ∃ B, π.HasSat w B) :
    π.HasSat w (sat π w) := by
  unfold sat
  rw [dif_pos h]
  exact h.choose_spec

theorem prod_map_val (B : Multiset ℂˣ) : (B.map (fun α : ℂˣ => (α : ℂ))).prod = ((B.prod : ℂˣ) : ℂ) := by
  induction B using Multiset.induction_on with
  | empty => simp
  | cons b B ih => simp [ih]

theorem offDiag : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a b : ℕ) (σ : CG E a) (σ' : CG E b), 1 ≤ a → 1 ≤ b → σ.IsUnitary → σ'.IsUnitary → (⟨a, σ⟩ : Σ a, CG E a) ≠ ⟨b, σ'⟩ → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), IsGood T → UnrOutside T σ → UnrOutside T σ' → ∃ G : ℂ → ℂ, (∀ x : ℝ, 0 < x → AnalyticAt ℂ G (x : ℂ)) ∧ ∀ x : ℝ, 1 < x → HasProd (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => lfac σ σ' (x : ℂ) w.1) (G x) := by
  intro E _ _ _ a b σ σ' ha hb hσ hσ' hne T hgood hU hU'
  rcases lt_trichotomy a b with hab | rfl | hab
  · obtain ⟨F, H, hF, hH, hHpos, hFH⟩ := GlobalTheory.T.rankinSelberg_GLn_GLm_partialL_eq_div_entire E b a σ' σ ha hab hσ' hσ T hgood.2 hU' hU
    refine ⟨fun z => starRingEnd ℂ (F (starRingEnd ℂ z) / H (starRingEnd ℂ z)), ?_, ?_⟩
    · intro x hx
      have hopen : IsOpen {z : ℂ | H (starRingEnd ℂ z) ≠ 0} :=
        isOpen_ne_fun (hH.continuous.comp Complex.continuous_conj) continuous_const
      have hxmem : (x : ℂ) ∈ {z : ℂ | H (starRingEnd ℂ z) ≠ 0} := by
        simp only [Set.mem_setOf_eq, Complex.conj_ofReal]
        intro h0
        have := (hHpos x).1
        rw [h0, Complex.zero_re] at this
        exact lt_irrefl 0 this
      refine DifferentiableOn.analyticAt (fun z hz => ?_) (hopen.mem_nhds hxmem)
      have hd : DifferentiableAt ℂ (fun u => F u / H u) (starRingEnd ℂ z) := (hF _).div (hH _) hz
      have := hd.conj_conj
      rw [Complex.conj_conj] at this
      exact this.differentiableWithinAt
    · intro x hx
      have hp := (GlobalTheory.T.localRankinSelberg_logarithm_formula.2 E a b σ σ' hσ hσ' T hU hU' x hx).2
      have e := GlobalTheory.T.partial_rankinSelberg_product_conj_swap_real E b a σ' σ hσ' hσ T hU' hU x hx
      have h2 : ∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, lfac σ' σ (x : ℂ) w.1 = F x / H x := (hFH x hx).tprod_eq
      have h3 : ∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, lfac σ σ' (x : ℂ) w.1 =
          starRingEnd ℂ (F (starRingEnd ℂ (x : ℂ)) / H (starRingEnd ℂ (x : ℂ))) := by
        rw [e, h2, Complex.conj_ofReal]
      beta_reduce
      rw [← h3]
      exact hp.multipliable.hasProd
  · have hne' : σ ≠ σ' := fun h => hne (by rw [h])
    obtain ⟨F, hFa, hF1, hF⟩ := GlobalTheory.T.rankinSelberg_sameDegree_meromorphic_continuation E a σ σ' ha hσ hσ' T hgood hU hU'
    refine ⟨dslope F 1, fun x hx => analyticAt_dslope' (hFa x hx), fun x hx => ?_⟩
    have hx1 : (x : ℂ) ≠ 1 := by exact_mod_cast hx.ne'
    have e : dslope F 1 (x : ℂ) = F x / ((x : ℂ) - 1) := by
      rw [dslope_of_ne _ hx1, slope_def_module, hF1 hne', sub_zero, smul_eq_mul, inv_mul_eq_div]
    rw [e]
    exact hF x hx
  · obtain ⟨F, H, hF, hH, hHpos, hFH⟩ := GlobalTheory.T.rankinSelberg_GLn_GLm_partialL_eq_div_entire E a b σ σ' hb hab hσ hσ' T hgood.2 hU hU'
    refine ⟨fun z => F z / H z, fun x hx => (hF.analyticAt _).div (hH.analyticAt _) ?_, fun x hx => hFH x hx⟩
    intro h0
    have := (hHpos x).1
    rw [h0, Complex.zero_re] at this
    exact lt_irrefl 0 this

theorem tendsto_of_analyticAt {G : ℂ → ℂ} (hG : AnalyticAt ℂ G 1) :
    Tendsto (fun x : ℝ => G x) (𝓝[>] 1) (𝓝 (G 1)) := by
  have h := hG.continuousAt.comp (x := (1 : ℝ)) (by simpa using Complex.continuous_ofReal.continuousAt)
  have h2 := h.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ)))
  simp only [Function.comp_def, Complex.ofReal_one] at h2
  exact h2

theorem tendsto_partialL_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a b : ℕ) (σ : CG E a) (σ' : CG E b), 1 ≤ a → 1 ≤ b → σ.IsUnitary → σ'.IsUnitary → (⟨a, σ⟩ : Σ a, CG E a) ≠ ⟨b, σ'⟩ → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), UnrOutside T σ → UnrOutside T σ' → ∃ z : ℂ, z ≠ 0 ∧ Tendsto (fun x : ℝ => ∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, locL (Ideal.absNorm w.1.asIdeal) (sat σ w.1) ((sat σ' w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) (𝓝[>] 1) (𝓝 z) := by
  intro E _ _ _ a b σ σ' ha hb hσ hσ' hne T hT hT'
  classical
  obtain ⟨T', hTT', hgood⟩ := GlobalTheory.T.exists_goodRankinSelbergPlaceSet_superset_totallyComplex E T
  have hU : UnrOutside T' σ := fun w hw => hT w fun h => hw (hTT' h)
  have hU' : UnrOutside T' σ' := fun w hw => hT' w fun h => hw (hTT' h)
  obtain ⟨G, hGa, hG⟩ := offDiag E a b σ σ' ha hb hσ hσ' hne T' hgood hU hU'
  obtain ⟨G', hG'a, hG'⟩ := offDiag E b a σ' σ hb ha hσ' hσ (Ne.symm hne) T' hgood hU' hU
  obtain ⟨D, hDa, -, hD⟩ := GlobalTheory.T.rankinSelberg_sameDegree_meromorphic_continuation E a σ σ ha hσ hσ T' hgood hU hU
  obtain ⟨D', hD'a, -, hD'⟩ := GlobalTheory.T.rankinSelberg_sameDegree_meromorphic_continuation E b σ' σ' hb hσ' hσ' T' hgood hU' hU'
  have hGa1 : AnalyticAt ℂ G 1 := by simpa using hGa 1 one_pos
  have hG'a1 : AnalyticAt ℂ G' 1 := by simpa using hG'a 1 one_pos
  have hlim : Tendsto (fun x : ℝ => ∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T'}, lfac σ σ' (x : ℂ) w.1)
      (𝓝[>] 1) (𝓝 (G 1)) :=
    (tendsto_of_analyticAt hGa1).congr' (eventually_nhdsWithin_of_forall fun x hx => ((hG x hx).tprod_eq).symm)
  have hG1 : G 1 ≠ 0 := by
    intro h0
    have hG'1 : G' 1 = 0 := by
      have hlimc : Tendsto (fun x : ℝ => G' x) (𝓝[>] 1) (𝓝 (starRingEnd ℂ (G 1))) := by
        refine ((Complex.continuous_conj.tendsto _).comp (tendsto_of_analyticAt hGa1)).congr'
          (eventually_nhdsWithin_of_forall fun x hx => ?_)
        have e := GlobalTheory.T.partial_rankinSelberg_product_conj_swap_real E a b σ σ' hσ hσ' T' hU hU' x hx
        simp only [Function.comp]
        rw [← (hG x hx).tprod_eq, ← (hG' x hx).tprod_eq, e]
      rw [tendsto_nhds_unique (tendsto_of_analyticAt hG'a1) hlimc, h0, map_zero]
    let P : ℂ → ℂ := fun z => D z * D' z * dslope G 1 z * dslope G' 1 z
    have hPa : ∀ x : ℝ, 0 < x → AnalyticAt ℂ P (x : ℂ) := fun x hx =>
      (((hDa x hx).mul (hD'a x hx)).mul (analyticAt_dslope' (hGa x hx))).mul (analyticAt_dslope' (hG'a x hx))
    have hP : ∀ x : ℝ, 1 < x → ∃ g : ℂ, HasSum (fun p : {w : HeightOneSpectrum (𝓞 E) // w ∉ T'} × ℕ =>
        ((dcoef σ σ' p.1.1 p.2 : ℝ) : ℂ) * Complex.exp (-((dexp p.1.1 p.2 : ℝ) : ℂ) * (x : ℂ))) g ∧ P x = Complex.exp g := by
      intro x hx
      obtain ⟨g, hg, he⟩ := GlobalTheory.T.dirichlet_series_exponential_sum_converges E a b σ σ' hσ hσ' T' hU hU' x hx
      refine ⟨g, hg, ?_⟩
      rw [← he, (hD x hx).tprod_eq, (hD' x hx).tprod_eq, (hG x hx).tprod_eq, (hG' x hx).tprod_eq]
      have hx1 : (x : ℂ) ≠ 1 := by exact_mod_cast hx.ne'
      have hx1' : (x : ℂ) - 1 ≠ 0 := sub_ne_zero.2 hx1
      have e1 : dslope G 1 (x : ℂ) = G x / ((x : ℂ) - 1) := by
        rw [dslope_of_ne _ hx1, slope_def_module, h0, sub_zero, smul_eq_mul, inv_mul_eq_div]
      have e2 : dslope G' 1 (x : ℂ) = G' x / ((x : ℂ) - 1) := by
        rw [dslope_of_ne _ hx1, slope_def_module, hG'1, sub_zero, smul_eq_mul, inv_mul_eq_div]
      simp only [P, e1, e2]
      field_simp
    have hN : (0 : ℝ) < 1 / ((a + b : ℕ) : ℝ) := by
      have : (0 : ℝ) < ((a + b : ℕ) : ℝ) := by exact_mod_cast (show 0 < a + b by omega)
      positivity
    obtain ⟨g, hg, -⟩ := GlobalTheory.landau_exp_hasSum_of_analyticAt ({w : HeightOneSpectrum (𝓞 E) // w ∉ T'} × ℕ)
      (fun p => dcoef σ σ' p.1.1 p.2) (fun p => dexp p.1.1 p.2) 0 1 P (fun p => dcoef_nonneg _ _ _ _)
      (fun p => dexp_nonneg _ _) one_pos hPa hP _ hN
    set y : ℝ := 1 / ((a + b : ℕ) : ℝ) with hy
    have hs : Summable (fun p : {w : HeightOneSpectrum (𝓞 E) // w ∉ T'} × ℕ =>
        dcoef σ σ' p.1.1 p.2 * Real.exp (-(dexp p.1.1 p.2) * y)) := by
      rw [← Complex.summable_ofReal]
      refine hg.summable.congr fun p => ?_
      push_cast
      rfl
    refine GlobalTheory.PowerSumDiv.not_summable_psum_sq (a + b) (by omega) T'
      (fun w => (sat σ w).map (fun α : ℂˣ => (α : ℂ)) + (sat σ' w).map (fun α : ℂˣ => (α : ℂ))) ?_ ?_ (le_of_eq hy) ?_
    · intro w hw
      rw [Multiset.card_add, Multiset.card_map, Multiset.card_map, (sat_spec (hU w hw)).card, (sat_spec (hU' w hw)).card]
    · intro w hw
      rw [Multiset.prod_add, norm_mul, prod_map_val, prod_map_val, GlobalTheory.T.norm_prod_satakeParameters_unitary_eq_one E a σ w _ hσ (sat_spec (hU w hw)),
        GlobalTheory.T.norm_prod_satakeParameters_unitary_eq_one E b σ' w _ hσ' (sat_spec (hU' w hw)), one_mul]
    · refine hs.congr fun p => ?_
      have hq : (0 : ℝ) < (Ideal.absNorm p.1.1.asIdeal : ℝ) := by
        have := NumberField.HeightOneSpectrum.one_lt_absNorm p.1.1
        have : (0 : ℝ) < ((Ideal.absNorm p.1.1.asIdeal : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < Ideal.absNorm p.1.1.asIdeal)
        exact this
      simp only [dcoef, dexp]
      rw [Real.rpow_def_of_pos hq]
      have : -(((p.2 : ℝ) + 1) * Real.log (Ideal.absNorm p.1.1.asIdeal : ℝ)) * y =
          Real.log (Ideal.absNorm p.1.1.asIdeal : ℝ) * -(((p.2 : ℝ) + 1) * y) := by ring
      rw [this]
      ring
  have hfac : ∀ w ∈ T' \ T, Tendsto (fun x : ℝ => lfac σ σ' (x : ℂ) w) (𝓝[>] 1) (𝓝 (lfac σ σ' 1 w)) ∧
      lfac σ σ' 1 w ≠ 0 := by
    intro w hw
    have hw2 := (Finset.mem_sdiff.1 hw).2
    exact GlobalTheory.T.localRankinSelbergFactor_conj_tendsto_one_ne_zero (Ideal.absNorm w.asIdeal) (sat σ w) (sat σ' w) (NumberField.HeightOneSpectrum.one_lt_absNorm w)
      (GlobalTheory.T.satakeParameter_normSq_lt_absNorm_unitaryCusp E a σ ha hσ T hT w hw2) (GlobalTheory.T.satakeParameter_normSq_lt_absNorm_unitaryCusp E b σ' hb hσ' T hT' w hw2)
  refine ⟨(∏ w ∈ T' \ T, lfac σ σ' 1 w) * G 1,
    mul_ne_zero (Finset.prod_ne_zero_iff.2 fun w hw => (hfac w hw).2) hG1, ?_⟩
  have hprodlim : Tendsto (fun x : ℝ => ∏ w ∈ T' \ T, lfac σ σ' (x : ℂ) w) (𝓝[>] 1)
      (𝓝 (∏ w ∈ T' \ T, lfac σ σ' 1 w)) := tendsto_finset_prod _ fun w hw => (hfac w hw).1
  refine (hprodlim.mul hlim).congr' (eventually_nhdsWithin_of_forall fun x hx => ?_)
  have hp := (GlobalTheory.T.localRankinSelberg_logarithm_formula.2 E a b σ σ' hσ hσ' T' hU hU' x hx).2
  have h1 := hasProd_of_subset (fun w => lfac σ σ' (x : ℂ) w) hTT' hp.multipliable.hasProd
  exact h1.tprod_eq.symm

end GlobalTheory.RSNonvan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalPhaseThetaSeriesExpandsCuspFormsSmallFie
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.ConjTwist
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.SeriesTie.RatExpand

variable {D : D7}

theorem castDict_sum_smul {V W : HSp D} (e : V = W) {m : ℕ} (a : Fin m → ℂ) (ψ : Fin m → GA D V → ℂ) (g : GA D W) :
    castDict e (∑ i, a i • ψ i) g = ∑ i, a i * castDict e (ψ i) g := by
  subst e
  simp [castDict, Finset.sum_apply]

theorem castDict_phiJ {T : CoreJ D} {j : ℕ} {W : HSp D} {σ : T.Q.c.F →+* ℂ} (hσ : σ = T.σ₀) (h1 : T.V j σ = W)
    (h2 : T.V j T.σ₀ = W) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) (g : GA D W) :
    (h1 ▸ T.phiJ j σ a f : GA D W → ℂ) g = castDict h2 (T.phiJ j T.σ₀ a f) g := by
  subst hσ
  subst h1
  rfl

theorem mem_ratVec {G : Type} [Group G] [Fintype G] {Pl0 T1 : Type} {A : FamIn D.what₂.LL G Pl0 T1 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (j : Fin D.R.m)
    (c0 : VsV D j D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV j).W) (v : VsV D j D.what₂.LL)
    (hv : ∀ m, ∃ q : ℚ, MvPolynomial.coeff m (v : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank) = (q : D.what₂.LL))
    (k : Subfield ℂ) : c0 v ∈ GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.ratVec R j c0 k := by
  refine Submodule.subset_span ⟨v, fun m => ?_, rfl⟩
  obtain ⟨q, hq⟩ := hv m
  rw [hq, map_ratCast]
  exact SubfieldClass.ratCast_mem k q

theorem expands_of_isRatPhase : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m), GlobalTheory.NT.RayField → ∀ (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T.Q.c.F) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (F : Face D A3.A) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (O : ∀ j, OMDat T.toCore Rl.toRealDat j Unit (fun _ => A3.A.μ0)), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → LawsJ T → GlobalTheory.Hk3.Core Rl.toRealDat F → Nonempty (FWTie T Rl.toRealDat κ v₀) → TieIn T Rl.toRealDat κ v₀ → IoExt Rl.toRealDat → QGuard Rl.toRealDat → IsGalois ℚ D.LL0 → Formalism.L2.Host.ValLL0 D Rl.C → RayIn D (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') (embLL0 D).fieldRange → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange) → ∀ (j : Fin D.R.m) (hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j), OMPins T Rl.toRealDat κ v₀ O j → GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T Rl.toRealDat j T.σ₀ hV → ∀ gramR c0R c0L, Bridge.FamTie Rl.B Rl.pl (Rl.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) Rl.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ) (fun j τ => Bridge.lamLdef (Vc D j).rank ((j : ℕ) + 1) τ) gramR c0R c0L → CoefficientBaseChange Rl.toRealDat j (O j).jL (inC (O j).c') (c0L j) (O j).c0' → ∀ (u : ∀ ρ, lowT (Rl.MW j (sg0 D A3.A)) ρ), (∀ ρ, (u ρ : (Rl.MW j (sg0 D A3.A)).sm ρ) = v₀ j _ ρ) → ∀ (ph₀ : ℂ), GlobalTheory.SeriesTie.IsRatPhase T Rl.toRealDat j hV (κ j) u (c0L j) ph₀ → ∀ (c : VsV D j ℂ →ₗ[ℂ] (Rl.cV j).W), ExtC Rl.toRealDat j (inC (O j).c') (O j).c0' c → ∀ (v : VsV D j D.what₂.LL), (∀ m, ∃ q : ℚ, MvPolynomial.coeff m (v : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank) = (q : D.what₂.LL)) → ∀ (x : VsV D j ℂ), (x : Pol ℂ D.what₂.Tau (Vc D j).rank) = MvPolynomial.map D.what₂.embLL (v : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank) → ∀ h ∈ GfC (Vc D j), ∃ (n : ℕ) (e : Fin n → ℂ) (f : Fin n → T.toCore.cuspA ((j : ℕ) + 1) (wtA (κ j)) (κ j).n), Expands (O j) (κ j) (fun g => ph₀ * ser Rl.toRealDat j A3.A.μ0 (Rl.vP j A3.A.μ0) u h (c x) g) e f ∧ ∀ k, e k ∈ (embLL0 D).fieldRange := by
  intro D Γ _ _ Pl0 I0 T0 A3 hRF T _ Rl cG S YS F κ v₀ O hnV hT hcore hfw hti hio hQ hgal hval hray hroots j hV hpins hfp
    gramR c0R c0L hft hbc u hu ph₀ hph c hc v hv x hx h hh
  have hInR : Formalism.L2.Pj.InR D ((j : ℕ) + 1) := ⟨by omega, by have := j.2; omega⟩
  have hlast : (κ j).LastPos := fun τ i hi => by
    rw [(hti.kap j τ).1 i]
    exact GlobalTheory.LiftWeight.kapTop_lastPos D j τ i hi
  have hn : 8 * D.R.f * D.R.r + 4 ≤ (κ j).n := by
    rw [(hti.kap j (D.eTau.symm 1)).2.2]
    exact hnV

  obtain ⟨C, hpd, hfr, hgood⟩ := GlobalTheory.T.exists_goodCover_levelOne_over_smallField D Γ Pl0 I0 T0 A3 hRF T Rl cG S YS F κ v₀ O hT hcore hfw hti hio hQ hgal hval hray hroots j hV
    hpins hfp (κ j).n
  have hser := hph C hgood hfr.ge
  have hdat : GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.IsLevDatum Rl.toRealDat.ψ (Vc D j) (Wc D j) (Rl.toRealDat.ΛV j) (Rl.toRealDat.ΛW j)
      (T.Q.l.M * C.d.pd) C.σ₂.fieldRange (Rl.toRealDat.vacP j) (Rl.toRealDat.vP j A3.A.μ0) := by
    rw [hpd, mul_one, hfr]
    exact GlobalTheory.T.isLevelDatum_referenceTuple_smallField D Γ Pl0 I0 T0 A3 hRF T Rl cG S YS F κ v₀ O hT hcore hfw hti hio hQ hgal hval hray hroots j hV hpins hfp

  have hcx : c x = c0L j v := by
    obtain ⟨v', hv', he⟩ := hbc v
    refine (hc v' x ?_).trans he
    rw [hx, hv', MvPolynomial.map_map, hpins.2.lift.field]
  have hw : c x ∈ GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.ratVec Rl.toRealDat j (c0L j) C.σ₂.fieldRange := by
    rw [hcx]
    exact mem_ratVec Rl.toRealDat j (c0L j) v hv _
  obtain ⟨φ', hφ'm, hφ'e⟩ := (hser h hh _ hdat (c x) hw).1

  have hspan : Formalism.L2.Pj.holSub0 (T.U ((j : ℕ) + 1) T.σ₀).X (laU (T.U ((j : ℕ) + 1) T.σ₀) (wtA (κ j)) (κ j).n) ≤
      Submodule.span ℂ (rdU (T.U ((j : ℕ) + 1) T.σ₀) '' {f | f ∈ sec (T.Q.Xo ((j : ℕ) + 1)) T.Q.c (wtA (κ j)) (κ j).n ∧
        rdU (T.U ((j : ℕ) + 1) T.σ₀) f ∈ Formalism.L2.Pj.holSub0 (T.U ((j : ℕ) + 1) T.σ₀).X
          (laU (T.U ((j : ℕ) + 1) T.σ₀) (wtA (κ j)) (κ j).n)}) := by
    refine (GlobalTheory.OntoCore.holSub0_le_span_cuspA D T hT _ hInR (κ j) hlast hn T.σ₀ T.toCore.good_σ₀).trans
      (Submodule.span_mono (Set.image_mono fun f hf => ⟨Formalism.L2.Pj.cusp_le_sec _ _ _ _ _ hf, ?_, ?_⟩))
    · exact ((Formalism.L2.Pj.mem_cusp _ _ _ _ _ f).1 hf).2 T.σ₀ T.toCore.good_σ₀
    · exact Formalism.L2.Pj.rdU_mem_offZero _ _
  have hmu := GlobalTheory.T.dictionaryCharacter_right_invariant_coreLevel D Γ Pl0 I0 T0 A3 hRF T Rl cG S YS F κ v₀ O hT hcore hfw hti hio hQ hgal hval hray hroots j hV hpins hfp
  have hinv := GlobalTheory.T.liftDatum_thetaSeries_right_invariant_coreLevel D Γ Pl0 I0 T0 A3 hRF T Rl cG S YS F κ v₀ O hT hcore hfw hti hio hQ hgal hval hray hroots j hV hpins hfp
    u h hh (c x) ph₀ φ' hφ'e
  obtain ⟨m, xs, ψ, hψ, hφeq⟩ := GlobalTheory.T.holomorphic_sections_span_restriction D T hT _ hInR T.σ₀ T.toCore.good_σ₀ C hgood.1 (wtA (κ j)) (κ j).n
    (dom_wtA _) (hgood.2.1 _ (dom_wtA _)) hspan hmu φ' hφ'm hinv
  have hψ' : ∀ k, ∃ f, (f ∈ sec (T.Q.Xo ((j : ℕ) + 1)) T.Q.c (wtA (κ j)) (κ j).n ∧
      rdU (T.U ((j : ℕ) + 1) T.σ₀) f ∈ Formalism.L2.Pj.holSub0 (T.U ((j : ℕ) + 1) T.σ₀).X
        (laU (T.U ((j : ℕ) + 1) T.σ₀) (wtA (κ j)) (κ j).n)) ∧ T.phiJ ((j : ℕ) + 1) T.σ₀ (wtA (κ j)) f = ψ k := hψ
  choose fs hfs using hψ'
  let f' : Fin m → T.toCore.cuspA ((j : ℕ) + 1) (wtA (κ j)) (κ j).n := fun k =>
    ⟨fs k, GlobalTheory.T.mem_cuspForms_of_reading_bounded_cuspidal_holomorphic D T hT _ hInR (κ j) hlast hn (fs k) (hfs k).1.1 (hfs k).1.2⟩
  refine ⟨m, fun k => C.σ₂ (xs k), f', fun g => ?_, fun k => by rw [← hfr]; exact ⟨xs k, rfl⟩⟩
  show ph₀ * ser Rl.toRealDat j A3.A.μ0 (Rl.vP j A3.A.μ0) u h (c x) g = _
  rw [show ph₀ * ser Rl.toRealDat j A3.A.μ0 (Rl.vP j A3.A.μ0) u h (c x) g = castDict hV φ' g from
    (congrFun hφ'e g).symm, hφeq, castDict_sum_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  rw [← (hfs k).2]
  exact ((Formalism.IndefR.FWT.phi_cE T Rl.toRealDat O j (wtA (κ j)) (fs k) g).trans
    (castDict_phiJ (sOv_eq _ _ _) (O j).hV hV _ _ g)).symm

end GlobalTheory.SeriesTie.RatExpand
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealFockThetaLiftVanishingOfGeneratingVectorsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realFockThetaLift_vanishing_of_generating_vectors : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (y : (R.HV i t).H), (∀ (x : LowT (R.MW i (sg0 D A))) (w : (R.cV i).W) (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)), downInt R i t y (R.ptP i t (R.ioP i x w)) l g = 0) → ∀ (P : PolF D (Wc D i).rank (Vc D i).rank) (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)), downInt R i t y (R.ptP i t P) l g = 0 := by
  first | exact @GlobalTheory.GenRealFock.gen | exact GlobalTheory.GenRealFock.gen | (intros; apply GlobalTheory.GenRealFock.gen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalAwayFromTypesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spherical_away_from_types : PrN → OverRows fun _ _ _ _ w Z _ _ z _ Y => ∀ (σ : (w.st Z).toD7.what₂.FT) (s : ReciprocityTheory.Aut.SplitPlace (w.st Z).toD7.host.E), (∀ k : Fin 2, s.w ∉ placesOver (w.st Z).toD7.host.E ((w.st Z).toD7.host.g k)) → ∃ τ, IsLocS (repOf Y σ).S s τ ∧ GlobalTheory.SmGL.IsSpherical τ.ρ := by
  first | exact @GlobalTheory.RowSphOff.rowSph_overRows | exact GlobalTheory.RowSphOff.rowSph_overRows | (intros; apply GlobalTheory.RowSphOff.rowSph_overRows <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalInertiaOfIsotypicStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spherical_inertia_of_isotypic : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, GlobalTheory.LiftRef.AtRows hL fun D _ _ _ a M => ∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (S : Submodule ℂ (Formalism.AUTREP.GAf D.host.E D.R.nV → (M D.what₂.mu0 j h1 h2).wt.W)) (hS : NG.IsIrrRep (M D.what₂.mu0 j h1 h2).wt.ρ S), (NG.isoTyp (M D.what₂.mu0 j h1 h2).wt.ρ S).comap (M D.what₂.mu0 j h1 h2).real ≠ ⊥ → SphericalInertData.SphInert D.nd D.naut D.nbc j (a.A.cls j h1 h2 (GlobalTheory.LiftRef.autOf (M D.what₂.mu0 j h1 h2) S hS)) := by
  first | exact @GlobalTheory.SphInertRef.sph_inert | exact GlobalTheory.SphInertRef.sph_inert | (intros; apply GlobalTheory.SphInertRef.sph_inert <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaIsotypicInjectiveStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_isotypic_injective : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, GlobalTheory.LiftRef.AtRows hL fun D _ _ _ _ _ => ∀ (j : ℕ) (_ : 1 ≤ j) (_ : j ≤ D.R.m) (σ : D.what₂.FT), ∀ y ∈ D.what₂.isot j σ, D.what₂.thetaT D.what₂.mu0 j y = 0 → y = 0 := by
  first | exact @GlobalTheory.LiftRef.UpInjRows.main | exact GlobalTheory.LiftRef.UpInjRows.main | (intros; apply GlobalTheory.LiftRef.UpInjRows.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaSeriesIntegralFormsEqSpanDedekindCoefRingStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSeriesIntegralForms_eq_span_dedekindCoefRing : ∀ (D : D7) (S T : HSp D) (B : Base S T), B.Good → ∀ ψ : Twist D Circle, ψ.Good → B.admitted ψ.Q → ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K)) (R : Type) [CommRing R] [IsDedekindDomain R] (φ : R →+* ℂ), Function.Injective φ → IsCoefRing σ emb φ.range →
  (∀ k : B.levJ ψ, ((B.levLam ψ k : ℂˣ) : ℂ) ∈ φ.range) → ∀ O : Subring ℂ, φ.range ≤ O →
  B.mtLat σ emb O ψ = Submodule.span O (B.mtLat σ emb φ.range ψ : Set (Bridge.Gf S → PolF D T.rank S.rank)) := by
  first | exact @GlobalTheory.FormsBaseChange.mtLat_eq_span | exact GlobalTheory.FormsBaseChange.mtLat_eq_span | (intros; apply GlobalTheory.FormsBaseChange.mtLat_eq_span <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedDescentIntegralFormsTowerCoverStatement
section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_descent_integral_forms_tower_cover : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), VStd D i → ∀ hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i T.σ₀ hV → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.DescIntAt T i (κ i) := by
  first | exact @GlobalTheory.DescIntRoad.descIntAt_of_laws | exact GlobalTheory.DescIntRoad.descIntAt_of_laws | (intros; apply GlobalTheory.DescIntRoad.descIntAt_of_laws <;> assumption)
end

