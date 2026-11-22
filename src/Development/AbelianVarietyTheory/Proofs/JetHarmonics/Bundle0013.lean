import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.WeierstrassCurvePointOfLatticeAddOfGeneric
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsMulEqPolynomialWeierstrassP
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.EqZeroOfMulEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsAnalyticOfTendsto
section
open Filter PeriodPair
open scoped Topology

noncomputable section

namespace GlobalTheory.EllipticPoles

variable (L : PeriodPair)

lemma tendsto_neg_ne (a : ℂ) : Tendsto (fun z : ℂ ↦ -z) (𝓝[≠] a) (𝓝[≠] (-a)) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    (continuous_neg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (by filter_upwards [self_mem_nhdsWithin] with z hz using by simpa using hz)

lemma tendsto_add_ne (a l : ℂ) : Tendsto (fun z : ℂ ↦ z + l) (𝓝[≠] a) (𝓝[≠] (a + l)) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    ((continuous_add_const l).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (by filter_upwards [self_mem_nhdsWithin] with z hz using by simpa using hz)

lemma tendsto_two_ne (a : ℂ) : Tendsto (fun z : ℂ ↦ z + z) (𝓝[≠] a) (𝓝[≠] (a + a)) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    ((by fun_prop : Continuous fun z : ℂ ↦ z + z).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (by
      filter_upwards [self_mem_nhdsWithin] with z hz h
      apply hz
      simp only [Set.mem_singleton_iff] at h ⊢
      linear_combination h / 2)

lemma exists_analytic_of_tendsto {f : ℂ → ℂ} {a c : ℂ} (hf : MeromorphicAt f a)
    (h : Tendsto f (𝓝[≠] a) (𝓝 c)) : ∃ g, AnalyticAt ℂ g a ∧ f =ᶠ[𝓝[≠] a] g :=
  hf.meromorphicOrderAt_nonneg_iff.1 ((tendsto_nhds_iff_meromorphicOrderAt_nonneg hf).1 ⟨c, h⟩)

lemma even_case {g : ℂ → ℂ} (hg : Meromorphic g)
    (hd : ∀ a ∉ L.lattice, ∃ c, Tendsto g (𝓝[≠] a) (𝓝 c))
    (hp : ∀ z, ∀ l ∈ L.lattice, g (z + l) = g z) (hev : ∀ z, g (-z) = g z) :
    ∃ A : Polynomial ℂ, ∀ z₀ : ℂ, ∀ᶠ z in 𝓝[≠] z₀, g z = A.eval (℘[L] z) := by
  classical
  let G : ℂ → ℂ := fun z ↦ if z ∈ L.lattice then 0 else limUnder (𝓝[≠] z) g
  have hG : ∀ a ∉ L.lattice, ∀ c, Tendsto g (𝓝[≠] a) (𝓝 c) → G a = c := fun a ha c h ↦ by
    simp only [G, if_neg ha]
    exact h.limUnder_eq
  have hGg : ∀ z₀, G =ᶠ[𝓝[≠] z₀] g := fun z₀ ↦ by
    filter_upwards [(hg z₀).eventually_analyticAt, eventually_ne_notMem_periodLattice L z₀]
      with z h1 h2
    exact hG z h2 _ (h1.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  obtain ⟨A, hA⟩ := exists_eq_polynomial_weierstrassP L (g := G) ((hg 0).congr (hGg 0).symm)
    (fun a ha ↦ by
      obtain ⟨c, hc⟩ := hd a ha
      obtain ⟨h, hh, hgh⟩ := exists_analytic_of_tendsto (hg a) hc
      refine hh.differentiableAt.congr_of_eventuallyEq ?_
      rw [← nhdsNE_sup_pure, EventuallyEq, eventually_sup]
      refine ⟨(hGg a).trans hgh, ?_⟩
      simp only [eventually_pure]
      exact hG a ha _ ((hh.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' hgh.symm))
    (fun z l hl ↦ by
      by_cases hz : z ∈ L.lattice
      · simp [G, hz, add_mem hz hl]
      · have hz' : z + l ∉ L.lattice := by rwa [L.lattice.add_mem_iff_left hl]
        obtain ⟨c, hc⟩ := hd _ hz'
        rw [hG _ hz' c hc, hG z hz c
          ((hc.comp (tendsto_add_ne z l)).congr fun w ↦ hp w l hl)])
    (fun z ↦ by
      by_cases hz : z ∈ L.lattice
      · simp [G, hz]
      · have hz' : -z ∉ L.lattice := by simpa using hz
        obtain ⟨c, hc⟩ := hd _ hz'
        rw [hG _ hz' c hc, hG z hz c ((hc.comp (tendsto_neg_ne z)).congr fun w ↦ hev w)])
  refine ⟨A, fun z₀ ↦ ?_⟩
  filter_upwards [hGg z₀, eventually_ne_notMem_periodLattice L z₀] with z h1 h2
  rw [← h1, hA z h2]

lemma no_pole_case {g : ℂ → ℂ} (hg : Meromorphic g)
    (hd : ∀ a ∉ L.lattice, ∃ c, Tendsto g (𝓝[≠] a) (𝓝 c))
    (hp : ∀ z, ∀ l ∈ L.lattice, g (z + l) = g z) :
    ∃ A B : Polynomial ℂ, ∀ z₀ : ℂ, ∀ᶠ z in 𝓝[≠] z₀,
      g z = A.eval (℘[L] z) + B.eval (℘[L] z) * ℘'[L] z := by
  have hgn : Meromorphic fun z ↦ g (-z) := fun a ↦
    MeromorphicAt.comp_analyticAt (f := g) (g := fun z ↦ -z) (hg (-a)) (by fun_prop)
  have hdn : ∀ a ∉ L.lattice, ∃ c, Tendsto (fun z ↦ g (-z)) (𝓝[≠] a) (𝓝 c) := fun a ha ↦ by
    obtain ⟨c, hc⟩ := hd (-a) (by simpa using ha)
    exact ⟨c, hc.comp (tendsto_neg_ne a)⟩
  have hpn : ∀ z, ∀ l ∈ L.lattice, g (-(z + l)) = g (-z) := fun z l hl ↦ by
    rw [neg_add, hp _ _ (neg_mem hl)]
  obtain ⟨A, hA⟩ := even_case L (g := fun z ↦ (g z + g (-z)) / 2)
    (fun a ↦ by have := hg a; have := hgn a; fun_prop)
    (fun a ha ↦ by
      obtain ⟨c, hc⟩ := hd a ha
      obtain ⟨c', hc'⟩ := hdn a ha
      exact ⟨_, (hc.add hc').div_const 2⟩)
    (fun z l hl ↦ by simp only [hp z l hl, hpn z l hl])
    (fun z ↦ by simp only [neg_neg, add_comm])
  let o : ℂ → ℂ := fun z ↦ (g z - g (-z)) / 2
  have ho : Meromorphic o := fun a ↦ by have := hg a; have := hgn a; fun_prop
  have hop : ∀ z, ∀ l ∈ L.lattice, o (z + l) = o z := fun z l hl ↦ by
    simp only [o, hp z l hl, hpn z l hl]
  have hon : ∀ z, o (-z) = -o z := fun z ↦ by simp only [o, neg_neg]; ring
  obtain ⟨B, hB⟩ := even_case L (g := fun z ↦ o z / ℘'[L] z)
    (fun a ↦ (ho a).div (L.meromorphic_derivWeierstrassP a))
    (fun a ha ↦ by
      obtain ⟨c, hc⟩ := hd a ha
      obtain ⟨c', hc'⟩ := hdn a ha
      have h1 : Tendsto o (𝓝[≠] a) (𝓝 ((c - c') / 2)) := (hc.sub hc').div_const 2
      have hP := hasDerivAt_derivWeierstrassP L ha
      by_cases h0 : ℘'[L] a = 0
      · have h2 := (derivWeierstrassP_eq_zero_iff L ha).1 h0
        obtain ⟨h, hh, hoh⟩ := exists_analytic_of_tendsto (ho a) h1
        have h3 : Tendsto o (𝓝[≠] a) (𝓝 (h a)) :=
          (hh.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' hoh.symm
        have h4 : Tendsto (fun z : ℂ ↦ -z + (a + a)) (𝓝[≠] a) (𝓝[≠] a) := by
          have := (tendsto_add_ne (-a) (a + a)).comp (tendsto_neg_ne a)
          simpa [Function.comp_def] using this
        have h5 : Tendsto o (𝓝[≠] a) (𝓝 (-h a)) :=
          (h3.comp h4).neg.congr fun z ↦ by simp [hop _ _ h2, hon]
        have h6 : h a = 0 := CharZero.eq_neg_self_iff.1 (tendsto_nhds_unique h3 h5)
        refine ⟨_, ((hasDerivAt_iff_tendsto_slope.1 hh.differentiableAt.hasDerivAt).div
          (hasDerivAt_iff_tendsto_slope.1 hP) (weierstrassP_second_ne_zero L ha h0)).congr' ?_⟩
        filter_upwards [hoh, self_mem_nhdsWithin] with z hz hza
        have : z - a ≠ 0 := sub_ne_zero.2 hza
        simp only [Pi.div_apply, slope_def_field, h6, h0, sub_zero, hz]
        rw [div_div_div_cancel_right₀ this]
      · exact ⟨_, h1.div (hP.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) h0⟩)
    (fun z l hl ↦ by simp only [hop z l hl, L.derivWeierstrassP_add_coe z ⟨l, hl⟩])
    (fun z ↦ by simp only [hon, derivWeierstrassP_neg, neg_div_neg_eq])
  refine ⟨A, B, fun z₀ ↦ ?_⟩
  filter_upwards [hA z₀, hB z₀,
    (tendsto_two_ne z₀).eventually (eventually_ne_notMem_periodLattice L (z₀ + z₀))]
    with z h1 h2 h3
  have h4 : ℘'[L] z ≠ 0 := fun h ↦
    h3 ((derivWeierstrassP_eq_zero_iff L fun hz ↦ h3 (add_mem hz hz)).1 h)
  rw [← h1, ← h2, div_mul_cancel₀ _ h4]
  simp only [o]
  ring

theorem exists_mul_prod_eq (L : PeriodPair) (φ : ℂ → ℂ) (hφ : GlobalTheory.MomOne.Ell L φ) :
    ∃ (m : ℕ) (P : Fin m → ℂ) (A B : Polynomial ℂ),
      (∀ i, P i ∉ L.lattice ∧ meromorphicOrderAt φ (P i) < 0) ∧
      ∀ z₀ : ℂ, ∀ᶠ z in 𝓝[≠] z₀, φ z * ∏ i, (L.weierstrassP z - L.weierstrassP (P i)) =
        A.eval (L.weierstrassP z) + B.eval (L.weierstrassP z) * L.derivWeierstrassP z := by
  classical
  obtain ⟨hf, hp⟩ := hφ
  have hK := (ZSpan.fundamentalDomain_isBounded L.basis).isCompact_closure
  set K := closure (ZSpan.fundamentalDomain L.basis)
  have hS := hK.finite_sdiff_of_mem_codiscreteWithin
    (hf.meromorphicOn (s := K)).analyticAt_mem_codiscreteWithin
  let S : Finset ℂ := hS.toFinset.filter fun a ↦ a ∉ L.lattice ∧ meromorphicOrderAt φ a < 0
  choose n hn using id hf
  let e := Fintype.equivFin (Σ a : S, Fin (n a))
  let D : ℂ → ℂ := fun z ↦ ∏ a ∈ S, (℘[L] z - ℘[L] a) ^ n a
  have hD : ∀ z, ∏ i, (℘[L] z - ℘[L] (e.symm i).1) = D z := fun z ↦ by
    rw [e.symm.prod_comp (fun x : (Σ a : S, Fin (n a)) ↦ ℘[L] z - ℘[L] x.1), Fintype.prod_sigma]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact Finset.prod_coe_sort S fun a ↦ (℘[L] z - ℘[L] a) ^ n a
  have hK' : ∀ a ∈ K, a ∉ L.lattice → ∃ c, Tendsto (fun z ↦ φ z * D z) (𝓝[≠] a) (𝓝 c) := by
    intro a haK ha
    have hP := L.analyticOnNhd_weierstrassP a ha
    have hP' := hP.continuousAt
    by_cases haS : a ∈ S
    · obtain ⟨u, hu, hu'⟩ := (natCast_le_analyticOrderAt (f := fun z ↦ ℘[L] z - ℘[L] a)
        (z₀ := a) (by fun_prop) (n := 1)).mp
        ((natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (by fun_prop)).mpr fun i hi ↦ by
          interval_cases i; simp)
      have h1 := (hn a).continuousAt
      have h2 := hu.continuousAt
      have h3 : ContinuousAt (fun z ↦ ((z - a) ^ n a • φ z) * u z ^ n a *
          ∏ b ∈ S.erase a, (℘[L] z - ℘[L] b) ^ n b) a := by fun_prop
      refine ⟨_, (h3.tendsto.congr' ?_).mono_left nhdsWithin_le_nhds⟩
      filter_upwards [hu'] with z hz
      simp only [D]
      rw [← Finset.mul_prod_erase _ _ haS, hz]
      simp only [smul_eq_mul, mul_pow]
      ring
    · have h1 : 0 ≤ meromorphicOrderAt φ a := by
        by_contra h
        refine haS (Finset.mem_filter.2 ⟨?_, ha, not_le.1 h⟩)
        simp only [Set.Finite.mem_toFinset]
        exact ⟨haK, fun h' ↦ h (AnalyticAt.meromorphicOrderAt_nonneg h')⟩
      obtain ⟨c, hc⟩ := (tendsto_nhds_iff_meromorphicOrderAt_nonneg (hf a)).2 h1
      have h2 : ContinuousAt D a := by simp only [D]; fun_prop
      exact ⟨_, hc.mul (h2.tendsto.mono_left nhdsWithin_le_nhds)⟩
  have hper : ∀ z, ∀ l ∈ L.lattice, φ (z + l) * D (z + l) = φ z * D z := fun z l hl ↦ by
    simp only [D, hp l hl z, L.weierstrassP_add_coe z ⟨l, hl⟩]
  obtain ⟨A, B, hAB⟩ := no_pole_case L (g := fun z ↦ φ z * D z)
    (fun a ↦ by
      have h1 := hf a
      have h2 := L.meromorphic_weierstrassP a
      simp only [D]
      fun_prop)
    (fun z hz ↦ by
      have hl : -(ZSpan.floor L.basis z : ℂ) ∈ L.lattice := by
        rw [L.lattice_eq_span_range_basis]; exact neg_mem (ZSpan.floor L.basis z).2
      obtain ⟨c, hc⟩ := hK' (z + -ZSpan.floor L.basis z)
        (by rw [← sub_eq_add_neg]; exact subset_closure (ZSpan.fract_mem_fundamentalDomain L.basis z))
        (by rwa [L.lattice.add_mem_iff_left hl])
      exact ⟨c, (hc.comp (tendsto_add_ne z _)).congr fun w ↦ hper w _ hl⟩)
    hper
  refine ⟨_, fun i ↦ (e.symm i).1, A, B, fun i ↦ (Finset.mem_filter.1 (e.symm i).1.2).2, fun z₀ ↦ ?_⟩
  simpa only [hD] using hAB z₀

end GlobalTheory.EllipticPoles
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsEqConstMulOfForallExistsNormEq
section
namespace GlobalTheory

open Metric Set Filter Topology

theorem exists_eventually_eq_mul_of_norm_eq {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {O : Set V} (hO : IsOpen O) {P Q : V → ℂ} (hP : DifferentiableOn ℂ P O) (hQ : DifferentiableOn ℂ Q O)
    {x : V} (hx : x ∈ O) (h : ∀ᶠ y in 𝓝 x, ‖P y‖ = ‖Q y‖) :
    ∃ z ∈ O, ∃ c : ℂ, ∀ᶠ y in 𝓝 z, P y = c * Q y := by
  by_cases h0 : ∀ᶠ y in 𝓝 x, Q y = 0
  · refine ⟨x, hx, 0, ?_⟩
    filter_upwards [h, h0] with y hy hy0
    rw [hy0, norm_zero, norm_eq_zero] at hy
    simp [hy]
  · have hfr : ∃ᶠ y in 𝓝 x, Q y ≠ 0 := not_eventually.mp h0
    obtain ⟨z, hz0, hzO, hz⟩ :=
      (hfr.and_eventually (Filter.Eventually.and (hO.mem_nhds hx) h.eventually_nhds)).exists
    have hzO' : z ∈ O := hzO
    have hne : ∀ᶠ y in 𝓝 z, Q y ≠ 0 :=
      (hQ.continuousOn.continuousAt (hO.mem_nhds hzO')).eventually_ne hz0
    have hall : ∀ᶠ y in 𝓝 z, y ∈ O ∧ Q y ≠ 0 ∧ ‖P y‖ = ‖Q y‖ :=
      Filter.Eventually.and (hO.mem_nhds hzO') (hne.and hz)
    obtain ⟨ε, hε, hb⟩ := Metric.eventually_nhds_iff_ball.mp hall
    have hsub : ball z ε ⊆ O := fun y hy => (hb y hy).1
    have hd : DifferentiableOn ℂ (fun y => P y / Q y) (ball z ε) := by
      simp only [div_eq_mul_inv]
      exact (hP.mono hsub).mul ((hQ.mono hsub).inv (fun y hy => (hb y hy).2.1))
    have hn : ∀ y ∈ ball z ε, ‖P y / Q y‖ = 1 := by
      intro y hy
      rw [norm_div, (hb y hy).2.2, div_self (norm_ne_zero_iff.mpr (hb y hy).2.1)]
    have hmax : IsMaxOn (norm ∘ fun y => P y / Q y) (ball z ε) z := by
      intro y hy
      show ‖P y / Q y‖ ≤ ‖P z / Q z‖
      rw [hn y hy, hn z (mem_ball_self hε)]
    have hc := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm (convex_ball z ε).isPreconnected
      isOpen_ball hd (mem_ball_self hε) hmax
    refine ⟨z, hzO', P z / Q z, ?_⟩
    filter_upwards [ball_mem_nhds z hε] with y hy
    have e : P y / Q y = P z / Q z := hc hy
    rw [← e, div_mul_cancel₀ _ (hb y hy).2.1]

theorem exists_eq_const_mul_of_forall_exists_norm_eq :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (ι : Type) [Countable ι]
      (O : Set V), IsOpen O → IsPreconnected O → O.Nonempty → ∀ (P : V → ℂ) (Q : ι → V → ℂ),
      DifferentiableOn ℂ P O → (∀ i, DifferentiableOn ℂ (Q i) O) → (∀ x ∈ O, ∃ i, ‖P x‖ = ‖Q i x‖) →
      ∃ (i : ι) (c : ℂ), ∀ x ∈ O, P x = c * Q i x := by
  intro V _ _ _ ι _ O hO hc hne P Q hP hQ h
  haveI : CompleteSpace V := FiniteDimensional.complete ℂ V
  haveI : BaireSpace O := hO.baireSpace
  haveI : Nonempty O := hne.to_subtype
  have hcl : ∀ i, IsClosed {x : O | ‖P x‖ = ‖Q i x‖} := fun i =>
    isClosed_eq (hP.continuousOn.restrict.norm) ((hQ i).continuousOn.restrict.norm)
  have hcov : ⋃ i, {x : O | ‖P x‖ = ‖Q i x‖} = univ := by
    refine eq_univ_of_forall fun x => ?_
    obtain ⟨i, hi⟩ := h x x.2
    exact mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨i, x, hx⟩ := nonempty_interior_of_iUnion_of_closed hcl hcov
  have hx1 : ∀ᶠ y : O in 𝓝 x, ‖P y‖ = ‖Q i y‖ := mem_interior_iff_mem_nhds.mp hx
  have hx2 : ∀ᶠ y in 𝓝 (x : V), ‖P y‖ = ‖Q i y‖ := by
    rw [← hO.isOpenEmbedding_subtypeVal.map_nhds_eq x]
    exact hx1
  obtain ⟨z, hz, c, hzc⟩ := exists_eventually_eq_mul_of_norm_eq hO hP (hQ i) x.2 hx2
  refine ⟨i, c, fun y hy => ?_⟩
  have hd : DifferentiableOn ℂ (fun y => P y - c * Q i y) O := hP.sub ((hQ i).const_mul c)
  have := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.eq_zero_of_eventually hO hc hd hz
    (by filter_upwards [hzc] with y hy; simp [hy]) y hy
  exact sub_eq_zero.mp this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsMeasureOfBoundedMoments
section
open Filter
open scoped BigOperators Topology

namespace GlobalTheory.MultiMahler

variable {q : ℕ} [Fact q.Prime]

theorem fwdDiff_tendsto_zero' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℚ_[q] E]
    [IsUltrametricDist E] (f : C(ℤ_[q], E)) :
    Tendsto (fun n => (fwdDiff (1 : ℤ_[q]))^[n] f 0) atTop (𝓝 0) := by
  letI : Module ℤ_[q] E := Module.compHom E (algebraMap ℤ_[q] ℚ_[q])
  haveI : IsBoundedSMul ℤ_[q] E := IsBoundedSMul.of_norm_smul_le fun r x =>
    norm_smul_le (r : ℚ_[q]) x
  exact PadicInt.fwdDiff_tendsto_zero f

noncomputable def curryFirst {g : ℕ} (F : C(Fin (g + 1) → ℤ_[q], ℂ_[q])) :
    C(ℤ_[q], C(Fin g → ℤ_[q], ℂ_[q])) :=
  ContinuousMap.curry (F.comp ⟨fun x : ℤ_[q] × (Fin g → ℤ_[q]) => Fin.cons x.1 x.2,
    Continuous.finCons continuous_fst continuous_snd⟩)

theorem curryFirst_apply {g : ℕ} (F : C(Fin (g + 1) → ℤ_[q], ℂ_[q])) (t : ℤ_[q])
    (a : Fin g → ℤ_[q]) : curryFirst F t a = F (Fin.cons t a) := rfl

theorem norm_curryFirst_le {g : ℕ} (F : C(Fin (g + 1) → ℤ_[q], ℂ_[q])) :
    ‖curryFirst F‖ ≤ ‖F‖ := by
  rw [ContinuousMap.norm_le _ (norm_nonneg _)]
  intro t
  rw [ContinuousMap.norm_le _ (norm_nonneg _)]
  intro a
  exact F.norm_coe_le_norm _

noncomputable def diffFirst {g : ℕ} (m : ℕ) :
    C(Fin (g + 1) → ℤ_[q], ℂ_[q]) →ₗ[ℂ_[q]] C(Fin g → ℤ_[q], ℂ_[q]) where
  toFun F := (fwdDiff (1 : ℤ_[q]))^[m] (curryFirst F) 0
  map_add' F G := by
    have : (curryFirst (F + G) : ℤ_[q] → _) = curryFirst F + curryFirst G := by
      ext t a; simp [curryFirst_apply]
    rw [this, fwdDiff_iter_add]; rfl
  map_smul' r F := by
    have : (curryFirst (r • F) : ℤ_[q] → _) = r • (curryFirst F : ℤ_[q] → _) := by
      ext t a; simp [curryFirst_apply]
    rw [this, fwdDiff_iter_const_smul]; rfl

theorem diffFirst_apply {g : ℕ} (m : ℕ) (F : C(Fin (g + 1) → ℤ_[q], ℂ_[q])) :
    diffFirst m F = (fwdDiff (1 : ℤ_[q]))^[m] (curryFirst F) 0 := rfl

theorem exists_multiDiff (g : ℕ) :
    ∃ D : (Fin g → ℕ) → C(Fin g → ℤ_[q], ℂ_[q]) →ₗ[ℂ_[q]] ℂ_[q],
      (∀ n F, ‖D n F‖ ≤ ‖F‖) ∧
      (∀ n (f : Fin g → C(ℤ_[q], ℂ_[q])) (F : C(Fin g → ℤ_[q], ℂ_[q])),
        (∀ a, F a = ∏ i, f i (a i)) → D n F = ∏ i, (fwdDiff (1 : ℤ_[q]))^[n i] (f i) 0) ∧
      (∀ F, Tendsto (fun n => D n F) cofinite (𝓝 0)) := by
  induction g with
  | zero =>
    refine ⟨fun _ => { toFun := fun F => F 0, map_add' := fun _ _ => rfl,
                       map_smul' := fun _ _ => rfl }, fun n F => F.norm_coe_le_norm _,
      fun n f F hF => by simpa using hF 0, fun F => ?_⟩
    rw [Filter.cofinite_eq_bot]
    exact tendsto_bot
  | succ g ih =>
    obtain ⟨D, h1, h2, h3⟩ := ih
    refine ⟨fun n => (D (Fin.tail n)).comp (diffFirst (n 0)), fun n F => ?_,
      fun n f F hF => ?_, fun F => ?_⟩
    · exact (h1 _ _).trans ((IsUltrametricDist.norm_fwdDiff_iter_apply_le 1 _ 0 _).trans
        (norm_curryFirst_le F))
    · let P : C(Fin g → ℤ_[q], ℂ_[q]) := ⟨fun a => ∏ i, f i.succ (a i), by fun_prop⟩
      have hP : diffFirst (n 0) F = (fwdDiff (1 : ℤ_[q]))^[n 0] (f 0) 0 • P := by
        rw [diffFirst_apply, fwdDiff_iter_eq_sum_shift, fwdDiff_iter_eq_sum_shift,
          Finset.sum_smul]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [smul_assoc]
        congr 1
        ext a
        simp [curryFirst_apply, hF, Fin.prod_univ_succ, P]
      rw [LinearMap.comp_apply, hP, map_smul, h2 _ (fun i => f i.succ) P (fun _ => rfl),
        Fin.prod_univ_succ]
      rfl
    · refine NormedAddGroup.tendsto_nhds_zero.mpr fun ε hε => ?_
      have hA := NormedAddGroup.tendsto_nhds_zero.mp (fwdDiff_tendsto_zero' (curryFirst F)) ε hε
      rw [← Nat.cofinite_eq_atTop, Filter.eventually_cofinite] at hA
      have hB : ∀ m, {n' : Fin g → ℕ | ¬ ‖D n' (diffFirst m F)‖ < ε}.Finite := fun m =>
        Filter.eventually_cofinite.mp (NormedAddGroup.tendsto_nhds_zero.mp (h3 _) ε hε)
      rw [Filter.eventually_cofinite]
      refine (hA.biUnion fun m _ => (hB m).image
        (fun n' => (Fin.cons m n' : Fin (g + 1) → ℕ))).subset fun n hn => ?_
      simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_image, not_lt] at hn ⊢
      exact ⟨n 0, hn.trans (h1 _ _), Fin.tail n, hn, Fin.cons_self_tail n⟩

noncomputable def binomC (k : ℕ) : C(ℤ_[q], ℂ_[q]) :=
  ⟨fun x => algebraMap ℚ_[q] ℂ_[q] ((mahler k x : ℤ_[q]) : ℚ_[q]),
    (continuous_algebraMap _ _).comp (continuous_subtype_val.comp (mahler k).continuous)⟩

theorem norm_binomC_le (k : ℕ) (x : ℤ_[q]) : ‖binomC k x‖ ≤ 1 := by
  change ‖algebraMap ℚ_[q] ℂ_[q] ((mahler k x : ℤ_[q]) : ℚ_[q])‖ ≤ 1
  rw [norm_algebraMap']
  exact PadicInt.norm_le_one _

theorem binomC_natCast (k n : ℕ) : binomC k (n : ℤ_[q]) = (n.choose k : ℂ_[q]) := by
  change algebraMap ℚ_[q] ℂ_[q] ((mahler k (n : ℤ_[q]) : ℤ_[q]) : ℚ_[q]) = _
  rw [mahler_natCast_eq, PadicInt.coe_natCast, map_natCast]

theorem fwdDiff_binomC (k m : ℕ) :
    (fwdDiff (1 : ℤ_[q]))^[m] (binomC (q := q) k) 0 = if m = k then 1 else 0 := by
  have h := fwdDiff_iter_choose_zero k m
  rw [fwdDiff_iter_eq_sum_shift] at h ⊢
  have h' := congrArg (Int.cast : ℤ → ℂ_[q]) h
  simp only [zero_add, nsmul_one, binomC_natCast] at h' ⊢
  simpa using h'

theorem exists_measure_of_bounded_moments :
    ∀ (q : ℕ) [Fact q.Prime] (g : ℕ) (c : (Fin g → ℕ) → ℂ_[q]), (∃ B : ℝ, ∀ n, ‖c n‖ ≤ B) →
      ∃ μ : C(Fin g → ℤ_[q], ℂ_[q]) →L[ℂ_[q]] ℂ_[q],
        (∀ B : ℝ, 0 ≤ B → (‖μ‖ ≤ B ↔ ∀ n, ‖c n‖ ≤ B)) ∧
        ∀ (f : Fin g → C(ℤ_[q], ℂ_[q])) (F : C(Fin g → ℤ_[q], ℂ_[q])),
          (∀ a, F a = ∏ i, f i (a i)) →
          HasSum (fun n : Fin g → ℕ => c n * ∏ i, (fwdDiff (1 : ℤ_[q]))^[n i] (f i) 0) (μ F) := by
  intro q _ g c ⟨B₀, hB₀⟩
  obtain ⟨D, h1, h2, h3⟩ := exists_multiDiff (q := q) g
  have hs : ∀ F, Summable fun n => c n * D n F := fun F => by
    refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have := (tendsto_zero_iff_norm_tendsto_zero.mp (h3 F)).const_mul B₀
    rw [mul_zero] at this
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) this
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hB₀ n) (norm_nonneg _)
  let L : C(Fin g → ℤ_[q], ℂ_[q]) →ₗ[ℂ_[q]] ℂ_[q] :=
    { toFun := fun F => ∑' n, c n * D n F
      map_add' := fun F G => by
        simp only [map_add, mul_add]
        exact (hs F).tsum_add (hs G)
      map_smul' := fun r F => by
        simp only [map_smul, smul_eq_mul, RingHom.id_apply]
        rw [← tsum_mul_left]
        exact tsum_congr fun n => by ring }
  have hL : ∀ B : ℝ, (∀ n, ‖c n‖ ≤ B) → ∀ F, ‖L F‖ ≤ B * ‖F‖ := fun B hB F => by
    refine IsUltrametricDist.norm_tsum_le_of_forall_le fun n => ?_
    rw [norm_mul]
    exact mul_le_mul (hB n) (h1 n F) (norm_nonneg _) ((norm_nonneg _).trans (hB n))
  have hsum : ∀ (f : Fin g → C(ℤ_[q], ℂ_[q])) (F : C(Fin g → ℤ_[q], ℂ_[q])),
      (∀ a, F a = ∏ i, f i (a i)) →
      HasSum (fun n : Fin g → ℕ => c n * ∏ i, (fwdDiff (1 : ℤ_[q]))^[n i] (f i) 0) (L F) := by
    intro f F hF
    have := (hs F).hasSum
    simp only [fun n => h2 n f F hF] at this
    convert this using 1
    exact tsum_congr fun n => by rw [h2 n f F hF]
  refine ⟨L.mkContinuous B₀ (hL B₀ hB₀), fun B hB => ⟨fun hμ n => ?_, fun h => ?_⟩, hsum⟩
  · let P : C(Fin g → ℤ_[q], ℂ_[q]) := ⟨fun a => ∏ i, binomC (n i) (a i), by fun_prop⟩
    have hP : ‖P‖ ≤ 1 := by
      rw [ContinuousMap.norm_le _ zero_le_one]
      intro a
      change ‖∏ i, binomC (n i) (a i)‖ ≤ 1
      rw [norm_prod]
      exact Finset.prod_le_one (fun _ _ => norm_nonneg _) fun _ _ => norm_binomC_le _ _
    have hv : L P = c n := by
      refine (hsum (fun i => binomC (n i)) P fun _ => rfl).unique ?_
      convert hasSum_single (f := fun m : Fin g → ℕ =>
        c m * ∏ i, (fwdDiff (1 : ℤ_[q]))^[m i] (binomC (q := q) (n i)) 0) n ?_ using 1
      · simp [fwdDiff_binomC]
      · intro m hm
        obtain ⟨i, hi⟩ := Function.ne_iff.mp hm
        rw [Finset.prod_eq_zero (Finset.mem_univ i) (by rw [fwdDiff_binomC, if_neg hi]), mul_zero]
    calc ‖c n‖ = ‖L.mkContinuous B₀ (hL B₀ hB₀) P‖ := by rw [← hv]; rfl
      _ ≤ _ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ B * 1 := mul_le_mul hμ hP (norm_nonneg _) hB
      _ = B := mul_one _
  · exact ContinuousLinearMap.opNorm_le_bound _ hB (hL B h)

end GlobalTheory.MultiMahler
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MeanFundamentalDomainEqOfPeriodic
section
open MeasureTheory
open scoped Pointwise

namespace GlobalTheory

theorem setIntegral_translate_of_periodic {n : Type} [Fintype n] (L : AddSubgroup (n → ℝ))
    [Countable L] (D : Set (n → ℝ)) (g : (n → ℝ) → ℂ)
    (hD : IsAddFundamentalDomain L D volume) (hp : ∀ p ∈ L, ∀ s, g (s + p) = g s)
    (s : n → ℝ) : ∫ t in D, g (s + t) = ∫ t in D, g t := by
  have hsD : IsAddFundamentalDomain L (s +ᵥ D) volume := hD.vadd_of_comm s
  have himg : (fun t => s + t) '' D = s +ᵥ D := by
    change (fun t => s +ᵥ t) '' D = s +ᵥ D
    exact Set.image_vadd
  rw [← (measurePreserving_add_left volume s).setIntegral_image_emb
    (MeasurableEquiv.addLeft s).measurableEmbedding g D, himg]
  refine hsD.setIntegral_eq hD (fun p x => ?_)
  rw [AddSubgroup.vadd_def, vadd_eq_add, add_comm]
  exact hp p p.2 x

theorem mean_fundamentalDomain_eq_of_periodic :
    ∀ (n : Type) [Fintype n] (L L' : AddSubgroup (n → ℝ)) [Countable L] [Countable L'] (D D' : Set (n → ℝ)) (g : (n → ℝ) → ℂ), MeasureTheory.IsAddFundamentalDomain L D MeasureTheory.volume → MeasureTheory.IsAddFundamentalDomain L' D' MeasureTheory.volume → MeasureTheory.volume D < ⊤ → MeasureTheory.volume D' < ⊤ → Continuous g → (∃ C : ℝ, ∀ s, ‖g s‖ ≤ C) → (∀ p ∈ L, ∀ s, g (s + p) = g s) → (∀ p ∈ L', ∀ s, g (s + p) = g s) → ((MeasureTheory.volume D).toReal : ℂ) * ∫ s in D', g s = ((MeasureTheory.volume D').toReal : ℂ) * ∫ s in D, g s := by
  intro n _ L L' _ _ D D' g hD hD' hDfin hD'fin hg ⟨C, hC⟩ hp hp'
  have : IsFiniteMeasure (volume.restrict D) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hDfin⟩
  have : IsFiniteMeasure (volume.restrict D') :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hD'fin⟩
  have hint : Integrable (Function.uncurry fun s t => g (s + t))
      ((volume.restrict D).prod (volume.restrict D')) := by
    refine Integrable.of_bound ?_ C (Filter.Eventually.of_forall fun z => hC _)
    exact (hg.comp (continuous_fst.add continuous_snd)).aestronglyMeasurable
  have h1 : ∫ s in D, ∫ t in D', g (s + t) = ((volume D).toReal : ℂ) * ∫ t in D', g t := by
    simp_rw [setIntegral_translate_of_periodic L' D' g hD' hp']
    rw [setIntegral_const]
    simp [Complex.real_smul, Measure.real]
  have h2 : ∫ t in D', ∫ s in D, g (s + t) = ((volume D').toReal : ℂ) * ∫ s in D, g s := by
    have : ∀ t, ∫ s in D, g (s + t) = ∫ s in D, g s := fun t => by
      simp_rw [add_comm _ t]
      exact setIntegral_translate_of_periodic L D g hD hp t
    simp_rw [this]
    rw [setIntegral_const]
    simp [Complex.real_smul, Measure.real]
  rw [← h1, ← h2]
  exact integral_integral_swap hint

end GlobalTheory
end

