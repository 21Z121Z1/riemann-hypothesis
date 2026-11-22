import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0008
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0009

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PHolomorphicIsolatedFibreOpen
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Metric

theorem HolomorphicIsolatedFibreOpen.proof (hPS : ProperHolomorphicSurjective.Statement) :
    HolomorphicIsolatedFibreOpen.Statement := by
  intro k U g u hU hu hg ⟨W, hW, hiso⟩ V hV
  obtain ⟨r, hr, hrsub⟩ : ∃ r > 0, closedBall u r ⊆ U ∩ W ∩ V :=
    nhds_basis_closedBall.mem_iff.1 (Filter.inter_mem (Filter.inter_mem (hU.mem_nhds hu) hW) hV)
  have hgc : ContinuousOn g (closedBall u r) := hg.continuousOn.mono fun x hx => (hrsub hx).1.1

  have hSc : IsCompact (g '' sphere u r) :=
    (isCompact_sphere u r).image_of_continuousOn (hgc.mono sphere_subset_closedBall)
  have hnot : g u ∉ g '' sphere u r := by
    rintro ⟨s, hs, hgs⟩
    have hsK := hrsub (sphere_subset_closedBall hs)
    have := hiso s hsK.1.2 hsK.1.1 hgs
    subst this
    rw [mem_sphere, dist_self] at hs
    exact hr.ne' hs.symm
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.1 hSc.isClosed.isOpen_compl (g u) hnot

  have key : ∀ v ∈ closedBall u r, g v ∈ ball (g u) ε → v ∈ ball u r := by
    intro v hv hgv
    rcases (mem_closedBall.1 hv).lt_or_eq with h | h
    · exact h
    · exact (hεsub hgv ⟨v, mem_sphere.2 h, rfl⟩).elim
  have hΩ : IsOpen (ball u r ∩ g ⁻¹' ball (g u) ε) :=
    (hgc.mono ball_subset_closedBall).isOpen_inter_preimage isOpen_ball isOpen_ball
  have hproper : ∀ L ⊆ ball (g u) ε, IsCompact L →
      IsCompact ((ball u r ∩ g ⁻¹' ball (g u) ε) ∩ g ⁻¹' L) := by
    intro L hLD hL
    have heq : (ball u r ∩ g ⁻¹' ball (g u) ε) ∩ g ⁻¹' L = closedBall u r ∩ g ⁻¹' L := by
      ext v
      constructor
      · rintro ⟨⟨hv, _⟩, hvL⟩
        exact ⟨ball_subset_closedBall hv, hvL⟩
      · rintro ⟨hv, hvL⟩
        exact ⟨⟨key v hv (hLD hvL), hLD hvL⟩, hvL⟩
    rw [heq]
    exact (isCompact_closedBall u r).of_isClosed_subset
      (hgc.preimage_isClosed_of_isClosed isClosed_closedBall hL.isClosed) Set.inter_subset_left
  have hsurj := hPS k _ _ g hΩ ⟨u, mem_ball_self hr, mem_ball_self hε⟩ isOpen_ball
    (convex_ball _ _).isPreconnected (hg.mono fun x hx => (hrsub (ball_subset_closedBall hx.1)).1.1)
    (fun x hx => hx.2) hproper
  refine Filter.mem_of_superset (ball_mem_nhds _ hε) ?_
  rw [← hsurj]
  exact Set.image_mono fun x hx => (hrsub (ball_subset_closedBall hx.1)).2

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PIdealHeightSpread
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem IdealHeightSpread.proof : IdealHeightSpread.Statement := by
  intro R _ _ I P _ _
  classical
  have hF := I.finite_minimalPrimes_of_isNoetherianRing R

  let a : Ideal R → R := fun p =>
    if h : ¬ (p : Set R) ⊆ P then Classical.choose (Set.not_subset.mp h) else 1
  have ha : ∀ p : Ideal R, ¬ p ≤ P → a p ∈ p ∧ a p ∉ P := by
    intro p h
    have h' : ¬ (p : Set R) ⊆ P := h
    simp only [a, dif_pos h']
    exact Classical.choose_spec (Set.not_subset.mp h')
  let s : Finset (Ideal R) := hF.toFinset.filter (fun p => ¬ p ≤ P)
  refine ⟨∏ p ∈ s, a p, ?_, ?_⟩
  · rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨p, hp, hpP⟩
    exact (ha p (Finset.mem_filter.mp hp).2).2 hpP
  · intro Q _ _ hgQ
    rw [Ideal.height_eq_inf_minimalPrimes (I.map (algebraMap R (Localization.AtPrime Q)))]
    refine le_iInf₂ fun J hJ => ?_
    have hJp : J.IsPrime := hJ.isPrime
    have hmin : J.comap (algebraMap R (Localization.AtPrime Q)) ∈ I.minimalPrimes := by
      rw [IsLocalization.minimalPrimes_map Q.primeCompl] at hJ
      exact hJ
    set p := J.comap (algebraMap R (Localization.AtPrime Q)) with hpdef
    have hpp : p.IsPrime := hmin.1.1

    have hpQ : p ≤ Q := by
      intro x hx
      by_contra hxQ
      have hu := IsLocalization.map_units (Localization.AtPrime Q) (⟨x, hxQ⟩ : Q.primeCompl)
      exact hJp.ne_top (Ideal.eq_top_of_isUnit_mem J hx hu)

    have hpP : p ≤ P := by
      by_contra hnot
      apply hgQ
      apply hpQ
      have hps : p ∈ s := Finset.mem_filter.mpr ⟨hF.mem_toFinset.mpr hmin, hnot⟩
      exact Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem a hps) (ha p hnot).1
    have hdisj : Disjoint (P.primeCompl : Set R) (p : Set R) := by
      rw [Set.disjoint_left]
      intro x hx hxp
      exact hx (hpP hxp)
    have hJh : J.height = p.height := (IsLocalization.height_under Q.primeCompl J).symm
    rw [hJh, ← IsLocalization.height_map_of_disjoint P.primeCompl (S := Localization.AtPrime P) p hdisj]
    exact Ideal.height_mono (Ideal.map_mono hmin.1.2)

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PInjectiveHolomorphicDerivNeZero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Filter Topology

theorem InjectiveHolomorphicDerivNeZero.proof : InjectiveHolomorphicDerivNeZero.Statement := by
  intro D f hD hf hinj a ha hder
  have hDa : D ∈ 𝓝 a := hD.mem_nhds ha
  set g : ℂ → ℂ := fun z ↦ f z - f a with hg
  have hga : AnalyticAt ℂ g a := (hf.analyticAt hDa).sub analyticAt_const

  have hntop : analyticOrderAt g a ≠ ⊤ := by
    intro htop
    rw [analyticOrderAt_eq_top] at htop
    have hev : ∀ᶠ z in 𝓝[≠] a, (g z = 0 ∧ z ∈ D) ∧ z ∈ ({a}ᶜ : Set ℂ) :=
      ((htop.and (hDa : ∀ᶠ z in 𝓝 a, z ∈ D)).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
    obtain ⟨z, ⟨hz0, hzD⟩, hza⟩ := hev.exists
    exact hza (hinj hzD ha (sub_eq_zero.mp hz0))
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hntop
  obtain ⟨u, hu, hua, hfac⟩ := hga.analyticOrderAt_eq_natCast.mp hn.symm
  simp only [smul_eq_mul] at hfac
  have hn0 : n ≠ 0 := by
    rintro rfl
    have := hfac.self_of_nhds
    simp [hg] at this
    exact hua this.symm
  have hn1 : n ≠ 1 := by
    rintro rfl
    have hd : HasDerivAt (fun z ↦ (z - a) ^ 1 * u z) (u a) a := by
      have := ((hasDerivAt_id' a).sub_const a).mul hu.differentiableAt.hasDerivAt
      simp only [pow_one]
      exact this.congr_deriv (by simp)
    have : deriv g a = u a :=
      (EventuallyEq.deriv_eq (hfac : g =ᶠ[𝓝 a] fun z ↦ (z - a) ^ 1 * u z)).trans hd.deriv
    rw [hg, deriv_sub_const, hder] at this
    exact hua this.symm

  set c : ℂ := u a ^ ((n : ℂ)⁻¹) with hc
  set v : ℂ → ℂ := fun z ↦ c * (u z / u a) ^ ((n : ℂ)⁻¹) with hv
  have hva : AnalyticAt ℂ v a := analyticAt_const.mul
    ((hu.div analyticAt_const hua).cpow analyticAt_const (by simp [hua, Complex.one_mem_slitPlane]))
  have hvpow : ∀ z, v z ^ n = u z := by
    intro z
    rw [hv, mul_pow, hc, Complex.cpow_nat_inv_pow _ hn0, Complex.cpow_nat_inv_pow _ hn0]
    field_simp
  have hv0 : v a ≠ 0 := by
    intro h
    have := hvpow a
    rw [h, zero_pow hn0] at this
    exact hua this.symm
  set w : ℂ → ℂ := fun z ↦ (z - a) * v z with hw
  have hwd : HasDerivAt w (v a) a := by
    have := ((hasDerivAt_id' a).sub_const a).mul hva.differentiableAt.hasDerivAt
    exact this.congr_deriv (by simp)
  have hwa : w a = 0 := by simp [hw]
  have hgw : ∀ z, g z = (z - a) ^ n * u z → g z = w z ^ n := by
    intro z hz
    rw [hz, ← hvpow z, ← mul_pow]

  have hmap : 𝓝 (w a) ≤ map w (𝓝 a) := by
    have hwan : AnalyticAt ℂ w a := (analyticAt_id.sub analyticAt_const).mul hva
    refine hwan.eventually_constant_or_nhds_le_map_nhds.resolve_left ?_
    intro hconst
    have h1 : deriv w a = 0 := by
      rw [EventuallyEq.deriv_eq (hconst : w =ᶠ[𝓝 a] fun _ ↦ w a)]
      simp
    exact hv0 (hwd.deriv.symm.trans h1)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    (hmap (image_mem_map (inter_mem hDa hfac)))
  rw [hwa] at hball
  have hk : 1 < n := by omega
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / n) with hζ
  have hprim : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hn0
  set t : ℂ := ((ε / 2 : ℝ) : ℂ) with ht
  have htn : ‖t‖ = ε / 2 := by rw [ht, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have ht0 : t ≠ 0 := by
    intro h
    rw [h, norm_zero] at htn
    linarith
  obtain ⟨z₁, ⟨hz₁D, hz₁⟩, hw₁⟩ := hball (by
    rw [Metric.mem_ball, dist_zero_right, htn]; linarith)
  obtain ⟨z₂, ⟨hz₂D, hz₂⟩, hw₂⟩ := hball (show ζ * t ∈ Metric.ball 0 ε by
    rw [Metric.mem_ball, dist_zero_right, norm_mul, hprim.norm'_eq_one hn0, htn]; linarith)
  have hg₁ := hgw z₁ hz₁
  have hg₂ := hgw z₂ hz₂
  rw [hw₁] at hg₁
  rw [hw₂, mul_pow, hprim.pow_eq_one, one_mul] at hg₂
  have hf12 : f z₁ = f z₂ := by
    have : g z₁ = g z₂ := hg₁.trans hg₂.symm
    simpa [hg] using this
  have h12 := hinj hz₁D hz₂D hf12
  rw [h12, hw₂] at hw₁
  have : (ζ - 1) * t = 0 := by rw [sub_mul, one_mul, hw₁, sub_self]
  rcases mul_eq_zero.mp this with h | h
  · exact hprim.ne_one hk (sub_eq_zero.mp h)
  · exact ht0 h

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PInvarianceOfDomain
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

namespace InvarianceOfDomain

open Metric Set MeasureTheory

variable {n : ℕ}

theorem brouwer_closedBall (hB : BrouwerFixedPoint.Statement) {a : Fin n → ℝ} {r : ℝ} (hr : 0 < r)
    {h : (Fin n → ℝ) → Fin n → ℝ} (hc : ContinuousOn h (closedBall a r))
    (hm : MapsTo h (closedBall a r) (closedBall a r)) : ∃ x ∈ closedBall a r, h x = x := by
  have haff : MapsTo (fun x : Fin n → ℝ => a + r • x) (closedBall 0 1) (closedBall a r) := by
    intro x hx
    rw [mem_closedBall, dist_zero_right] at hx
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr.le]
    nlinarith [norm_nonneg x]
  have hcont : ContinuousOn (fun x : Fin n → ℝ => a + r • x) (closedBall 0 1) :=
    by fun_prop
  have hcomp : ContinuousOn (fun x : Fin n → ℝ => h (a + r • x)) (closedBall 0 1) := hc.comp hcont haff
  obtain ⟨x, hx, hfix⟩ := hB n (fun x => r⁻¹ • (h (a + r • x) - a)) (by fun_prop)
    (by
      intro x hx
      have hy := hm (haff hx)
      rw [mem_closedBall, dist_eq_norm] at hy
      rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hr.le),
        inv_mul_le_iff₀ hr, mul_one]
      exact hy)
  refine ⟨a + r • x, haff hx, ?_⟩
  have h2 : r • (r⁻¹ • (h (a + r • x) - a)) = r • x := by rw [hfix]
  rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul] at h2
  exact sub_eq_iff_eq_add'.mp h2

def smoothSubalgebra (n : ℕ) : Subalgebra ℝ C(Fin n → ℝ, ℝ) where
  carrier := {g | ContDiff ℝ 1 (g : (Fin n → ℝ) → ℝ)}
  mul_mem' {g h} hg hh := by
    simp only [mem_ofPred_eq, ContinuousMap.coe_mul]
    exact ContDiff.mul hg hh
  add_mem' {g h} hg hh := by
    simp only [mem_ofPred_eq, ContinuousMap.coe_add]
    exact ContDiff.add hg hh
  algebraMap_mem' c := by
    simp only [mem_ofPred_eq]
    convert (contDiff_const (c := c) : ContDiff ℝ 1 fun _ : Fin n → ℝ => c) using 1
    ext x
    simp

theorem smoothSubalgebra_separatesPoints : (smoothSubalgebra n).SeparatesPoints := by
  intro x y hxy
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
  refine ⟨fun z => z i, ⟨⟨fun z => z i, continuous_apply i⟩, ?_, rfl⟩, hi⟩
  show ContDiff ℝ 1 fun z : Fin n → ℝ => z i
  exact contDiff_apply ℝ ℝ i

theorem exists_differentiable_near {S : Set (Fin n → ℝ)} (hS : IsCompact S)
    (G : (Fin n → ℝ) → Fin n → ℝ) (hG : Continuous G) {η : ℝ} (hη : 0 < η) :
    ∃ P : (Fin n → ℝ) → Fin n → ℝ, Differentiable ℝ P ∧ ∀ y ∈ S, ‖P y - G y‖ < η := by
  have h : ∀ i : Fin n, ∃ g ∈ smoothSubalgebra n, ∀ y ∈ S, ‖(g : (Fin n → ℝ) → ℝ) y - G y i‖ < η :=
    fun i => ContinuousMap.exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints
      smoothSubalgebra_separatesPoints ⟨fun y => G y i, (continuous_apply i).comp hG⟩ hS hη
  choose g hg hgS using h
  refine ⟨fun y i => g i y, differentiable_pi.2 fun i => ?_, fun y hy => ?_⟩
  · exact (show ContDiff ℝ 1 (g i : (Fin n → ℝ) → ℝ) from hg i).differentiable one_ne_zero
  · rw [pi_norm_lt_iff hη]
    intro i
    simpa using hgS i y hy

theorem exists_small_avoid {P : (Fin n → ℝ) → Fin n → ℝ} (hP : Differentiable ℝ P) (c a : Fin n → ℝ)
    {ρ δ : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ) :
    ∃ v : Fin n → ℝ, ‖v‖ < δ ∧ ∀ y ∈ sphere c ρ, P y ≠ a + v := by
  have hnull : volume (P '' sphere c ρ) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hP.differentiableOn
      (Measure.addHaar_sphere_of_ne_zero volume c hρ.ne')
  by_contra! hall
  have hsub : ball a δ ⊆ P '' sphere c ρ := by
    intro z hz
    obtain ⟨y, hy, hyz⟩ := hall (z - a) (by rwa [mem_ball, dist_eq_norm] at hz)
    exact ⟨y, hy, by rw [hyz]; abel⟩
  have hle := measure_mono (μ := volume) hsub
  rw [hnull] at hle
  exact (measure_ball_pos volume a hδ).ne' (nonpos_iff_eq_zero.mp hle)

theorem exists_pos_le {s : Set (Fin n → ℝ)} (hs : IsCompact s) {g : (Fin n → ℝ) → ℝ}
    (hg : ContinuousOn g s) (hpos : ∀ y ∈ s, 0 < g y) : ∃ δ > 0, ∀ y ∈ s, δ ≤ g y := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, by simp⟩
  · obtain ⟨y0, hy0, hmin⟩ := hs.exists_isMinOn hne hg
    exact ⟨g y0, hpos y0 hy0, fun y hy => hmin hy⟩

noncomputable def radialPush (c : Fin n → ℝ) (ρ : ℝ) (y : Fin n → ℝ) : Fin n → ℝ :=
  c + max 1 (ρ / ‖y - c‖) • (y - c)

theorem radialPush_of_le {c y : Fin n → ℝ} {ρ : ℝ} (hρ : 0 < ρ) (hy : ρ ≤ dist y c) :
    radialPush c ρ y = y := by
  rw [dist_eq_norm] at hy
  have hpos : 0 < ‖y - c‖ := hρ.trans_le hy
  have h1 : ρ / ‖y - c‖ ≤ 1 := (div_le_one hpos).2 hy
  rw [radialPush, max_eq_left h1, one_smul, add_sub_cancel]

theorem radialPush_mem_sphere {c y : Fin n → ℝ} {ρ : ℝ} (hy : dist y c < ρ) (hyc : y ≠ c) :
    radialPush c ρ y ∈ sphere c ρ := by
  rw [dist_eq_norm] at hy
  have hpos : 0 < ‖y - c‖ := norm_pos_iff.2 (sub_ne_zero.2 hyc)
  have h1 : 1 ≤ ρ / ‖y - c‖ := (one_le_div hpos).2 hy.le
  rw [mem_sphere, dist_eq_norm, radialPush, max_eq_right h1, add_sub_cancel_left, norm_smul,
    Real.norm_of_nonneg (div_nonneg (hpos.trans hy).le hpos.le), div_mul_cancel₀ ρ hpos.ne']

theorem continuousOn_radialPush (c : Fin n → ℝ) (ρ : ℝ) : ContinuousOn (radialPush c ρ) {y | y ≠ c} := by
  have hn : ContinuousOn (fun y : Fin n → ℝ => ρ / ‖y - c‖) {y | y ≠ c} := by
    refine ContinuousOn.div continuousOn_const (by fun_prop) ?_
    intro y hy
    exact norm_ne_zero_iff.2 (sub_ne_zero.2 hy)
  have hm : ContinuousOn (fun y : Fin n → ℝ => max 1 (ρ / ‖y - c‖)) {y | y ≠ c} :=
    continuousOn_const.sup hn
  unfold radialPush
  fun_prop

theorem mem_interior_image (hB : BrouwerFixedPoint.Statement) {f : (Fin n → ℝ) → Fin n → ℝ}
    {a : Fin n → ℝ} {r : ℝ} (hr : 0 < r) (hc : ContinuousOn f (closedBall a r))
    (hi : InjOn f (closedBall a r)) : f a ∈ interior (f '' closedBall a r) := by
  have hK : IsCompact (closedBall a r) := isCompact_closedBall a r

  obtain ⟨G, hGf⟩ : ∃ G : C(Fin n → ℝ, Fin n → ℝ), ∀ x ∈ closedBall a r, G (f x) = x := by
    have : CompactSpace (closedBall a r) := isCompact_iff_compactSpace.mp hK
    have hce : Topology.IsClosedEmbedding ((closedBall a r).domRestrict f) :=
      hc.domRestrict.isClosedEmbedding hi.injective
    obtain ⟨G, hG⟩ := ContinuousMap.exists_extension' hce ⟨Subtype.val, continuous_subtype_val⟩
    exact ⟨G, fun x hx => congrFun hG ⟨x, hx⟩⟩
  have hGa : G (f a) = a := hGf a (mem_closedBall_self hr.le)
  by_contra hno

  obtain ⟨ρ3, hρ3, hρG⟩ := Metric.continuousAt_iff.mp G.continuous.continuousAt (r / 4) (by positivity)
  obtain ⟨ρ, hρ, hρlt⟩ : ∃ ρ : ℝ, 0 < ρ ∧ 2 * ρ < ρ3 := ⟨ρ3 / 3, by positivity, by linarith⟩
  have hGnear : ∀ y, dist y (f a) ≤ 2 * ρ → dist (G y) a < r / 4 := fun y hy => by
    have h1 := hρG (show dist y (f a) < ρ3 by linarith)
    rwa [hGa] at h1

  obtain ⟨c, hcball, hcK⟩ : ∃ c, dist c (f a) < ρ ∧ c ∉ f '' closedBall a r := by
    by_contra! hall
    exact hno (mem_interior_iff_mem_nhds.2
      (Metric.mem_nhds_iff.2 ⟨ρ, hρ, fun c hc => hall c (mem_ball.1 hc)⟩))
  have hfK : IsCompact (f '' closedBall a r) := hK.image_of_continuousOn hc
  have hS1c : IsCompact (f '' closedBall a r ∩ {y | ρ ≤ dist y c}) :=
    hfK.inter_right (isClosed_le continuous_const (continuous_id.dist continuous_const))
  have hSc : IsCompact ((f '' closedBall a r ∩ {y | ρ ≤ dist y c}) ∪ sphere c ρ) :=
    hS1c.union (isCompact_sphere c ρ)

  have hS1pos : ∀ y ∈ f '' closedBall a r ∩ {y | ρ ≤ dist y c}, 0 < dist (G y) a := by
    rintro _ ⟨⟨x, hx, rfl⟩, hy⟩
    rw [hGf x hx, dist_pos]
    intro hxa
    subst hxa
    rw [mem_ofPred_eq, dist_comm] at hy
    linarith
  obtain ⟨δ0, hδ0, hδ0le⟩ :=
    exists_pos_le hS1c (G.continuous.dist continuous_const).continuousOn hS1pos
  obtain ⟨δ, hδ, hδδ0, hδr⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ≤ r / 4 :=
    ⟨min δ0 (r / 4), lt_min hδ0 (by positivity), min_le_left _ _, min_le_right _ _⟩

  obtain ⟨P, hPd, hPS⟩ := exists_differentiable_near hSc G G.continuous (half_pos hδ)
  obtain ⟨v, hv, hPv⟩ := exists_small_avoid hPd c a hρ (half_pos hδ)
  have hQG : ∀ y ∈ (f '' closedBall a r ∩ {y | ρ ≤ dist y c}) ∪ sphere c ρ,
      ‖P y - v - G y‖ < δ := fun y hy => by
    have h1 := hPS y hy
    calc ‖P y - v - G y‖ = ‖(P y - G y) - v‖ := by congr 1; abel
      _ ≤ ‖P y - G y‖ + ‖v‖ := norm_sub_le _ _
      _ < δ / 2 + δ / 2 := add_lt_add h1 hv
      _ = δ := add_halves δ
  have hQne : ∀ y ∈ (f '' closedBall a r ∩ {y | ρ ≤ dist y c}) ∪ sphere c ρ, P y - v ≠ a := by
    rintro y (hy | hy) hQa
    · have h1 := hQG y (Or.inl hy)
      have h2 := hδ0le y hy
      rw [hQa, norm_sub_rev] at h1
      rw [dist_eq_norm] at h2
      linarith
    · exact hPv y hy (eq_add_of_sub_eq hQa)

  have hfc : ∀ x ∈ closedBall a r, f x ≠ c := fun x hx h => hcK ⟨x, hx, h⟩
  have hΦS : ∀ x ∈ closedBall a r,
      radialPush c ρ (f x) ∈ (f '' closedBall a r ∩ {y | ρ ≤ dist y c}) ∪ sphere c ρ := by
    intro x hx
    by_cases hle : ρ ≤ dist (f x) c
    · rw [radialPush_of_le hρ hle]
      exact Or.inl ⟨⟨x, hx, rfl⟩, hle⟩
    · exact Or.inr (radialPush_mem_sphere (not_le.1 hle) (hfc x hx))
  have hΦc : ContinuousOn (fun x => radialPush c ρ (f x)) (closedBall a r) :=
    (continuousOn_radialPush c ρ).comp hc (fun x hx => hfc x hx)
  have hPΦ : ContinuousOn (fun x => P (radialPush c ρ (f x))) (closedBall a r) :=
    hPd.continuous.comp_continuousOn hΦc
  have hH : ContinuousOn (fun x => x - (P (radialPush c ρ (f x)) - v - a)) (closedBall a r) := by
    have h1 := (hPΦ.sub (continuousOn_const (c := v))).sub (continuousOn_const (c := a))
    exact continuousOn_id.sub h1

  obtain ⟨x, hxK, hfix⟩ := brouwer_closedBall hB (a := a) hr
    (h := fun x => x - (P (radialPush c ρ (f x)) - v - a)) hH (by
      intro x hx
      have hGx : G (f x) = x := hGf x hx
      rw [mem_closedBall, dist_eq_norm]
      show ‖x - (P (radialPush c ρ (f x)) - v - a) - a‖ ≤ r
      by_cases hle : ρ ≤ dist (f x) c
      · rw [radialPush_of_le hρ hle]
        have h1 := hQG (f x) (Or.inl ⟨⟨x, hx, rfl⟩, hle⟩)
        rw [hGx] at h1
        calc ‖x - (P (f x) - v - a) - a‖ = ‖-(P (f x) - v - x)‖ := by congr 1; abel
          _ = ‖P (f x) - v - x‖ := norm_neg _
          _ ≤ r := by linarith
      · have hzS := radialPush_mem_sphere (not_le.1 hle) (hfc x hx)
        have hxa : dist x a < r / 4 := by
          rw [← hGx]
          apply hGnear
          calc dist (f x) (f a) ≤ dist (f x) c + dist c (f a) := dist_triangle _ _ _
            _ ≤ 2 * ρ := by linarith [not_le.1 hle]
        generalize radialPush c ρ (f x) = z at hzS ⊢
        have h1 := hQG z (Or.inr hzS)
        have hza : dist (G z) a < r / 4 := by
          apply hGnear
          have hzc : dist z c = ρ := mem_sphere.mp hzS
          calc dist z (f a) ≤ dist z c + dist c (f a) := dist_triangle _ _ _
            _ ≤ 2 * ρ := by linarith
        rw [dist_eq_norm] at hxa hza
        calc ‖x - (P z - v - a) - a‖ = ‖(x - a) - (P z - v - G z) - (G z - a)‖ := by congr 1; abel
          _ ≤ ‖(x - a) - (P z - v - G z)‖ + ‖G z - a‖ := norm_sub_le _ _
          _ ≤ ‖x - a‖ + ‖P z - v - G z‖ + ‖G z - a‖ := by
            gcongr
            exact norm_sub_le _ _
          _ ≤ r := by linarith)
  exact hQne _ (hΦS x hxK) (sub_eq_zero.mp (sub_eq_self.mp hfix))

theorem proof (hB : BrouwerFixedPoint.Statement) : InvarianceOfDomain.Statement := by
  intro n U f hU hc hi
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU x hx
  have hsub : closedBall x (r / 2) ⊆ U := (closedBall_subset_ball (half_lt_self hr)).trans hball
  have h := mem_interior_image hB (half_pos hr) (hc.mono hsub) (hi.mono hsub)
  exact Filter.mem_of_superset (mem_interior_iff_mem_nhds.mp h)
    (Set.image_mono hsub)

end InvarianceOfDomain

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PProperOpenProjectionCover
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

theorem subset_closure_nonvanishing_of_open {σ : Type} [Fintype σ] {Y : Set (σ → ℂ)} {d : ℕ}
    {A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)} {D : Set (Fin d → ℂ)} {δ : (Fin d → ℂ) → ℂ}
    (hDc : IsPreconnected D) (hmaps : Set.MapsTo A Y D)
    (hopen : ∀ x ∈ Y, ∀ V ∈ 𝓝 x, A '' (Y ∩ V) ∈ 𝓝 (A x))
    (hδ : AnalyticOnNhd ℂ δ D) (hne : ∃ y ∈ D, δ y ≠ 0) :
    Y ⊆ closure {x | x ∈ Y ∧ δ (A x) ≠ 0} := by
  obtain ⟨y₁, hy₁D, hy₁⟩ := hne
  intro x hx
  rw [mem_closure_iff_nhds]
  intro V hV
  by_contra hempty
  have hzero : δ =ᶠ[𝓝 (A x)] 0 := by
    filter_upwards [hopen x hx V hV] with y hy
    obtain ⟨x', ⟨hx'Y, hx'V⟩, rfl⟩ := hy
    by_contra h0
    exact hempty ⟨x', hx'V, hx'Y, h0⟩
  exact hy₁ (hδ.eqOn_zero_of_preconnected_of_eventuallyEq_zero hDc (hmaps hx) hzero hy₁D)

theorem ProperOpenProjectionCover.proof (hbranch : ProperOpenProjectionBranchLocus.Statement)
    (hcount : UnbranchedProperCountConstant.Statement) : ProperOpenProjectionCover.Statement := by
  intro σ _ X B k f d A D hB hf hXB hD hDc hDne hmaps hprop hopen
  obtain ⟨δ, hδ, hne, hsec⟩ := hbranch σ X B k f d A D hB hf hXB hD hDc hDne hmaps hprop hopen
  obtain ⟨N, hN⟩ := hcount σ (X ∩ B) d A D δ hD hDc hmaps hprop hδ (fun x hx hx0 => by
    obtain ⟨O, V, g, hO, hV, hxV, hg, hAg, hXV⟩ := hsec x hx hx0
    exact ⟨O, V, g, hO, hV, hxV, hg.continuousOn, hAg, hXV⟩)
  exact ⟨δ, N, hδ, hne, hN, hsec, subset_closure_nonvanishing_of_open hDc hmaps hopen hδ hne⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

