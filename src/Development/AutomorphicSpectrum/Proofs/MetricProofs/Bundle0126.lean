import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0122
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.NonemptyComponentModel
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle0001
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0019
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0118
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0092
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0100
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FibreDensityIndependentProjection
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.Bundle0001
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.SheetDensityEqSetSheetDensity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0018
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0039
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0049
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0025
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0014
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0038
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0037
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0014
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDensityNonnegOffNullSet
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0123
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0042
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0044
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0059
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0041
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0023

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ChartLocalAnalyticTrivialization
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp

theorem exists_analytic_param {A B E : Type} [NormedAddCommGroup A] [NormedSpace ℂ A] [FiniteDimensional ℂ A]
    [NormedAddCommGroup B] [NormedSpace ℂ B] [FiniteDimensional ℂ B]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {Φ : E → A} {G : A → B} {e₀ : E}
    (hΦ : AnalyticAt ℂ Φ e₀) (hG : AnalyticAt ℂ G (Φ e₀))
    (hinj : ∀ e, fderiv ℂ Φ e₀ e = 0 → e = 0)
    (hker : ∀ w, fderiv ℂ G (Φ e₀) w = 0 → ∃ e, w = fderiv ℂ Φ e₀ e)
    (hzero : ∀ᶠ e in 𝓝 e₀, G (Φ e) = 0) {U : Set E} (hU : U ∈ 𝓝 e₀) :
    ∃ (V : Set A) (S : A → E), IsOpen V ∧ Φ e₀ ∈ V ∧ AnalyticOnNhd ℂ S V ∧ S (Φ e₀) = e₀ ∧
      ∀ z ∈ V, G z = 0 → S z ∈ U ∧ z = Φ (S z) := by
  set L := fderiv ℂ Φ e₀ with hL
  have hLi : LinearMap.ker (L : E →ₗ[ℂ] A) = ⊥ := LinearMap.ker_eq_bot'.mpr hinj
  obtain ⟨p, hp⟩ := (L : E →ₗ[ℂ] A).exists_leftInverse_of_injective hLi
  let π : A →L[ℂ] E := LinearMap.toContinuousLinearMap p
  have hπ : ∀ e, π (L e) = e := fun e => LinearMap.congr_fun hp e

  let h : E → E := fun e => π (Φ e)
  have hh : HasStrictFDerivAt h ((ContinuousLinearEquiv.refl ℂ E : E ≃L[ℂ] E) : E →L[ℂ] E) e₀ := by
    have h1 := π.hasStrictFDerivAt.comp e₀ hΦ.hasStrictFDerivAt
    refine h1.congr_fderiv ?_
    ext e
    simp [hπ, ← hL]
  let Φ₁ := hh.toOpenPartialHomeomorph h
  have hΦ₁ : ∀ e, Φ₁ e = π (Φ e) := fun e => rfl
  have hs₁ : e₀ ∈ Φ₁.source := hh.mem_toOpenPartialHomeomorph_source
  have han₁ : AnalyticAt ℂ Φ₁ e₀ := (π.analyticAt _).comp hΦ
  have hsymm : AnalyticAt ℂ Φ₁.symm (Φ₁ e₀) :=
    Φ₁.analyticAt_symm' (i := ContinuousLinearEquiv.refl ℂ E) hs₁ han₁ hh.hasFDerivAt.fderiv
  have hback : Φ₁.symm (Φ₁ e₀) = e₀ := Φ₁.left_inv hs₁

  let M : A →L[ℂ] B × E := (fderiv ℂ G (Φ e₀)).prod π
  have hMi : LinearMap.ker (M : A →ₗ[ℂ] B × E) = ⊥ := by
    refine LinearMap.ker_eq_bot'.mpr fun w hw => ?_
    have h1 : fderiv ℂ G (Φ e₀) w = 0 := congrArg Prod.fst hw
    have h2 : π w = 0 := congrArg Prod.snd hw
    obtain ⟨e, rfl⟩ := hker w h1
    rw [hπ] at h2
    rw [h2, map_zero]
  obtain ⟨q, hq⟩ := (M : A →ₗ[ℂ] B × E).exists_leftInverse_of_injective hMi
  let R : B × E →L[ℂ] A := LinearMap.toContinuousLinearMap q
  have hR : ∀ w, R (M w) = w := fun w => LinearMap.congr_fun hq w
  let Ξ : A → A := fun z => R (G z, π z)
  have hΞ : HasStrictFDerivAt Ξ ((ContinuousLinearEquiv.refl ℂ A : A ≃L[ℂ] A) : A →L[ℂ] A) (Φ e₀) := by
    have h1 := R.hasStrictFDerivAt.comp (Φ e₀) (hG.hasStrictFDerivAt.prodMk π.hasStrictFDerivAt)
    refine h1.congr_fderiv ?_
    ext w
    exact hR w
  let Φ₂ := hΞ.toOpenPartialHomeomorph Ξ
  have hs₂ : Φ e₀ ∈ Φ₂.source := hΞ.mem_toOpenPartialHomeomorph_source

  have hN : ∀ᶠ e in 𝓝 e₀, e ∈ U ∧ G (Φ e) = 0 ∧ Φ e ∈ Φ₂.source :=
    (Filter.eventually_of_mem hU fun _ h => h).and (hzero.and
      (hΦ.continuousAt.eventually_mem (Φ₂.open_source.mem_nhds hs₂)))
  have hc₁ : ContinuousAt Φ₁.symm (Φ₁ e₀) := hsymm.continuousAt
  have hN' : ∀ᶠ x in 𝓝 (Φ₁ e₀), Φ₁.symm x ∈ U ∧ G (Φ (Φ₁.symm x)) = 0 ∧ Φ (Φ₁.symm x) ∈ Φ₂.source := by
    have := hc₁.tendsto.eventually (by rw [hback]; exact hN)
    exact this
  have ht₁ : Φ₁ e₀ ∈ Φ₁.target := Φ₁.map_source hs₁
  have hP : ∀ᶠ x in 𝓝 (Φ₁ e₀), (Φ₁.symm x ∈ U ∧ G (Φ (Φ₁.symm x)) = 0 ∧ Φ (Φ₁.symm x) ∈ Φ₂.source) ∧
      x ∈ Φ₁.target ∧ AnalyticAt ℂ Φ₁.symm x :=
    hN'.and ((Φ₁.open_target.mem_nhds ht₁ |> Filter.eventually_of_mem <| fun _ h => h).and hsymm.eventually_analyticAt)
  have hπc : Tendsto π (𝓝 (Φ e₀)) (𝓝 (Φ₁ e₀)) := π.continuous.tendsto _
  have hQ : ∀ᶠ z in 𝓝 (Φ e₀), ((Φ₁.symm (π z) ∈ U ∧ G (Φ (Φ₁.symm (π z))) = 0 ∧ Φ (Φ₁.symm (π z)) ∈ Φ₂.source) ∧
      π z ∈ Φ₁.target ∧ AnalyticAt ℂ Φ₁.symm (π z)) ∧ z ∈ Φ₂.source :=
    (hπc.eventually hP).and (Φ₂.open_source.mem_nhds hs₂ |> Filter.eventually_of_mem <| fun _ h => h)
  obtain ⟨V, hVs, hVo, hV0⟩ := mem_nhds_iff.mp hQ
  refine ⟨V, fun z => Φ₁.symm (π z), hVo, hV0, ?_, hback, ?_⟩
  · intro z hz
    exact AnalyticAt.comp (f := fun z => π z) (hVs hz).1.2.2 (π.analyticAt z)
  · intro z hz hGz
    obtain ⟨⟨⟨hU', hG', hsrc⟩, htgt, -⟩, hzs⟩ := hVs hz
    refine ⟨hU', ?_⟩
    have h1 : π (Φ (Φ₁.symm (π z))) = π z := Φ₁.right_inv htgt
    refine Φ₂.injOn hzs hsrc ?_
    show R (G z, π z) = R (G _, π _)
    rw [hGz, hG', h1]

open MvPolynomial in

theorem exists_chart_inverse {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {P : Ideal (MRing J)}
    (hP : IsMultiHomogIdeal P) {n : ℕ} {Bd : Set ((Σ k, J k) → ℂ)} (χ : SncChart P n Bd) {t₀ : Fin n → ℂ}
    (ht₀ : t₀ ∈ Metric.ball (0 : Fin n → ℂ) 1)
    (htan : ∀ v, IsConeTangent (Int.castRingHom ℂ) P (χ.γ t₀) v →
      ∃ (u : Fin n → ℂ) (c : K → ℂ), v = fderiv ℂ χ.γ t₀ u + torusSmul c (χ.γ t₀)) :
    ∃ (V : Set ((Σ k, J k) → ℂ)) (T : ((Σ k, J k) → ℂ) → Fin n → ℂ), IsOpen V ∧ χ.γ t₀ ∈ V ∧
      AnalyticOnNhd ℂ T V ∧ T (χ.γ t₀) = t₀ ∧ ∀ z ∈ V ∩ mcPts P, T z ∈ Metric.ball 0 1 ∧
        ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ z = torusSmul c (χ.γ (T z)) := by
  classical
  set z₀ := χ.γ t₀ with hz₀
  let σ : ℤ →+* ℂ := Int.castRingHom ℂ

  let ell : MRing J → Module.Dual ℂ ((Σ k, J k) → ℂ) := fun f =>
    ∑ i, eval z₀ (pderiv i (map σ f)) • LinearMap.proj i
  have hell : ∀ f w, ell f w = ∑ i, eval z₀ (pderiv i (map σ f)) * w i := fun f w => by
    simp [ell, LinearMap.sum_apply]
  obtain ⟨s, hsub, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset (ell '' (P : Set (MRing J)))).1
    (IsNoetherian.noetherian (Submodule.span ℂ (ell '' (P : Set (MRing J)))))
  have hch : ∀ l : s, ∃ f ∈ P, ell f = l.1 := fun l => by
    obtain ⟨f, hf, h⟩ := hsub l.2
    exact ⟨f, hf, h⟩
  choose f hfP hfl using hch
  let g : s → MvPolynomial (Σ k, J k) ℂ := fun l => map σ (f l)
  let G : ((Σ k, J k) → ℂ) → s → ℂ := fun z l => eval z (g l)
  let Φ : (K → ℂ) × (Fin n → ℂ) → (Σ k, J k) → ℂ := fun e => torusSmul e.1 (χ.γ e.2)
  let e₀ : (K → ℂ) × (Fin n → ℂ) := (1, t₀)
  have hΦ₀ : Φ e₀ = z₀ := by
    funext p
    simp [Φ, e₀, torusSmul, hz₀]
  have hγ : AnalyticAt ℂ χ.γ t₀ := χ.analytic t₀ ht₀
  have hΦan : AnalyticAt ℂ Φ e₀ := by
    refine AnalyticAt.pi fun p => ?_
    have h1 : AnalyticAt ℂ (fun e : (K → ℂ) × (Fin n → ℂ) => e.1 p.1) e₀ :=
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : K => ℂ) p.1).comp
        (ContinuousLinearMap.fst ℂ (K → ℂ) (Fin n → ℂ))).analyticAt e₀
    have h2 : AnalyticAt ℂ (fun e : (K → ℂ) × (Fin n → ℂ) => χ.γ e.2) e₀ :=
      AnalyticAt.comp (f := fun e : (K → ℂ) × (Fin n → ℂ) => e.2) hγ
        ((ContinuousLinearMap.snd ℂ (K → ℂ) (Fin n → ℂ)).analyticAt e₀)
    have h3 : AnalyticAt ℂ (fun e : (K → ℂ) × (Fin n → ℂ) => χ.γ e.2 p) e₀ :=
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, J k) => ℂ) p).analyticAt _).comp h2
    exact h1.mul h3
  have hGan : AnalyticAt ℂ G (Φ e₀) := by
    refine AnalyticAt.pi fun l => ?_
    exact AnalyticOnNhd.eval_mvPolynomial (𝕜 := ℂ) (g l) _ (Set.mem_univ _)

  have hdΦ : ∀ c u, fderiv ℂ Φ e₀ (c, u) = fderiv ℂ χ.γ t₀ u + torusSmul c z₀ := by
    have hγd := hγ.differentiableAt.hasFDerivAt
    have hD : HasFDerivAt Φ (ContinuousLinearMap.pi fun p : (Σ k, J k) =>
        (1 : ℂ) • ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, J k) => ℂ) p).comp
            ((fderiv ℂ χ.γ t₀).comp (ContinuousLinearMap.snd ℂ (K → ℂ) (Fin n → ℂ)))) +
          z₀ p • ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : K => ℂ) p.1).comp
            (ContinuousLinearMap.fst ℂ (K → ℂ) (Fin n → ℂ)))) e₀ := by
      refine hasFDerivAt_pi.2 fun p => ?_
      have h1 : HasFDerivAt (fun e : (K → ℂ) × (Fin n → ℂ) => e.1 p.1)
          ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : K => ℂ) p.1).comp
            (ContinuousLinearMap.fst ℂ (K → ℂ) (Fin n → ℂ))) e₀ :=
        ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : K => ℂ) p.1).comp
            (ContinuousLinearMap.fst ℂ (K → ℂ) (Fin n → ℂ))).hasFDerivAt
      have h2 : HasFDerivAt (fun e : (K → ℂ) × (Fin n → ℂ) => χ.γ e.2)
          ((fderiv ℂ χ.γ t₀).comp (ContinuousLinearMap.snd ℂ (K → ℂ) (Fin n → ℂ))) e₀ :=
        HasFDerivAt.comp e₀ (f := fun e : (K → ℂ) × (Fin n → ℂ) => e.2) hγd
          (ContinuousLinearMap.snd ℂ (K → ℂ) (Fin n → ℂ)).hasFDerivAt
      have h3 : HasFDerivAt (fun e : (K → ℂ) × (Fin n → ℂ) => χ.γ e.2 p)
          ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, J k) => ℂ) p).comp
            ((fderiv ℂ χ.γ t₀).comp (ContinuousLinearMap.snd ℂ (K → ℂ) (Fin n → ℂ)))) e₀ :=
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, J k) => ℂ) p).hasFDerivAt.comp e₀ h2
      refine (h1.mul h3).congr_fderiv ?_
      simp [e₀, hz₀]
    intro c u
    rw [hD.fderiv]
    funext p
    simp [torusSmul, mul_comm]

  have hdG : ∀ w l, fderiv ℂ G (Φ e₀) w l = ell (f l) w := by
    have hD : HasFDerivAt G (ContinuousLinearMap.pi fun l : s =>
        ∑ i, eval (Φ e₀) (pderiv i (g l)) • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, J k) => ℂ) i)
        (Φ e₀) := hasFDerivAt_pi.2 fun l => hasFDerivAt_eval (g l) (Φ e₀)
    intro w l
    rw [hD.fderiv, hell, hΦ₀]
    simp [g]
  have hinj : ∀ e, fderiv ℂ Φ e₀ e = 0 → e = 0 := by
    rintro ⟨c, u⟩ h
    rw [hdΦ] at h
    have hu : u = 0 := by
      refine χ.immersion t₀ ht₀ u ⟨fun k => - c k, ?_⟩
      funext p
      have := congrFun h p
      simp only [Pi.add_apply, Pi.zero_apply, torusSmul] at this ⊢
      rw [← hz₀]
      linear_combination this
    subst hu
    have hc : c = 0 := by
      funext k
      obtain ⟨i, hi⟩ := (χ.mem t₀ ht₀).1 k
      have := congrFun h ⟨k, i⟩
      simp only [map_zero, Pi.add_apply, Pi.zero_apply, zero_add, torusSmul] at this
      exact (mul_eq_zero.mp this).resolve_right hi
    simp [hc]
  have hker : ∀ w, fderiv ℂ G (Φ e₀) w = 0 → ∃ e, w = fderiv ℂ Φ e₀ e := by
    intro w hw
    have hs0 : ∀ l ∈ Submodule.span ℂ (s : Set (Module.Dual ℂ ((Σ k, J k) → ℂ))), l w = 0 := by
      intro l hl
      induction hl using Submodule.span_induction with
      | mem x hx =>
        have := congrFun hw ⟨x, hx⟩
        rw [hdG, hfl] at this
        exact this
      | zero => simp
      | add x y _ _ hx hy => simp [hx, hy]
      | smul a x _ hx => simp [hx]
    have htv : IsConeTangent (Int.castRingHom ℂ) P z₀ w := by
      intro q hq
      have : ell q ∈ Submodule.span ℂ (s : Set (Module.Dual ℂ ((Σ k, J k) → ℂ))) := by
        rw [← hspan]
        exact Submodule.subset_span ⟨q, hq, rfl⟩
      have h0 := hs0 _ this
      rw [hell] at h0
      exact h0
    obtain ⟨u, c, hv⟩ := htan w htv
    exact ⟨(c, u), by rw [hdΦ, hv]⟩
  have hopen : ∀ᶠ e : (K → ℂ) × (Fin n → ℂ) in 𝓝 e₀, (∀ k, e.1 k ≠ 0) ∧ e.2 ∈ Metric.ball (0 : Fin n → ℂ) 1 := by
    refine Filter.Eventually.and (eventually_all.2 fun k => ?_) ?_
    · have hc : ContinuousAt (fun e : (K → ℂ) × (Fin n → ℂ) => e.1 k) e₀ := by fun_prop
      exact hc.eventually_ne (by simp [e₀])
    · have hc : ContinuousAt (fun e : (K → ℂ) × (Fin n → ℂ) => e.2) e₀ := by fun_prop
      exact hc.eventually_mem (Metric.isOpen_ball.mem_nhds ht₀)
  have hzero : ∀ᶠ e in 𝓝 e₀, G (Φ e) = 0 := by
    filter_upwards [hopen] with e he
    funext l
    exact (mcPts_smul hP e.1 he.1 (χ.mem e.2 he.2)).2 (f l) (hfP l)
  obtain ⟨V, S, hVo, hV0, hSan, hS0, hS⟩ := exists_analytic_param hΦan hGan hinj hker hzero hopen
  rw [hΦ₀] at hV0 hS0
  refine ⟨V, fun z => (S z).2, hVo, hV0, ?_, by simp [hS0, e₀], ?_⟩
  · intro z hz
    exact ((ContinuousLinearMap.snd ℂ (K → ℂ) (Fin n → ℂ)).analyticAt _).comp (hSan z hz)
  · rintro z ⟨hzV, hzP⟩
    have hGz : G z = 0 := by
      funext l
      exact hzP.2 (f l) (hfP l)
    obtain ⟨hU, hz⟩ := hS z hzV hGz
    exact ⟨hU.2, (S z).1, hU.1, hz⟩

theorem chart_torus_open : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (a : Fin D.nCharts), ∀ t₀ ∈ Metric.ball (0 : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) 1, ∃ (V : Set ((Σ k, J k) → ℂ)) (T : ((Σ k, J k) → ℂ) → Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ), IsOpen V ∧ (D.chart a).γ t₀ ∈ V ∧ AnalyticOnNhd ℂ T V ∧ T ((D.chart a).γ t₀) = t₀ ∧ ∀ z ∈ V ∩ mcPts (mCoordIdeal D.y), T z ∈ Metric.ball 0 1 ∧ ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ z = torusSmul c ((D.chart a).γ (T z)) := by
  intro K _ J _ II Ψ _ Ω _ _ W _ _ D a t₀ ht₀
  exact exists_chart_inverse D.arith.2.1.2.1 (D.chart a) ht₀
    (GlobalTheory.T.cone_tangent_lift_in_chart K J II Ψ Ω W D a t₀ ht₀)

end GlobalTheory.CompanionTheory.Ar.Cusp
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsCompactifiedModel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.exists_compactified_model : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W), Nonempty (XModel D) := by
  first | exact @LevelTowerAlt.nonempty_component_model | exact LevelTowerAlt.nonempty_component_model
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExpandMIntStatement
section
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixed_integral_inclusion_exclusion_alt : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (U : Set X) (P : Fin e → LocPot X) (f : Fin e → X → ℝ) (Θ : LocPot X) (g : X → ℝ), IsOpen U → (∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Uᶜ) = 0) → (∀ i, IsPotential A (P i)) → IsPotential A Θ → (∀ i, A.SmoothOn U (f i)) → (∀ T : Finset (Fin e), MIntegrable A (fun i => (if i ∈ T then P i else LocPot.ofFun 0) + LocPot.ofFun (if i ∈ T then f i else 0) + Θ) g) → MIntegrable A (fun i => P i + LocPot.ofFun (f i)) g ∧ mInt A (fun i => P i + LocPot.ofFun (f i)) g = ∑ T : Finset (Fin e), (-1 : ℝ) ^ (e - T.card) * mInt A (fun i => (if i ∈ T then P i else LocPot.ofFun 0) + LocPot.ofFun (if i ∈ T then f i else 0) + Θ) g := by
  first | exact @GlobalTheory.CompanionTheory.Metric.ExpandMInt.expand_mInt | exact GlobalTheory.CompanionTheory.Metric.ExpandMInt.expand_mInt | (intros; apply GlobalTheory.CompanionTheory.Metric.ExpandMInt.expand_mInt <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FibreDensityIndependentProjectionStatement
section
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_density_independent_projection : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e : ℕ) (Ψ Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (L : Fin e → HermLine ι) (g : ((Σ k, ι k) → ℂ) → ℝ) (z : (Σ k, ι k) → ℂ),
    IsCxVar Q e → IsSetGoodProj (conePts Q) Ψ → IsSetGoodProj (conePts Q) Ψ' →
    (∀ j, IsSmoothHerm (L j)) → Measurable g →
    (∀ (c : K → ℂ) (z' : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → g (fun p => c p.1 * z' p) = g z') →
    z ∈ conePts Q → cxSimple (conePts Q) Ψ ((Ψ (segre z) 0)⁻¹ • segre z) →
    cxSimple (conePts Q) Ψ' ((Ψ' (segre z) 0)⁻¹ • segre z) →
      ∃ W : Set ((Σ k, ι k) → ℂ), IsOpen W ∧ z ∈ W ∧
        (∀ (c : K → ℂ) (z' : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → ((fun p => c p.1 * z' p) ∈ W ↔ z' ∈ W)) ∧
        ∀ E : Set ((Σ k, ι k) → ℂ), MeasurableSet E →
          (∀ (c : K → ℂ) (z' : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → ((fun p => c p.1 * z' p) ∈ E ↔ z' ∈ E)) →
          E ⊆ W →
            ∫⁻ y, ENNReal.ofReal (cxPosDens (conePts Q) Ψ (pot L) (E.indicator g) y) =
              ∫⁻ y, ENNReal.ofReal (cxPosDens (conePts Q) Ψ' (pot L) (E.indicator g) y) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Pub.CxPosLocal.cxPosPart_local | exact GlobalTheory.CompanionTheory.Ar.Pub.CxPosLocal.cxPosPart_local | (intros; apply GlobalTheory.CompanionTheory.Ar.Pub.CxPosLocal.cxPosPart_local <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FiniteFibresOfAnalyticLocalDiffeo
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.Giv.Push

open LintegralFibSum

theorem lintegral_absFibre_eq {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Φ : Fin e → LocPot X) (q : X → Fin e → ℂ) (S : Set X) (G : X → ℝ)
    (hS : ∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' S) = 0)
    (hq : ∀ x ∉ S, ∀ j, x ∈ (A.chart j).source →
      AnalyticAt ℂ (q ∘ (A.chart j).symm) (A.chart j x) ∧
        LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) (A.chart j x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0)
    (hfin : ∀ y, (q ⁻¹' {y} \ S).Finite)
    (hsm : ∀ x ∉ S, ∀ i k, x ∈ (A.chart k).source →
      ContDiffAt ℝ 2 ((Φ i).φ x ∘ (A.chart k).symm) (A.chart k x))
    (hGm : ∀ j, AEStronglyMeasurable (fun u => G ((A.chart j).symm u) * locDens A Φ j u)
      (volume.restrict (A.chart j).target))
    (Pt : ChartPartition A) :
    ∫⁻ y, ENNReal.ofReal (∑ᶠ x ∈ q ⁻¹' {y} \ S, |G x * pushDens A Φ q x|) =
      ∑ j, ∫⁻ u in (A.chart j).target, ENNReal.ofReal
        |Pt.χ j ((A.chart j).symm u) * G ((A.chart j).symm u) * locDens A Φ j u| := by
  classical
  set Qj : Fin A.n → (Fin e → ℂ) → (Fin e → ℂ) := fun j => q ∘ (A.chart j).symm with hQj
  set h : Fin A.n → (Fin e → ℂ) → ℝ := fun j u =>
    |Pt.χ j ((A.chart j).symm u) * G ((A.chart j).symm u) * locDens A Φ j u| with hh
  have hms : ∀ j, MeasurableSet (A.chart j).target := fun j => (A.chart j).open_target.measurableSet
  have hdiff : ∀ j (s : Set (Fin e → ℂ)), s ⊆ goodT A q j → volume s = 0 →
      volume (Qj j '' s) = 0 := by
    intro j s hs h0
    refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_ h0
    intro u hu
    exact ((hs hu).2.1.differentiableAt.restrictScalars ℝ).differentiableWithinAt
  have hN : ∀ j, volume (Qj j '' (goodT A q j ∩ (A.chart j).symm ⁻¹' S)) = 0 := fun j =>
    hdiff j _ Set.inter_subset_left
      (measure_mono_null (Set.inter_subset_inter_left _ fun u (hu : u ∈ goodT A q j) => hu.1) (hS j))
  have hTn : ∀ j, volume ((A.chart j).target \ goodT A q j) = 0 := fun j =>
    measure_mono_null (target_diff_goodT_subset A q S hq j) (hS j)
  have hgt : ∀ j, goodT A q j =ᵐ[volume] (A.chart j).target := by
    intro j
    refine ae_eq_set.mpr ⟨?_, hTn j⟩
    have : goodT A q j \ (A.chart j).target = ∅ := Set.diff_eq_empty.mpr fun u hu => hu.1
    rw [this]
    exact measure_empty
  have hAE : ∀ j, AEMeasurable (h j) (volume.restrict (A.chart j).target) := by
    intro j
    have hχ : ContinuousOn (fun u => Pt.χ j ((A.chart j).symm u)) (A.chart j).target := by
      have := (Pt.smooth j j).continuousOn
      rw [Set.preimage_univ, Set.inter_univ] at this
      exact this
    have h1 := hχ.aestronglyMeasurable (μ := volume) (hms j)
    have h2 := (h1.mul (hGm j)).norm
    refine h2.aemeasurable.congr (ae_of_all _ fun u => ?_)
    simp only [hh, Real.norm_eq_abs, Pi.mul_apply, mul_assoc]
  set h' : Fin A.n → (Fin e → ℂ) → ℝ := fun j u => |(hAE j).mk (h j) u| with hh'
  have hm' : ∀ j, Measurable (h' j) := fun j =>
    continuous_abs.measurable.comp (hAE j).measurable_mk
  have heq : ∀ j, ∀ᵐ u, u ∈ (A.chart j).target → h j u = h' j u := by
    intro j
    filter_upwards [(ae_restrict_iff' (hms j)).mp (hAE j).ae_eq_mk] with u hu ht
    have h0 : 0 ≤ h j u := abs_nonneg _
    show h j u = |(hAE j).mk (h j) u|
    rw [← hu ht, abs_of_nonneg h0]
  have hD : ∀ j, volume (Qj j '' (goodT A q j ∩ {u | h j u ≠ h' j u})) = 0 := fun j =>
    hdiff j _ Set.inter_subset_left
      (measure_mono_null (t := {u | ¬ (u ∈ (A.chart j).target → h j u = h' j u)})
        (fun u hu hc => hu.2 (hc hu.1.1)) (ae_iff.mp (heq j)))
  have hfinj : ∀ j, ∀ᵐ y, (goodT A q j ∩ Qj j ⁻¹' {y}).Finite := by
    intro j
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp (hN j)] with y hy
    rw [show goodT A q j ∩ Qj j ⁻¹' {y} = _ from goodT_fibre_eq A q S hq j hy]
    exact ((hfin y).subset Set.inter_subset_right).image _
  have hlow : ∀ j, AEMeasurable (fun y => ENNReal.ofReal (fibSum (goodT A q j) (Qj j) (h' j) y)) ∧
      ∫⁻ y, ENNReal.ofReal (fibSum (goodT A q j) (Qj j) (h' j) y) =
        ∫⁻ u in goodT A q j, ENNReal.ofReal (h' j u) := fun j =>
    lintegral_fibSum_open (isOpen_goodT A q j) (fun u hu => hu.2) (fun u => abs_nonneg _)
      ((hm' j).comp measurable_subtype_coe) (hfinj j)
  have hsame : ∀ᵐ y, ∀ j, fibSum (goodT A q j) (Qj j) (h j) y =
      fibSum (goodT A q j) (Qj j) (h' j) y := by
    refine ae_all_iff.mpr fun j => ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp (hD j)] with y hy
    unfold fibSum
    refine finsum_mem_congr rfl fun u hu => ?_
    have : h j u = h' j u := by
      by_contra hne
      exact hy ⟨u, ⟨hu.1, hne⟩, hu.2⟩
    rw [this]
  have hterm : ∀ j x, x ∈ (A.chart j).source → x ∉ S →
      h j (A.chart j x) / jacN (q ∘ (A.chart j).symm) (A.chart j x) =
        Pt.χ j x * |G x * pushDens A Φ q x| := by
    intro j x hx hxS
    have hJ : 0 ≤ jacN (q ∘ (A.chart j).symm) (A.chart j x) := by unfold jacN; positivity
    have hd := locDens_div_jacN A Φ q S hq hsm j hx hxS
    calc h j (A.chart j x) / jacN (q ∘ (A.chart j).symm) (A.chart j x)
        = |Pt.χ j x * G x * (locDens A Φ j (A.chart j x) /
            jacN (q ∘ (A.chart j).symm) (A.chart j x))| := by
          simp only [hh, (A.chart j).left_inv hx]
          rw [← mul_div_assoc, abs_div, abs_of_nonneg hJ]
      _ = Pt.χ j x * |G x * pushDens A Φ q x| := by
          rw [hd, mul_assoc, abs_mul, abs_of_nonneg (Pt.nonneg j x)]
  have hae := sum_fibSum_ae A q S hN hq hfin Pt h (fun x => |G x * pushDens A Φ q x|) hterm
  calc ∫⁻ y, ENNReal.ofReal (∑ᶠ x ∈ q ⁻¹' {y} \ S, |G x * pushDens A Φ q x|)
      = ∫⁻ y, ∑ j, ENNReal.ofReal (fibSum (goodT A q j) (Qj j) (h' j) y) := by
        refine lintegral_congr_ae ?_
        filter_upwards [hae, hsame] with y hy hs
        rw [← hy, ENNReal.ofReal_sum_of_nonneg fun j _ =>
          fibSum_nonneg _ _ (fun u => abs_nonneg _) y]
        exact Finset.sum_congr rfl fun j _ => by rw [hs j]
    _ = ∑ j, ∫⁻ u in goodT A q j, ENNReal.ofReal (h' j u) := by
        rw [lintegral_finsetSum' _ fun j _ => (hlow j).1]
        exact Finset.sum_congr rfl fun j _ => (hlow j).2
    _ = ∑ j, ∫⁻ u in (A.chart j).target, ENNReal.ofReal (h j u) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [setLIntegral_congr (hgt j)]
        refine lintegral_congr_ae ?_
        filter_upwards [(ae_restrict_iff' (hms j)).mpr (heq j)] with u hu
        rw [hu]

end GlobalTheory.CompanionTheory.Ar.Giv.Push
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticFirstStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_cover_arithmetic_first : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 2) → IsArithVar (mCoordIdeal y') (d + 2) → ∀ z ∈ mcPts (mCoordIdeal y'), ∃ (V : Set ((Σ k, ι' k) → ℂ)) (f : ((Σ k, ι' k) → ℂ) → (Σ k, ι k) → ℂ), IsOpen V ∧ z ∈ V ∧ AnalyticOnNhd ℂ f V ∧ ∀ z' ∈ V ∩ mcPts (mCoordIdeal y'), f z' ∈ mcPts (mCoordIdeal y) ∧ CovMap.IsImg Cv z' (f z') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.local_img | exact GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.local_img | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.local_img <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticNinthStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_arithVar_graph_of_flagCover : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 2) → IsArithVar (mCoordIdeal y') (d + 2) → ∃ Pt : Ideal (MRing (Sum.elim ι ι')), IsArithVar Pt (d + 2) ∧ imageZ inlV Pt = mCoordIdeal y ∧ imageZ inrV Pt = mCoordIdeal y' ∧ ∀ z ∈ mcPts (mCoordIdeal y'), ∀ w ∈ mcPts (mCoordIdeal y), CovMap.IsImg Cv z w → ∃ zt ∈ mcPts Pt, (∀ p, zt (inlV p) = w p) ∧ ∀ q, zt (inrV q) = z q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovGraph.graph_exists | exact GlobalTheory.CompanionTheory.Ar.PB.CovGraph.graph_exists | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovGraph.graph_exists <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgePotentialSmoothOffBoundaryStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_potential_smooth_off_boundary : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D), (∀ a, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => phMu Hd ((D.chart a).γ t)) (offBd D a)) ∧ ∀ a, ∀ t₀ : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ, ‖t₀‖ ≤ 1 / 2 → ∃ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ t ∈ offBd D a, ‖t - t₀‖ < ε → -(C * Real.log ((D.chart a).logR t)) ≤ phMu Hd ((D.chart a).γ t) ∧ phMu Hd ((D.chart a).γ t) ≤ C ∧ ‖fderiv ℝ (fun s => phMu Hd ((D.chart a).γ s)) t‖ ≤ C * (D.chart a).logR t ^ C * Real.exp ((D.chart a).logR t / 2) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.hodge_potential_smooth_off_boundary | exact GlobalTheory.CompanionTheory.Relay.hodge_potential_smooth_off_boundary | (intros; apply GlobalTheory.CompanionTheory.Relay.hodge_potential_smooth_off_boundary <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.PieceDegreeOfIntersectionAndResolutionStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.piece_degree_of_intersection_and_resolution : ArithIntersectionSystemStatement → ResExistsStatement → PtsIntegrableStatement → GroundTheory.Heights₂.Heights.HilbertSamuel.PieceDegree.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.pieceDegree | exact GlobalTheory.CompanionTheory.Ar.Giv.pieceDegree | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.pieceDegree <;> assumption)
end

