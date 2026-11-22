import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0125
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ExpRowsPf
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0003
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0001
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0002
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0077

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncChartLocalNormalForm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ChartGeo

open Topology

theorem inFrameDomain_eventually {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]
    (y : (Σ k, J k) → Ω) (cc : (k : K) → J k) (f : Ω) {z : (Σ k, J k) → ℂ} (hz : InFrameDomain y cc f z) :
    ∀ᶠ w in 𝓝 z, InFrameDomain y cc f w := by
  obtain ⟨hc, v, ⟨d, g, h, hg, hh, hy, hgh, hhz, rfl⟩, hv⟩ := hz
  have hgz : MvPolynomial.eval z (MvPolynomial.map (Int.castRingHom ℂ) g) ≠ 0 := by
    intro h0
    apply hv
    rw [h0, zero_div]
  have c1 : ∀ᶠ w in 𝓝 z, MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ) g) ≠ 0 :=
    (MvPolynomial.continuous_eval _).continuousAt.eventually_ne hgz
  have c2 : ∀ᶠ w in 𝓝 z, MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ) h) ≠ 0 :=
    (MvPolynomial.continuous_eval _).continuousAt.eventually_ne hhz
  have c3 : ∀ᶠ w : (Σ k, J k) → ℂ in 𝓝 z, ∀ k, w ⟨k, cc k⟩ ≠ 0 :=
    Filter.eventually_all.2 fun k => (continuous_apply _).continuousAt.eventually_ne (hc k)
  filter_upwards [c1, c2, c3] with w h1 h2 h3
  exact ⟨h3, _, ⟨d, g, h, hg, hh, hy, hgh, h2, rfl⟩, div_ne_zero h1 h2⟩

theorem exists_perm_prefix {n : ℕ} (A : Finset (Fin n)) :
    ∃ π : Equiv.Perm (Fin n), ∀ i, ((π i : Fin n) : ℕ) < A.card ↔ i ∈ A := by
  classical
  have hle : A.card ≤ n := by simpa using A.card_le_univ
  let e : {x // x ∈ A} ≃ {j : Fin n // (j : ℕ) < A.card} :=
    A.equivFin.trans (Fin.castLEOrderIso hle).toEquiv
  refine ⟨e.extendSubtype, fun i => ⟨fun h => ?_, fun h => e.extendSubtype_mem i h⟩⟩
  by_contra hi
  exact e.extendSubtype_not_mem i hi h

theorem recentre_apply {n : ℕ} (t₀ : Fin n → ℂ) (ρ : ℝ) (π : Equiv.Perm (Fin n)) (u : Fin n → ℂ) (i : Fin n) :
    HodgeMetric.recentre t₀ ρ π u i = t₀ i + (ρ : ℂ) * u (π i) := by
  simp [HodgeMetric.recentre]

theorem recentre_mem_ball {n : ℕ} {t₀ u : Fin n → ℂ} {ρ ε : ℝ} (hρ : 0 < ρ) (hε : ρ ≤ ε) (π : Equiv.Perm (Fin n))
    (hu : u ∈ Metric.ball (0 : Fin n → ℂ) 1) : HodgeMetric.recentre t₀ ρ π u ∈ Metric.ball t₀ ε := by
  rw [mem_ball_iff_norm]
  refine lt_of_lt_of_le ?_ hε
  rw [pi_norm_lt_iff hρ]
  intro i
  have h1 : ‖u (π i)‖ < 1 :=
    lt_of_le_of_lt (norm_le_pi_norm u (π i)) (by simpa using hu)
  have h2 : (HodgeMetric.recentre t₀ ρ π u - t₀) i = (ρ : ℂ) * u (π i) := by
    simp [recentre_apply]
  rw [h2, norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ.le]
  nlinarith

theorem exists_recentre_chart : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] (y : (Σ k, J k) → Ω) (P : Ideal (MRing J)) (n : ℕ) (Bd : Set ((Σ k, J k) → ℂ)) (χ : SncChart P n Bd) (t₀ : Fin n → ℂ) (cc : (k : K) → J k) (f : Ω), t₀ ∈ Metric.ball (0 : Fin n → ℂ) 1 → InFrameDomain y cc f (χ.γ t₀) → ∃ (a₀ : ℕ) (π : Equiv.Perm (Fin n)) (ρ₀ : ℝ), a₀ ≤ n ∧ 0 < ρ₀ ∧ ρ₀ ≤ 1 ∧ (∀ i : Fin n, (i : ℕ) < a₀ → ((π.symm i : Fin n) : ℕ) < χ.a ∧ t₀ (π.symm i) = 0) ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, HodgeMetric.recentre t₀ ρ π u ∈ Metric.ball (0 : Fin n → ℂ) 1 ∧ InFrameDomain y cc f (χ.γ (HodgeMetric.recentre t₀ ρ π u)) ∧ (χ.γ (HodgeMetric.recentre t₀ ρ π u) ∉ Bd ↔ u ∈ Flat.punct n a₀ 1) := by
  intro K _ J _ Ω _ y P n Bd χ t₀ cc f ht₀ hF
  classical
  let A : Finset (Fin n) := Finset.univ.filter (fun i => (i : ℕ) < χ.a ∧ t₀ i = 0)
  have hA : ∀ i, i ∈ A ↔ (i : ℕ) < χ.a ∧ t₀ i = 0 := fun i => by simp [A]
  obtain ⟨π, hπ⟩ := exists_perm_prefix A
  have hγ : ContinuousAt χ.γ t₀ := (χ.analytic t₀ ht₀).continuousAt
  have e1 : ∀ᶠ t in 𝓝 t₀, InFrameDomain y cc f (χ.γ t) :=
    hγ.eventually (inFrameDomain_eventually y cc f hF)
  have e2 : ∀ᶠ t : Fin n → ℂ in 𝓝 t₀, ∀ i : Fin n, t₀ i ≠ 0 → t i ≠ 0 := by
    refine Filter.eventually_all.2 fun i => ?_
    by_cases hi : t₀ i = 0
    · exact Filter.Eventually.of_forall fun t h => absurd hi h
    · filter_upwards [(continuous_apply i).continuousAt.eventually_ne hi] with t ht _ using ht
  have e3 : ∀ᶠ t in 𝓝 t₀, t ∈ Metric.ball (0 : Fin n → ℂ) 1 :=
    Metric.isOpen_ball.mem_nhds ht₀
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 (e1.and (e2.and e3))
  have hle : A.card ≤ n := by simpa using A.card_le_univ
  refine ⟨A.card, π, min ε 1, hle, lt_min hε one_pos, min_le_right _ _, fun i hi => ?_, fun ρ hρ hρ₀ u hu => ?_⟩
  · have : π.symm i ∈ A := (hπ _).1 (by simpa using hi)
    exact (hA _).1 this
  · obtain ⟨hF', hne, hb⟩ := hball _ (recentre_mem_ball hρ (hρ₀.trans (min_le_left _ _)) π hu)
    refine ⟨hb, hF', ?_⟩
    have hρc : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
    rw [χ.boundary _ hb]
    constructor
    · intro h
      refine ⟨by simpa using hu, fun j hj => fun h0 => h ?_⟩
      have hm : π.symm j ∈ A := (hπ _).1 (by simpa using hj)
      obtain ⟨h1, h2⟩ := (hA _).1 hm
      refine ⟨π.symm j, h1, ?_⟩
      rw [recentre_apply, h2]
      simp [h0]
    · rintro ⟨-, hu'⟩ ⟨i, hi, h0⟩
      by_cases hti : t₀ i = 0
      · have hm : i ∈ A := (hA i).2 ⟨hi, hti⟩
        have := hu' (π i) ((hπ i).2 hm)
        rw [recentre_apply, hti, zero_add] at h0
        exact (mul_ne_zero hρc this) h0
      · exact hne i hti h0

end GlobalTheory.CompanionTheory.Ar.ChartGeo
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TBijective
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.MonodromyBij

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open GroundTheory.Heights₂.Heights.Regular
open scoped Matrix ComplexOrder

def basePoint (n a : ℕ) : Fin n → ℂ := fun k => if k.val < a then -1 else 0

theorem basePoint_mem {n a : ℕ} (h : a ≤ n) : basePoint n a ∈ logCover h := by
  refine ⟨fun i => ?_, fun k hk => ?_⟩
  · have : (Fin.castLE h i).val < a := i.isLt
    simp [basePoint, this]
  · have : ¬ k.val < a := by omega
    simp [basePoint, this]

theorem shift_mem {n a : ℕ} (h : a ≤ n) (i : Fin a) :
    basePoint n a + Pi.single (Fin.castLE h i) (2 * Real.pi * Complex.I) ∈ logCover h := by
  refine ⟨fun j => ?_, fun k hk => ?_⟩
  · have hj : (Fin.castLE h j).val < a := j.isLt
    by_cases hji : Fin.castLE h j = Fin.castLE h i
    · simp [basePoint, hj, hji, Pi.single_apply]
    · simp [basePoint, hj, Pi.single_apply, hji]
  · have hk' : ¬ k.val < a := by omega
    have hne : k ≠ Fin.castLE h i := by
      intro e
      apply hk'
      rw [e]
      exact i.isLt
    simp [basePoint, hk', Pi.single_apply, hne]

theorem expCover_shift {n a : ℕ} (h : a ≤ n) (i : Fin a) (w : Fin n → ℂ) :
    expCover a (w + Pi.single (Fin.castLE h i) (2 * Real.pi * Complex.I)) = expCover a w := by
  funext k
  by_cases hk : k = Fin.castLE h i
  · subst hk
    have : (Fin.castLE h i).val < a := i.isLt
    simp [expCover, this, Complex.exp_add, Complex.exp_two_pi_mul_I]
  · simp [expCover, Pi.single_apply, hk]

theorem monodromy_preserves_form {n a g : ℕ} {Λ : Type} [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ) (i : Fin a) (x y : Λ) :
    L.E (L.T i x) (L.T i y) = L.E x y := by
  have hw := basePoint_mem L.a_le
  have h1 := L.im _ (shift_mem L.a_le i) x y
  rw [expCover_shift, L.mono i _ hw x, L.mono i _ hw y] at h1
  have h2 := L.im _ hw (L.T i x) (L.T i y)
  exact_mod_cast h2.symm.trans h1

theorem T_bijective : ∀ (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ) (i : Fin a),
    Function.Bijective (L.T i) := by
  intro n a g Λ _ L i
  haveI := L.fin
  let e : Λ ≃ₗ[ℤ] Module.Dual ℤ Λ := LinearEquiv.ofBijective L.E L.unimod
  let S : Λ →ₗ[ℤ] Λ := e.symm.toLinearMap ∘ₗ (L.T i).dualMap ∘ₗ e.toLinearMap
  have hS : ∀ x, S (L.T i x) = x := by
    intro x
    apply e.injective
    simp only [S, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    ext y
    simpa [e, LinearMap.dualMap_apply] using monodromy_preserves_form L i x y
  have hSsurj : Function.Surjective S := fun x => ⟨_, hS x⟩
  have hSinj : Function.Injective S := OrzechProperty.injective_of_surjective_endomorphism S hSsurj
  refine ⟨Function.LeftInverse.injective hS, fun y => ⟨S y, hSinj (hS (S y))⟩⟩

end GlobalTheory.CompanionTheory.Ar.Flat.MonodromyBij
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentVectorLiftsOpenImmersion
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ggeo.DOpen

theorem isDerivAt0_lift_of_isOpenImmersion :
    ∀ (A T : Scheme.{0}) (φ : A ⟶ T) [IsOpenImmersion φ] (g : ℕ) (W : (Fin g → ℂ) → (Sp ℂ ⟶ A))
      (y : Fin g → ℂ) (v : Sp (DualNumber ℂ) ⟶ T),
      IsDerivAt0 (fun x => W x ≫ φ) y v → ∃ v' : Sp (DualNumber ℂ) ⟶ A, v' ≫ φ = v ∧ IsDerivAt0 W y v' := by
  intro A T φ _ g W y v hv
  have hcl : IsLocalRing.closedPoint (DualNumber ℂ) ∈ v ⁻¹ᵁ φ.opensRange := by
    have h0 : ⊤ ≤ (W 0 ≫ φ) ⁻¹ᵁ φ.opensRange := fun p _ =>
      (show (W 0 ≫ φ) p ∈ Set.range φ from ⟨W 0 p, by simp⟩)
    have hpt : v (IsLocalRing.closedPoint _) = (W 0 ≫ φ) ReciprocityTheory.ChartRestriction.G.PullbackSections.cpt := by
      have hcomp : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = W 0 ≫ φ := hv.1
      rw [← hcomp, Scheme.Hom.comp_apply, spMap, Spec_closedPoint]
    show v (IsLocalRing.closedPoint _) ∈ φ.opensRange
    rw [hpt]
    exact h0 trivial
  have htop : ⊤ ≤ v ⁻¹ᵁ φ.opensRange := ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.dual_top_le _ hcl
  have hrange : Set.range v ⊆ Set.range φ := by
    rintro _ ⟨p, rfl⟩
    exact htop (show p ∈ (⊤ : (Sp (DualNumber ℂ)).Opens) from trivial)
  obtain ⟨v', rfl⟩ : ∃ v', v' ≫ φ = v := ⟨IsOpenImmersion.lift φ v hrange, IsOpenImmersion.lift_fac _ _ _⟩
  refine ⟨v', rfl, ?_, fun U' h f' => ?_⟩
  · rw [← cancel_mono φ, Category.assoc]
    exact hv.1
  · have key : ∀ (U : T.Opens) (U' : A.Opens) (e : φ ⁻¹ᵁ U = U') (h : ⊤ ≤ v' ⁻¹ᵁ U') (f : Γ(T, U)),
        TrivSqZeroExt.snd (show DualNumber ℂ from
          (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom.hom
            ((v'.appLE U' ⊤ h).hom (φ.appLE U U' e.ge f))) =
          fderiv ℂ (fun z => valAt' (W z) U' (φ.appLE U U' e.ge f)) 0 y := by
      intro U U' e h f
      subst e
      have hU : ⊤ ≤ (v' ≫ φ) ⁻¹ᵁ U := h
      have happ : φ.appLE U (φ ⁻¹ᵁ U) (le_refl (φ ⁻¹ᵁ U)) f = φ.app U f := by
        rw [Scheme.Hom.app_eq_appLE]
      have hfun : (fun z => valAt' (W z) (φ ⁻¹ᵁ U) (φ.app U f)) =
          fun z => valAt' ((fun x => W x ≫ φ) z) U f :=
        funext fun z => ReciprocityTheory.ChartRestriction.G.PullbackSections.valAt'_comp (W z) φ U f
      erw [happ]
      rw [hfun, ← hv.2 U hU f, Scheme.Hom.comp_appLE]
      rfl
    have hpre : φ ⁻¹ᵁ (φ ''ᵁ U') = U' := φ.preimage_image_eq U'
    have := key (φ ''ᵁ U') U' hpre h ((φ.appIso U').inv f')
    have hf : φ.appLE (φ ''ᵁ U') U' hpre.ge ((φ.appIso U').inv f') = f' := by
      have hh : φ.appLE (φ ''ᵁ U') U' hpre.ge = (φ.appIso U').hom := (Scheme.Hom.appIso_hom' φ U').symm
      rw [hh]
      exact ConcreteCategory.congr_hom (φ.appIso U').inv_hom_id f'
    rwa [hf] at this

end GlobalTheory.CompanionTheory.Ggeo.DOpen
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusKernelPrimeQuotient
section
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.TsField

theorem exists_ideal_eq_iff {S : Scheme.{0}} {Y : Over S} [IsSeparated Y.hom] {R : Type} [CommRing R]
    {c : Sp R ⟶ S} (f g : Over.mk c ⟶ Y) :
    ∃ J : Ideal R, ∀ (A : Type) [CommRing A] (ρ : R →+* A),
      spMap ρ ≫ f.left = spMap ρ ≫ g.left ↔ J ≤ RingHom.ker ρ := by
  haveI hcl : IsClosedImmersion (equalizer.ι f g).left := isClosedImmersion_equalizer_ι_left _ _
  obtain ⟨I, e, he⟩ := IsClosedImmersion.Spec_iff.1 hcl
  have hcond : (equalizer.ι f g).left ≫ f.left = (equalizer.ι f g).left ≫ g.left := by
    rw [← Over.comp_left, ← Over.comp_left, equalizer.condition]
  refine ⟨I, fun A _ ρ => ⟨fun h => ?_, fun h => ?_⟩⟩
  · let i : Over.mk (spMap ρ ≫ c) ⟶ Over.mk c := Over.homMk (spMap ρ)
    have hi : i ≫ f = i ≫ g := by
      ext1
      exact h
    let l := equalizer.lift i hi
    have h1 : spMap ρ = l.left ≫ (equalizer.ι f g).left := by
      rw [← Over.comp_left, equalizer.lift_ι]; rfl
    rw [he] at h1
    let σ := Spec.preimage (l.left ≫ e.hom)
    have h2 : spMap ρ = Spec.map σ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) := by
      rw [Spec.map_preimage, Category.assoc]
      exact h1
    rw [← Spec.map_comp] at h2
    have h3 := Spec.map_injective h2
    intro x hx
    have h4 : ρ x = σ.hom (Ideal.Quotient.mk I x) := by
      have := congrArg (fun q => q.hom x) h3
      simpa using this
    rw [RingHom.mem_ker, h4, Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]
  · let q : (R ⧸ I) →+* A := Ideal.Quotient.lift I ρ (fun a ha => h ha)
    have hq : CommRingCat.ofHom ρ =
        CommRingCat.ofHom (Ideal.Quotient.mk I) ≫ CommRingCat.ofHom q := by
      ext x
      exact (Ideal.Quotient.lift_mk I ρ (fun a ha => h ha)).symm
    have h1 : spMap ρ = (spMap q ≫ e.inv) ≫ (equalizer.ι f g).left := by
      rw [he, Category.assoc, Iso.inv_hom_id_assoc, spMap, hq, Spec.map_comp]
    rw [h1]
    simp only [Category.assoc, hcond]

open AddMonoidAlgebra in

theorem exists_span_of_coideal (k X : Type) [Field k] [AddCommGroup X] (J : Ideal (AddMonoidAlgebra k X))
    (h1 : ∀ f ∈ J, Coalgebra.counit (R := k) f = 0)
    (h2 : ∀ f ∈ J, TensorProduct.map (J.restrictScalars k).mkQ (J.restrictScalars k).mkQ
      (Coalgebra.comul (R := k) f) = 0) :
    ∃ Y : AddSubgroup X, J = Ideal.span {f | ∃ y ∈ Y, f = AddMonoidAlgebra.single y (1 : k) - 1} := by
  haveI : (J.restrictScalars k).IsCoideal := ⟨fun x hx => h1 x hx, fun x hx => h2 x hx⟩
  haveI : Nontrivial (AddMonoidAlgebra k X ⧸ J) := by
    refine Ideal.Quotient.nontrivial_iff.2 fun h => ?_
    have := h1 1 (h ▸ Submodule.mem_top)
    simp at this
  obtain ⟨Y, hY⟩ := GlobalTheory.CompanionTheory.CommAlg.ker_eq_span_single_sub_one k X (AddMonoidAlgebra k X ⧸ J)
    (Bialgebra.Quotient.mkBialgHom (R := k) J) Ideal.Quotient.mk_surjective
  refine ⟨Y, ?_⟩
  rw [← hY]
  exact (Ideal.mk_ker).symm

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X]
  {k : Type} [Field k]

theorem exists_ringHom_of_point {A : Type} [CommRing A] (g : k →+* A) {a : Sp A ⟶ S}
    (t : Over.mk a ⟶ splitTorus S X) :
    ∃ ρ : AddMonoidAlgebra k X →+* A, ρ.comp (algebraMap k (AddMonoidAlgebra k X)) = g ∧
      ∀ χ, ρ (AddMonoidAlgebra.single χ 1) = charVal t χ := by
  obtain ⟨h0, hadd⟩ := (GlobalTheory.T.charVal_multiplicative S X A a).2.2.2.1 t
  letI : Algebra k A := g.toAlgebra
  let w : Multiplicative X →* A :=
    { toFun := fun x => charVal t x.toAdd
      map_one' := h0
      map_mul' := fun x y => hadd x.toAdd y.toAdd }
  refine ⟨(AddMonoidAlgebra.lift k A X w : AddMonoidAlgebra k X →ₐ[k] A).toRingHom, ?_, fun χ => ?_⟩
  · ext c
    exact (AddMonoidAlgebra.lift k A X w).commutes c
  · simp [w]

theorem exists_universal_point (b : Sp k ⟶ S) :
    ∃ t₀ : Over.mk (spMap (algebraMap k (AddMonoidAlgebra k X)) ≫ b) ⟶ splitTorus S X,
      ∀ χ, charVal t₀ χ = AddMonoidAlgebra.single χ 1 := by
  obtain ⟨t, ht⟩ := (GlobalTheory.T.charVal_multiplicative S X (AddMonoidAlgebra k X)
    (spMap (algebraMap k (AddMonoidAlgebra k X)) ≫ b)).2.2.2.2.1 (AddMonoidAlgebra.of k X)
  exact ⟨t, fun χ => by simpa using ht χ⟩

theorem spMap_comp_base {K A : Type} [CommRing K] [CommRing A] (g₀ : k →+* K) (ρ : K →+* A) (b : Sp k ⟶ S) :
    spMap ρ ≫ spMap g₀ ≫ b = spMap (ρ.comp g₀) ≫ b := by
  rw [← Category.assoc, spMap, spMap, spMap, ← Spec.map_comp]
  rfl

theorem exists_killing_ideal [IsSeparated G.hom] (u : splitTorus S X ⟶ G) [IsMonHom u] (b : Sp k ⟶ S) :
    ∃ J : Ideal (AddMonoidAlgebra k X), ∀ (A : Type) [CommRing A] (ρ : AddMonoidAlgebra k X →+* A)
      (a : Sp A ⟶ S), a = spMap (ρ.comp (algebraMap k (AddMonoidAlgebra k X))) ≫ b →
      ∀ t : Over.mk a ⟶ splitTorus S X, (∀ χ, charVal t χ = ρ (AddMonoidAlgebra.single χ 1)) →
        (t ≫ u = 1 ↔ J ≤ RingHom.ker ρ) := by
  obtain ⟨t₀, ht₀⟩ := exists_universal_point (X := X) b
  obtain ⟨J, hJ⟩ := exists_ideal_eq_iff (t₀ ≫ u) (1 : _ ⟶ G)
  refine ⟨J, fun A _ ρ a ha t ht => ?_⟩
  rw [← spMap_comp_base] at ha
  subst ha
  rw [← hJ A ρ]
  let h : Over.mk (spMap ρ ≫ spMap (algebraMap k (AddMonoidAlgebra k X)) ≫ b) ⟶
      Over.mk (spMap (algebraMap k (AddMonoidAlgebra k X)) ≫ b) := Over.homMk (spMap ρ)
  have e : t = h ≫ t₀ := by
    refine (GlobalTheory.T.charVal_multiplicative S X A _).1 _ _ fun χ => ?_
    rw [ht, (GlobalTheory.T.charVal_multiplicative S X _ _).2.2.2.2.2 A ρ t₀ (h ≫ t₀) rfl χ, ht₀]
  have e1 : (1 : Over.mk (spMap ρ ≫ spMap (algebraMap k (AddMonoidAlgebra k X)) ≫ b) ⟶ G) = h ≫ 1 :=
    (MonObj.comp_one h).symm
  rw [e, Category.assoc, e1]
  constructor
  · intro h'
    exact congrArg (fun q => q.left) h'
  · intro h'
    ext1
    exact h'

open TensorProduct in

theorem killing_ideal_coideal (b : Sp k ⟶ S) (u : splitTorus S X ⟶ G) [IsMonHom u]
    (J : Ideal (AddMonoidAlgebra k X))
    (hJ : ∀ (A : Type) [CommRing A] (ρ : AddMonoidAlgebra k X →+* A)
      (a : Sp A ⟶ S), a = spMap (ρ.comp (algebraMap k (AddMonoidAlgebra k X))) ≫ b →
      ∀ t : Over.mk a ⟶ splitTorus S X, (∀ χ, charVal t χ = ρ (AddMonoidAlgebra.single χ 1)) →
        (t ≫ u = 1 ↔ J ≤ RingHom.ker ρ)) :
    (∀ f ∈ J, Coalgebra.counit (R := k) f = 0) ∧
    (∀ f ∈ J, TensorProduct.map (J.restrictScalars k).mkQ (J.restrictScalars k).mkQ
      (Coalgebra.comul (R := k) f) = 0) := by
  constructor
  · let ε : AddMonoidAlgebra k X →ₐ[k] k := Bialgebra.counitAlgHom k (AddMonoidAlgebra k X)
    have hε : (ε : AddMonoidAlgebra k X →+* k).comp (algebraMap k (AddMonoidAlgebra k X)) = RingHom.id k := by
      ext c
      exact ε.commutes c
    have hb : b = spMap ((ε : AddMonoidAlgebra k X →+* k).comp (algebraMap k (AddMonoidAlgebra k X))) ≫ b := by
      rw [hε]
      change b = Spec.map (𝟙 _) ≫ b
      rw [Spec.map_id, Category.id_comp]
    have hk := (hJ k (ε : AddMonoidAlgebra k X →+* k) b hb (1 : Over.mk b ⟶ splitTorus S X) ?_).1 (MonObj.one_comp u)
    · intro f hf
      exact hk hf
    · intro χ
      rw [(GlobalTheory.T.charVal_multiplicative S X k b).2.2.1 χ]
      simp [ε]
  · let Q := AddMonoidAlgebra k X ⧸ J
    let mkQ : AddMonoidAlgebra k X →ₐ[k] Q := Ideal.Quotient.mkₐ k J
    let c : AddMonoidAlgebra k X →ₐ[k] Q ⊗[k] Q :=
      (Algebra.TensorProduct.map mkQ mkQ).comp (Bialgebra.comulAlgHom k (AddMonoidAlgebra k X))
    let i₁ : AddMonoidAlgebra k X →ₐ[k] Q ⊗[k] Q := Algebra.TensorProduct.includeLeft.comp mkQ
    let i₂ : AddMonoidAlgebra k X →ₐ[k] Q ⊗[k] Q := Algebra.TensorProduct.includeRight.comp mkQ
    let A := Q ⊗[k] Q
    let a : Sp A ⟶ S := spMap (algebraMap k A) ≫ b
    have hcomp : ∀ φ : AddMonoidAlgebra k X →ₐ[k] A,
        a = spMap ((φ : AddMonoidAlgebra k X →+* A).comp (algebraMap k (AddMonoidAlgebra k X))) ≫ b := by
      intro φ
      rw [φ.comp_algebraMap]
    have hpt : ∀ φ : AddMonoidAlgebra k X →ₐ[k] A, ∃ t : Over.mk a ⟶ splitTorus S X,
        ∀ χ, charVal t χ = φ (AddMonoidAlgebra.single χ 1) := by
      intro φ
      obtain ⟨t, ht⟩ := (GlobalTheory.T.charVal_multiplicative S X A a).2.2.2.2.1
        (((φ : AddMonoidAlgebra k X →+* A) : AddMonoidAlgebra k X →* A).comp (AddMonoidAlgebra.of k X))
      exact ⟨t, fun χ => by simpa using ht χ⟩
    obtain ⟨t₁, ht₁⟩ := hpt i₁
    obtain ⟨t₂, ht₂⟩ := hpt i₂
    have k₁ : t₁ ≫ u = 1 := (hJ A (i₁ : AddMonoidAlgebra k X →+* A) a (hcomp i₁) t₁ ht₁).2 fun f hf => by
      have : mkQ f = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hf
      simp [RingHom.mem_ker, i₁, this]
    have k₂ : t₂ ≫ u = 1 := (hJ A (i₂ : AddMonoidAlgebra k X →+* A) a (hcomp i₂) t₂ ht₂).2 fun f hf => by
      have : mkQ f = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hf
      simp [RingHom.mem_ker, i₂, this]
    have hc : ∀ χ, charVal (t₁ * t₂) χ = (c : AddMonoidAlgebra k X →+* A) (AddMonoidAlgebra.single χ 1) := by
      intro χ
      rw [(GlobalTheory.T.charVal_multiplicative S X A a).2.1 t₁ t₂ χ, ht₁, ht₂]
      have e : (c : AddMonoidAlgebra k X →+* A) (AddMonoidAlgebra.single χ 1) = mkQ (AddMonoidAlgebra.single χ 1) ⊗ₜ mkQ (AddMonoidAlgebra.single χ 1) := by
        simp [c, AddMonoidAlgebra.comul_single, CommSemiring.comul_apply]
      rw [e]
      change (mkQ (AddMonoidAlgebra.single χ 1) ⊗ₜ[k] (1 : Q)) * ((1 : Q) ⊗ₜ[k] mkQ (AddMonoidAlgebra.single χ 1)) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, _root_.one_mul]
    have hk := (hJ A (c : AddMonoidAlgebra k X →+* A) a (hcomp c) (t₁ * t₂) hc).1
      (by rw [MonObj.mul_comp, k₁, k₂, _root_.mul_one])
    intro f hf
    exact hk hf

theorem exists_mu_killed : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsSeparated G.hom] (X : Type) [AddCommGroup X]
    [Module.Finite ℤ X] (u : splitTorus S X ⟶ G) [IsMonHom u] (k : Type) [Field k] (b : Sp k ⟶ S)
    (M : LieModel (splitTorus S X) b (X →+ k)), IsCocharLie M → ∀ δ : X →+ k, δ ≠ 0 → M.pt δ ≫ u = 1 →
    ∃ (l : ℕ) (_ : l.Prime) (ψ : X →+ ZMod l), Function.Surjective ψ ∧ KillsOver u ψ.ker b := by
  intro S G _ _ X _ _ u _ k _ b M hM δ hδ hu
  obtain ⟨J, hJ⟩ := exists_killing_ideal (k := k) u b
  obtain ⟨h1, h2⟩ := killing_ideal_coideal b u J hJ
  obtain ⟨Y, hY⟩ := exists_span_of_coideal k X J h1 h2
  have hmain : ∀ (A : Type) [CommRing A] (g : k →+* A) (a : Sp A ⟶ S), a = spMap g ≫ b →
      ∀ t : Over.mk a ⟶ splitTorus S X, (t ≫ u = 1 ↔ ∀ y ∈ Y, charVal t y = 1) := by
    intro A _ g a ha t
    obtain ⟨ρ, hρ, hv⟩ := exists_ringHom_of_point (k := k) g t
    rw [hJ A ρ a (by rw [hρ, ha]) t (fun χ => (hv χ).symm), hY, Ideal.span_le]
    constructor
    · intro h y hy
      have h0 : ρ (AddMonoidAlgebra.single y 1 - 1) = 0 := h ⟨y, hy, rfl⟩
      rwa [map_sub, map_one, hv, sub_eq_zero] at h0
    · rintro h _ ⟨y, hy, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one, hv, h y hy, sub_self]
  have hδY : ∀ y ∈ Y, δ y = 0 := by
    intro y hy
    have h0 := (hmain (DualNumber k) (algebraMap k (DualNumber k)) _ rfl (M.pt δ)).1 hu y hy
    rw [hM δ y] at h0
    simpa using congrArg TrivSqZeroExt.snd h0
  obtain ⟨l, hl, ψ, hs, hψ⟩ := GlobalTheory.CompanionTheory.QuotPrime.exists_surjective_zmod_of_ne_zero k X Y δ hδ hδY
  exact ⟨l, hl, ψ, hs, fun A _ g t ht => (hmain A g _ rfl t).2 fun y hy => ht y (hψ y hy)⟩

end GlobalTheory.CompanionTheory.Ar.TsField
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.VectorsAtComplexPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open GlobalTheory.CompanionTheory.Ar.LocFn.Transfer

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem isEigFrame_of_sameVec (Y : Model Xo c β) {F : Type} [Field F] (y : Sp F ⟶ Xo.XF c) (κ : 𝓞 E →+* F) {n : ℕ}
    (v : Fin n → (epsAt (under y) ⟶ Xo.univ.t.G)) (v₀ : Fin n → (epsAt (y ≫ Y.j) ⟶ Y.t.G))
    (hs : ∀ i, SameVec Y y (v i) (v₀ i)) (hf : IsEigFrame Y.t.act (y ≫ Y.j) κ v₀) :
    IsEigFrame Xo.univ.t.act (under y) κ v := by
  have hq : IsGrpPullback Y.oF.t.G Y.t.G Y.j Y.m.φ := Y.m.cart
  have hp : IsGrpPullback Y.oF.t.G Xo.univ.t.G (pullback.fst _ _) Y.m0.toSABMap.φ := Y.m0.cart
  choose u hu₀ hu₁ hu₂ using hs
  let a : Fin n → (epsAt y ⟶ Y.oF.t.G) := fun i => Over.homMk (u i) (hu₀ i)
  have e₀ : (fun i => tanMap hq y (a i)) = v₀ := funext fun i => Over.OverMorphism.ext (hu₂ i)
  have e₁ : (fun i => tanMap hp y (a i)) = v := funext fun i => Over.OverMorphism.ext (hu₁ i)
  have h₁ : IsEigFrame Y.oF.t.act y κ a :=
    (isEigFrame_iff hq Y.oF.t.act Y.t.act Y.m.act y κ a).1 (by rw [e₀]; exact hf)
  have h₂ := (isEigFrame_iff hp Y.oF.t.act Xo.univ.t.act Y.m0.act y κ a).2 h₁
  rw [e₁] at h₂
  exact h₂

theorem isFramed_of_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (τ : E →+* ℂ) (σ : c.F →+* ℂ) (y : Sp ℂ ⟶ Xo.XF c) (v : Vecs y D.p) (w : Vecs y D.q) (v₀ : Fin D.p → (epsAt (y ≫ Y.j) ⟶ Y.t.G)) (w₀ : Fin D.q → (epsAt (y ≫ Y.j) ⟶ Y.t.G)), y ≫ pullback.snd _ _ = spMap σ → (∀ i, SameVec Y y (v i) (v₀ i)) → (∀ j, SameVec Y y (w j) (w₀ j)) → IsEigFrame Y.t.act (y ≫ Y.j) (σ.comp (tauIn c τ)) v₀ → IsEigFrame Y.t.act (y ≫ Y.j) (σ.comp (tauIn c (ComplexEmbedding.conjugate τ))) w₀ → IsFramed Set.univ τ σ y v w := by
  intro E _ _ _ H D l Xo c O _ β Y τ σ y v w v₀ w₀ hy hv hw fv fw
  exact ⟨hy, Set.subset_univ _, isEigFrame_of_sameVec Y y _ v v₀ hv fv, isEigFrame_of_sameVec Y y _ w w₀ hw fw⟩

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

