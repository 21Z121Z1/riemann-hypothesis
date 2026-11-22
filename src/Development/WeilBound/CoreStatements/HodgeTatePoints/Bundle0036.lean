import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FormallyUnramifiedOfCompOfEtaleOfSurjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0007
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0016

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.MiOpen
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct

namespace PositivityTheory.HtPt.Mi

theorem flat_of_forall {X Z : Scheme.{0}} (f : X ⟶ Z)
    (h : ∀ x : X, ∃ (W : Scheme.{0}) (g : W ⟶ X) (w : W), g w = x ∧ Flat g ∧ Flat (g ≫ f)) : Flat f := by
  refine Flat.of_stalkMap f fun x => ?_
  obtain ⟨W, g, w, rfl, _, _⟩ := h x
  have h := Flat.stalkMap (g ≫ f) w
  rw [Scheme.Hom.stalkMap_comp] at h
  exact GlobalTheory.ringHom_flat_of_comp_faithfullyFlat (GlobalTheory.faithfullyFlat_stalkMap_of_flat g w) h

theorem open_crit : ∀ (R : Type) [CommRing R] (X Y : Scheme.{0}) (j : X ⟶ Y) (q : Y ⟶ Spec (CommRingCat.of R)) [LocallyOfFinitePresentation j], (∀ (P : Ideal R) [P.IsPrime], ∃ (R' : Type) (_ : CommRing R') (_ : IsLocalRing R') (_ : Algebra R R') (X' Y' : Scheme.{0}) (j' : X' ⟶ Y') (q' : Y' ⟶ Spec (CommRingCat.of R')) (a : X' ⟶ X) (b : Y' ⟶ Y) (U : X'.Opens), Module.Flat R R' ∧ (IsLocalRing.maximalIdeal R').comap (algebraMap R R') = P ∧ IsPullback b q' q (Spec.map (CommRingCat.ofHom (algebraMap R R'))) ∧ IsPullback a j' j b ∧ IsOpenImmersion (U.ι ≫ j') ∧ ∀ x : X', q' (j' x) = IsLocalRing.closedPoint R' → x ∈ U) → IsOpenImmersion j := by
  intro R _ X Y j q _ H
  have key : ∀ x : X, ∃ (U V : Scheme.{0}) (g : U ⟶ X) (u : U) (δ : U ⟶ V) (m : V ⟶ pullback j j),
      g u = x ∧ Flat g ∧ Flat (g ≫ j) ∧ IsOpenImmersion δ ∧ Flat m ∧ δ ≫ m = g ≫ pullback.diagonal j ∧
      ∀ z, pullback.snd j j z = x → ∃ u', m (δ u') = z := by
    intro x
    obtain ⟨R', _, _, _, X', Y', j', q', a, b, U, hfl, hP, hb, ha, hU, hcl⟩ := @H (q (j x)).asIdeal (q (j x)).isPrime
    have hs : Flat (Spec.map (CommRingCat.ofHom (algebraMap R R'))) :=
      Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 hfl)
    have hbf : Flat b := MorphismProperty.of_isPullback hb.flip hs
    have haf : Flat a := MorphismProperty.of_isPullback ha.flip hbf
    obtain ⟨x', hx1, hx2⟩ := Scheme.exists_preimage_of_isPullback (ha.paste_vert hb) x
      (IsLocalRing.closedPoint R') (PrimeSpectrum.ext hP.symm)
    have hx2' : q' (j' x') = IsLocalRing.closedPoint R' := by rw [← hx2]; simp
    let u : U.toScheme := ⟨x', hcl x' hx2'⟩
    have hu : U.ι u = x' := rfl
    have hw : (U.ι ≫ a) ≫ j = (U.ι ≫ j') ≫ b := by rw [Category.assoc, ha.w, Category.assoc]
    let δ : U.toScheme ⟶ pullback j' (U.ι ≫ j') := pullback.lift U.ι (𝟙 _) (by simp)
    have hδ : δ ≫ pullback.fst _ _ = U.ι := pullback.lift_fst _ _ _
    have hδ' : δ ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
    have hV := (IsPullback.of_hasPullback j' (U.ι ≫ j')).paste_horiz ha
    rw [← hw] at hV
    let m : pullback j' (U.ι ≫ j') ⟶ pullback j j :=
      pullback.lift (pullback.fst _ _ ≫ a) (pullback.snd _ _ ≫ U.ι ≫ a) (by rw [hV.w]; simp only [Category.assoc])
    have hm1 : m ≫ pullback.fst j j = pullback.fst _ _ ≫ a := pullback.lift_fst _ _ _
    have hm2 : m ≫ pullback.snd j j = pullback.snd _ _ ≫ U.ι ≫ a := pullback.lift_snd _ _ _
    have hm : IsPullback m (pullback.snd j' (U.ι ≫ j')) (pullback.snd j j) (U.ι ≫ a) :=
      IsPullback.of_right (by rw [hm1]; exact hV) hm2 (IsPullback.of_hasPullback j j)
    have hg : Flat (U.ι ≫ a) := inferInstance
    have hδo : IsOpenImmersion δ := by
      have : IsOpenImmersion (δ ≫ pullback.fst j' (U.ι ≫ j')) := by rw [hδ]; infer_instance
      exact IsOpenImmersion.of_comp δ (pullback.fst j' (U.ι ≫ j'))
    have hgu : (U.ι ≫ a) u = x := by rw [Scheme.Hom.comp_apply, hu]; exact hx1
    refine ⟨U, _, U.ι ≫ a, u, δ, m, hgu, hg, by rw [hw]; infer_instance, hδo,
      MorphismProperty.of_isPullback hm.flip hg, ?_, fun z hz => ?_⟩
    · apply pullback.hom_ext
      · rw [Category.assoc, hm1, reassoc_of% hδ]; simp
      · rw [Category.assoc, hm2, reassoc_of% hδ']; simp
    · obtain ⟨v, hv1, hv2⟩ := Scheme.exists_preimage_of_isPullback hm z u (hz.trans hgu.symm)
      have h1 : j' (pullback.fst j' (U.ι ≫ j') v) = j' x' := by
        rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
        exact congrArg (fun t => j' (U.ι t)) hv2
      let u' : U.toScheme := ⟨pullback.fst j' (U.ι ≫ j') v, hcl _ (by rw [h1, hx2'])⟩
      have h2 : δ u' = v := by
        apply (pullback.fst j' (U.ι ≫ j')).isOpenEmbedding.injective
        rw [← Scheme.Hom.comp_apply, hδ]
        rfl
      exact ⟨u', by rw [h2]; exact hv1⟩
  have : Flat j := flat_of_forall j fun x => by
    obtain ⟨U, V, g, u, δ, m, h1, h2, h3, -⟩ := key x
    exact ⟨U, g, u, h1, h2, h3⟩
  have : Flat (pullback.diagonal j) := flat_of_forall _ fun x => by
    obtain ⟨U, V, g, u, δ, m, h1, h2, -, h4, h5, h6, -⟩ := key x
    exact ⟨U, g, u, h1, h2, by rw [← h6]; infer_instance⟩
  have : Surjective (pullback.diagonal j) := ⟨fun z => by
    obtain ⟨U, V, g, u, δ, m, -, -, -, -, -, h6, h7⟩ := key (pullback.snd j j z)
    obtain ⟨u', hu'⟩ := h7 z rfl
    exact ⟨g u', by rw [← hu', ← Scheme.Hom.comp_apply, ← h6, Scheme.Hom.comp_apply]⟩⟩
  have : IsClosedImmersion (pullback.diagonal j) :=
    IsClosedImmersion.of_isPreimmersion _ (by rw [(pullback.diagonal j).surjective.range_eq]; exact isClosed_univ)
  have : IsIso (pullback.diagonal j) := Flat.isIso_of_surjective_of_mono _
  have : Mono j := (pullback.isIso_diagonal_iff j).1 this
  exact IsOpenImmersion.of_flat_of_mono j

end PositivityTheory.HtPt.Mi
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.MkChart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace PositivityTheory.HtPt.Mk

theorem gen_stalk {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) :
    Spec.map (CommRingCat.ofHom (genMap ξ p)) ≫ X.fromSpecStalk p.1 = ξ := by
  obtain ⟨q, hq⟩ := p
  have a := Scheme.SpecMap_stalkSpecializes_fromSpecStalk hq
  have b := Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
  have c : Spec.map (CommRingCat.ofHom (genMap ξ ⟨q, hq⟩)) =
      Spec.map (Scheme.stalkClosedPointTo ξ) ≫ Spec.map (X.presheaf.stalkSpecializes hq) :=
    Spec.map_comp _ _
  rw [c, Category.assoc]
  exact (congrArg (fun m => Spec.map (Scheme.stalkClosedPointTo ξ) ≫ m) a).trans b

theorem stalk_normal₀ {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} (hξ : IsCptGen ξ)
    (hN : Flat.NormalCpt ξ) (q : Cpt ξ) : ∃ (_ : IsDomain (X.presheaf.stalk q.1)),
      IsIntegrallyClosed (X.presheaf.stalk q.1) ∧ ∃ κ : FractionRing (X.presheaf.stalk q.1) ≃+* Ω,
        κ.toRingHom.comp (algebraMap _ _) = genMap ξ q := by
  have hd : IsDomain (X.presheaf.stalk q.1) := (hξ.inj q).isDomain _
  letI : Algebra (X.presheaf.stalk q.1) Ω := (genMap ξ q).toAlgebra
  have : FaithfulSMul (X.presheaf.stalk q.1) Ω := (faithfulSMul_iff_algebraMap_injective _ _).2 (hξ.inj q)
  have hf : IsFractionRing (X.presheaf.stalk q.1) Ω := by
    refine IsFractionRing.of_field _ _ fun a => ?_
    obtain ⟨b, c, hc, e⟩ := GlobalTheory.T.exists_stalk_fraction_of_generic ξ hξ q a
    exact ⟨b, c, (eq_div_iff hc).2 e⟩
  refine ⟨hd, ?_, (FractionRing.algEquiv _ Ω).toRingEquiv, RingHom.ext (FractionRing.algEquiv _ Ω).commutes⟩
  rw [isIntegrallyClosed_iff Ω]
  intro a ha
  exact hN q a (IsIntegral.map_of_comp_eq (genMap ξ q).rangeRestrict (RingHom.id Ω) (RingHom.ext fun _ => rfl) ha)

theorem ht_lat_chart : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → Flat.NormalCpt ξ → ∀ q : Cpt ξ, ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (x : Spec (CommRingCat.of R) ⟶ X) (κ : FractionRing R ≃+* Ω), IsNoetherianRing R ∧ IsIntegrallyClosed R ∧ IsOpenImmersion x ∧ q.1 ∈ Set.range x ∧ (∀ y ∈ Set.range x, genPt ξ ⤳ y) ∧ spMap (κ.toRingHom.comp (algebraMap R _)) ≫ x = ξ := by
  intro X _ Ω _ _ ξ hξ hN q
  obtain ⟨U, hqU, hU, hinj⟩ := X.exists_germ_injective q.1
  let k₀ : Γ(X, U) →+* Ω := (genMap ξ q).comp (X.presheaf.germ U q.1 hqU).hom
  have hk : Function.Injective k₀ := (hξ.inj q).comp hinj
  have hd : IsDomain Γ(X, U) := hk.isDomain _
  have hx : Spec.map (CommRingCat.ofHom k₀) ≫ hU.fromSpec = ξ := by
    refine Eq.trans ?_ (gen_stalk ξ q)
    rw [← hU.fromSpecStalk_eq_fromSpecStalk hqU, IsAffineOpen.fromSpecStalk, ← Category.assoc, ← Spec.map_comp]
    rfl
  have hall : ∀ p : Spec Γ(X, U), genPt ξ ⤳ hU.fromSpec p := by
    intro p
    have e : genPt ξ = hU.fromSpec (Spec.map (CommRingCat.ofHom k₀) (IsLocalRing.closedPoint Ω)) := by
      rw [← hx]; rfl
    rw [e]
    refine Specializes.map ?_ hU.fromSpec.continuous
    refine (PrimeSpectrum.le_iff_specializes _ _).1 fun a ha => ?_
    have h1 : k₀ a ∈ IsLocalRing.maximalIdeal Ω := ha
    rw [IsLocalRing.maximalIdeal_eq_bot] at h1
    rw [hk (h1.trans (map_zero k₀).symm)]
    exact Ideal.zero_mem _
  letI : Algebra Γ(X, U) Ω := k₀.toAlgebra
  have : FaithfulSMul Γ(X, U) Ω := (faithfulSMul_iff_algebraMap_injective _ _).2 hk
  have hf : IsFractionRing Γ(X, U) Ω := by
    refine IsFractionRing.of_field _ _ fun a => ?_
    obtain ⟨b, c, hc, e⟩ := GlobalTheory.T.exists_stalk_fraction_of_generic ξ hξ q a
    letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨q.1, hqU⟩ : U)
    have hl := hU.isLocalization_stalk ⟨q.1, hqU⟩
    obtain ⟨⟨b₁, s⟩, hb⟩ := IsLocalization.surj (hU.primeIdealOf ⟨q.1, hqU⟩).asIdeal.primeCompl
      (S := X.presheaf.stalk q.1) b
    obtain ⟨⟨c₁, t⟩, hc'⟩ := IsLocalization.surj (hU.primeIdealOf ⟨q.1, hqU⟩).asIdeal.primeCompl
      (S := X.presheaf.stalk q.1) c
    have hb' : genMap ξ q b * k₀ s = k₀ b₁ := by
      have := congrArg (genMap ξ q) hb
      rwa [map_mul] at this
    have hc'' : genMap ξ q c * k₀ t = k₀ c₁ := by
      have := congrArg (genMap ξ q) hc'
      rwa [map_mul] at this
    have hne : ∀ s : (hU.primeIdealOf ⟨q.1, hqU⟩).asIdeal.primeCompl, k₀ s ≠ 0 := fun s h =>
      s.2 (by rw [hk (h.trans (map_zero k₀).symm)]; exact Ideal.zero_mem _)
    refine ⟨b₁ * t, c₁ * s, ?_⟩
    change a = k₀ (b₁ * t) / k₀ (c₁ * s)
    rw [map_mul, map_mul, ← hb', ← hc'', ← e, eq_div_iff (mul_ne_zero (mul_ne_zero hc (hne t)) (hne s))]
    ring
  refine ⟨Γ(X, U), inferInstance, hd, hU.fromSpec, (FractionRing.algEquiv _ Ω).toRingEquiv,
    IsLocallyNoetherian.component_noetherian ⟨U, hU⟩, ?_, inferInstance, ?_, ?_, ?_⟩
  · refine IsIntegrallyClosed.of_localization_maximal fun p _ hp => ?_
    let P : PrimeSpectrum Γ(X, U) := ⟨p, hp.isPrime⟩
    have hy : hU.fromSpec P ∈ U := by
      rw [← SetLike.mem_coe, ← hU.range_fromSpec]
      exact ⟨P, rfl⟩
    letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨_, hy⟩ : U)
    have hl : IsLocalization p.primeCompl (X.presheaf.stalk (hU.fromSpec P)) := hU.isLocalization_stalk' P hy
    obtain ⟨_, hic, -⟩ := stalk_normal₀ hξ hN ⟨_, hall P⟩
    exact IsIntegrallyClosed.of_equiv (R := X.presheaf.stalk (hU.fromSpec P))
      (IsLocalization.algEquiv p.primeCompl (X.presheaf.stalk (hU.fromSpec P)) (Localization.AtPrime p)).toRingEquiv
  · rw [hU.range_fromSpec]
    exact hqU
  · rintro _ ⟨p, rfl⟩
    exact hall p
  · have e : (FractionRing.algEquiv Γ(X, U) Ω).toRingEquiv.toRingHom.comp (algebraMap _ _) = k₀ :=
      RingHom.ext (FractionRing.algEquiv _ Ω).commutes
    rw [e]
    exact hx

end PositivityTheory.HtPt.Mk
end
end

