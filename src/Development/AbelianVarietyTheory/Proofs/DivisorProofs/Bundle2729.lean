import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTangentPresentationPrime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2676
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2622
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2322
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2471
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2604
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2491
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2499
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2623
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2569
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2624
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2627
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2669
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.WitnessIsFormalParam
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2633

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointLiftToField
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.GenericFactor

theorem exists_factor_generic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l' : Level H)
    (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (p : ℕ),
    p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (R : Type) [CommRing R] [IsDomain R] (ξ : Sp R ⟶ Y.X),
    ξ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) ∈ Set.range Y.j →
    ∃ y : Sp (FractionRing R) ⟶ Xo'.XF c', spMap (algebraMap R (FractionRing R)) ≫ ξ = y ≫ Y.j := by
  intro E _ _ _ H Dw l' Xo' c' W Y p _ _ R _ _ ξ hξ
  haveI := Y.jQ_open
  obtain ⟨u, hu⟩ := hξ
  let g₀ : Sp (FractionRing R) ⟶ Y.X := spMap (algebraMap R (FractionRing R)) ≫ ξ
  let φ : c'.V W →+* FractionRing R := (Spec.preimage (g₀ ≫ Y.s)).hom
  have hφ : spMap φ = g₀ ≫ Y.s := Spec.map_preimage _
  have hpt : ∀ q : Sp (FractionRing R), g₀ q = Y.j u := by
    intro q
    rw [hu]
    show ξ ((spMap (algebraMap R (FractionRing R))) q) = _
    congr 1
    apply PrimeSpectrum.ext
    show Ideal.comap (algebraMap R (FractionRing R)) q.asIdeal = ⊥
    rw [@Ideal.eq_bot_of_prime _ _ q.asIdeal (PrimeSpectrum.isPrime (self := q)), ← RingHom.ker_eq_comap_bot]
    exact (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))
  have hinj : Function.Injective φ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    let q : Sp (FractionRing R) := ⟨⊥, Ideal.isPrime_bot⟩
    have h1 : ((spMap φ) q).asIdeal = RingHom.ker φ := by
      show Ideal.comap φ ⊥ = _
      exact (RingHom.ker_eq_comap_bot φ).symm
    have h2 : (spMap φ) q = Y.s (Y.j u) := by
      rw [hφ, ← hpt q]; rfl
    have h3 : Y.s (Y.j u) = (spMap (c'.V W).subtype) ((pullback.snd Y.s (spMap (c'.V W).subtype)) (Y.jQ u)) := by
      change (Y.j ≫ Y.s) u = (Y.jQ ≫ pullback.snd _ _ ≫ spMap (c'.V W).subtype) u
      rw [Model.j_s, ← Category.assoc, Y.jQ_over]
    rw [← h1, h2, h3]
    show Ideal.comap (c'.V W).subtype _ = ⊥
    have hF : ∀ z : Sp c'.F, z.asIdeal = ⊥ := fun z => @Ideal.eq_bot_of_prime _ _ z.asIdeal (PrimeSpectrum.isPrime (self := z))
    rw [hF, ← RingHom.ker_eq_comap_bot]
    exact (RingHom.injective_iff_ker_eq_bot _).1 Subtype.val_injective
  let ψ : c'.F →+* FractionRing R := IsFractionRing.lift hinj
  have hψ : ψ.comp (c'.V W).subtype = φ := IsLocalization.lift_comp _
  have hw : g₀ ≫ Y.s = spMap ψ ≫ spMap (c'.V W).subtype := by
    rw [← hφ, ← spMap_comp, hψ]
  let w : Sp (FractionRing R) ⟶ pullback Y.s (spMap (c'.V W).subtype) := pullback.lift g₀ (spMap ψ) hw
  have hr : Set.range w ⊆ Set.range Y.jQ := by
    rintro _ ⟨q, rfl⟩
    rw [← Y.ab_gen]
    show (w ≫ pullback.fst _ _) q ∈ abLocus Y.t.G
    rw [pullback.lift_fst, hpt q]
    have : Y.jQ u ∈ Set.range Y.jQ := ⟨u, rfl⟩
    rw [← Y.ab_gen] at this
    exact this
  refine ⟨IsOpenImmersion.lift Y.jQ w hr, ?_⟩
  show g₀ = _
  rw [Model.j, ← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_fst]

end GlobalTheory.GenericFactor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointsFiniteUnitaryModuliCoefficientField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.ZH GlobalTheory.UPoinc GlobalTheory.UCovSep
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.XScov

theorem genericPoints_XF_finite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), (genericPoints (Xo.XF c)).Finite := by
  intro E _ _ _ H Dw l Xo c
  obtain ⟨N, i, hi, hq, he⟩ := Xo.qproj
  have := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str (KA l) N
  haveI : QuasiCompact Xo.s := he ▸ inferInstance
  haveI : LocallyOfFiniteType Xo.s := he ▸ inferInstance
  haveI : QuasiCompact (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) := inferInstance
  haveI : LocallyOfFiniteType (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) := inferInstance
  haveI : IsLocallyNoetherian (Xo.XF c) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
  haveI : CompactSpace (Xo.XF c) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
  haveI : IsNoetherian (Xo.XF c) := {}
  exact genericPoints.finite finite_irreducibleComponents_of_isNoetherian

end GlobalTheory.XScov
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericUniformisedPullbackMumfordBundleMatchingStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_uniformised_pullback_mumfordBundle_matching : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∀ PP : LB (G2 G).left, ExtLam G (A.L.pull gen.hom.left) PP → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (φ : R →+* W) (GW : Over (Sp W)) [GrpObj GW] [IsCommMonObj GW] (βW : GW.left ⟶ G.left) (βW₂ : (G2 GW).left ⟶ (G2 G).left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW), GlobalTheory.LN.CDvr W → Function.Injective φ → IsLocalHom φ → IsGrpPullback GW G (spMap φ) βW → Geo.Tor.IsSquare βW βW₂ → LBIso (abelian₂ GW UW.LG.L) (PP.pull βW₂) → ∃ (ga : FractionRing R →+* FractionRing W) (α : AW.A.left ⟶ A.A.left) (α₂ : (G2 AW.A).left ⟶ (G2 A.A).left), (∀ r, ga (algebraMap R _ r) = algebraMap W _ (φ r)) ∧ IsGrpPullback AW.A A.A (spMap ga) α ∧ Geo.Tor.IsSquare α α₂ ∧ LBIso (abelian₂ AW.A AW.L) ((abelian₂ A.A A.L).pull α₂) ∧ UW.gen.inv.left ≫ pullback.fst GW.hom (jK W) ≫ βW = α ≫ gen.inv.left ≫ pullback.fst G.hom (jK R) := by
  first | exact @GlobalTheory.Mum.genLam_pull_of_unif | exact GlobalTheory.Mum.genLam_pull_of_unif | (intros; apply GlobalTheory.Mum.genLam_pull_of_unif <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalSectionsDimPullbackLeGenericallyFinite
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GlobalSectionsPullback

theorem globalSectionsDim_pullback_le_generically_finite : ∀ (F : Type) [Field F] (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W]
    (p : W ⟶ Sp F) (f : M ⟶ W), IsProjOver p → IsProjOver (f ≫ p) → Surjective f →
    f.residueDegree (genericPoint M) ≠ 0 → ∃ (r : ℕ) (A : LB W), IsAmpleLB A ∧
      ∀ B : LB W, B.IsLB → (letI := algebraΓOfHom (f ≫ p); lbH0 F (B.pull f)) ≤
        r * (letI := algebraΓOfHom p; lbH0 F (tens B A)) := by
  intro F _ M W _ _ p f hp hfp _ hdeg
  obtain ⟨r, co, hco, hinj⟩ := GlobalTheory.T.exists_coordinateFunctionals_functionField_extension M W f hdeg
  obtain ⟨hpp, H, hH⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp
  obtain ⟨hfpp, L, hL⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB (f ≫ p)).1 hfp
  haveI := hpp
  haveI := hfpp
  haveI : IsProper f := IsProper.of_comp f p
  haveI : IsNoetherian W := isNoetherian_of_isProjOver hp
  obtain ⟨n, hn, t, ht, htP⟩ := GlobalTheory.T.exists_section_pow_ample_forall_local_condition W H hH
    (fun y c => ∀ (V' : W.Opens), y ∈ V' → ∀ (h : genericPoint M ∈ f ⁻¹ᵁ V')
      (z : Γ(M, f ⁻¹ᵁ V')) (j : Fin r), RegAt y (c * co j (fnOf (f ⁻¹ᵁ V') h z)))
    (fun y c c' hc hc' V' hy h z j => by rw [mul_assoc]; exact hc'.mul (hc V' hy h z j))
    (fun y => by
      obtain ⟨V, hy, d, hd, hd'⟩ := GlobalTheory.T.exists_open_trace_coefficients_nonvanishing M W f L hL co hco y
      exact ⟨V, hy, d, hd, fun y' hy' V' hV' h z j => hd' y' hy' V' hV' h z j⟩)
  exact ⟨r, lbPow H n, (isAmpleLB_pow_iff hH.isLB hn).2 hH, fun B hB =>
    GlobalTheory.T.finrank_sections_pullback_le_mul_twist_of_dominant F M W p f hp co hco hinj (lbPow H n) (isLB_lbPow hH.isLB n) t ht
      (fun y i hi V' hV' h z j => htP y i hi V' hV' h z j) B hB⟩

end GlobalTheory.GlobalSectionsPullback
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueLocalDescentsNearClosedFibreGaloisStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glue_local_descents_near_closedFibre_galois : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U'), ∀ (H : G'.left.Opens) (hH : ∀ σ, a.act σ ⁻¹ᵁ H = H), (∀ g : G'.left, spMap ρ (G'.hom g) = closedPoint R → g ∈ H) → IsCompact (H : Set G'.left) → ∀ (X : Over (Sp R)) (π : H.toScheme ⟶ X.left) (hX : π ≫ X.hom = H.ι ≫ G'.hom ≫ spMap ρ), IsAffineHom π → Surjective π → (∀ σ, (a.act σ).resLE H H (hH σ).ge ≫ π = π) → (∀ x y : H.toScheme, π x = π y → ∃ σ, a.act σ (H.ι x) = H.ι y) → (∀ V : X.left.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(H.toScheme, π ⁻¹ᵁ V), (∀ σ (h : π ⁻¹ᵁ V ≤ ((a.act σ).resLE H H (hH σ).ge) ⁻¹ᵁ (π ⁻¹ᵁ V)), (((a.act σ).resLE H H (hH σ).ge).appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → (∀ x : H.toScheme, spMap ρ (G'.hom (H.ι x)) = closedPoint R → ∃ V : X.left.Opens, π x ∈ V ∧ IsAffineOpen V ∧ Smooth (V.ι ≫ X.hom) ∧ IsIso (pullback.lift (π.resLE V (π ⁻¹ᵁ V) le_rfl) ((π ⁻¹ᵁ V).ι ≫ H.ι ≫ G'.hom) (by rw [Scheme.Hom.resLE_comp_ι_assoc, hX]; simp only [Category.assoc]) : (π ⁻¹ᵁ V).toScheme ⟶ pullback (V.ι ≫ X.hom) (spMap ρ))) → ∃ N : Near (spMap ρ) G', (∀ σ (T : Scheme.{0}) (s : T ⟶ Sp R') (u : T ⟶ N.U.left) (x : T ⟶ G'.left), N.Pt s u x → N.Pt (s ≫ spMap (Gal.hom σ)) u (x ≫ a.act σ)) := by
  first | exact @GlobalTheory.Mum.GlueNear.glue_near | exact GlobalTheory.Mum.GlueNear.glue_near | (intros; apply GlobalTheory.Mum.GlueNear.glue_near <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueOverlapDiagonalAndTransfer
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem glue_overlap_cocycle : ∀ (B S X : Scheme.{0}) (π : S ⟶ B), Surjective π → ∀ (U : Over B) (J : Type) (e : J → (pullback U.hom π ⟶ X)), (∀ j, IsOpenImmersion (e j)) → ∀ (V : J → J → U.left.Opens) (τ : ∀ i j, (V i j).toScheme ⟶ U.left), (∀ (i j : J) (a : ↥(pullback U.hom π)), pullback.fst U.hom π a ∈ V i j ↔ e i a ∈ Set.range (e j)) → (∀ (i j : J) (T : Scheme.{0}) (a b : T ⟶ pullback U.hom π) (v : T ⟶ (V i j).toScheme), a ≫ e i = b ≫ e j → v ≫ (V i j).ι = a ≫ pullback.fst _ _ → v ≫ τ i j = b ≫ pullback.fst _ _) → (∀ i, V i i = ⊤) ∧ (∀ (i j k : J) (x : (V i j).toScheme), (V i j).ι x ∈ V i k → τ i j x ∈ V j k) := by
  intro B S X π hπ U J e he V τ hV hτ
  have hp : Function.Surjective (pullback.fst U.hom π) := (inferInstance : Surjective (pullback.fst U.hom π)).surj
  refine ⟨fun i => ?_, fun i j k x hx => ?_⟩
  · refine eq_top_iff.mpr fun y _ => ?_
    obtain ⟨a, rfl⟩ := hp y
    exact (hV i i a).mpr ⟨a, rfl⟩
  · obtain ⟨a, ha⟩ := hp ((V i j).ι x)
    have hij : e i a ∈ Set.range (e j) := (hV i j a).mp (by
      rw [ha]
      have hx' : (V i j).ι x ∈ Set.range (V i j).ι := ⟨x, rfl⟩
      rwa [Scheme.Opens.range_ι] at hx')
    obtain ⟨b, hb⟩ := hij
    have hik : e i a ∈ Set.range (e k) := (hV i k a).mp (by rw [ha]; exact hx)
    obtain ⟨t, ht1, ht2⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback (e i) (e j)) a b hb.symm
    have hrange : Set.range (pullback.fst (e i) (e j) ≫ pullback.fst U.hom π) ⊆ Set.range (V i j).ι := by
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι]
      show (pullback.fst U.hom π) (pullback.fst (e i) (e j) z) ∈ V i j
      rw [hV i j]
      refine ⟨pullback.snd (e i) (e j) z, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
    let v := IsOpenImmersion.lift (V i j).ι (pullback.fst (e i) (e j) ≫ pullback.fst U.hom π) hrange
    have hv : v ≫ (V i j).ι = pullback.fst (e i) (e j) ≫ pullback.fst U.hom π := IsOpenImmersion.lift_fac _ _ _
    have key := hτ i j _ (pullback.fst (e i) (e j)) (pullback.snd (e i) (e j)) v pullback.condition hv
    have hvt : v t = x := by
      apply (V i j).ι.isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, hv, Scheme.Hom.comp_apply, ht1, ha]
    have : τ i j x = pullback.fst U.hom π b := by
      rw [← hvt, ← Scheme.Hom.comp_apply, key, Scheme.Hom.comp_apply, ht2]
    rw [this, hV j k, hb]
    exact hik

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GraphLocalRingRegularParamsAndDimStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graphLocalRing_regular_params_and_dim : ∀ {K κ' L : Type} [Field K] [Field κ'] [Field L] [Algebra ℂ K]
  [Algebra ℂ κ'] [Algebra ℂ L] [Algebra (K ⊗[ℂ] κ') L] [IsScalarTower ℂ (K ⊗[ℂ] κ') L]
  [IsFractionRing (K ⊗[ℂ] κ') L] (σ : K →ₐ[ℂ] κ') (n : ℕ) (x : Fin n → K),
  Algebra.EssFiniteType ℂ K → Algebra.EssFiniteType ℂ κ' → TrBasis (algebraMap ℂ K) x →
  IsLocalRing.maximalIdeal (GlobalTheory.DiagLoc.loc L σ) =
      Ideal.span (Set.range fun i => GlobalTheory.DiagLoc.toLoc L σ (x i ⊗ₜ[ℂ] 1 - 1 ⊗ₜ[ℂ] σ (x i))) ∧
    ringKrullDim (GlobalTheory.DiagLoc.loc L σ) = n := by
  first | exact @GlobalTheory.DiagLoc.maximalIdeal_eq_span_and_ringKrullDim | exact GlobalTheory.DiagLoc.maximalIdeal_eq_span_and_ringKrullDim | (intros; apply GlobalTheory.DiagLoc.maximalIdeal_eq_span_and_ringKrullDim <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupFibreBaseChangeCommonFieldIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.FibBC

theorem pullCompIso_hom_eq {T S' S : Scheme.{0}} (p : T ⟶ S') (f : S' ⟶ S) (G : Over S) [GrpObj G] :
    (pullCompIso p f G).hom = (Over.pullbackComp p f).hom.app G := Category.comp_id _

theorem pullCompIso_fst {T S' S : Scheme.{0}} (p : T ⟶ S') (f : S' ⟶ S) (G : Over S) [GrpObj G] :
    (pullCompIso p f G).hom.left ≫ pullback.fst _ p ≫ pullback.fst G.hom f = pullback.fst G.hom (p ≫ f) := by
  rw [pullCompIso_hom_eq]
  simp [Over.pullbackComp, Over.mapComp, pullback.lift_fst_assoc, pullback.lift_fst]

theorem pullCompIso_inv_fst {T S' S : Scheme.{0}} (p : T ⟶ S') (f : S' ⟶ S) (G : Over S) [GrpObj G] :
    (pullCompIso p f G).inv.left ≫ pullback.fst G.hom (p ≫ f) = pullback.fst _ p ≫ pullback.fst G.hom f := by
  rw [← pullCompIso_fst, ← Category.assoc, ← Over.comp_left, Iso.inv_hom_id, Over.id_left, Category.id_comp]

theorem pullback_map_fst {S S' : Scheme.{0}} (g : S' ⟶ S) {A B : Over S} (u : A ⟶ B) :
    ((Over.pullback g).map u).left ≫ pullback.fst B.hom g = pullback.fst A.hom g ≫ u.left :=
  pullback.lift_fst _ _ _

theorem fibre_baseChange : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (W' : Type) [CommRing W'] [IsLocalRing W'] (G' : Over (Sp W')) [GrpObj G'] (ξ' : Sp W' ⟶ S) (β : G'.left ⟶ G.left), IsGrpPullback G' G ξ' β → ∀ (k : Type) [Field k] (Y : Over (Sp k)) [GrpObj Y] (κ' : k →+* ResidueField W') (e' : (Over.pullback (spMap (residue W'))).obj G' ≅ (Over.pullback (spMap κ')).obj Y), IsMonHom e'.hom → ∀ (Ω : Type) [Field Ω] (x : Sp Ω ⟶ S) (κ : k →+* Ω) (Ω' : Type) [Field Ω'] (io : Ω →+* Ω') (i₂ : ResidueField W' →+* Ω'), spMap io ≫ x = spMap i₂ ≫ spMap (residue W') ≫ ξ' → io.comp κ = i₂.comp κ' → ∃ (e : (Over.pullback (spMap io ≫ x)).obj G ≅ (Over.pullback (spMap (io.comp κ))).obj Y) (τ : ((Over.pullback (spMap io ≫ x)).obj G).left ⟶ ((Over.pullback (spMap (residue W'))).obj G').left), IsMonHom e.hom ∧ τ ≫ pullback.fst G'.hom (spMap (residue W')) ≫ β = pullback.fst G.hom (spMap io ≫ x) ∧ e.hom.left ≫ pullback.fst Y.hom (spMap (io.comp κ)) = τ ≫ e'.hom.left ≫ pullback.fst Y.hom (spMap κ') := by
  intro S G _ W' _ _ G' _ ξ' β hβ k _ Y _ κ' e' he' Ω _ x κ Ω' _ io i₂ hc hκ
  have hm : spMap i₂ ≫ spMap κ' = spMap (io.comp κ) := by
    rw [hκ, ← Spec.map_comp]; rfl
  rw [← hm]

  have h₁ : IsGrpPullback ((Over.pullback (spMap i₂ ≫ spMap (residue W'))).obj G') G (spMap io ≫ x)
      (pullback.fst G'.hom (spMap i₂ ≫ spMap (residue W')) ≫ β) :=
    ((isGrpPullback_pullback G' (spMap i₂ ≫ spMap (residue W'))).comp hβ).congr
      (by rw [hc, Category.assoc]) rfl
  obtain ⟨e₁, he₁, he₁f⟩ := grpPullback_iso (isGrpPullback_pullback G (spMap io ≫ x)) h₁
  let e₂ := pullCompIso (spMap i₂) (spMap (residue W')) G'
  let e₃ := (Over.pullback (spMap i₂)).mapIso e'
  let e₄ := (pullCompIso (spMap i₂) (spMap κ') Y).symm
  have i₃ : IsMonHom e₃.hom := by show IsMonHom ((Over.pullback (spMap i₂)).map e'.hom); infer_instance
  have i₄ : IsMonHom e₄.hom := by show IsMonHom (pullCompIso (spMap i₂) (spMap κ') Y).inv; infer_instance
  have f₂ : e₂.hom.left ≫ pullback.fst _ (spMap i₂) ≫ pullback.fst G'.hom (spMap (residue W')) =
      pullback.fst G'.hom (spMap i₂ ≫ spMap (residue W')) := pullCompIso_fst _ _ _
  have f₃ : e₃.hom.left ≫ pullback.fst _ (spMap i₂) = pullback.fst _ (spMap i₂) ≫ e'.hom.left :=
    pullback_map_fst _ _
  have f₄ : e₄.hom.left ≫ pullback.fst Y.hom (spMap i₂ ≫ spMap κ') =
      pullback.fst _ (spMap i₂) ≫ pullback.fst Y.hom (spMap κ') := pullCompIso_inv_fst _ _ _
  refine ⟨e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄, e₁.hom.left ≫ e₂.hom.left ≫ pullback.fst _ (spMap i₂), ?_, ?_, ?_⟩
  · show IsMonHom (e₁.hom ≫ e₂.hom ≫ e₃.hom ≫ e₄.hom); infer_instance
  · rw [Category.assoc, Category.assoc, reassoc_of% f₂, he₁f]
  · show (e₁.hom ≫ e₂.hom ≫ e₃.hom ≫ e₄.hom).left ≫ _ = _
    simp only [Over.comp_left, Category.assoc]
    rw [f₄, reassoc_of% f₃]

end GlobalTheory.Mum.FibBC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupLawDescendsGaloisInvariantOpenStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.groupLaw_descends_galois_invariant_open : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U'), ∀ N : Near (spMap ρ) G', (∀ σ (T : Scheme.{0}) (s : T ⟶ Sp R') (u : T ⟶ N.U.left) (x : T ⟶ G'.left), N.Pt s u x → N.Pt (s ≫ spMap (Gal.hom σ)) u (x ≫ a.act σ)) → N.Law := by
  first | exact @GlobalTheory.Mum.law_of_galAct_invariant | exact GlobalTheory.Mum.law_of_galAct_invariant | (intros; apply GlobalTheory.Mum.law_of_galAct_invariant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupPullbackTangentVectorsCompat
section
set_option autoImplicit false

noncomputable section

open NumberField GlobalTheory.ShFam.Pad AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiePull

set_option maxHeartbeats 800000 in

theorem exists_lieBasis_of_tanBasis {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}}
    (t : SAB H X0) {K : Type} [CommRing K] (x0 : Sp K ⟶ X0) (A : Over (Sp K)) [GrpObj A] (θ : A.left ⟶ t.G.left)
    (hθ : IsGrpPullback A t.G x0 θ) {m : ℕ} (u : Fin m → (Sp (DualNumber K) ⟶ t.G.left))
    (hu : ∀ j, IsTanAtG t x0 (u j)) (hc : ∀ w, IsTanAtG t x0 w → ∃! c : Fin m → K, IsCombAtG t x0 u c w) :
    ∃ v : Fin m → (epsR K ⟶ A), IsLieBasis v ∧ ∀ j, (v j).left ≫ θ = u j := by
  classical
  let up : ∀ w : Sp (DualNumber K) ⟶ t.G.left, w ≫ t.G.hom = spMap (algebraMap K (DualNumber K)) ≫ x0 →
      (epsR K ⟶ A) := fun w h => Over.homMk (hθ.1.lift w _ h) (hθ.1.lift_snd _ _ _)
  have hup : ∀ w h, (up w h).left ≫ θ = w := fun w h => hθ.1.lift_fst _ _ _
  have inj : ∀ {T : Over (Sp K)} {a b : T ⟶ A}, a.left ≫ θ = b.left ≫ θ → a = b := fun h =>
    Over.OverMorphism.ext (hθ.1.hom_ext h ((Over.w _).trans (Over.w _).symm))
  have one : ∀ T : Over (Sp K), (1 : T ⟶ A).left ≫ θ = (1 : Over.mk (T.hom ≫ x0) ⟶ t.G).left :=
    fun T => congrArg (fun q => q.left) (map_one (pushHom hθ T))
  have tan : ∀ w : epsR K ⟶ A, IsTangent w ↔ IsTanAtG t x0 (w.left ≫ θ) := fun w => by
    have e : (1 : Chart.sp (R₀ := K) K ⟶ A).left ≫ θ = (1 : Over.mk x0 ⟶ t.G).left :=
      (one _).trans (congrArg (· ≫ (η[t.G]).left) (show Spec.map (CommRingCat.ofHom (RingHom.id K)) ≫ x0 = x0 by simp))
    rw [← Chart.isTan_iff]
    refine ⟨fun h => ⟨Over.w (pushPt hθ.1.w w), ?_⟩, fun h => inj ?_⟩
    · exact (Category.assoc _ _ _).symm.trans ((congrArg (fun q => q.left ≫ θ) h).trans e)
    · exact (Category.assoc _ _ _).trans (h.2.trans e.symm)
  have pr : ∀ {n} (a : Fin n → (epsR K ⟶ A)), (List.ofFn a).prod.left ≫ θ =
      (List.ofFn fun i => (pushPt hθ.1.w (a i) : tEpsG x0 ⟶ t.G)).prod.left := fun a =>
    congrArg (fun q => q.left) ((map_list_prod (pushHom hθ (epsR K)) _).trans (by rw [List.map_ofFn]; rfl))
  have comb : ∀ {n} (c : Fin n → K) (v : Fin n → (epsR K ⟶ A)) w,
      IsLieComb c v w ↔ IsCombAtG t x0 (fun i => (v i).left ≫ θ) c (w.left ≫ θ) := fun c v w => by
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨fun i => pushPt hθ.1.w (a i), fun i => (congrArg (· ≫ θ) (ha i)).trans (Category.assoc _ _ _), (pr a).symm⟩
    · rintro ⟨a, ha, hw⟩
      refine ⟨fun i => up (a i).left (Over.w _), fun i => hθ.1.hom_ext ?_ ?_, inj (hw.symm.trans (Eq.trans ?_ (pr _).symm))⟩
      · exact (hup _ _).trans ((ha i).trans (Category.assoc _ _ _).symm)
      · refine (Over.w (up (a i).left (Over.w _))).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
        refine Eq.trans ?_ (congrArg (spMap (epsScaleR (c i)) ≫ ·) (Over.w (v i))).symm
        exact (Over.w (Chart.spMap (Chart.scaleD (c i)))).symm
      · have : a = fun i => (pushPt hθ.1.w (up (a i).left (Over.w _)) : tEpsG x0 ⟶ t.G) :=
          funext fun i => Over.OverMorphism.ext (hup (a i).left (Over.w _)).symm
        exact congrArg (fun q : _ → (tEpsG x0 ⟶ t.G) => (List.ofFn q).prod.left) this
  let v : Fin m → (epsR K ⟶ A) := fun j => up (u j) (hu j).1
  have hv : (fun i => (v i).left ≫ θ) = u := funext fun j => hup _ _
  refine ⟨v, ⟨fun j => (tan _).2 (by rw [hup]; exact hu j), fun w hw => ?_⟩, fun j => hup _ _⟩
  have key : ∀ c, IsLieComb c v w ↔ IsCombAtG t x0 u c (w.left ≫ θ) := fun c => by
    rw [comb, hv]
  obtain ⟨c, hc1, hc2⟩ := hc _ ((tan w).1 hw)
  exact ⟨c, (key c).2 hc1, fun c' h' => hc2 c' ((key c').1 h')⟩

theorem lieBasis_of_tanBasis : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X0 : Scheme.{0}} (t : ReciprocityTheory.ChartRestriction.G.Geo.Tor.SAB H X0) {K : Type} [CommRing K] (x0 : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K ⟶ X0) (A : Over (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)) [GrpObj A] (θ : A.left ⟶ t.G.left), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback A t.G x0 θ → ∀ {m : ℕ} (u : Fin m → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (DualNumber K) ⟶ t.G.left)), (∀ j, Formalism.L2.Pj.IsTanAtG t x0 (u j)) → (∀ w, Formalism.L2.Pj.IsTanAtG t x0 w → ∃! c : Fin m → K, Formalism.L2.Pj.IsCombAtG t x0 u c w) → ∃ v : Fin m → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsR K ⟶ A), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsLieBasis v ∧ ∀ j, (v j).left ≫ θ = u j :=
  by
  intro E _ _ _ H X0 t K _ x0 A _ θ hθ m u hu hc
  exact exists_lieBasis_of_tanBasis t x0 A θ hθ u hu hc

end GlobalTheory.LiePull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackDivisionPointsPushEq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DivPush

theorem push_div_pts : ∀ {S S₀ : Scheme.{0}} (f : S ⟶ S₀) (G : Over S) [GrpObj G] [IsCommMonObj G] (G₀ : Over S₀) [GrpObj G₀] [IsCommMonObj G₀] (β : G.left ⟶ G₀.left), IsGrpPullback G G₀ f β → ∀ (n r : ℕ) (d : Fin r → (𝟙_ (Over S) ⟶ G)) (c : (Fin r → ℤ) → (𝟙_ (Over S₀) ⟶ G₀)), (∀ a a', c (a + a') = c a * c a') → (∀ i, (d i ^ n).left ≫ β = f ≫ (c (Pi.single i 1)).left) → ∀ a, (∏ i, d i ^ ((n : ℤ) * a i)).left ≫ β = f ≫ (c a).left := by
  intro S S₀ f G _ _ G₀ _ _ β hp n r d c hc hd a
  let T : Over S := 𝟙_ (Over S)
  let U : Over.mk (T.hom ≫ f) ⟶ 𝟙_ (Over S₀) := toUnit _
  have hU : U.left = f := by
    simp [U, T, Over.toUnit_left]
  let cH : (Fin r → ℤ) →+ Additive (𝟙_ (Over S₀) ⟶ G₀) :=
    AddMonoidHom.mk' (fun a => Additive.ofMul (c a)) (fun a a' => by simp [hc])
  have hca : c a = ∏ i, c (Pi.single i 1) ^ a i := by
    have e : a = ∑ i, a i • (Pi.single i (1 : ℤ) : Fin r → ℤ) := by
      ext j; simp [Finset.sum_apply, Pi.single_apply]
    have := congrArg cH e
    rw [map_sum] at this
    simp only [map_zsmul] at this
    exact congrArg Additive.toMul this
  have hdi : ∀ i, pushHom hp T (d i ^ n) = preHom U (c (Pi.single i 1)) := by
    intro i
    apply Over.OverMorphism.ext
    show (d i ^ n).left ≫ β = U.left ≫ (c (Pi.single i 1)).left
    rw [hU]; exact hd i
  have key : pushHom hp T (∏ i, d i ^ ((n : ℤ) * a i)) = preHom U (c a) := by
    rw [hca, map_prod, map_prod]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [map_zpow, map_zpow, zpow_mul, zpow_natCast, ← map_pow, hdi]
  have := congrArg (fun z => z.left) key
  rw [← hU]
  exact this

end GlobalTheory.DivPush
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackPointsLiftMulInv
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem grpPullback_points_lift_mul_inv : ∀ (T S : Scheme.{0}) (f : S ⟶ T) (G : Over T) [GrpObj G] (G' : Over S) [GrpObj G'] (β : G'.left ⟶ G.left), IsGrpPullback G' G f β → ∀ (Z' : Over S) (Z : Over T) (ζ : Z'.left ⟶ Z.left), ζ ≫ Z.hom = Z'.hom ≫ f → (∀ u : Z ⟶ G, ∃ u' : Z' ⟶ G', u'.left ≫ β = ζ ≫ u.left) ∧ ∀ (u v : Z ⟶ G) (u' v' : Z' ⟶ G'), u'.left ≫ β = ζ ≫ u.left → v'.left ≫ β = ζ ≫ v.left → (u' * v').left ≫ β = ζ ≫ (u * v).left ∧ (u'⁻¹).left ≫ β = ζ ≫ (u⁻¹).left := by
  intro T S f G _ G' _ β hpb Z' Z ζ hζ
  have hw : ∀ u : Z ⟶ G, (ζ ≫ u.left) ≫ G.hom = Z'.hom ≫ f := fun u => by
    rw [Category.assoc, Over.w u, hζ]
  refine ⟨fun u => ⟨Over.homMk (hpb.1.lift (ζ ≫ u.left) Z'.hom (hw u)) (hpb.1.lift_snd _ _ _),
    hpb.1.lift_fst _ _ _⟩, ?_⟩
  intro u v u' v' hu hv
  let ζ' : Over.mk (Z'.hom ≫ f) ⟶ Z := Over.homMk ζ hζ
  let φ : (Z' ⟶ G') → (Over.mk (Z'.hom ≫ f) ⟶ G) := fun w =>
    Over.homMk (w.left ≫ β) (by
      change (w.left ≫ β) ≫ G.hom = Z'.hom ≫ f
      rw [Category.assoc, hpb.1.w, ← Category.assoc, Over.w w])
  have hφ : ∀ a b, φ (a * b) = φ a * φ b := fun a b =>
    Over.OverMorphism.ext (hpb.2 Z' a b (φ a) (φ b) rfl rfl).symm
  let ψ := MonoidHom.mk' φ hφ
  have hu' : ψ u' = ζ' ≫ u := Over.OverMorphism.ext hu
  have hv' : ψ v' = ζ' ≫ v := Over.OverMorphism.ext hv
  constructor
  · have h : ψ (u' * v') = ζ' ≫ (u * v) := by rw [map_mul, hu', hv', MonObj.comp_mul]
    exact congrArg CommaMorphism.left h
  · have h : ψ (u'⁻¹) = ζ' ≫ (u⁻¹) := by rw [map_inv, hu', GrpObj.comp_inv]
    exact congrArg CommaMorphism.left h

end GlobalTheory.Mum
end

