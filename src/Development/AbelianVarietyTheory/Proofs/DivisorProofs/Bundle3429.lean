import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapGermFromSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3393
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2517
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2935
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2680
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2739
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2966
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2756
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2762
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2710
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2702
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2692
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2722
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2746
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3409
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3381
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3373
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0026
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2065
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3330
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1200
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2180
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0677
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3391
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3405
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3401
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3410
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2643
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ReductionSurjectiveOfIsNilpotent
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.InvariantVectorFieldsBasisVerticalDerivations
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0044
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3384
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3411
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3377

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyValuesDetOmegaDeltaLocalUnits
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

open Classical

namespace GlobalTheory.KeyValsPf

theorem smooth_bG : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (g : ℕ) (R : Type) [CommRing R] (ξ : Sp R ⟶ S),
    SmoothOfRelativeDimension g G.hom → SmoothOfRelativeDimension g (KeyVals.bG G ξ).hom := by
  intro S G _ g R _ ξ h
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange g
  exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension g) (isGrpPullback_pullback G ξ).1 h

theorem semi_bG : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R : Type) [CommRing R] (ξ : Sp R ⟶ S),
    IsSemiAbelian G → IsSemiAbelian (KeyVals.bG G ξ) := by
  intro S G _ R _ ξ h
  exact IsSemiAbelian.pullback ξ G h

theorem mem_abLocus_bG {S : Scheme.{0}} (G : Over S) {R : Type} [CommRing R] (ξ : Sp R ⟶ S) (q : Sp R)
    (h : ξ q ∈ abLocus G) : q ∈ abLocus (KeyVals.bG G ξ) := by
  intro K _ _ t ⟨z, hz⟩
  have := h K (t ≫ ξ) ⟨z, by rw [← hz]; rfl⟩
  have P := (IsPullback.of_hasPullback (pullback.snd G.hom ξ) t).paste_horiz (IsPullback.of_hasPullback G.hom ξ)
  have e := P.isoPullback_hom_snd
  show IsProper (pullback.snd (pullback.snd G.hom ξ) t)
  rw [← e]
  infer_instance

theorem mem_abLocus_of_bG {S : Scheme.{0}} (G : Over S) {R : Type} [CommRing R] (ξ : Sp R ⟶ S) [IsOpenImmersion ξ] (q : Sp R)
    (h : q ∈ abLocus (KeyVals.bG G ξ)) : ξ q ∈ abLocus G := by
  intro K _ _ t ⟨z, hz⟩
  have hr : Set.range t ⊆ Set.range ξ := by
    rintro _ ⟨w, rfl⟩
    rw [Subsingleton.elim w z]
    exact ⟨q, hz.symm⟩
  obtain ⟨u, rfl⟩ : ∃ u : Sp K ⟶ Sp R, u ≫ ξ = t := ⟨IsOpenImmersion.lift ξ t hr, IsOpenImmersion.lift_fac _ _ _⟩
  have : IsProper (pullback.snd (pullback.snd G.hom ξ) u) := h K u ⟨z, ξ.isOpenEmbedding.injective hz⟩
  have P := (IsPullback.of_hasPullback (pullback.snd G.hom ξ) u).paste_horiz (IsPullback.of_hasPullback G.hom ξ)
  rw [← P.isoPullback_inv_snd]
  infer_instance

theorem abLocus_generic : ∀ (S : Scheme.{0}) [IsIntegral S] (G : Over S) [GrpObj G], genericPoint S ∈ abLocus G →
    abLocus (KeyVals.bG G (KeyVals.genPt S)) = Set.univ := by
  intro S _ G _ h
  refine Set.eq_univ_of_forall fun q => mem_abLocus_bG G _ q ?_
  have hp : KeyVals.genPt S q ∈ Set.range (S.fromSpecStalk (genericPoint S)) := ⟨q, rfl⟩
  rw [Scheme.range_fromSpecStalk] at hp
  rwa [(hp.antisymm (genericPoint_specializes _)).eq]

theorem abLocus_affine : ∀ (S : Scheme.{0}) [IsIntegral S] (G : Over S) [GrpObj G] (W : S.Opens) (hW : IsAffineOpen W), (W : Set S).Nonempty →
    IsOpen (abLocus G) → genericPoint S ∈ abLocus G → IsOpen (abLocus (KeyVals.bG G hW.fromSpec)) ∧
      Set.range (spMap (algebraMap Γ(S, W) (FractionRing Γ(S, W)))).base ⊆ abLocus (KeyVals.bG G hW.fromSpec) := by
  intro S _ G _ W hW hne hop h
  haveI : Nonempty W := ⟨⟨hne.some, hne.some_mem⟩⟩
  have e : abLocus (KeyVals.bG G hW.fromSpec) = hW.fromSpec ⁻¹' abLocus G :=
    Set.ext fun q => ⟨mem_abLocus_of_bG (R := Γ(S, W)) G hW.fromSpec q, mem_abLocus_bG (R := Γ(S, W)) G hW.fromSpec q⟩
  have ho : IsOpen (hW.fromSpec ⁻¹' abLocus G) := hop.preimage hW.fromSpec.continuous
  rw [e]
  refine ⟨ho, ?_⟩
  rintro _ ⟨z, rfl⟩
  obtain ⟨q, hq⟩ : genericPoint S ∈ Set.range hW.fromSpec := by
    rw [hW.range_fromSpec]
    exact ((genericPoint_spec S).mem_open_set_iff W.isOpen).2 ⟨hne.some, trivial, hne.some_mem⟩
  refine Specializes.mem_open (y := q) ?_ ho (show hW.fromSpec q ∈ abLocus G from hq ▸ h)
  refine (PrimeSpectrum.le_iff_specializes _ _).1 ?_
  intro a ha
  have ha' : algebraMap Γ(S, W) (FractionRing Γ(S, W)) a ∈ (show PrimeSpectrum (FractionRing Γ(S, W)) from z).asIdeal := ha
  have hz : (show PrimeSpectrum (FractionRing Γ(S, W)) from z).asIdeal = ⊥ := Ideal.eq_bot_of_prime _
  rw [hz, Ideal.mem_bot, map_eq_zero_iff _ (IsFractionRing.injective _ _)] at ha'
  exact ha' ▸ Ideal.zero_mem _

theorem exists_keyVal : ∀ κ : Rule, ∀ (S : Scheme.{0}) [IsIntegral S] [CharZero (KeyVals.FF S)] (s : S ⟶ Sp ℤ) (G : Over S) [GrpObj G] [IsCommMonObj G] (g : ℕ) (L : RigLB G) (δ : LB S)
    (σ : (CechPic.tens L.L (δ.pull G.hom)).Sec), 1 ≤ g → Geo.Tor.IsNormalScheme S → LocallyOfFiniteType s →
    CharZero Γ(S, ⊤) → IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → (abLocus G).Nonempty → IsOpen (abLocus G) →
    L.IsSymmetric → δ.IsLB → PolOnAb G L.L → UnifAlong G L.L → NzFib σ →
    ∀ (c : VB.Chart (LieVB.omega G) g) (i : δ.ι), genericPoint S ∈ c.U ⊓ δ.U i → ∃ v, KeyVals.IsKeyVal κ g L σ c i v := by
  intro κ S _ _ s G _ _ g L δ σ hg hN hs h0 hsa hsm hne hop hsym hδ hpol hunif hnz c i hgen
  have hgab : genericPoint S ∈ abLocus G := by
    obtain ⟨p, hp⟩ := hne
    exact ((genericPoint_spec S).mem_open_set_iff hop).2 ⟨p, trivial, hp⟩
  obtain ⟨t, ht⟩ := GlobalTheory.T.exists_localFormOfTensorSection_in_chart S G L δ σ i _ (KeyVals.genPt S) hδ (KeyVals.genPt_le _ hgen.2)
  obtain ⟨y, hy, hyb⟩ := GlobalTheory.T.exists_dualTangentBasis_pulledCotangentChartFrame S G g c _ (KeyVals.genPt S) hsa hsm (KeyVals.genPt_le _ hgen.1)
  have hab := abLocus_generic S G hgab
  obtain ⟨x, hxg, hx⟩ := GlobalTheory.KeyDatumAb.exists_keyOn (KeyVals.FF S) (KeyVals.FF S) (RingHom.id _)
    (KeyVals.bG G (KeyVals.genPt S)) (KeyVals.bL L (KeyVals.genPt S)) t g y hg (semi_bG S G _ _ hsa)
    (smooth_bG S G g _ _ hsm) (by rw [hab]; exact isOpen_univ) (GlobalTheory.T.isSymmetric_rigidifiedBundleBaseChange S G L _ _ hsym) (GlobalTheory.T.principalPolarisationOnAbLocus_genericFibre S G L hop hgab hpol) hyb
    (GlobalTheory.T.sectionNonzeroOnEveryFibre_localFormBaseChange S G L δ σ i _ _ t (KeyVals.genPt_le _ hgen.2) ht hnz) (by rw [hab]; exact Set.subset_univ _)
  exact ⟨_, t, y, x, hxg, ht, hy, hx, rfl⟩

theorem keyVal_unit : ∀ κ : Rule, Homog (fun _ => 1) κ → Funct κ → KeyLoc κ → ∀ (S : Scheme.{0}) [IsIntegral S] [CharZero (KeyVals.FF S)] (s : S ⟶ Sp ℤ) (G : Over S) [GrpObj G] [IsCommMonObj G] (g : ℕ) (L : RigLB G) (δ : LB S)
    (σ : (CechPic.tens L.L (δ.pull G.hom)).Sec), 1 ≤ g → Geo.Tor.IsNormalScheme S → LocallyOfFiniteType s →
    CharZero Γ(S, ⊤) → IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → (abLocus G).Nonempty → IsOpen (abLocus G) →
    L.IsSymmetric → δ.IsLB → PolOnAb G L.L → UnifAlong G L.L → NzFib σ →
    ∀ (c : VB.Chart (LieVB.omega G) g) (i : δ.ι) (v : KeyVals.FF S), KeyVals.IsKeyVal κ g L σ c i v → ∀ p ∈ c.U ⊓ δ.U i,
      ∃ (V : S.Opens) (_ : V ≤ c.U ⊓ δ.U i) (_ : p ∈ V) (u : Γ(S, V)ˣ), ∀ h : genericPoint S ∈ V,
        S.presheaf.germ V (genericPoint S) h (u : Γ(S, V)) = v := by
  intro κ hH hF hL S _ _ s G _ _ g L δ σ hg hN hs h0 hsa hsm hne hop hsym hδ hpol hunif hnz c i v hv p hp
  obtain ⟨t', y', x, hxg, ht', hy', hx, rfl⟩ := hv
  have hgab : genericPoint S ∈ abLocus G := by
    obtain ⟨p, hp⟩ := hne
    exact ((genericPoint_spec S).mem_open_set_iff hop).2 ⟨p, trivial, hp⟩
  obtain ⟨W, hW, hpW, hle⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 S.isBasis_affineOpens) hp
  have hW : IsAffineOpen W := hW
  haveI : Nonempty W := ⟨⟨p, hpW⟩⟩
  obtain ⟨hic, hcz, hft⟩ := GlobalTheory.T.affineOpen_ring_normal_charZero_finiteType_over_int S s W hW ⟨p, hpW⟩ hN hs h0
  haveI : IsNoetherianRing Γ(S, W) := Algebra.FiniteType.isNoetherianRing ℤ _
  have hr : ∀ U : S.Opens, W ≤ U → ⊤ ≤ hW.fromSpec ⁻¹ᵁ U := fun U h q _ =>
    h (show hW.fromSpec q ∈ (W : Set S) from hW.range_fromSpec ▸ ⟨q, rfl⟩)
  have hri := hr _ (hle.trans inf_le_right)
  obtain ⟨t, ht⟩ := GlobalTheory.T.exists_localFormOfTensorSection_in_chart S G L δ σ i Γ(S, W) hW.fromSpec hδ hri
  obtain ⟨y, hy, hyb⟩ := GlobalTheory.T.exists_dualTangentBasis_pulledCotangentChartFrame S G g c Γ(S, W) hW.fromSpec hsa hsm (hr _ (hle.trans inf_le_left))
  obtain ⟨hopW, habW⟩ := abLocus_affine S G W hW ⟨p, hpW⟩ hop hgab
  have hsaW := semi_bG S G Γ(S, W) hW.fromSpec hsa
  have hsmW := smooth_bG S G g Γ(S, W) hW.fromSpec hsm
  have hsyW := GlobalTheory.T.isSymmetric_rigidifiedBundleBaseChange S G L Γ(S, W) hW.fromSpec hsym
  have hpoW := GlobalTheory.T.principalPolarisationOnAbLocus_restrict_affineOpen S G L W hW hop hpol
  have hnzW := GlobalTheory.T.sectionNonzeroOnEveryFibre_localFormBaseChange S G L δ σ i Γ(S, W) hW.fromSpec t hri ht hnz
  obtain ⟨z, hzg, hz⟩ := GlobalTheory.KeyDatumAb.exists_keyOn Γ(S, W) (FractionRing Γ(S, W)) (algebraMap _ _)
    (KeyVals.bG G hW.fromSpec) (KeyVals.bL L hW.fromSpec) t g y hg hsaW hsmW hopW hsyW hpoW hyb hnzW habW
  subst hzg
  obtain ⟨u, hu⟩ := hL Γ(S, W) (KeyVals.bG G hW.fromSpec) (KeyVals.bL L hW.fromSpec) t z y hsaW hsmW hopW hsyW hpoW
    (GlobalTheory.T.uniformisedAlongAllTraits_restrict_affineOpen S G L W hW hsa hunif) hyb hnzW hz
  refine ⟨W, hle, hpW, u, fun h => ?_⟩
  let r : Γ(S, W) →+* KeyVals.FF S := (S.presheaf.germ W (genericPoint S) h).hom
  have hinj : Function.Injective r := germ_injective_of_isIntegral S (genericPoint S) h
  let e : FractionRing Γ(S, W) →+* KeyVals.FF S := IsFractionRing.lift hinj
  have he : (RingHom.id _).comp r = e.comp (algebraMap _ _) := RingHom.ext fun a => (IsFractionRing.lift_algebraMap hinj a).symm
  have hξ := KeyVals.spMap_germ_fromSpec W hW h
  have hx' := GlobalTheory.T.fibreDatum_baseChange_to_coarserPoint S G _ L δ σ i Γ(S, W) (KeyVals.FF S) (KeyVals.FF S) hW.fromSpec r (KeyVals.genPt S) (RingHom.id _)
    t y t' y' x hxg hξ hri ht ht' (GlobalTheory.T.dualTangentBasis_pulledFrame_compatible_pointChange S G _ c Γ(S, W) (KeyVals.FF S) hW.fromSpec r (KeyVals.genPt S) y y' hξ hsa hsm hy hy') hx
  rw [he] at hx'
  have hpb := GlobalTheory.KeyEven.keyPB_of_keyOn_comp Γ(S, W) (FractionRing Γ(S, W)) (KeyVals.FF S) (algebraMap _ _) e
    (KeyVals.bG G hW.fromSpec) (KeyVals.bL L hW.fromSpec) t _ y z x rfl hxg hz hx'
  rw [hF _ _ e z x hpb, hu]
  exact (IsFractionRing.lift_algebraMap hinj _).symm

theorem keyVal_compat : ∀ κ : Rule, Homog (fun _ => 1) κ → Funct κ → ∀ (S : Scheme.{0}) [IsIntegral S] [CharZero (KeyVals.FF S)]
    (G : Over S) [GrpObj G] [IsCommMonObj G] (g : ℕ) (L : RigLB G) (δ : LB S) (σ : (CechPic.tens L.L (δ.pull G.hom)).Sec),
    IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → δ.IsLB →
    ∀ (c c' : VB.Chart (LieVB.omega G) g) (i i' : δ.ι) (v v' : KeyVals.FF S)
      (h1 : genericPoint S ∈ (VB.det (LieVB.omega G) g).U c ⊓ (VB.det (LieVB.omega G) g).U c')
      (h2 : genericPoint S ∈ δ.U i ⊓ δ.U i'),
      KeyVals.IsKeyVal κ g L σ c i v → KeyVals.IsKeyVal κ g L σ c' i' v' →
      v * S.presheaf.germ _ (genericPoint S) h2 (δ.g i i' : Γ(S, δ.U i ⊓ δ.U i')) ^ 8 =
        S.presheaf.germ _ (genericPoint S) h1
          ((VB.det (LieVB.omega G) g).g c c' : Γ(S, (VB.det (LieVB.omega G) g).U c ⊓ (VB.det (LieVB.omega G) g).U c')) ^ 4 * v' := by
  intro κ hH hF S _ _ G _ _ g L δ σ hsa hsm hδ c c' i i' v v' h1 h2 hv hv'
  obtain ⟨t, y, x, hg, ht, hy, hk, rfl⟩ := hv
  obtain ⟨t', y', x', hg', ht', hy', hk', rfl⟩ := hv'
  obtain ⟨M, hM, hdet⟩ := GlobalTheory.T.dualTangentVectors_genericFibre_det_eq_detOmegaTrans S G g hsa hsm c c' h1 y y' hy hy'
  have hs := GlobalTheory.T.localFormsTensorSection_genericFibre_transitionGerm S G L δ σ hδ i i' h2 t t' ht ht'
  have := GlobalTheory.KeyEven.keyValue_homog_of_fibres κ hH hF (KeyVals.FF S) (KeyVals.bG G (KeyVals.genPt S)) (KeyVals.bL L (KeyVals.genPt S)) t' t g y' y
    x' x hg' hg _ M hk' hk hs hM
  rw [← hdet, mul_comm]
  exact this

theorem keyVals : ∀ κ : Rule, Homog (fun _ => 1) κ → Funct κ → KeyLoc κ →
  ∀ (S : Scheme.{0}) [IsIntegral S] (s : S ⟶ Sp ℤ) (G : Over S) [GrpObj G] [IsCommMonObj G] (g : ℕ) (L : RigLB G) (δ : LB S)
    (σ : (CechPic.tens L.L (δ.pull G.hom)).Sec), 1 ≤ g → Geo.Tor.IsNormalScheme S → LocallyOfFiniteType s →
    CharZero Γ(S, ⊤) → IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → (abLocus G).Nonempty → IsOpen (abLocus G) →
    L.IsSymmetric → δ.IsLB → PolOnAb G L.L → UnifAlong G L.L → NzFib σ →
    ∃ f : (VB.det (LieVB.omega G) g).ι → δ.ι → S.presheaf.stalk (genericPoint S),
      (∀ c i, ∀ x ∈ (VB.det (LieVB.omega G) g).U c ⊓ δ.U i, ∃ (V : S.Opens) (_ : V ≤ (VB.det (LieVB.omega G) g).U c ⊓ δ.U i)
        (_ : x ∈ V) (u : Γ(S, V)ˣ), ∀ h : genericPoint S ∈ V, S.presheaf.germ V (genericPoint S) h (u : Γ(S, V)) = f c i) ∧
      (∀ c c' i i' (h1 : genericPoint S ∈ (VB.det (LieVB.omega G) g).U c ⊓ (VB.det (LieVB.omega G) g).U c')
        (h2 : genericPoint S ∈ δ.U i ⊓ δ.U i'),
        f c i * S.presheaf.germ _ (genericPoint S) h2 (δ.g i i' : Γ(S, δ.U i ⊓ δ.U i')) ^ 8 =
          S.presheaf.germ _ (genericPoint S) h1
            ((VB.det (LieVB.omega G) g).g c c' : Γ(S, (VB.det (LieVB.omega G) g).U c ⊓ (VB.det (LieVB.omega G) g).U c')) ^ 4 * f c' i') := by
  intro κ hH hF hL S _ s G _ _ g L δ σ hg hN hs h0 hsa hsm hne hop hsym hδ hpol hunif hnz
  haveI : CharZero (KeyVals.FF S) :=
    charZero_of_injective_ringHom (f := (S.presheaf.germ ⊤ (genericPoint S) trivial).hom)
      (germ_injective_of_isIntegral S (U := ⊤) (genericPoint S) trivial)
  let f : (VB.det (LieVB.omega G) g).ι → δ.ι → S.presheaf.stalk (genericPoint S) := fun c i =>
    if h : ∃ v, KeyVals.IsKeyVal κ g L σ c i v then h.choose else 1
  have hf : ∀ c i, genericPoint S ∈ (VB.det (LieVB.omega G) g).U c ⊓ δ.U i → KeyVals.IsKeyVal κ g L σ c i (f c i) := by
    intro c i h
    have ex := exists_keyVal κ S s G g L δ σ hg hN hs h0 hsa hsm hne hop hsym hδ hpol hunif hnz c i h
    simp only [f, dif_pos ex]
    exact ex.choose_spec
  have hgen : ∀ U : S.Opens, (U : Set S).Nonempty → genericPoint S ∈ U := fun U ⟨p, hp⟩ =>
    ((genericPoint_spec S).mem_open_set_iff U.isOpen).2 ⟨p, trivial, hp⟩
  refine ⟨f, fun c i p hp => ?_, fun c c' i i' h1 h2 => ?_⟩
  · exact keyVal_unit κ hH hF hL S s G g L δ σ hg hN hs h0 hsa hsm hne hop hsym hδ hpol hunif hnz c i (f c i)
      (hf c i (hgen _ ⟨p, hp⟩)) p hp
  · exact keyVal_compat κ hH hF S G g L δ σ hsa hsm hδ c c' i i' (f c i) (f c' i') h1 h2
      (hf c i ⟨h1.1, h2.1⟩) (hf c' i' ⟨h1.2, h2.2⟩)

end GlobalTheory.KeyValsPf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopLePreimageNonemptyOpenOfPointValueInjectiveStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.top_le_preimage_nonempty_open_of_pointValue_injective : ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)), ∀ (F : Type) [Field F] (ψ : K →+* F) (ξ : Sp F ⟶ P₀.A.left), ξ ≫ P₀.A.hom = spMap ψ → (∀ O (f : Γ(P₀.A.left, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 → f = 0) → ∀ O : P₀.A.left.Opens, (O : Set P₀.A.left).Nonempty → ⊤ ≤ ξ ⁻¹ᵁ O := by
  first | exact @GlobalTheory.GenPtOpen.top_le_preimage_of_valR_injective | exact GlobalTheory.GenPtOpen.top_le_preimage_of_valR_injective | (intros; apply GlobalTheory.GenPtOpen.top_le_preimage_of_valR_injective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricChartCompGenericFibreInclusionEqSpecChartMaStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toricChart_comp_genericFibreInclusion_eq_spec_chartMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (U : Y.X.affineOpens) (k : Type) [Field k] (m d : ℕ) (ξ : Sp (ChartRing k m d) ⟶ gen Y) (hx : ξ (closedPoint _) ∈ genι Y ⁻¹ᵁ U.1), ξ ≫ genι Y = spMap (GlobalTheory.LocReg.chartHom Y U ξ hx) ≫ chart U := by
  first | exact @GlobalTheory.LocReg.comp_genι_eq_spMap_chartHom | exact GlobalTheory.LocReg.comp_genι_eq_spMap_chartHom | (intros; apply GlobalTheory.LocReg.comp_genι_eq_spMap_chartHom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricChartRingMapFlatAndComapMaximalIdealStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toricChart_ringMap_flat_and_comap_maximalIdeal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (U : Y.X.affineOpens) (k : Type) [Field k] (m d : ℕ) (ξ : Sp (ChartRing k m d) ⟶ gen Y) (hx : ξ (closedPoint _) ∈ genι Y ⁻¹ᵁ U.1), IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → ∀ mm : Ideal Γ(Y.X, U.1), mm.IsMaximal → (∀ f ∈ mm, genι Y (ξ (closedPoint _)) ∉ Y.X.basicOpen f) → (GlobalTheory.LocReg.chartHom Y U ξ hx).Flat ∧ (maximalIdeal (ChartRing k m d)).comap (GlobalTheory.LocReg.chartHom Y U ξ hx) = mm := by
  first | exact @GlobalTheory.LocRegFlat.chartHom_flat_comap | exact GlobalTheory.LocRegFlat.chartHom_flat_comap | (intros; apply GlobalTheory.LocRegFlat.chartHom_flat_comap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalChartSectionBound
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSApp.BigMoving

theorem dim_eq : ∀ (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    SmoothOfRelativeDimension D p → topologicalKrullDim X = D := by
  intro k _ X _ p D hp
  have hc (U : X.Opens) (hU : IsAffineOpen U) (h : (U : Set X).Nonempty) :
      topologicalKrullDim (U : Set X) = D := by
    rw [topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding hU.range_fromSpec]
    exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := Γ(X, U))).trans
      (GlobalTheory.SmoothDim.ringKrullDim_affineOpen k X p D hp U hU h)
  refine le_antisymm (topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_) ?_
  · obtain ⟨U, hU, hx, -⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens (Opens.mem_top x)
    exact ⟨U, U.isOpen, hx, (hc U hU ⟨x, hx⟩).le⟩
  · obtain ⟨U, hU, hx, -⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens (Opens.mem_top (genericPoint X))
    exact (hc U hU ⟨_, hx⟩).ge.trans (topologicalKrullDim_subspace_le _ _)

end GlobalTheory.HSApp.BigMoving
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantHeatOperatorActsOnFourierTerms
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Heat

theorem heat_acts_on_terms : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (h : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D), IsBasic Y h → ∀ (k : ℕ) (α : Dd.toPre.X) (σ : Dd.toPre.SecB k α), ∃ σ', TActs Y h k α σ σ' := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y n v dd hv D h hb k α σ
  obtain ⟨τ, hτ⟩ := GlobalTheory.RayEv.exists_sec_fourierTerm R Dd.toPre O oa Y k α σ
  obtain ⟨τ', hτ'⟩ := GlobalTheory.T.exists_heatOperator_glued_pullbackBundlePower Y.H Y.q.left Dd.toPre.P.L Dd.toPre.P.isLB dd (fun a => (hv a).1) (⇑D) h k τ
  have hE : ∀ a (β : Dd.toPre.X) (V : Y.H.left.Opens) f, IsWt Y β V f → IsWt Y β V (dd a V f) :=
    fun a => GlobalTheory.T.isRaynaudTorusWeightFunction_invariantField Y (v a) (dd a) (hv a)
  choose V hV using fun i => (hb i).1
  have hle : ∀ i, h.W i ≤ LB.wchart Dd.toPre.P.L (fun _ : Fin 1 => Y.q.left) (fun _ => h.j i) :=
    fun i x hx => Set.mem_iInter.2 fun _ => h.le i hx
  have hw : ∀ i, IsWt Y α (h.W i) (rsT (τ'.f fun _ => h.j i) (h.W i)) := by
    intro i
    rw [hτ' i]
    exact GlobalTheory.T.torusInvariant_heatOperator_preserves_weight Y dd _ h hE hb i k α _ (GlobalTheory.T.raynaudFourierTerm_chartFunctions_isWeight Y k α σ τ hτ _ _ (hle i))
  obtain ⟨σ', hσ'⟩ := GlobalTheory.T.isRaynaudFourierTerm_of_isWeight Y k α τ' h.J V (fun i _ => h.j i) (by simp only [← hV]; exact h.cover)
    (fun i => by rw [← hV i]; exact hle i) (fun i => by rw [← hV i]; exact hw i)
  exact ⟨σ', τ, τ', hτ, hσ', hτ'⟩

end GlobalTheory.Heat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantLiftAddInvariantCombinationStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusInvariantLift_add_invariantCombination : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (V : Dd.toPre.P.A.left.Opens) (d₀ : Fld Y.H.left) (y : Fin n → Γ(Y.H.left, Y.q.left ⁻¹ᵁ V)), IsLift Y.H ⇑D (Y.q.left ⁻¹ᵁ V) d₀ → (∀ (α : Dd.toPre.X) (V' : Dd.toPre.P.A.left.Opens), Y.q.left ⁻¹ᵁ V' ≤ Y.q.left ⁻¹ᵁ V → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') (d₀ _ f)) → (∀ a, IsWt Y 0 _ (y a)) → IsLift Y.H ⇑D (Y.q.left ⁻¹ᵁ V) (fun W f => d₀ W f + ∑ a, rsT (y a) W * dd a W f) ∧ (∀ (α : Dd.toPre.X) (V' : Dd.toPre.P.A.left.Opens), Y.q.left ⁻¹ᵁ V' ≤ Y.q.left ⁻¹ᵁ V → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') ((fun W f => d₀ W f + ∑ a, rsT (y a) W * dd a W f) _ f)) := by
  first | exact @GlobalTheory.Heat.Adjust.isLift_add_invComb | exact GlobalTheory.Heat.Adjust.isLift_add_invComb | (intros; apply GlobalTheory.Heat.Adjust.isLift_add_invComb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransitionUnitPointValueCocycleStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transitionUnit_pointValue_cocycle : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (F : Type) [Field F] (ξ : Sp F ⟶ X) (j j' j'' : L.ι), ⊤ ≤ ξ ⁻¹ᵁ L.U j → ⊤ ≤ ξ ⁻¹ᵁ L.U j' → ⊤ ≤ ξ ⁻¹ᵁ L.U j'' → valR ξ (L.U j ⊓ L.U j') (L.g j j').val * valR ξ (L.U j' ⊓ L.U j'') (L.g j' j'').val = valR ξ (L.U j ⊓ L.U j'') (L.g j j'').val := by
  first | exact @GlobalTheory.CocVal.valR_cocycle | exact GlobalTheory.CocVal.valR_cocycle | (intros; apply GlobalTheory.CocVal.valR_cocycle <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupsAdjointHomPairClosedFormStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum GlobalTheory.MumFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisedGroups_adjointHomPair_closedForm : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₁ : DegData R (maximalIdeal R)) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (U₁ : Unif (maximalIdeal R) D₁ A₁ G₁) (D₂ : DegData R (maximalIdeal R)) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₂ → ∀ (U₂ : Unif (maximalIdeal R) D₂ A₂ G₂) (a : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (a' : D₂.toPre.P.A ⟶ D₁.toPre.P.A) (h : D₁.toPre.X →+ D₂.toPre.X) (h' : D₂.toPre.X →+ D₁.toPre.X), Adj (pol D₁) (pol D₂) a a' h h' → ∃ (u : G₁ ⟶ G₂) (u' : G₂ ⟶ G₁), LinHom U₁.toUnifPre U₂.toUnifPre a h' u ∧ LinHom U₂.toUnifPre U₁.toUnifPre a' h u' ∧ GAdj U₁.LG.L U₂.LG.L u u' := by
  first | exact @GlobalTheory.MumAdj.adj_groups | exact GlobalTheory.MumAdj.adj_groups | (intros; apply GlobalTheory.MumAdj.adj_groups <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValueAtInvariantFieldTranslateSqZeroStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TangentOrigin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.value_at_invariantField_translate_sqZero : ∀ {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {u : TanM (𝟙 (Sp R)) G} {dd : Fld G.left}, IsInv G u dd → ∀ {B : Type} [CommRing B] [Algebra R B]
    (e : B) (he : e * e = 0) (z : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) B ⟶ G) (O : G.left.Opens) (h : ⊤ ≤ z.left ⁻¹ᵁ O),
    ∃ h' : ⊤ ≤ ((ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.epsTo R e he) ≫ GlobalTheory.VertCoeffRing.tvE u) * z).left ⁻¹ᵁ O, ∀ f,
      GlobalTheory.TangentOrigin.evalPt _ O h' f = GlobalTheory.TangentOrigin.evalPt z.left O h f + e * GlobalTheory.TangentOrigin.evalPt z.left O h (dd O f) := by
  first | exact @GlobalTheory.VertCoeffRing.evalPt_tvE_mul | exact GlobalTheory.VertCoeffRing.evalPt_tvE_mul | (intros; apply GlobalTheory.VertCoeffRing.evalPt_tvE_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorFieldFollowsDerivationOnSmallerOpenAtFieldStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vectorField_follows_derivation_on_smaller_open_at_fieldPoint : ∀ (Z : Scheme.{0}) (U : Z.Opens), IsAffineOpen U → ∀ (F : Type) [Field F] (ξ : Sp F ⟶ Z), ⊤ ≤ ξ ⁻¹ᵁ U → ∀ (d : Fld Z), IsField U d → ∀ (D : F → F), (∀ x y, D (x + y) = D x + D y) → (∀ x y, D (x * y) = x * D y + y * D x) → (∀ f : Γ(Z, U), valR ξ U (d U f) = D (valR ξ U f)) → ∀ O : Z.Opens, O ≤ U → ⊤ ≤ ξ ⁻¹ᵁ O → ∀ h : Γ(Z, O), valR ξ O (d O h) = D (valR ξ O h) := by
  first | exact @GlobalTheory.LocVal.valR_field_of_le | exact GlobalTheory.LocVal.valR_field_of_le | (intros; apply GlobalTheory.LocVal.valR_field_of_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VerticalDerivationLiftingPrincipalPolarizationEqStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vertical_derivation_lifting_principalPolarization_eq_zero : ∀ (k : Type) [Field k] (R : Type) [CommRing R] (P : PolAV (Sp R)) (x₀ : R →+* k) (A₀ : Over (Sp k)) [GrpObj A₀] (m₀ : A₀.left ⟶ P.A.left), IsGrpPullback A₀ P.A (spMap x₀) m₀ → ∀ {J : Type} (V : J → P.A.left.Opens) (jj : J → P.L.ι) (v : ∀ W : P.A.left.Opens, Γ(P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (q : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)), GlobalTheory.HeatConn.IsConnK P.A P.L A₀ m₀ (fun _ => 0) V jj v q → ∀ (W : P.A.left.Opens) (f : Γ(P.A.left, W)), v W f = 0 := by
  first | exact @GlobalTheory.HeatConn.Vert.vert_eq_zero | exact GlobalTheory.HeatConn.Vert.vert_eq_zero | (intros; apply GlobalTheory.HeatConn.Vert.vert_eq_zero <;> assumption)
end

