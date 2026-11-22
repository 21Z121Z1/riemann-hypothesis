import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3485
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0615
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3472
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0026
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrdegResidueFieldOfIsOpenImmersion
import GroundTheory.ArithmeticGeometry.SchemeCohomology.Bundle0002
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3473
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3462
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3474
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3475
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3452
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2892
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0657
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0638
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.CoeNonzeroLocusCanonicalEqComplRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkElementsApproxLeadingTermQuotients
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.QkExtExistsG
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3439
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0226
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2998
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3478
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2809
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2821

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfSpecializesSameFibreIsIntegralHom
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

namespace GlobalTheory

theorem eq_of_specializes_of_isIntegralHom : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIntegralHom f] {x x' : X}, x ⤳ x' → f x = f x' → x = x' := by
  intro X Y f _ x x' hxx' hf
  obtain ⟨_, ⟨V, hV0, rfl⟩, hxV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x')) isOpen_univ
  have hV : IsAffineOpen V := hV0
  have hU : IsAffineOpen (f ⁻¹ᵁ V) := hV.preimage f
  have hx' : x' ∈ f ⁻¹ᵁ V := hxV
  have hx : x ∈ f ⁻¹ᵁ V := hxx'.mem_open (f ⁻¹ᵁ V).isOpen hx'
  set P := hU.primeIdealOf ⟨x, hx⟩ with hPdef
  set P' := hU.primeIdealOf ⟨x', hx'⟩ with hP'def
  have eP : hU.fromSpec P = x := hU.fromSpec_primeIdealOf ⟨x, hx⟩
  have eP' : hU.fromSpec P' = x' := hU.fromSpec_primeIdealOf ⟨x', hx'⟩
  have hsp : P ⤳ P' := by
    exact hU.fromSpec.isOpenEmbedding.toIsInducing.specializes_iff.1 (by rw [eP, eP']; exact hxx')
  have hle : P.asIdeal ≤ P'.asIdeal := (PrimeSpectrum.le_iff_specializes P P').mpr hsp
  have sq : Spec.map (f.app V) ≫ hV.fromSpec = hU.fromSpec ≫ f := by
    rw [Scheme.Hom.app_eq_appLE]
    exact IsAffineOpen.SpecMap_appLE_fromSpec f hV hU le_rfl
  have img : ∀ Q : Spec Γ(X, f ⁻¹ᵁ V), hV.fromSpec (Spec.map (f.app V) Q) = f (hU.fromSpec Q) :=
    fun Q => (Scheme.Hom.comp_apply _ _ _).symm.trans
      ((congrArg (fun m : Spec Γ(X, f ⁻¹ᵁ V) ⟶ Y => m Q) sq).trans (Scheme.Hom.comp_apply _ _ _))
  have hc : Spec.map (f.app V) P = Spec.map (f.app V) P' := by
    apply hV.fromSpec.isOpenEmbedding.injective
    exact (img P).trans ((congrArg f eP).trans (hf.trans ((congrArg f eP').symm.trans (img P').symm)))
  have hc' : P.asIdeal.comap (f.app V).hom = P'.asIdeal.comap (f.app V).hom :=
    congrArg PrimeSpectrum.asIdeal hc
  letI : Algebra Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := (f.app V).hom.toAlgebra
  haveI : Algebra.IsIntegral Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := ⟨f.isIntegral_app V hV⟩
  have heq : P.asIdeal = P'.asIdeal := by
    by_contra hne
    have hlt := Ideal.IsIntegral.comap_lt_comap (R := Γ(Y, V)) (lt_of_le_of_ne hle hne)
    exact (ne_of_lt hlt) hc'
  have : P = P' := PrimeSpectrum.ext heq
  rw [← eP, ← eP', this]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqualVolumeDeepLevelStatement
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equal_volume_deep_level : Hypotheses2 → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → EqVolume Y.U := by
  first | exact @GlobalTheory.CompEqVol.eqVolume_good | exact GlobalTheory.CompEqVol.eqVolume_good | (intros; apply GlobalTheory.CompEqVol.eqVolume_good <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EssFiniteTypePreimageFromSpecStalk
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SmoothStalk

theorem essFiniteType_preimage_fromSpecStalk (F : Type) [CommRing F] (X : Scheme.{0})
    (g : X ⟶ Spec (CommRingCat.of F)) [LocallyOfFiniteType g] (z : X) :
    (Spec.preimage (X.fromSpecStalk z ≫ g)).hom.EssFiniteType := by
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (show z ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (hU.fromSpec ≫ g)
  have hft : φ.hom.FiniteType := by
    have : LocallyOfFiniteType (Spec.map φ) := by rw [hφ]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 this
  have he : Spec.preimage (X.fromSpecStalk z ≫ g) = φ ≫ X.presheaf.germ U z hx := by
    rw [← Spec.map_inj, Spec.map_preimage, Spec.map_comp, hφ, ← hU.fromSpecStalk_eq_fromSpecStalk hx,
      IsAffineOpen.fromSpecStalk, Category.assoc]
  rw [he, CommRingCat.hom_comp]
  refine RingHom.EssFiniteType.comp hft.essFiniteType ?_
  let _ := X.presheaf.algebra_section_stalk ⟨z, hx⟩
  have := hU.isLocalization_stalk ⟨z, hx⟩
  exact Algebra.EssFiniteType.of_isLocalization (X.presheaf.stalk z) (hU.primeIdealOf ⟨z, hx⟩).asIdeal.primeCompl

theorem stalk_regular_essFiniteType_dim : ∀ (F : Type) [Field F] (Cs : Scheme.{0}) (g : Cs ⟶ Sp F) (n : ℕ), SmoothOfRelativeDimension n g → ∀ z : Cs, IsRegularLocalRing (Cs.presheaf.stalk z) ∧ ∃ b : F →+* Cs.presheaf.stalk z, Cs.fromSpecStalk z ≫ g = spMap b ∧ b.EssFiniteType ∧ (letI := ((residue (Cs.presheaf.stalk z)).comp b).toAlgebra; ∃ a t : ℕ, ringKrullDim (Cs.presheaf.stalk z) = a ∧ Algebra.trdeg F (ResidueField (Cs.presheaf.stalk z)) = t ∧ a + t = n) := by
  intro F _ Cs g n hsm z
  haveI := hsm
  haveI : Smooth g := SmoothOfRelativeDimension.smooth n g
  haveI : IsRegularRing (CommRingCat.of F) := inferInstanceAs (IsRegularRing F)
  have hreg : ∀ x : Cs, IsRegularLocalRing (Cs.presheaf.stalk x) := fun x =>
    GroundTheory.Arith.SchemeCoh.isRegularLocalRing_stalk_of_smooth g x
  refine ⟨hreg z, (Spec.preimage (Cs.fromSpecStalk z ≫ g)).hom, ?_, essFiniteType_preimage_fromSpecStalk F Cs g z, ?_⟩
  · exact (Spec.map_preimage _).symm
  · have h := GlobalTheory.StalkDim.stalk_dim_add_trdeg F g (𝟙 Cs) n (by simp) (by simpa using hsm)
      (fun x => haveI := hreg x; ReciprocityTheory.AnForm.R.isDomain_of_isRegularLocalRing) z
    have he : Spec.preimage (Cs.fromSpecResidueField z ≫ g) =
        Spec.preimage (Cs.fromSpecStalk z ≫ g) ≫ Cs.residue z := by
      rw [← Spec.map_inj, Spec.map_preimage, Spec.map_comp, Spec.map_preimage, Scheme.fromSpecResidueField,
        Category.assoc]
    rw [he] at h
    exact h

end GlobalTheory.SmoothStalk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisPullbackMatrixInvariantFieldsRaynaudStatement
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
theorem _root_.GlobalTheory.T.exists_basis_pullback_matrix_invariantFields_raynaud : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∃ (g : ℕ) (w : Module.Basis (Fin g) R (TanM (𝟙 (Sp R)) Dd.toPre.P.A)) (e : Fin g → Fld Dd.toPre.P.A.left) (P : Matrix (Fin g) (Fin n) R) (Qm : Matrix (Fin n) (Fin g) R), (∀ c, IsInv Dd.toPre.P.A (w c) (e c)) ∧ P * Qm = 1 ∧ ∀ b (V : Dd.toPre.P.A.left.Opens) (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ V → ∀ f : Γ(Dd.toPre.P.A.left, V), dd b W (pbT Y.q.left f W) = ∑ c, constFn Y.H.hom W (P c b) * pbT Y.q.left (e c V f) W := by
  first | exact @GlobalTheory.InvFactor.exists_basis_pull_matrix | exact GlobalTheory.InvFactor.exists_basis_pull_matrix | (intros; apply GlobalTheory.InvFactor.exists_basis_pull_matrix <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDvrAlgClosedResidueInjectiveLocal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompleteClosedDvr

theorem exists_complete_dvr_isAlgClosed : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V], ¬ IsField V → Nonempty (ℚ →+* V) → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (ρ : V →+* W), IsAdicComplete (maximalIdeal W) W ∧ IsAlgClosed (ResidueField W) ∧ Function.Injective ρ ∧ IsLocalHom ρ := by
  intro V _ _ _ _ _ _
  obtain ⟨D, _, _, _, φ, hac, hinj, hc⟩ := GlobalTheory.UnifProperChar.exists_dvr_centre V (maximalIdeal V)
  have : IsLocalHom φ := ((IsLocalRing.local_hom_TFAE φ).out 0 4).mpr hc
  have hb := AdicCompletion.residueField_map_bijective_of_fg (R := D)
    (maximalIdeal D).fg_of_isNoetherianRing
  refine ⟨AdicCompletion (maximalIdeal D) D, inferInstance, inferInstance, inferInstance,
    (algebraMap D _).comp φ, inferInstance, ?_,
    (GlobalTheory.injective_and_isLocalHom_adicCompletion_comp φ hinj).1,
    (GlobalTheory.injective_and_isLocalHom_adicCompletion_comp φ hinj).2⟩
  exact IsAlgClosed.of_ringEquiv (ResidueField D) _ (RingEquiv.ofBijective _ hb)

end GlobalTheory.CompleteClosedDvr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplexUniformisationHarrisTaylorStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complexUniformisation_harrisTaylor : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (o : Obj b N (spMap σ)) h hL, 0 < N → N.Coprime p → b.IsType σ ρ → ∃ D' t Q e, D.Cls N D' t ∧ UnifAt (o.fam h hL) σ ρ N D' t Q (𝟙 _) e := by
  first | (exact @GlobalTheory.UPel.HT.Unif.exists_unifAt) | (exact GlobalTheory.UPel.HT.Unif.exists_unifAt) | (intros; apply GlobalTheory.UPel.HT.Unif.exists_unifAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjInvariantTraceGeneratorLocalStatement
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conj_invariant_trace_generator_local : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (𝔭 : Ideal (𝓞 E))
    (h𝔭 : 𝔭.IsMaximal),
    ∃ θ : 𝓞 E →+ ℤ, (∀ t, θ (H.bar t) = θ t) ∧ ∃ s : 𝓞 E, s ∉ 𝔭 ∧ H.bar s ∉ 𝔭 ∧
      ∀ ψ : 𝓞 E →+ ℤ, ∃ t : 𝓞 E, ∀ u, ψ (s * u) = θ (t * u) := by
  first | exact @GlobalTheory.RealTheta.exists_bar_inv_trace_gen | exact GlobalTheory.RealTheta.exists_bar_inv_trace_gen | (intros; apply GlobalTheory.RealTheta.exists_bar_inv_trace_gen <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstantUnitPulledBackBundleAutomorphism
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open TopologicalSpace

namespace GlobalTheory.PullAutConst

theorem gm_pullChart {X Z T : Scheme.{0}} (L : LB X) (F : Z ⟶ X) (f : T ⟶ Z) (y : T) (j j' : L.ι)
    (hj : F (f y) ∈ L.U j) (hj' : F (f y) ∈ L.U j') :
    gm f y _ ((L.pull F).g (fun _ => j) (fun _ => j')) = gm (f ≫ F) y _ (L.g j j') := by
  have hp : f y ∈ (L.pull F).U (fun _ => j) ⊓ (L.pull F).U (fun _ => j') := ⟨mem_pull.2 hj, mem_pull.2 hj'⟩
  show gm f y _ (∏ _k : PUnit, (res _ (pullU F _ (L.g j j'))) ^ (1 : ℤ)) = _
  rw [Fintype.prod_unique, zpow_one]
  exact (gm_res f y _ hp _).trans (gm_pull f F y (L.U j ⊓ L.U j') ⟨hj, hj'⟩ _)

theorem exists_glued {X Y B : Scheme.{0}} (L : LB X) (M₀ : LB Y) (β : X ⟶ Y) (wF : LB.Iso L (M₀.pull β))
    (π₁ π₂ : B ⟶ X) (w : LB.Iso (L.pull π₁) (L.pull π₂)) (hL : L.IsLB) (hM : M₀.IsLB)
    (hF : PGen wF) (hw : PGen w) (hβ : π₁ ≫ β = π₂ ≫ β) :
    ∃ s : Γ(B, ⊤)ˣ, ∀ (Z : Scheme.{0}) (f : Z ⟶ B) (z : Z) (j₀ : M₀.ι) (j₁ j₂ : L.ι),
      β (π₁ (f z)) ∈ M₀.U j₀ → π₁ (f z) ∈ L.U j₁ → π₂ (f z) ∈ L.U j₂ →
      gm f z ⊤ s = gw wF (f ≫ π₂) z j₀ j₂ * gw w f z j₂ (fun _ => j₁) * (gw wF (f ≫ π₁) z j₀ j₁)⁻¹ := by
  have hpt : ∀ x, β (π₁ x) = β (π₂ x) := fun x => congrArg (fun g : B ⟶ Y => g x) hβ
  obtain ⟨W, hW⟩ : ∃ W : M₀.ι × L.ι × L.ι → B.Opens, ∀ t x,
      x ∈ W t ↔ β (π₁ x) ∈ M₀.U t.1 ∧ π₁ x ∈ L.U t.2.1 ∧ π₂ x ∈ L.U t.2.2 :=
    ⟨fun t => π₁ ⁻¹ᵁ (β ⁻¹ᵁ M₀.U t.1) ⊓ (π₁ ⁻¹ᵁ L.U t.2.1 ⊓ π₂ ⁻¹ᵁ L.U t.2.2), fun _ _ => Iff.rfl⟩
  have l₂ : ∀ t, W t ≤ π₂ ⁻¹ᵁ ((M₀.pull β).U (fun _ => t.1) ⊓ L.U t.2.2) := fun t x hx =>
    ⟨mem_pull.2 (show β (π₂ x) ∈ _ by rw [← hpt]; exact ((hW t x).1 hx).1), ((hW t x).1 hx).2.2⟩
  have lw : ∀ t, W t ≤ (L.pull π₂).U (fun _ => t.2.2) ⊓ (L.pull π₁).U (fun _ => t.2.1) := fun t x hx =>
    ⟨mem_pull.2 ((hW t x).1 hx).2.2, mem_pull.2 ((hW t x).1 hx).2.1⟩
  have l₁ : ∀ t, W t ≤ π₁ ⁻¹ᵁ ((M₀.pull β).U (fun _ => t.1) ⊓ L.U t.2.1) := fun t x hx =>
    ⟨mem_pull.2 ((hW t x).1 hx).1, ((hW t x).1 hx).2.1⟩
  obtain ⟨u, hu⟩ : ∃ u : ∀ t, Γ(B, W t)ˣ, ∀ (Z : Scheme.{0}) (f : Z ⟶ B) (z : Z) (t : M₀.ι × L.ι × L.ι), f z ∈ W t →
      gm f z (W t) (u t) =
        gw wF (f ≫ π₂) z t.1 t.2.2 * gw w f z t.2.2 (fun _ => t.2.1) * (gw wF (f ≫ π₁) z t.1 t.2.1)⁻¹ :=
    ⟨fun t => res (l₂ t) (pullU π₂ _ (wF.s (fun _ => t.1, t.2.2))) * res (lw t) (w.s (fun _ => t.2.2, fun _ => t.2.1)) *
        (res (l₁ t) (pullU π₁ _ (wF.s (fun _ => t.1, t.2.1))))⁻¹, fun Z f z t hz =>
      (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_mul _ _ _).trans (congrArg₂ (· * ·)
        ((gm_res f z (l₂ t) hz _).trans (gm_pull f π₂ z _ (l₂ t hz) _)) (gm_res f z (lw t) hz _)))
        ((map_inv _ _).trans (congrArg (·⁻¹) ((gm_res f z (l₁ t) hz _).trans (gm_pull f π₁ z _ (l₁ t hz) _)))))⟩
  have indep : ∀ (Z : Scheme.{0}) (f : Z ⟶ B) (z : Z) (t t' : M₀.ι × L.ι × L.ι), f z ∈ W t → f z ∈ W t' →
      gw wF (f ≫ π₂) z t.1 t.2.2 * gw w f z t.2.2 (fun _ => t.2.1) * (gw wF (f ≫ π₁) z t.1 t.2.1)⁻¹ =
      gw wF (f ≫ π₂) z t'.1 t'.2.2 * gw w f z t'.2.2 (fun _ => t'.2.1) * (gw wF (f ≫ π₁) z t'.1 t'.2.1)⁻¹ := by
    rintro Z f z ⟨a, b, c⟩ ⟨a', b', c'⟩ h h'
    obtain ⟨ha, hb, hc⟩ := (hW _ _).1 h
    obtain ⟨ha', hb', hc'⟩ := (hW _ _).1 h'
    have e₂ := hF Z (f ≫ π₂) z a a' c c' (show β (π₂ (f z)) ∈ _ by rw [← hpt]; exact ha)
      (show β (π₂ (f z)) ∈ _ by rw [← hpt]; exact ha') hc hc'
    have e₁ := hF Z (f ≫ π₁) z a a' b b' ha ha' hb hb'
    have ew := hw Z f z c c' (fun _ => b) (fun _ => b') hc hc' (mem_pull.2 hb) (mem_pull.2 hb')
    rw [gm_pullChart L π₁ f z b b' hb hb'] at ew
    have hg : gm ((f ≫ π₂) ≫ β) z _ (M₀.g a a') = gm ((f ≫ π₁) ≫ β) z _ (M₀.g a a') := by
      simp only [Category.assoc, hβ]
    dsimp only
    rw [e₂, e₁, ew, hg]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  obtain ⟨s, hs⟩ := glue_unit ⊤ W (fun _ => le_top) (fun x _ => by
      obtain ⟨j₁, h₁⟩ := exists_chart hL (π₁ x)
      obtain ⟨j₂, h₂⟩ := exists_chart hL (π₂ x)
      obtain ⟨j₀, h₀⟩ := exists_chart hM (β (π₁ x))
      exact Opens.mem_iSup.2 ⟨(j₀, j₁, j₂), (hW _ x).2 ⟨h₀, h₁, h₂⟩⟩) u
    (fun t t' x hx => (hu _ (𝟙 B) x t hx.1).trans ((indep _ (𝟙 B) x t t' hx.1 hx.2).trans (hu _ (𝟙 B) x t' hx.2).symm))
  refine ⟨s, fun Z f z j₀ j₁ j₂ h₀ h₁ h₂ => ?_⟩
  have hz : f z ∈ W (j₀, j₁, j₂) := (hW _ _).2 ⟨h₀, h₁, h₂⟩
  exact (gm_res f z le_top hz s).symm.trans ((congrArg (gm f z _) (hs _)).trans (hu Z f z _ hz))

theorem exists_unit : ∀ (A : Type) [CommRing A] (B' : Over (Sp A)) [GrpObj B'], IsAbelianScheme B' → ∀ {X Y : Scheme.{0}} (L : LB X) (M₀ : LB Y) (β : X ⟶ Y) (wF : LB.Iso L (M₀.pull β)) (π₁ π₂ : B'.left ⟶ X) (w : LB.Iso (L.pull π₁) (L.pull π₂)), L.IsLB → M₀.IsLB → wF.IsGen → w.IsGen → π₁ ≫ β = π₂ ≫ β → ∃ u : Aˣ, ∀ (p : Sp A ⟶ B'.left), p ≫ B'.hom = 𝟙 _ → ∀ (zz : Sp A) (J : (Sp A ⟶ X) → L.ι) (J₀ : (Sp A ⟶ Y) → M₀.ι), Good L zz J → Good M₀ zz J₀ → gm (p ≫ π₂) zz _ (wF.s (fun _ => J₀ (p ≫ π₂ ≫ β), J (p ≫ π₂))) * gm p zz _ (w.s (fun _ => J (p ≫ π₂), fun _ => J (p ≫ π₁))) = gm (𝟙 _) zz ⊤ (unitOn u) * gm (p ≫ π₁) zz _ (wF.s (fun _ => J₀ (p ≫ π₁ ≫ β), J (p ≫ π₁))) := by
  intro A _ B' _ hB X Y L M₀ β wF π₁ π₂ w hL hM hwF hw hβ
  obtain ⟨s, hs⟩ := exists_glued L M₀ β wF π₁ π₂ w hL hM ((isGen_iff wF).1 hwF) ((isGen_iff w).1 hw) hβ
  have hbij := GlobalTheory.globalFns_holds _ B' hB
  let e := RingEquiv.ofBijective B'.hom.appTop.hom hbij
  let a : Γ(Sp A, ⊤)ˣ := Units.map e.symm.toMonoidHom s
  have ha : Units.map B'.hom.appTop.hom.toMonoidHom a = s := by
    ext
    exact e.apply_symm_apply _
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.toMonoidHom a, ?_⟩
  intro p hp zz J J₀ hJ hJ₀
  have hua : unitOn (Units.map (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.toMonoidHom a) = a := by
    ext
    simp [unitOn]
  have k₁ := gm_pull p B'.hom zz ⊤ trivial a
  rw [hp] at k₁
  have key : gm p zz ⊤ s = gm (𝟙 _) zz ⊤ a := by
    rw [← ha]
    exact k₁
  have hs' := hs (Sp A) p zz (J₀ (p ≫ π₁ ≫ β)) (J (p ≫ π₁)) (J (p ≫ π₂)) (hJ₀ _) (hJ _) (hJ _)
  rw [hua, ← key, show p ≫ π₂ ≫ β = p ≫ π₁ ≫ β by rw [hβ], hs']
  exact (inv_mul_cancel_right _ _).symm

end GlobalTheory.PullAutConst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCorrectionProperNormalCoverPowerLocalEquat
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

namespace GlobalTheory.CorrCover

theorem exists_corr : ∀ (Z M S₁ : Scheme.{0}) [IsIntegral M] [IsIntegral S₁] (sM : M ⟶ Sp ℤ) (p₁ : S₁ ⟶ M) (g : M ⟶ Z) (J : Z.IdealSheafData), LocallyOfFiniteType sM → QuasiCompact sM → Flat (p₁ ≫ sM) → Geo.Tor.IsNormalScheme S₁ → IsProper p₁ → IsDominant p₁ → FinalTheorems.EffCartier (J.comap (p₁ ≫ g)) → ∀ (U₁ : S₁.Opens), (U₁ : Set S₁).Nonempty → ∀ (z₁ : M) (R : Type) [CommRing R] [IsLocalRing R] (ev : M.presheaf.stalk z₁ →+* R), IsLocalHom ev → ∀ ξ₁ : Sp R ⟶ S₁, ξ₁ ≫ p₁ = spMap ev ≫ M.fromSpecStalk z₁ → ∃ g₀ : R, idlAlong (J.comap (p₁ ≫ g)) ξ₁ = Ideal.span {g₀} ∧ ∀ D e : ℕ, ∃ e' : ℕ, ∀ f : M.presheaf.stalk z₁, (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ (ξ' : Sp V ⟶ S₁) (ev' : M.presheaf.stalk z₁ →+* V), IsLocalHom ev' → spMap ev' ≫ M.fromSpecStalk z₁ = ξ' ≫ p₁ → Set.range (jK V ≫ ξ') ⊆ (U₁ : Set S₁) → ev' f ∈ idlAlong (J.comap (p₁ ≫ g)) ξ' ^ D ⊔ ((maximalIdeal (M.presheaf.stalk z₁)).map ev') ^ e') → ∃ h ∈ (Scheme.stalkClosedPointTo ξ₁).hom.range, ev f - h * g₀ ^ D ∈ maximalIdeal R ^ e := by
  intro Z M S₁ _ _ sM p₁ g J h1 h2 h3 hN h5 h6 hEC U₁ hU z₁ R _ _ ev hev ξ₁ hξ
  haveI := h1; haveI := h2; haveI := h3; haveI := h5; haveI := h6; haveI := hev
  set I := J.comap (p₁ ≫ g) with hIdef
  set x₁ := ξ₁ (closedPoint R)
  set ψ := (Scheme.stalkClosedPointTo ξ₁).hom
  obtain ⟨W, f₀, hx, -, hI⟩ := hEC x₁
  have st : ∀ k : ℕ, FinalTheorems.stalkId (I ^ k) x₁ = Ideal.span {(S₁.presheaf.germ _ x₁ hx).hom f₀ ^ k} := fun k => by
    rw [ReciprocityTheory.AnForm.R.ds_stalkId_eq_map _ W x₁ hx, Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, hI,
      Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton, map_pow]
  refine ⟨ψ ((S₁.presheaf.germ _ x₁ hx).hom f₀), ?_, ?_⟩
  · have := st 1
    rw [pow_one, pow_one] at this
    rw [idlAlong, this, Ideal.map_span, Set.image_singleton]
  intro D e
  obtain ⟨E, hE⟩ := EffCartierData.exists_idealSheaf_eq (CoverElements.effCartier_pow hEC D)
  obtain ⟨e', he'⟩ := GlobalTheory.T.exists_correction_approximate_ideal_sections M S₁ sM p₁ hN U₁ hU E z₁ e
  refine ⟨e', fun f hf => ?_⟩
  have hm := he' f (fun V _ _ _ _ hc ξ' ev' hl hc' hr => by
    rw [hE, TorRef.idlAlong_pow]
    exact hf V hc ξ' ev' hl hc' hr)
  obtain ⟨f₁, hf₁, r, hr, rfl⟩ := Submodule.mem_sup.1 hm
  obtain ⟨u, hu, hψ⟩ := CoverElements.exists_stalk_of_map p₁ E.idealSheaf ξ₁ ev hξ hf₁
  rw [hE, st D] at hu
  obtain ⟨h', rfl⟩ := Ideal.mem_span_singleton'.1 hu
  refine ⟨ψ h', ⟨h', rfl⟩, ?_⟩
  have hmR : (maximalIdeal (M.presheaf.stalk z₁)).map ev ≤ maximalIdeal R :=
    Ideal.map_le_iff_le_comap.2 fun x hx => (IsLocalRing.mem_maximalIdeal _).2 fun hu => hx (isUnit_of_map_unit ev x hu)
  have : ev r ∈ maximalIdeal R ^ e :=
    Ideal.pow_right_mono hmR e (by rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem ev hr)
  rw [map_add, ← hψ, map_mul, map_pow]
  convert this using 1
  exact add_sub_cancel_left _ _

end GlobalTheory.CorrCover
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDivisionPointPairOverAlgClosed
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCanon

theorem exists_qk_over_cF : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V), D.TauBimult →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k →
    ∀ (y : D.X) (x : TF (R := V) F ⟶ D.P.A), x ^ k = DegPre.cF D F y → ∃ p : QkPt D F k, p.y = y ∧ p.g.b = x := by
  intro V _ _ D hB F _ _ _ k hk y x hx
  obtain ⟨J, hJ⟩ := good_pt D.P.isLB (default : PrimeSpectrum F)
  exact exists_qk_over (F := F) hJ hB hk y x hx

end GlobalTheory.UCanon
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivLatticePartZeroIffMemNsmulStatement
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LowDat GlobalTheory.LowFilt
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_equiv_latticePart_zero_iff_mem_nsmul : ∀ (R : Type) [CommRing R] [IsDomain R] (D₀ : DegPre R), D₀.TauBimult →
    ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (n : ℕ), 0 < n → ∀ p : QkPt D₀ F n,
    (∃ q : QkPt D₀ F n, QkPt.Equiv D₀ F p q ∧ q.y = 0) ↔ ∃ e, p.y = n • e := by
  first | exact @GlobalTheory.LowFilt.exists_equiv_y_eq_zero_iff | exact GlobalTheory.LowFilt.exists_equiv_y_eq_zero_iff | (intros; apply GlobalTheory.LowFilt.exists_equiv_y_eq_zero_iff <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFibrePowerPointFiniteExtensionDvr
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LowChart

theorem exists_fibrePow_point_of_polAV : ∀ (n : ℕ), 3 ≤ n → Odd n → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → IsDiscreteValuationRing V → ∀ (b : cycAway n →+* V) (PB : PolAV (Sp V)) (r : ℕ) (c : (Fin r → ℤ) → (𝟙_ (Over (Sp V)) ⟶ PB.A)), (∀ a a', c (a + a') = c a * c a') → ∃ (F : SFam PB.g n (zetaAway n)) (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (f₁ : V →+* V₁) (v : Sp V₁ ⟶ (GlobalTheory.LowChart.powA F r).left) (hs : v ≫ GlobalTheory.LowChart.toO F r = spMap (f₁.comp b)), IsCN V₁ ∧ IsDiscreteValuationRing V₁ ∧ Function.Injective f₁ ∧ f₁.Finite ∧ IsLocalHom f₁ ∧ ∃ (β₁ : (GlobalTheory.LowChart.siegAt F v _ hs).A.left ⟶ PB.A.left) (β₁₂ : (G2 (GlobalTheory.LowChart.siegAt F v _ hs).A).left ⟶ (G2 PB.A).left), IsGrpPullback (GlobalTheory.LowChart.siegAt F v _ hs).A PB.A (spMap f₁) β₁ ∧ IsSquare β₁ β₁₂ ∧ LBIso (GlobalTheory.LowChart.siegAt F v _ hs).P ((abelian₂ PB.A PB.L).pull β₁₂) ∧ ∀ a, (GlobalTheory.LowChart.cAt F v _ hs ((n : ℤ) • a)).left ≫ β₁ = spMap f₁ ≫ (c a).left := by
  intro n hn hodd V _ _ _ hV hD b PB r c hc
  obtain ⟨V₁, _, _, _, f₁, s, β, β₂, d, h1, h2, h3, h4, h5, hP, hpb, hsq, hlb, hd⟩ :=
    GlobalTheory.T.exists_siegelLevel_after_finiteExtension_DVR n hn hodd V hV hD b PB r c
  have : CharZero V₁ := h1.2.2.2
  obtain ⟨F, x, hx, hpbF⟩ := GlobalTheory.T.exists_siegel_family_point_of_principal_object n hn hodd PB.g V₁ (f₁.comp b) s hP
  obtain ⟨v, hs, β₁, β₁₂, p1, p2, p3, p4⟩ :=
    GlobalTheory.T.exists_siegelObject_fibrePower_at_sections F (spMap f₁) (spMap (f₁.comp b)) x hx s hpbF PB.A (abelian₂ PB.A PB.L) β β₂ hpb hsq hlb r d
  refine ⟨F, V₁, inferInstance, inferInstance, inferInstance, f₁, v, hs, h1, h2, h3, h4, h5, β₁, β₁₂, p1, p2, p3,
    fun a => ?_⟩
  rw [p4]
  exact GlobalTheory.T.grpPullback_divisionPoints_push_eq (spMap f₁) s.A PB.A β hpb n r d c hc hd a

end GlobalTheory.LowChart
end
end

