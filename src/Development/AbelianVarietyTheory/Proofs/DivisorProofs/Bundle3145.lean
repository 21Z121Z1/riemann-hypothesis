import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3144
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2738
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3112
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0619
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2371
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2296
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0529
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentVectorFunctionalGlobalFormsAbelianS
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2726
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2420
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.Bundle0001
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3100
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0825
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0820
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2976
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1560
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2639
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0646
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianProperUniformisedWhereTrivialisationsGene
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem abelian_and_proper_of_psiUnitOn : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ W : (Sp R).Opens, (∀ y, PsiUnitOn D.toPre y W) → (W : Set (Sp R)) ⊆ abLocus G ∧ IsProper (G.hom ∣_ W) := by
  intro R _ _ _ hB D A G _ _ hG U W hW
  exact ⟨GlobalTheory.T.uniformised_group_abelian_where_trivialisations_units R hB D A G hG U W hW, GlobalTheory.T.isProper_uniformisedSemiAbelian_over_open_in_abLocus R hB D A G hG U W (GlobalTheory.T.uniformised_group_abelian_where_trivialisations_units R hB D A G hG U W hW)⟩

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeOneFormFrameAndPrimitiveOneForms
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem hasFrame_and_primF_of_isAbelianScheme : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → HasFrame (OAff A.hom) ∧ PrimF A := by
  intro R _ A _ g hA hg
  obtain ⟨M, _, _, j, hfin, hproj, hb⟩ := GlobalTheory.T.exists_invariant_oneForm_frame_abelianScheme R A g hA hg
  exact ⟨hasFrame_of_isBaseChange R (AffOp A.left) (OAff A.hom) M j fun U ↦ ⟨_, fun _ ↦ rfl, hb U⟩,
    GlobalTheory.T.globalOneForms_primitive_abelianScheme R A g hA hg⟩

end GlobalTheory.AbCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeTangentEqOfCrystallineValuesEq
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieInj

open GlobalTheory.CechDR

variable {R : Type} [CommRing R]

theorem cmpForm_surjective (hP : GlobalTheory.Published.CrystallineSmoothLift) (hH : GlobalTheory.Published.AbelianHodgeDeRham)
    (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hab : IsAbelianScheme A)
    (hdim : SmoothOfRelativeDimension g A.hom) :
    Function.Surjective (cmpForm (A.hom ≫ 𝟙 (Sp R))) := by
  intro ω
  obtain ⟨-, hinj, -⟩ := (hH R A g hab hdim).2.2.2.2.1
  haveI := hab.smooth
  haveI := hab.proper
  have hb := (cechDeRham_comparison_bijective_cup_smooth hP R A.left (A.hom ≫ 𝟙 (Sp R)) inferInstance inferInstance
    inferInstance).1
  obtain ⟨c, hc⟩ := hb.2 (clForm _ ω)
  have hmem : clForm (A.hom ≫ 𝟙 (Sp R)) ω ∈ CechHodgeFiltration (A.hom ≫ 𝟙 (Sp R)) := by
    rw [cechHodgeFiltration_eq_range]; exact ⟨ω, rfl⟩
  have h0 : toHO1 _ (cmp1 (A.hom ≫ 𝟙 (Sp R)) c) = 0 := by rw [hc]; exact hmem
  rw [structureSheaf_comparison_comm] at h0
  have h1 : toH1O _ c = 0 := GlobalTheory.CechDR.cmpO_injective R A.left _ (h0.trans (map_zero _).symm)
  have h2 : c ∈ F1 (A.hom ≫ 𝟙 (Sp R)) := h1
  rw [hodgeFiltration_eq_range] at h2
  obtain ⟨f, rfl⟩ := h2
  refine ⟨f, hinj ?_⟩
  change clForm (A.hom ≫ 𝟙 (Sp R)) (cmpForm _ f) = clForm (A.hom ≫ 𝟙 (Sp R)) ω
  rw [← comparison_formClass, hc]

section Lie

open ReciprocityTheory.ChartRestriction.G MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

theorem lie_finite_projective (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (g : ℕ)
    (hdim : SmoothOfRelativeDimension g A.hom) (a : OAct ℤ A) :
    Module.Finite R (GlobalTheory.Serre.Lie a) ∧ Module.Projective R (GlobalTheory.Serre.Lie a) ∧
      ∀ p, Module.rankAtStalk (R := R) (GlobalTheory.Serre.Lie a) p = g := by
  haveI : Smooth A.hom := hdim.smooth
  refine GlobalTheory.LieProj.finite_projective_of_localBasis (M := GlobalTheory.Serre.Lie a) g fun p ↦ ?_
  obtain ⟨r, hr, ⟨C⟩, v, hv⟩ := GlobalTheory.LieProj.exists_chart_lieBasis A g hdim p
  refine ⟨r, hr, ?_⟩
  obtain ⟨a', -⟩ := GlobalTheory.OActPull.exists_oAct_of_isGrpPullback a
    (isGrpPullback_pullback A (ReciprocityTheory.ChartRestriction.G.Chart.fB R (Localization.Away r)))
  obtain ⟨e⟩ := GlobalTheory.LieAway.lie_away A a r a' ⟨C⟩
  exact ⟨(GlobalTheory.Serre.Lie.basis a' hv).map e.symm⟩

end Lie

def valMap (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (a : OAct ℤ A) :
    GlobalTheory.Serre.Lie a →ₗ[R] Module.Dual R (Form (A.hom ≫ 𝟙 (Sp R))) where
  toFun v := tanVal v.hom
  map_add' v w := LinearMap.ext fun f ↦ by
    rw [LinearMap.add_apply, ← tanVal_mul v.isTangent w.isTangent, GlobalTheory.Serre.Lie.hom_add]
  map_smul' r v := LinearMap.ext fun f ↦ by
    rw [LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul, ← tanVal_epsScale, GlobalTheory.Serre.Lie.hom_smul]

theorem valMap_mem (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (a : OAct ℤ A) (u : GlobalTheory.Serre.Lie a) :
    valMap A a u ∈ (LinearMap.ker (cmpForm (A.hom ≫ 𝟙 (Sp R)))).dualAnnihilator := by
  rw [Submodule.mem_dualAnnihilator]
  intro f hf
  exact GlobalTheory.TanVanish.tanVal_eq_zero_of_cmpForm_eq_zero R A u.hom f hf

theorem valMap_surjective (hP : GlobalTheory.Published.CrystallineSmoothLift) (hH : GlobalTheory.Published.AbelianHodgeDeRham)
    (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hab : IsAbelianScheme A)
    (hdim : SmoothOfRelativeDimension g A.hom) [IsCommMonObj A] (a : OAct ℤ A) :
    Function.Surjective ((valMap A a).codRestrict _ (valMap_mem A a)) := by
  have hex := GlobalTheory.LieDual.exists_tangent_of_functional hP hH R A g hab hdim
  have key : ∀ φ : Module.Dual R (Form (A.hom ≫ 𝟙 (Sp R))),
      (∀ f, cmpForm (A.hom ≫ 𝟙 (Sp R)) f = 0 → φ f = 0) → ∃ u : GlobalTheory.Serre.Lie a, valMap A a u = φ := by
    intro φ hφ
    obtain ⟨u, hu, hu'⟩ := hex φ hφ
    exact ⟨GlobalTheory.Serre.Lie.mk a u hu, LinearMap.ext hu'⟩
  intro ψ
  have hψ : ∀ f, cmpForm (A.hom ≫ 𝟙 (Sp R)) f = 0 → ψ.1 f = 0 := fun f hf ↦
    (Submodule.mem_dualAnnihilator ψ.1).1 ψ.2 f (LinearMap.mem_ker.2 hf)
  exact (key ψ.1 hψ).imp fun u hu ↦ Subtype.ext hu

theorem tangent_eq_of_tanVal_eq : GlobalTheory.Published.CrystallineSmoothLift → GlobalTheory.Published.AbelianHodgeDeRham →
    ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
      SmoothOfRelativeDimension g A.hom → ∀ v w : epsR R ⟶ A, IsTangent v → IsTangent w →
        (∀ f : Form (A.hom ≫ 𝟙 (Sp R)), tanVal v f = tanVal w f) → v = w := by
  intro hP hH R _ A _ g hab hdim v w hv hw hvw
  haveI : IsCommMonObj A := hab.comm
  have hT := lie_finite_projective A g hdim (GlobalTheory.Serre.intAct A)
  haveI := hT.1
  haveI := hT.2.1
  have hcl : ClosedForm (A.hom ≫ 𝟙 (Sp R)) = ⊤ := (hH R A g hab hdim).2.2.2.2.1.1
  have hG := (hH R A g hab hdim).2.2.1
  haveI : Module.Finite R (GlobForm (A.hom ≫ 𝟙 (Sp R))) := hG.1
  haveI : Module.Projective R (GlobForm (A.hom ≫ 𝟙 (Sp R))) := hG.2.1
  have e1 : (Form (A.hom ≫ 𝟙 (Sp R)) ⧸ LinearMap.ker (cmpForm (A.hom ≫ 𝟙 (Sp R)))) ≃ₗ[R]
      GlobForm (A.hom ≫ 𝟙 (Sp R)) :=
    ((cmpForm (A.hom ≫ 𝟙 (Sp R))).quotKerEquivOfSurjective
      (cmpForm_surjective hP hH A g hab hdim)).trans (LinearEquiv.ofTop _ hcl)
  have eN : (LinearMap.ker (cmpForm (A.hom ≫ 𝟙 (Sp R)))).dualAnnihilator ≃ₗ[R]
      Module.Dual R (GlobForm (A.hom ≫ 𝟙 (Sp R))) :=
    (Submodule.dualQuotEquivDualAnnihilator _).symm.trans e1.symm.dualMap
  haveI : Module.Finite R (LinearMap.ker (cmpForm (A.hom ≫ 𝟙 (Sp R)))).dualAnnihilator :=
    Module.Finite.equiv eN.symm
  haveI : Module.Projective R (LinearMap.ker (cmpForm (A.hom ≫ 𝟙 (Sp R)))).dualAnnihilator :=
    Module.Projective.of_equiv eN.symm
  have hbij := Module.bijective_of_surjective_of_rankAtStalk_eq
    (valMap_surjective hP hH A g hab hdim (GlobalTheory.Serre.intAct A)) fun m _ ↦ by
      rw [hT.2.2, congrFun (Module.rankAtStalk_eq_of_equiv eN) _, GlobalTheory.TopExt.rankAtStalk_dual]
      exact (hG.2.2 _).symm
  have h := hbij.1 (a₁ := GlobalTheory.Serre.Lie.mk (GlobalTheory.Serre.intAct A) v hv)
    (a₂ := GlobalTheory.Serre.Lie.mk (GlobalTheory.Serre.intAct A) w hw) (Subtype.ext (LinearMap.ext hvw))
  exact congrArg GlobalTheory.Serre.Lie.hom h

end GlobalTheory.LieInj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyDimLeOfFiniteAndOfSurjectiveStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianVariety_dim_le_of_finite_and_of_surjective : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), (IsFinite f.hom.left → A.dim ≤ B.dim) ∧ (Surjective f.hom.left → B.dim ≤ A.dim) := by
  first | exact @GlobalTheory.AV.DimLe.dim_le | exact GlobalTheory.AV.DimLe.dim_le | (intros; apply GlobalTheory.AV.DimLe.dim_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyTopSelfIntersectionAmplePosStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianVariety_topSelfIntersection_ample_pos : ∀ (K : Type) [Field K] (A : AbVar K) (c : Pic A.X.left), IsAmpleCls c → ∀ (J : Type) [Fintype J], Fintype.card J = A.dim → 0 < inter A (fun _ : J => c) := by
  first | (exact @GlobalTheory.AV.AmpleTopPos.inter_top_pos) | (exact GlobalTheory.AV.AmpleTopPos.inter_top_pos) | (intros; apply GlobalTheory.AV.AmpleTopPos.inter_top_pos  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyWedgeNoPrimitiveH2
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh.WedgeSq

theorem exists_fin_sum_tmul {K V W : Type} [CommRing K] [AddCommGroup V] [Module K V] [AddCommGroup W]
    [Module K W] (t : V ⊗[K] W) : ∃ (n : ℕ) (x : Fin n → V) (y : Fin n → W), t = ∑ i, x i ⊗ₜ[K] y i := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  | tmul a b => exact ⟨1, fun _ ↦ a, fun _ ↦ b, by simp⟩
  | add s t hs ht =>
    obtain ⟨n, x, y, rfl⟩ := hs
    obtain ⟨m, x', y', rfl⟩ := ht
    exact ⟨n + m, Fin.append x x', Fin.append y y', by simp [Fin.sum_univ_add]⟩

theorem exists_fin_affine_cover {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) [QuasiCompact s] :
    ∃ (n : ℕ) (D : Fin n → X.Opens), (∀ i, IsAffineOpen (D i)) ∧ ⨆ i, D i = ⊤ := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  obtain ⟨S, hS, e⟩ := (isCompact_iff_finite_and_eq_biUnion_affineOpens (U := (⊤ : X.Opens))).1 isCompact_univ
  have := hS.fintype
  let q := (Fintype.equivFin S).symm
  refine ⟨_, fun i ↦ (q i).1.1, fun i ↦ (q i).1.2, ?_⟩
  rw [e]
  apply le_antisymm
  · exact iSup_le fun i ↦ le_iSup₂_of_le (q i).1 (q i).2 le_rfl
  · refine iSup₂_le fun U hU ↦ ?_
    obtain ⟨i, hi⟩ := q.surjective ⟨U, hU⟩
    exact le_iSup_of_le i (by simp only [hi]; exact le_rfl)

variable {K : Type} [Field K]

theorem overPullbackStructureSheaf_cohomology_cup {Y A : Over (Sp K)} (f : Y ⟶ A) (a b : HO1 A.hom) :
    structureSheafH2Pullback f (cup (OAff A.hom) a b) = cup (OAff Y.hom) (pO1 f a) (pO1 f b) :=
  ((GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id).2.1 K K A.left Y.left A.hom Y.hom (RingHom.id K) f.left (ovw f)).1 a b

variable (A : Over (Sp K)) [GrpObj A]

abbrev mixed : HO1 A.hom →ₗ[K] HO1 A.hom →ₗ[K] HO2 (A ⊗ A).hom :=
  (cup (OAff (A ⊗ A).hom)).compl₁₂ (pO1 (fst A A)) (pO1 (snd A A))

theorem defect_eq (hp : StructureSheafH1Primitive A) (t : HO1 A.hom ⊗[K] HO1 A.hom) :
    structureSheafH2Pullback μ[A] (TensorProduct.lift (cup (OAff A.hom)) t) - structureSheafH2Pullback (fst A A) (TensorProduct.lift (cup (OAff A.hom)) t)
      - structureSheafH2Pullback (snd A A) (TensorProduct.lift (cup (OAff A.hom)) t)
      = TensorProduct.lift (mixed A) (t - TensorProduct.comm K _ _ t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp only [TensorProduct.lift.tmul, TensorProduct.comm_tmul, map_sub, overPullbackStructureSheaf_cohomology_cup, hp a, hp b, map_add,
      LinearMap.add_apply, LinearMap.compl₁₂_apply]
    rw [GlobalTheory.T.commAlgFunctorCohomologyCup_anticomm K _ (OAff (A ⊗ A).hom) (pO1 (snd A A) a) (pO1 (fst A A) b)]
    abel
  | add s t hs ht =>
    have e : s + t - TensorProduct.comm K _ _ (s + t)
        = (s - TensorProduct.comm K _ _ s) + (t - TensorProduct.comm K _ _ t) := by
      rw [map_add]; abel
    rw [e, map_add (TensorProduct.lift (mixed A)), ← hs, ← ht]
    simp only [map_add]
    abel

theorem mixed_injective [IsSeparated A.hom] [QuasiCompact A.hom] (u : HO1 A.hom ⊗[K] HO1 A.hom)
    (hu : TensorProduct.lift (mixed A) u = 0) : u = 0 := by
  obtain ⟨n, x, y, rfl⟩ := exists_fin_sum_tmul u
  refine GlobalTheory.T.kunneth_cup_tensor_injective K A A inferInstance inferInstance inferInstance inferInstance n x y ?_
  simpa [map_sum] using hu

theorem symm_of_prim [IsSeparated A.hom] [QuasiCompact A.hom] (hp : StructureSheafH1Primitive A) (t : HO1 A.hom ⊗[K] HO1 A.hom)
    (ht : structureSheafH2Pullback μ[A] (TensorProduct.lift (cup (OAff A.hom)) t)
      = structureSheafH2Pullback (fst A A) (TensorProduct.lift (cup (OAff A.hom)) t)
        + structureSheafH2Pullback (snd A A) (TensorProduct.lift (cup (OAff A.hom)) t)) :
    TensorProduct.comm K _ _ t = t := by
  have h0 := defect_eq A hp t
  rw [ht, add_sub_cancel_left, sub_self] at h0
  exact (sub_eq_zero.1 (mixed_injective A _ h0.symm)).symm

end GlobalTheory.AbCoh.WedgeSq

open GlobalTheory.AbCoh.WedgeSq in

theorem GlobalTheory.AbCoh.wedgeO_noPrimO2 : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    GlobalTheory.AbCoh.WedgeO (OAff A.hom) ∧ GlobalTheory.AbCoh.NoPrimitiveStructureSheafH2 A := by
  intro K _ _ A _ g hab hsm
  haveI : IsProper A.hom := hab.proper
  haveI hsep : IsSeparated A.hom := inferInstance
  haveI hqc : QuasiCompact A.hom := inferInstance
  obtain ⟨-, hprim, -⟩ := GlobalTheory.T.abelian_variety_h1_axes_primitive_rank K A g hab hsm
  obtain ⟨n, D, hD, hcov⟩ := GlobalTheory.AbCoh.WedgeSq.exists_fin_affine_cover A.hom
  obtain ⟨⟨e1⟩, ⟨e2⟩⟩ := GlobalTheory.T.cech_cohomology_structure_sheaf_iso K A.left A.hom (Fin n) D hsep hD hcov
  obtain ⟨hfin, h1, h2⟩ := GlobalTheory.T.cech_cohomology_trivial_bundle_abelian K A g hab hsm (Fin n) D hD hcov
  haveI := hfin 1
  haveI := hfin 2
  haveI : Module.Finite K (HO1 A.hom) := Module.Finite.equiv e1.symm
  haveI : Module.Finite K (HO2 A.hom) := Module.Finite.equiv e2.symm
  have hdim : Module.finrank K (HO2 A.hom) ≤ (Module.finrank K (HO1 A.hom)).choose 2 := by
    rw [e2.finrank_eq, e1.finrank_eq, h1]; exact h2
  have hrel : ∀ t : HO1 A.hom ⊗[K] HO1 A.hom, TensorProduct.lift (cup (OAff A.hom)) t = 0 →
      TensorProduct.comm K _ _ t = t := fun t ht ↦ symm_of_prim A hprim t (by simp [ht])
  obtain ⟨hw, hsurj, hsym⟩ := GlobalTheory.T.exteriorSquare_of_symmetric_tensor_relations K (HO1 A.hom) (HO2 A.hom) (cup (OAff A.hom)) hdim hrel
  refine ⟨hw, fun z hz ↦ ?_⟩
  obtain ⟨t, rfl⟩ := hsurj z
  exact hsym t (symm_of_prim A hprim t hz)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsCoeffLeOfHomogeneousTorusBound
section
open Filter Topology MvPolynomial GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp.CoefTorus

theorem sum_eq_of_coeff_ne_zero {n q : ℕ} {T : MvPolynomial (Fin n) ℤ} (hT : T.IsHomogeneous q)
    {d : Fin n →₀ ℕ} (hd : coeff d T ≠ 0) : ∑ i, d i = q := by
  have := hT hd
  simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using this

theorem aeval_smul_of_homogeneous {n q : ℕ} {T : MvPolynomial (Fin n) ℤ} (hT : T.IsHomogeneous q)
    (c : ℂ) (z : Fin n → ℂ) : aeval (c • z) T = c ^ q * aeval z T := by
  rw [aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [sum_eq_of_coeff_ne_zero hT (Finsupp.mem_support_iff.mp hd)]
  ring

theorem geom_root {N m : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N) (h0 : 0 < m) (h2 : m < 2 * N) :
    ∑ j : Fin N, (ζ ^ m) ^ (j : ℕ) = if m = N then (N : ℂ) else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun j => (ζ ^ m) ^ j) N]
  split_ifs with hm
  · subst hm; simp [hζ.pow_eq_one]
  · have hne : ζ ^ m ≠ 1 := by
      rw [Ne, hζ.pow_eq_one_iff_dvd]
      rintro ⟨c, hc⟩
      rcases c with _ | _ | c
      · omega
      · omega
      · nlinarith
    rw [geom_sum_eq hne, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow, sub_self, zero_div]

theorem key_sum {n q N : ℕ} {T : MvPolynomial (Fin n) ℤ} (hT : T.IsHomogeneous q) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) (α : Fin n →₀ ℕ) (hq : q < N) (hα : ∀ i, α i < N) :
    ∑ k : Fin n → Fin N, aeval (fun i => ζ ^ (k i : ℕ)) T * ∏ i, (ζ ^ (k i : ℕ)) ^ (N - α i)
      = ((coeff α T : ℤ) : ℂ) * (N : ℂ) ^ n := by
  have inner : ∀ d ∈ T.support, ∑ k : Fin n → Fin N,
      (algebraMap ℤ ℂ (coeff d T) * ∏ i, (ζ ^ (k i : ℕ)) ^ d i) * ∏ i, (ζ ^ (k i : ℕ)) ^ (N - α i)
      = if d = α then ((coeff α T : ℤ) : ℂ) * (N : ℂ) ^ n else 0 := by
    intro d hd
    have hdq : ∀ i, d i ≤ q := fun i => by
      rw [← sum_eq_of_coeff_ne_zero hT (Finsupp.mem_support_iff.mp hd)]
      exact Finset.single_le_sum (f := fun j => d j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have e1 : ∑ k : Fin n → Fin N,
        (algebraMap ℤ ℂ (coeff d T) * ∏ i, (ζ ^ (k i : ℕ)) ^ d i) * ∏ i, (ζ ^ (k i : ℕ)) ^ (N - α i)
        = algebraMap ℤ ℂ (coeff d T) * ∏ i, ∑ j : Fin N, (ζ ^ (d i + (N - α i))) ^ (j : ℕ) := by
      rw [Fintype.prod_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [mul_assoc, ← Finset.prod_mul_distrib]
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← pow_add, ← pow_mul, ← pow_mul, mul_comm]
    rw [e1]
    have e2 : ∀ i, ∑ j : Fin N, (ζ ^ (d i + (N - α i))) ^ (j : ℕ)
        = if d i = α i then (N : ℂ) else 0 := by
      intro i
      rw [geom_root hζ (by have := hα i; omega) (by have := hα i; have := hdq i; omega)]
      have := hα i; have := hdq i
      by_cases h : d i = α i
      · rw [if_pos (by omega), if_pos h]
      · rw [if_neg (by omega), if_neg h]
    simp_rw [e2]
    by_cases h : d = α
    · subst h; simp [Finset.prod_const, Finset.card_univ]
    · rw [if_neg h]
      obtain ⟨i, hi⟩ : ∃ i, d i ≠ α i := by
        by_contra hc; push_neg at hc; exact h (Finsupp.ext hc)
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (by rw [if_neg hi]), mul_zero]
  simp_rw [aeval_def, eval₂_eq', Finset.sum_mul]
  rw [Finset.sum_comm, Finset.sum_congr rfl inner, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · have h0 : coeff α T = 0 := not_not.mp (mt MvPolynomial.mem_support_iff.mpr h)
    simp [h0]

theorem coeff_le_of_torus_bound : ∀ (D q : ℕ) (T : MvPolynomial (Fin (D + 1)) ℤ) (M : ℝ), T.IsHomogeneous q →
    (∀ z : Fin (D + 1) → ℂ, z 0 = 1 → (∀ l, ‖z l‖ = 1) → ‖aeval z T‖ ≤ M) →
    ∀ α, |((coeff α T : ℤ) : ℝ)| ≤ M := by
  intro D q T M hT hM α
  have htor : ∀ z : Fin (D + 1) → ℂ, (∀ l, ‖z l‖ = 1) → ‖aeval z T‖ ≤ M := by
    intro z hz
    have h0 : z 0 ≠ 0 := by
      intro h; have := hz 0; simp [h] at this
    have hb := hM ((z 0)⁻¹ • z) (by simp [h0]) (by intro l; simp [norm_inv, hz])
    have e : z = z 0 • ((z 0)⁻¹ • z) := by rw [smul_smul, mul_inv_cancel₀ h0, one_smul]
    rw [e, aeval_smul_of_homogeneous hT, norm_mul, norm_pow, hz 0, one_pow, one_mul]
    exact hb
  set N := q + (∑ i, α i) + 1 with hN
  have hNpos : N ≠ 0 := by omega
  have hζ : IsPrimitiveRoot (Complex.exp (2 * ↑Real.pi * Complex.I / ↑N)) N :=
    Complex.isPrimitiveRoot_exp N hNpos
  set ζ := Complex.exp (2 * ↑Real.pi * Complex.I / ↑N)
  have hζn : ‖ζ‖ = 1 := hζ.norm'_eq_one hNpos
  have hα : ∀ i, α i < N := fun i => by
    have := Finset.single_le_sum (f := fun j => α j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  have key := key_sum hT hζ α (by omega) hα
  have hbound : ‖((coeff α T : ℤ) : ℂ) * (N : ℂ) ^ (D + 1)‖ ≤ (N : ℝ) ^ (D + 1) * M := by
    rw [← key]
    refine (norm_sum_le _ _).trans ?_
    have : ∀ k : Fin (D + 1) → Fin N,
        ‖aeval (fun i => ζ ^ (k i : ℕ)) T * ∏ i, (ζ ^ (k i : ℕ)) ^ (N - α i)‖ ≤ M := by
      intro k
      rw [norm_mul, norm_prod]
      simp only [norm_pow, hζn, one_pow, Finset.prod_const_one, mul_one]
      exact htor _ (fun l => by simp [hζn])
    refine (Finset.sum_le_sum fun k _ => this k).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
      nsmul_eq_mul]
    push_cast; exact le_refl _
  rw [norm_mul, norm_pow, Complex.norm_natCast, mul_comm] at hbound
  have hpos : (0 : ℝ) < (N : ℝ) ^ (D + 1) := by positivity
  have := le_of_mul_le_mul_left hbound hpos
  simpa [Complex.norm_intCast] using this

end GlobalTheory.HSAmp.CoefTorus
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsFinsumIntegralWeightSubLe
section
open Filter Topology MeasureTheory GlobalTheory.HSAmp
open scoped ComplexOrder Matrix

namespace GlobalTheory.HSAmp

theorem abs_integral_weight_sub_le_one {Y : Type} [MeasurableSpace Y] (μ : Measure Y)
    (B β w : Y → ℝ) (C : ℝ) (hB : Integrable B μ) (hβ : Integrable β μ) (hle : ∀ y, B y ≤ β y)
    (hw : Measurable w) (hC : ∀ y, |w y| ≤ C) :
    |∫ y, w y * B y ∂μ - ∫ y, w y * β y ∂μ| ≤ C * (∫ y, β y ∂μ - ∫ y, B y ∂μ) := by
  have hwm : AEStronglyMeasurable w μ := hw.aestronglyMeasurable
  have hb : ∀ᵐ y ∂μ, ‖w y‖ ≤ C := Eventually.of_forall fun y => by simpa using hC y
  have h1 : Integrable (fun y => w y * B y) μ := hB.bdd_mul hwm hb
  have h2 : Integrable (fun y => w y * β y) μ := hβ.bdd_mul hwm hb
  rw [← integral_sub h1 h2, ← integral_sub hβ hB, ← integral_const_mul]
  refine (abs_integral_le_integral_abs).trans ?_
  refine integral_mono (h1.sub h2).abs ((hβ.sub hB).const_mul C) fun y => ?_
  have h3 : 0 ≤ β y - B y := sub_nonneg.2 (hle y)
  show |w y * B y - w y * β y| ≤ C * (β y - B y)
  rw [← mul_sub, abs_mul, abs_sub_comm, abs_of_nonneg h3]
  exact mul_le_mul_of_nonneg_right (hC y) h3

theorem abs_finsum_integral_weight_sub_le :
    ∀ (S : Type) [Finite S] (Y : S → Type) [∀ σ, MeasurableSpace (Y σ)] (μ : ∀ σ, Measure (Y σ)) (B β w : ∀ σ, Y σ → ℝ) (C : ℝ), (∀ σ, Integrable (B σ) (μ σ)) → (∀ σ, Integrable (β σ) (μ σ)) → (∀ σ y, B σ y ≤ β σ y) → (∀ σ, Measurable (w σ)) → 0 ≤ C → (∀ σ y, |w σ y| ≤ C) → |∑ᶠ σ, ∫ y, w σ y * B σ y ∂μ σ - ∑ᶠ σ, ∫ y, w σ y * β σ y ∂μ σ| ≤ C * (∑ᶠ σ, ∫ y, β σ y ∂μ σ - ∑ᶠ σ, ∫ y, B σ y ∂μ σ) := by
  intro S _ Y _ μ B β w C hB hβ hle hw _ hC
  haveI := Fintype.ofFinite S
  simp only [finsum_eq_sum_of_fintype]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun σ _ => ?_)
  exact abs_integral_weight_sub_le_one (μ σ) (B σ) (β σ) (w σ) C (hB σ) (hβ σ) (hle σ) (hw σ) (hC σ)

end GlobalTheory.HSAmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchLogNormChernIntegrableOfPrincipalisation
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

namespace GlobalTheory.ArchIntegClosing

theorem archInteg : GlobalTheory.Published.Principalisation → GlobalTheory.MixHt.ArchInteg :=
  fun hP k _ Y _ q e hY M N r hr => GlobalTheory.ArchIntGenSmooth.archIntegrable hP k Y q e hY M N r hr

end GlobalTheory.ArchIntegClosing
end

