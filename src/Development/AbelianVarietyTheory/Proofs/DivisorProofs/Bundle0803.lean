import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0782
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeightedNormSquareRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0777
import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0778
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0754
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0066
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NonemptyIsLimitBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRefinementOfIsLimit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0783
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0061
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0084
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.WchartLePreimage
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0009

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralOfModelAtStatement
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_variableChange_isIntegral_of_modelAt : ∀ (F : IntermediateField ℚ ℂ) [NumberField F] (w : HeightOneSpectrum (𝓞 F)) (V : ValuationSubring ℂ) (A : WeierstrassCurve F) (D : F), (∀ x : F, (x : ℂ) ∈ V ↔ x ∈ w.valuationSubringAtPrime F) → D ≠ 0 → ModelAt V F (A.map (algebraMap F ℂ)) (D : ℂ) → ∃ (C : VariableChange F) (u : (w.valuationSubringAtPrime F)ˣ), (C • A).IsIntegral (w.valuationSubringAtPrime F) ∧ (C • A).Δ = ((u : w.valuationSubringAtPrime F) : F) * D := by
  first | exact @GlobalTheory.CMModel.exists_integral_of_modelAt | exact GlobalTheory.CMModel.exists_integral_of_modelAt | (intros; apply GlobalTheory.CMModel.exists_integral_of_modelAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvFrameOfPosDef
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows
open scoped ComplexOrder

namespace GlobalTheory.ColRows

theorem exists_inv_frame_of_posDef {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (hA : A.PosDef) :
    ∃ X : Matrix n n ℂ, IsUnit X.det ∧ (X⁻¹).conjTranspose * X⁻¹ = A := by
  open scoped MatrixOrder in
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.posSemidef.nonneg
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  have hBdet : IsUnit B.det := by
    rw [hB, Matrix.det_mul] at hdet
    exact isUnit_of_mul_isUnit_right hdet
  refine ⟨B⁻¹, Matrix.isUnit_nonsing_inv_det B hBdet, ?_⟩
  rw [Matrix.nonsing_inv_nonsing_inv B hBdet, hB, Matrix.star_eq_conjTranspose]

theorem exists_isFrames (K : Type) [Field K] [NumberField K] [StarRing K] (Bs : DefBase K) (Df : DefSide Bs)
    (h : ∀ v : InfinitePlace K, ((Df.HV Bs.μ0).map v.embedding).PosDef) : ∃ X0, IsFrames Df X0 := by
  choose X hX using fun v => exists_inv_frame_of_posDef _ (h v)
  exact ⟨X, hX⟩

end GlobalTheory.ColRows
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInverseConjMemClosureOfIsCompactStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conj_mem_closure_of_isCompact : ∀ (X : Type) [Monoid X] [TopologicalSpace X] [ContinuousMul X] [T2Space X] (H C : Set X), IsCompact C → ∀ g : X, (∀ W ∈ 𝓝 g, ∃ c ∈ C, ∃ c' ∈ C, c * c' = 1 ∧ c' * c = 1 ∧ ∃ w ∈ W, c * w * c' ∈ H) → ∃ c ∈ C, ∃ c' ∈ C, c * c' = 1 ∧ c' * c = 1 ∧ c * g * c' ∈ closure H := by
  first | exact @GlobalTheory.exists_inverse_conj_mem_closure_of_isCompact | exact GlobalTheory.exists_inverse_conj_mem_closure_of_isCompact | (intros; apply GlobalTheory.exists_inverse_conj_mem_closure_of_isCompact <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsConnIsEtSplittingStatement
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_connected_etale_splitting_pDivGroup : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k), ∃ (G₀ G₁ : PDivGroup p k) (i₀ : G₀ ⟶ G) (q₀ : G ⟶ G₀) (i₁ : G₁ ⟶ G) (q₁ : G ⟶ G₁), G₀.IsConn ∧ G₁.IsEt ∧ i₀ ≫ q₀ = 𝟙 G₀ ∧ i₁ ≫ q₁ = 𝟙 G₁ ∧ q₀ ≫ i₀ + q₁ ≫ i₁ = 𝟙 G := by
  first | exact @GlobalTheory.PDivGroup.exists_isConn_isEt_splitting | exact GlobalTheory.PDivGroup.exists_isConn_isEt_splitting | (intros; apply GlobalTheory.PDivGroup.exists_isConn_isEt_splitting <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsIsoMorphismRestrictOfIsProjOverStatement
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonempty_isIso_morphismRestrict_of_isProjOver : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (Y M : RatModel o Ω), IsProjOver Y.s → ∀ q : Y.Z ⟶ M.Z, M.IsHom Y (AlgHom.id o Ω) q → ∃ U : M.Z.Opens, (U : Set M.Z).Nonempty ∧ IsIso (q ∣_ U) := by
  first | exact @GlobalTheory.ZH.RatModel.exists_isIso_morphismRestrict_of_isProjOver | exact GlobalTheory.ZH.RatModel.exists_isIso_morphismRestrict_of_isProjOver | (intros; apply GlobalTheory.ZH.RatModel.exists_isIso_morphismRestrict_of_isProjOver <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsStd
section
set_option autoImplicit false

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace GlobalTheory.PDA

theorem PDPoly.exists_isStd : ∀ (B : Type) [CommRing B] (J : Ideal B) (δ : DividedPowers J) (Q : PDPoly B),
    ∃ η : DividedPowers (Q.ext J), Q.IsStd δ η := by
  intro B _ J δ Q
  obtain ⟨η, hη⟩ := GlobalTheory.T.exists_dividedPowers_dividedPowerPolyAlgebra_augIdeal B Q
  obtain ⟨ε, hε⟩ := (GlobalTheory.T.exists_lift_and_augmentation_map B Q).2
  obtain ⟨θ, hθ, hθη⟩ := GlobalTheory.T.exists_dividedPowers_split_augmentation_extension B J δ Q.P ε Q.aug η hε
  refine ⟨θ, ⟨hθ, fun n ↦ ?_⟩⟩
  rw [hθη n _ (Q.e_succ_mem_aug 0), hη]

end GlobalTheory.PDA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKernelEquivConjugatePointsStatement
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_kernel_equiv_conjugate_points : ∀ (L : PeriodPair) (σ : ℂ ≃+* ℂ) (α : ℂ) (S S' : Finset ℂ), L.g₂ = σ L.g₂ → L.g₃ = σ L.g₃ → MulStable L α → IsKerReps L α S → IsKerReps L (σ α) S' → ∃ e : S ≃ S', ∀ t : S, GlobalTheory.ConjPoint.IsConj L L σ (t : ℂ) (e t : ℂ) := by
  first | exact @GlobalTheory.ConjPoint.exists_equiv_kerReps_isConj | exact GlobalTheory.ConjPoint.exists_equiv_kerReps_isConj | (intros; apply GlobalTheory.ConjPoint.exists_equiv_kerReps_isConj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKummerClassOnFinerEtaleNbhdCurveStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_kummerClass_on_finer_etaleNbhd_curve : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ (A' : Type) [CommRing A'] [Algebra B A'], IsExcisionNbhd B A' f → ∀ w : Ht q (sp (Localization.Away (algebraMap B A' f))) 1 1, ∃ (A₂ : Type) (_ : CommRing A₂) (_ : Algebra B A₂) (_ : Algebra A' A₂) (_ : IsScalarTower B A' A₂), IsExcisionNbhd B A₂ f ∧ ∃ c : (Γ(Spec (CommRingCat.of (Localization.Away (algebraMap B A₂ f))), ⊤))ˣ, ∀ φ : Localization.Away (algebraMap B A' f) →+* Localization.Away (algebraMap B A₂ f), φ.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂) → pull _ (spMap φ) _ _ w = kum q c := by
  first | (exact @GlobalTheory.EtC.KummerLoc.exists_kummer_on_finer_nbhd) | (exact GlobalTheory.EtC.KummerLoc.exists_kummer_on_finer_nbhd) | (intros; apply GlobalTheory.EtC.KummerLoc.exists_kummer_on_finer_nbhd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoNhdOfStalkBaseChange
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.StalkLBIso

set_option backward.isDefEq.respectTransparency false

theorem lbIso_pull_iff {X Y : Scheme.{0}} {A B : LB X} (hA : A.IsLB) (hB : B.IsLB) (f : Y ⟶ X) :
    LBIso (A.pull f) (B.pull f) ↔
      CechPic.pull f (CechPic.cls A hA) = CechPic.pull f (CechPic.cls B hB) := by
  rw [← CechPic.cls_pull hA f (pull_isLB hA f), ← CechPic.cls_pull hB f (pull_isLB hB f)]
  exact (CechPic.cls_eq_iff _ _).symm

theorem exists_lbIso_nhd : ∀ {S X : Scheme.{0}} [IsLocallyNoetherian S] (h : X ⟶ S) [QuasiCompact h]
    [QuasiSeparated h] (x : S) (A B : LB X), A.IsLB → B.IsLB →
    LBIso (A.pull (pullback.fst h (S.fromSpecStalk x))) (B.pull (pullback.fst h (S.fromSpecStalk x))) →
    ∃ W : S.Opens, x ∈ W ∧ LBIso (A.pull (h ⁻¹ᵁ W).ι) (B.pull (h ⁻¹ᵁ W).ι) := by
  intro S X _ h _ _ x A B hA hB hAB

  have hpb : IsPullback (pullback.fst h (S.fromSpecStalk x)) (pullback.snd h (S.fromSpecStalk x)) h
      (S.fromSpecStalk x) := IsPullback.of_hasPullback _ _
  have hc := (GlobalTheory.StalkLimit.nonempty_isLimit hpb).some
  obtain ⟨V₀⟩ : Nonempty (GlobalTheory.StalkLimit.AffNhd x) := IsCofiltered.nonempty
  have : IsAffine V₀.1.toScheme := V₀.2.2
  have : CompactSpace ((GlobalTheory.StalkLimit.diagram x h).obj V₀) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd h V₀.1.ι)
  have : QuasiSeparatedSpace ((GlobalTheory.StalkLimit.diagram x h).obj V₀) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd h V₀.1.ι)

  have h0 : LBIso ((A.pull (pullback.fst h V₀.1.ι)).pull ((GlobalTheory.StalkLimit.cone hpb).π.app V₀))
      ((B.pull (pullback.fst h V₀.1.ι)).pull ((GlobalTheory.StalkLimit.cone hpb).π.app V₀)) := by
    rw [lbIso_pull_iff (pull_isLB hA _) (pull_isLB hB _), CechPic.cls_pull hA, CechPic.cls_pull hB,
      ← CechPic.pull_comp, ← CechPic.pull_comp, GlobalTheory.StalkLimit.cone_π_fst, ← lbIso_pull_iff hA hB]
    exact hAB

  obtain ⟨j, f, hj⟩ := GlobalTheory.exists_lbIso_of_isLimit (GlobalTheory.StalkLimit.diagram x h)
    (fun V => (GlobalTheory.StalkLimit.cone hpb).π.app V) (fun f => (GlobalTheory.StalkLimit.cone hpb).w f) hc
    (A.pull (pullback.fst h V₀.1.ι)) (B.pull (pullback.fst h V₀.1.ι)) (pull_isLB hA _) (pull_isLB hB _) h0
  have hj' : CechPic.pull (pullback.fst h j.1.ι) (CechPic.cls A hA) =
      CechPic.pull (pullback.fst h j.1.ι) (CechPic.cls B hB) := by
    rw [lbIso_pull_iff (pull_isLB hA _) (pull_isLB hB _), CechPic.cls_pull hA, CechPic.cls_pull hB,
      ← CechPic.pull_comp, ← CechPic.pull_comp, GlobalTheory.StalkLimit.diagram_map_fst] at hj
    exact hj

  refine ⟨j.1, j.2.1, ?_⟩
  rw [lbIso_pull_iff hA hB, ← pullbackRestrictIsoRestrict_inv_fst, CechPic.pull_comp, CechPic.pull_comp, hj']

end GlobalTheory.StalkLBIso
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleNhdOfStalkBaseChange
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.StalkLB

set_option backward.isDefEq.respectTransparency false

theorem exists_lb_nhd : ∀ {S X : Scheme.{0}} [IsLocallyNoetherian S] (h : X ⟶ S) [QuasiCompact h]
    [QuasiSeparated h] (x : S) (N : LB (pullback h (S.fromSpecStalk x))), N.IsLB →
    ∃ W : S.Opens, x ∈ W ∧ ∃ N' : LB ↑(h ⁻¹ᵁ W), N'.IsLB ∧
      ∀ a : pullback h (S.fromSpecStalk x) ⟶ ↑(h ⁻¹ᵁ W),
        a ≫ (h ⁻¹ᵁ W).ι = pullback.fst h (S.fromSpecStalk x) → LBIso (N'.pull a) N := by
  intro S X _ h _ _ x N hN
  have hpb := IsPullback.of_hasPullback h (S.fromSpecStalk x)
  have hlim : IsLimit (GlobalTheory.schemeConeOfFamily (GlobalTheory.StalkLimit.diagram x h)
      (fun V => (GlobalTheory.StalkLimit.cone hpb).π.app V) (fun f => (GlobalTheory.StalkLimit.cone hpb).w f)) :=
    (GlobalTheory.StalkLimit.nonempty_isLimit hpb).some
  have hcpt : ∀ V : GlobalTheory.StalkLimit.AffNhd x, CompactSpace ((GlobalTheory.StalkLimit.diagram x h).obj V) := by
    intro V
    haveI : IsAffine V.1.toScheme := V.2.2
    exact QuasiCompact.compactSpace_of_compactSpace (pullback.snd h V.1.ι)
  have hqs : ∀ V : GlobalTheory.StalkLimit.AffNhd x,
      QuasiSeparatedSpace ((GlobalTheory.StalkLimit.diagram x h).obj V) := by
    intro V
    haveI : IsAffine V.1.toScheme := V.2.2
    exact quasiSeparatedSpace_of_quasiSeparated (pullback.snd h V.1.ι)
  obtain ⟨j, M, hM, -, hall⟩ := GlobalTheory.LBLimit.exists_lb_of_isLimit (GlobalTheory.StalkLimit.diagram x h)
    (fun V => (GlobalTheory.StalkLimit.cone hpb).π.app V) (fun f => (GlobalTheory.StalkLimit.cone hpb).w f) hlim N hN
  refine ⟨j.1, j.2.1, M.pull (pullbackRestrictIsoRestrict h j.1).inv, pull_isLB hM _, fun a ha => ?_⟩
  refine LBIso.symm (hall _ a (pullbackRestrictIsoRestrict h j.1).inv ?_)
  have hfst : (GlobalTheory.StalkLimit.cone hpb).π.app j ≫ pullback.fst h j.1.ι =
      pullback.fst h (S.fromSpecStalk x) := GlobalTheory.StalkLimit.cone_π_fst hpb j
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackRestrictIsoRestrict_inv_fst, ha, hfst]
  · rw [← cancel_mono j.1.ι]
    simp only [Category.assoc]
    rw [← pullback.condition, pullbackRestrictIsoRestrict_inv_fst_assoc, reassoc_of% ha,
      reassoc_of% hfst]

end GlobalTheory.StalkLB
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonicSimpleRootGeneratorResidueStatement
section
open IsLocalRing GlobalTheory.Toroidal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_monic_simple_root_generating_residue : ∀ (O R' Ω : Type) [CommRing O] [IsLocalRing O] [CommRing R'] [IsLocalRing R'] [Field Ω] (φ' : O →+* R') (u' : R' →+* Ω), IsEtaleCompletion φ' → ((residue R').comp φ').FormallyUnramified → RingHom.ker u' = maximalIdeal R' → ∃ (G : Polynomial O) (β : Ω), G.Monic ∧ (G.map (u'.comp φ')).eval β = 0 ∧ (G.map (u'.comp φ')).derivative.eval β ≠ 0 ∧ ∀ r : R', ∃ q : Polynomial O, u' r = (q.map (u'.comp φ')).eval β := by
  first | exact @GlobalTheory.exists_monic_simple_root_generator_residue | exact GlobalTheory.exists_monic_simple_root_generator_residue | (intros; apply GlobalTheory.exists_monic_simple_root_generator_residue <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulOfValLe
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH GlobalTheory.UT
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ThetaDvr

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real}
  {V : Type} [CommRing V] [IsDomain V]

theorem torsion_points (yK : S.R →+* FractionRing V) {A : PolAV (Sp (FractionRing V))} {φ : A.A.left ⟶ ρ.P.A.left}
    (cart : IsGrpPullback A.A ρ.P.A (spMap yK) φ) :
    ∃ x : S.Gam → (TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ A.A),
      (∀ a, (x a).left ≫ φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp yK) ≫
        (ρ.pt a).left) ∧ (∀ a b, x (a + b) = x a * x b) ∧ Function.Injective x ∧
      ∀ z : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ A.A, z ^ (S.r * S.N) = 1 → ∃ a, z = x a := by
  have e : (TFK (R := V) (AlgebraicClosure (FractionRing V))).hom ≫ spMap yK =
      spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp yK) :=
    (Spec.map_comp (CommRingCat.ofHom yK) (CommRingCat.ofHom (algebraMap _ _))).symm
  obtain ⟨x, h₁, h₂⟩ := labelled_torsion_pull cart (TFK (R := V) (AlgebraicClosure (FractionRing V)))
    (E := baseOver (Sp S.R))
    (Over.homMk ((TFK (R := V) (AlgebraicClosure (FractionRing V))).hom ≫ spMap yK :) (by simp)) ρ.pt (S.r * S.N)
    ρ.pt_add (fun a => (ρ.fr_tors a).1) (fun z hz => ρ.pt_bij (AlgebraicClosure (FractionRing V)) _ z hz)
  exact ⟨x, fun a => (h₁ a).trans (by rw [← e]; rfl), h₂⟩

theorem frames (yK : S.R →+* FractionRing V) {A : PolAV (Sp (FractionRing V))} {φ : A.A.left ⟶ ρ.P.A.left}
    (cart : IsGrpPullback A.A ρ.P.A (spMap yK) φ) (lb : LBIso A.L (ρ.P.L.pull φ))
    (x : S.Gam → (TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ A.A))
    (hx : ∀ a, (x a).left ≫ φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp yK) ≫
      (ρ.pt a).left) :
    ∃ (rig : LB.Gen (A.L.pull (eSec A.A)))
      (e : ∀ a, LB.Gen (LB.LinComb A.L (Y := (TFK (R := V) (AlgebraicClosure (FractionRing V))).left) (K := Fin 1)
        (fun _ => (x a).left) (fun _ => 1))),
      rig.IsGen ∧ (∀ a, IsTorsFrame A rig (S.r * S.N) (x a) (e a)) ∧
      ∀ (k : ℕ) (σ : LB.Sec (LPow ρ.P.A ρ.P.L (k : ℤ) (baseOver (Sp S.R)))),
        ∃ t : SecA A (AlgebraicClosure (FractionRing V)) k, ∀ (a : S.Gam) (c : S.R),
          IsValueAt ρ.P.A ρ.P.L (k : ℤ) σ (ρ.pt a) (powFrame ρ.P.A ρ.P.L (ρ.pt a) (ρ.fr a) (k : ℤ)) (fn c) →
          ∀ z J, Good A.L z J → sA t (ptSecT A.A (x a)).left z J =
            @id ((TFK (R := V) (AlgebraicClosure (FractionRing V))).left.presheaf.stalk z)
              (cst (R := V) (AlgebraicClosure (FractionRing V)) z
                ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp yK c)) *
            (val (powFrame A.A A.L (x a) (e a) (k : ℤ)) (𝟙 _) z J).val := by
  have hh : (spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp yK) :
      (TFK (R := V) (AlgebraicClosure (FractionRing V))).left ⟶ (baseOver (Sp S.R)).left) ≫ (baseOver (Sp S.R)).hom =
      (TFK (R := V) (AlgebraicClosure (FractionRing V))).hom ≫ spMap yK :=
    (Category.comp_id _).trans (Spec.map_comp (CommRingCat.ofHom yK) (CommRingCat.ofHom (algebraMap _ _)))
  obtain ⟨rig, e, h₁, h₂, h₃⟩ := GlobalTheory.FrameMove.exists_move (T := baseOver (Sp S.R))
    (T' := TFK (R := V) (AlgebraicClosure (FractionRing V))) cart lb hh ρ.rig_gen hx ρ.fr_tors
  refine ⟨rig, e, h₁, h₂, fun k σ => ?_⟩
  obtain ⟨t, ht⟩ := h₃ k σ
  exact ⟨t, fun a c hc z J hJ => (ht a _ hc z J hJ).trans (congrArg (· * _) (GlobalTheory.FrameMove.gs_spMap _ z c))⟩

end GlobalTheory.ThetaDvr
end

namespace GlobalTheory.ThetaDvr

open ReciprocityTheory.ChartRestriction.G.DVR

theorem exists_mul_of_val_le {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
    (hϖ : Irreducible ϖ) {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)}
    (hv : ValOver ϖ F v) {x y : FractionRing V} (hy : y ≠ 0)
    (h : v (algebraMap (FractionRing V) F y) ≤ v (algebraMap (FractionRing V) F x)) :
    ∃ w : V, x = algebraMap V (FractionRing V) w * y ∧
      (v (algebraMap (FractionRing V) F y) < v (algebraMap (FractionRing V) F x) → w ∈ IsLocalRing.maximalIdeal V) := by
  by_cases hx : x = 0
  · exact ⟨0, by rw [hx, map_zero, zero_mul], fun _ => zero_mem _⟩
  obtain ⟨n, u, hu⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.RegC.exists_hasVal hϖ x hx
  obtain ⟨m, u', hu'⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.RegC.exists_hasVal hϖ y hy
  have hn := hv x n ⟨u, hu⟩
  have hm := hv y m ⟨u', hu'⟩
  rw [hn, hm, WithTop.coe_le_coe, Int.cast_le] at h
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = m + k := ⟨(n - m).toNat, by omega⟩
  have hϖ0 : algebraMap V (FractionRing V) ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 hϖ.ne_zero
  have hu'1 : algebraMap V (FractionRing V) (↑u'⁻¹ : V) * algebraMap V (FractionRing V) (u' : V) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  refine ⟨ϖ ^ k * u * ↑u'⁻¹, ?_, fun hlt => ?_⟩
  · rw [hu, hu', hk, zpow_add₀ hϖ0, zpow_natCast, map_mul, map_mul, map_pow]
    linear_combination (-(algebraMap V (FractionRing V) ϖ ^ m * algebraMap V (FractionRing V) ϖ ^ k *
      algebraMap V (FractionRing V) (u : V))) * hu'1
  · rw [hn, hm, WithTop.coe_lt_coe, Int.cast_lt] at hlt
    have hk0 : k ≠ 0 := by omega
    refine Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ ?_ k (Nat.pos_of_ne_zero hk0)))
    exact (IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit

end GlobalTheory.ThetaDvr
end

