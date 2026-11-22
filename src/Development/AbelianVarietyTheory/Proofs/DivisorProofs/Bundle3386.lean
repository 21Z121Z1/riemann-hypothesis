import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3368
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictCapFBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0687
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0701
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0705
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2875
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1537
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0786
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0951
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3256
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3364
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0037
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0035
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0646
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1017
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2411
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingEqExpRiemannFormAppellHumbertFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3369
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingRiemannForm
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.WeilIsGrpPullbackIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0187
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0140
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0010
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianCechH1BasisCocycles
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechDR (HO1)

namespace GlobalTheory.CechFree

theorem cech_free : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (g : ℕ) (I : Type) [Finite I] (U : I → B.left.Opens), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → ⨆ i, U i = ⊤ → (∀ i, IsAffineOpen (U i)) → ∃ b : Fin g → C1 U, (∀ a, IsCoc U (b a)) ∧ ∀ c : C1 U, IsCoc U c → ∃! cc : Fin g → A, IsCob U (fun i j => c i j - ∑ a, constFn B.hom _ (cc a) * b a i j) := by
  intro A _ _ _ B _ _ g I _ U hA hg hcov hU
  classical
  have hinf : ∀ V W : B.left.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W) := by
    haveI := hA.proper
    have : B.left.IsSeparated := ⟨by rw [← terminal.comp_from B.hom]; infer_instance⟩
    exact fun V W hV hW => hV.inf hW
  obtain ⟨hfin, hproj, hrk⟩ := (GlobalTheory.T.abelianScheme_structureSheafCohomology_noetherian A B g hA hg).1
  haveI := hfin
  haveI := hproj
  haveI : Module.Free A (HO1 B.hom) := Module.free_of_flat_of_isLocalRing
  have hr : Module.finrank A (HO1 B.hom) = g := by
    rw [← hrk (IsLocalRing.closedPoint A), Module.rankAtStalk_eq_finrank_tensorProduct, Module.finrank_baseChange]
  let bH := Module.finBasisOfFinrankEq A (HO1 B.hom) hr
  let F := GlobalTheory.CechCmp.capF B.hom U hU hinf
  let e : HO1 B.hom ≃ₗ[A] CatCoh.H1 F :=
    LinearEquiv.ofBijective (CatCoh.CoefMap.restrict (GlobalTheory.CechDR.OAff B.hom)
      (GlobalTheory.CechCmp.capAff_mono U hU hinf).functor.op).pull1 (GlobalTheory.CechCmp.restrict_capF_bijective B.hom U hU hinf hcov)
  let bP := bH.map e
  choose f hf using fun a => CatCoh.H1.mk_surjective F (bP a)
  let b : Fin g → C1 U := fun a => GlobalTheory.CechCmp.toCech B.hom U hU hinf (f a).1
  have hb : ∀ a, IsCoc U (b a) := fun a => GlobalTheory.T.isCechOneCocycle_posetOneCochainToCechCochain I B.left A B.hom U hU hinf _ (f a).2
  have hbP : ∀ a, CatCoh.H1.mk F ⟨GlobalTheory.CechCmp.toPos B.hom U hU hinf (b a),
      GlobalTheory.T.toPos_mem_Z1_of_isCoc I B.left A B.hom U hU hinf _ (hb a)⟩ = bP a := by
    intro a
    rw [← hf a, CatCoh.H1.mk_eq_mk]
    exact GlobalTheory.T.exists_d0_eq_toPos_toCech_sub_of_mem_Z1 I B.left A B.hom U hU hinf _ (f a).2
  have hbb : ∀ a, GlobalTheory.CechCmp.toCech B.hom U hU hinf (GlobalTheory.CechCmp.toPos B.hom U hU hinf (b a)) = b a :=
    fun a => GlobalTheory.T.posetToCech_cechToPoset_cocycle_eq I B.left A B.hom U hU hinf _ (hb a)

  have hlc : ∀ (cc : Fin g → A) (hm : GlobalTheory.CechCmp.toPos B.hom U hU hinf
      (fun i j => ∑ a, constFn B.hom (U i ⊓ U j) (cc a) * b a i j) ∈ CatCoh.Z1 F),
      CatCoh.H1.mk F ⟨_, hm⟩ = ∑ a, cc a • bP a := by
    intro cc hm
    have : (⟨_, hm⟩ : CatCoh.Z1 F) = ∑ a, cc a • ⟨GlobalTheory.CechCmp.toPos B.hom U hU hinf (b a),
        GlobalTheory.T.toPos_mem_Z1_of_isCoc I B.left A B.hom U hU hinf _ (hb a)⟩ := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simp only [Submodule.coe_smul]
      exact GlobalTheory.CechCmp.toPos_lc B.hom U hU hinf cc b
    rw [this, map_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [map_smul, hbP]
  have hmem : ∀ cc : Fin g → A, GlobalTheory.CechCmp.toPos B.hom U hU hinf
      (fun i j => ∑ a, constFn B.hom (U i ⊓ U j) (cc a) * b a i j) ∈ CatCoh.Z1 F := by
    intro cc
    rw [GlobalTheory.CechCmp.toPos_lc]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (GlobalTheory.T.toPos_mem_Z1_of_isCoc I B.left A B.hom U hU hinf _ (hb a))
  refine ⟨b, hb, fun c hc => ?_⟩
  have hcm := GlobalTheory.T.toPos_mem_Z1_of_isCoc I B.left A B.hom U hU hinf c hc
  let x := CatCoh.H1.mk F ⟨_, hcm⟩
  have hex : IsCob U (fun i j => c i j - ∑ a, constFn B.hom (U i ⊓ U j) (bP.repr x a) * b a i j) := by
    let l : C1 U := fun i j => ∑ a, constFn B.hom (U i ⊓ U j) (bP.repr x a) * b a i j
    have hl : GlobalTheory.CechCmp.toCech B.hom U hU hinf (GlobalTheory.CechCmp.toPos B.hom U hU hinf l) = l := by
      rw [GlobalTheory.CechCmp.toPos_lc, GlobalTheory.CechCmp.toCech_lc]
      simp only [hbb, l]
    have h0 : CatCoh.H1.mk F ⟨_, hcm⟩ = CatCoh.H1.mk F ⟨_, hmem (bP.repr x)⟩ := by
      rw [hlc _ (hmem _)]
      exact (bP.sum_repr x).symm
    obtain ⟨g0, hg0⟩ := CatCoh.H1.mk_eq_mk.1 h0
    have key : (fun i j => c i j - l i j) = GlobalTheory.CechCmp.toCech B.hom U hU hinf (CatCoh.d0 F g0) := by
      rw [hg0, GlobalTheory.CechCmp.toCech_sub, GlobalTheory.T.posetToCech_cechToPoset_cocycle_eq I B.left A B.hom U hU hinf c hc, hl]
      rfl
    show IsCob U (fun i j => c i j - l i j)
    rw [key]
    exact GlobalTheory.T.isCob_toCech_d0 I B.left A B.hom U hU hinf g0
  refine ⟨bP.repr x, hex, fun cc hcc => ?_⟩
  have hcs : ∀ (O : B.left.Opens) (y z : A), constFn B.hom O (y - z) = constFn B.hom O y - constFn B.hom O z :=
    fun O y z => by simp only [constFn, map_sub]
  let δ : Fin g → A := fun a => bP.repr x a - cc a
  have hcob : IsCob U (fun i j => ∑ a, constFn B.hom (U i ⊓ U j) (δ a) * b a i j) := by
    obtain ⟨β₁, h₁⟩ := hcc
    obtain ⟨β₂, h₂⟩ := hex
    refine ⟨fun i => β₁ i - β₂ i, fun i j => ?_⟩
    have e₁ := h₁ i j
    have e₂ := h₂ i j
    simp only [δ, hcs, sub_mul, Finset.sum_sub_distrib, GlobalTheory.KS.rsT_sub] at e₁ e₂ ⊢
    linear_combination e₁ - e₂
  obtain ⟨g1, hg1⟩ := GlobalTheory.T.exists_d0_eq_toPos_of_isCob I B.left A B.hom U hU hinf _ hcob
  have hz : ∑ a, δ a • bP a = 0 := by
    rw [← hlc δ (hmem δ)]
    exact CatCoh.H1.mk_eq_zero.2 ⟨g1, hg1⟩
  have hδ := Fintype.linearIndependent_iff.1 bP.linearIndependent δ hz
  funext a
  exact (sub_eq_zero.1 (hδ a)).symm

end GlobalTheory.CechFree
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianCechH1TrivialBundleRankBound
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.AbCoh.FDimField

theorem cechLB_triv_finite_finrank_one_le : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → A.left.Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → Module.Finite K ((GlobalTheory.AbLaw.cechLB A.hom (LB.triv A.left) D).homology 1) ∧ Module.finrank K ((GlobalTheory.AbLaw.cechLB A.hom (LB.triv A.left) D).homology 1) ≤ g := by
  intro K _ A _ g hA hsm κ _ _ D hD hcov
  let L := AlgebraicClosure K
  let f : Sp L ⟶ Sp K := spMap (algebraMap K L)
  let A' : Over (Sp L) := (Over.pullback f).obj A
  let π : A'.left ⟶ A.left := pullback.fst A.hom f
  have hGP : IsGrpPullback A' A (spMap (algebraMap K L)) π := isGrpPullback_pullback A f
  have H : IsPullback π A'.hom A.hom (Spec.map (CommRingCat.ofHom (algebraMap K L))) := hGP.1
  obtain ⟨hA', hg'⟩ :=
    GlobalTheory.AbBaseChange.isAbelianScheme_and_relDim_of_isGrpPullback (algebraMap K L) A A' π g hGP hA hsm
  haveI := hA.proper
  haveI := GlobalTheory.isAffineHom_diagonal_of_isSeparated A.hom
  have hDs := GlobalTheory.isAffineOpen_finset_biInf hD
  let D' : κ → A'.left.Opens := fun i => π ⁻¹ᵁ D i
  have hD' : ∀ i, IsAffineOpen (D' i) := fun i => GlobalTheory.AbLaw.isAffineOpen_preimage_of_isPullback H (hD i)
  have hcov' : ⨆ i, D' i = ⊤ := by
    show ⨆ i, π ⁻¹ᵁ D i = ⊤
    rw [← Scheme.Hom.preimage_iSup, hcov]; rfl
  obtain ⟨hfin', hrank', -⟩ :=
    GlobalTheory.AbCoh.FDim.cechLB_triv_finrank_one_two L A' g hA' hg' κ D' hD' hcov'

  obtain ⟨c, hc⟩ := (GlobalTheory.CechPic.iso_triv_iff (LB.triv A.left)).1 ((GlobalTheory.CechPic.setoid A.left).iseqv.refl ⟨LB.triv A.left, LB.isLB_triv A.left⟩)
  obtain ⟨w, hw⟩ := (GlobalTheory.CechPic.iso_triv_iff ((LB.triv A.left).pull π)).2
    ⟨LB.genPull (LB.triv A.left) c π, LB.isGen_genPull (LB.triv A.left) c hc π⟩
  let C := GlobalTheory.AbLaw.cechLB A.hom (LB.triv A.left) D
  obtain ⟨e₃⟩ := GlobalTheory.FieldChangeInter.nonempty_homology_equiv L C 1
  have e₄ := ((HomologicalComplex.homologyFunctor _ _ 1).mapIso
    (GlobalTheory.AbLaw.cechLBBaseChangeIso (LB.isLB_triv A.left) H (fun s hs => hDs s hs))).toLinearEquiv
  have e₅ := (HomologicalComplex.homologyMapIso
    (GlobalTheory.AbLaw.cechLBCongr A'.hom D' (LB.isLB_triv A'.left) (LB.isLB_pull (LB.isLB_triv A.left) π) w hw) 1).toLinearEquiv
  let E : (L ⊗[K] C.homology 1) ≃ₗ[L] (GlobalTheory.AbLaw.cechLB A'.hom (LB.triv A'.left) D').homology 1 :=
    e₃.symm ≪≫ₗ e₄ ≪≫ₗ e₅.symm
  haveI := hfin' 1
  haveI : Module.Finite L (L ⊗[K] C.homology 1) := Module.Finite.equiv E.symm
  have hfinK : Module.Finite K (C.homology 1) := by
    have h1 : Module.rank L (L ⊗[K] C.homology 1) < Cardinal.aleph0 := Module.rank_lt_aleph0 L _
    rw [Module.rank_baseChange, Cardinal.lift_id] at h1
    exact Module.rank_lt_aleph0_iff.1 h1
  refine ⟨hfinK, le_of_eq ?_⟩
  rw [← Module.finrank_baseChange (R := L), E.finrank_eq]
  exact hrank'

end GlobalTheory.AbCoh.FDimField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDeRhamFreeHodgeSequenceBaseChange
section
set_option autoImplicit false

namespace GlobalTheory

theorem abelianDeRham_free_hodge_baseChange : GlobalTheory.Published.AbelianHodgeDeRham →
    GlobalTheory.Published.AbelianDeRham.Free ∧ GlobalTheory.Published.AbelianDeRham.Hodge ∧
      GlobalTheory.Published.AbelianDeRham.BaseChange := by
  intro hH
  obtain ⟨hF, hBC, -⟩ := GlobalTheory.abelianDeRham_free_baseChange_rigid hH
  exact ⟨hF, GlobalTheory.AbelianHodge.abelianDeRham_hodge
    GlobalTheory.SmoothLift.crystallineSmoothLift_of_relations hH, hBC⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDeRhamStructureOfCubeDualPoincareStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianSchemeDeRhamStructure_of_cube_dual_poincare : GlobalTheory.Published.AbelianHodgeDeRham → GlobalTheory.Published.CubeTheorem → GlobalTheory.Published.DualAbelianScheme → GlobalTheory.Published.PoincareDeRhamDuality → GlobalTheory.Published.AbelianDeRham := by
  first | exact @GlobalTheory.abelianDeRham_of_hodge_cube_dual_poincare | exact GlobalTheory.abelianDeRham_of_hodge_cube_dual_poincare | (intros; apply GlobalTheory.abelianDeRham_of_hodge_cube_dual_poincare <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDualNumberEndoEqTranslationStatement
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
theorem _root_.GlobalTheory.T.abelianScheme_dualNumber_endo_eq_translation : ∀ (k : Type) [Field k] (B : Over (Sp (DualNumber k))) [GrpObj B], IsAbelianScheme B → ∀ (α : B ⟶ B), (∀ (Z : Scheme.{0}) (z : Z ⟶ B.left) (y : Z ⟶ Sp k), z ≫ B.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → z ≫ α.left = z) → α = lift (toUnit B ≫ η[B] ≫ α) (𝟙 B) ≫ μ[B] := by
  first | exact @GlobalTheory.RigidEndo.eq_translate | exact GlobalTheory.RigidEndo.eq_translate | (intros; apply GlobalTheory.RigidEndo.eq_translate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeSquareZeroLiftsOfDeRhamCohomologyStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianSchemeSquareZeroLifts_of_deRhamCohomology : AbelianHodgeDeRham → AbelianSchemeLifts := by
  first | exact @GlobalTheory.LiftSys.abelianSchemeLifts_of_abelianHodgeDeRham | exact GlobalTheory.LiftSys.abelianSchemeLifts_of_abelianHodgeDeRham | (intros; apply GlobalTheory.LiftSys.abelianSchemeLifts_of_abelianHodgeDeRham <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeStructureSheafCohomologyAnyRing
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh

def semiToLin {S R : Type} [CommRing S] [CommRing R] [Algebra S R] {M N : Type} [AddCommGroup M] [Module S M]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower S R N] (f : M →ₛₗ[algebraMap S R] N) :
    M →ₗ[S] N where
  toFun := f
  map_add' := f.map_add
  map_smul' s m := by simp [f.map_smulₛₗ, algebraMap_smul]

theorem fp_of_tensor_equiv {S R M N : Type} [CommRing S] [CommRing R] [Algebra S R] [AddCommGroup M] [Module S M]
    [AddCommGroup N] [Module R N] {g : ℕ} (e : R ⊗[S] M ≃ₗ[R] N) (h : FP S M g) : FP R N g := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨Module.Finite.equiv e, Module.Projective.of_equiv e, fun p => ?_⟩
  rw [← Module.rankAtStalk_eq_of_equiv e, Module.rankAtStalk_baseChange, h3]

theorem wedge_of_isBaseChange {S R M N M₂ N₂ : Type} [CommRing S] [CommRing R] [Algebra S R]
    [AddCommGroup M] [Module S M] [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower S R N]
    [AddCommGroup M₂] [Module S M₂] [AddCommGroup N₂] [Module R N₂] [Module S N₂] [IsScalarTower S R N₂]
    {φ : M →ₗ[S] N} {ψ : M₂ →ₗ[S] N₂} (hφ : IsBaseChange R φ) (hψ : IsBaseChange R ψ)
    (cM : M →ₗ[S] M →ₗ[S] M₂) (cN : N →ₗ[R] N →ₗ[R] N₂) (hc : ∀ m m', ψ (cM m m') = cN (φ m) (φ m'))
    (eM : ⋀[S]^2 M ≃ₗ[S] M₂) (heM : ∀ a b, eM (exteriorPower.ιMulti S 2 ![a, b]) = cM a b) :
    ∃ e : ⋀[R]^2 N ≃ₗ[R] N₂, ∀ a b, e (exteriorPower.ιMulti R 2 ![a, b]) = cN a b := by
  have hE := GlobalTheory.TopForm.isBaseChange_exteriorPower hφ 2
  let e : ⋀[R]^2 N ≃ₗ[R] N₂ := hE.equiv.symm ≪≫ₗ eM.baseChange S R _ _ ≪≫ₗ hψ.equiv
  refine ⟨e, ?_⟩
  have key : ∀ m m', e (exteriorPower.ιMulti R 2 ![φ m, φ m']) = cN (φ m) (φ m') := by
    intro m m'
    have h1 : exteriorPower.ιMulti R 2 ![φ m, φ m'] =
        GlobalTheory.exteriorPowerMapOver R 2 φ (exteriorPower.ιMulti S 2 ![m, m']) := by
      rw [GlobalTheory.exteriorPowerMapOver_ιMulti]
      congr 1
      funext k
      fin_cases k <;> rfl
    have h2 : hE.equiv.symm (GlobalTheory.exteriorPowerMapOver R 2 φ (exteriorPower.ιMulti S 2 ![m, m'])) =
        1 ⊗ₜ exteriorPower.ιMulti S 2 ![m, m'] := by
      rw [LinearEquiv.symm_apply_eq, IsBaseChange.equiv_tmul, one_smul]
    rw [h1]
    change hψ.equiv (eM.baseChange S R _ _ (hE.equiv.symm _)) = _
    rw [h2, LinearEquiv.baseChange_tmul, IsBaseChange.equiv_tmul, one_smul, heM, hc]
  let iw := exteriorPower.ιMulti R 2 (M := N)
  have u0 : ∀ a b x : N, (![x, b] : Fin 2 → N) = Function.update ![a, b] 0 x := by
    intro a b x; funext k; fin_cases k <;> simp
  have u1 : ∀ a b x : N, (![a, x] : Fin 2 → N) = Function.update ![a, b] 1 x := by
    intro a b x; funext k; fin_cases k <;> simp
  have add0 : ∀ a a' b : N, iw ![a + a', b] = iw ![a, b] + iw ![a', b] := by
    intro a a' b
    have := iw.map_update_add ![a, b] 0 a a'
    rwa [← u0 a b (a + a'), ← u0 a b a, ← u0 a b a'] at this
  have add1 : ∀ a b b' : N, iw ![a, b + b'] = iw ![a, b] + iw ![a, b'] := by
    intro a b b'
    have := iw.map_update_add ![a, b] 1 b b'
    rwa [← u1 a b (b + b'), ← u1 a b b, ← u1 a b b'] at this
  have smul0 : ∀ (r : R) (a b : N), iw ![r • a, b] = r • iw ![a, b] := by
    intro r a b
    have := iw.map_update_smul ![a, b] 0 r a
    rwa [← u0 a b (r • a), ← u0 a b a] at this
  have smul1 : ∀ (r : R) (a b : N), iw ![a, r • b] = r • iw ![a, b] := by
    intro r a b
    have := iw.map_update_smul ![a, b] 1 r b
    rwa [← u1 a b (r • b), ← u1 a b b] at this
  have zero0 : ∀ b : N, iw ![0, b] = 0 := fun b => by
    simpa using smul0 0 0 b
  have zero1 : ∀ a : N, iw ![a, 0] = 0 := fun a => by
    simpa using smul1 0 a 0
  intro a b
  induction a using hφ.inductionOn with
  | zero => simp [iw, zero0]
  | add x y hx hy => simp only [iw] at add0; rw [add0, map_add, hx, hy, map_add, LinearMap.add_apply]
  | smul r x hx => simp only [iw] at smul0; rw [smul0, map_smul, hx, map_smul, LinearMap.smul_apply]
  | tmul m =>
    induction b using hφ.inductionOn with
    | zero => simp only [iw] at zero1; rw [zero1, map_zero, map_zero]
    | add x y hx hy => simp only [iw] at add1; rw [add1, map_add, hx, hy, map_add]
    | smul r x hx => simp only [iw] at smul1; rw [smul1, map_smul, hx, map_smul]
    | tmul m' => exact key m m'

theorem tensor_equiv_of_tower {S R R' M N P : Type} [CommRing S] [CommRing R] [CommRing R'] [Algebra S R]
    [Algebra R R'] [Algebra S R'] [IsScalarTower S R R'] [AddCommGroup M] [Module S M] [AddCommGroup N]
    [Module R N] [AddCommGroup P] [Module R' P]
    (φ : M →ₛₗ[algebraMap S R] N) (χ : N →ₛₗ[algebraMap R R'] P) (θ : M →ₛₗ[algebraMap S R'] P)
    (hθ : ∀ m, χ (φ m) = θ m) (e1 : R ⊗[S] M ≃ₗ[R] N) (he1 : ∀ m, e1 (1 ⊗ₜ m) = φ m)
    (e2 : R' ⊗[S] M ≃ₗ[R'] P) (he2 : ∀ m, e2 (1 ⊗ₜ m) = θ m) :
    ∃ e : R' ⊗[R] N ≃ₗ[R'] P, ∀ c, e (1 ⊗ₜ c) = χ c := by
  refine ⟨(e1.symm.baseChange R R' _ _) ≪≫ₗ AlgebraTensorModule.cancelBaseChange S R R' R' M ≪≫ₗ e2,
    fun c => ?_⟩
  obtain ⟨x, rfl⟩ := e1.surjective c
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r m =>
    have h1 : e1 (r ⊗ₜ m) = r • φ m := by
      rw [← he1, ← e1.map_smul, smul_tmul', smul_eq_mul, _root_.mul_one]
    have h2 : (algebraMap R R' r) ⊗ₜ[S] m = (algebraMap R R' r) • ((1 : R') ⊗ₜ[S] m) := by
      rw [smul_tmul', smul_eq_mul, _root_.mul_one]
    simp only [LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul, LinearEquiv.symm_apply_apply,
      AlgebraTensorModule.cancelBaseChange_tmul]
    rw [Algebra.smul_def, _root_.mul_one, h2, e2.map_smul, he2, h1, χ.map_smulₛₗ, hθ]
  | add x y hx hy => simp only [tmul_add, map_add, hx, hy]

theorem oStr_of_noetherian : OStr := by
  intro R _ A _ g hA hg
  obtain ⟨S, B, _, φ, -, hfg, hB, hBg, hpb⟩ :=
    GlobalTheory.AbelianLimit.abelianScheme_descends_to_fg_subring R g A ∅ hA hg
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing ℤ S
  obtain ⟨hFP, hW, hBC1, hBC2⟩ := GlobalTheory.T.abelianScheme_structureSheafCohomology_noetherian S B g hB hBg
  have hAB : IsPullback φ A.hom B.hom (spMap (algebraMap S R)) := hpb.1
  obtain ⟨e1, he1⟩ := hBC1 R A.left A.hom φ hAB
  obtain ⟨e2, he2⟩ := hBC2 R A.left A.hom φ hAB
  have hp1 : IsBaseChange R (semiToLin (pullHO1 hAB.w)) := IsBaseChange.of_equiv e1 he1
  have hp2 : IsBaseChange R (semiToLin (pullHO2 hAB.w)) := IsBaseChange.of_equiv e2 he2
  have hcomp := GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id
  refine ⟨fp_of_tensor_equiv e1 hFP, ?_, ?_, ?_⟩
  · obtain ⟨eM, heM⟩ := hW
    exact wedge_of_isBaseChange hp1 hp2 (cup _) (cup _)
      ((hcomp.2.1 S R B.left A.left B.hom A.hom (algebraMap S R) φ hAB.w).1) eM heM
  · intro R' _ _ X' s' ψ h
    letI : Algebra S R' := ((algebraMap R R').comp (algebraMap S R)).toAlgebra
    haveI : IsScalarTower S R R' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have es : spMap (algebraMap R R') ≫ spMap (algebraMap S R) = spMap (algebraMap S R') := by
      simp only [spMap, ← Spec.map_comp]; rfl
    have hc : IsPullback (ψ ≫ φ) s' B.hom (spMap (algebraMap S R')) := es ▸ h.paste_horiz hAB
    obtain ⟨e3, he3⟩ := hBC1 R' X' s' (ψ ≫ φ) hc
    exact tensor_equiv_of_tower (pullHO1 hAB.w) (pullHO1 h.w) (pullHO1 hc.w)
      ((hcomp.1 S R B.left A.left B.hom A.hom (algebraMap S R) φ hAB.w R' X' s' (algebraMap R R') ψ h.w
        (algebraMap S R') (ψ ≫ φ) hc.w rfl (fun _ => rfl)).1) e1 he1 e3 he3
  · intro R' _ _ X' s' ψ h
    letI : Algebra S R' := ((algebraMap R R').comp (algebraMap S R)).toAlgebra
    haveI : IsScalarTower S R R' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have es : spMap (algebraMap R R') ≫ spMap (algebraMap S R) = spMap (algebraMap S R') := by
      simp only [spMap, ← Spec.map_comp]; rfl
    have hc : IsPullback (ψ ≫ φ) s' B.hom (spMap (algebraMap S R')) := es ▸ h.paste_horiz hAB
    obtain ⟨e3, he3⟩ := hBC2 R' X' s' (ψ ≫ φ) hc
    exact tensor_equiv_of_tower (pullHO2 hAB.w) (pullHO2 h.w) (pullHO2 hc.w)
      ((hcomp.1 S R B.left A.left B.hom A.hom (algebraMap S R) φ hAB.w R' X' s' (algebraMap R R') ψ h.w
        (algebraMap S R') (ψ ≫ φ) hc.w rfl (fun _ => rfl)).2.1) e2 he2 e3 he3

end GlobalTheory.AbCoh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyDegreePolynomialMapEqCharpolyRatioStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianVariety_degreePolynomial_map_eq_charpoly_rationalTate : ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ (A : AbVar K) [Module.Finite ℚ_[l] (Vl l A)] (f : End A) (P : Polynomial ℚ), P.Monic → P.natDegree = 2 * A.dim → (∀ n : ℤ, P.eval (n : ℚ) = (deg (A := A) (B := A) ((n : End A) - f) : ℚ)) → P.map (algebraMap ℚ ℚ_[l]) = (vmap l (A := A) (B := A) f).charpoly := by
  first | (exact @GlobalTheory.AV.AbVar.map_eq_charpoly_vmap) | (exact GlobalTheory.AV.AbVar.map_eq_charpoly_vmap) | (intros; apply GlobalTheory.AV.AbVar.map_eq_charpoly_vmap  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointAppellHumbertFormOfMumfordBundleLbIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

namespace GlobalTheory.AdjFwd

theorem adjoint_hermForm_of_lbIso : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (N : LB A.left), N.IsLB → Out.RelAmple A N → ∀ (M : LB A.left) (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), M.IsLB → GlobalTheory.TorusRM.IsFactorAH u Hm χ → ∀ (f f' : A ⟶ A) (F F' : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), IsMonHom f → IsMonHom f' → (∀ z, u.ex (F z) = u.ex z ≫ f) → (∀ z, u.ex (F' z) = u.ex z ≫ f') → LBIso (cubeLB A ![fst A A ≫ f, snd A A] M) (cubeLB A ![fst A A, snd A A ≫ f'] M) → ∀ z w, hermForm Hm (F z) w = hermForm Hm z (F' w) := by
  intro A _ _ g hA _ N _ _ M u Hm χ hM hF f f' F F' hf hf' e e' hiso
  haveI := hf
  haveI := hf'
  obtain ⟨Mr, hMr, ⟨c⟩⟩ := GlobalTheory.AHWeilAny.exists_cubical A hA M hM
  subst hMr
  have hR := GlobalTheory.AdjPolLocal.rosatiAdj_of_lbIso _ A Mr.L f f' hM hiso
  have hFl : ∀ a : u.Λ, F a ∈ u.Λ := fun a => by rw [← u.ker, e, (u.ker _).2 a.2, MonObj.one_comp]
  have hF'l : ∀ a : u.Λ, F' a ∈ u.Λ := fun a => by rw [← u.ker, e', (u.ker _).2 a.2, MonObj.one_comp]
  refine GlobalTheory.HermAdjoint.adjoint_of_im Hm F F' _ u.full fun a ha b hb => ?_
  obtain ⟨E₁, hE₁⟩ := GlobalTheory.AHWeilFactor.im_hermForm_int hM u hF ⟨_, hFl ⟨a, ha⟩⟩ ⟨b, hb⟩
  obtain ⟨E₂, hE₂⟩ := GlobalTheory.AHWeilFactor.im_hermForm_int hM u hF ⟨a, ha⟩ ⟨_, hF'l ⟨b, hb⟩⟩
  have hE : E₁ = E₂ := GlobalTheory.HermAdjoint.int_eq_of_exp fun n hn => by
    have hx := GlobalTheory.HermAdjoint.ex_period_pow u hn ⟨a, ha⟩
    have hy := GlobalTheory.HermAdjoint.ex_period_pow u hn ⟨b, hb⟩
    have hy' : (u.ex ((n : ℂ)⁻¹ • b) ≫ f') ^ n = 1 := by
      rw [← MonObj.pow_comp]
      exact (congrArg (· ≫ f') hy).trans (MonObj.one_comp _)
    let c₁ : ℂˣ := Units.mk0 _ (Complex.exp_ne_zero (-(2 * Real.pi * Complex.I) * (E₁ : ℂ) / n))
    let c₂ : ℂˣ := Units.mk0 _ (Complex.exp_ne_zero (-(2 * Real.pi * Complex.I) * (E₂ : ℂ) / n))
    have v₁ : Out.WeilIs A Mr.L n (u.ex ((n : ℂ)⁻¹ • a) ≫ f) (u.ex ((n : ℂ)⁻¹ • b)) (unitOn c₁) := by
      rw [← e, map_smul]
      refine GlobalTheory.AHWeilFactor.weilIs_exp_riemannForm A hA Mr.L hM g u Hm χ hF n (F a) b c₁ hn
        (hFl ⟨a, ha⟩) hb ?_
      show Complex.exp _ = _
      rw [← hE₁, Complex.ofReal_intCast]
    have v₂ : Out.WeilIs A Mr.L n (u.ex ((n : ℂ)⁻¹ • a)) (u.ex ((n : ℂ)⁻¹ • b) ≫ f') (unitOn c₂) := by
      rw [← e', map_smul]
      refine GlobalTheory.AHWeilFactor.weilIs_exp_riemannForm A hA Mr.L hM g u Hm χ hF n a (F' b) c₂ hn
        ha (hF'l ⟨b, hb⟩) ?_
      show Complex.exp _ = _
      rw [← hE₂, Complex.ofReal_intCast]
    have v₁' := (GlobalTheory.WeilCube.weilIs_rosati c GlobalTheory.globalFns_holds hA f f' hR hx hy _).1 v₁
    obtain ⟨e₀, he₀⟩ := GlobalTheory.WeilCube.exists_isRatio c n _ _ hx hy'
    have h₁ := (GlobalTheory.WeilCube.weilIs_iff c GlobalTheory.globalFns_holds hA hx hy' he₀ _).1 v₁'
    have h₂ := (GlobalTheory.WeilCube.weilIs_iff c GlobalTheory.globalFns_holds hA hx hy' he₀ _).1 v₂
    exact congrArg Units.val (GlobalTheory.HermAdjoint.unitOn_injective (h₁.trans h₂.symm))
  show (F a ⬝ᵥ Hm *ᵥ star b).im = (a ⬝ᵥ Hm *ᵥ star (F' b)).im
  rw [← hE₁, ← hE₂, hE]

end GlobalTheory.AdjFwd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraisationProperFormalSchemeAmpleBundleStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraisation_properFormalScheme_ampleBundle : GlobalTheory.Published.FormalAlgebraisation.Schemes := by
  first | exact @GlobalTheory.FormalAlg.formalAlgebraisation_schemes | exact GlobalTheory.FormalAlg.formalAlgebraisation_schemes | (intros; apply GlobalTheory.FormalAlg.formalAlgebraisation_schemes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernNumbersEqIntegralChernFormsSmoothMetricStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernNumbers_eq_integral_chernForms_smoothMetric : GlobalTheory.Published.ChernWeilNumbers := by
  first | exact @GlobalTheory.ChernDegree.chernWeilNumbers_holds | exact GlobalTheory.ChernDegree.chernWeilNumbers_holds | (intros; apply GlobalTheory.ChernDegree.chernWeilNumbers_holds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCechDeRhamComparisonBijectiveComplexAStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bijective_cmp1_of_isAbelianScheme_over_complex : ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → Function.Bijective (cmp1 (str A)) := by
  first | exact @GlobalTheory.CechPer.crystallineCechDeRhamComparison_bijective_complexAbelian | exact GlobalTheory.CechPer.crystallineCechDeRhamComparison_bijective_complexAbelian | (intros; apply GlobalTheory.CechPer.crystallineCechDeRhamComparison_bijective_complexAbelian <;> assumption)
end

