import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2865
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatSurjectiveKernel
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2432
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2779
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2821
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2829
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2259
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2316
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2652
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2639
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2838
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2801
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2822
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasThetaConstantsTwoLevelsMoveCartesian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1604
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2813
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0592
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1323
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2844

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermPullbackRestrictEq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem germPullback_restrict_eq {X Z : Scheme.{0}} (f : Z ⟶ X) (z : Z) {U V : X.Opens} (hle : V ≤ U) (h : f z ∈ V)
    (a : Γ(X, U)) : gs f z V (resG X hle a) = gs f z U a := gs_res f z hle h a

open GlobalTheory.ProjSpace in

theorem secRatio_isTermOf_zero : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (Y : Ext D) (k : ℕ) (b₀ b : D.SecB k 0) (τ₀ τ : SecK D.P.L Y.q.left k), IsTermOf Y b₀ τ₀ → IsTermOf Y b τ → ∀ (W : Y.H.left.Opens) (h₁ : W ≤ Y.q.left ⁻¹ᵁ nonzeroLocus b₀) (h₂ : W ≤ nonzeroLocus τ₀), (Y.q.left.appLE (nonzeroLocus b₀) W h₁).hom (GlobalTheory.ProjSpace.secRatio b₀ b) = resG Y.H.left h₂ (GlobalTheory.ProjSpace.secRatio τ₀ τ) := by
  intro R _ _ D Y k b₀ b τ₀ τ h₀ h W h₁ h₂
  apply fn_ext
  intro y hy
  rw [gs_appLE Y.q.left (nonzeroLocus b₀) W h₁ (𝟙 _) y hy, Category.id_comp,
    germPullback_restrict_eq (𝟙 Y.H.left) y h₂ hy]
  choose J hJ using fun ψ : Y.H.left ⟶ D.P.A.left => ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart D.P.isLB (ψ y)
  have hG : Good D.P.L y J := hJ
  have e := h Y.H (𝟙 _) y J hG
  have e₀ := h₀ Y.H (𝟙 _) y J hG
  rw [Category.id_comp] at e e₀

  have hqy : Y.q.left y ∈ nonzeroLocus b₀ ⊓ LB.wchart D.P.L (D.famφB 0) (fun κ => J (Y.q.left ≫ D.famφB 0 κ)) :=
    ⟨h₁ hy, hG.mem (D.famφB 0) Y.q.left⟩
  have sb := congrArg (gs Y.q.left y _) (secRatio_on b₀ b (fun κ => J (Y.q.left ≫ D.famφB 0 κ))
    (W := nonzeroLocus b₀ ⊓ LB.wchart D.P.L (D.famφB 0) (fun κ => J (Y.q.left ≫ D.famφB 0 κ))) inf_le_left inf_le_right)
  rw [gs_mul _ y _ hqy] at sb
  erw [germPullback_restrict_eq _ y _ hqy, germPullback_restrict_eq _ y _ hqy, germPullback_restrict_eq _ y _ hqy] at sb

  have hyτ : (𝟙 Y.H.left) y ∈ nonzeroLocus τ₀ ⊓ LB.wchart D.P.L (fun _ : Fin 1 => Y.q.left) (fun _ : Fin 1 => J (𝟙 Y.H.left ≫ Y.q.left)) :=
    ⟨h₂ hy, hG.mem (fun _ : Fin 1 => Y.q.left) (𝟙 Y.H.left)⟩
  have sτ := congrArg (gs (𝟙 Y.H.left) y _) (secRatio_on τ₀ τ (fun _ : Fin 1 => J (𝟙 Y.H.left ≫ Y.q.left))
    (W := nonzeroLocus τ₀ ⊓ LB.wchart D.P.L (fun _ : Fin 1 => Y.q.left) (fun _ : Fin 1 => J (𝟙 Y.H.left ≫ Y.q.left))) inf_le_left inf_le_right)
  rw [gs_mul _ y _ hyτ] at sτ
  erw [germPullback_restrict_eq _ y _ hyτ, germPullback_restrict_eq _ y _ hyτ, germPullback_restrict_eq _ y _ hyτ] at sτ
  have hu : IsUnit (sval τ₀ (𝟙 Y.H.left) y J) :=
    (GlobalTheory.AmpleSpan.mem_nonzeroLocus_iff_gs τ₀ (𝟙 Y.H.left) y hyτ.2).1 hyτ.1
  change sval τ (𝟙 Y.H.left) y J = _ * sval τ₀ (𝟙 Y.H.left) y J at sτ
  change sval b Y.q.left y J = _ * sval b₀ Y.q.left y J at sb
  change sval τ (𝟙 Y.H.left) y J = _ at e
  change sval τ₀ (𝟙 Y.H.left) y J = _ at e₀
  refine hu.mul_right_cancel ?_
  rw [← sτ, e, sb, e₀]
  exact (_root_.mul_assoc _ _ _).symm
end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalOneFormsPrimitiveAbelianScheme
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

theorem GlobalTheory.AbCoh.primF_of_isAbelianScheme : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → GlobalTheory.AbCoh.PrimF A :=
  fun R _ A _ g hA hg ↦ GlobalTheory.AbCoh.PrimForm.prim_of_axes A (GlobalTheory.T.abelianSquare_globalOneForm_eq_zero_of_axes R A g hA hg)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueProjectiveSpaceMapsOfAgreeGeometricPointsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glue_projectiveSpace_maps_of_agree_geometric_points : ∀ (o : Type) [CommRing o] (n : ℕ) (X : Scheme.{0}) [IsReduced X] (s : X ⟶ Sp o) (I : Type) (W : I → X.Opens) (f : ∀ i, (W i).toScheme ⟶ PSpace o n), (⨆ i, W i) = ⊤ → (∀ i, f i ≫ PSpace.str o n = (W i).ι ≫ s) → (∀ i j (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ (W i).toScheme) (y' : Sp K ⟶ (W j).toScheme), y ≫ (W i).ι = y' ≫ (W j).ι → y ≫ f i = y' ≫ f j) → ∃ g : X ⟶ PSpace o n, g ≫ PSpace.str o n = s ∧ ∀ i, (W i).ι ≫ g = f i := by
  first | exact @GlobalTheory.ThetaGlue.glue_geom | exact GlobalTheory.ThetaGlue.glue_geom | (intros; apply GlobalTheory.ThetaGlue.glue_geom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GluedSectionGenericValueNonvanishing
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin.ThBdl.Glued

theorem valF_resG {F : Type} [Field F] {X : Scheme.{0}} (y : Sp F ⟶ X) {U W : X.Opens} (h : W ≤ U) (f : Γ(X, U))
    (hy : ⊤ ≤ y ⁻¹ᵁ W) : valF y W (resG X h f) = valF y U f := by
  have hU : ⊤ ≤ y ⁻¹ᵁ U := fun a ha => h (hy ha)
  unfold valF
  rw [dif_pos hy, dif_pos hU]
  congr 1
  show (X.presheaf.map (homOfLE h).op ≫ y.appLE W ⊤ hy).hom f = _
  rw [Scheme.Hom.map_appLE]

theorem glued : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (K : Type) [Field K] (ξ : Sp K ⟶ S)
    (V : S.Opens) (κ : Type) (N : κ → S.Opens) (s : ∀ k, LocSec G L (N k)) (s' : LocSec G L V)
    (v : SecM G L 1 (Over.mk ξ)) (hN : ∀ k, N k ≤ V), (⨆ k, N k) = V →
    (∀ k i, resG _ (fun _ hx => ⟨hx.1, hN k hx.2⟩ : L.U i ⊓ G.hom ⁻¹ᵁ N k ≤ L.U i ⊓ G.hom ⁻¹ᵁ V) (s' i) = s k i) →
    (∀ k, GenIs ξ (s k) v) → (∀ k, FibNz (s k) (N k)) → (Nonempty κ → GenIs ξ s' v) ∧ FibNz s' V := by
  intro S G _ L K _ ξ V κ N s s' v hN hsup hres hgen hnz
  refine ⟨fun ⟨k⟩ => ?_, ?_⟩
  · obtain ⟨hξk, hk⟩ := hgen k
    refine ⟨hξk.trans (hN k), ?_⟩
    rw [← hk]
    funext j
    unfold genPull
    rw [← hres k (j 0)]
    show _ = (G.left.presheaf.map _ ≫ (snd (Over.mk ξ) G).left.appLE _ _ _).hom (s' (j 0))
    rw [Scheme.Hom.map_appLE]
  · intro K' _ _ x hx
    obtain ⟨p⟩ : Nonempty (Sp K') := inferInstance
    have hp : x p ∈ (⨆ k, N k : S.Opens) := hsup ▸ hx ⟨p, rfl⟩
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hp
    have hxk : Set.range x ⊆ N k := by
      rintro _ ⟨q, rfl⟩
      rw [Subsingleton.elim q p]
      exact hk
    obtain ⟨y, i, hyx, hyr, hval⟩ := hnz k K' x hxk
    refine ⟨y, i, hyx, fun z hz => ⟨(hyr hz).1, hN k (hyr hz).2⟩, ?_⟩
    rw [← hres k i] at hval
    convert hval using 1
    exact (valF_resG y _ (s' i) ((GlobalTheory.ZH.top_le_preimage_iff _ _).2 hyr)).symm

end GlobalTheory.UMin.ThBdl.Glued
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GluingOfConnectedness
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FlatModel

theorem glueSt_of (hC : ConnSt) (hZ : GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.PropZ) : GlueSt := by
  intro F _ _ V p _ hp X s Xw hN hP hF hXw hG n K hK hCh
  obtain ⟨X₁, s₁, Xw₁, K₁, hI₁, hN₁, hP₁, hF₁, hXw₁, hG₁, hK₁, hCh₁, hT₁⟩ :=
    GlobalTheory.T.restriction_statement_holds F V p hp X s Xw hN hP hF hXw hG n K hK hCh
  obtain ⟨X₂, s₂, Xw₂, K₂, hI₂, hN₂, hP₂, hF₂, hXw₂, hG₂, hK₂, hCh₂, hT₂⟩ :=
    GlobalTheory.T.modularity_of_density GlobalTheory.T.density_statement_holds F V p hp X₁ s₁ Xw₁ hI₁ hN₁ hP₁ hF₁ hXw₁ hG₁ n K₁ hK₁ hCh₁
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.principal_of_connected_density hC hZ GlobalTheory.T.density_statement_holds F V p hp X₂ s₂ Xw₂ hI₂ hN₂ hP₂ hF₂ hXw₂ hG₂ K₂ hK₂ hCh₂
  refine ⟨ρ, fun yb hyb κ hκ => ?_⟩
  obtain ⟨yb₁, h1, hs1⟩ := hT₁ yb hyb
  obtain ⟨yb₂, h2, hs2⟩ := hT₂ yb₁ h1
  exact hρ yb₂ h2 κ (hs2 (hs1 hκ))

end GlobalTheory.FlatModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HRedFst
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.IntEval

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {G : Over (Sp R)}

variable (I) in

def hRed (h : 𝟙_ (Over (Sp R)) ⟶ G) (e : ℕ) : Sp (R ⧸ I ^ (e + 1)) ⟶ (thickObj R I e G).left :=
  pullback.lift (thick R I e ≫ h.left) (𝟙 _) (by
    rw [Category.assoc, Over.w h, Category.id_comp]
    exact Category.comp_id _)

theorem hRed_fst (h : 𝟙_ (Over (Sp R)) ⟶ G) (e : ℕ) : hRed I h e ≫ fGl I G e = thick R I e ≫ h.left :=
  pullback.lift_fst _ _ _

variable {D : DegData R I} {A : PolAV (Sp (FractionRing R))} [GrpObj G] [IsCommMonObj G]

def TRel (U : UnifPre I D A G) (h : 𝟙_ (Over (Sp R)) ⟶ G) (b : 𝟙_ (Over (Sp R)) ⟶ D.toPre.P.A)
    (f : LB.Gen (LB.LinComb U.LG.L (K := Fin 1) (fun _ => h.left) (fun _ => 1)))
    (t : LB.Gen (LB.LinComb D.toPre.P.L ![(η[D.toPre.P.A]).left, b.left] (DegPre.lineε 1))) (e : ℕ) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp (R ⧸ I ^ (e + 1))) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι)
    (JG : (Z ⟶ G.left) → U.LG.L.ι), Good D.toPre.P.L z J → Good U.LG.L z JG →
    val t (r ≫ thick R I e) z J *
        wv U e (r ≫ hRed I h e) z (J (r ≫ hRed I h e ≫ pGl U e)) (JG (r ≫ hRed I h e ≫ fGl I G e)) *
        val f (r ≫ thick R I e) z JG =
      val (L := D.toPre.P.L) D.toPre.rig (r ≫ thick R I e) z J

end GlobalTheory.Poinc.IntEval
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDivOfHasDivThetaSymmetricFunctionsDegreeFactoStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDiv_of_hasDiv_thetaSymmetricFunctionsDegreeFactorial : ∀ (k Ω : Type) [CommRing k] [Field Ω] [Algebra k Ω] (M : RatModel k Ω) (N : ℕ) (c : Fin N → Ω), Geo.Tor.IsNormalScheme M.Z → M.HasDiv (symTup c) → M.HasDiv c := by
  first | exact @GlobalTheory.UMin.hasDiv_of_hasDiv_symTup | exact GlobalTheory.UMin.hasDiv_of_hasDiv_symTup | (intros; apply GlobalTheory.UMin.hasDiv_of_hasDiv_symTup <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasProperSmoothDualRepOfFiniteProductAlgebrasStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasProperSmoothDualRep_of_finite_product_algebras : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → ∀ (n : ℕ) (D : Fin n → Type) [∀ i, CommRing (D i)] [∀ i, Algebra R (D i)], (∀ i, HasRepAF A g (Over.mk (spMap (algebraMap R (D i))))) → HasRepAF A g (Over.mk (spMap (algebraMap R (∀ i, D i)))) := by
  first | exact @GlobalTheory.DualCon.ProdGlue.hasRepAF_pi | exact GlobalTheory.DualCon.ProdGlue.hasRepAF_pi | (intros; apply GlobalTheory.DualCon.ProdGlue.hasRepAF_pi <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasThetaConstantsTwoLevelsMoveCartesianStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasThetaConstantsTwoLevels_move_cartesian : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (S' : Scheme.{0}) (A : Over S') [GrpObj A] [IsCommMonObj A] (L' : LB A.left) (ρ' : LB.Gen (L'.pull (eSec A))) (f : S' ⟶ S) (φ : A.left ⟶ G.left), L'.IsLB → ρ'.IsGen → IsGrpPullback A G f φ → LBIso L' (L.pull φ) → ∀ (m m' N N' : ℕ) (K : Type) [Field K] (x : Sp K ⟶ S') (c : Fin N → K) (c' : Fin N' → K), HasTh₂ A L' ρ' m m' x c c' ↔ HasTh₂ G L ρ m m' (x ≫ f) c c' := by
  first | exact @GlobalTheory.UMin.ThMove.hasTh₂_move | exact GlobalTheory.UMin.ThMove.hasTh₂_move | (intros; apply GlobalTheory.UMin.ThMove.hasTh₂_move <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeadLastMeasMeasurePreserving
section
open Set MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.CxForm GlobalTheory.LocFub

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LocFub

def headLastIsom (n : ℕ) : V (n + 1) →ₗᵢ[ℂ] WithLp 2 (V n × ℂ) where
  toLinearMap := (WithLp.linearEquiv 2 ℂ (V n × ℂ)).symm.toLinearMap ∘ₗ
    LinearMap.prod (headL n).toLinearMap ((EuclideanSpace.proj (Fin.last n) : V (n + 1) →L[ℂ] ℂ).toLinearMap)
  norm_map' v := by
    have h : ‖(WithLp.toLp 2 (headL n v, v (Fin.last n)) : WithLp 2 (V n × ℂ))‖ ^ 2 = ‖v‖ ^ 2 := by
      rw [WithLp.prod_norm_sq_eq_of_L2, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
        Fin.sum_univ_castSucc]
      simp [headL_apply]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

theorem headLastIsom_apply (n : ℕ) (v : V (n + 1)) :
    headLastIsom n v = WithLp.toLp 2 (headL n v, v (Fin.last n)) := rfl

theorem headLastIsom_surjective (n : ℕ) : Function.Surjective (headLastIsom n) := by
  intro p
  obtain ⟨q, rfl⟩ : ∃ q, p = WithLp.toLp 2 q := ⟨WithLp.ofLp p, (WithLp.toLp_ofLp (p := 2) p).symm⟩
  refine ⟨WithLp.toLp 2 (Fin.snoc (α := fun _ => ℂ) (WithLp.ofLp q.1) q.2), ?_⟩
  rw [headLastIsom_apply]
  congr 1
  ext
  · simp [headL_apply]
  · simp

def headLastMeas (n : ℕ) : V (n + 1) ≃ᵐ V n × ℂ :=
  ((LinearIsometryEquiv.ofSurjective (headLastIsom n) (headLastIsom_surjective n)).toHomeomorph.toMeasurableEquiv).trans
    (MeasurableEquiv.toLp 2 (V n × ℂ)).symm

theorem headLastMeas_apply (n : ℕ) (v : V (n + 1)) : headLastMeas n v = (headL n v, v (Fin.last n)) := rfl

theorem headLastMeas_measurePreserving (n : ℕ) : MeasurePreserving (headLastMeas n) := by
  let e := LinearIsometryEquiv.ofSurjective (headLastIsom n) (headLastIsom_surjective n)
  let eR : V (n + 1) ≃ₗᵢ[ℝ] WithLp 2 (V n × ℂ) :=
    { toLinearEquiv := e.toLinearEquiv.restrictScalars ℝ, norm_map' := e.norm_map }
  have h1 : MeasurePreserving eR := LinearIsometryEquiv.measurePreserving eR
  exact (WithLp.volume_preserving_ofLp (V n) ℂ).comp h1

theorem integral_headL_last {n : ℕ} (F : V n → ℂ → ℝ)
    (hF : Integrable (fun v : V (n + 1) => F (headL n v) (v (Fin.last n)))) :
    Integrable (fun w => ∫ x, F w x) ∧ ∫ v, F (headL n v) (v (Fin.last n)) = ∫ w, ∫ x, F w x := by
  have hmp := headLastMeas_measurePreserving n
  have hc : (fun v : V (n + 1) => F (headL n v) (v (Fin.last n))) = Function.uncurry F ∘ headLastMeas n := rfl
  have hI : Integrable (Function.uncurry F) ((volume : Measure (V n)).prod (volume : Measure ℂ)) := by
    rw [hc] at hF
    exact (hmp.integrable_comp_emb (headLastMeas n).measurableEmbedding).1 hF
  refine ⟨hI.integral_prod_left, ?_⟩
  calc ∫ v, F (headL n v) (v (Fin.last n)) = ∫ v, Function.uncurry F (headLastMeas n v) := rfl
    _ = ∫ z, Function.uncurry F z ∂((volume : Measure (V n)).prod (volume : Measure ℂ)) :=
        hmp.integral_comp' (Function.uncurry F)
    _ = ∫ w, ∫ x, F w x := integral_prod _ hI

end GlobalTheory.LocFub
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeLFunctionEulerProductConvergent
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory.CMTorsion
open GlobalTheory.WeierstrassCurve (scheme toSpec mapHom)

theorem GlobalTheory.GrpPullback.points_conj : ∀ (G G' : Over (Sp ℂ)) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (g : ℂ ≃+* ℂ) (p : G'.left ⟶ G.left), IsGrpPullback G' G (spMap (g : ℂ →+* ℂ)) p → (∀ P Q : 𝟙_ (Over (Sp ℂ)) ⟶ G', P.left ≫ p = Q.left ≫ p → P = Q) ∧ (∀ (P Q : 𝟙_ (Over (Sp ℂ)) ⟶ G) (P' Q' : 𝟙_ (Over (Sp ℂ)) ⟶ G'), P'.left ≫ p = spMap (g : ℂ →+* ℂ) ≫ P.left → Q'.left ≫ p = spMap (g : ℂ →+* ℂ) ≫ Q.left → (P' * Q').left ≫ p = spMap (g : ℂ →+* ℂ) ≫ (P * Q).left) ∧ ∀ (J : Type) (s : Finset J) (P : J → (𝟙_ (Over (Sp ℂ)) ⟶ G)) (P' : J → (𝟙_ (Over (Sp ℂ)) ⟶ G')), (∀ i ∈ s, (P' i).left ≫ p = spMap (g : ℂ →+* ℂ) ≫ (P i).left) → (∏ i ∈ s, P' i : 𝟙_ (Over (Sp ℂ)) ⟶ G').left ≫ p = spMap (g : ℂ →+* ℂ) ≫ (∏ i ∈ s, P i : 𝟙_ (Over (Sp ℂ)) ⟶ G).left := by
  intro G G' _ _ _ _ g p h
  obtain ⟨hpb, hmul⟩ := h
  have h1 : ∀ P Q : 𝟙_ (Over (Sp ℂ)) ⟶ G', P.left ≫ p = Q.left ≫ p → P = Q := by
    intro P Q hPQ
    have hw : P.left ≫ G'.hom = Q.left ≫ G'.hom := by rw [Over.w P, Over.w Q]
    exact Over.OverMorphism.ext (hpb.hom_ext hPQ hw)
  have h2 : ∀ (P Q : 𝟙_ (Over (Sp ℂ)) ⟶ G) (P' Q' : 𝟙_ (Over (Sp ℂ)) ⟶ G'),
      P'.left ≫ p = spMap (g : ℂ →+* ℂ) ≫ P.left → Q'.left ≫ p = spMap (g : ℂ →+* ℂ) ≫ Q.left →
      (P' * Q').left ≫ p = spMap (g : ℂ →+* ℂ) ≫ (P * Q).left := by
    intro P Q P' Q' hP hQ
    let u : Over.mk ((𝟙_ (Over (Sp ℂ))).hom ≫ spMap (g : ℂ →+* ℂ)) ⟶ 𝟙_ (Over (Sp ℂ)) := toUnit _
    have hu : u.left = spMap (g : ℂ →+* ℂ) := by
      have := Over.w u
      simpa using this
    have key := hmul (𝟙_ (Over (Sp ℂ))) P' Q' (u ≫ P) (u ≫ Q) (by simp [hu, hP]) (by simp [hu, hQ])
    rw [← key, ← MonObj.comp_mul]
    simp [hu]
  have h0 : (1 : 𝟙_ (Over (Sp ℂ)) ⟶ G').left ≫ p = spMap (g : ℂ →+* ℂ) ≫ (1 : 𝟙_ (Over (Sp ℂ)) ⟶ G).left := by
    have hw : (spMap (g : ℂ →+* ℂ) ≫ (1 : 𝟙_ (Over (Sp ℂ)) ⟶ G).left) ≫ G.hom = 𝟙 _ ≫ spMap (g : ℂ →+* ℂ) := by
      rw [Category.assoc, Over.w]; simp
    let e' : Sp ℂ ⟶ G'.left := hpb.lift _ _ hw
    have he' : e' ≫ G'.hom = (𝟙_ (Over (Sp ℂ))).hom := by
      simp only [e', IsPullback.lift_snd]; rfl
    let E' : 𝟙_ (Over (Sp ℂ)) ⟶ G' := Over.homMk e' he'
    have hE : E'.left ≫ p = spMap (g : ℂ →+* ℂ) ≫ (1 : 𝟙_ (Over (Sp ℂ)) ⟶ G).left := by
      simp [E', e']
    have hEE : E' * E' = E' := by
      apply h1
      rw [h2 1 1 E' E' hE hE, hE, _root_.mul_one (1 : 𝟙_ (Over (Sp ℂ)) ⟶ G)]
    have : E' = 1 := mul_eq_left.mp hEE
    rw [← this, hE]
  refine ⟨h1, h2, ?_⟩
  intro J s P P' hs
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h0
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact h2 _ _ _ _ (hs a (Finset.mem_insert_self a s)) (ih fun i hi => hs i (Finset.mem_insert_of_mem hi))
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairSectionBallFinite
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem fg_addSubgroup_field_finite_or_basis {K : Type} [Field K] (H : AddSubgroup K) (hH : H.FG) :
    (H : Set K).Finite ∨ ∃ (r : ℕ) (f : Fin r → K), (∀ j, f j ∈ H) ∧ LinearIndependent ℤ f ∧
      ∀ x ∈ H, ∃ c : Fin r → ℤ, x = ∑ j, c j • f j := by
  have hfin : Module.Finite ℤ H :=
    Module.Finite.iff_addGroup_fg.2 ((AddGroup.fg_iff_addSubgroup_fg H).2 hH)
  rcases CharP.char_is_prime_or_zero K (ringChar K) with hq | h0
  · left
    have htor : Module.IsTorsion ℤ H := by
      intro x
      refine ⟨⟨(ringChar K : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hq.ne_zero)⟩, ?_⟩
      ext
      simp [ringChar.Nat.cast_ringChar]
    have : Finite H := Module.finite_of_fg_torsion H htor
    exact Set.toFinite _
  · right
    haveI : CharP K 0 := h0 ▸ ringChar.charP K
    haveI : CharZero K := CharP.charP_to_charZero K
    haveI : NoZeroSMulDivisors ℤ H := inferInstance
    haveI : Module.Free ℤ H := Module.free_of_finite_type_torsion_free'
    let bs := Module.finBasis ℤ H
    refine ⟨_, fun j => (bs j : K), fun j => (bs j).2, ?_, ?_⟩
    · exact bs.linearIndependent.map' H.subtype.toIntLinearMap
        (LinearMap.ker_eq_bot.2 Subtype.val_injective)
    · intro x hx
      refine ⟨bs.repr ⟨x, hx⟩, ?_⟩
      have h := congrArg Subtype.val (bs.sum_repr ⟨x, hx⟩)
      calc x = ((⟨x, hx⟩ : H) : K) := rfl
        _ = ((∑ i, bs.repr ⟨x, hx⟩ i • bs i : H) : K) := h.symm
        _ = ∑ j, bs.repr ⟨x, hx⟩ j • (bs j : K) := by
          simp only [AddSubgroup.val_finset_sum, AddSubgroup.coe_zsmul]

theorem bl_finite : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (P : Pair p) (a b : ℤ) (R : ℝ), (P.Bl a b R).Finite := by
  intro k _ X _ p D hX P a b R
  rcases fg_addSubgroup_field_finite_or_basis (P.H a b) (GlobalTheory.T.pairSections_fg_of_projArithVariety k X p D hX P a b) with
    hfin | ⟨r, f, hf, hli, hspan⟩
  · exact hfin.subset (fun x hx => hx.1)
  · obtain ⟨C, -, hC⟩ := GlobalTheory.T.exists_coeff_bound_of_linearIndependent_sections k X p D hX P a b r f hf hli
    have hS : {c : Fin r → ℤ | ∀ j, |(c j : ℝ)| ≤ C * R}.Finite := by
      refine (Set.Finite.pi (t := fun _ : Fin r => Set.Icc (-⌈C * R⌉) ⌈C * R⌉)
        (fun _ => Set.finite_Icc _ _)).subset ?_
      intro c hc j _
      have h := abs_le.1 (hc j)
      have hc1 := Int.le_ceil (C * R)
      have h1 : (c j : ℝ) ≤ (⌈C * R⌉ : ℝ) := h.2.trans hc1
      have h2 : -((⌈C * R⌉ : ℤ) : ℝ) ≤ c j := by linarith
      exact ⟨by exact_mod_cast h2, by exact_mod_cast h1⟩
    refine (hS.image (fun c => ∑ j, c j • f j)).subset ?_
    intro x hx
    obtain ⟨c, rfl⟩ := hspan x hx.1
    exact ⟨c, fun j => hC c R hx j, rfl⟩

end GlobalTheory.HSNef
end

