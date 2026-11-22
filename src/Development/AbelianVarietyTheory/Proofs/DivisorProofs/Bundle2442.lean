import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2360
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2284
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2361
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2250
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0653
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemBasesNonempty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2362
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0062
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2347
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2348
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2290
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1607
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0485
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0369
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLawPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2306

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetrySecondDifferenceEqCubicalRatio
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDeg.SymCube

open GlobalTheory.UU

theorem sym_cube (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (T : Over (Spec (CommRingCat.of R)))
    (x y : T ⟶ D.P.A) (z : T.left) (J : (T.left ⟶ D.P.A.left) → D.P.L.ι) (hJ : Good D.P.L z J) :
    val D.sym (x * y).left z J * cubV D.cub z J y y⁻¹ x⁻¹ =
      val D.sym x.left z J * val D.sym y.left z J * cubV D.cub z J x x⁻¹ y := by
  let G := D.P.A
  let a := x3 G 0
  let b := x3 G 1
  let sy := fun p : G3 G ⟶ G => LB.pullGen D.P.L _ _ D.sym p.left
  let cu := fun p q r : G3 G ⟶ G => LB.pullGen D.P.L (thφ G (x3 G)) thε D.cub.t (lift p (lift q r)).left
  have gs : ∀ p, (sy p).IsGen := fun p => DVR.pullGen_isGen _ _ _ _ D.sym_gen _
  have gc : ∀ p q r, (cu p q r).IsGen := fun p q r => DVR.pullGen_isGen _ _ _ _ D.cub.isGen _
  have vs : ∀ {T' : Over (Spec (CommRingCat.of R))} (σ : T' ⟶ G3 G) {z : T'.left} {J}, Good D.P.L z J → ∀ p,
      val (sy p) σ.left z J = val D.sym (σ ≫ p).left z J := fun σ z J hJ p => val_pull hJ _ _ _
  let t₁ := LB.mulGen D.P.L _ _ _ _ (sy (a * b)) (cu b b⁻¹ a⁻¹)
  let t₂ := LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (sy a) (sy b)) (cu a a⁻¹ b)
  have ev : ∀ {T' : Over (Spec (CommRingCat.of R))} (σ : T' ⟶ G3 G) {z : T'.left} {J}, Good D.P.L z J →
      val t₁ σ.left z J = val D.sym ((σ ≫ a) * (σ ≫ b)).left z J * cubV D.cub z J (σ ≫ b) (σ ≫ b)⁻¹ (σ ≫ a)⁻¹ ∧
      val t₂ σ.left z J = val D.sym (σ ≫ a).left z J * val D.sym (σ ≫ b).left z J *
        cubV D.cub z J (σ ≫ a) (σ ≫ a)⁻¹ (σ ≫ b) := fun σ z J hJ => by
    constructor
    · rw [← MonObj.comp_mul, ← GrpObj.comp_inv, ← GrpObj.comp_inv]
      exact (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vs σ hJ _) (val_cub D.cub σ hJ _ _ _))
    · rw [← GrpObj.comp_inv]
      exact (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
        (congrArg₂ (· * ·) (vs σ hJ _) (vs σ hJ _))) (val_cub D.cub σ hJ _ _ _))
  let e : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G3 G := lift 1 (lift 1 1)
  have e₀ : e ≫ a = 1 := by simp [e, a, x3]
  have e₁ : e ≫ b = 1 := by simp [e, b, x3]
  let ρ : T ⟶ G3 G := lift x (lift y 1)
  have r₀ : ρ ≫ a = x := by simp [ρ, a, x3]
  have r₁ : ρ ≫ b = y := by simp [ρ, b, x3]
  have h3 := GlobalTheory.UU.surjective_cube GlobalTheory.globalFns_holds D.P.isAb
  have key : val t₁ ρ.left z J = val t₂ ρ.left z J := by
    refine gen_unique' D.P.isLB (fun V _ k => ?_) (G3 G).hom e.left (Over.w e) h3
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (gs _) (gc _ _ _))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (gs _) (gs _)) (gc _ _ _))
      (fun y I hI => ?_) _ ρ.left z J hJ
    · refine (DVR.prod_sum₂ (K := Fin 2 ⊕ Fin 2) (K' := thK) (U := V) _
        (DVR.prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := V) _ (prod_sym a k) (prod_sym b k))
        (prod_cub a a⁻¹ b k)).trans (Eq.trans ?_
        (DVR.prod_sum₂ (K := Fin 2) (K' := thK) (U := V) _ (prod_sym (a * b) k) (prod_cub b b⁻¹ a⁻¹ k)).symm)
      have m₁ : b * b⁻¹ * a⁻¹ = a⁻¹ := by rw [mul_inv_cancel, _root_.one_mul]
      have m₂ : b * b⁻¹ = 1 := mul_inv_cancel b
      have m₃ : b * a⁻¹ = a⁻¹ * b := mul_comm _ _
      have m₄ : b⁻¹ * a⁻¹ = (a * b)⁻¹ := (mul_inv_rev a b).symm
      have m₅ : a * a⁻¹ * b = b := by rw [mul_inv_cancel, _root_.one_mul]
      have m₆ : a * a⁻¹ = 1 := mul_inv_cancel a
      rw [m₁, m₂, m₃, m₄, m₅, m₆]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    · have s1 : val D.sym (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G).left y I = 1 := by
        rw [one_left]
        exact (val_pull hI D.sym (eSec G) _).symm.trans ((val_corr hI D.sym_rig _).trans (val_one _))
      refine (ev e hI).1.trans (Eq.trans ?_ (ev e hI).2.symm)
      rw [e₀, e₁]
      simp only [inv_one, _root_.mul_one, s1, _root_.one_mul]
  have := (ev ρ hJ).1.symm.trans (key.trans (ev ρ hJ).2)
  rwa [r₀, r₁] at this

end GlobalTheory.PolDeg.SymCube
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisAffineOpenRestrictBasicOpenStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangentBasis_affineOpen_restrict_basicOpen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (U W : X.affineOpens) (hW : W.1 ≤ U.1) (f : Γ(X, U.1)), W.1 = X.basicOpen f → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ i, IsTanAtG t (GlobalTheory.LogKS.chart U) (v i)) → (∀ w, IsTanAtG t (GlobalTheory.LogKS.chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (GlobalTheory.LogKS.chart U) v cf w) → ∀ w, IsTanAtG t (GlobalTheory.LogKS.chart W) w → ∃! cf : Fin n → Γ(X, W.1), IsCombAtG t (GlobalTheory.LogKS.chart W) (fun i => spMap (dualMap (X.presheaf.map (homOfLE hW).op).hom) ≫ v i) cf w := by
  first | exact @GlobalTheory.LogKSDiv.tanBasis_basicOpen | exact GlobalTheory.LogKSDiv.tanBasis_basicOpen | (intros; apply GlobalTheory.LogKSDiv.tanBasis_basicOpen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisExtendsToAffineOpen
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.KSAgree.TanLoc

theorem exists_comb_basicOpen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (U W : X.affineOpens) (hW : W.1 ≤ U.1) (f : Γ(X, U.1)), W.1 = X.basicOpen f → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ i, IsTanAtG t (GlobalTheory.LogKS.chart U) (v i)) → (∀ w, IsTanAtG t (GlobalTheory.LogKS.chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (GlobalTheory.LogKS.chart U) v cf w) → ∀ w, IsTanAtG t (GlobalTheory.LogKS.chart W) w → ∃ cf : Fin n → Γ(X, W.1), IsCombAtG t (GlobalTheory.LogKS.chart W) (fun i => spMap (dualMap (X.presheaf.map (homOfLE hW).op).hom) ≫ v i) cf w :=
  fun E _ _ _ H X t U W hW f hf n v hv hb w hw =>
    (GlobalTheory.LogKSDiv.tanBasis_basicOpen E H X t U W hW f hf n v hv hb w hw).exists

end GlobalTheory.KSAgree.TanLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisGenericPointStatement
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_basis_generic_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l' : Level H) (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (A : Type) [CommRing A] (ξ : Sp A ⟶ Y.X) (g : ℕ)
    (e : Fin g → (Sp (DualNumber A) ⟶ Y.t.G.left)), IsTanBasis Y.t ξ e →
    ∀ (L : Type) [CommRing L] (io : A →+* L) (yL : Sp L ⟶ Xo'.XF c'), yL ≫ Y.j = spMap io ≫ ξ →
    ∀ cf : Fin g → L, ∃ w : Sp (DualNumber L) ⟶ Y.oF.t.G.left,
      IsCombAtG Y.t (yL ≫ Y.j) (bcV Y.t io e) cf (w ≫ Y.m.φ) ∧ IsTanAtG Y.oF.t yL w := by
  first | exact @GlobalTheory.FlatModel.LiftGen.exists_lift_comb | exact GlobalTheory.FlatModel.LiftGen.exists_lift_comb | (intros; apply GlobalTheory.FlatModel.LiftGen.exists_lift_comb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisMapCompatible
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.FrameCoordUnit

theorem coord_unit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (A : Type) [CommRing A] (ξ : Sp A ⟶ Y.X) (g : ℕ)
    (e : Fin g → (Sp (DualNumber A) ⟶ Y.t.G.left)), IsTanBasis Y.t ξ e →
    ∀ (σ : E →+* ℂ) (U h : Fin (Dw.mult σ) → Fin g → A), IsUnit (pairDet h U) →
    ∀ (L : Type) [CommRing L] [Algebra c.F L] (io : A →+* L) (yL : Sp L ⟶ Xo'.XF c'), yL ≫ Y.j = spMap io ≫ ξ →
    ∀ z₀ : FrPt Xo c L, z₀.x = yL ≫ r ≫ pullback.fst _ _ →
    ∀ w : Fin (Dw.mult σ) → (Sp (DualNumber L) ⟶ Y.oF.t.G.left),
      (∀ i, IsCombAtG Y.t (yL ≫ Y.j) (bcV Y.t io e) (fun b => io (U i b)) (w i ≫ Y.m.φ)) →
      (∀ i, IsTanAtG Y.oF.t yL (w i)) → (∀ i, IsEigAt c σ (w i ≫ ν.φ)) →
      ∃ g₁ : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) L, IsUnit g₁.det ∧
        ∀ i, IsCombAt z₀.x (z₀.u σ) (g₁ i) (w i ≫ ν.φ) := by
  intro E _ _ _ H Dw l l' Xo Xo' c c' W Y r ν A _ ξ g e he σ U h hU L _ _ io yL hyL z₀ hz₀ w hwc hwt hwe
  have ht1 : ∀ i, IsTanAt z₀.x (w i ≫ ν.φ) := fun i => by
    have := (GlobalTheory.LocM.BaseMdl.tan_push ν (hwt i).1).1 (hwt i)
    rw [hz₀]; exact this
  choose g₁ hg₁ using fun i => (z₀.basis σ (w i ≫ ν.φ) (ht1 i) (hwe i)).exists
  have hub : ∀ j, z₀.u σ j ≫ Xo.univ.t.G.hom =
      spMap (algebraMap L (DualNumber L)) ≫ yL ≫ r ≫ pullback.fst _ _ := fun j => by
    rw [← hz₀]; exact (z₀.tan σ j).1
  choose q hq1 hq2 using fun j => GlobalTheory.LocM.BaseMdl.exists_lift ν (x' := yL) (hub j)
  have hqt : ∀ j, IsTanAtG Y.oF.t yL (q j) := fun j =>
    (GlobalTheory.LocM.BaseMdl.tan_push ν (hq2 j)).2 (by rw [hq1, ← hz₀]; exact z₀.tan σ j)
  have hqt' : ∀ j, IsTanAtG Y.t (spMap io ≫ ξ) (q j ≫ Y.m.φ) := fun j => by
    rw [← hyL]; exact (GlobalTheory.LocM.BaseMdl.tan_push Y.m (hq2 j)).1 (hqt j)
  choose Q hQ using fun j => (he.2 L io (q j ≫ Y.m.φ) (hqt' j)).exists
  have hqb : ∀ j (a : L), (spMap (epsMul a) ≫ q j) ≫ Y.oF.t.G.hom = spMap (algebraMap L (DualNumber L)) ≫ yL :=
    fun j a => by rw [Category.assoc, hq2, ← Category.assoc, GlobalTheory.LocM.BaseMdl.epsMul_comp]
  have hcomb : ∀ i, IsCombAtG Y.oF.t yL q (g₁ i) (w i) := fun i => by
    let u : Fin (Dw.mult σ) → (tEpsG yL ⟶ Y.oF.t.G) := fun j => Over.homMk (spMap (epsMul (g₁ i j)) ≫ q j) (hqb j _)
    have hc : IsCombAtG Y.oF.t yL q (g₁ i) (List.ofFn u).prod.left := ⟨u, fun _ => rfl, rfl⟩
    have hcb : (List.ofFn u).prod.left ≫ Y.oF.t.G.hom = spMap (algebraMap L (DualNumber L)) ≫ yL :=
      Over.w (List.ofFn u).prod
    have hc2 := (GlobalTheory.LocM.BaseMdl.comb_push ν hq2 (g₁ i) hcb).1 hc
    have hq1' : (fun j => q j ≫ ν.φ) = z₀.u σ := funext hq1
    rw [hq1', ← hz₀] at hc2
    have heq : (List.ofFn u).prod.left ≫ ν.φ = w i ≫ ν.φ :=
      GlobalTheory.FlatModel.LiftBC.isCombAtG_unique Xo.univ.t hc2 (hg₁ i)
    have heq2 : (List.ofFn u).prod.left = w i := ν.cart.1.hom_ext heq (hcb.trans (hwt i).1.symm)
    rw [← heq2]; exact hc
  have hwt' : ∀ i, IsTanAtG Y.t (spMap io ≫ ξ) (w i ≫ Y.m.φ) := fun i => by
    rw [← hyL]; exact (GlobalTheory.LocM.BaseMdl.tan_push Y.m (hwt i).1).1 (hwt i)
  have hcomb' : ∀ i, IsCombAtG Y.t (spMap io ≫ ξ) (fun j => q j ≫ Y.m.φ) (g₁ i) (w i ≫ Y.m.φ) := fun i => by
    rw [← hyL]; exact (GlobalTheory.LocM.BaseMdl.comb_push Y.m hq2 (g₁ i) (hwt i).1).1 (hcomb i)
  have hbt : ∀ b, IsTanAtG Y.t (spMap io ≫ ξ) (spMap (dualMap io) ≫ e b) :=
    (GlobalTheory.FlatModel.isTanBasis_bc he io).1
  have hcoef : ∀ i b, io (U i b) = ∑ j, Q j b * g₁ i j := fun i b => by
    have h1 := GlobalTheory.TangentLinear.isCombAtG_mulVec (fun b => spMap (dualMap io) ≫ e b) hbt
      (fun j => q j ≫ Y.m.φ) (Matrix.of fun b j => Q j b) (g₁ i) (w i ≫ Y.m.φ) (fun j => hQ j) (hcomb' i)
    have h2 : IsCombAtG Y.t (spMap io ≫ ξ) (fun b => spMap (dualMap io) ≫ e b) (fun b => io (U i b)) (w i ≫ Y.m.φ) := by
      rw [← hyL]; exact hwc i
    have := (he.2 L io (w i ≫ Y.m.φ) (hwt' i)).unique h2 h1
    have := congrFun this b
    simpa [Matrix.mulVec, dotProduct] using this
  refine ⟨Matrix.of g₁, ?_, fun i => hg₁ i⟩
  let M : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) L := Matrix.of fun j k' => ∑ b, Q j b * io (h k' b)
  have hdet : io (pairDet h U) = (Matrix.of g₁ * M).det := by
    rw [pairDet, RingHom.map_det]
    congr 1
    ext k k'
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, map_sum, map_mul, hcoef,
      Matrix.mul_apply, M, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun b _ => by ring
  have hu := hU.map io
  rw [hdet, Matrix.det_mul] at hu
  exact isUnit_of_mul_isUnit_left hu

end GlobalTheory.FrameCoordUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentCombinationPreservedByBaseChangeStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_combination_preserved_by_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S') (x : Sp S ⟶ X) (x' : Sp S' ⟶ X), spMap φ ≫ x = x' → (∀ v : Sp (DualNumber S) ⟶ t.G.left, IsTanAtG t x v → IsTanAtG t x' (spMap (dualMap φ) ≫ v)) ∧ ∀ (m : ℕ) (v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)) (cf : Fin m → S) (w : Sp (DualNumber S) ⟶ t.G.left), IsCombAtG t x v cf w → IsCombAtG t x' (fun i => spMap (dualMap φ) ≫ v i) (fun i => φ (cf i)) (spMap (dualMap φ) ≫ w) := by
  first | exact @GlobalTheory.TanBaseChange.tan_comb_baseChange | exact GlobalTheory.TanBaseChange.tan_comb_baseChange | (intros; apply GlobalTheory.TanBaseChange.tan_comb_baseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentDerivationAffineChart
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSPkg

open GlobalTheory.DeRham GlobalTheory.Cris

theorem spMap_comp_spMap {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R')
    (g : R' →+* R'') : spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem ksPackage : GlobalTheory.CovTop.Hypotheses₂ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) (δ : Γ(TF.Y.X, U.1) → Γ(TF.Y.X, U.1)) (K : Type) [Field K] [Algebra c.F K] (P : FrPt Xo c K) (hU : ⊤ ≤ (frX P ≫ TF.Y.j) ⁻¹ᵁ U.1) (y' : Sp (DualNumber K) ⟶ Xo.XF c) (hU' : ⊤ ≤ (y' ≫ TF.Y.j) ⁻¹ᵁ U.1), y' ≫ pullback.snd _ _ = spMap (algebraMap c.F (DualNumber K)) → (∀ r, ev (y' ≫ TF.Y.j) U.1 hU' r = TrivSqZeroExt.inl (ev (frX P ≫ TF.Y.j) U.1 hU r) + TrivSqZeroExt.inr (ev (frX P ≫ TF.Y.j) U.1 hU (δ r))) → ∃ (A : Over (Sp K)) (_ : GrpObj A) (A' : Over (Sp (DualNumber K))) (_ : GrpObj A') (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) (ψ : LinearMap.BilinForm K (GlobalTheory.DeRham.HdR A)) (ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR K ⟶ A)) (hb : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) → GlobalTheory.DeRham.HdR A) (g : ℕ), IsGrpPullback A Xo.univ.t.G P.x π ∧ IsGrpPullback A' Xo.univ.t.G (y' ≫ pullback.fst _ _) π' ∧ i ≫ π' = π ∧ GlobalTheory.DeRham.IsPolForm (GlobalTheory.Cris.dp0 K) (𝟙 _) A (Xo.univ.t.PP.L.pull π) ψ ∧ (∀ σ k, (ub σ k).left ≫ π = P.u σ k) ∧ (∀ σ k, GlobalTheory.DeRham.IsLieImage (hb ⟨σ, k⟩) (ub σ k)) ∧ (∀ (τ : GlobalTheory.FlagTan.psiSet H) (a : Fin (Dw.mult (conjEmb τ.1))), ∃ w, GlobalTheory.FlagTan.IsKSRow h ψ hb ⟨conjEmb τ.1, a⟩ w) ∧ IsAbelianScheme A ∧ SmoothOfRelativeDimension g A.hom ∧ IsAbelianScheme A' ∧ SmoothOfRelativeDimension g A'.hom ∧ (Xo.univ.t.PP.L.pull π).IsLB := by
  intro PP E _ _ _ H Dw l Xo c TF U δ K _ _ P hU y' hU' hs hev
  have hred : spMap (GlobalTheory.FlagTan.red c K).toRingHom ≫ y' = frX P := by
    apply GlobalTheory.FlagMod.xF_ext (Y := TF.Y)
    · rw [Category.assoc, hs, spMap_comp_spMap]
      congr 1
    · exact GlobalTheory.FlagMod.frX_snd P
    · have h1 : ⊤ ≤ (spMap (GlobalTheory.FlagTan.red c K).toRingHom ≫ (y' ≫ TF.Y.j)) ⁻¹ᵁ U.1 :=
        GlobalTheory.FlagMod.le_preimage_comp _ hU'
      rw [Category.assoc, ← GlobalTheory.FlagMod.spMap_ev _ U.2 h1, ← GlobalTheory.FlagMod.spMap_ev _ U.2 hU,
        GlobalTheory.FlagMod.ev_spMap _ _ _ hU' h1]
      refine congrArg (fun f => spMap f ≫ (U.2 : IsAffineOpen U.1).fromSpec) ?_
      ext r
      rw [RingHom.comp_apply, hev r]
      simp [GlobalTheory.FlagTan.red]
  have hx : GlobalTheory.FlagTan.IsTanX P (y' ≫ pullback.fst _ _) := by
    refine ⟨?_, ?_⟩
    · rw [Category.assoc, pullback.condition, ← Category.assoc, hs, spMap_comp_spMap]
      rfl
    · rw [← Category.assoc, hred, GlobalTheory.FlagMod.frX_fst]
  have P5 := PP.p5
  obtain ⟨A', _, π', hπ'⟩ := GlobalTheory.FlagTan.exists_isGrpPullback Xo.univ.t.G (y' ≫ pullback.fst _ _)
  obtain ⟨A, _, j, hj⟩ := GlobalTheory.FlagTan.exists_isGrpPullback A' (GlobalTheory.DeRham.epsRed K)
  have hπ : IsGrpPullback A Xo.univ.t.G P.x (j ≫ π') := by
    have := hj.comp hπ'
    rw [← hx.2]
    exact this
  have hUn := GlobalTheory.ObjDim.isAbelianScheme Xo.univ
  have hg := GlobalTheory.ObjDim.smoothOfRelativeDimension Xo.univ
  have hA := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hUn hπ
  have gA := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ.1 hg
  have hA' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hUn hπ'
  have gA' := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ'.1 hg
  have : IsCommMonObj A := hA.comm
  obtain ⟨a', ha'⟩ := GlobalTheory.T.exists_ringAction_of_isGrpPullback Xo.univ.t.act hπ'
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_ringAction_of_isGrpPullback Xo.univ.t.act hπ
  have hc : ∀ z, (a.act z).left ≫ j = j ≫ (a'.act z).left := fun z => by
    apply hπ'.1.hom_ext
    · rw [Category.assoc, Category.assoc, ha' z, ← Category.assoc j π', ← ha z]
    · rw [Category.assoc, Category.assoc, Over.w, hj.1.w, ← Category.assoc, Over.w]
  obtain ⟨ψ, hpol, hiso, hperf, hlag⟩ := GlobalTheory.T.exists_polarizationCrystalForm_perfect_selfAnnihilating P5 Xo hπ
  have hadj := GlobalTheory.T.polarizationCrystalForm_adjoint_conj_action P5 Xo hπ a ha hpol
  have hK := GlobalTheory.T.kodairaSpencerUniqueValue_abelianScheme_field P5 hj hA' gA'
  obtain ⟨ub, hu, ht, he, hbasis⟩ := GlobalTheory.T.exists_frame_tangentVectors_of_isGrpPullback P hπ a ha
  have hL := (P5.2.1 K A _ hA gA).1
  choose hb hbl using fun k : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) => hL.2 (ub k.1 k.2) (ht k.1 k.2)
  obtain ⟨hspan, hind⟩ := GlobalTheory.T.frameLifts_basis_deRhamHomology_mod_hodgeFiltration P5 P hπ ub hu hb hbl
  let χ : (E →+* ℂ) → 𝓞 E →+* K := fun σ => (algebraMap c.F K).comp (embK c σ)
  have heig : ∀ k (z : 𝓞 E), act (dp0 K) (𝟙 _) a z (hb k) - χ k.1 z • hb k ∈ Fil A := fun k z => by
    have := a.hom z
    rw [act_apply]
    have h1 := (hbl k).push (a.act z)
    rw [he] at h1
    exact h1.sub_mem ((hbl k).smul _)
  have hrow : ∀ (τ : GlobalTheory.FlagTan.psiSet H) (a₀ : Fin (Dw.mult (conjEmb τ.1))),
      ∃ w, GlobalTheory.FlagTan.IsKSRow hj ψ hb ⟨conjEmb τ.1, a₀⟩ w := fun τ a₀ => by
    obtain ⟨_, w, -, hw⟩ := GlobalTheory.T.kodairaSpencerRow_dual_eigenvector_mem_span_field hj a (fun z => H.bar z) ψ hiso hlag hperf hadj hK
      (fun z f w hw => GlobalTheory.T.isKodairaSpencerValue_endomorphism_lift hj a a' hc z hw)
      χ ub hb hspan hind heig hbasis τ.1 (conjEmb τ.1)
      (fun z => by simp only [χ, RingHom.comp_apply, GlobalTheory.KSExist.conj_embK]) a₀
    exact ⟨w, hw⟩
  exact ⟨A, inferInstance, A', inferInstance, j ≫ π', π', j, hj, ψ, ub, hb, _, hπ, hπ', rfl, hpol, hu,
    fun σ k => hbl ⟨σ, k⟩, hrow, hA, gA, hA', gA', LB.isLB_pull Xo.univ.t.PP.isLB _⟩

end GlobalTheory.KSPkg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentDerivativeLinearInKodairaSpencerMatrixOfIStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangentDerivative_linear_in_kodairaSpencerMatrix_of_iso : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (K : Type) [Field K] [Algebra c.F K] (P₀ : FrPt Xo c K), KSIso (psiSet H) P₀ → ∀ (U : TF.Y.X.Opens), ⊤ ≤ (frX P₀ ≫ TF.Y.j) ⁻¹ᵁ U → ∃ δ : HIx Dw (psiSet H) → Γ(TF.Y.X, U) → K, ∀ (y' : Sp (DualNumber K) ⟶ Xo.XF c) (hy : ⊤ ≤ (y' ≫ TF.Y.j) ⁻¹ᵁ U), y' ≫ pullback.snd _ _ = spMap (algebraMap c.F (DualNumber K)) → spMap (FlagTan.red c K).toRingHom ≫ y' = frX P₀ → ∀ (M : HIx Dw (psiSet H) → K), FlagTan.IsKS (psiSet H) P₀ (y' ≫ pullback.fst _ _) M → ∀ r, (ev (y' ≫ TF.Y.j) U hy r).snd = ∑ k, M k * δ k r := by
  first | exact @GlobalTheory.LogPole.exists_snd_ev_eq_sum_of_ksIso | exact GlobalTheory.LogPole.exists_snd_ev_eq_sum_of_ksIso | (intros; apply GlobalTheory.LogPole.exists_snd_ev_eq_sum_of_ksIso <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentFrameBaseChangeStatement
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_frame_base_change : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l' : Level H}
    {Xo' : Moduli Dw l'} {c' : Coeff l'} {W : ValuationSubring ℂ} (Y : Model Xo' c' (c'.V W).subtype) {L k : Type}
    [CommRing L] [CommRing k] (φ : L →+* k) (yL : Sp L ⟶ Xo'.XF c') {g : ℕ}
    (e : Fin g → (Sp (DualNumber L) ⟶ Y.t.G.left)) (cf : Fin g → L) (w : Sp (DualNumber L) ⟶ Y.oF.t.G.left)
    (w' : Sp (DualNumber k) ⟶ Y.oF.t.G.left),
    IsCombAtG Y.t (yL ≫ Y.j) e cf (w ≫ Y.m.φ) →
    IsCombAtG Y.t (spMap φ ≫ yL ≫ Y.j) (bcV Y.t φ e) (fun b => φ (cf b)) (w' ≫ Y.m.φ) →
    w' = spMap (dualMap φ) ≫ w := by
  first | exact @GlobalTheory.FlatModel.LiftBC.eq_bc_of_isCombAtG | exact GlobalTheory.FlatModel.LiftBC.eq_bc_of_isCombAtG | (intros; apply GlobalTheory.FlatModel.LiftBC.eq_bc_of_isCombAtG <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentFrameLocalizationIndependent
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieSpanLoc

open GlobalTheory.Serre GlobalTheory.FlatRow.EigLocal

theorem exists_smul_mem_span : ∀ {R O : Type} [CommRing R] [CommRing O] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G],
    Smooth G.hom → ∀ (a : OAct O G) (p : Ideal R) [p.IsPrime] {n : ℕ} (w : Fin n → GlobalTheory.Serre.Lie a),
    (∀ (G' : Over (Sp (Localization.AtPrime p))) [GrpObj G'] (ψ : G'.left ⟶ G.left),
        IsGrpPullback G' G (spMap (algebraMap R (Localization.AtPrime p))) ψ →
        ∀ v : Fin n → (epsR (Localization.AtPrime p) ⟶ G'),
          (∀ i, GlobalTheory.IsVecOver (algebraMap R (Localization.AtPrime p)) ψ (w i).hom (v i)) → IsLieBasis v) →
    ∀ l : GlobalTheory.Serre.Lie a, ∃ s ∉ p, s • l ∈ Submodule.span R (Set.range w) := by
  intro R O _ _ G _ _ hsm a p _ n w hw l
  haveI := hsm
  let Gp := (Over.pullback (spMap (algebraMap R (Localization.AtPrime p)))).obj G
  letI : GrpObj Gp := Functor.grpObjObj
  haveI : IsCommMonObj Gp := Functor.isCommMonObj_obj
  have hp := isGrpPullback_pullback G (spMap (algebraMap R (Localization.AtPrime p)))
  obtain ⟨ap, hap⟩ := GlobalTheory.OActPull.exists_oAct_of_isGrpPullback a hp
  obtain ⟨ρ, hρ, -⟩ := exists_res hp a ap hap
  have hb := hw Gp _ hp (fun i => (ρ (w i)).hom) (fun i => hρ (w i))
  have hbij := (Lie.isLieBasis_iff (a := ap) fun i => ρ (w i)).1 hb
  obtain ⟨c, hc⟩ := hbij.2 (ρ l)
  rw [Fintype.linearCombination_apply] at hc
  obtain ⟨⟨q, hq⟩, hqi⟩ := IsLocalization.exist_integer_multiples p.primeCompl (Finset.univ : Finset (Fin n)) c
  choose b hb' using fun i => hqi i (Finset.mem_univ _)
  have hz : ρ (q • l - ∑ i, b i • w i) = 0 := by
    rw [map_sub, map_smulₛₗ, ← hc, map_sum, Finset.smul_sum, sub_eq_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smulₛₗ, hb', smul_smul, Algebra.smul_def]
  obtain ⟨r, hr, e⟩ := exists_smul_eq_zero a p (q • l - ∑ i, b i • w i) (by
    have e := hρ (q • l - ∑ i, b i • w i)
    have e₀ := hρ 0
    rw [map_zero, Lie.hom_zero, Lie.hom_zero] at e₀
    rw [hz, Lie.hom_zero] at e
    exact e.symm.trans e₀)
  refine ⟨r * q, p.primeCompl.mul_mem hr hq, ?_⟩
  rw [mul_smul, sub_eq_zero.1 ((smul_sub _ _ _).symm.trans e)]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

end GlobalTheory.LieSpanLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentTransportEquivariantCartesianPreservesComStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangentTransport_equivariant_cartesian_preserves_comb : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X Y : Scheme.{0}} (t : SAB H Y) (p : X ⟶ Y) (G' : Over X) [GrpObj G'] (ψ : G'.left ⟶ t.G.left) (b : X ⟶ X) (g : G'.left ⟶ G'.left) (hG : IsGrpPullback G' t.G p ψ), IsGrpPullback G' G' b g → ∀ {R : Type} [CommRing R] (q : Sp R ⟶ X) {n : ℕ} (v : Fin n → (Sp (DualNumber R) ⟶ t.G.left)) (a : Fin n → R) (w : Sp (DualNumber R) ⟶ t.G.left), (∀ i, IsTanAtG t (q ≫ p) (v i)) → IsTanAtG t (q ≫ p) w → IsCombAtG t (q ≫ p) v a w → IsCombAtG t ((q ≫ b) ≫ p) (fun i => GlobalTheory.EqvTrans.trv hG.1 g q (v i)) a (GlobalTheory.EqvTrans.trv hG.1 g q w) := by
  first | exact @GlobalTheory.EqvTrans.trv_comb | exact GlobalTheory.EqvTrans.trv_comb | (intros; apply GlobalTheory.EqvTrans.trv_comb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopFormDerivationDetPairingChangeMatrixStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topFormDerivationDetPairing_change_matrix : ∀ {k A : Type} [CommRing k] [CommRing A] (α : k →+* A) {n : ℕ}
    (D D' : Fin n → (letI := α.toAlgebra; Derivation k A A)) (L : Matrix (Fin n) (Fin n) A),
    (letI := α.toAlgebra; ∀ j, D j = ∑ i, L i j • D' i) →
    ∀ η, GlobalTheory.LogKSDiv.topPair α D η = L.det * GlobalTheory.LogKSDiv.topPair α D' η := by
  first | exact @GlobalTheory.LogKSDiv.topPair_change_matrix | exact GlobalTheory.LogKSDiv.topPair_change_matrix | (intros; apply GlobalTheory.LogKSDiv.topPair_change_matrix <;> assumption)
end

