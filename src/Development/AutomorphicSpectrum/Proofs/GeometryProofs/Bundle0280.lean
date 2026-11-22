import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryChartHodgeMap
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0010
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0007
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0279
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FinConstFor
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0002
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionEmbeddingGeometricPoints
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicColimitOfFactor
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CInfGood
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0015
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.OnbMat
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0014
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CuspOnto
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0006
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Statements.GeometryStatements.LamLevel
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0005
import Development.AutomorphicSpectrum.Statements.MetricStatements.SmallOnTower
import Development.AutomorphicSpectrum.Statements.MetricStatements.RankBound
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0015
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.Bundle0001
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.ShareLow
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.SpecFirstDetFormNeZero
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0278
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0027
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkSpecializesBijective
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0070
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0143
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0216
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0078
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameLawsOfModuli
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0226
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0228
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValuationComponentUnique

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryChartHodgeMapStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundary_chart_hodge_map : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (σ : KA l →+* ℂ) (n a : ℕ) (C : Flat.BdryChart Xo σ n a) (jj : Sp C.R ⟶ 𝔐.X) (m : SABMap C.t 𝔐.t jj) (B₀ : Set (Fin n → ℂ)) (e : Flat.FamExp C.t.G C.M B₀ C.ψ) (b : Fin n → ℂ) (Bb : 𝓞 E →+* Module.End ℂ (Fin C.g → ℂ)) (Hm : Matrix (Fin C.g) (Fin C.g) ℂ), 1 ≤ D.p + D.q → b ∈ B₀ → 𝔐.Interior (spMap (C.ψ b) ≫ jj) → C.IsRiem b Hm → (∀ a' x, e.ex b (Bb a' x) = e.ex b x ≫ C.t.act.act a') → ∃ (A : Over (Sp ℂ)) (_ : GrpObj A) (φ : A.left ⟶ 𝔐.t.G.left) (u : HolUnif A (𝔐.t.PP.L.pull φ) C.g) (χ : u.Λ → ℂ), IsGrpPullback A 𝔐.t.G (spMap (C.ψ b) ≫ jj) φ ∧ u.IsAH Hm χ ∧ (∀ x, (u.ex x).left ≫ φ = (e.ex b x).left ≫ m.φ) ∧ (∀ x, x ∈ u.Λ ↔ x ∈ e.per b) ∧ (∀ (x : Fin C.g → ℂ) (v : Sp (DualNumber ℂ) ⟶ C.t.G.left), IsDerivAt0 (fun x => (e.ex b x).left) x v → ∃ v' : epsR ℂ ⟶ A, v'.left ≫ φ = v ≫ m.φ ∧ u.IsDiff x v') ∧ ∀ a' a'' : 𝓞 E, (a'' : E) = IsCMField.complexConj E (a' : E) → ∀ x x', hermForm Hm (Bb a' x) x' = hermForm Hm x (Bb a'' x') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.ChartUnif.exists_unif_of_interior | exact GlobalTheory.CompanionTheory.Ar.Cusp.ChartUnif.exists_unif_of_interior | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.ChartUnif.exists_unif_of_interior <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteConstantAllHoldsStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_constant_all_holds : GlobalTheory.CompanionTheory.Ar.Flat.FinConstAll := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.FinAll.finConstAll | exact GlobalTheory.CompanionTheory.Ar.Flat.FinAll.finConstAll | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.FinAll.finConstAll <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteMapEqOfThickeningsEq
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.BT.EqRed
open GlobalTheory.AdicColimit

variable {R : Type} [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]

theorem eq_zero_of_forall_mem_map (A : Type) [CommRing A] [Algebra R A] [Module.Finite R A] (x : A)
    (h : ∀ e : ℕ, x ∈ (I ^ (e + 1)).map (algebraMap R A)) : x = 0 := by
  have hI : I ≤ (⊥ : Ideal R).jacobson := IsAdicComplete.le_jacobson_bot I
  have key := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := A) I hI
  have hx : x ∈ (⨅ i : ℕ, I ^ i • (⊤ : Submodule R A)) := by
    refine Submodule.mem_iInf _ |>.2 fun i => ?_
    have h1 : x ∈ (I ^ (i + 1) • (⊤ : Submodule R A)) := by
      rw [Ideal.smul_top_eq_map]
      exact h i
    exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ i)) h1
  rw [key] at hx
  simpa using hx

theorem eq_of_reductions (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    (X Y : Over (Spec (CommRingCat.of R))) [IsFinite X.hom] [IsFinite Y.hom] (f g : X ⟶ Y)
    (h : ∀ e, (Over.pullback (thick R I e)).map f = (Over.pullback (thick R I e)).map g) : f = g := by
  have : IsAffine X.left := isAffine_of_isAffineHom X.hom
  have : IsAffine Y.left := isAffine_of_isAffineHom Y.hom

  let ψ : CommRingCat.of R ⟶ Γ(X.left, ⊤) := Spec.preimage (X.left.isoSpec.inv ≫ X.hom)
  have hψ : Spec.map ψ = X.left.isoSpec.inv ≫ X.hom := Spec.map_preimage _
  let _ : Algebra R Γ(X.left, ⊤) := ψ.hom.toAlgebra
  have hfin : IsFinite (Spec.map ψ) := by rw [hψ]; infer_instance
  have hfin' : ψ.hom.Finite := (IsFinite.SpecMap_iff ψ).1 hfin
  have : Module.Finite R Γ(X.left, ⊤) := hfin'

  let u : Spec Γ(X.left, ⊤) ⟶ Spec Γ(Y.left, ⊤) := X.left.isoSpec.inv ≫ f.left ≫ Y.left.isoSpec.hom
  let v : Spec Γ(X.left, ⊤) ⟶ Spec Γ(Y.left, ⊤) := X.left.isoSpec.inv ≫ g.left ≫ Y.left.isoSpec.hom
  have hu : Spec.map (Spec.preimage u) = u := Spec.map_preimage _
  have hv : Spec.map (Spec.preimage v) = v := Spec.map_preimage _

  have hred : ∀ e : ℕ, Spec.preimage u ≫ CommRingCat.ofHom (Ideal.Quotient.mk
      ((I ^ (e + 1)).map (algebraMap R Γ(X.left, ⊤)))) = Spec.preimage v ≫ CommRingCat.ofHom (Ideal.Quotient.mk
      ((I ^ (e + 1)).map (algebraMap R Γ(X.left, ⊤)))) := by
    intro e
    let J := (I ^ (e + 1)).map (algebraMap R Γ(X.left, ⊤))
    let m : Spec (CommRingCat.of (Γ(X.left, ⊤) ⧸ J)) ⟶ Spec Γ(X.left, ⊤) :=
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
    let q : Spec (CommRingCat.of (Γ(X.left, ⊤) ⧸ J)) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) :=
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap J (algebraMap R Γ(X.left, ⊤)) Ideal.le_comap_map))
    have hcond : (m ≫ X.left.isoSpec.inv) ≫ X.hom = q ≫ thick R I e := by
      rw [Category.assoc, ← hψ]
      simp only [m, q, thick, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 1
    let t : Spec (CommRingCat.of (Γ(X.left, ⊤) ⧸ J)) ⟶ (thickObj R I e X).left :=
      pullback.lift (m ≫ X.left.isoSpec.inv) q hcond
    have ht : t ≫ thickι I e X = m ≫ X.left.isoSpec.inv := pullback.lift_fst _ _ _
    have hfg : thickι I e X ≫ f.left = thickι I e X ≫ g.left := by
      have hl : thickHom I e f = thickHom I e g := congrArg (fun φ => φ.left) (h e)
      rw [← thickHom_ι, ← thickHom_ι, hl]
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, hu, hv]
    change m ≫ u = m ≫ v
    simp only [u, v]
    rw [← Category.assoc m, ← Category.assoc m, ← ht, Category.assoc t, Category.assoc t,
      reassoc_of% hfg]
  have hpre : Spec.preimage u = Spec.preimage v := by
    ext b
    refine sub_eq_zero.1 (eq_zero_of_forall_mem_map I Γ(X.left, ⊤) _ fun e => ?_)
    exact Ideal.Quotient.eq.1 (congrArg (fun φ => φ.hom b) (hred e))
  have huv : u = v := by rw [← hu, ← hv, hpre]
  apply Over.OverMorphism.ext
  have h1 : f.left ≫ Y.left.isoSpec.hom = g.left ≫ Y.left.isoSpec.hom := (cancel_epi X.left.isoSpec.inv).1 huv
  exact (cancel_mono Y.left.isoSpec.hom).1 h1

end GlobalTheory.CompanionTheory.Ar.BT.EqRed
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FramePointBorelSectionScalingStatement
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_point_borel_section_scaling : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (a : GlobalTheory.CompanionTheory.Ar.Rec.WZ E) (f : Rul Xo c) (L : Type) [Field L] [Algebra c.F L] (t : Ix Dw → Lˣ) (y y' : FrPt Xo c L), f ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c a → FrBor t y y' → evR Xo c f y' = ((∏ i, t i ^ GlobalTheory.CompanionTheory.Ar.Rec.exZ Dw a i : Lˣ) : L) * evR Xo c f y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FieldPt.evR_frBor_secZ_field | exact GlobalTheory.CompanionTheory.Ar.Rec.FieldPt.evR_frBor_secZ_field | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FieldPt.evR_frBor_secZ_field <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointsOfClosedSubgroup
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.BT.RatKer

theorem exists_section_of_generic : ∀ (R : Type) [CommRing R] [IsDomain R] (H : Type) [CommGroup H] (Γf : QFGroup R H) (A E : Over (Spec (CommRingCat.of R))) (a : A ⟶ Γf.G) (b : Γf.G ⟶ E) (e : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ E), IsClosedImmersion a.left → IsPullback a (toUnit A) b e → ∀ g : A.left, (A.hom g).asIdeal = ⊥ → ∃ (κ : genPt R ⟶ A) (x : Spec (CommRingCat.of (FractionRing R))), κ.left x = g := by
  intro R _ _ H _ Γf A E a b e ha hP g hg
  have hwa : Γf.G.hom (a.left g) = A.hom g := by
    rw [← Scheme.Hom.comp_apply, Over.w]
  obtain ⟨t, x, hx⟩ := Γf.11 (a.left g) (by rw [hwa]; exact hg)
  have hgen : (GlobalTheory.CompanionTheory.Ar.BT.genPt R).hom x = A.hom g := by
    rw [← Over.w (Γf.9 t), Scheme.Hom.comp_apply, hx, hwa]
  have hab := congrArg (fun φ => φ.left g) hP.w
  simp only [Over.comp_left, Scheme.Hom.comp_apply, Over.toUnit_left] at hab
  have hpt : Γf.9 t ≫ b = toUnit (GlobalTheory.CompanionTheory.Ar.BT.genPt R) ≫ e := by
    apply Over.OverMorphism.ext
    apply GlobalTheory.CompanionTheory.Ar.BT.Tors.eq_of_same_point E.hom _ _ (Over.w _) (Over.w _) x x
    simp only [Over.comp_left, Scheme.Hom.comp_apply, Over.toUnit_left]
    rw [hx, hab, hgen]
  refine ⟨hP.lift (Γf.9 t) (toUnit _) hpt, x, ?_⟩
  apply a.left.isClosedEmbedding.injective
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hP.lift_fst, hx]

end GlobalTheory.CompanionTheory.Ar.BT.RatKer
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointsOfTorsionKernel
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.BT.Tors

section Identity
variable {R : Type} [CommRing R]

def toIdMk (Y : Over (Spec (CommRingCat.of R))) : Y ⟶ Over.mk (Y.hom ≫ 𝟙 _) :=
  Over.homMk (𝟙 _) (by simp)

def ofIdMk (Y : Over (Spec (CommRingCat.of R))) : Over.mk (Y.hom ≫ 𝟙 _) ⟶ Y :=
  Over.homMk (𝟙 _) (by simp)

theorem ofIdMk_toIdMk (Y : Over (Spec (CommRingCat.of R))) : ofIdMk Y ≫ toIdMk Y = 𝟙 _ := by
  ext
  simp [ofIdMk, toIdMk]

end Identity

theorem exists_qfGroup_kernel : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CharZero R] (B : Over (Spec (CommRingCat.of R))) [GrpObj B], IsSemiAbelian B → ∀ (N : ℕ), 1 ≤ N → ∀ (A : Over (Spec (CommRingCat.of R))) [GrpObj A] [IsCommMonObj A] (j : A ⟶ B) [IsMonHom j], IsPullback j (toUnit A) ((𝟙 B) ^ N) η[B] → (∀ g : A.left, (A.hom g).asIdeal = ⊥ → ∃ (κ : genPt R ⟶ A) (x : Spec (CommRingCat.of (FractionRing R))), κ.left x = g) → ∃ (C : Type) (_ : CommGroup C) (Γ : QFGroup R C) (φ : Γ.G ≅ A), IsMonHom φ.hom ∧ Γ.IsTorsionAlong B (𝟙 _) N (φ.hom.left ≫ j.left) := by
  intro R _ _ _ _ B _ hB N hN A _ _ j _ hp hpt
  have := hB.smooth
  have := hB.separated
  have := hB.quasiCompact
  have := hB.comm
  have := GlobalTheory.CompanionTheory.Ar.BT.flat_mul_semiAbelian (Spec (CommRingCat.of R)) B hB N hN
  have := GlobalTheory.CompanionTheory.Ar.BT.locallyQuasiFinite_pow_semiAbelian (Spec (CommRingCat.of R)) B hB N hN
  have hm := mono_of_pullback hp
  obtain ⟨h1, h2, h3, h4, h5⟩ := kernel_props hp
  have := kernel_base_etale (genPt R).hom hp (isUnit_natCast_generic hN)
  haveI : IsReduced (genPt R).left := inferInstanceAs (IsReduced (Spec (CommRingCat.of (FractionRing R))))
  have hred := GlobalTheory.isReduced_of_smooth_of_isReduced (pullback.snd A.hom (genPt R).hom)
  have hv : ∀ {Y : Over (Spec (CommRingCat.of R))} (g : Over.mk (Y.hom ≫ 𝟙 _) ⟶ B) (y : Y ⟶ A),
      y.left ≫ j.left = g.left → y ≫ j = toIdMk Y ≫ g := fun {Y} g y h => by
    ext
    simpa [toIdMk] using h
  refine ⟨genPt R ⟶ A, inferInstance,
    { G := A, flat := h1, quasiFinite := h2, separated := h3, quasiCompact := h4, finPres := h5,
      pt := MonoidHom.id _, pt_inj := ?_, pt_onto := hpt, gen_reduced := hred }, Iso.refl _, ?_, ?_⟩
  · intro s t u v h
    exact Over.OverMorphism.ext (eq_of_same_point A.hom _ _ (Over.w _) (Over.w _) u v h)
  · show IsMonHom (𝟙 A)
    infer_instance
  · refine { isOver := ?_, mul := ?_, inj := ?_, kernel := ?_ }
    · show (𝟙 _ ≫ j.left) ≫ B.hom = A.hom ≫ 𝟙 _
      simpa using Over.w j
    · intro Y y z y₀ z₀ hy hz
      have hy' : y ≫ j = toIdMk Y ≫ y₀ := hv y₀ y (by rw [hy]; simp)
      have hz' : z ≫ j = toIdMk Y ≫ z₀ := hv z₀ z (by rw [hz]; simp)
      have e : (y * z) ≫ j = toIdMk Y ≫ (y₀ * z₀) := by
        rw [MonObj.mul_comp, hy', hz', MonObj.comp_mul]
      have e' := congrArg (fun w => w.left) e
      simpa [toIdMk] using e'.symm
    · intro Y y z h
      rw [← cancel_mono j]
      ext
      simpa using h
    · intro Y g
      constructor
      · intro h
        have h' : (toIdMk Y ≫ g) ^ N = 1 := by
          rw [← MonObj.comp_pow, h, MonObj.comp_one]
        obtain ⟨y, hy⟩ := lift_of_torsion hp _ h'
        refine ⟨y, ?_⟩
        have e := congrArg (fun w => w.left) hy
        simpa [toIdMk] using e
      · rintro ⟨y, hy⟩
        have e : y ≫ j = toIdMk Y ≫ g := hv g y (by rw [← hy]; simp)
        have h' : (toIdMk Y ≫ g) ^ N = 1 := by rw [← e]; exact torsion_of_comp hp y
        have e2 : ofIdMk Y ≫ toIdMk Y ≫ g = g := by
          rw [← Category.assoc, ofIdMk_toIdMk, Category.id_comp]
        rw [← e2, ← MonObj.comp_pow, h', MonObj.comp_one]

end GlobalTheory.CompanionTheory.Ar.BT.Tors
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsCombBaseChangeStatement
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.is_comb_base_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S T : Type) [CommRing S] [CommRing T] (φ : S →+* T) (x : Sp S ⟶ Xo.X) (m : ℕ) (v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (cf : Fin m → S) (w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left), IsCombAt x v cf w → IsCombAt (spMap φ ≫ x) (fun i => spMap (Formalism.L2.Pj.dualMap φ) ≫ v i) (fun i => φ (cf i)) (spMap (Formalism.L2.Pj.dualMap φ) ≫ w) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CombMap.isCombAt_spMap | exact GlobalTheory.CompanionTheory.Ar.CombMap.isCombAt_spMap | (intros; apply GlobalTheory.CompanionTheory.Ar.CombMap.isCombAt_spMap <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LevelLawsFrameDictionaryStatement
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_laws_frame_dictionary : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c) (W : HSp D) (dict : ∀ σ : c.F →+* ℂ, GA D W → Σ k, Frame ((U σ).X k).Ψ D.R.r), CompLaws U h e → abelian₂.LevelLaws U W dict → FinVol W → ∀ σ, GoodEmb c σ → ∀ Z k, Over (U σ) (e Z) k → ∀ (a : WZ D.host.E) (x0 : Frame ((U σ).X k).Ψ D.R.r) (FF : Set (ReciprocityTheory.L2DbarEstimates.V (nd ((U σ).X k)))), IsOrth ((U σ).X k) x0 → IsFundSet ((U σ).X k) x0 FF → (0 < muF ((U σ).X k) x0 FF ∧ muF ((U σ).X k) x0 FF < ⊤) ∧ (∀ f ∈ cuspOn U h a Z, ∀ g ∈ cuspOn U h a Z, ipOn U W dict (xiR D) a (e Z) σ f g = ((lieFacZ Dw (xiR D) a ^ 2 : ℝ) : ℂ) * Deg.pet ((U σ).X k) (laZ (U σ) a k) (rdU (U σ) f k) (rdU (U σ) g k)) ∧ ∀ (m : ℕ) (as : Fin m → ℂ) (fs : Fin m → Rul Xo c), (∀ j, fs j ∈ cuspOn U h a Z) → (∑ j, ∑ j', as j * starRingEnd ℂ (as j') * ipOn U W dict (xiR D) a (e Z) σ (fs j) (fs j')).re = lieFacZ Dw (xiR D) a ^ 2 * ThA.nrm2 ((U σ).X k) x0 FF (laZ (U σ) a k) (fun y => ∑ j, as j * rdU (U σ) (fs j) k y) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.level_laws_frame_dictionary | exact GlobalTheory.CompanionTheory.Relay.level_laws_frame_dictionary | (intros; apply GlobalTheory.CompanionTheory.Relay.level_laws_frame_dictionary <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginComponentGenericPointStatement
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_origin_component_generic_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Z : Comp Xo c), GlobalTheory.CompanionTheory.Ar.genPt Fx.ξf = Y.j (Formalism.L2.Pj.genPt Z) → ∃ ψ : kap Z ≃+* Or.𝔐.Ω₀, spMap ψ.toRingHom ≫ genSp Z ≫ Y.j = Or.𝔐.ξ₀ ∧ ∀ a : c.F, Or.𝔐.fn (ψ (algebraMap c.F (kap Z) a)) = Or.𝔐.cst a := by
  first | exact @GlobalTheory.CompanionTheory.Ar.KapEquiv.exists_kap_equiv | exact GlobalTheory.CompanionTheory.Ar.KapEquiv.exists_kap_equiv | (intros; apply GlobalTheory.CompanionTheory.Ar.KapEquiv.exists_kap_equiv <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionEmbeddingGeometricPointsStatement
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G.Semi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_embedding_geometric_points : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CharZero R] (T : Type) [CommGroup T] (S : Scheme.{0}) (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ), 1 ≤ N → ∀ τ : T →* (Over.mk ((genPt R).hom ≫ x) ⟶ G), Function.Injective τ → (∀ t, τ t ^ N = 1) → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (a : FractionRing R →+* Ω) (g : Over.mk (Spec.map (CommRingCat.ofHom a) ≫ (genPt R).hom ≫ x) ⟶ G), g ^ N = 1 → ∃ t, g.left = Spec.map (CommRingCat.ofHom a) ≫ (τ t).left) → ∃ (Γ : QFGroup R T) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i ∧ ∀ t, (Γ.pt t).left ≫ i = (τ t).left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.Tors.exists_qfGroup_torsion | exact GlobalTheory.CompanionTheory.Ar.BT.Tors.exists_qfGroup_torsion | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.Tors.exists_qfGroup_torsion <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValuationComponentUniqueStatement
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_component_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → (∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, ∃ Z, v (e Z) = 0 ∧ ∀ Z', Z' ≠ Z → v (e Z') = ⊤ ∧ ∀ a, ∀ f ∈ cuspOn U h a Z', v f = ⊤) ∧ (∀ la Z, ∃ v ∈ valSet Xo c (algCls Xo c) la, v (e Z) = 0) ∧ ∀ a, (∀ Z, ∀ f ∈ cuspZ Xo c U a, e Z * f ∈ cuspOn U h a Z) ∧ ⨆ Z, cuspOn U h a Z = cuspZ Xo c U a := by
  first | exact @GlobalTheory.CompanionTheory.Relay.valuation_component_unique | exact GlobalTheory.CompanionTheory.Relay.valuation_component_unique | (intros; apply GlobalTheory.CompanionTheory.Relay.valuation_component_unique <;> assumption)
end

