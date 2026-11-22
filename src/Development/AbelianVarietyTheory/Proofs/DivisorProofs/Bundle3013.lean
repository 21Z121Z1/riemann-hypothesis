import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2930
import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2931
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2821
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0085
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralElemNearFibreOfGenericPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2684
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2737
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2888
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2668
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2932
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0084
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2761
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2624
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2210
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0037
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2472
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2919
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenCastIsGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2933
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2676
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2744

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteIffFiniteKer
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.FinKer

theorem finite_of_isClosed_of_finite_closedPoints {T : Type*} [TopologicalSpace T]
    [JacobsonSpace T] {S : Set T} (hS : IsClosed S) (h : (S ∩ closedPoints T).Finite) :
    S.Finite := by
  have hc : IsClosed (S ∩ closedPoints T) := by
    rw [← Set.biUnion_of_singleton (S ∩ closedPoints T)]
    exact h.isClosed_biUnion fun x hx ↦ hx.2
  rw [← JacobsonSpace.closure_inter_closedPoints hS, hc.closure_eq]
  exact h

theorem locallyQuasiFinite_of_finite_closedFibres {Y X : Scheme.{0}} (f : Y ⟶ X)
    [LocallyOfFiniteType f] [JacobsonSpace Y]
    (h : ∀ y : Y, IsClosed ({y} : Set Y) → (f ⁻¹' {f y}).Finite) : LocallyQuasiFinite f := by
  rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff, eq_top_iff]
  refine subset_of_isOpen_of_closedPoints isOpen_univ f.quasiFiniteLocus.isOpen fun y hy _ ↦ ?_
  have : Finite (f.fiber (f y)) := (f.fiberHomeo (f y)).finite_iff.mpr (h y hy)
  exact Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mpr (isOpen_discrete _)

theorem exists_lift_of_isClosed {Ω : Type} [Field Ω] [IsAlgClosed Ω] {X Y : Scheme.{0}} (g : X ⟶ Y)
    [LocallyOfFiniteType g] (u : Sp Ω ⟶ Y) (z : X) (hz : IsClosed ({z} : Set X))
    (h : u (IsLocalRing.closedPoint Ω) = g z) :
    ∃ w : Sp Ω ⟶ X, w ≫ g = u ∧ w (IsLocalRing.closedPoint Ω) = z := by
  obtain ⟨p, -, hp2⟩ := Scheme.Pullback.exists_preimage_pullback (f := u) (g := g) _ z h
  have : JacobsonSpace ↥(pullback u g) := LocallyOfFiniteType.jacobsonSpace (pullback.fst u g)
  have hcl : IsClosed (closure ({p} : Set ↥(pullback u g))) := isClosed_closure
  have hne : (closure ({p} : Set ↥(pullback u g)) ∩ closedPoints _).Nonempty := by
    by_contra hc
    rw [Set.not_nonempty_iff_eq_empty] at hc
    have := JacobsonSpace.closure_inter_closedPoints hcl
    rw [hc, closure_empty] at this
    exact (this.symm ▸ subset_closure (Set.mem_singleton p) : p ∈ (∅ : Set _))
  obtain ⟨q, hqp, hq₀⟩ := hne
  have hq : IsClosed ({q} : Set ↥(pullback u g)) := mem_closedPoints_iff.mp hq₀
  refine ⟨pointOfClosedPoint (pullback.fst u g) q hq ≫ pullback.snd u g, ?_, ?_⟩
  · rw [Category.assoc, ← pullback.condition, pointOfClosedPoint_comp_assoc]
  · change (pullback.snd u g) (pointOfClosedPoint (pullback.fst u g) q hq _) = z
    erw [pointOfClosedPoint_apply]
    have hs : p ⤳ q := specializes_iff_mem_closure.mpr hqp
    have := (hs.map (pullback.snd u g).continuous).mem_closed hz (by rw [hp2]; rfl)
    exact this

end GlobalTheory.AV.FinKer

namespace GlobalTheory.AV.AbVar

open GlobalTheory.AV.FinKer in

theorem isFinite_iff_finite_ker : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B),
    IsFinite f.hom.left ↔ Finite (ptMap f).ker := by
  intro K _ A B f
  have : IsProper A.X.hom := A.ab.proper
  have : IsProper B.X.hom := B.ab.proper
  have hw : f.hom.left ≫ B.X.hom = A.X.hom := Over.w f.hom
  have : LocallyOfFiniteType (f.hom.left ≫ B.X.hom) := by rw [hw]; infer_instance
  have : LocallyOfFiniteType f.hom.left := locallyOfFiniteType_of_comp _ B.X.hom
  let pt : Sp (AlgebraicClosure K) := IsLocalRing.closedPoint (AlgebraicClosure K)
  constructor
  · intro hf
    let u : Sp (AlgebraicClosure K) ⟶ B.X.left := (1 : B.Pt).left
    have : IsFinite (pullback.fst u f.hom.left) := inferInstance
    have hfin := ((pullback.fst u f.hom.left).finite_preimage_singleton pt).to_subtype
    have hmem : ∀ x : (ptMap f).ker, 𝟙 _ ≫ u = x.1.left ≫ f.hom.left := fun x ↦ by
      rw [Category.id_comp, ← Over.comp_left]
      exact congrArg CommaMorphism.left (MonoidHom.mem_ker.mp x.2).symm
    refine Finite.of_injective (β := (pullback.fst u f.hom.left) ⁻¹' {pt})
      (fun x ↦ ⟨pullback.lift (𝟙 _) x.1.left (hmem x) pt, Subsingleton.elim _ _⟩) fun x y hxy ↦ ?_
    have e := ext_of_apply_closedPoint_eq (pullback.fst u f.hom.left) (pullback.lift_fst _ _ _)
      (pullback.lift_fst _ _ _) (congrArg Subtype.val hxy)
    have e2 := congrArg (· ≫ pullback.snd u f.hom.left) e
    simp only [pullback.lift_snd] at e2
    exact Subtype.ext (Over.OverMorphism.ext e2)
  · intro hker
    have : IsProper (f.hom.left ≫ B.X.hom) := by rw [hw]; infer_instance
    have : IsProper f.hom.left := IsProper.of_comp _ B.X.hom
    have : JacobsonSpace A.X.left := LocallyOfFiniteType.jacobsonSpace A.X.hom
    have : LocallyQuasiFinite f.hom.left := by
      refine locallyQuasiFinite_of_finite_closedFibres f.hom.left fun y hy ↦ ?_
      obtain ⟨a, ha, hay⟩ := exists_lift_of_isClosed A.X.hom (spMap (algebraMap K (AlgebraicClosure K)))
        y hy (Subsingleton.elim _ _)
      let x : A.Pt := Over.homMk a ha
      have hcl : IsClosed (f.hom.left ⁻¹' {f.hom.left y}) := by
        have := f.hom.left.isClosedMap _ hy
        rw [Set.image_singleton] at this
        exact this.preimage f.hom.left.continuous
      refine finite_of_isClosed_of_finite_closedPoints hcl ?_
      refine (Set.finite_range (fun k : (ptMap f).ker ↦ (x * k.1).left pt)).subset ?_
      rintro z ⟨hzS, hz⟩
      have hzS' : f.hom.left z = f.hom.left y := hzS
      obtain ⟨w, hw1, hw2⟩ := exists_lift_of_isClosed f.hom.left (a ≫ f.hom.left) z hz
        (by change f.hom.left (a pt) = _; rw [hay, hzS'])
      let w' : A.Pt := Over.homMk w (by
        change w ≫ A.X.hom = _
        rw [← hw, ← Category.assoc, hw1, Category.assoc, hw]; exact ha)
      have hk : x⁻¹ * w' ∈ (ptMap f).ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]
        exact Over.OverMorphism.ext hw1.symm
      refine ⟨⟨_, hk⟩, ?_⟩
      change (x * (x⁻¹ * w')).left pt = z
      rw [mul_inv_cancel_left]
      exact hw2
    exact IsFinite.of_isProper_of_locallyQuasiFinite _

end GlobalTheory.AV.AbVar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackPasteFactorisationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isGrpPullback_paste_factorisation : ∀ {B S T T' : Scheme.{0}} (Gb : Over B) [GrpObj Gb] (Gs : Over S) [GrpObj Gs] (Gt : Over T) [GrpObj Gt] (Gt' : Over T') [GrpObj Gt'] (fS : S ⟶ B) (fT : T ⟶ B) (g : T' ⟶ T) (h : T' ⟶ S) (φS : Gs.left ⟶ Gb.left) (φT : Gt.left ⟶ Gb.left) (ψ : Gt'.left ⟶ Gt.left), IsGrpPullback Gs Gb fS φS → IsGrpPullback Gt Gb fT φT → IsGrpPullback Gt' Gt g ψ → h ≫ fS = g ≫ fT → ∃ φ : Gt'.left ⟶ Gs.left, IsGrpPullback Gt' Gs h φ ∧ φ ≫ φS = ψ ≫ φT := by
  first | exact @GlobalTheory.isGrpPullback_paste | exact GlobalTheory.isGrpPullback_paste | (intros; apply GlobalTheory.isGrpPullback_paste <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGtPointInvolutionActionSubOfIdempotentStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isGtPointInvolutionAction_sub_of_idempotent : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F] {O : Type} [Ring O] [StarRing O] [Module O D.X] (oa : D.OAct O) (a : O), a * a = a → ∀ g₀ g h t : GtPtF D F, GtPtAct oa a g₀ g → GtPtAct oa a h h → GtPtF.IsAdd t h g → GtPtAct oa a t t := by
  first | exact @GlobalTheory.Mum.IdemDiff.gtPtAct_of_isAdd | exact GlobalTheory.Mum.IdemDiff.gtPtAct_of_isAdd | (intros; apply GlobalTheory.Mum.IdemDiff.gtPtAct_of_isAdd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHolomorphicUnitMatrixAtRationalMatrixValues
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernCalc

theorem holUnitAt_ratVal : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (s : ℕ) (T : Matrix (Fin s) (Fin s) X.Fn)
    (y : CxPts X.str σ), (∀ i j, RegAt (under y) (T i j)) → T.det ≠ 0 → RegAt (under y) (T.det)⁻¹ →
    HolUnitAt (atlas X σ) (fun z => T.map (ratVal · z)) y := by
  intro F _ σ X s T y hT hd hdi
  refine ⟨?_, fun c hc a b => ?_⟩
  · obtain ⟨ψ, hψ⟩ := exists_ratVal_hom y
    let T' : Matrix (Fin s) (Fin s) ((ratOf X).O (under y)).toSubring :=
      Matrix.of fun i j => ⟨T i j, mem_O_ratOf.2 (hT i j)⟩
    have e1 : T.map (ratVal · y) = T'.map ψ := by
      ext i j
      exact hψ (T' i j)
    have e2 : ((T'.det : ((ratOf X).O (under y)).toSubring) : X.Fn) = T.det :=
      (RingHom.map_det (((ratOf X).O (under y)).toSubring.subtype) T').trans rfl
    have hu : UnitAt (under y) T.det := (unitAt_iff hd).2 ⟨e2 ▸ mem_O_ratOf.1 T'.det.2, hdi⟩
    have hne := ratVal_ne_zero (y := y) hu
    rw [← e2, hψ] at hne
    show IsUnit (T.map (ratVal · y)).det
    rw [e1, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact isUnit_iff_ne_zero.2 hne
  · obtain ⟨U, hU, g, e⟩ := (hT a b).exists_fnOf
    have hyU : y ∈ ptsIn X.str σ U := mem_ptsIn.2 hU
    filter_upwards [(GlobalTheory.ChartGlue.isOpen_over c.e (isOpen_ptsIn U)).mem_nhds (GlobalTheory.ChartGlue.mem_over c.e hc hyU)] with v hv
    have hdv : DifferentiableAt ℂ (ev X.str σ U g ∘ c.e.symm) v :=
      (c.holo U g).differentiableAt ((GlobalTheory.ChartGlue.isOpen_over c.e (isOpen_ptsIn U)).mem_nhds hv)
    refine hdv.congr_of_eventuallyEq ?_
    filter_upwards [(GlobalTheory.ChartGlue.isOpen_over c.e (isOpen_ptsIn U)).mem_nhds hv] with u hu
    show ratVal (T a b) (c.e.symm u) = ev X.str σ U g (c.e.symm u)
    rw [← e, ratVal_fnOf hu.2]

end GlobalTheory.ChernCalc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralElemNearFibreOfGenericPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegralElem_near_fibre_of_generic_point : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (M : Modif R) (G : Over M.S), Smooth G.hom → QuasiCompact G.hom → GeometricallyIrreducible G.hom → ∀ (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)), IsPullback α t G.hom M.gp → ∀ (W : G.left.Opens), IsAffineOpen W → ∀ (U : M.S.Opens), IsAffineOpen U → W ≤ G.hom ⁻¹ᵁ U → ∀ (f : Γ(Y, α ⁻¹ᵁ W)) (x ζ : G.left), x ∈ W → G.hom ζ = G.hom x → (∀ z, G.hom z = G.hom x → ζ ⤳ z) → (∃ c : Γ(G.left, W), ζ ∈ G.left.basicOpen c ∧ (α.app (G.left.basicOpen c)).hom.IsIntegralElem ((Y.presheaf.map (homOfLE (α.preimage_mono (G.left.basicOpen_le c))).op).hom f)) → ∃ c : Γ(G.left, W), x ∈ G.left.basicOpen c ∧ (α.app (G.left.basicOpen c)).hom.IsIntegralElem ((Y.presheaf.map (homOfLE (α.preimage_mono (G.left.basicOpen_le c))).op).hom f) := by
  first | exact @GlobalTheory.Mum.intElem_basicOpen_of_fibre_generic | exact GlobalTheory.Mum.intElem_basicOpen_of_fibre_generic | (intros; apply GlobalTheory.Mum.intElem_basicOpen_of_fibre_generic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoOfIsIsoOnGeometricFibresOfSmooth
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_common_ext_of_apply_eq {T : Scheme.{0}} (K Ω : Type) [Field K] [Field Ω]
    (a : Sp K ⟶ T) (b : Sp Ω ⟶ T)
    (u : Sp K) (v : Sp Ω) (e : a u = b v) :
    ∃ (L : Type) (_ : Field L) (j₁ : K →+* L) (j₂ : Ω →+* L), spMap j₁ ≫ a = spMap j₂ ≫ b := by
  obtain ⟨⟨s₁, φ₁⟩, e₁⟩ := (Scheme.SpecToEquivOfField K T).symm.surjective a
  obtain ⟨⟨s₂, φ₂⟩, e₂⟩ := (Scheme.SpecToEquivOfField Ω T).symm.surjective b
  simp only [Scheme.SpecToEquivOfField_symm_apply] at e₁ e₂
  have hs : s₁ = s₂ := by
    rw [← e₁, ← e₂] at e
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply,
      Scheme.fromSpecResidueField_apply] at e
    exact e
  subst hs
  obtain ⟨L, _, j₁, j₂, hj⟩ := GlobalTheory.exists_common_field_extension (T.residueField s₁) K Ω φ₁.hom φ₂.hom
  refine ⟨L, inferInstance, j₁, j₂, ?_⟩
  rw [← e₁, ← e₂, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 2
  ext1
  exact hj

end GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem universallyInjective_of_fieldPoints' {G P : Scheme.{0}} (h : G ⟶ P)
    (H : ∀ (K : Type) [Field K] (z z' : Sp K ⟶ G), z ≫ h = z' ≫ h → z = z') :
    UniversallyInjective h := by
  rw [UniversallyInjective.iff_diagonal, surjective_iff]
  intro x
  let w := (Limits.pullback h h).fromSpecResidueField x
  have e : w ≫ Limits.pullback.fst h h = w ≫ Limits.pullback.snd h h :=
    H ((Limits.pullback h h).residueField x) _ _ (by
      simp only [Category.assoc, Limits.pullback.condition])
  have e2 : (w ≫ Limits.pullback.fst h h) ≫ Limits.pullback.diagonal h = w := by
    apply Limits.pullback.hom_ext
    · simp
    · simp [e]
  let pt : Spec ((Limits.pullback h h).residueField x) := IsLocalRing.closedPoint _
  refine ⟨(w ≫ Limits.pullback.fst h h) pt, ?_⟩
  rw [← Scheme.Hom.comp_apply, e2, Scheme.fromSpecResidueField_apply]

theorem isIso_of_isIso_fibres : ∀ (T X Z : Scheme.{0}) (p : X ⟶ T) (q : Z ⟶ T) (h : X ⟶ Z) (hh : h ≫ q = p), Smooth p → Smooth q → (∀ s : T, ∃ (Ω : Type) (_ : Field Ω) (x : Sp Ω ⟶ T), s ∈ Set.range x ∧ IsIso (pullback.map p x q x h (𝟙 _) (𝟙 _) (by simp [hh]) (by simp))) → IsIso h := by
  intro T X Z p q h hh hp hq H
  apply GlobalTheory.T.isIso_of_etale_of_surjective_of_universallyInjective' X Z h
  ·
    have hloc : ∀ z : X, ∃ V : X.Opens, z ∈ V ∧ Etale (V.ι ≫ h) := by
      intro z
      obtain ⟨Ω, _, x, ⟨t, ht⟩, hiso⟩ := H (p z)
      obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := x) z t ht.symm
      have hE : Etale ((⊤ : (pullback p x).Opens).ι ≫
          pullback.map p x q x h (𝟙 _) (𝟙 _) (by simp [hh]) (by simp)) := inferInstance
      obtain ⟨V, hV, hVe⟩ := GlobalTheory.T.etale_near_point_of_etale_on_fibre_smooth T X Z p q h hh hp hq Ω x ⊤ w trivial hE
      exact ⟨V, hw ▸ hV, hVe⟩
    choose V hV hVe using hloc
    have : IsZariskiLocalAtSource @Etale := HasRingHomProperty.instIsZariskiLocalAtSource
    refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @Etale) V ?_ hVe
    exact top_unique fun z _ => TopologicalSpace.Opens.mem_iSup.2 ⟨z, hV z⟩
  ·
    refine ⟨fun y => ?_⟩
    obtain ⟨Ω, _, x, ⟨t, ht⟩, hiso⟩ := H (q y)
    obtain ⟨v, hv, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := q) (g := x) y t ht.symm
    let m := pullback.map p x q x h (𝟙 _) (𝟙 _) (by simp [hh]) (by simp)
    refine ⟨pullback.fst p x (inv m v), ?_⟩
    rw [← Scheme.Hom.comp_apply, ← pullback.lift_fst (f := q) (g := x) (pullback.fst p x ≫ h)
      (pullback.snd p x ≫ 𝟙 _) (by simp [hh, pullback.condition]), Scheme.Hom.comp_apply]
    change pullback.fst q x (m (inv m v)) = y
    rw [← Scheme.Hom.comp_apply m, ← Scheme.Hom.comp_apply, IsIso.inv_hom_id_assoc]
    exact hv
  ·
    refine universallyInjective_of_fieldPoints' h fun K _ z z' hz => ?_
    let u : Sp K := IsLocalRing.closedPoint K
    obtain ⟨Ω, _, x, ⟨t, ht⟩, hiso⟩ := H ((z ≫ p) u)
    obtain ⟨L, _, j₁, j₂, hj⟩ := exists_common_ext_of_apply_eq K Ω (z ≫ p) x u t ht.symm
    have hj' : spMap j₁ ≫ z' ≫ p = spMap j₂ ≫ x := by
      rw [← hh, ← Category.assoc z', ← hz, Category.assoc, hh, hj]
    let m := pullback.map p x q x h (𝟙 _) (𝟙 _) (by simp [hh]) (by simp)
    let a := pullback.lift (f := p) (g := x) (spMap j₁ ≫ z) (spMap j₂) (by rw [Category.assoc, hj])
    let a' := pullback.lift (f := p) (g := x) (spMap j₁ ≫ z') (spMap j₂) (by rw [Category.assoc, hj'])
    have haa : a ≫ m = a' ≫ m := by
      apply pullback.hom_ext
      · simp only [m, a, a', Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, hz]
      · simp only [m, a, a', pullback.map, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
          Category.comp_id]
    have haa' : a = a' := (cancel_mono m).1 haa
    have := congrArg (· ≫ pullback.fst p x) haa'
    simp only [a, a', pullback.lift_fst] at this
    exact GlobalTheory.Mum.spMap_field_cancel K L j₁ X z z' this

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNoetherianFunctionFieldModelArithBaseStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNoetherian_functionFieldModel_arithBase : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω), AlgebraicGeometry.IsNoetherian M.Z := by
  first | exact @GlobalTheory.ratModel_isNoetherian_of_arithBase | exact GlobalTheory.ratModel_isNoetherian_of_arithBase | (intros; apply GlobalTheory.ratModel_isNoetherian_of_arithBase <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularRingFormalFibreMvPolynomialPerfect
section
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem isRegularRing_adicCompletion_tensor_of_mvPolynomial :
    ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsRegularRing Λ] [PerfectField (FractionRing Λ)] (n : ℕ)
      (P : Ideal (MvPolynomial (Fin n) Λ)) [P.IsPrime] (K : Type) [Field K]
      [Algebra (Localization.AtPrime P) K] [Algebra.EssFiniteType (Localization.AtPrime P) K],
      (∀ a : Λ, algebraMap (Localization.AtPrime P) K
        (algebraMap Λ (Localization.AtPrime P) a) = 0 → a = 0) →
      IsRegularRing (AdicCompletion (maximalIdeal (Localization.AtPrime P))
        (Localization.AtPrime P) ⊗[Localization.AtPrime P] K) := by
  intro Λ _ _ _ _ n P _ K _ _ _ hinj
  let S₀ := MvPolynomial (Fin n) Λ
  let R := Localization.AtPrime P
  let B := AdicCompletion (maximalIdeal R) R
  haveI : IsRegularLocalRing R := inferInstance
  haveI : IsRegularLocalRing B := GlobalTheory.RegularCompletion.isRegularLocalRing_adicCompletion R
  haveI : IsRegularRing B := GlobalTheory.isRegularRing_of_isRegularLocalRing B
  letI : Algebra S₀ K := ((algebraMap R K).comp (algebraMap S₀ R)).toAlgebra
  haveI : IsScalarTower S₀ R K := .of_algebraMap_eq fun _ => rfl
  haveI : Algebra.EssFiniteType S₀ R := Algebra.EssFiniteType.of_isLocalization R P.primeCompl
  haveI : Algebra.EssFiniteType S₀ K := Algebra.EssFiniteType.comp S₀ R K
  have hC : ∀ a : Λ, algebraMap S₀ K (MvPolynomial.C a) = 0 → a = 0 := by
    intro a ha
    apply hinj a
    rw [IsScalarTower.algebraMap_apply Λ S₀ R a]
    exact ha
  have hD : ∀ s : Fin n, ∃ D : Derivation ℤ B B, ∀ x,
      D (algebraMap S₀ B x) = algebraMap S₀ B (MvPolynomial.pderiv s x) := fun s =>
    GlobalTheory.T.exists_derivation_extend_adicCompletion_localization S₀ P ((MvPolynomial.pderiv s).restrictScalars ℤ)
  have hD' : ∀ s : Fin n, ∃ D : @Derivation ℤ B B _ _ _ (Ring.toIntAlgebra B) _ _, ∀ x,
      D (algebraMap S₀ B x) = algebraMap S₀ B (MvPolynomial.pderiv s x) := by
    intro s
    obtain ⟨D, hD⟩ := hD s
    exact ⟨@Derivation.mk ℤ B B _ _ _ (Ring.toIntAlgebra B) _ _ D.toLinearMap
      D.map_one_eq_zero' D.leibniz', hD⟩
  have h := GlobalTheory.T.regular_fibre_of_lifted_partialDerivations Λ (Fin n) B K hC hD'
  let e : B ⊗[R] K ≃ₐ[R] B ⊗[S₀] K := IsLocalization.algebraTensorEquiv P.primeCompl R B K
  exact IsRegularRing.of_ringEquiv e.symm.toRingEquiv

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSeparatedSiegelModuliOverIntegersStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSeparated_siegelModuli_over_integers : ∀ {g n : ℕ} (F : SFam g n (zetaAway n)), IsSeparated (toZ F.X) := by
  first | exact @GlobalTheory.SepSiegel.isSeparated_toZ | exact GlobalTheory.SepSiegel.isSeparated_toZ | (intros; apply GlobalTheory.SepSiegel.isSeparated_toZ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymmetricFramePullbackMumfordFrameGaloisTwist
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj

namespace GlobalTheory.Mum.Conj

theorem gm_comp_stalkMap {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (h : g (f z) ∈ U)
    (a : Γ(X, U)ˣ) : gm (f ≫ g) z U a = Units.map (f.stalkMap z).hom.toMonoidHom (gm g (f z) U a) := by
  apply Units.ext
  rw [gm_val (f ≫ g) z U h, Units.coe_map, gm_val g (f z) U h]
  exact (Scheme.Hom.germ_stalkMap_apply f (g ⁻¹ᵁ U) z h ((g.app U).hom a.val)).symm

theorem val_comp_stalkMap {X Y Z W : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (f : Z ⟶ W) (r : W ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) (hJ : Good L z J) :
    val t (f ≫ r) z J = Units.map (f.stalkMap z).hom.toMonoidHom (val t r (f z) (fun ψ => J (f ≫ ψ))) := by
  rw [val_of t (f ≫ r) z J (fun k => J (f ≫ r ≫ φ k)) (fun k => by rw [Category.assoc])]
  exact gm_comp_stalkMap f r z _ (Set.mem_iInter.2 fun k => hJ (f ≫ r ≫ φ k)) _

theorem good_comp {X Z W : Scheme.{0}} {L : LB X} (f : Z ⟶ W) {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    Good L (f z) (fun ψ => J (f ≫ ψ)) := fun ψ => hJ (f ≫ ψ)

end GlobalTheory.Mum.Conj

namespace GlobalTheory.Mum.Conj

theorem txFrame_frTw (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (N : ℕ)
    (τ : Kb R →ₐ[FractionRing R] Kb R) (p p₀ : QkPt D (Kb R) N) (h : QkExt τ.toRingHom p p₀)
    (w : GlobalTheory.UT.Frm D (Kb R) N p.g.b) : GlobalTheory.UT.TXFrame N p w → GlobalTheory.UT.TXFrame N p₀ (frTw D τ h w) := by
  rintro ⟨hg, h2, hN⟩
  set f : (TF (R := R) (Kb R)).left ⟶ (TF (R := R) (Kb R)).left := spMap τ.toRingHom with hf
  have hfr : ∀ (z : (TF (R := R) (Kb R)).left) (J), Good D.P.L z J →
      val (frTw D τ h w) (𝟙 _) z J = Units.map (f.stalkMap z).hom.toMonoidHom (val w (𝟙 _) (f z) (fun ψ => J (f ≫ ψ))) := by
    intro z J hJ
    rw [frTw, val_genCast, val_pull hJ, Category.id_comp, ← Category.comp_id f]
    exact val_comp_stalkMap w f (𝟙 _) z J hJ
  have hsy : ∀ (z : (TF (R := R) (Kb R)).left) (J), Good D.P.L z J →
      val (p₀.g.s p₀.y) (𝟙 _) z J = Units.map (f.stalkMap z).hom.toMonoidHom (val (p.g.s p.y) (𝟙 _) (f z) (fun ψ => J (f ≫ ψ))) := by
    intro z J hJ
    rw [h.1, val_corr hJ (h.2.2 p.y), val_pull hJ, Category.id_comp, ← Category.comp_id f]
    exact val_comp_stalkMap _ f (𝟙 _) z J hJ
  refine ⟨genCast_isGen _ (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen D.P.L _ _ w hg _), ?_, ?_⟩
  · intro ν hν z J hJ
    rw [hfr z J hJ, hsy z J hJ, h.2.1, val_comp_stalkMap ν f _ z J hJ, ← map_pow, ← map_mul,
      h2 ν hν (f z) _ (good_comp f hJ)]
  · intro κ hκ z J hJ
    have hpsi : val (D.psi p₀.y) (jFK (R := R) (Kb R)) z J =
        Units.map (f.stalkMap z).hom.toMonoidHom (val (D.psi p.y) (jFK (R := R) (Kb R)) (f z) (fun ψ => J (f ≫ ψ))) := by
      have e := val_comp_stalkMap (D.psi p.y) f (jFK (R := R) (Kb R)) z J hJ
      rw [h.1]
      refine Eq.trans ?_ e
      exact congrArg (fun r => val (D.psi p.y) r z J) (spMap_jFK τ).symm
    have hrig : GlobalTheory.UT.rigV D (TF (R := R) (Kb R)).hom z J =
        Units.map (f.stalkMap z).hom.toMonoidHom (GlobalTheory.UT.rigV D (TF (R := R) (Kb R)).hom (f z) (fun ψ => J (f ≫ ψ))) := by
      unfold GlobalTheory.UT.rigV
      rw [← val_comp_stalkMap _ f _ z J hJ]
      exact congrArg (fun r => val D.rig r z J) (spMap_jFKR τ).symm
    rw [id_eq, hfr z J hJ, hpsi, hrig, h.2.1, val_comp_stalkMap κ f _ z J hJ, ← map_pow, ← map_mul, ← map_mul,
]
    exact congrArg _ (hN κ hκ (f z) _ (good_comp f hJ))

end GlobalTheory.Mum.Conj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaPointOfAlgebraicSeriesOneTraitStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isThetaPoint_of_algebraic_series_one_trait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → OneTrait D.toPre A lab → ∀ (j : ℕ) (v : QkPt D.toPre (Kb R) ((n ^ j) ^ 2) → Kb R), (∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [Algebra (FractionRing R) C], GlobalTheory.Ex.CExt R (maximalIdeal R) C → ∀ (em : Kb R →ₐ[FractionRing R] C) (N : GlobalTheory.Ex.NumD C) (nu : GlobalTheory.Ex.NumOf D.toPre C N) (p₁ : QkPt D.toPre (Kb R) ((n ^ j) ^ 2) → QkPt D.toPre C ((n ^ j) ^ 2)) (q : QkPt D.toPre (Kb R) ((n ^ j) ^ 2) → N.QT ((n ^ j) ^ 2)), (∀ i, QkExt em.toRingHom i (p₁ i)) → (∀ i, nu.QPt (p₁ i) (q i)) → ∃ s : Cˣ, ∀ i, em (v i) = s * N.tx (n ^ j) (q i)) → IsThetaPt A (n ^ j) (lab ((n ^ j) ^ 2)) (fun p => GlobalTheory.Ex.fnOf (v p)) := by
  first | exact @GlobalTheory.Mum.OneTraitTheta.isThetaPt_of_series | exact GlobalTheory.Mum.OneTraitTheta.isThetaPt_of_series | (intros; apply GlobalTheory.Mum.OneTraitTheta.isThetaPt_of_series <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorsionLabelingGaloisConjugateAlgClosureStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTorsionLabeling_galoisConjugate_algClosure : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (σ : Kb R →ₐ[FractionRing R] Kb R) (k : ℕ), 1 ≤ k → ∀ (x x' : QkPt D.toPre (Kb R) k → (TFK (R := R) (Kb R) ⟶ A.A)), LabTors D.toPre A k x → (∀ p p', QkExt σ.toRingHom p p' → (x' p').left = spMap σ.toRingHom ≫ (x p).left) → LabTors D.toPre A k x' := by
  first | exact @GlobalTheory.Mum.labTors_galConj | exact GlobalTheory.Mum.labTors_galConj | (intros; apply GlobalTheory.Mum.labTors_galConj <;> assumption)
end

