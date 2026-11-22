import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0239
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieMultIffExistsFrame
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0013
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0018
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0130
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0126
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0103
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0007
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0169
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCMFrame
import Development.WeilBound.CoreStatements.SesquilinearFractions.DualMapCompAlgebraMap
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0185
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0140
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0020
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0119
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HodgeIPIffHodgeFormConj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionDivision
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsLocalHomeomorphAddMonoidHomOfEventuallyEq
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0017
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0013
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0015
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0016
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0012
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0005
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0014
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ContinuousOnValue
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1547
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0072
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0047
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0158
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0061
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0240
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ThreeLeLevel
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0241
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LevClauses
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0121
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniformisationOfPoint
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0184
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.ExistsGoodLevel
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.Bundle0002
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0196
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LabelSigBijective

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianPartLieMultShiftStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_part_lie_mult_shift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (L : Type) [Field L] [CharZero L] (z : Sp L ⟶ S) (P : AbPart t z), ∃ r : ℕ, ∀ (k : Type) [Field k] [IsAlgClosed k] (g : L →+* k) (τ : 𝓞 E →+* k) (n : ℕ), LieMult P.tK.act (spMap g) τ n → r ≤ n ∧ LieMult P.tB.act (spMap g) τ (n - r) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.AbMult.lieMult_abPart | exact GlobalTheory.CompanionTheory.Ar.AbMult.lieMult_abPart | (intros; apply GlobalTheory.CompanionTheory.Ar.AbMult.lieMult_abPart <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryChartHolomorphic
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem isOpen_punct (n a : ℕ) (ρ : ℝ) : IsOpen (punct n a ρ) := by
  have h : punct n a ρ = Metric.ball 0 ρ ∩ ⋂ i : Fin n, {z : Fin n → ℂ | (i : ℕ) < a → z i ≠ 0} := by
    ext z
    simp only [punct, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [h]
  refine Metric.isOpen_ball.inter (isOpen_iInter_of_finite fun i => ?_)
  by_cases hi : (i : ℕ) < a
  · simp only [hi, true_implies]
    exact isOpen_ne_fun (continuous_apply i) continuous_const
  · simp [hi]

theorem isHolTo_of_comp_openImmersion {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] {X Y : Scheme.{0}}
    (j : X ⟶ Y) [IsOpenImmersion j] {B : Set W} {y : W → (Sp ℂ ⟶ X)}
    (h : IsHolTo B fun b => y b ≫ j) : IsHolTo B y := by
  intro U f
  have hpre : ∀ x : Sp ℂ ⟶ X, (x ≫ j) ⁻¹ᵁ (j ''ᵁ U) = x ⁻¹ᵁ U := by
    intro x
    ext p
    simp
  have key : ∀ (x : Sp ℂ ⟶ X) (h1 : ⊤ ≤ (x ≫ j) ⁻¹ᵁ (j ''ᵁ U)) (h2 : ⊤ ≤ x ⁻¹ᵁ U),
      valAt (x ≫ j) (j ''ᵁ U) h1 ((j.appIso U).inv f) = valAt x U h2 f := by
    intro x h1 h2
    have e : (j.appIso U).inv ≫ (x ≫ j).appLE (j ''ᵁ U) ⊤ h1 = x.appLE U ⊤ h2 := by
      rw [← Scheme.Hom.appLE_comp_appLE x j (j ''ᵁ U) U ⊤ (j.preimage_image_eq U).ge h2]
      rw [← Category.assoc, Scheme.Hom.appIso_inv_appLE]
      simp
    unfold valAt
    rw [← e]
    rfl
  have hval : ∀ b, valAt' (y b ≫ j) (j ''ᵁ U) ((j.appIso U).inv f) = valAt' (y b) U f := by
    intro b
    unfold valAt'
    by_cases hb : ⊤ ≤ y b ⁻¹ᵁ U
    · have hb' : ⊤ ≤ (y b ≫ j) ⁻¹ᵁ (j ''ᵁ U) := by rw [hpre]; exact hb
      rw [dif_pos hb, dif_pos hb']
      exact key _ hb' hb
    · have hb' : ¬ ⊤ ≤ (y b ≫ j) ⁻¹ᵁ (j ''ᵁ U) := by rw [hpre]; exact hb
      rw [dif_neg hb, dif_neg hb']
  obtain ⟨ho, hd⟩ := h (j ''ᵁ U) ((j.appIso U).inv f)
  simp only [hpre] at ho hd
  exact ⟨ho, by simpa only [hval] using hd⟩

theorem isHolTo_pt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H)
    (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : BdryChart Xo σ n a), IsHolTo (punct n a 1) C.pt := by
  intro E _ _ _ H D l Xo σ n a C
  haveI := C.j_open
  apply isHolTo_of_comp_openImmersion C.j
  have hB : IsOpen (punct n a 1) := isOpen_punct n a 1
  have hsub : punct n a 1 ⊆ Metric.ball 0 1 := fun z hz => hz.1
  have h0 : IsHolTo (punct n a 1) fun z => ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (C.ψ z) :=
    ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_spMap hB fun r => (C.hol.2 r).mono hsub
  exact GlobalTheory.FiniteOrderConst.isHolTo_of_eqOn h0 fun z hz => (C.pt_eq z hz).1

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmImageUniqueLattice
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.cm_image_unique_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (X : CMPack Z c FU i hP) (b : Bool) (a : PureType.lat hP (sgnRt H b)), (∃! u, X.IsImage b a u) ∧ ∀ u, X.IsImage b a u → IsTanAt Xo.univ.t.G _ u ∧ IsDerivAt0 (fun s => (FU.ex i P s).left) ((Z b).z • P a) (spMap (dualMap (algebraMap X.K ℂ)) ≫ u.left) := by
  first | exact @PositivityTheory.Xgf.cm_image_unique_lattice | exact PositivityTheory.Xgf.cm_image_unique_lattice
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CubicalTripleTrivialStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.UU

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cubical_triple_trivial : ∀ (K : Type) [Field K] (G : Over (Sp K)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → TorusExtension G → ∀ (v : Γ((G ⊗ G ⊗ G).left, ⊤)ˣ), (∀ (T : Over (Sp K)) (x y : T ⟶ G), (lift (1 : T ⟶ G) (lift x y)).left.appTop.hom v.val = 1 ∧ (lift x (lift (1 : T ⟶ G) y)).left.appTop.hom v.val = 1 ∧ (lift x (lift y (1 : T ⟶ G))).left.appTop.hom v.val = 1) → ∀ x y w : 𝟙_ (Over (Sp K)) ⟶ G, (lift x (lift y w)).left.appTop.hom v.val = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CubeUnit.eq_one_at_rational_points | exact GlobalTheory.CompanionTheory.Ar.CubeUnit.eq_one_at_rational_points | (intros; apply GlobalTheory.CompanionTheory.Ar.CubeUnit.eq_one_at_rational_points <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsExpChartCoordinates
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory.CompanionTheory.Ar.AVExp

open GlobalTheory.AbelianExp

attribute [local instance] GlobalTheory.AbelianExp.pointTopology

theorem compactSpace_points (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (hL : Out.RelAmple A L) :
    @CompactSpace _ (PointsCompact.pointTopology A) := by
  have h1 := @valAt'_rules
  have h2 := @existsUnique_point_of_ringHom
  obtain ⟨N, -, M, s, hcov, H⟩ := hL ⊤ (isAffineOpen_top _)
  let Y : Over (Sp ℂ) := Over.mk ((A.hom ∣_ ⊤) ≫ (⊤ : (Sp ℂ).Opens).ι)
  let φ : Y ⟶ A := Over.homMk (A.hom ⁻¹ᵁ ⊤).ι (morphismRestrict_ι A.hom ⊤).symm
  let c₀ : ℂ →+* Γ((⊤ : (Sp ℂ).Opens).toScheme, ⊤) :=
    ((⊤ : (Sp ℂ).Opens).ι.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  have hc₀ : Function.Surjective c₀ := by
    have : IsIso (⊤ : (Sp ℂ).Opens).ι := inferInstanceAs (IsIso (Sp ℂ).topIso.hom)
    exact (ConcreteCategory.bijective_of_isIso ((⊤ : (Sp ℂ).Opens).ι.app ⊤)).2.comp
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).2
  have hY : @CompactSpace _ (PointsCompact.pointTopology Y) := by
    refine PointsCompact.compact_of_sections h1 h2 Y (Out.powOver A L ⊤ N) s hcov
      fun i => ⟨(H i).1, ?_⟩
    obtain ⟨r, hr, hs⟩ := (H i).2
    refine ⟨r, hr, ((A.hom ∣_ ⊤).appLE ⊤ (Out.nonzeroLocus (s i)) le_top).hom.comp c₀,
      fun a => ?_, fun f => ?_⟩
    · have := Scheme.Hom.comp_appLE (A.hom ∣_ ⊤) (⊤ : (Sp ℂ).Opens).ι ⊤
        (Out.nonzeroLocus (s i)) le_top
      exact (congrArg (fun u => u.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a)) this).symm
    · obtain ⟨p, rfl⟩ := hs f
      obtain ⟨q, rfl⟩ := MvPolynomial.map_surjective c₀ hc₀ p
      exact ⟨q, (MvPolynomial.eval₂_map c₀ r _ q).symm⟩
  letI := PointsCompact.pointTopology Y
  letI := PointsCompact.pointTopology A
  have hsurj : Function.Surjective fun x : 𝟙_ (Over (Sp ℂ)) ⟶ Y => x ≫ φ := by
    intro x
    have hrange : Set.range x.left ⊆ Set.range (A.hom ⁻¹ᵁ ⊤).ι := by
      rw [Scheme.Opens.range_ι]
      intro _ _
      trivial
    have hl := IsOpenImmersion.lift_fac (A.hom ⁻¹ᵁ ⊤).ι x.left hrange
    refine ⟨Over.homMk (IsOpenImmersion.lift (A.hom ⁻¹ᵁ ⊤).ι x.left hrange) ?_, ?_⟩
    · have := Over.w x
      rw [← hl, Category.assoc, ← morphismRestrict_ι] at this
      exact this
    · ext1
      exact hl
  exact hsurj.compactSpace (PointsCompact.continuous_comp h1 φ)

theorem surjective_mulA (A : Over (Sp ℂ)) [GrpObj A] (hA : IsAbelianScheme A) (r : ℕ) (hr : 1 ≤ r) :
    Surjective (Out.mulA A r).left := by
  obtain ⟨hfin, hflat⟩ := GlobalTheory.AbTorsionAnyBase.isFinite_and_flat_mulA (Sp ℂ) A hA r hr
  have := hA.smooth
  have := hA.geomConnected
  have : ConnectedSpace A.left := GeometricallyConnected.connectedSpace A.hom A.hom.isOpenMap
  have : LocallyOfFinitePresentation ((Out.mulA A r).left ≫ A.hom) := by
    rw [Over.w]; infer_instance
  have : LocallyOfFinitePresentation (Out.mulA A r).left :=
    GlobalTheory.TangentCrit.locallyOfFinitePresentation_of_comp _ A.hom
  have hcl : IsClosed (Set.range (Out.mulA A r).left) := (Out.mulA A r).left.isClosedMap.isClosed_range
  have hop : IsOpen (Set.range (Out.mulA A r).left) := (Out.mulA A r).left.isOpenMap.isOpen_range
  have hne : (Set.range (Out.mulA A r).left).Nonempty := Set.range_nonempty _
  exact ⟨Set.range_eq_univ.1 (IsClopen.eq_univ ⟨hcl, hop⟩ hne)⟩

theorem exists_div (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A)
    (a₀ : 𝟙_ (Over (Sp ℂ)) ⟶ A) (r : ℕ) (hr : 1 ≤ r) : ∃ b : 𝟙_ (Over (Sp ℂ)) ⟶ A, b ^ r = a₀ := by
  obtain ⟨hfin, -⟩ := GlobalTheory.AbTorsionAnyBase.isFinite_and_flat_mulA (Sp ℂ) A hA r hr
  have hsurj := surjective_mulA A hA r hr
  obtain ⟨t, ht⟩ := H1.SectionDivision.exists_section (pullback.snd (Out.mulA A r).left a₀.left)
  have hb' : (t ≫ pullback.fst (Out.mulA A r).left a₀.left) ≫ (Out.mulA A r).left = a₀.left := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, ht, Category.id_comp]
  have hw : (t ≫ pullback.fst (Out.mulA A r).left a₀.left) ≫ A.hom = (𝟙_ (Over (Sp ℂ))).hom := by
    rw [← Over.w (Out.mulA A r), ← Category.assoc, hb', Over.w a₀]
  refine ⟨Over.homMk _ hw, ?_⟩
  have e : ∀ b : 𝟙_ (Over (Sp ℂ)) ⟶ A, b ^ r = b ≫ Out.mulA A r := fun b =>
    (congrArg (· ^ r) (Category.comp_id b).symm).trans (MonObj.comp_pow (𝟙 A) r b).symm
  rw [e]
  exact Over.OverMorphism.ext hb'

theorem exists_holUnif : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g : ℕ), IsAbelianScheme A → Out.RelAmple A L → SmoothOfRelativeDimension g A.hom → ∃ u : HolUnif A (⟨PUnit, fun _ => ⊤, fun _ _ => 1⟩ : LB A.left) g, ∃ (U : A.left.Opens) (t : Fin g → Γ(A.left, U)), IsAffineOpen U ∧ ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U ∧ (∀ D : Γ(A.left, U) →+ ℂ, (∀ a, D (constFn A.hom U a) = 0) → (∀ f f', D (f * f') = valAt' (u.ex 0).left U f * D f' + valAt' (u.ex 0).left U f' * D f) → (∀ i, D (t i) = 0) → D = 0) ∧ HasFDerivAt (fun w i => valAt' (u.ex w).left U (t i)) (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0 := by
  intro A _ L g hA hL hdim
  have hval := @valAt'_rules
  have hprod := @holFamily_lift hval
  have htop := @isTopologicalGroup_complexPoints hval
  have hchart := @HolChart.exists_holomorphic_chart hval (@existsUnique_point_of_ringHom)
    (@exists_holomorphic_section_of_etale)
  have := hA.comm
  have := htop A
  have := compactSpace_points A L hL
  have hpost := fun X x => (hval X x).2.2.2.1
  have hmulHol : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Set E)
      (a b : E → (𝟙_ (Over (Sp ℂ)) ⟶ A)), HolOn W a → HolOn W b → HolOn W fun w => a w * b w :=
    fun E _ _ W a b ha hb => HolOn.post hpost (hprod E W _ _ a b ha hb) μ[A]
  obtain ⟨W, σ, U, t, hW, h0, hσ0, hU, hσ, ht, ho, hD⟩ := hchart A g hdim 1
  let φ : OpenPartialHomeomorph (Additive (𝟙_ (Over (Sp ℂ)) ⟶ A)) (Fin g → ℂ) :=
    chart t hW hσ ht ho
  have hU1 : ⊤ ≤ (1 : 𝟙_ (Over (Sp ℂ)) ⟶ A).left ⁻¹ᵁ U := hσ0 ▸ (ht 0 h0).1
  have hφ : IsAnalyticGroupChart φ := by
    refine ⟨⟨0, h0, hσ0⟩, funext fun i => ?_, ?_⟩
    · have := (ht 0 h0).2 i
      rwa [hσ0] at this
    · have hH := hmulHol _ (W ×ˢ W) _ _
        (HolOn.comp hσ (hW.prod hW) differentiableOn_fst fun p hp => hp.1)
        (HolOn.comp hσ (hW.prod hW) differentiableOn_snd fun p hp => hp.2)
      refine hH.analyticAt t (w := 0) ⟨h0, h0⟩ ?_
      simpa only [Prod.fst_zero, Prod.snd_zero, hσ0, _root_.mul_one] using hU1
  have hex0 : (hφ.exp 0).toMul = 1 := by rw [map_zero]; rfl
  have hsurj : Function.Surjective hφ.exp := hφ.exp_surjective fun n hn x =>
    exists_div A hA x.toMul n (Nat.one_le_iff_ne_zero.mpr hn)

  obtain ⟨W', large₂, hW', h0', hL', hLm, hLe⟩ : ∃ (W' : Set (Fin g → ℂ))
      (large₂ : (Fin g → ℂ) → (Fin g → ℂ)), IsOpen W' ∧ 0 ∈ W' ∧ DifferentiableOn ℂ large₂ W' ∧
      Set.MapsTo large₂ W' W ∧ ∀ᶠ v in 𝓝 0, (hφ.exp v).toMul = σ (large₂ v) := by
    have ha := hφ.isLocalCommGroupLaw.analyticAt_logChart_symm
    have h1 : ∀ᶠ v in 𝓝 0, hφ.isLocalCommGroupLaw.logChart.symm v ∈ W :=
      ha.continuousAt.eventually (hW.mem_nhds (by simpa using h0))
    obtain ⟨W', h2, h3, h4⟩ := eventually_nhds_iff.mp (ha.eventually_analyticAt.and h1)
    exact ⟨W', _, h3, h4, fun v hv => (h2 v hv).1.differentiableAt.differentiableWithinAt,
      fun v hv => (h2 v hv).2, hφ.exp_eventuallyEq⟩
  refine ⟨⟨fun v => (hφ.exp v).toMul, fun z w => congrArg Additive.toMul (hφ.exp.map_add z w), hsurj,
    hφ.periodLattice, fun z => Iff.rfl, inferInstance, hφ.isZLattice_periodLattice.span_top,
    HolOn.of_local fun z => ?_, fun _ _ => 1, fun _ => differentiableOn_const _,
    fun _ _ _ => one_ne_zero, fun i j z hz => ?_⟩, U, t, hU, ?_, ?_, hφ.hasFDerivAt_chart_exp⟩
  · have hs : Continuous fun v : Fin g → ℂ => v - z := continuous_sub_right z
    have hWz : IsOpen ((fun v => v - z) ⁻¹' W') := hW'.preimage hs
    refine ⟨(fun v => v - z) ⁻¹' W', fun v => (hφ.exp z).toMul * σ (large₂ (v - z)), by simpa using h0',
      hmulHol _ _ _ _ (HolOn.const hWz _) (HolOn.comp (HolOn.comp hσ hW' hL' hLm) hWz
        (differentiableOn_id.sub_const z) fun v hv => hv), ?_⟩
    filter_upwards [(hs.tendsto' z 0 (sub_self z)).eventually hLe] with v hv
    rw [← hv, ← toMul_add, ← map_add, add_sub_cancel]
  · obtain ⟨e, he⟩ := (hval _ _).2.1 _ hz
    rw [he]
    simp
  · show ⊤ ≤ (hφ.exp 0).toMul.left ⁻¹ᵁ U
    rwa [hex0]
  · show ∀ D : Γ(A.left, U) →+ ℂ, _ → (∀ f f', D (f * f') =
      valAt' (hφ.exp 0).toMul.left U f * D f' + valAt' (hφ.exp 0).toMul.left U f' * D f) → _
    rwa [hex0]

end GlobalTheory.CompanionTheory.Ar.AVExp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsSqrtNegDiscPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.PointDet

theorem isReduced_of_isNormalScheme {X : Scheme.{0}} (h : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) : IsReduced X := by
  have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
    have := (h x).1
    infer_instance
  exact isReduced_of_isReduced_stalk X

theorem connectedSpace_of_specializes {X : Scheme.{0}} (x : X) (h : ∀ q : X, x ⤳ q) : ConnectedSpace X := by
  have hcl : closure {x} = (Set.univ : Set X) :=
    Set.eq_univ_of_forall fun q => specializes_iff_mem_closure.1 (h q)
  have hp : PreconnectedSpace X := ⟨by rw [← hcl]; exact isPreconnected_singleton.closure⟩
  exact { toPreconnectedSpace := hp, toNonempty := ⟨x⟩ }

theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

noncomputable def rtF {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l) : c.F :=
  ⟨H.rt0, c.le (IntermediateField.subset_adjoin _ _ (by simp))⟩

theorem rtF_sq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l) :
    rtF c ^ 2 = -(H.d : c.F) := by
  apply Subtype.ext
  simpa [rtF] using H.sqrt_neg_disc_sq

theorem isIntegral_rtF {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l) :
    IsIntegral ℤ (rtF c) := by
  refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
  rw [rtF_sq]
  have := isIntegral_algebraMap (R := ℤ) (A := c.F) (x := -(H.d : ℤ))
  simpa using this

noncomputable def rtO {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l) : 𝓞 c.F :=
  IsIntegralClosure.mk' (𝓞 c.F) (rtF c) (isIntegral_rtF c)

theorem algebraMap_rtO {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l) :
    algebraMap (𝓞 c.F) c.F (rtO c) = rtF c :=
  IsIntegralClosure.algebraMap_mk' _ _ _

theorem rtO_sq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l) :
    rtO c ^ 2 = -(H.d : 𝓞 c.F) := by
  apply RingOfIntegers.ext
  have := rtF_sq c
  rw [← algebraMap_rtO] at this
  simpa using this

theorem detCond_at_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (L : Type) [Field L] [NumberField L] (z : Sp L ⟶ 𝔐.X), ∃ ρ : L, ρ ^ 2 = -(H.d : L) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (g : L →+* k), DetCond D 𝔐.t.act (spMap g ≫ z) (g ρ) := by
  intro E _ _ _ H D l Xo c Y S Ω _ Kf _ J _ y 𝔐 L _ _ z
  haveI : IsReduced 𝔐.X := isReduced_of_isNormalScheme 𝔐.normal
  haveI : ConnectedSpace 𝔐.X := connectedSpace_of_specializes _ 𝔐.all
  haveI : Smooth 𝔐.t.G.hom := 𝔐.t.semi.smooth
  obtain ⟨n, hn⟩ := GlobalTheory.CompanionTheory.Ggeo.exists_smoothOfRelativeDimension_of_geometricallyConnected 𝔐.X 𝔐.t.G 𝔐.t.semi.smooth 𝔐.t.semi.geomConnected
  let s : 𝔐.X ⟶ Sp (𝓞 c.F) := 𝔐.f ≫ Y.s
  have hd : Dense {p : 𝔐.X | ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (_ : CharZero K) (x : Sp K ⟶ 𝔐.X)
      (β : 𝓞 c.F →+* K), p ∈ Set.range x ∧ x ≫ s = spMap β ∧ DetCond D 𝔐.t.act x (β (rtO c))} := by
    intro q
    refine closure_mono (Set.singleton_subset_iff.2 ?_) (specializes_iff_mem_closure.1 (𝔐.all q))
    let i : Ω →+* AlgebraicClosure Ω := algebraMap Ω (AlgebraicClosure Ω)
    haveI : CharZero Ω := charZero_of_injective_ringHom 𝔐.cst.injective
    haveI : CharZero (AlgebraicClosure Ω) := charZero_of_injective_ringHom i.injective
    refine ⟨AlgebraicClosure Ω, inferInstance, inferInstance, inferInstance, spMap i ≫ 𝔐.ξ,
      i.comp (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)), ?_, ?_, ?_⟩
    · let y₀ : Sp (AlgebraicClosure Ω) := (default : PrimeSpectrum (AlgebraicClosure Ω))
      refine ⟨y₀, ?_⟩
      rw [Scheme.Hom.comp_apply]
      exact congrArg 𝔐.ξ (Subsingleton.elim _ _)
    · have h := 𝔐.cst_over
      change (spMap i ≫ 𝔐.ξ) ≫ 𝔐.f ≫ Y.s = _
      rw [Category.assoc, h, spMap_comp_spMap]
    · intro τ
      have hβ : (i.comp (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F))) (rtO c) = (i.comp 𝔐.cst) (rtF c) := by
        simp only [RingHom.comp_apply, algebraMap_rtO]
      rw [hβ]
      obtain ⟨h₁, h₂⟩ := GlobalTheory.CompanionTheory.Ar.LabelCover.exists_label E H l c (rtF c) rfl (AlgebraicClosure Ω) (i.comp 𝔐.cst) τ
      constructor
      · intro h
        obtain ⟨t, rfl⟩ := h₁ h
        exact (GlobalTheory.DetExtend.lieMult_extend i 𝔐.ξ 𝔐.t.act (𝔐.emb (.inl t)) D.p).2
          (GlobalTheory.CompanionTheory.Ar.HodgeCpt.lieMult_label_generic E H D l Xo c (𝓞 c.F) (algebraMap (𝓞 c.F) c.F) Y S Ω Kf J y 𝔐 (.inl t))
      · intro h
        obtain ⟨t, rfl⟩ := h₂ h
        exact (GlobalTheory.DetExtend.lieMult_extend i 𝔐.ξ 𝔐.t.act (𝔐.emb (.inr t)) D.q).2
          (GlobalTheory.CompanionTheory.Ar.HodgeCpt.lieMult_label_generic E H D l Xo c (𝓞 c.F) (algebraMap (𝓞 c.F) c.F) Y S Ω Kf J y 𝔐 (.inr t))
  obtain ⟨b, hb⟩ := Spec.map_surjective (z ≫ s)
  refine ⟨b.hom (rtO c), ?_, ?_⟩
  · have := congrArg b.hom (rtO_sq c)
    rw [map_pow, map_neg, map_natCast] at this
    exact this
  · intro k _ _ g
    haveI : CharZero k := charZero_of_injective_ringHom g.injective
    refine GlobalTheory.DetSpread.detCond_of_dense E H D 𝔐.X 𝔐.t.G n 𝔐.t.act (𝓞 c.F) s (rtO c) hn (rtO_sq c) hd k
      (spMap g ≫ z) (g.comp b.hom) ?_
    rw [Category.assoc, ← hb]
    exact spMap_comp_spMap b.hom g

end GlobalTheory.CompanionTheory.Ar.PointDet
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyPeriodRiemannLatticeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.family_period_riemann_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo σ ty) (i : Fin FU.n) (R : RiemLat E g (FU.Di i).La) (P : (FU.Di i).La →+ (Fin g → ℂ)) (h : Matrix (Fin g) (Fin g) ℂ), IsPeriod (FU.Di i) ty P → R.form = (FU.Di i).EF → IsUnit h.det → (∀ x, P x = h *ᵥ R.P x) → ∀ (A₀ : Type) (x : A₀ → Fin g → ℂ) (v : A₀ → (epsAt (FU.u i P) ⟶ Xo.univ.t.G)), (∀ a, IsDerivAt0 (fun z => (FU.ex i P z).left) (h *ᵥ x a) (v a).left) → FibreLatVec Xo.univ.t (FU.u i P) R x v := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.FibreAtPeriod.fibreLatVec_of_period | exact GlobalTheory.CompanionTheory.Ar.Cusp.FibreAtPeriod.fibreLatVec_of_period | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.FibreAtPeriod.fibreLatVec_of_period <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameFunctionsFlatAgreeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_functions_flat_agree : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (φ φ' : FrameFn Xo c), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → τ (H.rt : E) = H.rt0 → Z.IsGeom → IsLineFn U τ φ → FlatOnModel Z τ φ → IsLineFn U τ φ' → FlatOnModel Z τ φ' → ∃ x : c.F, x ≠ 0 ∧ ∀ (F : Type) [Field F] (βF : c.F →+* F) y v w, IsFramed U τ βF y v w → φ' F y v w = βF x * φ F y v w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_const_of_flatOnModel | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_const_of_flatOnModel | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_const_of_flatOnModel <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolUnifCompareIsogenyStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hol_unif_compare_isogeny : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (L : LB G.left) (z : Spec (CommRingCat.of ℂ) ⟶ X) (A A' : Over (Sp ℂ)) [GrpObj A] [GrpObj A'] (φ : A.left ⟶ G.left) (φ' : A'.left ⟶ G.left) (g g' : ℕ) (u : HolUnif A (L.pull φ) g) (u' : HolUnif A' (L.pull φ') g') (Hm : Matrix (Fin g) (Fin g) ℂ) (Hm' : Matrix (Fin g') (Fin g') ℂ) (χ : u.Λ → ℂ) (χ' : u'.Λ → ℂ), L.IsLB → IsAbelianScheme A → IsGrpPullback A G z φ → IsGrpPullback A' G z φ' → (∀ v, IsTangent v → ∃! w, u.IsDiff w v) → (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) → u.IsAH Hm χ → u'.IsAH Hm' χ' → ∀ (x y : epsR ℂ ⟶ A) (x' y' : epsR ℂ ⟶ A') (a b : Fin g → ℂ) (a' b' : Fin g' → ℂ), IsTangent x → IsTangent y → x'.left ≫ φ' = x.left ≫ φ → y'.left ≫ φ' = y.left ≫ φ → u.IsDiff a x → u.IsDiff b y → u'.IsDiff a' x' → u'.IsDiff b' y' → hermForm Hm' a' b' = hermForm Hm a b := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HodgeUniq.hermForm_eq_of_pullbacks | exact GlobalTheory.CompanionTheory.Ar.HodgeUniq.hermForm_eq_of_pullbacks | (intros; apply GlobalTheory.CompanionTheory.Ar.HodgeUniq.hermForm_eq_of_pullbacks <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PicardClassTrivialBySeesawStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CechPic
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.picard_class_trivial_by_seesaw : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (T : TorusExtension G) (Y : Over (Sp k)), Smooth Y.hom → GeometricallyConnected Y.hom → ∀ (y₀ : 𝟙_ (Over (Sp k)) ⟶ Y) (c : Pic (T.B ⊗ Y).left), pull (lift (fst G Y ≫ T.q) (snd G Y)).left c = 0 → pull (lift (𝟙 T.B) (toUnit T.B ≫ y₀)).left c = 0 → c = 0 := by
  first | exact @GlobalTheory.CompanionTheory.TorusPic.pic_inj | exact GlobalTheory.CompanionTheory.TorusPic.pic_inj | (intros; apply GlobalTheory.CompanionTheory.TorusPic.pic_inj <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrincipalGoodReductionExtendsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principal_good_reduction_extends : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (t : SAB H (Sp L)), IsPrincipal t → (∀ (σ : L →+* ℂ) (τ : 𝓞 E →+* ℂ), LieMult t.act (spMap σ) τ 0) → ∃ t' : SAB H (Sp (𝓞 L)), Nonempty (SABMap t t' (spMap (algebraMap (𝓞 L) L))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TrivialModel.exists_model_of_rank_zero | exact GlobalTheory.CompanionTheory.Ar.TrivialModel.exists_model_of_rank_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.TrivialModel.exists_model_of_rank_zero <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameSectionBoundStatement
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_origin_frame_section_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or), ∀ (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t → ∀ x : (Ref.pjSys Xo c).Pt la, (∀ f, (Ref.pjSys Xo c).val x f = nval T.V e (evI y f)) → FinRd.ReadsZ Fr z x (FinRd.tOf p la T e t) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.readsZ_of_isIntPt | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.readsZ_of_isIntPt | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.readsZ_of_isIntPt <;> assumption)
end

