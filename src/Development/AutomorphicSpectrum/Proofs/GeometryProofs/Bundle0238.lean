import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0185
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0140
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0020
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0119
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueCharacterOfMul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNormalisedGen
import Development.AutomorphicSpectrum.Statements.GeometryStatements.KeyBadSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0105
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EqZeroOfSmulEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsSecNeObj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
import Development.WeilBound.CoreStatements.SesquilinearFractions.ExistsFactorThroughMultiplication
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0237
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0134
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0039
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LevClauses
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0121
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniformisationOfPoint
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0184
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.ExistsGoodLevel
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.Bundle0002
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0196
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ModelObjectSections

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EqSingleOfIsUnitCoeff
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.UU

open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.TorusMono

open AddMonoidAlgebra (single)
open GlobalTheory.TorusUnit GlobalTheory.BiextTriv

theorem eq_single_of_isUnit_coeff {A X : Type} [CommRing A] [IsReduced A] [AddCommGroup X]
    [TwoUniqueSums X] {u : AddMonoidAlgebra A X} (hu : IsUnit u) {χ : X}
    (hχ : IsUnit (u.coeff χ)) : u = single χ (u.coeff χ) := by
  classical
  have key : ∀ z, z ≠ χ → u.coeff z = 0 := by
    intro z hz
    have hn : u.coeff z ∈ nilradical A := by
      rw [nilradical_eq_sInf]
      refine Ideal.mem_sInf.2 fun {p} hp => ?_
      have : p.IsPrime := hp
      obtain ⟨a, c, -, e⟩ := Semi.Rosenlicht.isUnit_eq_single
        (hu.map (AddMonoidAlgebra.mapRingHom X (Ideal.Quotient.mk p)))
      have ec : ∀ w, Ideal.Quotient.mk p (u.coeff w) = (single a c : AddMonoidAlgebra (A ⧸ p) X).coeff w := by
        intro w
        rw [← e, AddMonoidAlgebra.coeff_mapRingHom]
      have ha : a = χ := by
        by_contra hne
        have h1 := ec χ
        simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg hne] at h1
        exact (hχ.map (Ideal.Quotient.mk p)).ne_zero h1
      have h2 := ec z
      simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg (ha.trans_ne hz.symm)] at h2
      exact Ideal.Quotient.eq_zero_iff_mem.1 h2
    rw [nilradical_eq_zero] at hn
    exact hn
  ext z
  by_cases h : z = χ
  · subst h; simp
  · simp [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, key z h, Ne.symm h]

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {Y : Over S}

def IsMonoNear (ρ : Γ((splitTorus S X ⊗ Y).left, ⊤)) (χ : X) (p : Y.left) : Prop :=
  ∃ (R : CommRingCat.{0}) (y : Spec R ⟶ Y.left), IsOpenImmersion y ∧
    p ∈ Set.range y ∧ ∃ c : R, IsUnit c ∧ (expand y).hom ρ = single χ c

theorem IsMonoNear.residueField {ρ : Γ((splitTorus S X ⊗ Y).left, ⊤)} {χ : X} {p : Y.left}
    (h : IsMonoNear ρ χ p) : ∃ c : Y.left.residueField p, c ≠ 0 ∧
      (expand (Y.left.fromSpecResidueField p)).hom ρ = single χ c := by
  obtain ⟨R, y, hy, hp, c, hc, he⟩ := h
  have H : Set.range (Y.left.fromSpecResidueField p) ⊆ Set.range y := by
    rw [Scheme.range_fromSpecResidueField]; simpa using hp
  obtain ⟨f, hf⟩ : ∃ f, Spec.map f ≫ y = Y.left.fromSpecResidueField p :=
    ⟨Spec.preimage (IsOpenImmersion.lift y _ H), by
      rw [Spec.map_preimage, IsOpenImmersion.lift_fac]⟩
  refine ⟨f.hom c, (hc.map _).ne_zero, ?_⟩
  rw [← hf, expand_map, he]
  simp

theorem IsMonoNear.unique {ρ : Γ((splitTorus S X ⊗ Y).left, ⊤)} {χ χ' : X} {p : Y.left}
    (h : IsMonoNear ρ χ p) (h' : IsMonoNear ρ χ' p) : χ = χ' := by
  classical
  obtain ⟨c, hc, e⟩ := h.residueField
  obtain ⟨c', -, e'⟩ := h'.residueField
  by_contra hne
  have := congrArg (fun f => AddMonoidAlgebra.coeff f χ) (e.symm.trans e')
  simp [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, Ne.symm hne] at this
  exact hc this

theorem exists_isMonoNear [Module.Free ℤ X] [IsReduced Y.left]
    (ρ : Γ((splitTorus S X ⊗ Y).left, ⊤)ˣ) (p : Y.left) : ∃ χ, IsMonoNear ρ.val χ p := by
  have : TwoUniqueSums X := twoUniqueSums_of_free X
  obtain ⟨R, y, hy, q, hq⟩ : ∃ (R : CommRingCat.{0}) (y : Spec R ⟶ Y.left), IsOpenImmersion y ∧
      p ∈ Set.range y :=
    ⟨_, Y.left.affineOpenCover.f (Y.left.affineOpenCover.idx p), inferInstance,
      Y.left.affineOpenCover.covers p⟩
  obtain ⟨χ, hχ⟩ := exists_coeff_notMem (ρ.isUnit.map (expand y).hom) q.asIdeal q.2.ne_top
  set a := ((expand y).hom ρ.val).coeff χ with ha
  let g : R ⟶ CommRingCat.of (Localization.Away a) :=
    CommRingCat.ofHom (algebraMap R (Localization.Away a))
  have hopen : IsOpenImmersion (Spec.map g ≫ y) := inferInstance
  have hred : IsReduced (Spec (CommRingCat.of (Localization.Away a))) :=
    isReduced_of_isOpenImmersion (Spec.map g ≫ y)
  have hred' : _root_.IsReduced (Localization.Away a) :=
    (affine_isReduced_iff (CommRingCat.of (Localization.Away a))).1 hred
  have hcoeff : ((expand (Spec.map g ≫ y)).hom ρ.val).coeff χ = algebraMap R (Localization.Away a) a := by
    rw [expand_map, AddMonoidAlgebra.coeff_mapRingHom]
    rfl
  have hunit : IsUnit (((expand (Spec.map g ≫ y)).hom ρ.val).coeff χ) := by
    rw [hcoeff]
    exact IsLocalization.Away.algebraMap_isUnit a
  refine ⟨χ, _, Spec.map g ≫ y, hopen, ?_, _, hunit,
    eq_single_of_isUnit_coeff (ρ.isUnit.map (expand _).hom) hunit⟩
  have := PrimeSpectrum.localization_away_comap_range (Localization.Away a) a
  obtain ⟨r, hr⟩ : q ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away a))) := by
    rw [this]; exact hχ
  refine ⟨r, ?_⟩
  rw [← hq, ← hr]
  exact Scheme.Hom.comp_apply _ _ _

theorem snd_expand {R : CommRingCat.{0}} (y : Spec R ⟶ Y.left) :
    (snd (splitTorus S X) Y).left.appTop ≫ expand y =
      y.appTop ≫ (Scheme.ΓSpecIso R).hom ≫ const X R := by
  rw [expand, value, ← Scheme.Hom.comp_appTop_assoc, prodPoint_snd, Scheme.Hom.comp_appTop,
    Category.assoc, Scheme.ΓSpecIso_naturality]

theorem eq_char_mul [Module.Free ℤ X] [ConnectedSpace Y.left] [IsReduced Y.left]
    (ρ : Γ((splitTorus S X ⊗ Y).left, ⊤)ˣ) :
    ∃ χ : X, ρ.val = (fst (splitTorus S X) Y).left.appTop.hom (charUnit S X χ).val *
      (snd (splitTorus S X) Y).left.appTop.hom ((unitSec X Y).appTop.hom ρ.val) := by
  choose c hc using exists_isMonoNear (X := X) (Y := Y) ρ
  have hlc : IsLocallyConstant c := by
    rw [IsLocallyConstant.iff_exists_open]
    intro p
    obtain ⟨R, y, hy, hp, he⟩ := hc p
    exact ⟨Set.range y, y.isOpenEmbedding.isOpen_range, hp,
      fun p' hp' => (hc p').unique ⟨R, y, hy, hp', he⟩⟩
  obtain ⟨p₀⟩ : Nonempty Y.left := inferInstance
  refine ⟨c p₀, ext_of_expand fun p => ?_⟩
  obtain ⟨R, y, hy, hp, d, -, he⟩ := hc p
  refine ⟨R, y, hy, hp, ?_⟩
  have e1 := congrArg (fun f => f.hom ρ.val) (expand_aug (X := X) y)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e1
  rw [he, aug_single] at e1
  have e2 := congrArg (fun f => f.hom ((unitSec X Y).appTop.hom ρ.val)) (snd_expand (X := X) y)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e2
  rw [map_mul, e2, ← e1, expand_char, he, hlc.apply_eq_of_preconnectedSpace p p₀]
  simp [const, AddMonoidAlgebra.single_mul_single]

end GlobalTheory.CompanionTheory.TorusMono

open GlobalTheory.CompanionTheory.TorusMono GlobalTheory.BiextTriv in

theorem GlobalTheory.CompanionTheory.TorusMono.torus_unit_eq_char_mul : ∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] [Module.Free ℤ X] (Y : Over S) [ConnectedSpace Y.left] [IsReduced Y.left] (ρ : Γ((splitTorus S X ⊗ Y).left, ⊤)ˣ), ∃ χ : X, ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (y : Z ⟶ Y), (lift t y).left.appTop.hom ρ.val = (chV t χ).val * (lift (1 : Z ⟶ splitTorus S X) y).left.appTop.hom ρ.val := by
  intro S X _ _ Y _ _ ρ
  obtain ⟨χ, hχ⟩ := eq_char_mul ρ
  refine ⟨χ, fun Z t y => ?_⟩
  have c1 : ∀ v, (lift t y).left.appTop.hom ((fst (splitTorus S X) Y).left.appTop.hom v) =
      t.left.appTop.hom v := fun v => by
    have e : (lift t y).left ≫ (fst (splitTorus S X) Y).left = t.left := by
      rw [← Over.comp_left, lift_fst]
    rw [← e, Scheme.Hom.comp_appTop]
    rfl
  have c2 : ∀ v, (lift t y).left.appTop.hom ((snd (splitTorus S X) Y).left.appTop.hom v) =
      y.left.appTop.hom v := fun v => by
    have e : (lift t y).left ≫ (snd (splitTorus S X) Y).left = y.left := by
      rw [← Over.comp_left, lift_snd]
    rw [← e, Scheme.Hom.comp_appTop]
    rfl
  have c3 : y.left.appTop.hom ((unitSec X Y).appTop.hom ρ.val) =
      (lift (1 : Z ⟶ splitTorus S X) y).left.appTop.hom ρ.val := by
    rw [← comp_unitSec, Scheme.Hom.comp_appTop]
    rfl
  conv_lhs => rw [hχ]
  rw [map_mul, c1, c2, c3, chV_val]
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsNonzeroSectionPpData
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.KeyGen GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1 in

theorem exists_sec_ne_zero_int : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L), ∃ t : SecMod D.t.G.hom (LB.LinComb D.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => ((1 : ℕ) : ℤ))), t ≠ 0 := by
  intro E _ _ _ H L _ _ D
  have hS : SecBaseChangeAnySt := GlobalTheory.lawsFieldsSeparately.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have := D.tK.semi.smooth
  have := D.tK.semi.geomConnected
  have : ConnectedSpace D.tK.G.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := D.tK.G.hom) (𝟙 _) (𝟙 _) D.tK.G.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected D.tK.G.hom (eSec D.tK.G (default : PrimeSpectrum L))
  obtain ⟨-, ws, gs', -⟩ := D.tK.sym
  obtain ⟨hprop, hamp, hkt⟩ := D.princ
  have eid : spMap (RingHom.id L) = 𝟙 (Sp L) := by
    simp [spMap]
  have hpb : IsPullback (𝟙 D.tK.G.left) D.tK.G.hom D.tK.G.hom (spMap (RingHom.id L)) := by
    rw [eid]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  obtain ⟨β, hβ⟩ : ∃ β : LB.Sec D.tK.PP.L, ¬ ∀ y j, (𝟙 D.tK.G.left : D.tK.G.left ⟶ D.tK.G.left) y ∈ D.tK.PP.L.U j →
      gs (𝟙 D.tK.G.left) y _ (β.f j) = 0 := exists_sec_ne hS
    { A := D.tK.G, g := d, smoothDim := hd, L := D.tK.PP.L, isLB := D.tK.PP.isLB
      ample := hamp
      ktriv := hkt
      isAb := ⟨inferInstance, inferInstance, hprop, ‹_›⟩
      rigid := ⟨D.tK.PP.rig, D.tK.PP.rigGen⟩
      sym := fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩ } (RingHom.id L) hpb
  obtain ⟨w, gw', -⟩ := D.m.lin
  have := D.t.semi.separated
  have := D.t.semi.quasiCompact
  have : CompactSpace D.t.G.left := QuasiCompact.compactSpace_of_compactSpace D.t.G.hom
  obtain ⟨a, ha, σ, hσ⟩ := exists_extend (nonZeroDivisors (𝓞 L)) D.m.cart.1 D.t.PP.isLB D.tK.PP.isLB
    ((isGen_iff w).1 gw') β
  obtain ⟨w₁, hw₁⟩ := exists_iso_linComb (F := 𝟙 D.t.G.left) D.t.PP.isLB (K := Fin 1) (fun _ => 𝟙 _)
    (fun _ => ((1 : ℕ) : ℤ)) (fun U _ k => by simp)
  have hM := linComb_isLB D.t.PP.L D.t.PP.isLB (K := Fin 1) (fun _ => 𝟙 D.t.G.left) (fun _ => ((1 : ℕ) : ℤ))
  obtain ⟨τ, hτ⟩ := sec_pull_down ((isGen_iff w₁).1 hw₁) D.t.PP.isLB hM σ
  refine ⟨τ, fun h0 => hβ fun y k hk => ?_⟩
  obtain ⟨j, hj⟩ := exists_chart D.t.PP.isLB (D.m.φ y)
  obtain ⟨k', hk'⟩ := exists_chart hM (D.m.φ y)
  have hz : LB.Sec.f τ k' = 0 := congrArg (fun s : SecMod D.t.G.hom (LB.LinComb D.t.PP.L (K := Fin 1) (fun _ => 𝟙 _)
    (fun _ => ((1 : ℕ) : ℤ))) => LB.Sec.f s k') h0
  have e₁ := hτ _ D.m.φ y j k' hj hk'
  rw [hz, gs_zero _ y _ hk', mul_zero, Category.comp_id] at e₁
  have e₂ := hσ y j k hj hk
  rw [e₁, D.m.cart.1.w, cst_comp] at e₂
  have ha' : algebraMap (𝓞 L) L a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 L) L)).2 (nonZeroDivisors.ne_zero ha)
  have u₁ : IsUnit (cst D.tK.G.hom y (algebraMap (𝓞 L) L a)) :=
    IsUnit.of_mul_eq_one (cst D.tK.G.hom y (algebraMap (𝓞 L) L a)⁻¹) (by
      rw [← cst_mul, mul_inv_cancel₀ ha', cst_one])
  exact (Units.isUnit _).mul_right_eq_zero.1 (u₁.mul_right_eq_zero.1 e₂.symm)

end GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsNthRootHomomorphism
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.exists_nth_root_homomorphism : ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (n : ℕ) (A B : Out.PolAV (Sp (𝓞 K))) (f : A.A ⟶ B.A), IsMonHom f → 0 < n → (∀ x : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ A.A, x ^ n = 1 → x ≫ f = 1) → ∃ f' : A.A ⟶ B.A, IsMonHom f' ∧ f' ^ n = f := by
  first | exact @PositivityTheory.Xgf.exists_nth_root_homomorphism | exact PositivityTheory.Xgf.exists_nth_root_homomorphism
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricallyConnectedDescendsToFinitelyGenerateStatement
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj
theorem _root_.GlobalTheory.T.geometricallyConnected_descends_to_finitelyGenerated : ∀ (k V : Type) [CommRing k] [IsNoetherianRing k] [CommRing V] [Algebra k V] (G : Over (Sp k)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → IsProper G.hom → GeometricallyConnected (pullback.snd G.hom (spMap (algebraMap k V))) → ∃ R : Subalgebra k V, R.FG ∧ GeometricallyConnected (pullback.snd G.hom (spMap (algebraMap k R))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Approx.geometricallyConnected_descends_to_fg | exact GlobalTheory.CompanionTheory.Ar.Approx.geometricallyConnected_descends_to_fg | (intros; apply GlobalTheory.CompanionTheory.Ar.Approx.geometricallyConnected_descends_to_fg <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolUnifPeriodMatrixLeft
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.QuotLoc

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.Flat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem isHolTo_fibreSlice {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
    [NormedSpace ℂ W] {X : Scheme.{0}} {B : Set V} {y : V × W → (Sp ℂ ⟶ X)} (h : IsHolTo (B ×ˢ Set.univ) y)
    {b : V} (hb : b ∈ B) : IsHolTo Set.univ (fun z => y (b, z)) := by
  intro U f
  have hc : Differentiable ℂ (fun z : W => (b, z)) := by fun_prop
  refine ⟨?_, (h U f).2.comp hc.differentiableOn fun z hz => ⟨⟨hb, trivial⟩, hz.2⟩⟩
  convert (h U f).1.preimage hc.continuous using 1
  ext z
  exact ⟨fun hz => ⟨⟨hb, trivial⟩, hz.2⟩, fun hz => ⟨trivial, hz.2⟩⟩

theorem tangent_of_isGrpPullback {tB : SAB H (Sp ℂ)} (A : Over (Sp ℂ)) [GrpObj A] (φ : A.left ⟶ tB.G.left)
    (hφ : IsGrpPullback A tB.G (𝟙 _) φ) (hP : IsPrincipal tB) {g : ℕ} (u : HolUnif A (tB.PP.L.pull φ) g)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (hu : u.IsAH Hm χ) :
    IsAbelianScheme A ∧ (∀ v, IsTangent v → ∃! w, u.IsDiff w v) ∧ (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) := by
  have := tB.semi.smooth
  have := tB.semi.geomConnected
  have hAb : IsAbelianScheme tB.G := ⟨tB.semi.comm, tB.semi.smooth, hP.1, tB.semi.geomConnected⟩
  have hA : IsAbelianScheme A := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hAb hφ
  have : ConnectedSpace tB.G.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := tB.G.hom) (𝟙 _) (𝟙 _) tB.G.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected tB.G.hom (eSec tB.G (default : PrimeSpectrum ℂ))
  obtain ⟨-, ws, gs', -⟩ := tB.sym
  have hL' := pull_isLB tB.PP.isLB φ
  have hw := (isGen_iff _).1 (idIso_isGen hL')
  let Q : Out.PolAV (Sp ℂ) :=
    { A := A, isAb := hA, g := d
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hφ.1 hd
      L := tB.PP.L.pull φ, isLB := hL'
      rigid := GlobalTheory.PolBaseChange.rigidified_pull hφ ⟨tB.PP.rig, tB.PP.rigGen⟩
      sym := GlobalTheory.PolBaseChange.sym_pull hφ fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩
      ample := relAmple_pull hφ.1 tB.PP.isLB hL' hw ⊤ (isAffineOpen_top _) (fun _ => trivial) hP.2.1
      ktriv := kTriv_pull hφ tB.PP.isLB hL' hw hP.2.2 }
  obtain ⟨-, -, -, -, h₁, h₂, -⟩ := GlobalTheory.AHWeil.tangent_and_weil_of_isAH GlobalTheory.thetaUnifAV_all Q g u Hm χ hu
  exact ⟨hA, h₁, h₂⟩

theorem exists_isAbLift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (t : SAB H (Sp R)) (g n : ℕ) (M : LieModel t.G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : Flat.FamExp t.G M B ψ) (b : Fin n → ℂ) (P : AbPart t (spMap (ψ b))) (A : Over (Sp ℂ)) (_ : GrpObj A) (φ : A.left ⟶ P.tB.G.left) (g' : ℕ) (u : HolUnif A (P.tB.PP.L.pull φ) g') (Hm : Matrix (Fin g') (Fin g') ℂ) (χ : u.Λ → ℂ), b ∈ B → IsGrpPullback A P.tB.G (𝟙 _) φ → u.IsAH Hm χ → IsPrincipal P.tB → ∃ ℓ : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ), GlobalTheory.CompanionTheory.Ar.QuotLoc.IsAbLift e b P φ u ℓ := by
  intro E _ _ _ H R _ t g n M B ψ e b P A _ φ g' u Hm χ hb hφ hu hP
  obtain ⟨hA, h₁, h₂⟩ := tangent_of_isGrpPullback A φ hφ hP u Hm χ hu
  obtain ⟨p, hp⟩ := GlobalTheory.CMSpreadCompare.exists_pointEquiv P.m.cart (𝟙_ _) (s := spMap (ψ b)) (Category.id_comp _).symm
  obtain ⟨c, hc⟩ := GlobalTheory.CMSpreadCompare.exists_pointEquiv hφ (𝟙_ _) (s := 𝟙 _) (Category.comp_id _).symm
  letI := P.τ.grpB
  haveI : IsMonHom P.τ.q := P.τ.q_hom
  haveI : IsMonHom P.e.hom := P.e_hom
  let r : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.tB.G) := fun y => p.symm (e.ex b y) ≫ P.τ.q ≫ P.e.hom
  let G : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ A) := fun y => c.symm (r y)
  have hr : ∀ z w, r (z + w) = r z * r w := fun z w => by
    simp only [r, e.add b hb, map_mul, MonObj.mul_comp]
  have hG : ∀ z w, G (z + w) = G z * G w := fun z w => by
    simp only [G, hr, map_mul]
  have hGr : ∀ y, (G y).left ≫ φ = (r y).left := fun y => by
    rw [← hc, c.apply_symm_apply]
  have hs : IsHolTo Set.univ (fun y => (p.symm (e.ex b y)).left) := by
    refine GlobalTheory.HolFibre.isHolTo_of_isPullback P.m.cart.1 ?_ ?_
    · have h := isHolTo_fibreSlice e.hol hb
      have e₁ : (fun y => (p.symm (e.ex b y)).left ≫ P.m.cm.F) = fun y => (e.ex b y).left :=
        funext fun y => by rw [← hp, p.apply_symm_apply]
      rw [e₁]
      exact h
    · have e₁ : (fun y => (p.symm (e.ex b y)).left ≫ P.tK.G.hom) = fun _ => 𝟙 (Sp ℂ) :=
        funext fun y => Over.w (p.symm (e.ex b y))
      rw [e₁]
      exact GlobalTheory.HolFibre.isHolTo_const isOpen_univ _
  have hol : IsHolTo (Set.univ : Set (Fin g → ℂ)) (fun z => (G z).left) := by
    refine GlobalTheory.HolFibre.isHolTo_of_isPullback hφ.1 ?_ ?_
    · have h := GlobalTheory.CMSpreadCompare.isHolTo_postcomp hs (P.τ.q ≫ P.e.hom).left
      have e₁ : (fun y => (G y).left ≫ φ) = fun y => (p.symm (e.ex b y)).left ≫ (P.τ.q ≫ P.e.hom).left :=
        funext fun y => by rw [hGr]; rfl
      rw [e₁]
      exact h
    · have e₁ : (fun y => (G y).left ≫ A.hom) = fun _ => 𝟙 (Sp ℂ) := funext fun y => Over.w (G y)
      rw [e₁]
      exact GlobalTheory.HolFibre.isHolTo_const isOpen_univ _
  obtain ⟨F, hF, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo A hA _ g' g u h₁ h₂ G hG hol
  refine ⟨F, fun y s hs' => ?_⟩
  have es : s = p.symm (e.ex b y) := by
    rw [eq_comm, MulEquiv.symm_apply_eq]
    exact Over.OverMorphism.ext ((hp s).trans hs').symm
  rw [hF, hGr, es]

end GlobalTheory.CompanionTheory.Ar.QuotLoc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrincipalLieMultiplicityType
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.SabModel

theorem obj_of_sections : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (F : IntermediateField ℚ ℂ) (hK : KA l ≤ F) (t : SAB H (Sp F)), IsPrincipal t → l.A = 1 → (∀ (k : Type) [Field k] [IsAlgClosed k] (g : F →+* k) (τ : 𝓞 E →+* k), (τ H.rt = g (IntermediateField.inclusion hK (baseKA l).ρ) → LieMult t.act (spMap g) τ D.p) ∧ (τ H.rt ≠ g (IntermediateField.inclusion hK (baseKA l).ρ) → LieMult t.act (spMap g) τ D.q)) → ∀ I : TateIso D ℂ (Over.mk (spMap (algebraMap F ℂ)) ⟶ t.G) (fun a g => g ≫ t.act.act a) (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c)), (∀ a : D.La, ∃ s : 𝟙_ (Over (Sp F)) ⟶ t.G, toUnit _ ≫ s = I.ev l.M a) → ∃ o : Obj D l (baseKA l) (spMap (IntermediateField.inclusion hK).toRingHom), o.t = t :=
  @PositivityTheory.Xgn.model_object_sections

end GlobalTheory.CompanionTheory.Ar.SabModel
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionPointsNumberFieldStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_points_number_field : ∀ (L : Type) [Field L] [NumberField L] (σ : L →+* ℂ) (P : Out.PolAV (Sp L)) (n : ℕ), 0 < n → ∃ (F : IntermediateField ℚ ℂ) (_ : FiniteDimensional ℚ F) (e : L →+* F), (∀ x, ((e x : F) : ℂ) = σ x) ∧ ∀ x : Over.mk (spMap σ) ⟶ P.A, x ^ n = 1 → ∃ y : Sp F ⟶ P.A.left, y ≫ P.A.hom = spMap e ∧ spMap (algebraMap F ℂ) ≫ y = x.left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.torsion_defined_over_numberField | exact GlobalTheory.CompanionTheory.Ar.torsion_defined_over_numberField | (intros; apply GlobalTheory.CompanionTheory.Ar.torsion_defined_over_numberField <;> assumption)
end

