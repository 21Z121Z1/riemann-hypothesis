import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversallyClosedOfIsClosedRange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothGrpSchemeDescendsToFgSubring
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeSubsetAbelianLocusOfGoodReduction
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0033
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0005
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.QuasiCompactIffLocallyOfFinitePresentation
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0009
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0055
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhiskerLeftIsOpenImmersionRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1009
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1012
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0125
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicTransvectionSubgroupEqAdelesClosed
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0982
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedEigenvaluesClasses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0983
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0978
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescendsToFinitelyGeneratedSubring
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.AbelianLimit

open RationalPoint in

theorem connectedSpace_of_surjective_pow {k : Type} [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G]
    [IsCommMonObj G] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    (h : ∀ n : ℕ, 1 ≤ n → Surjective ((𝟙 G) ^ n : G ⟶ G).left) : ConnectedSpace G.left := by
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have : IsNoetherian G.left := {}
  have key (f : G ⟶ G) {x y : 𝟙_ (Over (Sp k)) ⟶ G} (hx : pt x ∈ connectedComponent (pt y)) :
      pt (x ≫ f) ∈ connectedComponent (pt (y ≫ f)) :=
    f.left.continuous.image_connectedComponent_subset (pt y) ⟨_, hx, rfl⟩
  have tr (x z : 𝟙_ (Over (Sp k)) ⟶ G) : x ≫ (𝟙 G * (toUnit G ≫ z)) = x * z := by
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, toUnit_unique (x ≫ toUnit G) (𝟙 _), Category.id_comp]
  have key' (z : 𝟙_ (Over (Sp k)) ⟶ G) {x y : 𝟙_ (Over (Sp k)) ⟶ G} (hx : pt x ∈ connectedComponent (pt y)) :
      pt (x * z) ∈ connectedComponent (pt (y * z)) := by
    simpa only [tr] using key (𝟙 G * (toUnit G ≫ z)) hx
  let H : Subgroup (𝟙_ (Over (Sp k)) ⟶ G) :=
    { carrier := {x | pt x ∈ connectedComponent (pt (1 : 𝟙_ (Over (Sp k)) ⟶ G))}
      one_mem' := mem_connectedComponent
      mul_mem' := fun {x y} hx hy => by
        have := key' y hx
        rw [_root_.one_mul, ← connectedComponent_eq hy] at this
        exact this
      inv_mem' := fun {x} hx => by
        have := key (𝟙 G)⁻¹ hx
        rwa [GrpObj.comp_inv, GrpObj.comp_inv, Category.comp_id, Category.comp_id, inv_one] at this }
  have : H.Normal := ⟨fun x hx g => by rwa [_root_.mul_comm g x, mul_inv_cancel_right]⟩
  have : DiscreteTopology (_root_.ConnectedComponents G.left) :=
    ConnectedComponents.discreteTopology_iff.2 isOpen_connectedComponent_of_noetherianSpace
  have : Finite (_root_.ConnectedComponents G.left) := finite_of_compact_of_discrete
  have : Finite ((𝟙_ (Over (Sp k)) ⟶ G) ⧸ H) := by
    refine Finite.of_injective (fun q => ConnectedComponents.mk (pt q.out)) fun q q' e => ?_
    rw [← q.out_eq, ← q'.out_eq]
    refine QuotientGroup.eq.2 ?_
    have := key' q.out⁻¹ (ConnectedComponents.coe_eq_coe'.1 e.symm)
    rwa [mul_inv_cancel, _root_.mul_comm] at this
  have : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have all (x : 𝟙_ (Over (Sp k)) ⟶ G) : x ∈ H := by
    have := h H.index (Nat.one_le_iff_ne_zero.2 Subgroup.FiniteIndex.index_ne_zero)
    obtain ⟨z, hz⟩ := ((𝟙 G) ^ H.index : G ⟶ G).left.surjective (pt x)
    obtain ⟨y, -, rfl⟩ := (pt_mem_image_iff ((𝟙 G) ^ H.index) isClosed_univ x).1 ⟨z, trivial, hz⟩
    rw [MonObj.comp_pow, Category.comp_id]
    exact H.pow_index_mem y
  have hu : connectedComponent (pt (1 : 𝟙_ (Over (Sp k)) ⟶ G)) = Set.univ := by
    by_contra hne
    obtain ⟨x, hx⟩ := exists_pt_mem (isOpen_connectedComponent_of_noetherianSpace _).isClosed_compl
      (Set.nonempty_compl.2 hne)
    exact hx (all x)
  exact connectedSpace_iff_connectedComponent.2 ⟨_, hu⟩

theorem pow_comm {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (n : ℕ) :
    ((𝟙 G') ^ n : G' ⟶ G').left ≫ φ = φ ≫ ((𝟙 G) ^ n : G ⟶ G).left := by
  have e := congrArg (fun q => q.left) (map_pow (pushHom h G') (𝟙 G') n)
  have e' (x : Over.mk (G'.hom ≫ f) ⟶ G) : x ^ n = x ≫ (𝟙 G) ^ n := by
    rw [MonObj.comp_pow, Category.comp_id]
  rw [e'] at e
  refine Eq.trans e ?_
  change (𝟙 _ ≫ φ) ≫ _ = _
  rw [Category.id_comp]

theorem isPullback_pow {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (n : ℕ) :
    IsPullback φ ((𝟙 G') ^ n : G' ⟶ G').left ((𝟙 G) ^ n : G ⟶ G).left φ := by
  refine IsPullback.of_bot ?_ (pow_comm h n).symm h.1
  rw [Over.w, Over.w]
  exact h.1

theorem surjective_pow {S : Scheme.{0}} (A : Over S) [GrpObj A] (hA : IsAbelianScheme A) (n : ℕ) (hn : 1 ≤ n) :
    Surjective ((𝟙 A) ^ n : A ⟶ A).left := by
  refine ⟨fun x => ?_⟩
  have := hA.comm
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  let K := AlgebraicClosure (S.residueField (A.hom x))
  let t : Sp K ⟶ S := spMap (algebraMap (S.residueField (A.hom x)) K) ≫ S.fromSpecResidueField (A.hom x)
  have ht : A.hom x = t (IsLocalRing.closedPoint K) := by
    exact (Scheme.fromSpecResidueField_apply _ _).symm
  let B := (Over.pullback t).obj A
  have hB : IsAbelianScheme B :=
    { comm := inferInstance
      smooth := inferInstanceAs (Smooth (pullback.snd A.hom t))
      proper := inferInstanceAs (IsProper (pullback.snd A.hom t))
      geomConnected := inferInstanceAs (GeometricallyConnected (pullback.snd A.hom t)) }
  have hm : IsMonHom ((𝟙 B) ^ n : B ⟶ B) := by
    have := hB.comm
    clear hn
    induction n with
    | zero => rw [pow_zero]; exact inferInstanceAs (IsMonHom (toUnit B ≫ η[B]))
    | succ n ih => rw [pow_succ]; exact inferInstanceAs (IsMonHom (lift ((𝟙 B) ^ n) (𝟙 B) ≫ μ[B]))
  have hs := (flat_and_surjective_of_isFinite_abelianEnd
    (fun _ _ f _ _ => (geometricallyIntegral_of_smooth_of_geometricallyConnected.1 f).1) K B hB ((𝟙 B) ^ n)
    hm (MulFiniteAny.isFinite_mulA K B hB n hn)).2
  obtain ⟨y, hy, -⟩ := Scheme.exists_preimage_of_isPullback (.of_hasPullback A.hom t) x _ ht
  obtain ⟨z, rfl⟩ := ((𝟙 B) ^ n : B ⟶ B).left.surjective y
  exact ⟨pullback.fst A.hom t z, (congrArg (fun g => g z) (pow_comm (isGrpPullback_pullback A t) n)).symm.trans hy⟩

theorem isAbelianScheme_of_isDominant {S S' : Scheme.{0}} {B : Over S} {A : Over S'} [GrpObj B] [GrpObj A]
    [IsCommMonObj B] [Smooth B.hom] [IsProper B.hom] {f : S' ⟶ S} [IsDominant f] {φ : A.left ⟶ B.left}
    (h : IsGrpPullback A B f φ) (hA : IsAbelianScheme A) : IsAbelianScheme B := by
  have hd : DenseRange φ := by
    rw [DenseRange, ProperLimit.range_eq_of_isPullback h.1.flip]
    exact f.denseRange.preimage B.hom.isOpenMap
  have hs (n : ℕ) (hn : 1 ≤ n) : Surjective ((𝟙 B) ^ n : B ⟶ B).left := by
    have := surjective_pow A hA n hn
    have : IsProper (((𝟙 B) ^ n : B ⟶ B).left ≫ B.hom) := by rw [Over.w]; infer_instance
    have : IsProper ((𝟙 B) ^ n : B ⟶ B).left := IsProper.of_comp _ B.hom
    refine ⟨Set.range_eq_univ.1 ?_⟩
    rw [← ((𝟙 B) ^ n : B ⟶ B).left.isClosedMap.isClosed_range.closure_eq]
    refine (Dense.mono ?_ hd).closure_eq
    rintro _ ⟨y, rfl⟩
    obtain ⟨z, rfl⟩ := ((𝟙 A) ^ n : A ⟶ A).left.surjective y
    exact ⟨φ z, (congrArg (fun g => g z) (pow_comm h n)).symm⟩
  refine ⟨‹_›, ‹_›, ‹_›, SemiAbelianCompare.geometricallyConnected_of_isAlgClosed _ fun k _ _ s => ?_⟩
  have : LocallyOfFiniteType ((Over.pullback s).obj B).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd B.hom s))
  have : QuasiCompact ((Over.pullback s).obj B).hom := inferInstanceAs (QuasiCompact (pullback.snd B.hom s))
  exact connectedSpace_of_surjective_pow ((Over.pullback s).obj B) fun n hn =>
    MorphismProperty.of_isPullback (isPullback_pow (isGrpPullback_pullback B s) n) (hs n hn)

theorem abelianScheme_descends_to_fg_subring :
    ∀ (R : Type) [CommRing R] (g : ℕ) (A : Over (Sp R)) [GrpObj A] (F : Finset R), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∃ (S : Subring R) (B : Over (Sp S)) (_ : GrpObj B) (φ : A.left ⟶ B.left), (F : Set R) ⊆ S ∧ Algebra.FiniteType ℤ S ∧
      IsAbelianScheme B ∧ SmoothOfRelativeDimension g B.hom ∧ IsGrpPullback A B (spMap S.subtype) φ := by
  intro R _ g A _ F hA hg
  have := hA.comm
  have := hA.proper
  obtain ⟨k, A₀, _, _, φ₀, hF, hk, _, _, _, h₀⟩ :=
    smooth_grpScheme_descends_to_fg_subring R A F hA.smooth inferInstance inferInstance
  have : IsNoetherianRing k := Algebra.FiniteType.isNoetherianRing ℤ k
  have h₁ : IsPullback φ₀ A.hom A₀.hom (spMap (algebraMap k R)) := h₀.1
  have : UniversallyClosed (pullback.snd A₀.hom (spMap (algebraMap k R))) := by
    rw [← h₁.isoPullback_inv_snd]
    infer_instance
  obtain ⟨s, hs⟩ := ProperLimit.exists_finset_isProper k R A₀.hom
  let S : Subalgebra k R := Algebra.adjoin k (s : Set R)
  let t : Sp S.toSubring ⟶ Sp k := spMap (algebraMap k S)
  have e : spMap S.toSubring.subtype ≫ t = spMap k.subtype := Spread.spMap_algHom_comp S.val
  obtain ⟨φ, hφ⟩ := GoodVal.exists_isGrpPullback_of_comp A₀ t (spMap S.toSubring.subtype) (e ▸ h₀)
  have hsm : Smooth ((Over.pullback t).obj A₀).hom := inferInstanceAs (Smooth (pullback.snd A₀.hom t))
  have : IsProper ((Over.pullback t).obj A₀).hom := hs
  have hd : IsDominant (spMap S.toSubring.subtype) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical S.toSubring.subtype).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 Subtype.val_injective]
      exact bot_le)⟩
  exact ⟨S.toSubring, (Over.pullback t).obj A₀, inferInstance, φ, fun x hx => S.algebraMap_mem ⟨x, hF hx⟩,
    SpreadGroup.finiteType_of_fg hk (Subalgebra.fg_adjoin_finset s), isAbelianScheme_of_isDominant hφ hA,
    smoothOfRelativeDimension_of_isPullback_isDominant _ _ _ _ _ _ _ _ g hφ.1 hd hsm hg, hφ⟩

end GlobalTheory.AbelianLimit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditivePicClassOfLocallyAdditive
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue

variable {S : Scheme.{0}}

theorem pull_pull_over {X Y Z : Over S} (u : Z ⟶ Y) (v : Y ⟶ X) (c : Pic X.left) :
    CechPic.pull u.left (CechPic.pull v.left c) = CechPic.pull (u ≫ v).left c := by
  rw [Over.comp_left, pull_comp]

def addDefect (A T : Over S) [GrpObj A] (c : Pic (A ⊗ T).left) : Pic (A ⊗ (A ⊗ T)).left :=
  CechPic.pull (lift (fst A (A ⊗ T) * (snd A (A ⊗ T) ≫ fst A T)) (snd A (A ⊗ T) ≫ snd A T)).left c -
    CechPic.pull (lift (fst A (A ⊗ T)) (snd A (A ⊗ T) ≫ snd A T)).left c -
    CechPic.pull (lift (snd A (A ⊗ T) ≫ fst A T) (snd A (A ⊗ T) ≫ snd A T)).left c

theorem pull_addDefect (A T : Over S) [GrpObj A] (c : Pic (A ⊗ T).left) {Z : Over S} (u : Z ⟶ A ⊗ (A ⊗ T)) :
    CechPic.pull u.left (addDefect A T c) =
      CechPic.pull (lift ((u ≫ fst _ _) * (u ≫ snd _ _ ≫ fst _ _)) (u ≫ snd _ _ ≫ snd _ _)).left c -
      CechPic.pull (lift (u ≫ fst _ _) (u ≫ snd _ _ ≫ snd _ _)).left c -
      CechPic.pull (lift (u ≫ snd _ _ ≫ fst _ _) (u ≫ snd _ _ ≫ snd _ _)).left c := by
  simp only [addDefect, map_sub, pull_pull_over, comp_lift, MonObj.comp_mul]

theorem addCls_of_locally : ∀ (S : Scheme.{0}) (A T : Over S) [GrpObj A], IsAbelianScheme A →
    ∀ c : Pic (A ⊗ T).left, GlobalTheory.CechPic.pull (lift (1 : T ⟶ A) (𝟙 T)).left c = 0 →
    (∀ p : T.left, ∃ (Z : Over S) (z : Z ⟶ T), IsOpenImmersion z.left ∧ p ∈ Set.range z.left ∧
      AddCls A (GlobalTheory.CechPic.pull (A ◁ z).left c)) → AddCls A c := by
  intro S A T _ hA c h0 hloc
  have hd : addDefect A T c = 0 := by
    refine GlobalTheory.T.rigidified_picard_class_zero_of_locally_zero S A (A ⊗ T) hA _ ?_ fun p ↦ ?_
    · rw [pull_addDefect]
      have h1 : lift (1 : A ⊗ T ⟶ A) (snd A T) = snd A T ≫ lift (1 : T ⟶ A) (𝟙 T) := by
        rw [comp_lift, MonObj.comp_one, Category.comp_id]
      simp only [lift_fst, lift_snd_assoc, Category.id_comp, _root_.one_mul]
      rw [h1, ← pull_pull_over, h0, map_zero, sub_zero, sub_self]
    · obtain ⟨Z, z, hz, hp, hadd⟩ := hloc ((snd A T).left p)
      obtain ⟨ho, hr⟩ := GlobalTheory.whiskerLeft_isOpenImmersion_range S A T Z z hz
      refine ⟨A ⊗ Z, A ◁ z, ho, (hr p).2 hp, ?_⟩
      have h2 := hadd (A ⊗ (A ⊗ Z)) (fst _ _) (snd _ _ ≫ fst _ _) (snd _ _ ≫ snd _ _)
      simp only [pull_pull_over, lift_whiskerLeft, Category.assoc] at h2
      rw [pull_addDefect]
      simp only [whiskerLeft_fst, whiskerLeft_snd_assoc, whiskerLeft_snd]
      rw [h2]
      abel
  intro Z a a' t
  have h3 := pull_addDefect A T c (lift a (lift a' t))
  rw [hd, map_zero] at h3
  simp only [lift_fst, lift_snd_assoc, lift_snd] at h3
  rw [sub_sub] at h3
  exact sub_eq_zero.1 h3.symm

end GlobalTheory.PicGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHaarMeasureScaling
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKCx

theorem herm_laws : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ), sh G β = β →
    (∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) → (herm G v β).IsHermitian ∧ (herm G v β).det ≠ 0 ∧
      ∃ Z : GL (Fin G.n) ℂ, herm G v β =
        (Z : Matrix (Fin G.n) (Fin G.n) ℂ)ᴴ * G.gram v * (Z : Matrix (Fin G.n) (Fin G.n) ℂ) := by
  intro p _ G v β _ hR
  obtain ⟨z, hz⟩ := hR
  have hc : ∃ Z : GL (Fin G.n) ℂ, herm G v β =
      (Z : Matrix (Fin G.n) (Fin G.n) ℂ)ᴴ * G.gram v * (Z : Matrix (Fin G.n) (Fin G.n) ℂ) := by
    refine ⟨Units.map (G.psiR v).toMonoidHom z, ?_⟩
    set Zm : Matrix (Fin G.n) (Fin G.n) ℂ := G.psiR v (z : ℝ ⊗[ℚ] G.C) with hZm
    change G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C) = Zmᴴ * G.gram v * Zm
    have hb : G.psiR v (inC G ℝ (β : G.C)) = G.psi v (β : G.C) := by
      change G.psiR v ((1 : ℝ) ⊗ₜ (β : G.C)) = _
      rw [psiR_tmul, one_smul]
    have h1 := congrArg (G.psiR v) hz
    rw [map_mul, map_mul, psiR_starT, hb] at h1
    simp only [Units.val_one, map_one] at h1
    rw [← hZm] at h1
    have hg : IsUnit (G.gram v).det := isUnit_iff_ne_zero.2 (G.gram_det v)
    set M := G.psi v ((β⁻¹ : G.Cˣ) : G.C)
    have hMb : M * G.psi v (β : G.C) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have h2 : G.psi v (β : G.C) * ((G.gram v)⁻¹ * Zmᴴ * G.gram v * Zm) = 1 := by
      have := mul_eq_one_comm.1 (by simpa [Matrix.mul_assoc] using h1 :
        Zm * (G.psi v (β : G.C) * ((G.gram v)⁻¹ * Zmᴴ * G.gram v)) = 1)
      simpa [Matrix.mul_assoc] using this
    have h3 : M = (G.gram v)⁻¹ * Zmᴴ * G.gram v * Zm := by
      calc M = M * (G.psi v (β : G.C) * ((G.gram v)⁻¹ * Zmᴴ * G.gram v * Zm)) := by rw [h2, Matrix.mul_one]
        _ = _ := by rw [← Matrix.mul_assoc, hMb, Matrix.one_mul]
    rw [h3]
    simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hg, Matrix.one_mul]
  obtain ⟨Z, hZ⟩ := hc
  refine ⟨?_, ?_, Z, hZ⟩
  · rw [hZ]
    exact isHermitian_conjTranspose_mul_mul _ (G.gram_herm v)
  · rw [hZ, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]
    have hZd : (Z : Matrix (Fin G.n) (Fin G.n) ℂ).det ≠ 0 := (Matrix.isUnit_det_of_left_inverse
      (show ((Z⁻¹ : GL (Fin G.n) ℂ) : Matrix (Fin G.n) (Fin G.n) ℂ) * Z = 1 by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one])).ne_zero
    exact mul_ne_zero (mul_ne_zero (star_ne_zero.2 hZd) (G.gram_det v)) hZd

end GlobalTheory.LKCx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicModuleNormRationalUnitEqOne
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

open MeasureTheory

namespace GlobalTheory.NormModule

theorem norm_inclR (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (z : E) :
    Algebra.norm (AF F) (inclR (F := F) (AF F) z : AE F E) = algebraMap F (AF F) (Algebra.norm F z) := by
  have e : (inclR (F := F) (AF F) z : AE F E) = (1 : AF F) ⊗ₜ[F] z := rfl
  rw [e, Algebra.norm_apply, Algebra.norm_apply, ← Algebra.baseChange_lmul, LinearMap.det_baseChange]

theorem modu_rat (F : Type) [Field F] [NumberField F] (w : (AF F)ˣ) (t : F) (hw : (w : AF F) = algebraMap F (AF F) t) :
    distribHaarChar (AdeleRing (𝓞 F) F) w = 1 := by
  haveI : Nontrivial (AF F) :=
    nontrivial_of_ne 0 1 (fun h => zero_ne_one (congrArg (fun a : AF F => a.1) h))
  have ht : t ≠ 0 := by
    rintro rfl
    rw [map_zero] at hw
    exact not_isUnit_zero (hw ▸ w.isUnit)
  obtain ⟨ν, hν⟩ := GlobalTheory.SWQ.exists_adeles_haarMeasure_covolume_one F
  haveI := hν.1
  have h1 := GlobalTheory.SWQ.modrat_main F 0 ν hν t ht
  have h2 := GlobalTheory.SWQ.map_unit_mul_eq F ν w
  have e : (fun x : AF F => w • x) = fun x => algebraMap F (AF F) t * x := by
    funext x; rw [Units.smul_def, smul_eq_mul, hw]
  rw [e, h1] at h2
  obtain ⟨K, hKc, hK0⟩ : ∃ K : Set (AF F), IsCompact K ∧ K ∈ nhds (0 : AF F) := exists_compact_mem_nhds 0
  have h3 := congrArg (fun m : Measure (AF F) => m K) h2
  simp only [Measure.smul_apply, smul_eq_mul] at h3
  have h4 : ((distribHaarChar (AF F) w⁻¹ : NNReal) : ENNReal) = 1 :=
    ((ENNReal.mul_left_inj (Measure.measure_pos_of_mem_nhds ν hK0).ne' hKc.measure_lt_top.ne).1
      (h3.symm.trans (one_mul _).symm))
  have h5 : distribHaarChar (AF F) w⁻¹ = 1 := by exact_mod_cast h4
  rw [map_inv, inv_eq_one] at h5
  exact h5

end GlobalTheory.NormModule

theorem GlobalTheory.NormModule.modu_norm_rat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (u : (AE F E)ˣ) (z : E), (u : AE F E) = inclR (AF F) z → (adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F) u) = 1 := by
  intro F E _ _ _ _ _ u z hu
  apply GlobalTheory.NormModule.modu_rat F _ (Algebra.norm F z)
  rw [Units.coe_map, hu, GlobalTheory.NormModule.norm_inclR]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMem
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

noncomputable section

open scoped Classical

namespace GlobalTheory.SchwartzTranslate

variable (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]

def transl (a : κ → AdeleRing (𝓞 F) F) : ((κ → AdeleRing (𝓞 F) F) → ℂ) →ₗ[ℂ] ((κ → AdeleRing (𝓞 F) F) → ℂ) where
  toFun φ x := φ (x + a)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem SB_translate {X : Type} [TopologicalSpace X] [AddGroup X] [IsTopologicalAddGroup X] (b : X) {g : X → ℂ}
    (hg : g ∈ SB X) : (fun y => g (y + b)) ∈ SB X :=
  ⟨hg.1.comp_continuous (continuous_add_const b), hg.2.comp_homeomorph (Homeomorph.addRight b)⟩

theorem pureA_translate (a : κ → AdeleRing (𝓞 F) F) (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    transl F a (pureA F f g) = pureA F (f.compSubConstCLM ℂ (-fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (a i).1))
      (fun y => g (y + fun i => (a i).2)) := by
  funext x
  simp only [transl, LinearMap.coe_mk, AddHom.coe_mk, pureA, SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add]
  congr 2
  funext i
  exact map_add _ _ _

theorem schA_translate (a : κ → AdeleRing (𝓞 F) F) {φ : (κ → AdeleRing (𝓞 F) F) → ℂ} (hφ : φ ∈ schA F κ) :
    (fun x => φ (x + a)) ∈ schA F κ := by
  have key : schA F κ ≤ (schA F κ).comap (transl F a) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, g, hg, rfl⟩
    show transl F a (pureA F f g) ∈ schA F κ
    rw [pureA_translate]
    exact Submodule.subset_span ⟨_, _, SB_translate _ hg, rfl⟩
  exact key hφ

theorem main : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : κ → AF F), ∀ φ ∈ schA F κ,
    (fun x => φ (x + a)) ∈ schA F κ :=
  fun F _ _ _ _ a φ hφ => schA_translate F a hφ

end GlobalTheory.SchwartzTranslate

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicThetaDistributionSumProductFunction
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

namespace GlobalTheory.ThetaBox

theorem thetaSum_boxFun : ∀ (F : Type) [Field F] [NumberField F] (κ κ' : Type) [Fintype κ] [Fintype κ'], ∀ φ₁ ∈ schA F κ, ∀ φ₂ ∈ schA F κ', thetaSum F (boxFun φ₁ φ₂) = thetaSum F φ₁ * thetaSum F φ₂ := by
  intro F _ _ κ κ' _ _ φ₁ h₁ φ₂ h₂
  have s₁ := (thetaSum_summable_linear F κ).2.1 φ₁ h₁
  have s₂ := (thetaSum_summable_linear F κ').2.1 φ₂ h₂
  unfold thetaSum
  rw [tsum_mul_tsum_of_summable_norm s₁ s₂]
  rw [← (Equiv.sumArrowEquivProdArrow κ κ' F).symm.tsum_eq]
  rfl

end GlobalTheory.ThetaBox
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicTransvectionSubgroupEqAdelesClosedStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicTransvectionSubgroup_eq_adeles_closed : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∀ ξ, IsoVec V ξ → (∃ e : Multiplicative (AF D.host.F) ≃ₜ* ZI V ξ, (∀ a, ((e a : ZI V ξ) : GA D V) ∈ GQ V ↔ Multiplicative.toAdd a ∈ Set.range (algebraMap D.host.F (AF D.host.F)))) ∧ IsClosed (ZI V ξ : Set (GA D V)) ∧ (∀ z ∈ ZI V ξ, ∀ τ, InZe (gramAt D V τ) (fun i => tauE D τ (ξ i)) (archM V (θ τ) z)) ∧ (∀ m : D.what₂.Tau → Mt V.rank, (∀ τ, InZe (gramAt D V τ) (fun i => tauE D τ (ξ i)) (m τ)) → ∃ z ∈ ZI V ξ, z ∈ GinfC V ∧ ∀ τ, archM V (θ τ) z = m τ) ∧ ∀ z ∈ ZI V ξ, (matHom V z).1.mulVec (fun i => incA D (ξ i)) = fun i => incA D (ξ i) := by
  first | exact @GlobalTheory.HolDict.TransvGroup.transvection_group | exact GlobalTheory.HolDict.TransvGroup.transvection_group | (intros; apply GlobalTheory.HolDict.TransvGroup.transvection_group <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveRealTensorToProdMatrixAlgebrasInfPlacesStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bijective_realTensor_to_prod_matrixAlgebras_infPlaces : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), Function.Bijective (fun x : ℝ ⊗[ℚ] G.C => fun v : InfinitePlace G.F => G.psiR v x) := by
  first | (exact @GlobalTheory.LKTrip.HTGroup.psiR_pi_bijective) | (exact GlobalTheory.LKTrip.HTGroup.psiR_pi_bijective) | (intros; apply GlobalTheory.LKTrip.HTGroup.psiR_pi_bijective  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedAutomorphicHasRepresentativeStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bounded_automorphic_has_representative : ∀ (D : D7) (V : HSp D), ∀ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (ρ : GA D V →* (Lp ℂ 2 (nuQ V μ 𝓕) →L[ℂ] Lp ℂ 2 (nuQ V μ 𝓕))), FinPair V μ 𝓕 → IsReg V μ 𝓕 ρ → (∀ φ : GA D V → ℂ, Continuous φ → (∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) → (∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C) → ∃ F, Repr V μ 𝓕 F φ) ∧ (∀ F ψ ψ', Continuous ψ → Continuous ψ' → Repr V μ 𝓕 F ψ → Repr V μ 𝓕 F ψ' → ψ = ψ') ∧ (∀ F F' ψ, Repr V μ 𝓕 F ψ → Repr V μ 𝓕 F' ψ → F = F') ∧ (∀ F ψ g, Repr V μ 𝓕 F ψ → Repr V μ 𝓕 (ρ g F) (rTr V g ψ)) ∧ (∀ F F' ψ ψ' (a : ℂ), Repr V μ 𝓕 F ψ → Repr V μ 𝓕 F' ψ' → Repr V μ 𝓕 (a • F + F') (a • ψ + ψ')) ∧ ∀ F F' ψ ψ', Repr V μ 𝓕 F ψ → Repr V μ 𝓕 F' ψ' → IntegrableOn (fun x => star (ψ x) * ψ' x) 𝓕 μ ∧ ⟪F, F'⟫_ℂ = ∫ x in 𝓕, star (ψ x) * ψ' x ∂μ := by
  first | exact @GlobalTheory.HolDict.RepresentativeL2.repr_properties | exact GlobalTheory.HolDict.RepresentativeL2.repr_properties | (intros; apply GlobalTheory.HolDict.RepresentativeL2.repr_properties <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedEigenvaluesClassesStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bounded_eigenvalues_classes : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), IsSimple G → ∀ (β y : G.Cˣ) (c : ℚˣ), (y : G.C) * β * sh G y = algebraMap ℚ G.C c * β → ∀ B : ℝ, ‖((c : ℚ) : ℚ_[p])‖ ≤ B → ‖(((c⁻¹ : ℚˣ) : ℚ) : ℚ_[p])‖ ≤ B → (∀ (w : Fin G.m) (μ : PadicAlgCl p), ((G.rho w (y : G.C)).charpoly.map (algebraMap (G.Fw w) (PadicAlgCl p))).IsRoot μ → ‖μ‖ ≤ B) → (∀ (w : Fin G.m) (μ : PadicAlgCl p), ((G.rho w ((y⁻¹ : G.Cˣ) : G.C)).charpoly.map (algebraMap (G.Fw w) (PadicAlgCl p))).IsRoot μ → ‖μ‖ ≤ B) → ∀ μ : PadicAlgCl p, ((LinearMap.mulLeft ℚ (y : G.C)).charpoly.map (algebraMap ℚ (PadicAlgCl p))).IsRoot μ → ‖μ‖ ≤ B * B := by
  first | (exact @GlobalTheory.GlobEig.root_norm_le) | (exact GlobalTheory.GlobEig.root_norm_le) | (intros; apply GlobalTheory.GlobEig.root_norm_le  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedSectionInSpanOfGapStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bounded_section_in_span_of_gap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (P : Frame X.Ψ r → ℂ), X.IsBddSec la P → (∀ (τ : X.Ψ) (a b : Fin r), (a : ℕ) < X.p0 → X.p0 ≤ (b : ℕ) → la τ a < la τ b) → P ∈ X.SS la := by
  first | exact @GlobalTheory.SepCusp.mem_SS_of_sep | exact GlobalTheory.SepCusp.mem_SS_of_sep | (intros; apply GlobalTheory.SepCusp.mem_SS_of_sep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedSubgroupFiniteCosetsStatement
section
open Matrix
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bounded_subgroup_finite_cosets : ∀ (p : ℕ) [Fact p.Prime] (L : IntermediateField ℚ_[p] (PadicAlgCl p)), FiniteDimensional ℚ_[p] L →
    ∀ (n : ℕ) (B : Subgroup (GL (Fin n) L)) (c : ℝ),
      (∀ z ∈ B, ∀ i j, ‖((((z : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j : L) : PadicAlgCl p)‖ ≤ c) →
      ∃ T : Finset (GL (Fin n) L), (∀ t ∈ T, t ∈ B) ∧ ∀ z ∈ B, ∃ t ∈ T, t⁻¹ * z ∈ GlobalTheory.LKLoc.KintK p L n := by
  first | (exact @GlobalTheory.LKLoc.exists_finset_inv_mul_mem_KintK) | (exact GlobalTheory.LKLoc.exists_finset_inv_mul_mem_KintK) | (intros; apply GlobalTheory.LKLoc.exists_finset_inv_mul_mem_KintK <;> assumption)
end

