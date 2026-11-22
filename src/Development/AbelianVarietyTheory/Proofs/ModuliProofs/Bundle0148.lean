import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsIsoOfIsFiniteOfUniqueLiftOfClassicalPoints
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0003
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0133
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0043
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0066
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0132
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0002
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0051
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0137

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProperOfCompleteDVRLiftGeneric
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.ValuativeGeneric

theorem exists_lift_of_surjectiveOnStalks {X Z : Scheme.{0}} (j : X ⟶ Z) [SurjectiveOnStalks j]
    (K : Type) [Field K] (t : Spec (.of K) ⟶ Z) (x : X)
    (hx : t (IsLocalRing.closedPoint K) = j x) :
    ∃ u : Spec (.of K) ⟶ X, u ≫ j = t ∧ ∀ p, u p = x := by
  obtain ⟨⟨z, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField K Z).symm.surjective t
  obtain rfl : z = j x := (Scheme.fromSpecResidueField_apply z
    (Spec.map φ (IsLocalRing.closedPoint K))).symm.trans hx
  have : IsIso (j.residueFieldMap x) := by
    refine (ConcreteCategory.isIso_iff_bijective _).mpr ⟨(j.residueFieldMap x).hom.injective, ?_⟩
    intro a
    obtain ⟨b, rfl⟩ := X.residue_surjective x a
    obtain ⟨c, rfl⟩ := j.stalkMap_surjective x b
    refine ⟨Z.residue _ c, ?_⟩
    rw [← CommRingCat.comp_apply, Scheme.residue_residueFieldMap]
    rfl
  refine ⟨Spec.map (inv (j.residueFieldMap x) ≫ φ) ≫ X.fromSpecResidueField x, ?_, fun p => by simp⟩
  rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
    ← Spec.map_comp_assoc, IsIso.hom_inv_id_assoc]
  rfl

theorem isClosedImmersion_of_lift {X Z : Scheme.{0}} [IsLocallyNoetherian Z] [Z.IsSeparated]
    (j : X ⟶ Z) [IsPreimmersion j] [QuasiCompact j]
    (h : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
      [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [Algebra V K] [IsFractionRing V K]
      (x : Sp K ⟶ X) (y : Sp V ⟶ Z), Set.range x ⊆ genericPoints X →
      x ≫ j = spMap (algebraMap V K) ≫ y → ∃ x' : Sp V ⟶ X, spMap (algebraMap V K) ≫ x' = x) :
    IsClosedImmersion j := by
  refine .of_isPreimmersion j (IsClosedMap.isClosed_range ?_)
  rw [isClosedMap_iff_specializingMap]
  refine j.isEmbedding.isInducing.specializingMap ?_
  rintro _ z hz ⟨x, rfl⟩
  obtain ⟨x₀, hx₀, hs⟩ := exists_mem_genericPoints_specializes x
  have hs' : j x₀ ⤳ z := (hs.map j.continuous).trans hz
  by_cases hne : j x₀ = z
  · exact ⟨x₀, hne⟩
  obtain ⟨O, _, _, _, g, hg₀, hg₁⟩ := exists_complete_discreteValuationRing_of_specializes hs' hne
  have hinj : Function.Injective (algebraMap O (FractionRing O)) := IsFractionRing.injective _ _
  have hpt : (spMap (algebraMap O (FractionRing O)) ≫ g)
      (IsLocalRing.closedPoint (FractionRing O)) = j x₀ := by
    refine Eq.trans (congrArg g (PrimeSpectrum.ext ?_)) hg₀
    change Ideal.comap (algebraMap O (FractionRing O)) (IsLocalRing.maximalIdeal _) = ⊥
    rw [IsLocalRing.maximalIdeal_eq_bot]
    exact Ideal.comap_bot_of_injective _ hinj
  obtain ⟨u, hu, hux⟩ := exists_lift_of_surjectiveOnStalks j (FractionRing O) _ x₀ hpt
  obtain ⟨x', hx'⟩ := h O (FractionRing O) u g (by rintro _ ⟨p, rfl⟩; rw [hux]; exact hx₀) hu
  have : IsDominant (spMap (algebraMap O (FractionRing O))) := by
    refine ⟨?_⟩
    refine (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr ?_
    exact ((RingHom.injective_iff_ker_eq_bot _).mp hinj).le.trans bot_le
  have e : x' ≫ j = g :=
    ext_of_isDominant (spMap (algebraMap O (FractionRing O))) (by rw [← Category.assoc, hx', hu])
  exact ⟨x' (IsLocalRing.closedPoint O), by rw [← hg₁, ← e]; rfl⟩

theorem isProper_of_lift_generic : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X Y : Scheme.{0}) [IsLocallyNoetherian Y] (f : X ⟶ Y) (s : Y ⟶ Sp R), IsSeparated s → IsQProjOver (f ≫ s) → (∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [Algebra V K] [IsFractionRing V K] (x : Sp K ⟶ X) (y : Sp V ⟶ Y), Set.range x ⊆ genericPoints X → x ≫ f = spMap (algebraMap V K) ≫ y → ∃ x' : Sp V ⟶ X, spMap (algebraMap V K) ≫ x' = x) → IsProper f := by
  intro R _ _ X Y _ f s hs ⟨N, i, hi, hq, e⟩ h
  have := isProper_str R N
  let j : X ⟶ pullback s (PSpace.str R N) := pullback.lift f i e.symm
  have hj₁ : j ≫ pullback.fst _ _ = f := pullback.lift_fst _ _ _
  have hj₂ : j ≫ pullback.snd _ _ = i := pullback.lift_snd _ _ _
  have : IsImmersion (j ≫ pullback.snd _ _) := hj₂ ▸ hi
  have : QuasiCompact (j ≫ pullback.snd _ _) := hj₂ ▸ hq
  have : IsImmersion j := IsImmersion.of_comp j (pullback.snd _ _)
  have : QuasiCompact j := QuasiCompact.of_comp j (pullback.snd _ _)
  have : IsLocallyNoetherian (pullback s (PSpace.str R N)) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst _ _)
  have : (pullback s (PSpace.str R N)).IsSeparated := by
    refine ⟨?_⟩
    rw [← terminal.comp_from (pullback.fst s (PSpace.str R N) ≫ s)]
    infer_instance
  have : IsClosedImmersion j := isClosedImmersion_of_lift j fun V K _ _ _ _ _ _ _ x y hx hy =>
    h V K x (y ≫ pullback.fst _ _) hx (by rw [← hj₁, ← Category.assoc, hy, Category.assoc])
  rw [← hj₁]
  infer_instance

end GlobalTheory.ValuativeGeneric
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverOfIsComplOpenImmersions
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum

namespace GlobalTheory.ProjSpace

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct Pointwise in
private theorem isImmersion_coprod_map {X Y X' Y' : Scheme.{0}} (f : X ⟶ X') (g : Y ⟶ Y')
    [IsImmersion f] [IsImmersion g] : IsImmersion (coprod.map f g) := by
  refine IsZariskiLocalAtTarget.of_openCover (coprodOpenCover.{0, 0} X' Y') ?_
  rintro (⟨⟩ | ⟨⟩)
  · change IsImmersion (pullback.snd (coprod.map f g) coprod.inl)
    have h := (isPullback_inl_inl_coprodMap f g).flip
    rw [← Iso.inv_hom_id_assoc h.isoPullback (pullback.snd _ _), h.isoPullback_hom_snd]
    infer_instance
  · change IsImmersion (pullback.snd (coprod.map f g) coprod.inr)
    have h := (isPullback_inr_inr_coprodMap f g).flip
    rw [← Iso.inv_hom_id_assoc h.isoPullback (pullback.snd _ _), h.isoPullback_hom_snd]
    infer_instance

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct Pointwise in

theorem _root_.GlobalTheory.ProjSpace.isQProjOver_of_isCompl : ∀ (R : Type) [CommRing R] (X X₁ X₂ : Scheme.{0})
    (f₁ : X₁ ⟶ X) (f₂ : X₂ ⟶ X) (s : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R), IsOpenImmersion f₁ → IsOpenImmersion f₂ →
    IsCompl (Set.range f₁) (Set.range f₂) → _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsQProjOver (f₁ ≫ s) → _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsQProjOver (f₂ ≫ s) →
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsQProjOver s := by
  intro R _ X X₁ X₂ f₁ f₂ s h₁ h₂ hc q₁ q₂
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsQProjOver at q₁ q₂ ⊢
  obtain ⟨N₁, i₁, hi₁, hq₁, e₁⟩ := q₁
  obtain ⟨N₂, i₂, hi₂, hq₂, e₂⟩ := q₂
  have hP := _root_.GlobalTheory.ProjSpace.isProjOver_coprodDesc (_root_.GlobalTheory.ProjSpace.isProjOver_pspace_str R N₁)
    (_root_.GlobalTheory.ProjSpace.isProjOver_pspace_str R N₂)
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver at hP
  obtain ⟨M, j, hj, ej⟩ := hP
  have hc' : IsCompl f₁.opensRange f₂.opensRange :=
    ⟨disjoint_iff.mpr (SetLike.coe_injective (by simpa using hc.inf_eq_bot)),
      codisjoint_iff.mpr (SetLike.coe_injective (by simpa using hc.sup_eq_top))⟩
  obtain ⟨hX⟩ := nonempty_isColimit_binaryCofanMk_of_isCompl f₁ f₂ hc'
  let e : X₁ ⨿ X₂ ≅ X := (coprodIsCoprod X₁ X₂).coconePointUniqueUpToIso hX
  have he₁ : coprod.inl ≫ e.hom = f₁ :=
    (coprodIsCoprod X₁ X₂).comp_coconePointUniqueUpToIso_hom hX ⟨WalkingPair.left⟩
  have he₂ : coprod.inr ≫ e.hom = f₂ :=
    (coprodIsCoprod X₁ X₂).comp_coconePointUniqueUpToIso_hom hX ⟨WalkingPair.right⟩
  have hcomp : (e.inv ≫ coprod.map i₁ i₂ ≫ j) ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.PSpace.str R M = s := by
    rw [Category.assoc, Category.assoc, ej, Iso.inv_comp_eq]
    apply coprod.hom_ext
    · rw [coprod.inl_map_assoc, coprod.inl_desc, ← Category.assoc, he₁, e₁]
    · rw [coprod.inr_map_assoc, coprod.inr_desc, ← Category.assoc, he₂, e₂]
  haveI := isImmersion_coprod_map i₁ i₂
  haveI := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str R M
  haveI := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str R N₁
  haveI := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str R N₂
  haveI : CompactSpace X₁ := (quasiCompact_iff_compactSpace (f₁ ≫ s)).mp (by rw [← e₁]; infer_instance)
  haveI : CompactSpace X₂ := (quasiCompact_iff_compactSpace (f₂ ≫ s)).mp (by rw [← e₂]; infer_instance)
  haveI : CompactSpace X := ⟨by
    rw [← Set.top_eq_univ, ← hc.sup_eq_top]
    exact (isCompact_range f₁.continuous).union (isCompact_range f₂.continuous)⟩
  haveI : QuasiCompact s := (quasiCompact_iff_compactSpace s).mpr inferInstance
  haveI : QuasiCompact ((e.inv ≫ coprod.map i₁ i₂ ≫ j) ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.PSpace.str R M) := by
    rw [hcomp]; infer_instance
  exact ⟨M, e.inv ≫ coprod.map i₁ i₂ ≫ j, inferInstance,
    QuasiCompact.of_comp _ (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.PSpace.str R M), hcomp⟩

end GlobalTheory.ProjSpace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSharpDescends
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.SharpDescent

theorem univ_descend {S S₁ : Scheme.{0}} (i : S ⟶ S₁) [Surjective i] [Flat i] [QuasiCompact i]
    {A C : Over S} {A₁ C₁ : Over S₁} {ψ : A.left ⟶ A₁.left} {χ : C.left ⟶ C₁.left}
    (hψ : IsPullback ψ A.hom A₁.hom i) (hχ : IsPullback χ C.hom C₁.hom i) {I : Type} [Finite I]
    (pr : I → (A ⟶ C)) (pr₁ : I → (A₁ ⟶ C₁)) (hc : ∀ u, ψ ≫ (pr₁ u).left = (pr u).left ≫ χ)
    (hU : ∀ (T : Over S) (y : I → (T ⟶ C)), ∃! x : T ⟶ A, ∀ u, x ≫ pr u = y u)
    (T : Over S₁) (y : I → (T ⟶ C₁)) : ∃! x : T ⟶ A₁, ∀ u, x ≫ pr₁ u = y u := by
  let Q₁ : Over S₁ := ∏ᶜ (fun _ : I => C₁)
  let π : I → (Q₁ ⟶ C₁) := fun u => Pi.π (fun _ : I => C₁) u
  let m₁ : A₁ ⟶ Q₁ := Pi.lift pr₁
  have hm₁ : ∀ u, m₁ ≫ π u = pr₁ u := fun u => Pi.lift_π _ _
  have ext₁ : ∀ {Z : Scheme.{0}} (a b : Z ⟶ Q₁.left), a ≫ Q₁.hom = b ≫ Q₁.hom →
      (∀ u, a ≫ (π u).left = b ≫ (π u).left) → a = b := by
    intro Z a b h1 h2
    have : (Over.homMk a rfl : Over.mk (a ≫ Q₁.hom) ⟶ Q₁) = Over.homMk b h1.symm :=
      Pi.hom_ext _ _ fun u => Over.OverMorphism.ext (h2 u)
    exact congrArg (fun z => z.left) this
  let Q : Over S := Over.mk (pullback.snd Q₁.hom i)
  let q : I → (Q ⟶ C) := fun u => Over.homMk (hχ.lift (pullback.fst Q₁.hom i ≫ (π u).left) (pullback.snd Q₁.hom i)
    (by rw [Category.assoc, Over.w, pullback.condition])) (hχ.lift_snd _ _ _)
  have hq : ∀ u, (q u).left ≫ χ = pullback.fst Q₁.hom i ≫ (π u).left := fun u => hχ.lift_fst _ _ _
  let m : A ⟶ Q := Over.homMk (pullback.lift (ψ ≫ m₁.left) A.hom (by rw [Category.assoc, Over.w, hψ.w]))
    (pullback.lift_snd _ _ _)
  have hm : m.left ≫ pullback.fst Q₁.hom i = ψ ≫ m₁.left := pullback.lift_fst _ _ _
  have hm' : m.left ≫ pullback.snd Q₁.hom i = A.hom := pullback.lift_snd _ _ _
  have hmq : ∀ u, m ≫ q u = pr u := fun u => Over.OverMorphism.ext (hχ.hom_ext
    (by rw [Over.comp_left, Category.assoc, hq, ← Category.assoc, hm, Category.assoc, ← Over.comp_left, hm₁, hc])
    (by rw [Over.w, Over.w]))
  obtain ⟨n, hn, -⟩ := hU Q q
  have h1 : m ≫ n = 𝟙 A := (hU A pr).unique (fun u => by rw [Category.assoc, hn, hmq]) (fun u => Category.id_comp _)
  have h2 : n.left ≫ m.left = 𝟙 Q.left := by
    have hs : (n.left ≫ m.left) ≫ pullback.snd Q₁.hom i = 𝟙 Q.left ≫ pullback.snd Q₁.hom i := by
      rw [Category.assoc, hm', Over.w, Category.id_comp]; rfl
    refine pullback.hom_ext (ext₁ _ _ ?_ fun u => ?_) hs
    · rw [Category.assoc, Category.assoc (𝟙 _), pullback.condition, ← Category.assoc, hs, Category.assoc]
    · rw [Category.assoc, Category.assoc (𝟙 _), ← hq, Category.id_comp, ← Category.assoc, ← Over.comp_left,
        ← Over.comp_left, Category.assoc, hmq, hn]
  have hI : IsIso m.left := ⟨⟨n.left, by rw [← Over.comp_left, h1, Over.id_left], h2⟩⟩
  have hp : IsPullback m.left ψ (pullback.fst Q₁.hom i) m₁.left := by
    refine IsPullback.of_right (h₁₂ := pullback.snd Q₁.hom i) (v₁₃ := i) (h₂₂ := Q₁.hom) ?_ hm
      (IsPullback.of_hasPullback Q₁.hom i).flip
    rw [hm', Over.w]; exact hψ.flip
  have hI₁ : IsIso m₁.left :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := MorphismProperty.isomorphisms Scheme.{0})
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hp ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hI
  have : IsIso ((Over.forget S₁).map m₁) := hI₁
  have : IsIso m₁ := isIso_of_reflects_iso m₁ (Over.forget S₁)
  refine ⟨Pi.lift y ≫ inv m₁, fun u => ?_, fun x hx => ?_⟩
  · rw [← hm₁, Category.assoc, IsIso.inv_hom_id_assoc]; exact Pi.lift_π _ _
  · rw [IsIso.eq_comp_inv]
    refine Pi.hom_ext _ _ fun u => ?_
    rw [Category.assoc, Pi.lift_π]
    exact (hx u).trans (Pi.lift_π _ _).symm

theorem prod_descend {S S₁ : Scheme.{0}} {i : S ⟶ S₁} {A C : Over S} {A₁ C₁ : Over S₁} [GrpObj C] [GrpObj C₁]
    {ψ : A.left ⟶ A₁.left} {χ : C.left ⟶ C₁.left} [Epi ψ] (hψ : ψ ≫ A₁.hom = A.hom ≫ i)
    (hχ : IsGrpPullback C C₁ i χ) {n : ℕ} (pr : Fin n → (A ⟶ C)) (pr₁ : Fin n → (A₁ ⟶ C₁))
    (hc : ∀ u, ψ ≫ (pr₁ u).left = (pr u).left ≫ χ) (e : Fin n → ℤ) (z : A ⟶ C) (z₁ : A₁ ⟶ C₁)
    (hz : ψ ≫ z₁.left = z.left ≫ χ) (h : z = (List.ofFn fun v => pr v ^ e v).prod) :
    z₁ = (List.ofFn fun v => pr₁ v ^ e v).prod := by
  let U : Over.mk (A.hom ≫ i) ⟶ A₁ := Over.homMk ψ hψ
  have key : ∀ (x : A ⟶ C) (x₁ : A₁ ⟶ C₁), ψ ≫ x₁.left = x.left ≫ χ → preHom U x₁ = pushHom hχ A x :=
    fun x x₁ hx => Over.OverMorphism.ext hx
  have E : preHom U z₁ = preHom U (List.ofFn fun v => pr₁ v ^ e v).prod := by
    rw [key z z₁ hz, h, map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn]
    congr 2
    funext v
    simp only [Function.comp, map_zpow, key _ _ (hc v)]
  exact Over.OverMorphism.ext ((cancel_epi ψ).1 (congrArg (fun w => w.left) E))

theorem iso_pull_cancel {X X₁ X₀ : Scheme.{0}} {L : LB X} {L₁ : LB X₁} {L₀ : LB X₀} (hL : L.IsLB) (hL₁ : L₁.IsLB)
    (hL₀ : L₀.IsLB) {φ : X ⟶ X₀} {φ₁ : X₁ ⟶ X₀} {ψ : X ⟶ X₁} (e : ψ ≫ φ₁ = φ) (h : LBIso L (L₀.pull φ))
    (h₁ : LBIso L₁ (L₀.pull φ₁)) : LBIso L (L₁.pull ψ) := by
  obtain ⟨w, hw⟩ := h₁
  have := iso_linComb ((isGen_iff w).1 hw) (fun _ : PUnit => ψ) (fun _ => 1)
  subst e
  exact LBIso.trans hL (pull_isLB hL₀ _) (pull_isLB hL₁ _) h (LBIso.symm this)

theorem isSharp_descends : ∀ (h g k : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (o : Type) [CommRing o] (b : TBase o k) (K : Type) [Field K] (K₀ : Subfield K) (β₀ : o →+* K₀) (s : Sp K ⟶ Sp o) (t : TObj g k J b s) (c : SiegPre h k (b.ζ : o) s) (t₀ : TObj g k J b (spMap β₀)) (c₀ : SiegPre h k (b.ζ : o) (spMap β₀)), s = spMap K₀.subtype ≫ spMap β₀ → TMap t t₀ (spMap K₀.subtype) → SiegPB c c₀ (spMap K₀.subtype) → c₀.Principal → IsSharp W a bas t c → ∃ (F : Finset K) (β₁ : o →+* Subfield.closure ((K₀ : Set K) ∪ F)) (t₁ : TObj g k J b (spMap β₁)) (c₁ : SiegPre h k (b.ζ : o) (spMap β₁)), s = spMap (Subfield.subtype _) ≫ spMap β₁ ∧ TMap t t₁ (spMap (Subfield.subtype _)) ∧ c₁.Principal ∧ IsSharp W a bas t₁ c₁ := by
  intro h g k W J a bas o _ b K _ K₀ β₀ s t c t₀ c₀ hs ⟨φ, hφ, hφL, hφp, hφa⟩ ⟨ξ, ξ₂, hξ, hξs, hξL, hξl⟩ hP
    ⟨pr, hm, hU, hL, hA, hp⟩
  have := t₀.ab.proper
  have := c₀.ab.smooth
  have hf : ∀ u, ((pr u).left ≫ ξ) ≫ c₀.A.hom = φ ≫ t₀.A.hom := fun u => by
    rw [Category.assoc, hξ.1.w, ← Category.assoc, Over.w, hφ.1.w]
  obtain ⟨F, hF⟩ := GlobalTheory.T.exists_descent_of_morphisms_to_subfield K K₀ _ _ t₀.A.hom t.A.hom φ _ c₀.A.hom (Fin 8) (fun u => (pr u).left ≫ ξ) hφ.1 hf
  refine ⟨F, ?_⟩
  have hle : K₀ ≤ Subfield.closure ((K₀ : Set K) ∪ F) := fun x hx => Subfield.subset_closure (Or.inl hx)
  have hFs : (F : Set K) ⊆ Subfield.closure ((K₀ : Set K) ∪ F) := fun x hx => Subfield.subset_closure (Or.inr hx)
  have hF₁ := hF _ hle hFs
  generalize Subfield.closure ((K₀ : Set K) ∪ F) = K₁ at hle hF₁ ⊢
  clear hF hFs
  have e₁ : spMap (Subfield.inclusion hle) ≫ spMap β₀ = spMap ((Subfield.inclusion hle).comp β₀) :=
    (Spec.map_comp _ _).symm
  have e₂ : spMap K₁.subtype ≫ spMap (Subfield.inclusion hle) = spMap K₀.subtype := (Spec.map_comp _ _).symm
  obtain ⟨t₁, φ₁, hφ₁, hφ₁L, hφ₁p, hφ₁a⟩ := GlobalTheory.T.exists_thetaLevelAbelianScheme_pullback o g k J b _ _ _ _ _ t₀ e₁
  obtain ⟨⟨c₁, hc₁⟩, hc₁P⟩ := GlobalTheory.T.siegelObject_pullback_exists_and_principal h k o (b.ζ : o) _ _ _ _ _ c₀ e₁
  have hP₁ := hc₁P c₁ hc₁ hP
  obtain ⟨ξ₁, ξ₁₂, hξ₁, hξ₁s, hξ₁L, hξ₁l⟩ := hc₁

  obtain ⟨ψ, hψ, hψw⟩ : ∃ ψ : t.A.left ⟶ t₁.A.left, ψ ≫ φ₁ = φ ∧ ψ ≫ t₁.A.hom = t.A.hom ≫ spMap K₁.subtype :=
    ⟨hφ₁.1.lift φ (t.A.hom ≫ spMap K₁.subtype) (by rw [Category.assoc, e₂, hφ.1.w]), hφ₁.1.lift_fst _ _ _,
      hφ₁.1.lift_snd _ _ _⟩
  obtain ⟨χ, hχ, hχw⟩ : ∃ χ : c.A.left ⟶ c₁.A.left, χ ≫ ξ₁ = ξ ∧ χ ≫ c₁.A.hom = c.A.hom ≫ spMap K₁.subtype :=
    ⟨hξ₁.1.lift ξ (c.A.hom ≫ spMap K₁.subtype) (by rw [Category.assoc, e₂, hξ.1.w]), hξ₁.1.lift_fst _ _ _,
      hξ₁.1.lift_snd _ _ _⟩
  have gψ : IsGrpPullback t.A t₁.A (spMap K₁.subtype) ψ := hφ₁.cancel (hφ.congr e₂.symm hψ.symm) hψw
  have gχ : IsGrpPullback c.A c₁.A (spMap K₁.subtype) χ := hξ₁.cancel (hξ.congr e₂.symm hχ.symm) hχw
  obtain ⟨f₁, hf₁⟩ := hF₁ _ t₁.A.hom φ₁ ψ hφ₁.1 hψ hψw
  obtain ⟨pr₁, hpr₁⟩ : ∃ pr₁ : Fin 8 → (t₁.A ⟶ c₁.A), ∀ u, (pr₁ u).left ≫ ξ₁ = f₁ u :=
    ⟨fun u => Over.homMk (hξ₁.1.lift (f₁ u) t₁.A.hom ((hf₁ u).2.trans hφ₁.1.w)) (hξ₁.1.lift_snd _ _ _),
      fun u => hξ₁.1.lift_fst _ _ _⟩
  have hc : ∀ u, ψ ≫ (pr₁ u).left = (pr u).left ≫ χ := fun u => hξ₁.1.hom_ext
    (by rw [Category.assoc, hpr₁, (hf₁ u).1, Category.assoc, hχ])
    (by rw [Category.assoc, Over.w, hψw, Category.assoc, hχw, ← Category.assoc, Over.w])
  obtain ⟨D₁, D₂⟩ := GlobalTheory.FieldBaseChange.epi_and_isMonHom_iff K₁ K K₁.subtype
  obtain ⟨i₁, i₂, i₃, i₄, -⟩ := D₁ _ _ (𝟙 _) (𝟙 _) (spMap K₁.subtype) (IsPullback.of_vert_isIso ⟨by simp⟩)
  obtain ⟨j₁, -⟩ := D₁ _ _ _ _ ψ gψ.1
  have hψL : LBIso t.L (t₁.L.pull ψ) := iso_pull_cancel t.isLB t₁.isLB t₀.isLB hψ hφL hφ₁L
  have hψp : ∀ i, (t.pt i).left ≫ ψ = spMap K₁.subtype ≫ (t₁.pt i).left := fun i => hφ₁.1.hom_ext
    (by rw [Category.assoc, hψ, hφp, Category.assoc, hφ₁p, ← Category.assoc, e₂])
    (by rw [Category.assoc, hψw, ← Category.assoc, Over.w, Category.assoc, Over.w]; simp)
  have hψa : ∀ j, (t.act j).left ≫ ψ = ψ ≫ (t₁.act j).left := fun j => hφ₁.1.hom_ext
    (by rw [Category.assoc, hψ, hφa, Category.assoc, hφ₁a, ← Category.assoc, hψ])
    (by rw [Category.assoc, hψw, ← Category.assoc, Over.w, Category.assoc, Over.w, hψw])
  have hχl : ∀ v, (c.lev v).left ≫ χ = spMap K₁.subtype ≫ (c₁.lev v).left := fun v => hξ₁.1.hom_ext
    (by rw [Category.assoc, hχ, hξl, Category.assoc, hξ₁l, ← Category.assoc, e₂])
    (by rw [Category.assoc, hχw, ← Category.assoc, Over.w, Category.assoc, Over.w]; simp)
  refine ⟨_, t₁, c₁, by rw [hs, ← e₁, ← Category.assoc, e₂], ⟨ψ, gψ, hψL, hψp, hψa⟩, hP₁, pr₁,
    fun u => (D₂ _ _ _ _ ψ χ (pr₁ u) (pr u) gψ gχ (hc u)).1 (hm u), univ_descend _ gψ.1 gχ.1 pr pr₁ hc hU, ?_,
    fun j u => prod_descend hψw gχ pr pr₁ hc _ (t.act j ≫ pr u) _ ?_ (hA j u), fun i u => ?_⟩
  · have lb := fun {X Y : Scheme.{0}} (L : LB X) (hL : L.IsLB) (φ : Fin 8 × Fin 8 → (Y ⟶ X)) =>
      DVR.linComb_isLB L hL φ (fun uv => W uv.1 uv.2)
    refine (GlobalTheory.T.lineBundle_trivial_iso_descend_field K₁ K K₁.subtype _ _ _ _ ψ t₁.ab.smooth t₁.ab.proper t₁.ab.geomConnected gψ.1).2 _ _ t₁.isLB
      (lb _ c₁.isLB _) ?_
    obtain ⟨w, hw⟩ := hξL
    obtain ⟨w₁, hw₁⟩ := hξ₁L
    have a₁ := iso_linComb ((isGen_iff w).1 hw) (fun uv : Fin 8 × Fin 8 => (lift (pr uv.1) (pr uv.2)).left)
      (fun uv => W uv.1 uv.2)
    have a₂ := iso_linComb ((isGen_iff w₁).1 hw₁) (fun uv : Fin 8 × Fin 8 => ψ ≫ (lift (pr₁ uv.1) (pr₁ uv.2)).left)
      (fun uv => W uv.1 uv.2)
    have e : (fun uv : Fin 8 × Fin 8 => (ψ ≫ (lift (pr₁ uv.1) (pr₁ uv.2)).left) ≫ ξ₁₂) =
        fun uv => (lift (pr uv.1) (pr uv.2)).left ≫ ξ₂ := by
      funext uv
      apply pullback.hom_ext
      · show (_ ≫ ξ₁₂) ≫ (fst c₀.A c₀.A).left = (_ ≫ ξ₂) ≫ (fst c₀.A c₀.A).left
        rw [Category.assoc, hξ₁s.1, Category.assoc, Category.assoc, hξs.1, ← Over.comp_left_assoc,
          ← Over.comp_left_assoc, lift_fst, lift_fst, hpr₁, (hf₁ _).1]
      · show (_ ≫ ξ₁₂) ≫ (snd c₀.A c₀.A).left = (_ ≫ ξ₂) ≫ (snd c₀.A c₀.A).left
        rw [Category.assoc, hξ₁s.2, Category.assoc, Category.assoc, hξs.2, ← Over.comp_left_assoc,
          ← Over.comp_left_assoc, lift_snd, lift_snd, hpr₁, (hf₁ _).1]
    rw [e] at a₂
    have a₃ := LBIso.trans t.isLB (lb _ c.isLB _) (lb _ c₀.isLB _) hL a₁
    have a₄ := LBIso.trans t.isLB (lb _ c₀.isLB _) (lb _ c₁.isLB _) a₃ a₂.symm
    have a₅ := LBIso.trans (pull_isLB t₁.isLB ψ) t.isLB (lb _ c₁.isLB _) hψL.symm a₄
    exact LBIso.chartPull (chartPullId _) (chartPullOut c₁.P _ _ ψ _ fun _ => rfl) a₅
  · rw [Over.comp_left, Over.comp_left, ← Category.assoc, ← hψa, Category.assoc, hc, Category.assoc]
  · rw [← cancel_epi (spMap K₁.subtype), Over.comp_left, ← Category.assoc, ← hψp, Category.assoc, hc,
      ← Category.assoc, ← Over.comp_left, hp]
    exact hχl _

end GlobalTheory.SharpDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSquareUnique
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.LamPull

theorem exists_isSquare {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
    (w : φ ≫ G.hom = G'.hom ≫ f) :
    IsSquare φ (lift (pushPt w (fst G' G')) (pushPt w (snd G' G'))).left :=
  ⟨congrArg (fun z => z.left) (lift_fst (pushPt w (fst G' G')) (pushPt w (snd G' G'))),
    congrArg (fun z => z.left) (lift_snd (pushPt w (fst G' G')) (pushPt w (snd G' G')))⟩

theorem isSquare_unique {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} {φ : G'.left ⟶ G.left}
    {a b : (G' ⊗ G').left ⟶ (G ⊗ G).left} (ha : IsSquare φ a) (hb : IsSquare φ b) : a = b := by
  apply pullback.hom_ext
  · exact ha.1.trans hb.1.symm
  · exact ha.2.trans hb.2.symm

theorem lbIso_lam_pull {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {L : LB G.left}
    {L' : LB G'.left} (hL : L.IsLB) (hL' : L'.IsLB) (H : LBIso L' (L.pull φ))
    {φ₂ : (G2 G').left ⟶ (G2 G).left} (hφ : IsSquare φ φ₂) : LBIso (abelian₂ G' L') ((abelian₂ G L).pull φ₂) := by
  obtain rfl := isSquare_unique hφ (exists_isSquare h.1.w)
  have hΛ : (abelian₂ G L).IsLB := DVR.linComb_isLB L hL _ _
  have h₁ : LBIso (abelian₂ G' L') (abelian₂ G' (L.pull φ)) := by
    obtain ⟨w, hw⟩ := H
    exact ⟨LB.linCombIso w _ _, DVR.linCombIso_isGen w hw _ _⟩
  let U := lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G'))
  have h₂ : LBIso (abelian₂ G' (L.pull φ)) ((abelian₂ G L).pull U.left) := by
    refine LBIso.chartPull
      (chartPullLinComb L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down)
      (Geo.Tor.chartPullPull (abelian₂ G L) _ U.left rfl) ⟨idIso _, idIso_isGen hΛ⟩
    fin_cases i <;> simp [U, x2]
  exact LBIso.trans (DVR.linComb_isLB L' hL' _ _) (DVR.linComb_isLB _ (pull_isLB hL φ) _ _) (pull_isLB hΛ _) h₁ h₂

theorem lam_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (t : SAB H S) (t' : SAB H S') (f : S' ⟶ S), (∀ φ : t'.G.left ⟶ t.G.left, φ ≫ t.G.hom = t'.G.hom ≫ f → ∃ φ₂ : (G2 t'.G).left ⟶ (G2 t.G).left, IsSquare φ φ₂) ∧ ∀ (ν : SABMap t' t f) (φ₂ : (G2 t'.G).left ⟶ (G2 t.G).left), IsSquare ν.φ φ₂ → LBIso (abelian₂ t'.G t'.PP.L) ((abelian₂ t.G t.PP.L).pull φ₂) := by
  intro E _ _ _ H S S' t t' f
  refine ⟨fun φ w => ⟨_, exists_isSquare w⟩, fun ν φ₂ hφ => ?_⟩
  obtain ⟨w, hw, -⟩ := ν.lin
  exact lbIso_lam_pull ν.cart t.PP.isLB t'.PP.isLB ⟨w, hw⟩ hφ

end GlobalTheory.LamPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbIsoPullOfIsConst
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.SymRigid

open GlobalTheory.CechPic

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem sym_iff_cls {L : LB A.left} (hL : L.IsLB) : Out.Sym A L ↔ ∀ s : S, ∃ U : S.Opens, s ∈ U ∧
    pull ((A.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : A ⟶ A).left) (cls L hL) = pull (A.hom ⁻¹ᵁ U).ι (cls L hL) := by
  refine forall_congr' fun s => exists_congr fun U => and_congr_right fun _ => ?_
  rw [← cls_eq_zero_iff (LB.isLB_linComb hL _ _), cls_linComb hL, Fin.sum_univ_two]
  change (1 : ℤ) • pull ((A.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : A ⟶ A).left) (cls L hL) +
    (-1 : ℤ) • pull (A.hom ⁻¹ᵁ U).ι (cls L hL) = 0 ↔ _
  rw [one_zsmul, neg_one_zsmul, add_neg_eq_zero]

theorem pull_restrict {U V : S.Opens} (h : V ≤ U) {c : Pic A.left}
    (e : pull ((A.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : A ⟶ A).left) c = pull (A.hom ⁻¹ᵁ U).ι c) :
    pull ((A.hom ⁻¹ᵁ V).ι ≫ (GrpObj.inv : A ⟶ A).left) c = pull (A.hom ⁻¹ᵁ V).ι c := by
  have hle : A.hom ⁻¹ᵁ V ≤ A.hom ⁻¹ᵁ U := fun _ hx => h hx
  rw [← Scheme.homOfLE_ι A.left hle, Category.assoc, pull_comp, e, ← pull_comp]

theorem sym_of_cls_eq_sub {L M Q : LB A.left} (hL : L.IsLB) (hM : M.IsLB) (hQ : Q.IsLB)
    (e : cls Q hQ = cls L hL - cls M hM) (sL : Out.Sym A L) (sM : Out.Sym A M) : Out.Sym A Q := by
  refine (sym_iff_cls hQ).2 fun s => ?_
  obtain ⟨U, hU, eU⟩ := (sym_iff_cls hL).1 sL s
  obtain ⟨V, hV, eV⟩ := (sym_iff_cls hM).1 sM s
  refine ⟨U ⊓ V, ⟨hU, hV⟩, ?_⟩
  rw [e, map_sub, map_sub, pull_restrict inf_le_left eU, pull_restrict inf_le_right eV]

theorem lbIso_pull_of_isConst : Out.Laws → ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (A' : Over (Sp (DualNumber ℂ))) [GrpObj A'] (ρ : A'.left ⟶ P₀.A.left) (j : P₀.A.left ⟶ A'.left), IsConst A' P₀.A ρ j → ∀ M : LB A'.left, M.IsLB → Out.Sym A' M → LBIso P₀.L (M.pull j) → LBIso M (P₀.L.pull ρ) := by
  intro laws P₀ u Hm χ hu A' _ ρ j hc M hM sM H
  have hL := pull_isLB P₀.isLB ρ
  have hQ : (LB.div (P₀.L.pull ρ) M).IsLB := LB.isLB_div hL hM
  have e₀ : cls _ P₀.isLB = pull j (cls M hM) := (cls_eq_iff _ (pull_isLB hM j)).2 H
  have triv : ∃ t : ((LB.div (P₀.L.pull ρ) M).pull j).Gen, t.IsGen := by
    rw [← cls_eq_zero_iff (pull_isLB hQ j), cls_pull hQ, cls_div hL hM, map_sub, cls_pull P₀.isLB, ← pull_comp,
      hc.2.2, pull_id, e₀, sub_self]
  obtain ⟨Q, k, hQ', iso, hk⟩ := GlobalTheory.T.exists_lineBundle_cocycle_one_add_eps _ _ P₀.A.hom A'.hom ρ j hc.1.1 hc.2.2 hc.2.1.1.w _ hQ triv
  have e : cls Q hQ' = cls _ hL - cls M hM := ((cls_eq_iff hQ hQ').2 iso).symm.trans (cls_div hL hM hQ)
  have z := (cls_eq_zero_iff hQ').2 (GlobalTheory.T.symmetric_bundle_trivial_constant_family_dualNumber laws P₀ u Hm χ hu A' ρ j hc Q k hQ' hk
    (sym_of_cls_eq_sub hL hM hQ' e (PolBaseChange.sym_pull hc.1 P₀.sym) sM))
  exact (cls_eq_iff hM hL).1 (sub_eq_zero.1 (e.symm.trans z)).symm

end GlobalTheory.SymRigid
end

