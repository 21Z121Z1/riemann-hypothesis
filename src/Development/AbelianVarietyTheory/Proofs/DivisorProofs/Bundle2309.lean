import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivBasicOpenOfTrivFibre
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAmpleCubSpFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2284
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumLifts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionHeightLowerBound
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0131
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsSecNeObj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2261
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2262
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2264
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeLocallyConstantRelDim
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon

theorem abelianScheme_locally_relDim : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ s : S,
    ∃ (V : S.Opens) (g : ℕ), IsAffineOpen V ∧ s ∈ V ∧ SmoothOfRelativeDimension g (pullback.snd A.hom V.ι) := by
  intro S A _ hA s
  have := hA.smooth
  have := hA.geomConnected
  choose n W hW hd using ReciprocityTheory.ChartRestriction.G.H1.exists_dim A.hom
  have loc : ∀ x y, y ∈ W x → n y = n x := fun x y hy => by
    have := hd x
    have := hd y
    have e₁ : SmoothOfRelativeDimension (0 + n y) ((W y ⊓ W x).ι ≫ A.hom) := by
      rw [← Scheme.homOfLE_ι _ (inf_le_left : W y ⊓ W x ≤ W y), Category.assoc]; infer_instance
    have e₂ : SmoothOfRelativeDimension (0 + n x) ((W y ⊓ W x).ι ≫ A.hom) := by
      rw [← Scheme.homOfLE_ι _ (inf_le_right : W y ⊓ W x ≤ W x), Category.assoc]; infer_instance
    simpa using ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ e₁ e₂ ⟨y, hW y, hy⟩
  have hc : IsLocallyConstant n :=
    (IsLocallyConstant.iff_exists_open n).2 fun x => ⟨W x, (W x).isOpen, hW x, loc x⟩
  have hsec : η[A].left ≫ A.hom = 𝟙 S := Over.w η[A]
  have he : ∀ t : S, A.hom (η[A].left t) = t := fun t => by
    rw [← Scheme.Hom.comp_apply, hsec]; rfl
  have fib : ∀ x, n x = n (η[A].left (A.hom x)) := fun x => by
    have hconn : _root_.IsPreconnected (A.hom ⁻¹' {A.hom x}) := by
      rw [← Scheme.Hom.range_fiberι, ← Set.image_univ]
      exact isPreconnected_univ.image _ (A.hom.fiberι _).continuous.continuousOn
    exact hc.apply_eq_of_isPreconnected hconn rfl (he (A.hom x))
  let x₀ : A.left := η[A].left s
  let U : S.Opens := η[A].left ⁻¹ᵁ W x₀
  have hsU : s ∈ U := hW x₀
  obtain ⟨V, hV, hsV, hVU⟩ := exists_isAffineOpen_mem_and_subset hsU
  refine ⟨V, n x₀, hV, hsV, ?_⟩
  have dimy : ∀ y, n (pullback.fst A.hom V.ι y) = n x₀ := fun y => by
    have h1 : A.hom (pullback.fst A.hom V.ι y) ∈ V := by
      have := congrArg (fun g => g y) (pullback.condition (f := A.hom) (g := V.ι))
      simp only [Scheme.Hom.comp_apply] at this
      rw [this]; exact (pullback.snd A.hom V.ι y).2
    rw [fib, loc _ _ (hVU h1)]
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension (n x₀)) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension (n x₀))
    (fun y => pullback.fst A.hom V.ι ⁻¹ᵁ W (pullback.fst A.hom V.ι y))
    (top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hW _⟩) fun y => ?_
  rw [← dimy y]
  exact (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
    ((isPullback_morphismRestrict (pullback.fst A.hom V.ι) (W _)).paste_vert (IsPullback.of_hasPullback _ _))
    (hd (pullback.fst A.hom V.ι y))

end GlobalTheory.DualCon
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeUnitsLiftAlongThickening
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.DualOpen

theorem isUnit_of_isUnit_appTop_of_surjective {X Y : Scheme.{0}} (f : X ⟶ Y) [Surjective f]
    (a : Γ(Y, ⊤)) (h : IsUnit (f.appTop a)) : IsUnit a := by
  refine Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y _ => ?_
  obtain ⟨x, rfl⟩ := f.surjective y
  have hx : x ∈ X.basicOpen (f.appTop a) := by
    rw [Scheme.basicOpen_of_isUnit _ h]; trivial
  rw [← Scheme.preimage_basicOpen_top] at hx
  exact (Y.mem_basicOpen _ _ (by trivial)).1 hx

theorem units_lift_of_thickening : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A →
    ∀ (T₂ T₀ : Over S) (k : T₀ ⟶ T₂), IsAffine T₂.left → IsClosedImmersion k.left → Surjective k.left →
      Function.Surjective (Units.map (A ◁ k).left.appTop.hom.toMonoidHom) := by
  intro S A _ hA T₂ T₀ k _ _ _ u
  have hb₀ : Function.Bijective (snd A T₀).left.appTop.hom :=
    CubeOpen.bijective_appTop GlobalTheory.globalFns_holds A hA (IsPullback.of_hasPullback A.hom T₀.hom)
  have hk : Function.Surjective k.left.appTop.hom :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine k.left).2
  have hc : (A ◁ k).left ≫ (snd A T₂).left = (snd A T₀).left ≫ k.left := by
    rw [← Over.comp_left, ← Over.comp_left, whiskerLeft_snd]
  have hc' : ∀ w, (A ◁ k).left.appTop ((snd A T₂).left.appTop w) =
      (snd A T₀).left.appTop (k.left.appTop w) := by
    intro w
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
      ← Scheme.Hom.comp_appTop, hc]
  obtain ⟨v, hv⟩ := hb₀.2 (u : Γ((A ⊗ T₀).left, ⊤))
  obtain ⟨w, rfl⟩ := hk v
  let e := RingEquiv.ofBijective (snd A T₀).left.appTop.hom hb₀
  have hvu : IsUnit (k.left.appTop w) := by
    have : IsUnit (e (k.left.appTop w)) := by
      show IsUnit ((snd A T₀).left.appTop (k.left.appTop w)); rw [hv]; exact u.isUnit
    exact (isUnit_map_iff e _).1 this
  have hw : IsUnit w := isUnit_of_isUnit_appTop_of_surjective k.left w hvu
  obtain ⟨w', hw'⟩ := hw.map (snd A T₂).left.appTop.hom
  refine ⟨w', Units.ext ?_⟩
  show (A ◁ k).left.appTop (w' : Γ((A ⊗ T₂).left, ⊤)) = u
  rw [hw', hc', hv]

end GlobalTheory.DualOpen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyFiniteCoverByTranslatePairs
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCover

theorem cover : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ V : A.left.Opens, (V : Set A.left).Nonempty → ∃ (n : ℕ) (a : Fin n → (𝟙_ (Over (Sp K)) ⟶ A)), ⨆ i, ((𝟙 A * (toUnit A ≫ a i)).left ⁻¹ᵁ V ⊓ (𝟙 A * (toUnit A ≫ a i)⁻¹).left ⁻¹ᵁ V) = ⊤ := by
  classical
  intro K _ _ A _ hA V hV
  have := hA.smooth
  have := hA.proper
  have : GeometricallyIntegral A.hom :=
    forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hA.smooth hA.geomConnected
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian A.hom
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  let O : (𝟙_ (Over (Sp K)) ⟶ A) → A.left.Opens := fun a =>
    (𝟙 A * (toUnit A ≫ a)).left ⁻¹ᵁ V ⊓ (𝟙 A * (toUnit A ≫ a)⁻¹).left ⁻¹ᵁ V
  have key : ∀ y : 𝟙_ (Over (Sp K)) ⟶ A, ∃ a : 𝟙_ (Over (Sp K)) ⟶ A, ∀ p, y.left p ∈ O a := by
    intro y
    have := GlobalTheory.AbelianProjective.isIso_transl_left y
    have : IsIso ((toUnit A ≫ y) * 𝟙 A).left :=
      inferInstanceAs (IsIso ((Over.forget _).map ((toUnit A ≫ y) * 𝟙 A)))
    have : IsIso (ι[A] ≫ ((toUnit A ≫ y) * 𝟙 A)).left :=
      inferInstanceAs (IsIso ((Over.forget _).map (ι[A] ≫ ((toUnit A ≫ y) * 𝟙 A))))
    have h1 : ((((toUnit A ≫ y) * 𝟙 A).left ⁻¹ᵁ V : A.left.Opens) : Set A.left).Nonempty :=
      GlobalTheory.SS.AmpCub.nonempty_preimage _ hV
    have h2 : (((ι[A] ≫ ((toUnit A ≫ y) * 𝟙 A)).left ⁻¹ᵁ V : A.left.Opens) : Set A.left).Nonempty :=
      GlobalTheory.SS.AmpCub.nonempty_preimage _ hV
    have h3 := nonempty_preirreducible_inter (TopologicalSpace.Opens.isOpen _)
      (TopologicalSpace.Opens.isOpen _) h1 h2
    obtain ⟨a, ha⟩ := GlobalTheory.AbelianProjective.exists_point A
      ((((toUnit A ≫ y) * 𝟙 A).left ⁻¹ᵁ V ⊓ (ι[A] ≫ ((toUnit A ≫ y) * 𝟙 A)).left ⁻¹ᵁ V).isOpen).isLocallyClosed h3
    refine ⟨a, fun p => ?_⟩
    have e : y ≫ (𝟙 A * (toUnit A ≫ a)) = a ≫ ((toUnit A ≫ y) * 𝟙 A) := by
      simp [MonObj.comp_mul, ← Category.assoc]
    have e' : y ≫ (𝟙 A * (toUnit A ≫ a)⁻¹) = a ≫ ι[A] ≫ ((toUnit A ≫ y) * 𝟙 A) := by
      simp [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc]
      rfl
    have hp := ha p
    refine ⟨?_, ?_⟩
    · change (y.left ≫ (𝟙 A * (toUnit A ≫ a)).left) p ∈ V
      rw [← Over.comp_left, e, Over.comp_left]
      exact hp.1
    · change (y.left ≫ (𝟙 A * (toUnit A ≫ a)⁻¹).left) p ∈ V
      rw [← Over.comp_left, e', Over.comp_left]
      exact hp.2
  have htop : ⨆ a, O a = ⊤ := by
    by_contra hne
    have hc : ((⨆ a, O a : A.left.Opens) : Set A.left)ᶜ.Nonempty :=
      Set.nonempty_compl.2 fun h => hne (TopologicalSpace.Opens.ext h)
    obtain ⟨y, hy⟩ := GlobalTheory.AbelianProjective.exists_point A
      (TopologicalSpace.Opens.isOpen _).isClosed_compl.isLocallyClosed hc
    obtain ⟨a, ha⟩ := key y
    exact hy (IsLocalRing.closedPoint K) (TopologicalSpace.Opens.mem_iSup.2 ⟨a, ha _⟩)
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover (fun a => (O a : Set A.left))
    (fun a => (O a).isOpen) fun x _ => by
      have hx : x ∈ ⨆ a, O a := by rw [htop]; trivial
      exact Set.mem_iUnion.2 (TopologicalSpace.Opens.mem_iSup.1 hx)
  refine ⟨F.card, fun i => (F.equivFin.symm i).1, top_unique fun x _ => ?_⟩
  obtain ⟨a, ha, hx⟩ := Set.mem_iUnion₂.1 (hF (Set.mem_univ x))
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨F.equivFin ⟨a, ha⟩, by simp only [Equiv.symm_apply_apply]; exact hx⟩

end GlobalTheory.AbCover
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveLineBundleFamilyCalculusRules
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.FamCalc

variable {S : Scheme.{0}} {A : Over S}

theorem whisker_eq {Y T : Over S} (y : Y ⟶ T) : A ◁ y = lift (fst A Y) (snd A Y ≫ y) := by
  ext <;> simp

theorem lift_whisker {Y T Z : Over S} (y : Y ⟶ T) (a : Z ⟶ A) (t : Z ⟶ Y) :
    lift a t ≫ A ◁ y = lift a (t ≫ y) := by
  ext <;> simp

theorem pull_whisker_evc {T Y Z : Over S} {N : LB (A ⊗ T).left} (hN : N.IsLB) (y : Y ⟶ T) (a : Z ⟶ A)
    (t : Z ⟶ Y) :
    CechPic.pull (lift a t).left (CechPic.pull (A ◁ y).left (cls N hN)) = evc hN a (t ≫ y) := by
  rw [← pull_comp, ← Over.comp_left, lift_whisker, evc]

theorem evc_whisker {T Y : Over S} {N : LB (A ⊗ T).left} (hN : N.IsLB) (y : Y ⟶ T) :
    evc hN (fst A Y) (snd A Y ≫ y) = CechPic.pull (A ◁ y).left (cls N hN) := by
  rw [evc, whisker_eq]

theorem evc_ev_whisker {T Y Z : Over S} {N : LB (A ⊗ T).left} (hN : N.IsLB) (y : Y ⟶ T)
    (h : (ev N (fst A Y) (snd A Y ≫ y)).IsLB) (a : Z ⟶ A) (t : Z ⟶ Y) :
    evc h a t = evc hN a (t ≫ y) := by
  rw [evc_ev hN, lift_fst, lift_snd_assoc]

theorem famCalc : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], (∀ (T Y : Over S) (N : LB (A ⊗ T).left) (y : Y ⟶ T), Fam A N → Fam A (ev N (fst A Y) (snd A Y ≫ y))) ∧ (∀ (T U Y : Over S) (N : LB (A ⊗ T).left) (M : LB (A ⊗ U).left) (hN : Fam A N) (hM : Fam A M) (y : Y ⟶ T) (u : Y ⟶ U) (D : LB (A ⊗ Y).left) (hD : D.IsLB), (cls D hD = GlobalTheory.CechPic.pull (A ◁ y).left (cls N hN.isLB) + GlobalTheory.CechPic.pull (A ◁ u).left (cls M hM.isLB) ∨ cls D hD = GlobalTheory.CechPic.pull (A ◁ y).left (cls N hN.isLB) - GlobalTheory.CechPic.pull (A ◁ u).left (cls M hM.isLB)) → Fam A D) ∧ (∀ (T U Y : Over S) (N : LB (A ⊗ T).left) (M : LB (A ⊗ U).left) (hN : N.IsLB) (hM : M.IsLB) (y : Y ⟶ T) (u : Y ⟶ U), Same A N M y u ↔ GlobalTheory.CechPic.pull (A ◁ y).left (cls N hN) = GlobalTheory.CechPic.pull (A ◁ u).left (cls M hM)) ∧ (∀ (T U Y Z : Over S) (N : LB (A ⊗ T).left) (M : LB (A ⊗ U).left) (y : Y ⟶ T) (u : Y ⟶ U) (z : Z ⟶ Y), N.IsLB → M.IsLB → Same A N M y u → Same A N M (z ≫ y) (z ≫ u)) ∧ (∀ (T U Y Z : Over S) (N : LB (A ⊗ T).left) (M : LB (A ⊗ U).left) (y : Y ⟶ T) (z : Z ⟶ Y) (u : Z ⟶ U), N.IsLB → M.IsLB → (Same A (ev N (fst A Y) (snd A Y ≫ y)) M z u ↔ Same A N M (z ≫ y) u)) := by
  intro S A _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro T Y N y hN
    have h : (ev N (fst A Y) (snd A Y ≫ y)).IsLB := pull_isLB hN.isLB _
    refine ⟨h, (isAdditive_iff h).2 fun Z a a' t ↦ ?_⟩
    simp only [evc_ev_whisker hN.isLB y h]
    exact (isAdditive_iff hN.isLB).1 hN.add Z a a' (t ≫ y)
  · intro T U Y N M hN hM y u D hD hc
    refine ⟨hD, (isAdditive_iff hD).2 fun Z a a' t ↦ ?_⟩
    have aN := (isAdditive_iff hN.isLB).1 hN.add Z a a' (t ≫ y)
    have aM := (isAdditive_iff hM.isLB).1 hM.add Z a a' (t ≫ u)
    rcases hc with hc | hc
    · have e : ∀ b : Z ⟶ A, evc hD b t = evc hN.isLB b (t ≫ y) + evc hM.isLB b (t ≫ u) := fun b ↦ by
        rw [evc, hc, map_add, pull_whisker_evc, pull_whisker_evc]
      rw [e, e, e, aN, aM]
      abel
    · have e : ∀ b : Z ⟶ A, evc hD b t = evc hN.isLB b (t ≫ y) - evc hM.isLB b (t ≫ u) := fun b ↦ by
        rw [evc, hc, map_sub, pull_whisker_evc, pull_whisker_evc]
      rw [e, e, e, aN, aM]
      abel
  · intro T U Y N M hN hM y u
    rw [same_iff hN hM, evc_whisker, evc_whisker]
  · intro T U Y Z N M y u z hN hM h
    rw [same_iff hN hM] at h ⊢
    have e := congrArg (CechPic.pull (A ◁ z).left) h
    rwa [pull_evc, pull_evc, whiskerLeft_fst, whiskerLeft_snd_assoc, whiskerLeft_snd_assoc] at e
  · intro T U Y Z N M y z u hN hM
    have h : (ev N (fst A Y) (snd A Y ≫ y)).IsLB := pull_isLB hN _
    rw [same_iff h hM, same_iff hN hM, evc_ev_whisker hN y h, Category.assoc]

end GlobalTheory.FamCalc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineMilnorSquareOfCartesianRingSquare
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualOpen

theorem milnor_of_ring_square : ∀ (P C₁ C₂ C₀ : Type) [CommRing P] [CommRing C₁] [CommRing C₂] [CommRing C₀] (p₁ : P →+* C₁) (p₂ : P →+* C₂) (q₁ : C₁ →+* C₀) (q₂ : C₂ →+* C₀), q₁.comp p₁ = q₂.comp p₂ → (∀ x, p₁ x = 0 → p₂ x = 0 → x = 0) → (∀ a b, q₁ a = q₂ b → ∃ x, p₁ x = a ∧ p₂ x = b) → Function.Surjective q₂ → Milnor (spMap p₁) (spMap p₂) (spMap q₁) (spMap q₂) := by
  intro P C₁ C₂ C₀ _ _ _ _ p₁ p₂ q₁ q₂ hw hinj hsurj hq₂
  have hwc : CommRingCat.ofHom p₁ ≫ CommRingCat.ofHom q₁ = CommRingCat.ofHom p₂ ≫ CommRingCat.ofHom q₂ := by
    ext x; exact congrArg (fun f : P →+* C₀ => f x) hw
  have H : IsPullback (CommRingCat.ofHom p₁) (CommRingCat.ofHom p₂) (CommRingCat.ofHom q₁) (CommRingCat.ofHom q₂) := by
    refine IsPullback.of_map (forget CommRingCat) hwc ?_
    rw [Types.isPullback_iff]
    refine ⟨by rw [← Functor.map_comp, ← Functor.map_comp, hwc], ?_, ?_⟩
    · rintro x y ⟨h1, h2⟩
      have h1' : p₁ x = p₁ y := h1
      have h2' : p₂ x = p₂ y := h2
      exact sub_eq_zero.mp (hinj _ (by rw [map_sub, h1', sub_self]) (by rw [map_sub, h2', sub_self]))
    · intro a b hab
      exact hsurj a b hab
  refine ⟨inferInstance, inferInstance, inferInstance, IsClosedImmersion.spec_of_surjective _ hq₂, ?_, ?_⟩
  · simp only [spMap, ← Spec.map_comp, hwc]
  · refine IsPullback.of_iso H (Scheme.ΓSpecIso _).symm (Scheme.ΓSpecIso _).symm (Scheme.ΓSpecIso _).symm
      (Scheme.ΓSpecIso _).symm ?_ ?_ ?_ ?_ <;>
    simp [spMap, Scheme.ΓSpecIso_inv_naturality]

end GlobalTheory.DualOpen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineOpenMeetingFibresPullbackSpecRingHom
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem affine_preimage_pullback_meets_fibres {R R' : Type} [CommRing R] [CommRing R'] (a : R →+* R')
    (A : Over (Sp R)) (W : A.left.Opens) : IsAffineOpen W →
    (∀ t ∈ Set.range (spMap a), ∃ x ∈ W, A.hom x = t) →
    ∃ V : ((Over.pullback (spMap a)).obj A).left.Opens, IsAffineOpen V ∧
      ∀ s : Sp R', ∃ x ∈ V, ((Over.pullback (spMap a)).obj A).hom x = s := by
  intro hW hfib
  haveI : IsAffineHom (pullback.fst A.hom (spMap a)) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _).flip inferInstance
  refine ⟨(pullback.fst A.hom (spMap a)) ⁻¹ᵁ W, hW.preimage _, ?_⟩
  intro s
  obtain ⟨x, hxW, hx⟩ := hfib (spMap a s) ⟨s, rfl⟩
  obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback (f := A.hom) (g := spMap a) x s hx
  exact ⟨z, by show (pullback.fst A.hom (spMap a)) z ∈ W; rw [hz1]; exact hxW, hz2⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineOpenToFunctionFieldInjectiveAndFraction
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

namespace GlobalTheory.GenFrac

theorem injective_and_frac : ∀ (X : Scheme.{0}) (V : X.Opens) [IsIntegral V.toScheme] (W : X.affineOpens), W.1 ≤ V → ∀ (ρW : Γ(X, W.1) →+* V.toScheme.functionField), spMap ρW ≫ GlobalTheory.LogKS.chart W = V.toScheme.fromSpecStalk (genericPoint V.toScheme) ≫ V.ι → Function.Injective ρW ∧ ∀ x : V.toScheme.functionField, ∃ a b : Γ(X, W.1), ρW b ≠ 0 ∧ x * ρW b = ρW a := by
  intro X V _ W hWV ρW h
  set η := genericPoint V.toScheme with hη
  have hx : V.ι η ∈ W.1 := by
    have h1 := congrArg (fun f : Spec (V.toScheme.presheaf.stalk η) ⟶ X =>
      f (IsLocalRing.closedPoint (V.toScheme.presheaf.stalk η))) h
    have h3 : (V.toScheme.fromSpecStalk η ≫ V.ι)
        (IsLocalRing.closedPoint (V.toScheme.presheaf.stalk η)) = V.ι η :=
      congrArg V.ι (Scheme.fromSpecStalk_closedPoint (x := η))
    rw [← h1.trans h3]
    have h2 : Set.range (W.2.fromSpec) = (W.1 : Set X) := W.2.range_fromSpec
    rw [← SetLike.mem_coe, ← h2]
    exact ⟨_, rfl⟩
  have he : CommRingCat.ofHom ρW = X.presheaf.germ W.1 (V.ι η) hx ≫ V.ι.stalkMap η := by
    apply Spec.map_injective
    have hW : IsAffineOpen W.1 := W.2
    haveI : IsOpenImmersion hW.fromSpec := hW.isOpenImmersion_fromSpec
    rw [← cancel_mono hW.fromSpec, Spec.map_comp, Category.assoc]
    refine Eq.trans h ?_
    rw [← Scheme.SpecMap_stalkMap_fromSpecStalk, ← W.2.fromSpecStalk_eq_fromSpecStalk hx]
    rfl
  have he' : ∀ a, ρW a = V.ι.stalkMap η (X.presheaf.germ W.1 (V.ι η) hx a) := fun a =>
    congrArg (fun f : Γ(X, W.1) ⟶ V.toScheme.presheaf.stalk η => f a) he
  have hbij : Function.Bijective (V.ι.stalkMap η) := ConcreteCategory.bijective_of_isIso _
  refine ⟨?_, fun x => ?_⟩
  · have hiso : IsIso (V.ι.app W.1) := V.ι.isIso_app W.1 (by simpa using hWV)
    have hinj1 : Function.Injective (V.ι.app W.1) := (ConcreteCategory.bijective_of_isIso _).1
    have hinj2 := germ_injective_of_isIntegral V.toScheme (U := V.ι ⁻¹ᵁ W.1) η hx
    intro a b hab
    rw [he', he', Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.germ_stalkMap_apply] at hab
    exact hinj1 (hinj2 hab)
  · obtain ⟨y, rfl⟩ := hbij.2 x
    letI : Algebra Γ(X, W.1) (X.presheaf.stalk (V.ι η)) :=
      (X.presheaf.germ W.1 (V.ι η) hx).hom.toAlgebra
    haveI : IsLocalization.AtPrime (X.presheaf.stalk (V.ι η))
        (W.2.primeIdealOf ⟨V.ι η, hx⟩).asIdeal := W.2.isLocalization_stalk ⟨V.ι η, hx⟩
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj
      (W.2.primeIdealOf ⟨V.ι η, hx⟩).asIdeal.primeCompl y
    have hu := IsLocalization.map_units (X.presheaf.stalk (V.ι η)) b
    refine ⟨a, b, ?_, ?_⟩
    · rw [he']
      exact (hu.map (V.ι.stalkMap η).hom).ne_zero
    · rw [he', he']
      exact (map_mul (V.ι.stalkMap η).hom _ _).symm.trans (congrArg (V.ι.stalkMap η) hab)

end GlobalTheory.GenFrac
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleSectionsAvoidClosedPoints
section
set_option autoImplicit false

noncomputable section

open NumberField CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.CechPic

namespace GlobalTheory.GenFibreSecs

theorem cls_comb {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {ι : Type} [Fintype ι]
    (L : ι → HermLB p) (n : ι → ℤ) :
    cls _ (ArInt.comb L n).isLB = ∑ i, n i • cls _ (L i).isLB := by
  have hz (A : HermLB p) (m : ℤ) : cls _ (zp A m).isLB = m • cls _ A.isLB := by
    have e : cls _ (zp A m).isLB = cls _ (isLB_lbPow A.isLB m.toNat) + -cls _ (isLB_lbPow A.isLB (-m).toNat) :=
      (cls_tens (A.pow m.toNat).isLB (A.pow (-m).toNat).dual.isLB _).trans
        (congrArg _ (cls_dual (A.pow (-m).toNat).isLB _))
    rw [e, cls_lbPow A.isLB, cls_lbPow A.isLB, ← natCast_zsmul, ← natCast_zsmul, ← sub_eq_add_neg,
      ← sub_smul, Int.toNat_sub_toNat_neg]
  rw [← Finset.sum_map_toList, ArInt.comb]
  induction (Finset.univ : Finset ι).toList with
  | nil =>
    exact (cls_eq_zero_iff (LB.isLB_triv X)).2 ⟨⟨fun _ => 1⟩, fun _ _ => by simp only [map_one, mul_one]⟩
  | cons i l ih =>
    rw [List.foldr_cons, List.map_cons, List.sum_cons, ← ih, ← hz]
    exact cls_tens _ _ _

theorem exists_secs_of_isGenerated {S T : Type} [CommRing S] [IsDomain S] [Field T] [Algebra S T] [IsFractionRing S T]
    {X X' : Scheme.{0}} {p : X ⟶ Sp S} {p' : X' ⟶ Sp T} {φ : X' ⟶ X}
    (H : IsPullback φ p' p (spMap (algebraMap S T))) [CompactSpace X] [IsSeparated p] {B : LB X} (hB : B.IsLB)
    (h : IsGenerated (B.pull φ)) : ∃ (m : ℕ) (s : Fin m → B.Sec), ∀ w : X', ∃ i, φ w ∈ nonzeroLocus (s i) := by
  have hB' := h.isLB
  obtain ⟨m, t, ht⟩ := h
  choose a ha s hs using fun i => exists_extend (nonZeroDivisors S) H hB hB'
    ((isGen_iff (idIso _)).1 (idIso_isGen hB')) (t i)
  refine ⟨m, s, fun w => ?_⟩
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (ht.ge (Set.mem_univ w))
  obtain ⟨j, hj⟩ := exists_chart hB (φ w)
  obtain ⟨k, hk⟩ := exists_chart hB' w
  refine ⟨i, (mem_nonzeroLocus_iff_isUnit (s i) hj).2 ?_⟩
  have u : IsUnit (gs φ w _ ((s i).f j)) := by
    rw [hs i w j k hj hk]
    refine IsUnit.mul ?_ ((Units.isUnit _).mul ((mem_nonzeroLocus_iff_isUnit (t i) hk).1 hi))
    rw [H.w, cst_comp]
    have h0 : algebraMap S T (a i) ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (ha i)
    refine IsUnit.of_mul_eq_one (cst p' w (algebraMap S T (a i))⁻¹) ?_
    rw [← H1.cst_mul, mul_inv_cancel₀ h0, H1.cst_one]
  rw [gs_stalkMap φ w _ hj] at u
  exact isUnit_of_map_unit _ _ u

theorem main : ∀ {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y) (L M : HermLB V.p),
    IsAmpleLB (L.B.pull V.j) → ∃ (n m : ℕ) (s : Fin m → (ArInt.comb ![L, M] ![(n : ℤ), 1]).B.Sec),
      ∀ w : V.G, IsClosed ({w} : Set V.G) → ∃ i, V.j w ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s i) := by
  intro F _ _ Y V L M hL
  obtain ⟨N, ι, _, hι⟩ := V.ar.isProjOver
  have := isProper_str (𝓞 F) N
  have : IsProper V.p := hι ▸ inferInstance
  have : IsProper (V.π ≫ Y.str) := MorphismProperty.of_isPullback (P := @IsProper) V.pb inferInstance
  have : CompactSpace V.X := QuasiCompact.compactSpace_of_compactSpace V.p
  have hM := LB.isLB_pull M.isLB V.j
  obtain ⟨n, hn⟩ := (AmpleDominates.eventually_isGenerated (V.π ≫ Y.str) hL (isLB_dual hM)).exists
  have hC := (ArInt.comb ![L, M] ![(n : ℤ), 1]).isLB
  have hG : IsGenerated ((ArInt.comb ![L, M] ![(n : ℤ), 1]).B.pull V.j) := by
    refine hn.of_lbIso (LB.isLB_pull hC _) ((cls_eq_iff (LB.isLB_pull hC _) hn.isLB).1 ?_)
    rw [cls_div (isLB_lbPow hL.isLB n) (isLB_dual hM), cls_lbPow hL.isLB, cls_dual hM, cls_pull hC, cls_pull L.isLB,
      cls_pull M.isLB, cls_comb]
    simp [Fin.sum_univ_two]
  obtain ⟨m, s, hs⟩ := exists_secs_of_isGenerated V.pb hC hG
  exact ⟨n, m, s, fun w _ => hs w⟩

end GlobalTheory.GenFibreSecs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSubmoduleSecondFactorStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.augmentation_submodule_second_factor : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ v, X.Good v → (∀ (t : E →ₐ[F] Fv F v) (k : ℤ), k ≠ 0 → chrW X.ν t (unifAt v) ^ k ≠ 1) →
    ∀ N : Submodule ℂ ((Fin a' × Fin (a + a') → Fv F v) → ℂ), augAt om' v ≤ N → N ≤ SB _ →
      (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ N, ∀ φ₁ ∈ SB _, Acts (evFin F v) (om' (1, h)) φ φ₁ → φ₁ ∈ N) →
      N = augAt om' v ∨ N = SB _ := by
  first | exact @GlobalTheory.IrrCoinvSmall.irr_small | exact GlobalTheory.IrrCoinvSmall.irr_small | (intros; apply GlobalTheory.IrrCoinvSmall.irr_small <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseIdealSheafOfIdealComapSpecMapSupportStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseIdealSheafOfIdeal_comap_specMap_support : (∀ (R : Type) [CommRing R] (W W' : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)) (π : W' ⟶ W) (J : Ideal R), (baseIdeal f J).comap π = baseIdeal (π ≫ f) J) ∧ (∀ (R C : Type) [CommRing R] [CommRing C] (φ : R →+* C) (W : Scheme.{0}) (p : W ⟶ Spec (CommRingCat.of C)) (J : Ideal R), baseIdeal (p ≫ Spec.map (CommRingCat.ofHom φ)) J = baseIdeal p (J.map φ)) ∧ (∀ (R : Type) [CommRing R] (W : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)) (J : Ideal R) (x : W), x ∈ (baseIdeal f J).support ↔ J ≤ (f x).asIdeal) := by
  first | exact @GlobalTheory.FormalAlg.baseIdeal_calculus | exact GlobalTheory.FormalAlg.baseIdeal_calculus | (intros; apply GlobalTheory.FormalAlg.baseIdeal_calculus <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseIdealSheafOfIdealSpecBijectiveCalculusStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseIdealSheafOfIdeal_spec_bijective_calculus : (∀ (C : Type) [CommRing C], Function.Bijective (fun a : Ideal C => baseIdeal (𝟙 (Spec (CommRingCat.of C))) a) ∧ (∀ a b : Ideal C, baseIdeal (𝟙 (Spec (CommRingCat.of C))) (a ⊔ b) = baseIdeal (𝟙 _) a ⊔ baseIdeal (𝟙 _) b)) ∧ (∀ (W : Scheme.{0}) (V : W.affineOpens) (C : Type) [CommRing C] (φ : Γ(W, V.1) →+* C) (J : W.IdealSheafData), J.comap (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) = baseIdeal (𝟙 (Spec (CommRingCat.of C))) ((J.ideal V).map φ)) := by
  first | exact @GlobalTheory.FormalAlg.specIdeal | exact GlobalTheory.FormalAlg.specIdeal | (intros; apply GlobalTheory.FormalAlg.specIdeal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoveringLeFromMeasureStatement
section
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covering_le_from_measure : Gram → Meas → GlobalTheory.CovTop.Rat → CoreLe := by
  first | exact @GlobalTheory.CoreSlope.coreLe_of_gram_meas_rat | exact GlobalTheory.CoreSlope.coreLe_of_gram_meas_rat | (intros; apply GlobalTheory.CoreSlope.coreLe_of_gram_meas_rat <;> assumption)
end

