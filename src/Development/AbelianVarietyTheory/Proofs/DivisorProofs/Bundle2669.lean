import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SplitTorusHomEqOneOfNilpotent
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0006
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0002
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2546
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2547
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2549
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2367
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2376
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2389
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2485
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2558
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusHomEqOfNilpotent
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory

theorem splitTorus_hom_eq_of_nilpotent : ∀ (A κ : Type) [CommRing A] [IsLocalRing A] [CommRing κ]
    (π : A →+* κ), Function.Surjective π → IsNilpotent (RingHom.ker π) → ∀ (X : Type)
    [AddCommGroup X] (H : Over (Sp A)) [GrpObj H] [IsCommMonObj H]
    (i₁ i₂ : splitTorus (Sp A) X ⟶ H), IsMonHom i₁ → IsMonHom i₂ →
    GlobalTheory.SplitTorus.bcMap (spMap π) X ≫ i₁.left = GlobalTheory.SplitTorus.bcMap (spMap π) X ≫ i₂.left →
    i₁ = i₂ := by
  intro A κ _ _ _ π hπ hJ X _ H _ _ i₁ i₂ h₁ h₂ h
  set J := RingHom.ker π
  haveI : IsMonHom i₂⁻¹ := inferInstance
  haveI hf : IsMonHom (i₁ * i₂⁻¹) := GlobalTheory.Serre.isMonHom_mul _ _
  set r : Sp (A ⧸ J) ⟶ Sp A := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
  let e : A ⧸ J ≃+* κ := RingHom.quotientKerEquivOfSurjective hπ
  have hr : r = spMap e.symm.toRingHom ≫ spMap π := by
    simp only [r, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, Ideal.Quotient.mk_eq_mk]
    rw [RingEquiv.eq_symm_apply]
    rfl

  obtain ⟨l, hl⟩ : ∃ l, l ≫ SplitTorus.bcMap (spMap π) X = pullback.fst (splitTorus (Sp A) X).hom r :=
    ⟨_, (SplitTorus.isPullback_bcMap (spMap π) X).lift_fst (pullback.fst (splitTorus (Sp A) X).hom r)
      (pullback.snd (splitTorus (Sp A) X).hom r ≫ spMap e.symm.toRingHom)
      (by rw [pullback.condition, Category.assoc, ← hr])⟩
  let t : Over.mk (pullback.fst (splitTorus (Sp A) X).hom r ≫ (splitTorus (Sp A) X).hom) ⟶ splitTorus (Sp A) X := Over.homMk (pullback.fst (splitTorus (Sp A) X).hom r)
  have ht : t ≫ i₁ = t ≫ i₂ := by
    ext
    simp only [t, Over.comp_left, Over.homMk_left]
    simp only [← hl, Category.assoc, h]
  have ht1 : t ≫ (i₁ * i₂⁻¹) = t ≫ (toUnit _ ≫ η[H]) := by
    rw [MonObj.comp_mul, GrpObj.comp_inv, ht, mul_inv_cancel, ← Category.assoc,
      Hom.one_def]
    congr 1
  have key := splitTorus_hom_eq_one_of_nilpotent A J hJ X H (i₁ * i₂⁻¹) hf (by
    ext
    · apply pullback.hom_ext
      · simp only [Over.pullback_map_left, pullback.lift_fst]
        exact congrArg CommaMorphism.left ht1
      · simp only [Over.pullback_map_left, pullback.lift_snd])
  rw [← Hom.one_def, mul_inv_eq_one] at key
  exact key

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusHomExtOfEqModMaximalIdealPow
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps (torus lieMap lieAdd LieCongr IsLieLinear lieCoord)

namespace GlobalTheory

open TorusNil TorusLocal in

theorem splitTorus_hom_ext_of_forall_pow (R : Type) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (A : Type) [AddCommGroup A] (B : Over (Spec (CommRingCat.of R)))
    (hB : IsSeparated B.hom) (f g : splitTorus (Spec (CommRingCat.of R)) A ⟶ B)
    (hn : ∀ n : ℕ, (Over.pullback (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1)))))).map f =
      (Over.pullback (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1)))))).map g) : f = g := by
  set t := torusPt R A (AddMonoidAlgebra.of R A) with ht
  have h1 : t ≫ f = t ≫ g := by
    refine pt_ext_of_quotients (fun n : ℕ =>
      (IsLocalRing.maximalIdeal R ^ (n + 1)).map (algebraMap R (AddMonoidAlgebra R A)))
      eq_zero_of_forall_mem_map_pow fun n => ?_
    rw [← Category.assoc, ← Category.assoc _ t]
    exact comp_eq_of_pullback_map_eq (hn n) _
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift _
        (algebraMap R (AddMonoidAlgebra R A ⧸ (IsLocalRing.maximalIdeal R ^ (n + 1)).map
          (algebraMap R (AddMonoidAlgebra R A)))) (fun a ha => by
          rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq_zero_iff_mem]
          exact Ideal.mem_map_of_mem _ ha))))
      (by rw [← Spec.map_comp]; rfl)
  have := isIso_torusPt_of R A
  apply Over.OverMorphism.ext
  rw [← cancel_epi t.left, ← Over.comp_left, h1, ← Over.comp_left]

end GlobalTheory

open GlobalTheory in
example : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (A : Type) [AddCommGroup A] (B : Over (Spec (CommRingCat.of R))), IsSeparated B.hom → ∀ (f g : splitTorus (Spec (CommRingCat.of R)) A ⟶ B), (∀ n : ℕ, (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1)))))).map f = (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1)))))).map g) → f = g := GlobalTheory.splitTorus_hom_ext_of_forall_pow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusHomTrivialModPow
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps (torus lieMap lieAdd LieCongr IsLieLinear lieCoord)

namespace GlobalTheory

namespace TorusThicken

theorem pullback_map_eq_of_comp {S S' S'' : Scheme.{0}} (s : S'' ⟶ S') (p : S' ⟶ S) {V W : Over S}
    {a b : V ⟶ W} (h : (Over.pullback p).map a = (Over.pullback p).map b) :
    (Over.pullback (s ≫ p)).map a = (Over.pullback (s ≫ p)).map b := by
  have ha := (Over.pullbackComp s p).hom.naturality a
  have hb := (Over.pullbackComp s p).hom.naturality b
  simp only [Functor.comp_map] at ha hb
  rw [← cancel_mono ((Over.pullbackComp s p).hom.app W), ha, hb, h]

theorem pullback_pullback_map_eq_of_comp {S S' S'' : Scheme.{0}} (s : S'' ⟶ S') (p : S' ⟶ S)
    {V W : Over S} {a b : V ⟶ W} (h : (Over.pullback (s ≫ p)).map a = (Over.pullback (s ≫ p)).map b) :
    (Over.pullback s).map ((Over.pullback p).map a) = (Over.pullback s).map ((Over.pullback p).map b) := by
  have ha := (Over.pullbackComp s p).hom.naturality a
  have hb := (Over.pullbackComp s p).hom.naturality b
  simp only [Functor.comp_map] at ha hb
  rw [← cancel_epi ((Over.pullbackComp s p).hom.app V), ← ha, ← hb, h]

end TorusThicken

open TorusThicken in

theorem splitTorus_hom_trivial_mod_pow (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (A : Type) [AddCommGroup A] (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
    (f : splitTorus (Spec (CommRingCat.of R)) A ⟶ G) (hf : IsMonHom f)
    (h : (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R (IsLocalRing.ResidueField R)).map f =
      (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R (IsLocalRing.ResidueField R)).map 1) (n : ℕ) :
    (Over.pullback (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1)))))).map f =
      (Over.pullback (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1)))))).map 1 := by
  set I := IsLocalRing.maximalIdeal R ^ (n + 1) with hI
  set p := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) with hp
  have hIt : I ≠ ⊤ := fun e => (IsLocalRing.maximalIdeal.isMaximal R).ne_top
    (top_le_iff.1 (e ▸ Ideal.pow_le_self (Nat.succ_ne_zero n)))
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hIt
  have : IsLocalRing (R ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  set J : Ideal (R ⧸ I) := (IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk I) with hJ
  have hJn : IsNilpotent J := ⟨n + 1, by
    rw [hJ, ← Ideal.map_pow, ← hI, Ideal.map_quotient_self]; rfl⟩
  set q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) with hq
  let ℓ : IsLocalRing.ResidueField R →+* (R ⧸ I) ⧸ J :=
    Ideal.Quotient.lift (IsLocalRing.maximalIdeal R) ((Ideal.Quotient.mk J).comp (Ideal.Quotient.mk I))
      (fun a ha => by
        rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mem_map_of_mem _ ha)
  have hsq : q ≫ p = Spec.map (CommRingCat.ofHom ℓ) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R))) := by
    rw [hq, hp, ← Spec.map_comp, ← Spec.map_comp]; rfl

  have h1 : (Over.pullback q).map ((Over.pullback p).map f) =
      (Over.pullback q).map ((Over.pullback p).map 1) := by
    apply pullback_pullback_map_eq_of_comp
    rw [hsq]
    exact pullback_map_eq_of_comp _ _ h
  obtain ⟨e, he, -⟩ := splitTorus_baseChange _ _ p A
  have hg : IsMonHom (e.hom ≫ (Over.pullback p).map f) := inferInstance
  have hp1 : (Over.pullback p).map (1 : splitTorus (Spec (CommRingCat.of R)) A ⟶ G) = 1 :=
    Functor.map_one _
  have key := splitTorus_hom_eq_one_of_nilpotent (R ⧸ I) J hJn A _ (e.hom ≫ (Over.pullback p).map f) hg
    (by rw [Functor.map_comp, h1, hp1, ← Functor.map_comp, ← Hom.one_def, MonObj.comp_one])
  rw [← cancel_epi e.hom, key, ← Hom.one_def, hp1, MonObj.comp_one]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareDecompositionExtendsFromGenericFibreSemiAbStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.squareDecomposition_extends_from_genericFibre_semiAbelian : ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsNoetherianRing R'] [IsIntegrallyClosed R'] [IsLocalRing R'] (G : Over (Sp R')) [GrpObj G], IsSemiAbelian G → ∀ (L M : LB G.left), L.IsLB → M.IsLB → SqDec ((Over.pullback (jK R')).obj G) (L.pull (pullback.fst G.hom (jK R'))) (M.pull (pullback.fst G.hom (jK R'))) → SqDec G L M := by
  first | exact @GlobalTheory.GenericDec.sqDec_of_generic | exact GlobalTheory.GenericDec.sqDec_of_generic | (intros; apply GlobalTheory.GenericDec.sqDec_of_generic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareDecompositionOfBaseChangeAlongIdentityStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.squareDecomposition_of_baseChange_along_identity : ∀ (F : Type) [CommRing F] (A : Over (Sp F)) [GrpObj A] (L M : LB A.left), L.IsLB → M.IsLB → SqDec ((Over.pullback (spMap (RingHom.id F))).obj A) (L.pull (pullback.fst A.hom (spMap (RingHom.id F)))) (M.pull (pullback.fst A.hom (spMap (RingHom.id F)))) → SqDec A L M := by
  first | exact @GlobalTheory.SqDecIdBC.sqDec_of_baseChange_id | exact GlobalTheory.SqDecIdBC.sqDec_of_baseChange_id | (intros; apply GlobalTheory.SqDecIdBC.sqDec_of_baseChange_id <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTheoremPicClassOverOpen
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SquareOpen

theorem pull_mul_add_pull_mul_inv_of_opens : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (U : S.Opens) (c : Pic (A.hom ⁻¹ᵁ U).toScheme) (Y : Over S) (l : (Y ⟶ A) → (Y.left ⟶ (A.hom ⁻¹ᵁ U).toScheme)), (∀ y, Y.hom y ∈ U) → (∀ p, l p ≫ (A.hom ⁻¹ᵁ U).ι = p.left) → ∀ x a : Y ⟶ A, GlobalTheory.CechPic.pull (l (x * a)) c + GlobalTheory.CechPic.pull (l (x * a⁻¹)) c = 2 • GlobalTheory.CechPic.pull (l (x)) c + GlobalTheory.CechPic.pull (l (a)) c + GlobalTheory.CechPic.pull (l (a⁻¹)) c - 2 • GlobalTheory.CechPic.pull (l ((1 : Y ⟶ A))) c := by
  intro S _ A _ hA U c Y l hY hl x a
  let A' := (Over.pullback U.ι).obj A
  have hA' : IsAbelianScheme A' := ReciprocityTheory.ChartRestriction.G.Out.TLinPf.isAb_pullback U.ι A hA
  have h := isGrpPullback_pullback A U.ι
  let e := (isPullback_morphismRestrict A.hom U).flip.isoPullback
  have he : e.inv ≫ (A.hom ⁻¹ᵁ U).ι = pullback.fst A.hom U.ι := by
    rw [Iso.inv_comp_eq, IsPullback.isoPullback_hom_fst]
  have hrange : Set.range Y.hom.base ⊆ Set.range U.ι.base := by
    rintro _ ⟨y, rfl⟩
    rw [U.range_ι]
    exact hY y
  let Y' : Over U.toScheme := Over.mk (IsOpenImmersion.lift U.ι Y.hom hrange)
  have hY' : Y'.hom ≫ U.ι = Y.hom := IsOpenImmersion.lift_fac _ _ _
  let τ : Over.mk (Y'.hom ≫ U.ι) ⟶ Y := Over.homMk (𝟙 Y.left) (by erw [Category.id_comp]; exact hY'.symm)
  have lift : ∀ p : Y ⟶ A, ∃ p' : Y' ⟶ A', pushHom h Y' p' = τ ≫ p := by
    intro p
    refine ⟨Over.homMk (pullback.lift p.left Y'.hom (by rw [Over.w p, hY'])) (by
      exact pullback.lift_snd _ _ _), ?_⟩
    apply Over.OverMorphism.ext
    simp only [pushHom, pushPt, τ, MonoidHom.mk'_apply, Over.homMk_left, Over.comp_left]
    rw [pullback.lift_fst]
    exact (Category.id_comp _).symm
  have key : ∀ (p : Y ⟶ A) (p' : Y' ⟶ A'), pushHom h Y' p' = τ ≫ p → l p = p'.left ≫ e.inv := by
    intro p p' hp
    rw [← cancel_mono (A.hom ⁻¹ᵁ U).ι, hl, Category.assoc, he]
    have := congrArg (fun q => q.left) hp
    simp only [pushHom, pushPt, τ, MonoidHom.mk'_apply, Over.homMk_left, Over.comp_left] at this
    exact (Category.id_comp _).symm.trans this.symm
  obtain ⟨x', hx⟩ := lift x
  obtain ⟨a', ha⟩ := lift a
  have hmul : pushHom h Y' (x' * a') = τ ≫ (x * a) := by
    rw [map_mul, hx, ha, MonObj.comp_mul]
  have hainv : pushHom h Y' a'⁻¹ = τ ≫ a⁻¹ := by
    rw [map_inv, ha, GrpObj.comp_inv]
  have hinv : pushHom h Y' (x' * a'⁻¹) = τ ≫ (x * a⁻¹) := by
    rw [map_mul, hainv, hx, MonObj.comp_mul]
  have hone : pushHom h Y' 1 = τ ≫ 1 := by
    rw [map_one, MonObj.comp_one]
  rw [key _ _ hmul, key _ _ hinv, key _ _ hx, key _ _ ha, key _ _ hainv, key _ _ hone]
  simp only [pull_comp]
  exact GlobalTheory.T.theorem_of_square_cechPicard_translates U.toScheme A' hA' (pull e.inv c) Y' x' a'

end GlobalTheory.SquareOpen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkStepMono
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.QCoh (freeModule)

namespace GlobalTheory.FlagZ.Univ

variable {X : Scheme.{0}} {N : ℕ}

variable (X N) in

def stalkStd (x : X) : Module.Basis (Fin N) (X.presheaf.stalk x) ((freeModule X (Fin N)).presheaf.stalk x :) :=
  (VB.isFrame_freeFrame X (Fin N)).stalkBasis x trivial

def colSpan {x : X} (g : Matrix (Fin N) (Fin N) (X.presheaf.stalk x)) (l : ℕ) :
    Submodule (X.presheaf.stalk x) ((freeModule X (Fin N)).presheaf.stalk x :) :=
  Submodule.span _ {v | ∃ j : Fin N, (j : ℕ) < l ∧ v = ∑ i, g i j • stalkStd X N x i}

end GlobalTheory.FlagZ.Univ

namespace GlobalTheory.FlagZ.Univ

variable (ι : Type) [Fintype ι] (N : ℕ)

def stalkStep (τ : ι) (l : ℕ) (y : Fl ι N) :
    Submodule ((Fl ι N).presheaf.stalk y) ((freeModule (Fl ι N) (Fin N)).presheaf.stalk y :) :=
  ⨅ (g : ι → GL (Fin N) ((Fl ι N).presheaf.stalk y))
    (_ : flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g = (Fl ι N).fromSpecStalk y), colSpan (g τ).1 l

def sub (τ : ι) (l : ℕ) : VB.Sub (freeModule (Fl ι N) (Fin N)) := VB.Sub.ofStalks (stalkStep ι N τ l)

def freeIso : (Scheme.Modules.pullback (flStr ι N)).obj (freeModule (Sp ℤ) (Fin N)) ≅ freeModule (Fl ι N) (Fin N) :=
  ((VB.isFrame_freeFrame (Sp ℤ) (Fin N)).pullback (flStr ι N)).iso (VB.isFrame_freeFrame _ (Fin N))

def F (τ : ι) (i : Fin (N + 1)) : (Fl ι N).Modules := (sub ι N τ i).toMod

def incl (τ : ι) (i : Fin (N + 1)) : F ι N τ i ⟶ (Scheme.Modules.pullback (flStr ι N)).obj (freeModule (Sp ℤ) (Fin N)) :=
  (sub ι N τ i).incl ≫ (freeIso ι N).inv

theorem stalkStep_mono (τ : ι) {l l' : ℕ} (h : l ≤ l') (y : Fl ι N) : stalkStep ι N τ l y ≤ stalkStep ι N τ l' y :=
  iInf_mono fun _ => iInf_mono fun _ => Submodule.span_mono fun _ ⟨j, hj, e⟩ => ⟨j, lt_of_lt_of_le hj h, e⟩

def step (τ : ι) (i : Fin N) : F ι N τ i.castSucc ⟶ F ι N τ i.succ :=
  (sub ι N τ i.succ).lift (sub ι N τ i.castSucc).incl fun _ s x hx => by
    exact stalkStep_mono ι N τ (by simp [Fin.val_succ]) x ((sub ι N τ i.castSucc).incl_app_mem s x hx)

theorem step_incl (τ : ι) (i : Fin N) : step ι N τ i ≫ incl ι N τ i.succ = incl ι N τ i.castSucc :=
  (Category.assoc _ _ _).symm.trans (congrArg (· ≫ (freeIso ι N).inv) (VB.Sub.lift_incl _ _ _))

variable {ι N} in

def Lifts {T : Scheme.{0}} (g : T ⟶ Sp ℤ)
    (fl' : ι → Vert.Flag ((Scheme.Modules.pullback g).obj (freeModule (Sp ℤ) (Fin N))) N) (g' : T ⟶ Fl ι N) : Prop :=
  ∃ w : g' ≫ flStr ι N = g, ∀ a i, ∃ e : (Scheme.Modules.pullback g').obj (F ι N a i) ≅ (fl' a).F i,
    e.hom ≫ (fl' a).ι i = (Scheme.Modules.pullback g').map (incl ι N a i) ≫
      (Scheme.Modules.pullbackComp g' (flStr ι N)).hom.app _ ≫ (Scheme.Modules.pullbackCongr w).hom.app _

end GlobalTheory.FlagZ.Univ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepLatZero
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.GeometryOfNumbersTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Toroidal GlobalTheory.Mean4O GlobalTheory.LieHt

namespace GlobalTheory.LieRead

variable {D : D7} (O : Setup D)

def FibTie (y : Pt O.s) {K : Type} [Field K] [NumberField K] (F : SemiFib K) (ι : K →+* Qb) : Prop :=
  ∃ (jF : O.κ.c.F →+* K) (yO : Sp (𝓞 K) ⟶ O.s.T.Z.X) (ψ : F.G.left ⟶ O.s.T.Z.t.G.left),
    ι.comp jF = y.fK ∧
    spMap (ι.comp (algebraMap (𝓞 K) K)) ≫ yO = y.y ≫ genι O.s.T.Z ∧
    IsGrpPullback F.G O.s.T.Z.t.G yO ψ ∧
    LBIso (O.s.T.Z.t.PP.L.pull (F.φ ≫ ψ)) F.P₀.L ∧
    F.P₀.g = (letters O.S.Dw).length ∧
    ∀ (k : Fin F.P₀.g) (x : Letter O.S.Dw), (letters O.S.Dw)[(k : ℕ)]? = some x →
      y.u x.1 x.2 = spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR ι) ≫ (F.v k).left ≫ F.φ ≫ ψ

def stepLat {K : Type} [Field K] [NumberField K] (F : SemiFib K) (τ : D.host.E →+* ℂ) (k : ℕ) :
    Submodule (𝓞 K) (Fin F.P₀.g → K) :=
  F.lieLat ⊓ (Submodule.span K {v | ∃ (i : Fin F.P₀.g) (x : Letter O.S.Dw), x.1 = τ ∧ (x.2 : ℕ) < k ∧
    (letters O.S.Dw)[(i : ℕ)]? = some x ∧ v = Pi.single i 1}).restrictScalars (𝓞 K)

theorem stepLat_zero {K : Type} [Field K] [NumberField K] (F : SemiFib K) (τ : D.host.E →+* ℂ) :
    stepLat O F τ 0 = ⊥ := by
  have : {v : Fin F.P₀.g → K | ∃ (i : Fin F.P₀.g) (x : Letter O.S.Dw), x.1 = τ ∧ (x.2 : ℕ) < 0 ∧
      (letters O.S.Dw)[(i : ℕ)]? = some x ∧ v = Pi.single i 1} = ∅ := by
    ext v; simp
  rw [stepLat, this, Submodule.span_empty, Submodule.restrictScalars_bot, inf_bot_eq]

end GlobalTheory.LieRead

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonSpectrumDualNumber
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualOpen

theorem subsingleton_spectrum_dualNumber (K : Type) [Field K] : Subsingleton (PrimeSpectrum (DualNumber K)) := by
  have key : ∀ (p : PrimeSpectrum (DualNumber K)) (x : DualNumber K), x ∈ p.asIdeal ↔ x.fst = 0 := by
    intro p x
    constructor
    · intro hx
      by_contra h
      have hu : IsUnit x := TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (isUnit_iff_ne_zero.2 h)
      exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hx hu)
    · intro h
      have hsq : x * x = 0 := by
        refine TrivSqZeroExt.ext ?_ ?_ <;> simp [h]
      exact p.isPrime.mem_of_pow_mem 2 (by rw [pow_two, hsq]; exact p.asIdeal.zero_mem)
  exact ⟨fun p q => PrimeSpectrum.ext (Ideal.ext fun x => by rw [key p x, key q x])⟩

private theorem spMap_comp_of_eq {R₁ R₂ R₂' R₃ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₂'] [CommRing R₃]
    {f : R₁ →+* R₂} {g : R₂ →+* R₃} {f' : R₁ →+* R₂'} {g' : R₂' →+* R₃} (h : g.comp f = g'.comp f') :
    spMap g ≫ spMap f = spMap g' ≫ spMap f' := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h]

theorem tanLift_of_fieldChart : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A →
    ∀ (U : Over S) [LocallyOfFiniteType U.hom] (M : LB (A ⊗ U).left), Fam A M → Inj A M → FieldChart A M →
      TanLift A M := by
  intro S A _ hA U _ M hM hInj hFC k _ s N hN u₀ h₀
  obtain ⟨hpull, -, -, hcomp, hev⟩ := GlobalTheory.T.additiveLineBundleFamily_calculus_rules S A
  obtain ⟨ψ, hψ₁, hψ₂, hflat, hsurj⟩ :=
    GlobalTheory.T.dualNumber_fieldHom_flat_surjective k (AlgebraicClosure k) (algebraMap k (AlgebraicClosure k))

  let T : Over S := Over.mk (spMap (dnInl k) ≫ s)
  haveI : IsNoetherianRing (DualNumber k) := inferInstance
  haveI : IsLocallyNoetherian T.left := (inferInstance : IsLocallyNoetherian (Sp (DualNumber k)))
  obtain ⟨G, π, hmono, -, hG⟩ := GlobalTheory.T.exists_mono_finiteType_agreement_locus_injective_family S A hA T U N M hN hM hInj
  haveI : Mono π.left := hmono

  let Y : Over S := Over.mk (spMap ψ ≫ spMap (dnInl k) ≫ s)
  let y : Y ⟶ T := Over.homMk (spMap ψ)
  have hq : spMap ψ ≫ spMap (dnInl k) =
      spMap (dnInl (AlgebraicClosure k)) ≫ spMap (algebraMap k (AlgebraicClosure k)) :=
    spMap_comp_of_eq hψ₁
  let q : Y ⟶ Over.mk (spMap (algebraMap k (AlgebraicClosure k)) ≫ s) :=
    Over.homMk (spMap (dnInl (AlgebraicClosure k))) ((reassoc_of% hq) s).symm
  have hN' : Fam A (ev N (fst A Y) (snd A Y ≫ y)) := hpull T Y N y hN
  obtain ⟨W, hW⟩ := hFC (AlgebraicClosure k) (spMap (algebraMap k (AlgebraicClosure k)) ≫ s) Y q _ hN'

  let Z : Over S := Over.mk (spMap (dnFst (AlgebraicClosure k)) ≫ Y.hom)
  let z : Z ⟶ Y := Over.homMk (spMap (dnFst (AlgebraicClosure k)))
  have hr : spMap (dnFst (AlgebraicClosure k)) ≫ spMap ψ =
      spMap (algebraMap k (AlgebraicClosure k)) ≫ spMap (dnFst k) :=
    spMap_comp_of_eq hψ₂
  let e : Z ⟶ Over.mk (spMap (dnFst k) ≫ spMap (dnInl k) ≫ s) :=
    Over.homMk (spMap (algebraMap k (AlgebraicClosure k))) ((reassoc_of% hr) (spMap (dnInl k) ≫ s)).symm
  have hez : e ≫ ptMap _ (dnFst k) = z ≫ y := by
    ext
    exact hr.symm
  have h₁ : Same A N M (z ≫ y) (e ≫ u₀) := by
    rw [← hez]
    exact hcomp T U _ Z N M (ptMap _ (dnFst k)) u₀ e hN.isLB hM.isLB h₀
  have h₂ : Same A (ev N (fst A Y) (snd A Y ≫ y)) M z (e ≫ u₀) :=
    (hev T U Y Z N M y z _ hN.isLB hM.isLB).2 h₁
  have hx : ∀ x, z.left x ∈ W := (hW Z z).1 ⟨_, h₂⟩

  haveI : Subsingleton Y.left := subsingleton_spectrum_dualNumber (AlgebraicClosure k)
  have x₀ : Z.left := IsLocalRing.closedPoint (AlgebraicClosure k)
  have hall : ∀ x : Y.left, x ∈ W := fun x => by
    rw [Subsingleton.elim x (z.left x₀)]
    exact hx x₀
  obtain ⟨u', hu'⟩ := (hW Y (𝟙 Y)).2 (fun x => hall _)
  have h₃ : Same A N M y u' := by
    have := (hev T U Y Y N M y (𝟙 Y) u' hN.isLB hM.isLB).1 hu'
    rwa [Category.id_comp] at this

  obtain ⟨z', hz'⟩ := (hG Y y).1 ⟨u', h₃⟩
  haveI : Flat (spMap ψ) := hflat
  haveI : Surjective (spMap ψ) := hsurj
  obtain ⟨w, hw⟩ := GlobalTheory.T.exists_lift_mono_of_fpqc_cover_lift G.left T.left Y.left T.left π.left (𝟙 _) (spMap ψ) z'
    (by rw [Category.comp_id]; exact hz')
  exact (hG T (𝟙 T)).2 ⟨w, hw⟩

end GlobalTheory.DualOpen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumTwoPointFunctionMultiplesNaturalCharPStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sumTwoPointFunction_multiples_natural_charP : ∀ (p : ℕ) (R : Type) [CommRing R], (p : R) = 0 → ∀ (A : Over (Sp R)) [GrpObj A] (f : Fn1 A) (g : Fn2 A), IsAdd f g → ∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (x : Pt A D), chi p g D' (spOver φ ≫ x) - φ (chi p g D x) = f D D' φ (x ^ p) - f D D' φ 1 := by
  first | exact @GlobalTheory.PtExt.chi_natural | exact GlobalTheory.PtExt.chi_natural | (intros; apply GlobalTheory.PtExt.chi_natural <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitLemmaUnramifiedProductUnitaryGroupsStatement
section
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitLemma_unramified_product_unitary_groups : ∀ (K : UQ) (B₁ B₂ : InvAlg K), B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 → (B₁.P * B₂.P).Separable → InvAlg.Identity B₁ B₂ := by
  first | exact @GlobalTheory.UnitLemma.unitLemma_identity_unconditional | exact GlobalTheory.UnitLemma.unitLemma_identity_unconditional | (intros; apply GlobalTheory.UnitLemma.unitLemma_identity_unconditional <;> assumption)
end

