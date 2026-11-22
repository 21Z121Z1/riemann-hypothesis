import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2455
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2467
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0646
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0638
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0610
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0681
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0752
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0707
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0762
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2505
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0102
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1553
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsLocalRingQuotientPow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2453
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2444
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2454
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2412
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1536
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2252
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2228
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2179
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2531
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2502
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticSurfaceFibreIsProjOverZmodDimLeOne
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo
open GlobalTheory.LB (toMod)
open GlobalTheory.VB (degOfRank)

namespace GlobalTheory.FibreDim

theorem charZero_residueField_genericPoint' (X : Scheme.{0}) [IsIntegral X] (hc : CharZero Γ(X, ⊤)) :
    CharZero (X.residueField (genericPoint X)) := by
  have hg : Function.Injective (X.presheaf.germ ⊤ (genericPoint X) trivial) :=
    germ_injective_of_isIntegral X _ _
  have hr : Function.Injective (X.residue (genericPoint X)) := (X.residue (genericPoint X)).hom.injective
  exact charZero_of_injective_ringHom (f := (X.presheaf.germ ⊤ (genericPoint X) trivial ≫ X.residue _).hom)
    (by simpa using hr.comp hg)

theorem not_charZero_residueField {Z : Scheme.{0}} (p : ℕ) [Fact p.Prime] (s : Z ⟶ Sp (ZMod p)) (z : Z) :
    ¬ CharZero (Z.residueField z) := by
  intro hc
  let φ : ZMod p →+* Z.residueField z :=
    ((Scheme.ΓSpecIso (CommRingCat.of (ZMod p))).inv ≫ s.appTop ≫ Z.Γevaluation z).hom
  have h0 : ((p : ZMod p) : ZMod p) = 0 := ZMod.natCast_self p
  have : (p : Z.residueField z) = 0 := by rw [← map_natCast φ p, h0, map_zero]
  exact (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) this

end GlobalTheory.FibreDim

namespace GlobalTheory.FibreDim

theorem fibre_isProjOver_and_dim_le : ∀ (k : Type) [CommRing k] (W : Scheme.{0}) (q : W ⟶ Sp k), IsArithVar q 1 → ∀ (p : ℕ) [Fact p.Prime], (letI := GlobalTheory.algebraΓOfHom (pullback.snd (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p)))); IsProjOver (strHom (ZMod p) (pullback (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p)))))) ∧ topologicalKrullDim ↥(pullback (C := Scheme.{0}) (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p)))) ≤ 1 := by
  intro k _ W q hq p _
  haveI hgc : IsClosedImmersion (spMap (Int.castRingHom (ZMod p))) :=
    IsClosedImmersion.spec_of_surjective _ (ZMod.ringHom_surjective _)
  refine ⟨?_, ?_⟩
  · letI := GlobalTheory.algebraΓOfHom (pullback.snd (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p))))
    exact VertProj.isProjOver_strHom_zmod k W q 1 hq _
      (pullback.fst (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p)))) p
  · set f := q ≫ spMap (Int.castRingHom k)
    set g := spMap (Int.castRingHom (ZMod p))
    have := hq.isIntegral
    have hemb := (pullback.fst f g).isClosedEmbedding
    have hs : IsClosed (Set.range (pullback.fst f g)) := hemb.isClosed_range
    have hne : ∀ z, (pullback.fst f g) z ≠ genericPoint W := by
      intro z hz
      have h1 := charZero_residueField_genericPoint' W hq.charZero
      rw [← hz] at h1
      exact not_charZero_residueField p (pullback.snd f g) z
        (charZero_of_injective_ringHom ((pullback.fst f g).residueFieldMap z).hom.injective)
    have key := topologicalKrullDim_add_one_le hs isClosed_univ (T := W) fun x hx =>
      ⟨genericPoint W, trivial, fun ⟨z, hz⟩ => hne z hz, genericPoint_specializes x⟩
    have hW : topologicalKrullDim (Set.univ : Set W) ≤ 2 := by
      have := topologicalKrullDim_subspace_le W Set.univ
      rw [hq.dim_eq] at this
      exact this
    have heq : topologicalKrullDim (Set.range (pullback.fst f g)) =
        topologicalKrullDim ↥(pullback (C := Scheme.{0}) f g) :=
      GlobalTheory.topologicalKrullDim_eq_of_isEmbedding hemb.isEmbedding rfl
    rw [← heq]
    have h2 := key.trans hW
    generalize topologicalKrullDim (Set.range (pullback.fst f g)) = d at h2 ⊢
    induction d with
    | bot => exact bot_le
    | coe n =>
      norm_cast at h2 ⊢
      induction n with
      | top => exact absurd h2 (by decide)
      | coe m =>
        norm_cast at h2 ⊢
        have h3 : m + 1 ≤ 2 := by exact_mod_cast h2
        omega

end GlobalTheory.FibreDim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArtinianLiftAxesWedgeLocal
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section
namespace GlobalTheory.AbCoh.StepPrim

theorem pO1_comp {R : Type} [CommRing R] {X Y Z : Over (Sp R)} (f : X ⟶ Y) (g : Y ⟶ Z) (a : HO1 Z.hom) :
    pO1 (f ≫ g) a = pO1 f (pO1 g a) :=
  ((GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id).1 R R Z.left Y.left Z.hom Y.hom (RingHom.id R) g.left (ovw g) R X.left X.hom
    (RingHom.id R) f.left (ovw f) (RingHom.id R) (f ≫ g).left (ovw (f ≫ g)) (Over.comp_left _ _ _ f g)
    (fun _ ↦ rfl)).1 a |>.symm

theorem pO1_id {R : Type} [CommRing R] (A : Over (Sp R)) (a : HO1 A.hom) : pO1 (𝟙 A) a = a :=
  ((GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id).2.2 R A).1 a

theorem eq_zero_of_base {R : Type} [CommRing R] (a : HO1 (𝟙_ (Over (Sp R))).hom) : a = 0 := by
  haveI := ((GlobalTheory.AbCoh.Vanish.main).1 R (𝟙_ (Over (Sp R))).left (𝟙_ (Over (Sp R))).hom
    (inferInstanceAs (IsAffine (Sp R)))).1
  exact Subsingleton.elim _ _

theorem axes_defect {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] (x : HO1 A.hom) :
    pO1 (lift (𝟙 A) (1 : A ⟶ A)) (pO1 μ[A] x - pO1 (fst A A) x - pO1 (snd A A) x) = 0 ∧
    pO1 (lift (1 : A ⟶ A) (𝟙 A)) (pO1 μ[A] x - pO1 (fst A A) x - pO1 (snd A A) x) = 0 := by
  have h1 : ∀ a : HO1 A.hom, pO1 (1 : A ⟶ A) a = 0 := fun a ↦ by
    rw [Hom.one_def, pO1_comp, eq_zero_of_base (pO1 η[A] a), map_zero]
  refine ⟨?_, ?_⟩
  · rw [map_sub, map_sub, ← pO1_comp, ← pO1_comp, ← pO1_comp, lift_fst, lift_snd, ← Hom.mul_def,
      _root_.mul_one, pO1_id, h1, sub_self, sub_zero]
  · rw [map_sub, map_sub, ← pO1_comp, ← pO1_comp, ← pO1_comp, lift_fst, lift_snd, ← Hom.mul_def,
      _root_.one_mul, pO1_id, h1, sub_zero, sub_self]

theorem main : ∀ (R : Type) [CommRing R] [IsLocalRing R] (t : R) (R' : Type) [CommRing R'] (σ' : R →+* R'), Function.Surjective σ' → RingHom.ker σ' = Ideal.span {t} → t ≠ 0 → (∀ a ∈ IsLocalRing.maximalIdeal R, a * t = 0) → (∀ (k : Type) [CommRing k], IsField k → ∀ (B : Over (Sp k)) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → AxesVanishingStructureSheafDegOne B ∧ NoPrimitiveStructureSheafH2 B ∧ WedgeO (OAff B.hom)) → (∀ (B : Over (Sp R')) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → StructureSheafH1Primitive B) → ∀ (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → StructureSheafH1Primitive A := by
  intro R _ _ t R' _ σ' hsurj hker ht hmt hfield hR' A _ g hab hsm
  letI : Algebra R R' := σ'.toAlgebra
  have hkF : IsField (R ⧸ IsLocalRing.maximalIdeal R) :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp inferInstance
  have hSE : SmallExt t (algebraMap R R') (algebraMap R (R ⧸ IsLocalRing.maximalIdeal R)) := by
    refine ⟨hsurj, hker, Ideal.Quotient.mk_surjective, fun a ↦ ?_⟩
    rw [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
    refine ⟨hmt a, fun h ↦ ?_⟩
    by_contra hna
    exact ht ((IsLocalRing.notMem_maximalIdeal.mp hna).mul_right_eq_zero.mp h)
  haveI := hsm
  haveI : Smooth A.hom := SmoothOfRelativeDimension.smooth g A.hom
  haveI : Flat A.hom := inferInstance
  have hfl2 : Flat (A ⊗ A).hom := by rw [Over.tensorObj_hom]; infer_instance
  obtain ⟨B', _, pr, pr', hab', hsm', hpr, hpr', hμ', hf', hs', he1', he2'⟩ := GlobalTheory.T.exists_abelianScheme_baseChange_and_square R R' A g hab hsm
  obtain ⟨B₀, _, pr0, pr0', hab0, hsm0, hpr0, hpr0', -, -, -, he10, he20⟩ :=
    GlobalTheory.T.exists_abelianScheme_baseChange_and_square R (R ⧸ IsLocalRing.maximalIdeal R) A g hab hsm
  intro x
  have key : pO1 μ[A] x - pO1 (fst A A) x - pO1 (snd A A) x = 0 := by
    set y := pO1 μ[A] x - pO1 (fst A A) x - pO1 (snd A A) x with hy
    have hnat := GlobalTheory.AbCoh.pull_over_baseChange_comm R R' (algebraMap R R') A (A ⊗ A) B' (B' ⊗ B')
    have ya : pullHO1 hpr'.w y = 0 := by
      have hP := hR' B' g hab' hsm' (pullHO1 hpr.w x)
      rw [hy, map_sub, map_sub, (hnat μ[A] μ[B'] pr pr' hpr.w hpr'.w hμ').1,
        (hnat (fst A A) (fst B' B') pr pr' hpr.w hpr'.w hf').1,
        (hnat (snd A A) (snd B' B') pr pr' hpr.w hpr'.w hs').1, hP]
      abel
    obtain ⟨u, hu⟩ := GlobalTheory.T.eq_smul_residueFibre_class_of_pullback_eq_zero R R' (R ⧸ IsLocalRing.maximalIdeal R) t (algebraMap R R')
      (algebraMap R (R ⧸ IsLocalRing.maximalIdeal R)) (A ⊗ A).left (B' ⊗ B').left (B₀ ⊗ B₀).left (A ⊗ A).hom
      (B' ⊗ B').hom (B₀ ⊗ B₀).hom pr' pr0' hpr' hpr0' hSE hfl2 y ya
    have hH0 := (GlobalTheory.T.globalFunctionsConstantAfterBaseChange_of_abelianScheme R A hab) R' B'.left B'.hom pr hpr
    have hax := axes_defect A x
    have hu1 : pO1 (lift (𝟙 B₀) (1 : B₀ ⟶ B₀)) u = 0 :=
      GlobalTheory.T.residueFibre_class_eq_zero_of_smul_pullback_eq_zero R R' (R ⧸ IsLocalRing.maximalIdeal R) t (algebraMap R R')
        (algebraMap R (R ⧸ IsLocalRing.maximalIdeal R)) (A ⊗ A).left (B' ⊗ B').left (B₀ ⊗ B₀).left (A ⊗ A).hom
        (B' ⊗ B').hom (B₀ ⊗ B₀).hom pr' pr0' hpr' hpr0' A.left B'.left B₀.left A.hom B'.hom B₀.hom pr pr0 hpr hpr0
        (lift (𝟙 A) (1 : A ⟶ A)).left (lift (𝟙 B') (1 : B' ⟶ B')).left (lift (𝟙 B₀) (1 : B₀ ⟶ B₀)).left
        (ovw _) (ovw _) (ovw _) he1' he10 hSE hfl2 inferInstance hH0 u y hu hax.1
    have hu2 : pO1 (lift (1 : B₀ ⟶ B₀) (𝟙 B₀)) u = 0 :=
      GlobalTheory.T.residueFibre_class_eq_zero_of_smul_pullback_eq_zero R R' (R ⧸ IsLocalRing.maximalIdeal R) t (algebraMap R R')
        (algebraMap R (R ⧸ IsLocalRing.maximalIdeal R)) (A ⊗ A).left (B' ⊗ B').left (B₀ ⊗ B₀).left (A ⊗ A).hom
        (B' ⊗ B').hom (B₀ ⊗ B₀).hom pr' pr0' hpr' hpr0' A.left B'.left B₀.left A.hom B'.hom B₀.hom pr pr0 hpr hpr0
        (lift (1 : A ⟶ A) (𝟙 A)).left (lift (1 : B' ⟶ B') (𝟙 B')).left (lift (1 : B₀ ⟶ B₀) (𝟙 B₀)).left
        (ovw _) (ovw _) (ovw _) he2' he20 hSE hfl2 inferInstance hH0 u y hu hax.2
    have hu0 : u = 0 := (hfield _ hkF B₀ g hab0 hsm0).1 u hu1 hu2
    subst hu0
    exact GlobalTheory.T.smallExtension_element_mul_zeroClass_eq_zero R R' (R ⧸ IsLocalRing.maximalIdeal R) t (algebraMap R R')
      (algebraMap R (R ⧸ IsLocalRing.maximalIdeal R)) (A ⊗ A).left (B' ⊗ B').left (B₀ ⊗ B₀).left (A ⊗ A).hom
      (B' ⊗ B').hom (B₀ ⊗ B₀).hom pr' pr0' hpr' hpr0' hSE hfl2 y hu
  rw [sub_sub, sub_eq_zero] at key
  exact key

end GlobalTheory.AbCoh.StepPrim
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AxisTrivialLineBundleGroupPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AxisTriv

theorem lift_comp_sq {S T : Scheme.{0}} {A : Over S} {B : Over T} {β : B.left ⟶ A.left}
    {β₂ : (B ⊗ B).left ⟶ (A ⊗ A).left} (hs : IsSquare β β₂) (a b : B ⟶ B) (a' b' : A ⟶ A)
    (ha : a.left ≫ β = β ≫ a'.left) (hb : b.left ≫ β = β ≫ b'.left) :
    (lift a b).left ≫ β₂ = β ≫ (lift a' b').left := by
  have k₁ : (lift a b).left ≫ (fst B B).left = a.left := congrArg (fun z => z.left) (lift_fst a b)
  have k₂ : (lift a' b').left ≫ (fst A A).left = a'.left := congrArg (fun z => z.left) (lift_fst a' b')
  have l₁ : (lift a b).left ≫ (snd B B).left = b.left := congrArg (fun z => z.left) (lift_snd a b)
  have l₂ : (lift a' b').left ≫ (snd A A).left = b'.left := congrArg (fun z => z.left) (lift_snd a' b')
  apply pullback.hom_ext
  · change ((lift a b).left ≫ β₂) ≫ (fst A A).left = (β ≫ (lift a' b').left) ≫ (fst A A).left
    rw [Category.assoc, hs.1, ← Category.assoc, k₁, Category.assoc, k₂, ha]
  · change ((lift a b).left ≫ β₂) ≫ (snd A A).left = (β ≫ (lift a' b').left) ≫ (snd A A).left
    rw [Category.assoc, hs.2, ← Category.assoc, l₁, Category.assoc, l₂, hb]

theorem exists_gen_pull {S T : Scheme.{0}} {A : Over S} {B : Over T} {β : B.left ⟶ A.left}
    {β₂ : (B ⊗ B).left ⟶ (A ⊗ A).left} {P : LB (A ⊗ A).left} (hP : P.IsLB) (a : B ⟶ B ⊗ B) (a' : A ⟶ A ⊗ A)
    (e : a.left ≫ β₂ = β ≫ a'.left) (h : ∃ u : (P.pull a'.left).Gen, u.IsGen) :
    ∃ u : ((P.pull β₂).pull a.left).Gen, u.IsGen := by
  obtain ⟨u, hu⟩ := h
  have i₁ : LBIso ((P.pull β₂).pull a.left) (P.pull (a.left ≫ β₂)) :=
    GlobalTheory.ZM.SiegPull.lbIso_pull_comp (GlobalTheory.lbIso_refl (pull_isLB hP β₂)) a.left
  have i₂ : LBIso ((P.pull a'.left).pull β) (P.pull (β ≫ a'.left)) :=
    GlobalTheory.ZM.SiegPull.lbIso_pull_comp (GlobalTheory.lbIso_refl (pull_isLB hP a'.left)) β
  rw [e] at i₁
  have i := LBIso.trans (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _) i₁ i₂.symm
  obtain ⟨w, hw⟩ := i.symm
  obtain ⟨v, hv, -⟩ := GlobalTheory.WtTower.exists_gen_of_iso (pull_isLB (pull_isLB hP _) _) (pull_isLB (pull_isLB hP _) _)
    w hw (pullGenLB u β) (pullGenLB_isGen hu β)
  exact ⟨v, hv⟩

theorem axes_pull : ∀ (S T : Scheme.{0}) (A : Over S) [GrpObj A] (P : LB (G2 A).left), P.IsLB → (∃ u : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, u.IsGen) → (∃ u : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, u.IsGen) → ∀ (t : T ⟶ S) (B : Over T) [GrpObj B] (β : B.left ⟶ A.left) (β₂ : (G2 B).left ⟶ (G2 A).left), IsGrpPullback B A t β → IsSquare β β₂ → (∃ u : ((P.pull β₂).pull (lift (1 : B ⟶ B) (𝟙 B)).left).Gen, u.IsGen) ∧ (∃ u : ((P.pull β₂).pull (lift (𝟙 B) (1 : B ⟶ B)).left).Gen, u.IsGen) := by
  intro S T A _ P hP h₁ h₂ t B _ β β₂ h hs
  have e₁ := GlobalTheory.PPAS.one_comp_of_isGrpPullback h
  exact ⟨exists_gen_pull hP _ _ (lift_comp_sq hs _ _ _ _ e₁ rfl) h₁,
    exists_gen_pull hP _ _ (lift_comp_sq hs _ _ _ _ rfl e₁) h₂⟩

end GlobalTheory.AxisTriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeCoefficientComparisonCommPairPullbackStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseChange_coefficient_comparison_comm_pairPullback : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (X₀ X₁ Y₀ Y₁ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀) (t₀ : Y₀ ⟶ Sp R₀) (t₁ : Y₁ ⟶ Sp R₁) (pr' : Y₁ ⟶ Y₀) [IsAffineHom pr] [IsAffineHom pr'] (w : pr ≫ s₀ = s₁ ≫ spMap (algebraMap R₀ R₁)) (w' : pr' ≫ t₀ = t₁ ≫ spMap (algebraMap R₀ R₁)) (f₀ : Y₀ ⟶ X₀) (f₁ : Y₁ ⟶ X₁) (h₀ : f₀ ≫ s₀ = t₀ ≫ spMap (RingHom.id R₀)) (h₁ : f₁ ≫ s₁ = t₁ ≫ spMap (RingHom.id R₁)) (e : f₁ ≫ pr = pr' ≫ f₀) (p : (Pair f₀)ᵒᵖ) (b : (ext R₁ (OAff s₀)).obj ((pairSnd f₀).obj p)), (GlobalTheory.Obs.BC.tensPair w' e).α p ((extMap R₁ (pairPull h₀)).α p b) = (pairPull h₁).α ((GlobalTheory.Obs.BC.pairBC pr pr' e).obj p) ((GlobalTheory.Obs.BC.tensCoef w).α ((pairSnd f₀).obj p) b) := by
  first | exact @GlobalTheory.Obs.BC.tensPair_extMap_pairPull | exact GlobalTheory.Obs.BC.tensPair_extMap_pairPull | (intros; apply GlobalTheory.Obs.BC.tensPair_extMap_pairPull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeEighthPowerProductMonHomStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isMonHom_pullback_pr_and_unique_lift_fin_eight : ∀ (S S' : Scheme.{0}) (t : S' ⟶ S) (G H : Over S) [GrpObj G] [GrpObj H] (pr : Fin 8 → (G ⟶ H)), (∀ a, IsMonHom (pr a)) → (∀ (T : Over S) (y : Fin 8 → (T ⟶ H)), ∃! x : T ⟶ G, ∀ a, x ≫ pr a = y a) → (∀ a, IsMonHom ((Over.pullback t).map (pr a))) ∧ ∀ (T : Over S') (y : Fin 8 → (T ⟶ (Over.pullback t).obj H)), ∃! x : T ⟶ (Over.pullback t).obj G, ∀ a, x ≫ (Over.pullback t).map (pr a) = y a := by
  first | exact @GlobalTheory.baseChange_eighthPower_product_monHom | exact GlobalTheory.baseChange_eighthPower_product_monHom | (intros; apply GlobalTheory.baseChange_eighthPower_product_monHom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeSectionsComparisonHomBijectiveStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseChangeSectionsComparisonHom_bijective : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (X₀ X₁ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀) (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) (U : X₀.affineOpens), Function.Bijective (GlobalTheory.Obs.BaseChg.beta hp U) := by
  first | exact @GlobalTheory.Obs.BaseChg.beta_bijective | exact GlobalTheory.Obs.BaseChg.beta_bijective | (intros; apply GlobalTheory.Obs.BaseChg.beta_bijective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeTensorSectionsHomBijectiveStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseChangeTensorSectionsHom_bijective : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (X₀ X₁ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀) (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) (U : X₀.affineOpens) (hU : IsAffineOpen (pr ⁻¹ᵁ U.1)), Function.Bijective (GlobalTheory.Obs.BC.tensHom hp.w U hU) := by
  first | exact @GlobalTheory.Obs.BC.tensHom_bijective | exact GlobalTheory.Obs.BC.tensHom_bijective | (intros; apply GlobalTheory.Obs.BC.tensHom_bijective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcFlag
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits

namespace GlobalTheory.CovTest

variable {B Y B' : Scheme.{0}}

def bcIso (π : Y ⟶ B) (g : B' ⟶ B) (E : B.Modules) :
    (Scheme.Modules.pullback (pullback.fst π g)).obj ((Scheme.Modules.pullback π).obj E) ≅
      (Scheme.Modules.pullback (pullback.snd π g)).obj ((Scheme.Modules.pullback g).obj E) :=
  (Scheme.Modules.pullbackComp (pullback.fst π g) π).app E ≪≫
    (Scheme.Modules.pullbackCongr pullback.condition).app E ≪≫
      ((Scheme.Modules.pullbackComp (pullback.snd π g) g).app E).symm

def bcFlag (π : Y ⟶ B) (g : B' ⟶ B) {E : B.Modules} {n : ℕ}
    (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) n) :
    Vert.Flag ((Scheme.Modules.pullback (pullback.snd π g)).obj ((Scheme.Modules.pullback g).obj E)) n :=
  (fl.pull (pullback.fst π g)).ofIso (bcIso π g E)

end GlobalTheory.CovTest

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BilinFormPsdOfMinimalTupleModNStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bilinForm_psd_of_minimal_tuple_modN : ∀ {r N : ℕ}, 0 < N → ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (b : LinearMap.BilinForm ℤ (Fin r → ℤ)) (μ : Fin 8 → Fin r → ℤ), (∀ α : Fin 8 → Fin r → ℤ, (∀ u i, ∃ m : ℤ, α u i = μ u i + N * m) → qW W b μ ≤ qW W b α) → ∀ x, 0 ≤ b x x := by
  first | exact @GlobalTheory.Poinc.psd_of_min | exact GlobalTheory.Poinc.psd_of_min | (intros; apply GlobalTheory.Poinc.psd_of_min <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BirationalPrimeDivisorOrdersFunctionsTopForms
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
open GlobalTheory.Discrepancy GlobalTheory.EtaleKlt

set_option autoImplicit false

namespace GlobalTheory.BirOrd

theorem ord_and_formOrd_of_over : ∀ {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] (n : ℕ),
    topologicalKrullDim X = n → ∀ (s : Y ⟶ X) [IsDominant s], Function.Bijective (functionFieldMap s) →
    ∀ (E : DivOver p) (E' : DivOver (s ≫ p)), DivOver.Over s E' E →
      (∀ g : X.functionFieldˣ, E'.ord (fnPull s g) = E.ord g) ∧
      ∀ η : RatForms p n, η ≠ 0 → E'.formOrd (ratPull p s n η) = E.formOrd η := by
  intro X Y _ _ p _ n _ s _ hbij E E' hO
  exact ⟨DivOver.Over.ord_fnPull_of_bijective ℂ X Y p s hbij E' E hO,
    fun η hη => formOrd_ratPull_of_over ℂ X Y p s hbij E' E hO n η hη⟩

end GlobalTheory.BirOrd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BirigidifiedLiftPullbackOneProdEndomorphism
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Published

namespace GlobalTheory.BirigidLift

theorem pull_one_prod_of_lift : GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDualCrystal →
    ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (κ : DividedPowers I), IsNilDP κ →
    ∀ (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I →
    ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A : Over (Sp R)) [GrpObj A] (i : A₀.left ⟶ A.left),
      IsGrpPullback A₀ A (spMap π) i → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ (l : (A₀ ⊗ A₀).left ⟶ (A ⊗ A).left), IsSquare i l →
    ∀ (L : LB A.left), L.IsLB → Out.RelAmple A L →
    ∀ (u₀ : A₀ ⟶ A₀) (u : A ⟶ A) [IsMonHom u₀] [IsMonHom u], u₀.left ≫ i = i ≫ u.left →
    ∀ (P₀ Q₀ : LB (A₀ ⊗ A₀).left), P₀.IsLB → Q₀.IsLB → LBIso Q₀ (P₀.pull (lift (fst A₀ A₀) (snd A₀ A₀ ≫ u₀)).left) →
    ∀ (P Q : LB (A ⊗ A).left), P.IsLB → Q.IsLB →
      HasGen (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left) → HasGen (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left) →
      HasGen (Q.pull (lift (1 : A ⟶ A) (𝟙 A)).left) → HasGen (Q.pull (lift (𝟙 A) (1 : A ⟶ A)).left) →
      LBIso (P.pull l) P₀ → LBIso (Q.pull l) Q₀ → LBIso Q (P.pull (lift (fst A A) (snd A A ≫ u)).left) := by
  intro HG HD R R₀ _ _ I κ hκ π hπ hI g A₀ _ A _ i h hA hg l hl L hL aL u₀ u _ _ hu P₀ Q₀ hP₀ hQ₀ eQ₀ P Q hP hQ
    p₁ p₂ q₁ q₂ eP eQ
  set m : (A ⊗ A).left ⟶ (A ⊗ A).left := (lift (fst A A) (snd A A ≫ u)).left with hm
  set m₀ : (A₀ ⊗ A₀).left ⟶ (A₀ ⊗ A₀).left := (lift (fst A₀ A₀) (snd A₀ A₀ ≫ u₀)).left with hm₀
  have hP' : (P.pull m).IsLB := pull_isLB hP m
  have hev : ∀ (a : A ⟶ A) (t : A ⟶ A), evc hP' a t = evc hP a (t ≫ u) := fun a t ↦ by
    have := evc_ev hP (fst A A) (snd A A ≫ u) hP' a t
    rw [this, lift_fst, lift_snd_assoc]
  have z₁ : evc hP (1 : A ⟶ A) (𝟙 A) = 0 := (triv_ev_iff hP _ _).1 p₁
  have z₂ : evc hP (𝟙 A) (1 : A ⟶ A) = 0 := (triv_ev_iff hP _ _).1 p₂
  have h₁' : Triv (ev (P.pull m) (1 : A ⟶ A) (𝟙 A)) := by
    rw [triv_ev_iff hP', hev, Category.id_comp]
    have := pull_evc hP u (1 : A ⟶ A) (𝟙 A)
    rw [z₁, map_zero, Category.comp_id, MonObj.comp_one] at this
    exact this.symm
  have h₂' : Triv (ev (P.pull m) (𝟙 A) (1 : A ⟶ A)) := by
    rw [triv_ev_iff hP', hev, MonObj.one_comp]
    exact z₂
  have sq : l ≫ m = m₀ ≫ l := by
    apply left_ext
    · rw [Category.assoc, Category.assoc, hm, hm₀, lift_left_fst, hl.1, lift_left_fst_assoc]
    · rw [Category.assoc, Category.assoc, hm, hm₀, lift_left_snd, hl.2, lift_left_snd_assoc, Over.comp_left,
        Over.comp_left, ← Category.assoc, hl.2, Category.assoc, Category.assoc, hu]
  have e' : LBIso ((P.pull m).pull l) Q₀ := by
    refine (cls_eq_iff (pull_isLB hP' l) hQ₀).1 ?_
    rw [cls_pull hP' l, cls_pull hP m, ← pull_comp, sq, pull_comp, ← cls_pull hP l (pull_isLB hP l),
      (cls_eq_iff (pull_isLB hP l) hP₀).2 eP, ← cls_pull hP₀ m₀ (pull_isLB hP₀ m₀),
      (cls_eq_iff hQ₀ (pull_isLB hP₀ m₀)).2 eQ₀]
  exact lift_unique HG HD.1 hκ hπ hI hA hg hA hg h h hl.1 hl.2 hL aL hL aL hQ₀ hQ q₁ q₂ eQ hP' h₁' h₂' e'

end GlobalTheory.BirigidLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BirigidifiedLiftSymmetricOfSymmetricReduction
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic

namespace GlobalTheory.BirigidLift

theorem symm_of_lift : GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDualCrystal →
    ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (κ : DividedPowers I), IsNilDP κ →
    ∀ (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I →
    ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A : Over (Sp R)) [GrpObj A] (i : A₀.left ⟶ A.left),
      IsGrpPullback A₀ A (spMap π) i → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ (l : (A₀ ⊗ A₀).left ⟶ (A ⊗ A).left), IsSquare i l →
    ∀ (L : LB A.left), L.IsLB → Out.RelAmple A L →
    ∀ (P₀ : LB (A₀ ⊗ A₀).left), P₀.IsLB → LBIso P₀ (P₀.pull (lift (snd A₀ A₀) (fst A₀ A₀)).left) →
    ∀ (P : LB (A ⊗ A).left), P.IsLB → HasGen (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left) →
      HasGen (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left) → LBIso (P.pull l) P₀ →
      LBIso P (P.pull (lift (snd A A) (fst A A)).left) := by
  intro HG HD R R₀ _ _ I κ hκ π hπ hI g A₀ _ A _ i h hA hg l hl L hL aL P₀ hP₀ hsym P hP h₁ h₂ e
  obtain ⟨l₁, l₂⟩ := hl
  have hs : (P.pull (lift (snd A A) (fst A A)).left).IsLB := pull_isLB hP _
  have h₁' : Triv (ev (swap P) (1 : A ⟶ A) (𝟙 A)) := by
    rw [triv_ev_iff hs, evc_swap hP hs, ← triv_ev_iff hP]
    exact h₂
  have h₂' : Triv (ev (swap P) (𝟙 A) (1 : A ⟶ A)) := by
    rw [triv_ev_iff hs, evc_swap hP hs, ← triv_ev_iff hP]
    exact h₁
  have sq : l ≫ (lift (snd A A) (fst A A)).left = (lift (snd A₀ A₀) (fst A₀ A₀)).left ≫ l := by
    apply left_ext
    · rw [Category.assoc, Category.assoc, lift_left_fst, l₂, l₁, lift_left_fst_assoc]
    · rw [Category.assoc, Category.assoc, lift_left_snd, l₁, l₂, lift_left_snd_assoc]
  have hl0 := pull_isLB hP l
  have e' : LBIso ((swap P).pull l) P₀ := by
    refine (cls_eq_iff (pull_isLB hs l) hP₀).1 ?_
    rw [cls_pull hs l, cls_pull hP, ← pull_comp, sq, pull_comp, ← cls_pull hP l hl0,
      (cls_eq_iff hl0 hP₀).2 e, ← cls_pull hP₀ _ (pull_isLB hP₀ _)]
    exact ((cls_eq_iff hP₀ (pull_isLB hP₀ _)).2 hsym).symm
  exact lift_unique HG HD.1 hκ hπ hI hA hg hA hg h h l₁ l₂ hL aL hL aL hP₀ hP h₁ h₂ e hs h₁' h₂' e'

end GlobalTheory.BirigidLift
end

