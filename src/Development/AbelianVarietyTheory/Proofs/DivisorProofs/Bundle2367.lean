import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0114
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1374
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0478
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0045
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0041
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2326
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2309
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianAmpleSymmPreservedFieldBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.FieldBaseChange

theorem inv_left_comp {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) :
    (GrpObj.inv : G' ⟶ G').left ≫ φ = φ ≫ (GrpObj.inv : G ⟶ G).left := by
  have e := congrArg (fun q => q.left) (map_inv (pushHom h G') (𝟙 G'))
  simpa [pushHom, pushPt, Hom.inv_def] using e

theorem abelian_ample_symm_baseChange : ∀ (k Ω : Type) [Field k] [Field Ω] (σ : k →+* Ω) (A₀ : Over (Sp k)) [GrpObj A₀], IsAbelianScheme A₀ → ∀ L : LB A₀.left, L.IsLB → RelAmple A₀ L → LBIso (L.pull (GrpObj.inv : A₀ ⟶ A₀).left) L → IsAbelianScheme ((Over.pullback (spMap σ)).obj A₀) ∧ RelAmple ((Over.pullback (spMap σ)).obj A₀) (L.pull (pullback.fst A₀.hom (spMap σ))) ∧ LBIso ((L.pull (pullback.fst A₀.hom (spMap σ))).pull (GrpObj.inv : (Over.pullback (spMap σ)).obj A₀ ⟶ (Over.pullback (spMap σ)).obj A₀).left) (L.pull (pullback.fst A₀.hom (spMap σ))) := by
  intro k Ω _ _ σ A₀ _ hA L hL hamp hsym
  have h := isGrpPullback_pullback A₀ (spMap σ)
  refine ⟨GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA h, ?_, ?_⟩
  · have := hA.proper
    exact GlobalTheory.AmpleBaseChange.relAmple_of_isPullback hL hamp h.1
  · have hinv := inv_left_comp h
    have i₁ := GlobalTheory.AlgUniq.lbIso_pull_comp hL (pullback.fst A₀.hom (spMap σ))
      (GrpObj.inv : (Over.pullback (spMap σ)).obj A₀ ⟶ (Over.pullback (spMap σ)).obj A₀).left _ rfl
    have i₂ := GlobalTheory.AlgUniq.lbIso_pull_comp hL (GrpObj.inv : A₀ ⟶ A₀).left
      (pullback.fst A₀.hom (spMap σ)) _ hinv.symm
    have i₃ := GlobalTheory.RigidBundleGlue.LBIso.pull hsym (pullback.fst A₀.hom (spMap σ))
    exact (LBIso.trans (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _) (pull_isLB (pull_isLB hL _) _)
      i₁.symm i₂).trans (pull_isLB (pull_isLB hL _) _) (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _) i₃

end GlobalTheory.FieldBaseChange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeCrystalReducesToDeRhamSqZero
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LiftSys

open TensorProduct in

theorem oneTmul_surjective_ker {R R₀ : Type} [CommRing R] [CommRing R₀] (I : Ideal R) (π : R →+* R₀)
    (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (M : Type*) [AddCommGroup M] [Module R M] :
    letI := π.toAlgebra
    Function.Surjective (TensorProduct.mk R R₀ M 1) ∧
      ∀ m : M, (1 : R₀) ⊗ₜ[R] m = 0 ↔ m ∈ I • (⊤ : Submodule R M) := by
  letI := π.toAlgebra
  subst hk
  let f : (R ⧸ RingHom.ker π) ≃ₐ[R] R₀ := Ideal.quotientKerAlgEquivOfSurjective (f := (Algebra.ofId R R₀)) hπ
  let E : R₀ ⊗[R] M ≃ₗ[R] M ⧸ (RingHom.ker π • (⊤ : Submodule R M)) :=
    (TensorProduct.congr f.toLinearEquiv.symm (LinearEquiv.refl R M)) ≪≫ₗ quotTensorEquivQuotSMul M (RingHom.ker π)
  have hE : ∀ m : M, E (1 ⊗ₜ m) = Submodule.Quotient.mk m := fun m ↦ by
    simp [E, map_one]
  refine ⟨fun t ↦ ?_, fun m ↦ ?_⟩
  · obtain ⟨m, hm⟩ := Submodule.Quotient.mk_surjective _ (E t)
    exact ⟨m, E.injective (by rw [← hm]; exact hE m)⟩
  · rw [← Submodule.Quotient.mk_eq_zero, ← hE, LinearEquiv.map_eq_zero_iff]

theorem mem_smul_top_of_equiv {R : Type} [CommRing R] (I : Ideal R) {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (L : M ≃ₗ[R] N) (x : M) :
    L x ∈ I • (⊤ : Submodule R N) ↔ x ∈ I • (⊤ : Submodule R M) := by
  have e : (I • ⊤ : Submodule R N) = (I • ⊤ : Submodule R M).map (L : M →ₗ[R] N) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.2 L.surjective]
  rw [e, Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]

theorem rhoBC_of_abelianLift : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀]
    (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (g : ℕ)
    (A₀ : Over (Sp R₀)) [GrpObj A₀] (A' : Over (Sp R)) [GrpObj A'] (i' : A₀.left ⟶ A'.left)
    (h' : IsGrpPullback A₀ A' (spMap π) i'), IsAbelianScheme A' → SmoothOfRelativeDimension g A'.hom →
    RhoBC hI hk A₀.hom := by
  intro H1 H2 R R₀ _ _ I hI π hπ hk g A₀ _ A' _ i' h' hA hg
  letI := π.toAlgebra
  have := hA.smooth
  have := hA.proper
  haveI : Smooth A₀.hom := MorphismProperty.of_isPullback (P := @Smooth) h'.1 hA.smooth
  haveI : IsProper A₀.hom := MorphismProperty.of_isPullback (P := @IsProper) h'.1 hA.proper
  have w : i' ≫ A'.hom = A₀.hom ≫ spMap π := h'.1.w
  have hm : IsMor (dp0 R) A'.hom (divided₂ hI) (A₀.hom ≫ spMap π) (RingHom.id R) i' :=
    IsMor.of_dividedPowersZeroIdeal _ (by rw [Cris.spMap_id, Category.comp_id]; exact w)
  have hn : IsMor (dp0 R) A'.hom (dp0 R₀) A₀.hom π i' := IsMor.of_dividedPowersZeroIdeal _ w
  have bm : Function.Bijective hm.pull1 :=
    (H1.toCrystallineDeRham R I (divided₂ hI) (isDPNilpotent_squareZero hI) R₀ π hπ hk A'.left A₀.left A'.hom A₀.hom i'
      inferInstance inferInstance inferInstance h'.1 hm).1
  have comp : ∀ c, rho hI hk A₀.hom (hm.pull1 c) = hn.pull1 c := fun c ↦
    IsMor.pullback1_comp hm (redMor hI hk A₀.hom) hn (fun _ ↦ rfl) (Category.id_comp _) c
  have b' := H1.bijective_cechDeRhamComparison_degreeOne A'.hom inferInstance inferInstance inferInstance
  have b₀ := H1.bijective_cechDeRhamComparison_degreeOne A₀.hom inferInstance inferInstance inferInstance
  obtain ⟨⟨e, he⟩, -, -⟩ := (H2 R A' g hA hg).2.2.2.2.2 R₀ A₀.left A₀.hom i' h'.1
  have key : ∀ c, cmp1 A₀.hom (hn.pull1 c) = e (1 ⊗ₜ cmp1 A'.hom c) := fun c ↦
    (pairRes_injective i' A₀.hom).2.2 ((comparison_pullback hn c).symm.trans (he _))
  obtain ⟨hsurj, hker⟩ := oneTmul_surjective_ker I π hπ hk (HH1 A'.hom)
  let L := LinearEquiv.ofBijective hm.pull1 bm
  let C := LinearEquiv.ofBijective (cmp1 A'.hom) b'
  refine ⟨fun y ↦ ?_, fun c ↦ ?_⟩
  · obtain ⟨t, ht⟩ := e.surjective (cmp1 A₀.hom y)
    obtain ⟨m, rfl⟩ := hsurj t
    obtain ⟨c', rfl⟩ := b'.2 m
    exact ⟨hm.pull1 c', by rw [comp]; exact b₀.1 ((key c').trans ht)⟩
  · obtain ⟨c', rfl⟩ := bm.2 c
    rw [comp, show hm.pull1 c' = L c' from rfl, mem_smul_top_of_equiv I L c', ← mem_smul_top_of_equiv I C c',
      ← hker]
    change _ ↔ (1 : R₀) ⊗ₜ cmp1 A'.hom c' = 0
    rw [← LinearEquiv.map_eq_zero_iff e, ← key, ← map_zero (cmp1 A₀.hom)]
    exact ⟨fun h ↦ by rw [h], fun h ↦ b₀.1 h⟩

end GlobalTheory.LiftSys
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescendsGaloisCoverNoetherianBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor

namespace GlobalTheory

namespace GaloisDescentNoetherian

open QuotientDescent (up up_left up_comp)

variable {X Y : Scheme.{0}} {π : X ⟶ Y} {G : Over X} {G' : Over Y} {φ : G.left ⟶ G'.left}
  {Ga : Type} [Group Ga] {ρ : Ga → (X ⟶ X)} {ν : Ga → (G.left ⟶ G.left)}

noncomputable def act (hc : IsGaloisCover Ga ρ π) (T : Over Y) (a : Ga) :
    pullback T.hom π ⟶ pullback T.hom π :=
  pullback.lift (pullback.fst T.hom π) (pullback.snd T.hom π ≫ ρ a)
    (by rw [Category.assoc, hc.inv, pullback.condition])

theorem act_fst (hc : IsGaloisCover Ga ρ π) (T : Over Y) (a : Ga) :
    act hc T a ≫ pullback.fst T.hom π = pullback.fst T.hom π := pullback.lift_fst _ _ _

theorem act_snd (hc : IsGaloisCover Ga ρ π) (T : Over Y) (a : Ga) :
    act hc T a ≫ pullback.snd T.hom π = pullback.snd T.hom π ≫ ρ a := pullback.lift_snd _ _ _

theorem isGaloisCover_act (hc : IsGaloisCover Ga ρ π) (T : Over Y) :
    IsGaloisCover Ga (act hc T) (pullback.fst T.hom π) :=
  ((GlobalTheory.T.galoisCover_descent_and_cartesian_squares X Y π Ga ρ hc).2.2 _ _ (pullback.fst T.hom π) (act hc T) (pullback.snd T.hom π) T.hom
    (act_snd hc T) pullback.condition.symm).2 (IsPullback.of_hasPullback T.hom π).flip (act_fst hc T)

theorem cover_ext (hc : IsGaloisCover Ga ρ π) {Z : Scheme.{0}} {f g : Y ⟶ Z} (h : π ≫ f = π ≫ g) :
    f = g :=
  ((GlobalTheory.T.galoisCover_descent_and_cartesian_squares X Y π Ga ρ hc).1 Z (π ≫ g) fun a ↦ by rw [← Category.assoc, hc.inv]).unique h rfl

theorem up_injective (hc : IsGaloisCover Ga ρ π) (H : IsPullback φ G.hom G'.hom π) {T : Over Y}
    {x y : T ⟶ G'} (e : up H x = up H y) : x = y := by
  refine Over.OverMorphism.ext (cover_ext (isGaloisCover_act hc T) ?_)
  rw [← up_left H, ← up_left H, e]

noncomputable def equivariant [GrpObj G] (hc : IsGaloisCover Ga ρ π)
    (hν : ∀ a, IsGrpPullback G G (ρ a) (ν a)) (T : Over Y) : Subgroup ((Over.pullback π).obj T ⟶ G) :=
  ⨅ a : Ga, (preHom (Over.homMk (act hc T a) (act_snd hc T a))).eqLocus
    (pushHom (hν a) ((Over.pullback π).obj T))

theorem mem_equivariant [GrpObj G] (hc : IsGaloisCover Ga ρ π)
    (hν : ∀ a, IsGrpPullback G G (ρ a) (ν a)) {T : Over Y} {w : (Over.pullback π).obj T ⟶ G} :
    w ∈ equivariant hc hν T ↔ ∀ a, act hc T a ≫ w.left = w.left ≫ ν a := by
  simp only [equivariant, Subgroup.mem_iInf]
  exact ⟨fun h a ↦ congrArg (fun z ↦ z.left) (h a), fun h a ↦ Over.OverMorphism.ext (h a)⟩

theorem exists_up [GrpObj G] (hc : IsGaloisCover Ga ρ π) (H : IsPullback φ G.hom G'.hom π)
    (hν : ∀ a, IsGrpPullback G G (ρ a) (ν a)) (hφ : ∀ a, ν a ≫ φ = φ) {T : Over Y}
    {w : (Over.pullback π).obj T ⟶ G} (hw : w ∈ equivariant hc hν T) : ∃ z : T ⟶ G', up H z = w := by
  have hc' := isGaloisCover_act hc T
  obtain ⟨z, hz, -⟩ := (GlobalTheory.T.galoisCover_descent_and_cartesian_squares _ _ _ Ga _ hc').1 _ (w.left ≫ φ) fun a ↦ by
    rw [← Category.assoc, (mem_equivariant hc hν).mp hw a, Category.assoc, hφ]
  refine ⟨Over.homMk z (cover_ext hc' ?_), QuotientDescent.hom_ext H ((up_left H _).trans hz)⟩
  rw [reassoc_of% hz, H.w, pullback.condition]
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ π) (Over.w w))

theorem up_mem [GrpObj G] (hc : IsGaloisCover Ga ρ π) (H : IsPullback φ G.hom G'.hom π)
    (hν : ∀ a, IsGrpPullback G G (ρ a) (ν a)) (hφ : ∀ a, ν a ≫ φ = φ) {T : Over Y} (z : T ⟶ G') :
    up H z ∈ equivariant hc hν T := (mem_equivariant hc hν).mpr fun a ↦ by
  have e : (up H z).left ≫ G.hom = pullback.snd T.hom π := Over.w _
  have h₁ := act_fst hc T a
  refine H.hom_ext ?_ ?_
  · rw [Category.assoc, Category.assoc, hφ, up_left, reassoc_of% h₁]
  · rw [Category.assoc, Category.assoc, (hν a).1.w, e, act_snd, reassoc_of% e]

theorem exists_grpObj [GrpObj G] [IsCommMonObj G] (hc : IsGaloisCover Ga ρ π)
    (H : IsPullback φ G.hom G'.hom π) (hν : ∀ a, IsGrpPullback G G (ρ a) (ν a))
    (hφ : ∀ a, ν a ≫ φ = φ) : ∃ _ : GrpObj G', IsCommMonObj G' ∧ IsGrpPullback G G' π φ := by
  have inj {T : Over Y} {x y : T ⟶ G'} (e : up H x = up H y) : x = y := up_injective hc H e
  have mem {T : Over Y} (z : T ⟶ G') := up_mem hc H hν hφ z
  obtain ⟨m, hm⟩ := exists_up hc H hν hφ (mul_mem (mem (fst G' G')) (mem (snd G' G')))
  obtain ⟨e, he⟩ := exists_up hc H hν hφ (T := 𝟙_ _) (one_mem _)
  obtain ⟨i, hi⟩ := exists_up hc H hν hφ (inv_mem (mem (𝟙 G')))
  have hm' {T : Over Y} (u : T ⟶ G' ⊗ G') :
      up H (u ≫ m) = up H (u ≫ fst _ _) * up H (u ≫ snd _ _) := by
    rw [up_comp, hm, MonObj.comp_mul, ← up_comp, ← up_comp]
  have he' {T : Over Y} (u : T ⟶ 𝟙_ _) : up H (u ≫ e) = 1 := by
    rw [up_comp, he, MonObj.comp_one]
  letI : GrpObj G' :=
    { one := e
      mul := m
      one_mul := inj (by
        rw [hm', whiskerRight_fst, he', _root_.one_mul, whiskerRight_snd, leftUnitor_hom])
      mul_one := inj (by
        rw [hm', whiskerLeft_snd, he', _root_.mul_one, whiskerLeft_fst, rightUnitor_hom])
      mul_assoc := inj (by
        rw [← Category.assoc, hm' (m ▷ G'), hm' (_ ≫ G' ◁ m), whiskerRight_fst, whiskerRight_snd,
          Category.assoc, Category.assoc, whiskerLeft_fst, whiskerLeft_snd, hm' (fst _ _),
          ← Category.assoc _ _ m, hm', Category.assoc, Category.assoc, associator_hom_fst,
          associator_hom_snd_fst, associator_hom_snd_snd, _root_.mul_assoc])
      inv := i
      left_inv := inj (by rw [hm', he', lift_fst, lift_snd, hi, inv_mul_cancel])
      right_inv := inj (by rw [hm', he', lift_fst, lift_snd, hi, mul_inv_cancel]) }
  have hmul {T : Over Y} (x y : T ⟶ G') : up H (x * y) = up H x * up H y := by
    rw [Hom.mul_def]
    exact (hm' _).trans (by rw [lift_fst, lift_snd])
  have hcomm : IsCommMonObj G' := ⟨inj (by
    refine (hm' _).trans (Eq.trans ?_ hm.symm)
    rw [braiding_hom_fst, braiding_hom_snd, mul_comm])⟩
  have sec {T : Over X} : ∃ s : T ⟶ (Over.pullback π).obj (Over.mk (T.hom ≫ π)),
      s.left ≫ pullback.fst _ π = 𝟙 T.left :=
    ⟨Over.homMk (pullback.lift (𝟙 T.left) T.hom (Category.id_comp _)) (pullback.lift_snd ..),
      pullback.lift_fst ..⟩
  refine ⟨inferInstance, hcomm, H, fun T x y x₀ y₀ hx hy ↦ ?_⟩
  obtain ⟨s, hs⟩ := sec (T := T)
  have k (z : Over.mk (T.hom ≫ π) ⟶ G') : (s ≫ up H z).left ≫ φ = z.left := by
    rw [Over.comp_left, Category.assoc, up_left, reassoc_of% hs]
  rw [← k, hmul, MonObj.comp_mul, QuotientDescent.hom_ext H ((k x₀).trans hx),
    QuotientDescent.hom_ext H ((k y₀).trans hy)]

end GaloisDescentNoetherian

open GaloisDescentNoetherian

theorem abelianScheme_descends_galoisCover_noetherian :
    ∀ (K : Type) [CommRing K] [IsNoetherianRing K] (X Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp K) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (G : Over X) [GrpObj G] (ν : Ga → (G.left ⟶ G.left)), IsGaloisCover Ga ρ π → IsQProjOver (G.hom ≫ π ≫ sY) → IsAbelianScheme G → (∀ a, IsGrpPullback G G (ρ a) (ν a)) → ν 1 = 𝟙 _ → (∀ a c, ν (a * c) = ν a ≫ ν c) → ∃ (G' : Over Y) (_ : GrpObj G') (φ : G.left ⟶ G'.left), IsAbelianScheme G' ∧ IsGrpPullback G G' π φ ∧ IsGaloisCover Ga ν φ := by
  intro K _ _ X Y π sY Ga _ ρ G _ ν hc hq hG hν h1 hmul
  have := hc.finite
  have hinv (a : Ga) : ν a ≫ G.hom ≫ π = G.hom ≫ π := by
    rw [← Category.assoc, (hν a).1.w, Category.assoc, hc.inv]
  obtain ⟨Z, φ, sZ, -, hφ, -⟩ := GlobalTheory.T.exists_galoisCover_quotient_freeFiniteAction K G.left (G.hom ≫ π ≫ sY) Ga ν hq h1 hmul
    (fun a ↦ by rw [reassoc_of% (hinv a)]) (fun k _ _ y a hy ↦ by
      refine (hc.fibre k (y ≫ G.hom) (y ≫ G.hom) rfl).unique ?_ ?_
      · rw [Category.assoc, ← (hν a).1.w, reassoc_of% hy]
      · rw [hc.one, Category.comp_id])
  obtain ⟨v, hv, -⟩ := (GlobalTheory.T.galoisCover_descent_and_cartesian_squares _ _ φ Ga ν hφ).1 Y (G.hom ≫ π) hinv
  have H : IsPullback φ G.hom (Over.mk v).hom π :=
    (((GlobalTheory.T.galoisCover_descent_and_cartesian_squares X Y π Ga ρ hc).2.2 _ _ φ ν G.hom v (fun a ↦ (hν a).1.w) hv.symm).1 hφ).flip
  have := hG.comm
  obtain ⟨inst, hcomm, hp⟩ := exists_grpObj (G' := Over.mk v) hc H hν hφ.inv
  refine ⟨Over.mk v, inst, φ, ?_, hp, hφ⟩
  have := hc.fin
  have := hc.etale
  have := hc.onto
  have := hφ.fin
  have := hφ.onto
  have := hG.smooth
  have := hG.proper
  have := hG.geomConnected
  have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) π :=
    ⟨⟨‹_›, inferInstance⟩, inferInstance⟩
  have hs : Smooth (Over.mk v).hom :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth) H.flip hQ ‹_›
  have hu : UniversallyClosed (Over.mk v).hom :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @UniversallyClosed) H.flip hQ inferInstance
  have hsep : IsSeparated (Over.mk v).hom := by
    have : IsSeparated (φ ≫ (Over.mk v).hom) := by rw [H.w]; infer_instance
    exact SemiAbelianDescent.isSeparated_of_comp φ _
  exact ⟨hcomm, hs, ⟨⟩, SemiAbelianDescent.geometricallyConnected_of_isPullback H⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeGlobalFormsPrimitiveOfFrames
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FormsOnAb

open GlobalTheory.AbCoh

variable {R : Type} [CommRing R] {X : Scheme.{0}}

theorem globalFunctionsConstant_of_constant_after_baseChange (s : X ⟶ Sp R) (hU : UConst s) : CohomZeroIsConstants (OAff s) := by
  refine hU R X s (𝟙 X) ?_
  rw [Algebra.algebraMap_self, Cris.spMap_id]
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

variable {s : X ⟶ Sp R} {n : ℕ} (fr : Frame (OAff s) n) (hc : CohomZeroIsConstants (OAff s))

theorem coboundaryZero_frame_vectorField_globalForm_eq_zero (i : Fin n) (ω : GlobForm s) : d0 (OAff s) (fun T ↦ fr.δ i T (ω.1 T)) = 0 := by
  funext T T' φ
  rw [amitsur_d0_apply, ω.2 φ, fr.nat]
  exact sub_self _

def coef (i : Fin n) (ω : GlobForm s) : R := (hc _ (coboundaryZero_frame_vectorField_globalForm_eq_zero fr i ω)).exists.choose

theorem coef_spec (i : Fin n) (ω : GlobForm s) (T : AffOp X) :
    fr.δ i T (ω.1 T) = algebraMap R ((OAff s).obj T) (coef fr hc i ω) :=
  (hc _ (coboundaryZero_frame_vectorField_globalForm_eq_zero fr i ω)).exists.choose_spec T

theorem coef_eq (i : Fin n) (ω : GlobForm s) (r : R)
    (h : ∀ T, fr.δ i T (ω.1 T) = algebraMap R ((OAff s).obj T) r) : coef fr hc i ω = r :=
  (hc _ (coboundaryZero_frame_vectorField_globalForm_eq_zero fr i ω)).unique (coef_spec fr hc i ω) h

def coefL : GlobForm s →ₗ[R] (Fin n → R) where
  toFun ω i := coef fr hc i ω
  map_add' ω ω' := funext fun i ↦ coef_eq fr hc i _ _ fun T ↦ by
    simp only [Submodule.coe_add, Pi.add_apply, map_add]
    rw [coef_spec fr hc i ω T, coef_spec fr hc i ω' T]
  map_smul' r ω := funext fun i ↦ coef_eq fr hc i _ _ fun T ↦ by
    simp only [Submodule.coe_smul, Pi.smul_apply, LinearMap.map_smul_of_tower, RingHom.id_apply,
      smul_eq_mul, map_mul, Algebra.smul_def]
    rw [coef_spec fr hc i ω T]

def sumL : (Fin n → R) →ₗ[R] GlobForm s where
  toFun c := ∑ i, c i • fr.w i
  map_add' c c' := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' r c := by simp [Finset.smul_sum, mul_smul]

theorem sumL_coefL (ω : GlobForm s) : sumL fr (coefL fr hc ω) = ω := by
  apply Subtype.ext
  funext T
  conv_rhs => rw [fr.sum T (ω.1 T)]
  simp only [sumL, coefL, LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_sum, Submodule.coe_smul,
    Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [coef_spec, algebraMap_smul]

include fr hc in

theorem projective : Module.Projective R (GlobForm s) :=
  Module.Projective.of_split (coefL fr hc) (sumL fr) (LinearMap.ext (sumL_coefL fr hc))

def back (U : AffOp X) (x : Ω[Sec s U.unop.1⁄R]) : Sec s U.unop.1 ⊗[R] GlobForm s :=
  ∑ i, (fr.δ i U x : Sec s U.unop.1) ⊗ₜ[R] fr.w i

theorem back_add (U : AffOp X) (x y : Ω[Sec s U.unop.1⁄R]) : back fr U (x + y) = back fr U x + back fr U y := by
  simp only [back, map_add, TensorProduct.add_tmul, Finset.sum_add_distrib]

include fr hc in

theorem par (U : AffOp X) : IsBaseChange (Sec s U.unop.1) (evForm s U) := by
  change Function.Bijective (TensorProduct.lift _)
  rw [Function.bijective_iff_has_inverse]
  refine ⟨back fr U, fun t ↦ ?_, fun x ↦ ?_⟩
  · induction t using TensorProduct.induction_on with
    | zero => simp [back]
    | tmul a ω =>
      simp only [TensorProduct.lift.tmul, LinearMap.restrictScalars_apply, LinearMap.flip_apply,
        Algebra.linearMap_apply, Module.algebraMap_end_apply, LinearMap.smul_apply]
      conv_rhs => rw [← sumL_coefL fr hc ω]
      simp only [back, sumL, coefL, LinearMap.coe_mk, AddHom.coe_mk, TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [← TensorProduct.smul_tmul]
      congr 1
      change fr.δ i U (a • ω.1 U) = coef fr hc i ω • a
      rw [(fr.δ i U).map_smul a (ω.1 U), coef_spec fr hc i ω U, Algebra.smul_def, mul_comm]
      rfl
    | add t t' ht ht' => rw [map_add, back_add, ht, ht']
  · conv_rhs => rw [fr.sum U x]
    simp only [back, map_sum, TensorProduct.lift.tmul, LinearMap.restrictScalars_apply, LinearMap.flip_apply,
        Algebra.linearMap_apply, Module.algebraMap_end_apply, LinearMap.smul_apply]
    rfl

end GlobalTheory.FormsOnAb

namespace GlobalTheory.FormsOnAb

open GlobalTheory.AbCoh

theorem formSt_of (H : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom →
      GlobalTheory.AbCoh.HasFrame (OAff A.hom) ∧ GlobalTheory.AbCoh.UConst A.hom ∧ GlobalTheory.AbCoh.PrimF A) : FormSt := by
  intro R₀ _ A _ g hA hs
  obtain ⟨⟨n, ⟨fr⟩⟩, hU, hP⟩ := H R₀ A g hA hs
  have hc := globalFunctionsConstant_of_constant_after_baseChange A.hom hU
  refine ⟨fun U ↦ par fr hc U, projective fr hc, fun w wm w₁ w₂ hm h1 h2 ↦ ?_⟩
  rw [hm.eq_pullForm, h1.eq_pullForm, h2.eq_pullForm]
  exact hP w

end GlobalTheory.FormsOnAb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeLocallyConstantRelDimStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_locally_constant_relDim : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ s : S, ∃ (V : S.Opens) (g : ℕ), IsAffineOpen V ∧ s ∈ V ∧ SmoothOfRelativeDimension g (pullback.snd A.hom V.ι) := by
  first | exact @GlobalTheory.DualCon.abelianScheme_locally_relDim | exact GlobalTheory.DualCon.abelianScheme_locally_relDim | (intros; apply GlobalTheory.DualCon.abelianScheme_locally_relDim <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeUnitsLiftAlongThickeningStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_units_lift_along_thickening : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (T₂ T₀ : Over S) (k : T₀ ⟶ T₂), IsAffine T₂.left → IsClosedImmersion k.left → Surjective k.left → Function.Surjective (Units.map (A ◁ k).left.appTop.hom.toMonoidHom) := by
  first | exact @GlobalTheory.DualOpen.units_lift_of_thickening | exact GlobalTheory.DualOpen.units_lift_of_thickening | (intros; apply GlobalTheory.DualOpen.units_lift_of_thickening <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSquareAffineH1Vanish
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Obs

theorem sq_abelian_and_affine_H1 : ∀ (R : Type) [CommRing R], (∀ (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → IsAbelianScheme (A ⊗ A) ∧ SmoothOfRelativeDimension (g + g) (A ⊗ A).hom) ∧ ∀ (X : Scheme.{0}) [IsAffine X] (s : X ⟶ Sp R) (c : HO1 s), c = 0 := by
  intro R _
  refine ⟨fun A _ g hA hg ↦ ⟨ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA, ?_⟩, fun X _ s c ↦ ?_⟩
  · haveI := hg
    haveI : SmoothOfRelativeDimension g (Limits.pullback.fst A.hom A.hom) :=
      (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
        (IsPullback.of_hasPullback _ _).flip hg
    exact inferInstanceAs (SmoothOfRelativeDimension (g + g) (Limits.pullback.fst A.hom A.hom ≫ A.hom))
  · let T₀ : AffOp X := Opposite.op ⟨⊤, isAffineOpen_top X⟩
    have h : Limits.IsInitial T₀ := Limits.IsInitial.ofUniqueHom
      (fun U ↦ (homOfLE (show U.unop ≤ ⟨⊤, isAffineOpen_top X⟩ from le_top (a := U.unop.1))).op) fun _ _ ↦ rfl
    exact H1.eq_zero_of_isInitial _ h c

end GlobalTheory.Obs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyFiniteCoverByTranslatePairsStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianVariety_finite_cover_by_translate_pairs : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ V : A.left.Opens, (V : Set A.left).Nonempty → ∃ (n : ℕ) (a : Fin n → (𝟙_ (Over (Sp K)) ⟶ A)), ⨆ i, ((𝟙 A * (toUnit A ≫ a i)).left ⁻¹ᵁ V ⊓ (𝟙 A * (toUnit A ≫ a i)⁻¹).left ⁻¹ᵁ V) = ⊤ := by
  first | exact @GlobalTheory.AbCover.cover | exact GlobalTheory.AbCover.cover | (intros; apply GlobalTheory.AbCover.cover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveLineBundleFamilyCalculusRulesStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additiveLineBundleFamily_calculus_rules : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], (∀ (T Y : Over S) (N : LB (A ⊗ T).left) (y : Y ⟶ T), Fam A N → Fam A (ev N (fst A Y) (snd A Y ≫ y))) ∧ (∀ (T U Y : Over S) (N : LB (A ⊗ T).left) (M : LB (A ⊗ U).left) (hN : Fam A N) (hM : Fam A M) (y : Y ⟶ T) (u : Y ⟶ U) (D : LB (A ⊗ Y).left) (hD : D.IsLB), (cls D hD = GlobalTheory.CechPic.pull (A ◁ y).left (cls N hN.isLB) + GlobalTheory.CechPic.pull (A ◁ u).left (cls M hM.isLB) ∨ cls D hD = GlobalTheory.CechPic.pull (A ◁ y).left (cls N hN.isLB) - GlobalTheory.CechPic.pull (A ◁ u).left (cls M hM.isLB)) → Fam A D) ∧ (∀ (T U Y : Over S) (N : LB (A ⊗ T).left) (M : LB (A ⊗ U).left) (hN : N.IsLB) (hM : M.IsLB) (y : Y ⟶ T) (u : Y ⟶ U), Same A N M y u ↔ GlobalTheory.CechPic.pull (A ◁ y).left (cls N hN) = GlobalTheory.CechPic.pull (A ◁ u).left (cls M hM)) ∧ (∀ (T U Y Z : Over S) (N : LB (A ⊗ T).left) (M : LB (A ⊗ U).left) (y : Y ⟶ T) (u : Y ⟶ U) (z : Z ⟶ Y), N.IsLB → M.IsLB → Same A N M y u → Same A N M (z ≫ y) (z ≫ u)) ∧ (∀ (T U Y Z : Over S) (N : LB (A ⊗ T).left) (M : LB (A ⊗ U).left) (y : Y ⟶ T) (z : Z ⟶ Y) (u : Z ⟶ U), N.IsLB → M.IsLB → (Same A (ev N (fst A Y) (snd A Y ≫ y)) M z u ↔ Same A N M (z ≫ y) u)) := by
  first | exact @GlobalTheory.FamCalc.famCalc | exact GlobalTheory.FamCalc.famCalc | (intros; apply GlobalTheory.FamCalc.famCalc <;> assumption)
end

