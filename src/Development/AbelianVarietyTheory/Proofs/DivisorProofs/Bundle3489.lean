import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0518
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3471
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3462
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2492
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundaryBranchesDistinctPrimesToricChart
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2875
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0066
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivPullCompIff
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeTorusCompare
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0469
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SplitsAt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianLocusOpenFamilyOverLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3485
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheaf
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3407
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3432
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3446
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianPartIdentificationsAgreeConstantTangent
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RigHom

theorem isNilpotent_ker_fst (k : Type) [Field k] :
    IsNilpotent (RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom) := by
  refine ⟨2, ?_⟩
  rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff]
  refine Submodule.mul_le.2 fun a ha b hb => ?_
  rw [RingHom.mem_ker] at ha hb
  change a.fst = 0 at ha
  change b.fst = 0 at hb
  rw [Submodule.mem_bot]
  ext <;> simp [ha, hb]

theorem mk_ker_fst_eq (k : Type) [Field k] :
    Ideal.Quotient.mk (RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom) =
      ((Ideal.Quotient.mk (RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom)).comp
        (algebraMap k (DualNumber k))).comp (TrivSqZeroExt.fstHom k k k).toRingHom := by
  refine RingHom.ext fun x => ?_
  simp only [RingHom.comp_apply]
  rw [Ideal.Quotient.eq, RingHom.mem_ker]
  simp [TrivSqZeroExt.algebraMap_eq_inl]

end GlobalTheory.RigHom

namespace GlobalTheory.RigHom

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

theorem comp_eq_of_const : ∀ {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) {W₀ : Type} [CommRing W₀] (ιb : W₀ →+* R) (B₀ : Over (Sp W₀)) [GrpObj B₀] (β : Q.P.A.left ⟶ B₀.left), IsGrpPullback Q.P.A B₀ (spMap ιb) β → ∀ (k : Type) [Field k] (ρ : R →+* DualNumber k), ρ.comp ιb = GlobalTheory.RigChart.constHom (ρ.comp ιb) → ∀ (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ Q.P.A.left), IsGrpPullback B' Q.P.A (spMap ρ) π₁ → IsGrpPullback B' Q.P.A (spMap (GlobalTheory.RigChart.constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → π₁ ≫ β = π₂ ≫ β := by
  intro R _ _ Q W₀ _ ιb B₀ _ β hβ k _ ρ hρ B' _ π₁ π₂ h₁ h₂ h0
  have c₁ : IsGrpPullback B' B₀ (spMap (ρ.comp ιb)) (π₁ ≫ β) :=
    (IsGrpPullback.comp h₁ hβ).congr (spMap_comp' ιb ρ) rfl
  have c₂ : IsGrpPullback B' B₀ (spMap (ρ.comp ιb)) (π₂ ≫ β) := by
    refine (IsGrpPullback.comp h₂ hβ).congr ?_ rfl
    rw [spMap_comp', hρ]
    rfl
  have hab : IsAbelianScheme B' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback Q.P.isAb h₁
  obtain ⟨e₁, he₁, f₁⟩ := grpPullback_iso c₁ (isGrpPullback_pullback B₀ (spMap (ρ.comp ιb)))
  obtain ⟨e₂, he₂, f₂⟩ := grpPullback_iso c₂ (isGrpPullback_pullback B₀ (spMap (ρ.comp ιb)))
  let I := RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom
  have hI : I ≤ nilradical (DualNumber k) := by
    obtain ⟨n, hn⟩ := isNilpotent_ker_fst k
    intro x hx
    exact ⟨n, by
      have : x ^ n ∈ I ^ n := Ideal.pow_mem_pow hx n
      rw [hn] at this
      simpa using this⟩
  have hj : pullback.fst B'.hom (spMap (Ideal.Quotient.mk I)) ≫ π₁ =
      pullback.fst B'.hom (spMap (Ideal.Quotient.mk I)) ≫ π₂ := by
    refine h0 _ _ (pullback.snd B'.hom (spMap (Ideal.Quotient.mk I)) ≫
      spMap ((Ideal.Quotient.mk I).comp (algebraMap k (DualNumber k)))) ?_
    rw [pullback.condition, Category.assoc, spMap_comp']
    congr 2
    exact mk_ker_fst_eq k
  have key : e₁.hom = e₂.hom := by
    refine GlobalTheory.NilRigidity.eq_of_eq_on_quotient I hI B' _ hab e₁.hom e₂.hom ?_
      (by rw [he₁.one_hom, he₂.one_hom])
    apply pullback.hom_ext
    · have f₁' : e₁.hom.left ≫ pullback.fst B₀.hom (spMap (ρ.comp ιb)) = π₁ ≫ β := f₁
      have f₂' : e₂.hom.left ≫ pullback.fst B₀.hom (spMap (ρ.comp ιb)) = π₂ ≫ β := f₂
      rw [Category.assoc, Category.assoc, f₁', f₂', ← Category.assoc, hj, Category.assoc]
    · have w₁ : e₁.hom.left ≫ pullback.snd B₀.hom (spMap (ρ.comp ιb)) = B'.hom := Over.w e₁.hom
      have w₂ : e₂.hom.left ≫ pullback.snd B₀.hom (spMap (ρ.comp ιb)) = B'.hom := Over.w e₂.hom
      rw [Category.assoc, Category.assoc, w₁, w₂]
  rw [← f₁, ← f₂, key]

end GlobalTheory.RigHom
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeHomEqOfPowEqStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_hom_eq_of_pow_eq : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B], IsAbelianScheme A → IsAbelianScheme B → ∀ (d : ℕ), 0 < d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → ∀ (x y : B ⟶ A), IsMonHom x → IsMonHom y → x ^ d = y ^ d → x = y := by
  first | (exact @GlobalTheory.HomTorsionFree.eq_of_pow_eq) | (exact GlobalTheory.HomTorsionFree.eq_of_pow_eq) | (intros; apply GlobalTheory.HomTorsionFree.eq_of_pow_eq  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeModuleActionHomomorphism
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbDivLocal

theorem exists_pow_eq {V : Type} [CommRing V] [IsLocalRing V] [IsNoetherianRing V]
    (hc : IsAdicComplete (maximalIdeal V) V) (hk : IsAlgClosed (ResidueField V))
    (B : Over (Sp V)) [GrpObj B] (hB : IsAbelianScheme B) (n : ℕ) (hn : IsUnit (n : V))
    (P : 𝟙_ (Over (Sp V)) ⟶ B) : ∃ Q : 𝟙_ (Over (Sp V)) ⟶ B, Q ^ n = P := by
  have hn' : IsUnit (n : Γ(Sp V, ⊤)) := by
    simpa using hn.map (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom
  obtain ⟨-, hfin, het, hsurj⟩ :=
    GlobalTheory.abelianScheme_id_pow_finite_etale_surjective (Sp V) B n hB hn'
  set m : B ⟶ B := (𝟙 B) ^ n with hm
  let U : Over (Sp V) := Over.mk (pullback.snd m.left P.left)
  have hU : Smooth U.hom := by dsimp [U]; infer_instance
  let r : Sp (ResidueField V) ⟶ Sp V := spMap (residue V)
  let P₀ : Sp (ResidueField V) ⟶ B.left := r ≫ P.left
  have : CompactSpace ↥(pullback m.left P₀) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd m.left P₀)
  obtain ⟨p, -⟩ := (pullback.snd m.left P₀).surjective (default : PrimeSpectrum (ResidueField V))
  obtain ⟨z, -, hz⟩ :=
    isClosed_univ.exists_closed_singleton (X := ↥(pullback m.left P₀)) ⟨p, trivial⟩
  have hw := pointOfClosedPoint_comp (pullback.snd m.left P₀) z hz
  let x₀ : Sp (ResidueField V) ⟶ U.left :=
    pullback.lift (pointOfClosedPoint (pullback.snd m.left P₀) z hz ≫ pullback.fst _ _) r (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hw, Category.id_comp])
  have hx₀ : x₀ ≫ U.hom = spMap ((residue V).comp (RingHom.id V)) := by
    rw [RingHom.comp_id]
    exact pullback.lift_snd _ _ _
  obtain ⟨a, ha, -⟩ :=
    GlobalTheory.HenselLift.exists_lift_mem_open V V hc (RingHom.id V) U hU x₀ hx₀ ⊤ (by simp)
  have ha' : a ≫ pullback.snd m.left P.left = 𝟙 _ := by
    refine ha.trans ?_
    rw [spMap, show CommRingCat.ofHom (RingHom.id V) = 𝟙 (CommRingCat.of V) from rfl, Spec.map_id]
  have key : (a ≫ pullback.fst m.left P.left) ≫ m.left = P.left := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, ha', Category.id_comp]
  refine ⟨Over.homMk (a ≫ pullback.fst m.left P.left) ?_, ?_⟩
  · rw [← Over.w m, ← Category.assoc, key]
    exact Over.w P
  · have e : ∀ Q : 𝟙_ (Over (Sp V)) ⟶ B, Q ^ n = Q ≫ m := fun Q => by
      rw [hm, comp_pow, Category.comp_id]
    rw [e]
    exact Over.OverMorphism.ext key

end GlobalTheory.AbDivLocal

namespace GlobalTheory.AbDivLocal

abbrev ptsModule {S : Scheme.{0}} (T : Over S) (B : Over S) [GrpObj B] [IsCommMonObj B] (O : Type)
    [CommRing O] (a : OAct O B) : Module O (Additive (T ⟶ B)) where
  smul o p := Additive.ofMul (p.toMul ≫ a.act o)
  one_smul p := by
    change Additive.ofMul (p.toMul ≫ a.act 1) = p
    rw [a.one, Category.comp_id]; rfl
  mul_smul o o' p := by
    change Additive.ofMul (p.toMul ≫ a.act (o * o')) =
      Additive.ofMul ((p.toMul ≫ a.act o') ≫ a.act o)
    rw [mul_comm, a.mul, Category.assoc]
  smul_zero o := by
    change Additive.ofMul ((1 : T ⟶ B) ≫ a.act o) = Additive.ofMul 1
    haveI := a.hom o
    rw [one_comp]
  smul_add o p q := by
    change Additive.ofMul ((p.toMul * q.toMul) ≫ a.act o) =
      Additive.ofMul ((p.toMul ≫ a.act o) * (q.toMul ≫ a.act o))
    haveI := a.hom o
    rw [mul_comp]
  add_smul o o' p := by
    change Additive.ofMul (p.toMul ≫ a.act (o + o')) =
      Additive.ofMul ((p.toMul ≫ a.act o) * (p.toMul ≫ a.act o'))
    rw [a.add, comp_mul]
  zero_smul p := by
    change Additive.ofMul (p.toMul ≫ a.act 0) = Additive.ofMul 1
    have h0 : a.act 0 = 1 := by
      have h := a.add 0 0
      rw [add_zero] at h
      exact (mul_eq_left.mp h.symm)
    rw [h0, comp_one]

theorem exists_divided_linear : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V], IsAdicComplete (maximalIdeal V) V → IsAlgClosed (ResidueField V) → ∀ (B : Over (Sp V)) [GrpObj B], IsAbelianScheme B → ∀ (O : Type) [CommRing O] [IsDomain O] [Module.Finite ℤ O] (a : OAct O B) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] (x : X → (𝟙_ (Over (Sp V)) ⟶ B)), (∀ y z, x (y + z) = x y * x z) → (∀ (o : O) y, x (o • y) = x y ≫ a.act o) → ∀ n : ℕ, IsUnit (n : V) → ∃ x' : X → (𝟙_ (Over (Sp V)) ⟶ B), (∀ y z, x' (y + z) = x' y * x' z) ∧ (∀ (o : O) y, x' (o • y) = x' y ≫ a.act o) ∧ ∀ y, x' (n • y) = x y := by
  intro V _ _ _ _ hc hk B _ hB O _ _ _ a X _ _ _ _ x hadd hsmul n hn
  haveI := hB.comm
  letI := ptsModule (𝟙_ (Over (Sp V))) B O a
  let g : X →ₗ[O] Additive (𝟙_ (Over (Sp V)) ⟶ B) :=
    { toFun := fun y => Additive.ofMul (x y)
      map_add' := fun y z => by rw [hadd]; rfl
      map_smul' := fun o y => by rw [hsmul]; rfl }
  let f : Additive (𝟙_ (Over (Sp V)) ⟶ B) →ₗ[O] Additive (𝟙_ (Over (Sp V)) ⟶ B) :=
    n • LinearMap.id
  have hf : Function.Surjective f := by
    intro p
    obtain ⟨Q, hQ⟩ := exists_pow_eq hc hk B hB n hn p.toMul
    refine ⟨Additive.ofMul Q, ?_⟩
    change n • Additive.ofMul Q = p
    rw [← ofMul_pow, hQ]; rfl
  obtain ⟨h, hh⟩ := Module.projective_lifting_property f g hf
  refine ⟨fun y => (h y).toMul, fun y z => by
      change (h (y + z)).toMul = (h y).toMul * (h z).toMul
      rw [map_add]; rfl,
    fun o y => by
      change (h (o • y)).toMul = (h y).toMul ≫ a.act o
      rw [map_smul]; rfl, fun y => ?_⟩
  have e : n • h y = Additive.ofMul (x y) := LinearMap.congr_fun hh y
  change (h (n • y)).toMul = x y
  rw [map_nsmul, e]; rfl

end GlobalTheory.AbDivLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeUnobstructedSquareZeroAffineStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_unobstructed_squareZero_affine : GlobalTheory.Published.AbelianUnobstructed := by
  first | exact @GlobalTheory.UnobTop.abelianUnobstructed | exact GlobalTheory.UnobTop.abelianUnobstructed | (intros; apply GlobalTheory.UnobTop.abelianUnobstructed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchLogNormReciprocityOfPrincipalisationStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archLogNormReciprocity_of_principalisation : GlobalTheory.Published.Principalisation → GlobalTheory.MixHt.ArchRecip := by
  first | exact @GlobalTheory.MixHt.archRecip_of_principalisation | exact GlobalTheory.MixHt.archRecip_of_principalisation | (intros; apply GlobalTheory.MixHt.archRecip_of_principalisation <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithIntersectionNumberExistsOfMixedHeightsStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithIntersectionNumber_exists_of_mixedHeights : ArchInteg → (∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsAmb q → ∀ m : ℕ, ∃ T, IsMix q m T) → GlobalTheory.Published.ArFormExists := by
  first | exact @GlobalTheory.MixHt.arFormExists_of_isMix | exact GlobalTheory.MixHt.arFormExists_of_isMix | (intros; apply GlobalTheory.MixHt.arFormExists_of_isMix <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithMixedInterInductiveOfMixedHeightsStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithMixedInterInductive_of_mixedHeights : ArchInteg → (∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsAmb q → ∀ m : ℕ, ∃ T, IsMix q m T) → GlobalTheory.Published.ArMix := by
  first | exact @GlobalTheory.MixHt.arMix_of_mixHt | exact GlobalTheory.MixHt.arMix_of_mixHt | (intros; apply GlobalTheory.MixHt.arMix_of_mixHt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundaryBranchesDistinctPrimesToricChartStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundaryBranches_distinct_primes_toricChart : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → (∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) → ∀ (k : Type) [Field k] (m e : ℕ) (C : MonoFam Xo c φ (ChartRing k m e)) (ξ : Sp (ChartRing k m e) ⟶ S), IsTaut C → C.y ≫ j = jK _ ≫ ξ → ξ (closedPoint _) ∉ Set.range j → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → idlAlong (Scheme.IdealSheafData.vanishingIdeal j.opensRange.compl) ξ = Ideal.span {∏ i, C.s i} → (∀ p : Sp (ChartRing k m e), ξ p ∈ Set.range j ↔ ∏ i, C.s i ∉ p.asIdeal) → ∀ i i' : Fin m, (Ideal.span {bdParam k m e i}).comap (Scheme.stalkClosedPointTo ξ).hom = (Ideal.span {bdParam k m e i'}).comap (Scheme.stalkClosedPointTo ξ).hom → i = i' := by
  first | exact @GlobalTheory.BranchSep.branch_sep | exact GlobalTheory.BranchSep.branch_sep | (intros; apply GlobalTheory.BranchSep.branch_sep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCocycleMemCoboundaryAddMaximalSmul
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

noncomputable section

namespace GlobalTheory.CechBCInj

theorem grp_of_isPullback {X S' P : Scheme.{0}} (G : Over X) [GrpObj G] (hG : IsAbelianScheme G) (f : S' ⟶ X)
    (fst : P ⟶ G.left) (snd : P ⟶ S') (h : IsPullback fst snd G.hom f) :
    ∃ _ : GrpObj (Over.mk snd), IsAbelianScheme (Over.mk snd) := by
  letI : GrpObj ((Over.pullback f).obj G) := Functor.grpObjObj
  have hP := GlobalTheory.AbLaw.CubeGen.isAb_baseChange hG f
  let e : Over.mk snd ≅ (Over.pullback f).obj G := Over.isoMk h.isoPullback (by simp)
  letI gr : GrpObj (Over.mk snd) := GrpObj.ofIso e.symm
  refine ⟨gr, GlobalTheory.Compare.AbelianSchemeTorusCompare.isAbelianScheme_of_iso e ?_ hP⟩
  haveI : IsMonHom e.symm.hom := inferInstance
  exact isMonHom_inv_of_iso e.symm

theorem restrict_isPullback {X T : Scheme.{0}} (p : T ⟶ X) (U : X.affineOpens) :
    IsPullback (p ⁻¹ᵁ U.1).ι ((p ∣_ U.1) ≫ U.2.isoSpec.hom : (p ⁻¹ᵁ U.1).toScheme ⟶ Sp Γ(X, U.1)) p (chart U) := by
  have h1 := (isPullback_morphismRestrict p U.1).flip
  have h2 : IsPullback U.1.ι U.2.isoSpec.hom (𝟙 X) (U.2.isoSpec.inv ≫ U.1.ι) :=
    IsPullback.of_vert_isIso ⟨by simp⟩
  have h3 := h1.paste_vert h2
  rw [Category.comp_id] at h3
  have e : chart U = U.2.isoSpec.inv ≫ U.1.ι := (IsAffineOpen.isoSpec_inv_ι U.2).symm
  rw [e]
  exact h3

theorem resG_appLE' {X T : Scheme.{0}} (p : T ⟶ X) (U : X.affineOpens) {O O' : T.Opens} (hO : O ≤ p ⁻¹ᵁ U.1)
    (h : O' ≤ O) (r : Γ(X, U.1)) :
    resG T h ((p.appLE U.1 O hO).hom r) = (p.appLE U.1 O' (h.trans hO)).hom r := by
  show ((p.appLE U.1 O hO) ≫ T.presheaf.map (homOfLE h).op).hom r = _
  rw [Scheme.Hom.appLE_map]

theorem exists_fin_sum {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R) (x : M)
    (hx : x ∈ I • (⊤ : Submodule R M)) :
    ∃ (N : ℕ) (r : Fin N → R) (y : Fin N → M), (∀ k, r k ∈ I) ∧ x = ∑ k, r k • y k := by
  have key : ∃ l : List (R × M), (∀ p ∈ l, p.1 ∈ I) ∧ x = (l.map fun p => p.1 • p.2).sum := by
    refine Submodule.smul_induction_on hx (fun r hr n _ => ⟨[(r, n)], by simpa using hr, by simp⟩) ?_
    rintro a b ⟨l₁, h₁, rfl⟩ ⟨l₂, h₂, rfl⟩
    refine ⟨l₁ ++ l₂, fun p hp => ?_, by simp⟩
    rcases List.mem_append.1 hp with h | h
    exacts [h₁ p h, h₂ p h]
  obtain ⟨l, hl, rfl⟩ := key
  refine ⟨l.length, fun k => l[k].1, fun k => l[k].2, fun k => hl _ (List.getElem_mem _), ?_⟩
  exact (Fin.sum_univ_fun_getElem l (fun p => p.1 • p.2)).symm

theorem cocycle_mem_coboundary_add_smul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → ∀ (U : X.affineOpens) (J : Type) (W : J → t.G.left.Opens), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1) (m : Ideal Γ(X, U.1)), m.IsMaximal → ∀ (A : Over (Sp (Γ(X, U.1) ⧸ m))) (ι : A.left ⟶ t.G.left), IsPullback ι A.hom t.G.hom (spMap (Ideal.Quotient.mk m) ≫ chart U) → ∀ (c : ∀ i i' : J, Γ(t.G.left, W i ⊓ W i')), (∀ i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) → (∃ h' : ∀ i, Γ(A.left, ι ⁻¹ᵁ W i), ∀ i i', (ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom (c i i') = resG A.left inf_le_left (h' i) - resG A.left inf_le_right (h' i')) → ∃ (h : ∀ i : J, Γ(t.G.left, W i)) (N : ℕ) (r : Fin N → Γ(X, U.1)) (e : Fin N → ∀ i i' : J, Γ(t.G.left, W i ⊓ W i')), (∀ k, r k ∈ m) ∧ (∀ k i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (e k i i') + resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (e k i' i'') = resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (e k i i'')) ∧ ∀ i i', c i i' = resG t.G.left inf_le_left (h i) - resG t.G.left inf_le_right (h i') + ∑ k, (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (r k) * e k i i' := by
  intro E _ _ _ H X t hP U J W hWa hcov hWU m hm A ι hpb c hc hcob
  have sq := restrict_isPullback t.G.hom U
  obtain ⟨inst, hAb⟩ := grp_of_isPullback t.G
    (GlobalTheory.AbelianLocusNormalisation.isAbelianScheme_of_isProper t hP) (chart U) _ _ sq
  have hsq : ι ≫ t.G.hom = (A.hom ≫ spMap (Ideal.Quotient.mk m)) ≫ chart U := by
    rw [hpb.w, Category.assoc]
  let ι' := sq.lift ι (A.hom ≫ spMap (Ideal.Quotient.mk m)) hsq
  have hι' : ι' ≫ (t.G.hom ⁻¹ᵁ U.1).ι = ι := sq.lift_fst _ _ _
  have hw : ι' ≫ ((t.G.hom ∣_ U.1) ≫ U.2.isoSpec.hom : (t.G.hom ⁻¹ᵁ U.1).toScheme ⟶ Sp Γ(X, U.1)) =
      A.hom ≫ spMap (Ideal.Quotient.mk m) := sq.lift_snd _ _ _
  have hpb' : IsPullback ι' A.hom (Over.mk ((t.G.hom ∣_ U.1) ≫ U.2.isoSpec.hom :
      (t.G.hom ⁻¹ᵁ U.1).toScheme ⟶ Sp Γ(X, U.1))).hom (spMap (algebraMap Γ(X, U.1) (Γ(X, U.1) ⧸ m))) :=
    IsPullback.of_right (by rw [hι']; exact hpb) hw sq
  obtain ⟨Φ, hlin, hinj, hsurj, hnat⟩ := GlobalTheory.T.cech_comparison_structure_h1_affine X t.G.left t.G.hom t.semi.separated U J W hWa hcov hWU
  have h0 := hnat _ (algebraMap Γ(X, U.1) (Γ(X, U.1) ⧸ m)) A.left A.hom ι ι' hι' hpb'.w c hc hcob
  have hmem := GlobalTheory.T.structure_h1_nakayama_closed_fibre _ _ hAb m hm A.left A.hom ι' hpb' (Φ c) h0
  obtain ⟨N, r, y, hr, hy⟩ := exists_fin_sum m _ hmem
  choose e he hΦe using hsurj
  let ρ : ∀ i i' : J, Γ(X, U.1) →+* Γ(t.G.left, W i ⊓ W i') := fun i i' =>
    (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom
  let c' : ∀ i i' : J, Γ(t.G.left, W i ⊓ W i') := fun i i' => c i i' - ∑ k, ρ i i' (r k) * e (y k) i i'
  have hc' : (∀ i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c' i i') + resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c' i' i'') = resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c' i i'')) := by
    intro i i' i''
    simp only [c', ρ, map_sub, map_sum, map_mul, resG_appLE']
    rw [← hc i i' i'']
    have := fun k => he (y k) i i' i''
    simp only [← this, mul_add, Finset.sum_add_distrib]
    ring
  have hΦ : Φ c' = 0 := by
    rw [hlin c hc N r (fun k => e (y k)) (fun k => he (y k))]
    simp only [hΦe, ← hy, sub_self]
  obtain ⟨h, hh⟩ := hinj c' hc' hΦ
  refine ⟨h, N, r, fun k => e (y k), hr, fun k => he (y k), fun i i' => ?_⟩
  have := hh i i'
  simp only [c'] at this
  rw [sub_eq_iff_eq_add] at this
  exact this

end GlobalTheory.CechBCInj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechH1FiniteGenerationAffine
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechFin
open GlobalTheory.CatCoh GlobalTheory.CechDR

theorem isCoc_sub {Z : Scheme.{0}} {J : Type} (W : J → Z.Opens) {c c' : ∀ i i' : J, Γ(Z, W i ⊓ W i')}
    (hc : IsCoc W c) (hc' : IsCoc W c') : IsCoc W (fun i i' => c i i' - c' i i') := by
  intro i i' i''
  simp only [map_sub]
  linear_combination hc i i' i'' - hc' i i' i''

theorem cechFG_of_finite (R : Type) [CommRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) [CompactSpace Z]
    (hfin : Module.Finite R (HO1 s)) (J : Type) (W : J → Z.Opens)
    (hD : ∀ I : Finset J, I.Nonempty → IsAffineOpen (⨅ i ∈ I, W i)) (hc : ⨆ i, W i = ⊤) :
    CechFG W R (fun i i' => (secMap s (W i ⊓ W i')).hom) := by
  classical
  have hW : ∀ i, IsAffineOpen (W i) := fun i => by simpa using hD {i} (Finset.singleton_nonempty i)
  have hW2 : ∀ i i', IsAffineOpen (W i ⊓ W i') := fun i i' => by
    have h := hD {i, i'} (Finset.insert_nonempty _ _)
    rwa [Finset.iInf_insert, Finset.iInf_singleton] at h
  have hW3 : ∀ i i' i'', IsAffineOpen (W i ⊓ W i' ⊓ W i'') := fun i i' i'' => by
    have h := hD {i, i', i''} (Finset.insert_nonempty _ _)
    rwa [Finset.iInf_insert, Finset.iInf_insert, Finset.iInf_singleton, ← inf_assoc] at h
  obtain ⟨S, hS⟩ : ∃ S : Finset J, ⨆ i ∈ S, W i = ⊤ := by
    have hcov : (Set.univ : Set Z) ⊆ ⋃ i, (W i : Set Z) := by
      intro x _
      have hx : x ∈ ⨆ i, W i := hc ▸ trivial
      rw [TopologicalSpace.Opens.mem_iSup] at hx
      exact Set.mem_iUnion.2 hx
    obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover (fun i => (W i : Set Z)) (fun i => (W i).isOpen) hcov
    refine ⟨S, eq_top_iff.2 fun x _ => ?_⟩
    obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.1 (hS (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, TopologicalSpace.Opens.mem_iSup.2 ⟨hi, hx⟩⟩
  have hsur : ∀ c, IsCoc W c → ∃ (f : Z1 (OAff s)) (h : ∀ i, Γ(Z, W i)), ∀ i i',
      c i i' = rho W s hW hW2 f.1 i i' + (resG Z inf_le_left (h i) - resG Z inf_le_right (h i')) := by
    intro c hcoc
    obtain ⟨f, h₀, hf⟩ := GlobalTheory.T.cechCocycle_of_finite_affine_subcover R Z s J W hW hW2 hD S hS c hcoc
    obtain ⟨h, hh⟩ := GlobalTheory.T.cechCocycle_isCoboundary_of_isCoboundary_subcover Z J W (↑S) (fun i => by
        rw [show (⨆ a ∈ (↑S : Set J), W a) = ⨆ a ∈ S, W a from by simp, hS]; exact le_top)
      (fun i i' => c i i' - rho W s hW hW2 f.1 i i') (isCoc_sub W hcoc (rho_isCoc W s hW hW2 hW3 f)) h₀
      (fun a ha b hb => by rw [hf a ha b hb]; ring)
    exact ⟨f, h, fun i i' => by rw [← hh]; ring⟩
  obtain ⟨n, v, hv⟩ := Module.Finite.exists_fin (R := R) (M := HO1 s)
  choose fk hfk using fun k => H1.mk_surjective (OAff s) (v k)
  refine ⟨n, fun k => rho W s hW hW2 (fk k).1, fun k => rho_isCoc W s hW hW2 hW3 (fk k), fun c hcoc => ?_⟩
  obtain ⟨f, h, hfh⟩ := hsur c hcoc
  have hmem : H1.mk (OAff s) f ∈ Submodule.span R (Set.range v) := hv ▸ Submodule.mem_top
  obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hmem
  have hcl : H1.mk (OAff s) f = H1.mk (OAff s) (∑ k, r k • fk k) := by
    rw [map_sum, ← hr]
    simp only [map_smul, hfk]
  obtain ⟨g, hg⟩ := H1.mk_eq_mk.1 hcl
  have e1 : f.1 = (∑ k, r k • (fk k).1) + d0 (OAff s) g := by
    rw [hg, Submodule.coe_sum]
    simp only [Submodule.coe_smul]
    abel
  refine ⟨r, fun i => h i + (-gv s g ⟨W i, hW i⟩), fun i i' => ?_⟩
  rw [hfh, e1, rho_add, rho_sum, rho_d0, map_add, map_add]
  ring

end GlobalTheory.CechFin

open GlobalTheory.CechFin in
theorem GlobalTheory.CechFin.cech_h1_finite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → ∀ (U : X.affineOpens) (J : Type) (W : J → t.G.left.Opens), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1), ∃ (N : ℕ) (e : Fin N → ∀ i i' : J, Γ(t.G.left, W i ⊓ W i')), (∀ k i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (e k i i') + resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (e k i' i'') = resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (e k i i'')) ∧ ∀ c : ∀ i i' : J, Γ(t.G.left, W i ⊓ W i'), (∀ i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) → ∃ (r : Fin N → Γ(X, U.1)) (h : ∀ i : J, Γ(t.G.left, W i)), ∀ i i', c i i' = resG t.G.left inf_le_left (h i) - resG t.G.left inf_le_right (h i') + ∑ k, (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (r k) * e k i i' := by
  intro E _ _ _ H X t hP hA U J W hWaff hcov hWU
  obtain ⟨hcomp, hD, htop⟩ := GlobalTheory.T.properSemiAbelian_affineOpen_baseChange_compact_cover E H X t hP U J W hWaff hcov
  have hfin := GlobalTheory.T.structure_h1_finite_affine_open E H X t hP U
  exact GlobalTheory.T.cech_finite_generation_of_affine_base_change t.G.left X t.G.hom U J W hWU
    (cechFG_of_finite Γ(X, U.1) (pullback t.G.hom U.2.fromSpec) (pullback.snd t.G.hom U.2.fromSpec) hfin J _ hD htop)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartRingActionCompatibleExtendedStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_ringAction_compatible_extended : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {R : Type} [CommRing R] [IsDomain R] (tC : SAB H (Sp R)) {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (ξ : Sp R ⟶ S) (πC : tC.G.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback tC.G G ξ πC → ∀ (act : OAct (𝓞 E) G) (tK : SAB H (Sp (FractionRing R))) (a : SABMap tK tC (jK R)) (ψ : tK.G.left ⟶ G.left), (∀ u, (tK.act.act u).left ≫ ψ = ψ ≫ (act.act u).left) → a.φ ≫ πC = ψ → ∀ u, (tC.act.act u).left ≫ πC = πC ≫ (act.act u).left := by
  first | exact @GlobalTheory.UChart.act_chart_compat | exact GlobalTheory.UChart.act_chart_compat | (intros; apply GlobalTheory.UChart.act_chart_compat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreProjectiveEmbeddingFactorsProperStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closedFibre_projectiveEmbedding_factors_proper : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ E : Emb M.π G', ∃ (P' : Scheme.{0}) (b : P' ⟶ PSpace R E.N) (X : E.H.toScheme.Opens) (a : X.toScheme ⟶ P'), IsNoetherian P' ∧ IsSeparated b ∧ LocallyOfFiniteType b ∧ IsProper a ∧ Surjective a ∧ (∀ V : P'.Opens, Function.Bijective (a.app V).hom) ∧ a ≫ b = X.ι ≫ E.f ∧ (∀ z : E.H.toScheme, M.π (G'.hom (E.H.ι z)) = closedPoint R → z ∈ X) ∧ ∀ x : P', IsClosed ({x} : Set P') → (b ≫ PSpace.str R E.N) x = closedPoint R → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ξ : Sp Ω ⟶ P') (s : Sp Ω ⟶ M.S), Set.range ξ = {x} → ξ ≫ b ≫ PSpace.str R E.N = s ≫ M.π → ∃ p : Sp Ω ⟶ X.toScheme, p ≫ a = ξ ∧ p ≫ X.ι ≫ E.H.ι ≫ G'.hom = s := by
  first | exact @GlobalTheory.Mum.closedFibre_chart | exact GlobalTheory.Mum.closedFibre_chart | (intros; apply GlobalTheory.Mum.closedFibre_chart <;> assumption)
end

