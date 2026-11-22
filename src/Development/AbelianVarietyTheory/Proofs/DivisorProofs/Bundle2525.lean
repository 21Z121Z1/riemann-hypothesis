import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2432
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FlatBCSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2423
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2382
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2290
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2422
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2375
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2377
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SizeBoundStatement

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearlyDisjointFunctionFieldOfFlatBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

set_option autoImplicit false

namespace GlobalTheory.Desc.FlatLin

theorem fnOf_algX {X : Scheme.{0}} [IsIntegral X] {R : Type} [CommRing R] (p : X ⟶ Sp R) (U : X.Opens)
    (hU : genericPoint X ∈ U) (r : R) :
    fnOf U hU (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U r) = cst p r := by
  simp only [ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX, cst, RingHom.comp_apply, fnOf, Scheme.Hom.appLE,
    CommRingCat.hom_comp]
  erw [TopCat.Presheaf.germ_res_apply]
  rfl

theorem gen_map {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] {π : Y ⟶ X}
    {θ : X.functionField →+* Y.functionField} (h : PFF (𝟙 _) π θ) : π (genericPoint Y) = genericPoint X := by
  obtain ⟨l, h1, h2⟩ := h
  rw [Category.comp_id] at h1
  subst h1
  have eY : gp Y (closedPoint (Y.presheaf.stalk (genericPoint Y))) = genericPoint Y :=
    Scheme.fromSpecStalk_closedPoint
  have hc : (spMap θ) (closedPoint (Y.presheaf.stalk (genericPoint Y))) =
      closedPoint (X.presheaf.stalk (genericPoint X)) :=
    Subsingleton.elim (α := PrimeSpectrum X.functionField) _ _
  calc π (genericPoint Y) = π (gp Y (closedPoint (Y.presheaf.stalk (genericPoint Y)))) := by rw [eY]
    _ = (gp Y ≫ π) (closedPoint (Y.presheaf.stalk (genericPoint Y))) := (Scheme.Hom.comp_apply _ _ _).symm
    _ = (spMap θ ≫ gp X) (closedPoint (Y.presheaf.stalk (genericPoint Y))) := by rw [h2]
    _ = gp X (spMap θ (closedPoint (Y.presheaf.stalk (genericPoint Y)))) := Scheme.Hom.comp_apply _ _ _
    _ = genericPoint X := by rw [hc]; exact Scheme.fromSpecStalk_closedPoint

theorem fnOf_appLE {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] {π : Y ⟶ X}
    {θ : X.functionField →+* Y.functionField} (h : PFF (𝟙 _) π θ) (U : X.Opens) (V : Y.Opens)
    (e : V ≤ π ⁻¹ᵁ U) (hU : genericPoint X ∈ U) (hV : genericPoint Y ∈ V) (a : Γ(X, U)) :
    fnOf V hV ((π.appLE U V e).hom a) = θ (fnOf U hU a) := by
  rw [GaussPt.theta_fnOf h U hU (e hV) a]
  simp only [fnOf, Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply]
  erw [TopCat.Presheaf.germ_res_apply]

theorem linDisj_of_flat : ∀ (T D : Type) [CommRing T] [CommRing D] (a : T →+* D), a.Flat → ∀ (H : Over (Sp T)) [IsIntegral H.left] (H' : Over (Sp D)) [IsIntegral H'.left] (π : H'.left ⟶ H.left) (θ : H.left.functionField →+* H'.left.functionField), IsPullback π H'.hom H.hom (spMap a) → PFF (𝟙 _) π θ → LinDisj (GlobalTheory.Desc.cst H.hom) (GlobalTheory.Desc.cst H'.hom) θ := by
  intro T D _ _ a ha H _ H' _ π θ hpb hθ n u hu r hr
  classical
  letI : Algebra T D := a.toAlgebra
  haveI : Module.Flat T D := ha
  have hη : π (genericPoint H'.left) = genericPoint H.left := gen_map hθ
  obtain ⟨U, hUa, hηU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 H.left.isBasis_affineOpens)
    (show genericPoint H.left ∈ (⊤ : H.left.Opens) from trivial)
  haveI : Nonempty U := ⟨⟨_, hηU⟩⟩
  haveI := functionField_isFractionRing_of_isAffineOpen H.left U hUa
  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors Γ(H.left, U)) u
  choose A hA using hs
  have hA' : ∀ i, fnOf U hηU (A i) = fnOf U hηU s * u i := fun i => by
    have := hA i; rw [Algebra.smul_def] at this; exact this
  have hs0 : fnOf U hηU s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
  letI : Algebra T Γ(H.left, U) := (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX H.hom U).toAlgebra
  let f : (Fin n → T) →ₗ[T] Γ(H.left, U) :=
    { toFun := fun c => ∑ i, c i • A i
      map_add' := fun c d => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun t c => by simp [Finset.smul_sum, smul_smul] }
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    apply hu c
    have h1 := congrArg (fnOf U hηU) hc
    simp only [f, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_zero, Algebra.smul_def, map_mul,
      RingHom.algebraMap_toAlgebra, fnOf_algX, hA'] at h1
    have e : fnOf U hηU s * ∑ i, cst H.hom (c i) * u i = 0 := by
      rw [Finset.mul_sum, ← h1]; refine Finset.sum_congr rfl fun i _ => ?_; ring
    exact (mul_eq_zero.1 e).resolve_left hs0
  have hfD : Function.Injective (f.lTensor D) := Module.Flat.lTensor_preserves_injective_linearMap f hf
  let x := (TensorProduct.piScalarRight T T D (Fin n)).symm r
  have hx : f.lTensor D x = ∑ i, r i ⊗ₜ[T] A i := by
    conv_lhs => rw [show x = ∑ i, (TensorProduct.piScalarRight T T D (Fin n)).symm (Pi.single i (r i)) by
      simp only [x, ← map_sum, Finset.univ_sum_single]]
    simp only [TensorProduct.piScalarRight_symm_single, map_sum, LinearMap.lTensor_tmul]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    simp [f, Pi.single_apply]
  let V' : H'.left.Opens := π ⁻¹ᵁ U ⊓ H'.hom ⁻¹ᵁ ⊤
  have hV' : genericPoint H'.left ∈ V' := ⟨show π _ ∈ U by rw [hη]; exact hηU, trivial⟩
  let E := ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.eTens H.hom H'.hom π hpb U hUa
  let y : TensorProduct T Γ(H.left, U) D := TensorProduct.comm T D Γ(H.left, U) (f.lTensor D x)
  have hy : y = ∑ i, A i ⊗ₜ[T] r i := by
    simp only [y, hx, map_sum, TensorProduct.comm_tmul]
  have hEy : fnOf V' hV' (E y) = 0 := by
    rw [hy, map_sum, map_sum]
    have step : ∀ i, fnOf V' hV' (E (A i ⊗ₜ[T] r i)) = θ (fnOf U hηU s * u i) * cst H'.hom (r i) := fun i => by
      rw [show E (A i ⊗ₜ[T] r i) = _ from ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.eTens_tmul H.hom H'.hom π hpb U hUa (A i) (r i)]
      rw [map_mul, fnOf_appLE hθ U V' inf_le_left hηU hV', fnOf_algX, hA']
    rw [Finset.sum_congr rfl fun i _ => step i]
    have e : ∑ i, θ (fnOf U hηU s * u i) * cst H'.hom (r i) =
        θ (fnOf U hηU s) * ∑ i, cst H'.hom (r i) * θ (u i) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; rw [map_mul]; ring
    rw [e, hr, mul_zero]
  have hy0 : y = 0 := by
    have : E y = 0 := fnOf_injective V' hV' (by rw [hEy, map_zero])
    exact E.injective (this.trans E.map_zero.symm)
  have hx0 : x = 0 := by
    apply hfD
    rw [map_zero]
    exact (TensorProduct.comm T D Γ(H.left, U)).injective (hy0.trans (map_zero _).symm)
  have : r = (TensorProduct.piScalarRight T T D (Fin n)) x := by simp only [x, LinearEquiv.apply_symm_apply]
  rw [this, hx0, map_zero]

end GlobalTheory.Desc.FlatLin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyFreeOfMaximalIdealGeneratorStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locally_free_of_maximal_ideal_generator : ∀ (R O : Type) [CommRing R] [CommRing O] (J : Type) [Fintype J] (b : Module.Basis J ℤ O)
    (M : Type) [AddCommGroup M] [Module R M] [Module O M] [SMulCommClass R O M],
    (∀ p : Ideal R, p.IsMaximal → ∃ g : R, g ∉ p ∧ ∃ m : M,
      (∀ x : M, ∃ (n : ℕ) (c : J →₀ R), g ^ n • x = Finsupp.linearCombination R (fun i => b i • m) c) ∧
      (∀ c : J →₀ R, Finsupp.linearCombination R (fun i => b i • m) c = 0 → ∃ n : ℕ, g ^ n • c = 0)) →
    letI : Module (R ⊗[ℤ] O) M := TensorProduct.Algebra.module
    Module.Invertible (R ⊗[ℤ] O) M := by
  first | exact @GlobalTheory.InvGlue.invertible_of_locally_singly_generated | exact GlobalTheory.InvGlue.invertible_of_locally_singly_generated | (intros; apply GlobalTheory.InvGlue.invertible_of_locally_singly_generated <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyOfFiniteTypeNearGenerisationOfPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.USpread

theorem lft_of_pullback {X V P S T Y : Scheme.{0}} (j : X ⟶ V) (q : V ⟶ P) (s : S ⟶ P) (t : T ⟶ S)
    (u : Y ⟶ X) (b : Y ⟶ T) [LocallyOfFiniteType j] [LocallyOfFiniteType (pullback.snd q s)]
    (h : IsPullback u b (j ≫ q) (t ≫ s)) : LocallyOfFiniteType b := by
  have h1 := (IsPullback.of_hasPullback j (pullback.fst q s)).paste_vert (IsPullback.of_hasPullback q s)
  have h2 := (IsPullback.of_hasPullback (pullback.snd j (pullback.fst q s) ≫ pullback.snd q s) t).paste_horiz h1
  rw [← h.isoIsPullback_hom_snd _ _ h2]
  infer_instance

theorem exists_to_stalk (R : Type) [CommRing R] (x : Sp R) [x.asIdeal.IsPrime] :
    ∃ t : Sp (Localization.AtPrime x.asIdeal) ⟶ Spec ((Sp R).presheaf.stalk x),
      t ≫ (Sp R).fromSpecStalk x =
        Spec.map (CommRingCat.ofHom (algebraMap R (Localization.AtPrime x.asIdeal))) := by
  let y : PrimeSpectrum R := x
  haveI := StructureSheaf.IsLocalization.to_stalk R y
  let e := IsLocalization.algEquiv (R := R) y.asIdeal.primeCompl
    ((Spec.structureSheaf R).presheaf.stalk y) (Localization.AtPrime y.asIdeal)
  refine ⟨Spec.map (CommRingCat.ofHom e.toRingEquiv.toRingHom), ?_⟩
  have := Scheme.Spec_fromSpecStalk' (CommRingCat.of R) x
  erw [this, ← Spec.map_comp]
  congr 1
  ext r
  exact e.commutes r

theorem away_finiteType (R : Type) [CommRing R] (f : R) (P A : Scheme.{0})
    (p : P ⟶ Sp R) (ιA : A ⟶ P) (a : A ⟶ Sp (Localization.Away f))
    (h : IsPullback ιA a p (GlobalTheory.Desc.awayMap f)) [LocallyOfFiniteType a]
    (C : Type) [CommRing C] [Algebra R C] (j : Sp C ⟶ P) [IsOpenImmersion j]
    (hj : j ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R C))) :
    Algebra.FiniteType R (Localization.Away (algebraMap R C f)) := by
  let D := Localization.Away (algebraMap R C f)
  have hu : IsUnit (algebraMap R D f) := by
    rw [IsScalarTower.algebraMap_apply R C D]
    exact IsLocalization.Away.algebraMap_isUnit _
  let ψ : Localization.Away f →+* D := IsLocalization.Away.lift f hu
  have hψ : ψ.comp (algebraMap R (Localization.Away f)) = algebraMap R D :=
    IsLocalization.Away.lift_comp f hu
  let k : Sp D ⟶ Sp C := Spec.map (CommRingCat.ofHom (algebraMap C D))
  haveI : IsOpenImmersion k := IsOpenImmersion.of_isLocalization (algebraMap R C f)
  have hψ' : Spec.map (CommRingCat.ofHom ψ) ≫ GlobalTheory.Desc.awayMap f =
      Spec.map (CommRingCat.ofHom (algebraMap R D)) := by
    rw [← hψ, CommRingCat.ofHom_comp, Spec.map_comp]
  have w : (k ≫ j) ≫ p = Spec.map (CommRingCat.ofHom ψ) ≫ GlobalTheory.Desc.awayMap f := by
    rw [hψ', Category.assoc, hj, IsScalarTower.algebraMap_eq R C D, CommRingCat.ofHom_comp,
      Spec.map_comp]
  haveI : IsOpenImmersion (GlobalTheory.Desc.awayMap f) := IsOpenImmersion.of_isLocalization f
  haveI : IsOpenImmersion ιA := MorphismProperty.of_isPullback h.flip ‹_›
  let l := h.lift _ _ w
  have hl : l ≫ ιA = k ≫ j := h.lift_fst _ _ w
  haveI : IsOpenImmersion (l ≫ ιA) := by rw [hl]; infer_instance
  haveI : IsOpenImmersion l := IsOpenImmersion.of_comp l ιA
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap R D))) := by
    rw [← hψ', ← h.lift_snd _ _ w]
    change LocallyOfFiniteType ((l ≫ a) ≫ _)
    infer_instance
  exact RingHom.finiteType_algebraMap.1
    ((HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 this)

theorem ne_zero (R : Type) [CommRing R] (f : R) (P A : Scheme.{0}) [IsIntegral P] [Nonempty A]
    (p : P ⟶ Sp R) (ιA : A ⟶ P) (a : A ⟶ Sp (Localization.Away f))
    (h : IsPullback ιA a p (GlobalTheory.Desc.awayMap f))
    (C : Type) [CommRing C] [Algebra R C] [Nonempty (Sp C)] (j : Sp C ⟶ P) [IsOpenImmersion j]
    (hj : j ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R C))) :
    algebraMap R C f ≠ 0 := by
  intro h0
  haveI : IsOpenImmersion (GlobalTheory.Desc.awayMap f) := IsOpenImmersion.of_isLocalization f
  haveI : IsOpenImmersion ιA := MorphismProperty.of_isPullback h.flip ‹_›
  obtain ⟨y, ⟨c, hc⟩, ⟨t, ht⟩⟩ := nonempty_preirreducible_inter
    j.isOpenEmbedding.isOpen_range ιA.isOpenEmbedding.isOpen_range
    (Set.range_nonempty _) (Set.range_nonempty _)
  have h1 : p y = PrimeSpectrum.comap (algebraMap R C) c := by
    rw [← hc, ← Scheme.Hom.comp_apply, hj]; rfl
  have h2 : p y = PrimeSpectrum.comap (algebraMap R (Localization.Away f)) (a t) := by
    rw [← ht, ← Scheme.Hom.comp_apply, h.w, Scheme.Hom.comp_apply]; rfl
  have h3 : f ∈ (PrimeSpectrum.comap (algebraMap R C) c).asIdeal := by
    change algebraMap R C f ∈ c.asIdeal
    rw [h0]; exact zero_mem _
  rw [← h1, h2] at h3
  exact (a t).isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h3
    (IsLocalization.Away.algebraMap_isUnit f))

theorem affine_case (R : Type) [CommRing R] [IsNoetherianRing R] (f : R) (P A : Scheme.{0})
    [IsIntegral P] [Nonempty A]
    (p : P ⟶ Sp R) (ιA : A ⟶ P) (a : A ⟶ Sp (Localization.Away f))
    (h : IsPullback ιA a p (GlobalTheory.Desc.awayMap f)) [LocallyOfFiniteType a]
    (x : Sp R) (V : P.Opens)
    [LocallyOfFiniteType (Limits.pullback.snd (V.ι ≫ p) ((Sp R).fromSpecStalk x))]
    (C : Type) [CommRing C] [IsDomain C] [Algebra R C] (j : Sp C ⟶ V) [IsOpenImmersion j]
    (hj : (j ≫ V.ι) ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R C)))
    (c : Sp C) (hc : (p ((j ≫ V.ι) c)).asIdeal ≤ x.asIdeal) :
    ∃ W : P.Opens, (j ≫ V.ι) c ∈ W ∧ W ≤ V ∧ LocallyOfFiniteType (W.ι ≫ p) := by
  haveI : Nonempty (Sp C) := ⟨c⟩
  haveI := x.isPrime
  have h1 := ne_zero R f P A p ιA a h C (j ≫ V.ι) hj
  have h2 := away_finiteType R f P A p ιA a h C (j ≫ V.ι) hj
  obtain ⟨t, ht⟩ := exists_to_stalk R x
  have hpb := (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct R (Localization.AtPrime x.asIdeal) C)).flip
  rw [← hj, ← ht, Category.assoc] at hpb
  have h3 := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1
    (lft_of_pullback _ _ _ _ _ _ hpb)
  have h4 : Algebra.FiniteType (Localization.AtPrime x.asIdeal)
      (TensorProduct R (Localization.AtPrime x.asIdeal) C) := RingHom.finiteType_algebraMap.1 h3
  obtain ⟨g, hg, hft⟩ := GlobalTheory.T.exists_finiteType_away_of_finiteType_atPrime R C f x.asIdeal h1 h2 h4
  let D := Localization.Away (algebraMap R C g)
  let k : Sp D ⟶ Sp C := Spec.map (CommRingCat.ofHom (algebraMap C D))
  haveI : IsOpenImmersion k := IsOpenImmersion.of_isLocalization (algebraMap R C g)
  have h5 : p ((j ≫ V.ι) c) = PrimeSpectrum.comap (algebraMap R C) c := by
    rw [← Scheme.Hom.comp_apply, hj]; rfl
  refine ⟨(k ≫ j ≫ V.ι).opensRange, ?_, ?_, ?_⟩
  · have : c ∈ Set.range (PrimeSpectrum.comap (algebraMap C D)) := by
      rw [PrimeSpectrum.localization_away_comap_range D (algebraMap R C g)]
      intro hgc
      apply hg
      apply hc
      rw [h5]
      exact hgc
    obtain ⟨d, hd⟩ := this
    exact ⟨d, by rw [Scheme.Hom.comp_apply, ← hd]; rfl⟩
  · rintro _ ⟨d, rfl⟩
    rw [← Category.assoc, Scheme.Hom.comp_apply]
    exact ((k ≫ j) d).2
  · have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap R D))) :=
      (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2
        (RingHom.finiteType_algebraMap.2 hft)
    have e : (k ≫ j ≫ V.ι) ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R D)) := by
      rw [Category.assoc, hj, IsScalarTower.algebraMap_eq R C D, CommRingCat.ofHom_comp,
        Spec.map_comp]
    rw [← Scheme.Hom.isoOpensRange_inv_comp, Category.assoc, e]
    infer_instance

theorem locally_finiteType_near : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (f : R) (P A : Scheme.{0}) [IsIntegral P] [Nonempty A] (p : P ⟶ Sp R) (ιA : A ⟶ P) (a : A ⟶ Sp (Localization.Away f)), IsPullback ιA a p (GlobalTheory.Desc.awayMap f) → LocallyOfFiniteType a → ∀ (x : Sp R) (V : P.Opens), LocallyOfFiniteType (Limits.pullback.snd (V.ι ≫ p) ((Sp R).fromSpecStalk x)) → ∀ z : P, z ∈ V → (p z).asIdeal ≤ x.asIdeal → ∃ W : P.Opens, z ∈ W ∧ W ≤ V ∧ LocallyOfFiniteType (W.ι ≫ p) := by
  intro R _ _ f P A _ _ p ιA a h ha x V hV z hz hzx
  obtain ⟨_, ⟨W₀, hW₀, rfl⟩, hzW, hWV⟩ :=
    P.isBasis_affineOpens.exists_subset_of_mem_open hz V.isOpen
  replace hW₀ : IsAffineOpen W₀ := hW₀
  haveI : Nonempty W₀ := ⟨⟨z, hzW⟩⟩
  have hr : Set.range hW₀.fromSpec ⊆ Set.range V.ι := by
    rw [hW₀.range_fromSpec, Scheme.Opens.range_ι]; exact hWV
  let j := IsOpenImmersion.lift V.ι hW₀.fromSpec hr
  have hj : j ≫ V.ι = hW₀.fromSpec := IsOpenImmersion.lift_fac _ _ _
  haveI : IsOpenImmersion (j ≫ V.ι) := by rw [hj]; infer_instance
  haveI : IsOpenImmersion j := IsOpenImmersion.of_comp j V.ι
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (hW₀.fromSpec ≫ p)
  letI : Algebra R Γ(P, W₀) := φ.hom.toAlgebra
  obtain ⟨c, hc⟩ : z ∈ Set.range hW₀.fromSpec := by rw [hW₀.range_fromSpec]; exact hzW
  have hc' : (j ≫ V.ι) c = z := by rw [hj]; exact hc
  have := affine_case R f P A p ιA a h x V Γ(P, W₀) j (by rw [hj, ← hφ]; rfl) c
    (by erw [hc']; exact hzx)
  erw [hc'] at this
  exact this

end GlobalTheory.USpread
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDerivationDetEqUnitMulProdNormalCrossings
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

namespace GlobalTheory

theorem derivation_prod_eq_zero_of_forall {F R : Type} [CommRing F] [CommRing R] [Algebra F R]
    (D : Derivation F R R) {ι : Type} (s : Finset ι) (f : ι → R) (h : ∀ i ∈ s, D (f i) = 0) :
    D (∏ i ∈ s, f i) = 0 :=
  Finset.prod_induction f (fun y => D y = 0)
    (fun a b ha hb => by rw [Derivation.leibniz, ha, hb, smul_zero, smul_zero, add_zero])
    (Derivation.map_one_eq_zero D) h

theorem logDet_local_eq_unit_mul_prod :
    ∀ (F A R : Type) [Field F] [CommRing A] [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsRegularLocalRing R] [IsNoetherianRing A] [Algebra F A] [Algebra A R] [Algebra F R] [IsScalarTower F A R] [Algebra.FiniteType F A] (P : Ideal A) [P.IsPrime] [IsLocalization.AtPrime R P] (n m : ℕ) (x : Fin n → A) (e : Fin m ↪ Fin n) (J : Finset (Fin m)), ReciprocityTheory.AnForm.R.FinalTheorems.Rsp R m (fun j => algebraMap A R (x (e j))) → (∃ bs : Module.Basis (Fin n) R Ω[R⁄F], ∀ i, bs i = KaehlerDifferential.D F R (algebraMap A R (x i))) → ∀ (I : Ideal A), I.map (algebraMap A R) = Ideal.span {algebraMap A R (∏ j ∈ J, x (e j))} → ∀ (b : Fin n → Derivation ℤ A A), (∀ j c, b j (algebraMap F A c) = 0) → (∀ j, ∀ f ∈ I, b j f ∈ I) → (∀ D : Derivation ℤ A A, (∀ c, D (algebraMap F A c) = 0) → (∀ f ∈ I, D f ∈ I) → ∃ c : Fin n → A, D = ∑ j, c j • b j) → ∃ u : Rˣ, algebraMap A R (GlobalTheory.LogPole.logDet b x) = u * algebraMap A R (∏ j ∈ J, x (e j)) := by
  intro F A R _ _ _ _ _ _ _ _ _ _ _ _ P _ _ n m x e J hrsp hbs I hI b _hbF hbI hspan
  obtain ⟨bs, hbs⟩ := hbs
  set φ := algebraMap A R with hφ
  set r : Fin m → R := fun j => φ (x (e j)) with hr
  set g : R := ∏ j ∈ J, r j with hg
  have hφg : φ (∏ j ∈ J, x (e j)) = g := by rw [map_prod]
  have hIg : I.map φ = Ideal.span {g} := by rw [hI, hφg]

  let dd : Fin n → Derivation F R R := fun i => (bs.coord i).compDer (KaehlerDifferential.D F R)
  have hδ : ∀ i l, dd i (φ (x l)) = if l = i then 1 else 0 := by
    intro i l
    show bs.coord i (KaehlerDifferential.D F R (φ (x l))) = _
    rw [← hbs l, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  let hm : Fin n → R := fun l => if l ∈ J.map e then φ (x l) else 1
  let E : Fin n → Derivation F R R := fun i => hm i • dd i
  have hEapp : ∀ i y, E i y = hm i * dd i y := fun i y => rfl

  have hEg : ∀ i, E i g ∈ Ideal.span {g} := by
    intro i
    rw [hEapp]
    by_cases hi : i ∈ J.map e
    · obtain ⟨j0, hj0, rfl⟩ := Finset.mem_map.mp hi
      have hsplit : g = r j0 * ∏ j ∈ J.erase j0, r j := (Finset.mul_prod_erase J r hj0).symm
      have hrest : dd (e j0) (∏ j ∈ J.erase j0, r j) = 0 := by
        refine derivation_prod_eq_zero_of_forall _ _ _ fun j hj => ?_
        have hne : e j ≠ e j0 := fun h => (Finset.ne_of_mem_erase hj) (e.injective h)
        show dd (e j0) (φ (x (e j))) = 0
        rw [hδ, if_neg hne]
      have hone : dd (e j0) (r j0) = 1 := by
        show dd (e j0) (φ (x (e j0))) = 1
        rw [hδ, if_pos rfl]
      have hmv : hm (e j0) = r j0 := if_pos hi
      have : hm (e j0) * dd (e j0) g = g := by
        conv_lhs => rw [hsplit]
        rw [Derivation.leibniz, hrest, hone, hmv, smul_zero, zero_add, smul_eq_mul, mul_one, ← hsplit]
      rw [this]
      exact Ideal.mem_span_singleton_self g
    · have : dd i g = 0 := by
        refine derivation_prod_eq_zero_of_forall _ _ _ fun j hj => ?_
        have hne : e j ≠ i := fun h => hi (Finset.mem_map.mpr ⟨j, hj, h⟩)
        show dd i (φ (x (e j))) = 0
        rw [hδ, if_neg hne]
      rw [this, mul_zero]
      exact Ideal.zero_mem _
  have hE : ∀ i, ∀ f ∈ I.map φ, E i f ∈ I.map φ := by
    intro i f hf
    rw [hIg] at hf ⊢
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hf
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (hEg i))
      (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self g))
  choose N hN using fun i => GlobalTheory.T.logarithmicDerivation_localizationAtPrime_span_of_ring F A R P I n b hspan (E i) (hE i)

  choose D' hD' using fun k =>
    GlobalTheory.T.exists_derivation_extend_localization_atPrime ℤ A R P ((Algebra.linearMap A R).compDer (b k))
  have hD'a : ∀ k a, D' k (φ a) = φ (b k a) := fun k a => hD' k a
  have hD'I : ∀ k, ∀ f ∈ I.map φ, D' k f ∈ I.map φ := by
    intro k f hf
    induction hf using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ha, rfl⟩ := hy
      rw [hD'a]
      exact Ideal.mem_map_of_mem _ (hbI k a ha)
    | zero => rw [map_zero]; exact Ideal.zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact Ideal.add_mem _ hy hz
    | smul c y hy hy' =>
      rw [smul_eq_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hy') (Ideal.mul_mem_right _ _ hy)
  have hdiv : ∀ l k, ∃ c, φ (b k (x l)) = hm l * c := by
    intro l k
    by_cases hl : l ∈ J.map e
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hl
      have hgk : D' k g ∈ Ideal.span {g} := by
        rw [← hIg]; exact hD'I k g (by rw [hIg]; exact Ideal.mem_span_singleton_self g)
      have := GlobalTheory.T.dvd_derivation_of_mem_span_prod_params' R m r hrsp J (D' k) hgk j hj
      obtain ⟨c, hc⟩ := this
      refine ⟨c, ?_⟩
      have hmv : hm (e j) = r j := if_pos hl
      rw [hmv, ← hc]
      exact (hD'a k (x (e j))).symm
    · refine ⟨φ (b k (x l)), ?_⟩
      have hmv : hm l = 1 := if_neg hl
      rw [hmv, one_mul]
  choose M hM using hdiv

  let Bm : Matrix (Fin n) (Fin n) R := Matrix.of fun l k => φ (b k (x l))
  have hBdet : φ (logDet b x) = Bm.det := by
    rw [logDet, RingHom.map_det]
    congr 1
  have h1 : Bm = Matrix.diagonal hm * Matrix.of M := by
    ext l k
    simp [Bm, Matrix.diagonal_mul, hM]
  have h2 : Matrix.diagonal hm = Bm * (Matrix.of N).transpose := by
    ext l i
    rw [Matrix.mul_apply]
    have hsum : ∑ k, Bm l k * (Matrix.of N).transpose k i = ∑ k, N i k * φ (b k (x l)) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [Bm, mul_comm]
    rw [hsum, ← hN i (x l), hEapp, hδ, Matrix.diagonal_apply]
    by_cases hli : l = i
    · subst hli; simp
    · simp [hli]
  have hdetD : (Matrix.diagonal hm).det = g := by
    rw [Matrix.det_diagonal]
    have : ∏ l, hm l = ∏ l ∈ J.map e, φ (x l) := by
      rw [← Finset.prod_filter]
      congr 1
      ext l; simp
    rw [this, Finset.prod_map]
  haveI : IsDomain R := ReciprocityTheory.AnForm.R.isDomain_of_isRegularLocalRing
  have hprime : ∀ j, Prime (r j) := ReciprocityTheory.AnForm.R.prime_of_regular_params r hrsp.1 hrsp.2
  have hg0 : g ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => (hprime j).ne_zero
  have hMN : (Matrix.of M).det * (Matrix.of N).transpose.det = 1 := by
    have h3 : Matrix.diagonal hm = Matrix.diagonal hm * (Matrix.of M * (Matrix.of N).transpose) := by
      conv_lhs => rw [h2, h1]
      rw [Matrix.mul_assoc]
    have h4 := congrArg Matrix.det h3
    rw [Matrix.det_mul, Matrix.det_mul, hdetD] at h4
    exact (mul_left_cancel₀ hg0 (h4.symm.trans (mul_one g).symm))
  refine ⟨Units.mkOfMulEqOne _ _ hMN, ?_⟩
  rw [Units.val_mkOfMulEqOne, hφg, hBdet, h1, Matrix.det_mul, hdetD, mul_comm]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogKappaLengthBoundsStatement
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_kappa_length_bounds : Size → Covers fun Fm x _ ι p i Y PP _ => Real.log (kap p i) ≤ 2 * (Fm.L x ι).sc.L ∧ (lenT p i PP : ℝ) * PP ≤ Real.sqrt (Fm.L x ι).sc.b := by
  first | exact @GlobalTheory.CovTop.CovSz.kapT | exact GlobalTheory.CovTop.CovSz.kapT | (intros; apply GlobalTheory.CovTop.CovSz.kapT <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAbelianLocusOfMemRangeSiegelModuliChartStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_abelianLocus_of_mem_range_siegelModuli_chart : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (S : Scheme.{0}) (j : F.X ⟶ S) [IsOpenImmersion j] (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] (ξ : Sp R ⟶ S) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing R) ⟶ F.X) (A₁ : Over (Sp (FractionRing R))) [GrpObj A₁] (i₁ : A₁.left ⟶ G₁.left) (β : A₁.left ⟶ F.univ.A.left), IsSemiAbelian G₁ → IsGrpPullback A₁ G₁ (jK R) i₁ → IsGrpPullback A₁ F.univ.A y β → y ≫ j = jK R ≫ ξ → ∀ p : Sp R, ξ p ∈ Set.range j → p ∈ abLocus G₁ := by
  first | exact @GlobalTheory.ChartAbelian.mem_abLocus_of_mem_range | exact GlobalTheory.ChartAbelian.mem_abLocus_of_mem_range | (intros; apply GlobalTheory.ChartAbelian.mem_abLocus_of_mem_range <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SizeBoundStatementStatement
section
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.size_bound_statement : Size := by
  first | exact @GlobalTheory.CovTop.SizeRows.size | exact GlobalTheory.CovTop.SizeRows.size | (intros; apply GlobalTheory.CovTop.SizeRows.size <;> assumption)
end

