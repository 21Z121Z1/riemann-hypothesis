import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsAffineOpenPreimageEqOfIsNilpotent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0439
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2364
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleRigidTranslateLineBundleRationalPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0037
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2317
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0485

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareZeroAugmentedAlgebra
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Obs.TrivAug

variable {R R₀ : Type} [CommRing R] [CommRing R₀]

theorem mul_eq_of_map_eq {I : Ideal R} (hI : I ^ 2 = 0) {π : R →+* R₀} (hk : RingHom.ker π = I)
    {a b : R} (h : π a = π b) (i : I) : a * (i : R) = b * i := by
  have h1 : a - b ∈ I := hk ▸ (RingHom.mem_ker.2 (by rw [map_sub, h, sub_self]))
  have h2 : (a - b) * (i : R) ∈ I ^ 2 := by
    rw [pow_two]; exact Ideal.mul_mem_mul h1 i.2
  rw [hI, Ideal.zero_eq_bot, Ideal.mem_bot, sub_mul, sub_eq_zero] at h2
  exact h2

def smulI (I : Ideal R) {π : R →+* R₀} (hπ : Function.Surjective π) : SMul R₀ I :=
  ⟨fun r i => ⟨Function.surjInv hπ r * i, I.mul_mem_left _ i.2⟩⟩

def modI {I : Ideal R} (hI : I ^ 2 = 0) {π : R →+* R₀} (hπ : Function.Surjective π)
    (hk : RingHom.ker π = I) : Module R₀ I :=
  @Function.Surjective.moduleLeft R R₀ I _ _ _ _ (smulI I hπ) π hπ (fun c x => by
    apply Subtype.ext
    show Function.surjInv hπ (π c) * (x : R) = c * x
    exact mul_eq_of_map_eq hI hk (Function.surjInv_eq hπ (π c)) x)

def modOpI {I : Ideal R} (hI : I ^ 2 = 0) {π : R →+* R₀} (hπ : Function.Surjective π)
    (hk : RingHom.ker π = I) : Module R₀ᵐᵒᵖ I :=
  letI := modI hI hπ hk
  Module.compHom I (RingEquiv.toOpposite R₀).symm.toRingHom

end GlobalTheory.Obs.TrivAug
end

open GlobalTheory.Obs.TrivAug in
theorem GlobalTheory.Obs.exists_aug : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I), ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra R₀ R₁), Nonempty (Aug I π R₁) := by
  intro R R₀ _ _ I hI π hπ hk
  letI : Module R₀ I := modI hI hπ hk
  letI : Module R₀ᵐᵒᵖ I := modOpI hI hπ hk
  haveI : IsCentralScalar R₀ I := ⟨fun r m => by
    apply Subtype.ext
    show Function.surjInv hπ (MulOpposite.unop (MulOpposite.op r)) * (m : R) = Function.surjInv hπ r * m
    rfl⟩
  haveI : IsScalarTower R₀ R₀ᵐᵒᵖ I := ⟨fun r s m => by
    apply Subtype.ext
    show Function.surjInv hπ (MulOpposite.unop (r • s)) * (m : R) = Function.surjInv hπ r * (Function.surjInv hπ (MulOpposite.unop s) * m)
    rw [← _root_.mul_assoc]
    refine mul_eq_of_map_eq hI hk ?_ m
    simp [Function.surjInv_eq hπ, smul_eq_mul, mul_comm]⟩
  refine ⟨TrivSqZeroExt R₀ I, inferInstance, inferInstance, ⟨?_⟩⟩
  exact
  { q := TrivSqZeroExt.fstHom R₀ R₀ I
    k := { toFun := fun y => (y.snd : R), map_zero' := rfl, map_add' := fun _ _ => rfl }
    mem := fun y => y.snd.2
    smul := fun r y => by
      show Function.surjInv hπ (π r) * (y.snd : R) = r * y.snd
      exact mul_eq_of_map_eq hI hk (Function.surjInv_eq hπ (π r)) _
    one := rfl
    sq := fun y y' h h' => by
      have h0 : y.fst = 0 := h
      have h0' : y'.fst = 0 := h'
      ext
      · simp [h0]
      · simp [h0, h0']
    inj := fun y h h' => by
      have h0 : y.fst = 0 := h
      ext
      · exact h0
      · have h1 : (y.snd : R) = 0 := h'
        rw [h1]; rfl
    surj := fun i hi => ⟨TrivSqZeroExt.inr ⟨i, hi⟩, rfl, rfl⟩ }
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareZeroSmoothLiftSystemPresents
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftSys.OfLift

theorem sec_smooth {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) [Smooth s] (U : X.affineOpens) :
    Algebra.Smooth R (Sec s U.1) := by
  have h := HasRingHomProperty.appLE @Smooth s ‹_› ⟨⊤, isAffineOpen_top _⟩ U le_top
  have h' : RingHom.Smooth ((s.appLE ⊤ U.1 le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) :=
    RingHom.Smooth.comp (RingHom.Smooth.of_bijective
      (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.bijective) h
  exact RingHom.smooth_algebraMap.mp h'

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀}
  {X₀ X : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀} {s : X ⟶ Sp R} {i : X₀ ⟶ X}

theorem surjective_spMap (hI : I ^ 2 = 0) (hk : RingHom.ker π = I) (hπ : Function.Surjective π) :
    Surjective (spMap π) := by
  constructor
  intro x
  have hx : (show PrimeSpectrum R from x) ∈ Set.range (PrimeSpectrum.comap π) := by
    refine (range_comap_of_surjective R₀ π hπ).ge ?_
    rw [hk]
    intro a ha
    have h2 : a ^ 2 = 0 := by
      have := Ideal.pow_mem_pow ha 2
      rwa [hI, Ideal.zero_eq_bot, Ideal.mem_bot] at this
    exact (show PrimeSpectrum R from x).2.mem_of_pow_mem 2 (by rw [h2]; exact zero_mem _)
  obtain ⟨y, hy⟩ := hx
  exact ⟨y, hy⟩

variable (hpb : IsPullback i s₀ s (spMap π)) (hπ : Function.Surjective π) (hn : IsNilpotent (RingHom.ker π))

def liftOpen (U : X₀.affineOpens) : X.affineOpens :=
  ⟨(GlobalTheory.AffineThickening.exists_isAffineOpen_preimage_eq_of_isNilpotent R R₀ π hπ hn X X₀ s s₀ i hpb U.1 U.2).choose,
    (GlobalTheory.AffineThickening.exists_isAffineOpen_preimage_eq_of_isNilpotent R R₀ π hπ hn X X₀ s s₀ i hpb U.1 U.2).choose_spec.1⟩

theorem preimage_liftOpen (U : X₀.affineOpens) : i ⁻¹ᵁ (liftOpen hpb hπ hn U).1 = U.1 :=
  (GlobalTheory.AffineThickening.exists_isAffineOpen_preimage_eq_of_isNilpotent R R₀ π hπ hn X X₀ s s₀ i hpb U.1 U.2).choose_spec.2

theorem liftOpen_mono (hi : Function.Surjective i.base) {U V : X₀.affineOpens} (h : V ≤ U) :
    liftOpen hpb hπ hn V ≤ liftOpen hpb hπ hn U := by
  intro x hx
  obtain ⟨y, rfl⟩ := hi x
  have hy : y ∈ i ⁻¹ᵁ (liftOpen hpb hπ hn V).1 := hx
  rw [preimage_liftOpen] at hy
  have hy' : y ∈ i ⁻¹ᵁ (liftOpen hpb hπ hn U).1 := by
    rw [preimage_liftOpen]; exact h hy
  exact hy'

def pr (U : X₀.affineOpens) : GlobalTheory.CechDR.Pair i := ⟨(U, liftOpen hpb hπ hn U), (preimage_liftOpen hpb hπ hn U).ge⟩

end GlobalTheory.LiftSys.OfLift

open GlobalTheory.LiftSys.OfLift in

theorem GlobalTheory.LiftSys.exists_sys_presents : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), ∀ (X : Scheme.{0}) (s : X ⟶ Sp R) (i : X₀ ⟶ X), IsPullback i s₀ s (spMap π) → Smooth s → ∃ S : Sys I π s₀, Nonempty (S.Presents s i) := by
  intro R R₀ _ _ I hI π hπ hk X₀ s₀ X s i hpb hsm
  have hn : IsNilpotent (RingHom.ker π) := ⟨2, hk ▸ hI⟩
  haveI := surjective_spMap hI hk hπ
  have hi : Function.Surjective i.base :=
    (MorphismProperty.of_isPullback (P := @Surjective) hpb.flip ‹_›).surj
  let G : AffOp X₀ ⥤ AffOp X :=
    (Monotone.functor (f := liftOpen hpb hπ hn) fun _ _ h ↦ liftOpen_mono hpb hπ hn hi h).op
  let S : Sys I π s₀ :=
    { F := G ⋙ OAff s
      p := fun U ↦ GlobalTheory.CechDR.secPull s s₀ (pr hpb hπ hn U.unop)
      semi := fun U ↦ GlobalTheory.CechDR.semiHom_secPull hpb.w _
      nat := fun {U V} a b ↦ (congrArg (fun t ↦ t.hom b) (i.map_appLE (pr hpb hπ hn V.unop).2
          (homOfLE (liftOpen_mono hpb hπ hn hi (leOfHom a.unop))).op)).trans
        (congrArg (fun t ↦ t.hom b) (i.appLE_map (pr hpb hπ hn U.unop).2 (homOfLE (show V.unop.1 ≤ U.unop.1 from leOfHom a.unop)).op)).symm
      surj := fun U ↦ (GlobalTheory.CechDR.secPull_surjective_and_ker R R₀ I π hπ hk X₀ X s₀ s i hpb (pr hpb hπ hn U.unop) (preimage_liftOpen hpb hπ hn U.unop)).1
      ker := fun U b ↦ (GlobalTheory.CechDR.secPull_surjective_and_ker R R₀ I π hπ hk X₀ X s₀ s i hpb (pr hpb hπ hn U.unop) (preimage_liftOpen hpb hπ hn U.unop)).2 b
      smooth := fun U ↦ sec_smooth s _ }
  exact ⟨S, ⟨⟨fun U ↦ affPt s (liftOpen hpb hπ hn U.unop), fun U ↦ (liftOpen hpb hπ hn U.unop).2.isOpenImmersion_fromSpec, fun U ↦ affPt_w s _,
    fun U V a ↦ affPt_res s _, fun U ↦ GlobalTheory.CechDR.secPull_affPt s s₀ (pr hpb hπ hn U.unop),
    S.cover_of_surjective ⟨hi⟩ _ fun U ↦ GlobalTheory.CechDR.secPull_affPt s s₀ (pr hpb hπ hn U.unop)⟩⟩⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSubOneMemMulKerNakayamaFlat
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Pinch

theorem mem_map_mul_ker_of_flat {R' A C' : Type} [CommRing R'] [CommRing A] [CommRing C']
    [Algebra R' A] [Algebra R' C'] [Module.Flat R' C'] (f : A →ₐ[R'] C')
    (hf : Function.Surjective f) (J : Ideal R') {x : A}
    (hx : x ∈ J.map (algebraMap R' A)) (hfx : f x = 0) :
    x ∈ J.map (algebraMap R' A) * RingHom.ker f := by
  rw [Ideal.map, Ideal.span, Submodule.mem_span_set'] at hx
  obtain ⟨n, c, g, rfl⟩ := hx
  have hg : ∀ i, ∃ j ∈ J, algebraMap R' A j = (g i : A) := fun i => (g i).2
  choose j hjJ hjg using hg
  have hsum : ∑ i, j i • f (c i) = 0 := by
    rw [← hfx, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, ← hjg i, map_mul, AlgHom.commutes, Algebra.smul_def, _root_.mul_comm]
  obtain ⟨k, a, y, hy, ha⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := R') (M := C') (f := j)
    (x := fun i => f (c i)) hsum
  choose z hz using fun l => hf (y l)
  have hd : ∀ i, c i - ∑ l, a i l • z l ∈ RingHom.ker f := by
    intro i
    rw [RingHom.mem_ker]
    change f (c i - ∑ l, a i l • z l) = 0
    rw [map_sub, map_sum]
    simp only [map_smul, hz]
    rw [← hy i, sub_self]
  have h0 : ∑ i, algebraMap R' A (j i) * ∑ l, a i l • z l = 0 := by
    have hl : ∀ l, ∑ i, algebraMap R' A (j i) * (a i l • z l) = 0 := by
      intro l
      have : ∑ i, algebraMap R' A (j i) * (a i l • z l) = (∑ i, j i * a i l) • z l := by
        rw [Finset.sum_smul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, _root_.mul_assoc]
      rw [this, ha l, zero_smul]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun l _ => hl l
  have key : ∑ i, c i • (g i : A) =
      ∑ i, algebraMap R' A (j i) * (c i - ∑ l, a i l • z l) := by
    simp only [mul_sub, Finset.sum_sub_distrib, h0, sub_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, ← hjg i, _root_.mul_comm]
  rw [key]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ (hjJ i)) (hd i)

theorem exists_sub_one_mem_mul_ker_le :
    ∀ (R' A C' : Type) [CommRing R'] [CommRing A] [CommRing C'] [Algebra R' A] [Algebra R' C']
      [IsNoetherianRing A] [Module.Flat R' C'] (f : A →ₐ[R'] C'), Function.Surjective f →
      ∀ (I : Ideal A) (J : Ideal R'), I ≤ RingHom.ker f →
        RingHom.ker f ≤ I ⊔ J.map (algebraMap R' A) →
          ∃ s : A, s - 1 ∈ J.map (algebraMap R' A) ∧ ∀ G ∈ RingHom.ker f, s * G ∈ I := by
  intro R' A C' _ _ _ _ _ _ _ f hf I J hI hK
  have hle : RingHom.ker f ≤ I ⊔ (J.map (algebraMap R' A)) • RingHom.ker f := by
    intro G hG
    obtain ⟨i, hi, x, hx, rfl⟩ := Submodule.mem_sup.1 (hK hG)
    have hfx : f x = 0 := by
      have h1 : f (i + x) = 0 := hG
      have h2 : f i = 0 := hI hi
      rw [map_add, h2, zero_add] at h1
      exact h1
    exact Submodule.add_mem_sup hi (mem_map_mul_ker_of_flat f hf J hx hfx)
  obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup
    (IsNoetherian.noetherian (RingHom.ker f)) le_rfl hle
  refine ⟨r, hr1, fun G hG => ?_⟩
  exact hr (Submodule.smul_mem_pointwise_smul G r _ hG)

end GlobalTheory.Pinch
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSubmersivePresentationAddZeroVariables
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PinchEnl

open MvPolynomial

theorem ker_aeval_zero_eq_span (D κ : Type) [CommRing D] :
    RingHom.ker (aeval (R := D) (fun _ : κ ↦ (0 : D))) = Ideal.span (Set.range X) := by
  apply le_antisymm
  · intro p hp
    rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
    intro m hm
    by_contra h
    push_neg at h
    have hm0 : m = 0 := by ext i; simpa using h i (Set.mem_univ i)
    subst hm0
    rw [RingHom.mem_ker] at hp
    have : aeval (R := D) (fun _ : κ ↦ (0 : D)) p = coeff 0 p := by
      first
        | (show MvPolynomial.eval (0 : κ → D) p = _
           exact congrFun (congrArg DFunLike.coe (MvPolynomial.eval_zero (R := D) (σ := κ))) p)
        | (rw [MvPolynomial.aeval_def]; simp [MvPolynomial.eval₂_eq, MvPolynomial.coeff_zero_eq_constantCoeff])
    exact (mem_support_iff.mp hm) (this ▸ hp)
  · rw [Ideal.span_le]
    rintro _ ⟨k, rfl⟩
    simp

noncomputable def zeroPre (D κ : Type) [CommRing D] :
    Algebra.PreSubmersivePresentation D D κ κ where
  val _ := 0
  σ' x := C x
  aeval_val_σ' x := by simp
  relation k := X k
  span_range_relation_eq_ker := by
    rw [Algebra.Generators.ker_eq_ker_aeval_val]
    exact (ker_aeval_zero_eq_span D κ).symm
  map := id
  map_inj := Function.injective_id

theorem zeroPre_jacobian (D κ : Type) [CommRing D] [Finite κ] : (zeroPre D κ).jacobian = 1 := by
  classical
  have : Fintype κ := Fintype.ofFinite κ
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
  have h1 : (zeroPre D κ).jacobiMatrix = 1 := by
    ext i j
    rw [Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
    simp [zeroPre, Matrix.one_apply, pderiv_X, Pi.single_apply, eq_comm]
  rw [h1]
  simp

end GlobalTheory.PinchEnl

theorem GlobalTheory.PinchEnl.exists_submersivePresentation_sum_zero : ∀ (R D ν σ κ : Type) [CommRing R] [CommRing D] [Algebra R D] [Finite ν] [Finite σ] [Finite κ] (P : Algebra.SubmersivePresentation R D ν σ), ∃ P' : Algebra.SubmersivePresentation R D (κ ⊕ ν) (κ ⊕ σ), P'.val = Sum.elim (fun _ ↦ 0) P.val := by
  intro R D ν σ κ _ _ _ _ _ _ P
  let Q : Algebra.SubmersivePresentation D D κ κ :=
    { __ := GlobalTheory.PinchEnl.zeroPre D κ
      jacobian_isUnit := by rw [GlobalTheory.PinchEnl.zeroPre_jacobian]; exact isUnit_one }
  refine ⟨Q.comp P, ?_⟩
  ext i
  rcases i with k | j
  · rfl
  · rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymmetricRigidifiedTranslateAmpleKTrivial
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SymTranslate

open GlobalTheory.CechPic (cls)

theorem exists_sym_translate : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (M : LB B.left) (b : 𝟙_ _ ⟶ B), IsAbelianScheme B → M.IsLB → RelAmple B M → KTriv B M → (∃ t : LB.Gen (Theta B M), t.IsGen) → LBIso (M.pull (ι[B]).left) (M.pull ((toUnit B ≫ b ^ 2) * 𝟙 B).left) → ∃ L : LB B.left, L.IsLB ∧ Rigidified B L ∧ Out.Sym B L ∧ RelAmple B L ∧ KTriv B L ∧ LBIso (abelian₂ B L) (abelian₂ B M) := by
  intro A _ _ _ B _ _ M b hB hM hamp hK hT hiso
  have := hB.proper
  obtain ⟨c, hc⟩ := hT
  have hL' : (GlobalTheory.RigidTranslate.rigTransl M b).IsLB := LB.isLB_linComb hM _ _
  refine ⟨GlobalTheory.RigidTranslate.rigTransl M b, hL', GlobalTheory.RigidTranslate.rigidified_rigTransl hM, ?_,
    GlobalTheory.RigidTranslate.relAmple_rigTransl_of_section b hM hamp, GlobalTheory.RigidTranslate.kTriv_rigTransl_any _ B M hM b hK, ?_⟩
  · have h2 : CechPic.pull (GrpObj.inv : B ⟶ B).left (cls M hM) =
        CechPic.pull ((toUnit B ≫ b ^ 2) * 𝟙 B).left (cls M hM) :=
      (CechPic.cls_eq_iff (pull_isLB hM _) (pull_isLB hM _)).2 hiso
    have h3 := congrArg (CechPic.pull (𝟙 B * (toUnit B ≫ b)⁻¹).left) h2
    rw [← CechPic.pull_comp, ← CechPic.pull_comp, ← Over.comp_left, ← Over.comp_left] at h3
    have e1 : (𝟙 B * (toUnit B ≫ b)⁻¹) ≫ (GrpObj.inv : B ⟶ B) =
        (GrpObj.inv : B ⟶ B) ≫ (𝟙 B * (toUnit B ≫ b)) := by
      rw [← Hom.inv_def, MonObj.comp_mul, ← Category.assoc, comp_toUnit, Category.comp_id, mul_inv, inv_inv,
        Hom.inv_def, Category.id_comp]
    have e2 : (𝟙 B * (toUnit B ≫ b)⁻¹) ≫ ((toUnit B ≫ b ^ 2) * 𝟙 B) = 𝟙 B * (toUnit B ≫ b) := by
      rw [MonObj.comp_mul, ← Category.assoc, comp_toUnit, Category.comp_id, MonObj.comp_pow, sq,
        _root_.mul_comm (𝟙 B), _root_.mul_comm (𝟙 B), _root_.mul_assoc, mul_inv_cancel_left]
    rw [e1, e2, Over.comp_left, CechPic.pull_comp] at h3
    have e3 : (GrpObj.inv : B ⟶ B).left ≫ (toUnit B ≫ b).left = (toUnit B ≫ b).left := by
      rw [← Over.comp_left, ← Category.assoc, comp_toUnit]
    have h4 : cls _ hL' = CechPic.pull (𝟙 B * (toUnit B ≫ b)).left (cls M hM) -
        CechPic.pull (toUnit B ≫ b).left (cls M hM) := by
      rw [CechPic.cls_linComb hM, Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul, ← sub_eq_add_neg]
      rfl
    refine GlobalTheory.RigSymSubring.sym_of_cls hL' ?_
    rw [h4, map_sub, h3, ← CechPic.pull_comp, e3]
  · have hΛ : (abelian₂ B M).IsLB := LB.isLB_linComb hM _ _
    refine (CechPic.cls_eq_iff (LB.isLB_linComb hL' _ _) hΛ).1
      (((CechPic.cls_eq_iff (LB.isLB_linComb hL' _ _) (pull_isLB hΛ _)).2
        (GlobalTheory.RigidTranslate.lam_rigTransl hM c hc)).trans ?_)
    rw [CechPic.cls_pull hΛ]
    exact CechPic.pull_id _

end GlobalTheory.SymTranslate
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorSquareEquivFibreSquareSections
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LBDescent
open TensorProduct

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LBDescent

theorem exists_tensorSquare_equiv_sections {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] (V₀ : Y.Opens)
    (hV₀ : IsAffineOpen V₀)
    (h : pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀ ≤ pullback.snd f f ⁻¹ᵁ f ⁻¹ᵁ V₀) :
    letI : Algebra Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀) := (f.app V₀).hom.toAlgebra
    ∃ e : Γ(X, f ⁻¹ᵁ V₀) ⊗[Γ(Y, V₀)] Γ(X, f ⁻¹ᵁ V₀) ≃+* Γ(pullback f f, pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀),
      ∀ a b : Γ(X, f ⁻¹ᵁ V₀), e (a ⊗ₜ b) =
        ((pullback.fst f f).app (f ⁻¹ᵁ V₀)).hom a * ((pullback.snd f f).appLE (f ⁻¹ᵁ V₀) _ h).hom b := by
  letI : Algebra Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀) := (f.app V₀).hom.toAlgebra
  have hV' : IsAffineOpen (f ⁻¹ᵁ V₀) := hV₀.preimage f
  have P := ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.isPushout_appLE (IsPullback.of_hasPullback f f).flip
    inferInstance hV₀ hV' le_rfl h
  rw [Scheme.Hom.appLE_eq_app] at P
  have T := CommRingCat.isPushout_tensorProduct Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀) Γ(X, f ⁻¹ᵁ V₀)
  let I := IsPushout.isoIsPushout _ _ T P.flip
  refine ⟨I.commRingCatIsoToRingEquiv, fun a b => ?_⟩
  have h1 : I.hom.hom (a ⊗ₜ 1) = ((pullback.fst f f).app (f ⁻¹ᵁ V₀)).hom a :=
    congrArg (fun t => t.hom a) (IsPushout.inl_isoIsPushout_hom _ _ T P.flip)
  have h2 : I.hom.hom (1 ⊗ₜ b) = ((pullback.snd f f).appLE (f ⁻¹ᵁ V₀) _ h).hom b :=
    congrArg (fun t => t.hom b) (IsPushout.inr_isoIsPushout_hom _ _ T P.flip)
  have hab : (a ⊗ₜ[Γ(Y, V₀)] b : Γ(X, f ⁻¹ᵁ V₀) ⊗[Γ(Y, V₀)] Γ(X, f ⁻¹ᵁ V₀)) = (a ⊗ₜ 1) * (1 ⊗ₜ b) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, _root_.one_mul]
  change I.hom.hom (a ⊗ₜ b) = _
  rw [hab, map_mul, h1, h2]

end GlobalTheory.LBDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionBasisRealMultiplication
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionPoints

theorem exists_torsion_basis : ∀ (F : Type) [Field F] [NumberField F] (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A]
    (rm : OAct (𝓞 F) A) (L : LB A.left) (u : HolUnif A L (Module.finrank ℚ F))
    (Fa : 𝓞 F →+* Module.End ℂ (Fin (Module.finrank ℚ F) → ℂ)),
    (∀ (a : 𝓞 F) (z : Fin (Module.finrank ℚ F) → ℂ), u.ex (Fa a z) = u.ex z ≫ rm.act a) →
    ∀ N : ℕ, 1 ≤ N → ∃ pt : Fin 2 → (𝟙_ (Over (Sp ℂ)) ⟶ A), (∀ i, pt i ^ N = 1) ∧
      (∀ a b : 𝓞 F, (pt 0 ≫ rm.act a) * (pt 1 ≫ rm.act b) = 1 → (N : 𝓞 F) ∣ a ∧ (N : 𝓞 F) ∣ b) ∧
      ∀ y : 𝟙_ (Over (Sp ℂ)) ⟶ A, y ^ N = 1 → ∃ a b : 𝓞 F, y = (pt 0 ≫ rm.act a) * (pt 1 ≫ rm.act b) := by
  intro F _ _ A _ _ rm L u Fa hFa N hN
  have hst : ∀ (a : 𝓞 F) (l : Fin (Module.finrank ℚ F) → ℂ), l ∈ u.Λ → Fa a l ∈ u.Λ := by
    intro a l hl
    rw [← u.ker, hFa, (u.ker l).2 hl, Hom.one_def, Category.assoc, (rm.hom a).one_hom]
  letI : Module (𝓞 F) (Fin (Module.finrank ℚ F) → ℂ) := Module.compHom _ Fa
  have hsmul : ∀ (a : 𝓞 F) (v : Fin (Module.finrank ℚ F) → ℂ), a • v = Fa a v := fun _ _ => rfl
  let Λ' : Submodule (𝓞 F) (Fin (Module.finrank ℚ F) → ℂ) :=
    { carrier := u.Λ
      add_mem' := fun ha hb => u.Λ.add_mem ha hb
      zero_mem' := u.Λ.zero_mem
      smul_mem' := fun a l hl => hst a l hl }
  let e : u.Λ ≃+ Λ' :=
    { toFun := fun l => ⟨l.1, l.2⟩, invFun := fun l => ⟨l.1, l.2⟩, left_inv := fun _ => rfl,
      right_inv := fun _ => rfl, map_add' := fun _ _ => rfl }
  haveI := u.discrete
  haveI : IsZLattice ℝ u.Λ := ⟨u.full⟩
  haveI : Module.Finite ℤ u.Λ := ZLattice.module_finite ℝ u.Λ
  haveI : Module.Finite ℤ Λ' := Module.Finite.equiv e.toIntLinearEquiv
  haveI : IsAddTorsionFree Λ' := ⟨fun n hn a b h => by
    apply Subtype.ext
    have h' : n • (a : Fin (Module.finrank ℚ F) → ℂ) = n • (b : Fin (Module.finrank ℚ F) → ℂ) := by
      simpa using congrArg Subtype.val h
    rw [← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ n] at h'
    exact smul_right_injective _ (Nat.cast_ne_zero.2 hn) h'⟩
  have hrank : Module.finrank ℤ Λ' = 2 * Module.finrank ℚ F := by
    rw [← e.toIntLinearEquiv.finrank_eq, ZLattice.rank ℝ u.Λ]
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, mul_comm]
  obtain ⟨x, hgen, hfree⟩ := GlobalTheory.T.exists_rank_two_basis_mod_N F Λ' hrank N hN
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hpow : ∀ (z : Fin (Module.finrank ℚ F) → ℂ) (k : ℕ), u.ex (k • z) = u.ex z ^ k := by
    intro z k
    induction k with
    | zero => rw [zero_smul, pow_zero]; exact (u.ker 0).2 u.Λ.zero_mem
    | succ n ih => rw [succ_nsmul, u.ex_add, ih, pow_succ]
  have hcancel : ∀ v : Fin (Module.finrank ℚ F) → ℂ, N • ((N : ℂ)⁻¹ • v) = v := by
    intro v
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hN0, one_smul]
  have key : ∀ a b : 𝓞 F, (u.ex ((N : ℂ)⁻¹ • (x 0 : Fin (Module.finrank ℚ F) → ℂ)) ≫ rm.act a) *
      (u.ex ((N : ℂ)⁻¹ • (x 1 : Fin (Module.finrank ℚ F) → ℂ)) ≫ rm.act b) =
      u.ex ((N : ℂ)⁻¹ • ((a • x 0 + b • x 1 : Λ') : Fin (Module.finrank ℚ F) → ℂ)) := by
    intro a b
    rw [← hFa, ← hFa, ← u.ex_add, Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul, hsmul, hsmul,
      smul_add, map_smul, map_smul]
  refine ⟨fun i => u.ex ((N : ℂ)⁻¹ • (x i : Fin (Module.finrank ℚ F) → ℂ)), ?_, ?_, ?_⟩
  · intro i
    rw [← hpow, hcancel]
    exact (u.ker _).2 (x i).2
  · intro a b h
    rw [key] at h
    refine hfree a b ⟨⟨_, (u.ker _).1 h⟩, Subtype.ext ?_⟩
    exact (hcancel _).symm
  · intro y hy
    obtain ⟨z, rfl⟩ := u.ex_onto y
    have hz : N • z ∈ u.Λ := (u.ker _).1 (by rw [hpow]; exact hy)
    obtain ⟨a, b, m', hm⟩ := hgen ⟨N • z, hz⟩
    refine ⟨a, b, ?_⟩
    rw [key]
    have hm' : N • z = ((a • x 0 + b • x 1 : Λ') : Fin (Module.finrank ℚ F) → ℂ) + N • (m' : Fin (Module.finrank ℚ F) → ℂ) := by
      simpa using congrArg Subtype.val hm
    have hz' : z = (N : ℂ)⁻¹ • ((a • x 0 + b • x 1 : Λ') : Fin (Module.finrank ℚ F) → ℂ) + (m' : Fin (Module.finrank ℚ F) → ℂ) := by
      have h1 : z = (N : ℂ)⁻¹ • (N • z) := by
        rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hN0, one_smul]
      rw [h1, hm', smul_add, ← Nat.cast_smul_eq_nsmul ℂ N (m' : Fin (Module.finrank ℚ F) → ℂ), smul_smul,
        inv_mul_cancel₀ hN0, one_smul]
    conv_lhs => rw [hz']
    rw [u.ex_add, (u.ker _).2 m'.2, _root_.mul_one]

end GlobalTheory.TorsionPoints
end

