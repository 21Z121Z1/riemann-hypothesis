import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2530
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2496
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2447
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2497
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0058
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0183
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2452
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2370
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueBaseChangeEqOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2418

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueSectionOfNaturalPointwiseFunction
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt.NatSec

theorem nat_of_comp (R : Type) [CommRing R] (Y : Over (Sp R)) (U : Y.left.Opens) (t : Fn0 Y)
    (ht : ∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (ψ : E →ₐ[R] E')
      (z : Pt Y E), ⊤ ≤ z.left ⁻¹ᵁ U → t E' (spOver ψ ≫ z) = ψ (t E z))
    (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →+* D')
    (x : Pt Y D) (x' : Pt Y D') (hx : ⊤ ≤ x.left ⁻¹ᵁ U) (h : spMap φ ≫ x.left = x'.left) :
    t D' x' = φ (t D x) := by
  have h1 : x.left ≫ Y.hom = spMap (algebraMap R D) := Over.w x
  have h2 : x'.left ≫ Y.hom = spMap (algebraMap R D') := Over.w x'
  have h3 : CommRingCat.ofHom (algebraMap R D) ≫ CommRingCat.ofHom φ = CommRingCat.ofHom (algebraMap R D') := by
    apply Spec.map_injective
    rw [Spec.map_comp]
    change spMap φ ≫ spMap _ = spMap _
    rw [← h1, ← h2, ← h, Category.assoc]
  let ψ : D →ₐ[R] D' := ⟨φ, fun r ↦ congrArg (fun f ↦ CommRingCat.Hom.hom f r) h3⟩
  have h4 := ht D D' ψ x hx
  have h5 : spOver ψ ≫ x = x' := Over.OverMorphism.ext h
  rw [h5] at h4
  exact h4

theorem fromSpecStalk_top {X : Scheme.{0}} (x : X) (U : X.Opens) (hx : x ∈ U) :
    ⊤ ≤ X.fromSpecStalk x ⁻¹ᵁ U := by
  intro z _
  have hz : X.fromSpecStalk x z ⤳ x := by
    have : X.fromSpecStalk x z ∈ Set.range (X.fromSpecStalk x) := ⟨z, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  exact hz.mem_open U.2 hx

theorem fromSpecStalk_appLE {X : Scheme.{0}} (x : X) (U : X.Opens) (hx : x ∈ U) :
    (X.fromSpecStalk x).appLE U ⊤ (fromSpecStalk_top x U hx) =
      X.presheaf.germ U x hx ≫ (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv := by
  rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hx]
  simp only [Category.assoc, ← Functor.map_comp]
  have e : ((homOfLE le_top).op ≫ (homOfLE (fromSpecStalk_top x U hx)).op :
      Opposite.op (⊤ : (Spec (X.presheaf.stalk x)).Opens) ⟶ Opposite.op ⊤) = 𝟙 _ := rfl
  rw [e, CategoryTheory.Functor.map_id, Category.comp_id]

theorem ext_of_evU (R : Type) [CommRing R] (Y : Over (Sp R)) (U : Y.left.Opens) (a a' : Γ(Y.left, U))
    (h : ∀ (E : Type) [CommRing E] [Algebra R E] (z : Pt Y E), ⊤ ≤ z.left ⁻¹ᵁ U →
      evU z.left U a = evU z.left U a') : a = a' := by
  refine TopCat.Presheaf.section_ext Y.left.sheaf U a a' fun y hy ↦ ?_
  let S : CommRingCat.{0} := Y.left.presheaf.stalk y
  letI al : Algebra R S := (Spec.preimage (R := CommRingCat.of R) (Y.left.fromSpecStalk y ≫ Y.hom)).hom.toAlgebra
  let z : Pt Y S := Over.homMk (Y.left.fromSpecStalk y)
    (Spec.map_preimage (R := CommRingCat.of R) (Y.left.fromSpecStalk y ≫ Y.hom)).symm
  have hz : ⊤ ≤ z.left ⁻¹ᵁ U := fromSpecStalk_top y U hy
  have e := h S z hz
  unfold evU at e
  rw [dif_pos hz, dif_pos hz] at e
  unfold evalAt at e
  change (Scheme.ΓSpecIso S).hom ((Y.left.fromSpecStalk y).appLE U ⊤ hz a) =
    (Scheme.ΓSpecIso S).hom ((Y.left.fromSpecStalk y).appLE U ⊤ hz a') at e
  rw [fromSpecStalk_appLE y U hy] at e
  simp only [CommRingCat.comp_apply] at e
  change (Scheme.ΓSpecIso (Y.left.presheaf.stalk y)).hom _ = (Scheme.ΓSpecIso (Y.left.presheaf.stalk y)).hom _ at e
  simp only [Iso.inv_hom_id_apply] at e
  exact e

theorem exists_unique_section : ∀ (R : Type) [CommRing R] (Y : Over (Sp R)) (U : Y.left.Opens) (t : Fn0 Y), (∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (ψ : E →ₐ[R] E') (z : Pt Y E), ⊤ ≤ z.left ⁻¹ᵁ U → t E' (spOver ψ ≫ z) = ψ (t E z)) → ∃! a : Γ(Y.left, U), ∀ (E : Type) [CommRing E] [Algebra R E] (z : Pt Y E), ⊤ ≤ z.left ⁻¹ᵁ U → evU z.left U a = t E z := by
  intro R _ Y U t ht
  let Z : Scheme.{0} := U.toScheme
  let al : ∀ (D : CommRingCat.{0}) (x : Spec D ⟶ Z), Algebra R D := fun D x ↦
    (Spec.preimage (R := CommRingCat.of R) (x ≫ U.ι ≫ Y.hom)).hom.toAlgebra
  let pt : ∀ (D : CommRingCat.{0}) (x : Spec D ⟶ Z), @Pt R _ Y D _ (al D x) := fun D x ↦
    Over.homMk (x ≫ U.ι) (by rw [Category.assoc]; exact (Spec.map_preimage (R := CommRingCat.of R) (x ≫ U.ι ≫ Y.hom)).symm)
  have hin : ∀ (D : CommRingCat.{0}) (x : Spec D ⟶ Z), ⊤ ≤ (x ≫ U.ι) ⁻¹ᵁ U := by
    intro D x p _
    exact (x p).2
  let κ : ∀ D : CommRingCat.{0}, (Spec D ⟶ Z) → D := fun D x ↦ @t D _ (al D x) (pt D x)
  obtain ⟨s, hs⟩ := NatConst.exists_section Z (fun _ : Unit ↦ (⊤ : Z.Opens)) (by simp) κ
    fun D D' φ x _ ↦ @NatSec.nat_of_comp R _ Y U t ht D _ (al D x) D' _ (al D' (Spec.map φ ≫ x)) φ.hom
      (pt D x) (pt D' _) (hin D x) (by change Spec.map φ ≫ x ≫ U.ι = (Spec.map φ ≫ x) ≫ U.ι; rw [Category.assoc])
  have hex : ∀ (E : Type) [CommRing E] [Algebra R E] (z : Pt Y E), ⊤ ≤ z.left ⁻¹ᵁ U →
      evU z.left U (U.topIso.hom s) = t E z := by
    intro E _ inst z hz
    have hr : Set.range z.left ⊆ Set.range U.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨q, rfl⟩
      exact hz (Set.mem_univ q)
    let w : Spec (CommRingCat.of E) ⟶ Z := IsOpenImmersion.lift U.ι z.left hr
    have hw : w ≫ U.ι = z.left := IsOpenImmersion.lift_fac U.ι z.left hr
    have h1 : κ (CommRingCat.of E) w = t E z := by
      refine (@NatSec.nat_of_comp R _ Y U t ht E _ inst E _ (al (CommRingCat.of E) w) (RingHom.id E) z
        (pt (CommRingCat.of E) w) hz ?_)
      change Spec.map (CommRingCat.ofHom (RingHom.id E)) ≫ z.left = w ≫ U.ι
      rw [hw, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
    rw [← h1, hs (CommRingCat.of E) w ⟨(), le_top⟩]
    unfold evU
    rw [dif_pos hz]
    unfold evalAt
    simp only [RingHom.comp_apply]
    congr 1
    have key : ∀ (g : Spec (CommRingCat.of E) ⟶ Y.left) (_ : w ≫ U.ι = g) (h : ⊤ ≤ g ⁻¹ᵁ U),
        g.appLE U ⊤ h = U.ι.appLE U ⊤ (by simp) ≫ w.appLE ⊤ ⊤ le_top := by
      rintro _ rfl h
      exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
    rw [key _ hw hz, CommRingCat.comp_apply, Scheme.Opens.ι_appLE]
    have hid : ∀ (f : Opposite.op U ⟶ Opposite.op (U.ι ''ᵁ ⊤)) (g : Opposite.op (U.ι ''ᵁ ⊤) ⟶ Opposite.op U)
        (x : Γ(Y.left, U.ι ''ᵁ ⊤)), Y.left.presheaf.map f (Y.left.presheaf.map g x) = x := by
      intro f g x
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, Subsingleton.elim (g ≫ f) (𝟙 _),
        CategoryTheory.Functor.map_id]
      rfl
    rw [Scheme.Opens.topIso_hom]
    erw [hid]
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  refine ⟨U.topIso.hom s, hex, fun a ha ↦ ?_⟩
  exact NatSec.ext_of_evU R Y U a _ fun E _ _ z hz ↦ (ha E z hz).trans (hex E z hz).symm

end GlobalTheory.PtExt.NatSec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueSimilitudeBetweenSymplecticLevelsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_similitude_between_symplecticLevels : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ), 0 < M →
  Odd M → 1 ≤ h → ∀ (σ : sympSimGrp h M → (cycAway M →+* cycAway M)),
  (∀ a, ∃ n : ℕ, IsMultOf a n ∧ σ a (zetaAway M) = zetaAway M ^ n) →
  ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S)
    (t₁ t₁' : Sp K ⟶ Sp (cycAway M)) (lv lv' : (Fin h ⊕ Fin h → ℤ) → (Over.mk x ⟶ o.A)),
    SympCond o h M (Over.mk x) t₁ lv → SympCond o h M (Over.mk x) t₁' lv' →
    ∃! a : sympSimGrp h M, t₁ ≫ spMap (σ a) = t₁' ∧ ∀ c, sympTwist a lv c = lv' c := by
  first | exact @GlobalTheory.HTSympCover.sympCond_fibre_existsUnique | exact GlobalTheory.HTSympCover.sympCond_fibre_existsUnique | (intros; apply GlobalTheory.HTSympCover.sympCond_fibre_existsUnique <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitOfNormOneFractionRingDvrStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_of_norm_one_fractionRing_dvr : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (C : Type) [NormedField C] [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → ∀ a : FractionRing V, ‖algebraMap (FractionRing V) C a‖ = 1 → ∃ u : Vˣ, a = algebraMap V (FractionRing V) u := by
  first | exact @GlobalTheory.KeyEven.fractionRing_norm_one_unit | exact GlobalTheory.KeyEven.fractionRing_norm_one_unit | (intros; apply GlobalTheory.KeyEven.fractionRing_norm_one_unit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniversalSectionBasesShrunkAffineChartStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_universal_section_bases_shrunk_affineChart : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (U₀ : M.Z.Opens) (w : M.Z), IsAffineOpen U₀ → w ∈ U₀ → ∀ (P : PolAV (Sp (M.ringOn U₀))) (N : ℕ), 1 ≤ N → ∃ (U : M.Z.Opens) (h : M.ringOn U₀ ≤ M.ringOn U) (P' : PolAV (Sp (M.ringOn U))) (φ : P'.A.left ⟶ P.A.left), U ≤ U₀ ∧ IsAffineOpen U ∧ w ∈ U ∧ IsGrpPullback P'.A P.A (spMap (Subalgebra.inclusion h).toRingHom) φ ∧ LBIso P'.L (P.L.pull φ) ∧ P'.g = P.g ∧ (∃ th : LB.Sec (LPow P'.A P'.L 1 (baseOver (Sp (M.ringOn U)))), GlobalTheory.ThetaReal.UnivBasis P' 1 (fun _ : Fin 1 => SecM.ofSec P'.A th)) ∧ ∃ b : Fin (N ^ P'.g) → SecM P'.A P'.L (N : ℕ) (baseOver (Sp (M.ringOn U))), GlobalTheory.ThetaReal.UnivBasis P' (N : ℕ) b := by
  first | exact @GlobalTheory.Poinc.exists_univBasis_affineChart | exact GlobalTheory.Poinc.exists_univBasis_affineChart | (intros; apply GlobalTheory.Poinc.exists_univBasis_affineChart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsXPowMulSubMemVanishingIdealReduction
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

noncomputable section
namespace GlobalTheory.FormalAlg.PolyLoc

open MvPolynomial

theorem exists_homogeneous_coeff_mem {σ R : Type} [CommRing R] (J : Ideal R) (i : σ) (g : MvPolynomial σ R)
    (hg : ∀ m, coeff m g ∈ J) : ∃ e : ℕ, ∀ d, e ≤ d → ∃ G : MvPolynomial σ R, G.IsHomogeneous d ∧
      (∀ m, coeff m G ∈ J) ∧ (X i - 1 : MvPolynomial σ R) ∣ G - g := by
  let Q : MvPolynomial σ R → Prop := fun p => ∃ e : ℕ, ∀ d, e ≤ d → ∃ G : MvPolynomial σ R, G.IsHomogeneous d ∧
      (∀ m, coeff m G ∈ J) ∧ (X i - 1 : MvPolynomial σ R) ∣ G - p
  have h0 : Q 0 := ⟨0, fun d _ => ⟨0, isHomogeneous_zero _ _ _, fun m => by rw [coeff_zero]; exact J.zero_mem,
    by rw [sub_zero]; exact dvd_zero _⟩⟩
  have hadd : ∀ p q, Q p → Q q → Q (p + q) := by
    rintro p q ⟨e, he⟩ ⟨e', he'⟩
    refine ⟨max e e', fun d hd => ?_⟩
    obtain ⟨G, hG, hGJ, hGd⟩ := he d (le_of_max_le_left hd)
    obtain ⟨G', hG', hGJ', hGd'⟩ := he' d (le_of_max_le_right hd)
    refine ⟨G + G', hG.add hG', fun m => by rw [coeff_add]; exact J.add_mem (hGJ m) (hGJ' m), ?_⟩
    rw [add_sub_add_comm]
    exact hGd.add hGd'
  have hmon : ∀ v (c : R), c ∈ J → Q (monomial v c) := by
    intro v c hc
    refine ⟨v.degree, fun d hd => ⟨monomial v c * X i ^ (d - v.degree), ?_, fun m => ?_, ?_⟩⟩
    · have := (isHomogeneous_monomial (R := R) c (rfl : v.degree = v.degree)).mul (isHomogeneous_X_pow i (d - v.degree))
      rwa [Nat.add_sub_cancel' hd] at this
    · classical
      rw [X_pow_eq_monomial, monomial_mul, coeff_monomial, _root_.mul_one]
      split_ifs
      · exact hc
      · exact J.zero_mem
    · rw [← mul_sub_one]
      exact (sub_one_dvd_pow_sub_one _ _).mul_left _
  rw [g.as_sum]
  exact Finset.sum_induction _ Q hadd h0 fun v _ => hmon v _ (hg v)

theorem exists_X_pow_mul_mem_vanIdeal {X : Scheme.{0}} {R : Type} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R))
    {H : LB X} {m : ℕ} {s : Fin (m + 1) → LB.Sec H} (hc : ⨆ j, nonzeroLocus (s j) = ⊤)
    (ha : ∀ j, IsAffineOpen (nonzeroLocus (s j))) (r : ∀ j, Fin (m + 1) → Γ(X, nonzeroLocus (s j)))
    (hr : ∀ j, IsRatioFamily s j (r j)) (i : Fin (m + 1)) {Q : MvPolynomial (Fin (m + 1)) R} {e : ℕ}
    (hQ : Q.IsHomogeneous e) (h0 : eval₂Hom (cst f _) (r i) Q = 0) :
    ∃ c : ℕ, MvPolynomial.X i ^ c * Q ∈ vanIdeal f s := by
  have hn : ∀ j, ∃ n, r j i ^ n * eval₂Hom (cst f _) (r j) Q = 0 := fun j => by
    refine exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen X (ha j) _ _ (fn_ext fun y hy => ?_)
    have hj : y ∈ nonzeroLocus (s j) := X.basicOpen_le _ hy
    obtain ⟨k, hk⟩ := exists_chart_of_mem_nonzeroLocus hj
    have uj := (mem_nonzeroLocus_iff_isUnit _ hk).1 hj
    have hi : y ∈ nonzeroLocus (s i) := by
      rw [mem_nonzeroLocus_iff_isUnit _ hk, (hr j).gs_eq hj hk i]
      exact ((LBGerm.isUnit_gs_iff (𝟙 X) y _ hj _).2 hy).mul uj
    have e₁ := ((hr j).gs_form f hj hk hQ).symm.trans ((hr i).gs_form f hi hk hQ)
    rw [h0, LBGerm.gs_zero _ y _ hi, mul_zero] at e₁
    rw [LBGerm.gs_zero _ y _ hy]
    exact (gs_res _ y (X.basicOpen_le _) hy _).trans ((uj.pow e).mul_right_eq_zero.1 e₁)
  choose n hn using hn
  refine ⟨Finset.univ.sup n, (mem_vanIdeal _ _ _).2 ?_⟩
  refine (mem_vanishingForms_of_ratios f hc r hr ((isHomogeneous_X_pow i _).mul hQ) fun j => ?_).2
  have hle : n j ≤ Finset.univ.sup n := Finset.le_sup (Finset.mem_univ j)
  obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_le' hle
  rw [hb, map_mul, map_pow, eval₂Hom_X', pow_add, _root_.mul_assoc, hn j, mul_zero]

theorem app_eval_eq_zero {R : Type} [CommRing R] {X X' : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R))
    (β : X' ⟶ X) {H : LB X} {H' : LB X'} {w : LB.Iso H' (H.pull β)} {m : ℕ} {s : Fin (m + 1) → LB.Sec H}
    {s' : Fin (m + 1) → LB.Sec H'} (hH : H.IsLB) (hH' : H'.IsLB) (hrel : ∀ j, Rel β w (s j) (s' j))
    (i : Fin (m + 1)) (r : Fin (m + 1) → Γ(X, nonzeroLocus (s i))) (hr : IsRatioFamily s i r)
    {F : MvPolynomial (Fin (m + 1)) R} {t : ℕ} (hF : F.IsHomogeneous t) (h0 : F ∈ vanIdeal (β ≫ f) s') :
    (β.app (nonzeroLocus (s i))).hom (eval₂Hom (cst f _) r F) = 0 := by
  refine fn_ext fun z hz => ?_
  rw [gs_pull (𝟙 X') β z _ hz, Category.id_comp, LBGerm.gs_zero _ z _ hz]
  obtain ⟨k, hk⟩ := exists_chart hH (β z)
  obtain ⟨k', hk'⟩ := exists_chart hH' z
  have e₁ := Rel.form hrel f hF z k k' hk hk'
  rw [(mem_vanIdeal _ _ _).1 h0 k', LBGerm.gs_zero _ z _ hk', mul_zero] at e₁
  have e₂ := congrArg (β.stalkMap z).hom (hr.gs_form f hz hk hF)
  rw [map_mul, map_pow, gs_stalkMap_comp β (𝟙 X) z _ hk, gs_stalkMap_comp β (𝟙 X) z _ hk,
    gs_stalkMap_comp β (𝟙 X) z _ hz] at e₂
  simp only [Category.comp_id] at e₂
  rw [e₁] at e₂
  have u := (mem_nonzeroLocus_iff_pull (s i) β z hk).1 hz
  exact ((u.pow t).mul_right_eq_zero.1 e₂.symm)

end GlobalTheory.FormalAlg.PolyLoc

open GlobalTheory.FormalAlg.PolyLoc MvPolynomial in

theorem GlobalTheory.FormalAlg.exists_X_pow_mul_sub_mem_vanIdeal : ∀ (R : Type) [CommRing R] (J : Ideal R) (X X' : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (β : X' ⟶ X) (q : X' ⟶ Spec (CommRingCat.of (R ⧸ J))), IsPullback β q f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) → ∀ (H : LB X) (H' : LB X') (w : LB.Iso H' (H.pull β)) (n : ℕ) (s : Fin (n + 1) → LB.Sec H) (s' : Fin (n + 1) → LB.Sec H'), H.IsLB → H'.IsLB → w.IsGen → (∀ j, Rel β w (s j) (s' j)) → VeryAmpleBy f H s → ∀ (t : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous t → F ∈ vanIdeal (β ≫ f) s' → ∀ i, ∃ (N : ℕ) (G : MvPolynomial (Fin (n + 1)) R), G.IsHomogeneous (t + N) ∧ (∀ m, MvPolynomial.coeff m G ∈ J) ∧ MvPolynomial.X i ^ N * F - G ∈ vanIdeal f s := by
  intro R _ J X X' f β q hpb H H' w n s s' hH hH' _ hrel hva t F hF h0 i
  obtain ⟨hc, hva⟩ := hva
  choose ha r hr hsur using hva
  have hR : ∀ j, IsRatioFamily s j (r j) := hr
  set φ := eval₂Hom (AbLaw.cst f (nonzeroLocus (s i))) (r i) with hφ
  have hker := ((GlobalTheory.T.baseChange_quotient_closedImmersion_idealSheaf R J X X' f β q hpb).2.2 _ (ha i)).2
  have hβ : (β.app (nonzeroLocus (s i))).hom (φ F) = 0 := app_eval_eq_zero f β hH hH' hrel i (r i) (hR i) hF h0
  have hJ : φ F ∈ (Ideal.map (C : R →+* MvPolynomial (Fin (n + 1)) R) J).map φ := by
    have h2 : φ F ∈ J.map (AbLaw.cst f (nonzeroLocus (s i))) := hker ▸ (RingHom.mem_ker.2 hβ)
    have h3 : AbLaw.cst f (nonzeroLocus (s i)) = φ.comp C := by
      ext a
      simp [hφ]
    rwa [h3, ← Ideal.map_map] at h2
  obtain ⟨g, hg, hgF⟩ := (Ideal.mem_map_iff_of_surjective φ (hsur i)).1 hJ
  rw [MvPolynomial.mem_map_C_iff] at hg
  obtain ⟨e, he⟩ := exists_homogeneous_coeff_mem J i g hg
  obtain ⟨G₁, hG₁, hG₁J, hdvd⟩ := he (t + e) (Nat.le_add_left e t)
  have hQ : (MvPolynomial.X i ^ e * F - G₁).IsHomogeneous (t + e) := by
    have := (isHomogeneous_X_pow i e).mul hF
    rw [Nat.add_comm e t] at this
    exact this.sub hG₁
  have hφQ : φ (MvPolynomial.X i ^ e * F - G₁) = 0 := by
    obtain ⟨P, hP⟩ := hdvd
    have hx : φ (MvPolynomial.X i) = 1 := by rw [hφ, eval₂Hom_X']; exact (hR i).self_eq_one
    have hG : G₁ = g + (MvPolynomial.X i - 1) * P := by rw [← hP]; ring
    rw [hG, map_sub, map_mul, map_pow, hx, one_pow, _root_.one_mul, map_add, map_mul, map_sub, hx, map_one, sub_self,
      zero_mul, add_zero, hgF, sub_self]
  obtain ⟨c, hc'⟩ := exists_X_pow_mul_mem_vanIdeal f hc ha r hR i hQ hφQ
  refine ⟨c + e, MvPolynomial.X i ^ c * G₁, ?_, fun m => ?_, ?_⟩
  · have := (isHomogeneous_X_pow i c).mul hG₁
    convert this using 1
    ring
  · have h4 : MvPolynomial.X i ^ c * G₁ ∈ Ideal.map (C : R →+* MvPolynomial (Fin (n + 1)) R) J :=
      Ideal.mul_mem_left _ _ (mem_map_C_iff.2 hG₁J)
    exact mem_map_C_iff.1 h4 m
  · convert hc' using 1
    ring
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorPairingAdd
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.FactorAdd

open GlobalTheory.CechPic

variable {S S' : Scheme.{0}}

theorem comp_psum {G T T' : Over S} [GrpObj G] [IsCommMonObj G] (u : T' ⟶ T) {n : ℕ} (x : Fin n → (T ⟶ G))
    (x' : Fin n → (T' ⟶ G)) (h : ∀ i, u ≫ x i = x' i) (I : Finset (Fin n)) :
    u.left ≫ (psum G x I).left = (psum G x' I).left :=
  congrArg (fun q => q.left) ((psum_hom (preHom u) x I).trans (congrArg (fun q => psum G q I) (funext h)))

theorem pull_lam {G T : Over S} [GrpObj G] [IsCommMonObj G] {L : LB G.left} (hL : L.IsLB) (h : (abelian₂ G L).IsLB)
    (x y : T ⟶ G) :
    pull (lift x y : T ⟶ G2 G).left (cls (abelian₂ G L) h) =
      pull (x * y).left (cls L hL) - pull x.left (cls L hL) - pull y.left (cls L hL) +
        pull (1 : T ⟶ G).left (cls L hL) := by
  have e := cls_linComb hL (K := ULift.{0} (Finset (Fin 2))) (fun I => (psum G (x2 G) I.down).left)
    (fun I => (-1) ^ (2 - I.down.card)) h
  refine (congrArg (pull (lift x y : T ⟶ G2 G).left) e).trans ?_
  rw [map_sum]
  refine (Fintype.sum_equiv Equiv.ulift _
    (fun I => ((-1 : ℤ) ^ (2 - I.card)) • pull (psum G ![x, y] I).left (cls L hL)) fun I => ?_).trans ?_
  · rw [map_zsmul, ← pull_comp, comp_psum (lift x y : T ⟶ G2 G) (x2 G) ![x, y] (fun i => by fin_cases i <;> simp [x2])]
    rfl
  rw [show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  have p₀ : psum G ![x, y] ∅ = 1 := rfl
  have p₁ : psum G ![x, y] {0} = x := _root_.mul_one x
  have p₂ : psum G ![x, y] {1} = y := _root_.mul_one y
  have p₃ : psum G ![x, y] {0, 1} = x * y := congrArg (x * ·) (_root_.mul_one y)
  have q₀ : (-1 : ℤ) ^ (2 - (∅ : Finset (Fin 2)).card) = 1 := by decide
  have q₁ : ∀ i : Fin 2, (-1 : ℤ) ^ (2 - ({i} : Finset (Fin 2)).card) = -1 := by decide
  have q₃ : (-1 : ℤ) ^ (2 - ({0, 1} : Finset (Fin 2)).card) = 1 := by decide
  rw [p₀, p₁, p₂, p₃, q₀, q₁, q₁, q₃]
  simp only [neg_smul, one_smul]
  abel

theorem cube {G T : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L) (x x' y : T ⟶ G) :
    pull (x * x' * y).left (cls L.L L.isLB) - pull (x * x').left (cls L.L L.isLB) - pull (x * y).left (cls L.L L.isLB)
      - pull (x' * y).left (cls L.L L.isLB) + pull x.left (cls L.L L.isLB) + pull x'.left (cls L.L L.isLB)
      + pull y.left (cls L.L L.isLB) - pull (1 : T ⟶ G).left (cls L.L L.isLB) = 0 := by
  have h : (Theta G L.L).IsLB := LB.isLB_linComb L.isLB _ _
  have z : cls (Theta G L.L) h = 0 := (cls_eq_zero_iff h).2 ⟨c.t, c.isGen⟩
  have e := cls_linComb L.isLB (K := ULift.{0} (Finset (Fin 3))) (fun I => (psum G (x3 G) I.down).left)
    (fun I => (-1) ^ (3 - I.down.card)) h
  have e' := (congrArg (pull (lift x (lift x' y) : T ⟶ G3 G).left) (e.symm.trans z)).trans (map_zero _)
  refine Eq.trans (Eq.symm ?_) e'
  rw [map_sum]
  refine (Fintype.sum_equiv Equiv.ulift _
    (fun I => ((-1 : ℤ) ^ (3 - I.card)) • pull (psum G ![x, x', y] I).left (cls L.L L.isLB)) fun I => ?_).trans ?_
  · rw [map_zsmul, ← pull_comp, comp_psum (lift x (lift x' y) : T ⟶ G3 G) (x3 G) ![x, x', y]
      (fun i => by fin_cases i <;> simp [x3])]
    rfl
  rw [show (Finset.univ : Finset (Finset (Fin 3))) = {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  have p₀ : psum G ![x, x', y] ∅ = 1 := rfl
  have p₁ : psum G ![x, x', y] {0} = x := _root_.mul_one x
  have p₂ : psum G ![x, x', y] {1} = x' := _root_.mul_one x'
  have p₃ : psum G ![x, x', y] {2} = y := _root_.mul_one y
  have p₄ : psum G ![x, x', y] {0, 1} = x * x' := congrArg (x * ·) (_root_.mul_one x')
  have p₅ : psum G ![x, x', y] {0, 2} = x * y := congrArg (x * ·) (_root_.mul_one y)
  have p₆ : psum G ![x, x', y] {1, 2} = x' * y := congrArg (x' * ·) (_root_.mul_one y)
  have p₇ : psum G ![x, x', y] {0, 1, 2} = x * x' * y :=
    (congrArg (fun q => x * (x' * q)) (_root_.mul_one y)).trans (_root_.mul_assoc _ _ _).symm
  have q₀ : (-1 : ℤ) ^ (3 - (∅ : Finset (Fin 3)).card) = -1 := by decide
  have q₁ : ∀ i : Fin 3, (-1 : ℤ) ^ (3 - ({i} : Finset (Fin 3)).card) = 1 := by decide
  have q₄ : (-1 : ℤ) ^ (3 - ({0, 1} : Finset (Fin 3)).card) = -1 := by decide
  have q₅ : (-1 : ℤ) ^ (3 - ({0, 2} : Finset (Fin 3)).card) = -1 := by decide
  have q₆ : (-1 : ℤ) ^ (3 - ({1, 2} : Finset (Fin 3)).card) = -1 := by decide
  have q₇ : (-1 : ℤ) ^ (3 - ({0, 1, 2} : Finset (Fin 3)).card) = 1 := by decide
  rw [p₀, p₁, p₂, p₃, p₄, p₅, p₆, p₇, q₀, q₁, q₁, q₁, q₄, q₅, q₆, q₇]
  simp only [neg_smul, one_smul]
  abel

theorem lam_add {G T : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L) (h : (abelian₂ G L.L).IsLB)
    (x x' y : T ⟶ G) :
    pull (lift (x * x') y : T ⟶ G2 G).left (cls (abelian₂ G L.L) h) - pull (lift x y : T ⟶ G2 G).left (cls (abelian₂ G L.L) h)
      - pull (lift x' y : T ⟶ G2 G).left (cls (abelian₂ G L.L) h) = 0 := by
  rw [pull_lam L.isLB, pull_lam L.isLB, pull_lam L.isLB, ← cube c x x' y]
  abel

theorem lift_square {G : Over S} {H : Over S'} [GrpObj G] [GrpObj H] {f : S' ⟶ S} {φ : H.left ⟶ G.left}
    (hp : IsGrpPullback H G f φ) {κ : (G2 H).left ⟶ (G2 G).left} (hκ : Geo.Tor.IsSquare (G' := H) (G := G) φ κ)
    {T : Over S'} (x y : T ⟶ H) :
    (lift x y : T ⟶ G2 H).left ≫ κ = (lift (pushHom hp T x) (pushHom hp T y) : Over.mk (T.hom ≫ f) ⟶ G2 G).left := by
  have A : ∀ (p q : Over.mk (T.hom ≫ f) ⟶ G), p.left = x.left ≫ φ → q.left = y.left ≫ φ →
      (lift x y : T ⟶ G2 H).left ≫ κ = (lift p q : Over.mk (T.hom ≫ f) ⟶ G2 G).left := by
    intro p q hp' hq'
    apply pullback.hom_ext
    · show (_ ≫ κ) ≫ (fst G G).left = (lift p q ≫ fst G G).left
      rw [lift_fst, hp', Category.assoc, hκ.1, ← Category.assoc, ← Over.comp_left, lift_fst]
    · show (_ ≫ κ) ≫ (snd G G).left = (lift p q ≫ snd G G).left
      rw [lift_snd, hq', Category.assoc, hκ.2, ← Category.assoc, ← Over.comp_left, lift_snd]
  exact A _ _ rfl rfl

theorem exists_gen {G G' : Over S} {H : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] [GrpObj H]
    {L : RigLB G'} (c : CubicalStr G' L) (a b : G ⟶ G') [IsMonHom a] {f : S' ⟶ S} {φ : H.left ⟶ G.left}
    (hp : IsGrpPullback H G f φ) {κ : (G2 H).left ⟶ (G2 G).left} (hκ : Geo.Tor.IsSquare (G' := H) (G := G) φ κ)
    {T : Over S'} (x x' y : T ⟶ H) (ψ : Fin 3 → (T.left ⟶ (G2 H).left))
    (h₀ : ψ 0 = (lift (x * x') y : T ⟶ G2 H).left) (h₁ : ψ 1 = (lift x y : T ⟶ G2 H).left)
    (h₂ : ψ 2 = (lift x' y : T ⟶ G2 H).left) :
    ∃ u : LB.Gen (LB.LinComb (((abelian₂ G' L.L).pull (lift (fst G G ≫ a) (snd G G ≫ b) : G2 G ⟶ G2 G').left).pull κ)
      (K := Fin 3) ψ ![1, -1, -1]), u.IsGen := by
  have hΛ : (abelian₂ G' L.L).IsLB := LB.isLB_linComb L.isLB _ _
  have hP := pull_isLB (pull_isLB hΛ (lift (fst G G ≫ a) (snd G G ≫ b) : G2 G ⟶ G2 G').left) κ
  have key : ∀ p q : T ⟶ H, pull (lift p q : T ⟶ G2 H).left (cls _ hP) =
      pull (lift (pushHom hp T p ≫ a) (pushHom hp T q ≫ b) : Over.mk (T.hom ≫ f) ⟶ G2 G').left (cls _ hΛ) := by
    intro p q
    rw [cls_pull (pull_isLB hΛ _), cls_pull hΛ, ← pull_comp, ← pull_comp, lift_square hp hκ]
    refine congrArg (fun m => pull m (cls _ hΛ)) ?_
    refine congrArg (fun m : Over.mk (T.hom ≫ f) ⟶ G2 G' => m.left)
      (show lift (pushHom hp T p) (pushHom hp T q) ≫ lift (fst G G ≫ a) (snd G G ≫ b) = _ from ?_)
    simp
  refine (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).1 ?_
  rw [cls_linComb hP, Fin.sum_univ_three, h₀, h₁, h₂, key, key, key, map_mul, MonObj.mul_comp]
  have e := lam_add c hΛ (pushHom hp T x ≫ a) (pushHom hp T x' ≫ a) (pushHom hp T y ≫ b)
  refine Eq.trans ?_ e
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    one_smul, neg_smul, sub_eq_add_neg]

end GlobalTheory.Mum.FactorAdd

theorem GlobalTheory.Mum.factorPairing_add : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∀ κ₀ : (G2 ((Over.pullback (jK R)).obj G)).left ⟶ (G2 G).left, Geo.Tor.IsSquare (G' := ((Over.pullback (jK R)).obj G)) (G := G) (pullback.fst G.hom (jK R)) κ₀ → ∃ u : LB.Gen (LB.LinComb (((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left).pull κ₀) (K := Fin 3) ![(lift (fst ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) * (snd ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ≫ fst ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G))) (snd ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ≫ snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)) : ((Over.pullback (jK R)).obj G) ⊗ (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ⟶ G2 ((Over.pullback (jK R)).obj G)).left, (lift (fst ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G))) (snd ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ≫ snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)) : ((Over.pullback (jK R)).obj G) ⊗ (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ⟶ G2 ((Over.pullback (jK R)).obj G)).left, (snd ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) : ((Over.pullback (jK R)).obj G) ⊗ (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ⟶ G2 ((Over.pullback (jK R)).obj G)).left] ![1, -1, -1]), u.IsGen := by
  intro R _ _ _ _ D D' F A' G' _ _ _ U' oA oG _ G _ _ _ inc pr hinc _ _ _ κ₀ hκ
  exact GlobalTheory.Mum.FactorAdd.exists_gen U'.cubG inc (inc ≫ oG.act F.f) (isGrpPullback_pullback G (jK R)) hκ
    (fst _ _) (snd _ _ ≫ fst _ _) (snd _ _ ≫ snd _ _) _ rfl rfl
    (by rw [lift_comp_fst_snd]; rfl)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorsFibreOverPointIffFactorsProductStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.factors_fibreOverPoint_iff_factors_product : ∀ {R : Type} [CommRing R] (A : Over (Sp R)) {T : Over (Sp R)} {V : Type} [CommRing V] (φ : Sp V ⟶ T.left) {H : Over (Sp R)} (h : H ⟶ A ⊗ T) (Y : Over (Sp V)) (x : Y ⟶ GlobalTheory.TwistFlat.bc A φ), (∃ y : Y ⟶ GlobalTheory.TwistFlat.ker A φ h, y ≫ GlobalTheory.TwistFlat.kerι A φ h = x) ↔ ∃ z : GlobalTheory.TwistFlat.up φ Y ⟶ H, z ≫ h = lift (GlobalTheory.TwistFlat.upa φ x) (GlobalTheory.TwistFlat.upt φ Y) := by
  first | exact @GlobalTheory.TwistFlat.factor_ker_iff | exact GlobalTheory.TwistFlat.factor_ker_iff | (intros; apply GlobalTheory.TwistFlat.factor_ker_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FfDescentElem
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem ff_descent_elem : ∀ (D D' : Type) [CommRing D] [CommRing D'] [Algebra D D']
    [Module.FaithfullyFlat D D'] (a : D'), a ⊗ₜ[D] (1 : D') = (1 : D') ⊗ₜ[D] a →
      ∃ e : D, algebraMap D D' e = a := by
  intro D D' _ _ _ _ a h
  have hx : FlatDescent.amitsurDiff (A := D) D' D (a ⊗ₜ[D] (1 : D)) = 0 := by
    apply (LinearEquiv.lTensor D' (TensorProduct.rid D D')).injective
    simp [FlatDescent.amitsurDiff_tmul, h]
  obtain ⟨m, hm⟩ := ((FlatDescent.amitsur_exact (A := D) (B := D') (M := D)).2 _).1 hx
  refine ⟨m, ?_⟩
  have := congrArg (TensorProduct.rid D D') hm
  simpa [Algebra.algebraMap_eq_smul_one] using this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSectionOverOrdinaryLocusStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_section_over_ordinary_locus : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (M : Model b N) (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ M.X) (gs : Y₀ ⟶ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme), gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = s₀ → IsFinite gs → ∀ u : M.X, u ∈ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))) → {z : M.X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ M.X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ s₀ ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧ y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z}.Finite := by
  first | (exact @GlobalTheory.UPel.HT.ES.CorrQF.finite_specialisations_of_finite_source) | (exact GlobalTheory.UPel.HT.ES.CorrQF.finite_specialisations_of_finite_source) | (intros; apply GlobalTheory.UPel.HT.ES.CorrQF.finite_specialisations_of_finite_source  <;> assumption)
end

