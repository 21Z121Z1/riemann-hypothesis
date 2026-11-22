import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleDescentToSubfield
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0070
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0067
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0106
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsNonvanishing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0016
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfAssociated
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0107
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleDescentToSubfieldStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundle_descent_to_subfield : ∀ (K : Type) [Field K] (K₀ : Subfield K) (X₀ X : Scheme.{0}) (p₀ : X₀ ⟶ Sp K₀) (p : X ⟶ Sp K) (φ : X ⟶ X₀) [QuasiCompact p₀] [QuasiSeparated p₀] (L : LB X), L.IsLB → IsPullback φ p p₀ (spMap K₀.subtype) → ∃ s : Finset K, ∀ (K₁ : Subfield K) (h : K₀ ≤ K₁), (s : Set K) ⊆ K₁ → ∀ (X₁ : Scheme.{0}) (p₁ : X₁ ⟶ Sp K₁) (φ₁ : X₁ ⟶ X₀) (ψ : X ⟶ X₁), IsPullback φ₁ p₁ p₀ (spMap (Subfield.inclusion h)) → ψ ≫ φ₁ = φ → ψ ≫ p₁ = p ≫ spMap K₁.subtype → ∃ L₁ : LB X₁, L₁.IsLB ∧ LBIso L (L₁.pull ψ) := by
  first | exact @GlobalTheory.LBDescent.exists_lb_subfield | exact GlobalTheory.LBDescent.exists_lb_subfield | (intros; apply GlobalTheory.LBDescent.exists_lb_subfield <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsNonzeroCoordinateAffineChart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.CoordChart

private theorem isIso_restrict_lemma {X Z Y : Scheme.{0}} (x : X ⟶ Z) [Mono x] (j : Y ⟶ X)
    [IsOpenImmersion (j ≫ x)] : IsIso (x ∣_ (j ≫ x).opensRange) := by
  set V := (j ≫ x).opensRange with hV
  let s : V.toScheme ⟶ X := (j ≫ x).isoOpensRange.inv ≫ j
  have hs : s ≫ x = V.ι := by
    rw [← cancel_epi (j ≫ x).isoOpensRange.hom]
    simp only [s, Category.assoc, Iso.hom_inv_id_assoc]
    exact (Scheme.Hom.isoOpensRange_hom_ι (j ≫ x)).symm
  have hr : Set.range s ⊆ Set.range (x ⁻¹ᵁ V).ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    show x (s y) ∈ V
    have e : x (s y) = V.ι y := by rw [← Scheme.Hom.comp_apply, hs]
    rw [e]
    have hm : V.ι y ∈ Set.range V.ι := ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι] at hm
    exact hm
  let s' := IsOpenImmersion.lift (x ⁻¹ᵁ V).ι s hr
  have h1 : s' ≫ (x ⁻¹ᵁ V).ι = s := IsOpenImmersion.lift_fac _ _ _
  refine ⟨⟨s', ?_, ?_⟩⟩
  · rw [← cancel_mono ((x ⁻¹ᵁ V).ι ≫ x), Category.assoc, reassoc_of% h1, hs, morphismRestrict_ι,
      Category.id_comp]
  · rw [← cancel_mono V.ι, Category.assoc, morphismRestrict_ι, reassoc_of% h1, hs, Category.id_comp]

theorem isOpenImmersion_of_mono_of_local {X Z : Scheme.{0}} (x : X ⟶ Z) [Mono x]
    (h : ∀ p : X, ∃ (Y : Scheme.{0}) (j : Y ⟶ X), IsOpenImmersion (j ≫ x) ∧
      x p ∈ Set.range (j ≫ x)) : IsOpenImmersion x := by
  choose Y j hj hp using h
  refine IsZariskiLocalAtTarget.of_range_subset_iSup (P := @IsOpenImmersion)
    (fun p => (j p ≫ x).opensRange) ?_ (fun p => ?_)
  · rintro _ ⟨p, rfl⟩
    simp only [TopologicalSpace.Opens.coe_iSup, Set.mem_iUnion, SetLike.mem_coe]
    exact ⟨p, by rw [Scheme.Hom.mem_opensRange]; exact hp p⟩
  · have := isIso_restrict_lemma x (j p)
    infer_instance

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp, CommRingCat.ofHom_comp]

theorem spMap_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) :
    f = g := by
  have e := congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  simpa using e

theorem exists_spMap {A B : Type} [CommRing A] [CommRing B] (y : Sp B ⟶ Sp A) :
    ∃ f : A →+* B, y = spMap f := by
  refine ⟨(Spec.preimage y).hom, ?_⟩
  simp only [spMap, CommRingCat.ofHom_hom, Spec.map_preimage]

theorem mono_of_ring_points {A : Type} [CommRing A] {Z : Scheme.{0}} (x : Sp A ⟶ Z)
    (h : ∀ (B : Type) [CommRing B] (f g : A →+* B), spMap f ≫ x = spMap g ≫ x → f = g) : Mono x := by
  refine ⟨fun {W} a b hab => ?_⟩
  have key : ∀ (B : Type) [CommRing B] (t : Sp B ⟶ W), t ≫ a = t ≫ b := by
    intro B _ t
    obtain ⟨f, hf⟩ := exists_spMap (t ≫ a)
    obtain ⟨g, hg⟩ := exists_spMap (t ≫ b)
    have hfg : f = g := h _ f g (by rw [← hf, ← hg, Category.assoc, Category.assoc, hab])
    rw [hf, hg, hfg]
  exact W.affineOpenCover.openCover.hom_ext a b
    (fun k => key (W.affineOpenCover.X k) (W.affineOpenCover.openCover.f k))

theorem exists_chart : ∀ (R σ : Type) [CommRing R] (I : Ideal (MvPolynomial σ R)) (Z : Scheme.{0}) (s : Z ⟶ Sp R) (M : LB Z) (th : σ → M.Sec) (i : σ), ProjRep I s M th → ∃ x : Sp (MvPolynomial σ R ⧸ (I ⊔ Ideal.span {MvPolynomial.X i - 1})) ⟶ Z, IsOpenImmersion x ∧ Set.range x = (Out.nonzeroLocus (th i) : Set Z) ∧ x ≫ s = spMap ((Ideal.Quotient.mk _).comp MvPolynomial.C) ∧ SecCoord M th x (fun a => Ideal.Quotient.mk _ (MvPolynomial.X a)) := by
  intro R σ _ I Z s M th i hP
  obtain ⟨hM, hpts, hrep⟩ := hP
  set J := I ⊔ Ideal.span {MvPolynomial.X i - 1} with hJ
  set q := Ideal.Quotient.mk J with hq

  have hq1 : q (MvPolynomial.X i) = 1 := by
    rw [← sub_eq_zero, ← map_one q, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_right (Ideal.subset_span rfl)

  have hev : ∀ F, MvPolynomial.eval₂ (q.comp MvPolynomial.C) (fun a => q (MvPolynomial.X a)) F = q F := by
    intro F
    have e : MvPolynomial.eval₂Hom (q.comp MvPolynomial.C) (fun a => q (MvPolynomial.X a)) = q :=
      MvPolynomial.ringHom_ext (fun r => by simp) (fun a => by simp)
    exact RingHom.congr_fun e F
  obtain ⟨x, ⟨hxs, hxc⟩, -⟩ := hrep _ (q.comp MvPolynomial.C) (fun a => q (MvPolynomial.X a))
    (by rw [Ideal.eq_top_iff_one, ← hq1]; exact Ideal.subset_span ⟨i, rfl⟩)
    (fun F hF => by rw [hev, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.mem_sup_left hF)

  have hmono : Mono x := by
    apply mono_of_ring_points
    intro B _ f g hfg
    have hcf := GlobalTheory.ZM.Coord.baseChange hxc f
    have hcg := GlobalTheory.ZM.Coord.baseChange hxc g
    rw [hfg] at hcf
    obtain ⟨u, hu⟩ := GlobalTheory.ZM.Coord.unique hM hcg hcf
    have hu1 : (u : B) = 1 := by
      have e := hu i
      simp only [hq1, map_one] at e
      simpa using e.symm
    have hv : ∀ a, f (q (MvPolynomial.X a)) = g (q (MvPolynomial.X a)) := fun a => by
      rw [hu a, hu1, _root_.one_mul]
    have hb : f.comp (q.comp MvPolynomial.C) = g.comp (q.comp MvPolynomial.C) := by
      apply spMap_inj
      rw [← spMap_comp (q.comp MvPolynomial.C) f, ← spMap_comp (q.comp MvPolynomial.C) g, ← hxs,
        reassoc_of% hfg]
    have hc : f.comp q = g.comp q :=
      MvPolynomial.ringHom_ext (fun r => by simpa using RingHom.congr_fun hb r) (fun a => by simpa using hv a)
    exact Ideal.Quotient.ringHom_ext hc

  have hsub : Set.range x ⊆ (Out.nonzeroLocus (th i) : Set Z) := by
    rintro _ ⟨p, rfl⟩
    refine (GlobalTheory.ZM.CoordMove.mem_nonzeroLocus_iff hM i p hxc).2 ?_
    show q (MvPolynomial.X i) ∉ p.asIdeal
    rw [hq1]
    exact fun h1 => p.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)

  have hloc : ∀ z ∈ (Out.nonzeroLocus (th i) : Set Z), ∃ (B : Type) (_ : CommRing B)
      (ψ : (MvPolynomial σ R ⧸ J) →+* B), IsOpenImmersion (spMap ψ ≫ x) ∧ z ∈ Set.range (spMap ψ ≫ x) := by
    intro z hz
    obtain ⟨R', _, x', v', hx'o, ⟨p, rfl⟩, hx'c⟩ := (GlobalTheory.T.sectionCoordinateVector_exists_locally Z M σ th hM).2.2 z
    have hp : v' i ∉ p.asIdeal := (GlobalTheory.ZM.CoordMove.mem_nonzeroLocus_iff hM i p hx'c).1 hz
    have hunit : IsUnit (algebraMap R' (Localization.Away (v' i)) (v' i)) :=
      IsLocalization.Away.algebraMap_isUnit (v' i)
    have hc1 := GlobalTheory.ZM.Coord.scale (GlobalTheory.ZM.Coord.baseChange hx'c (algebraMap R' (Localization.Away (v' i))))
      hunit.unit⁻¹
    set w : σ → Localization.Away (v' i) :=
      fun a => ((hunit.unit⁻¹ : (Localization.Away (v' i))ˣ) : Localization.Away (v' i)) *
        algebraMap R' (Localization.Away (v' i)) (v' a) with hw
    have hwi : w i = 1 := by simp [w]
    obtain ⟨β', hβ'⟩ := exists_spMap ((spMap (algebraMap R' (Localization.Away (v' i))) ≫ x') ≫ s)
    obtain ⟨hspan, hI⟩ := hpts _ β' _ w hβ' hc1
    have hker : J ≤ RingHom.ker (MvPolynomial.eval₂Hom β' w) := by
      refine sup_le (fun F hF => hI F hF) (Ideal.span_le.2 ?_)
      rintro _ rfl
      simp [hwi]
    let ψ : (MvPolynomial σ R ⧸ J) →+* Localization.Away (v' i) :=
      Ideal.Quotient.lift J (MvPolynomial.eval₂Hom β' w) (fun F hF => hker hF)
    have hψC : ∀ r, ψ (q (MvPolynomial.C r)) = β' r := fun r =>
      (Ideal.Quotient.lift_mk J _ _).trans (by simp)
    have hψX : ∀ a, ψ (q (MvPolynomial.X a)) = w a := fun a =>
      (Ideal.Quotient.lift_mk J _ _).trans (by simp)
    obtain ⟨y, -, hyu⟩ := hrep _ β' w hspan hI
    have e2 : spMap (algebraMap R' (Localization.Away (v' i))) ≫ x' = y := hyu _ ⟨hβ', hc1⟩
    have e1 : spMap ψ ≫ x = y := by
      refine hyu _ ⟨?_, ?_⟩
      · rw [Category.assoc, hxs, spMap_comp]
        congr 1
        exact RingHom.ext hψC
      · have e := GlobalTheory.ZM.Coord.baseChange hxc ψ
        convert e using 2 with a
        exact (hψX a).symm
    have hrange := PrimeSpectrum.localization_away_comap_range (Localization.Away (v' i)) (v' i)
    have hpm : p ∈ Set.range (PrimeSpectrum.comap (algebraMap R' (Localization.Away (v' i)))) := by
      rw [hrange]
      exact hp
    obtain ⟨p', hp'⟩ := hpm
    refine ⟨Localization.Away (v' i), inferInstance, ψ, ?_, p', ?_⟩
    · rw [e1, ← e2]
      infer_instance
    · rw [e1, ← e2]
      show x' (PrimeSpectrum.comap (algebraMap R' (Localization.Away (v' i))) p') = x' p
      rw [hp']
  have := hmono
  refine ⟨x, ?_, ?_, hxs, hxc⟩
  · apply isOpenImmersion_of_mono_of_local x
    intro p
    obtain ⟨B, _, ψ, h1, h2⟩ := hloc (x p) (hsub ⟨p, rfl⟩)
    exact ⟨Sp B, spMap ψ, h1, h2⟩
  · refine Set.Subset.antisymm hsub (fun z hz => ?_)
    obtain ⟨B, _, ψ, -, ⟨b, hb⟩⟩ := hloc z hz
    exact ⟨(spMap ψ) b, hb⟩

end GlobalTheory.ZM.CoordChart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsNonzeroLocusLeOpenPolarisationComplexStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzeroLocus_le_open_polarisation_complex : Out.Laws → ∀ (P₀ : Out.PolAV (Sp ℂ)) (O : P₀.A.left.Opens) (y : P₀.A.left), y ∈ O → ∃ (n : ℕ) (σ : (lbPow P₀.L n).Sec), y ∈ Out.nonzeroLocus σ ∧ Out.nonzeroLocus σ ≤ O := by
  first | exact @GlobalTheory.exists_nonzeroLocus_le | exact GlobalTheory.exists_nonzeroLocus_le | (intros; apply GlobalTheory.exists_nonzeroLocus_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsRigidifiedTwist
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.RigidifyTwist

open CechPic

theorem pull_cls_eq_zero {X Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (r : Z ⟶ X) (i : L.ι)
    (hi : ∀ z, r z ∈ L.U i) : CechPic.pull r (cls L hL) = 0 := by
  rw [← cls_pull hL r (pull_isLB hL r), cls_eq_zero_iff]
  refine (iso_triv_iff _).1 (iso_of_chart (pull_isLB hL r) ⟨fun _ _ => i, fun _ y _ => mem_pull.2 (hi y), ?_⟩)
  intro y p q hp hq
  rw [gm_pull_g L r (𝟙 Z) y (fun _ => i) (fun _ => i) (mem_pull.2 (hi y)) (mem_pull.2 (hi y))]
  have hy : (𝟙 Z ≫ r) y ∈ L.U i := by
    simpa using hi y
  rw [gm_self hL _ y hy]
  exact map_one _

theorem eSec_hom {S : Scheme.{0}} (A : Over S) [GrpObj A] : eSec A ≫ A.hom = 𝟙 S := by
  unfold eSec
  exact (Over.w _).trans rfl

private theorem cls_pull_tens_dual_eq_sub {S Y : Scheme.{0}} (A : Over S) (M : LB A.left) (hM : M.IsLB) (N : LB S)
    (hN : N.IsLB) (f : Y ⟶ A.left) (h : ((tens M (dual (N.pull A.hom))).pull f).IsLB) :
    cls _ h = pull f (cls M hM) - pull (f ≫ A.hom) (cls N hN) := by
  have hP := pull_isLB hN A.hom
  rw [cls_pull (isLB_tens hM (isLB_dual hP)) f h, cls_tens hM (isLB_dual hP), cls_dual hP,
    cls_pull hN A.hom, map_add, map_neg, pull_comp, sub_eq_add_neg]

private theorem pGen_of_isGen {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}
    (w : LB.Iso L' (L.pull F)) (hw : w.IsGen) : PGen w := by
  intro Y f y j1 j2 k1 k2 h1 h2 h3 h4
  unfold gw
  have m1 : f y ∈ (L.pull F).U (fun _ => j1) := mem_pull.2 h1
  have m2 : f y ∈ (L.pull F).U (fun _ => j2) := mem_pull.2 h2
  have hV : f y ∈ ((L.pull F).div L').U (fun _ => j1, k1) ⊓ ((L.pull F).div L').U (fun _ => j2, k2) :=
    ⟨⟨m1, h3⟩, ⟨m2, h4⟩⟩
  have e := congrArg (gm f y _) (hw (fun _ => j1, k1) (fun _ => j2, k2))
  rw [map_mul, gm_res f y _ hV, gm_res f y _ hV, gm_div' (L.pull F) L' f y _ _ ⟨m1, h3⟩ ⟨m2, h4⟩,
    gm_pull_g L F f y _ _ m1 m2] at e
  exact e

private theorem lbIso_tens_dual_pull_eSec_restrict {S : Scheme.{0}} (A : Over S) [GrpObj A] (M : LB A.left) (hM : M.IsLB)
    (U : S.Opens) (j : (M.pull (eSec A)).ι) (hU : U ≤ (M.pull (eSec A)).U j) :
    LBIso ((tens M (dual ((M.pull (eSec A)).pull A.hom))).pull (A.hom ⁻¹ᵁ U).ι) (M.pull (A.hom ⁻¹ᵁ U).ι) := by
  have hN : (M.pull (eSec A)).IsLB := pull_isLB hM _
  have hT := isLB_tens hM (isLB_dual (pull_isLB hN A.hom))
  have hz : ∀ z : U.toScheme, U.ι z ∈ (M.pull (eSec A)).U j := fun z => by
    exact hU z.2
  refine (cls_eq_iff (pull_isLB hT _) (pull_isLB hM _)).1 ?_
  rw [cls_pull_tens_dual_eq_sub A M hM _ hN, ← morphismRestrict_ι, pull_comp, pull_cls_eq_zero hN U.ι j hz, map_zero,
    sub_zero, cls_pull hM]

theorem exists_rigidified_twist : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (M : LB A.left), M.IsLB → ∃ M' : LB A.left, M'.IsLB ∧ Out.Rigidified A M' ∧ (∀ p : S, ∃ U : S.Opens, p ∈ U ∧ LBIso (M'.pull (A.hom ⁻¹ᵁ U).ι) (M.pull (A.hom ⁻¹ᵁ U).ι)) ∧ (∀ (K : Type) [Field K] (x : Sp K ⟶ S) (X : Scheme.{0}) (φ : X ⟶ A.left) (π : X ⟶ Sp K), φ ≫ A.hom = π ≫ x → LBIso (M'.pull φ) (M.pull φ)) ∧ (IsProper A.hom → Out.RelAmple A M → Out.RelAmple A M') := by
  intro S A _ M hM
  have hN : (M.pull (eSec A)).IsLB := pull_isLB hM _
  have hP : ((M.pull (eSec A)).pull A.hom).IsLB := pull_isLB hN _
  have hT : (tens M (dual ((M.pull (eSec A)).pull A.hom))).IsLB := isLB_tens hM (isLB_dual hP)
  refine ⟨tens M (dual ((M.pull (eSec A)).pull A.hom)), hT, ?_, ?_, ?_, ?_⟩
  · unfold Out.Rigidified
    refine (cls_eq_zero_iff (pull_isLB hT _)).1 ?_
    rw [cls_pull_tens_dual_eq_sub A M hM _ hN, eSec_hom A, pull_id, cls_pull hM (eSec A) hN, sub_self]
  · intro p
    obtain ⟨j, hj⟩ := exists_chart hN p
    exact ⟨_, hj, lbIso_tens_dual_pull_eSec_restrict A M hM _ j le_rfl⟩
  · intro K _ x X φ π hφ
    obtain ⟨j, hj⟩ := exists_chart hN (x (Classical.arbitrary (Sp K)))
    have hx : ∀ z, x z ∈ (M.pull (eSec A)).U j := fun z => by
      rw [Subsingleton.elim z (Classical.arbitrary _)]
      exact hj
    refine (cls_eq_iff (pull_isLB hT _) (pull_isLB hM _)).1 ?_
    rw [cls_pull_tens_dual_eq_sub A M hM _ hN, hφ, pull_comp, pull_cls_eq_zero hN x j hx, map_zero, sub_zero, cls_pull hM]
  · intro hpr hamp
    have := hpr
    refine AmpleLocal.relAmple_of_locally S A _ hT inferInstance inferInstance fun s => ?_
    obtain ⟨j, hj⟩ := exists_chart hN s
    obtain ⟨V, hV, hsV, hVle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens hj
    obtain ⟨w, hw⟩ := lbIso_tens_dual_pull_eSec_restrict A M hM V j hVle
    have hpw : PGen w := pGen_of_isGen w hw
    exact ⟨V, hsV, relAmple_pull (A' := Over.mk (A.hom ∣_ V)) (isPullback_morphismRestrict A.hom V).flip hM
      (pull_isLB hT _) (w := w) hpw V hV (fun y => y.2) hamp⟩

end GlobalTheory.RigidifyTwist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecOnNonvanishing
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.SecFamily

theorem pushInvertible_of_laws (h : Out.Laws) (X : Scheme.{0}) [IsLocallyNoetherian X] (P : Out.PolAV X) :
    PushInvertible P.A P.L :=
  GlobalTheory.PushInv.pushInvertible h.secBaseChange X P

theorem exists_secOn_nonvanishing : Out.Laws → ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (P : Out.PolAV X) (x : X), ∃ (V : X.Opens) (θ : ∀ i, Γ(P.A.left, P.A.hom ⁻¹ᵁ V ⊓ P.L.U i)), x ∈ V ∧ θ ∈ secOn P.L (P.A.hom ⁻¹ᵁ V) ∧ (∀ y ∈ V, ∃ (a : P.A.left) (i : P.L.ι), P.A.hom a = y ∧ a ∈ P.A.left.basicOpen (θ i)) := by
  intro h X _ P x
  obtain ⟨V, hV, θ, hθ, -, H⟩ := pushInvertible_of_laws h X P x
  exact ⟨V, θ, hV, hθ, H⟩

end GlobalTheory.SecFamily
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSectionsCoverCubeEffectiveAbelianVariety
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.EffectiveCube

theorem unitAt_pull {X Y : Scheme.{0}} {N : LB X} (s : N.Sec) (φ : Y ⟶ X) (y : Y)
    (h : φ y ∈ Out.nonzeroLocus s) : UnitAt N (K := PUnit) (fun _ => φ) (fun _ => 1) y := by
  have h' : y ∈ Out.nonzeroLocus (GlobalTheory.secPull s φ) := by
    rw [GlobalTheory.nonzeroLocus_secPull]; exact h
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 h'
  exact ⟨GlobalTheory.secPull s φ, fun J hJ => isUnit_sval _ (𝟙 Y) y hJ k hk⟩

theorem exists_mem_of_unitAt {X Y : Scheme.{0}} {N : LB X} (hN : N.IsLB) {I : Type} [Fintype I]
    {φ : I → (Y ⟶ X)} {ε : I → ℤ} {y : Y} (h : UnitAt N φ ε y) :
    ∃ u : (LB.LinComb N φ ε).Sec, y ∈ Out.nonzeroLocus u := by
  obtain ⟨u, hu⟩ := h
  choose J hJ using fun χ : Y ⟶ X => exists_chart hN (χ y)
  exact ⟨u, (mem_nonzeroLocus u y).2 ⟨_, Good.mem hJ φ (𝟙 Y), hu J hJ⟩⟩

theorem exists_fin_cover {X : Scheme.{0}} [CompactSpace X] [JacobsonSpace X] (M : LB X)
    (h : ∀ y : X, IsClosed {y} → ∃ u : M.Sec, y ∈ Out.nonzeroLocus u) :
    ∃ (r : ℕ) (u : Fin r → M.Sec), ⨆ i, Out.nonzeroLocus (u i) = ⊤ := by
  have hall : (Set.univ : Set X) ⊆ ⋃ u : M.Sec, (Out.nonzeroLocus u : Set X) := by
    intro y _
    by_contra hy
    have ho : IsOpen (⋃ u : M.Sec, (Out.nonzeroLocus u : Set X)) :=
      isOpen_iUnion fun u => (Out.nonzeroLocus u).isOpen
    obtain ⟨c, hc, hcl⟩ := nonempty_inter_closedPoints
      (Z := (⋃ u : M.Sec, (Out.nonzeroLocus u : Set X))ᶜ) ⟨y, hy⟩ ho.isClosed_compl.isLocallyClosed
    obtain ⟨u, hu⟩ := h c hcl
    exact hc (Set.mem_iUnion.2 ⟨u, hu⟩)
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover _ (fun u : M.Sec => (Out.nonzeroLocus u).isOpen) hall
  refine ⟨T.card, fun i => (T.equivFin.symm i).1, eq_top_iff.2 fun y _ => ?_⟩
  obtain ⟨u, hu, hy⟩ := Set.mem_iUnion₂.1 (hT (Set.mem_univ y))
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨T.equivFin ⟨u, hu⟩, ?_⟩
  simp only [Equiv.symm_apply_apply]
  exact hy

theorem exists_sections_cube_cover :
    (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N : LB P.A.left) (s : N.Sec), N.IsLB → (∃ j, s.f j ≠ 0) → ∃ (r : ℕ) (u : Fin r → (lbPow N 3).Sec), ⨆ i, Out.nonzeroLocus (u i) = ⊤ := by
  intro hcube K _ _ P N s hN ⟨j, hj⟩
  obtain ⟨t, ht⟩ := hcube _ P N hN
  have := P.isAb.smooth
  have := P.isAb.proper
  have := P.isAb.geomConnected
  have := geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres P.A.hom
  have : IsIntegral P.A.left := GeometricallyIntegral.isIntegral_of_subsingleton P.A.hom
  let T : Over (Sp K) := Over.mk (𝟙 (Sp K))
  have : IsIntegral (T ⊗ P.A).left :=
    GeometricallyIntegral.geometrically_isIntegral (𝟙 (Sp K)) _ _ (IsPullback.of_hasPullback (𝟙 (Sp K)) P.A.hom).flip
  have : JacobsonSpace P.A.left := LocallyOfFiniteType.jacobsonSpace P.A.hom
  have : CompactSpace P.A.left := QuasiCompact.compactSpace_of_compactSpace P.A.hom
  let π : P.A ⟶ T := Over.homMk P.A.hom (Category.comp_id _)
  have hD : (((snd T P.A).left ⁻¹ᵁ Out.nonzeroLocus s : (T ⊗ P.A).left.Opens) : Set (T ⊗ P.A).left).Nonempty := by
    obtain ⟨d, hd⟩ : ((P.A.left.basicOpen (s.f j) : P.A.left.Opens) : Set P.A.left).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro h
      exact hj ((basicOpen_eq_bot_iff _).1 (SetLike.coe_injective h))
    refine ⟨(lift π (𝟙 _)).left d, ?_⟩
    show (snd T P.A).left ((lift π (𝟙 _)).left d) ∈ Out.nonzeroLocus s
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, lift_snd]
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, hd⟩
  refine exists_fin_cover _ fun y hy => ?_
  let x : T ⟶ P.A := Over.homMk (pointOfClosedPoint P.A.hom y hy) (pointOfClosedPoint_comp P.A.hom y hy)
  let p : T.left := IsLocalRing.closedPoint K
  have hx : x.left p = y := pointOfClosedPoint_apply P.A.hom y hy p
  have hxπ : x ≫ π = 𝟙 T := Over.OverMorphism.ext (pointOfClosedPoint_comp P.A.hom y hy)
  have good : ∀ a : T ⟶ P.A, (Out.ptSecT P.A (a * x)).left p ∈ (snd T P.A).left ⁻¹ᵁ Out.nonzeroLocus s →
      UnitAt N (K := PUnit) (fun _ => ((π ≫ a) * 𝟙 P.A).left) (fun _ => 1) y := fun a ha => by
    refine unitAt_pull s _ y ?_
    have e : x ≫ ((π ≫ a) * 𝟙 P.A) = Out.ptSecT P.A (a * x) ≫ snd T P.A := by
      simp [Out.ptSecT, MonObj.comp_mul, reassoc_of% hxπ]
    rw [← hx, ← Scheme.Hom.comp_apply, ← Over.comp_left, e]
    exact ha
  obtain ⟨a, ha, -⟩ := NoBasePoint.exists_two_points (𝟙 (Sp K)) _ hD x x
  obtain ⟨b, hb, hc⟩ := NoBasePoint.exists_two_points (𝟙 (Sp K)) _ hD x (a⁻¹ * x)
  rw [← _root_.mul_assoc] at hc
  choose i hi using fun k : Fin 4 => exists_chart hN ((![a, b, b⁻¹ * a⁻¹, 1] k).left p)
  obtain ⟨w, hw⟩ := SepPoints.exists_gen_three hN t ht (π ≫ a) (π ≫ b) (π ≫ (b⁻¹ * a⁻¹)) (𝟙 P.A) 1
    (by rw [pow_one, ← MonObj.comp_mul, ← MonObj.comp_mul]; simp) i (fun k z => by
      have e : (![(π ≫ a).left, (π ≫ b).left, (π ≫ (b⁻¹ * a⁻¹)).left, (1 : P.A ⟶ P.A).left] k) =
          π.left ≫ (![a, b, b⁻¹ * a⁻¹, 1] k).left := by
        fin_cases k
        · rfl
        · rfl
        · rfl
        · exact congrArg (fun q : P.A ⟶ P.A => q.left) (MonObj.comp_one π).symm
      rw [e, Scheme.Hom.comp_apply, spec_pt_eq (k := K) (π.left z) p]
      exact hi k)
  have hw' : UnitAt N _ _ y := ⟨genSec w hw, fun J hJ => by
    rw [sval_genSec w hw _ y hJ]; exact Units.isUnit _⟩
  refine exists_mem_of_unitAt hN (UnitAt.congr hN (formEq_of_add fun U _ hh => ?_)
    (((hw'.mul (good a (ha p))).mul (good b (hb p))).mul (good _ (hc p))))
  simp [Fin.sum_univ_succ]
  module

end GlobalTheory.EffectiveCube
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSectionsGenerateSquareBundleStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sections_generate_square_bundle : ∀ (O K : Type) [CommRing O] [IsDomain O] [ValuationRing O] [Field K] [IsAlgClosed K] [Algebra O K] [IsFractionRing O K] (A : Over (Sp O)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ H : LB A.left, H.IsLB → Triv (Theta A H) → ∀ s : LB.Sec H, (∃ x ∈ Out.nonzeroLocus s, A.hom x = IsLocalRing.closedPoint O) → ∃ (m : ℕ) (u : Fin (m + 1) → LB.Sec (pw H 2)), ⨆ i, Out.nonzeroLocus (u i) = ⊤ := by
  first | exact @GlobalTheory.SquareGenerated.exists_secs_sq_generate | exact GlobalTheory.SquareGenerated.exists_secs_sq_generate | (intros; apply GlobalTheory.SquareGenerated.exists_secs_sq_generate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjRigidAnyBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem obj_rigid_any_base : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' : Type) [CommRing B] [CommRing B'] (b : Base l B) (b' : Base l B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (o : Obj D l b s) (o' : Obj D l b' s') (f : S' ⟶ S), ∀ m m' : SABMap o'.t o.t f, (∀ a, ∃ σ, (o'.eta a).left ≫ m.φ = σ ∧ (o'.eta a).left ≫ m'.φ = σ) → m.φ = m'.φ :=
  fun hL => obj_rigid_of_pol hL obj_isAbelianScheme_dim_rigidified_sym

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjRigidClosed
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem obj_rigid_closed : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' : Type) [CommRing B] [CommRing B'] (b : Base l B) (b' : Base l B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (o : Obj D l b s) (o' : Obj D l b' s') (f : S' ⟶ S), (IsReduced S' ∨ IsLocallyNoetherian S') → ∀ m m' : SABMap o'.t o.t f, (∀ a, ∃ σ, (o'.eta a).left ≫ m.φ = σ ∧ (o'.eta a).left ≫ m'.φ = σ) → m.φ = m'.φ :=
  fun hL E _ _ _ H D l B B' _ _ b b' S S' s s' o o' f _ =>
    obj_rigid_of_pol hL obj_isAbelianScheme_dim_rigidified_sym E H D l B B' b b' S S' s s' o o' f

end GlobalTheory
end

