import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2296
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2357
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3300
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2679
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0631
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0706
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0708
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2684
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0836
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2681
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2830
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3232
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2588
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2790
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2867
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SamePolarisedDataOfIdempotentFactorUniformisatio
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RosatiAdjointAbelianPartAndClassifyingMapLinear
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3042
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3100
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3043
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3160
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3304
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2972
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2150
import Development.AbelianVarietyTheory.Definitions.Foundations.CanonicalExponents
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0062
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0802
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0585
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3301
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2292
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2897
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2196
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0018
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3146
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3102
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3122
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3131
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3189
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3108
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3303
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0085
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamOfHyp
section
set_option autoImplicit false

namespace GlobalTheory

theorem abelianDeRham_of_crystallineSmoothLift : GlobalTheory.Published.CrystallineSmoothLift →
    GlobalTheory.Published.AbelianHodgeDeRham → GlobalTheory.Published.CubeTheorem → GlobalTheory.Published.DualAbelianScheme →
    GlobalTheory.Published.PoincareDeRhamDuality → GlobalTheory.Published.AbelianDeRham := by
  intro hL hH hC hD hP
  obtain ⟨⟨hfree, hhodge, hbc⟩, hcrys⟩ := GlobalTheory.T.crystallineDeRham_abelianStructure_of_statements hL hH
  have hF : GlobalTheory.Published.AbelianDeRham.Free := GlobalTheory.AbelianPrim.abelianDeRham_free hfree
  exact ⟨hF, hhodge, hbc,
    GlobalTheory.Published.AbelianDeRham.rigid_of_free_of_crystallineDeRham hF hcrys,
    GlobalTheory.T.abelianDeRham_poincareDuality_of_cube_dual hC hD hP hF⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeSpecialFibreCohomologyLiftArtinian
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh

theorem artinian_pullHO_surjective : ∀ (R : Type) [CommRing R] [IsArtinianRing R] [IsLocalRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (k : Type) [Field k] (σ : R →+* k), Function.Surjective σ → ∀ (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp k) (ψ : X₀ ⟶ A.left) (w : IsPullback ψ s₀ A.hom (spMap σ)), Function.Surjective (pullHO1 w.w) ∧ Function.Surjective (pullHO2 w.w) := by
  intro R _ _ _ A _ g hA hsm k _ σ hσ X₀ s₀ ψ w
  have FF := GlobalTheory.T.abelian_over_field_axes_wedge
  have key : ∀ n : ℕ, ∀ (R : Type) [CommRing R] [IsArtinianRing R] [IsLocalRing R], Module.length R R ≤ n →
      ∀ (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
        (∀ (k : Type) [Field k] (σ : R →+* k), Function.Surjective σ → ∀ (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp k) (ψ : X₀ ⟶ A.left) (w : IsPullback ψ s₀ A.hom (spMap σ)), Function.Surjective (pullHO1 w.w)) ∧ StructureSheafH1Primitive A := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro R _ _ _ hlen A _ g hA hsm
      by_cases hF : IsField R
      · refine ⟨?_, GlobalTheory.T.primitive_of_axes_vanishing R A (FF R hF A g hA hsm).1⟩
        intro k _ σ hσ X₀ s₀ ψ w
        letI := hF.toField
        exact GlobalTheory.T.pull_h1_surjective_bijective_fibre R k σ ⟨σ.injective, hσ⟩ _ _ X₀ s₀ ψ w
      · obtain ⟨t, ht0, htm, hlt⟩ := (GlobalTheory.T.isArtinianLocal_length_finite_and_exists_socle_elem R).2 hF
        obtain ⟨n0, hn0⟩ := (GlobalTheory.T.isArtinianLocal_length_finite_and_exists_socle_elem R).1
        have htop : Ideal.span {t} ≠ ⊤ := by
          intro h
          have hu : IsUnit t := by simpa [Ideal.span_singleton_eq_top] using h
          apply hF
          have hm : IsLocalRing.maximalIdeal R = ⊥ := by
            rw [eq_bot_iff]; intro a ha
            have := htm a ha
            simpa [hu.mul_left_eq_zero] using this
          exact (IsLocalRing.isField_iff_maximalIdeal_eq).2 hm
        haveI : Nontrivial (R ⧸ Ideal.span {t}) := Ideal.Quotient.nontrivial_iff.2 htop
        haveI : IsLocalRing (R ⧸ Ideal.span {t}) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
        obtain ⟨n1, hn1⟩ := (GlobalTheory.T.isArtinianLocal_length_finite_and_exists_socle_elem (R ⧸ Ideal.span {t})).1
        have hlt' : n1 < n := by
          rw [hn0, hn1] at hlt; rw [hn0] at hlen
          exact lt_of_lt_of_le (by exact_mod_cast hlt) (by exact_mod_cast hlen)
        have IH := ih n1 hlt' (R ⧸ Ideal.span {t}) (le_of_eq hn1)
        exact ⟨GlobalTheory.T.artinian_lift_axes_wedge R t _ (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective (Ideal.mk_ker) ht0 htm FF
            (fun B _ g hB hs ↦ IH B g hB hs) A g hA hsm,
          GlobalTheory.T.artinian_lift_axes_wedge_local R t _ (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective (Ideal.mk_ker) ht0 htm FF
            (fun B _ g hB hs ↦ (IH B g hB hs).2) A g hA hsm⟩
  obtain ⟨n, hn⟩ := (GlobalTheory.T.isArtinianLocal_length_finite_and_exists_socle_elem R).1
  have h1 := (key n R (le_of_eq hn) A g hA hsm).1 k σ hσ X₀ s₀ ψ w
  exact ⟨h1, GlobalTheory.T.surjective_pullHO2_of_pullHO1 _ _ _ _ _ _ _ _ w.w h1 (GlobalTheory.T.closed_fibre_pull_h1_abelian FF R A g hA hsm k σ X₀ s₀ ψ w)⟩

end GlobalTheory.AbCoh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointAbelianPartsOfUniformisedRetract
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData

noncomputable section

namespace GlobalTheory.Mum.PowData

theorem cls_lam_proj {S : Scheme.{0}} {H : Over S} [GrpObj H] {L : LB H.left} (hL : L.IsLB) (h : (abelian₂ H L).IsLB) :
    cls (abelian₂ H L) h = lam (cls L hL) (fst H H) (snd H H) :=
  cls_cube_two hL (fst H H) (snd H H) h

theorem lbIso_iff_lam {S : Scheme.{0}} {H₁ H₂ : Over S} [GrpObj H₁] [GrpObj H₂] {L₁ : LB H₁.left} {L₂ : LB H₂.left}
    (h₁ : L₁.IsLB) (h₂ : L₂.IsLB) (f g : H₁ ⟶ H₂) :
    LBIso (abelian₂ H₁ L₁) ((abelian₂ H₂ L₂).pull (lift (fst H₁ H₁ ≫ f) (snd H₁ H₁ ≫ g) : G2 H₁ ⟶ G2 H₂).left) ↔
      ∀ (T : Over S) (x z : T ⟶ H₁), lam (cls L₁ h₁) x z = lam (cls L₂ h₂) (x ≫ f) (z ≫ g) := by
  have hA : (abelian₂ H₁ L₁).IsLB := LB.isLB_linComb h₁ _ _
  have hB : (abelian₂ H₂ L₂).IsLB := LB.isLB_linComb h₂ _ _
  rw [← cls_eq_iff hA (pull_isLB hB _), cls_pull hB, cls_lam_proj h₁, cls_lam_proj h₂, pull_lam, lift_fst, lift_snd]
  constructor
  · intro h T x z
    have e := congrArg (pull (lift x z).left) h
    simpa only [pull_lam, lift_fst_assoc, lift_snd_assoc, lift_fst, lift_snd] using e
  · intro h
    exact h _ _ _

theorem lam_of_rosatiGen {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] {M : LB B.left} (hM : M.IsLB)
    {a b : B ⟶ B} (u : LB.Gen (LB.LinComb M (rosatiφ B a b) rosatiε)) (hu : u.IsGen) {T : Over S} (x y : T ⟶ B) :
    lam (cls M hM) (x ≫ a) y = lam (cls M hM) x (y ≫ b) := by
  unfold lam
  rw [GlobalTheory.EndRosati.cls_of_rosati hM u hu x y]

end GlobalTheory.Mum.PowData

namespace GlobalTheory.Mum.PowData

set_option maxHeartbeats 1000000 in

theorem adjCls_abelianPart : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D₀ : DegData R (maximalIdeal R)) (A A₀ : PolAV (Sp (FractionRing R))) (G G₀ : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G → IsSemiAbelian G₀ → ∀ (U : Unif (maximalIdeal R) D A G) (U₀ : Unif (maximalIdeal R) D₀ A₀ G₀), ∀ (q r : G ⟶ G₀) (inc j : G₀ ⟶ G), IsMonHom q → IsMonHom r → IsMonHom inc → IsMonHom j → inc ≫ q = 𝟙 G₀ → j ≫ r = 𝟙 G₀ → AdjCls (cls U.LG.L U.LG.isLB) (cls U₀.LG.L U₀.LG.isLB) q j → AdjCls (cls U.LG.L U.LG.isLB) (cls U₀.LG.L U₀.LG.isLB) r inc → ∀ (qB : D.toPre.P.A ⟶ D₀.toPre.P.A) (jB : D₀.toPre.P.A ⟶ D.toPre.P.A), IsMonHom qB → IsMonHom jB → Over₀ U.toUnifPre U₀.toUnifPre q qB → Over₀ U₀.toUnifPre U.toUnifPre j jB → AdjCls (cls D.toPre.P.L D.toPre.P.isLB) (cls D₀.toPre.P.L D₀.toPre.P.isLB) qB jB := by
  intro R _ _ _ hR D D₀ A A₀ G G₀ _ _ _ _ hG hG₀ U U₀ q r inc j hq hr hinc hj hiq hjr hqj hri qB jB hqB hjB hOq hOj
  obtain ⟨hAdm, hCZ⟩ := hR
  obtain ⟨incB, hincB, hOinc⟩ := exists_abelian_hom R _ hAdm D₀ D A₀ A G₀ G U₀.toUnifPre U.toUnifPre inc hinc
  obtain ⟨rB, hrB, hOr⟩ := exists_abelian_hom R _ hAdm D D₀ A A₀ G G₀ U.toUnifPre U₀.toUnifPre r hr
  have hjrB : jB ≫ rB = 𝟙 _ :=
    (over₀_onTorus_unique R _ hAdm D₀ D₀ A₀ A₀ G₀ G₀ U₀.toUnifPre U₀.toUnifPre (j ≫ r)).1 _ _
      (FactorPol.over_comp hOj hOr) (by rw [hjr]; exact FactorPol.over_id)

  have h1 : ∀ (T : Over (Sp R)) (x z : T ⟶ G₀),
      lam (cls U₀.LG.L U₀.LG.isLB) x z = lam (cls U.LG.L U.LG.isLB) (x ≫ inc) (z ≫ j) := by
    intro T x z
    rw [hqj T (x ≫ inc) z, Category.assoc, hiq, Category.comp_id]
  have hI := GlobalTheory.T.mumfordBundle_iso_along_homs_descends_abelianPart R hAdm D₀ D A₀ A G₀ G hG₀ hG U₀ U inc j incB jB hinc hj hincB hjB hOinc hOj
    ((lbIso_iff_lam U₀.LG.isLB U.LG.isLB inc j).2 h1)
  have h1B := (lbIso_iff_lam D₀.toPre.P.isLB D.toPre.P.isLB incB jB).1 hI

  have hadj : ∀ (T : Over (Sp R)) (x z : T ⟶ G),
      lam (cls U.LG.L U.LG.isLB) (x ≫ q ≫ inc) z = lam (cls U.LG.L U.LG.isLB) x (z ≫ r ≫ j) := by
    intro T x z
    rw [lam_comm, ← Category.assoc x, hri T z (x ≫ q), lam_comm, ← hqj T x (z ≫ r), Category.assoc]
  have hiso : LBIso (cubeLB G ![fst G G ≫ (q ≫ inc), snd G G] U.LG.L)
      (cubeLB G ![fst G G, snd G G ≫ (r ≫ j)] U.LG.L) := by
    have ha : (cubeLB G ![fst G G ≫ (q ≫ inc), snd G G] U.LG.L).IsLB := LB.isLB_linComb U.LG.isLB _ _
    have hb : (cubeLB G ![fst G G, snd G G ≫ (r ≫ j)] U.LG.L).IsLB := LB.isLB_linComb U.LG.isLB _ _
    refine (cls_eq_iff ha hb).1 ?_
    rw [cls_cube_two U.LG.isLB _ _ ha, cls_cube_two U.LG.isLB _ _ hb]
    exact hadj _ _ _

  haveI : IsMonHom U.gen.hom := U.gen_hom
  have hext : ∀ a : G ⟶ G, (Over.pullback (jK R)).map a ≫ U.gen.hom =
      U.gen.hom ≫ (U.gen.inv ≫ (Over.pullback (jK R)).map a ≫ U.gen.hom) := fun a => by simp
  obtain ⟨E, hE, -⟩ := exists_degenerationEndomorphism_of_admissibleBase R _ hAdm D A G hG U (q ≫ inc) _ inferInstance inferInstance (hext _)
  obtain ⟨E', hE', -⟩ := exists_degenerationEndomorphism_of_admissibleBase R _ hAdm D A G hG U (r ≫ j) _ inferInstance inferInstance (hext _)
  have hros := (rosatiAdjoint_and_linear_of_admissibleBase R _ hAdm D A G hG U E E' (by rw [hE, hE']; exact hiso)).2.1
  have hEB : E.aB = qB ≫ incB :=
    (over₀_onTorus_unique R _ hAdm D D A A G G U.toUnifPre U.toUnifPre E.aG).1 _ _ (lin_of_endU E).1.2.2.1
      (by rw [hE]; exact FactorPol.over_comp hOq hOinc)
  have hE'B : E'.aB = rB ≫ jB :=
    (over₀_onTorus_unique R _ hAdm D D A A G G U.toUnifPre U.toUnifPre E'.aG).1 _ _ (lin_of_endU E').1.2.2.1
      (by rw [hE']; exact FactorPol.over_comp hOr hOj)
  haveI := E.homB
  haveI := E'.homB
  obtain ⟨u, hu, -⟩ := exists_ros GlobalTheory.firstFiveLaws.1.globalFns D.toPre.P.isAb D.toPre.P.isLB E.aB E'.aB hros
  intro T x z
  rw [h1B T (x ≫ qB) z, Category.assoc, ← hEB, lam_of_rosatiGen D.toPre.P.isLB u hu, hE'B, Category.assoc,
    reassoc_of% hjrB]

end GlobalTheory.Mum.PowData
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointUniqueAdditiveScalar
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar.AdjCalc

variable {K : Type} [Field K]

theorem comp_zpow' {X Y G : Over (Sp K)} [GrpObj G] (f : X ⟶ Y) (g : Y ⟶ G) (m : ℤ) :
    f ≫ g ^ m = (f ≫ g) ^ m :=
  map_zpow (MonoidHom.mk' (fun g : Y ⟶ G => f ≫ g) (MonObj.comp_mul f)) g m

theorem isAdj_pt {A B : AbVar K} {c : Pic A.X.left} {d : Pic B.X.left} {f : A ⟶ B} {n : ℤ} {h : B ⟶ A}
    (H : IsAdj c d f n h) {Y : Over (Sp K)} (x : Y ⟶ A.X) (y : Y ⟶ B.X) :
    n • lam d (x ≫ f.hom) y = lam c x (y ≫ h.hom) := by
  have H' := congrArg (CechPic.pull (lift x y).left) H
  rw [map_zsmul, (GlobalTheory.T.abelianVarietyMumfordClass_symm_natural_additive K A A c c c (𝟙 A) _ Y (lift x y) _ _).2.1,
    (GlobalTheory.T.abelianVarietyMumfordClass_symm_natural_additive K B B d d d (𝟙 B) _ Y (lift x y) _ _).2.1] at H'
  simpa only [lift_fst_assoc, lift_snd_assoc, lift_fst, lift_snd] using H'

end GlobalTheory.AV.AbVar.AdjCalc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArcZeroCuspSec
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
open GlobalTheory.ShFam GlobalTheory.ShFam.BdArc GlobalTheory.Toroidal

noncomputable section

namespace GlobalTheory.KoecherArc

theorem tendsto_val {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β)
    {σ : c.F →+* ℂ} {N : ℕ} {U : Unf Xo c σ N} (hσ : GoodEmb c σ) (hU : IsUnf U) (la : ∀ k, Wt (U.X k).Ψ N)
    (hχ : ∀ k, ∀ γ ∈ (U.X k).Γ, (U.X k).χ (la k) γ = 1) {e : Ix Dw → ℤ} (he : e none = 0) {g : Rul Xo c}
    (hg : g ∈ AllWt.secZ Xo c e) (hS : ∀ k, rdU U g k ∈ (U.X k).SS (la k)) {A : Type} [CommRing A] {φ : c.F →+* A}
    {x : Sp A ⟶ gen Z} (fr : EigFrame Z φ (x ≫ genι Z)) {ψ : ℂ → (A →+* ℂ)} {r : ℝ} {y : ℂ → FrPt Xo c (CAt σ)}
    (hb : IsBdArc Z σ φ x ψ r) (hm : ∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → Matches fr (ψ u) (y u)) (p q : A)
    (hpq : ∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → ψ u q ≠ 0 ∧ toC (evR Xo c g (y u)) * ψ u q = ψ u p) :
    Tendsto (fun u => toC (evR Xo c g (y u))) (𝓝[≠] 0) (𝓝 0) := by
  haveI : IsLocalRing (CAt σ) := inferInstanceAs (IsLocalRing ℂ)
  obtain ⟨k, T, M₀, γ₀, xx, hT, hO₀, hL⟩ := GlobalTheory.T.exists_holomorphicFrameOrbit_lift_of_arc E H Dw l Xo c O β Z σ N U A φ x fr ψ r y hσ hU hb.1 hm
  obtain ⟨M, γ, hO, hγ⟩ := GlobalTheory.T.exists_holomorphicFrameOrbit_unipotent_order_two E N _ T M₀ γ₀ xx hO₀
  have hne : γ ≠ 1 := by
    rintro rfl
    obtain ⟨x₀, hx₀, x', h1, h2⟩ := GlobalTheory.T.trivial_monodromy_orbit_converges_symmetric_domain E N _ T M xx hO
    exact GlobalTheory.T.boundary_arc_lift_not_converges_symmetric_domain E H Dw l Xo c O β Z σ N U A φ x fr ψ r y k T xx hσ hU hb hm hL x₀ hx₀ x' h1 h2
  obtain ⟨ξ, c', hξ, hc', ht⟩ := GlobalTheory.T.holomorphicFrameOrbit_isotropic_vector_short E N _ T M γ xx hO hγ hne
  obtain ⟨m, v, Lp, Lm, hlim⟩ :=
    GlobalTheory.T.exists_arcLift_periods_tendsto_span E H Dw l Xo c O β Z σ N U A φ x fr ψ r y k T M γ xx hσ hU hb.1 hm hO hL
  have hper := GlobalTheory.T.eigenframe_specialization_uniform_bound E H Dw l Xo c O β Z σ N U A φ x fr ψ r y k T M γ xx hσ hU hb.1 hm hO hL
  obtain ⟨C', B, hn⟩ := GlobalTheory.T.normFactor_inv_le_pow_holomorphicOrbit_periodBound E N _ T M γ xx (la k) m v Lp Lm hO hlim hper
  have hp := tendsto_cusp (hS k) hO.2.2.2.1 hξ hc' ht hn
  have hsec := (hS k).1.1
  obtain ⟨hM, hΓ, hdiff, hdom, hperd⟩ := hO
  have hγd : ∀ w : ℂ, T < w.im → lact γ (xx w) ∈ (U.X k).dom := fun w hw =>
    GlobalTheory.MajInv.lact_mem_dom _ ((U.X k).Γ_stab γ hΓ) (hdom w hw)
  refine GlobalTheory.T.meromorphic_germ_vanishes_of_periodic_exp_modulus (fun w => rdU U g k (xx w)) (fun _ => 0) _ (fun u => ψ u p) (fun u => ψ u q) T r M 1 1 hM
    one_pos (one_pow 1) hb.1.1.1 (hsec.1.comp hdiff hdom) (differentiableOn_const 0) (fun w hw => ?_) hp
    (hb.1.1.2 p) (hb.1.1.2 q) hpq
  obtain ⟨b, hb1, hb2, hb3⟩ := hperd w hw
  obtain ⟨h, hl⟩ := hL w hw
  refine ⟨?_, rfl, ?_⟩
  · simp only [hb3]
    rw [hsec.2.1 _ (hγd w hw) b hb1, hsec.2.2 γ hΓ _ (hdom w hw), hχ k γ hΓ]
    simp [ReciprocityTheory.ChartRestriction.G.FD.bchar, hb2]
  · rw [Complex.exp_zero, norm_one, mul_one]
    have rd : rdU U g k (xx w) = toC (evR Xo c g (U.un k ⟨xx w, h⟩)) := dif_pos h
    show ‖toC (evR Xo c g (y (eTwoPi w)))‖ = ‖rdU U g k (xx w)‖
    rw [rd, GlobalTheory.ShFam.KeyRel.evR_sameLie he hg hl]

theorem isBdArc_mono {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
    {σ : c.F →+* ℂ} {A : Type} [CommRing A] {φ : c.F →+* A} {x : Sp A ⟶ gen Z} {ψ : ℂ → (A →+* ℂ)} {r ρ : ℝ}
    (h : IsBdArc Z σ φ x ψ r) (hρ : 0 < ρ) (hρr : ρ ≤ r) : IsBdArc Z σ φ x ψ ρ :=
  ⟨⟨⟨hρ, fun a => (h.1.1.2 a).mono (Metric.ball_subset_ball hρr)⟩, h.1.2.1,
    fun u hu => h.1.2.2 u (Metric.ball_subset_ball hρr hu)⟩, h.2.1, fun u hu => h.2.2 u (Metric.ball_subset_ball hρr hu)⟩

end GlobalTheory.KoecherArc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchIntersectionCombinationLogNormStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arch_intersection_combination_log_norm : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsRegVar p D) (ι : Type) [Fintype ι] (L : ι → HermLB p) (N : HermLB p)
    (r : N.B.ι → X.functionFieldˣ) (hr : IsRatSec N.B r) (g : ∀ σ : k →+* ℂ, CxPts p σ → ℝ),
    (∀ σ, ∀ y ∈ offSupp p σ (N.div hr), logNorm (N.φ σ) r y = g σ y) →
    ∀ (s : Finset (ι → ℤ)) (c : (ι → ℤ) → ℝ),
      ∑ n ∈ s, c n * (comb L n).archInt N D hr =
        ∑ᶠ σ : k →+* ℂ, wInt (hX.atlas σ) (g σ) (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) (∑ n ∈ s, c n • lin (fun i => (n i : ℝ)) ^ D)) := by
  first | exact @GlobalTheory.ChernPoly.archInt_sum_eq_wInt | exact GlobalTheory.ChernPoly.archInt_sum_eq_wInt | (intros; apply GlobalTheory.ChernPoly.archInt_sum_eq_wInt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHeightProjectionFormulaInductiveStep
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false

noncomputable section

open GlobalTheory.TwistTop

namespace GlobalTheory.ProjStep

theorem archInt_refines {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    {N L : HermLB p} {ρ : N.B.ι → L.B.ι} (h : Refines N L ρ 0) {r : L.B.ι → X.functionFieldˣ}
    (hr : IsRatSec L.B r) (e : ℕ) :
    N.archInt N e (h.isRatSec hr) = L.archInt L e hr := by
  unfold HermLB.archInt
  rw [h.div hr]
  refine finsum_congr fun σ => ?_
  rw [h.chernInt]
  exact Weight.chernInt_congr (isOpen_offSupp _).measurableSet fun y hy => h.logNorm hr hy

end GlobalTheory.ProjStep

namespace GlobalTheory.ProjStep

theorem main : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D E : ℕ), IsArithVar p D → IsArithVar q E → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (L : HermLB p) (h : X → ℝ) (h' : Y → ℝ), L.IsArithHeight h → (L.pull π hπ).IsArithHeight h' → ∀ (y : Y) (e : ℕ), CharZero Γ(clo y, ⊤) → HasDim y (e + 1 + 1) → (∀ w : Y, HasDim w (e + 1) → h' w = (π.residueDegree w : ℝ) * h (π w)) → h' y = (π.residueDegree y : ℝ) * h (π y) := by
  intro k _ X Y p q D E hX hY π hπ L h h' H H' y e hc hy hrec
  have hAX : IsAmb p := isAmb_of_isArithVar hX
  have hAY : IsAmb q := isAmb_of_isArithVar hY
  have := hX.isNoetherian
  have := hY.isNoetherian
  obtain ⟨hbdX, -, -, -, hsubX, hgenX⟩ := GlobalTheory.T.hasPointClosureDim_basic_projArithAmbient k X p hAX
  obtain ⟨-, -, -, -, hsubY, hgenY⟩ := GlobalTheory.T.hasPointClosureDim_basic_projArithAmbient k Y q hAY
  obtain ⟨g, hgc, hgη, hgdeg⟩ := GlobalTheory.T.exists_dominant_restriction_pointClosures X Y π y

  have hdW : topologicalKrullDim (clo y) = ((e + 1 + 1 : ℕ) : WithBot ℕ∞) := by
    refine (hgenY (clo y) (e + 1 + 1)).1 ((hsubY (clo y) (cloι y) _ _).1 ?_)
    rw [cloι_genericPoint]; exact hy
  have hcZ : CharZero Γ(clo (π y), ⊤) := g.appTop.hom.charZero
  have hg1 : g ≫ cloι (π y) ≫ p = cloι y ≫ q := by
    rw [← Category.assoc, hgc, Category.assoc, hπ]
  have hC : (g ≫ cloι (π y)) ≫ p = cloι y ≫ q := by rw [Category.assoc]; exact hg1
  have hη' : g (genericPoint (clo y)) ⤳ genericPoint (clo (π y)) := hgη ▸ specializes_rfl
  have happ (w : clo y) : π (cloι y w) = cloι (π y) (g w) := by
    have := congrArg (fun f : clo y ⟶ X => f w) hgc
    simpa using this.symm
  have hδ : g.residueDegree (genericPoint (clo y)) = π.residueDegree y := by
    rw [hgdeg, cloι_genericPoint]

  obtain ⟨r, hr⟩ := exists_isRatSec (L.restr (cloι (π y))).isLB
  have hr1 := MultPull.isRatSec_pull_map g hη' hr
  have ref1 := L.refines_pull_comp (cloι (π y)) rfl g hg1 hC
  have hrC := ref1.isRatSec hr1
  obtain ⟨ρ, ref2⟩ : ∃ ρ, Refines ((L.pull π hπ).restr (cloι y)) (L.pull (g ≫ cloι (π y)) hC) ρ 0 := by
    have key : ∀ (f : clo y ⟶ X) (hf : f ≫ p = cloι y ≫ q), f = cloι y ≫ π →
        ∃ ρ, Refines ((L.pull π hπ).restr (cloι y)) (L.pull f hf) ρ 0 := by
      rintro f hf rfl
      exact ⟨_, L.refines_pull_pull π hπ (cloι y) rfl hf⟩
    exact key _ hC hgc
  have hrA := ref2.isRatSec hrC
  obtain ⟨-, hrecW⟩ := H'.recursion_one (cloι y) hc (by omega : 1 ≤ e + 1) hdW hrA
  rw [cloι_genericPoint] at hrecW
  have ediv : ((L.pull π hπ).restr (cloι y)).div hrA = (((L.restr (cloι (π y))).pull g hg1)).div hr1 :=
    (ref2.div hrC).trans (ref1.div hr1)
  have earch : ((L.pull π hπ).restr (cloι y)).archInt ((L.pull π hπ).restr (cloι y)) (e + 1) hrA =
      ((L.restr (cloι (π y))).pull g hg1).archInt ((L.restr (cloι (π y))).pull g hg1) (e + 1) hr1 :=
    (archInt_refines ref2 hrC (e + 1)).trans (archInt_refines ref1 hr1 (e + 1))
  have hsum : ∑ᶠ w, ((((L.pull π hπ).restr (cloι y)).div hrA).mult w : ℝ) * h' (cloι y w) =
      (π.residueDegree y : ℝ) * ∑ᶠ z, (((L.restr (cloι (π y))).div hr).mult z : ℝ) * h (cloι (π y) z) := by
    rw [ediv, ← hδ]
    refine Eq.trans (finsum_congr fun w => ?_) (GlobalTheory.T.finsum_mult_pullback_rationalSection_pushforward k (clo (π y)) (clo y) (cloι (π y) ≫ p) (cloι y ≫ q)
      (hAX.sub _) (hAY.sub _) g hg1 hgη (L.restr (cloι (π y))).B (L.restr (cloι (π y))).isLB r hr
      (fun z => h (cloι (π y) z)))
    by_cases hm : ((((L.restr (cloι (π y))).pull g hg1)).div hr1).mult w = 0
    · have hm' : ((((L.restr (cloι (π y))).pull g hg1)).div hr1).mult w = 0 := hm
      rw [hm, Int.cast_zero, zero_mul]
      exact (mul_eq_zero_of_left (Int.cast_eq_zero.2 hm) _).symm
    · have hco := CartierDiv.coheight_eq_one_of_mult_ne_zero hm
      have hd1 := ((GlobalTheory.T.coheight_one_iff_pointClosure_dim_projArith k (clo y) (cloι y ≫ q) (hAY.sub _) (e + 1) hdW).1 w).1 hco
      have hd2 := (hsubY (clo y) (cloι y) w (e + 1)).2 hd1
      rw [hrec _ hd2, happ, hgdeg]
      rfl

  obtain ⟨m, hm⟩ := hbdX
  obtain ⟨d', -, hd'⟩ := hm (π y)
  obtain ⟨hle, hiff⟩ := GlobalTheory.T.pointClosureDim_le_and_residueDegree_ne_zero_iff k X Y p q hAX hAY π hπ y (e + 1 + 1) d' hy hd'
  have hdZ : topologicalKrullDim (clo (π y)) = (d' : WithBot ℕ∞) := by
    refine (hgenX (clo (π y)) d').1 ((hsubX (clo (π y)) (cloι (π y)) _ _).1 ?_)
    rw [cloι_genericPoint]; exact hd'
  have hWv := hY.of_isClosedImmersion (cloι y) hc hdW
  rw [hsum, earch] at hrecW
  by_cases h0 : π.residueDegree y = 0
  ·
    have hlt : d' < e + 1 + 1 := lt_of_le_of_ne hle fun h1 => hiff.2 h1.symm h0
    have hd0 : d' ≠ 0 := fun h2 => hX.dim_ne_zero (cloι (π y)) hcZ (by rw [hdZ, h2]; rfl)
    obtain ⟨e0, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd0
    have hZv0 := hX.of_isClosedImmersion (cloι (π y)) hcZ (e := e0) hdZ
    have hzero (σ : k →+* ℂ) (ε : ℤˣ) :
        (((L.restr (cloι (π y))).pull g hg1).φ σ).chernPart (e + 1) ε = 0 :=
      GlobalTheory.T.chernForm_topPower_pullback_smaller_dim_eq_zero k (clo (π y)) (clo y) (cloι (π y) ≫ p) (cloι y ≫ q) e0 (e + 1) hZv0 hWv (by omega) g hg1 hgη
        (L.restr (cloι (π y))) σ ε
    have harch0 : ((L.restr (cloι (π y))).pull g hg1).archInt ((L.restr (cloι (π y))).pull g hg1) (e + 1) hr1 = 0 := by
      unfold HermLB.archInt Weight.chernInt
      simp [hzero]
    rw [harch0, h0] at hrecW
    rw [hrecW, h0]
    simp
  ·
    have hde : d' = e + 1 + 1 := (hiff.1 h0).symm
    subst hde
    have hZv := hX.of_isClosedImmersion (cloι (π y)) hcZ hdZ
    obtain ⟨-, hrecZ⟩ := H.recursion_one (cloι (π y)) hcZ (by omega : 1 ≤ e + 1) hdZ hr
    rw [cloι_genericPoint] at hrecZ
    have hpa := GlobalTheory.T.archimedeanIntegral_pull_mul_degree k (clo (π y)) (clo y) (cloι (π y) ≫ p) (cloι y ≫ q) (e + 1) hZv hWv g hg1 hgη
      (hδ ▸ h0) (L.restr (cloι (π y))) (L.restr (cloι (π y))) r hr
    rw [hδ] at hpa
    rw [hrecW, hpa, hrecZ]
    ring

end GlobalTheory.ProjStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalFamilyBundleBirigidSymmetricStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonicalFamily_bundle_birigid_symmetric : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (Q : Data R) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), Canon Q G P → IsBiRig G P := by
  first | exact @GlobalTheory.Mum.canon_isBiRig | exact GlobalTheory.Mum.canon_isBiRig | (intros; apply GlobalTheory.Mum.canon_isBiRig <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTorsionGeometricPointsEqPowTwoDimStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_torsion_geometricPoints_eq_pow_two_dim : ∀ (K : Type) [Field K] (A : AbVar K) (n : ℕ), (n : K) ≠ 0 → Nat.card {x : A.Pt // x ^ n = 1} = n ^ (2 * A.dim) := by
  first | exact @GlobalTheory.AV.AbVar.card_torsion_pt | exact GlobalTheory.AV.AbVar.card_torsion_pt | (intros; apply GlobalTheory.AV.AbVar.card_torsion_pt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormFieldDbarCohomologousTwoConnectionsStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernFormField_dbarCohomologous_two_connections : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) (r : Type) [Fintype r] [DecidableEq r] (G G' : M → M → Matrix r r ℂ), IsGramPair A G G' → ∀ j, DbarCoh A (chernFld A G j) (chernFld A G' j) := by
  first | exact @GlobalTheory.ChernCalc.dbarCoh_chernFld | exact GlobalTheory.ChernCalc.dbarCoh_chernFld | (intros; apply GlobalTheory.ChernCalc.dbarCoh_chernFld <;> assumption)
end

