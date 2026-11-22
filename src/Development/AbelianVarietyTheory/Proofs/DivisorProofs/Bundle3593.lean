import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOfPoint
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2505
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2326
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2356
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymLam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0945
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2310
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2474
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2588
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2901
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0130
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0086
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamPolarizationFormPrimitive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2871
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0005
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsIsGenOfUniqueFactorizationMonoid
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0925
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3539
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2836
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3586
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2749
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0598
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0294
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2765
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2717
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2691
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3002
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3584
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3142
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3117
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3060
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2770
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2773
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2913
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2714
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2993
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2981
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3108
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3587
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3585
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1547

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigLBCubical
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolBundleLoc

open GlobalTheory.PolRoot GlobalTheory.CechPic GlobalTheory.LamOfDouble

theorem exists_rigLB_cubical (R : Type) [CommRing R] [IsLocalRing R] (B : Over (Sp R)) [GrpObj B] [IsCommMonObj B]
    (hB : IsAbelianScheme B) (L : LB B.left) (hL : L.IsLB) : ∃ M : RigLB B, M.L = L ∧ Nonempty (CubicalStr B M) := by
  have hR : Out.Rigidified B L := GlobalTheory.LB.exists_isGen_of_isLocalRing (R := R) (pull_isLB hL _)
  exact GlobalTheory.Moduli.cubicalStr_of_triv_theta GlobalTheory.abelianSchemeLaws_all.1 _ B hB L hL hR
    (GlobalTheory.HodgeWeil.triv_theta GlobalTheory.CubeTop.cubeTheorem hB hL)

theorem exists_descent_two {K : Type} [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A]
    (hA : IsAbelianScheme A) {M : LB A.left} (hM : M.IsLB)
    (H : LBIso (M.pull (pullback.fst ((𝟙 A) ^ 2 : A ⟶ A).left ((𝟙 A) ^ 2 : A ⟶ A).left))
      (M.pull (pullback.snd ((𝟙 A) ^ 2 : A ⟶ A).left ((𝟙 A) ^ 2 : A ⟶ A).left))) :
    ∃ L : LB A.left, L.IsLB ∧ LBIso (lbPow M 2) (L.pull ((𝟙 A) ^ 2 : A ⟶ A).left) := by
  have hf := GlobalTheory.MulFinite.isFinite_mul K A hA 2 (by norm_num)
  have hm : IsMonHom ((𝟙 A) ^ 2 : A ⟶ A) := by
    rw [← GlobalTheory.GrpTangent.mulN_eq_pow]; infer_instance
  obtain ⟨hfl, hsu⟩ := GlobalTheory.flat_and_surjective_of_isFinite_abelianEnd
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected K A hA _ hm hf
  have := hA.smooth
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  obtain ⟨φ, hφ⟩ := GlobalTheory.LBDescent.descCompat_of_lbIso _ M hM H
  obtain ⟨D, hD⟩ := GlobalTheory.T.exists_descentCocycleDefect_of_compatible _ M φ hM hφ
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_unit_killing_square_tripleFibreCocycle_mulTwo K A hA hf D (GlobalTheory.T.descentCocycleDefect_isTripleCocycle _ _ _ M hM φ D hD)
  obtain ⟨M₂, ψ, hM₂, e, hc, hco⟩ := GlobalTheory.T.exists_squareBundle_descent_of_defect_killed _ _ _ M hM φ D u hφ hD hu
  obtain ⟨L, hL, e'⟩ := GlobalTheory.T.exists_lineBundle_descent_finiteFlat _ _ ((𝟙 A) ^ 2 : A ⟶ A).left M₂ hM₂ ψ hc hco
  have hP : (lbPow M 2).IsLB := LB.isLB_linComb hM _ _
  exact ⟨L, hL, (cls_eq_iff hP (pull_isLB hL _)).1
    (((cls_eq_iff hP hM₂).2 e).trans ((cls_eq_iff hM₂ (pull_isLB hL _)).2 e'))⟩

theorem ev_symm {S : Scheme.{0}} {A : Over S} {P : LB (A ⊗ A).left} (hP : P.IsLB)
    (hs : LBIso P (P.pull (lift (snd A A) (fst A A)).left)) (T : Over S) (x y : T ⟶ A) :
    ev (cls P hP) x y = ev (cls P hP) y x := by
  have e : cls P hP = ev (cls P hP) (snd A A) (fst A A) := (cls_eq_iff hP (pull_isLB hP _)).2 hs
  calc ev (cls P hP) x y = pull (lift x y).left (ev (cls P hP) (snd A A) (fst A A)) := by rw [← e]; rfl
    _ = ev (cls P hP) y x := by rw [pull_ev, lift_fst, lift_snd]

theorem exists_ample_root {K : Type} [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A]
    (hA : IsAbelianScheme A) {P : LB (G2 A).left} (hP : P.IsLB)
    (r₁ : ∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen)
    (r₂ : ∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen)
    (hs : LBIso P (P.pull (lift (snd A A) (fst A A)).left)) (ha : RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left)) :
    ∃ L : LB A.left, L.IsLB ∧ LBIso (abelian₂ A L) P ∧ RelAmple A L := by
  have hLaws : Out.Laws := GlobalTheory.lawsAndExpansions.1.1
  have hM : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  have bP : Biadd (cls P hP) := biadd_of_axes hLaws.globalFns hA _ hM ha _ hP r₁ r₂
  have sy := ev_symm hP hs
  set p := cls P hP with hp
  have hm : ∀ (T : Over (Sp K)) (x : T ⟶ A), pull x.left (cls _ hM) = ev p x x := fun T x =>
    (pull_ev x p (𝟙 A) (𝟙 A)).trans (by rw [Category.comp_id])
  have h1 : ∀ (T : Over (Sp K)) (y : T ⟶ A), ev p 1 y = 0 := fun T y => by
    have := (bP T 1 1 y).1
    rw [_root_.mul_one] at this
    exact left_eq_add.1 this
  have hψ : ∀ {T : Over (Sp K)} (x : T ⟶ A), x ≫ ((𝟙 A) ^ 2 : A ⟶ A) = x * x := fun x => by
    rw [MonObj.comp_pow, Category.comp_id, pow_two]

  have hker : ∀ (T : Over (Sp K)) (t : T ⟶ A), t * t = 1 → ev p t t = 0 := by
    intro T t ht
    have hf := GlobalTheory.MulFinite.isFinite_mul K A hA 2 (by norm_num)
    let N := pullback ((𝟙 A) ^ 2 : A ⟶ A).left (η[A]).left
    have hfin : IsFinite (pullback.snd ((𝟙 A) ^ 2 : A ⟶ A).left (η[A]).left) := inferInstance
    haveI : IsAffine (𝟙_ (Over (Sp K))).left := inferInstanceAs (IsAffine (Sp K))
    have haff : IsAffine N := isAffine_of_isAffineHom (pullback.snd ((𝟙 A) ^ 2 : A ⟶ A).left (η[A]).left)
    haveI : IsAffine (𝟙_ (Over (Sp K))).left := inferInstanceAs (IsAffine (Sp K))
    have hN : Finite N := by
      haveI : IsFinite (𝟙_ (Over (Sp K))).hom := inferInstanceAs (IsFinite (𝟙 (Sp K)))
      have hq := ((pullback.snd ((𝟙 A) ^ 2 : A ⟶ A).left (η[A]).left) ≫ (𝟙_ (Over (Sp K))).hom).finite_preimage_singleton
        (⊥ : PrimeSpectrum K)
      exact Set.finite_univ_iff.1 (hq.subset fun x _ => Subsingleton.elim _ _)
    have w : t.left ≫ ((𝟙 A) ^ 2 : A ⟶ A).left = T.hom ≫ (η[A]).left := by
      rw [← Over.comp_left, hψ, ht]; rfl
    have z : pull (pullback.fst ((𝟙 A) ^ 2 : A ⟶ A).left (η[A]).left) (cls _ hM) = 0 :=
      (cls_eq_zero_iff (pull_isLB hM _)).2 (GlobalTheory.exists_isGen_of_finite (pull_isLB hM _))
    rw [← hm, ← pullback.lift_fst t.left T.hom w, pull_comp, z, map_zero]
  obtain ⟨L, hL, e⟩ := exists_descent_two A hA hM (by
    let f := ((𝟙 A) ^ 2 : A ⟶ A).left
    let T : Over (Sp K) := Over.mk (pullback.fst f f ≫ A.hom)
    let x : T ⟶ A := Over.homMk (pullback.fst f f) rfl
    let y : T ⟶ A := Over.homMk (pullback.snd f f) (by
      show pullback.snd f f ≫ A.hom = pullback.fst f f ≫ A.hom
      rw [← Over.w ((𝟙 A) ^ 2 : A ⟶ A), ← Category.assoc, ← Category.assoc]
      exact congrArg (· ≫ A.hom) pullback.condition.symm)
    have exy : x * x = y * y := by
      rw [← hψ, ← hψ]
      exact Over.OverMorphism.ext pullback.condition
    have ht : (x⁻¹ * y) * (x⁻¹ * y) = 1 := by
      rw [_root_.mul_mul_mul_comm, ← exy, ← mul_inv, inv_mul_cancel]
    refine (cls_eq_iff (pull_isLB hM _) (pull_isLB hM _)).1 ((hm T x).trans (Eq.trans ?_ (hm T y).symm))
    have ey : y = x * (x⁻¹ * y) := by rw [mul_inv_cancel_left]
    generalize x⁻¹ * y = t at ht ey
    have h2 : ev p t x + ev p t x = 0 := by rw [← (bP T t t x).1, ht, h1]
    rw [ey, (bP T _ _ _).1, (bP T _ _ _).2, (bP T _ _ _).2, hker T t ht, sy T x t, add_zero, add_assoc, h2, add_zero])
  have hΛ := GlobalTheory.SymBiextHalf.lam_iso hLaws hA hM ha hP bP sy hL e
  refine ⟨L, hL, hΛ, ?_⟩
  have hLam : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  have hPow : (lbPow (P.pull (lift (𝟙 A) (𝟙 A)).left) 2).IsLB := LB.isLB_linComb hM _ _
  have hL2 : (lbPow L 2).IsLB := LB.isLB_linComb hL _ _
  have c₁ : p = lam (cls L hL) (fst A A) (snd A A) :=
    ((cls_eq_iff hLam hP).2 hΛ).symm.trans (cls_cube_two hL _ _ hLam)
  have c₂ : 2 • cls _ hM = pull ((𝟙 A) ^ 2 : A ⟶ A).left (cls L hL) :=
    (cls_lbPow hM 2 hPow).symm.trans ((cls_eq_iff hPow (pull_isLB hL _)).2 e)
  have c₃ : cls _ hM = lam (cls L hL) (𝟙 A) (𝟙 A) := by
    have := hm A (𝟙 A)
    rw [Over.id_left, pull_id] at this
    rw [this, ev, c₁, pull_lam, lift_fst, lift_snd]
  have c₄ : pull (1 : A ⟶ A).left (cls L hL) = 0 := by
    have z : pull (η[A]).left (cls L hL) = 0 :=
      (cls_eq_zero_iff (pull_isLB hL _)).2 (GlobalTheory.LB.exists_isGen_of_isLocalRing (R := K) (pull_isLB hL _))
    show pull (toUnit A ≫ η[A]).left _ = 0
    rw [Over.comp_left, pull_comp, z, map_zero]
  have c₅ : cls _ hL2 = cls _ hM := by
    rw [cls_lbPow hL 2 hL2]
    rw [lam, c₄, ← pow_two, ← c₂, Over.id_left, pull_id] at c₃
    linear_combination (norm := abel) c₃
  have := hA.proper
  rw [relAmple_iff_isAmpleLB_of_isAffine A hL, ← isAmpleLB_pow_iff hL (k := 2) (by norm_num),
    isAmpleLB_congr hL2 hM ((cls_eq_iff hL2 hM).1 c₅), ← relAmple_iff_isAmpleLB_of_isAffine A hM]
  exact ha

section Siegel

variable {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ)

theorem root_of_siegPB {S' : Scheme.{0}} {s' : S' ⟶ Sp o} (c : SiegPre g n ζ s') (x : S' ⟶ F.X)
    (h : SiegPB c F.univ x) (L : LB c.A.left) (hL : L.IsLB) (e : LBIso (abelian₂ c.A L) c.P) :
    Root F.univ.A F.univ.P x := by
  obtain ⟨φ, φ₂, pb, sq, iso, -⟩ := h
  have hΛ : (abelian₂ c.A L).IsLB := LB.isLB_linComb hL _ _
  exact ⟨c.A, inferInstance, inferInstance, φ, φ₂, pb, sq, L, hL,
    LBIso.trans hΛ c.isLB (pull_isLB F.univ.isLB _) e iso⟩

theorem root_geom (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ F.X) : Root F.univ.A F.univ.P x := by
  obtain ⟨⟨c, hc⟩, hpr⟩ := GlobalTheory.siegPre_pullback g n o ζ F.X (Sp K) F.s (x ≫ F.s) x F.univ rfl
  have hcp := hpr c hc F.princ
  obtain ⟨L, hL, e, -⟩ := exists_ample_root c.A c.ab c.isLB c.rig₁ c.rig₂ c.symm hcp.1
  exact root_of_siegPB F c x hc L hL e

end Siegel

end GlobalTheory.PolBundleLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionsPrescribedReductionFiniteExt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.SecsAsm

theorem gs_scal_one {R : Type} [CommRing R] {Y Z : Scheme.{0}} (q : Y ⟶ Sp R) (p : Z ⟶ Y) (z : Z) :
    gs p z ⊤ (scal q 1) = 1 := by
  unfold scal
  rw [map_one, map_one, gs_eq p z ⊤ trivial, map_one, map_one]

theorem closed_pt (R : Type) [CommRing R] [IsLocalRing R] :
    spMap (residue R) (closedPoint (ResidueField R)) = closedPoint R :=
  IsLocalRing.comap_closedPoint (residue R)

theorem secs_exists (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hB : Base R) (D : DegData R (maximalIdeal R))
    (C : LabCover D) : Nonempty (Secs C.toModif C.G C.P.L.L C.α) := by
  obtain ⟨Y⟩ : Nonempty (Ext D.toPre) := inferInstance
  obtain ⟨hsm, -, -, -, -⟩ := GlobalTheory.Mum.ext_smooth_affine_surj_terms R D.toPre Y
  obtain ⟨S, k₁, himm⟩ := GlobalTheory.T.exists_theta_immersion_torus_extension_projective R hB D Y
  obtain ⟨hth, hth0⟩ := GlobalTheory.T.exists_integralThetaFamily_prescribed_leadingTerm R hB D
  choose k₀ hk₀ using hth
  obtain ⟨⟨j₀, hdesc⟩, hdescθ⟩ := GlobalTheory.Mum.exists_secs_of_intFam R hB D C
  have hk : k₁ + ∑ a ∈ S, k₀ a ≤ C.n ^ (max j₀ (k₁ + ∑ a ∈ S, k₀ a)) :=
    (le_max_right _ _).trans (Nat.lt_pow_self C.n_prime.one_lt).le
  obtain ⟨Φ, hΦ⟩ := hdesc (max j₀ (k₁ + ∑ a ∈ S, k₀ a)) (le_max_left _ _)
  obtain ⟨N, α, b, τ, hτ, hατ, hI⟩ := himm _ ((Nat.le_add_right _ _).trans hk)
  have hF : ∀ i, ∃ F : IntFam (maximalIdeal R) D.toPre (C.n ^ (max j₀ (k₁ + ∑ a ∈ S, k₀ a))), F.Lead (α i) (b i) :=
    fun i => hk₀ (α i) _ (((Finset.single_le_sum (fun _ _ => Nat.zero_le _) (hατ i).1).trans
      (Nat.le_add_left _ _)).trans hk) (b i)
  choose F hFl using hF
  obtain ⟨bθ, τθ, y₀, hθt, hy₀c, hy₀⟩ := GlobalTheory.Mum.exists_term_nonzero_closed R hB D Y
  obtain ⟨F₁, hF₁⟩ := hth0 1 le_rfl bθ
  obtain ⟨θ, hθ⟩ := hdescθ F₁
  have hsm0 : Smooth ((Over.pullback (spMap (residue R))).obj Y.H).hom :=
    inferInstanceAs (Smooth (pullback.snd Y.H.hom (spMap (residue R))))
  have himm0 : IsImmersion (pullback.fst Y.H.hom (spMap (residue R)) ≫ GlobalTheory.ProjSpace.toProj Y.H.hom τ hτ) := by
    have : IsClosedImmersion (spMap (residue R)) := IsClosedImmersion.spec_of_surjective _ residue_surjective
    have : IsClosedImmersion (pullback.fst Y.H.hom (spMap (residue R))) := inferInstance
    infer_instance
  refine ⟨{ N := N, k := _, s := fun i => Φ (F i), θ := θ, Y := (Over.pullback (spMap (residue R))).obj Y.H
            smooth := hsm0
            j := pullback.fst Y.H.hom (spMap (residue R)) ≫ GlobalTheory.ProjSpace.toProj Y.H.hom τ hτ
            j_over := ?_
            imm := himm0
            O := pullback.fst Y.H.hom (spMap (residue R)) ⁻¹ᵁ nonzeroLocus τθ
            O_ne := ?_
            trait := ?_ }⟩
  · rw [Category.assoc, GlobalTheory.ProjSpace.toProj_str, pullback.condition]; rfl
  · obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := Y.H.hom) (g := spMap (residue R)) y₀
      (closedPoint _) (hy₀c.trans (closed_pt R).symm)
    exact ⟨z, show pullback.fst Y.H.hom (spMap (residue R)) z ∈ nonzeroLocus τθ by rw [hz]; exact hy₀⟩
  intro W _ _ _ hW φ ξ hφ hloc hξ
  obtain ⟨W', _, _, _, io, T, hio, hfin, hTφ, hTξ⟩ := C.exists_trait W hW φ ξ hφ hloc hξ
  obtain ⟨u, hu⟩ := hΦ W' T
  obtain ⟨uθ, huθ⟩ := hθ W' T
  choose σ hσE hσA using fun i => hu (F i)
  obtain ⟨θ', hθE, hθA⟩ := huθ
  obtain ⟨κ, e, hκ, he, hred⟩ := GlobalTheory.Mum.trait_lead_value R hB D C Y W' T
  have hκ' : κ.comp (residue R) = (residue W').comp (io.comp φ) := by rw [hκ, hTφ]
  refine ⟨W', _, inferInstance, inferInstance, io, T.G, inferInstance, T.β, σ, θ', κ, e, T.cdvr, hio, hfin,
    by rw [← hTξ]; exact T.cart, hκ', he, fun i Z p p' hpp z J hJ => ?_, fun Z p p' hpp z J hJ => ?_, ?_⟩
  · rw [hσA i Z p p' hpp z J hJ, gs_scal_one, _root_.one_mul]
  · rw [hθA Z p p' hpp z J hJ, gs_scal_one, _root_.one_mul]
  intro Ω _ p p' y hp hy
  have hval := hred (Sp Ω) p p' (y ≫ pullback.fst Y.H.hom (spMap (residue R))) hp
    (by rw [hy]; simp only [Category.assoc])
  have e1 : spMap (residue W') ≫ spMap (io.comp φ) = spMap κ ≫ spMap (residue R) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hκ']
  have hw := Over.w e.hom
  have hbase : p' ≫ T.G.hom ≫ spMap (io.comp φ) = (y ≫ pullback.fst Y.H.hom (spMap (residue R))) ≫ Y.H.hom := by
    rw [hp]
    simp only [Category.assoc]
    rw [pullback.condition_assoc, e1, pullback.condition]
    rw [hy]
    simp only [Category.assoc]
    erw [pullback.condition_assoc]
    rw [← Category.assoc e.hom.left]
    erw [hw]
    rfl
  refine ⟨?_, fun x hx => ?_⟩
  · obtain ⟨-, hs, hP⟩ := GlobalTheory.Mum.toProj_secPull_of_sval R Ω C.G.left D.toPre.P.A.left T.G.left Y.H.left C.P.L.L D.toPre.P.L
      T.β Y.q.left _ N σ τ Y.H.hom hτ p' (y ≫ pullback.fst Y.H.hom (spMap (residue R))) C.P.L.isLB D.toPre.P.isLB
      (fun z J J' hJ hJ' => by
        obtain ⟨c, hc⟩ := hval _ u z J J' hJ hJ'
        exact ⟨c, fun i => hc (α i) (b i) (τ i) (F i) (σ i) (hατ i).2 (hFl i) (hσE i)⟩)
    rw [hbase]
    exact ⟨hs, hP.trans (by simp only [Category.assoc])⟩
  · choose J hJ using fun χ : Sp Ω ⟶ C.G.left => exists_chart C.P.L.isLB (χ x)
    choose J' hJ' using fun χ : Sp Ω ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (χ x)
    obtain ⟨c, hc⟩ := hval 1 uθ x J J' hJ hJ'
    have h1 := hc 0 bθ τθ F₁ θ' hθt hF₁ hθE
    have hx' : (y ≫ pullback.fst Y.H.hom (spMap (residue R))) x ∈ nonzeroLocus τθ := hx
    have hu1 := (GlobalTheory.mem_nonzeroLocus_iff_pull τθ _ x (Good.mem hJ' _ _)).1 hx'
    refine (GlobalTheory.mem_nonzeroLocus_iff_pull θ' p' x (Good.mem hJ _ _)).2 ?_
    change IsUnit (sval θ' p' x J)
    rw [h1]
    exact c.isUnit.mul hu1

end GlobalTheory.Mum.SecsAsm

theorem GlobalTheory.Mum.exists_secs_finExt : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D), ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsLocalRing R₁) (ρ : R →+* R₁) (D₁ : DegData R₁ (maximalIdeal R₁)) (C₁ : LabCover D₁), FinExt ρ ∧ Nonempty (IsPullDeg ρ D.toPre D₁.toPre) ∧ Nonempty (Secs C₁.toModif C₁.G C₁.P.L.L C₁.α) := by
  intro R _ _ _ hB D C
  obtain ⟨h, -, -⟩ := GlobalTheory.DegPullId.exists_isPullDeg_id_self R (maximalIdeal R) hB.1 D
  exact ⟨R, inferInstance, inferInstance, inferInstance, RingHom.id R, D, C,
    ⟨hB.1, Function.injective_id, RingHom.Finite.id R⟩, ⟨h⟩, GlobalTheory.Mum.SecsAsm.secs_exists R hB D C⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSetupTowerBaseChangeMember
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep

theorem exists_ringHom_val_of_regAt : ∀ {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z} (X₂ : Setup F W i) (z : X₂.M.Z) {V : Type} [CommRing V] [IsDomain V] (ev : X₂.M.Z.presheaf.stalk z →+* V), RegAt X₂ z ev → ∃ yK : X₂.S.R →+* FractionRing V, ∀ a : X₂.S.R, yK a = X₂.M.val (jK V ≫ spMap ev ≫ X₂.M.Z.fromSpecStalk z) a := by
  intro g n F W Z i X₂ z V _ _ ev hr
  have hR : X₂.S.R ≤ X₂.M.O ((jK V ≫ spMap ev ≫ X₂.M.Z.fromSpecStalk z) (IsLocalRing.closedPoint (FractionRing V))) :=
    fun a ha => hr a ha
  exact ⟨(RatModel.valHomOf (jK V ≫ spMap ev ≫ X₂.M.Z.fromSpecStalk z) _
    (RatModel.specializes_of_range_eq (RatModel.range_eq_singleton (M := X₂.M) (jK V ≫ spMap ev ≫ X₂.M.Z.fromSpecStalk z) (IsLocalRing.closedPoint (FractionRing V))))).comp
      (Subalgebra.inclusion hR).toRingHom, fun a => rfl⟩

theorem Tower.comp_act₂_of_comp_act : ∀ {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z} {X₁ : Setup F W i} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (𝔗 : Tower X₁ act) {K : Type} [Field K] (A' : Over (Sp K)) (y₂ : 𝔗.X₂.S.R →+* K) (φ₂ : A'.left ⟶ 𝔗.X₂.ρ.P.A.left), φ₂ ≫ 𝔗.X₂.ρ.P.A.hom = A'.hom ≫ spMap y₂ → ∀ (e : A' ⟶ A') (a : Matrix (Fin 8) (Fin 8) ℤ), e.left ≫ φ₂ ≫ 𝔗.φ = φ₂ ≫ 𝔗.φ ≫ (act a).left → e.left ≫ φ₂ = φ₂ ≫ (𝔗.act₂ a).left := by
  intro g n F W Z i X₁ act 𝔗 K _ A' y₂ φ₂ hφ e a h
  refine 𝔗.cart.1.hom_ext ?_ ?_
  · simp only [Category.assoc, 𝔗.act_eq a]
    simpa only [Category.assoc] using h
  · simp only [Category.assoc, Over.w (𝔗.act₂ a), hφ]
    rw [← Category.assoc, Over.w e]

theorem Tower.pt_iff_pt_gl : ∀ {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z} {X₁ : Setup F W i} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (𝔗 : Tower X₁ act) {K : Type} [Field K] (A' : Over (Sp K)) [GrpObj A'] (ya yb : 𝔗.X₂.S.R →+* K) (φa φb : A'.left ⟶ 𝔗.X₂.ρ.P.A.left) (σ : 𝔗.X₂.Ω₁ ≃ₐ[X₁.Ω₁] 𝔗.X₂.Ω₁), IsGrpPullback A' 𝔗.X₂.ρ.P.A (spMap ya) φa → IsGrpPullback A' 𝔗.X₂.ρ.P.A (spMap yb) φb → φa ≫ 𝔗.φ = φb ≫ 𝔗.φ → ya = yb.comp (𝔗.sR σ) → ∀ {L : Type} [Field L] (j : K →+* L) (x : Sp L ⟶ A'.left), x ≫ A'.hom = spMap j → ∀ a, (x ≫ φa = spMap (j.comp ya) ≫ (𝔗.X₂.ρ.pt a).left ↔ x ≫ φb = spMap (j.comp yb) ≫ (𝔗.X₂.ρ.pt (𝔗.gl σ a)).left) := by
  intro g n F W Z i X₁ act 𝔗 K _ A' _ ya yb φa φb σ ha hb hab hy L _ j x hx a
  have hc := 𝔗.cart.1
  have hsec : ∀ b, (𝔗.X₂.ρ.pt b).left ≫ 𝔗.X₂.ρ.P.A.hom = 𝟙 _ := fun b => Over.w (𝔗.X₂.ρ.pt b)
  have hsp : ∀ y : 𝔗.X₂.S.R →+* K, spMap j ≫ spMap y = spMap (j.comp y) := fun y => by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hxa : (x ≫ φa) ≫ 𝔗.X₂.ρ.P.A.hom = spMap (j.comp ya) := by
    rw [Category.assoc, ha.1.w, ← Category.assoc, hx, hsp]
  have hxb : (x ≫ φb) ≫ 𝔗.X₂.ρ.P.A.hom = spMap (j.comp yb) := by
    rw [Category.assoc, hb.1.w, ← Category.assoc, hx, hsp]
  have hra : (spMap (j.comp ya) ≫ (𝔗.X₂.ρ.pt a).left) ≫ 𝔗.X₂.ρ.P.A.hom = spMap (j.comp ya) := by
    rw [Category.assoc, hsec]
    exact Category.comp_id _
  have hrb : (spMap (j.comp yb) ≫ (𝔗.X₂.ρ.pt (𝔗.gl σ a)).left) ≫ 𝔗.X₂.ρ.P.A.hom = spMap (j.comp yb) := by
    rw [Category.assoc, hsec]
    exact Category.comp_id _
  have hg : spMap (j.comp yb) ≫ (𝔗.X₂.ρ.pt (𝔗.gl σ a)).left ≫ 𝔗.φ = spMap (j.comp ya) ≫ (𝔗.X₂.ρ.pt a).left ≫ 𝔗.φ := by
    rw [𝔗.gl_pt, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, RingHom.comp_assoc, ← hy]
  constructor
  · intro h1
    refine hc.hom_ext ?_ (hxb.trans hrb.symm)
    rw [Category.assoc, ← hab, ← Category.assoc, h1, Category.assoc, Category.assoc, hg]
  · intro h1
    refine hc.hom_ext ?_ (hxa.trans hra.symm)
    rw [Category.assoc, hab, ← Category.assoc, h1, Category.assoc, Category.assoc, hg]

end GlobalTheory.Poinc.Sep

namespace GlobalTheory

theorem exists_baseChange_member_of_tower : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∀ (𝔗 : Tower X₁ act) (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ x₀ : X₁.S.Gam, X₁.M.Div X₁.S.th x₀ z₁ → ∃ eps : X₁.S.Gam → ℕ, ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam) (T : (Fin 8 → X) → C → V), 𝔪.Terms x₀ lab T → ∀ (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (io : V →+* V'), IsCN V' → Function.Injective io → io.Finite → ∃ 𝔪₂ : ∀ ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V', 𝔗.Ext ev io ev₂ → UMem 𝔗.X₂ z₂ 𝔗.act₂ V' ev₂ X (fun k => io (t k)) δ, (∀ ev₂ h (zt : 𝔗.X₂.M.Z.presheaf.stalk z₂), 𝔗.X₂.M.stalkHom z₂ zt = algebraMap 𝔗.X₂.o₁ 𝔗.X₂.Ω₁ 𝔗.X₂.S.ζ → (𝔪₂ ev₂ h).Terms (𝔗.lam x₀) (fun c => 𝔗.lam (lab c)) (fun mu c => ev₂ zt ^ eps (lab c) * io (T mu c))) ∧ ∀ ev₂ h ev₂' h' (σ : 𝔗.X₂.Ω₁ ≃ₐ[X₁.Ω₁] 𝔗.X₂.Ω₁), (∀ x x', 𝔗.X₂.M.stalkHom z₂ x' = σ (𝔗.X₂.M.stalkHom z₂ x) → ev₂' x = ev₂ x') → (∀ x, ∃ x', 𝔗.X₂.M.stalkHom z₂ x' = σ (𝔗.X₂.M.stalkHom z₂ x)) → ∀ a mu, (𝔪₂ ev₂' h').YY a mu ↔ (𝔪₂ ev₂ h).YY (𝔗.gl σ a) mu := by
  intro g hg n hn hodd F Z z i _ hproj hnorm hiz hdense W hE8 hth X₁ z₁ act hact 𝔗 z₂ hz₂ x₀ hdiv
  obtain ⟨eps, heps⟩ := GlobalTheory.T.thetaSetupTower_member_terms_baseChange X₁ act 𝔗 z₁ z₂ hz₂ x₀ hdiv
  refine ⟨eps, ?_⟩
  intro V _ _ _ ev X _ m t δ 𝔪 C lab T hT V' _ _ _ io hcn hinj hfin
  have hle : nonZeroDivisors V ≤ (nonZeroDivisors V').comap io :=
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective io hinj
  let f : FractionRing V →+* FractionRing V' := IsLocalization.map (FractionRing V') io hle
  have hf : ∀ v, f (algebraMap V (FractionRing V) v) = algebraMap V' (FractionRing V') (io v) :=
    fun v => IsLocalization.map_eq hle v
  obtain ⟨D', e₈', G', _, _, A', U', ψ, hD, bc, hsemi, hψ, hw, hbc, hPU, hxe, hgen, hE, hpsi⟩ :=
    GlobalTheory.T.exists_baseChange_finite_injective_complete_normal X₁ z₁ act V ev X m t δ 𝔪 V' io f hf hcn hinj hfin
  have hreg : ∀ ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V', 𝔗.Ext ev io ev₂ → RegAt 𝔗.X₂ z₂ ev₂ :=
    fun ev₂ h => GlobalTheory.T.deeperThetaRing_regular_at_extension_point 𝔗 hz₂ ev io ev₂ hinj h 𝔪.reg
  choose yK hyK using fun (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (h : 𝔗.Ext ev io ev₂) =>
    exists_ringHom_val_of_regAt 𝔗.X₂ z₂ ev₂ (hreg ev₂ h)
  have hyKc : ∀ ev₂ h, (yK ev₂ h).comp 𝔗.om = f.comp 𝔪.yK := by
    intro ev₂ h
    ext a
    simp only [RingHom.comp_apply]
    rw [hyK, 𝔪.yK_eq]
    exact GlobalTheory.T.deeperTheta_value_image_eq_image_value 𝔗 hz₂ ev io ev₂ f hf hinj h 𝔪.reg a
  have hsq : ∀ ev₂ h, spMap (yK ev₂ h) ≫ spMap 𝔗.om = spMap f ≫ spMap 𝔪.yK := by
    intro ev₂ h
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hyKc ev₂ h]
  choose φ₂ hφ₂ using fun (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (h : 𝔗.Ext ev io ev₂) =>
    GlobalTheory.T.isGrpPullback_paste_factorisation X₁.ρ.P.A 𝔗.X₂.ρ.P.A 𝔪.A.A A'.A (spMap 𝔗.om) (spMap 𝔪.yK) (spMap f) (spMap (yK ev₂ h)) 𝔗.φ 𝔪.φ ψ
      𝔗.cart 𝔪.cart hψ (hsq ev₂ h)
  choose wl hwl using fun (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (h : 𝔗.Ext ev io ev₂) =>
    GlobalTheory.T.exists_lineBundleIso_pullback_commSquare A'.L 𝔪.A.L X₁.ρ.P.L 𝔗.X₂.ρ.P.L ψ 𝔪.φ (φ₂ ev₂ h) 𝔗.φ A'.isLB 𝔪.A.isLB X₁.ρ.P.isLB 𝔗.X₂.ρ.P.isLB
      (hφ₂ ev₂ h).2.symm hw ⟨𝔪.wl, 𝔪.wl_gen⟩ 𝔗.lb
  let 𝔪₂ : ∀ ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V', 𝔗.Ext ev io ev₂ →
      UMem 𝔗.X₂ z₂ 𝔗.act₂ V' ev₂ X (fun k => io (t k)) δ := fun ev₂ h =>
    { cn := hcn
      loc := h.1
      reg := hreg ev₂ h
      yK := yK ev₂ h
      yK_eq := hyK ev₂ h
      D := D'
      e₈ := e₈'
      G := G'
      semi := hsemi
      A := A'
      U := U'
      φ := φ₂ ev₂ h
      cart := (hφ₂ ev₂ h).1
      wl := wl ev₂ h
      wl_gen := hwl ev₂ h
      equiv := fun a a' hc => by
        obtain ⟨E, hE1, hE2⟩ := 𝔪.equiv a a' hc
        obtain ⟨E', hE'1, hE'2⟩ := hE E
        refine ⟨E', ?_, fun mu => hD.xe.injective ?_⟩
        · have e2 := (hφ₂ ev₂ h).2
          refine Tower.comp_act₂_of_comp_act 𝔗 A'.A (yK ev₂ h) (φ₂ ev₂ h) (hφ₂ ev₂ h).1.1.w E'.aA a ?_
          calc E'.aA.left ≫ φ₂ ev₂ h ≫ 𝔗.φ = E'.aA.left ≫ ψ ≫ 𝔪.φ := by rw [e2]
            _ = ψ ≫ E.aA.left ≫ 𝔪.φ := by rw [← Category.assoc, hE'1, Category.assoc]
            _ = ψ ≫ 𝔪.φ ≫ (act a).left := by rw [hE1]
            _ = φ₂ ev₂ h ≫ 𝔗.φ ≫ (act a).left := by rw [← Category.assoc, ← e2, Category.assoc]
        · rw [hE'2, hxe, hE2, hxe]
      psi := hpsi }
  refine ⟨𝔪₂, ?_, ?_⟩
  · intro ev₂ h zt hzt
    exact heps V ev X m t δ 𝔪 C lab T hT V' io f hf hinj hfin ev₂ (𝔪₂ ev₂ h) ψ hD bc h (hyKc ev₂ h) hψ hw
      (hφ₂ ev₂ h).2 hbc hPU hxe hgen zt hzt
  · intro ev₂ h ev₂' h' σ h1 h2 a mu
    have hy : yK ev₂' h' = (yK ev₂ h).comp (𝔗.sR σ) := by
      ext b
      simp only [RingHom.comp_apply]
      rw [hyK, hyK]
      exact GlobalTheory.T.deeperTheta_value_galoisConjugate_extension 𝔗 ev₂ ev₂' σ h1 h2 (hreg ev₂ h) (hreg ev₂' h') b
    unfold UMem.YY
    refine exists_congr fun p => exists_congr fun x => and_congr_right fun _ => and_congr_right fun _ => ?_
    exact Tower.pt_iff_pt_gl 𝔗 A'.A (yK ev₂' h') (yK ev₂ h) (φ₂ ev₂' h') (φ₂ ev₂ h) σ (hφ₂ ev₂' h').1 (hφ₂ ev₂ h).1
      ((hφ₂ ev₂' h').2.trans (hφ₂ ev₂ h).2.symm) hy
      (algebraMap (FractionRing V') (AlgebraicClosure (FractionRing V'))) x.left (Over.w x) a

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorSymbolUniquePrincipalPolarisationStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heatOperator_symbol_unique_principalPolarisation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (D : Derivation ℤ R R), ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ t.G.left) (δ : Fin n → Derivation ℤ Ω Ω) (dd' : Fin n → Fld t.G.left), IsAdicComplete ((maximalIdeal R).map φ) Ω → x' ≫ t.G.hom = spMap φ → (∀ a, IsInv t.G (v' a) (dd' a)) → (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x' ⁻¹ᵁ O → valR x' O (dd' a O f) = δ a (valR x' O f)) → (∀ O (f : Γ(t.G.left, O)), ⊤ ≤ x' ⁻¹ᵁ O → valR x' O f = 0 → f = 0) → ∀ (g : GlobalTheory.RayEv.Transport.Frame t.PP.L (x' ≫ 𝟙 t.G.left)), g.IsGen → ∀ (δL : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)), (∀ a ω, δL a ((algebraMap Ω (FractionRing Ω)) ω) = (algebraMap Ω (FractionRing Ω)) (δ a ω)) → ∀ (Λ₁ Λ₂ : Matrix (Fin n) (Fin n) (FractionRing Ω)) (d₁ d₂ : Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (u₁ u₂ : Fin n → (FractionRing Ω)) (p₁ p₁' p₂ p₂' : (FractionRing Ω)), Λ₁ᵀ = Λ₁ → Λ₂ᵀ = Λ₂ → (∀ r, d₁ ((algebraMap Ω (FractionRing Ω)) (φ r)) = d₂ ((algebraMap Ω (FractionRing Ω)) (φ r))) → (∀ (k : ℕ), 1 ≤ k → ∀ s : (FractionRing Ω), (∃ (r : R) (σ : SecM (𝟙 t.G.left) t.PP.L k) (ω : Ω), r ≠ 0 ∧ IsValue (𝟙 _) t.PP.L x' g k σ ω ∧ (algebraMap Ω (FractionRing Ω)) ω = (algebraMap Ω (FractionRing Ω)) (φ r) * (s)) → (∃ (r : R) (σ : SecM (𝟙 t.G.left) t.PP.L k) (ω : Ω), r ≠ 0 ∧ IsValue (𝟙 _) t.PP.L x' g k σ ω ∧ (algebraMap Ω (FractionRing Ω)) ω = (algebraMap Ω (FractionRing Ω)) (φ r) * (ringOp ⇑d₁ (fun a => ⇑(δL a)) Λ₁ u₁ p₁ p₁' k s))) → (∀ (k : ℕ), 1 ≤ k → ∀ s : (FractionRing Ω), (∃ (r : R) (σ : SecM (𝟙 t.G.left) t.PP.L k) (ω : Ω), r ≠ 0 ∧ IsValue (𝟙 _) t.PP.L x' g k σ ω ∧ (algebraMap Ω (FractionRing Ω)) ω = (algebraMap Ω (FractionRing Ω)) (φ r) * (s)) → (∃ (r : R) (σ : SecM (𝟙 t.G.left) t.PP.L k) (ω : Ω), r ≠ 0 ∧ IsValue (𝟙 _) t.PP.L x' g k σ ω ∧ (algebraMap Ω (FractionRing Ω)) ω = (algebraMap Ω (FractionRing Ω)) (φ r) * (ringOp ⇑d₂ (fun a => ⇑(δL a)) Λ₂ u₂ p₂ p₂' k s))) → Λ₁ = Λ₂ := by
  first | exact @GlobalTheory.HeatSym.symbol_unique | exact GlobalTheory.HeatSym.symbol_unique | (intros; apply GlobalTheory.HeatSym.symbol_unique <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProjOverOfCompactB
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT

theorem Model.isProjOver_of_compactB (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R]
    [IsDomain R] [CharZero R] [IsNoetherianRing R] (b : Base D R) (N : ℕ) (_hN : 3 ≤ N) (_hNp : N.Coprime p)
    (hD : D.CompactB) (M : Model b N) : IsProjOver M.s :=
  GlobalTheory.UPel.isProjOver_of_isQProjOver_of_isProper R M.X M.s M.qproj
    (GlobalTheory.T.harrisTaylor_integralModel_isProper_of_compact p D R b N M hD)

end GlobalTheory.UPel.HT
end

