import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2469
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThickId
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2468
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2487
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2547
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2491
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2511
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2509
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2411
import Development.AbelianVarietyTheory.Definitions.Divisors.StepsNonvacuous
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0013
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0017
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0015
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0012
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0004
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0002
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.CubeSectionFacesAndDoubling
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.SeriesApplyEqZeroOfFace
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsGlobalFrameOfLocal
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0001
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.AppellHumbertNormalFormOfLinearExponent
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0031
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0056
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2485
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0056
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaOfTranslDiff
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0208
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0101
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0222
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2470
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2506
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0081
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2252
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2228
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2179
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineChartSmoothLiftSqZeroStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Obs GlobalTheory.LBLift
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_chart_smooth_lift_sqZero : ∀ (R : Type) [CommRing R] (J : Ideal R), J ^ 2 = ⊥ → ∀ (g : ℕ) (B : Over (Sp R)) (b : B ⟶ Over.mk (spMap (Ideal.Quotient.mk J))), SmoothOfRelativeDimension g b.left → ∀ x : B.left, ∃ (C : Type) (_ : CommRing C) (σ : R →+* C) (j : Over.mk (spMap σ) ⊗ Over.mk (spMap (Ideal.Quotient.mk J)) ⟶ B), SmoothOfRelativeDimension g (spMap σ) ∧ j ≫ b = snd _ _ ∧ IsOpenImmersion j.left ∧ x ∈ Set.range j.left := by
  first | exact @GlobalTheory.LBLift.exists_chart_lift | exact GlobalTheory.LBLift.exists_chart_lift | (intros; apply GlobalTheory.LBLift.exists_chart_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineNhdsAvoidingImagesOfSpecializationsStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_nhds_avoiding_images_of_specializations : ∀ (X Y : Scheme.{0}) [IsIntegral X] (s : Y ⟶ X) [IsProper s] (T : Set Y) (σ : Y) (y : X) (N : CartierDiv X), T.Finite → (∀ v ∈ T, ∀ w : Y, v ⤳ w → σ ⤳ w → ¬ s w ⤳ y) → ∃ (U : X.Opens) (e : X.functionFieldˣ), IsAffineOpen U ∧ y ∈ U ∧ (∀ x ∈ U, N.IsEqn x e) ∧ ∀ v ∈ T, ∀ w : Y, v ⤳ w → σ ⤳ w → s w ∉ U := by
  first | exact @GlobalTheory.BadOpen.exists_affine_nhds_avoid | exact GlobalTheory.BadOpen.exists_affine_nhds_avoid | (intros; apply GlobalTheory.BadOpen.exists_affine_nhds_avoid <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineNonzeroLocusFlatLocalBaseChange
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.AmplePt

theorem exists_affine_nonzeroLocus_of_square : (∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsNoetherianRing R'] [IsIntegrallyClosed R'] [IsLocalRing R'] (G' : Over (Sp R')) [GrpObj G'], IsSemiAbelian G' → IsAbelianScheme ((Over.pullback (jK R')).obj G') → ∀ N : LB G'.left, N.IsLB → ∀ a : 𝟙_ (Over (Sp R')) ⟶ G', ∃ t : LB.Gen (LB.LinComb N (K := Fin 3) ![(𝟙 G' * (toUnit G' ≫ a)).left, (𝟙 G' * (toUnit G' ≫ a⁻¹)).left, 𝟙 G'.left] ![1, 1, -2]), t.IsGen) → ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → IsAbelianScheme ((Over.pullback (jK R)).obj G) → ∀ (M₀ : LB G.left), M₀.IsLB → ∀ s₀ : M₀.Sec, IsAffineOpen (nonzeroLocus s₀) → (∃ y₀ ∈ nonzeroLocus s₀, G.hom y₀ = closedPoint R) → ∀ y : G.left, ∃ (R' : Type) (_ : CommRing R') (ρ : R →+* R'), ρ.Flat ∧ ∃ x' : ↥(pullback G.hom (spMap ρ)), pullback.fst G.hom (spMap ρ) x' = y ∧ ∃ n, 1 ≤ n ∧ ∃ s : (lbPow (M₀.pull (pullback.fst G.hom (spMap ρ))) n).Sec, x' ∈ nonzeroLocus s ∧ IsAffineOpen (nonzeroLocus s) := by
  intro H R _ _ _ G _ hG hab M₀ hM s₀ hV hy₀ y
  obtain ⟨z, hz1, hz2, hz3⟩ := GlobalTheory.T.exists_point_translates_in_open_semiAbelian_local R G hG (nonzeroLocus s₀) hy₀ y
  obtain ⟨hd, hn, hic, hfl, hinj⟩ := GlobalTheory.T.stalk_normal_flat_of_smooth_over_regular_local R G.left G.hom hG.smooth ((snd G G).left z)
  let R' : Type := G.left.presheaf.stalk ((snd G G).left z)
  let ρ : R →+* R' := (Spec.preimage (G.left.fromSpecStalk ((snd G G).left z) ≫ G.hom)).hom
  have hc : G.left.fromSpecStalk ((snd G G).left z) ≫ G.hom = spMap ρ := (Spec.map_preimage _).symm
  obtain ⟨a, Φ, hpb, hΦ1, hΦ2, hΦ3⟩ := GlobalTheory.T.exists_section_translate_baseChange_of_point R R' ρ G (G.left.fromSpecStalk ((snd G G).left z)) hc
  obtain ⟨x', hx'⟩ : ∃ x', Φ x' = z := by
    obtain ⟨w, hw1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := (snd G G).left)
      (g := G.left.fromSpecStalk ((snd G G).left z)) z (closedPoint R') Scheme.fromSpecStalk_closedPoint.symm
    refine ⟨hpb.isoPullback.inv w, ?_⟩
    rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst, hw1]
  have e1 : pullback.fst G.hom (spMap ρ) x' = (fst G G).left z := by
    rw [← hΦ1, Scheme.Hom.comp_apply, hx']
  have e2 : ((𝟙 ((Over.pullback (spMap ρ)).obj G) * (toUnit _ ≫ a)).left ≫ pullback.fst G.hom (spMap ρ)) x' =
      (fst G G * snd G G).left z := by rw [hΦ2, Scheme.Hom.comp_apply, hx']
  have e3 : ((𝟙 ((Over.pullback (spMap ρ)).obj G) * (toUnit _ ≫ a⁻¹)).left ≫ pullback.fst G.hom (spMap ρ)) x' =
      (fst G G * (snd G G)⁻¹).left z := by rw [hΦ3, Scheme.Hom.comp_apply, hx']
  have hsemi' : IsSemiAbelian ((Over.pullback (spMap ρ)).obj G) := IsSemiAbelian.pullback _ G hG
  haveI := hd; haveI := hn; haveI := hic
  have hab' := GlobalTheory.T.isAbelianScheme_genericFibre_injective_domain_map R R' ρ hinj G hab
  obtain ⟨t, ht⟩ := H R' ((Over.pullback (spMap ρ)).obj G) hsemi' hab'
    (M₀.pull (pullback.fst G.hom (spMap ρ))) (LB.isLB_pull hM _) a
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_section_sq_nonzeroLocus_of_translate_generator _ _ (pullback.fst G.hom (spMap ρ)) M₀ hM s₀ _ _ ⟨t, ht⟩
  haveI : IsAffineHom (pullback.fst G.hom (spMap ρ)) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback G.hom (spMap ρ)).flip inferInstance
  have hW : IsAffineOpen (pullback.fst G.hom (spMap ρ) ⁻¹ᵁ nonzeroLocus s₀) := hV.preimage _
  have hL := GlobalTheory.T.isAffineOpen_preimage_translates_separated_grp R' ((Over.pullback (spMap ρ)).obj G) hsemi'.separated a _ hW
  refine ⟨R', inferInstance, ρ, hfl, x', e1.trans hz1, 2, by norm_num, s, ?_, ?_⟩
  · rw [hs]
    exact ⟨(Scheme.Hom.mem_preimage _).2 (e2 ▸ hz2), (Scheme.Hom.mem_preimage _).2 (e3 ▸ hz3)⟩
  · rw [hs, Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage]; exact hL

end GlobalTheory.AmplePt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertLineBundle
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_isFactorAH_frame_of_unif :
    ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (L₀ : LB A.left) (g : ℕ) (u₀ : HolUnif A L₀ g)
    (M : LB A.left), M.IsLB → ∃ (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ),
      u.ex = u₀.ex ∧ GlobalTheory.TorusRM.IsFactorAH u Hm χ := by
  intro A _ _ hA L₀ g u M hL
  have hval := @valAt'_rules
  have hholprod := @holFamily_lift hval
  have hcubet := @cube_trivialisation_on_uniformising_space hval hholprod
  have hdbl := @exists_doubling_solution_pi
  have hdblu := @eventually_eq_zero_of_isBigO_cube_of_doubling
  have hlock := @LocalCube.exists_third_difference hdbl hdblu
  have hface := @cube_section_faces_and_doubling
  have hloc := @exists_localFrame_compatible_cube @hface hlock
  have hglob := @CubeFrame.exists_global_frame
  have hfac := @automorphyFactor_exp_linear_of_cube
  have hnf := @appellHumbert_normal_form_of_linear_exponent
  obtain ⟨t, ht⟩ := exists_gen_theta_of_isAbelianScheme ℂ A hA M hL
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, T, hT1, hT2, hT3, hT4⟩ :=
    hcubet A L₀ M g u hL t ht _ _ rfl rfl
  obtain ⟨fr, κ, hfr, hκ⟩ := hglob g _ _ h1 h2 h3 h4 h5 T hT1 hT2 hT3
    (hloc g _ _ h1 h2 h3 h4 h5 T hT1 hT2 hT3 u.Λ u.discrete u.full h6 h7 hT4)
  obtain ⟨a, B, ha, hab, hfa⟩ := hfac g _ _ h1 h2 h3 h4 h5 T hT1 hT2 hT3 u.Λ u.discrete u.full
    h6 h7 hT4 fr κ hfr hκ
  obtain ⟨Hm, χ, Ef, Q, hH, hχ, hE, hQ, hQ0, hQn⟩ := hnf g u.Λ u.discrete u.full a B ha hab
  obtain ⟨f1, f2, f3⟩ := hfr
  refine ⟨{ ex := u.ex, ex_add := u.ex_add, ex_onto := u.ex_onto, Λ := u.Λ, ker := u.ker,
            discrete := u.discrete, full := u.full, hol := u.hol,
            fr := fun i z => fr i z * Complex.exp (Q z),
            fr_hol := fun i => ?_, fr_ne := fun i z hz => ?_, fr_compat := fun i j z hz => ?_ },
    Hm, χ, rfl, hH, hχ, ?_⟩
  · have := f1 i
    rw [Set.inter_univ] at this
    exact this.mul hQ.cexp.differentiableOn
  · exact mul_ne_zero (f2 i z hz trivial) (Complex.exp_ne_zero _)
  · have := f3 i j z (le_trans hz (fun _ h => h.1)) (le_trans hz (fun _ h => h.2)) trivial
    rw [this]
    ring
  · intro l i z hz
    show fr i z * Complex.exp (Q z) = _ * (fr i (z + l) * Complex.exp (Q (z + l)))
    rw [← hQn l z, hfa l i z hz, Complex.exp_sub]
    have := Complex.exp_ne_zero (Q (z + l))
    field_simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArithBaseFiniteContainingRootOfUnityStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_arithBase_finite_containing_rootOfUnity : ∀ {o₁ Ω₁ : Type} [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [ArithBase o₁ Ω₁] (Ω₂ : Type) [Field Ω₂] [Algebra Ω₁ Ω₂] (K : ℕ) (ζ : Ω₂ˣ), 0 < K → IsPrimitiveRoot ζ K → ∃ (o₂ : Type) (_ : CommRing o₂) (_ : Algebra o₂ Ω₂) (_ : ArithBase o₂ Ω₂) (κ : o₁ →+* o₂) (ze : o₂ˣ), κ.Finite ∧ (algebraMap o₂ Ω₂).comp κ = (algebraMap Ω₁ Ω₂).comp (algebraMap o₁ Ω₁) ∧ Units.map (algebraMap o₂ Ω₂ : o₂ →* Ω₂) ze = ζ := by
  first | exact @GlobalTheory.Poinc.exists_arithBase_rootOfUnity | exact GlobalTheory.Poinc.exists_arithBase_rootOfUnity | (intros; apply GlobalTheory.Poinc.exists_arithBase_rootOfUnity <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseChangePolarisationTranslateTwoTorsion
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.BaseTransl

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G']
  {g : G'.left ⟶ G.left}

theorem toBase_injective (hg : IsPullback g G'.hom G.hom f) {T : Over S'} {x x' : T ⟶ G'}
    (h : toBase hg.w x = toBase hg.w x') : x = x' := by
  have e : x.left ≫ g = x'.left ≫ g := congrArg (fun z => z.left) h
  ext
  exact hg.hom_ext e (by rw [Over.w x, Over.w x'])

theorem toBase_one (hg : IsPullback g G'.hom G.hom f)
    (hm : ∀ (T : Over S') (x y : T ⟶ G'), toBase hg.w (x * y) = toBase hg.w x * toBase hg.w y) (T : Over S') :
    toBase hg.w (1 : T ⟶ G') = 1 := by
  have := hm T 1 1
  rw [_root_.mul_one] at this
  exact mul_eq_left.1 this.symm

theorem isGrpPullback_of_toBase (hg : IsPullback g G'.hom G.hom f)
    (hm : ∀ (T : Over S') (x y : T ⟶ G'), toBase hg.w (x * y) = toBase hg.w x * toBase hg.w y) :
    IsGrpPullback G' G f g := by
  refine ⟨hg, fun T x y x₀ y₀ hx hy => ?_⟩
  have ex : x₀ = toBase hg.w x := by ext; exact hx
  have ey : y₀ = toBase hg.w y := by ext; exact hy
  rw [ex, ey, ← hm]
  rfl

open GlobalTheory.RigidTranslate in

theorem exists_baseChange_translate : ∀ (K K' : Type) [Field K] [Field K'] (io : K →+* K') (A : PolAV (Sp K)) (y : Over.mk (spMap io) ⟶ A.A), y * y = 1 → ∃ (A₁ : PolAV (Sp K')) (α₁ : A₁.A.left ⟶ A.A.left) (α₁₂ : (G2 A₁.A).left ⟶ (G2 A.A).left) (t : 𝟙_ (Over (Sp K')) ⟶ A₁.A), IsGrpPullback A₁.A A.A (spMap io) α₁ ∧ IsSquare α₁ α₁₂ ∧ LBIso (abelian₂ A₁.A A₁.L) ((abelian₂ A.A A.L).pull α₁₂) ∧ t.left ≫ α₁ = y.left ∧ LBIso A₁.L (GlobalTheory.RigidTranslate.rigTransl (A.L.pull α₁) t) := by
  intro K K' _ _ io A y hy
  obtain ⟨P, g, hg, -, hm, w, hw⟩ := GlobalTheory.polBaseChange_holds (Sp K) (Sp K') (spMap io) A
  have hpb : IsGrpPullback P.A A.A (spMap io) g := isGrpPullback_of_toBase hg hm
  have := P.isAb.comm
  have := P.isAb.proper
  have := A.isAb.comm
  let t₀ : 𝟙_ (Over (Sp K')) ⟶ P.A := Over.homMk (hg.lift y.left (𝟙 _) (by rw [Over.w y, Category.id_comp]; rfl))
    (hg.lift_snd _ _ _)
  have ht₀ : t₀.left ≫ g = y.left := hg.lift_fst _ _ _
  let e : Over.mk ((𝟙_ (Over (Sp K'))).hom ≫ spMap io) ⟶ Over.mk (spMap io) := Over.homMk (𝟙 _) (Category.id_comp _)
  have hte : toBase hg.w t₀ = e ≫ y := by
    ext
    exact ht₀.trans (Category.id_comp _).symm
  have htt : t₀ * t₀ = 1 := by
    refine toBase_injective hg ?_
    rw [hm, hte, toBase_one hg hm, ← MonObj.comp_mul, hy, MonObj.comp_one]
  have hwL : LBIso (A.L.pull g) P.L := ⟨w, hw⟩
  obtain ⟨c, hc⟩ := GlobalTheory.Moduli.cube_of_isLB _ P P.L P.isLB
  let A₁ : PolAV (Sp K') :=
    { A := P.A, isAb := P.isAb, g := P.g, smoothDim := P.smoothDim, L := rigTransl P.L t₀
      isLB := DVR.linComb_isLB _ P.isLB _ _
      rigid := rigidified_rigTransl P.isLB
      sym := sym_rigTransl htt P.isLB P.sym
      ample := relAmple_rigTransl htt P.isLB P.ample
      ktriv := kTriv_rigTransl htt P.isLB P.ktriv }
  obtain ⟨β₂, hsq, hlam⟩ := GlobalTheory.Mum.lbIso_lam_pull_of_isGrpPullback _ _ _ A.A P.A g hpb
  have hLamA : (abelian₂ A.A A.L).IsLB := DVR.linComb_isLB _ A.isLB _ _
  have hLamP : (abelian₂ P.A P.L).IsLB := DVR.linComb_isLB _ P.isLB _ _
  have h3 := hlam A.L P.L _ (abelian₂ A.A A.L) (𝟙 _) A.isLB P.isLB hLamA hwL.symm (GlobalTheory.DescendedPrincipal.lbIso_pull_id hLamA).symm
  rw [Category.comp_id] at h3
  have h1 : LBIso (abelian₂ A₁.A A₁.L) ((abelian₂ P.A P.L).pull (𝟙 _)) := lam_rigTransl P.isLB c hc
  refine ⟨A₁, g, β₂, t₀, hpb, hsq, ?_, ht₀, GlobalTheory.PelPrim.lbIso_linComb hwL.symm _ _⟩
  exact LBIso.trans (DVR.linComb_isLB _ A₁.isLB _ _) (pull_isLB hLamP _) (pull_isLB hLamA _) h1
    (LBIso.trans (pull_isLB hLamP _) hLamP (pull_isLB hLamA _) (GlobalTheory.DescendedPrincipal.lbIso_pull_id hLamP) h3)

end GlobalTheory.BaseTransl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseMulSectionOfGermDvdFlatDomainStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_baseMul_section_of_germ_dvd_flat_domain : ∀ (R : Type) [CommRing R] [IsDomain R] (X : Scheme.{0}) (p : X ⟶ Spec (CommRingCat.of R)), Flat p → ∀ (L : LB X) (s : LB.Sec L) (q : R), q ≠ 0 → (∀ (x : X) j, x ∈ L.U j → ∃ t, gs (𝟙 X) x (L.U j) (s.f j) = cst p x q * t) → ∃ t : LB.Sec L, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul p q s t := by
  first | exact @GlobalTheory.Mum.exists_secIsMul_of_germ_dvd | exact GlobalTheory.Mum.exists_secIsMul_of_germ_dvd | (intros; apply GlobalTheory.Mum.exists_secIsMul_of_germ_dvd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenBetweenFinsetAndOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_basicOpen_between_finset_and_open : ∀ (X : Scheme.{0}) (W : X.Opens), IsAffineOpen W → ∀ (V : X.Opens), V ≤ W → ∀ s : Finset X, (∀ x ∈ s, x ∈ V) → ∃ f : Γ(X, W), X.basicOpen f ≤ V ∧ ∀ x ∈ s, x ∈ X.basicOpen f := by
  classical
  intro X W hW V hVW s hs
  rcases s.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · refine ⟨0, ?_, fun x hx => absurd hx (Finset.notMem_empty x)⟩
    rw [Scheme.basicOpen_zero]
    exact bot_le
  set Z : Set (PrimeSpectrum Γ(X, W)) := {p | hW.fromSpec p ∉ V} with hZ
  have hZc : IsClosed Z := by
    have h := (hW.fromSpec ⁻¹ᵁ V).isOpen.isClosed_compl
    exact h
  let P : X → Ideal Γ(X, W) := fun x => if h : x ∈ W then (hW.primeIdealOf ⟨x, h⟩).asIdeal else ⊤
  have hPx : ∀ x (h : x ∈ W), P x = (hW.primeIdealOf ⟨x, h⟩).asIdeal := fun x h => by
    simp only [P, dif_pos h]
  have hP : ∀ i ∈ s, i ≠ x₀ → i ≠ x₀ → (P i).IsPrime := by
    intro x hx _ _
    rw [hPx x (hVW (hs x hx))]
    exact (hW.primeIdealOf _).isPrime
  have key : ¬ ((PrimeSpectrum.vanishingIdeal Z : Set Γ(X, W)) ⊆
      ⋃ i ∈ (↑s : Set X), (P i : Set Γ(X, W))) := by
    rw [Ideal.subset_union_prime x₀ x₀ hP]
    rintro ⟨x, hx, hle⟩
    have hxW : x ∈ W := hVW (hs x hx)
    rw [hPx x hxW] at hle
    have hmem : hW.primeIdealOf ⟨x, hxW⟩ ∈
        PrimeSpectrum.zeroLocus (PrimeSpectrum.vanishingIdeal Z : Set Γ(X, W)) :=
      (PrimeSpectrum.mem_zeroLocus _ _).2 hle
    rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hZc.closure_eq] at hmem
    apply hmem
    show hW.fromSpec (hW.primeIdealOf ⟨x, hxW⟩) ∈ V
    rw [hW.fromSpec_primeIdealOf]
    exact hs x hx
  obtain ⟨f, hfI, hfP⟩ := Set.not_subset.mp key
  refine ⟨f, ?_, ?_⟩
  · intro y hy
    have hyW : y ∈ W := X.basicOpen_le f hy
    obtain ⟨p, rfl⟩ : y ∈ Set.range hW.fromSpec := by rw [hW.range_fromSpec]; exact hyW
    have hp : p ∈ hW.fromSpec ⁻¹ᵁ X.basicOpen f := hy
    rw [hW.fromSpec_preimage_basicOpen] at hp
    by_contra hnot
    have hpZ : p ∈ Z := hnot
    exact (PrimeSpectrum.mem_basicOpen _ _).1 hp
      ((PrimeSpectrum.mem_vanishingIdeal _ _).1 hfI p hpZ)
  · intro x hx
    have hxW : x ∈ W := hVW (hs x hx)
    have hf : f ∉ (hW.primeIdealOf ⟨x, hxW⟩).asIdeal := by
      intro h
      apply hfP
      rw [Set.mem_iUnion₂]
      exact ⟨x, hx, by rw [hPx x hxW]; exact h⟩
    have hmem : hW.primeIdealOf ⟨x, hxW⟩ ∈ hW.fromSpec ⁻¹ᵁ X.basicOpen f := by
      rw [hW.fromSpec_preimage_basicOpen]
      exact (PrimeSpectrum.mem_basicOpen _ _).2 hf
    have h2 : hW.fromSpec (hW.primeIdealOf ⟨x, hxW⟩) ∈ X.basicOpen f := hmem
    rwa [hW.fromSpec_primeIdealOf] at h2

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenCoverAlgebraPointLiesInCoverStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basicOpen_cover_algebraPoint_liesInCover : ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (K : Type) (W : K → X.left.Opens), ⨆ i, W i = ⊤ → ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt X D), ∃ (n : ℕ) (s : Fin n → D), Ideal.span (Set.range s) = ⊤ ∧ ∀ a, Sm W (spOver (IsScalarTower.toAlgHom R D (Localization.Away (s a))) ≫ x) := by
  first | exact @GlobalTheory.PtExt.exists_away_cover_sm | exact GlobalTheory.PtExt.exists_away_cover_sm | (intros; apply GlobalTheory.PtExt.exists_away_cover_sm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBundleIsoRescaledPreservingRigidification
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
namespace GlobalTheory.Mum.RigScale

private theorem mem_pull_lemma {X X' Y : Scheme.{0}} {L : LB X} {F : X' ⟶ X} (f : Y ⟶ X') (y : Y) (i : L.ι)
    (hi : F (f y) ∈ L.U i) : f y ∈ (L.pull F).U (fun _ => i) := by
  simp only [LB.pull, LB.LinComb, LB.wchart]
  simpa using hi

private theorem mem_U_of_mem_pull_U {X X' Y : Scheme.{0}} {L : LB X} {F : X' ⟶ X} (f : Y ⟶ X') (y : Y) (i : L.ι)
    (hi : f y ∈ (L.pull F).U (fun _ => i)) : F (f y) ∈ L.U i := by
  simp only [LB.pull, LB.LinComb, LB.wchart] at hi
  simpa using hi

set_option maxHeartbeats 1000000 in
private theorem pgen_of_isGen {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}
    (w : LB.Iso L' (L.pull F)) (hw : LB.Gen.IsGen w) : PGen w := by
  intro Y f y j j' k k' h1 h2 h3 h4
  have m1 := mem_pull_lemma f y j h1
  have m2 := mem_pull_lemma f y j' h2
  have hy : f y ∈ ((L.pull F).div L').U (fun _ => j, k) ⊓ ((L.pull F).div L').U (fun _ => j', k') :=
    ⟨⟨m1, h3⟩, ⟨m2, h4⟩⟩
  have e := congrArg (gm f y _) (hw (fun _ => j, k) (fun _ => j', k'))
  rw [map_mul, gm_res _ _ _ hy, gm_res _ _ _ hy] at e
  unfold gw
  refine e.trans ?_
  congr 1
  refine (map_mul (gm f y _) _ _).trans ?_
  congr 1
  · refine (gm_res f y _ hy _).trans ?_
    simp only [LB.pull, LB.LinComb, Finset.univ_unique, Finset.prod_singleton, zpow_one]
    refine (gm_res f y _ (show f y ∈ (L.pull F).U (fun _ => j) ⊓ (L.pull F).U (fun _ => j') from ⟨m1, m2⟩) _).trans ?_
    exact gm_pull f F y (L.U j ⊓ L.U j') ⟨h1, h2⟩ _
  · refine (map_inv (gm f y _) _).trans ?_
    congr 1
    exact gm_res f y _ hy _

set_option maxHeartbeats 1000000 in
private theorem isGen_of_pgen {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}
    (w : LB.Iso L' (L.pull F)) (hw : PGen w) : LB.Gen.IsGen w := by
  rintro ⟨a, k⟩ ⟨a', k'⟩
  apply unit_ext
  intro x hx
  have m1 : (𝟙 X') x ∈ (L.pull F).U (fun _ => a PUnit.unit) := hx.1.1
  have m2 : (𝟙 X') x ∈ (L.pull F).U (fun _ => a' PUnit.unit) := hx.2.1
  have n1 := mem_U_of_mem_pull_U (𝟙 X') x (a PUnit.unit) m1
  have n2 := mem_U_of_mem_pull_U (𝟙 X') x (a' PUnit.unit) m2
  have h := hw X' (𝟙 X') x (a PUnit.unit) (a' PUnit.unit) k k' n1 n2 hx.1.2 hx.2.2
  unfold gw at h
  rw [map_mul, gm_res, gm_res]
  · refine h.trans ?_
    symm
    congr 1
    refine (map_mul (gm (𝟙 X') x _) _ _).trans ?_
    congr 1
    · refine (gm_res (𝟙 X') x _ hx _).trans ?_
      simp only [LB.pull, LB.LinComb, Finset.univ_unique, Finset.prod_singleton, zpow_one]
      refine (gm_res (𝟙 X') x _ (show (𝟙 X') x ∈ (L.pull F).U (fun _ => a PUnit.unit) ⊓ (L.pull F).U (fun _ => a' PUnit.unit) from ⟨m1, m2⟩) _).trans ?_
      exact gm_pull (𝟙 X') F x (L.U (a PUnit.unit) ⊓ L.U (a' PUnit.unit)) ⟨n1, n2⟩ _
    · refine (map_inv (gm (𝟙 X') x _) _).trans ?_
      congr 1
      exact gm_res (𝟙 X') x _ hx _
  all_goals first | exact hx | skip

theorem exists_rig_rescale : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R') (D₂ : DegPre R) (D₃ : DegPre R') (Φ : D₃.P.A.left ⟶ D₂.P.A.left), IsGrpPullback D₃.P.A D₂.P.A (spMap ρ) Φ → ∀ w₀ : LB.Iso D₃.P.L (D₂.P.L.pull Φ), PGen w₀ → ∃ w : LB.Iso D₃.P.L (D₂.P.L.pull Φ), PGen w ∧ PMaps w (K := PUnit) (fun _ => eSec D₃.P.A) (fun _ => eSec D₂.P.A) (fun _ => 1) D₃.rig D₂.rig (spMap ρ) := by
  intro R R' _ _ _ _ ρ D₂ D₃ Φ hΦ w₀ hw₀
  have hσ : eSec D₃.P.A ≫ D₃.P.A.hom = 𝟙 _ := Over.w (η[D₃.P.A])
  obtain ⟨w, hw, hm⟩ := GlobalTheory.UnifPreCompare.exists_rigidified (F := Φ) D₂.P.isLB D₃.P.isLB D₃.P.A.hom
    (eSec D₃.P.A) hσ w₀ (isGen_of_pgen w₀ hw₀) D₃.rig D₃.rig_gen D₂.rig D₂.rig_gen (spMap ρ)
    (GlobalTheory.PolBaseChange.eSec_comm hΦ)
  exact ⟨w, pgen_of_isGen w hw, hm⟩

end GlobalTheory.Mum.RigScale
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCentreOfValuationSubringProperDominantStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
open GlobalTheory.Discrepancy GlobalTheory.EtaleKlt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_centre_of_valuationSubring_proper_dominant : ∀ {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (s : Y ⟶ X) [IsDominant s] [IsProper s]
    (V : ValuationSubring Y.functionField) (x : X), (∀ f, RegAt x f → functionFieldMap s f ∈ V) →
    ∃ y : Y, s y ⤳ x ∧ ∀ f, RegAt y f → f ∈ V := by
  first | exact @GlobalTheory.ProperCentre.exists_regAt_centre | exact GlobalTheory.ProperCentre.exists_regAt_centre | (intros; apply GlobalTheory.ProperCentre.exists_regAt_centre <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCharacterSymmetricDefectTwiceFieldExtStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_character_symmetricDefect_twice_fieldExt : ∀ (k k' : Type) [CommRing k] [CommRing k'], IsField k → IsField k' → ∀ (ρ : k →+* k') (G₀ : Over (Sp k)) [GrpObj G₀] [IsCommMonObj G₀] (G'₀ : Over (Sp k')) [GrpObj G'₀] [IsCommMonObj G'₀] (β₀ : G'₀.left ⟶ G₀.left) (hβ₀ : IsGrpPullback G'₀ G₀ (spMap ρ) β₀) (P₀ : GlobalTheory.UU.CP G₀) (P'₀ : GlobalTheory.UU.CP G'₀) (w₀ : LB.Iso P'₀.L.L (P₀.L.L.pull β₀)), GlobalTheory.UU.IsCPMap P'₀ P₀ (spMap ρ) β₀ hβ₀.1.w w₀ → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (i : splitTorus (Sp k) X ⟶ G₀) (i₁ : splitTorus (Sp k') X ⟶ G'₀), IsMonHom i → IsMonHom i₁ → GlobalTheory.UU.TorusCompat (spMap ρ) β₀ i₁ i → ∀ (σ : GlobalTheory.UU.CubTriv P₀.c i) (σ₁ : GlobalTheory.UU.CubTriv P'₀.c i₁), GlobalTheory.UU.CubTriv.Even (P := P'₀) σ₁ → ∃ χ : X, GlobalTheory.UU.CubTriv.Even (P := P₀) (σ.twist χ) := by
  first | exact @GlobalTheory.TwistCompare.exists_twist_even | exact GlobalTheory.TwistCompare.exists_twist_even | (intros; apply GlobalTheory.TwistCompare.exists_twist_even <;> assumption)
end

