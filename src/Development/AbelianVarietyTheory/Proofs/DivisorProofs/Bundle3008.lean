import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2924
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2923
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0104
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleGeneratorExtendingDensePart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2871
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0072
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RangeSubsetAbLocusOfIsProper
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2952
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2034
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2033
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2035
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2075
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2159
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2180
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2801
import Development.AbelianVarietyTheory.Definitions.Divisors.StepsNonvacuous
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2925
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2829
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0085
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreSemiAbelianEndoTorsionExtendStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericFibre_semiAbelian_endo_torsion_extend : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), (U₀ : Set M.Z).Nonempty → ∃ (A₀ : Over (Sp Ω)) (_ : GrpObj A₀) (a₀ : A₀.left ⟶ ρ.P.A.left) (ψ : A₀.left ⟶ FinalForm.G.left), IsGrpPullback A₀ ρ.P.A (spMap S.R.val.toRingHom) a₀ ∧ IsGrpPullback A₀ FinalForm.G M.pt ψ ∧ (∀ e : ρ.P.A ⟶ ρ.P.A, IsMonHom e → ∃ F : FinalForm.G ⟶ FinalForm.G, IsMonHom F ∧ ∀ e₀ : A₀ ⟶ A₀, e₀.left ≫ a₀ = a₀ ≫ e.left → e₀.left ≫ ψ = ψ ≫ F.left) ∧ ∀ b : S.Gam, ∃ gγ : Over.mk M.pt ⟶ FinalForm.G, gγ ^ (S.r * S.N) = 1 ∧ (∀ w : Sp Ω ⟶ A₀.left, w ≫ A₀.hom = 𝟙 _ → w ≫ a₀ = spMap S.R.val.toRingHom ≫ (ρ.pt b).left → w ≫ ψ = gγ.left) ∧ ∀ z, b ∈ S.HH M z → ExtNear gγ z := by
  first | exact @GlobalTheory.Poinc.FibLat.genFibre_endo_torsion | exact GlobalTheory.Poinc.FibLat.genFibre_endo_torsion | (intros; apply GlobalTheory.Poinc.FibLat.genFibre_endo_torsion <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointMapOverRingHomUniqueStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericPointMap_over_ringHom_unique : ∀ {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (θ : R →+* V) (κ κ' : Sp (FractionRing V) ⟶ Sp (FractionRing R)), κ ≫ jK R = jK V ≫ spMap θ → κ' ≫ jK R = jK V ≫ spMap θ → κ = κ' := by
  first | exact @GlobalTheory.TInj.genPt_map_unique | exact GlobalTheory.TInj.genPt_map_unique | (intros; apply GlobalTheory.TInj.genPt_map_unique <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointsSubsetAbLocus
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.RigCube

theorem genericPoints_subset_abLocus {R : Type} [CommRing R] [IsDomain R] (G : Over (Sp R)) [GrpObj G]
    (hG : IsSemiAbelian G) (hp : IsProper (pullback.snd G.hom (jK R))) : genericPoints (Sp R) ⊆ abLocus G := by
  have : IsProper ((Over.pullback (jK R)).obj G).hom := hp
  refine Set.Subset.trans ?_ (range_subset_abLocus_of_isProper (G' := (Over.pullback (jK R)).obj G) hG
    (IsPullback.of_hasPullback G.hom (jK R)))
  rw [genericPoints_eq_singleton, genericPoint_eq_bot_of_affine]
  rintro _ rfl
  refine ⟨(⊥ : PrimeSpectrum (FractionRing R)), PrimeSpectrum.ext ?_⟩
  exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R (FractionRing R))

theorem exists_gen_theta_generic {R : Type} [CommRing R] [IsDomain R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    (hG : IsSemiAbelian G) (hp : IsProper (pullback.snd G.hom (jK R))) {M : LB G.left} (hM : M.IsLB) :
    ∃ t : ((Theta G M).pull (pullback.fst (G3 G).hom (jK R))).Gen, t.IsGen := by
  let j := jK R
  let A : Over (Spec (CommRingCat.of (FractionRing R))) := (Over.pullback j).obj G
  have gp : IsGrpPullback A G j (pullback.fst G.hom j) := isGrpPullback_pullback G j
  have hA : IsSemiAbelian A := IsSemiAbelian.pullback j G hG
  have : IsProper A.hom := hp
  have hAb : IsAbelianScheme A := AbelianSchemeGerms.isAbelianScheme_of_proper A hA
  have := hA.comm
  let P : Over (Spec (CommRingCat.of (FractionRing R))) := Over.mk (pullback.snd (G3 G).hom j)
  let x : Fin 3 → (P ⟶ A) := fun i => Over.homMk
    (gp.1.lift (pullback.fst _ _ ≫ (x3 G i).left) P.hom (by
      rw [Category.assoc, Over.w]; exact pullback.condition)) (gp.1.lift_snd _ _ _)
  let U : Over.mk (P.hom ≫ j) ⟶ G3 G := Over.homMk (pullback.fst (G3 G).hom j) pullback.condition
  have hx : ∀ i, pushPt gp.1.w (x i) = U ≫ x3 G i := fun i => Over.OverMorphism.ext (gp.1.lift_fst _ _ _)
  let πA := pullback.fst G.hom j
  let pf := pullback.fst (G3 G).hom j
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.CubeTop.cubeTheorem _ A hAb (M.pull πA) (pull_isLB hM _) P (x 0) (x 1) (x 2)
  obtain ⟨t₁, ht₁⟩ := CubeDescent.exists_gen_comp M πA _ _ t₀ ht₀
  let y : Fin 3 → (Over.mk (P.hom ≫ j) ⟶ G) := fun i => U ≫ x3 G i
  have key : ∀ z : P ⟶ A, z.left ≫ πA = (pushHom gp P z).left := fun z => rfl
  have hxp : ∀ i, pushHom gp P (x i) = y i := hx
  have e : lift (y 0) (lift (y 1) (y 2)) = U := by ext <;> simp [y, x3]
  obtain ⟨t₂, ht₂, -⟩ := exists_gen hM (φ' := fun I => pf ≫ thφ G (x3 G) I) (ε' := thε) (fun V _ h => by
    have hθ := prod_cub (y 0) (y 1) (y 2) h
    rw [e] at hθ
    refine Eq.trans ?_ hθ.symm
    simp only [Fin.prod_univ_eight, key, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, map_mul, map_one, hxp, zpow_one, zpow_neg_one]
    simp only [Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_succ, key, map_mul, map_one, hxp,
      zpow_one, zpow_neg_one]) t₁ ht₁
  let c := CechPic.cls M hM
  refine (CechPic.cls_eq_zero_iff (pull_isLB (LB.isLB_linComb hM _ _) pf)).1 ?_
  rw [CechPic.cls_pull (LB.isLB_linComb hM _ _), CechPic.cls_linComb hM, map_sum]
  simp only [map_zsmul, ← CechPic.pull_comp]
  have h2 := (CechPic.cls_eq_zero_iff (LB.isLB_linComb hM (fun I => pf ≫ thφ G (x3 G) I) thε)).2 ⟨t₂, ht₂⟩
  rw [CechPic.cls_linComb hM] at h2
  exact h2

theorem exists_rigLB_cubicalStr : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → IsProper (pullback.snd G.hom (jK R)) → ∀ M : LB G.left, M.IsLB → ∃ (L : RigLB G) (_ : CubicalStr G L), L.L = M := by
  intro R _ _ _ _ _ G _ _ hG hp M hM
  have hab := genericPoints_subset_abLocus G hG hp
  have a₁ := hG.smooth
  have := hG.geomConnected
  have b₁ := GlobalTheory.grpObj_geometricallyIntegral_of_smooth _ G
  obtain ⟨a₂, b₂, -⟩ := GlobalTheory.smooth_geometricallyIntegral_abLocus_tensorObj _ G G a₁ a₁ b₁ b₁
  obtain ⟨a₃, b₃, -⟩ := GlobalTheory.smooth_geometricallyIntegral_abLocus_tensorObj _ G _ a₁ a₂ b₁ b₂
  obtain ⟨r, hr⟩ := DVR.exists_gen_of_isLB_local (V := R) (M.pull (eSec G)) (pull_isLB hM _)
  let L : RigLB G := ⟨M, r, hM, hr⟩
  have hΘ : (Theta G M).IsLB := LB.isLB_linComb hM _ _
  have h₁ : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have h₂ : Flat (jK R) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ (nonZeroDivisors R))
  let e : 𝟙_ (Over (Sp R)) ⟶ G3 G := lift 1 (lift 1 1)
  obtain ⟨t, ht⟩ := GenericExtend.exists_isGen_of_densePart (Sp R) _ (jK R) (ZJ.isNormalScheme_sp R) h₁ h₂
    DVR.isDominant_jK inferInstance (G3 G) e.left (Theta G M) (Over.w e) a₃ b₃ hΘ
    (DVR.exists_gen_of_isLB_local _ (pull_isLB hΘ _)) (exists_gen_theta_generic G hG hp hM)
  obtain ⟨c⟩ := (CubeGen.cubical_and_symmetric (Sp R) G L hG ⟨inferInstance, hab⟩).1 ⟨t, ht⟩
  exact ⟨L, c, rfl⟩

end GlobalTheory.RigCube
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricFromPageEstimate
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn

section Comparison₂

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem indefinitePoint_splitPartContent_eq_forcedContent (p : PtAt ex Csz) (C CH : ℝ) :
    Formalism.L2.Indef.Tree.DepthCond.ContentEqualsDatumContent ((R2 p).num (F2 p) C CH) (GlobalTheory.RunDepth.numOf D L) (fun j : Fin D.R.m => (j : ℕ) + 1) := by
  intro w j
  rw [numOf_Fj_eq_ofRecord D L p.Del p.h0 p.hDel p.hh0]
  rfl

end Comparison₂

theorem geoSt_of_pageSt : PageSt → GeoSt := by
  intro hP
  obtain ⟨CK, xa, HR⟩ := runsHold_of_ties
  obtain ⟨xb, HL⟩ := leaves_sup_span_data CK
  obtain ⟨Cd, HD⟩ := leafDepth_all_record
  refine ((hP.and (GlobalTheory.T.runNumericalConditions_hold_along_family xa)).and (GlobalTheory.T.runNumericalConditions_hold_along_family xb)).imp fun Fm CH _ H => ?_
  obtain ⟨⟨⟨c0, hc0⟩, ⟨ya, hya⟩⟩, ⟨yb, hyb⟩⟩ := H
  refine ⟨max c0 Cd, fun c hc hbad => ?_⟩
  obtain ⟨x0, hx0⟩ := hc0 c ((le_max_left _ _).trans hc) hbad
  refine ⟨max x0 (max ya yb), fun x hx hle i p hrows hmore r O hrec => ?_⟩
  have h0 : x0 ≤ x := (le_max_left _ _).trans hle
  have ha : ya ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hle
  have hb : yb ≤ x := ((le_max_right _ _).trans (le_max_right _ _)).trans hle
  obtain ⟨hPg, hSz, -, -, -, -, hOb, -, -⟩ := hx0 x hx h0 i p hrows hmore r O hrec
  obtain ⟨pna, hx3, hkb, hxe, -⟩ := hya x hx ha i
  obtain ⟨pnb, -, -, -, -⟩ := hyb x hx hb i
  have hcore := hmore.2.1
  have hown := hrec.2
  have hch := (GlobalTheory.T.second_link_of_weight_rows _ _ _ _ _ _ _ _ _ _ p hrows hmore.1).1
  have hRH := HR _ _ _ _ _ _ _ (F2 p) _ _ _ _ _ _ (Fm.ex x hx i).kap_def _ _ hcore hrec.1.ok hown pna
  obtain ⟨hSup, hSpan, hS, hData⟩ := HL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ O hrec.1 hcore hown pnb hRH hch.grp
    hch.tup.mu_conj hch.tup.mu_off hch.tup.mu_ne
  refine ⟨hSup, hSpan, hS, hData, hasIndexBound_of_runs CK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ O hrec.1 hcore hown hRH hSup hSpan
    hOb, fun C CH' => ?_⟩
  exact HD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ O hrec.1 _ hPg hSz hx3 hkb (indefinitePoint_splitPartContent_eq_forcedContent p C CH')
    ((le_max_right _ _).trans hc) (le_of_eq pna.2.1.symm) hxe

end GlobalTheory.BigOn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricTorsionPointAbelianPartLiesUnderClassZeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometricTorsionPoint_abelianPart_lies_under_classZero : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V) D A G) (N : ℕ), 1 ≤ N → ∀ β : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ D.toPre.P.A, β ^ N = 1 → ∃ xb : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ A.A, xb ^ N = 1 ∧ (∃ p : QkPt D.toPre (AlgebraicClosure (FractionRing V)) N, p.y = 0 ∧ QkToAkU U.toUnifPre (AlgebraicClosure (FractionRing V)) N p xb) ∧ ∀ p : QkPt D.toPre (AlgebraicClosure (FractionRing V)) N, p.y = 0 → QkToAkU U.toUnifPre (AlgebraicClosure (FractionRing V)) N p xb → p.g.b = β := by
  first | exact @GlobalTheory.Poinc.IntTerm.torsion_lies_under | exact GlobalTheory.Poinc.IntTerm.torsion_lies_under | (intros; apply GlobalTheory.Poinc.IntTerm.torsion_lies_under <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricTorsionPointGenericFibreMemberHasLabelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometricTorsionPoint_genericFibre_member_has_label : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (xb : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ 𝔪.A.A), xb ^ (X₁.S.r * X₁.S.N) = 1 → ∃ a : X₁.S.Gam, xb.left ≫ 𝔪.φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) ≫ (X₁.ρ.pt a).left := by
  first | exact @GlobalTheory.Poinc.IntTerm.torsion_has_label | exact GlobalTheory.Poinc.IntTerm.torsion_has_label | (intros; apply GlobalTheory.Poinc.IntTerm.torsion_has_label <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermExistenceOfChartStatement
section
open GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatJet.An
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.germ_existence_of_chart : Chart → HolLift → GermEx := by
  first | exact @GlobalTheory.LatJet.An.germEx_of_chart_holLift | exact GlobalTheory.LatJet.An.germEx_of_chart_holLift | (intros; apply GlobalTheory.LatJet.An.germEx_of_chart_holLift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalOneFormsPrimitiveAbelianSchemeStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.globalOneForms_primitive_abelianScheme : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → GlobalTheory.AbCoh.PrimF A := by
  first | exact @GlobalTheory.AbCoh.primF_of_isAbelianScheme | exact GlobalTheory.AbCoh.primF_of_isAbelianScheme | (intros; apply GlobalTheory.AbCoh.primF_of_isAbelianScheme <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GluedSectionGenericValueNonvanishingStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glued_section_generic_value_nonvanishing : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (K : Type) [Field K] (ξ : Sp K ⟶ S)
    (V : S.Opens) (κ : Type) (N : κ → S.Opens) (s : ∀ k, LocSec G L (N k)) (s' : LocSec G L V)
    (v : SecM G L 1 (Over.mk ξ)) (hN : ∀ k, N k ≤ V), (⨆ k, N k) = V →
    (∀ k i, resG _ (fun _ hx => ⟨hx.1, hN k hx.2⟩ : L.U i ⊓ G.hom ⁻¹ᵁ N k ≤ L.U i ⊓ G.hom ⁻¹ᵁ V) (s' i) = s k i) →
    (∀ k, GenIs ξ (s k) v) → (∀ k, FibNz (s k) (N k)) → (Nonempty κ → GenIs ξ s' v) ∧ FibNz s' V := by
  first | exact @GlobalTheory.UMin.ThBdl.Glued.glued | exact GlobalTheory.UMin.ThBdl.Glued.glued | (intros; apply GlobalTheory.UMin.ThBdl.Glued.glued <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GluingOfConnectednessStatement
section
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gluing_of_connectedness : ConnSt → GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.PropZ → GlueSt := by
  first | exact @GlobalTheory.FlatModel.glueSt_of | exact GlobalTheory.FlatModel.glueSt_of | (intros; apply GlobalTheory.FlatModel.glueSt_of <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramLowerTriangularFactorGradedLengthSmooth
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

theorem leadMinor_re_pos_of_posDef {s : ℕ} {G : Matrix (Fin s) (Fin s) ℂ} (hG : G.PosDef) (j : ℕ) :
    0 < (leadMinor G j).re := by
  have hsub : (G.submatrix (Subtype.val : {a : Fin s // (a : ℕ) < j} → Fin s) Subtype.val).PosDef :=
    hG.submatrix Subtype.val_injective
  have h := hsub.det_pos
  unfold leadMinor
  exact (Complex.pos_iff.mp h).1

theorem contDiffAt_leadMinor {n s : ℕ} {G : V n → Matrix (Fin s) (Fin s) ℂ} {v : V n}
    (h : MContDiffAt ∞ G v) (j : ℕ) : ContDiffAt ℝ ∞ (fun x => leadMinor (G x) j) v :=
  (h.submatrix _ _).det

theorem ldPart_grD_smooth : ∀ (n s : ℕ) (G : V n → Matrix (Fin s) (Fin s) ℂ) (v : V n), MContDiffAt ∞ G v → (G v).PosDef →
    MContDiffAt ∞ (fun x => ldPart (G x)) v ∧ ∀ i, ContDiffAt ℝ ∞ (fun x => grD (G x) i) v := by
  intro n s G v hG hp
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · have hnum : ContDiffAt ℝ ∞ (fun x => ((G x).submatrix
        (fun a : {a : Fin s // (a : ℕ) < j + 1} => if a.1 = j then i else a.1) Subtype.val).det) v :=
      (hG.submatrix _ _).det
    have hden := contDiffAt_leadMinor hG (j : ℕ)
    have hne : leadMinor (G v) j ≠ 0 := fun h0 => by
      have := leadMinor_re_pos_of_posDef hp j
      rw [h0] at this; simp at this
    simp only [ldPart, Matrix.of_apply]
    exact hnum.mul (hden.inv hne)
  · have hnum : ContDiffAt ℝ ∞ (fun x => (leadMinor (G x) (i + 1)).re) v :=
      Complex.reCLM.contDiff.contDiffAt.comp v (contDiffAt_leadMinor hG _)
    have hden : ContDiffAt ℝ ∞ (fun x => (leadMinor (G x) i).re) v :=
      Complex.reCLM.contDiff.contDiffAt.comp v (contDiffAt_leadMinor hG _)
    exact hnum.div hden (leadMinor_re_pos_of_posDef hp i).ne'

end GlobalTheory.ChernCalc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramLowerTriangularFactorPosDefProperties
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

variable {s : ℕ} {G : Matrix (Fin s) (Fin s) ℂ}

theorem leadMinor_pos_of_posDef (h : G.PosDef) (j : ℕ) : 0 < (leadMinor G j).re ∧ (leadMinor G j).im = 0 := by
  have h1 : 0 < leadMinor G j := (h.submatrix Subtype.val_injective).det_pos
  rw [Complex.lt_def] at h1
  exact ⟨by simpa using h1.1, by simpa using h1.2.symm⟩

theorem ldPart_diag_of_posDef (h : G.PosDef) (i : Fin s) : 0 < grD G i ∧ ldPart G i i = grD G i := by
  obtain ⟨a1, a2⟩ := leadMinor_pos_of_posDef h ((i : ℕ) + 1)
  obtain ⟨b1, b2⟩ := leadMinor_pos_of_posDef h (i : ℕ)
  refine ⟨div_pos a1 b1, ?_⟩
  have e : (fun a : {a : Fin s // (a : ℕ) < (i : ℕ) + 1} => if a.1 = i then i else a.1) = Subtype.val := by
    funext a
    split_ifs with ha
    · exact ha.symm
    · rfl
  have ea : leadMinor G ((i : ℕ) + 1) = ((leadMinor G ((i : ℕ) + 1)).re : ℂ) :=
    Complex.ext (by simp) (by simpa using a2)
  have eb : leadMinor G (i : ℕ) = ((leadMinor G (i : ℕ)).re : ℂ) :=
    Complex.ext (by simp) (by simpa using b2)
  simp only [ldPart, Matrix.of_apply, grD]
  rw [e, Complex.ofReal_div, ← ea, ← eb]
  rfl

theorem ldPart_eq_zero_of_lt (G : Matrix (Fin s) (Fin s) ℂ) {i j : Fin s} (hij : i < j) : ldPart G i j = 0 := by
  have hij' : (i : ℕ) < j := hij
  simp only [ldPart, Matrix.of_apply]
  rw [Matrix.det_zero_of_row_eq (i := ⟨i, by omega⟩) (j := ⟨j, by omega⟩), zero_div]
  · intro h
    exact hij.ne (congrArg Subtype.val h)
  · funext b
    simp [Matrix.submatrix_apply]

theorem ldPart_posDef_spec : ∀ (s : ℕ) (G : Matrix (Fin s) (Fin s) ℂ), G.PosDef → (∀ j, 0 < (leadMinor G j).re ∧ (leadMinor G j).im = 0) ∧ (∀ i, 0 < grD G i ∧ ldPart G i i = grD G i) ∧ (∀ i j, i < j → ldPart G i j = 0) ∧ IsUnit (ldPart G).det := by
  intro s G h
  refine ⟨leadMinor_pos_of_posDef h, ldPart_diag_of_posDef h, fun i j hij => ldPart_eq_zero_of_lt G hij, ?_⟩
  rw [Matrix.det_of_lowerTriangular (ldPart G) (fun i j hij => ldPart_eq_zero_of_lt G (by simpa using hij)),
    isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
  intro i _
  obtain ⟨h1, h2⟩ := ldPart_diag_of_posDef h i
  rw [h2]
  exact_mod_cast h1.ne'

end GlobalTheory.ChernCalc
end

