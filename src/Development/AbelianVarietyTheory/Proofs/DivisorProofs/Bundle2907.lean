import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0084
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2554
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2643
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2801
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0092
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2807
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2332
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0051
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsSharpAndPrim
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0194
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2512
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2773
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2631
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2785
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0085
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2584
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2565
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2453
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingRiemannForm
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UnifMetricScalar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0031
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0894
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2687
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2846
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2516
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2808
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2739

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPeriodsPulledDegenerationData
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TauPullOn

open GlobalTheory.HalfBC GlobalTheory.PrimCocycle GlobalTheory.ArcPull GlobalTheory.FactorPull
open GlobalTheory.PsiEvenPull (proj)

variable {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {θ : R →+* V} {D₀ : DegPre R}
  {D₁ : DegPre V} (hD : IsPullDeg θ D₀ D₁) {z : (TK V).left} {J : ((TK V).left ⟶ D₀.P.A.left) → D₀.P.L.ι}
  {J₁ : ((TK V).left ⟶ D₁.P.A.left) → D₁.P.L.ι} (hJ : Good D₀.P.L z J) (hJ₁ : Good D₁.P.L z J₁)
include hJ hJ₁

theorem psiW_val (x : D₁.X) : val (hD.psiW.psi (hD.xe x)) hD.g z J =
    (om hD.w z J J₁ (D₁.xK x))⁻¹ * val (D₁.psi x) (𝟙 _) z J₁ := by
  have e := PsiEvenPull.psi_pull hD x (𝟙 _) z hJ hJ₁
  simp only [Category.id_comp] at e
  exact e

theorem rigW_val : val (D₀.rigW hD.W) hD.g z J =
    om hD.w z J J₁ (1 : TK V ⟶ D₁.P.A).left * val D₁.rigK (𝟙 _) z J₁ := by
  have pm := (maps_iff hD.w _ (fun _ => eSec D₀.P.A) _ D₁.rig D₀.rig (specOf θ) _
    (rigPull_le (proj hD) (specOf θ) hD.he D₀.P.L) (fun _ => rfl)).1 hD.w_rig
  have e := pmaps_om (fun _ => hD.he) pm (jK V) z hJ hJ₁
  rw [Fintype.prod_unique, zpow_one] at e
  refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (congrArg₂ (· * ·) rfl (val_pull hJ₁ _ _ _).symm))
  rw [Category.id_comp]
  exact (congrArg (fun q => val D₀.rig q z J) hD.g_comm).trans e

omit hJ hJ₁ in

theorem tau_pull : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (θ : R →+* V) (D₀ : DegPre R) (D₁ : DegPre V) (hD : IsPullDeg θ D₀ D₁), ∃ (β₂ : (G2 D₁.P.A).left ⟶ (G2 D₀.P.A).left) (w₀ : LB.Iso (abelian₂ D₁.P.A D₁.P.L) ((abelian₂ D₀.P.A D₀.P.L).pull β₂)), IsSquare (GlobalTheory.PsiEvenPull.proj hD) β₂ ∧ w₀.IsGen ∧ ∀ a b z J J₁, Good D₀.P.L z J → Good D₁.P.L z J₁ → val (D₁.tau a b) (𝟙 _) z J₁ = lamVal w₀ (lift (toUnit (TK V) ≫ D₁.c a) (toUnit (TK V) ≫ D₁.c b)).left z J J₁ * val (hD.psiW.tau (hD.xe a) (hD.xe b)) hD.g z J := by
  intro R V _ _ _ _ θ D₀ D₁ hD
  refine ⟨sqOf (pull_grp hD), lamIso (pull_grp hD) hD.w, isSquare_sqOf _, isGen_lamIso _ _ hD.w_gen,
    fun a b z J J₁ hJ hJ₁ => ?_⟩
  have g := gw_lam (pull_grp hD) hD.w (lift (toUnit (TK V) ≫ D₁.c a) (toUnit (TK V) ≫ D₁.c b)).left z hJ hJ₁
  have p := prod_lam (DVR.cP D₁ (TK V) a) (DVR.cP D₁ (TK V) b) (om hD.w z J J₁)
  rw [← DVR.cPoint_add] at p
  have l : lamVal (lamIso (pull_grp hD) hD.w) (lift (toUnit (TK V) ≫ D₁.c a) (toUnit (TK V) ≫ D₁.c b)).left z J J₁ =
      om hD.w z J J₁ (D₁.xK (a + b)) * (om hD.w z J J₁ (D₁.xK a))⁻¹ * (om hD.w z J J₁ (D₁.xK b))⁻¹ *
        om hD.w z J J₁ (1 : TK V ⟶ D₁.P.A).left := by
    refine Eq.trans ?_ (g.trans p)
    simp only [Category.assoc]
    rfl
  rw [l, TauPull.val_tauW _ _ hJ, TauPull.val_tau _ hJ₁, ← map_add, psiW_val hD hJ hJ₁, psiW_val hD hJ hJ₁,
    psiW_val hD hJ hJ₁, rigW_val hD hJ hJ₁]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.TauPullOn

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointsFramesThetaSectionGenericFibreMember
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.IntTerm

theorem exists_points_frames_theta : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), ∃ (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)) (th : SecA 𝔪.A (FractionRing V) 1) (ρ : LB.Gen (𝔪.A.L.pull (eSec 𝔪.A.A))), (∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) ∧ (∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' → Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' = val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) ∧ (∀ a, ValAt th (x a) (fr a) (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩)) ∧ ρ.IsGen ∧ ∀ a, IsTorsFrame 𝔪.A ρ (X₁.S.r * X₁.S.N) (x a) (fr a) := by
  intro g n F W Z i X₁ z₁ act V _ _ _ ev X _ m t δ 𝔪
  have hj : (TFK (R := V) (FractionRing V)).hom = 𝟙 _ := by
    show Spec.map (CommRingCat.ofHom (algebraMap (FractionRing V) (FractionRing V))) = _
    rw [Algebra.algebraMap_self]
    exact Spec.map_id _
  have gp := 𝔪.cart
  have hsq : ∀ a, (spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) ≫ X₁.ρ.P.A.hom = (TFK (R := V) (FractionRing V)).hom ≫ spMap 𝔪.yK := by
    intro a
    rw [Category.assoc, Over.w (X₁.ρ.pt a), hj]
    simp
  let x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A) := fun a =>
    Over.homMk (gp.1.lift _ _ (hsq a)) (gp.1.lift_snd _ _ _)
  have hx : ∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left := fun a => gp.1.lift_fst _ _ _
  obtain ⟨rig, fr, hrig, -, hfr⟩ := GlobalTheory.exists_frames_move_through (T := baseOver (Sp X₁.S.R))
    (T' := TFK (R := V) (FractionRing V)) (h := spMap 𝔪.yK) gp 𝔪.wl_gen X₁.ρ.rig_gen hx X₁.ρ.fr_tors
  have hτ : (spMap 𝔪.yK : (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left) ≫
      (baseOver (Sp X₁.S.R)).hom = (TFK (R := V) (FractionRing V)).hom ≫ spMap 𝔪.yK := by
    rw [hj]; simp
  obtain ⟨th, hth⟩ := GlobalTheory.ThetaPtMove.exists_secRel (T := TFK (R := V) (FractionRing V))
    (T₀ := baseOver (Sp X₁.S.R)) (τ := spMap 𝔪.yK) gp hτ (w := 𝔪.wl) 𝔪.wl_gen X₁.ρ.P.isLB 𝔪.A.isLB (a := 1) X₁.ρ.th₁
  refine ⟨x, fr, th, rig, hx, fun a => ⟨(hfr a).1.2.1, fun z J J' hJ hJ' => ?_⟩, fun a => ?_, hrig, fun a => (hfr a).1⟩
  · have e := (hfr a).2 _ (𝟙 _) z J J' hJ hJ'
    rw [Fin.prod_univ_one, zpow_one, Category.id_comp, Category.id_comp] at e
    exact e.symm
  · have hv := GlobalTheory.ThetaPtMove.isValueAt_move (T := TFK (R := V) (FractionRing V))
      (T₀ := baseOver (Sp X₁.S.R)) (τ := spMap 𝔪.yK) gp hτ (w := 𝔪.wl) X₁.ρ.P.isLB 𝔪.A.isLB (a := 1)
      (x := x a) (x₀ := X₁.ρ.pt a) (hx a).symm (ρ₀ := X₁.ρ.fr a) (ρ := fr a) (hfr a).2 (s₀ := X₁.ρ.th₁) (s := th) hth
      (X₁.ρ.th_val a)
    intro z J hJ
    have e := GlobalTheory.FrameMove.sval_valueAt hv (𝟙 _) hJ
    rw [Category.id_comp] at e
    refine e.trans ?_
    rw [GlobalTheory.FrameMove.val_powFrame, Nat.cast_one, zpow_one]
    congr 1
    exact (gs_pull (𝟙 _) (spMap 𝔪.yK) z ⊤ trivial _).trans
      ((congrArg (fun q => gs q z ⊤ _) (Category.id_comp _)).trans (GlobalTheory.FrameMove.gs_spMap 𝔪.yK z _))

end GlobalTheory.Poinc.IntTerm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarisationSectionNonvanishingClosedFibreStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polarisation_section_nonvanishing_closed_fibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ t : SAB H (Sp R), Nonempty (PELUnif (IsLocalRing.maximalIdeal R) t) → ∃ σ : SecAt t.G t.PP.L (𝟙 (Sp R)), NZ t.G t.PP.L (𝟙 (Sp R)) σ := by
  first | exact @GlobalTheory.UMin.ExtNZ.exists_sec_nz | exact GlobalTheory.UMin.ExtNZ.exists_sec_nz | (intros; apply GlobalTheory.UMin.ExtNZ.exists_sec_nz <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarisedE8ThetaPowerOverModuli
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SiegEighth

theorem exists_isSharpBasis (h : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (hW : IsE8 W) :
    ∃ bas : (Fin (2 * (8 * h)) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ)), IsSharpBasis W bas := by
  have hS : (W + W.transpose).transpose = W + W.transpose := by
    rw [Matrix.transpose_add, Matrix.transpose_transpose, add_comm]
  have h1 : (W + W.transpose) * (W + W.transpose).adjugate = 1 := by rw [Matrix.mul_adjugate, hW.2, one_smul]
  have h2 : (W + W.transpose).adjugate * (W + W.transpose) = 1 := by rw [Matrix.adjugate_mul, hW.2, one_smul]
  let e : (Fin 8 → (Fin h ⊕ Fin h → ℤ)) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ)) :=
    { twistSnd (W + W.transpose).adjugate with
      invFun := twistSnd (W + W.transpose)
      left_inv := twistSnd_twistSnd _ _ h1
      right_inv := twistSnd_twistSnd _ _ h2 }
  refine ⟨(sharpReindex h).trans e, fun i j => ?_⟩
  rw [← sum_omegaStd_single h i j]
  exact sum_omegaStd_twistSnd _ _ hS h1 _ _

theorem exists_polAV_sharpOver : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∃ (P : PolAV F.X) (rig : LB.Gen (P.L.pull (eSec P.A))), P.g = 8 * g ∧ GlobalTheory.Poinc.SharpOver F W P (𝟙 F.X) ∧ rig.IsGen ∧ (letI := P.isAb.comm; HypS P.A P.L) := by
  intro g n _ hn hno F W hW
  have hn0 : n ≠ 0 := by omega
  let b := cycBase hn0
  let c : SiegPre g n (b.ζ : cycAway n) (𝟙 F.X ≫ F.s) := GlobalTheory.LowChart.siegPull F.univ (𝟙 F.X) (𝟙 F.X ≫ F.s) rfl
  have hc : c.Principal := GlobalTheory.LowChart.principal_siegPull F.univ _ _ rfl F.princ
  have hd : SmoothOfRelativeDimension g c.A.hom :=
    SiegSharpCover.smoothDim c (by omega) b.ζ.isUnit b.unit
  have hpow : b.ζ ^ n = 1 :=
    Units.ext ((Units.val_pow_eq_pow_val _ _).trans (Subtype.ext (Complex.isPrimitiveRoot_exp n hn0).pow_eq_one))
  obtain ⟨L₁, L₂⟩ := abelianSchemeLaws_all
  haveI : IsDedekindDomain (cycAway n) := GlobalTheory.CycAwayReg.isDedekindDomain_cycAway _
  haveI : IsLocallyNoetherian (Sp (cycAway n)) :=
    inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of _)))
  haveI := F.smooth
  haveI : Smooth F.s := SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) F.s
  haveI : IsLocallyNoetherian F.X := LocallyOfFiniteType.isLocallyNoetherian F.s
  obtain ⟨bas, hb⟩ := exists_isSharpBasis g W hW
  obtain ⟨a, w, w', hw, hw', hs⟩ := EighthPowerFactor.exists_matrices hW.2
  obtain ⟨t, ⟨pr, hpr, hu, hL, -, -⟩, hp⟩ := GlobalTheory.exists_isSharp_and_prim L₁ L₂ Moduli.cube_of_isLB g (8 * g) W _ a w w'
    bas hW hb hw hw' hs n (cycAway n) b F.X (𝟙 F.X ≫ F.s) c hpow hno hc hd
  obtain ⟨r, hr⟩ := t.rigid
  exact ⟨t.pol, r, rfl, ⟨c, GlobalTheory.LowChart.siegPB_siegPull F.univ _ _ rfl, pr, hpr, hu, hL⟩, hr,
    t.act w, t.act w', t.hom w, t.hom w', hp.1, hp.2.2, hp.2.1⟩

end GlobalTheory.SiegEighth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarizedSpecializationFieldStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polarized_specialization_field : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (gQ : ℕ) (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁]
  (Q : Data V), Q.g = gQ → ∀ (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X),
  SharpRef W Q ρ D e → ∀ (K : Type) [Field K] (ev : V₁ →+* K),
  ∃ (P' : PolAV (Sp K)) (ψ : ((Over.pullback (spMap ev)).obj D.P.A).left ⟶ P'.A.left) (B : Over (Sp K)) (_ : GrpObj B)
    (M : RigLB B) (pr : Fin 8 → (P'.A ⟶ B)),
    P'.g = 8 * gQ ∧ IsGrpPullback ((Over.pullback (spMap ev)).obj D.P.A) P'.A (𝟙 _) ψ ∧
    LBIso (D.P.L.pull (pullback.fst D.P.A.hom (spMap ev))) (P'.L.pull ψ) ∧
    E8Fibration.IsPPFib B gQ M ∧ E8Fibration.IsProd pr ∧ E8Fibration.IsE8WeightedBundle W pr P'.L M.L ∧
    ∀ (n : ℕ) (y : Over.mk (spMap ev) ⟶ D.P.A), y ^ n = 1 →
      ∀ q : Sp K ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left,
      q ≫ pullback.fst D.P.A.hom (spMap ev) = y.left → q ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ →
      ∃ y' : Out.baseOver (Sp K) ⟶ P'.A, y'.left = q ≫ ψ ∧ y' ^ n = 1 := by
  first | exact @GlobalTheory.Poinc.Sep.E8Fibration.fibre_exists | exact GlobalTheory.Poinc.Sep.E8Fibration.fibre_exists | (intros; apply GlobalTheory.Poinc.Sep.E8Fibration.fibre_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolynomialChartOfFlagBundleStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical
open GlobalTheory.FlagCell GlobalTheory.FlagConnect

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polynomial_chart_of_flag_bundle : ∀ (B Y : Scheme.{0}) (π : Y ⟶ B) (U : B.Opens) (hU : IsAffineOpen U) (W : Y.Opens) (hW : W ≤ π ⁻¹ᵁ U) (N : Type) (n : N → Γ(Y, W)), W.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom (π.appLE U W hW).hom n)) ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.C : Γ(B, U) →+* MvPolynomial N Γ(B, U))) ≫ hU.fromSpec = W.ι ≫ π ∧ ∀ (h : ⊤ ≤ (W.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom (π.appLE U W hW).hom n))) ⁻¹ᵁ ⊤) (h' : ⊤ ≤ W.ι ⁻¹ᵁ W) (s : N), ((W.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom (π.appLE U W hW).hom n))).appLE ⊤ ⊤ h).hom ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial N Γ(B, U)))).inv.hom (MvPolynomial.X s)) = (W.ι.appLE W ⊤ h').hom (n s) := by
  first | exact @GlobalTheory.cellToSpec | exact GlobalTheory.cellToSpec | (intros; apply GlobalTheory.cellToSpec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPositiveRiemannFormOfRelAmpleExponential
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

namespace GlobalTheory

theorem im_dot_mulVec_star_zsmul_left {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (c : ℤ) (v w : Fin g → ℂ) :
    ((c • v) ⬝ᵥ Hm *ᵥ star w).im = c * (v ⬝ᵥ Hm *ᵥ star w).im := by
  rw [smul_dotProduct, zsmul_eq_mul, Complex.mul_im]
  simp

theorem im_dot_mulVec_star_zsmul_right {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (c : ℤ) (v w : Fin g → ℂ) :
    (v ⬝ᵥ Hm *ᵥ star (c • w)).im = c * (v ⬝ᵥ Hm *ᵥ star w).im := by
  rw [star_zsmul, Matrix.mulVec_smul, dotProduct_smul, zsmul_eq_mul, Complex.mul_im]
  simp

theorem exists_riemannForm_of_relAmple : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (g : ℕ), IsAbelianScheme G → SmoothOfRelativeDimension g G.hom → ∀ (L : LB G.left), L.IsLB → Out.RelAmple G L → ∀ (y : Sp ℂ ⟶ X) (e : (Fin g → ℂ) → (Over.mk y ⟶ G)) (La : Type) [AddCommGroup La] (P : La →+ (Fin g → ℂ)), IsExp y e → Function.Injective P → (∀ z, e z = 1 ↔ z ∈ P.range) → ∃ (Hm : Matrix (Fin g) (Fin g) ℂ) (EF : LinearMap.BilinForm ℤ La), Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ (∀ x x', (hermForm Hm (P x) (P x')).im = EF x x') ∧ (∀ (k : ℕ) (a b : La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k) → Out.WeilIs G L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P b)) (unitOn c)) := by
  intro X G _ _ g hG hsm L hL hamp y e La _ P he hP hker
  obtain ⟨Λ, hd, hfull, hΛ⟩ := GlobalTheory.T.complexFibreExponential_kernel_full_lattice X G g hG hsm y e he
  obtain ⟨hadd, honto, hhol, -, -⟩ := he
  letI : GrpObj ((Over.pullback y).obj G) := Functor.grpObjObj
  haveI : IsCommMonObj ((Over.pullback y).obj G) := Functor.isCommMonObj_obj
  have hp : IsGrpPullback ((Over.pullback y).obj G) G y (pullback.fst G.hom y) := isGrpPullback_pullback G y
  have hLA : (L.pull (pullback.fst G.hom y)).IsLB := LB.isLB_pull hL _
  obtain ⟨hA, hampA, -⟩ := GlobalTheory.pol_pull X (Sp ℂ) G ((Over.pullback y).obj G) y (pullback.fst G.hom y) L
    (L.pull (pullback.fst G.hom y)) hL hLA hG hp (GlobalTheory.PolBaseChange.lbIso_refl hLA)
  let L₀ : LB G.left := ⟨PUnit, fun _ => ⊤, fun _ _ => 1⟩
  let u₀ : HolUnif ((Over.pullback y).obj G) (L₀.pull (pullback.fst G.hom y)) g :=
    GlobalTheory.OrthoMetric.fibreUnif hp (L := L₀) e Λ.toAddSubgroup (fun _ _ => 1) hadd honto hΛ hd hfull hhol
      (fun _ => differentiableOn_const _) (fun _ _ _ => one_ne_zero)
      (fun j j' z hz => by
        show (1 : ℂ) = valAt' (e z).left (⊤ ⊓ ⊤) (1 : Γ(G.left, ⊤ ⊓ ⊤)ˣ).val * 1
        rw [_root_.mul_one]
        exact (valAt'_one _ hz).symm)
  obtain ⟨u, Hm, χ, hex, hF⟩ := GlobalTheory.exists_isFactorAH_frame_of_unif _ hA _ g u₀ _ hLA
  have hpos := GlobalTheory.AmpleHermPos.re_form_pos_of_relAmple _ hA _ hLA (hampA hamp) g u Hm χ hF.1 hF.2.1 hF.2.2
  have hAH : u.IsAH Hm χ := GlobalTheory.TorusRM.isAH_of_isFactorAH hF hpos
  have huΛ : ∀ z, z ∈ u.Λ ↔ z ∈ P.range := fun z => by
    rw [← u.ker, hex]
    exact (u₀.ker z).trans ((hΛ z).symm.trans (hker z))
  have hmem : ∀ a, P a ∈ u.Λ := fun a => (huΛ _).2 ⟨a, rfl⟩
  choose N hN using fun a b => GlobalTheory.TorusRM.ahFactor_im_int g _ _ u Hm χ hLA hF (P a) (hmem a) (P b) (hmem b)
  let EF : LinearMap.BilinForm ℤ La := LinearMap.mk₂ ℤ N
    (fun a a' b => Int.cast_injective (α := ℝ) (by
      push_cast; rw [← hN, ← hN, ← hN, map_add, add_dotProduct, Complex.add_im]))
    (fun c a b => Int.cast_injective (α := ℝ) (by
      rw [smul_eq_mul, Int.cast_mul, ← hN, ← hN, map_zsmul]
      exact im_dot_mulVec_star_zsmul_left Hm c _ _))
    (fun a b b' => Int.cast_injective (α := ℝ) (by
      push_cast; rw [← hN, ← hN, ← hN, map_add, star_add, Matrix.mulVec_add, dotProduct_add, Complex.add_im]))
    (fun c a b => Int.cast_injective (α := ℝ) (by
      rw [smul_eq_mul, Int.cast_mul, ← hN, ← hN, map_zsmul]
      exact im_dot_mulVec_star_zsmul_right Hm c _ _))
  have hEF : ∀ a b, EF a b = N a b := fun _ _ => rfl
  have tr : ∀ (t : Sp ℂ ⟶ X), (𝟙_ (Over (Sp ℂ))).hom ≫ y = t → ∀ (k : ℤ)
      (x x' : 𝟙_ (Over (Sp ℂ)) ⟶ (Over.pullback y).obj G) (x₀ x₀' : Over.mk t ⟶ G) (c : Γ(Sp ℂ, ⊤)ˣ),
      x₀.left = x.left ≫ pullback.fst G.hom y → x₀'.left = x'.left ≫ pullback.fst G.hom y →
      Out.WeilIs _ (L.pull (pullback.fst G.hom y)) k x x' c → Out.WeilIs G L k x₀ x₀' c := by
    intro t ht
    subst ht
    intro k x x' x₀ x₀' c h1 h2 hw
    exact (GlobalTheory.weilIs_iff_of_isGrpPullback_comm X (Sp ℂ) G _ y _ L _ hL hLA hp
      (GlobalTheory.PolBaseChange.lbIso_refl hLA) (𝟙_ _) k x x' x₀ x₀' c h1 h2).1 hw
  have hexl : ∀ z, (e z).left = (u.ex z).left ≫ pullback.fst G.hom y := fun z => by
    rw [hex]
    exact (GlobalTheory.OrthoMetric.liftPt_comp hp (e z)).symm
  refine ⟨Hm, EF, hF.1, fun z hz => hpos z hz, fun x x' => (hN x x').trans (by rw [hEF]), ?_⟩
  intro k a b c hk hc
  have hw := GlobalTheory.AHWeilAny.weilIs_exp_riemannForm _ hA _ hLA g u Hm χ hAH k (P a) (P b) c hk (hmem a) (hmem b)
    (by rw [hc, hN a b, hEF, Complex.ofReal_intCast])
  exact tr y (Category.id_comp y) k _ _ _ _ _ (hexl _) (hexl _) hw

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOneOfPoincareKernelComplex
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

namespace GlobalTheory.KerPoincare

open GlobalTheory.CechPic

attribute [local instance] Over.cartesianMonoidalCategory

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

theorem lift_mul_lift {T : Over S} (u v u' v' : T ⟶ A) : lift u v * lift u' v' = lift (u * u') (v * v') := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [MonObj.mul_comp, lift_fst, lift_fst, lift_fst]
  · rw [MonObj.mul_comp, lift_snd, lift_snd, lift_snd]

theorem one_eq_lift {T : Over S} : (1 : T ⟶ A ⊗ A) = lift (1 : T ⟶ A) 1 := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [MonObj.one_comp, lift_fst]
  · rw [MonObj.one_comp, lift_snd]

theorem lam_diag (p : Pic (A ⊗ A).left)
    (hmul : ∀ {T : Over S} (X X' Y : T ⟶ A ⊗ A), lam p (X * X') Y = lam p X Y + lam p X' Y)
    (r₁ : ∀ {T : Over S} (v : T ⟶ A), pull (lift (1 : T ⟶ A) v).left p = 0)
    (r₂ : ∀ {T : Over S} (u : T ⟶ A), pull (lift u (1 : T ⟶ A)).left p = 0)
    {T : Over S} (a b : T ⟶ A) :
    lam (pull (lift (𝟙 A) (𝟙 A)).left p) a b = pull (lift a b).left p + pull (lift b a).left p := by
  rw [lam_pull, comp_lift, comp_lift]
  simp only [Category.comp_id]
  have ha : lift a a = lift a (1 : T ⟶ A) * lift 1 a := by rw [lift_mul_lift, _root_.mul_one, _root_.one_mul]
  have hb : lift b b = lift b (1 : T ⟶ A) * lift 1 b := by rw [lift_mul_lift, _root_.mul_one, _root_.one_mul]
  have hmul' : ∀ (X Y Y' : T ⟶ A ⊗ A), lam p X (Y * Y') = lam p X Y + lam p X Y' := fun X Y Y' ↦ by
    rw [lam_comm, hmul, lam_comm, lam_comm p Y']
  rw [ha, hb, hmul, hmul', hmul']
  simp only [lam, lift_mul_lift, one_eq_lift, _root_.mul_one, _root_.one_mul, r₁, r₂]
  abel

end GlobalTheory.KerPoincare

namespace GlobalTheory.KerPoincare

open GlobalTheory.CechPic

attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_pow_eq_one_of_kernel : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom → ∀ P : LB (G2 A).left, P.IsLB →
    (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) →
    (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) →
    LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) →
    ∀ (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)) (La : Type) [AddCommGroup La] (Q : La →+ (Fin g → ℂ))
      (EF : LinearMap.BilinForm ℤ La), IsExp (𝟙 (Sp ℂ)) e → Function.Injective Q →
    Submodule.span ℝ (Set.range Q) = ⊤ → (∀ z, e z = 1 ↔ z ∈ Q.range) →
    (∀ (k : ℕ) (a b : La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k) →
      Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) k (e ((k : ℂ)⁻¹ • Q a)) (e ((k : ℂ)⁻¹ • Q b)) (unitOn c)) →
    ∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ A,
      (∃ t : (P.pull (lift (snd A (𝟙_ (Over (Sp ℂ))) ≫ x) (fst A (𝟙_ (Over (Sp ℂ))))).left).Gen, t.IsGen) →
      ∃ k : ℕ, 0 < k ∧ x ^ k = 1 := by
  intro A _ _ g hA hsm P hP hr₁ hr₂ hsym hamp e La _ Q EF he _ _ _ _ x hx
  have hL : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  obtain ⟨Λ, hd, hf, hk⟩ := GlobalTheory.ExpKernel.kernel_isFullLattice (Sp ℂ) A g hA hsm (𝟙 _) e he
  obtain ⟨L₀, u₀, -⟩ := GlobalTheory.exists_holUnif_of_isExp A g e Λ he hd hf hk
  obtain ⟨u, Hm, χ, -, hAH⟩ := GlobalTheory.exists_isFactorAH_frame_of_unif A hA L₀ g u₀ _ hL
  have pos := GlobalTheory.AmpleHermPos.re_form_pos_of_relAmple A hA _ hL hamp g u Hm χ hAH.1 hAH.2.1 hAH.2.2
  obtain ⟨PP, ψ, ρ, N, hN, hψ, hρ, h₁, h₂, h₃⟩ := GlobalTheory.PosAHIsog.exists_isog_principal_lam g A hA _ u Hm χ hL
    (GlobalTheory.TorusRM.isAH_of_isFactorAH hAH pos)
  refine ⟨N * N, Nat.mul_pos hN hN,
    GlobalTheory.KillSquare.pow_sq_eq_one_of_lam_trivial A hA _ hL PP ψ ρ N hψ hρ h₁ h₂ h₃ _ x ?_⟩
  have hG : IsAbelianScheme (A ⊗ A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have hΘ := GlobalTheory.exists_gen_theta_of_isAbelianScheme ℂ (A ⊗ A) hG P hP
  have r₁ : ∀ {T : Over (Sp ℂ)} (v : T ⟶ A), pull (lift (1 : T ⟶ A) v).left (cls P hP) = 0 := fun {T} v ↦ by
    have hv : lift (1 : T ⟶ A) v = v ≫ lift (1 : A ⟶ A) (𝟙 A) := by
      rw [comp_lift, MonObj.comp_one, Category.comp_id]
    rw [hv, Over.comp_left, pull_comp, ← cls_pull hP _ (pull_isLB hP _),
      (cls_eq_zero_iff (pull_isLB hP _)).2 hr₁, map_zero]
  have r₂ : ∀ {T : Over (Sp ℂ)} (v : T ⟶ A), pull (lift v (1 : T ⟶ A)).left (cls P hP) = 0 := fun {T} v ↦ by
    have hv : lift v (1 : T ⟶ A) = v ≫ lift (𝟙 A) (1 : A ⟶ A) := by
      rw [comp_lift, MonObj.comp_one, Category.comp_id]
    rw [hv, Over.comp_left, pull_comp, ← cls_pull hP _ (pull_isLB hP _),
      (cls_eq_zero_iff (pull_isLB hP _)).2 hr₂, map_zero]
  have e₀ : cls P hP = pull (lift (snd A A) (fst A A)).left (cls P hP) := by
    rw [← cls_pull hP _ (pull_isLB hP _)]
    exact (cls_eq_iff hP (pull_isLB hP _)).2 hsym
  have hsymm : ∀ {T : Over (Sp ℂ)} (u v : T ⟶ A),
      pull (lift u v).left (cls P hP) = pull (lift v u).left (cls P hP) := fun {T} u v ↦ by
    conv_lhs => rw [e₀]
    rw [← pull_comp, ← Over.comp_left, comp_lift, lift_snd, lift_fst]
  have hxA : pull (lift (snd A (𝟙_ (Over (Sp ℂ))) ≫ x) (fst A (𝟙_ (Over (Sp ℂ))))).left (cls P hP) = 0 := by
    rw [← cls_pull hP _ (pull_isLB hP _)]
    exact (cls_eq_zero_iff _).2 hx
  refine (cls_eq_zero_iff (pull_isLB (LB.isLB_linComb hL _ _) _)).1
    ((GlobalTheory.RealMult.Elliptic.cls_pull_lam hL _ _ _).trans ?_)
  rw [cls_pull hP _ hL,
    lam_diag (cls P hP) (fun X X' Y ↦ lam_mul_left hP hΘ X X' Y) r₁ r₂, hsymm, hxA, add_zero]

end GlobalTheory.KerPoincare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrincipalPolarisationMumfordBundleAlgClosuStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_principalPolarisation_mumfordBundle_algClosure : ∀ (K : Type) [Field K] [CharZero K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ PP : LB (G2 A).left, PP.IsLB → (∃ u : LB.Gen (LB.LinComb PP (K := Fin 2) ![(lift (snd A A) (fst A A) : G2 A ⟶ G2 A).left, 𝟙 (G2 A).left] ![1, -1]), u.IsGen) → (∃ u : LB.Gen (LB.LinComb PP (K := Fin 3) ![(lift (fst A (A ⊗ A) * (snd A (A ⊗ A) ≫ fst A A)) (snd A (A ⊗ A) ≫ snd A A) : A ⊗ (A ⊗ A) ⟶ G2 A).left, (lift (fst A (A ⊗ A)) (snd A (A ⊗ A) ≫ snd A A) : A ⊗ (A ⊗ A) ⟶ G2 A).left, (snd A (A ⊗ A) : A ⊗ (A ⊗ A) ⟶ G2 A).left] ![1, -1, -1]), u.IsGen) → Out.RelAmple A (PP.pull (lift (𝟙 A) (𝟙 A) : A ⟶ G2 A).left) → (∀ (T : Over (Sp K)) (x : T ⟶ A), (∃ t : LB.Gen (PP.pull (lift (snd A T ≫ x) (fst A T) : A ⊗ T ⟶ G2 A).left), t.IsGen) → x = toUnit T ≫ η[A]) → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] (κ : (G2 ((Over.pullback (spMap (algebraMap K Ω))).obj A)).left ⟶ (G2 A).left), Geo.Tor.IsSquare (pullback.fst A.hom (spMap (algebraMap K Ω))) κ → ∃ L : LB ((Over.pullback (spMap (algebraMap K Ω))).obj A).left, L.IsLB ∧ Out.Sym ((Over.pullback (spMap (algebraMap K Ω))).obj A) L ∧ LBIso (abelian₂ ((Over.pullback (spMap (algebraMap K Ω))).obj A) L) (PP.pull κ) ∧ Out.RelAmple ((Over.pullback (spMap (algebraMap K Ω))).obj A) L ∧ Out.KTriv ((Over.pullback (spMap (algebraMap K Ω))).obj A) L := by
  first | exact @GlobalTheory.PrincipalBaseChange.exists_principal_algClosure | exact GlobalTheory.PrincipalBaseChange.exists_principal_algClosure | (intros; apply GlobalTheory.PrincipalBaseChange.exists_principal_algClosure <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProductPrincipallyPolarisedAbelianSchemeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_product_principallyPolarised_abelianScheme : ∀ (S : Scheme.{0}) (P₁ P₂ : PolAV S), ∃ (P : PolAV S) (a₁ : P.A ⟶ P₁.A) (a₂ : P.A ⟶ P₂.A), IsSumPolAV P P₁ P₂ a₁ a₂ ∧ P.L = extLB P₁.L P₂.L a₁.left a₂.left := by
  first | exact @GlobalTheory.MumProd.SumPol.exists_sum_polAV | exact GlobalTheory.MumProd.SumPol.exists_sum_polAV | (intros; apply GlobalTheory.MumProd.SumPol.exists_sum_polAV <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjectiveSpaceMapOfModelHasDivStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_projectiveSpace_map_of_model_hasDiv : ∀ (k Ω : Type) [CommRing k] [Field Ω] [Algebra k Ω] (M : RatModel k Ω) (n : ℕ) (c : Fin (n + 1) → Ω), M.HasDiv c → ∃ h : M.Z ⟶ PSpace k n, h ≫ PSpace.str k n = M.s ∧ PCrd (M.pt ≫ h) c := by
  first | exact @GlobalTheory.UMin.CrdMap.exists_map_of_hasDiv | exact GlobalTheory.UMin.CrdMap.exists_map_of_hasDiv | (intros; apply GlobalTheory.UMin.CrdMap.exists_map_of_hasDiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjectiveSpacePointOfUnitCoordinateStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_projectiveSpace_point_of_unit_coordinate : ∀ (o R : Type) [CommRing o] [CommRing R] (n : ℕ) (β : o →+* R) (v : Fin (n + 1) → R), (∃ j, IsUnit (v j)) → ∃ ξ : Sp R ⟶ PSpace o n, ξ ≫ PSpace.str o n = spMap β ∧ PCrd ξ v := by
  first | exact @GlobalTheory.UMin.exists_pCrd_of_isUnit | exact GlobalTheory.UMin.exists_pCrd_of_isUnit | (intros; apply GlobalTheory.UMin.exists_pCrd_of_isUnit <;> assumption)
end

