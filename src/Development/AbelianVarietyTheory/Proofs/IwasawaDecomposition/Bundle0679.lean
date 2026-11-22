import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0567
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecEqZeroAndHomEqOfThickenings
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0005
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0096
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0002
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0619
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0628
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0663
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FrameMatrixHasSum
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLaw
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0661
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0652
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0655
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0673
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsExtendResidue
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0659
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0610
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0662
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0586

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbelianPartSectionSqEqOfThickeningPoints
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SqDescend

variable {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]

theorem wchart_sq_le (φ : K → (Y ⟶ X)) (p : K → Fin 1 → L.ι) :
    LB.wchart (SqLB.sq L) φ p ≤ LB.wchart L φ (fun k => p k 0) :=
  fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (Set.mem_iInter.1 hy k) 0

theorem gm_sq_g' (f : Y ⟶ X) (y : Y) (j j' : Fin 1 → L.ι) (hj : f y ∈ (SqLB.sq L).U j)
    (hj' : f y ∈ (SqLB.sq L).U j') :
    gm f y ((SqLB.sq L).U j ⊓ (SqLB.sq L).U j') ((SqLB.sq L).g j j') =
      gm f y (L.U (j 0) ⊓ L.U (j' 0)) (L.g (j 0) (j' 0)) ^ (2 : ℤ) := by
  obtain ⟨a, rfl⟩ : ∃ a, j = fun _ => a := ⟨j 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  obtain ⟨b, rfl⟩ : ∃ b, j' = fun _ => b := ⟨j' 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  exact SqLB.gm_sq_g f y (Set.mem_iInter.1 hj 0) (Set.mem_iInter.1 hj' 0)

theorem gs_sub (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a b : Γ(X, U)) :
    gs f y U (a - b) = gs f y U a - gs f y U b := by simp only [gs_eq f y U h, map_sub]

theorem gs_zero (f : Y ⟶ X) (y : Y) (U : X.Opens) : gs f y U 0 = 0 := by
  unfold gs; split_ifs <;> simp

theorem trF_sq (φ : K → (Y ⟶ X)) (ε : K → ℤ) (y : Y) (p p' : K → Fin 1 → L.ι)
    (hy : y ∈ LB.wchart (SqLB.sq L) φ p ⊓ LB.wchart (SqLB.sq L) φ p') :
    (∏ k, gm (𝟙 Y ≫ φ k) y ((SqLB.sq L).U (p k) ⊓ (SqLB.sq L).U (p' k)) ((SqLB.sq L).g (p k) (p' k)) ^ ε k) =
      trF φ ε (𝟙 Y) y (fun k => p k 0) (fun k => p' k 0) ^ 2 := by
  simp only [trF]
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [gm_sq_g' (𝟙 Y ≫ φ k) y (p k) (p' k) (Set.mem_iInter.1 hy.1 k) (Set.mem_iInter.1 hy.2 k), ← zpow_mul, ← zpow_natCast,
    ← zpow_mul]
  congr 1
  push_cast
  ring

def sqSec {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) :
    LB.Sec (LB.LinComb (SqLB.sq L) φ ε) where
  f := fun p => (Y.presheaf.map (homOfLE (wchart_sq_le φ p)).op).hom (s.f (fun k => p k 0)) *
    (Y.presheaf.map (homOfLE (wchart_sq_le φ p)).op).hom (s.f (fun k => p k 0))
  compat := fun p p' => fn_ext fun y hy => by
    have h₁ := wchart_sq_le φ p hy.1
    have h₂ := wchart_sq_le φ p' hy.2
    have eA : gs (𝟙 Y) y _ ((Y.presheaf.map (homOfLE (wchart_sq_le φ p)).op).hom (s.f (fun k => p k 0))) =
        gs (𝟙 Y) y (LB.wchart L φ (fun k => p k 0)) (s.f (fun k => p k 0)) := gs_res (𝟙 Y) y _ hy.1 _
    have eB : gs (𝟙 Y) y _ ((Y.presheaf.map (homOfLE (wchart_sq_le φ p')).op).hom (s.f (fun k => p' k 0))) =
        gs (𝟙 Y) y (LB.wchart L φ (fun k => p' k 0)) (s.f (fun k => p' k 0)) := gs_res (𝟙 Y) y _ hy.2 _
    have eL := (gs_res (𝟙 Y) y inf_le_left hy _).trans ((gs_mul (𝟙 Y) y _ hy.1 _ _).trans (congrArg₂ (· * ·) eA eA))
    have eR := (gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·) ((gs_unit (𝟙 Y) y _ hy _).trans
      (congrArg Units.val ((gm_linComb (SqLB.sq L) φ ε (𝟙 Y) y p p' hy.1 hy.2).trans (trF_sq φ ε y p p' hy))))
      ((gs_res (𝟙 Y) y inf_le_right hy _).trans ((gs_mul (𝟙 Y) y _ hy.2 _ _).trans (congrArg₂ (· * ·) eB eB))))
    refine eL.trans (Eq.trans ?_ eR.symm)
    rw [sec_trans s (𝟙 Y) y h₁ h₂, Units.val_pow_eq_pow_val]
    ring

theorem good_sq {J : (Z ⟶ X) → L.ι} {z : Z} (hJ : Good L z J) : Good (SqLB.sq L) z (fun q _ => J q) :=
  fun ψ => Set.mem_iInter.2 fun _ => hJ ψ

theorem sval_sqSec {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z)
    {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (sqSec s) r z (fun q _ => J q) = sval s r z J ^ 2 := by
  have h0 := hJ.mem φ r
  have hm : r z ∈ LB.wchart (SqLB.sq L) φ (fun k _ => J (r ≫ φ k)) :=
    Set.mem_iInter.2 fun k => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 h0 k
  exact (gs_mul r z _ hm _ _).trans ((congrArg₂ (· * ·) (gs_res r z _ hm _) (gs_res r z _ hm _)).trans
    (pow_two _).symm)

def secSub {M : LB Y} (a b : LB.Sec M) : LB.Sec M where
  f := fun i => a.f i - b.f i
  compat := fun i j => by rw [map_sub, map_sub, a.compat, b.compat, mul_sub]

theorem sval_secSub {M : LB X} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (a b : LB.Sec (LB.LinComb M φ ε)) (r : Z ⟶ Y)
    (z : Z) {J : (Z ⟶ X) → M.ι} (hJ : Good M z J) :
    sval (secSub a b) r z J = sval a r z J - sval b r z J :=
  gs_sub r z _ (hJ.mem φ r) _ _

end GlobalTheory.SqDescend

open GlobalTheory.SqDescend in

theorem GlobalTheory.sq_corr_of_thickenings : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)), w.IsGen → (∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left) → ∀ (α : D.toPre.X) (α' : D'.toPre.X), (∀ κ, D'.toPre.famφB α' κ ≫ Φ.hom.left = Φ.hom.left ≫ D.toPre.famφB α κ) → ∀ (s : D.toPre.SecB 2 α) (s' : D'.toPre.SecB 2 α'), (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → sval s (r ≫ (U.gt e).pG.left) z J ^ 2 = (∏ κ, ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (r ≫ (U'.gt e).pG.left ≫ D'.toPre.famφB α' κ) ^ DegPre.famε 2 κ).val * sval s' (r ≫ (U'.gt e).pG.left) z J' ^ 2) → ∀ (Z : Scheme.{0}) (ρ : Z ⟶ D'.toPre.P.A.left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → sval s (ρ ≫ Φ.hom.left) z J ^ 2 = (∏ κ, ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (ρ ≫ D'.toPre.famφB α' κ) ^ DegPre.famε 2 κ).val * sval s' ρ z J' ^ 2 := by
  intro R _ _ _ hCN G _ _ hSA D D' A A' U U' Φ w hw hpG α α' hφ s s' hE Z ρ z J J' hJ hJ'
  classical
  have hL := D.toPre.P.isLB
  have hL' := D'.toPre.P.isLB
  have hM : (SqLB.sq D.toPre.P.L).IsLB := DVR.linComb_isLB _ hL _ _
  have hM' : (SqLB.sq D'.toPre.P.L).IsLB := DVR.linComb_isLB _ hL' _ _
  obtain ⟨a, ha, -⟩ := SecPull.existsUnique_secPull _ _ _ _ _ _ Φ.hom.left hM hM' w hw (Fin 4)
    (D'.toPre.famφB α') (D.toPre.famφB α) (DegPre.famε 2) Φ.hom.left hφ (sqSec s)
  have hT : ∀ (Z : Scheme.{0}) (r : Z ⟶ D'.toPre.P.A.left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι)
      (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' →
      sval s (r ≫ Φ.hom.left) z J ^ 2 = (∏ κ, ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q)
        (r ≫ D'.toPre.famφB α' κ) ^ DegPre.famε 2 κ).val * sval a r z (fun q _ => J' q) := by
    intro Z r z J J' hJ hJ'
    rw [← sval_sqSec s _ z hJ]
    exact ExpTrans.sec_val w _ _ _ Φ.hom.left hφ (sqSec s) a r z (ha Z r z) (good_sq hJ) (good_sq hJ')
  have hvan : ∀ (e : ℕ) (q : Fin 4 → Fin 1 → D'.toPre.P.L.ι),
      ((U'.gt e).pG.left.app _).hom ((secSub a (sqSec s')).f q) = 0 := by
    intro e q
    refine fn_ext fun y hy => ?_
    choose J₁ hJ₁ using fun ψ : (thickObj R (maximalIdeal R) e G).left ⟶ D.toPre.P.A.left =>
      exists_chart hL (ψ y)
    choose J₂ hJ₂ using fun ψ : (thickObj R (maximalIdeal R) e G).left ⟶ D'.toPre.P.A.left =>
      exists_chart hL' (ψ y)
    have g₁ : Good D.toPre.P.L y J₁ := hJ₁
    have g₂ : Good D'.toPre.P.L y J₂ := hJ₂
    have e1 := hE e _ (𝟙 _) y J₁ J₂ g₁ g₂
    have e2 := hT _ (U'.gt e).pG.left y J₁ J₂ g₁ g₂
    simp only [Category.id_comp] at e1
    rw [hpG e, e1, ← sval_sqSec s' _ y g₂] at e2
    have e3 := (Units.mul_right_inj _).1 e2
    have hΔ : sval (secSub a (sqSec s')) (U'.gt e).pG.left y (fun q _ => J₂ q) = 0 := by
      rw [sval_secSub a (sqSec s') _ y (good_sq g₂), e3, sub_self]
    refine (gs_pull (𝟙 _) (U'.gt e).pG.left y _ hy _).trans ?_
    rw [Category.id_comp, gs_zero]
    refine (sec_trans (secSub a (sqSec s')) (U'.gt e).pG.left y (j := q) hy ((good_sq g₂).mem _ _)).trans ?_
    change _ * sval (secSub a (sqSec s')) (U'.gt e).pG.left y (fun q _ => J₂ q) = 0
    rw [hΔ, mul_zero]
  obtain ⟨hN, -, -, -⟩ := TorRef.admissibleBase_of_completeNormalLocalCharZero hCN
  have hI : maximalIdeal R ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
  have := D'.toPre.P.isAb.smooth
  have := D'.toPre.P.isAb.geomConnected
  have h0 := (sec_eq_zero_and_hom_eq_of_thickenings R (maximalIdeal R) hI D'.toPre.P.A).1 _
    (DVR.linComb_isLB _ hM' _ _) (secSub a (sqSec s'))
    fun e q => (ExtDiv.pG_app_eq_zero_iff (U'.gt e) _ _).1 (hvan e q)
  have key : sval a ρ z (fun q _ => J' q) = sval (sqSec s') ρ z (fun q _ => J' q) := by
    have h1 : sval (secSub a (sqSec s')) ρ z (fun q _ => J' q) = 0 := by
      show gs _ _ _ _ = 0
      exact (congrArg (gs ρ z _) (h0 _)).trans (gs_zero _ _ _)
    have h2 := sval_secSub a (sqSec s') ρ z (good_sq hJ')
    rw [h1] at h2
    exact sub_eq_zero.1 h2.symm
  rw [hT Z ρ z J J' hJ hJ', key, sval_sqSec s' ρ z hJ']
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArcLieBasisExponentialCoordsHasSum
section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.ArcLieCoord

open MonoidalCategory CartesianMonoidalCategory MonObj Filter GlobalTheory.ArcLie

theorem comb_tan {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {n : ℕ}
    (v : Fin n → (epsR R ⟶ G)) (hv : ∀ k, IsTangent (v k)) (c : Fin n → R) (w : epsR R ⟶ G) (hc : IsLieComb c v w) :
    IsTangent w := by
  rw [GlobalTheory.PowLie.isLieComb_iff_prod] at hc
  subst hc
  rw [GlobalTheory.PowLie.isTangent_iff]
  have e0 : ∀ a : R, GlobalTheory.PowLie.zeroPt R ≫ GlobalTheory.PowLie.sc a = GlobalTheory.PowLie.zeroPt R := fun a => by
    refine Over.OverMorphism.ext ?_
    simp only [Over.comp_left, GlobalTheory.PowLie.zeroPt, GlobalTheory.PowLie.sc, Over.homMk_left]
    rw [GlobalTheory.TanMod.spMap_comp']
    congr 1
    refine RingHom.ext fun r => ?_
    simp [epsScaleR]
  have e1 := map_prod (ReciprocityTheory.ChartRestriction.G.Geo.Tor.preHom (G := G) (GlobalTheory.PowLie.zeroPt R)) (fun k => GlobalTheory.PowLie.sc (c k) ≫ v k)
    Finset.univ
  refine e1.trans ?_
  refine (Finset.prod_congr rfl fun k _ => ?_).trans (Finset.prod_const_one)
  show GlobalTheory.PowLie.zeroPt R ≫ GlobalTheory.PowLie.sc (c k) ≫ v k = 1
  rw [← Category.assoc, e0, (GlobalTheory.PowLie.isTangent_iff _).1 (hv k)]
  rfl

theorem sep_laurent {X : Scheme.{0}} {x : Sp (PowerSeries ℂ) ⟶ X} {G : Over X} {G' : Over (Sp (PowerSeries ℂ))} [GrpObj G]
    [GrpObj G'] [IsCommMonObj G'] {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G x φ) {n : ℕ}
    (v : Fin n → (epsR (PowerSeries ℂ) ⟶ G')) (hv : IsLieBasis v) {V : G.left.Opens} (hA : IsAffineOpen V)
    (hV : ⊤ ≤ ((η[G']).left ≫ φ) ⁻¹ᵁ V) (a : Fin n → ℂ⸨X⸩)
    (ha : ∀ f : Γ(G.left, V), ∑ k, a k * HahnSeries.ofPowerSeries ℤ ℂ (valR ((v k).left ≫ φ) V f).snd = 0) : a = 0 := by
  classical
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (M := nonZeroDivisors (PowerSeries ℂ)) (S := ℂ⸨X⸩)
    Finset.univ a
  choose b hb using fun k => hd k (Finset.mem_univ k)
  have hinj : Function.Injective (HahnSeries.ofPowerSeries ℤ ℂ) := HahnSeries.ofPowerSeries_injective
  have hb' : ∀ k, HahnSeries.ofPowerSeries ℤ ℂ (b k) = HahnSeries.ofPowerSeries ℤ ℂ (d : PowerSeries ℂ) * a k := fun k => by
    rw [← LaurentSeries.coe_algebraMap, hb k, Algebra.smul_def, LaurentSeries.coe_algebraMap]
  have h0 := GlobalTheory.T.derivatives_separate_lieBasis_coeffs_cartesian h v hv hA hV b fun f => hinj (by
    rw [map_sum, map_zero]
    have e := congrArg (fun t => HahnSeries.ofPowerSeries ℤ ℂ (d : PowerSeries ℂ) * t) (ha f)
    simp only [mul_zero, Finset.mul_sum] at e
    rw [← e]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, hb', _root_.mul_assoc])
  funext k
  have hd0 : HahnSeries.ofPowerSeries ℤ ℂ (d : PowerSeries ℂ) ≠ 0 := fun e =>
    nonZeroDivisors.coe_ne_zero d (hinj (e.trans (map_zero _).symm))
  have := hb' k
  rw [h0, Pi.zero_apply, map_zero] at this
  exact (mul_eq_zero.1 this.symm).resolve_left hd0

theorem valR_eq_ev' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (f : Γ(X, U)) : valR x U f = ev x U h f := by
  rw [valR, dif_pos h]; rfl

section Point

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem point_snd {Y : Model Xo c β} (M : GChart Y) {z : Sp ℂ ⟶ Y.X} {hz : ⊤ ≤ z ⁻¹ᵁ M.U} {x : KeyIn ℂ}
    {φ : x.P.A.left ⟶ Y.t.G.left} (hK : GlobalTheory.ArcNormal.KeyAtVia M z hz x φ) {g : ℕ} (u : HolUnif x.P.A x.P.L g)
    (e : (Fin g → ℂ) → (Sp ℂ ⟶ Y.t.G.left)) (he : ∀ t, e t = (u.ex t).left ≫ φ) (i : Fin x.P.g) (j : Fin M.n)
    (hij : (i : ℕ) = j) (wv : Fin g → ℂ) (hd : u.IsDiff wv (x.v i)) (V : Y.t.G.left.Opens)
    (hV : ⊤ ≤ (spMap (dualMap (ev z M.U hz)) ≫ M.v₀ j) ⁻¹ᵁ V) (f : Γ(Y.t.G.left, V)) :
    (valR (spMap (dualMap (ev z M.U hz)) ≫ M.v₀ j) V f).snd = fderiv ℂ (fun t => valAt' (e t) V f) 0 wv := by
  obtain ⟨-, -, hg', -, -, -, -, hv⟩ := hK
  have e1 : (x.v i).left ≫ φ = spMap (dualMap (ev z M.U hz)) ≫ M.v₀ j := by
    rw [hv i]
    congr 2
    exact Fin.ext hij
  rw [← e1] at hV ⊢
  have hU : ⊤ ≤ (x.v i).left ⁻¹ᵁ (φ ⁻¹ᵁ V) := hV
  have hd' := hd (φ ⁻¹ᵁ V) hU ((φ.app V).hom f)
  have e2 : (fun t => valAt' (e t) V f) = fun t => valAt' (u.ex t).left (φ ⁻¹ᵁ V) ((φ.app V).hom f) :=
    funext fun t => by rw [he, GlobalTheory.HolHom.valAt'_eq_valR, GlobalTheory.HolHom.valAt'_eq_valR, GlobalTheory.HolHom.valR_comp]
  rw [e2, ← hd', GlobalTheory.HolHom.valR_comp, GlobalTheory.HolHom.valR_eq _ _ hU]
  rfl

end Point

open AlgebraicGeometry CategoryTheory Limits in

theorem lie_coords_hasSum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) (a : ArcIn Dw l V.subtype ℂ (σ.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : GlobalTheory.ArcQ.Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) (M : GChart Y) (hM : ⊤ ≤ χ ⁻¹ᵁ M.U) (e : Fin g → Out.GtPt a.D₀ (epsR ℂ)) (v : Fin g → (epsR (PowerSeries ℂ) ⟶ W.t.G)) (z : Fin g → Fin g → ℂ) (hn : M.n = g) (v' : Fin g → (epsR (PowerSeries ℂ) ⟶ W.t.G)) (A : Matrix (Fin g) (Fin g) (PowerSeries ℂ)), Formalism.L2.PjFree.GoodEmb c σ → IsTypeFn H Dw.p Dw.q ty → PushInvertible Y.t.G Y.t.PP.L → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp V.subtype) → (∀ x : Sp (PowerSeries ℂ), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → (∀ k, GlobalTheory.ArcQ.LieImg W (e k) (v k) ∧ GlobalTheory.ArcQ.AnVec Ha (e k) (z k)) → IsLieBasis v → (Matrix.of z).det ≠ 0 → (∀ i, (v' i).left ≫ W.m.φ = spMap (dualMap (ev χ M.U hM)) ≫ M.v₀ (Fin.cast hn.symm i)) → (∀ i, IsLieComb (A i) v (v' i)) → ∃ T : ℝ, ∀ w : ℂ, T < w.im → ∀ yF : Sp ℂ ⟶ Xo.XF c, yF ≫ pullback.fst _ _ = Fu.u Ha.i (Ha.Pw w) → yF ≫ pullback.snd _ _ = spMap σ → ∀ (hz : ⊤ ≤ (yF ≫ Y.j) ⁻¹ᵁ M.U) (x : KeyIn ℂ) (φ : x.P.A.left ⟶ Y.t.G.left), GlobalTheory.ArcNormal.KeyAtVia M (yF ≫ Y.j) hz x φ → ∀ (hg : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (Wv : Fin x.P.g → Fin g → ℂ), GlobalTheory.ArcNormal.ArcFib Y σ Fu Ha.i (Ha.Pw w) x φ u → (∀ i, u.IsDiff (Wv i) (x.v i)) → ∀ i, (∀ k, Summable (fun m : ℕ => PowerSeries.coeff m (A i k) * eTwoPi w ^ m)) ∧ ∀ j, Wv (Fin.cast hg.symm i) j = ∑ k, (∑' m : ℕ, PowerSeries.coeff m (A i k) * eTwoPi w ^ m) * z k j := by
  intro E _ _ _ H Dw l Xo c σ _ _ V Y a χ W g ty Fu Ha M hM e v z hn v' A _ _ _ hχ _ hez hvb hdet hv' hA
  let Ω : Type := {q : ℂ × (Sp ℂ ⟶ Xo.XF c) × ((Fin g → ℂ) → (Sp ℂ ⟶ Y.oF.t.G.left)) × (Fin g → Fin g → ℂ) //
    q.2.1 ≫ pullback.fst _ _ = Fu.u Ha.i (Ha.Pw q.1) ∧ q.2.1 ≫ pullback.snd _ _ = spMap σ ∧
    (∀ t, q.2.2.1 t ≫ Y.m0.toSABMap.φ = (Fu.ex Ha.i (Ha.Pw q.1) t).left ∧
      q.2.2.1 t ≫ Y.oF.t.G.hom ≫ pullback.snd _ _ = spMap σ) ∧
    ⊤ ≤ (q.2.1 ≫ Y.j) ⁻¹ᵁ M.U ∧ ∀ (hz : ⊤ ≤ (q.2.1 ≫ Y.j) ⁻¹ᵁ M.U) (i : Fin g) (Vo : Y.t.G.left.Opens)
      (f : Γ(Y.t.G.left, Vo)), ⊤ ≤ (spMap (dualMap (ev (q.2.1 ≫ Y.j) M.U hz)) ≫ M.v₀ (Fin.cast hn.symm i)) ⁻¹ᵁ Vo →
      (valR (spMap (dualMap (ev (q.2.1 ≫ Y.j) M.U hz)) ≫ M.v₀ (Fin.cast hn.symm i)) Vo f).snd =
        ∑ k, q.2.2.2 i k * fderiv ℂ (fun t => valAt' (q.2.2.1 t ≫ Y.m.φ) Vo f) 0 (z k)}
  let pw : Ω → ℂ := fun ω => ω.1.1
  let ψ : Ω → (Γ(Y.X, M.U) →+* ℂ) := fun ω => ev (ω.1.2.1 ≫ Y.j) M.U ω.2.2.2.2.1
  have hcart := W.m.cart
  have tanv : ∀ k, IsTangent (v k) := hvb.1
  suffices hs : ∀ i k, Cv pw (HahnSeries.ofPowerSeries ℤ ℂ (A i k)) (fun ω => ω.1.2.2.2 i k) by
    obtain ⟨T, hT⟩ := high_iff.1 (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun k => hs i k)
    refine ⟨T, fun w hw yF h1 h2 hz x φ hK hg u Wv hF hD i => ?_⟩
    choose xF hxF using hF
    have hu : IsUnit (Matrix.of z).det := isUnit_iff_ne_zero.2 hdet
    let Gw : Fin g → Fin g → ℂ := fun i' => Matrix.vecMul (Wv (Fin.cast hg.symm i')) (Matrix.of z)⁻¹
    have hGw : ∀ i' j, Wv (Fin.cast hg.symm i') j = ∑ k, Gw i' k * z k j := fun i' j => by
      have e0 : Matrix.vecMul (Gw i') (Matrix.of z) = Wv (Fin.cast hg.symm i') := by
        simp only [Gw]
        rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hu, Matrix.vecMul_one]
      rw [← e0]
      simp [Matrix.vecMul, dotProduct]
    have hω : ∀ (hz' : ⊤ ≤ (yF ≫ Y.j) ⁻¹ᵁ M.U) (i' : Fin g) (Vo : Y.t.G.left.Opens) (f : Γ(Y.t.G.left, Vo)),
        ⊤ ≤ (spMap (dualMap (ev (yF ≫ Y.j) M.U hz')) ≫ M.v₀ (Fin.cast hn.symm i')) ⁻¹ᵁ Vo →
        (valR (spMap (dualMap (ev (yF ≫ Y.j) M.U hz')) ≫ M.v₀ (Fin.cast hn.symm i')) Vo f).snd =
          ∑ k, Gw i' k * fderiv ℂ (fun t => valAt' (xF t ≫ Y.m.φ) Vo f) 0 (z k) := by
      intro hz' i' Vo f hV
      rw [point_snd M hK u (fun t => xF t ≫ Y.m.φ) (fun t => (hxF t).2.2.symm) (Fin.cast hg.symm i') (Fin.cast hn.symm i')
        rfl _ (hD _) Vo hV f]
      have e3 : Wv (Fin.cast hg.symm i') = ∑ k, Gw i' k • z k := funext fun j => by
        rw [hGw i' j, Finset.sum_apply]
        simp
      rw [e3, map_sum]
      simp [smul_eq_mul]
    have hT' := hT ⟨(w, yF, xF, Gw), h1, h2, fun t => ⟨(hxF t).1, (hxF t).2.1⟩, hz, hω⟩ hw i
    have hS : ∀ k, SumsAt (A i k) w (Gw i k) := fun k => GlobalTheory.Conv.sumsAt_iff.2 (hT' k)
    refine ⟨fun k => HasSum.summable (hS k), fun j => ?_⟩
    rw [hGw i j]
    exact Finset.sum_congr rfl fun k _ => by rw [HasSum.tsum_eq (hS k)]
  intro i
  obtain ⟨Vo, hVo, hpV, -⟩ := exists_isAffineOpen_mem_and_subset (X := Y.t.G.left) (U := ⊤)
    (x := (show Sp (PowerSeries ℂ) ⟶ Y.t.G.left from (η[W.t.G]).left ≫ W.m.φ) (IsLocalRing.closedPoint (PowerSeries ℂ)))
    trivial
  have hVη : ⊤ ≤ ((η[W.t.G]).left ≫ W.m.φ) ⁻¹ᵁ Vo :=
    (Scheme.preimage_eq_top_of_closedPoint_mem (R := CommRingCat.of (PowerSeries ℂ)) _ hpV).ge
  have hvV : ∀ k, ⊤ ≤ ((v k).left ≫ W.m.φ) ⁻¹ᵁ Vo := fun k => tan_le hcart _ (tanv k) Vo hVη
  have hv'V : ⊤ ≤ ((v' i).left ≫ W.m.φ) ⁻¹ᵁ Vo := tan_le hcart _ (comb_tan v tanv _ _ (hA i)) Vo hVη
  let φL : Γ(Y.X, M.U) →+* ℂ⸨X⸩ := (HahnSeries.ofPowerSeries ℤ ℂ).comp (ev χ M.U hM)
  have eχ : spMap (dualMap φL) ≫ M.v₀ (Fin.cast hn.symm i) =
      spMap (dualMap (HahnSeries.ofPowerSeries ℤ ℂ)) ≫ (v' i).left ≫ W.m.φ := by
    rw [hv' i, dualMap_comp, ← spMap_comp', Category.assoc]
  have hc : ∀ r, Cv pw (φL r) (fun ω => ψ ω r) := by
    intro r
    obtain ⟨T', hT'⟩ := Ha.point M.U r hM
    refine high_iff.2 ⟨T', fun ω hω => ?_⟩
    obtain ⟨-, hs⟩ := hT' _ hω ω.1.2.1 ω.2.1 ω.2.2.1
    have h3 := GlobalTheory.Conv.sumsAt_iff.1 hs
    have e4 : valR χ M.U r = ev χ M.U hM r := valR_eq_ev' χ M.U hM r
    have e5 : valAt' (ω.1.2.1 ≫ Y.j) M.U r = ψ ω r := valR_eq_ev' (ω.1.2.1 ≫ Y.j) M.U ω.2.2.2.2.1 r
    rw [e4, e5] at h3
    exact h3
  have hch := fun f => cv_chart (M.v₀ (Fin.cast hn.symm i)) Vo f φL ψ hc (by rw [eχ]; exact le_preimage_comp _ hv'V)
  refine cv_coeff (F := Γ(Y.t.G.left, Vo)) (m := g)
    (A := fun f k => HahnSeries.ofPowerSeries ℤ ℂ (valR ((v k).left ≫ W.m.φ) Vo f).snd)
    (B := fun f => HahnSeries.ofPowerSeries ℤ ℂ (valR ((v' i).left ≫ W.m.φ) Vo f).snd)
    (Aw := fun f k ω => fderiv ℂ (fun t => valAt' (ω.1.2.2.1 t ≫ Y.m.φ) Vo f) 0 (z k))
    (Bw := fun f ω => (valR (spMap (dualMap (ψ ω)) ≫ M.v₀ (Fin.cast hn.symm i)) Vo f).snd)
    (Gw := fun k ω => ω.1.2.2.2 i k)
    (fun f => ?_) (sep_laurent hcart v hvb hVo hVη) (fun f k => ?_) (fun f => ?_) (fun f => ?_)
  · rw [comb_snd hcart v tanv (A i) (v' i) (hA i) Vo hVη f, map_sum]
    exact Finset.sum_congr rfl fun k _ => map_mul _ _ _
  · obtain ⟨T', hT'⟩ := Ha.diff (z k) (e k) (v k) Vo f (hez k).2.1 (hez k).2.2
      (fun n ρ κ vn h1 h2 h3 h4 h5 => (hez k).1 n ρ κ vn h1 h2 h3 h4 (thick_base _ n (v k) ρ vn h1 h5) h5) (hvV k)
    exact high_iff.2 ⟨T', fun ω hω => GlobalTheory.Conv.sumsAt_iff.1 (hT' _ hω _ ω.2.2.2.1)⟩
  · have h1 := (hch f).2
    rw [eχ, GlobalTheory.HolHom.valR_spMap _ _ _ hv'V] at h1
    simpa [dualMap] using h1
  · filter_upwards [(hch f).1] with ω hω
    exact ω.2.2.2.2.2 ω.2.2.2.2.1 i Vo f hω

end GlobalTheory.ArcLieCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BalancedIntMatrixTriangularGramAdjointWeightedSqStatement
section
open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.balancedIntMatrix_triangularGram_adjoint_weighted_sq_trace : ∀ (n : ℕ) (A A' : Matrix (Fin n) (Fin n) ℤ) (d : Fin n → ℝ) (u v : Matrix (Fin n) (Fin n) ℝ), (∀ i, 0 < d i) → v * u = 1 → u * v = 1 → (A.map (Int.cast : ℤ → ℝ))ᵀ * gram d u = gram d u * A'.map (Int.cast : ℤ → ℝ) → (∀ p q, d p * (u * A.map (Int.cast : ℤ → ℝ) * v) p q = d q * (u * A'.map (Int.cast : ℤ → ℝ) * v) q p) ∧ (∑ p, ∑ q, d p / d q * (u * A.map (Int.cast : ℤ → ℝ) * v) p q ^ 2 = (((A' * A).trace : ℤ) : ℝ)) ∧ ∑ p, ∑ q, d p / d q * (u * A'.map (Int.cast : ℤ → ℝ) * v) p q ^ 2 = (((A' * A).trace : ℤ) : ℝ) := by
  first | exact @GlobalTheory.RedTh.adjoint_weighted_sq_trace | exact GlobalTheory.RedTh.adjoint_weighted_sq_trace | (intros; apply GlobalTheory.RedTh.adjoint_weighted_sq_trace <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BalancedPsdRationalRadicalConeSubsetIntCone
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolFan

theorem psdCone_subset_psdCone_int (O : Type) [CommRing O] [Module.Finite ℤ O] [Module.Free ℤ O] (bar : O → O)
    (X : Type) [AddCommGroup X] [Module O X] : psdCone bar X ⊆ psdCone (id : ℤ → ℤ) X := by
  rintro B ⟨X₁, _, _, hP, r, B₁, hr, h1, h2, h3⟩
  haveI : Module.Projective ℤ X₁ := by
    obtain ⟨s, hs⟩ := Module.projective_def'.1 hP
    exact Module.Projective.of_split (s.restrictScalars ℤ) ((Finsupp.linearCombination O id).restrictScalars ℤ)
      (by ext x; exact congrArg (· x) hs)
  refine ⟨X₁, inferInstance, inferInstance, inferInstance, r.toAddMonoidHom.toIntLinearMap, B₁, hr,
    ⟨h1.1, fun a y z => ?_⟩, h2, h3⟩
  show B₁ (a • y) z = B₁ y (a • z)
  rw [map_zsmul, map_zsmul, LinearMap.smul_apply]

end GlobalTheory.PolFan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseChangeAdjoint
section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open scoped TensorProduct
open GlobalTheory.EigenSplit GlobalTheory.HTLat GlobalTheory.TotalFrame

namespace GlobalTheory.RedForm

theorem bilin_skew_of_alt {M : Type} [AddCommGroup M] (B : LinearMap.BilinForm ℤ M) (halt : ∀ x, B x x = 0)
    (x y : M) : B x y = - B y x := by
  have h := halt (x + y)
  simp only [map_add, LinearMap.add_apply, halt, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact h)

theorem baseChange_adjoint {K M : Type} [CommRing K] [AddCommGroup M] (B : LinearMap.BilinForm ℤ M)
    (f g : Module.End ℤ M) (h : ∀ x y, B x (f y) = B (g x) y) (x y : K ⊗[ℤ] M) :
    B.baseChange K x (f.baseChange K y) = B.baseChange K (g.baseChange K x) y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul k m =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul k' m' => simp [LinearMap.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul, h]
    | add y1 y2 h1 h2 => simp only [map_add, h1, h2]
  | add x1 x2 h1 h2 => simp only [map_add, LinearMap.add_apply, h1, h2]

theorem baseChange_nondeg {K M : Type} [CommRing K] [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]
    (B : LinearMap.BilinForm ℤ M) (hskew : ∀ x y, B x y = - B y x) (hB : Function.Bijective B)
    (x : K ⊗[ℤ] M) (hx : ∀ y, B.baseChange K x y = 0) : x = 0 := by
  let b := Module.Free.chooseBasis ℤ M
  let b' := Algebra.TensorProduct.basis K b
  choose c hc using fun j => hB.2 (b.coord j)
  have key : ∀ j, (B.baseChange K).flip (1 ⊗ₜ (-c j)) = b'.coord j := by
    intro j
    refine b'.ext fun i => ?_
    show B.baseChange K (b' i) (1 ⊗ₜ (-c j)) = b'.coord j (b' i)
    rw [Algebra.TensorProduct.basis_apply, LinearMap.BilinForm.baseChange_tmul,
      Module.Basis.coord_apply, Algebra.TensorProduct.basis_repr_tmul, map_neg, hskew, neg_neg, hc, Module.Basis.coord_apply,
      b.repr_self, one_smul, one_mul]
    by_cases hij : i = j
    · subst hij; simp
    · simp [Finsupp.single_eq_of_ne hij, Finsupp.single_eq_of_ne' hij]
  refine b'.forall_coord_eq_zero_iff.1 fun j => ?_
  rw [← key j]
  exact hx _

theorem free_of_unimod {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} (Dw : Datum H) :
    Module.Free ℤ Dw.La := by
  have := Dw.fin
  have : Module.Finite ℤ Dw.La := .trans (𝓞 E) _
  have : Module.IsTorsionFree ℤ Dw.La := by
    have : NoZeroSMulDivisors ℤ Dw.La := by
      refine ⟨fun {n x} h => or_iff_not_imp_left.2 fun hn => Dw.unimod.1 ?_⟩
      refine LinearMap.ext fun y => ?_
      have h1 : Dw.EF (n • x) y = n * Dw.EF x y := by simp
      rw [h, map_zero, LinearMap.zero_apply] at h1
      simpa [hn] using h1.symm
    infer_instance
  exact Module.free_of_finite_type_torsion_free'

theorem psiBar_props : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (p : ℕ) (ct : At S κ p),
  (∀ a : 𝓞 D.host.E, (A.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) ((A.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) a) = a) ∧
  (∀ (a : 𝓞 D.host.E) (x y : ct.LaBar), ct.psiBar x ((baseChangeAction ct.kbar (Module.toModuleEnd ℤ S.Dw.La : 𝓞 D.host.E →+* Module.End ℤ S.Dw.La)) a y) = ct.psiBar ((baseChangeAction ct.kbar (Module.toModuleEnd ℤ S.Dw.La : 𝓞 D.host.E →+* Module.End ℤ S.Dw.La)) ((A.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) a) x) y) ∧
  (∀ x : ct.LaBar, (∀ y, ct.psiBar x y = 0) → x = 0) := by
  intro D A N j S κ p ct
  have hbb : ∀ a : 𝓞 D.host.E, A.H.bar (A.H.bar a) = a := fun a => by
    apply RingOfIntegers.ext
    rw [A.H.bar_eq, A.H.bar_eq, IsCMField.complexConj_apply_apply]
  have hskew := bilin_skew_of_alt S.Dw.EF S.Dw.alt
  refine ⟨fun a => hbb a, fun a x y => ?_, fun x hx => ?_⟩
  · rw [baseChangeAction_apply, baseChangeAction_apply]
    refine baseChange_adjoint S.Dw.EF _ _ (fun u v => ?_) x y
    simp only [Module.toModuleEnd_apply, DistribSMul.toLinearMap_apply, RingHom.coe_coe]
    rw [hskew, S.Dw.adj, hskew (A.H.bar a • u)]
  · have := free_of_unimod S.Dw
    have := S.Dw.fin
    have : Module.Finite ℤ S.Dw.La := .trans (𝓞 D.host.E) _
    exact baseChange_nondeg S.Dw.EF hskew S.Dw.unimod x hx

end GlobalTheory.RedForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundedCombinationOfSpanCoordinateRowsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bounded_combination_of_span_coordinate_rows : ∀ (X : Type) (g r r₀ : ℕ) (T : Set X) (lam : X → Fin r → Fin g → ℂ) (u : X → Fin r₀ → Fin g → ℂ) (A : Fin r₀ → Fin r → ℤ) (C : ℝ), (∀ x ∈ T, ∀ i, u x i = ∑ m, A i m • lam x m) → (∀ x ∈ T, ‖u x‖ ≤ C) → ∀ w ∈ Submodule.span ℝ (Set.range fun i j => (A i j : ℝ)), ∃ C' : ℝ, ∀ x ∈ T, ‖∑ j, (w j : ℂ) • lam x j‖ ≤ C' := by
  first | exact @GlobalTheory.combo_of_bounded_rows_bounded | exact GlobalTheory.combo_of_bounded_rows_bounded | (intros; apply GlobalTheory.combo_of_bounded_rows_bounded <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarrierIndependentSpanIffStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.carrier_independent_span_iff : ∀ (O : Type) [CommRing O] (Z Z' : Scheme.{0}) (C : Coc Z) (N k : ℕ) (Em : C.Emb N) (f : Z' ⟶ Z) (q : Z' ⟶ PSpace O (plN N k)) (K : Type) [Field K] (w : Sp K ⟶ Z') (β : C.A) (hβ : ⊤ ≤ (w ≫ f) ⁻¹ᵁ C.B β) (ξ : Fin k → Fin (C.n β) → K), Car Em f q w β hβ ξ → LinearIndependent K ξ ∧ (∀ ξ' : Fin k → Fin (C.n β) → K, Car Em f q w β hβ ξ' ↔ LinearIndependent K ξ' ∧ Submodule.span K (Set.range ξ') = Submodule.span K (Set.range ξ)) ∧ ∀ (α : C.A) (hα : ⊤ ≤ (w ≫ f) ⁻¹ᵁ C.B α), Car Em f q w α hα fun l => (C.tr α β (w ≫ f) hα hβ).mulVec (ξ l) := by
  first | exact @GlobalTheory.GrCl.car_span | exact GlobalTheory.GrCl.car_span | (intros; apply GlobalTheory.GrCl.car_span <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellCoordinatesBaseChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_coordinates_base_change : ∀ (K R R' : Type) [Field K] [CommRing R] [CommRing R'] (m a k b N : ℕ) (hk : k ≤ m) (D c : Fin m → Fin (N + 1) → R) (D' c' : Fin m → Fin (N + 1) → R') (φ : R →+* K) (ψ' : MvPolynomial (GVar m a k b) R' →+* K) (w' : GPm m a b), a ≤ k → k ≤ b → LeftInv D c → LeftInv D' c' → (∀ e : ℕ, e = a ∨ e = b → initSpan K (fun l => φ ∘ c l) e = initSpan K (fun l => (ψ'.comp MvPolynomial.C) ∘ c' l) e) → (∃ w : GPm m a b, ∑ q, φ (gell a b hk D w q) * ψ' (gxi a b hk c' w' q) ≠ 0) ∧ ∀ w : GPm m a b, ∑ q, φ (gell a b hk D w q) * ψ' (gxi a b hk c' w' q) ≠ 0 → ∃ (ψ : MvPolynomial (GVar m a k b) R →+* K) (u : Kˣ), ψ.comp MvPolynomial.C = φ ∧ ψ' ∘ gxi a b hk c' w' = (u : K) • (ψ ∘ gxi a b hk c w) := by
  first | exact @GlobalTheory.GrCl.CellGlue.mem_cell_of_initSpan_eq | exact GlobalTheory.GrCl.CellGlue.mem_cell_of_initSpan_eq | (intros; apply GlobalTheory.GrCl.CellGlue.mem_cell_of_initSpan_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharacterTrivialOnUnitTransvectionsStatement
section
open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_trivial_on_unit_transvections : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N), 1 < Module.finrank ℚ E / 2 → ∀ (φ : X.Γ →* Multiplicative ℝ) (ξ : Fin N → E), ξ ∈ X.Λ → ξ ≠ 0 → herm X.Gm ξ ξ = 0 → ∃ u : 𝓞 E, u ≠ 0 ∧ cc (u : E) = u ∧ ∀ t : E, cc t = t → IsIntegral ℤ t → ∀ γ : X.Γ, ((γ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) = transvMat X.Gm ξ (X.m * (u * t) * X.κ0) → φ γ = 1 := by
  first | exact @GlobalTheory.UnipKill.killsScaled | exact GlobalTheory.UnipKill.killsScaled | (intros; apply GlobalTheory.UnipKill.killsScaled <;> assumption)
end

