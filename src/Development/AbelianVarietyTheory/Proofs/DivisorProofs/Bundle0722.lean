import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0602
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SplitsAt
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0031
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0686
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0700
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0656
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0268
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0657

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomFixRepBasicOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out

noncomputable section

namespace GlobalTheory.HomFixTransport

theorem lbIso_self {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) : LBIso L L := by
  refine ⟨⟨fun p => L.g p.1 p.2⟩, fun p q => unit_ext fun y hy => ?_⟩
  refine (gm_res _ y _ hy _).trans (Eq.symm ((map_mul _ _ _).trans ((congrArg₂ (· * ·)
    (gm_div L L (𝟙 X) y p q hy) (gm_res _ y _ hy _)).trans ?_)))
  have a := gm_cocycle hL (𝟙 X) y hy.1.1 hy.2.1 hy.2.2
  have b := gm_cocycle hL (𝟙 X) y hy.1.1 hy.1.2 hy.2.2
  show gm (𝟙 X) y _ (L.g p.1 q.1) * (gm (𝟙 X) y _ (L.g p.2 q.2))⁻¹ * gm (𝟙 X) y _ (L.g q.1 q.2) =
    gm (𝟙 X) y _ (L.g p.1 p.2)
  rw [mul_right_comm, a, ← b, mul_inv_cancel_right]

theorem lbIso_pull_pull {X Y Y' Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (F : Y ⟶ X) (G : Z ⟶ Y) (F' : Y' ⟶ X)
    (G' : Z ⟶ Y') (h : G ≫ F = G' ≫ F') : LBIso ((L.pull F).pull G) ((L.pull F').pull G') :=
  LBIso.chartPull
    (chartPullLinComb L F (fun _ : PUnit => G) (fun _ => G ≫ F) (fun _ => 1) (𝟙 Z)
      fun _ => (Category.id_comp _).symm)
    (chartPullLinComb L F' (fun _ : PUnit => G') (fun _ => G ≫ F) (fun _ => 1) (𝟙 Z)
      fun _ => by rw [Category.id_comp, h])
    (lbIso_self (pull_isLB hL (G ≫ F)))

theorem lbIso_pull {X Y : Scheme.{0}} {L M : LB X} (H : LBIso L M) (h : Y ⟶ X) : LBIso (L.pull h) (M.pull h) :=
  LBIso.chartPull (chartPullPull L h h rfl) (chartPullPull M h h rfl) H

theorem lbIso_congr {X : Scheme.{0}} {P P' Q Q' : LB X} (hP : P.IsLB) (hP' : P'.IsLB) (hQ : Q.IsLB) (hQ' : Q'.IsLB)
    (e₁ : LBIso P' P) (H : LBIso P Q) (e₂ : LBIso Q Q') : LBIso P' Q' :=
  LBIso.trans hP' hQ hQ' (LBIso.trans hP' hP hQ e₁ H) e₂

section Transport

variable {S S₁ S₂ : Scheme.{0}} (e : S₁ ≅ S₂) {A B : Over S} [GrpObj A] [GrpObj B] {L : LB A.left} {M : LB B.left}
  (hL : L.IsLB) (hM : M.IsLB) {Af Bf : Over S₂} [GrpObj Af] [GrpObj Bf] (φA : Af.left ⟶ A.left)
  (φB : Bf.left ⟶ B.left)

def transport (R : HomFixRep Af Bf (L.pull φA) (M.pull φB)) :
    HomFixRep ((Over.pullback e.hom).obj Af) ((Over.pullback e.hom).obj Bf)
      (L.pull (pullback.fst Af.hom e.hom ≫ φA)) (M.pull (pullback.fst Bf.hom e.hom ≫ φB)) where
  H := R.H
  π := R.π ≫ e.inv
  AH := R.AH
  BH := R.BH
  φA := pullback.lift R.φA (R.AH.hom ≫ R.π ≫ e.inv) (by simp [R.pbA.1.w])
  φB := pullback.lift R.φB (R.BH.hom ≫ R.π ≫ e.inv) (by simp [R.pbB.1.w])
  pbA := ReciprocityTheory.ChartRestriction.G.Chart.isGrpPullback_factor e.hom (R.π ≫ e.inv) (R.pbA.congr (by simp) rfl)
  pbB := ReciprocityTheory.ChartRestriction.G.Chart.isGrpPullback_factor e.hom (R.π ≫ e.inv) (R.pbB.congr (by simp) rfl)
  Φ := R.Φ
  hom := R.hom
  iso := lbIso_congr (pull_isLB (pull_isLB hL _) _) (pull_isLB (pull_isLB hL _) _)
    (pull_isLB (pull_isLB (pull_isLB hM _) _) _) (pull_isLB (pull_isLB (pull_isLB hM _) _) _)
    (lbIso_pull_pull hL _ _ _ _ (by erw [pullback.lift_fst_assoc])) R.iso
    (lbIso_pull (lbIso_pull_pull hM _ _ _ _ (by erw [pullback.lift_fst_assoc])) _)
  rep := by
    intro T t A' B' _ _ φA' φB' Φ' hA hB hΦ hI
    have hA₂ := hA.comp (isGrpPullback_pullback Af e.hom)
    have hB₂ := hB.comp (isGrpPullback_pullback Bf e.hom)
    obtain ⟨h, ⟨hπ, ψA, ψB, pA, pB, eA, eB, eΦ⟩, hu⟩ := R.rep T (t ≫ e.hom) A' B'
      (φA' ≫ pullback.fst Af.hom e.hom) (φB' ≫ pullback.fst Bf.hom e.hom) Φ' hA₂ hB₂ hΦ
      (lbIso_congr (pull_isLB (pull_isLB hL _) _) (pull_isLB (pull_isLB hL _) _)
        (pull_isLB (pull_isLB (pull_isLB hM _) _) _) (pull_isLB (pull_isLB (pull_isLB hM _) _) _)
        (lbIso_pull_pull hL φA (φA' ≫ pullback.fst Af.hom e.hom) (pullback.fst Af.hom e.hom ≫ φA) φA' (by simp)) hI
        (lbIso_pull (lbIso_pull_pull hM (pullback.fst Bf.hom e.hom ≫ φB) φB' φB (φB' ≫ pullback.fst Bf.hom e.hom)
          (by simp)) Φ'.left))
    refine ⟨h, ⟨?_, ψA, ψB, pA, pB, ?_, ?_, eΦ⟩, ?_⟩
    · rw [← Category.assoc, hπ, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    · apply pullback.hom_ext
      · erw [Category.assoc, pullback.lift_fst]; exact eA
      · simp only [Category.assoc, pullback.lift_snd]
        rw [reassoc_of% pA.1.w, reassoc_of% hπ, Iso.hom_inv_id, Category.comp_id]
        exact hA.1.w.symm
    · apply pullback.hom_ext
      · erw [Category.assoc, pullback.lift_fst]; exact eB
      · simp only [Category.assoc, pullback.lift_snd]
        rw [reassoc_of% pB.1.w, reassoc_of% hπ, Iso.hom_inv_id, Category.comp_id]
        exact hB.1.w.symm
    · rintro h' ⟨hπ', ψA', ψB', pA', pB', eA', eB', eΦ'⟩
      refine hu h' ⟨by rw [← hπ']; simp, ψA', ψB', pA', pB', by rw [← eA', Category.assoc]; erw [pullback.lift_fst],
        by rw [← eB', Category.assoc]; erw [pullback.lift_fst], eΦ'⟩

end Transport

end GlobalTheory.HomFixTransport

open GlobalTheory.HomFixTransport in

theorem GlobalTheory.HomFixTransport.homFixRep_basicOpen : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (f : Rg), L.IsLB → M.IsLB → (∀ (Af Bf : Over (Sp (Localization.Away f))) [GrpObj Af] [GrpObj Bf] (φA : Af.left ⟶ A.left) (φB : Bf.left ⟶ B.left), IsGrpPullback Af A (spMap (algebraMap Rg (Localization.Away f))) φA → IsGrpPullback Bf B (spMap (algebraMap Rg (Localization.Away f))) φB → ∃ R : HomFixRep Af Bf (L.pull φA) (M.pull φB), QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π) → ∀ U : (Sp Rg).Opens, U = PrimeSpectrum.basicOpen f → ∃ (AU : Over U.toScheme) (_ : GrpObj AU) (BU : Over U.toScheme) (_ : GrpObj BU) (φA : AU.left ⟶ A.left) (φB : BU.left ⟶ B.left), IsGrpPullback AU A U.ι φA ∧ IsGrpPullback BU B U.ι φB ∧ ∃ R : HomFixRep AU BU (L.pull φA) (M.pull φB), QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π := by
  intro Rg _ A B _ _ L M f hL hM hyp U hU
  have hr : Set.range U.ι = Set.range (spMap (algebraMap Rg (Localization.Away f))) := by
    rw [Scheme.Opens.range_ι, hU]
    exact (PrimeSpectrum.localization_away_comap_range (Localization.Away f) f).symm
  haveI : IsOpenImmersion (spMap (algebraMap Rg (Localization.Away f))) :=
    inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap Rg (Localization.Away f)))))
  let e := IsOpenImmersion.isoOfRangeEq U.ι (spMap (algebraMap Rg (Localization.Away f))) hr
  have he : e.hom ≫ spMap (algebraMap Rg (Localization.Away f)) = U.ι := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  obtain ⟨R, h₁, h₂, h₃⟩ := hyp _ _ _ _ (isGrpPullback_pullback A (spMap (algebraMap Rg (Localization.Away f))))
    (isGrpPullback_pullback B (spMap (algebraMap Rg (Localization.Away f))))
  refine ⟨_, inferInstance, _, inferInstance, _, _,
    ((isGrpPullback_pullback _ e.hom).comp (isGrpPullback_pullback A _)).congr he rfl,
    ((isGrpPullback_pullback _ e.hom).comp (isGrpPullback_pullback B _)).congr he rfl,
    transport e hL hM _ _ R, ?_, ?_, ?_⟩
  · show QuasiCompact (R.π ≫ e.inv); infer_instance
  · show IsSeparated (R.π ≫ e.inv); infer_instance
  · show LocallyOfFiniteType (R.π ≫ e.inv); infer_instance
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomFixRepOfUniversal
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.EndLoc.HomFixGlue
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open Opposite

namespace GlobalTheory.EndLoc.HomFixGlue

theorem pullPull_mem {X Y Z Y' Z' : Scheme.{0}} (M : LB X) (F : Y ⟶ X) (G : Z ⟶ Y) (F' : Y' ⟶ X) (G' : Z' ⟶ Y')
    (h : Z' ⟶ Z) (hc : G' ≫ F' = h ≫ G ≫ F) (J : PUnit → PUnit → M.ι) (y : Z')
    (hy : y ∈ ((M.pull F').pull G').U J) :
    h y ∈ ((M.pull F).pull G).U (fun _ => fun _ => J PUnit.unit PUnit.unit) := by
  have h1 := mem_pull.1 (mem_pull.1 hy)
  have e : F (G (h y)) = F' (G' y) := by
    have := congrArg (fun k => k y) hc
    simpa using this.symm
  exact mem_pull.2 (mem_pull.2 (by rw [e]; exact h1))

def chartPullPullPull {X Y Z Y' Z' : Scheme.{0}} (M : LB X) (F : Y ⟶ X) (G : Z ⟶ Y) (F' : Y' ⟶ X) (G' : Z' ⟶ Y')
    (h : Z' ⟶ Z) (hc : G' ≫ F' = h ≫ G ≫ F) : ChartPull ((M.pull F').pull G') ((M.pull F).pull G) h where
  idx J := fun _ => fun _ => J PUnit.unit PUnit.unit
  le J y hy := pullPull_mem M F G F' G' h hc J y hy
  g y J J' hj hj' := by
    have a1 := gm_pull_g (M.pull F') G' (𝟙 _) y J J' hj hj'
    have a2 := gm_pull_g M F' (𝟙 _ ≫ G') y (J PUnit.unit) (J' PUnit.unit) (mem_pull.1 hj) (mem_pull.1 hj')
    have m1 := pullPull_mem M F G F' G' h hc J y hj
    have m2 := pullPull_mem M F G F' G' h hc J' y hj'
    have b1 := gm_pull_g (M.pull F) G h y _ _ m1 m2
    have b2 := gm_pull_g M F (h ≫ G) y (fun _ => J PUnit.unit PUnit.unit) (fun _ => J' PUnit.unit PUnit.unit)
      (mem_pull.1 m1) (mem_pull.1 m2)
    rw [a1, a2, b1, b2]
    have e : (𝟙 _ ≫ G') ≫ F' = (h ≫ G) ≫ F := by simp [hc]
    rw [e]

section
variable {S : Scheme.{0}}

variable (A B : Over S) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left)

end

end GlobalTheory.EndLoc.HomFixGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HormanderEstimateOnBallConstLeviBound
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.HormanderBall

open ReciprocityTheory.ChartRestriction.G.AR.Up.HE

theorem measurable_wdb (n : ℕ) (j : Fin n) (g : V n → ℂ) : Measurable (wdb n j g) := by
  unfold wdb
  exact (((measurable_fderiv_apply_const ℝ g _).add
    ((measurable_fderiv_apply_const ℝ g _).const_mul _)).div_const _)

theorem norm_sum_mul_conj_sq_le {n : ℕ} (a ξ : Fin n → ℂ) :
    ‖∑ j, a j * (starRingEnd ℂ) (ξ j)‖ ^ 2 ≤ (∑ j, ‖a j‖ ^ 2) * ∑ j, ‖ξ j‖ ^ 2 := by
  have h1 : ‖∑ j, a j * (starRingEnd ℂ) (ξ j)‖ ≤ ∑ j, ‖a j‖ * ‖ξ j‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [norm_mul, Complex.norm_conj]
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖a j‖) (fun j => ‖ξ j‖)
  calc ‖∑ j, a j * (starRingEnd ℂ) (ξ j)‖ ^ 2 ≤ (∑ j, ‖a j‖ * ‖ξ j‖) ^ 2 := by
        gcongr
    _ ≤ _ := h2

theorem hormander_ball : ∀ (n : ℕ) (c : V n) (r t : ℝ) (φ : V n → ℝ) (F0 : V n → ℂ), 0 < t → ContDiffOn ℝ ∞ φ (ball c r) → ContDiffOn ℝ ∞ F0 (ball c r) → (∀ v ∈ ball c r, ∀ ξ : Fin n → ℂ, t * ∑ j, ‖ξ j‖ ^ 2 ≤ (leviV n (fun w => (φ w : ℂ)) v ξ).re) → ∃ F : V n → ℂ, DifferentiableOn ℂ F (ball c r) ∧ ∫⁻ v in ball c r, ENNReal.ofReal (‖F0 v - F v‖ ^ 2 * Real.exp (-φ v)) ≤ ENNReal.ofReal t⁻¹ * ∫⁻ v in ball c r, ENNReal.ofReal ((∑ j, ‖wdb n j F0 v‖ ^ 2) * Real.exp (-φ v)) := by
  intro n c r t φ F0 ht hφ hF0 hlevi
  have hU : IsOpen (ball c r) := isOpen_ball
  obtain ⟨X, hX⟩ := GlobalTheory.T.ball_exists_etaleStein_exhaustion n c r
  set h : V n → ℝ≥0∞ := fun v => ENNReal.ofReal (t⁻¹ * ∑ j, ‖wdb n j F0 v‖ ^ 2) with hhdef
  have hh : Measurable h := by
    refine ENNReal.measurable_ofReal.comp (Measurable.const_mul ?_ _)
    exact Finset.measurable_sum _ fun j _ => ((measurable_wdb n j F0).norm.pow_const 2)
  have hb : ∀ y ∈ ball c r, ∀ ξ : Fin n → ℂ,
      ENNReal.ofReal (‖∑ j, wdb n j F0 y * (starRingEnd ℂ) (ξ j)‖ ^ 2) ≤
        h y * ENNReal.ofReal (leviV n (fun w => (φ w : ℂ)) y ξ).re := by
    intro y hy ξ
    rw [hhdef, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ((norm_sum_mul_conj_sq_le _ _).trans ?_)
    have h1 := hlevi y hy ξ
    have h2 : ∑ j, ‖ξ j‖ ^ 2 ≤ t⁻¹ * (leviV n (fun w => (φ w : ℂ)) y ξ).re := by
      rw [le_inv_mul_iff₀ ht]; exact h1
    have h3 : 0 ≤ ∑ j, ‖wdb n j F0 y‖ ^ 2 := by positivity
    calc (∑ j, ‖wdb n j F0 y‖ ^ 2) * ∑ j, ‖ξ j‖ ^ 2
        ≤ (∑ j, ‖wdb n j F0 y‖ ^ 2) * (t⁻¹ * (leviV n (fun w => (φ w : ℂ)) y ξ).re) := by
          gcongr
      _ = _ := by ring
  obtain ⟨F, hF, hest⟩ := hormander n (ball c r) X (fun x => φ x.1) (fun x => F0 x.1)
    (fun x => h x.1)
    (by rw [hX]; exact smoothR_val hφ)
    (fun x ξ => by
      rw [hX, levi_val hU]
      exact le_trans (by positivity) (hlevi x.1 x.2 ξ))
    (by rw [hX]; exact smooth_val hF0)
    (hh.comp measurable_subtype_coe) (fun x ξ => by
      have := hb x.1 x.2 ξ
      rw [hX]
      show ENNReal.ofReal (‖dbarDot n Subtype.val (fun x : ball c r => F0 x.1) x ξ‖ ^ 2) ≤
        h x.1 * ENNReal.ofReal (Levi n Subtype.val (fun x : ball c r => φ x.1) x ξ).re
      simp only [dbarDot, db_val hU]
      rw [levi_val hU]
      exact this)
  refine ⟨ext0 F, differentiableOn_extendByZero hU (hX ▸ hF), ?_⟩
  have hest' : wint n Subtype.val (fun x : ball c r => F0 x.1 - F x) (fun x : ball c r => φ x.1) ≤
      ∫⁻ x, h x.1 * ENNReal.ofReal (Real.exp (-φ x.1)) ∂vol n (Subtype.val : ball c r → V n) := by
    rw [hX] at hest; exact hest
  have h4 : ∫⁻ v in ball c r, ENNReal.ofReal (‖F0 v - ext0 F v‖ ^ 2 * Real.exp (-φ v)) ≤
      ∫⁻ v in ball c r, h v * ENNReal.ofReal (Real.exp (-φ v)) := by
    rw [← lintegral_val hU, ← lintegral_val hU]
    simpa [wint, extendByZeroOnSubset_apply_coe] using hest'
  refine h4.trans (le_of_eq ?_)
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun hU.measurableSet fun v _ => ?_
  rw [hhdef, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  ring_nf

end GlobalTheory.HormanderBall
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperH2GeneratedByCups
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh.SpanCup

theorem sum_append {R M N P : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] (B : M →ₗ[R] N →ₗ[R] P) {n m : ℕ} (a : Fin n → M) (b : Fin n → N)
    (a' : Fin m → M) (b' : Fin m → N) :
    ∑ k, B (a k) (b k) + ∑ k, B (a' k) (b' k) = ∑ k, B (Fin.append a a' k) (Fin.append b b' k) := by
  rw [Fin.sum_univ_add]; simp [Fin.append_left, Fin.append_right]

theorem exists_sum_ιMulti {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (w : ⋀[R]^2 M) :
    ∃ (n : ℕ) (x y : Fin n → M), w = ∑ k, exteriorPower.ιMulti R 2 ![x k, y k] := by
  have hw : w ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R 2 (M := M))) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hw using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨v, rfl⟩ := hv
    refine ⟨1, fun _ ↦ v 0, fun _ ↦ v 1, ?_⟩
    rw [Fin.sum_univ_one]
    congr 1
    ext i; fin_cases i <;> rfl
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨n, x, y, rfl⟩ := hu
    obtain ⟨m, x', y', rfl⟩ := hv
    refine ⟨n + m, Fin.append x x', Fin.append y y', ?_⟩
    rw [Fin.sum_univ_add]
    simp [Fin.append_left, Fin.append_right]
  | smul r v _ hv =>
    obtain ⟨n, x, y, rfl⟩ := hv
    refine ⟨n, fun k ↦ r • x k, y, ?_⟩
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    have e : (![r • x k, y k] : Fin 2 → M) = Function.update ![x k, y k] 0 (r • ![x k, y k] 0) := by
      ext i; fin_cases i <;> simp
    rw [e, AlternatingMap.map_update_smul, Function.update_eq_self]

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

def fn2 : cechDeRhamTotalCocyclesTwo F →ₗ[R] Z2 F where
  toFun c := ⟨c.1.1, (mem_cechDeRhamTotalCocyclesTwo_iff.1 c.2).1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem cechDeRhamFunctionPart_cup_eq_cup (a b : cechDeRhamTotalCocyclesOne F) : fn2 F (cupZZ F a b) = cupZ F (cechDeRhamTotalCocyclesOne.fn F a) (cechDeRhamTotalCocyclesOne.fn F b) := rfl

end GlobalTheory.AbCoh.SpanCup

open GlobalTheory.AbCoh.SpanCup in

theorem GlobalTheory.AbCoh.hyp2_eq_sum_cupHyp : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → Closed1 F = ⊤ → Function.Surjective (toO F) →
    WedgeO F → ∀ z : Hyp2 F, ∃ (n : ℕ) (a b : Fin n → Hyp1 F), z = ∑ k, cupHyp F (a k) (b k) := by
  intro R _ C _ F hfr h0 hc hsurj hw z
  obtain ⟨c, rfl⟩ := Hyp2.mk_surjective F z
  obtain ⟨e, he⟩ := hw
  obtain ⟨n, x, y, hxy⟩ := exists_sum_ιMulti (e.symm (H2.mk F (fn2 F c)))
  have hrep : ∀ u : H1 F, ∃ p : cechDeRhamTotalCocyclesOne F, toO F (Hyp1.mk F p) = u := fun u ↦ by
    obtain ⟨q, hq⟩ := hsurj u
    obtain ⟨p, rfl⟩ := Hyp1.mk_surjective F q
    exact ⟨p, hq⟩
  choose p hp using hrep
  have hcls : H2.mk F (fn2 F c) = ∑ k, cup F (x k) (y k) := by
    have h := congrArg e hxy
    rw [LinearEquiv.apply_symm_apply] at h
    rw [h, map_sum]
    simp only [he]
  obtain ⟨c', hc'⟩ : ∃ c' : cechDeRhamTotalCocyclesTwo F, c' = c - ∑ k, cupZZ F (p (x k)) (p (y k)) := ⟨_, rfl⟩
  have hfn : ∃ f, d1 F f = c'.1.1 := by
    have h : H2.mk F (fn2 F c') = 0 := by
      rw [hc']
      simp only [map_sub, map_sum]
      rw [hcls, sub_eq_zero]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [cechDeRhamFunctionPart_cup_eq_cup, ← cup_mk, ← toO_mk, ← toO_mk, hp, hp]
    exact H2.mk_eq_zero.1 h
  obtain ⟨m, a, w, hm⟩ := GlobalTheory.T.hyper_h2_sum_of_cups_exact R C F hfr h0 hc hsurj c' hfn
  refine ⟨m + n, Fin.append a (fun k ↦ Hyp1.mk F (p (x k))),
    Fin.append (fun k ↦ clAll F hc (w k)) (fun k ↦ Hyp1.mk F (p (y k))), ?_⟩
  rw [← sum_append, ← hm, hc']
  simp only [map_sub, map_sum, cupHyp_mk, sub_add_cancel]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsSideBis
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer.Charts

theorem glue : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F), K.Rich → ∀ f : ∀ k, Hol (K.W k), (∀ k k' (h : K.le 0 k' k), Charts.sh h (f k) = f k') → ∃ G : Tot I g → ℂ, AnalyticOnNhd ℂ G {p | p.1 ∈ F.V} ∧ (∀ k, ∀ p ∈ K.W k, (f k).fn p = G p) ∧ (∀ (l : Λ) (q : Hol F.V), (∀ k k' (h : K.le l k' k), Charts.sh h (f k) = f k' + K.cst k' q) → ∀ p : Tot I g, p.1 ∈ F.V → G (F.shift l p) = G p + q.fn p.1) ∧ ((∀ k a, dw a (f k) = 0) → ∀ z ∈ F.V, ∀ w, G (z, w) = G (z, 0)) := by
  intro I _ g Λ _ F K hK f hf
  classical
  have indep : ∀ k₁ k₂ p, p ∈ K.W k₁ → p ∈ K.W k₂ → (f k₁).fn p = (f k₂).fn p := by
    intro k₁ k₂ p h₁ h₂
    obtain ⟨k, hk, hl₁, hl₂⟩ := hK.2 0 k₁ k₂ p h₁ (by rw [F.shift_zero]; exact h₂)
    have e₁ := Charts.fn_sh hl₁ (f k₁) hk
    have e₂ := Charts.fn_sh hl₂ (f k₂) hk
    rw [hf k₁ k hl₁, F.shift_zero] at e₁
    rw [hf k₂ k hl₂, F.shift_zero] at e₂
    rw [← e₁, ← e₂]
  let G : Tot I g → ℂ := fun p ↦ if h : ∃ k, p ∈ K.W k then (f h.choose).fn p else 0
  have hG : ∀ k, ∀ p ∈ K.W k, (f k).fn p = G p := by
    intro k p hp
    have h : ∃ k, p ∈ K.W k := ⟨k, hp⟩
    simp only [G, dif_pos h]
    exact indep _ _ _ hp h.choose_spec
  have hGev : ∀ k, ∀ p ∈ K.W k, G =ᶠ[𝓝 p] (f k).fn := fun k p hp ↦ by
    filter_upwards [(K.W k).isOpen.mem_nhds hp] with q hq using (hG k q hq).symm
  refine ⟨G, ?_, hG, ?_, ?_⟩
  · intro p hp
    obtain ⟨k, hk⟩ := hK.1 p hp
    exact ((f k).analytic p hk).congr (hGev k p hk).symm
  · intro l q hq p hp
    obtain ⟨k₁, h₁⟩ := hK.1 p hp
    obtain ⟨k₂, h₂⟩ := hK.1 (F.shift l p) hp
    obtain ⟨k, hk, -, hl⟩ := hK.2 l k₁ k₂ p h₁ h₂
    have e := congrArg (fun u ↦ Hol.fn u p) (hq k₂ k hl)
    rw [Charts.fn_sh hl _ hk, Hol.fn_add _ _ hk, Charts.fn_cst K k q hk] at e
    rw [← hG k₂ _ h₂, ← hG k p hk, e]
  · intro h0 z hz w
    have hder : ∀ w' : Fin g → ℂ, HasFDerivAt (fun u ↦ G (z, u)) (0 : (Fin g → ℂ) →L[ℂ] ℂ) w' := by
      intro w'
      obtain ⟨k, hk⟩ := hK.1 (z, w') hz
      have hfd : HasFDerivAt (fun u : Fin g → ℂ ↦ ((z, u) : Tot I g))
          (ContinuousLinearMap.inr ℂ (I → ℂ) (Fin g → ℂ)) w' :=
        (hasFDerivAt_const z w').prodMk (hasFDerivAt_id w')
      have hGd : HasFDerivAt G (fderiv ℂ (f k).fn (z, w')) (z, w') := by
        rw [← (hGev k _ hk).fderiv_eq]
        exact (((f k).analytic _ hk).differentiableAt.congr_of_eventuallyEq (hGev k _ hk)).hasFDerivAt
      have hL : (fderiv ℂ (f k).fn (z, w')).comp (ContinuousLinearMap.inr ℂ (I → ℂ) (Fin g → ℂ)) = 0 := by
        have hs : ∀ a : Fin g, fderiv ℂ (f k).fn (z, w') ((0, Pi.single a 1) : Tot I g) = 0 := by
          intro a
          have := Hol.fn_der ((0, Pi.single a 1) : Tot I g) (f k) hk
          rw [show Hol.der _ (f k) = dw a (f k) from rfl, h0 k a, ← Hol.ev_apply _ hk, map_zero] at this
          exact this.symm
        refine ContinuousLinearMap.ext fun v ↦ ?_
        rw [← Finset.univ_sum_single v, map_sum, ContinuousLinearMap.zero_apply]
        refine Finset.sum_eq_zero fun a _ ↦ ?_
        have e : Pi.single a (v a) = v a • (Pi.single a 1 : Fin g → ℂ) := by
          rw [← Pi.single_smul]; simp
        rw [e, map_smul, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, hs a, smul_zero]
      have := hGd.comp w' hfd
      rw [hL] at this
      exact this
    exact is_const_of_fderiv_eq_zero (fun w' ↦ (hder w').differentiableAt) (fun w' ↦ (hder w').fderiv) w 0

end GlobalTheory.AnPer.Charts
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveOfSurjectiveProjectiveConstRankStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.injective_of_surjective_projective_constRank : ∀ (B M : Type) [CommRing B] [AddCommGroup M] [Module B M] (g : ℕ) (f : M →ₗ[B] (Fin g → B)), Module.Finite B M → Module.Projective B M → (∀ p : PrimeSpectrum B, Module.rankAtStalk M p = g) → Function.Surjective f → Function.Injective f := by
  first | exact @GlobalTheory.CechPer.injective_of_surjective_of_rankAtStalk_eq | exact GlobalTheory.CechPer.injective_of_surjective_of_rankAtStalk_eq | (intros; apply GlobalTheory.CechPer.injective_of_surjective_of_rankAtStalk_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralStrictHenselianAcyclicFinitary
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.IntAcyc

variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B]

def finDiag : Finset B ⥤ CommRingCat.{0} where
  obj t := CommRingCat.of (Algebra.adjoin A (t : Set B))
  map {t u} h := CommRingCat.ofHom
    (Subalgebra.inclusion (Algebra.adjoin_mono (Finset.coe_subset.2 h.le))).toRingHom
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

def finCocone : Cocone (finDiag A B) where
  pt := CommRingCat.of B
  ι := { app := fun t => CommRingCat.ofHom (Algebra.adjoin A (t : Set B)).val.toRingHom
         naturality := fun _ _ _ => by ext; rfl }

def finCoconeIsColimit : IsColimit (finCocone A B) := by
  classical
  haveI : ReflectsColimitsOfShape (Finset B) (forget CommRingCat.{0}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine isColimitOfReflects (forget CommRingCat.{0})
    (Types.FilteredColimit.isColimitOf _ ((forget CommRingCat.{0}).mapCocone (finCocone A B)) ?_ ?_)
  · intro x
    exact ⟨{x}, ⟨x, Algebra.subset_adjoin (Finset.mem_coe.2 (Finset.mem_singleton_self x))⟩, rfl⟩
  · intro i j xi xj h
    refine ⟨i ⊔ j, homOfLE le_sup_left, homOfLE le_sup_right, ?_⟩
    apply Subtype.ext
    exact h

theorem finite_finDiag [Algebra.IsIntegral A B] (t : Finset B) :
    Module.Finite A (Algebra.adjoin A (t : Set B)) :=
  Algebra.finite_adjoin_of_finite_of_isIntegral t.finite_toSet
    (fun x _ => Algebra.IsIntegral.isIntegral x)

end GlobalTheory.EtC.IntAcyc
end

namespace GlobalTheory.EtC.IntAcyc

theorem acycF_of_isIntegral : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F →
    ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Algebra.IsIntegral A B],
      SH A → AcycF R (sp B) F := by
  classical
  intro R _ F hF A B _ _ _ _ hA
  obtain ⟨hHens, hSep⟩ := hA
  intro n hn
  suffices h : ∀ x : H R (sp B) F n, x = 0 from ⟨fun x y => by rw [h x, h y]⟩
  intro x
  obtain ⟨j, y, hy⟩ := (GlobalTheory.T.etaleCohomology_filteredColimit_rings_finitary R F hF (Finset B) (finDiag A B) (finCocone A B)
    (finCoconeIsColimit A B) n).1 x
  haveI := finite_finDiag A B j
  obtain ⟨ι, hι, T, hT, hAl, e, hH, hS⟩ :=
    GlobalTheory.finite_algebra_strictly_henselian_pi A (Algebra.adjoin A (j : Set B))
  have hac : AcycF R (sp ((finDiag A B).obj j)) F :=
    GlobalTheory.T.acycF_of_pi_sh' R F ι T ((finDiag A B).obj j) ⟨e.toRingEquiv⟩ (fun i => ⟨hH i, (hS i).1⟩)
  haveI := hac n hn
  have hy0 : y = 0 := Subsingleton.elim _ _
  rw [← hy, hy0]
  exact map_zero _

end GlobalTheory.EtC.IntAcyc
end

