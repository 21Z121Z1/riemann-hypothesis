import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2168
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1582
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0619
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2598
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2390
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0010
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0084
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2554
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2643
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2990
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2995
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3012
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfIsGenerated
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1111
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2733
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2751
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2970
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2905
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeadWeightLineNef
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi)
open GlobalTheory.HSApp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NefHodge

def chartwise {X C : Scheme.{0}} (A : LB X) (g : C ⟶ X) : LB C :=
  ⟨A.ι, fun k => g ⁻¹ᵁ A.U k, fun k k' => pullU g (A.U k ⊓ A.U k') (A.g k k')⟩

theorem isLB_chartwise {X C : Scheme.{0}} {A : LB X} (hA : A.IsLB) (g : C ⟶ X) :
    (chartwise A g).IsLB ∧ LBIso (chartwise A g) (A.pull g) := by
  let a : ChartPull (chartwise A g) (A.pull g) (𝟙 C) :=
    ⟨fun k _ => k, fun k y hy => mem_pull.2 hy, fun y k k' hk hk' =>
      (gm_pull (𝟙 C) g y (A.U k ⊓ A.U k') ⟨hk, hk'⟩ _).trans
        (gm_pull_g A g (𝟙 C) y (fun _ => k) (fun _ => k') (mem_pull.2 hk) (mem_pull.2 hk')).symm⟩
  refine ⟨NefFibre.isLB_of_chartPull a (LB.isLB_pull hA g) fun y => ?_, iso_of_chart (LB.isLB_pull hA g) a⟩
  exact (Opens.mem_iSup (s := A.U)).1 (hA.cover.ge (Set.mem_univ (g y)))

open GlobalTheory.VB GlobalTheory.DualPull in

theorem isIso_theta_of_frames {X C : Scheme.{0}} {F : X.Modules} (g : C ⟶ X)
    (h : ∀ x : X, ∃ (U : X.Opens) (n : ℕ) (e : Fin n → Γ(F, U)), x ∈ U ∧ IsFrame e) : IsIso (theta g F) := by
  have := OmegaGlobal.isQuasicoherent_of_frames h
  have : (VB.dual F).IsQuasicoherent := OmegaGlobal.isQuasicoherent_of_frames fun x =>
    have ⟨U, n, _, hx, he⟩ := h x
    ⟨U, n, _, hx, he.dual⟩
  choose U n e hx he using h
  refine Twist.isIso_of_cover _ (U := fun y => g ⁻¹ᵁ U (g y))
    (top_le_iff.1 fun y _ => Opens.mem_iSup.2 ⟨y, hx (g y)⟩) fun y W hW => ?_
  have H (i : Fin (n (g y))) : (theta g F).app _ (QCoh.pullbackSections g (VB.dual F) (le_refl (g ⁻¹ᵁ U (g y)))
      ((he (g y)).coord i)) = ((he (g y)).pullback g).coord i :=
    dual_pull_ext g le_rfl fun W hW S hS e' s => by
      rw [dualApp_theta g _ hW, IsFrame.dualApp_coord, IsFrame.dualApp_coord]
      exact ((he (g y)).pullback_basis_repr g hW e' s i).symm
  have : QCoh.appLinear (theta g F) W =
      (((he (g y)).dual.pullback g).equiv ((he (g y)).pullback g).dual hW).toLinearMap :=
    (((he (g y)).dual.pullback g).basis hW).ext fun i => by
      rw [IsFrame.basis_apply, LinearEquiv.coe_coe, IsFrame.equiv_resM_frame, ← H]
      exact Twist.app_resM (theta g F) hW _
  rw [← QCoh.coe_appLinear, this]
  exact LinearEquiv.bijective _

section Step

open GlobalTheory.FlagMod GlobalTheory.Reg GlobalTheory.VB GlobalTheory.LieVB
open GlobalTheory.Twist (resM)
open GlobalTheory.QCoh (pullbackSections)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {Z C : Scheme.{0}} {π : Z ⟶ Y.X} (F : Frames Y π) (g : C ⟶ Z) (σ : E →+* ℂ)
  (f : ∀ M : MChart Y, Fin M.n → Γ(Lie Y.t.G, M.U))

theorem le_chart {k : F.J} {V : C.Opens} (h : V ≤ g ⁻¹ᵁ F.U k) : V ≤ (g ≫ π) ⁻¹ᵁ (F.M k).U :=
  fun _ hx => F.le k (h hx)

def vecSec (k : F.J) (V : C.Opens) (h : V ≤ g ⁻¹ᵁ F.U k) (i : Fin (Dw.mult σ)) :
    Γ((Scheme.Modules.pullback (g ≫ π)).obj (Lie Y.t.G), V) :=
  ∑ a, g.appLE (F.U k) V h (F.u k σ a i) • pullbackSections (g ≫ π) _ (le_chart F g h) (f (F.M k).toMChart a)

theorem resM_vecSec (k : F.J) {V V' : C.Opens} (h : V ≤ g ⁻¹ᵁ F.U k) (h' : V' ≤ V) (i : Fin (Dw.mult σ)) :
    resM _ h' (vecSec F g σ f k V h i) = vecSec F g σ f k V' (h'.trans h) i := by
  rw [vecSec, vecSec, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Twist.resM_smul, DualPull.resG_appLE]
  exact congrArg _ (QCoh.res_pullbackSections _ _ _ _ _)

theorem linearIndependent_vecSec (hf : ∀ M, IsFrame (f M)) (k : F.J) {V : C.Opens} (h : V ≤ g ⁻¹ᵁ F.U k) :
    LinearIndependent Γ(C, V) (vecSec F g σ f k V h) := by
  have := Y.t.semi
  have := Y.t.semi.smooth
  have : (Lie Y.t.G).IsQuasicoherent := OmegaGlobal.isQuasicoherent_of_frames fun x =>
    have ⟨U, n, _, hx, he⟩ := exists_isFrame_omega Y.t.G x
    ⟨U, n, _, hx, he.dual⟩
  let b := ((hf (F.M k).toMChart).pullback (g ≫ π)).basis (le_chart F g h)
  have hb : ∀ a, b a = pullbackSections (g ≫ π) _ (le_chart F g h) (f (F.M k).toMChart a) := fun a =>
    (IsFrame.basis_apply _ _ a).trans (QCoh.res_pullbackSections _ _ _ _ _)
  obtain ⟨w, hw⟩ := F.split k σ
  rw [Fintype.linearIndependent_iff]
  intro a ha
  simp only [vecSec, ← hb, Finset.smul_sum, smul_smul] at ha
  rw [Finset.sum_comm] at ha
  simp only [← Finset.sum_smul] at ha
  have h₁ : ((F.u k σ).map (g.appLE (F.U k) V h).hom).mulVec a = 0 := funext fun j =>
    show ∑ i, g.appLE (F.U k) V h (F.u k σ j i) * a i = 0 from
    Eq.trans (Finset.sum_congr rfl fun i _ => _root_.mul_comm _ _)
      (Fintype.linearIndependent_iff.1 b.linearIndependent _ ha j)
  have h₂ := congrArg (w.map (g.appLE (F.U k) V h).hom).mulVec h₁
  rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hw, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec,
    Matrix.mulVec_zero] at h₂
  exact congrFun h₂

theorem vecSec_chg (hc : ∀ (M M' : MChart Y) (j : Fin M'.n), resM _ (inf_le_right : M.U ⊓ M'.U ≤ M'.U) (f M' j) =
      ∑ i, chg M M' i j • resM _ (inf_le_left : M.U ⊓ M'.U ≤ M.U) (f M i))
    (k k' : F.J) {V : C.Opens} (h : V ≤ g ⁻¹ᵁ F.U k) (h' : V ≤ g ⁻¹ᵁ F.U k') (hh : V ≤ g ⁻¹ᵁ (F.U k ⊓ F.U k'))
    (i : Fin (Dw.mult σ)) : vecSec F g σ f k' V h' i =
      ∑ j, g.appLE _ V hh (F.B k k' σ j i) • vecSec F g σ f k V h j := by
  have hM : V ≤ (g ≫ π) ⁻¹ᵁ ((F.M k).U ⊓ (F.M k').U) := fun _ hx => ⟨le_chart F g h hx, le_chart F g h' hx⟩
  have e₁ : ∀ a, pullbackSections (g ≫ π) _ (le_chart F g h') (f (F.M k').toMChart a) =
      ∑ b, (g ≫ π).appLE _ V hM (chg (F.M k).toMChart (F.M k').toMChart b a) •
        pullbackSections (g ≫ π) _ (le_chart F g h) (f (F.M k).toMChart b) := fun a => by
    have := congrArg (pullbackSections (g ≫ π) _ hM) (hc (F.M k).toMChart (F.M k').toMChart a)
    rw [map_sum] at this
    refine ((QCoh.pullbackSections_res _ _ _ _ _).symm.trans this).trans (Finset.sum_congr rfl fun b _ => ?_)
    rw [QCoh.pullbackSections_smul]
    exact congrArg _ (QCoh.pullbackSections_res _ _ _ _ _)
  have e₂ : ∀ b, ∑ a, g.appLE _ V h' (F.u k' σ a i) *
      (g ≫ π).appLE _ V hM (chg (F.M k).toMChart (F.M k').toMChart b a) =
      ∑ j, g.appLE _ V hh (F.B k k' σ j i) * g.appLE _ V h (F.u k σ b j) := fun b => by
    have e₀ : ∑ a, π.appLE ((F.M k).U ⊓ (F.M k').U) (F.U k ⊓ F.U k') (inf_le_inf (F.le k) (F.le k'))
        (chg (F.M k).toMChart (F.M k').toMChart b a) * resG Z inf_le_right (F.u k' σ a i) =
        ∑ j, resG Z inf_le_left (F.u k σ b j) * F.B k k' σ j i :=
      congrFun (congrFun (F.tri k k' σ).choose_spec.2 b) i
    have := congrArg (g.appLE _ V hh).hom e₀
    rw [map_sum, map_sum] at this
    refine (Finset.sum_congr rfl fun a _ => ?_).trans (this.trans (Finset.sum_congr rfl fun j _ => ?_))
    · rw [_root_.mul_comm, map_mul, ← Scheme.Hom.appLE_comp_appLE g π _ _ V (inf_le_inf (F.le k) (F.le k')) hh]
      exact congrArg₂ (· * ·) rfl (DualPull.appLE_resG g _ hh _).symm
    · rw [map_mul, _root_.mul_comm]
      exact congrArg₂ (· * ·) rfl (DualPull.appLE_resG g _ hh _)
  simp only [vecSec, e₁, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm, Finset.sum_comm (s := (Finset.univ : Finset (Fin (Dw.mult σ))))]
  simp only [← Finset.sum_smul, e₂]

open Classical in

theorem val_dual_LL_stepEx {j : ℕ} (hj : j ≤ Dw.mult σ) (k k' : F.J) :
    ((CechPic.dual (F.LL (NefStep.stepEx σ j))).g k k').val =
      ((F.B k k' σ).submatrix (Fin.castLE hj) (Fin.castLE hj)).det := by
  have ht : ((F.B k k' σ).submatrix (Fin.castLE hj) (Fin.castLE hj)).BlockTriangular id := fun a b h =>
    F.B_tri k k' σ (show Fin.castLE hj b < Fin.castLE hj a from h)
  rw [Matrix.det_of_upperTriangular ht]
  change ((∏ ix, F.T k k' ix ^ (-NefStep.stepEx σ j ix))⁻¹).val = _
  have e : (∏ ix, F.T k k' ix ^ (-NefStep.stepEx σ j ix))⁻¹ = ∏ i : Fin j, F.T k k' (some ⟨σ, Fin.castLE hj i⟩) := by
    rw [← Finset.prod_inv_distrib]
    refine (Finset.prod_of_injOn (fun i : Fin j => (some ⟨σ, Fin.castLE hj i⟩ : Ix Dw)) (fun a _ b _ h => ?_)
      (fun _ _ => Finset.mem_univ _) (fun ix _ h => ?_) fun i _ => ?_).symm
    · exact Fin.castLE_injective hj (eq_of_heq (Sigma.mk.inj (Option.some.inj h)).2)
    · have : NefStep.stepEx σ j ix = 0 := by
        rcases ix with _ | ⟨σ', i⟩
        · rfl
        · refine if_neg ?_
          rintro ⟨rfl, hi⟩
          exact h ⟨⟨i, hi⟩, Finset.mem_coe.2 (Finset.mem_univ _), rfl⟩
      rw [this, neg_zero, zpow_zero, inv_one]
    · have : NefStep.stepEx σ j (some ⟨σ, Fin.castLE hj i⟩ : Ix Dw) = 1 := if_pos ⟨rfl, i.2⟩
      rw [this, zpow_neg_one, inv_inv]
  rw [e, Units.coe_prod]
  rfl

theorem exists_step {j : ℕ} (hj : j ≤ Dw.mult σ) :
    ∃ (W : C.Modules) (ι : W ⟶ (Scheme.Modules.pullback (g ≫ π)).obj (Lie Y.t.G)), Mono ι ∧ IsVB W j ∧
      LBIso (chartwise (CechPic.dual (F.LL (NefStep.stepEx σ j))) g) (det W j) := by
  obtain ⟨f, hf, hc⟩ := GlobalTheory.T.exists_lieBundle_frames_charts_change_basis E H Dw l Xo c O β Y
  refine GlobalTheory.T.exists_locallyFree_subsheaf_det_iso C _ j _ (isLB_chartwise (isLB_dual (F.isLB_LL _)) g).1
    (fun k i => vecSec F g σ f k (g ⁻¹ᵁ F.U k) le_rfl (Fin.castLE hj i))
    (fun k k' => ((F.B k k' σ).submatrix (Fin.castLE hj) (Fin.castLE hj)).map (g.app (F.U k ⊓ F.U k')).hom)
    (fun k V h => ?_) (fun k k' i => ?_) fun k k' => ?_
  · have := (linearIndependent_vecSec F g σ f hf k h).comp _ (Fin.castLE_injective hj)
    exact (funext fun i => resM_vecSec F g σ f k le_rfl h (Fin.castLE hj i)) ▸ this
  · refine (resM_vecSec F g σ f k' le_rfl _ _).trans ((vecSec_chg F g σ f hc k k'
      (V := g ⁻¹ᵁ F.U k ⊓ g ⁻¹ᵁ F.U k') inf_le_left inf_le_right le_rfl _).trans ?_)
    refine (Finset.sum_of_injOn (Fin.castLE hj) (Fin.castLE_injective hj).injOn (fun _ _ => Finset.mem_univ _)
      (fun a _ h => ?_) fun a _ => ?_).symm
    · have : F.B k k' σ a (Fin.castLE hj i) = 0 := F.B_tri k k' σ (by
        by_contra h'
        exact h ⟨⟨a, lt_of_le_of_lt (not_lt.1 h') i.2⟩, Finset.mem_coe.2 (Finset.mem_univ _), rfl⟩)
      rw [this, map_zero, zero_smul]
    · exact congrArg₂ (· • ·) congr($(g.appLE_eq_app (U := F.U k ⊓ F.U k')) _).symm
        (resM_vecSec F g σ f k le_rfl _ _)
  · exact (congrArg (g.app (F.U k ⊓ F.U k')).hom (val_dual_LL_stepEx F σ hj k k')).trans (RingHom.map_det _ _)

open scoped CategoryTheory.Obj in

theorem curveTest_stepEx (hS : Published.SemiAbelianLieSeminegative) (K : Type) [Field K] [CharZero K] {j : ℕ}
    (hj : j ≤ Dw.mult σ) : NefCurveTest.CurveTest K (F.LL (NefStep.stepEx σ j)) := by
  intro C _ hs hp hc g
  obtain ⟨W, ι, _, hW, e⟩ := exists_step F g σ hj
  have := Y.t.semi
  have := Y.t.semi.smooth
  have := IsSemiAbelian.pullback (g ≫ π) Y.t.G Y.t.semi
  have hG := isGrpPullback_pullback Y.t.G (g ≫ π)
  have := isIso_theta_of_frames (g ≫ π) (exists_isFrame_omega Y.t.G)
  have : IsIso (lieBase hG) :=
    inferInstanceAs (IsIso (DualPull.theta _ (omega Y.t.G) ≫ (dualIso (asIso (omegaBase hG)).symm).hom))
  have hL := F.isLB_LL (NefStep.stepEx σ j)
  have h₁ := isLB_chartwise (isLB_dual hL) g
  refine (hS.dual_det_nonneg hs hp hc _ hW (ι ≫ lieBase hG)).trans_eq (interNum_congr_cls K _
    (isLB_vecOne (isLB_dual hW.isLB_det)) (isLB_vecOne (LB.isLB_pull hL g)) fun i => ?_)
  fin_cases i
  change cls (CechPic.dual (det W j)) (isLB_dual hW.isLB_det) =
    cls ((F.LL (NefStep.stepEx σ j)).pull g) (LB.isLB_pull hL g)
  rw [cls_dual hW.isLB_det, ← (cls_eq_iff h₁.1 hW.isLB_det).2 e,
    (cls_eq_iff h₁.1 (LB.isLB_pull (isLB_dual hL) g)).2 h₁.2, cls_pull (isLB_dual hL), cls_dual hL, map_neg, neg_neg,
    cls_pull hL]

end Step

theorem isNef_stepEx (hS : Published.SemiAbelianLieSeminegative) (hN : Published.NefProductNonneg) {E : Type} [Field E]
    [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
    {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagMod.FlagCover Y) (Z : Comp Xo c) (σ : E →+* ℂ) {j : ℕ}
    (hj : j ≤ Dw.mult σ) : letI := algebraΓOfHom (str₀ X Z); IsNef c.F (LL₀ X Z (NefStep.stepEx σ j)) :=
  letI := algebraΓOfHom (str₀ X Z)
  ((curveTest_stepEx X.F σ hS _ hj).pull (X.F.isLB_LL _) _).isNef hN (LB.isLB_pull (X.F.isLB_LL _) _)

theorem isNef_headWt : GlobalTheory.Published.SemiAbelianLieSeminegative → GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.NefNumerics → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → ∀ (τ : Psi H) (k : ℕ), k < Dw.p → letI := algebraΓOfHom (str₀ TF.X Z); IsNef c.F (L₀ TF.X Z (GlobalTheory.NefWt.headWt τ k)) := by
  intro hS _ hN E _ _ _ H Dw l Xo c TF Z _ τ k hk
  rw [NefStep.L₀_headWt TF.X Z τ k hk]
  exact isNef_stepEx hS hN.1 TF.X Z τ.1 (by rw [FlagMod.mult_of_mem τ]; exact hk)

end GlobalTheory.NefHodge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealVanishingIdealClosure
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SncForm

theorem ideal_vanishingIdeal_closure {X : Scheme.{0}} (U : X.affineOpens) {η : X} (hη : η ∈ U.1) :
    (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {η})).ideal U =
      (U.2.primeIdealOf ⟨η, hη⟩).asIdeal := by
  have hU : IsAffineOpen U.1 := U.2
  have emb := hU.fromSpec.isOpenEmbedding
  have h1 : hU.fromSpec (hU.primeIdealOf ⟨η, hη⟩) = η := hU.fromSpec_primeIdealOf ⟨η, hη⟩
  have h2 : hU.fromSpec ⁻¹' ({η} : Set X) = {hU.primeIdealOf ⟨η, hη⟩} := by
    ext Q
    exact ⟨fun h => emb.injective (h.trans h1.symm), fun h => (congrArg _ h).trans h1⟩
  rw [Scheme.IdealSheafData.vanishingIdeal_ideal]
  change PrimeSpectrum.vanishingIdeal (hU.fromSpec ⁻¹' closure ({η} : Set X)) = _
  have h3 := (emb.isOpenMap.preimage_closure_eq_closure_preimage emb.continuous {η}).trans
    (congrArg closure h2)
  exact (congrArg PrimeSpectrum.vanishingIdeal h3).trans
    ((PrimeSpectrum.vanishingIdeal_closure _).trans (PrimeSpectrum.vanishingIdeal_singleton _))

theorem exists_isLocalization_stalk {X : Scheme.{0}} (U : X.affineOpens) {y η : X} (hy : y ∈ U.1)
    (hη : η ∈ U.1) (hηy : η ⤳ y) (p : Ideal (X.presheaf.stalk y)) [p.IsPrime]
    (hp : FinalTheorems.stalkId (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {η})) y = p) :
    ∃ _ : Algebra (X.presheaf.stalk y) (X.presheaf.stalk η),
      IsLocalization.AtPrime (X.presheaf.stalk η) p ∧ ∀ a : Γ(X, U.1),
        X.presheaf.germ U.1 η hη a =
          algebraMap (X.presheaf.stalk y) (X.presheaf.stalk η) (X.presheaf.germ U.1 y hy a) := by
  have hU : IsAffineOpen U.1 := U.2
  let yU : U.1 := ⟨y, hy⟩
  let algY : Algebra Γ(X, U.1) (X.presheaf.stalk y) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf yU
  have hlocY : IsLocalization.AtPrime (X.presheaf.stalk y) (hU.primeIdealOf yU).asIdeal :=
    hU.isLocalization_stalk yU
  set Py := hU.primeIdealOf yU with hPy
  let Pη := hU.primeIdealOf ⟨η, hη⟩
  have hfromη : hU.fromSpec Pη = η := hU.fromSpec_primeIdealOf ⟨η, hη⟩
  have hfromy : hU.fromSpec Py = y := hU.fromSpec_primeIdealOf yU
  have emb := hU.fromSpec.isOpenEmbedding
  have hspec : ∀ P Q : PrimeSpectrum Γ(X, U.1), hU.fromSpec P ⤳ hU.fromSpec Q ↔ P ≤ Q := by
    intro P Q
    rw [PrimeSpectrum.le_iff_specializes]
    exact emb.isInducing.specializes_iff
  have hle : Pη ≤ Py := (hspec _ _).mp (by rw [hfromη, hfromy]; exact hηy)
  have hdisj : Disjoint (Py.asIdeal.primeCompl : Set Γ(X, U.1)) Pη.asIdeal :=
    Set.disjoint_left.mpr fun x hx hx' => hx ((show Pη.asIdeal ≤ Py.asIdeal from hle) hx')
  rw [WMult.stalkId_eq_map_germ _ y U hy, ideal_vanishingIdeal_closure U hη] at hp
  have hPeq : Pη.asIdeal = p.comap (algebraMap Γ(X, U.1) (X.presheaf.stalk y)) := by
    rw [← hp]
    exact (IsLocalization.under_map_of_isPrime_disjoint Py.asIdeal.primeCompl
      (X.presheaf.stalk y) Pη.isPrime hdisj).symm
  let T := Localization.AtPrime p
  have hT : IsLocalization.AtPrime T (p.comap (algebraMap Γ(X, U.1) (X.presheaf.stalk y))) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (M := Py.asIdeal.primeCompl) (S := X.presheaf.stalk y) (T := T) p
  have hT' : IsLocalization Pη.asIdeal.primeCompl T := by
    have hsm : Pη.asIdeal.primeCompl =
        (Ideal.comap (algebraMap Γ(X, U.1) (X.presheaf.stalk y)) p).primeCompl := by
      ext x; rw [Ideal.mem_primeCompl_iff, Ideal.mem_primeCompl_iff, hPeq]
    rw [hsm]; exact hT
  let ηU : U.1 := ⟨η, hη⟩
  let algη : Algebra Γ(X, U.1) (X.presheaf.stalk η) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ηU
  have hlocη : IsLocalization.AtPrime (X.presheaf.stalk η) Pη.asIdeal :=
    hU.isLocalization_stalk ηU
  let φ : X.presheaf.stalk η ≃ₐ[Γ(X, U.1)] T := IsLocalization.algEquiv Pη.asIdeal.primeCompl _ _
  let algYη : Algebra (X.presheaf.stalk y) (X.presheaf.stalk η) :=
    (φ.symm.toRingEquiv.toRingHom.comp (algebraMap (X.presheaf.stalk y) T)).toAlgebra
  refine ⟨algYη, (IsLocalization.isLocalization_iff_of_ringEquiv (M := p.primeCompl)
      (S := T) φ.symm.toRingEquiv).mp inferInstance, fun a => ?_⟩
  have h1 := (φ.symm.commutes a).symm
  rw [IsScalarTower.algebraMap_apply Γ(X, U.1) (X.presheaf.stalk y) T] at h1
  exact h1

theorem germ_eq_unit_mul_monomial : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (B : LB X) (hB : B.IsLB) (s : B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (r : ℕ) (z : Fin r → X), Function.Injective z → (∀ a, Order.coheight (z a) = 1) → ((nonzeroLocus s : Set X)ᶜ = ⋃ a, closure {z a}) → ∀ x : X, FinalTheorems.LSncAt X (fun a => (Closeds.closure {z a})) x → ∀ (i : B.ι) (hi : x ∈ B.U i), ∃ (n : ℕ) (g : Fin n → X.presheaf.stalk x) (e : {a : Fin r // x ∈ (Closeds.closure {z a})} ↪ Fin n) (u : (X.presheaf.stalk x)ˣ) (_ : Fintype {a : Fin r // x ∈ (Closeds.closure {z a})}), FinalTheorems.Rsp (X.presheaf.stalk x) n g ∧ (∀ a, FinalTheorems.stalkId (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {z a.1})) x = Ideal.span {g (e a)}) ∧ X.presheaf.germ _ x hi (s.f i) = u * ∏ a, g (e a) ^ ((divOfSec hB s hs).mult (z a.1)).toNat := by
  classical
  intro X _ _ B hB s hs r z _ hz hZ x hx i hi
  obtain ⟨hreg, n, g, e, hg, hI⟩ := hx
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVi⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hi (B.U i).isOpen
  let U : X.affineOpens := ⟨V, hV⟩
  have hVi' : V ≤ B.U i := hVi
  let t : Γ(X, V) := X.presheaf.map (homOfLE hVi').op (s.f i)
  have ht : ∀ (w : X) (hw : w ∈ V), X.presheaf.germ V w hw t =
      X.presheaf.germ _ w (hVi' hw) (s.f i) := fun w hw =>
    X.presheaf.germ_res_apply (homOfLE hVi') w hw _
  set γ := X.presheaf.germ _ x hi (s.f i) with hγ
  have hγ0 : γ ≠ 0 := fun h0 => fnOf_sec_ne_zero hs (gen_mem hi)
    ((algebraMap_germ hi (s.f i)).symm.trans ((congrArg _ h0).trans (map_zero _)))
  let J : Finset (Fin n) := Finset.univ.map e
  have hrad : (∏ j ∈ J, g j) ∈ (Ideal.span {γ}).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro Q ⟨hQγ, hQ⟩
    let P : PrimeSpectrum Γ(X, V) := ⟨Q.comap (X.presheaf.germ V x hxV).hom, inferInstance⟩
    have htP : t ∈ P.asIdeal := by
      change X.presheaf.germ V x hxV t ∈ Q
      rw [ht]
      exact hQγ (Ideal.mem_span_singleton_self _)
    have hmem : hV.fromSpec P ∈ V := by
      have : hV.fromSpec P ∈ Set.range hV.fromSpec := ⟨P, rfl⟩
      rwa [hV.range_fromSpec] at this
    have hnz : hV.fromSpec P ∉ nonzeroLocus s := by
      rw [mem_nonzeroLocus_iff s i (hVi' hmem)]
      intro h
      have h' : hV.fromSpec P ∈ X.basicOpen t := by
        rw [Scheme.mem_basicOpen _ _ _ hmem, ht]
        exact (Scheme.mem_basicOpen _ _ _ _).1 h
      have h'' : P ∈ hV.fromSpec ⁻¹ᵁ X.basicOpen t := h'
      rw [hV.fromSpec_preimage_basicOpen] at h''
      exact h'' htP
    have hc : hV.fromSpec P ∈ ((nonzeroLocus s : Set X)ᶜ) := hnz
    rw [hZ] at hc
    obtain ⟨a, ha⟩ := Set.mem_iUnion.1 hc
    have hPx : hV.fromSpec P ⤳ x := by
      have h1 : hV.fromSpec (hV.primeIdealOf ⟨x, hxV⟩) = x := hV.fromSpec_primeIdealOf ⟨x, hxV⟩
      have h2 : P ≤ hV.primeIdealOf ⟨x, hxV⟩ := by
        rw [hV.primeIdealOf_eq_map_closedPoint]
        exact Ideal.comap_mono (IsLocalRing.le_maximalIdeal hQ.ne_top)
      have h3 := ((PrimeSpectrum.le_iff_specializes _ _).1 h2).map hV.fromSpec.continuous
      rwa [h1] at h3
    have hxa : x ∈ Closeds.closure {z a} := hPx.mem_closed isClosed_closure ha
    have hsup : hV.fromSpec P ∈
        ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {z a})).support : Set X) := by
      rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
      exact ha
    rw [WMult.mem_support_fromSpec_iff _ U hV] at hsup
    have h3 : Ideal.span {g (e ⟨a, hxa⟩)} ≤ Q := by
      rw [← hI ⟨a, hxa⟩, WMult.stalkId_eq_map_germ _ x U hxV]
      exact Ideal.map_le_iff_le_comap.mpr hsup
    exact Q.mem_of_dvd (Finset.dvd_prod_of_mem _ (Finset.mem_map_of_mem e (Finset.mem_univ _)))
      (h3 (Ideal.mem_span_singleton_self _))
  obtain ⟨u, m, -, hγu⟩ := eq_unit_mul_monomial g hg.1 hg.2 J hγ0 hrad
  refine ⟨n, g, e, u, inferInstance, hg, hI, ?_⟩
  have hord : ∀ a, ((divOfSec hB s hs).mult (z a.1)).toNat = m (e a) := by
    intro a
    have hsp : z a.1 ⤳ x := specializes_iff_mem_closure.2 a.2
    have hzV : z a.1 ∈ V := hsp.mem_open V.isOpen hxV
    have hpr : Prime (g (e a)) := prime_of_regular_params g hg.1 hg.2 _
    have hP : (Ideal.span {g (e a)}).IsPrime := (Ideal.span_singleton_prime hpr.ne_zero).mpr hpr
    obtain ⟨alg, hloc, hgerm⟩ := exists_isLocalization_stalk U hxV hzV hsp _ (hI a)
    have h := WMult.ord_isLocalization_eq_exponent g hg.1 hg.2 J u m (e a)
      (Finset.mem_map_of_mem e (Finset.mem_univ _)) (X.presheaf.stalk (z a.1))
    rw [← hγu, hγ, ← ht x hxV, ← hgerm t, ht] at h
    rw [mult_divOfSec (hz _) (hVi' hzV), Int.toNat_natCast]
    exact (congrArg ENat.toNat h).trans (ENat.toNat_natCast _)
  rw [hγu, Finset.prod_map]
  exact congrArg _ (Finset.prod_congr rfl fun a _ => by rw [hord])

end GlobalTheory.SncForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorPeriodsAtGeneratingPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.FactorPeriod

set_option maxHeartbeats 800000 in

theorem factor_period : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (θ : R →+* V) (Q : Data R) (D₀ : DegPre R) (F : PFactor Q D₀) (W : (Sp R).Opens) (ψW : PsiOn D₀ W) (g : (TK V).left ⟶ W.toScheme), g ≫ W.ι = jK V ≫ spMap θ → ∀ (a b : Q.X) (u : LB.Gen (LB.LinComb Q.M.L (lamPts (Q.c a) (Q.c b)) negε)) (x y : R) (k : (FractionRing R)ˣ) (k' : (FractionRing V)ˣ), u.IsGen → θ y ≠ 0 → (k : FractionRing R) * algebraMap R _ y = algebraMap R _ x → (k' : FractionRing V) * algebraMap V _ (θ y) = algebraMap V _ (θ x) → (∀ z J, Good Q.M.L z J → val (Q.tau a b) (𝟙 _) z J = gm (𝟙 (TK R).left) z ⊤ (unitOn k) * val u (toUnit (TK R)).left z J) → ∀ z J J', Good D₀.P.L z J → Good Q.M.L z J' → gm (𝟙 (TK V).left) z ⊤ (unitOn k') * val u ((TK V).hom ≫ spMap θ) z J' = lamVal F.w (((TK V).hom ≫ spMap θ) ≫ (lift (Q.c a) (Q.c b)).left) z J J' * val (ψW.tau (F.xi a) (F.f • F.xi b)) g z J := by
  intro R V _ _ _ _ θ Q D₀ F W ψW g hg a b u x y k k' hu hy hk hk' hτ z J J' hJ hJ'
  letI := D₀.P.isAb.comm
  obtain ⟨t, ht, tv, tl⟩ := GlobalTheory.T.exists_period_generator_on_open R D₀ W ψW (F.xi a) (F.f • F.xi b)
  have hQ : ∀ T : Over (Sp R), (lift (toUnit T ≫ Q.c a) (toUnit T ≫ Q.c b)).left ≫
      (lift (fst Q.B Q.B ≫ F.inc) (snd Q.B Q.B ≫ F.inc ≫ F.o.onB.act F.f) : G2 Q.B ⟶ G2 D₀.P.A).left =
      𝟙 _ ≫ (lift (toUnit T ≫ D₀.c (F.xi a)) (toUnit T ≫ D₀.c (F.f • F.xi b))).left := fun T => by
    rw [Category.id_comp, ← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc, F.o.c_lin, F.c_xi, F.c_xi]
    simp only [Category.assoc]
  obtain ⟨t₁, ht₁, v₁⟩ := GlobalTheory.T.exists_generator_transport_mumfordBundleIso _ _ Q.B D₀.P.A Q.M.L D₀.P.L Q.M.isLB D₀.P.isLB _ F.w F.w_gen (TW W) (TW W)
    (toUnit (TW W) ≫ Q.c a) (toUnit (TW W) ≫ Q.c b) _ _ (𝟙 _) (hQ (TW W)) t ht
  obtain ⟨lam, hlam⟩ : ∃ lam : (TK R).left ⟶ W.toScheme, lam ≫ W.ι = jK R :=
    ⟨IsOpenImmersion.lift W.ι (jK R) (by
      rintro _ ⟨p, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact GlobalTheory.TauPull.jK_mem p _ ⟨(g z).1, (g z).2⟩), IsOpenImmersion.lift_fac _ _ _⟩
  have hl : ∀ T : Over (Sp R), (lift (toUnit T ≫ Q.c a) (toUnit T ≫ Q.c b)).left =
      T.hom ≫ (lift (Q.c a) (Q.c b)).left := fun T => by
    rw [← comp_lift]; rfl
  have H := GlobalTheory.T.generator_proportionality_spreads_from_generic R V θ W Q.B.left Q.M.L Q.M.isLB (Fin 4) (Fin 4)
    (lamPts (toUnit (TW W) ≫ Q.c a) (toUnit (TW W) ≫ Q.c b)) negε
    (fun i => W.ι ≫ lamPts (Q.c a) (Q.c b) i) negε (fun U _ h => Finset.prod_congr rfl fun i _ => by
      congr 2
      fin_cases i
      · exact congrArg (fun q : TW W ⟶ Q.B => q.left) (MonObj.comp_mul (toUnit (TW W)) (Q.c a) (Q.c b)).symm
      · rfl
      · rfl
      · exact congrArg (fun q : TW W ⟶ Q.B => q.left) (MonObj.comp_one (toUnit (TW W))).symm)
    t₁ (LB.pullGen Q.M.L _ _ u W.ι) ht₁ (DVR.pullGen_isGen _ _ _ _ hu _) lam hlam g hg x y k k' hy hk hk'
    (fun p I' hI' => by
      obtain ⟨I, hI⟩ := DegPull.exists_good' D₀.P.isLB p
      have e₁ := v₁ _ lam p I I' hI hI'
      have e₂ : lam ≫ (lift (toUnit (TW W) ≫ Q.c a) (toUnit (TW W) ≫ Q.c b)).left =
          (lift (toUnit (TK R) ≫ Q.c a) (toUnit (TK R) ≫ Q.c b)).left := by
        rw [hl, hl, ← Category.assoc]
        exact congrArg (· ≫ _) hlam
      rw [e₂] at e₁
      erw [Category.comp_id] at e₁
      refine e₁.trans ((congrArg (_ * ·) (tl lam hlam p I hI)).trans ((F.tau a b p I I' hI hI').symm.trans
        ((hτ p I' hI').trans (congrArg (_ * ·) ?_))))
      rw [val_pull hI', hlam]
      rfl) z J' hJ'
  have e₁ := v₁ _ g z J J' hJ hJ'
  have e₂ : g ≫ (lift (toUnit (TW W) ≫ Q.c a) (toUnit (TW W) ≫ Q.c b)).left =
      ((TK V).hom ≫ spMap θ) ≫ (lift (Q.c a) (Q.c b)).left := by
    rw [hl, ← Category.assoc]
    exact congrArg (· ≫ _) hg
  rw [e₂] at e₁
  erw [Category.comp_id] at e₁
  rw [val_pull hJ', hg] at H
  exact H.symm.trans (e₁.trans (congrArg (_ * ·) (tv _ g z J hJ)))

end GlobalTheory.FactorPeriod
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageModelMetricsSemiPositiveStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.imageModel_metrics_semiPositive : ∀ (K V Ω : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (D : ℕ) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (L : GlobalTheory.HermLB p) (ψ : Ω →+* X.functionField) (s : W → L.B.Sec), GlobalTheory.ImageModel.IsModelOf Nm W ev D p L ψ s → ev ≠ 0 → L.SemiPos D := by
  first | exact @GlobalTheory.ImageModelSemi.semiPos_of_isModelOf | exact GlobalTheory.ImageModelSemi.semiPos_of_isModelOf | (intros; apply GlobalTheory.ImageModelSemi.semiPos_of_isModelOf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCharpolyOfMonicIntegralAnnihilatorStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_charpoly_of_monic_integral_annihilator : ∀ (k V : Type) [Field k] [Algebra ℚ k] [AddCommGroup V] [Module k V] [Module.Finite k V] (φ : V →ₗ[k] V) (P : Polynomial ℚ) (Q : Polynomial ℤ), Q.Monic → Polynomial.aeval φ Q = 0 → P.map (algebraMap ℚ k) = φ.charpoly → ∃ P₀ : Polynomial ℤ, P₀.map (algebraMap ℤ ℚ) = P := by
  first | exact @GlobalTheory.AV.AbVar.int_of_charpoly_rat_of_monic_annihilator | exact GlobalTheory.AV.AbVar.int_of_charpoly_rat_of_monic_annihilator | (intros; apply GlobalTheory.AV.AbVar.int_of_charpoly_rat_of_monic_annihilator <;> assumption)
end

