import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0288
import Development.AbelianVarietyTheory.Definitions.Divisors.DiagValExtTraceNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1290
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1313
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1310
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1318
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1291
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2688
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1292
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1298
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0803
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0134
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2765
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2589
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0730
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0725
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2692
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PtMapDualBCLeft
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2404
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2662
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2597
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2726
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2754
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2748

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubquotientCurvatureStatement
section
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms

noncomputable section

namespace GlobalTheory.SubQuotCurv

theorem connBlocks : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U), ConnBlocks H z (fun η => -secondFormAdj H z η) (secondForm H z) :=
  GlobalTheory.T.connection_blocks_hermitian_frame

theorem gaussS : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U) (ξ η : V), curv (gramS H) z ξ η = blockSS (H z) (curv H z ξ η) + wedgeAntiHol (secondFormAdj H z) (secondForm H z) ξ η :=
  GlobalTheory.T.subbundle_curvature_formula

theorem gaussQ : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U) (ξ η : V), curv (gramQ H) z ξ η = blockQQ (H z) (curv H z ξ η) + wedgeHolAnti (secondForm H z) (secondFormAdj H z) ξ η :=
  GlobalTheory.T.quotient_bundle_curvature_formula

theorem curvSQ : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U) (ξ η : V), blockSQ (H z) (curv H z ξ η) = covDelAnti (gramQ H) (gramS H) (extForm H) z ξ η :=
  GlobalTheory.T.curvature_off_diagonal_block

theorem curvQS : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U) (ξ η : V), blockQS (curv H z ξ η) = -dbarHol (extFormAdj H) z ξ η :=
  GlobalTheory.T.curvature_quotient_sub_block

theorem dbarExt : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U) (η₁ η₂ : V), dbarAnti (extForm H) z η₁ η₂ = 0 :=
  GlobalTheory.T.dbar_extension_form_zero

theorem delExtAdj : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U) (ξ₁ ξ₂ : V), covDelHol (gramS H) (gramQ H) (extFormAdj H) z ξ₁ ξ₂ = 0 :=
  GlobalTheory.T.cov_del_hol_extension_zero

theorem ddcAny : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U) (hb : ∀ x ∈ U, ExtBlocksAt H x) (ξ₁ η₁ ξ₂ η₂ : V), ddcForm (extTrace H) z ξ₁ η₁ ξ₂ η₂ = chTwo (gramS H) z ξ₁ η₁ ξ₂ η₂ + chTwo (gramQ H) z ξ₁ η₁ ξ₂ η₂ - chTwo H z ξ₁ η₁ ξ₂ η₂ :=
  GlobalTheory.T.ddc_extension_trace_chern_forms

theorem nonneg : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsPosFrame U H) (hz : z ∈ U), IsNonnegForm (extTrace H z) :=
  GlobalTheory.T.ext_trace_nonneg_of_pos_frame

theorem sqZero : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsPosFrame U H) (hz : z ∈ U) (hm : Fintype.card m = 1) (hl : Fintype.card l = 1) (ξ₁ η₁ ξ₂ η₂ : V), wedge (extTrace H z) (extTrace H z) ξ₁ η₁ ξ₂ η₂ = 0 :=
  GlobalTheory.T.ext_trace_wedge_self_eq_zero

theorem line_bundle_curvature_subquotient : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsPosFrame U H) (hz : z ∈ U) (hm : Fintype.card m = 1) (hl : Fintype.card l = 1) (hg : ∀ ξ η, curv (gramS H) z ξ η = blockSS (H z) (curv H z ξ η) + wedgeAntiHol (secondFormAdj H z) (secondForm H z) ξ η) (hc : ∀ ξ η, chernOne H z ξ η = chernOne (gramS H) z ξ η + chernOne (gramQ H) z ξ η) (u : m → ℂ) (hu : u ≠ 0) (ξ η : V), chernOne (gramS H) z ξ η = lineCurv H z (incl m l *ᵥ u) ξ η - extTrace H z ξ η ∧ chernOne (gramQ H) z ξ η = chernOne H z ξ η - lineCurv H z (incl m l *ᵥ u) ξ η + extTrace H z ξ η :=
  GlobalTheory.T.sub_bundle_curvature_rank_one

theorem ddcTwo : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (hm : Fintype.card m = 1) (hl : Fintype.card l = 1) (hc : ∀ ξ η, chernOne H z ξ η = chernOne (gramS H) z ξ η + chernOne (gramQ H) z ξ η) (hd : ∀ ξ₁ η₁ ξ₂ η₂, ddcForm (extTrace H) z ξ₁ η₁ ξ₂ η₂ = chTwo (gramS H) z ξ₁ η₁ ξ₂ η₂ + chTwo (gramQ H) z ξ₁ η₁ ξ₂ η₂ - chTwo H z ξ₁ η₁ ξ₂ η₂) (ξ₁ η₁ ξ₂ η₂ : V), ddcForm (extTrace H) z ξ₁ η₁ ξ₂ η₂ = chernTwo H z ξ₁ η₁ ξ₂ η₂ - wedge (chernOne (gramS H) z) (chernOne (gramQ H) z) ξ₁ η₁ ξ₂ η₂ :=
  GlobalTheory.T.chern_two_ddc_ext_trace

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V]
  {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]
  {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V}

theorem formTypes_secondForm (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det)
    (hz : z ∈ U) : FormTypes (secondFormAdj H) (secondForm H) z := by
  refine ⟨fun η η' => ?_, fun c η => ?_, fun ξ ξ' => ?_, fun c ξ => ?_,
    fun η => GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm.smooth_secondFormAdj h hs hz η, fun ξ => GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm.smooth_secondForm h hz ξ⟩
  · simp only [secondFormAdj, adj, secondForm, blockQS, conn_add_vec, Matrix.mul_add,
      Matrix.add_mul, conjTranspose_add]
  · simp only [secondFormAdj, adj, secondForm, blockQS, conn_smul_vec, Matrix.mul_smul,
      Matrix.smul_mul, conjTranspose_smul, Complex.star_def]
  · simp only [secondForm, blockQS, conn_add_vec, Matrix.mul_add, Matrix.add_mul]
  · simp only [secondForm, blockQS, conn_smul_vec, Matrix.mul_smul, Matrix.smul_mul]

theorem subQuotAt (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U) :
    SubQuotAt H z :=
  ⟨fun ξ _ => ⟨eq_conn_of_compatible (h.isUnit z hz),
      fun e => e ▸ conn_transpose_mul (h.isUnit z hz) ξ⟩,
    formTypes_secondForm h hs hz, fun ξ s q => form_secondForm (h.herm z hz) (hs z hz) ξ s q,
    connBlocks h hs hz, gaussS h hs hz, gaussQ h hs hz⟩

theorem extForm_eq (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U) :
    extForm H z = fun η => -secondFormAdj H z η :=
  funext fun η => extForm_eq_neg_secondFormAdj (h.one hz) (h.eventually_herm hz) (h.isUnit z hz)
    (hs z hz) η

theorem extFormAdj_eq (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det)
    (hz : z ∈ U) : extFormAdj H z = fun ξ => -secondForm H z ξ :=
  funext fun ξ => extFormAdj_eq_neg_secondForm (h.one hz) (h.eventually_herm hz) (h.isUnit z hz)
    (hs z hz) ξ

theorem extBlocksAt (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U) :
    ExtBlocksAt H z := by
  have hh := h.herm z hz
  have eβ := extForm_eq h hs hz
  have eγ := extFormAdj_eq h hs hz
  have ft := formTypes_secondForm h hs hz
  have w1 : ∀ ξ η, wedgeAntiHol (extForm H z) (extFormAdj H z) ξ η =
      wedgeAntiHol (secondFormAdj H z) (secondForm H z) ξ η := fun ξ η => by
    simp only [wedgeAntiHol, eβ, eγ, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  have w2 : ∀ ξ η, wedgeHolAnti (extFormAdj H z) (extForm H z) ξ η =
      wedgeHolAnti (secondForm H z) (secondFormAdj H z) ξ η := fun ξ η => by
    simp only [wedgeHolAnti, eβ, eγ, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  refine ⟨⟨fun η η' => ?_, fun c η => ?_, fun ξ ξ' => ?_, fun c ξ => ?_,
      fun η => GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm.smooth_extForm h hs hz η, fun ξ => GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm.smooth_extFormAdj h hs hz ξ⟩,
    fun ξ q s => form_adj (isHermitian_quotGram hh) (isUnit_det_quotGram (h.isUnit z hz) (hs z hz))
      (isHermitian_subGram hh) _ q s, ?_, fun ξ η => ?_, curvSQ h hs hz, curvQS h hs hz,
    fun ξ η => ?_, dbarExt h hs hz, delExtAdj h hs hz⟩
  · rw [eβ]; simp only [ft.1 η η', neg_add]
  · rw [eβ]; simp only [ft.2.1 c η, smul_neg]
  · rw [eγ]; simp only [ft.2.2.1 ξ ξ', neg_add]
  · rw [eγ]; simp only [ft.2.2.2.1 c ξ, smul_neg]
  · have e2 : (fun ξ => -extFormAdj H z ξ) = secondForm H z := by
      rw [eγ]; funext ξ; simp
    rw [eβ, e2]; exact connBlocks h hs hz
  · rw [w1, gaussS h hs hz]; abel
  · rw [w2, gaussQ h hs hz]; abel

theorem chernOne_add (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det)
    (hz : z ∈ U) (ξ η : V) :
    chernOne H z ξ η = chernOne (gramS H) z ξ η + chernOne (gramQ H) z ξ η := by
  rw [chernOne, chernOne, chernOne, GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm.trace_eq_blocks (H z), gaussS h hs hz, gaussQ h hs hz]
  simp only [wedgeAntiHol, wedgeHolAnti, trace_add, trace_neg,
    trace_mul_comm (secondForm H z ξ)]
  ring

theorem subQuotCurvature : SubQuotCurvature := by
  intro V _ _ _ _ _ m l _ _ _ _ U H
  refine ⟨fun h hs => ⟨h.sub hs, h.quot hs, fun z hz => subQuotAt h hs hz⟩, fun hp => ?_⟩
  have h := hp.isHermFrame
  have hs : ∀ z ∈ U, IsUnit (subGram (H z)).det := fun z hz => GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm.isUnit_sub hp z hz
  refine ⟨hp.sub, hp.quot, fun z hz => ⟨fun ξ s => ?_, extBlocksAt h hs hz,
    nonneg hp hz, chernOne_add h hs hz, ddcAny h hs hz (fun x hx => extBlocksAt h hs hx)⟩,
    fun hm hl z hz => ⟨nonneg hp hz, sqZero hp hz hm hl,
      fun u hu ξ η => line_bundle_curvature_subquotient hp hz hm hl (gaussS h hs hz) (chernOne_add h hs hz) u hu ξ η,
      ddcTwo hm hl (chernOne_add h hs hz) (ddcAny h hs hz (fun x hx => extBlocksAt h hs hx))⟩⟩
  have hh := h.herm z hz
  simp only [wedgeAntiHol, gramS, gramQ]
  rw [form_secondFormAdj_mul hh (hs z hz) ξ s, form_self (posDef_quotGram (hp.posDef z hz)).posSemidef]

end GlobalTheory.SubQuotCurv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveLabelHomLatticeModLevelThetaMember
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep.Labels

theorem comp_pow_overScheme_grpObj {S : Scheme.{0}} {A T T' : Over S} [GrpObj A] (ρ : T' ⟶ T) (x : T ⟶ A) (n : ℕ) :
    ρ ≫ x ^ n = (ρ ≫ x) ^ n := by
  induction n with
  | zero => simp only [pow_zero, MonObj.comp_one]
  | succ n ih => rw [pow_succ, MonObj.comp_mul, ih, pow_succ]

open GlobalTheory.TorusExt in
attribute [local instance] gtGroup in

theorem yy_hom : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), (∀ a, ∃ mu, 𝔪.YY a mu) ∧ (∀ mu, ∃ a, 𝔪.YY a mu) ∧ (∀ a mu mu', 𝔪.YY a mu → (𝔪.YY a mu' ↔ ∀ v, CongMod (X₁.S.r * X₁.S.N) (mu' v) (mu v))) ∧ (∀ a a' mu mu', 𝔪.YY a mu → 𝔪.YY a' mu' → 𝔪.YY (a + a') (mu + mu')) := by
  intro g n F W Z i X₁ z₁ act V _ _ _ ev X _ m t δ 𝔪
  haveI : CharZero V := 𝔪.cn.2.2.2
  have hL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws
  have hA : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩
  have hB := 𝔪.D.tau_bimult
  have hk : 1 ≤ X₁.S.r * X₁.S.N := by
    have := X₁.S.r_pos; have := X₁.S.N_ge
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  obtain ⟨x, hx, xadd, -, xonto⟩ := GlobalTheory.ThetaDvr.torsion_points 𝔪.yK 𝔪.cart
  obtain ⟨rig, e, -, he, -⟩ := GlobalTheory.ThetaDvr.frames 𝔪.yK 𝔪.cart ⟨𝔪.wl, 𝔪.wl_gen⟩ x hx
  obtain ⟨f, f₁, f₂, f₃, f₄, -⟩ := GlobalTheory.TorsionIso.torsion_eq hL V (maximalIdeal V) hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U
    (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) hk
  have tor : ∀ p y, QkToAkU 𝔪.U.toUnifPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) p y →
      y ^ (X₁.S.r * X₁.S.N) = 1 := fun p y h => by
    obtain ⟨w, hw⟩ := 𝔪.U.ext
    exact (h w hw).1
  have uniq : ∀ a (y : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ 𝔪.A.A), y ^ (X₁.S.r * X₁.S.N) = 1 →
      y.left ≫ 𝔪.φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) ≫
        (X₁.ρ.pt a).left → y = x a := by
    intro a y hy hya
    obtain ⟨b, rfl⟩ := xonto y hy
    obtain ⟨c, -, hc⟩ := X₁.ρ.pt_bij (AlgebraicClosure (FractionRing V))
      (spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK))
      ((Over.homMk (spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK)) (by simp) :
        Over.mk (spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK)) ⟶
          baseOver (Sp X₁.S.R)) ≫ X₁.ρ.pt a)
      (by rw [← comp_pow_overScheme_grpObj, (X₁.ρ.fr_tors a).1, MonObj.comp_one])
    have h1 := hc a rfl
    have h2 := hc b (by
      ext1
      simp only [Over.comp_left, Over.homMk_left]
      rw [← hx b, hya])
    rw [h1.trans h2.symm]
  have ex : ∀ a, ∃ p, QkToAkU 𝔪.U.toUnifPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) p (x a) :=
    fun a => by
      obtain ⟨p, hp⟩ := f₂ (x a) (he a).1
      exact ⟨p, (f₁ _ _).2 hp.symm⟩
  have yyI : ∀ a mu, 𝔪.YY a mu ↔ ∃ p : QkPt 𝔪.D.toPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N),
      p.y = 𝔪.e₈ mu ∧ QkToAkU 𝔪.U.toUnifPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) p (x a) := by
    intro a mu
    constructor
    · rintro ⟨p, y, hpy, hq, hov⟩
      obtain rfl := uniq a y (tor p y hq) hov
      exact ⟨p, hpy, hq⟩
    · rintro ⟨p, hpy, hq⟩
      exact ⟨p, x a, hpy, hq, hx a⟩
  refine ⟨fun a => ?_, fun mu => ?_, fun a mu mu' h => ?_, fun a a' mu mu' h h' => ?_⟩
  · obtain ⟨p, hp⟩ := ex a
    exact ⟨𝔪.e₈.symm p.y, (yyI a _).2 ⟨p, by simp, hp⟩⟩
  · obtain ⟨p, hp⟩ := exists_qkPt (F := AlgebraicClosure (FractionRing V)) hL.1.mulN (Or.inr hL.1.polBaseChange) hB
      (n := X₁.S.r * X₁.S.N) (by omega) (𝔪.e₈ mu)
    obtain ⟨a, ha⟩ := xonto (f p) (tor p _ ((f₁ _ _).2 rfl))
    exact ⟨a, (yyI a mu).2 ⟨p, hp, (f₁ _ _).2 ha.symm⟩⟩
  · obtain ⟨p, hpy, hq⟩ := (yyI a mu).1 h
    rw [yyI]
    constructor
    · rintro ⟨p', hpy', hq'⟩
      have hpp : QkPt.Equiv _ _ p p' := (f₃ p p').1 (((f₁ _ _).1 hq).symm.trans ((f₁ _ _).1 hq'))
      obtain ⟨z, hz, -⟩ := (equiv_iff hB _ _).1 hpp
      have e' : mu' = mu + (X₁.S.r * X₁.S.N) • 𝔪.e₈.symm z := 𝔪.e₈.injective (by
        rw [map_add, map_nsmul, AddEquiv.apply_symm_apply, ← hpy, ← hpy', hz])
      intro v
      exact ⟨𝔪.e₈.symm z v, by rw [e']; rfl⟩
    · intro hc
      choose w hw using hc
      refine ⟨qkShift hB p (𝔪.e₈ w), ?_, (f₁ _ _).2 (((f₁ _ _).1 hq).trans ((f₃ _ _).2 (equiv_qkShift hB p _)))⟩
      show p.y + (X₁.S.r * X₁.S.N) • 𝔪.e₈ w = 𝔪.e₈ mu'
      rw [hpy, ← map_nsmul, ← map_add]
      congr 1
      funext v
      exact (hw v).symm
  · obtain ⟨p, hpy, hq⟩ := (yyI a mu).1 h
    obtain ⟨p', hpy', hq'⟩ := (yyI a' mu').1 h'
    refine (yyI _ _).2 ⟨qkAdd hB p p', ?_, ?_⟩
    · show p.y + p'.y = 𝔪.e₈ (mu + mu')
      rw [map_add, hpy, hpy']
    · rw [f₁, f₄ _ _ _ (qkAdd_qkAdd hB p p'), ← (f₁ _ _).1 hq, ← (f₁ _ _).1 hq', xadd]

end GlobalTheory.Poinc.Sep.Labels
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOpenPartProductMapIrreducibleFibresStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.surjective_openPart_productMap_irreducible_fibres : ∀ (T : Scheme.{0}) (H V : Over T) [GrpObj H] (e : V ⟶ H), IsOpenImmersion e.left → Surjective V.hom → (∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ T), IrreducibleSpace (pullback H.hom t : Scheme.{0})) → Surjective ((fst V V ≫ e) * (snd V V ≫ e)).left := by
  first | exact @GlobalTheory.Mum.surjective_mul_of_open_of_irreducible_fibres | exact GlobalTheory.Mum.surjective_mul_of_open_of_irreducible_fibres | (intros; apply GlobalTheory.Mum.surjective_mul_of_open_of_irreducible_fibres <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectivePiLiftKaehlerCoordinateDerivations
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem surjective_pi_liftKaehler_of_pointwise {K B J : Type*} [Field K] [CommRing B] [Algebra K B] [Fintype J] [DecidableEq J]
    (d : J → Derivation K B B)
    (h : ∀ m : Ideal B, m.IsMaximal → ∃ e : B →ₐ[K] K, (∀ b, e b = 0 → b ∈ m) ∧
      ∀ w : J → K, (∀ x, ∑ a, e (d a x) * w a = 0) → w = 0) :
    Function.Surjective (LinearMap.pi fun a => (d a).liftKaehlerDifferential) := by
  rw [← LinearMap.range_eq_top]
  by_contra hN
  obtain ⟨M, hM, hle⟩ := (eq_top_or_exists_le_coatom
    (LinearMap.range (LinearMap.pi fun a => (d a).liftKaehlerDifferential))).resolve_left hN
  have hs : IsSimpleModule B ((J → B) ⧸ M) := isSimpleModule_iff_isCoatom.2 hM
  obtain ⟨e, he, hw⟩ := h (Module.annihilator B ((J → B) ⧸ M)) IsSimpleModule.annihilator_isMaximal
  let φ : B →ₗ[K] (J → K) := LinearMap.pi fun a => e.toLinearMap ∘ₗ (d a).toLinearMap
  have hφ : LinearMap.range φ = ⊤ := by
    by_contra hφ
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hφ)
    have hfy : ∀ y : J → K, f y = ∑ a, y a * f (Pi.single a 1) := by
      intro y
      conv_lhs => rw [pi_eq_sum_univ' y]
      simp [map_sum]
    have h0 := hw (fun a => f (Pi.single a 1)) fun x => by
      have : f (φ x) = 0 := hf ⟨x, rfl⟩
      rw [hfy] at this
      exact this
    apply hf0
    refine LinearMap.ext fun y => ?_
    rw [hfy]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [congrFun h0 a]
    simp
  apply hM.1
  rw [eq_top_iff]
  intro y _
  obtain ⟨x, hx⟩ := LinearMap.range_eq_top.1 hφ fun a => e (y a)
  have h1 : (fun a => d a x) ∈ M := by
    refine hle ⟨KaehlerDifferential.D K B x, ?_⟩
    funext a
    simp
  have h2 : y - (fun a => d a x) ∈ M := by
    rw [pi_eq_sum_univ' (y - fun a => d a x)]
    refine M.sum_mem fun a _ => ?_
    have hm : (y - fun a => d a x) a ∈ Module.annihilator B ((J → B) ⧸ M) := by
      apply he
      have : e (d a x) = e (y a) := congrFun hx a
      simp [this]
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
    exact Module.mem_annihilator.1 hm _
  simpa using M.add_mem h2 h1

theorem surjective_pi_liftKaehler_coord : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g),
    IsAbelianScheme A → ∀ (U : A.left.affineOpens) (d : Fin g → Derivation ℂ (Sec (str A) U.1) (Sec (str A) U.1)),
    (∀ a x, ∀ z ∈ pre u.ex U.1, val u.ex U.1 (d a x) z = fderiv ℂ (val u.ex U.1 x) z (Pi.single a 1)) →
    Function.Surjective (LinearMap.pi fun a => (d a).liftKaehlerDifferential) := by
  intro A _ g L u hA U d hd
  refine surjective_pi_liftKaehler_of_pointwise d fun m hm => ?_
  obtain ⟨z, hz, hm'⟩ := GlobalTheory.T.maximalIdeal_affineOpen_eq_vanishing_uniformisationPoint A g L u hA U.1 U.2 m hm
  obtain ⟨e, he⟩ := (GlobalTheory.T.uniformisation_preimage_value_rules A g L u).2.2.2.2.2.2.2.2.2.1 U.1 z hz
  refine ⟨e, fun b hb => (hm' b).2 ((he b).trans hb), fun w hw => ?_⟩
  refine GlobalTheory.T.eq_zero_of_fderiv_regular_functions_affineOpen A g L u hA U.1 U.2 z hz w fun b => ?_
  rw [← hw b]
  conv_lhs => rw [pi_eq_sum_univ' w]
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]
  exact congrArg (· * w a) ((hd a b z hz).symm.trans (he _))

end GlobalTheory.CechPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisFrameMapImports
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel GlobalTheory.FinPartAt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FinPartAt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
  {R : Type} [CommRing R] {ξ : Sp R ⟶ X} {q : ℕ} (P' : GlobalTheory.HTMap.FP t ξ q)
  {O : Type} [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f))

theorem one_left_π {S' S : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {π : G'.left ⟶ G.left} (hg : IsGrpPullback G' G f π) (T : Over S') :
    (1 : T ⟶ G').left ≫ π = (1 : Over.mk (T.hom ≫ f) ⟶ G).left := by
  let x₀ : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk ((1 : T ⟶ G').left ≫ π) (by
    show _ = T.hom ≫ f
    rw [Category.assoc, hg.1.w, ← Category.assoc, Over.w])
  have h := hg.2 T 1 1 x₀ x₀ rfl rfl
  rw [_root_.mul_one] at h
  have e : x₀ * x₀ = x₀ := Over.OverMorphism.ext h
  have e' : x₀ = 1 := by
    have := congrArg (· * x₀⁻¹) e
    simpa using this
  exact congrArg Over.Hom.left e'

theorem exists_unit {G' : Over (Sp O)} [GrpObj G'] {π : G'.left ⟶ t.G.left}
    (hg : IsGrpPullback G' t.G (spMap x0 ≫ ξ) π) (S : Over (Sp O)) :
    ∃ z : S ⟶ Hs P' x0 hu, z ≫ aH P' x0 hu hg.1 = 1 := by
  obtain ⟨β₀, h1, h2⟩ := P'.fin.one O (lo P' x0 hu)
  have hβ₀ : β₀.comp P'.str = (algebraMap O O).comp x0 := by
    rw [GlobalTheory.HTMap.FP.str, ← RingHom.comp_assoc, h1, lo_comp]
    try rfl
  have hid : (specO O O).hom = 𝟙 _ := by
    change Spec.map (CommRingCat.ofHom (algebraMap O O)) = _
    rw [Algebra.algebraMap_self]
    exact Spec.map_id _
  let c : S ⟶ specO O O := Over.homMk S.hom (by rw [hid, Category.comp_id]; try rfl)
  refine ⟨c ≫ ptOf P' x0 hu β₀ hβ₀, ?_⟩
  have hz : ptOf P' x0 hu β₀ hβ₀ ≫ aH P' x0 hu hg.1 = 1 := by
    refine Over.OverMorphism.ext (hg.1.hom_ext ?_ ?_)
    · rw [ptOf_aH_π, h2, one_left_π hg]
      refine (GlobalTheory.HTMap.one_of (G := t.G) (g := 𝟙 _) ?_).trans (Category.id_comp _)
      rw [Category.id_comp, hid, Category.id_comp, GlobalTheory.HTMap.spc_assoc, lo_comp]
    · rw [Over.w, Over.w]
  rw [Category.assoc, hz, MonObj.comp_one]

end GlobalTheory.FinPartAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentDifferentialUnique
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.AbDual in

theorem GlobalTheory.KerDeform.ker_deform : GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (R R₀ : Type) [CommRing R] [CommRing R₀]
    (I : Ideal R) (κ : DividedPowers I), IsNilDP κ → ∀ (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I →
  ∀ (X₀ : Obj F 𝔠 (Sp R₀)) (A : Over (Sp R)) [GrpObj A] (i : X₀.A.left ⟶ A.left),
    IsGrpPullback X₀.A A (spMap π) i → IsAbelianScheme A → SmoothOfRelativeDimension (Module.finrank ℚ F) A.hom →
  ∀ (rm : OAct (𝓞 F) A), (∀ a, (X₀.rm.act a).left ≫ i = i ≫ (rm.act a).left) →
  ∀ (P : 𝔠.elt → LB (G2 A).left) (l : (G2 X₀.A).left ⟶ (G2 A).left), IsSquare i l → (∀ c, (P c).IsLB) →
    (∀ c, HasGen ((P c).pull (lift (1 : A ⟶ A) (𝟙 A)).left)) → (∀ c, HasGen ((P c).pull (lift (𝟙 A) (1 : A ⟶ A)).left)) →
    (∀ c, LBIso ((P c).pull l) (X₀.P c)) →
    (∀ c, LBIso (P c) ((P c).pull (lift (snd A A) (fst A A)).left)) →
    (∀ c c', LBIso (P c') (LB.div (P (c + c')) (P c))) →
    (∀ (a : 𝓞 F) c, LBIso (P (a • c)) ((P c).pull (lift (fst A A) (snd A A ≫ rm.act a)).left)) →
    (∀ c : 𝔠.elt, IsTotPos (c : F) → Out.RelAmple A ((P c).pull (lift (𝟙 A) (𝟙 A)).left)) →
  ∀ (c : 𝔠.elt) (T : Over (Sp R)) (x : T ⟶ A), HasGen ((P c).pull (lift (fst A T) (snd A T ≫ x)).left) →
    ∀ a : 𝓞 F, (∀ d : 𝔠.elt, ∃ b : 𝓞 F, a • d = b • c) → x ≫ rm.act a = 1 := by
  intro HG HR HD F _ _ _ 𝔠 R R₀ _ _ I κ hκ π hπ hI X₀ A _ i hi hA hdim rm hrm P l hl hLB rig₁ rig₂ hred symm add smul pos c T x hx a ha
  obtain ⟨n, d, a', hd, hsum⟩ := GlobalTheory.T.fractional_ideal_partition_of_unity F 𝔠
  have k₀ : ∀ (T₀ : Over (Sp R₀)) (y₀ : T₀ ⟶ X₀.A),
      (∀ j, HasGen ((X₀.P (d j)).pull (lift (fst X₀.A T₀) (snd X₀.A T₀ ≫ y₀)).left)) → y₀ = 1 := by
    intro T₀ y₀ hy
    have h0 : X₀.rm.act 0 = 1 := by
      have e := X₀.rm.add 0 0
      rw [add_zero] at e
      exact left_eq_mul.1 e
    have hs : ∀ s : Finset (Fin n), y₀ ≫ X₀.rm.act (∑ j ∈ s, a' j) = 1 := by
      intro s
      induction s using Finset.induction_on with
      | empty => rw [Finset.sum_empty, h0, MonObj.comp_one]
      | @insert j s hj ih =>
        rw [Finset.sum_insert hj, X₀.rm.add, MonObj.comp_mul, ih, X₀.ker (d j) T₀ y₀ (hy j) (a' j) (hd j), _root_.mul_one]
    have e := hs Finset.univ
    rwa [hsum, X₀.rm.one, Category.comp_id] at e
  obtain ⟨N, hN⟩ := GlobalTheory.AmpleNilThickening.exists_pow_eq_bot_of_isNilDP hκ
  obtain ⟨D, _, Q, hDab, -, q, q'⟩ := HD.1 _ A hA
  obtain ⟨cp, hcp⟩ := fracId_exists_totPos F 𝔠
  have hL : ((P cp).pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB (hLB cp) _
  choose lam hlam hiff using fun j ↦ GlobalTheory.PoincarePull.exists_hom_triv_iff R A hA D Q q q' _ hL (pos cp hcp) (P (d j)) (hLB _) (rig₁ _) (rig₂ _)
  have key : ∀ (T : Over (Sp R)) (y : T ⟶ A),
      (∀ j, HasGen ((P (d j)).pull (lift (fst A T) (snd A T ≫ y)).left)) → y = 1 := by
    intro T y hy
    haveI := hDab.proper
    haveI := hA.proper
    refine GlobalTheory.T.monomorphism_trivial_on_kernel R R₀ π hπ ⟨N, by rw [hI]; exact hN⟩ A inferInstance n D inferInstance lam hlam ?_ T y
      fun j ↦ (hiff j T y).1 (hy j)
    intro T₀ z hz
    let z₀ : Over.mk T₀.hom ⟶ X₀.A := liftPt hi T₀.hom z.left (Over.w z)
    have hz₀ : z₀.left ≫ i = z.left := liftPt_left hi _ _ _
    have hpush : pushP hi (s := T₀.hom) rfl z₀ = z := Over.OverMorphism.ext hz₀
    have k₁ : z₀ = 1 := k₀ _ z₀ fun j ↦ by
      have hP := hLB (d j)
      have hP' := X₀.isLB (d j)
      have e := evc_trR hi hi hl.1 hl.2 hP hP' (hred (d j)) (Over.mk T₀.hom) z₀
      have e0 : evc hP (fst A (Over.mk (T₀.hom ≫ spMap π))) (snd A _ ≫ z) = 0 :=
        (triv_ev_iff hP _ _).1 ((hiff j _ z).2 (hz j))
      rw [hpush] at e
      obtain ⟨s, hs⟩ : ∃ s, s ≫ (trR hi (Over.mk T₀.hom)).left = 𝟙 _ := ⟨_, trR_section hi _⟩
      have e2 := congrArg (CechPic.pull s) (e.trans e0)
      rw [← GlobalTheory.CechPic.pull_comp, hs, GlobalTheory.CechPic.pull_id, map_zero] at e2
      exact (triv_ev_iff hP' _ _).2 e2
    apply Over.OverMorphism.ext
    rw [← hz₀, k₁]
    exact one_left_comp hi (s := T₀.hom) rfl
  refine key T (x ≫ rm.act a) fun j ↦ ?_
  obtain ⟨b, hb⟩ := ha (d j)
  exact GlobalTheory.T.poincare_bundle_isomorphism_compat F 𝔠 _ A rm P hLB symm smul c (d j) a b hb T x hx
end

