import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0288
import Development.AbelianVarietyTheory.Definitions.Divisors.DiagValExtTraceNonneg
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1081
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1074
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1127
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1224
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1146
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1235
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DdcExtensionTraceChernForms
section
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms

noncomputable section

namespace GlobalTheory.SubQuotChTwo

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
  [IsScalarTower ℝ ℂ V]

section Calc

variable {m n : Type} [Fintype m] [Fintype n]

theorem dbar_trace_mul {X : V → Matrix n m ℂ} {Y : V → Matrix m n ℂ} {z : V}
    (hX : MContDiffAt 1 X z) (hY : MContDiffAt 1 Y z) (η : V) :
    dbar (fun x => (X x * Y x).trace) z η = (mdbar X z η * Y z).trace + (X z * mdbar Y z η).trace := by
  have e : (fun x => (X x * Y x).trace) = fun x => ∑ a, (X x * Y x) a a := rfl
  rw [e, dbar_sum (fun a _ => ((hX.mul hY).diff a a))]
  have := mdbar_mul hX hY η
  simp only [ContinuousLinearMap.sum_apply, Matrix.trace, Matrix.diag]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h2 := congrFun (congrFun this a) a
  simp only [mdbar_apply, Matrix.add_apply] at h2
  rw [h2, add_comm]

variable [DecidableEq m] [DecidableEq n]

theorem del_trace_mul {A : V → Matrix m m ℂ} {B : V → Matrix n n ℂ} {X : V → Matrix n m ℂ}
    {Y : V → Matrix m n ℂ} {z : V} (hX : MContDiffAt 1 X z) (hY : MContDiffAt 1 Y z) (ξ : V) :
    del (fun x => (X x * Y x).trace) z ξ =
      (homDel A B X z ξ * Y z).trace + (X z * homDel B A Y z ξ).trace := by
  have e : (fun x => (X x * Y x).trace) = fun x => ∑ a, (X x * Y x) a a := rfl
  rw [e, del_sum (fun a _ => (hX.mul hY).diff a a)]
  simp only [ContinuousLinearMap.sum_apply]
  have h1 : ∑ a, del (fun x => (X x * Y x) a a) z ξ = (mdel (fun x => X x * Y x) z ξ).trace := rfl
  rw [h1, mdel_mul hX hY]
  simp only [homDel, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub,
    Matrix.trace_add, Matrix.trace_sub, Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm (conn B z ξ)]
  simp only [Matrix.mul_assoc]
  ring

theorem mdbar_homDel {A : V → Matrix m m ℂ} {B : V → Matrix n n ℂ} {T : V → Matrix n m ℂ} {z : V}
    (hA : MContDiffAt 2 A z) (hAu : IsUnit (A z).det) (hB : MContDiffAt 2 B z)
    (hBu : IsUnit (B z).det) (hT : MContDiffAt 2 T z) (ξ η : V) :
    mdbar (fun x => homDel A B T x ξ) z η =
      homDel A B (fun x => mdbar T x η) z ξ - curv B z ξ η * T z + T z * curv A z ξ η := by
  have hT1 : MContDiffAt 1 T z := hT.of_le one_le_two
  have hcA : MContDiffAt 1 (fun x => conn A x ξ) z := hA.conn hAu (by norm_num) ξ
  have hcB : MContDiffAt 1 (fun x => conn B x ξ) z := hB.conn hBu (by norm_num) ξ
  have hdT : MContDiffAt 1 (fun x => mdel T x ξ) z := hT.mdel (by norm_num) ξ
  show mdbar (fun x => mdel T x ξ + conn B x ξ * T x - T x * conn A x ξ) z η = _
  rw [show (fun x => mdel T x ξ + conn B x ξ * T x - T x * conn A x ξ) =
      fun x => (mdel T x ξ + conn B x ξ * T x) + -(T x * conn A x ξ) from
      funext fun x => sub_eq_add_neg _ _]
  rw [mdbar_add (hdT.add (hcB.mul hT1)) (hT1.mul hcA).neg, mdbar_neg,
    mdbar_add hdT (hcB.mul hT1), mdbar_mul hcB hT1, mdbar_mul hT1 hcA, mdbar_mdel hT]
  simp only [homDel, curv, mdel_mdbar hT, Matrix.neg_mul, Matrix.mul_neg]
  abel

theorem mContDiffAt_homDel {A : V → Matrix m m ℂ} {B : V → Matrix n n ℂ} {T : V → Matrix n m ℂ}
    {z : V} (hA : MContDiffAt ∞ A z) (hAu : IsUnit (A z).det) (hB : MContDiffAt ∞ B z)
    (hBu : IsUnit (B z).det) (hT : MContDiffAt ∞ T z) (ξ : V) :
    MContDiffAt 1 (fun x => homDel A B T x ξ) z := by
  have hA2 : MContDiffAt 2 A z := hA.of_le (by norm_cast)
  have hB2 : MContDiffAt 2 B z := hB.of_le (by norm_cast)
  have hT2 : MContDiffAt 2 T z := hT.of_le (by norm_cast)
  exact ((hT2.mdel (by norm_num) ξ).add ((hB2.conn hBu (by norm_num) ξ).mul
    (hT2.of_le one_le_two))).sub ((hT2.of_le one_le_two).mul (hA2.conn hAu (by norm_num) ξ))

end Calc

theorem chTwo_eq_trace {n : Type} [Fintype n] [DecidableEq n] (H : V → Matrix n n ℂ)
    (z ξ₁ η₁ ξ₂ η₂ : V) : chTwo H z ξ₁ η₁ ξ₂ η₂ = kappa ^ 2 / 2 *
      ((curv H z ξ₁ η₁ * curv H z ξ₂ η₂).trace + (curv H z ξ₂ η₂ * curv H z ξ₁ η₁).trace
        - (curv H z ξ₁ η₂ * curv H z ξ₂ η₁).trace - (curv H z ξ₂ η₁ * curv H z ξ₁ η₂).trace) := by
  simp only [chTwo, wedge, Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]

variable {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]

theorem trace_mul_eq_blocks (H K K' : Matrix (m ⊕ l) (m ⊕ l) ℂ) :
    (K * K').trace = (blockSS H K * blockSS H K').trace + (blockSQ H K * blockQS K').trace +
      (blockQS K * blockSQ H K').trace + (blockQQ H K * blockQQ H K').trace := by
  have hP := incl_mul_orthProj_add (m := m) (l := l) H
  have e : K * K' = K * (incl m l * orthProj H + orthLift H * quotMap m l) * K' *
      (incl m l * orthProj H + orthLift H * quotMap m l) := by rw [hP]; simp
  rw [e]
  simp only [blockSS, blockSQ, blockQS, blockQQ, Matrix.mul_add, Matrix.add_mul, Matrix.trace_add,
    Matrix.mul_assoc, Matrix.trace_mul_comm (orthProj H), Matrix.trace_mul_comm (quotMap m l)]
  ring

section Deriv

variable {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V}

theorem ddbar_extTrace (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det)
    (hz : z ∈ U) (ξ η ξ' η' : V) :
    ddbar (fun x => extTrace H x ξ' η') z ξ η = kappa *
      ((mdbar (fun x => homDel (gramS H) (gramQ H) (fun y => extFormAdj H y ξ') x ξ) z η *
          extForm H z η').trace +
        (homDel (gramS H) (gramQ H) (fun y => extFormAdj H y ξ') z ξ *
          mdbar (fun y => extForm H y η') z η).trace +
        (mdbar (fun y => extFormAdj H y ξ') z η *
          homDel (gramQ H) (gramS H) (fun y => extForm H y η') z ξ).trace +
        (extFormAdj H z ξ' *
          (homDel (gramQ H) (gramS H) (fun x => mdbar (fun y => extForm H y η') x η) z ξ -
            curv (gramS H) z ξ η * extForm H z η' + extForm H z η' * curv (gramQ H) z ξ η)).trace) := by
  have hS := h.sub hs
  have hQ := h.quot hs
  have hSu : ∀ x ∈ U, IsUnit (gramS H x).det := hs
  have hQu : ∀ x ∈ U, IsUnit (gramQ H x).det := fun x hx => hQ.isUnit x hx
  have sγ : ∀ x ∈ U, MContDiffAt ∞ (fun y => extFormAdj H y ξ') x := fun x hx =>
    GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm.smooth_extFormAdj h hs hx ξ'
  have sβ : ∀ x ∈ U, MContDiffAt ∞ (fun y => extForm H y η') x := fun x hx =>
    GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm.smooth_extForm h hs hx η'
  have one : ∀ {p q : Type} {F : V → Matrix p q ℂ} {x : V}, MContDiffAt ∞ F x →
      MContDiffAt 1 F x := fun hF => hF.of_le (by norm_cast)
  have two : ∀ {p q : Type} {F : V → Matrix p q ℂ} {x : V}, MContDiffAt ∞ F x →
      MContDiffAt 2 F x := fun hF => hF.of_le (by norm_cast)
  have htr : ContDiffAt ℝ 2 (fun x => (extFormAdj H x ξ' * extForm H x η').trace) z := by
    have hM := (two (sγ z hz)).mul (two (sβ z hz))
    simp only [Matrix.trace, Matrix.diag]
    exact ContDiffAt.sum fun a _ => hM a a
  have e : (fun x => extTrace H x ξ' η') =
      fun x => kappa • (extFormAdj H x ξ' * extForm H x η').trace := rfl
  rw [e, ddbar_const_smul kappa htr, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, ddbar_eq_dbar_del htr]
  congr 1
  have ev : (fun x => del (fun y => (extFormAdj H y ξ' * extForm H y η').trace) x ξ) =ᶠ[𝓝 z]
      fun x => (homDel (gramS H) (gramQ H) (fun y => extFormAdj H y ξ') x ξ * extForm H x η').trace +
        (extFormAdj H x ξ' * homDel (gramQ H) (gramS H) (fun y => extForm H y η') x ξ).trace := by
    filter_upwards [h.isOpen.mem_nhds hz] with x hx
    exact del_trace_mul (one (sγ x hx)) (one (sβ x hx)) ξ
  have hD1 : MContDiffAt 1 (fun x => homDel (gramS H) (gramQ H) (fun y => extFormAdj H y ξ') x ξ) z :=
    mContDiffAt_homDel (hS.mContDiffAt hz) (hSu z hz) (hQ.mContDiffAt hz) (hQu z hz) (sγ z hz) ξ
  have hD2 : MContDiffAt 1 (fun x => homDel (gramQ H) (gramS H) (fun y => extForm H y η') x ξ) z :=
    mContDiffAt_homDel (hQ.mContDiffAt hz) (hQu z hz) (hS.mContDiffAt hz) (hSu z hz) (sβ z hz) ξ
  have dtr : ∀ {F : V → Matrix l m ℂ} {G : V → Matrix m l ℂ}, MContDiffAt 1 F z →
      MContDiffAt 1 G z → DifferentiableAt ℝ (fun x => (F x * G x).trace) z := fun hF hG => by
    have hM := hF.mul hG
    simp only [Matrix.trace, Matrix.diag]
    exact DifferentiableAt.fun_sum fun a _ => hM.diff a a
  rw [dbar_congr ev, dbar_add (dtr hD1 (one (sβ z hz))) (dtr (one (sγ z hz)) hD2),
    ContinuousLinearMap.add_apply, dbar_trace_mul hD1 (one (sβ z hz)),
    dbar_trace_mul (one (sγ z hz)) hD2,
    mdbar_homDel (A := gramQ H) (B := gramS H) (two (hQ.mContDiffAt hz)) (hQu z hz) (two (hS.mContDiffAt hz)) (hSu z hz)
      (two (sβ z hz)) ξ η]
  ring

end Deriv

theorem ddcForm_extTrace_eq : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m]
    [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsHermFrame U H)
    (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U) (hb : ∀ x ∈ U, ExtBlocksAt H x)
    (ξ₁ η₁ ξ₂ η₂ : V), ddcForm (extTrace H) z ξ₁ η₁ ξ₂ η₂ =
      chTwo (gramS H) z ξ₁ η₁ ξ₂ η₂ + chTwo (gramQ H) z ξ₁ η₁ ξ₂ η₂ - chTwo H z ξ₁ η₁ ξ₂ η₂ := by
  intro V _ _ _ _ m l _ _ _ _ U H z h hs hz hb ξ₁ η₁ ξ₂ η₂
  have hU : U ∈ 𝓝 z := h.isOpen.mem_nhds hz

  have hFD : ∀ η, mdbar (fun x => homDel (gramS H) (gramQ H) (fun y => extFormAdj H y ξ₂) x ξ₁) z η =
      mdbar (fun x => homDel (gramS H) (gramQ H) (fun y => extFormAdj H y ξ₁) x ξ₂) z η := by
    intro η
    refine mdbar_congr ?_ η
    filter_upwards [hU] with x hx
    exact sub_eq_zero.1 ((hb x hx).2.2.2.2.2.2.2.2 ξ₁ ξ₂)
  have hG : homDel (gramS H) (gramQ H) (fun y => extFormAdj H y ξ₂) z ξ₁ =
      homDel (gramS H) (gramQ H) (fun y => extFormAdj H y ξ₁) z ξ₂ :=
    sub_eq_zero.1 ((hb z hz).2.2.2.2.2.2.2.2 ξ₁ ξ₂)
  have hBd : mdbar (fun y => extForm H y η₂) z η₁ = mdbar (fun y => extForm H y η₁) z η₂ :=
    sub_eq_zero.1 ((hb z hz).2.2.2.2.2.2.2.1 η₁ η₂)
  have hHm : ∀ ξ, homDel (gramQ H) (gramS H) (fun x => mdbar (fun y => extForm H y η₂) x η₁) z ξ =
      homDel (gramQ H) (gramS H) (fun x => mdbar (fun y => extForm H y η₁) x η₂) z ξ := by
    intro ξ
    have ev : (fun x => mdbar (fun y => extForm H y η₂) x η₁) =ᶠ[𝓝 z]
        fun x => mdbar (fun y => extForm H y η₁) x η₂ := by
      filter_upwards [hU] with x hx
      exact sub_eq_zero.1 ((hb x hx).2.2.2.2.2.2.2.1 η₁ η₂)
    simp only [homDel]
    rw [mdel_congr ev ξ, hBd]

  obtain ⟨-, -, -, hSS, hSQ, hQS, hQQ, -, -⟩ := hb z hz
  have hK : ∀ ξ η ξ' η', (curv H z ξ η * curv H z ξ' η').trace =
      ((curv (gramS H) z ξ η + extForm H z η * extFormAdj H z ξ) *
        (curv (gramS H) z ξ' η' + extForm H z η' * extFormAdj H z ξ')).trace +
      (homDel (gramQ H) (gramS H) (fun y => extForm H y η) z ξ *
        mdbar (fun y => extFormAdj H y ξ') z η').trace +
      (mdbar (fun y => extFormAdj H y ξ) z η *
        homDel (gramQ H) (gramS H) (fun y => extForm H y η') z ξ').trace +
      ((curv (gramQ H) z ξ η - extFormAdj H z ξ * extForm H z η) *
        (curv (gramQ H) z ξ' η' - extFormAdj H z ξ' * extForm H z η')).trace := by
    intro ξ η ξ' η'
    rw [trace_mul_eq_blocks (H z)]
    simp only [hSS, hSQ, hQS, hQQ, wedgeAntiHol, wedgeHolAnti, covDelAnti, dbarHol, neg_neg,
      sub_neg_eq_add]

  have c1 : ∀ (X : Matrix m m ℂ) (P : Matrix m l ℂ) (Q : Matrix l m ℂ),
      (X * (P * Q)).trace = (Q * (X * P)).trace := fun X P Q => by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
  have c3 : ∀ (Y : Matrix l l ℂ) (Q : Matrix l m ℂ) (P : Matrix m l ℂ),
      (Y * (Q * P)).trace = (Q * (P * Y)).trace := fun Y Q P => by
    rw [Matrix.trace_mul_comm, Matrix.mul_assoc]
  have c4 : ∀ (P : Matrix m l ℂ) (Q : Matrix l m ℂ), (P * Q).trace = (Q * P).trace :=
    fun P Q => Matrix.trace_mul_comm P Q
  simp only [ddcForm, ddbar_extTrace h hs hz, chTwo_eq_trace, hK]
  simp only [hFD, hG, hBd, hHm]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_add,
    Matrix.trace_sub, Matrix.mul_assoc]
  simp only [c1, c3, c4, Matrix.mul_assoc]
  ring

end GlobalTheory.SubQuotChTwo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteFormStabilizerFiniteAwayFromP
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.DefStab

variable {p : ℕ} [Fact p.Prime]

theorem psi_bound (G : HTGroup p) (B : GlobalTheory.LKDef.DForm G) : ∃ K : ℝ, ∀ y : GlobalTheory.LKCx.grp G B.β,
    ∀ (w : InfinitePlace G.F) (a b : Fin G.n), ‖G.psi w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) a b‖ ≤
      K * Real.sqrt ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) := by
  let f : InfinitePlace G.F → (Fin G.n → ℂ) → ℝ := fun w x =>
    if sigPosH (G.gram_herm w) = 1 then (star x ⬝ᵥ GlobalTheory.LKCx.herm G w B.β *ᵥ x).re
    else -(star x ⬝ᵥ GlobalTheory.LKCx.herm G w B.β *ᵥ x).re
  have hK : ∀ w, ∃ K : ℝ, ∀ (A : Matrix (Fin G.n) (Fin G.n) ℂ) (s : ℝ), 0 ≤ s →
      (∀ x, f w (A *ᵥ x) = s * f w x) → ∀ a b, ‖A a b‖ ≤ K * Real.sqrt s := by
    intro w
    apply GlobalTheory.LKCx.PsiBound.bound_of_form
    · by_cases h : sigPosH (G.gram_herm w) = 1
      · simp only [f, h, if_true]; fun_prop
      · simp only [f, h, if_false]; fun_prop
    · intro t x
      by_cases h : sigPosH (G.gram_herm w) = 1
      · simp only [f, h, if_true]; rw [GlobalTheory.LKCx.PsiBound.form_smul, Complex.re_ofReal_mul]
      · simp only [f, h, if_false]; rw [GlobalTheory.LKCx.PsiBound.form_smul, Complex.re_ofReal_mul]; ring
    · intro x hx
      have hp := B.posR w x hx
      by_cases h : sigPosH (G.gram_herm w) = 1
      · simp only [f, h, if_true]; exact hp.1 h
      · have h2 : (star x ⬝ᵥ GlobalTheory.LKCx.herm G w B.β *ᵥ x).re < 0 := hp.2 h
        simp only [f, h, if_false]; linarith
  choose K hK using hK
  refine ⟨∑ w, |K w|, fun y w a b => ?_⟩
  set s : ℝ := ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) with hs
  have hs0 : 0 < s := by rw [hs]; exact_mod_cast y.2.2
  set A := G.psi w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) with hA
  have hsim : ∀ x : Fin G.n → ℂ, star (A *ᵥ x) ⬝ᵥ GlobalTheory.LKCx.herm G w B.β *ᵥ (A *ᵥ x) =
      (s : ℂ) * (star x ⬝ᵥ GlobalTheory.LKCx.herm G w B.β *ᵥ x) := by
    intro x
    have h := GlobalTheory.LKCx.grp_similitude_herm p G w B.β y
    have h' : Aᴴ * GlobalTheory.LKCx.herm G w B.β * A =
        (((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ)) : ℂ) • GlobalTheory.LKCx.herm G w B.β := h
    rw [← GlobalTheory.LKCx.PsiBound.form_conj, h', smul_mulVec, dotProduct_smul, smul_eq_mul, hs, Complex.ofReal_ratCast]
  have hinv : ∀ x, f w (A *ᵥ x) = s * f w x := by
    intro x
    by_cases h : sigPosH (G.gram_herm w) = 1
    · simp only [f, h, if_true]; rw [hsim, Complex.re_ofReal_mul]
    · simp only [f, h, if_false]; rw [hsim, Complex.re_ofReal_mul]; ring
  calc ‖A a b‖ ≤ K w * Real.sqrt s := hK w A s hs0.le hinv a b
    _ ≤ |K w| * Real.sqrt s := mul_le_mul_of_nonneg_right (le_abs_self _) (Real.sqrt_nonneg _)
    _ ≤ (∑ u, |K u|) * Real.sqrt s := mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (f := fun u => |K u|) (fun u _ => abs_nonneg _) (Finset.mem_univ w))
        (Real.sqrt_nonneg _)

theorem isTest_indicator_comm (G : HTGroup p) (K' : Subgroup (Gr G 1))
    (hK : Subgroup.Commensurable K' (KHT p G.m G.n 1 G.Fw)) :
    IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' (Set.indicator (K' : Set (Gr G 1)) 1) := by
  have hθ : ∀ g, sigG G 1 g = g := GlobalTheory.LKCx.sigG_one G
  refine ⟨hK, ?_, fun k hk g => ?_, ?_⟩
  · rintro _ ⟨k, hk, rfl⟩; rw [hθ]; exact hk
  · rw [hθ]
    by_cases hg : g ∈ K'
    · have h' : k⁻¹ * g * k ∈ K' := K'.mul_mem (K'.mul_mem (K'.inv_mem hk) hg) hk
      simp [Set.indicator_apply, hg, h']
    · have h' : k⁻¹ * g * k ∉ K' := fun h => hg (by
        have e : g = k * (k⁻¹ * g * k) * k⁻¹ := by group
        rw [e]; exact K'.mul_mem (K'.mul_mem hk h) (K'.inv_mem hk))
      simp [Set.indicator_apply, hg, h']
  · set K₀ := KHT p G.m G.n 1 G.Fw
    haveI : (K₀.subgroupOf K').FiniteIndex := ⟨hK.2⟩
    haveI : Finite (K' ⧸ K₀.subgroupOf K') := Subgroup.finite_quotient_of_finiteIndex
    haveI : Fintype (K' ⧸ K₀.subgroupOf K') := Fintype.ofFinite _
    refine ⟨Finset.univ.image fun q : K' ⧸ K₀.subgroupOf K' => ((Quotient.out q : K') : Gr G 1), fun g hg => ?_⟩
    have hgK : g ∈ K' := by
      by_contra hn; exact hg (by simp [Set.indicator_apply, hn])
    set q : K' ⧸ K₀.subgroupOf K' := QuotientGroup.mk ⟨g, hgK⟩
    have hq : (Quotient.out q)⁻¹ * (⟨g, hgK⟩ : K') ∈ K₀.subgroupOf K' := by
      rw [← QuotientGroup.eq, QuotientGroup.out_eq']
    rw [Subgroup.mem_subgroupOf] at hq
    refine ⟨((Quotient.out q : K') : Gr G 1), Finset.mem_image_of_mem _ (Finset.mem_univ _), 1, K₀.one_mem, _, hq,
      ?_⟩
    simp

theorem finite_locPart : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ (L : G.Level) (K' : Subgroup (Gr G 1)),
    Subgroup.Commensurable K' (KHT p G.m G.n 1 G.Fw) → ∀ (B : GlobalTheory.LKDef.DForm G) (x : G.GAf × Gr G 1),
    Finite (GlobalTheory.LKLoc.locPart B.emb.range (L.K.toSubgroup.prod K') x) := by
  intro p _ G _ L K' hK B x
  have hp : p.Prime := Fact.out
  obtain ⟨xx, tt, hx, heq⟩ : ∃ (xx : (AfP p ⊗[ℚ] G.C)ˣ) (tt : (AfP p)ˣ) (hx : Triv G (AfP p) B.β xx tt),
      B.emb = B.embAt xx tt hx := ⟨_, _, B.trivAf.choose_spec.choose_spec, rfl⟩
  set fK : G.GAf → ℂ := Set.indicator (L.K.toSubgroup : Set G.GAf) 1 with hfK
  set fK' : Gr G 1 → ℂ := Set.indicator (K' : Set (Gr G 1)) 1 with hfK'
  have hf : IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup fK := isTest_indicator _ _ (by simp)
  have hf' : IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' fK' := isTest_indicator_comm G K' hK
  set S : Set (GlobalTheory.LKCx.grp G B.β) := {y | fK (x.1⁻¹ * GlobalTheory.LKCx.toAfF G B.β xx tt hx y * x.1) ≠ 0 ∧
    fK' (x.2⁻¹ * GlobalTheory.LKCx.toP1 G B.β y * x.2) ≠ 0} with hS
  have hSfin : S.Finite := by
    obtain ⟨D, hD, hAf⟩ := GlobalTheory.LKCx.BoundedDen.main p G B.β xx tt hx L fK hf x.1
    obtain ⟨k, hP⟩ := GlobalTheory.AtP.main p G B.β K' fK' hf' x.2
    obtain ⟨R, hR⟩ := GlobalTheory.CoordArch.coord_bound p G
    obtain ⟨Kb, hKb⟩ := psi_bound G B
    obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = D * p ^ k := ⟨_, rfl⟩
    have hN : 0 < N := hNdef ▸ Nat.mul_pos hD (pow_pos hp.pos k)
    obtain ⟨R', hR'⟩ : ∃ R' : ℝ,
        R' = |R| * (Fintype.card (InfinitePlace G.F) * G.n * G.n * (max Kb 0 * Real.sqrt N)) := ⟨_, rfl⟩
    let φ : GlobalTheory.LKCx.grp G B.β → (Fin (Module.finrank ℚ G.C) → ℚ) :=
      fun y => (Module.finBasis ℚ G.C).repr (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)
    have hφ : Function.Injective φ := fun y y' h =>
      GlobalTheory.FinFix.grp_val_injective G B.β ((Module.finBasis ℚ G.C).repr.injective (Finsupp.ext fun i => congrFun h i))
    refine Set.Finite.subset
      (Set.Finite.preimage hφ.injOn (Set.Finite.pi fun _ => GlobalTheory.FinFix.finite_den_bdd N hN R')) ?_
    rintro y ⟨hf1, hf2⟩
    have hs : (0 : ℚ) < (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) := y.2.2
    obtain ⟨m, hm⟩ := GlobalTheory.FinFix.exists_int_of_den_le (p := p) D k hD ((((y : G.Cˣ × ℚˣ).2)⁻¹ : ℚˣ) : ℚ)
      (fun ℓ hℓ => (hAf y hf1 ℓ hℓ).2) (hP y hf2).2
    have hsN : ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) ≤ N := by
      have hm' : ((N : ℚ)) * ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ))⁻¹ = m := by
        rw [hNdef, ← hm, Units.val_inv_eq_inv_val]
      have hmpos : (0 : ℚ) < m := by
        rw [← hm']; exact mul_pos (by exact_mod_cast hN) (inv_pos.2 hs)
      have hm1 : (1 : ℚ) ≤ m := by exact_mod_cast (show (0 : ℤ) < m by exact_mod_cast hmpos)
      have h2 : (1 : ℚ) ≤ (N : ℚ) * ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ))⁻¹ := hm' ▸ hm1
      have h3 : (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) ≤ N := by
        have := mul_le_mul_of_nonneg_right h2 hs.le
        rwa [one_mul, mul_assoc, inv_mul_cancel₀ hs.ne', mul_one] at this
      exact_mod_cast h3
    intro i _
    obtain ⟨m2, hm2⟩ := GlobalTheory.FinFix.exists_int_of_den_le (p := p) D k hD (φ y i)
      (fun ℓ hℓ => (hAf y hf1 ℓ hℓ).1 i) ((hP y hf2).1 i)
    refine ⟨⟨m2, ?_⟩, ?_⟩
    · rw [hNdef, mul_comm]; exact hm2
    · show |((φ y i : ℚ) : ℝ)| ≤ R'
      refine (hR _ i).trans ?_
      have hb : ∀ w a b, ‖G.psi w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) a b‖ ≤ max Kb 0 * Real.sqrt N := by
        intro w a b
        exact (hKb y w a b).trans
          (mul_le_mul (le_max_left _ _) (Real.sqrt_le_sqrt hsN) (Real.sqrt_nonneg _) (le_max_right _ _))
      have hsum : ∑ w : InfinitePlace G.F, ∑ a : Fin G.n, ∑ b : Fin G.n,
          ‖G.psi w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) a b‖ ≤
          Fintype.card (InfinitePlace G.F) * G.n * G.n * (max Kb 0 * Real.sqrt N) := by
        calc _ ≤ ∑ w : InfinitePlace G.F, ∑ a : Fin G.n, ∑ b : Fin G.n, max Kb 0 * Real.sqrt N :=
              Finset.sum_le_sum fun w _ => Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hb w a b
          _ = _ := by simp [Finset.sum_const, Finset.card_univ]; ring
      have hnn : 0 ≤ ∑ w : InfinitePlace G.F, ∑ a : Fin G.n, ∑ b : Fin G.n,
          ‖G.psi w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) a b‖ := by positivity
      rw [hR']
      calc R * _ ≤ |R| * _ := mul_le_mul_of_nonneg_right (le_abs_self R) hnn
        _ ≤ _ := mul_le_mul_of_nonneg_left hsum (abs_nonneg R)
  have hsub : ((GlobalTheory.LKLoc.locPart B.emb.range (L.K.toSubgroup.prod K') x : Subgroup (G.GAf × Gr G 1)) :
      Set (G.GAf × Gr G 1)) ⊆ B.emb '' S := by
    intro e he
    rw [SetLike.mem_coe, GlobalTheory.LKLoc.locPart, Subgroup.mem_inf, MonoidHom.mem_range, Subgroup.mem_map] at he
    obtain ⟨⟨y, rfl⟩, ⟨c, hc, hce⟩⟩ := he
    rw [Subgroup.mem_prod] at hc
    have hc' : x⁻¹ * B.emb y * x = c := by
      rw [← hce]; simp [MulAut.conj_apply, mul_assoc]
    have he1 : (B.emb y).1 = GlobalTheory.LKCx.toAfF G B.β xx tt hx y := by rw [heq]; rfl
    have he2 : (B.emb y).2 = GlobalTheory.LKCx.toP1 G B.β y := by rw [heq]; rfl
    have h1 : x.1⁻¹ * GlobalTheory.LKCx.toAfF G B.β xx tt hx y * x.1 = c.1 := by
      rw [← he1, ← hc']; rfl
    have h2 : x.2⁻¹ * GlobalTheory.LKCx.toP1 G B.β y * x.2 = c.2 := by
      rw [← he2, ← hc']; rfl
    refine ⟨y, ⟨?_, ?_⟩, rfl⟩
    · rw [hfK, h1, Set.indicator_of_mem hc.1]; exact one_ne_zero
    · rw [hfK', h2, Set.indicator_of_mem hc.2]; exact one_ne_zero
  exact ((hSfin.image _).subset hsub).to_subtype

end GlobalTheory.DefStab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteUnitaryFinitePartMulInjectiveRange
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.FinPart

open GlobalTheory.DefU.ClassFin

section Ring

variable {R S : Type} [CommRing R] [CommRing S] {n : ℕ}

def tw (n : ℕ) (c : R →+* R) : GL (Fin n) R →* GL (Fin n) R := (invT n R).comp (GeneralLinearGroup.map c)

theorem tw_inv_val (c : R →+* R) (g : GL (Fin n) R) : ((tw n c g)⁻¹).val = cT c g.val := rfl

theorem tw_eq_iff (c : R →+* R) (g : GL (Fin n) R) : tw n c g = g ↔ cT c g.val * g.val = 1 := by
  rw [← tw_inv_val, ← Units.val_mul, Units.val_eq_one, inv_mul_eq_one]

theorem map_tw (p : R →+* S) (c : R →+* R) (d : S →+* S) (h : ∀ y, p (c y) = d (p y)) (g : GL (Fin n) R) :
    GeneralLinearGroup.map p (tw n c g) = tw n d (GeneralLinearGroup.map p g) := by
  apply Units.ext
  ext i j
  exact h _

end Ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def pU : finU E n →* GL (Fin n) (Af E) :=
  ((GeneralLinearGroup.map (pFin E)).comp (UA E n).subtype).comp (finU E n).subtype

theorem finGL_pU (k : finU E n) : finGL E n (pU k) = k.1.1 := finGL_pFin k

theorem pU_injective : Function.Injective (pU (E := E) (n := n)) := fun a b h =>
  Subtype.ext (Subtype.ext (by rw [← finGL_pU, h, finGL_pU]))

theorem tw_pU (k : finU E n) : tw n (conjFin (cc E)) (pU k) = pU k := (tw_eq_iff _ _).2 (cT_pFin k.1)

def sU (g : GL (Fin n) (Af E)) (h : tw n (conjFin (cc E)) g = g) : finU E n :=
  ⟨⟨finGL E n g, finGL_mem_UA _ ((tw_eq_iff _ _).1 h)⟩, pInf_finGL _⟩

theorem pU_sU (g : GL (Fin n) (Af E)) (h : tw n (conjFin (cc E)) g = g) : pU (sU g h) = g := pFin_finGL g

theorem ratF_tw (g : GL (Fin n) E) :
    ratF E n (tw n (cc E).toRingHom g) = tw n (conjFin (cc E)) (ratF E n g) :=
  map_tw _ _ _ (fun y => (conjFin_algebraMap (cc E) y).symm) g

theorem mem_UE (g : GL (Fin n) E) : g ∈ UE E n ↔ tw n (cc E).toRingHom g = g := by
  rw [tw_eq_iff]
  change cT _ g.val * 1 * g.val = 1 ↔ _
  rw [mul_one]

theorem ratF_injective : Function.Injective (ratF E n) := fun a b h => by
  apply Units.ext
  ext i j
  obtain ⟨w⟩ : Nonempty (HeightOneSpectrum (𝓞 E)) := by
    obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 E)
    exact ⟨⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField E)⟩⟩
  haveI : Nontrivial (Af E) := (pLoc E w).domain_nontrivial
  have h' : (ratF E n a).val = (ratF E n b).val := congrArg Units.val h
  exact (algebraMap E (Af E)).injective (congrFun₂ h' i j)

theorem pU_finPt (γ : UE E n) : pU (finPt γ) = ratF E n γ.1 := by
  have h : tw n (conjFin (cc E)) (ratF E n γ.1) = ratF E n γ.1 := by rw [← ratF_tw, (mem_UE _).1 γ.2]
  have e : finPt γ = sU _ h := by
    have h1 : toSub (UA E n) (finGL E n (ratF E n γ.1)) = (sU _ h).1 := dif_pos (sU _ h).1.2
    rw [finPt, h1]
    exact dif_pos (sU _ h).2
  rw [e, pU_sU]

theorem mem_ratFinU (k : finU E n) : k ∈ ratFinU E n ↔ pU k ∈ (ratF E n).range := by
  constructor
  · rintro ⟨g, -, hg⟩
    exact ⟨g, (pFin_finGL _).symm.trans (congrArg (GeneralLinearGroup.map (pFin E)) hg)⟩
  · rintro ⟨g, hg⟩
    refine ⟨g, (mem_UE g).2 (ratF_injective ?_), (congrArg (finGL E n) hg).trans (finGL_pU k)⟩
    rw [ratF_tw, hg, tw_pU]

theorem finPt_props : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), (∀ a b : UE E n, finPt (a * b) = finPt a * finPt b) ∧ Function.Injective (finPt : UE E n → finU E n) ∧ ∀ x : finU E n, x ∈ ratFinU E n ↔ ∃ γ : UE E n, finPt γ = x := by
  intro E _ _ _ n
  refine ⟨fun a b => pU_injective ?_, fun a b h => Subtype.ext (ratF_injective ?_), fun x => ?_⟩
  · rw [map_mul, pU_finPt, pU_finPt, pU_finPt, Subgroup.coe_mul, map_mul]
  · rw [← pU_finPt, ← pU_finPt, h]
  · rw [mem_ratFinU]
    constructor
    · rintro ⟨g, hg⟩
      have hU : g ∈ UE E n := (mem_UE g).2 (ratF_injective (by rw [ratF_tw, hg, tw_pU]))
      exact ⟨⟨g, hU⟩, pU_injective (by rw [pU_finPt, hg])⟩
    · rintro ⟨γ, rfl⟩
      exact ⟨γ.1, (pU_finPt γ).symm⟩

end GlobalTheory.BCT.FinPart
end
end

