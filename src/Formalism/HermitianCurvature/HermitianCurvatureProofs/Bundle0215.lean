import Formalism.HermitianCurvature.StatementHeads
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0156
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0201
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0050
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0204
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0207
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0203

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PbRadHeadOf
section
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBP

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5

section smul

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]

theorem act_smul' (M : Wd.SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))) (x : Wd.Ix S → RadSp k r z z' π π') (a : ℂ) :
    P5.act M (fun e => a • x e) = fun e => a • P5.act M x e := by
  funext e
  simp only [P5.act, map_smul, Finset.smul_sum]

theorem rrform_smul (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (st : Fr.Start (Pr (RadSp k r z z' π π')))
    (μ : Measure (Mt k r)) (i : Fin (r + 1)) (w : List (Wd.Letter ℂ S)) (x y : Wd.Ix S → RadSp k r z z' π π')
    (c : Fin r → ℂ) (a : ℂ) :
    P5.RRform L st μ i w (fun e => a • x e) (fun e => a • y e) c = a * conj a * P5.RRform L st μ i w x y c := by
  unfold P5.RRform
  rw [act_smul']
  unfold P5.form
  rw [← integral_const_mul]
  congr 1
  funext c'
  simp only [HerA.pairAt_smul_left, HerA.pairAt_smul_right, ← Finset.mul_sum]
  ring

end smul

theorem isLocPt_snoc {h : C.LPt} {j : ℕ} (hh : D.IsLocPt h j) {t : ℂ} (ht : t ≠ 0) :
    D.IsLocPt (h ++ [(1, t)]) (j + 1) := by
  obtain ⟨h1, h2⟩ := hh
  refine ⟨fun b hb => ?_, ?_⟩
  · rcases List.mem_append.1 hb with hb | hb
    · exact h1 b hb
    · rw [List.mem_singleton] at hb
      subst hb
      exact ⟨le_rfl, ht⟩
  · unfold D.ptSize at h2 ⊢
    rw [List.map_append, List.sum_append, h2]
    simp

theorem levW_below (P : M.Par) (j : ℕ) (hj : j + 1 ≤ P.r) {t : ℂ} (ht : t ≠ 0) :
    ‖t‖ ^ (-2 : ℤ) * (‖t‖ ^ (2 * (P.r - j) + P.k)) ^ 2 = KB.levW P (j + 1) t := by
  have hj' : j + 1 ≠ P.r + 1 := by omega
  unfold KB.levW
  rw [if_neg hj']
  have ht' : ‖t‖ ≠ 0 := norm_ne_zero_iff.2 ht
  rw [← pow_mul, ← zpow_natCast, ← zpow_add₀ ht']
  congr 1
  unfold C.Mlev
  push_cast [Nat.cast_sub (show j ≤ P.r by omega)]
  ring

end Formalism.FourierDecayAlt.P.PBP

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.PBP

theorem pb_radHead_of (hOne : PBO.FormOne) (hZN : PBO.ZetaNormExists) (hHP : HeadPic) : KB.RadHead := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj w h h' hh hh' X μ L st Φ Φ' hD hZ hF hw hΦ hΦ' t ht
  let jF : Fin (P.r + 1) := ⟨j + 1, by omega⟩
  have hPl := Formalism.FourierDecayAlt.P.JCTx5.isPlace_lev P p.T jF p.hP
  obtain ⟨Xs⟩ := Formalism.FourierDecayAlt.P.actual_operators_exist _ _ _ _ _ _ _ hPl
  obtain ⟨Ls, sts, h1, h2, h3, h4, h5, h6⟩ := Formalism.FourierDecayAlt.P.level_start_actual _ _ _ _ _ _ _ hPl Xs p.l0
  obtain ⟨μs, hμs⟩ := hZN P.k (P.r - (j + 1)) Wp Wq (p.T.bs (j + 1))
  have hDs : IsData (JC.parLev P jF) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π' Xs μs Ls sts p.l0 :=
    ⟨hPl, hμs.1, h1, h2, h3, h4, h5, h6⟩
  obtain ⟨T, hT, hph⟩ :=
    Formalism.FourierDecayAlt.P.radial_transport_plus Wp Wq P p j hj X μ L st Xs μs Ls sts hD hZ hDs hμs t ht
  refine (hph (Fin w.length) (D.positionted w) Φ Φ' (fun _ => 1) 0).trans ?_
  have hl := isLocPt_snoc hh ht
  have hl' := isLocPt_snoc hh' ht

  set x2 := KB.slv p.T F (j + 1) hj w (h ++ [(1, t)]) hl.2 with hx2def
  set x2' := KB.slv p.T F (j + 1) hj w (h' ++ [(1, t)]) hl'.2 with hx2'def
  have hc2 : ∀ e, KB.CptCoef (p.T.bs (j + 1)) (x2 e) := fun e =>
    Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F (j + 1) hj w _ hl hF e
  have hc2' : ∀ e, KB.CptCoef (p.T.bs (j + 1)) (x2' e) := fun e =>
    Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F (j + 1) hj w _ hl' hF e
  obtain ⟨ε₁, hε₁, hx⟩ := PBO.nice_common (p.T.bs (j + 1)) hc2
  obtain ⟨ε₂, hε₂, hx'⟩ := PBO.nice_common (p.T.bs (j + 1)) hc2'
  have hε : 0 < min ε₁ ε₂ := lt_min hε₁ hε₂
  have mono : ∀ {ε' : ℝ} {G : B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp)}, min ε₁ ε₂ ≤ ε' →
      JC.NiceCoef (p.T.bs (j + 1)) ε' G → JC.NiceCoef (p.T.bs (j + 1)) (min ε₁ ε₂) G :=
    fun hle hG => ⟨hG.1, hG.2.1, fun g hg h0 => le_trans hle (hG.2.2 g hg h0)⟩
  have hxn : ∀ e, JC.NiceCoef (p.T.bs (j + 1)) (min ε₁ ε₂) (x2 e) := fun e => mono (min_le_left _ _) (hx e)
  have hxn' : ∀ e, JC.NiceCoef (p.T.bs (j + 1)) (min ε₁ ε₂) (x2' e) := fun e => mono (min_le_right _ _) (hx' e)

  set lam : ℝ := ‖t‖ ^ (2 * (P.r - j) + P.k) with hlam
  have hlam0 : lam ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 ht)
  have hlamC : ((lam : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hlam0
  let b0 : Fin (JC.parLev P j).r := ⟨0, by change 0 < P.r - j; omega⟩
  let Φ2 := fun e => (((lam⁻¹ : ℝ)) : ℂ) • T (P5.act (P5.bTl L b0 (D.positionted w)) Φ e)
  let Φ2' := fun e => (((lam⁻¹ : ℝ)) : ℂ) • T (P5.act (P5.bTl L b0 (D.positionted w)) Φ' e)
  have hpic : ∀ (hh₀ : C.LPt) (hhh : D.IsLocPt hh₀ j) (Ψ : Wd.Ix (Fin w.length) →
      Q.RadSp (JC.parLev P j).k (JC.parLev P j).r (p.T.bs j).z (p.T.bs j).z' (p.T.bs j).π (p.T.bs j).π'),
      (∀ e, Top.IsRadOf (JC.parLev P j) (p.T.bs j) (Ψ e) (KB.slv p.T F j (by omega) w hh₀ hhh.2 e)) →
      ∀ e, ∀ y ∈ Q.DomR (JC.parLev P jF).k (JC.parLev P jF).r (p.T.bs jF).z (p.T.bs jF).z',
        Subtype.val ((((lam⁻¹ : ℝ)) : ℂ) • T (P5.act (P5.bTl L b0 (D.positionted w)) Ψ e)) y.1 y.2 =
          Q.resG (JC.parLev P jF).k (JC.parLev P jF).r (Fin.last _)
            (B.JF (p.T.bs jF) (KB.slv p.T F (j + 1) hj w (hh₀ ++ [(1, t)]) (isLocPt_snoc hhh ht).2 e)) y.1 y.2 := by
    intro hh₀ hhh Ψ hΨ e y hy
    have e1 := hT (P5.act (P5.bTl L b0 (D.positionted w)) Ψ e) y.1 y.2
    have e2 := hHP Wp Wq P p F j hj w hh₀ hhh X μ L st Ψ hD hF hw hΨ t (isLocPt_snoc hhh ht) e y hy
    have hcl : ∀ v : Wq →L[ℂ] Wp, ((lam⁻¹ : ℝ) : ℂ) • (((lam : ℝ) : ℂ) • v) = v := fun v => by
      rw [smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hlam0, Complex.ofReal_one, one_smul]
    exact (congrArg (fun v => ((lam⁻¹ : ℝ) : ℂ) • v) (e1.trans e2)).trans (hcl _)
  have hΦ2 := hpic h hh Φ hΦ
  have hΦ2' := hpic h' hh' Φ' hΦ'
  have hOne' := hOne Wp Wq P p.T jF Xs μs Ls sts p.l0 hDs hμs w x2 x2' Φ2 Φ2' (min ε₁ ε₂) hε hxn hxn' hΦ2 hΦ2'
  have hTΦ : (fun a => T (P5.act (P5.bTl L b0 (D.positionted w)) Φ a)) = fun a => ((lam : ℝ) : ℂ) • Φ2 a := by
    funext a
    simp only [Φ2, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hlam0, Complex.ofReal_one, one_smul]
  have hTΦ' : (fun a => T (P5.act (P5.bTl L b0 (D.positionted w)) Φ' a)) = fun a => ((lam : ℝ) : ℂ) • Φ2' a := by
    funext a
    simp only [Φ2', smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hlam0, Complex.ofReal_one, one_smul]
  rw [hTΦ, hTΦ']
  have hRR : p.RR F (j + 1) w (h ++ [(1, t)]) (h' ++ [(1, t)]) = D.formLev p.T (M.sgn P p.l0) jF w x2 x2' := by
    unfold KB.Pl.RR D.RRplace
    rw [dif_pos ⟨hl, hl'⟩, dif_pos hj]
    rfl
  have key : P5.RRform Ls sts μs 0 (D.positionted w) Φ2 Φ2' 0 = D.formLev p.T (M.sgn P p.l0) jF w x2 x2' := hOne'.symm
  calc _ = ((‖t‖ ^ (-2 : ℤ) : ℝ) : ℂ) * ((lam : ℂ) * conj (lam : ℂ) * P5.RRform Ls sts μs 0 (D.positionted w) Φ2 Φ2' 0) :=
        congrArg _ (rrform_smul Ls sts μs 0 (D.positionted w) Φ2 Φ2' 0 (lam : ℂ))
    _ = ((‖t‖ ^ (-2 : ℤ) : ℝ) : ℂ) * ((lam : ℂ) * conj (lam : ℂ) * D.formLev p.T (M.sgn P p.l0) jF w x2 x2') := by
        rw [key]
    _ = _ := by
        rw [hRR, ← levW_below P j hj ht, Complex.conj_ofReal, hlam]
        push_cast
        ring

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PicMemUclsC
section
namespace Formalism.FourierDecayAlt.P.PBF

open Finset Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.Q Formalism.QuantumDeterminants
open scoped ComplexConjugate ComplexOrder

noncomputable section

section TowerC

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  {P0 : M.Par} {T : D.LevTower P0.k P0.r Wp Wq} {j : Fin (P0.r + 1)}

theorem transportC {X : ActualOps (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'}
    {μ : MeasureTheory.Measure (Mt (JC.parLev P0 j).k (JC.parLev P0 j).r)}
    {L : R.LevelData (Pr (RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'))
      (JC.parLev P0 j).r}
    {st : Fr.Start (Pr (RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'))}
    {l0 : ℕ} (hD : IsData (JC.parLev P0 j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' X μ L st l0)
    {ε : ℝ} (hε : 0 < ε) {F : B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)} (hF : JC.NiceCoef (T.bs j) ε F)
    (Φ : RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')
    (hΦ : IsPic T j Φ F) (Y : ℝ) (a b : Fin 2) {R : ℝ} (hRF : BSR R F) :
    ∃ F', JC.NiceCoef (T.bs j) ε F' ∧ BSR R F' ∧ IsPic T j ((QQi L st 0 (Y : ℂ) a b).1 Φ) F' := by
  let w : List C.Letter := [(true, Y)]
  let Fv : Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp) := Pi.single (eS 0 b) F
  have hFv : ∀ e, JC.NiceCoef (T.bs j) ε (Fv e) := by
    intro e
    by_cases h : e = eS 0 b
    · subst h; simpa [Fv] using hF
    · simp only [Fv, Pi.single_eq_of_ne h]; exact Formalism.FourierDecayAlt.P.JCx2.mn_nice_zero
  let xv : Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp) := fun e => B.JF (T.bs j) (Fv e)
  let Φv : Ix (Fin w.length) →
      RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' :=
    Pi.single (eS 0 b) Φ
  have hx : ∀ e, xv e ∈ FFl (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' 0
      (OmPlus (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z') := fun e =>
    Formalism.FourierDecayAlt.P.bessel_function_finite_class _ _ Wp Wq (T.bs j) (Fv e) ε hε (hFv e)
  have hΦv : ∀ e, ∀ y ∈ DomR (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z',
      (Φv e : Fn (JC.parLev P0 j).k (JC.parLev P0 j).r (Wq →L[ℂ] Wp)) y.1 y.2 =
        resG (JC.parLev P0 j).k (JC.parLev P0 j).r (Fin.last _) (xv e) y.1 y.2 := by
    intro e y hy
    by_cases h : e = eS 0 b
    · subst h
      have := hΦ y hy
      simp only [Φv, xv, Fv, Pi.single_eq_same]
      exact this
    · simp only [Φv, xv, Fv, Pi.single_eq_of_ne h]
      have h0 := congrFun (congrFun (resG_JF_zero (T.bs j) (Fin.last (JC.parLev P0 j).r)) y.1) y.2
      exact h0.symm
  have hRv : ∀ e, BSR R (Fv e) := by
    intro e
    by_cases h : e = eS 0 b
    · subst h; simpa [Fv] using hRF
    · simp only [Fv, Pi.single_eq_of_ne h]; exact fun g _ h0 => absurd rfl h0
  refine ⟨D.actOp (D.RRlev T (M.sgn P0 l0) j w) Fv (eS 0 a),
    Formalism.FourierDecayAlt.P.module_regularity Wp Wq P0 T (M.sgn P0 l0) j w Fv ε hε hFv (eS 0 a),
    (actOp_nice_bsr P0 T (M.sgn P0 l0) j w Fv hFv hRv (eS 0 a)).2, fun y hy => ?_⟩
  have hact := Formalism.FourierDecayAlt.P.radial_module_action Wp Wq P0 T j X μ L st l0 hD w xv Φv hx hΦv (eS 0 a) y hy
  have hbes := Formalism.FourierDecayAlt.P.bessel_module Wp Wq P0 T (M.sgn P0 l0) j w Fv ε hε hFv (eS 0 a) y hy
  have e : P5.act (RRi L st 0 (D.positionted w)) Φv (eS 0 a) = (QQi L st 0 (Y : ℂ) a b).1 Φ := by
    show actP (RRw (QQi L st 0) [(⟨true, 0, (Y : ℂ)⟩ : Letter ℂ (Fin 1))]) (Pi.single (eS 0 b) Φ) (eS 0 a) = _
    exact blockMulVec_one_letter _ _ _ _ _ _
  have e' := congrArg (fun Ψ : RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π
    (T.bs j).π' => (Ψ : Fn (JC.parLev P0 j).k (JC.parLev P0 j).r (Wq →L[ℂ] Wp)) y.1 y.2) e
  exact e'.symm.trans (hact.trans hbes.symm)

end TowerC

section ClsC

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  {P0 : M.Par} {T : D.LevTower P0.k P0.r Wp Wq} {j : Fin (P0.r + 1)}
  {X : ActualOps (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'}
  {μ : MeasureTheory.Measure (Mt (JC.parLev P0 j).k (JC.parLev P0 j).r)}
  {L : R.LevelData (Pr (RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'))
      (JC.parLev P0 j).r}
  {st : Fr.Start (Pr (RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'))}
  {l0 : ℕ}
  {K : Fin ((JC.parLev P0 j).r + 1) →
    Submodule ℂ (RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')}

def PicsInBS (T : D.LevTower P0.k P0.r Wp Wq) (j : Fin (P0.r + 1))
    (K0 : Submodule ℂ (RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')) :
    Prop :=
  ∀ (F : B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (ε R : ℝ), 0 < ε → JC.NiceCoef (T.bs j) ε F → BSR R F →
    ∃ Φ ∈ K0, ∀ x ∈ DomR (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z',
      (Φ : Fn (JC.parLev P0 j).k (JC.parLev P0 j).r (Wq →L[ℂ] Wp)) x.1 x.2 =
        resG (JC.parLev P0 j).k (JC.parLev P0 j).r (Fin.last (JC.parLev P0 j).r) (B.JF (T.bs j) F) x.1 x.2

theorem pic_mem_K0C (hJ : PicsInBS T j (K 0)) {ε R : ℝ} (hε : 0 < ε) {F : B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)}
    (hF : JC.NiceCoef (T.bs j) ε F) (hRF : BSR R F)
    (Φ : RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')
    (hΦ : IsPic T j Φ F) : Φ ∈ K 0 := by
  obtain ⟨Φ', hK, hΦ'⟩ := hJ F ε R hε hF hRF
  have e : Φ = Φ' := radSp_ext Φ Φ' (fun y hy => (hΦ y hy).trans (hΦ' y hy).symm)
  rw [e]; exact hK

theorem pic_mem_UclsC (hD : IsData (JC.parLev P0 j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' X μ L st l0)
    (hJ : PicsInBS T j (K 0)) (Pts : Set ℝ) {ε R : ℝ} (hε : 0 < ε) {F : B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)}
    (hF : JC.NiceCoef (T.bs j) ε F) (hRF : BSR R F)
    (Φ : RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')
    (hΦ : IsPic T j Φ F) : Φ ∈ Ucls (K 0) (Gen L st Pts) := by
  intro m hm
  have key : ∀ m ∈ Submonoid.closure (Gen L st Pts), ∀ (F : B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp))
      (Φ : RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'),
      JC.NiceCoef (T.bs j) ε F → BSR R F → IsPic T j Φ F →
      ∃ F', JC.NiceCoef (T.bs j) ε F' ∧ BSR R F' ∧ IsPic T j (m.1 Φ) F' := by
    intro m hm
    induction hm using Submonoid.closure_induction with
    | mem a ha =>
      intro F Φ hF hRF hΦ
      obtain ⟨Y, _, i, i', rfl⟩ := ha
      exact transportC hD hε hF Φ hΦ Y i i' hRF
    | one => intro F Φ hF hRF hΦ; exact ⟨F, hF, hRF, hΦ⟩
    | mul a b _ _ iha ihb =>
      intro F Φ hF hRF hΦ
      obtain ⟨F1, h1, hr1, h1'⟩ := ihb F Φ hF hRF hΦ
      obtain ⟨F2, h2, hr2, h2'⟩ := iha F1 _ h1 hr1 h1'
      exact ⟨F2, h2, hr2, h2'⟩
  obtain ⟨F', hF', hRF', hΦ'⟩ := key m hm F Φ hF hRF hΦ
  exact pic_mem_K0C hJ hε hF' hRF' _ hΦ'

end ClsC

end

end Formalism.FourierDecayAlt.P.PBF
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.RadAATopOfParts
section
open MeasureTheory Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBN

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def JAAop : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (u : ℂ), KB.CptCoef Bs F → ∀ g ∈ JF.Om k r Bs.z Bs.z',
    B.JF Bs (C3.AAop k r r le_rfl u F) g = C3.AAop k r r le_rfl u (B.JF Bs F) g

def AACell : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (f : B.Mat k r → E) (u : ℂ) (c : Fin r → ℂ)
    (g : B.Mat k r), g ∈ Q.Glev k r (Fin.last r) →
    C3.AAop k r r le_rfl u f (Q.wCell k r (Fin.last r) c * g) =
      (∏ a, c a) • qminorOp (EabH (Hpk k r)) (C3.xR k r r le_rfl) (C3.xR k r r le_rfl) u f
        (Q.wCell k r (Fin.last r) c * g)

def MinorCell : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (y : ℂ), KB.CptCoef Bs F → ∀ x ∈ Q.DomR k r Bs.z Bs.z',
    Q.resG k r (Fin.last r) (qminorOp (EabH (Hpk k r)) (C3.xR k r r le_rfl) (C3.xR k r r le_rfl)
        (y + ((2 * r + k : ℕ) : ℂ) / 2) (B.JF Bs F)) x.1 x.2 =
      Q.crd (Q.vAB r y r).1 (Q.resG k r (Fin.last r) (B.JF Bs F)) x.1 x.2

def RadSideA : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq)) (X : Q.ActualOps k r z z' π π')
    (L : R.LevelData (Q.Pr (Q.RadSp k r z z' π π')) r) (y : ℂ), Q.IsActualLevel X L →
    ∀ (Ψ : Q.RadSp k r z z' π π'), ∀ x ∈ Q.DomR k r z z',
      (((L.Ar y).1 Ψ : Q.RadSp k r z z' π π') : Q.Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 =
        Q.crd (Q.vAB r y r).1 (Ψ : Q.Fn k r (Wq →L[ℂ] Wp)) x.1 x.2

def AACpt : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (y : ℝ),
    KB.CptCoef Bs F → KB.CptCoef Bs (aaTop Bs y F)

def RadAATopOfParts : Prop := JAAop → AACell → MinorCell → RadSideA → AACpt → RadAATop

end Formalism.FourierDecayAlt.P.PBN
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.RightTypeAction0
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def cay {k r : ℕ} (X : B.Mat k r) : B.Mat k r := (1 + X) * (1 - X)⁻¹

def cayInv {k r : ℕ} (g : B.Mat k r) : B.Mat k r := (g - 1) * (g + 1)⁻¹

def LieBasis : Prop :=
  ∀ k r : ℕ, ∃ (d : ℕ) (L : (Fin d → ℝ) →L[ℝ] B.Mat k r) (M : B.Mat k r →L[ℝ] (Fin d → ℝ)),
    (∀ x, B.inLie k r (L x)) ∧ (∀ x, M (L x) = x) ∧ ∀ X, B.inLie k r X → L (M X) = X

def CayAlg : Prop :=
  ∀ k r : ℕ,
    (∀ X : B.Mat k r, B.inLie k r X → IsUnit (1 - X) → cay X ∈ B.GV k r ∧ IsUnit (cay X + 1) ∧ cayInv (cay X) = X) ∧
    ∀ g ∈ B.GV k r, IsUnit (g + 1) → B.inLie k r (cayInv g) ∧ IsUnit (1 - cayInv g) ∧ cay (cayInv g) = g

def GVGrp : Prop :=
  ∀ k r : ℕ, IsUnit ((1 : B.Mat k r) + 1) ∧ ∀ g₀ ∈ B.GV k r, g₀⁻¹ * g₀ = 1 ∧
    ∀ h ∈ B.GV k r, g₀ * h ∈ B.GV k r ∧ g₀⁻¹ * h ∈ B.GV k r ∧ g₀ * (g₀⁻¹ * h) = h

def CaySmooth : Prop :=
  ∀ (k r : ℕ) (g₀ : B.Mat k r),
    IsOpen {X : B.Mat k r | IsUnit (1 - X)} ∧ IsOpen {m : B.Mat k r | IsUnit (g₀⁻¹ * m + 1)} ∧
    ContDiffOn ℝ ∞ (fun X : B.Mat k r => g₀ * cay X) {X | IsUnit (1 - X)} ∧
    ContDiffOn ℝ ∞ (fun m : B.Mat k r => cayInv (g₀⁻¹ * m)) {m | IsUnit (g₀⁻¹ * m + 1)}

theorem gChart_of (hB : LieBasis) (hA : CayAlg) (hG : GVGrp) (hS : CaySmooth) : GChart := by
  intro k r
  obtain ⟨d, L, M, hL, hML, hLM⟩ := hB k r
  refine ⟨d, fun g₀ hg₀ => ?_⟩
  obtain ⟨hA1, hA2⟩ := hA k r
  obtain ⟨hOne, hGg⟩ := hG k r
  obtain ⟨hinv, hmul⟩ := hGg g₀ hg₀
  obtain ⟨hO1, hU1, hκs, hΦs⟩ := hS k r g₀
  refine ⟨{x | IsUnit (1 - L x)}, {m | IsUnit (g₀⁻¹ * m + 1)}, fun x => g₀ * cay (L x),
    fun m => M (cayInv (g₀⁻¹ * m)), hO1.preimage L.continuous, hU1, ?_, ?_, ?_, ?_, ?_⟩
  · show IsUnit (g₀⁻¹ * g₀ + 1)
    rw [hinv]; exact hOne
  · exact hκs.comp L.contDiff.contDiffOn (fun x hx => hx)
  · exact M.contDiff.comp_contDiffOn hΦs
  · intro x hx
    obtain ⟨hc, hc1, hci⟩ := hA1 (L x) (hL x) hx
    have e : g₀⁻¹ * (g₀ * cay (L x)) = cay (L x) := by
      rw [← Matrix.mul_assoc, hinv, Matrix.one_mul]
    refine ⟨(hmul _ hc).1, ?_, ?_⟩
    · show IsUnit (g₀⁻¹ * (g₀ * cay (L x)) + 1)
      rw [e]; exact hc1
    · show M (cayInv (g₀⁻¹ * (g₀ * cay (L x)))) = x
      rw [e, hci, hML]
  · intro g hg hgG
    obtain ⟨-, hh, hgh⟩ := hmul g hgG
    obtain ⟨hl, hu, hc⟩ := hA2 _ hh hg
    refine ⟨?_, ?_⟩
    · show IsUnit (1 - L (M (cayInv (g₀⁻¹ * g))))
      rw [hLM _ hl]; exact hu
    · show g₀ * cay (L (M (cayInv (g₀⁻¹ * g)))) = g
      rw [hLM _ hl, hc, hgh]

def IsDomOmPlus : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), inWb k r z → inWb k r z' →
    Q.IsDom k r z z' 0 (Q.OmPlus k r z z')

def RightTypeAction0 : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    [FiniteDimensional ℂ Wq]
    (k r m : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq))
    (D : Set (Q.Mx k r)) (mm : ℕ∞), inWb k r z → inWb k r z' → Q.IsDom k r z z' 0 D →
    IsCRepOn (UWset k r z') π' → ContinuousOn π' (UWset k r z') →
    ∀ J ∈ Gr.FFlM mm k r z z' π π' 0 D, ∀ g ∈ Q.Glev k r 0 ∩ D,
    ∀ Bs : Fin m → Fin (2 * r + k + 1) → ℂ, Q.IsFrameOf k r [z'] Bs → ∀ (w : ℂ) (v : Wq),
      Q.capR k r Bs w J g v = J g (Q.capRep k r π' Bs w v)

def LeftTypeAction0 : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    [FiniteDimensional ℂ Wp]
    (k r m : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq))
    (D : Set (Q.Mx k r)) (mm : ℕ∞), inWb k r z → inWb k r z' → Q.IsDom k r z z' 0 D →
    IsCRepOn (UWset k r z) π → ContinuousOn π (UWset k r z) →
    ∀ J ∈ Gr.FFlM mm k r z z' π π' 0 D, ∀ g ∈ Q.Glev k r 0 ∩ D,
    ∀ Bs : Fin m → Fin (2 * r + k + 1) → ℂ, Q.IsFrameOf k r [z] Bs → ∀ (w : ℂ) (v : Wq),
      Q.capLft k r Bs w J g v = Q.capRep k r π Bs w (J g v)

theorem uCap_of (h0 : IsDomOmPlus) (hR : RightTypeAction0) (hL : LeftTypeAction0) : UCap := by
  intro k r Wp Wq _ _ _ _ _ _ D u u' J hT hT' hF
  have hD := h0 k r D.z D.z' D.z_mem D.z'_mem
  have hg0 : ∀ g ∈ JF.Om k r D.z D.z', g ∈ Q.Glev k r 0 ∩ Q.OmPlus k r D.z D.z' :=
    fun g hg => ⟨⟨hg.1, fun a ha => absurd ha (Nat.not_lt_zero _)⟩, hg.2⟩
  refine ⟨fun Bs hBs w => ⟨∏ i ∈ Finset.Icc 1 k, (w - (k : ℂ) / 2 + 1 / 2 + (u i : ℂ)), fun g hg => ?_⟩,
    fun Bs hBs w => ⟨∏ i ∈ Finset.Icc 1 k, (w - (k : ℂ) / 2 + 1 / 2 + (u' i : ℂ)), fun g hg => ?_⟩⟩
  · refine ContinuousLinearMap.ext fun v => ?_
    rw [hL Wp Wq k r k D.z D.z' D.π D.π' _ _ D.z_mem D.z'_mem hD hT.2.1 hT.2.2.1 J hF g (hg0 g hg) Bs hBs w v,
      hT.2.2.2.2.2 Bs hBs w (J g v)]
    rfl
  · refine ContinuousLinearMap.ext fun v => ?_
    rw [hR Wp Wq k r k D.z D.z' D.π D.π' _ _ D.z_mem D.z'_mem hD hT'.2.1 hT'.2.2.1 J hF g (hg0 g hg) Bs hBs w v,
      hT'.2.2.2.2.2 Bs hBs w v, map_smul]
    rfl

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothOfCoefficientsHolds
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem smooth_of_coefficients_holds : SmoothOfCoeffs := by
  intro k r E _ _ _ Dm J h g₀ hg₀
  let b := Module.finBasis ℂ E
  let ℓ : Fin (Module.finrank ℂ E) → E →L[ℂ] ℂ := fun i => LinearMap.toContinuousLinearMap (b.coord i)
  choose U F hU hgU hF hJF using fun i => h (ℓ i) g₀ hg₀
  refine ⟨⋂ i, U i, fun g => ∑ i, F i g • b i, isOpen_iInter_of_finite hU, Set.mem_iInter.2 hgU, ?_, ?_⟩
  · refine ContDiffOn.sum fun i _ => ?_
    exact ((hF i).mono (Set.iInter_subset _ i)).smul contDiffOn_const
  · intro g hg hgG
    have hg' := Set.mem_iInter.1 hg
    conv_lhs => rw [← b.sum_repr (J g)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hJF i g (hg' i) hgG]
    rfl

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

