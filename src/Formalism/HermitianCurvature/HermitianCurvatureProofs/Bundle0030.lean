import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0029
import Formalism.HermitianCurvature.StatementWd
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0021
import Formalism.HermitianCurvature.HermitianCurvatureProofs.KroneckerEmbedMulApply
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0022
import Formalism.HermitianCurvature.HermitianCurvatureProofs.QEFirstMulSecondEqSwap
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0027
import Formalism.HermitianCurvature.HermitianCurvatureProofs.EntryCommuteTransposedRMatrix
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ScalarCommuteTransposedRMatrixEntry
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftMatrixTransferConjTransposeCommute
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiagScalarCommuteOfEntries
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PartialFlipCommuteDiagScalarOfFree
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiagScalarCommuteTransposedRMatrix

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.RealWeightedForms
section
namespace Formalism.FourierDecayAlt.P.RealWeightedForms

open Finset Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.GramProductIdentities Formalism.FourierDecayAlt.P.DualKernelLemmas
open scoped Matrix

theorem qwOfReal : QwOfReal := by
  intro S _ _ q w Y hq hw
  induction w with
  | nil =>
    simp only [qw, List.map_nil]
    exact Complex.ext (by simp) (by simpa using hq)
  | cons l w ih =>
    have him := hw l (List.mem_cons_self ..)
    have ih' := ih (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl'))
    obtain ⟨plus, intersection_update_fsHerm_neg_one, pt⟩ := l
    obtain ⟨p, rfl⟩ : ∃ p : ℝ, pt = p := ⟨pt.re, Complex.ext (by simp) (by simpa using him)⟩
    cases plus <;> simp [qw, ih']

section admitted

variable {S : Type}

def Cnd (l l' : Letter ℂ S) : Prop :=
  if l'.plus then
    2 < |l.pt.re - l'.pt.re| ∧ 2 < |l.pt.re - l'.pt.re + 1| ∧ 2 < |l.pt.re - l'.pt.re - 1|
  else
    2 < |l'.pt.re - l.pt.re| ∧ 2 < |l'.pt.re - l.pt.re - 1| ∧ 2 < |l'.pt.re - l.pt.re - 2|

theorem admissible_word_pairwise_condition {α β : ℝ} {w : List (Letter ℂ S)} (h : GrowthHypotheses α β w) :
    w.Pairwise (fun l l' => Cnd l l' ∧ Cnd l' l) := by
  rw [List.pairwise_iff_get]
  intro i j hij
  exact ⟨h.2.2 i j (ne_of_lt hij), h.2.2 j i (ne_of_lt hij).symm⟩

theorem regL_of_cnd {l l' : Letter ℂ S} (h : Cnd l l') : RegL l' l.pt := by
  unfold Cnd at h
  unfold RegL
  cases hp : l'.plus
  · simp only [hp, Bool.false_eq_true, if_false] at h ⊢
    intro he
    have hre := congrArg Complex.re he
    simp only [Complex.sub_re, Complex.one_re] at hre
    rw [hre] at h
    norm_num at h
  · simp only [hp, if_true] at h ⊢
    intro he
    have hre := congrArg Complex.re he
    simp only [Complex.sub_re, Complex.one_re] at hre
    rw [hre] at h
    norm_num at h

theorem good_of_adm {α β : ℝ} {w : List (Letter ℂ S)} (h : GrowthHypotheses α β w) : Good w := by
  refine ⟨h.1, fun l hl => ?_, (admissible_word_pairwise_condition h).imp fun hc => regL_of_cnd hc.1⟩
  rw [Complex.star_def]
  exact Complex.conj_eq_iff_im.2 (h.2.1 l hl).1

theorem pos_mul_ofReal {z : ℂ} {r : ℝ} (hz : z.im = 0 ∧ 0 < z.re) (hr : 0 < r) :
    (z * r).im = 0 ∧ 0 < (z * r).re := by
  refine ⟨by simp [hz.1], ?_⟩
  have e : (z * r).re = z.re * r := by simp [hz.1]
  rw [e]
  exact mul_pos hz.2 hr

theorem same_sign_pos {a b : ℝ} (ha : 2 < |a|) (hb : 2 < |b|) (hab : b = a + 1 ∨ b = a - 1) :
    0 < a / b := by
  rcases lt_abs.1 ha with ha' | ha' <;> rcases hab with rfl | rfl
  · exact div_pos (by linarith) (by linarith)
  · exact div_pos (by linarith) (by linarith)
  · exact div_pos_of_neg_of_neg (by linarith) (by linarith)
  · exact div_pos_of_neg_of_neg (by linarith) (by linarith)

def CndY (Y : ℝ) (l' : Letter ℂ S) : Prop :=
  if l'.plus then
    2 < |Y - l'.pt.re| ∧ 2 < |Y - l'.pt.re + 1| ∧ 2 < |Y - l'.pt.re - 1|
  else
    2 < |l'.pt.re - Y| ∧ 2 < |l'.pt.re - Y - 1| ∧ 2 < |l'.pt.re - Y - 2|

theorem qw_pos (q : ℂ → ℂ) (Y : ℝ) (hq : (q Y).im = 0 ∧ 0 < (q Y).re) :
    ∀ w : List (Letter ℂ S), (∀ l' ∈ w, l'.pt.im = 0 ∧ CndY Y l') →
      (qw q w (Y : ℂ)).im = 0 ∧ 0 < (qw q w (Y : ℂ)).re := by
  intro w
  induction w with
  | nil =>
    intro _
    simpa [qw] using hq
  | cons l w ih =>
    intro hw
    obtain ⟨hl, hc⟩ := hw l (List.mem_cons_self ..)
    have ih' := ih (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl'))
    obtain ⟨plus, intersection_update_fsHerm_neg_one, pt⟩ := l
    obtain ⟨p, rfl⟩ : ∃ p : ℝ, pt = p := ⟨pt.re, Complex.ext (by simp) (by simpa using hl)⟩
    cases plus
    · simp only [CndY, Bool.false_eq_true, if_false, Complex.ofReal_re] at hc
      have hpos := same_sign_pos hc.1 hc.2.1 (Or.inr rfl)
      have e : qw q ({ plus := false, intersection_update_fsHerm_neg_one := intersection_update_fsHerm_neg_one, pt := (p : ℂ) } :: w) (Y : ℂ) =
          qw q w (Y : ℂ) * (((p - Y) / (p - Y - 1) : ℝ) : ℂ) := by
        simp [qw]
      rw [e]
      exact pos_mul_ofReal ih' hpos
    · simp only [CndY, if_true, Complex.ofReal_re] at hc
      have hpos := same_sign_pos hc.2.1 hc.1 (Or.inr (by ring))
      have e : qw q ({ plus := true, intersection_update_fsHerm_neg_one := intersection_update_fsHerm_neg_one, pt := (p : ℂ) } :: w) (Y : ℂ) =
          qw q w (Y : ℂ) * (((Y - p + 1) / (Y - p) : ℝ) : ℂ) := by
        simp [qw]
      rw [e]
      exact pos_mul_ofReal ih' hpos

end admitted

theorem admissible_dual_kernel_identity : AdmDK := by
  intro S _ _ α β q w L hL hG h1 h2
  have hpw := List.pairwise_append.1 (admissible_word_pairwise_condition h1)
  have hreal : ∀ l ∈ L, l.pt = ((l.pt.re : ℝ) : ℂ) := fun l hl =>
    Complex.ext (by simp) (by simpa using (h1.2.1 l (List.mem_append_left w hl)).1)
  have hpos : ∀ l ∈ L, (qw q w l.pt).im = 0 ∧ 0 < (qw q w l.pt).re := by
    intro l hl
    have hq := hG l.pt.re (h1.2.1 l (List.mem_append_left w hl)).2.1
    rw [hreal l hl]
    refine qw_pos q l.pt.re hq w fun l' hl' => ⟨(h1.2.1 l' (List.mem_append_right L hl')).1, ?_⟩
    have hc := (hpw.2.2 l hl l' hl').1
    unfold Cnd at hc
    exact hc
  refine ⟨⟨hL, good_of_adm h1, good_of_adm h2, ?_, fun l hl => ?_⟩, hpos⟩
  · refine hpw.1.imp_of_mem fun {l l'} hl hl' hc => ?_
    have hc1 := hc.1
    unfold Cnd at hc1
    rw [if_pos (hL l' hl')] at hc1
    rw [hreal l hl, hreal l' hl']
    refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩
    · have hre := congrArg Complex.re he
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.zero_re] at hre
      rw [hre] at hc1
      norm_num at hc1
    · have hre := congrArg Complex.re he
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re] at hre
      rw [hre] at hc1
      norm_num at hc1
    · have hre := congrArg Complex.re he
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.neg_re, Complex.one_re] at hre
      rw [hre] at hc1
      norm_num at hc1
  · intro h0
    have := (hpos l hl).2
    rw [h0, Complex.zero_re] at this
    exact lt_irrefl _ this

theorem re_mul_div (u v : ℂ) (r : ℝ) (hu : u.im = 0) : (u * v / r).re = u.re * v.re / r := by
  rw [Complex.div_ofReal_re, Complex.mul_re, hu, zero_mul, sub_zero]

section Rep

variable {A S V : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S]
  [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V]

theorem frm_act_act_of_star_mul_mul_eq (ρ : Rep A V) (RR W : SlopeTestRemainingChoices S A) (hW : star W * RR * W = RR) (X X' : Ix S → V) :
    frm ρ RR (act W X) (act W X') = frm ρ RR X X' := by
  have hPA := fun (M N : SlopeTestRemainingChoices S A) (Y Y' : Ix S → V) => GramProductIdentities.pairAdj A S V ρ M N 1 Y Y'
  unfold frm
  have h1 := (hPA (star W) 1 (act RR (act W X)) X').2.2.2
  rw [star_star] at h1
  rw [← h1, ← (hPA (star W) RR (act W X) X').1, ← (hPA (star W * RR) W X X').1, hW]

end Rep

theorem mem_Lp {S : Type} {K : ℕ} (sl : Fin K → S) (y : Fin K → ℝ) (a : Fin K) :
    (⟨true, sl a, (y a : ℂ)⟩ : Letter ℂ S) ∈ Lp sl y := by
  unfold Lp
  rw [List.mem_ofFn]
  exact ⟨a, rfl⟩

theorem plus_Lp {S : Type} {K : ℕ} (sl : Fin K → S) (y : Fin K → ℝ) :
    ∀ l ∈ Lp sl y, l.plus = true := by
  intro l hl
  unfold Lp at hl
  rw [List.mem_ofFn] at hl
  obtain ⟨a, rfl⟩ := hl
  rfl

theorem prod_Lp {S : Type} {K : ℕ} (sl : Fin K → S) (y : Fin K → ℝ) (g : ℂ → ℂ) :
    ((Lp sl y).map fun l => g l.pt).prod = ∏ a, g (y a) := by
  unfold Lp
  rw [List.map_ofFn, List.prod_ofFn]
  rfl

private theorem sizeBoundOfParts_statement : SizeBoundOfParts := by
  intro hDK hPW hPA hAdm A S V _ _ _ _ _ _ _ _ _ _ ρ QQ q f fi s w n vA vB vAv vBv K sl x α β y hD hG hI h1 h2
  obtain ⟨hS, hW, hWQ, -, -, -, -, -, -, -, -⟩ := hD
  obtain ⟨hDKH, hpos⟩ := hAdm S α β q w (Lp sl y) (plus_Lp sl y) hG h1 h2
  obtain ⟨-, -, hinv, -⟩ := hPW ℂ A S QQ f fi s (Lp sl y ++ w) hW hWQ h1.1
  obtain ⟨-, hle⟩ := hDK A S V ρ QQ q w (Lp sl y) hS hDKH (hI _ h1)
    (act (Vw f s (Lp sl y ++ w)) (letters vA vB (Lp sl y) x)) (letters vAv vBv ((Lp sl y).map dl) x)
  rw [frm_act_act_of_star_mul_mul_eq ρ _ _ hinv] at hle
  have hWK : WK ρ QQ f s w vA vB vAv vBv sl y x =
      pair ρ (act (JL (Lp sl y) * RRw QQ w) (act (Vw f s (Lp sl y ++ w)) (letters vA vB (Lp sl y) x)))
        (letters vAv vBv ((Lp sl y).map dl) x) := by
    unfold WK
    congr 1
    exact (hPA A S V ρ (JL (Lp sl y) * RRw QQ w) (Vw f s (Lp sl y ++ w)) 1
      (letters vA vB (Lp sl y) x) (letters vAv vBv ((Lp sl y).map dl) x)).1
  rw [hWK]
  refine hle.trans_eq ?_
  have hP : ((Lp sl y).map fun l => qw q w l.pt).prod = ((∏ a, (qw q w (y a)).re : ℝ) : ℂ) := by
    rw [prod_Lp sl y (qw q w), Complex.ofReal_prod]
    refine Finset.prod_congr rfl fun a _ => ?_
    have hm := (hpos _ (mem_Lp sl y a)).1
    exact Complex.ext (by simp) (by simpa using hm)
  rw [hP, re_mul_div _ _ _ ((hI _ h1) _).2]

theorem first_polynomial_size : AdmissiblePointSizeBound := by
  exact sizeBoundOfParts_statement DualKernelLemmas.lemmaDK Formalism.FourierDecayAlt.P.plane_wave_word_identity GramProductIdentities.pairAdj admissible_dual_kernel_identity

theorem first_polynomial_size_of_parts : SizeBoundOfParts := sizeBoundOfParts_statement

end Formalism.FourierDecayAlt.P.RealWeightedForms

theorem Formalism.FourierDecayAlt.P.weighted_quadratic_of_real : Formalism.FourierDecayAlt.FormPairingAction.QwOfReal := Formalism.FourierDecayAlt.P.RealWeightedForms.qwOfReal
theorem Formalism.FourierDecayAlt.P.admDK_statement : Formalism.FourierDecayAlt.FormPairingAction.AdmDK := Formalism.FourierDecayAlt.P.RealWeightedForms.admissible_dual_kernel_identity
theorem Formalism.FourierDecayAlt.P.admissible_point_size_bound : Formalism.FourierDecayAlt.FormPairingAction.AdmissiblePointSizeBound := Formalism.FourierDecayAlt.P.RealWeightedForms.first_polynomial_size
theorem Formalism.FourierDecayAlt.P.first_polynomial_size_of_clauses : Formalism.FourierDecayAlt.FormPairingAction.SizeBoundOfParts := Formalism.FourierDecayAlt.P.RealWeightedForms.first_polynomial_size_of_parts
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictedDualKernel
section
namespace Formalism.FourierDecayAlt.P.RestrictedDualKernel

open Finset Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.GramProductIdentities Formalism.FourierDecayAlt.P.DualKernelLemmas
open scoped Matrix ComplexOrder

section Rep

variable {A S V : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S]
  [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V]

theorem cs_on (ρ : Rep A V) (M : SlopeTestRemainingChoices S A) (X : Submodule ℂ (Ix S → V)) (hP : IsPosOn ρ M X)
    {x y : Ix S → V} (hx : x ∈ X) (hy : y ∈ X) :
    ‖frm ρ M x y‖ ^ 2 ≤ (frm ρ M x x).re * (frm ρ M y y).re := by
  let Ξ : Formalism.FourierDecayAlt.F7.Sesq X :=
    LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun u v : X => frmS ρ M u v)
      (fun u v z => by simp) (fun c u z => by simp) (fun u v z => by simp) (fun c u z => by simp)
  have h := cs_of_pos Ξ (fun m => hP m.1 m.2) ⟨x, hx⟩ ⟨y, hy⟩
  simpa [Ξ, frmS_apply] using h

theorem pos_mul {c u : ℂ} (hc : 0 < c) (hu : 0 ≤ u.re ∧ u.im = 0) : 0 ≤ (c * u).re ∧ (c * u).im = 0 := by
  obtain ⟨h1, h2⟩ := Complex.pos_iff.mp hc
  have hci : c.im = 0 := by linarith
  rw [Complex.mul_re, Complex.mul_im, hci, hu.2]
  constructor
  · nlinarith [hu.1]
  · ring

end Rep

theorem d1cSub : DualityPositiveSubspace := by
  intro A S V _ _ _ _ _ _ _ _ _ _ ρ Ω RR TT q a Y X D hD hDX hΦ hP
  have hq : q Y ≠ 0 := hD.2.2.2.2.2
  have hm : ∀ X₂, frm ρ (RR * ins a (TT (↑Y + 1))ᵀ) X₂ X₂ =
      q Y * frm ρ (RR * ins a (TT ↑Y)) (act (PsiP TT q a ↑Y) X₂) (act (PsiP TT q a ↑Y) X₂) := by
    intro X₂
    rw [d1b A S V ρ Ω RR TT q a Y hD X₂ X₂]; field_simp
  refine ⟨fun X₁ h₁ X₂ h₂ => ?_, fun hq0 X₂ h₂ => ?_⟩
  · rw [hm, d1a A S V ρ Ω RR TT q a Y hD X₁ X₂]
    refine real_bound _ _ _ _ hq (hP X₁ h₁).2 (hP _ (hΦ X₂ h₂)).2 ?_
    exact cs_on ρ _ X hP h₁ (hΦ X₂ h₂)
  · rw [hm]; exact pos_mul hq0 (hP _ (hΦ X₂ h₂))

theorem lemmaDKSub : LemmaDKSub := by
  intro A S V _ _ _ _ _ _ _ _ _ _ ρ QQ q w L X D hS hD hDX hΦ hP
  have hok := dkDualOK S q w L hD
  have hdl := Formalism.FourierDecayAlt.P.duality_list_holds ℂ A S QQ q w L hS hD.2.1 hD.2.2.1 hok
  have hkap := Formalism.FourierDecayAlt.P.kappa_formula_holds ℂ S q w L hD.2.1 hD.2.2.1 hok
  have h4 := Formalism.FourierDecayAlt.P.GramProductIdentities.dkStep4 S q w L hD.1
  have hk0 : kap q w L ≠ 0 := hdl.2.1
  have hprod : (L.map fun l => qw q w l.pt).prod = kap q w L := by rw [hkap, h4]
  have hm : ∀ X₂, frm ρ (RRw QQ (L.map dl ++ w)) X₂ X₂ = kap q w L *
      frm ρ (RRw QQ (L ++ w)) (act (Ps QQ q w L) X₂) (act (Ps QQ q w L) X₂) := by
    intro X₂
    simp only [frm]
    rw [pair_act', ← act_mul, ← act_mul, hdl.2.2.2.1, act_csmul, pair_smul_left]
    field_simp
  refine ⟨fun X₁ h₁ X₂ h₂ => ?_, fun hq0 X₂ h₂ => ?_⟩
  · rw [hprod, hm, dkStep1 A S V ρ QQ q w L hS hD X₁ X₂]
    refine real_bound _ _ _ _ hk0 (hP X₁ h₁).2 (hP _ (hΦ X₂ h₂)).2 ?_
    exact cs_on ρ _ X hP h₁ (hΦ X₂ h₂)
  · rw [hprod] at hq0; rw [hm]; exact pos_mul hq0 (hP _ (hΦ X₂ h₂))

end Formalism.FourierDecayAlt.P.RestrictedDualKernel

theorem Formalism.FourierDecayAlt.P.duality_positive_subspace : Formalism.FourierDecayAlt.FormPairingAction.DualityPositiveSubspace := Formalism.FourierDecayAlt.P.RestrictedDualKernel.d1cSub
theorem Formalism.FourierDecayAlt.P.dual_kernel_lemma_restricted : Formalism.FourierDecayAlt.FormPairingAction.LemmaDKSub := Formalism.FourierDecayAlt.P.RestrictedDualKernel.lemmaDKSub
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.WordStatementsAllHold
section
namespace Formalism.FourierDecayAlt.P.Wd13

open Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P

end Formalism.FourierDecayAlt.P.Wd13

namespace Formalism.FourierDecayAlt.P

theorem word_statements_all_hold : Formalism.FourierDecayAlt.Wd.WordsAll :=
  ⟨word_module_structure, site_exchange_relation, word_matrix_entry_one, conjugate_word_eigen, word_product_formula,
    duality_list_holds, kappa_formula_holds, plane_wave_vector_identity, plane_wave_word_identity⟩

end Formalism.FourierDecayAlt.P
end

