import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0257
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0094
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0252
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0103
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0110
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0157
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0150
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0186
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0185
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRhoFrameLoc
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0113
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0258
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0256
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BaseIndexConstantInjective

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepTop
section
namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep

theorem thConst_of_open (hMC : Core.TC.ModConst) (hLN : Core.TC.LineNonzero)
    (hPoly : Core.TC.PolyRadial ∨ Core.TC.PolyRadialS) : Core.ThConst := by
  rcases hPoly with h | h
  · exact Core.TC.theta_constancy_assembly h hMC hLN Core.TC.polynomial_finish_holds
  · exact Core.TC.theta_constancy_assembly_scalar h hMC hLN Core.TC.polynomial_finish_holds

theorem ssnRep_of_open (hPE : PRho.PRhoExists) (hTF : ThtFacts) (hMC : Core.TC.ModConst)
    (hLN : Core.TC.LineNonzero) (hPoly : Core.TC.PolyRadial ∨ Core.TC.PolyRadialS) : SSnRep :=
  second_shift_representation_assembly hPE Formalism.FourierDecayAlt.P.CutMP.JA.gauge_lines_holds hTF datum_unit_norm_holds
    (Core.theta_gauge_constancy_holds Formalism.FourierDecayAlt.P.CutMP.JA.quadratic_second_shift_form Formalism.FourierDecayAlt.P.CutMP.JA.second_shift_pointwise_holds
      (thConst_of_open hMC hLN hPoly) Formalism.FourierDecayAlt.P.CutMP.JA.second_shift_entry_holds hPE Formalism.FourierDecayAlt.P.CutMP.JA.gauge_lines_holds
      datum_unit_norm_holds)

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJATCDtrSIo
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC.DT

noncomputable section

variable {k r : ℕ}

def eP (k r : ℕ) (z' ν v : Fin (2 * r + k + 1) → ℂ) : Fin (2 * r + k + 1) → ℂ :=
  SSn.prWv k r z' v - herm (Hpk k r) (SSn.prWv k r z' v) ν • ν

theorem eP_add (z' ν x y : Fin (2 * r + k + 1) → ℂ) : eP k r z' ν (x + y) = eP k r z' ν x + eP k r z' ν y := by
  unfold eP
  rw [PRhoCut.FL.prWv_add, DU.hadd_l, add_smul]
  abel

theorem eP_smul (z' ν : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (x : Fin (2 * r + k + 1) → ℂ) :
    eP k r z' ν (c • x) = c • eP k r z' ν x := by
  unfold eP
  rw [PRhoCut.FL.prWv_smul, DU.hsmul_l, smul_sub, smul_smul]

def ioLin (k r : ℕ) (μ : B.Mat k r) (z' ν : Fin (2 * r + k + 1) → ℂ) :
    (Fin (2 * r + k + 1) → ℂ) →ₗ[ℂ] (Fin (2 * r + k + 1) → ℂ) where
  toFun v := μ *ᵥ eP k r z' ν v
  map_add' x y := by rw [eP_add, Matrix.mulVec_add]
  map_smul' c x := by rw [eP_smul, Matrix.mulVec_smul]; rfl

theorem ioMulVec (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (ζ : ℂ)
    (v : Fin (2 * r + k + 1) → ℂ) :
    SSn.io0 k r z z' μsec ζ *ᵥ v = NF.muZ k r μsec ζ *ᵥ (SSn.prWv k r z' v -
      herm (Hpk k r) (SSn.prWv k r z' v) (SSn.nu0' k r z z' μsec ζ) • SSn.nu0' k r z z' μsec ζ) := by
  have e : SSn.io0 k r z z' μsec ζ =
      LinearMap.toMatrix' (ioLin k r (NF.muZ k r μsec ζ) z' (SSn.nu0' k r z z' μsec ζ)) := by
    ext i j
    rw [LinearMap.toMatrix'_apply]
    rfl
  rw [e, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  rfl

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC.DT
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDACapTodaVChain
section
open Matrix Finset

namespace Formalism.FourierDecayAlt.P.CutMP.TVG

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.SignAntidiagonal

theorem colsVm_castSucc {k r m : ℕ} (hm : m + 1 ≤ r) :
    colsVm k r (m + 1) ∘ Fin.castSucc = colsVm k r m := by
  funext j; ext; simp [colsVm]

theorem mirror_chain_expansion_holds : MirrorChainExpansion := by
  intro A _ _ M _ _ k r E La ρ hG m _hm u hR0 hR1 hL
  have hm : m + 2 ≤ r := _hm
  set a := colsVm k r (m + 2) with hadef
  have hav : ∀ l : Fin (m + 2), (a l).val = r + k + 1 + l.val := by
    intro l; have := l.isLt; simp [a, colsVm]; omega
  have hcs : a ∘ Fin.castSucc = colsVm k r (m + 1) := colsVm_castSucc hm
  have hexp := Formalism.FourierDecayAlt.P.expansion_last_column A _ (m + 1) E a a u
  rw [hexp, map_sum, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  have ha2 : a (Fin.last (m + 1)) = esI k r ⟨r - m - 2, by omega⟩ := by
    ext; rw [hav]; simp [esI]; omega

  have hzero : ∀ l : Fin m, La ((((-1 : ℤ) ^ (m + 1 + ((Fin.castSucc (Fin.castSucc l) : Fin (m + 2)) : ℕ)) : ℤ) : A) *
      (qminor E (a ∘ (Fin.castSucc (Fin.castSucc l)).succAbove) (a ∘ Fin.castSucc) u *
        Tm E (u - ((m + 1 : ℕ) : ℂ)) (a (Fin.castSucc (Fin.castSucc l))) (a (Fin.last (m + 1))))) = 0 := by
    intro l
    rw [la_intmul]
    have hne : a (Fin.castSucc (Fin.castSucc l)) ≠ a (Fin.last (m + 1)) := by
      intro h'; have := congrArg Fin.val h'; rw [hav, hav] at this; simp at this; omega
    rw [tm_offdiag _ _ hne]
    have ha1 : a (Fin.castSucc (Fin.castSucc l)) = esI k r ⟨r - 1 - l.val, by omega⟩ := by
      ext; rw [hav]; simp [esI]; omega
    rw [ha1, ha2, hR0 _ ⟨r - 1 - l.val, by omega⟩ (by simp; omega), smul_zero]
  rw [Finset.sum_eq_zero (fun l _ => hzero l), zero_add]

  have hlast : La ((((-1 : ℤ) ^ (m + 1 + ((Fin.last (m + 1) : Fin (m + 2)) : ℕ)) : ℤ) : A) *
      (qminor E (a ∘ (Fin.last (m + 1)).succAbove) (a ∘ Fin.castSucc) u *
        Tm E (u - ((m + 1 : ℕ) : ℂ)) (a (Fin.last (m + 1))) (a (Fin.last (m + 1))))) =
      La (qminor E (colsVm k r (m + 1)) (colsVm k r (m + 1)) u *
        Tm E (u - ((m + 1 : ℕ) : ℂ)) (esI k r ⟨r - m - 2, by omega⟩) (esI k r ⟨r - m - 2, by omega⟩)) := by
    rw [la_intmul, Fin.succAbove_last, hcs, ha2]
    have h2 : ((-1 : ℤ) ^ (m + 1 + ((Fin.last (m + 1) : Fin (m + 2)) : ℕ))) = 1 := by
      simp only [Fin.val_last]; rw [← two_mul, pow_mul]; norm_num
    rw [h2]; simp
  rw [hlast]

  set rowsP : Fin (m + 1) → Fin (2 * r + k + 1) := Fin.cons (esI k r ⟨r - m - 2, by omega⟩) (colsVm k r m) with hrP
  have hrows : a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove = rowsP ∘ (finRotate (m + 1)) := by
    funext q
    ext
    simp only [Function.comp_apply]
    by_cases hq : q = Fin.last m
    · subst hq
      rw [finRotate_last]
      simp only [rowsP, Fin.cons_zero]
      rw [hav, succAbove_val]; simp [esI]; omega
    · have hq' : q.val < m := by
        have := q.isLt; have : q.val ≠ m := fun h' => hq (Fin.ext (by simp [h'])); omega
      have hr1 : finRotate (m + 1) q = Fin.succ ⟨q.val, hq'⟩ := by
        ext; rw [coe_finRotate_of_ne_last hq]; simp
      rw [hr1]
      simp only [rowsP, Fin.cons_succ]
      rw [hav, succAbove_val]; simp [colsVm, hq']; omega
  have hQm : La (qminor E (a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove) (a ∘ Fin.castSucc) u) =
      ρ • La (qminor E (colsVm k r m) (colsVm k r m) u) := by
    rw [hrows, Formalism.REAL.quantumMinorRowSkew_holds A _ (m + 1) E rowsP _ (finRotate (m + 1)) u, la_intmul, sign_finRotate]
    rw [Formalism.FourierDecayAlt.P.expansion_first_line A _ m E hG rowsP _ u, map_sum]
    rw [Fin.sum_univ_castSucc, Finset.sum_eq_zero, zero_add]
    · rw [la_intmul]
      have hr0 : rowsP 0 = esI k r ⟨r - m - 2, by omega⟩ := by simp [rowsP]
      have hrs : rowsP ∘ Fin.succ = colsVm k r m := by funext q; simp [rowsP]
      rw [hr0, hrs, Fin.succAbove_last, hcs]
      have hx : colsVm k r (m + 1) (Fin.last m) = esI k r ⟨r - m - 1, by omega⟩ := by
        ext; simp [colsVm, esI]; omega
      have hne : esI k r ⟨r - m - 2, by omega⟩ ≠ colsVm k r (m + 1) (Fin.last m) := by
        rw [hx]; intro h'; have := congrArg Fin.val h'; simp [esI] at this; omega
      rw [tm_offdiag _ _ hne, hx, hL _ ⟨r - m - 1, by omega⟩ (by simp; omega), if_pos rfl]
      rw [colsVm_castSucc (by omega), smul_smul, smul_smul]
      congr 1
      simp only [Fin.val_last]
      push_cast
      rw [neg_one_sq', one_mul]
    · intro q _
      rw [la_intmul]
      have hr0 : rowsP 0 = esI k r ⟨r - m - 2, by omega⟩ := by simp [rowsP]
      rw [hr0, hcs]
      have hq := q.isLt
      have hx : colsVm k r (m + 1) (Fin.castSucc q) = esI k r ⟨r - 1 - q.val, by omega⟩ := by
        ext; simp [colsVm, esI]
      have hne : esI k r ⟨r - m - 2, by omega⟩ ≠ colsVm k r (m + 1) (Fin.castSucc q) := by
        rw [hx]; intro h'; have := congrArg Fin.val h'; simp [esI] at this; omega
      rw [tm_offdiag _ _ hne, hx, hL _ ⟨r - 1 - q.val, by omega⟩ (by simp; omega), if_neg (by simp; omega),
        zero_smul, smul_zero]
  have hmT : La (qminor E (a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove) (a ∘ Fin.castSucc) u *
      Tm E (u - ((m + 1 : ℕ) : ℂ)) (a (Fin.castSucc (Fin.last m))) (a (Fin.last (m + 1)))) =
      La (qminor E (a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove) (a ∘ Fin.castSucc) u) := by
    have hne : a (Fin.castSucc (Fin.last m)) ≠ a (Fin.last (m + 1)) := by
      intro h'; have := congrArg Fin.val h'; rw [hav, hav] at this; simp at this
    rw [tm_offdiag _ _ hne]
    have ha1 : a (Fin.castSucc (Fin.last m)) = esI k r ⟨r - m - 1, by omega⟩ := by ext; rw [hav]; simp [esI]; omega
    rw [ha1, ha2, hR1]
  rw [la_intmul, hmT, hQm]
  have h3 : ((((-1 : ℤ) ^ (m + 1 + ((Fin.castSucc (Fin.last m) : Fin (m + 2)) : ℕ))) : ℤ) : ℂ) = -1 := by
    simp only [Fin.val_castSucc, Fin.val_last]
    push_cast
    rw [show m + 1 + m = 2 * m + 1 by ring, pow_succ, pow_mul]; norm_num
  rw [h3, neg_one_smul]; abel

end Formalism.FourierDecayAlt.P.CutMP.TVG
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDACapTodaVGrp
section
open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.TVG

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Qx5 Formalism.FourierDecayAlt.P.Qx2 Formalism.FourierDecayAlt.P.PBN Formalism.FourierDecayAlt.P.PBN.MC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section loc

variable {r : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem pbOp_locO (l : Fin r) {f₁ f₂ : (Fin r → ℂ) → X} (h : ∀ c ∈ OmX r, f₁ c = f₂ c) {c : Fin r → ℂ}
    (hc : c ∈ OmX r) : pbOp l f₁ c = pbOp l f₂ c := by
  have hev : f₁ =ᶠ[nhds c] f₂ := by
    filter_upwards [(Formalism.FourierDecayAlt.P.Qx3.isOpen_OmX r).mem_nhds hc] with c' hc' using h c' hc'
  simp only [pbOp, wirtBar, if_pos hc, hev.fderiv_eq]

theorem pbN_locO (i : ℕ) {f₁ f₂ : (Fin r → ℂ) → X} (h : ∀ c ∈ OmX r, f₁ c = f₂ c) {c : Fin r → ℂ}
    (hc : c ∈ OmX r) : pbN r i f₁ c = pbN r i f₂ c := by
  unfold pbN
  split_ifs with hi
  · exact pbOp_locO _ h hc
  · rfl

theorem iteratedOperator_eqOn_of_eqOn (w : ℂ) : ∀ (m : ℕ) (f₁ f₂ : (Fin r → ℂ) → X), (∀ c ∈ OmX r, f₁ c = f₂ c) →
    ∀ c ∈ OmX r, (kvP r w m).1 f₁ c = (kvP r w m).1 f₂ c ∧ (kvP r w m).2 f₁ c = (kvP r w m).2 f₂ c
  | 0, f₁, f₂, h, c, hc => ⟨h c hc, rfl⟩
  | m + 1, f₁, f₂, h, c, hc => by
    have hin : ∀ c' ∈ OmX r, (w - (m : ℂ)) • f₁ c' - pbN r (r - m - 1) f₁ c' =
        (w - (m : ℂ)) • f₂ c' - pbN r (r - m - 1) f₂ c' := fun c' hc' => by
      rw [h c' hc', pbN_locO _ h hc']
    have ih1 := iteratedOperator_eqOn_of_eqOn w m _ _ hin
    have ih2 := iteratedOperator_eqOn_of_eqOn w m f₁ f₂ h
    refine ⟨?_, (ih2 c hc).1⟩
    show (kvP r w m).1 _ c - cbN r (r - m) (cbiN r (r - m - 1) ((kvP r w m).2 f₁)) c =
      (kvP r w m).1 _ c - cbN r (r - m) (cbiN r (r - m - 1) ((kvP r w m).2 f₂)) c
    rw [(ih1 c hc).1]
    congr 1
    unfold cbN cbiN
    split_ifs <;> simp [cbOp, cbiOp, (ih2 c hc).2]

theorem kvC_loc (w : ℂ) (m : ℕ) (f₁ f₂ : (Fin r → ℂ) → X) (h : ∀ c ∈ OmX r, f₁ c = f₂ c) {c : Fin r → ℂ}
    (hc : c ∈ OmX r) : kvC r w m f₁ c = kvC r w m f₂ c := (iteratedOperator_eqOn_of_eqOn w m f₁ f₂ h c hc).1

theorem kvC_zero (w : ℂ) (f : (Fin r → ℂ) → X) : kvC r w 0 f = f := rfl

theorem kvC_one (w : ℂ) (f : (Fin r → ℂ) → X) (hr : 1 ≤ r) (c : Fin r → ℂ) :
    kvC r w 1 f c = w • f c - pbOp ⟨r - 1, by omega⟩ f c := by
  show (w - ((0 : ℕ) : ℂ)) • f c - pbN r (r - 0 - 1) f c - cbN r (r - 0) (cbiN r (r - 0 - 1) (fun _ => 0)) c = _
  have h1 : r - 0 - 1 = r - 1 := by omega
  simp only [Nat.cast_zero, sub_zero, Nat.sub_zero]
  unfold pbN cbN
  rw [dif_pos (by omega), dif_neg (lt_irrefl r)]
  simp

theorem kvC_two (w : ℂ) (m : ℕ) (f : (Fin r → ℂ) → X) (c : Fin r → ℂ) :
    kvC r w (m + 2) f c = kvC r w (m + 1) (fun c => (w - ((m + 1 : ℕ) : ℂ)) • f c - pbN r (r - (m + 1) - 1) f c) c -
      cbN r (r - (m + 1)) (cbiN r (r - (m + 1) - 1) (kvC r w m f)) c := rfl

end loc

section alg

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Mx k r)}

abbrev TorV (hD : IsOpen D) (j : ℕ) : Subalgebra ℂ (SA E hD) :=
  Algebra.adjoin ℂ {x | ∃ l : Fin r, l.val < j ∧ x = EA hD (esI k r l) (esI k r l)}

theorem comm_TorV (hD : IsOpen D) (j : ℕ) (p q : Fin (2 * r + k + 1))
    (hp : ∀ l : Fin r, l.val < j → p ≠ esI k r l) (hq : ∀ l : Fin r, l.val < j → q ≠ esI k r l) (P : SA E hD)
    (hP : P ∈ TorV hD j) : Commute (EA hD p q) P := by
  induction hP using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    have h := EA_gl (E := E) hD p q (esI k r l) (esI k r l)
    rw [if_neg (hq l hl), if_neg (fun e => hp l hl e.symm), sub_zero] at h
    exact sub_eq_zero.1 h
  | algebraMap c => exact Algebra.commute_algebraMap_right c _
  | add y₁ y₂ _ _ h₁ h₂ => exact h₁.add_right h₂
  | mul y₁ y₂ _ _ h₁ h₂ => exact h₁.mul_right h₂

theorem TorV_mono (hD : IsOpen D) {j j' : ℕ} (h : j ≤ j') : TorV (E := E) hD j ≤ TorV hD j' := Algebra.adjoin_mono fun x ⟨l, hl, hx⟩ => ⟨l, lt_of_lt_of_le hl h, hx⟩

theorem EAs_mem_TorV (hD : IsOpen D) (l : Fin r) {j : ℕ} (h : l.val < j) :
    EA (E := E) hD (esI k r l) (esI k r l) ∈ TorV hD j := Algebra.subset_adjoin ⟨l, h, rfl⟩

theorem esI_ne {a b : Fin r} (h : a.val ≠ b.val) : esI k r a ≠ esI k r b := by
  intro h'
  have h2 := congrArg Fin.val h'
  simp only [esI] at h2
  have ha := a.isLt
  have hb := b.isLt
  omega

theorem root_action_on_truncated_vector (hD : IsOpen D) (z' : Fin (2 * r + k + 1) → ℂ) (hz' : inWb k r z') (hRR : RightRuleEv)
    {f : Mx k r → E} (hf : SmoothLev k r 0 D f) (hRf : RightEq k r z' 0 D f) (a b : Fin r) (hab : b.val < a.val) :
    ((EA hD (esI k r a) (esI k r b) : SA E hD) : Module.End ℂ (VS k r 0 D E)) ⟨cut k r 0 D f, cut_mem hD hf⟩ =
      (if a.val = b.val + 1 then (1 : ℂ) else 0) • ⟨cut k r 0 D f, cut_mem hD hf⟩ := by
  apply Subtype.ext
  funext g
  by_cases hg : g ∈ Glev k r 0 ∩ D
  · rw [EA_val, ev_E hD _ _ _ hg]
    have hloc := (good_eh (E := E) hD (cI (esI k r a)) (cI (esI k r b))).loc (cut k r 0 D f) f
      (fun x hx => cut_of_mem f hx) g hg
    simp only [posL_cI] at hloc
    rw [posL_cI, posL_cI]
    show EH k r (esI k r a) (esI k r b) (cut k r 0 D f) g = (if a.val = b.val + 1 then (1 : ℂ) else 0) • cut k r 0 D f g
    rw [hloc, hRR E k r z' D f hz' hD hf hRf g hg a b hab, cut_of_mem f hg]
  · show ((Eh hD (cI (esI k r a)) (cI (esI k r b)) ⟨cut k r 0 D f, cut_mem hD hf⟩ : VS k r 0 D E) : Mx k r → E) g =
      (if a.val = b.val + 1 then (1 : ℂ) else 0) • cut k r 0 D f g
    rw [(Eh hD (cI (esI k r a)) (cI (esI k r b)) ⟨cut k r 0 D f, cut_mem hD hf⟩).2.2 g hg,
      show cut k r 0 D f g = 0 from Set.indicator_of_notMem hg f, smul_zero]

theorem la_torus (hD : IsOpen D) (hTC : TorusCellv) (v₀ : VS k r 0 D E) (g₀ : Mx k r)
    (hg₀ : g₀ ∈ Glev k r (Fin.last r)) (hcell : ∀ c ∈ OmX r, wCell k r (Fin.last r) c * g₀ ∈ Glev k r 0 ∩ D)
    (l : Fin r) (w' : ℂ) (x : SA E hD) (c : Fin r → ℂ) (hc : c ∈ OmX r) :
    La hD v₀ (wCell k r (Fin.last r) c * g₀) (Tm (EA hD) w' (esI k r l) (esI k r l) * x) =
      w' • La hD v₀ (wCell k r (Fin.last r) c * g₀) x -
        pbOp l (fun c' => La hD v₀ (wCell k r (Fin.last r) c' * g₀) x) c := by
  have hγ := hcell c hc
  rw [La_apply, La_apply]
  simp only [Tm, Subalgebra.coe_mul, Subalgebra.coe_add, Module.End.mul_apply, LinearMap.add_apply, EA_val,
    Submodule.coe_add, Pi.add_apply, ite_true, Subalgebra.coe_algebraMap, Module.algebraMap_end_apply,
    Submodule.coe_smul, Pi.smul_apply]
  rw [ev_E hD _ _ _ hγ, posL_cI, hTC E k r D _ hD ((x : Module.End ℂ (VS k r 0 D E)) v₀).2.1 c hc g₀ hg₀ hγ.2 l,
    sub_eq_add_neg]
  rfl

end alg

section claim

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Mx k r)}

theorem claimV (hRR : RightRuleEv) (hLR : LeftRuleCellv) (hTC : TorusCellv) (hCh : MirrorChainExpansion)
    (hD : IsOpen D) (v₀ : VS k r 0 D E) (g₀ : Mx k r) (w : ℂ)
    (z z' : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hz' : inWb k r z')
    (hN : ∀ g ∈ Glev k r 0 ∩ D, ∀ n ∈ Nlev k r 0, n * g ∈ D)
    {f : Mx k r → E} (hf : SmoothLev k r 0 D f) (hLf : LeftEq k r z 0 D f) (hRf : RightEq k r z' 0 D f)
    (hv : v₀ = ⟨cut k r 0 D f, cut_mem hD hf⟩) (hg₀ : g₀ ∈ Glev k r (Fin.last r))
    (hcell : ∀ c ∈ OmX r, wCell k r (Fin.last r) c * g₀ ∈ Glev k r 0 ∩ D) :
    ∀ (m : ℕ), m ≤ r → ∀ P ∈ TorV hD (r - m), ∀ c ∈ OmX r,
      La hD v₀ (wCell k r (Fin.last r) c * g₀) (qminor (EA hD) (colsVm k r m) (colsVm k r m) w * P) =
        kvC r w m (fun c' => La hD v₀ (wCell k r (Fin.last r) c' * g₀) P) c := by
  have hLv : LeftEq k r z 0 D (v₀ : Mx k r → E) := by rw [hv]; exact leftEq_cut z hN hLf
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro hm P hP c hc
  rcases m with _ | _ | m
  · rw [MC.qminor_zero, one_mul]
    rfl
  · rw [MC.qminor_one]
    have hx0 : colsVm k r 1 0 = esI k r ⟨r - 1, by omega⟩ := by
      ext
      simp only [colsVm, esI, Fin.val_zero]
      omega
    rw [hx0, la_torus hD hTC v₀ g₀ hg₀ hcell ⟨r - 1, by omega⟩ w P c hc, kvC_one w _ hm c]
  · have hm2 : m + 2 ≤ r := hm
    have hP1 : P ∈ TorV hD (r - (m + 1)) := TorV_mono hD (by omega) hP
    have hP0 : P ∈ TorV hD (r - m) := TorV_mono hD (by omega) hP
    set ρ : ℂ := star (c ⟨r - m - 1, by omega⟩) / star (c ⟨r - m - 2, by omega⟩) with hρ
    set LaP : SA E hD →ₗ[ℂ] E := (La hD v₀ (wCell k r (Fin.last r) c * g₀)).comp (LinearMap.mulRight ℂ P) with hLaP
    have hLaP_apply : ∀ x, LaP x = La hD v₀ (wCell k r (Fin.last r) c * g₀) (x * P) := fun x => rfl
    have hnot : ∀ a : Fin r, r - m - 2 ≤ a.val → ∀ l' : Fin r, l'.val < r - (m + 2) → esI k r a ≠ esI k r l' :=
      fun a ha l' hl' => esI_ne (by omega)
    have hR0 : ∀ (x : SA E hD) (a : Fin r), r - m - 1 < a.val →
        LaP (x * EA hD (esI k r a) (esI k r ⟨r - m - 2, by omega⟩)) = 0 := by
      intro x a ha
      rw [hLaP_apply, mul_assoc, (comm_TorV hD (r - (m + 2)) _ _ (hnot a (by omega))
        (hnot ⟨r - m - 2, by omega⟩ le_rfl) P hP).eq, ← mul_assoc, La_apply, Subalgebra.coe_mul, Module.End.mul_apply]
      conv_lhs => rw [hv]
      rw [root_action_on_truncated_vector hD z' hz' hRR hf hRf a ⟨r - m - 2, by omega⟩ (by simp only; omega), if_neg (by simp only; omega),
        zero_smul, map_zero]
      rfl
    have hR1 : ∀ x : SA E hD,
        LaP (x * EA hD (esI k r ⟨r - m - 1, by omega⟩) (esI k r ⟨r - m - 2, by omega⟩)) = LaP x := by
      intro x
      rw [hLaP_apply, hLaP_apply, mul_assoc, (comm_TorV hD (r - (m + 2)) _ _ (hnot ⟨r - m - 1, by omega⟩ (by simp only; omega))
        (hnot ⟨r - m - 2, by omega⟩ le_rfl) P hP).eq, ← mul_assoc, La_apply, La_apply, Subalgebra.coe_mul,
        Module.End.mul_apply]
      conv_lhs => rw [hv]
      rw [root_action_on_truncated_vector hD z' hz' hRR hf hRf ⟨r - m - 1, by omega⟩ ⟨r - m - 2, by omega⟩ (by simp only; omega),
        if_pos (by simp only; omega), one_smul, ← hv]
    have hL : ∀ (x : SA E hD) (b : Fin r), r - m - 2 < b.val →
        LaP (EA hD (esI k r ⟨r - m - 2, by omega⟩) (esI k r b) * x) =
          (if b.val = r - m - 1 then ρ else 0) • LaP x := by
      intro x b hb
      rw [hLaP_apply, hLaP_apply, mul_assoc, La_apply, La_apply, Subalgebra.coe_mul, Module.End.mul_apply, EA_val,
        ev_E hD _ _ _ (hcell c hc), posL_cI, posL_cI]
      have hsm := (((x * P : SA E hD) : Module.End ℂ (VS k r 0 D E)) v₀).2.1
      have hle := leftEq_SA hD z hN (x * P) v₀ hLv
      rw [hLR E k r z D _ hz hD hN hsm hle c hc g₀ hg₀ (hcell c hc).2 b ⟨r - m - 2, by omega⟩ (by simp only; omega)]
      congr 1
      by_cases hbm : b.val = r - m - 1
      · have hb' : b = ⟨r - m - 1, by omega⟩ := Fin.ext hbm
        rw [if_pos (by simp only; omega), if_pos hbm, hρ, congrArg c hb']
      · rw [if_neg (by simp only; omega), if_neg hbm]
    have hX := hCh (SA E hD) E k r (EA (E := E) hD) LaP ρ (EA_gl (E := E) hD) m hm2 w hR0 hR1 hL
    set T := Tm (EA (E := E) hD) (w - ((m + 1 : ℕ) : ℂ)) (esI k r ⟨r - m - 2, by omega⟩)
      (esI k r ⟨r - m - 2, by omega⟩) with hT
    have hTmem : T ∈ TorV hD (r - (m + 1)) := by
      rw [hT]
      unfold Tm
      rw [if_pos rfl]
      exact Subalgebra.add_mem _ (Subalgebra.algebraMap_mem _ _) (EAs_mem_TorV hD ⟨r - m - 2, by omega⟩ (by simp only; omega))
    have hTP : T * P ∈ TorV hD (r - (m + 1)) := Subalgebra.mul_mem _ hTmem hP1
    have ih1 := ih (m + 1) (by omega) (by omega) (T * P) hTP c hc
    have ih0 := ih m (by omega) (by omega) P hP0 c hc
    rw [hLaP_apply, hLaP_apply, hLaP_apply, mul_assoc] at hX
    rw [hX, ih1, ih0, kvC_two]
    have hloc := kvC_loc w (m + 1) (fun c' => La hD v₀ (wCell k r (Fin.last r) c' * g₀) (T * P))
      (fun c' => (w - ((m + 1 : ℕ) : ℂ)) • La hD v₀ (wCell k r (Fin.last r) c' * g₀) P -
        pbN r (r - (m + 1) - 1) (fun c'' => La hD v₀ (wCell k r (Fin.last r) c'' * g₀) P) c')
      (fun c' hc' => by
        rw [hT, la_torus hD hTC v₀ g₀ hg₀ hcell ⟨r - m - 2, by omega⟩ _ P c' hc']
        unfold pbN
        rw [dif_pos (by omega)]
        have e : (⟨r - (m + 1) - 1, by omega⟩ : Fin r) = ⟨r - m - 2, by omega⟩ := Fin.ext (by simp only; omega)
        rw [e]) hc
    rw [hloc]
    congr 1
    unfold cbN cbiN
    rw [dif_pos (by omega), dif_pos (by omega)]
    have e1 : (⟨r - (m + 1), by omega⟩ : Fin r) = ⟨r - m - 1, by omega⟩ := Fin.ext (by simp only; omega)
    have e2 : (⟨r - (m + 1) - 1, by omega⟩ : Fin r) = ⟨r - m - 2, by omega⟩ := Fin.ext (by simp only; omega)
    rw [e1, e2]
    simp only [cbOp, cbiOp, hρ, div_eq_mul_inv, mul_smul]

end claim

end Formalism.FourierDecayAlt.P.CutMP.TVG
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadJOf
section
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.LevelPointCoordinates

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

theorem kapJ_eq (P : M.Par) (j : ℕ) : kapJ P j = levelZeroKernel P.k P.r j := rfl

theorem headJ_of (hW : WordInd) (hB : HeadBridge) : HeadJ := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj w h hh γ hF hw hγ hγ' φ hφ t ht e
  obtain ⟨X, _, μ, ℓ, Zx, Fx, Dm, φx, hDm, hDmsub, hR, hZ, hφx, hL, hRt⟩ :=
    hB Wp Wq P p F j hj w h hh γ hF hw hγ hγ' φ hφ t ht e
  have ht0 : t ≠ 0 := (ht.1 (1, t) (by simp)).2
  rw [hL, hRt]
  congr 1
  funext x
  rw [hW P.k P.r j hj _ _ (Wq →L[ℂ] Wp) Dm (Fx x) p.T.base.z_mem p.T.base.z'_mem hDm hDmsub (hR x) (Zx x) γ
    (hZ x).1 hγ (hZ x).2 w (φx x) (hφx x) t ht0 e, kapJ_eq]

end Formalism.FourierDecayAlt.P.LevelPointCoordinates
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.JAdjTrQQOfThree
section
namespace Formalism.FourierDecayAlt.P.CutMP.JA

theorem jAdjTrQQ_of_three (h1 : JDHatOpQQ) (h7 : JABddOpQQ) (h11 : JAStarOp) : JAdjTrQQ :=
  jAdjTrQQ_of_open h1 h7 h11 group_adjoint_transfer_holds local_class_transfer_holds

end Formalism.FourierDecayAlt.P.CutMP.JA
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.RuleOfEq
section
open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.LevelPointCoordinates

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.Qx5

def RuleOfEq : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ)
    (Φ : Q.Mx k r → E) (g : Q.Mx k r), inWb k r z' →
    (∀ n ∈ QuantumDeterminants.Nset k r, Φ (g * n) = psi k r z' cStd n • Φ g) →
    ∀ p q, C3.InNp k r p q → Q.EH k r p q Φ g = C3.dpsiP k r z' p q • Φ g

def AdjoinNL : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r j : ℕ) (hj : j + 1 ≤ r) (z : Fin (2 * r + k + 1) → ℂ)
    (Dm : Set (Q.Mx k r)) (hD : IsOpen Dm),
    (∀ g ∈ Q.Glev k r 0 ∩ Dm, ∀ a : Fin j → ℂ, nL k r j hj a * g ∈ Dm) →
    ∀ x ∈ Algebra.adjoin ℂ (Set.range fun pq : Fin (2 * r + k + 1) × Fin (2 * r + k + 1) =>
        (PBG.E0 (E := E) hD pq.1 pq.2 : Module.End ℂ (Formalism.FourierDecayAlt.P.Qx5.VS k r 0 Dm E))),
    ∀ v : Formalism.FourierDecayAlt.P.Qx5.VS k r 0 Dm E,
      (∀ g ∈ Q.Glev k r 0 ∩ Dm, ∀ a : Fin j → ℂ,
        (v : Q.Mx k r → E) (nL k r j hj a * g) = psi k r z cStd (nL k r j hj a) • (v : Q.Mx k r → E) g) →
      ∀ g ∈ Q.Glev k r 0 ∩ Dm, ∀ a : Fin j → ℂ,
        ((x v : Formalism.FourierDecayAlt.P.Qx5.VS k r 0 Dm E) : Q.Mx k r → E) (nL k r j hj a * g) =
          psi k r z cStd (nL k r j hj a) • ((x v : Formalism.FourierDecayAlt.P.Qx5.VS k r 0 Dm E) : Q.Mx k r → E) g

end Formalism.FourierDecayAlt.P.LevelPointCoordinates
end
end

