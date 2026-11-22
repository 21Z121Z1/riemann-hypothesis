import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointPinNorm
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HermitianZZEqNeg
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BDataOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0010

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointPinNormSt
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ComplexConjugate Matrix

namespace Formalism.L2.SG.Pf.Carrier.JointPinNormSt

open Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.EnergyCut Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.Carrier.JointQuot
  Formalism.L2.SG.Pf.Carrier.JointPin Formalism.L2.SG.Pf.Carrier.JointPinNorm Formalism.L2.SG.HidaSetting

section Lin

variable {n r : ℕ} (ε : Fin n → Bool)

theorem hJ_add_r (x y y' : Fin n → ℂ) : hJ ε x (y + y') = hJ ε x y + hJ ε x y' := by
  simp [hJ, Matrix.mulVec_add, dotProduct_add]

theorem hJ_sub_r (x y y' : Fin n → ℂ) : hJ ε x (y - y') = hJ ε x y - hJ ε x y' := by
  simp [hJ, Matrix.mulVec_sub, dotProduct_sub]

theorem hJ_smul_r (x : Fin n → ℂ) (c : ℂ) (y : Fin n → ℂ) : hJ ε x (c • y) = c * hJ ε x y := by
  simp [hJ, Matrix.mulVec_smul, dotProduct_smul]

theorem hJ_zero_r (x : Fin n → ℂ) : hJ ε x 0 = 0 := by
  simp [hJ]

theorem hJ_sum_r {ι : Type*} (s : Finset ι) (x : Fin n → ℂ) (f : ι → Fin n → ℂ) :
    hJ ε x (∑ i ∈ s, f i) = ∑ i ∈ s, hJ ε x (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hJ_zero_r]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hJ_add_r, ih]

theorem hJ_unit (M : Matrix (Fin n) (Fin n) ℂ) (hM : Mᴴ * Formalism.REAL.Jm ε * M = Formalism.REAL.Jm ε) (x y : Fin n → ℂ) :
    hJ ε (M *ᵥ x) (M *ᵥ y) = hJ ε x y := by
  unfold hJ
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM]

theorem hJ_conj_swap (x y : Fin n → ℂ) : hJ ε x y = conj (hJ ε y x) :=
  Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.hJ_conj ε x y

theorem recon (e u : Fin r → Fin n → ℂ) (κ : Fin r → ℂ) (hκ : ∀ d, κ d ≠ 0)
    (hue : ∀ d c, hJ ε (u d) (e c) = if d = c then κ d else 0) (s : Finset (Fin r)) (w : Fin n → ℂ)
    (hw : w ∈ Submodule.span ℂ (e '' ↑s)) : w = ∑ c ∈ s, (hJ ε (u c) w / κ c) • e c := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    rw [Finset.sum_eq_single b]
    · rw [hue, if_pos rfl, div_self (hκ b), one_smul]
    · intro c _ hcb; rw [hue, if_neg hcb, zero_div, zero_smul]
    · intro h; exact absurd hb h
  | zero => simp [hJ_zero_r]
  | add x y _ _ hx hy =>
    conv_lhs => rw [hx, hy]
    simp only [hJ_add_r, add_div, add_smul, Finset.sum_add_distrib]
  | smul t x _ hx =>
    conv_lhs => rw [hx]
    simp only [hJ_smul_r, Finset.smul_sum, smul_smul, mul_div_assoc]

theorem zero_of_pair (e u : Fin r → Fin n → ℂ) (κ : Fin r → ℂ) (hκ : ∀ d, κ d ≠ 0)
    (hue : ∀ d c, hJ ε (u d) (e c) = if d = c then κ d else 0) (s : Finset (Fin r)) (w : Fin n → ℂ)
    (hw : w ∈ Submodule.span ℂ (e '' ↑s)) (h0 : ∀ c ∈ s, hJ ε (u c) w = 0) : w = 0 := by
  rw [recon ε e u κ hκ hue s w hw]
  exact Finset.sum_eq_zero fun c hc => by rw [h0 c hc, zero_div, zero_smul]

theorem orth_span (e : Fin r → Fin n → ℂ) (x : Fin n → ℂ) (s : Set (Fin r)) (hx : ∀ c ∈ s, hJ ε x (e c) = 0)
    (w : Fin n → ℂ) (hw : w ∈ Submodule.span ℂ (e '' s)) : hJ ε x w = 0 := by
  induction hw using Submodule.span_induction with
  | mem y hy => obtain ⟨b, hb, rfl⟩ := hy; exact hx b hb
  | zero => exact hJ_zero_r ε x
  | add y y' _ _ hy hy' => rw [hJ_add_r, hy, hy', add_zero]
  | smul t y _ hy => rw [hJ_smul_r, hy, mul_zero]

theorem spanLt_eq (e : Fin r → Fin n → ℂ) (a : ℕ) :
    spanLt e a = Submodule.span ℂ (e '' ↑(Finset.univ.filter fun b : Fin r => b.1 < a)) := by
  unfold spanLt
  congr 2
  ext b
  simp

theorem st_one_lin (e : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (G Gi M : Matrix (Fin n) (Fin n) ℂ)
    (hGi : G * Gi = 1) (hG : Gᴴ * Formalism.REAL.Jm ε * G = Formalism.REAL.Jm ε)
    (hM : Mᴴ * Formalism.REAL.Jm ε * M = Formalism.REAL.Jm ε) (hee : ∀ a b, hJ ε (e a) (e b) = 0) (cv : Fin r → ℂ)
    (hcv : ∀ a, cv a ≠ 0) (hZ : ∀ a b, hJ ε (e a) (G *ᵥ e b) = if a = b then cv a else 0)
    (hN : InN ε e z M) (hN' : InN ε e z' (Gi * M * G)) : M = 1 := by
  classical
  have hGGi : ∀ x, G *ᵥ (Gi *ᵥ x) = x := fun x => by rw [Matrix.mulVec_mulVec, hGi, Matrix.one_mulVec]
  have hMG : ∀ x, G *ᵥ ((Gi * M * G) *ᵥ x) = M *ᵥ (G *ᵥ x) := fun x => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hGi, Matrix.one_mul]

  have hu1 : ∀ d c, hJ ε (G *ᵥ e d) (e c) = if d = c then conj (cv d) else 0 := by
    intro d c
    rw [hJ_conj_swap, hZ]
    by_cases h : c = d
    · subst h; simp
    · rw [if_neg h, if_neg (Ne.symm h), map_zero]
  have hu2 : ∀ d c, hJ ε (Gi *ᵥ e d) (e c) = if d = c then cv d else 0 := by
    intro d c
    rw [← hJ_unit ε G hG, hGGi, hZ]
  have hk1 : ∀ d, conj (cv d) ≠ 0 := fun d => by simpa using hcv d
  have hfx : ∀ x y, M *ᵥ x = x → hJ ε x (M *ᵥ y) = hJ ε x y := fun x y hx => by
    conv_lhs => rw [← hx]
    exact hJ_unit ε M hM x y

  have key : ∀ m : ℕ, ∀ c : Fin r, c.1 = m → M *ᵥ e c = e c ∧ M *ᵥ (G *ᵥ e c) = G *ᵥ e c := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro c hc
      have ih' : ∀ d : Fin r, d.1 < c.1 → M *ᵥ e d = e d ∧ M *ᵥ (G *ᵥ e d) = G *ᵥ e d :=
        fun d hd => ih d.1 (hc ▸ hd) d rfl
      have h1 : M *ᵥ e c = e c := by
        have hw := hN.1.1 c
        rw [spanLt_eq] at hw
        have h0 := zero_of_pair ε e (fun d => G *ᵥ e d) (fun d => conj (cv d)) hk1 hu1 _ _ hw (by
          intro d hd
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
          rw [Matrix.sub_mulVec, Matrix.one_mulVec, hJ_sub_r, hfx _ _ (ih' d hd).2, sub_self])
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h0
        exact h0
      refine ⟨h1, ?_⟩
      have hw := hN'.1.1 c
      rw [spanLt_eq] at hw
      have h0 := zero_of_pair ε e (fun d => Gi *ᵥ e d) cv hcv hu2 _ _ hw (by
        intro d hd
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
        rw [← hJ_unit ε G hG, hGGi, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, hMG, hJ_sub_r,
          hfx _ _ (ih' d hd).1, sub_self])
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h0
      rw [← hMG, h0]
  have hfix1 : ∀ c, M *ᵥ e c = e c := fun c => (key c.1 c rfl).1
  have hfix2 : ∀ c, M *ᵥ (G *ᵥ e c) = G *ᵥ e c := fun c => (key c.1 c rfl).2

  have hall : ∀ v, M *ᵥ v = v := by
    intro v
    set S1 : Fin n → ℂ := ∑ c, (hJ ε (G *ᵥ e c) v / conj (cv c)) • e c with hS1
    set S2 : Fin n → ℂ := ∑ c, (hJ ε (e c) v / cv c) • (G *ᵥ e c) with hS2
    set v1 := v - S1 - S2 with hv1
    have hGe : ∀ d c, hJ ε (G *ᵥ e d) (G *ᵥ e c) = 0 := fun d c => by rw [hJ_unit ε G hG, hee]
    have ho1 : ∀ d, hJ ε (e d) v1 = 0 := by
      intro d
      rw [hv1, hJ_sub_r, hJ_sub_r, hS1, hS2, hJ_sum_r, hJ_sum_r]
      simp only [hJ_smul_r, hee, mul_zero, Finset.sum_const_zero, sub_zero, hZ]
      rw [Finset.sum_eq_single d (fun c _ hc => by rw [if_neg (Ne.symm hc), mul_zero]) (by simp), if_pos rfl,
        div_mul_cancel₀ _ (hcv d), sub_self]
    have ho2 : ∀ d, hJ ε (G *ᵥ e d) v1 = 0 := by
      intro d
      rw [hv1, hJ_sub_r, hJ_sub_r, hS1, hS2, hJ_sum_r, hJ_sum_r]
      simp only [hJ_smul_r, hGe, mul_zero, Finset.sum_const_zero, sub_zero, hu1]
      rw [Finset.sum_eq_single d (fun c _ hc => by rw [if_neg (Ne.symm hc), mul_zero]) (by simp), if_pos rfl,
        div_mul_cancel₀ _ (hk1 d), sub_self]
    have hv : v = v1 + S1 + S2 := by rw [hv1]; abel
    clear_value v1 S1 S2

    have hX : (M - 1) *ᵥ v1 ∈ spanLt e r := hN.2 v1 ho1
    have hGX : (Gi * M * G - 1) *ᵥ (Gi *ᵥ v1) ∈ spanLt e r :=
      hN'.2 _ (fun a => by rw [← hJ_unit ε G hG, hGGi]; exact ho2 a)
    have hw : (M - 1) *ᵥ v1 = G *ᵥ ((Gi * M * G - 1) *ᵥ (Gi *ᵥ v1)) := by
      rw [Matrix.sub_mulVec (Gi * M * G), Matrix.mulVec_sub, hMG, hGGi, Matrix.one_mulVec, hGGi,
        Matrix.sub_mulVec, Matrix.one_mulVec]
    rw [spanLt_eq] at hX
    have h0 := zero_of_pair ε e (fun d => G *ᵥ e d) (fun d => conj (cv d)) hk1 hu1 _ _ hX (by
      intro d _
      rw [hw, hJ_unit ε G hG]
      exact orth_span ε e (e d) _ (fun c _ => hee d c) _ hGX)
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h0
    rw [hv, Matrix.mulVec_add, Matrix.mulVec_add, h0, hS1, hS2, Matrix.mulVec_sum, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul, hfix1, hfix2]
  exact Matrix.ext_of_mulVec_single fun i => by rw [hall, Matrix.one_mulVec]

end Lin

variable {D : D7}

theorem stOne_holds (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) : StOne X u u' := by
  intro v g cv hcv hZ
  have hee : ∀ a b, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.eR b)) = 0 := fun a b => by
    rw [show X.eR a = X.crd (X.eX a) from rfl, show X.eR b = X.crd (X.eX b) from rfl,
      Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.hJ_rvX, X.ee, map_zero]
  have hfrm : ∀ (w : D.what₂.Word) (c : Fin D.R.rS), frm X w 1 v (Fin.castSucc c) = rv X.B.I v (X.eR c) := by
    intro w c
    simp [frm, famSc, fam, Fin.snoc_castSucc]
  have hZ' : ∀ a b : Fin D.R.rS, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (uMat g *ᵥ rv X.B.I v (X.eR b)) =
      if a = b then cv (Fin.castSucc a) else 0 := by
    intro a b
    have := congrFun (congrFun hZ (Fin.castSucc a)) (Fin.castSucc b)
    unfold Formalism.L2.SG.RealObj.Zhat at this
    simp only [hfrm, Matrix.diagonal_apply, Fin.castSucc_inj] at this
    exact this
  have hmemUJ : ∀ y : Formalism.REAL.UJ (X.B.I.ε v), (uMat y)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * uMat y = Formalism.REAL.Jm (X.B.I.ε v) :=
    fun y => y.2
  have hone : (1 : Formalism.REAL.UJ (X.B.I.ε v)) ∈ StSet (NV X u v) (NV X u' v) g := by
    have h1 : ∀ w : D.what₂.Word, (1 : Formalism.REAL.UJ (X.B.I.ε v)) ∈ NV X w v := by
      intro w
      show InN _ _ _ (uMat (1 : Formalism.REAL.UJ (X.B.I.ε v)))
      have : uMat (1 : Formalism.REAL.UJ (X.B.I.ε v)) = 1 := rfl
      rw [this]
      refine ⟨⟨fun a => ?_, ?_⟩, fun y _ => ?_⟩ <;> simp [Submodule.zero_mem]
    refine ⟨h1 u, ?_⟩
    rw [mul_one, inv_mul_cancel]
    exact h1 u'
  ext y
  refine ⟨fun hy => ?_, fun hy => by rw [Set.mem_singleton_iff.1 hy]; exact hone⟩
  obtain ⟨hy1, hy2⟩ := hy
  have hcoe : uMat (g⁻¹ * y * g) = uMat g⁻¹ * uMat y * uMat g := by
    simp [uMat]
  have hGi : uMat g * uMat g⁻¹ = 1 := by
    simp [uMat]
  have hN' : InN (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u')) (uMat g⁻¹ * uMat y * uMat g) := by
    rw [← hcoe]; exact hy2
  have hM := st_one_lin (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) (rv X.B.I v (X.zR u'))
    (uMat g) (uMat g⁻¹) (uMat y) hGi (hmemUJ g) (hmemUJ y) hee (fun a => cv (Fin.castSucc a))
    (fun a => hcv.1 _) hZ' hy1 hN'
  rw [Set.mem_singleton_iff]
  apply Subtype.ext
  apply Units.ext
  exact hM

theorem normBridge_of_zhat {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word} (P : Parts X u u')
    (hr : P.S.G.r = D.R.rS) (hZ : ZhatTr P hr) : NormBridge P hr :=
  normBridge_of_two P hr (stOne_holds X u u') hZ

end Formalism.L2.SG.Pf.Carrier.JointPinNormSt
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.JointAmplitudePoints
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.LocWSOf
open scoped ENNReal

namespace Formalism.L2.SG.Pf.JointAmplitudePoints

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Pt

variable {D : D7} {X : HidaSetting D} {θ : ℝ} (C : Choice X θ) (u u' : D.what₂.Word)

def gamP (w : Point D.host.E (D.R.rS + 1)) (τ : D.what₂.Tau) : MatKR D.R.k D.R.rS :=
  Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) ((Formalism.L2.SG.RealObj.gamW X u u' w) (vOf X τ))

def ptP (w : Point D.host.E (D.R.rS + 1)) (τ : D.what₂.Tau) : Point ℂ (D.R.rS + 1) :=
  if h : ∃ p, RelPt D (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (gamP C u u' w τ) p ∧
      Formalism.MainNotions.S.Pv.Frames.turnPt p = ptLoc D τ w then h.choose else Formalism.L2.SG.Pf.LTL.pt0 D

def nu1P (w : Point D.host.E (D.R.rS + 1)) (τ : D.what₂.Tau) : Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) :=
  if h : ∃ ν, RMeas D (locW C u u' τ) (gamP C u u' w τ) 1 ν then h.choose else 0

variable {C} (hB : WuBessel C)

def localAmplitudeProduct (w : Point D.host.E (D.R.rS + 1)) : ℝ :=
  ∏ τ, hsNormSq ((locS hB u u' τ).J (nu1P C u u' w τ) (gamP C u u' w τ))

def thetaP (J2 : ℝ) (w : Point D.host.E (D.R.rS + 1)) : ℝ :=
  if 0 < J2 ∧ 0 < localAmplitudeProduct u u' hB w then
    (localAmplitudeProduct u u' hB w / J2) ^ ((1 : ℝ) / (2 * Fintype.card D.what₂.Tau))
  else 1

end Pt

section Stmts

variable {D : D7} {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word) (ν : X.B.I.Ginf → Measure X.B.I.Ginf)
  {θ : ℝ} (C : Choice X θ) (hB : WuBessel C)

def RelPtExP : Prop :=
  ∀ w : Point D.host.E (D.R.rS + 1), Formalism.L2.SG.ThmBUse.IsRowPt D (D.mem u).A.T (D.mem u').A.T w →
    (∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w g) → ∀ τ,
      ∃ p, RelPt D (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (gamP C u u' w τ) p ∧
        Formalism.MainNotions.S.Pv.Frames.turnPt p = ptLoc D τ w

def RMeasExP : Prop :=
  ∀ w : Point D.host.E (D.R.rS + 1), Formalism.L2.SG.ThmBUse.IsRowPt D (D.mem u).A.T (D.mem u').A.T w →
    (∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w g) → ∀ τ, ∃ ν₁, RMeas D (locW C u u' τ) (gamP C u u' w τ) 1 ν₁

def LocalAmplitudesPositive : Prop :=
  ∀ w : Point D.host.E (D.R.rS + 1), Formalism.L2.SG.ThmBUse.IsRowPt D (D.mem u).A.T (D.mem u').A.T w →
    0 < J2of Y u u' ν (toPts w) → 0 < localAmplitudeProduct u u' hB w

def ThetaWinP (large₂ : SizeData₂ D) (C1 : ℝ) : Prop :=
  ∀ w : Point D.host.E (D.R.rS + 1), Formalism.L2.SG.ThmBUse.IsRowPt D (D.mem u).A.T (D.mem u').A.T w →
    0 < J2of Y u u' ν (toPts w) → normWin D large₂ C1 (thetaP u u' hB (J2of Y u u' ν (toPts w)) w)

end Stmts

section Proof

variable {D : D7} {X : HidaSetting D}

theorem card_pos' (D : D7) : 0 < Fintype.card D.what₂.Tau := by
  first
  | (haveI : Nonempty D.what₂.Tau := ⟨D.eTau.symm 1⟩; exact Fintype.card_pos)
  | (haveI : Nonempty D.what₂.Tau := ⟨D.eTau.symm ⟨1, one_mem _⟩⟩; exact Fintype.card_pos)

def ofPts {K : Type} {i : ℕ} (s : Σ c : Composition (i + 1), (Fin c.length → K)) : List (K × ℕ) :=
  List.ofFn fun a => (s.2 a, s.1.blocksFun a)

theorem ofPts_toPts {K : Type} [Zero K] {i : ℕ} (p : Point K (i + 1)) : ofPts (toPts p) = p.1 := by
  first
  | (apply List.ext_getElem <;> simp [ofPts, toPts, Composition.blocksFun, Composition.length])
  | (apply List.ext_get <;> simp [ofPts, toPts, Composition.blocksFun, Composition.length])

theorem toPts_injective {K : Type} [Zero K] {i : ℕ} :
    Function.Injective (toPts : Point K (i + 1) → Σ c : Composition (i + 1), (Fin c.length → K)) := by
  intro p q h
  have h' := congrArg ofPts h
  rw [ofPts_toPts, ofPts_toPts] at h'
  exact Subtype.ext h'

theorem isPtRep_of_J2of {Y : Full X} {u u' : D.what₂.Word} {ν : X.B.I.Ginf → Measure X.B.I.Ginf}
    {w : Point D.host.E (D.R.rS + 1)} (h : 0 < J2of Y u u' ν (toPts w)) :
    ∃ w' : Point D.host.E (D.R.rS + 1), toPts w' = toPts w ∧ ∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w' g := by
  unfold J2of at h
  split_ifs at h with hc
  · exact hc
  · exact absurd h (lt_irrefl 0)

theorem jointAmplitudeFactorization_of_inj (Y : Full X) (u u' : D.what₂.Word) (large₂ : SizeData₂ D) (C1 : ℝ) {θ : ℝ} (C : Choice X θ)
    (hB : WuBessel C) (ν νL : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : Formalism.FourierDecayAlt.PN.Pts D.host.E D.R.rS → ℝ)
    (hinj : ∀ w w' : Point D.host.E (D.R.rS + 1), toPts w = toPts w' → w = w')
    (hR : RelPtExP u u' C) (hM : RMeasExP u u' C) (hP : LocalAmplitudesPositive Y u u' ν C hB) (hT : ThetaWinP Y u u' ν C hB large₂ C1) :
    Formalism.L2.SG.Pf.BDat.JointAmplitudeFactorization (Y.tO u u') (NOf2 Y u u' νL ν ng) large₂ C1 (Formalism.L2.SG.Pf.BDat.WX C u u')
      (Formalism.L2.SG.Pf.BDat.AX hB u u') (D.mem u).A.T (D.mem u').A.T 1 := by
  intro γ w _ hw hb hJ
  subst hw
  have hJ' : 0 < J2of Y u u' ν (toPts w) := hJ
  obtain ⟨w', hw', g0, hg0⟩ := isPtRep_of_J2of hJ'
  have hw'w : w' = w := hinj _ _ hw'
  subst hw'w
  have hrep : ∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w' g := ⟨g0, hg0⟩
  have hP1 := hP w' hb hJ'
  set J2 := J2of Y u u' ν (toPts w') with hJ2
  set th := thetaP u u' hB J2 w' with hth
  have hthv : th = (localAmplitudeProduct u u' hB w' / J2) ^ ((1 : ℝ) / (2 * Fintype.card D.what₂.Tau)) := by
    rw [hth]; unfold thetaP; rw [if_pos ⟨hJ', hP1⟩]
  have hth0 : 0 < th := by rw [hthv]; exact Real.rpow_pos_of_pos (div_pos hP1 hJ') _
  have hfc : (0 : ℝ) < 2 * Fintype.card D.what₂.Tau := by
    have := card_pos' D; positivity
  have hpow : th ^ (2 * Fintype.card D.what₂.Tau) = localAmplitudeProduct u u' hB w' / J2 := by
    rw [hthv, ← Real.rpow_natCast, ← Real.rpow_mul (div_pos hP1 hJ').le]
    push_cast
    rw [one_div_mul_cancel hfc.ne', Real.rpow_one]
  refine ⟨gamP C u u' w', ptP C u u' w', fun _ => th,
    fun τ => (ENNReal.ofReal th)⁻¹ • nu1P C u u' w' τ, fun τ => ?_, ?_⟩
  · have hpt : ∃ p, RelPt D (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (gamP C u u' w' τ) p ∧
        Formalism.MainNotions.S.Pv.Frames.turnPt p = ptLoc D τ w' := hR w' hb hrep τ
    have hnu : ∃ ν₁, RMeas D (locW C u u' τ) (gamP C u u' w' τ) 1 ν₁ := hM w' hb hrep τ
    have hp := hpt.choose_spec
    have hptP : ptP C u u' w' τ = hpt.choose := by unfold ptP; rw [dif_pos hpt]
    have hnuP : nu1P C u u' w' τ = hnu.choose := by unfold nu1P; rw [dif_pos hnu]
    refine ⟨?_, hT w' hb hJ', ?_, ?_⟩
    · rw [hptP]; exact hp.1
    · obtain ⟨p, μR, hR1, hQ⟩ := hnu.choose_spec
      refine ⟨p, μR, hR1, ?_⟩
      show IsQuotMeas _ (ENNReal.ofReal th • μR) ((ENNReal.ofReal th)⁻¹ • nu1P C u u' w' τ)
      rw [hnuP]
      have hQ' : IsQuotMeas (Formalism.L2.SG.Pf.BDat.WX C u u' τ).μG μR hnu.choose := by
        simpa [ENNReal.ofReal_one, one_smul] using hQ
      exact Formalism.L2.SG.Pf.LTL.isQuotMeas_smul hQ' (by simpa using hth0) ENNReal.ofReal_ne_top
    · rw [hptP]; exact hp.2
  ·
    have hloc : ∀ τ, hsNormSq ((Formalism.L2.SG.Pf.BDat.AX hB u u' τ).J ((ENNReal.ofReal th)⁻¹ • nu1P C u u' w' τ)
        (gamP C u u' w' τ)) = (th ^ 2)⁻¹ *
          hsNormSq ((locS hB u u' τ).J (nu1P C u u' w' τ) (gamP C u u' w' τ)) := by
      intro τ
      rw [Formalism.L2.SG.Pf.LTL.locJ_smul, Formalism.L2.SG.Pf.LTL.hsNormSq_smul, ENNReal.toReal_inv,
        ENNReal.toReal_ofReal hth0.le, Complex.normSq_ofReal]
      congr 1
      rw [sq, mul_inv]
    have hprod : ∏ τ, hsNormSq ((Formalism.L2.SG.Pf.BDat.AX hB u u' τ).J ((ENNReal.ofReal th)⁻¹ • nu1P C u u' w' τ)
        (gamP C u u' w' τ)) = J2 := by
      rw [Finset.prod_congr rfl fun τ _ => hloc τ, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
      change ((th ^ 2)⁻¹) ^ Fintype.card D.what₂.Tau * localAmplitudeProduct u u' hB w' = J2
      rw [inv_pow, ← pow_mul, hpow]
      field_simp
    have hnn : ∀ τ, 0 ≤ hsNormSq ((Formalism.L2.SG.Pf.BDat.AX hB u u' τ).J ((ENNReal.ofReal th)⁻¹ • nu1P C u u' w' τ)
        (gamP C u u' w' τ)) := fun τ => Formalism.L2.SG.Pf.LTL.hsNormSq_nonneg _
    rw [ENNReal.ofReal_one, one_mul, ← ENNReal.ofReal_prod_of_nonneg (fun τ _ => hnn τ), hprod]
    exact le_rfl

theorem jointAmplitudeFactorization_of (Y : Full X) (u u' : D.what₂.Word) (large₂ : SizeData₂ D) (C1 : ℝ) {θ : ℝ} (C : Choice X θ)
    (hB : WuBessel C) (ν νL : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : Formalism.FourierDecayAlt.PN.Pts D.host.E D.R.rS → ℝ)
    (hR : RelPtExP u u' C) (hM : RMeasExP u u' C) (hP : LocalAmplitudesPositive Y u u' ν C hB) (hT : ThetaWinP Y u u' ν C hB large₂ C1) :
    Formalism.L2.SG.Pf.BDat.JointAmplitudeFactorization (Y.tO u u') (NOf2 Y u u' νL ν ng) large₂ C1 (Formalism.L2.SG.Pf.BDat.WX C u u')
      (Formalism.L2.SG.Pf.BDat.AX hB u u') (D.mem u).A.T (D.mem u').A.T 1 :=
  jointAmplitudeFactorization_of_inj Y u u' large₂ C1 C hB ν νL ng (fun w w' h => toPts_injective h) hR hM hP hT

theorem rowBData_of (large₂ : SizeData₂ D) (Y : Full X) (u u' : D.what₂.Word) (ν : X.B.I.Ginf → Measure X.B.I.Ginf)
    (C1 Cn Ire : ℝ) (hIre : 0 ≤ Ire) {θ : ℝ} (C : Choice X θ) (hB : WuBessel C) (hθ0 : 0 < θ)
    (hθw : normWin D large₂ C1 θ)
    (hloc : ∀ τ, ColsTypeTr C u τ ∧ ColsTypeTr C u' τ ∧ ZTr C u τ ∧ ZTr C u' τ ∧ HaarTr C τ ∧ GoodSRest hB u u' τ)
    (hR : RelPtExP u u' C) (hM : RMeasExP u u' C) (hP : LocalAmplitudesPositive Y u u' ν C hB) (hT : ThetaWinP Y u u' ν C hB large₂ C1)
    (hN : ∀ sec : D.what₂.Tau → ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ,
        (∀ τ, Formalism.QuantumDeterminants.IsSection D.R.k D.R.rS (Formalism.L2.SG.Pf.BDat.WX C u u' τ).z (Formalism.L2.SG.Pf.BDat.WX C u u' τ).z'
          (sec τ)) →
        ∏ τ, MMv D u u' (Formalism.L2.SG.Pf.BDat.AX hB u u' τ) (sec τ) ≤
          ENNReal.ofReal (large₂.sc.b ^ (Cn * (D.R.m : ℝ) ^ 2 * D.R.f) * Ire)) :
    Formalism.L2.SG.Pf.BDat.RowBData large₂ Y u u' ν C1 Cn Ire := by
  unfold Formalism.L2.SG.Pf.BDat.RowBData
  exact ⟨hIre, θ, C, hB, hθ0, hθw, hloc, 1, zero_le_one,
    fun νL ng => jointAmplitudeFactorization_of Y u u' large₂ C1 C hB ν νL ng hR hM hP hT,
    fun sec hsec => by simpa using hN sec hsec⟩

end Proof

end Formalism.L2.SG.Pf.JointAmplitudePoints
end
end

