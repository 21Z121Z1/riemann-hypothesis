import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.Bundle0007
import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0003
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeMemAvoidedPrimes
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsRefill
import Formalism.LocalRingCardinality.HostCls
import Development.AutomorphicArithmetic.ThickFrames.topsBase
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0067
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0104
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0102
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Formalism.LocalToGlobal.Columns.TiedValLatG
import Formalism.LocalToGlobal.Columns.CoefModB
import Formalism.LocalToGlobal.KernelLattices.Bundle0001
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0014
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0080
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0093
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0103
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0086
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0105

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ClassC0PrimeExceedsSplitBound
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

namespace GlobalTheory.EX.TopsOfHost

theorem topsChoice_of
    (hnum : ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ Cb x₀ : ℝ, 0 < Cb ∧ ∀ s : Scale, s.eps = eps → x₀ ≤ s.x → ∀ e L₂ : ℕ, s.x ^ Formalism.MainNotions.G.hG s / 2 ≤ ((2 ^ e : ℕ) : ℝ) → ((2 ^ e : ℕ) : ℝ) ≤ 2 * s.x ^ Formalism.MainNotions.G.hG s → (L₂ : ℝ) ≤ 1242 / eps → ∀ bs : ZMod (2 ^ e) → ZMod (2 ^ e) → ZMod (2 ^ e), (∀ h t, ∃ i : ℕ, bs h t + i • h = t) → (∀ h t, bs h (t + h) = bs h t) → ∀ (PP : Finset ℕ) (hp : ℕ → ZMod (2 ^ e)) (ω : ℕ → ℝ), (∀ p, 0 ≤ ω p) → (∀ p ∈ PP, s.x ^ (eps / 4) ≤ (addOrderOf (hp p) : ℝ)) → ∃ TT : Finset (ZMod (2 ^ e)), s.delta1 * ((2 ^ e : ℕ) : ℝ) / 2 ≤ (TT.card : ℝ) ∧ (TT.card : ℝ) ≤ 2 * s.delta1 * ((2 ^ e : ℕ) : ℝ) ∧ ∑ p ∈ PP, ω p * (({t : ZMod (2 ^ e) | t ∈ TT ∧ ¬ Formalism.MainNotions.G.IsGoodOrbit (addOrderOf (hp p)) (Finset.univ.filter (fun i : Fin (addOrderOf (hp p)) => bs (hp p) t + (i : ℕ) • hp p ∈ TT)) L₂ (Formalism.MainNotions.G.KG s) (Formalism.MainNotions.G.rG s) s.delta1 (Formalism.MainNotions.G.hG s) s.x}.ncard : ℕ) : ℝ) ≤ 4 * (Cb * s.x ^ (-2 : ℝ)) * s.delta1 * ((2 ^ e : ℕ) : ℝ) * ∑ p ∈ PP, ω p) : TopsChoice := by
  intro eps Co he he'
  obtain ⟨Cb, x0, hCb, h⟩ := UpperTheory.BernoulliSumsFrobeniusOrbits.topsBase eps (max Co 2) he he' (le_trans one_le_two (le_max_right _ _))
  refine ⟨Cb, x0, hCb, fun s R H hs hx hR hJC ho hsb => ?_⟩
  subst hs
  have hx0 : 0 < s.x := lt_trans one_pos s.one_lt_alt
  have hJ : 1 ≤ s.J := s.one_le_J
  have hCo : Co ≤ max Co 2 := le_max_left _ _
  have hpw : 0 < s.x ^ (2 + 8 * s.eps) := Real.rpow_pos_of_pos hx0 _
  have hn1 : s.x ^ (2 + 8 * s.eps) / 2 ≤ (R.n : ℝ) := by linarith [hR.n_lo]
  have hn2 : (R.n : ℝ) ≤ max Co 2 * s.x ^ (2 + 8 * s.eps) :=
    hR.n_up.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hpw.le)
  have ho' : (R.toFrame.o : ℝ) ≤ max Co 2 := ho.trans hCo
  have hp : ∀ p : ℕ, p.Prime → H.cls p = PrimeClass.inertClass → s.x ^ (s.eps / (5 * max Co 2)) < p := by
    intro p hp hc
    obtain ⟨h2, -, -, h5, -⟩ := (primeClass_eq_inert_iff H.toHostRaw).1 hc
    have h2' : p ≠ 2 := by
      rintro rfl
      exact h2 H.two_mem_small
    have h6 : ⌊s.x ^ (s.ez / 5)⌋₊ < p := by
      by_contra hle
      exact h5 (H.split_small p hp h2' ((not_lt.mp hle).trans hsb))
    have h7 : s.x ^ (s.ez / 5) < p := (Nat.floor_lt (Real.rpow_nonneg hx0.le _)).1 h6
    refine lt_of_le_of_lt (Real.rpow_le_rpow_of_exponent_le s.one_lt_alt.le ?_) h7
    unfold Scale.ez
    rw [div_div]
    exact div_le_div_of_nonneg_left s.eps_pos.le (by linarith) (by linarith)
  obtain ⟨TT, t1, t2, t3, t4⟩ := h (baseOf s 0 0 H) (hPH H) rfl hx hn1 hn2 ho' hR.2.2.1.2 hp
  exact ⟨TT, t1, t2, t4, t3⟩

end GlobalTheory.EX.TopsOfHost

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsExplicitParameters
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem bottom_window_le (eps : ℝ) (K : G.Consts) (h0 : 0 < eps) (h1 : eps < 1 / 52) (hK : 1 ≤ K.La) :
    ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks), s.eps = eps → x0 ≤ s.x → RankVal s R →
      2 * (R.n : ℝ) * s.delta1 * s.x ^ s.eps * G.La K s * s.b' / (R.k : ℝ) ≤ s.b' := by
  obtain ⟨CN, x1, hx1⟩ := GlobalTheory.topCount_and_lambda_bounds eps h0 h1
  refine ⟨max x1 (32 * K.La * CN ^ 2), fun s R he hx hR => ?_⟩
  obtain ⟨-, -, hLa⟩ := hx1 s he (le_trans (le_max_left _ _) hx)
  obtain ⟨hLa1, hLa2⟩ := hLa K hK
  have hx2 : 32 * K.La * CN ^ 2 ≤ s.x := le_trans (le_max_right _ _) hx
  obtain ⟨⟨-, hn⟩, -, ⟨hk, -⟩, -⟩ := hR
  have hx1' : 1 < s.x := s.one_lt_alt
  have hxp : 0 < s.x := by linarith
  have hb : 0 < s.b' := by
    unfold Scale.b' Scale.a Scale.b Scale.X'
    positivity
  have hkp : (0 : ℝ) < R.k := lt_of_lt_of_le (Real.rpow_pos_of_pos hxp _) hk
  have hd0 : 0 < s.delta1 := Real.rpow_pos_of_pos hxp _
  have hd1 : s.delta1 ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1'.le (by have := s.eps_pos; linarith)
  have hy : 0 < s.x ^ s.eps := Real.rpow_pos_of_pos hxp _
  have hlog0 : 0 ≤ Real.log s.x := Real.log_nonneg hx1'.le
  have hlog : Real.log s.x ^ 2 ≤ 4 * s.x := by
    have h := Real.log_le_rpow_div hxp.le (show (0 : ℝ) < 1 / 2 by norm_num)
    have h2 : (s.x ^ (1 / 2 : ℝ)) ^ 2 = s.x := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hxp.le]; norm_num
    calc Real.log s.x ^ 2 ≤ (s.x ^ (1 / 2 : ℝ) / (1 / 2)) ^ 2 := pow_le_pow_left₀ hlog0 h 2
      _ = 4 * (s.x ^ (1 / 2 : ℝ)) ^ 2 := by ring
      _ = 4 * s.x := by rw [h2]
  have hKC : 0 ≤ K.La * CN ^ 2 := by positivity
  have hLa3 : G.La K s ≤ s.x ^ (2 : ℝ) / 4 * s.x ^ s.eps := by
    refine hLa2.trans ?_
    rw [Real.rpow_two]
    have : K.La * CN ^ 2 * Real.log s.x ^ 2 ≤ s.x / 32 * (4 * s.x) :=
      mul_le_mul (by linarith) hlog (by positivity) (by positivity)
    nlinarith
  have hLa0 : 0 ≤ G.La K s := hy.le.trans hLa1
  have hmain : 2 * (R.n : ℝ) * s.delta1 * s.x ^ s.eps * G.La K s ≤ R.k := by
    calc 2 * (R.n : ℝ) * s.delta1 * s.x ^ s.eps * G.La K s
        ≤ 2 * (2 * s.x ^ (2 + 8 * s.eps)) * 1 * s.x ^ s.eps * (s.x ^ (2 : ℝ) / 4 * s.x ^ s.eps) := by
          gcongr
      _ = s.x ^ (2 + 8 * s.eps) * s.x ^ s.eps * s.x ^ (2 : ℝ) * s.x ^ s.eps := by ring
      _ = s.x ^ (2 + 8 * s.eps + s.eps + 2 + s.eps) := by
          rw [← Real.rpow_add hxp, ← Real.rpow_add hxp, ← Real.rpow_add hxp]
      _ ≤ s.x ^ (9 / 2 + 10 * s.eps) := Real.rpow_le_rpow_of_exponent_le hx1'.le (by linarith)
      _ ≤ R.k := hk
  rw [div_le_iff₀ hkp]
  nlinarith

theorem middle_between {R : Ranks} (p : HCParam R) {S : ℝ}
    (hv : ∀ i : Fin (R.k - 1), 0 ≤ ((p.v i : ℚ) : ℝ) ∧ ((p.v i : ℚ) : ℝ) ≤ S) (i : Fin R.k) (h1 : 1 ≤ i.1)
    (h2 : i.1 + 1 < R.k) : 0 ≤ ((p.u i : ℚ) : ℝ) ∧ ((p.u i : ℚ) : ℝ) ≤ S := by
  obtain ⟨i, hi⟩ := i
  simp only at h1 h2
  have ha := p.u_gt_v ⟨i, by omega⟩
  have hb := p.v_gt_u ⟨i - 1, by omega⟩
  have he : (⟨i - 1 + 1, by omega⟩ : Fin R.k) = ⟨i, hi⟩ := Fin.ext (by simp only; omega)
  simp only [he] at hb
  have ha' : ((p.v ⟨i, by omega⟩ : ℚ) : ℝ) < ((p.u ⟨i, hi⟩ : ℚ) : ℝ) := by exact_mod_cast ha
  have hb' : ((p.u ⟨i, hi⟩ : ℚ) : ℝ) < ((p.v ⟨i - 1, by omega⟩ : ℚ) : ℝ) := by exact_mod_cast hb
  exact ⟨(hv _).1.trans ha'.le, hb'.le.trans (hv _).2⟩

theorem exists_sizeData_explicit : ∀ (eps : ℝ) (C : FC) (cD ch : ℝ), 0 < eps → eps < 1 / 52 → Std C → 0 ≤ cD → 402 ≤ ch → ∃ x0 : ℝ, ∀ (s : Scale) (D : D7) (aT bT : D.host.TT → ℤ), s.eps = eps → x0 ≤ s.x → RankVal s D.R → HostVal s C.P.Cpde D.host → HCVal s cD ch D.host (fun τ => (D.eTau τ : D.R.GG)) D.hc bT → |dlogH D.host| ≤ s.x ^ s.eps → D.s.Del = (Delv s cD : ℚ) → D.host.CT2 = C.CT2 → Fintype.card D.what₂.Word = ⌈3 * Real.exp (C.CGam * (D.R.m : ℝ) ^ 5 * D.R.f * s.L) ^ 2 * s.x ^ C.P.CF⌉₊ → D.div.etaF = 6 * s.x ^ (-C.P.CF) → (∀ u, Real.log (D.mem u).A.GamP = C.CGam * (D.R.m : ℝ) ^ 5 * D.R.f * s.L) → (∀ t, (s.a ≤ (aT t : ℝ) ∧ (aT t : ℝ) ≤ s.a + s.a / ((D.R.k : ℝ) * s.x ^ (Scale.A / 2))) ∧ s.b' ≤ (bT t : ℝ) ∧ (bT t : ℝ) ≤ s.b' + 2 * (D.R.n : ℝ) * s.delta1 * s.x ^ s.eps * G.La C.GK s * s.b' / (D.R.k : ℝ)) → (∀ τ (t : D.host.TT) (h : 0 < D.R.k), (D.eTau τ : D.R.GG) = D.R.tau1 t → (D.hc τ).u ⟨0, h⟩ = (aT t : ℚ) + ((D.R.k : ℚ) - 1) / 2 ∧ (D.hc τ).u ⟨D.R.k - 1, by omega⟩ = -(bT t : ℚ) - ((D.R.k : ℚ) - 1) / 2) → (∀ w, D.what₂.muAt w = D.what₂.mu0 → ∀ j, 1 ≤ j → j ≤ D.R.m → D.what₂.Aj j w = 0) → ∃ L : SizeData₂ D, L.sc = s ∧ L.aT = aT ∧ L.bT = bT ∧ Val C cD ch L := by
  intro eps C cD ch h0 h1 hC hcD hch
  obtain ⟨hfix, hCc, -, -, -, -, -, -, -, -, -, -, -, -, hmid, -⟩ := hC
  have hLa : 1 ≤ C.GK.La := hmid _ (by simp [FC.cMid])
  have hGam : 1 ≤ C.CGam := hmid _ (by simp [FC.cMid])
  have hCt : C.Ct = 401 := hfix.2.2.2.2.2.2.2.2.2
  obtain ⟨x1, hx1⟩ := bottom_window_le eps C.GK h0 h1 hLa
  obtain ⟨x2, hx2⟩ := GlobalTheory.T.windows_of_explicitParameters eps cD ch C.P.Cpde h0 h1 hcD hch
  refine ⟨max (max x1 x2) ((max C.P.Cpde 1) ^ (100 / eps)), ?_⟩
  intro s D aT bT he hx0 hR hH hHC hdl hDel hCT2 hW heta hG hwin htop hA
  have hx : max x1 x2 ≤ s.x := le_trans (le_max_left _ _) hx0
  have hCo : C.P.Cpde ≤ s.x ^ (s.eps / 100) := by
    have hM : (0 : ℝ) ≤ max C.P.Cpde 1 := le_trans zero_le_one (le_max_right _ _)
    have h3 : (max C.P.Cpde 1) ^ (100 / eps) ≤ s.x := le_trans (le_max_right _ _) hx0
    have h4 := Real.rpow_le_rpow (Real.rpow_nonneg hM _) h3 (show 0 ≤ eps / 100 by positivity)
    rw [← Real.rpow_mul hM, show 100 / eps * (eps / 100) = 1 by field_simp, Real.rpow_one] at h4
    rw [he]
    exact (le_max_left _ _).trans h4
  have hb := hx1 s D.R he (le_trans (le_max_left _ _) hx) hR
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13⟩ :=
    hx2 s D bT he (le_trans (le_max_right _ _) hx) hR hH
      (fun t => ⟨(hwin t).2.1, by linarith [(hwin t).2.2]⟩) hHC
  have hDelR : ((D.s.Del : ℚ) : ℝ) = (Delv s cD : ℝ) := by rw [hDel]; norm_cast
  have hkp : (0 : ℝ) < D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : 0 < D.R.k)
  have hmp : (0 : ℝ) < D.R.m := by
    have := D.R.two_le_m
    exact_mod_cast (by omega : 0 < D.R.m)
  have hnp : (0 : ℝ) < D.R.n := by
    unfold Ranks.n
    positivity
  have hxp : 0 < s.x := lt_trans one_pos s.one_lt_alt
  have hh0 : (0 : ℝ) < (h0v s ch : ℝ) := by
    have : 0 < ⌈s.x ^ ch⌉₊ := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hxp _)
    unfold h0v
    exact_mod_cast (by omega : 0 < 2 * ⌈s.x ^ ch⌉₊)
  have hDp : (0 : ℝ) < (Delv s cD : ℝ) := by
    rw [← hDelR]; exact_mod_cast D.s.Del_pos
  let L : SizeData₂ D :=
    { sc := s
      aT := aT
      aT_win := fun t => (hwin t).1
      bT := bT
      bT_ge := fun t => (hwin t).2.1
      top_u := fun τ t h hτ => by
        obtain ⟨e1, e2⟩ := htop τ t h hτ
        rw [e1, e2]
        push_cast
        exact ⟨rfl, rfl⟩
      top_b := w1
      supp := ∅
      gain := fun _ _ => 0
      F := fun _ _ => 0
      E := fun _ _ _ => 0
      tau := fun _ => 0
      io := fun _ => 0
      gain_supp := fun _ _ _ => rfl
      F_supp := fun _ _ _ => rfl
      E_supp := fun _ _ _ _ => rfl
      tau_supp := fun _ _ => rfl
      io_supp := fun _ _ => rfl
      gain_g := fun _ _ _ => rfl
      b_le := w2
      untwisted := fun w h j j1 j2 => ⟨hA w h j j1 j2, rfl⟩
      not_inert := fun _ _ _ => ⟨fun _ => rfl, rfl, rfl⟩
      drop := ∅
      drop_alt := fun _ => Set.notMem_empty _
      F_conj := fun _ _ => rfl
      F_above := fun _ _ _ _ _ => rfl
      j0 := ⌈Real.logb 5 ((D.R.n : ℝ) * D.R.N D.R.m / D.R.m)⌉₊
      logFiveDepth_le := Nat.le_ceil _
      weightLength_ge_depth := w11
      logDerivativeAtOne := dlogL D 1
      logDerivative_at_one_eq := rfl
      split_tie := hH.split_tie
      o_tie := hH.o_le.trans hCo
      QS_tie := by
        have h3 := hH.QS_le
        have h4 := mul_le_mul_of_nonneg_right hCo hnp.le
        have h5 : 0 ≤ s.x ^ (s.eps / 100) * D.R.n := by positivity
        show (D.host.QS : ℝ) ≤ 4 * D.R.n * s.x ^ (s.eps / 100)
        nlinarith
      NuLat := fun _ => ⊥
      de2 := (D.host.T2.card : ℝ) / D.R.n
      thickDensity_pos := div_pos (by exact_mod_cast w12) hnp
      thickDensity_le_one := (div_le_one hnp).mpr (by exact_mod_cast w13)
      typeDensity_eq_card_div := rfl
      LaG := G.La C.GK s
      Sc := (D.R.k : ℝ) * (4 * (Delv s cD : ℝ))
      etaSz := (D.R.m : ℝ) * (h0v s ch : ℝ)
      Sc_pos := by positivity
      Sc_eq := by rw [hDelR]
      Cc := C.Cc
      win_thick := w3
      win_top := w4
      win_thin := w5
      cloud_gap := by rw [hCc]; exact w6
      cloud_v := w7
      cloud_u := fun u τ i i1 i2 =>
        middle_between (D.hcW u τ) (by rw [D.hcW_v]; exact w7 τ) i i1 i2
      be_close := w8
      etaSz_pos := by positivity
      TTw := fun _ => Finset.univ
      TTw_full := fun _ _ => rfl
      Ct := C.Ct
      t_win := ⟨w9, by rw [hCt]; exact w10⟩
      CGam := C.CGam
      CGam_pos := by linarith
      Gam_eq := hG
      wPart := fun _ _ _ _ => 1
      wPart_ge := fun _ _ _ _ => le_rfl
      lenMN := fun _ _ => 0 }
  exact ⟨L, rfl, rfl, rfl,
    { ranks := hR
      host := hH
      hc := hHC
      dlog := hdl
      Del_eq := hDel
      eta_eq := rfl
      La_eq := rfl
      bT_le := fun t => (hwin t).2.2
      logFiveDepth_eq := rfl
      Ct_eq := rfl
      Cc_eq := rfl
      CGam_eq := rfl
      secondConstant_eq := hCT2
      words := hW
      etaF_eq := heta }⟩

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsHermitianFormDescentCoefficientFieldStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hermitianForm_descent_coefficientField : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] (emb : ι → E →+* K) (σ : K →+* ℂ) {n : ℕ} (S : GStep E K n) (lam : ι → DomWeight n) (h : (S.fam emb lam).Ok) (z : S.Cl → GlobalTheory.Mem.Col2.Fr emb σ n → ℂ), z ∈ S.Fi emb σ lam → ∀ v : S.Cl → Formalism.L2.DIV.VV K lam, (∀ c, z c = evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ (v c)) → ∃ y : S.FormsK emb lam h, (∀ c, y.1 c = v c) ∧ S.embF emb σ lam h y = z := by
  first | exact @GlobalTheory.Glob.FormDescent.desc | exact GlobalTheory.Glob.FormDescent.desc | (intros; apply GlobalTheory.Glob.FormDescent.desc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsNatMulIntegral
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

namespace GlobalTheory.ThetaMove.CommonRef

section

variable {E : Type} [Field E] [NumberField E] {W : Type} [AddCommGroup W] [Module (𝓞 E) W] [Module E W] [IsScalarTower (𝓞 E) E W]

theorem exists_nat_mul_integral (a : E) : ∃ n : ℕ, 0 < n ∧ ∃ r : 𝓞 E, (n : E) * a = algebraMap (𝓞 E) E r := by
  have ha : IsAlgebraic ℤ a := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic a)
  obtain ⟨y, hy, hint⟩ := ha.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩
  have h2 : IsIntegral ℤ ((y.natAbs : E) * a) := by
    rw [zsmul_eq_mul] at hint
    rcases Int.natAbs_eq y with h | h
    · have := congrArg (Int.cast : ℤ → E) h
      rw [Int.cast_natCast] at this
      rwa [this] at hint
    · have := congrArg (Int.cast : ℤ → E) h
      rw [Int.cast_neg, Int.cast_natCast] at this
      rw [this, neg_mul] at hint
      simpa using hint.neg
  exact ⟨⟨_, h2⟩, rfl⟩

theorem full_of_span {M : Submodule (𝓞 E) W} (hM : Submodule.span E (M : Set W) = ⊤) : Full M := by
  intro x
  have hx : x ∈ Submodule.span E (M : Set W) := hM ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx => exact ⟨1, Nat.one_pos, by simpa using hx⟩
  | zero => exact ⟨1, Nat.one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn, hx⟩ := hx
    obtain ⟨m, hm, hy⟩ := hy
    refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [Nat.cast_mul, mul_comm, mul_smul]; exact M.smul_mem _ hx
    · rw [Nat.cast_mul, mul_smul]; exact M.smul_mem _ hy
  | smul a x _ hx =>
    obtain ⟨n, hn, hx⟩ := hx
    obtain ⟨m, hm, r, hr⟩ := exists_nat_mul_integral a
    refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
    have : ((n * m : ℕ) : 𝓞 E) • a • x = r • (n : 𝓞 E) • x := by
      simp only [← algebraMap_smul E (_ : 𝓞 E), smul_smul, map_natCast, ← hr]
      congr 1
      push_cast
      ring
    rw [this]
    exact M.smul_mem _ hx

omit [Module E W] [IsScalarTower (𝓞 E) E W] in
theorem exists_nat_smul_le {M N : Submodule (𝓞 E) W} (hM : Full M) (hN : N.FG) :
    ∃ m : ℕ, 0 < m ∧ ∀ x ∈ N, (m : 𝓞 E) • x ∈ M := by
  first
  | exact @_root_.GlobalTheory.FinitelyGeneratedNatMultiple.exists_nat_smul_mem_of_fg
  | exact _root_.GlobalTheory.FinitelyGeneratedNatMultiple.exists_nat_smul_mem_of_fg
  | (apply _root_.GlobalTheory.FinitelyGeneratedNatMultiple.exists_nat_smul_mem_of_fg <;> assumption)
  | (intros; apply _root_.GlobalTheory.FinitelyGeneratedNatMultiple.exists_nat_smul_mem_of_fg <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FinitelyGeneratedNatMultiple.exists_nat_smul_mem_of_fg <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FinitelyGeneratedNatMultiple.exists_nat_smul_mem_of_fg ..)

theorem smul_mem_locP {M N : Submodule (𝓞 E) W} {m : ℕ} (h : ∀ x ∈ N, (m : 𝓞 E) • x ∈ M) (Q : HeightOneSpectrum (𝓞 E))
    {x : W} (hx : x ∈ localization₂ Q.asIdeal N) : (m : E) • x ∈ localization₂ Q.asIdeal M := by
  obtain ⟨s, hs, hx⟩ := hx
  refine ⟨s, hs, ?_⟩
  have := h _ hx
  rwa [smul_comm, Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul E] at this

theorem mem_localization_of_inv_smul_mem {M N : Submodule (𝓞 E) W} {m : ℕ} (hm : 0 < m) (h : ∀ x ∈ N, (m : 𝓞 E) • x ∈ M)
    (Q : HeightOneSpectrum (𝓞 E)) {x : W} (hx : (m : E)⁻¹ • x ∈ localization₂ Q.asIdeal N) : x ∈ localization₂ Q.asIdeal M := by
  have hmE : (m : E) ≠ 0 := by exact_mod_cast hm.ne'
  have := smul_mem_locP h Q hx
  rwa [smul_smul, mul_inv_cancel₀ hmE, one_smul] at this

theorem dom_twO [StarRing E] (S : Finset (HeightOneSpectrum (𝓞 E))) {M N : Submodule (𝓞 E) W} {m : ℕ} (hm : 0 < m)
    (h₁ : ∀ x ∈ N, (m : 𝓞 E) • x ∈ M) (h₂ : ∀ x ∈ M, (m : 𝓞 E) • x ∈ N)
    (hQ : ∀ Q : HeightOneSpectrum (𝓞 E), Q ∉ S → conjPrime₂ Q ∉ S → localization₂ Q.asIdeal M = localization₂ Q.asIdeal N) :
    Dom S M (twist₂ N m (expS S)) ∧ Dom S (twist₂ N m fun Q => -expS S Q) M := by
  have hb := expS_bound S
  have hb' : ∀ Q, -1 ≤ -expS S Q ∧ -expS S Q ≤ 1 := fun Q => by have := hb Q; omega
  refine ⟨⟨fun P hP x hx => ?_, fun Q hS x hx => ?_⟩, fun P hP x hx => ?_, fun Q hS x hx => ?_⟩
  · rw [mem_localization_twist N hm hb] at hx
    have e : expS S P = 1 := by simp [expS, hP]
    rw [e, zpow_one] at hx
    exact mem_localization_of_inv_smul_mem hm h₁ P hx
  · rw [mem_localization_twist N hm hb]
    by_cases hc : conjPrime₂ Q ∈ S
    · have e : expS S Q = -1 := by simp [expS, hS, hc]
      rw [e, zpow_neg_one, inv_inv]
      exact smul_mem_locP h₂ Q hx
    · have e : expS S Q = 0 := by simp [expS, hS, hc]
      rw [e, zpow_zero, inv_one, one_smul, ← hQ Q hS hc]
      exact hx
  · rw [mem_localization_twist N hm hb']
    have e : expS S P = 1 := by simp [expS, hP]
    rw [e, zpow_neg_one, inv_inv]
    exact smul_mem_locP h₂ P hx
  · rw [mem_localization_twist N hm hb'] at hx
    by_cases hc : conjPrime₂ Q ∈ S
    · have e : expS S Q = -1 := by simp [expS, hS, hc]
      rw [e, neg_neg, zpow_one] at hx
      exact mem_localization_of_inv_smul_mem hm h₁ Q hx
    · have e : expS S Q = 0 := by simp [expS, hS, hc]
      rw [e, neg_zero, zpow_zero, inv_one, one_smul, ← hQ Q hS hc] at hx
      exact hx

end

theorem common_refinement : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) (M₁ M₂ : Submodule (𝓞 E) (Sp E n)) (S : Finset (HeightOneSpectrum (𝓞 E))), (∀ P ∈ S, conjPrime₂ P ∉ S) → IsSdLat M₁ → IsSdLat M₂ → (∀ Q : HeightOneSpectrum (𝓞 E), Q ∉ S → conjPrime₂ Q ∉ S → localization₂ Q.asIdeal M₁ = localization₂ Q.asIdeal M₂) → ∃ F G : Submodule (𝓞 E) (Sp E n), IsSdLat F ∧ IsSdLat G ∧ Dom S M₁ F ∧ Dom S M₂ F ∧ Dom S G M₁ ∧ Dom S G M₂ := by
  intro E _ _ _ n M₁ M₂ S hS h₁ h₂ hQ
  obtain ⟨a, ha, hA⟩ := exists_nat_smul_le (full_of_span h₁.1.span_eq_top) h₂.1.fg
  obtain ⟨b, hb, hB⟩ := exists_nat_smul_le (full_of_span h₂.1.span_eq_top) h₁.1.fg
  have hm : 0 < a * b := Nat.mul_pos ha hb
  have hA' : ∀ x ∈ M₂, ((a * b : ℕ) : 𝓞 E) • x ∈ M₁ := fun x hx => by
    rw [Nat.cast_mul, mul_comm, mul_smul]; exact M₁.smul_mem _ (hA x hx)
  have hB' : ∀ x ∈ M₁, ((a * b : ℕ) : 𝓞 E) • x ∈ M₂ := fun x hx => by
    rw [Nat.cast_mul, mul_smul]; exact M₂.smul_mem _ (hB x hx)
  have hC : ∀ x ∈ M₂, ((a * b : ℕ) : 𝓞 E) • x ∈ M₂ := fun x hx => M₂.smul_mem _ hx
  obtain ⟨hF, hG⟩ := GlobalTheory.ThetaMove.TwistSd.isSdLat_twO_expS E n M₂ (a * b) S hS h₂ hm
  obtain ⟨d₁, d₂⟩ := dom_twO S hm hA' hB' hQ
  obtain ⟨d₃, d₄⟩ := dom_twO S hm hC hC fun _ _ _ => rfl
  exact ⟨_, _, hF, hG, d₁, d₃, d₂, d₄⟩

end GlobalTheory.ThetaMove.CommonRef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsPrimesInProgressionBoundedStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_primes_in_progression_bounded : SmallPrimeOne → ∃ C8 : ℝ, 1 ≤ C8 ∧ ∀ N : ℕ, 30 ≤ N → ∃ p p' q0 : ℕ, p.Prime ∧ p'.Prime ∧ q0.Prime ∧ p ≠ p' ∧ q0 ≠ p ∧ q0 ≠ p' ∧ p % (15 * N) = 1 ∧ p' % (15 * N) = 1 ∧ q0 % N = 1 ∧ (p : ℝ) ≤ (N : ℝ) ^ C8 ∧ (p' : ℝ) ≤ (N : ℝ) ^ C8 ∧ (q0 : ℝ) ≤ (N : ℝ) ^ C8 := by
  first | exact @GlobalTheory.EX.auxiliary_primes | exact GlobalTheory.EX.auxiliary_primes | (intros; apply GlobalTheory.EX.auxiliary_primes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsThinPrimeSetStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_noRel_finset_card_ge : ∃ CT2 : ℝ, ∀ eps Co : ℝ, 0 < eps → eps < 1 / 52 → ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks), s.eps = eps → x0 ≤ s.x → RankVal s R → (R.o : ℝ) ≤ Co → ∃ T : Finset ℕ, (∀ a ∈ T, 4 * Lwv s * a < R.n0) ∧ Formalism.FrobeniusOrbits.NoRel T (Lwv s) ∧ (R.n0 : ℝ) * Real.exp (-(CT2 * Real.sqrt (Real.log (R.n0 : ℝ) * Real.log (Lwv s)))) / (Lwv s) ≤ T.card ∧ s.x ^ (-s.eps) * R.n ≤ (T.card : ℝ) ∧ 4 * Lwv s * T.card ≤ R.n0 ∧ 2 ≤ Lwv s := by
  first | exact @GlobalTheory.EX.exists_thick_set_sizes | exact GlobalTheory.EX.exists_thick_set_sizes | (intros; apply GlobalTheory.EX.exists_thick_set_sizes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsTwoLargeNormOnePrimesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_two_large_norm_one_primes : NormPrimes → ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks) (N d : ℕ), s.eps = eps → x0 ≤ s.x → RankVal s R → ModRow s N d → ∃ g : Fin 2 → ℕ, (∀ i, (g i).Prime ∧ ((R.k : ℝ) * s.b) ^ 8 ≤ (g i : ℝ) ∧ (g i : ℝ) ≤ 2 * ((R.k : ℝ) * s.b) ^ 8 ∧ NormOne d N (g i)) ∧ g 0 ≠ g 1 ∧ Disjoint (Formalism.CyclotomicNorms.BB R.r (g 0)) (Formalism.CyclotomicNorms.BB R.r (g 1)) := by
  first | exact @GlobalTheory.EX.two_type_primes | exact GlobalTheory.EX.two_type_primes | (intros; apply GlobalTheory.EX.two_type_primes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitChoiceSizeEtaStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.explicitChoice_sizeEta : SzRow (fun _ _ L => SizeEta L) := by
  first | exact @GlobalTheory.EX.szRow_sizeEta | exact GlobalTheory.EX.szRow_sizeEta | (intros; apply GlobalTheory.EX.szRow_sizeEta <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitChoiceSizeLstarStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.explicitChoice_sizeLstar : SzRow (fun _ _ L => SizeLstar L) := by
  first | exact @GlobalTheory.EX.szRow_sizeLstar | exact GlobalTheory.EX.szRow_sizeLstar | (intros; apply GlobalTheory.EX.szRow_sizeLstar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitChoiceSizeNodesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.explicitChoice_sizeNodes : SzRow (fun _ _ L => SizeNodes L) := by
  first | exact @GlobalTheory.EX.szRow_sizeNodes | exact GlobalTheory.EX.szRow_sizeNodes | (intros; apply GlobalTheory.EX.szRow_sizeNodes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FieldIsoLatticesFormTaylorCorrespondStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fieldIso_lattices_form_taylor_correspond : ∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (a b : ℕ), s.Ok → (∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (z : TaylorLogMetric.VC D a b), z ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (s.lat N) (s.lat N') ↔ (fun τ => z (s.iT τ)) ∈ LamC (X.embC s.σ₀) δ (ambOf s B χ cD).AA N N') ∧ (∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), Even a → Even b → IsSdLat N → IsSdLat N' → TaylorLogMetric.admitted D a b (s.lat N) (s.lat N')) ∧ (∀ z w : TaylorLogMetric.VC D a b, TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) z w = HV (ambOf s B χ cD).sc (fun τ => z (s.iT τ)) (fun τ => w (s.iT τ))) ∧ ∀ G : TaylorLogMetric.VC D a b → ℂ, (∀ k : ℕ, ContDiff ℂ k G) → ∀ m : DVar X.Tau a b →₀ ℕ, derivAt0 (fun z : VCx X.Tau a b => G fun τ => z (s.iT.symm τ)) m = (m.prod fun _ n => (n.factorial : ℂ)) * TaylorLogMetric.taylor D G (m.mapDomain fun v => (s.iT v.1, v.2)) := by
  first | exact @GlobalTheory.SeamTransport.transport | exact GlobalTheory.SeamTransport.transport | (intros; apply GlobalTheory.SeamTransport.transport <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FieldIsoSelfDualAndPeriodLatticesAgreeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fieldIso_selfDual_and_periodLattices_agree : ∀ (X : Fields) (D : D7) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ), s.Ok → (∀ (n : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E n)), IsSdLat N → StandardLatticesGL3.SD D (s.lat N)) ∧ ∀ (a b : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (z : VCx X.Tau a b), z ∈ lam (ambOf s B χ cD) N N' ↔ (fun τ => z (s.iT.symm τ)) ∈ TaylorLogMetric.La D B.tor (s.lat N) (s.lat N') := by
  first | exact @GlobalTheory.PeriodTransport.seam_lattices | exact GlobalTheory.PeriodTransport.seam_lattices | (intros; apply GlobalTheory.PeriodTransport.seam_lattices <;> assumption)
end

