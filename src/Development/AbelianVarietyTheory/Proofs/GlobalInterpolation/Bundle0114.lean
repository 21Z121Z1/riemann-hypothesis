import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.Bundle0007
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0074
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0080
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0108
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0079
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0093
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0082
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0107
import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0003
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeMemAvoidedPrimes
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0101

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowNodeGapBlockLength
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem nodeGap_blockLength_poly (x T t P Dy f m N k c h : ℝ) (hx : 6 ≤ x)
    (hT0 : 0 ≤ T) (hT : T ≤ x ^ 378) (ht : t ≤ x ^ 401) (hP0 : 0 ≤ P) (hP : P ≤ x ^ 85)
    (hD0 : 0 ≤ Dy) (hD : Dy ≤ x ^ 12) (hf0 : 0 ≤ f) (hf : f ≤ x ^ 3) (hm1 : 1 ≤ m) (hm : m ≤ x)
    (hN0 : 0 ≤ N) (hN : N ≤ x ^ 402) (hk0 : 0 ≤ k) (hk : k ≤ x ^ 5) (hc : c ≤ x)
    (hh : x ^ 1000 ≤ h) :
    (4 * T ^ 2 + 2 * t ≤ h) ∧ (P * Dy * f * m ^ 2 * N * T ≤ h) ∧ (P * (f * m * k) ^ 3 * k / m ≤ h) ∧
      (c * T * N * f ^ 2 * m ^ 2 * k * Dy * P ≤ h) := by
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 ≤ x := by linarith
  have hm0 : 0 ≤ m := by linarith
  have hp : ∀ n : ℕ, n ≤ 1000 → x ^ n ≤ h := fun n hn => (pow_le_pow_right₀ hx1 hn).trans hh
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h1 : T ^ 2 ≤ x ^ 756 := by
      calc T ^ 2 ≤ (x ^ 378) ^ 2 := by gcongr
        _ = x ^ 756 := by ring
    have h2 : t ≤ x ^ 756 := ht.trans (pow_le_pow_right₀ hx1 (by norm_num))
    have h3 : 6 * x ^ 756 ≤ x ^ 757 := by
      calc 6 * x ^ 756 ≤ x * x ^ 756 := by gcongr
        _ = x ^ 757 := by ring
    have h4 := hp 757 (by norm_num)
    linarith
  · calc P * Dy * f * m ^ 2 * N * T ≤ x ^ 85 * x ^ 12 * x ^ 3 * x ^ 2 * x ^ 402 * x ^ 378 := by gcongr
      _ = x ^ 882 := by ring
      _ ≤ h := hp _ (by norm_num)
  · calc P * (f * m * k) ^ 3 * k / m ≤ P * (f * m * k) ^ 3 * k := div_le_self (by positivity) hm1
      _ ≤ x ^ 85 * (x ^ 3 * x * x ^ 5) ^ 3 * x ^ 5 := by gcongr
      _ = x ^ 117 := by ring
      _ ≤ h := hp _ (by norm_num)
  · calc c * T * N * f ^ 2 * m ^ 2 * k * Dy * P
        ≤ x * x ^ 378 * x ^ 402 * (x ^ 3) ^ 2 * x ^ 2 * x ^ 5 * x ^ 12 * x ^ 85 := by
          calc c * T * N * f ^ 2 * m ^ 2 * k * Dy * P = c * (T * N * f ^ 2 * m ^ 2 * k * Dy * P) := by ring
            _ ≤ x * (T * N * f ^ 2 * m ^ 2 * k * Dy * P) := by gcongr
            _ = x * T * N * f ^ 2 * m ^ 2 * k * Dy * P := by ring
            _ ≤ _ := by gcongr
      _ = x ^ 891 := by ring
      _ ≤ h := hp _ (by norm_num)

theorem szRow_nodeGap_blockLength : SzRow (fun C D L => (4 * ((TOv L.sc : ℕ) : ℝ) ^ 2 + 2 * D.R.t ≤ h0 L) ∧ ((C.T.CP * zBase L ^ C.T.eP) * (D.R.f * D.R.r.choose 2 : ℕ) * D.R.f * (D.R.m : ℝ) ^ 2 * (D.R.N D.R.m : ℝ) * (TOv L.sc : ℕ) ≤ h0 L) ∧ ((C.T.CP * zBase L ^ C.T.eP) * ((D.R.f : ℝ) * D.R.m * D.R.k) ^ 3 * D.R.k / D.R.m ≤ h0 L) ∧ (C.T.ChT * (TOv L.sc : ℕ) * (D.R.N D.R.m : ℝ) * (D.R.f : ℝ) ^ 2 * (D.R.m : ℝ) ^ 2 * D.R.k * (D.R.f * D.R.r.choose 2 : ℕ) * (C.T.CP * zBase L ^ C.T.eP) ≤ h0 L)) := by
  intro eps he he' C hC
  obtain ⟨x1, hx1⟩ := GlobalTheory.T.explicitRanks_basic_bounds_large_scale eps he he'
  have heP : C.T.eP = 12 := hC.2.2.2.2.2.2.2.2.1
  have hCP : 1000 ≤ C.T.CP := hC.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨0, fun cD _ => ⟨1000, fun ch hch => ⟨max (max x1 6) (max C.T.CP C.T.ChT), ?_⟩⟩⟩
  intro D L hLe hx V
  simp only [max_le_iff] at hx
  obtain ⟨⟨hxa, hx6⟩, hxP, hxC⟩ := hx
  obtain ⟨hf, hm, hr, hkr, -, -, hL1, -, hZ, hD, -, -, -, ht, hN, hm1, -⟩ := hx1 L.sc D.R hLe hxa V.ranks
  set x := L.sc.x with hxdef
  have hx1' : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hm1' : (1 : ℝ) ≤ D.R.m :=
    (Real.one_le_rpow hx1' (by rw [hLe]; linarith)).trans hm1
  have cast : ∀ n : ℕ, x ^ ((n : ℕ) : ℝ) = x ^ n := fun n => Real.rpow_natCast x n
  have hZ0 : 0 ≤ zBase L := by unfold zBase; have : (0:ℝ) ≤ L.sc.L := by linarith
                               positivity
  have hZ7 : zBase L ≤ x ^ 7 := by
    rw [← cast]
    exact hZ.trans (Real.rpow_le_rpow_of_exponent_le hx1' (by norm_num))
  have hPe : zBase L ^ C.T.eP = zBase L ^ (12 : ℕ) := by
    rw [heP]; first | rfl | exact_mod_cast Real.rpow_natCast _ 12
  refine nodeGap_blockLength_poly x _ _ _ _ _ _ _ _ _ _ hx6 (Nat.cast_nonneg _) ?_ ?_ ?_ ?_ (Nat.cast_nonneg _) ?_
    (Nat.cast_nonneg _) ?_ hm1' hm (Nat.cast_nonneg _) ?_ (Nat.cast_nonneg _) ?_ hxC ?_
  · have h1 : x ^ (377 : ℝ) = x ^ 377 := by exact_mod_cast cast 377
    have h2 : ((TOv L.sc : ℕ) : ℝ) ≤ x ^ 377 + 1 := by
      unfold TOv
      rw [← hxdef, h1]
      exact (Nat.ceil_lt_add_one (by positivity)).le
    have h3 : (1 : ℝ) ≤ x ^ 377 := one_le_pow₀ hx1'
    have h4 : 2 * x ^ 377 ≤ x ^ 378 := by
      calc 2 * x ^ 377 ≤ x * x ^ 377 := by gcongr; linarith
        _ = x ^ 378 := by ring
    linarith
  · exact_mod_cast ht
  · rw [hPe]; have : 0 ≤ C.T.CP := by linarith
    positivity
  · rw [hPe]
    calc C.T.CP * zBase L ^ 12 ≤ x * (x ^ 7) ^ 12 := by gcongr
      _ = x ^ 85 := by ring
  · exact_mod_cast hD
  · exact_mod_cast hf
  · exact_mod_cast hN
  · have : (D.R.k : ℝ) ≤ D.R.r := by exact_mod_cast hkr
    exact this.trans (by exact_mod_cast hr)
  · have h1 : h0 L = (h0v L.sc ch : ℝ) := by
      unfold h0
      rw [V.eta_eq]
      field_simp
    rw [h1, ← cast]
    unfold h0v
    rw [← hxdef]
    have h2 : x ^ ((1000 : ℕ) : ℝ) ≤ x ^ ch := Real.rpow_le_rpow_of_exponent_le hx1' (by exact_mod_cast hch)
    have h3 := Nat.le_ceil (x ^ ch)
    have h4 : (0 : ℝ) ≤ (⌈x ^ ch⌉₊ : ℝ) := Nat.cast_nonneg _
    push_cast at *
    linarith

theorem szRow_blockLengthParams : SzRow (fun C D L => ∀ P : ParameterChoice' D L, P.CnW = C.P.CnW → ∃ T : ParamsT D L P,
    [T.CP, T.eP, T.Cp, T.Cb, T.cTO, T.ChT, T.CbN] = C.PT ∧ T.eP = C.T.eP) := by
  have hand := szRow_and_imp.1
  have hall := hand _ _ GlobalTheory.T.sizes_PP_and_dim_and_TOv_le_x_rpow_Ct <| hand _ _ GlobalTheory.T.explicitChoice_windowRank_conditions <| hand _ _ GlobalTheory.T.explicitChoice_windowRank_le_polyBound <|
    hand _ _ GlobalTheory.T.sizes_PP_pow_mul_dim_pow_div_le_TOv <| hand _ _ GlobalTheory.T.sizes_rank_and_poly_counts_le_TOv <| hand _ _ GlobalTheory.T.sizes_TOv_mul_PP_le_b_and_sqrt_b <|
    hand _ _ GlobalTheory.T.sizes_TOv_sq_le_del_and_gap_mul_le_del <| hand _ _ szRow_nodeGap_blockLength GlobalTheory.T.explicitChoice_polynomial_le_baseSize
  refine szRow_and_imp.2 _ _ hall ?_
  rintro C cD ch D L hS - ⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩, ⟨c1, c2⟩, ⟨d1, d2⟩,
    ⟨e1, e2, e3, e4⟩, ⟨f1, f2, f3, f4⟩, ⟨g1, g2⟩, ⟨h1, h2, h3, h4⟩, ⟨i1, i2, i3⟩⟩ P hP
  obtain ⟨-, -, -, -, -, -, -, hCp, heP, -, -, -, -, hCP, -, hlast⟩ := hS
  have hCb : 1 ≤ C.T.Cb := hlast _ (by simp [FC.cLast])
  have hChT : 1 ≤ C.T.ChT := hlast _ (by simp [FC.cLast])
  have hCbN : 1 ≤ C.T.CbN := hlast _ (by simp [FC.cLast])
  refine ⟨{
    TO := TOv L.sc
    nWn := nWv D.R L.sc
    nP := 8 * D.R.f * D.R.r + 4
    PP := C.T.CP * zBase L ^ C.T.eP
    Dp := D.R.f * D.R.r.choose 2
    s := D.R.r + 6
    CP := C.T.CP
    one_le_CP := by linarith
    eP := C.T.eP
    eP_ge := heP.ge
    Cp := C.T.Cp
    Cp_ge := hCp.ge
    Cb := C.T.Cb
    Cb_nonneg := by linarith
    cTO := C.T.cTO
    ChT := C.T.ChT
    ChT_ge := hChT
    CbN := C.T.CbN
    CbN_ge := hCbN
    PP_eq := rfl
    Dp_eq := rfl
    PP_poly := a1
    Dp_poly := a2
    TO_poly := a3
    nW_win := hP ▸ b1
    nW_dvd := b2
    PP_nW := c1
    nW_le := c2
    nW_lo := b8
    split := b3
    nP_eq := rfl
    TO_eq := b4
    TO_ge := d1
    TO_PP := f1
    TO_nW := e1
    TO_40 := e2
    TO_11D2 := e3
    order_ge_rank_bound := e4
    TO_PP' := f2
    precision_cube_order_sq_le := f3
    precision_cube_order_sq_le_sqrt := f4
    TO_Dk := d2
    Del_TO := g1
    Del_gap := g2
    heightBound_ge_order_sq := h1
    heightBound_ge_precision_degree := h2
    heightBound_ge_precision_cubic := h3
    heightBound_ge_order_product := h4
    log_bound_le_sqrt := i1
    TD2' := i2
    b_ge := i3
    s_odd := b5
    s_lo := b6
    s_hi := b7 }, rfl, rfl⟩

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeightWindowRequirementHostOfPoint
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

noncomputable section

namespace GlobalTheory.EX

theorem weightWindowRequirement_host_of_point : ∀ (C : FC) (cD ch : ℝ) (p : Pt C) (R : Ranks) (H : Host R) (a b : R.A → ℤ) (M : ℕ) (c : Fin M → Fin (R.k - 2) → Bool) (u0 : ℕ), Std C → Val C cD ch p.L → p.From H a b c u0 → CanonInst p.ta.Gx → Formalism.MainNotions.AuxBlock8.WeightVectorExists p.D p.L p.ta.Gx C.GK → ∃ a' b' : R.A → ℤ, (∀ t, t ∉ H.TT → a' t = 0 ∧ b' t = 0) ∧ WinOK p.L.sc C.GK H a' b' ∧ WOK p.L.sc cD ch C.GK H a' b' := by
  intro C cD ch p R H a b M c u0 _ hV hF hC hW
  have hcl : p.D.host.cls = H.cls := hF.cls_eq
  obtain ⟨hR, hTT, -, hq, hd, -, -, -, -, -, hh, -, -⟩ := hF
  subst hR
  have hTT' : p.D.host.TT = H.TT :=
    Finset.image_injective (Formalism.HC.Frame.A.val_injective _) hTT
  have hh' : ∀ l, G.hP p.D l = hPH H l := fun l => Formalism.HC.Frame.A.val_injective _ (hh l)
  obtain ⟨a', ha, b', hb, hW⟩ := hW
  have ha' := Fintype.mem_piFinset.1 ha
  have hb' := Fintype.mem_piFinset.1 hb
  have hS : p.L.Sc = (p.D.R.k : ℝ) * (4 * (Delv p.L.sc cD : ℝ)) := by
    rw [p.L.Sc_eq, hV.Del_eq]; push_cast; rfl
  refine ⟨a', b', fun t ht => ?_, fun t ht => ?_, ?_⟩
  · rw [← hTT'] at ht
    have h1 := ha' t
    have h2 := hb' t
    simp only [ht, if_false, Finset.mem_singleton] at h1 h2
    exact ⟨h1, h2⟩
  · rw [← hTT'] at ht
    have h1 := ha' t
    have h2 := hb' t
    simp only [ht, if_true, G.winA, G.winB, Finset.mem_Icc, Int.ceil_le, Int.le_floor, G.Nstar] at h1 h2
    exact ⟨h1, h2⟩
  · have key : ∀ (q d : ℕ) (cl : ℕ → PrimeClass) (TT : Finset (p.D.R.A)) (Sc eta : ℝ) (hf : ℕ → p.D.R.A),
        p.D.host.q = q → p.D.host.d = d → p.D.host.cls = cl → p.D.host.TT = TT → p.L.Sc = Sc → p.L.etaSz = eta → (∀ l, G.hP p.D l = hf l) →
        (let B : Arith.Base := { R := p.D.R, sc := p.L.sc, q := q, d := d, cls := cl, TT := TT, Sc := Sc, eta := eta }
         open Classical in
         ∑ l ∈ (Finset.range ⌈p.L.sc.X'⌉₊).filter (fun l => Arith.Loc.Cand B C.GK (hf l) l), Real.log l / l *
          (2 * (if p.L.sc.x ^ (-p.L.sc.eps) < Arith.Loc.Sig B (Arith.ins B C.GK 1) C.GK a' b' (hf l) l then (1 : ℝ) else 0) +
            4 * Arith.Loc.Sig B (Arith.ins B C.GK 1) C.GK a' b' (hf l) l) ≤ p.L.sc.x ^ (-9 : ℝ)) := by
      intro q d cl TT Sc eta hf e1 e2 e0 e3 e4 e5 e6
      obtain rfl : G.hP p.D = hf := funext e6
      subst e1 e2 e0 e3 e4 e5
      unfold Formalism.MainNotions.AuxBlock8.WReq Formalism.MainNotions.AuxBlock8.cands at hW
      simp only [sig_eq_loc p.ta.Gx C.GK p.xa.ex.kapI_def hC.1] at hW
      exact hW
    exact key _ _ _ _ _ _ _ hq hd hcl hTT' hS hV.eta_eq hh'

end GlobalTheory.EX

end
end

