import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3479
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2404
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SizeBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0844
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3485
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3448
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3238
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3472
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3486
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3452
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3473
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3381
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3439
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0226
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3487
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2559
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2502

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortOfInputs
section
set_option synthInstance.maxHeartbeats 400000

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt

namespace GlobalTheory.CovHt.ShortPf

theorem budget_arith {f r l b PP T d ρ s : ℝ} (hf : 1 ≤ f) (hr : 1 ≤ r) (hl : 1 ≤ l) (hP : (f * r * l) ^ 12 ≤ PP)
    (hd : 1 ≤ d) (hT : d ^ 2 * PP ≤ T) (hTb : T ≤ b) (hρ : 0 ≤ ρ) (hρ1 : d * ρ * PP ≤ 6 * r ^ 2) (hs : 0 ≤ s)
    (hs1 : T * s ≤ 8 * f * r * b) :
    ((f * r * l) ^ 3 * s + (f * r * l) ^ 5) * (6 * d + 10 + T * (7 * (d ^ 2 / T + d * ρ) + 2 * ρ)) ≤ 693 * (f * b) := by
  have hrZ : r ≤ f * r * l := by
    calc r = 1 * r * 1 := by ring
      _ ≤ _ := by gcongr
  generalize f * r * l = Z at *
  have hZ : 1 ≤ Z := hr.trans hrZ
  have h7 : Z ^ 7 ≤ PP := (pow_le_pow_right₀ hZ (by norm_num)).trans hP
  have hP0 : 0 < PP := lt_of_lt_of_le (by positivity) h7
  have hT0 : 0 < T := lt_of_lt_of_le (by positivity) hT
  have hb0 : 0 < b := hT0.trans_le hTb
  have hr2 : 1 ≤ r ^ 2 := one_le_pow₀ hr
  have e : T * (7 * (d ^ 2 / T + d * ρ) + 2 * ρ) = 7 * d ^ 2 + 7 * T * (d * ρ) + 2 * T * ρ := by field_simp
  have hF : (6 * d + 10 + T * (7 * (d ^ 2 / T + d * ρ) + 2 * ρ)) * PP ≤ 77 * (r ^ 2 * T) := by
    rw [e]
    have a1 : d ≤ d ^ 2 := le_self_pow₀ hd (by norm_num)
    have a2 : ρ ≤ d * ρ := le_mul_of_one_le_left hρ hd
    have a3 : 6 * d + 10 + (7 * d ^ 2 + 7 * T * (d * ρ) + 2 * T * ρ) ≤ 23 * d ^ 2 + 9 * T * (d * ρ) := by
      nlinarith [mul_le_mul_of_nonneg_left a2 hT0.le]
    have a4 := mul_le_mul_of_nonneg_right a3 hP0.le
    have a5 := mul_le_mul_of_nonneg_left hρ1 hT0.le
    have a6 : T ≤ r ^ 2 * T := le_mul_of_one_le_left hT0.le hr2
    nlinarith
  generalize 6 * d + 10 + T * (7 * (d ^ 2 / T + d * ρ) + 2 * ρ) = F at hF ⊢
  refine le_of_mul_le_mul_right ?_ hP0
  have b1 : (Z ^ 3 * s + Z ^ 5) * (F * PP) ≤ (Z ^ 3 * s + Z ^ 5) * (77 * (r ^ 2 * T)) :=
    mul_le_mul_of_nonneg_left hF (by positivity)
  have b2 : Z ^ 3 * r ^ 2 * (T * s) ≤ Z ^ 3 * r ^ 2 * (8 * f * r * b) := mul_le_mul_of_nonneg_left hs1 (by positivity)
  have b3 : Z ^ 3 * r ^ 3 ≤ PP := by
    calc Z ^ 3 * r ^ 3 ≤ Z ^ 3 * Z ^ 4 :=
          mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ (by linarith) hrZ 3).trans (pow_le_pow_right₀ hZ (by norm_num)))
            (by positivity)
      _ = Z ^ 7 := by ring
      _ ≤ _ := h7
  have b4 : Z ^ 5 * r ^ 2 ≤ PP := by
    calc Z ^ 5 * r ^ 2 ≤ Z ^ 5 * Z ^ 2 := by gcongr
      _ = Z ^ 7 := by ring
      _ ≤ _ := h7
  have b5 : Z ^ 3 * r ^ 3 * (f * b) ≤ PP * (f * b) := mul_le_mul_of_nonneg_right b3 (by positivity)
  have b6 : Z ^ 5 * r ^ 2 * T ≤ PP * (f * b) :=
    mul_le_mul b4 (hTb.trans (le_mul_of_one_le_left hb0.le hf)) hT0.le hP0.le
  nlinarith

theorem len_mul_l1_le {ι : Type} [Fintype ι] {N : ℕ} (W : GlobalTheory.MeanTop.Wts ι N) (hW : W.Hyp) (hD : W.IsDiv) :
    (W.T : ℝ) * GlobalTheory.MeanTop.l1 W.u1 ≤ Fintype.card ι * (N * (2 * W.b)) := by
  refine (GlobalTheory.MeanTop.divided_weight_size _ _ W hW hD).1.trans ?_
  have h : ∑ τ, ∑ k, (|(W.u τ k : ℝ)| + W.c0 + 4 * N) ≤ ∑ _τ : ι, ∑ _k : Fin N, 2 * W.b :=
    Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun k _ => hW.h5 τ k
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  unfold GlobalTheory.MeanTop.l1
  linarith

theorem fieldSz_host {D : D7} {L : SizeData₂ D} {PP A M : ℝ} (h : HostNum D L PP A M) : fieldSz D.host.E ≤ 3 * L.sc.L := by
  have hf : (8 : ℝ) ≤ D.R.f := by exact_mod_cast h.f8
  have hr : (2 : ℝ) ≤ D.R.r := by
    have h1 := D.R.two_le_m
    have h2 := D.R.m_add_three_le_k
    exact_mod_cast (by unfold Ranks.r; omega : 2 ≤ D.R.r)
  unfold fieldSz
  rw [h.deg]
  push_cast
  have a1 : Real.log (2 * (D.R.f : ℝ)) ≤ Real.log ((D.R.f : ℝ) * D.R.r) := Real.log_le_log (by linarith) (by nlinarith)
  have a2 : Real.log |(discr D.host.E : ℝ)| / (2 * (D.R.f : ℝ)) ≤ 2 * L.sc.L := by
    rw [div_le_iff₀ (by linarith)]
    linarith [h.disc]
  linarith [h.logfr.1]

theorem log_level {D : D7} {L : SizeData₂ D} {PP A M : ℝ} (h : HostNum D L PP A M) :
    Real.log ((D.host.g 0 * D.host.g 1 * 15 ^ expL L.sc.L : ℕ) : ℝ) ≤ 30 * L.sc.L := by
  have hL := h.big.2.1
  have g0 : (0 : ℝ) < D.host.g 0 := by exact_mod_cast (D.host.g_prime 0).pos
  have g1 : (0 : ℝ) < D.host.g 1 := by exact_mod_cast (D.host.g_prime 1).pos
  have l3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have a1 : (expL L.sc.L : ℝ) * Real.log 3 ≤ 3 * L.sc.L :=
    (le_div_iff₀ l3).1 (Nat.floor_le (div_nonneg (by linarith) l3.le))
  have a2 : Real.log 15 ≤ 3 * Real.log 3 := by
    have : Real.log ((3 : ℝ) ^ 3) = 3 * Real.log 3 := by rw [Real.log_pow]; norm_num
    rw [← this]
    exact Real.log_le_log (by norm_num) (by norm_num)
  have a3 := mul_le_mul_of_nonneg_left a2 (Nat.cast_nonneg (α := ℝ) (expL L.sc.L))
  push_cast
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul g0.ne' g1.ne', Real.log_pow]
  linarith [h.logg 0, h.logg 1]

section Point

open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

set_option maxHeartbeats 800000 in

theorem weight_rows {PP A : ℝ} (h : HostNum D L PP A 1) (hw : WtNum p i PP) (hi : (i : ℕ) + 1 < D.R.m)
    (u1 : AllWt.Weight (dat p i)) (hq : Quo p i PP u1) :
    1 ≤ (dat p i).p ∧ 1 ≤ (dat p i).q ∧ (∀ τ, Antitone (u1 τ)) ∧
    (∀ τ (a b : Fin ((dat p i).p + (dat p i).q)), (b : ℕ) = a + 1 → (b : ℕ) = (dat p i).p →
      ((8 * D.R.f * D.R.r + 10 : ℕ) : ℤ) ≤ u1 τ a - u1 τ b) ∧
    Real.log (∑ τ, ∑ k, |(u1 τ k : ℝ)|) ≤ 10 * L.sc.L ∧
    (((D.R.f : ℝ) * D.R.r * L.sc.L) ^ 3 * (∑ τ, ∑ k, |(u1 τ k : ℝ)|) + ((D.R.f : ℝ) * D.R.r * L.sc.L) ^ 5) *
      (6 * dimFlag (dat p i) + 10 + lenT p i PP * (zed p i PP u1 + 2 * rhoB (dat p i) u1)) ≤ 693 * unitE p := by
  obtain ⟨h0, S, eta, -, -, -, -, hh, hH⟩ := hw.hyp hi
  have hW := hH u1
  have hD := (quo_iff p i PP h0 S eta u1).1 hq
  have m2 := D.R.two_le_m
  have k3 := D.R.m_add_three_le_k
  have f8 := h.f8
  have hL := h.big.2.1
  have hf : (8 : ℝ) ≤ D.R.f := by exact_mod_cast f8
  have hr : (2 : ℝ) ≤ D.R.r := by exact_mod_cast (by unfold Ranks.r; omega : 2 ≤ D.R.r)
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by omega : 1 ≤ D.R.m)
  have hmk : (D.R.m : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : D.R.m ≤ D.R.k)
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hcard : Fintype.card (Psi p.T.Q.H) = D.R.f := by rw [← hw.card, Nat.card_eq_fintype_card]
  have hDd : (1 : ℝ) ≤ dimFlag (dat p i) := by
    rw [hw.dim]
    exact_mod_cast Nat.mul_pos (by omega) (Nat.choose_pos (by unfold Ranks.r; omega))
  have hT : (1 : ℝ) ≤ lenT p i PP := by
    have : 4 * dimFlag (dat p i) + 4 ≤ lenT p i PP := hW.h1
    exact_mod_cast (by omega : 1 ≤ lenT p i PP)
  have hP : ((D.R.f : ℝ) * D.R.r * L.sc.L) ^ 12 ≤ PP := h.ppLow
  have hZ : (160 : ℝ) ≤ (D.R.f : ℝ) * D.R.r * L.sc.L := by
    calc (160 : ℝ) = 8 * 2 * 10 := by norm_num
      _ ≤ _ := by gcongr
  have hP1 : 160 ≤ PP := hZ.trans ((le_self_pow₀ (by linarith) (by norm_num)).trans hP)
  have kp : (wtsAt p i PP h0 S eta u1).kc < (dat p i).p := hW.kc_lt
  have pq : (dat p i).p < (dat p i).p + (dat p i).q := hW.p_lt
  have s0 : 0 ≤ ∑ τ, ∑ k, |(u1 τ k : ℝ)| := by positivity
  have s1 : (lenT p i PP : ℝ) * ∑ τ, ∑ k, |(u1 τ k : ℝ)| ≤ 8 * D.R.f * D.R.r * L.sc.b := by
    have := len_mul_l1_le _ hW hD
    rw [hcard, show (((dat p i).p + (dat p i).q : ℕ) : ℝ) = D.R.r by rw [hw.sig.2.2]] at this
    refine le_trans this (le_of_eq ?_)
    show (D.R.f : ℝ) * (D.R.r * (2 * (4 * L.sc.b))) = _
    ring
  have h1 : PP * lenT p i PP * D.R.r * D.R.f * dimFlag (dat p i) ≤ h0 := by
    refine le_trans ?_ hh
    have a1 : (D.R.f : ℝ) ≤ (D.R.f : ℝ) ^ 2 := le_self_pow₀ (by linarith) (by norm_num)
    have a2 : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 2 := one_le_pow₀ hm
    calc _ = PP * lenT p i PP * D.R.r * D.R.f * 1 * 1 * dimFlag (dat p i) := by ring
      _ ≤ _ := by gcongr; linarith
  refine ⟨by omega, by omega, fun τ => (GlobalTheory.MeanTop.divided_strictAnti _ _ _ hW hD τ).1.antitone, fun τ a b hab hb' => ?_, ?_, ?_⟩
  · have g : h0 ≤ 2 * (lenT p i PP : ℤ) * (u1 τ a - u1 τ b) := ((GlobalTheory.MeanTop.divided_gaps _ _ _ hW hD τ a b hab).2.1 hb').1
    have g' : (h0 : ℝ) ≤ 2 * (lenT p i PP : ℝ) * ((u1 τ a : ℝ) - u1 τ b) := by exact_mod_cast g
    have a1 : 160 * lenT p i PP * D.R.r * D.R.f * 1 ≤ PP * lenT p i PP * D.R.r * D.R.f * dimFlag (dat p i) := by gcongr
    have a2 : 80 * ((D.R.f : ℝ) * D.R.r) ≤ (u1 τ a : ℝ) - u1 τ b := by
      refine le_of_mul_le_mul_left ?_ (show (0 : ℝ) < 2 * lenT p i PP by linarith)
      linarith
    have a3 : (16 : ℝ) ≤ (D.R.f : ℝ) * D.R.r := by nlinarith
    have a4 : 8 * (D.R.f : ℝ) * D.R.r + 10 ≤ (u1 τ a : ℝ) - u1 τ b := by linarith
    exact_mod_cast a4
  · rcases s0.eq_or_lt with e | e
    · rw [← e, Real.log_zero]; linarith
    have a1 := Real.log_le_log e ((le_mul_of_one_le_left s0 hT).trans s1)
    rw [mul_assoc 8, Real.log_mul (by positivity) hb.ne', Real.log_mul (by norm_num) (by positivity),
      show Real.log L.sc.b = L.sc.L from Real.log_exp _] at a1
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 8 by norm_num), h.logfr.1]
  · obtain ⟨r0, -, r2⟩ := GlobalTheory.CovTop.SizeRows.rho_bounds _ hW hD
    have er : rhoOf (wtsAt p i PP h0 S eta u1).u' (wtsAt p i PP h0 S eta u1).u1 = rhoB (dat p i) u1 := by
      unfold rhoB
      congr 1
      funext τ k
      rw [uPrime_apply]; rfl
    rw [er] at r0 r2
    have r3 : rhoB (dat p i) u1 * h0 ≤ 6 * D.R.f * (D.R.r : ℝ) ^ 3 * lenT p i PP := by
      rw [← hcard, ← hw.sig.2.2]; exact r2
    have r4 : dimFlag (dat p i) * rhoB (dat p i) u1 * PP ≤ 6 * (D.R.r : ℝ) ^ 2 := by
      refine le_of_mul_le_mul_right ?_ (show (0 : ℝ) < D.R.f * D.R.r * lenT p i PP by positivity)
      linarith [mul_le_mul_of_nonneg_left h1 r0]
    have hTl : (dimFlag (dat p i) : ℝ) ^ 2 * PP ≤ lenT p i PP := by
      refine le_trans ?_ (Nat.le_ceil _)
      rw [le_div_iff₀ (by linarith), mul_comm _ PP]
      have : PP ≤ PP ^ 2 := le_self_pow₀ (by linarith) (by norm_num)
      gcongr
    have hTb : (lenT p i PP : ℝ) ≤ L.sc.b := by
      refine le_trans ?_ hw.what₂.2
      have a2 : (1 : ℝ) ≤ (dimFlag (dat p i) : ℝ) ^ 2 := one_le_pow₀ hDd
      calc (lenT p i PP : ℝ) = 1 * lenT p i PP * 1 * 1 := by ring
        _ ≤ _ := by gcongr <;> linarith
    refine (budget_arith (by linarith) (by linarith) (by linarith) hP hDd hTl hTb r0 r4 s0 s1).trans ?_
    rw [hw.unit]
    have hll := h.big.2.2.2
    calc 693 * ((D.R.f : ℝ) * L.sc.b) = 693 * (D.R.f * 1 * L.sc.b * 1 * 1) := by ring
      _ ≤ _ := by gcongr; linarith

end Point

set_option maxHeartbeats 800000 in

theorem short : Hypotheses2 → DeepGood → Size → FlatDeg → Short := fun hP _ _ hF => by
  obtain ⟨C, hC, H3⟩ := GlobalTheory.T.flat_constant_abs_le_nine_explicit hP
  refine Closed.imp (Closed.and (Closed.and (Sizes.hostN 1) WtShape.wtN) hF) fun Fm _ _ h => ?_
  obtain ⟨⟨⟨_, _, h1⟩, ⟨_, _, h2⟩⟩, ⟨_, _, h3⟩⟩ := h
  obtain ⟨x0, h⟩ := (h1.and h2).and h3
  refine ⟨C * 693, by positivity, x0, fun x hx hle ι p hp i hi Y hY u1 hq => ?_⟩
  obtain ⟨⟨g1, g2⟩, g3⟩ := h x hx hle ι p hp
  have hH := g1 i
  have hw := g2 i
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := weight_rows p i hH hw hi u1 hq
  have hL := hH.big.2.1
  have hM : Real.log Y.d.l₂.M ≤ 30 * (Fm.L x ι).sc.L := by
    rw [hY.1.lev.1.2.1, hY.1.pd, p.fw.laws.pins.2.1.1]
    exact log_level hH
  have key := H3 _ p.T p.fw.laws _ a1 a2 (by rw [hH.deg]; have := hH.f8; omega) ⟨by omega, hi.le⟩ Y _ _ hY.1 _ (by linarith) hM
    (fieldSz_host hH) hH.logfr.1 le_rfl _ (g3 i hi Y hY) (by rw [abs_neg]; exact FlatSz.abs_flatDegVal_le p i hH hw) u1 a3
    (fun τ => by
      unfold GlobalTheory.CompHS.gap
      rw [dif_pos (by show (dat p i).p - 1 + 1 < (dat p i).p + (dat p i).q; omega)]
      exact a4 τ _ _ rfl (by show (dat p i).p - 1 + 1 = _; omega)) a5
  refine ⟨Real.exp (C * ((((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r * (Fm.L x ι).sc.L) ^ 3 * (∑ τ, ∑ k, |(u1 τ k : ℝ)|) +
    (((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r * (Fm.L x ι).sc.L) ^ 5)), fun Z => ?_, ?_⟩
  · obtain ⟨n, w, abelian₂, hs, hl, -⟩ := key Z
    have := (Real.log_le_iff_le_exp (lt_of_lt_of_le one_pos hs.one_le)).1 hl
    exact ⟨n, w, hs.gen, fun k σ => (hs.le k σ).trans this, hs.one_le.trans this⟩
  · rw [Real.log_exp, mul_assoc, mul_assoc C]
    exact mul_le_mul_of_nonneg_left a6 hC

end GlobalTheory.CovHt.ShortPf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkValueClosedPointDefinedOverSubfield
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

namespace GlobalTheory.USep

theorem stalkClosedPointTo_comp_stalkMap_spec (X : Scheme.{0}) {R W : Type} [CommRing R] [IsLocalRing R]
    [CommRing W] [IsLocalRing W] (ξ : Sp R ⟶ X) (g : R →+* W)
    (hs : (spMap g ≫ ξ) (closedPoint W) ⤳ ξ (closedPoint R)) (a : X.presheaf.stalk (ξ (closedPoint R))) :
    (Scheme.stalkClosedPointTo (spMap g ≫ ξ)).hom ((X.presheaf.stalkSpecializes hs).hom a) =
      g ((Scheme.stalkClosedPointTo ξ).hom a) := by
  have key : X.presheaf.stalkSpecializes hs ≫ Scheme.stalkClosedPointTo (spMap g ≫ ξ) =
      Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom g := by
    apply Spec.map_injective
    rw [← cancel_mono (X.fromSpecStalk (ξ (closedPoint R))), Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.Spec_stalkClosedPointTo_fromSpecStalk,
      Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  exact congrArg (fun q => q.hom a) key

theorem bijective_stalkSpecializes_of_eq {X : Scheme.{0}} {x y : X} (h : x ⤳ y) (e : x = y) :
    Function.Bijective (X.presheaf.stalkSpecializes h).hom := by
  subst e
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  exact Function.bijective_id

theorem isLocalHom_stalkSpecializes_of_eq {X : Scheme.{0}} {x y : X} (h : x ⤳ y) (e : x = y) :
    IsLocalHom (X.presheaf.stalkSpecializes h).hom := by
  subst e
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  exact ⟨fun a ha => ha⟩

theorem stalkClosedPointTo_mem_subfield_of_definedOver {X : Scheme.{0}} {K : Type} [Field K] (k₀ : Subfield K) (Q : Sp K ⟶ X)
    (hQ : GlobalTheory.UChart.DefOver k₀ Q) (b : X.presheaf.stalk (Q (closedPoint K))) :
    (Scheme.stalkClosedPointTo Q).hom b ∈ k₀ := by
  obtain ⟨P₀, rfl⟩ := hQ
  have e : (spMap k₀.subtype ≫ P₀) (closedPoint K) = P₀ (closedPoint k₀) := by
    change P₀ ((spMap k₀.subtype) (closedPoint K)) = _
    congr 1
    exact Subsingleton.elim _ _
  have hs : (spMap k₀.subtype ≫ P₀) (closedPoint K) ⤳ P₀ (closedPoint k₀) := e ▸ specializes_refl _
  obtain ⟨a, rfl⟩ := (bijective_stalkSpecializes_of_eq hs e).2 b
  rw [stalkClosedPointTo_comp_stalkMap_spec X P₀ k₀.subtype hs a]
  exact SetLike.coe_mem _

theorem stalkVal_closedPoint : ∀ (X : Scheme.{0}) (R : Type) [CommRing R] [IsLocalRing R] (ξ₁ : Sp R ⟶ X) (K : Type) [Field K] (ev₁ : R →+* K) (k₀ : Subfield K), (∀ p, (spMap ev₁ ≫ ξ₁) p = ξ₁ (closedPoint R)) → GlobalTheory.UChart.DefOver k₀ (spMap ev₁ ≫ ξ₁) → ∀ h ∈ (Scheme.stalkClosedPointTo ξ₁).hom.range, ev₁ h ∈ k₀ ∧ (h ∈ maximalIdeal R → ev₁ h = 0) := by
  intro X R _ _ ξ₁ K _ ev₁ k₀ hpt hdef h hh
  obtain ⟨a, rfl⟩ := hh
  have e := hpt (closedPoint K)
  have hs : (spMap ev₁ ≫ ξ₁) (closedPoint K) ⤳ ξ₁ (closedPoint R) := e ▸ specializes_refl _
  have hv := stalkClosedPointTo_comp_stalkMap_spec X ξ₁ ev₁ hs a
  refine ⟨?_, fun hm => ?_⟩
  · rw [← hv]
    exact stalkClosedPointTo_mem_subfield_of_definedOver k₀ _ hdef _
  · by_contra hne
    have hl := isLocalHom_stalkSpecializes_of_eq hs e
    have hu : IsUnit ((Scheme.stalkClosedPointTo (spMap ev₁ ≫ ξ₁)).hom
        ((X.presheaf.stalkSpecializes hs).hom a)) := by
      rw [hv]; exact Ne.isUnit hne
    have ha : IsUnit a := isUnit_of_map_unit _ _ (isUnit_of_map_unit _ _ hu)
    exact (mem_maximalIdeal _).1 hm (ha.map _)

end GlobalTheory.USep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonCharacterGroupOfGoodReductionTrait
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc.GoodRedU

theorem subsingleton_lattice_of_range_subset : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (out : ZHOut X₁.ρ Y U₀ EE), X₁.S.admitted Y U₀ → ∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ Y.Z), Set.range ξ ⊆ (U₀ : Set Y.Z) → (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) → Subsingleton T.P.D.toPre.X := by
  intro E _ _ _ H Dw l Xo c C X₁ Y U₀ EE out _ T ξ hξ ⟨ξ₀, hξ₀, hlies⟩
  haveI : IsDiscreteValuationRing T.V := T.cdvr.1

  have hr : Set.range ξ ⊆ Set.range U₀.ι := by rw [Scheme.Opens.range_ι]; exact hξ
  let ξ' : Sp T.V ⟶ U₀.toScheme := IsOpenImmersion.lift U₀.ι ξ hr
  have hξ' : ξ' ≫ U₀.ι = ξ := IsOpenImmersion.lift_fac _ _ _
  have hK : jK T.V ≫ ξ' = ξ₀ := by
    rw [← cancel_mono U₀.ι, Category.assoc, hξ', hξ₀]
  let q : Sp T.V ⟶ Sp X₁.S.R := ξ' ≫ out.u₀
  have hB := GlobalTheory.isAbelianScheme_pullback_obj q X₁.ρ.P.A X₁.ρ.P.isAb

  obtain ⟨g, hg⟩ := Spec.map_surjective (ξ₀ ≫ out.u₀)
  have hf : X₁.Lies (spMap g.hom) T.y := by
    show X₁.Lies (Spec.map (CommRingCat.ofHom g.hom)) T.y
    rw [CommRingCat.ofHom_hom, hg]; exact hlies
  obtain ⟨G, _, α, β, hα, hβ, -⟩ := hf.uOver
  obtain ⟨tK, ⟨m₁⟩, ⟨m₂⟩⟩ := T.gen
  obtain ⟨e₁, he₁, -⟩ := grpPullback_iso m₂.cart hβ
  obtain ⟨e₂, he₂, -⟩ := grpPullback_iso (isGrpPullback_pullback T.t.G (jK T.V)) m₁.cart
  haveI := he₁
  haveI := he₂
  have hq : spMap g.hom = jK T.V ≫ q := by
    show Spec.map (CommRingCat.ofHom g.hom) = _
    rw [CommRingCat.ofHom_hom, hg, ← hK, Category.assoc]
  have h₁ := ((isGrpPullback_of_iso e₂).comp ((isGrpPullback_of_iso e₁).comp hα)).congr
    (by rw [Category.id_comp, Category.id_comp, hq]) rfl
  have h₂ := (isGrpPullback_pullback ((Over.pullback q).obj X₁.ρ.P.A) (jK T.V)).comp
    (isGrpPullback_pullback X₁.ρ.P.A q)
  obtain ⟨e, he, -⟩ := grpPullback_iso h₁ h₂

  obtain ⟨Eiso, -, -⟩ := TraitUniq.extIso T.t.semi (GlobalTheory.isSemiAbelian_of_isAbelianScheme _ hB) e he
  have hp : IsProper T.t.G.hom := by
    have := hB.proper
    have : IsIso Eiso.hom.left := inferInstanceAs (IsIso ((Over.forget _).map Eiso.hom))
    rw [← Over.w Eiso.hom]
    infer_instance
  have hc : (closedPoint T.V : Sp T.V) ∈ abLocus T.t.G := fun _ _ _ _ _ => inferInstance
  exact ChartNotAb.subsingleton_of_closed_mem_abLocus T.P hc

end GlobalTheory.UPoinc.GoodRedU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupSmulTopEqTopOfForallMaximalOverNatStatement
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sup_smul_top_eq_top_of_forall_maximal_over_nat : ∀ {E : Type} [Field E] [NumberField E] {X : Type} [AddCommGroup X] [Module (𝓞 E) X]
    (N : Submodule (𝓞 E) X) (n : ℕ) (hn : 0 < n)
    (h : ∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 → N ⊔ 𝔮 • (⊤ : Submodule (𝓞 E) X) = ⊤),
    N ⊔ Ideal.span {(n : 𝓞 E)} • (⊤ : Submodule (𝓞 E) X) = ⊤ := by
  first | exact @GlobalTheory.sup_smul_top_eq_top_of_maximal | exact GlobalTheory.sup_smul_top_eq_top_of_maximal | (intros; apply GlobalTheory.sup_smul_top_eq_top_of_maximal <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymbolEntriesRegularAffineOpen
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.Heat.SymReg

theorem sum_sum_bilin_regroup {I₁ I₂ J₁ J₂ R : Type} [Fintype I₁] [Fintype I₂] [Fintype J₁] [Fintype J₂] [CommRing R]
    (x : I₁ → R) (y : I₂ → R) (L : J₁ → J₂ → R) (u : J₁ → I₁ → R) (w : J₂ → I₂ → R) :
    ∑ i, ∑ j, x i * y j * ∑ a, ∑ e, L a e * u a i * w e j
      = ∑ a, ∑ e, L a e * (∑ i, x i * u a i) * (∑ j, y j * w e j) := by
  simp only [Finset.mul_sum, Finset.sum_mul]
  calc ∑ i, ∑ j, ∑ a, ∑ e, x i * y j * (L a e * u a i * w e j)
      = ∑ i, ∑ a, ∑ e, ∑ j, x i * y j * (L a e * u a i * w e j) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a, ∑ e, ∑ i, ∑ j, x i * y j * (L a e * u a i * w e j) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a, ∑ e, ∑ j, ∑ i, L a e * (x i * u a i) * (y j * w e j) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

theorem entry_regular : ∀ (K : Type) [Field K] [CharZero K] (P₀ : Out.PolAV (Sp K)) (n : ℕ) (v : Module.Basis (Fin n) K (TanM (𝟙 (Sp K)) P₀.A)) (dd : Fin n → Fld P₀.A.left), (∀ a, IsInv P₀.A (v a) (dd a)) → ∀ (F : Type) [Field F] (ψ : K →+* F) (ξ : Sp F ⟶ P₀.A.left), ξ ≫ P₀.A.hom = spMap ψ → (∀ O (f : Γ(P₀.A.left, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 → f = 0) → ∀ (δ : Fin n → Derivation ℤ F F), (∀ a O f, ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O (dd a O f) = δ a (valR ξ O f)) → ∀ (Λ : Matrix (Fin n) (Fin n) F) (W : P₀.A.left.Opens), IsAffineOpen W → ⊤ ≤ ξ ⁻¹ᵁ W → (∀ f f' : Γ(P₀.A.left, W), ∃ h : Γ(P₀.A.left, W), valR ξ _ h = ∑ a, ∑ e, Λ a e * δ a (valR ξ _ f) * δ e (valR ξ _ f')) → ∀ a e, ∃ h : Γ(P₀.A.left, W), valR ξ W h = Λ a e := by
  intro K _ _ P₀ n v dd hinv F _ ψ ξ _ _ δ hδ Λ W hW hξW hΛ a e
  let φ : Γ(P₀.A.left, W) →+* F :=
    (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom.comp (ξ.appLE W ⊤ hξW).hom
  have hφ : ∀ f, valR ξ W f = φ f := fun f => by
    unfold valR; rw [dif_pos hξW]; rfl
  have hδ' : ∀ b x, φ (dd b W x) = δ b (φ x) := fun b x => by
    rw [← hφ, ← hφ]; exact hδ b W x hξW
  obtain ⟨N, g, f, hgf⟩ := GlobalTheory.T.exists_dual_oneForms_invariantFields_affineOpen K P₀ n v dd hinv W hW a
  obtain ⟨N', g', f', hgf'⟩ := GlobalTheory.T.exists_dual_oneForms_invariantFields_affineOpen K P₀ n v dd hinv W hW e
  choose h hh using fun (i : Fin N) (j : Fin N') => hΛ (f i) (f' j)
  have hh' : ∀ i j, φ (h i j) = ∑ a', ∑ e', Λ a' e' * δ a' (φ (f i)) * δ e' (φ (f' j)) := by
    intro i j; rw [← hφ, hh]; simp only [hφ]
  have key : ∀ b, ∑ i, φ (g i) * δ b (φ (f i)) = if a = b then 1 else 0 := by
    intro b
    have := congrArg φ (hgf b)
    simp only [map_sum, map_mul, hδ'] at this
    rw [this]; split_ifs <;> simp
  have key' : ∀ b, ∑ j, φ (g' j) * δ b (φ (f' j)) = if e = b then 1 else 0 := by
    intro b
    have := congrArg φ (hgf' b)
    simp only [map_sum, map_mul, hδ'] at this
    rw [this]; split_ifs <;> simp
  refine ⟨∑ i, ∑ j, g i * g' j * h i j, ?_⟩
  rw [hφ]
  simp only [map_sum, map_mul, hh']
  rw [sum_sum_bilin_regroup (fun i => φ (g i)) (fun j => φ (g' j)) Λ (fun a' i => δ a' (φ (f i)))
    (fun e' j => δ e' (φ (f' j)))]
  simp only [key, key', mul_ite, _root_.mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

end GlobalTheory.Heat.SymReg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateIsoLatticePartSurjectiveCoisotropicKernelStatement
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LowDat GlobalTheory.LowFilt
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateIso_latticePart_surjective_coisotropicKernel : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    (D₀ : DegPre R) [Module (𝓞 E) D₀.X] (oa : letI := H.starRing; D₀.OAct (𝓞 E)), D₀.PsiEven → D₀.TauBimult →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing R) F] (I : TateIsoQ D D₀ oa F),
    ∃ y : ℕ → D.La →ₗ[𝓞 E] D₀.X, (∀ n, 0 < n → ∀ a, ∃ e, y n a = (I.ev n a).y + n • e) ∧
      ∀ n, 0 < n → Cois D (y n) n := by
  first | exact @GlobalTheory.LowFilt.tateIsoQ_y_cois | exact GlobalTheory.LowFilt.tateIsoQ_y_cois | (intros; apply GlobalTheory.LowFilt.tateIsoQ_y_cois <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyFormulaNormalCoverRationalThetaConstantsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaKeyFormula_normalCover_rational_thetaConstants : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (o : Type) [CommRing o] (m n : ℕ) (f : Xo.XF c ⟶ PSpace o n), Odd m → 3 ≤ m → IsUnit (m : o) → n + 1 = m ^ (4 * (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))) → ThMap Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig m (pullback.fst _ _ : Xo.XF c ⟶ Xo.X) f → ∀ (Y : Model Xo c (RingHom.id c.F)) (g : Y.X ⟶ PSpace o n), Y.j ≫ g = f → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [Algebra c.F Ω] (M : RatModel c.F Ω) (π : M.Z ⟶ Y.X) (y : Sp Ω ⟶ Xo.XF c) (d : Fin (n + 1) → Ω), Geo.Tor.IsNormalScheme M.Z → M.pt ≫ π = y ≫ Y.j → HasTh Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig m (y ≫ pullback.fst _ _) d → LBIso ((lbPow ((ProjSpace.O1 o n).pull g) 8).pull π) ((lbPow (GlobalTheory.SiegelTor.hodge Y.t.G (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))) (4 * (n + 1).factorial)).pull π) := by
  first | exact @GlobalTheory.UMin.key_on_cover | exact GlobalTheory.UMin.key_on_cover | (intros; apply GlobalTheory.UMin.key_on_cover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaWeightPartValueDependsTraitLabelsClassStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaWeightPart_value_depends_trait_labels_class : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (z₁ : X₁.M.Z) (z₂ : D.X.M.Z), D.q z₂ = z₁ → ∃ U : X₁.S.HH X₁.M z₁ → D.X.Ω₁, (∀ κ, ∃ k : ℕ, 0 < k ∧ U κ ^ k = 1) ∧ ∀ (p : ℕ) [Fact p.Prime] (c : CTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab X₁ ε₁ c yy₁ → ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y), y (cPt p) = z₂ → ∀ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X), IsLab D.X D.ε (D.lift c y h) yy → D.Compat yy₁ yy → ∀ (y' : Sp (OO p) ⟶ D.X.M.Z) (h' : y' ≫ D.q = c.y), y' (cPt p) = z₂ → ∀ yy' : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X), IsLab D.X D.ε (D.lift c y' h') yy' → D.Compat yy₁ yy' → ∀ a a' ν ν' κ, yy a = QuotientAddGroup.mk ν → yy' a' = QuotientAddGroup.mk ν' → CongMod D.m ν ν' → D.X.M.val (gPt p ≫ y) (U κ * GSum.part D z₁ z₂ a κ) = D.X.M.val (gPt p ≫ y') (U κ * GSum.part D z₁ z₂ a' κ) := by
  first | exact @GlobalTheory.Poinc.GSum.val_part_eq | exact GlobalTheory.Poinc.GSum.val_part_eq | (intros; apply GlobalTheory.Poinc.GSum.val_part_eq <;> assumption)
end

