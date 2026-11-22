import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsTauZeroNonzeroAll
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2114
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0010
import Development.AutomorphicArithmetic.LocalEmbeddings.ThinCover
import Development.AutomorphicArithmetic.LocalEmbeddings.ThinCore
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaBoundLengthUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2447
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2537
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2741
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0124
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2206
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1607
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2599
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2578
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2616
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2576
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2929
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2786
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2801
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2982
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2992
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2985
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3014
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2984
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormExistsBelowFrameBound
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt

namespace UpperTheory.Dv.Thin

private theorem covers_and_imp {Q₁ Q₂ Q₃ : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x) (p : Pt Fm x hx ι)
    (i : Fin (Fm.D x ι).R.m) (_Y : Cov p i) (PP C : ℝ), Prop}
    (h₁ : Covers Q₁) (h₂ : Covers Q₂)
    (h : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x) (p : Pt Fm x hx ι)
      (i : Fin (Fm.D x ι).R.m) (Y : Cov p i) (PP C C' : ℝ),
      Q₁ Fm x hx ι p i Y PP C → Q₂ Fm x hx ι p i Y PP C' → (i : ℕ) + 1 < (Fm.D x ι).R.m → GoodCov p i Y →
        Q₃ Fm x hx ι p i Y PP C) : Covers Q₃ := by
  unfold Covers Lifts at *
  refine (h₁.and h₂).imp fun Fm CH _ hh => ?_
  obtain ⟨⟨C, hC, h1⟩, ⟨C', _, h2⟩⟩ := hh
  obtain ⟨a, h3⟩ := h1.and h2
  exact ⟨C, hC, a, fun x hx hle ι p hp i hi Y hY =>
    h Fm x hx ι p i Y _ C C' ((h3 x hx hle ι p hp).1 i hi Y hY) ((h3 x hx hle ι p hp).2 i hi Y hY) hi hY⟩

private theorem cols_ge {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H) :
    Fintype.card (Psi H) * (Dw.p + Dw.q) * (Dw.p + Dw.q + 1) ≤ 2 * GlobalTheory.RefSum.nCol Dw := by
  refine le_trans ?_ (Nat.mul_le_mul_left 2 GlobalTheory.RefSum.sum_le_nCol)
  have h1 : ∀ m : ℕ, ∑ i : Fin m, 2 * (i.val + 1) = m * (m + 1) := fun m => by
    induction m with
    | zero => simp
    | succ m ih => rw [Fin.sum_univ_castSucc]; simp only [Fin.val_castSucc, Fin.val_last, ih]; ring
  rw [Fintype.sum_sigma]
  simp only [h1]
  rw [GlobalTheory.RawThetaSup.sum_emb_eq H, Finset.mul_sum, mul_assoc, ← Finset.card_univ, ← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun τ _ => ?_
  rw [Datum.mult, if_pos τ.2, Datum.mult, if_neg (conj_not_mem τ)]
  nlinarith [sq_nonneg ((Dw.p : ℤ) - Dw.q)]

private theorem one_le_DF {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
    (hp : 1 ≤ Dw.p) (hne : 0 < Fintype.card (Psi H)) {a : (E →+* ℂ) × ℕ → ℕ} (h : LastPos Dw a) :
    1 ≤ Formalism.L2.Pj.DF Dw a := by
  obtain ⟨τ⟩ := Fintype.card_pos_iff.1 hne
  have hm : 0 < Dw.mult τ.1 := by rw [Datum.mult, if_pos τ.2]; exact hp
  refine (h τ.1 τ.2 hm).trans_le ?_
  unfold Formalism.L2.Pj.DF
  refine le_trans ?_ (Finset.single_le_sum (f := fun τ : E →+* ℂ => ∑ i : Fin (Dw.mult τ), a (τ, i))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ τ.1))
  exact Finset.single_le_sum (f := fun i : Fin (Dw.mult τ.1) => a (τ.1, i)) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ ⟨Dw.mult τ.1 - 1, by omega⟩)

private theorem frn_le {f r n t : ℝ} (ht : 11 ≤ t) (hf0 : 0 ≤ f) (hr0 : 0 ≤ r) (hf : f ≤ t) (hr : r ≤ t)
    (hn : n ≤ 2 * r * (f * r) + 8 * (f * r) + 8) : f * r * n ≤ t ^ 150 := by
  have h1 : n ≤ 2 * t * (t * t) + 8 * (t * t) + 8 := hn.trans (by gcongr)
  have h2 : n ≤ t ^ 4 := by
    have : 11 * t ^ 3 ≤ t ^ 4 := by rw [pow_succ' t 3]; gcongr
    have : 11 * t ^ 2 ≤ t ^ 3 := by rw [pow_succ' t 2]; gcongr
    nlinarith
  calc f * r * n ≤ f * r * t ^ 4 := by gcongr
    _ ≤ t * t * t ^ 4 := by gcongr
    _ = t ^ 6 := by ring
    _ ≤ _ := pow_le_pow_right₀ (by linarith) (by norm_num)

set_option maxHeartbeats 1000000 in

private theorem sizes : Size → Covers fun Fm x _ ι p i Y PP _ => ∀ u1, Quo p i PP u1 → (Dom (GlobalTheory.RefSum.aOf p i u1) (GlobalTheory.RefSum.nCol (dat p i)) ∧ LastPos (dat p i) (GlobalTheory.RefSum.aOf p i u1) ∧ Nonempty (ErrX (Fm.D x ι))) ∧ 1000 ≤ (Fm.L x ι).sc.b ∧ (Fm.D x ι).R.r ≤ GlobalTheory.RefSum.nCol (dat p i) ∧ (Fm.D x ι).R.f * (Fm.D x ι).R.r * ((Fm.D x ι).R.r + 1) ≤ 2 * GlobalTheory.RefSum.nCol (dat p i) ∧ ((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r * GlobalTheory.RefSum.nCol (dat p i) ≤ (Fm.L x ι).sc.b ∧ (Fm.D x ι).host.rdE ^ 7 ≤ (Fm.L x ι).sc.b ∧ (Fm.L x ι).sc.b ^ 16 ≤ (((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1 : ℕ) : ℝ) ∧ (((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1 : ℕ) : ℝ) ≤ (Fm.L x ι).sc.b ^ 70 ∧ 1 ≤ Formalism.L2.Pj.DF (dat p i) (GlobalTheory.RefSum.aOf p i u1) ∧ ((Formalism.L2.Pj.DF (dat p i) (GlobalTheory.RefSum.aOf p i u1) : ℕ) : ℝ) ≤ (Fm.L x ι).sc.b ^ 2 ∧ (((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1 : ℕ) : ℝ) * (Fm.L x ι).sc.b ≤ (Y.d.l₂.M : ℝ) := by
  intro hS
  refine (Formalism.MainNotions.Closed.and (Formalism.MainNotions.Closed.and (GlobalTheory.CovTop.Sizes.hostN 6) GlobalTheory.CovTop.WtShape.wtN)
    (GlobalTheory.RefSum.QuoShape.quo_shape hS)).imp fun Fm CH _ hh => ?_
  obtain ⟨⟨⟨A, -, h1⟩, ⟨C2, -, h2⟩⟩, ⟨C3, -, h3⟩⟩ := hh
  obtain ⟨a, ha⟩ := h1.and (h2.and h3)
  refine ⟨0, le_rfl, a, fun x hx hle ι p hp i hi Y hY u1 hu => ?_⟩
  have hN : HostNum (Fm.D x ι) (Fm.L x ι) (Fm.parT x hx ι).PP A 6 := (ha x hx hle ι p hp).1 i
  have hW : WtNum p i (Fm.parT x hx ι).PP := (ha x hx hle ι p hp).2.1 i
  obtain ⟨q1, -, q3, q4, q5, q6, q7, q8, -⟩ := (ha x hx hle ι p hp).2.2 i hi u1 hu
  have S := Fm.sizes x hx ι
  obtain ⟨-, -, -, -, -, sC, sQD, -, -, -, -, -, -, -, -, -, -, -, -, -, sG, -⟩ := S
  obtain ⟨-, -, -, -, -, -, h1, h2⟩ := sQD
  have a1 := (Fm.D x ι).R.two_le_m
  have a2 := (Fm.D x ι).R.m_add_three_le_k
  have a3 : (Fm.D x ι).R.r + 5 ≤ (Fm.D x ι).R.t := (Fm.D x ι).R.rank_add_five_le
  have a4 : (Fm.D x ι).R.f ≤ (Fm.D x ι).R.k := (Fm.D x ι).R.f_le_k
  have a5 : (Fm.D x ι).R.k ≤ (Fm.D x ι).R.r ∧ (Fm.D x ι).R.m ≤ (Fm.D x ι).R.r ∧ 6 ≤ (Fm.D x ι).R.r := by
    unfold Formalism.BasicNotions.Ranks.r; omega
  have hf8 := hN.f8
  have hL10 : 10 ≤ (Fm.L x ι).sc.L := hN.big.2.1
  have hfR : (8 : ℝ) ≤ (Fm.D x ι).R.f := by exact_mod_cast hf8
  have hrR : (6 : ℝ) ≤ (Fm.D x ι).R.r := by exact_mod_cast a5.2.2
  have ht : (11 : ℝ) ≤ (Fm.D x ι).R.t := by exact_mod_cast (by omega : 11 ≤ (Fm.D x ι).R.t)
  have hft : ((Fm.D x ι).R.f : ℝ) ≤ (Fm.D x ι).R.t := by exact_mod_cast (by omega : (Fm.D x ι).R.f ≤ (Fm.D x ι).R.t)
  have hrt : ((Fm.D x ι).R.r : ℝ) ≤ (Fm.D x ι).R.t := by exact_mod_cast (by omega : (Fm.D x ι).R.r ≤ (Fm.D x ι).R.t)
  have hb : 1000 ≤ (Fm.L x ι).sc.b := by
    have e1 : Real.exp 10 ≤ (Fm.L x ι).sc.b := Real.exp_le_exp.2 hL10
    have e2 : (2 : ℝ) ^ 10 ≤ Real.exp 1 ^ 10 := by gcongr; linarith [Real.add_one_le_exp 1]
    rw [← Real.exp_nat_mul] at e2
    norm_num at e2
    linarith
  have hb1 : 1 ≤ (Fm.L x ι).sc.b := by linarith
  have hc : (Fm.D x ι).host.rdE ≤ szCond (Fm.L x ι) := by
    unfold szCond
    exact UpperTheory.Ram.Rd.rdE_le_cond _
  have hc1 : (1 : ℝ) ≤ szCond (Fm.L x ι) := h1.trans hc
  have hsb : Real.sqrt (Fm.L x ι).sc.b ≤ (Fm.L x ι).sc.b :=
    Real.sqrt_le_iff.2 ⟨by linarith, le_self_pow₀ hb1 (by norm_num)⟩
  have hrdb : (Fm.D x ι).host.rdE ^ 7 ≤ (Fm.L x ι).sc.b := by
    have e1 : (Fm.D x ι).host.rdE ^ 7 ≤ szCond (Fm.L x ι) ^ 36 * ((Fm.D x ι).R.t : ℝ) ^ 150 :=
      (pow_le_pow_left₀ (by linarith) hc 7).trans ((pow_le_pow_right₀ hc1 (by norm_num)).trans
        (le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by linarith))))
    exact (e1.trans sC).trans hsb
  have htb : ((Fm.D x ι).R.t : ℝ) ^ 150 ≤ (Fm.L x ι).sc.b :=
    ((le_mul_of_one_le_left (by positivity) (one_le_pow₀ hc1)).trans sC).trans hsb
  have hcard : Fintype.card (Psi p.T.Q.H) = (Fm.D x ι).R.f := Nat.card_eq_fintype_card.symm.trans hW.card
  have hcol := cols_ge (dat p i)
  rw [hcard, q3] at hcol
  have h2r := GlobalTheory.RefSum.NumPt.two_mul_rank_le_nCol (dat p i)
  rw [q3] at h2r
  have hnle : (GlobalTheory.RefSum.nCol (dat p i) : ℝ) ≤ 2 * (Fm.D x ι).R.r * ((Fm.D x ι).R.f * (Fm.D x ι).R.r) +
      8 * ((Fm.D x ι).R.f * (Fm.D x ι).R.r) + 8 := by exact_mod_cast GlobalTheory.LiftGaps.nCol_le p i _ _ _ hW hN
  have hfrn : ((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r * GlobalTheory.RefSum.nCol (dat p i) ≤ (Fm.L x ι).sc.b :=
    (frn_le ht (by positivity) (by positivity) hft hrt hnle).trans htb
  have hk : (1 : ℝ) ≤ (Fm.D x ι).R.k := by exact_mod_cast (by omega : 1 ≤ (Fm.D x ι).R.k)
  have hg : ∀ k, (Fm.L x ι).sc.b ^ 8 ≤ ((Fm.D x ι).host.g k : ℝ) := fun k =>
    (pow_le_pow_left₀ (by linarith) (le_mul_of_one_le_left (by linarith) hk) 8).trans (sG k k).1
  have hg' : ∀ k, ((Fm.D x ι).host.g k : ℝ) ≤ (Fm.L x ι).sc.b ^ 35 := fun k => by
    have h0 : (0 : ℝ) < (Fm.D x ι).host.g k := by exact_mod_cast ((Fm.D x ι).host.g_prime k).pos
    unfold Formalism.BasicNotions.Scale.b
    rw [← Real.exp_nat_mul, ← Real.log_le_iff_le_exp h0]
    push_cast
    linarith only [hN.logg k, hL10]
  have hev : Even (GlobalTheory.RefSum.nCol (dat p i)) := q7.2
  have hDF := (GlobalTheory.RefSum.thA_dominant_lastPos_degree _ _ (dat p i) u1 (GlobalTheory.RefSum.nCol (dat p i)) _ q1 hev q4 q5 q6).2.2.2.2
  rw [hN.deg, q3, Nat.mul_div_cancel_left _ two_pos] at hDF
  refine ⟨⟨q7, q8, ⟨(Fm.ex x hx ι).errX⟩⟩, hb, by omega, hcol, hfrn, hrdb, ?_, ?_,
    one_le_DF _ q1 (by rw [hcard]; omega) q8, hDF.trans ?_, GlobalTheory.ThetaSizeBounds.level_ge p i Y hY (by linarith)⟩
  · push_cast
    rw [show 16 = 8 + 8 from rfl, pow_add]
    exact mul_le_mul (hg 0) (hg 1) (by positivity) (by positivity)
  · push_cast
    rw [show 70 = 35 + 35 from rfl, pow_add]
    exact mul_le_mul (hg' 0) (hg' 1) (by positivity) (by positivity)
  · have h5 : (5 : ℝ) ≤ GlobalTheory.RefSum.nCol (dat p i) := by exact_mod_cast (by omega : 5 ≤ GlobalTheory.RefSum.nCol (dat p i))
    have h6 : ((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r * 5 ≤ (Fm.L x ι).sc.b :=
      (mul_le_mul_of_nonneg_left h5 (by positivity)).trans hfrn
    calc ((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r * (2 * (2 * (Fm.L x ι).sc.b) + 1)
        ≤ ((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r * (5 * (Fm.L x ι).sc.b) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = ((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r * 5 * (Fm.L x ι).sc.b := by ring
      _ ≤ (Fm.L x ι).sc.b * (Fm.L x ι).sc.b := mul_le_mul_of_nonneg_right h6 (by linarith)
      _ = _ := by ring

set_option maxHeartbeats 4000000 in

theorem _root_.GlobalTheory.T.cusp_form_exists_below_frame_bound : Hypotheses2 → HypothesesH → DeepGood → Size → FlatDeg → Covers fun Fm x _ ι p i Y PP _ => ∀ u1, Quo p i PP u1 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (σ : Y.d.c₂.F →+* ℂ), GoodEmb Y.d.c₂ σ → ∀ y : FPt (Y.U σ).X, (⟨y.1, y.2.1⟩ : Σ k, Frame ((Y.U σ).X k).Ψ (Fm.D x ι).R.r) ∈ framesOn (Y.U σ) Z → (Y.d.l₂.M : ℝ) * ((Y.U σ).X y.1).firstMinimumSq y.2.1 < (Fm.L x ι).sc.b → ∃ f ∈ cuspW Y.d.Xo₂ Y.d.c₂ Y.U (GlobalTheory.RefSum.GOf p i u1), rdU (Y.U σ) f y.1 y.2.1 ≠ 0 ∧ ∀ z : FPt (Y.U σ).X, (⟨z.1, z.2.1⟩ : Σ k, Frame ((Y.U σ).X k).Ψ (Fm.D x ι).R.r) ∈ framesOn (Y.U σ) Z → Real.exp (-(2 * (ReciprocityTheory.ChartRestriction.G.I2.PT.f (Fm.D x ι).host.E : ℝ) / (ReciprocityTheory.ChartRestriction.G.I2.PT.rd (Fm.D x ι).host.E ^ 2 * ((Y.U σ).X y.1).la1 y.2.1 ^ 2) / 1250)) * ptN (modelWt (Y.U σ) (GlobalTheory.RefSum.GOf p i u1)) (rdU (Y.U σ) f) ⟨z.1, z.2.1⟩ ≤ ptN (modelWt (Y.U σ) (GlobalTheory.RefSum.GOf p i u1)) (rdU (Y.U σ) f) ⟨y.1, y.2.1⟩ := by
  intro _ _ _ hS _
  refine covers_and_imp (sizes hS) (GlobalTheory.ThetaSizeBounds.params_sqrt_bounds hS) ?_
  intro eps Fm x hx ι p i Y PP C C' hA hB hi hY u1 hu Z σ hσ y hy hM
  obtain ⟨⟨hD, hLP, ⟨EX⟩⟩, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10⟩ := hA u1 hu
  obtain ⟨r1, -, -, r4⟩ := hB
  obtain ⟨hrun, -⟩ := r4 _ s8 s9
  have hj : InR (Fm.D x ι) ((i : ℕ) + 1) := ⟨by omega, hi.le⟩
  have hl : p.T.Q.l.M = (Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1 := p.fw.laws.toLawsM.pins.2.1.1
  obtain ⟨⟨α, hα1, hα2⟩, -⟩ := GlobalTheory.HalfGen.half_principal_and_split _ p.T.toCore p.fw.laws.toLawsM EX
  obtain ⟨φ, hφ, hg⟩ := cover_transport _ p.T _ Y _ _ p.fw.laws hj hY.1 _ _ hD σ hσ
  have hd := hφ ⟨y.1, y.2.1⟩ y.2.2
  have hσ' : GoodEmb p.T.Q.c (Y.resEmb σ) := Y.good_resEmb hσ
  have hla : ((p.T.U ((i : ℕ) + 1) (Y.resEmb σ)).X (φ ⟨y.1, y.2.1⟩).1).la1 (φ ⟨y.1, y.2.1⟩).2 =
      ((Y.U σ).X y.1).la1 y.2.1 := congrArg Real.sqrt hd.2
  have h0 : 0 ≤ ((Y.U σ).X y.1).firstMinimumSq y.2.1 := ReciprocityTheory.ChartRestriction.G.FD.MinimumGrowthBounds.minimumSq_nonneg _ y.2.2
  have hs1 : (((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1 : ℕ) : ℝ) * ((Y.U σ).X y.1).firstMinimumSq y.2.1 ≤ 1 := by
    have h1 := (mul_le_mul_of_nonneg_right s10 h0).trans hM.le
    rw [mul_right_comm] at h1
    exact le_of_mul_le_mul_right (h1.trans_eq (one_mul _).symm) (by linarith only [s1])
  obtain ⟨f, hf, hf0, hfz⟩ := core_ratio (GlobalTheory.LevGeo.laws_core _ p.T _ p.fw.laws hj) α hα1 hα2 hD hLP s1 s2 s3 s4 s5
    (by rw [hl]; exact s6) (by rw [hl]; exact s7) s9 (by rw [hl]; exact hrun) r1 hσ' (φ ⟨y.1, y.2.1⟩).1
    (φ ⟨y.1, y.2.1⟩).2 hd.1 (by rw [hl, hd.2]; exact hs1)
  obtain ⟨g, hg', hgy⟩ := hg f hf
  refine ⟨g, hg', (hgy ⟨y.1, y.2.1⟩ y.2.2).2.mpr hf0, fun z hz => ?_⟩
  rw [(hgy ⟨z.1, z.2.1⟩ z.2.2).1, (hgy ⟨y.1, y.2.1⟩ y.2.2).1, ← hla]
  exact hfz ⟨(φ ⟨z.1, z.2.1⟩).1, (φ ⟨z.1, z.2.1⟩).2, (hφ ⟨z.1, z.2.1⟩ z.2.2).1⟩

end UpperTheory.Dv.Thin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamPairingPullback
section
set_option autoImplicit false

noncomputable section

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory
open TopologicalSpace

namespace GlobalTheory.CechKS

set_option maxHeartbeats 1000000 in

theorem exists_isRep_eps {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {A' : Over (Sp (DualNumber K))}
    [GrpObj A'] {i : A.left ⟶ A'.left} (h : IsGrpPullback A A' (DeRham.epsRed K) i) (hA : IsAbelianScheme A)
    (L : LB A.left) {n : ℕ} (u : Fin n → (epsR K ⟶ A)) (θ : Matrix (Fin n) (Fin n) K) (hu : ∀ a, IsTangent (u a))
    (H : IsCechKS A A' i L u θ) (ω' : Form (A'.hom ≫ 𝟙 (Sp (DualNumber K))))
    (b : Z1 (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))))
    (e : (liftMor (epsDP K) h).isMor.pull1 (Form.cl _ ω') =
      (constMor A).isMor.pull1 (Form.cl _ ((fibMor h).isMor.pullForm ω')) +
        (DualNumber.eps : DualNumber K) • (constMor A).isMor.pull1 (H1.mk _ b)) :
    ∃ (J : Type) (V : J → A.left.affineOpens) (τ : J → L.ι), ⨆ j, (V j).1 = ⊤ ∧ (∀ j, (V j).1 ≤ L.U (τ j)) ∧
      IsRep (fun j ↦ (V j).1) b fun j j' P ↦ -∑ a, (∑ c, algebraMap K P.B (θ a c) * dlog L (u c) (τ j) (τ j') P) *
        algebraMap K P.B (tanVal (u a) ((fibMor h).isMor.pullForm ω')) := by
  classical
  obtain ⟨J, W, c, y, hW, hc, hl, hn, hd⟩ := GlobalTheory.T.exists_lifts_of_cechKodairaSpencerDeformation K A A' i L n u θ hu H
  obtain ⟨G, hG⟩ := GlobalTheory.T.epsilonPart_deformationForm_class_eq_coboundary_of_lifts K A A' i h ω' _ b e
  let J' : Type := {p : J × A'.left.affineOpens × A.left.affineOpens // p.2.2.1 ≤ W p.1 ⊓ i ⁻¹ᵁ p.2.1.1}
  refine ⟨J', fun j ↦ j.1.2.2, fun j ↦ c j.1.1, ?_, fun j ↦ (j.2.trans inf_le_left).trans (hc _), ?_⟩
  · refine eq_top_iff.2 fun p _ ↦ ?_
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (hW.ge (Set.mem_univ p))
    obtain ⟨_, ⟨U, hU, rfl⟩, hpU, -⟩ := A'.left.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (i p)) isOpen_univ
    obtain ⟨_, ⟨V, hV, rfl⟩, hpV, hle⟩ := A.left.isBasis_affineOpens.exists_subset_of_mem_open
      (show p ∈ W k ⊓ i ⁻¹ᵁ U from ⟨hk, hpU⟩) (W k ⊓ i ⁻¹ᵁ U).isOpen
    exact Opens.mem_iSup.2 ⟨⟨(k, ⟨U, hU⟩, ⟨V, hV⟩), hle⟩, hpV⟩
  · have hin : ∀ (j : J') (P : GPt A), P.In j.1.2.2.1 → P.In (W j.1.1) := fun j P hP ↦
      hP.mono (j.2.trans inf_le_left)
    refine ⟨fun j P ↦ if hP : P.In (W j.1.1) then (liftVal h ω'.1 (hl _ P hP)).snd + G P else 0,
      fun j P Q φ hP ↦ ?_, fun j j' P hj hj' ↦ ?_⟩
    · simp only [dif_pos (hin j P hP), dif_pos (hin j Q (hP.map φ))]
      exact hG P Q φ _ _ _ _ (hn _ P Q φ (hin j P hP))
    · simp only [dif_pos (hin j P hj), dif_pos (hin j' P hj')]
      have hU : P.In (i ⁻¹ᵁ j.1.2.1.1) := hj.mono (j.2.trans inf_le_right)
      rw [add_sub_add_right_eq_sub, ← TrivSqZeroExt.snd_sub]
      exact GlobalTheory.T.firstOrderDeformation_form_lift_values_sub K A A' i h hA ω' _ j.1.2.1.2 P hU _ _ _ _ n u _ hu
        fun f ↦ hd _ _ P _ f (hin j P hj) (hin j' P hj') hU

theorem eval_eq_zero {K M I : Type*} [Field K] [AddCommGroup M] [Module K M] [Fintype I] {n : ℕ}
    (f k : Module.Dual K M) (b x : M) (c : I → M) (θ : Matrix (Fin n) (Fin n) K) (hb : Fin n → Module.Dual K M)
    (α p : Fin n → K) (t : Fin n → I → K) (e4 : ∀ a, hb a x = α a) (e5 : ∀ b, p b = ∑ k, f (c k) * t b k)
    (e1 : f (b + ∑ a, ∑ b, (θ a b * α a) • ∑ k, t b k • c k) = 0)
    (e2 : (TrivSqZeroExt.inl (f x) + TrivSqZeroExt.inr (k x) : DualNumber K) +
      (DualNumber.eps : DualNumber K) • (TrivSqZeroExt.inl (f b) + TrivSqZeroExt.inr (k b) : DualNumber K) = 0) :
    (k - ∑ a, (∑ b, θ a b * p b) • hb a) x = 0 := by
  have e3 := congrArg TrivSqZeroExt.snd e2
  have e6 : ∀ b, ∑ k, t b k * f (c k) = p b := fun b ↦
    (Finset.sum_congr rfl fun k _ ↦ mul_comm _ _).trans (e5 b).symm
  simp only [map_add, map_sum, map_smul, smul_eq_mul, e6] at e1
  simp only [LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, e4, Finset.sum_mul]
  simp at e3
  have e7 : ∑ a, ∑ b, θ a b * p b * α a = ∑ a, ∑ b, θ a b * α a * p b :=
    Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ by ring
  rw [e7]
  linear_combination e3 - e1

set_option maxHeartbeats 1000000 in

theorem isKSValue_of_isCechKS (P : GlobalTheory.Published.AbelianDeRham) {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A]
    {A' : Over (Sp (DualNumber K))} [GrpObj A'] {i : A.left ⟶ A'.left} (h : IsGrpPullback A A' (DeRham.epsRed K) i)
    {g : ℕ} (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) (hA' : IsAbelianScheme A')
    (hg' : SmoothOfRelativeDimension g A'.hom) (L : LB A.left) (hL : L.IsLB) (ψ : LinearMap.BilinForm K (HdR A))
    (hψ : IsPolForm (dp0 K) (𝟙 _) A L ψ) {n : ℕ} (u : Fin n → (epsR K ⟶ A)) (θ : Matrix (Fin n) (Fin n) K)
    (hu : ∀ a, IsTangent (u a)) (H : IsCechKS A A' i L u θ) (hb : Fin n → HdR A)
    (hhb : ∀ b, DeRham.IsLieImage (hb b) (u b)) {f : HdR A} (hf : f ∈ Fil A) :
    IsKSValue h f (FlagTan.lieComb (fun a ↦ ∑ b, θ a b * ψ f (hb b)) u) := by
  classical
  obtain ⟨v, k, ⟨d, hd, hdk⟩, -⟩ := IsKSValue.exists_of_isAbelianScheme P h hA' hg' hf
  obtain ⟨I, _, c, ω, hω, hch, hψf⟩ := GlobalTheory.T.firstChern_eq_sum_cup_invariantForms P K A g hA hg L hL ψ hψ
  choose z hz using fun k ↦ H1.mk_surjective _ (c k).1
  have key : k - ∑ a, (∑ b, θ a b * ψ f (hb b)) • hb a ∈ Fil A := by
    letI : Algebra (DualNumber K) K := (TrivSqZeroExt.fstHom K K K).toRingHom.toAlgebra
    obtain ⟨-, hF⟩ := P.2.2.1 (DualNumber K) A' g hA' hg' K A i h
    rw [Fil, hF, Submodule.mem_dualAnnihilator]
    intro x hx
    refine (Submodule.span_le (p := LinearMap.ker (k - ∑ a, (∑ b, θ a b * ψ f (hb b)) • hb a))).2
      (fun x hx ↦ ?_) hx
    obtain ⟨⟨x, hx'⟩, hx, rfl⟩ := hx
    have hx0 := hx
    change x ∈ F1 _ at hx
    rw [hodgeFiltration_eq_range] at hx
    obtain ⟨ω', rfl⟩ := hx
    obtain ⟨b, hbe⟩ := GlobalTheory.T.deformation_class_pullback_eq_constant_add_eps P K A A' i h g hA' hg' ⟨_, hx'⟩
    obtain ⟨zb, hzb⟩ := H1.mk_surjective _ b.1
    let ω₀ := (fibMor h).isMor.pullForm ω'
    have hω₀ : Form.cl _ ω₀ ∈ primDR A := (fibMor h).pullback_mem_primitive hx'
    obtain ⟨J, V, τ, hV, hτ, hrep⟩ := exists_isRep_eps h hA L u θ hu H ω' zb (by
      rw [hzb]; exact congrArg Subtype.val hbe)
    have hch' : IsChern (dp0 K) (A.hom ≫ 𝟙 (Sp K)) L (∑ k, cup _ (H1.mk _ (z k)) (Form.cl _ (ω k))) := by
      simpa only [hz] using hch
    have hr := fun a ↦ GlobalTheory.T.isCechRepresentative_chernClass_tangentValue K A hA L hL I z ω hch' (u a) (hu a) J V τ hτ
    have hsum := hrep.add (IsRep.sum Finset.univ fun a _ ↦ IsRep.sum Finset.univ fun b _ ↦
      (hr b).smul (θ a b * tanVal (u a) ω₀))
    have hF1 := GlobalTheory.T.crystallineClass_mem_hodgeFiltration_of_cechRep_zero K _ _ J _ hV _ (hsum.congr (F' := 0) fun j j' Q _ _ ↦ by
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, Algebra.smul_def, map_mul,
        Finset.sum_mul]
      rw [neg_add_eq_zero]
      exact Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ mul_right_comm _ _ _)
    have hmem : b + ∑ a, ∑ b, (θ a b * tanVal (u a) ω₀) • ∑ k, tanVal (u b) (ω k) • c k ∈ PrimitiveSubmodule A := by
      refine Submodule.mem_comap.2 ?_
      simp only [map_add, map_sum, map_smul, hz, hzb] at hF1
      simp only [map_add, map_sum, map_smul]
      exact hF1
    have e1 := (Submodule.mem_dualAnnihilator _).1 hf _ hmem
    have e2 : d ((liftMor (epsDP K) h).pull ⟨_, hx'⟩) = 0 :=
      (Submodule.mem_dualAnnihilator _).1 hd _ hx0
    rw [hbe, map_add, map_smul, hdk, hdk] at e2
    have e4 : ∀ a, hb a ⟨_, hω₀⟩ = tanVal (u a) ω₀ := fun a ↦ (hhb a).2 ω₀ hω₀
    have e5 : ∀ b, ψ f (hb b) = ∑ k, f (c k) * tanVal (u b) (ω k) := fun b ↦
      (hψf f hf (hb b)).trans (Finset.sum_congr rfl fun k _ ↦ congrArg (f (c k) * ·) ((hhb b).2 (ω k) (hω k)))
    exact eval_eq_zero f k b ⟨_, hω₀⟩ c θ hb _ _ _ e4 e5 e1 e2
  refine ⟨k, ⟨d, hd, hdk⟩, ?_⟩
  have := (FlagTan.isLieImage_lieComb (fun a ↦ ∑ b, θ a b * ψ f (hb b)) hhb).add (isLieImage_one_iff.2 key)
  rwa [add_sub_cancel, _root_.mul_one] at this

end GlobalTheory.CechKS

end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

theorem GlobalTheory.CechKS.exists_const_isKSValue : GlobalTheory.CovTop.Hypotheses₂ → ∃ s : ℚ, s ≠ 0 ∧ ∀ (K : Type) [Field K] [CharZero K] (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (i : A.left ⟶ A'.left) (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → IsAbelianScheme A' → SmoothOfRelativeDimension g A'.hom → ∀ (L : LB A.left), L.IsLB → ∀ ψ : LinearMap.BilinForm K (GlobalTheory.DeRham.HdR A), GlobalTheory.DeRham.IsPolForm (GlobalTheory.Cris.dp0 K) (𝟙 _) A L ψ → ∀ (n : ℕ) (u : Fin n → (epsR K ⟶ A)) (θ : Matrix (Fin n) (Fin n) K), (∀ a, IsTangent (u a)) → GlobalTheory.CechKS.IsCechKS A A' i L u θ → ∀ (hb : Fin n → GlobalTheory.DeRham.HdR A), (∀ b, GlobalTheory.DeRham.IsLieImage (hb b) (u b)) → ∀ f ∈ GlobalTheory.DeRham.Fil A, ∀ w : epsR K ⟶ A, IsLieComb (fun a => (s : K) * ∑ b, θ a b * ψ f (hb b)) u w → GlobalTheory.DeRham.IsKSValue h f w := by
  intro P
  refine ⟨1, one_ne_zero, ?_⟩
  intro K _ _ A _ A' _ i h g hA hg hA' hg' L hL ψ hψ n u θ hu H hb hhb f hf w hw
  obtain ⟨u', hu', rfl⟩ := hw
  have := GlobalTheory.CechKS.isKSValue_of_isCechKS P.p5 h hA hg hA' hg' L hL ψ hψ u θ hu H hb hhb hf
  convert this using 1
  rw [GlobalTheory.FlagTan.lieComb]
  congr 2
  funext a
  refine Over.OverMorphism.ext ((hu' a).trans ?_)
  simp only [Rat.cast_one, one_mul]
  rfl

end
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeOneTermEqConstMulPsiMulTheta
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.IntTerm

theorem term_eq_const_psi_theta : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegPre V) (θ : D.SecB 1 0), IntTerm.IsTheta D θ → ∀ s : Fam D (FractionRing V) 1, ∃ κ : FractionRing V, ∀ (g : GtPt D (𝟙_ (Over (Sp V)))) (g' : GtPtF D (FractionRing V)) (w : Frm D (FractionRing V) 1 g'.b) (l : FractionRing V), GtPt.IsPullF (FractionRing V) (toUnit (TF (R := V) (FractionRing V))).left g g' → w.IsGen → IntTerm.IntFrm D g.b w l → ∀ (mu : D.X) (r : V), Formalism.L2.Pj.PsiCoord D mu r → ∃ a : V, l * coef s g' w mu = κ * algebraMap V (FractionRing V) (r * a) ∧ (IntTerm.UnitAt D θ (D.c mu * g.b) → IsUnit a) := by
  intro V _ _ _ D θ hθ s
  obtain ⟨c₀, hc₀, hc⟩ := GlobalTheory.T.psi_zero_mul_rigidification_constant_ne_zero V D
  obtain ⟨κ₀, hκ⟩ := GlobalTheory.T.degreeOneFamily_term_eq_psi_thetaValue_character V D θ hθ s
  refine ⟨κ₀ / c₀, fun g g' w l hpull hw hint mu r hr => ?_⟩
  obtain ⟨gam, hgam, vgam⟩ := GlobalTheory.T.exists_integralGenerator_of_psiCoordinate V D mu r hr
  obtain ⟨a, ha, hu⟩ := GlobalTheory.T.exists_base_element_theta_term_integralPoint V D θ g g' w l hpull hint mu gam hgam
  refine ⟨a, ?_, fun h => GlobalTheory.T.isUnit_of_isUnit_constant_closedPoint_localRing V a (hu h)⟩
  obtain ⟨z⟩ := CoefBasic.exists_pt (R := V) (F := FractionRing V)
  obtain ⟨J, hJ⟩ := CoefBasic.exists_good' D.P.isLB z
  have e₁ := hκ g' w hw mu z J hJ
  have e₂ := hc z J hJ
  have e₃ := vgam z J hJ
  have e₄ := ha z J hJ
  rw [_root_.mul_assoc (GlobalTheory.UT.cst _ z _), mul_comm (rigV D _ z J).val, e₂, e₃] at e₁
  have e₅ : GlobalTheory.UT.cst (FractionRing V) z (l * coef s g' w mu * c₀) =
      GlobalTheory.UT.cst (FractionRing V) z (κ₀ * (algebraMap V (FractionRing V) r * algebraMap V (FractionRing V) a)) := by
    simp only [CoefBasic.cst_eq, map_mul] at e₁ e₄ ⊢
    rw [← e₄]
    linear_combination CoefBasic.cstH z l * e₁
  have e₆ := CoefBasic.cstH_inj z ((CoefBasic.cst_eq _ _).symm.trans (e₅.trans (CoefBasic.cst_eq _ _)))
  rw [map_mul]
  field_simp
  linear_combination e₆

end GlobalTheory.Poinc.IntTerm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelDbarAdditiveComplexLinearOne
section
set_option autoImplicit false

open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

namespace GlobalTheory.CxForm.GlobLin

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

theorem loc_add (α β : A.Fld) (i : A.ι) : A.loc (α + β) i = fun v => A.loc α i v + A.loc β i v := by
  funext v
  unfold HolAtlas.loc
  split_ifs
  exacts [rfl, (add_zero _).symm]

theorem loc_smul (c : ℂ) (α : A.Fld) (i : A.ι) : A.loc (c • α) i = fun v => c • A.loc α i v := by
  funext v
  unfold HolAtlas.loc
  split_ifs
  exacts [rfl, (smul_zero _).symm]

theorem target_mem_nhds (x : A.Pt) : (A.e x.1.1).target ∈ 𝓝 x.crd :=
  (A.e x.1.1).open_target.mem_nhds (x.ch.map_source x.2)

theorem differentiableAt_coef {α : A.Fld} (h : A.IsForm α) (x : A.Pt) (S : Finset (Fin (n + n))) :
    DifferentiableAt ℝ (fun v => (bas n).repr (A.loc α x.1.1 v) S) x.crd :=
  ((h.smooth x.1.1 S).contDiffAt (target_mem_nhds A x)).differentiableAt (by simp)

theorem loc_one_eventuallyEq (x : A.Pt) : A.loc 1 x.1.1 =ᶠ[𝓝 x.crd] fun _ => 1 :=
  Filter.eventually_of_mem (target_mem_nhds A x) fun v hv => by
    rw [HolAtlas.loc, dif_pos hv]
    rfl

end GlobalTheory.CxForm.GlobLin

open GlobalTheory.CxForm.GlobLin in

theorem GlobalTheory.CxForm.HolAtlas.del_dbar_linear : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n),
    (A.del 1 = 0 ∧ A.dbar 1 = 0) ∧
    ∀ (c : ℂ) (α β : A.Fld), A.IsForm α → A.IsForm β →
      A.del (α + β) = A.del α + A.del β ∧ A.dbar (α + β) = A.dbar α + A.dbar β ∧
      A.del (c • α) = c • A.del α ∧ A.dbar (c • α) = c • A.dbar α := by
  intro M _ n A
  refine ⟨⟨funext fun x => ?_, funext fun x => ?_⟩, fun c α β hα hβ =>
    ⟨funext fun x => ?_, funext fun x => ?_, funext fun x => ?_, funext fun x => ?_⟩⟩
  all_goals obtain ⟨hadd, hsmul, -, hgerm, hconst⟩ := GlobalTheory.T.delOperatorAt_dbarOperatorAt_linear_local n x.crd
  · exact (hgerm _ _ (loc_one_eventuallyEq A x)).1.trans (hconst 1).1
  · exact (hgerm _ _ (loc_one_eventuallyEq A x)).2.trans (hconst 1).2
  · rw [HolAtlas.del, loc_add]
    exact (hadd _ _ (differentiableAt_coef A hα x) (differentiableAt_coef A hβ x)).1
  · rw [HolAtlas.dbar, loc_add]
    exact (hadd _ _ (differentiableAt_coef A hα x) (differentiableAt_coef A hβ x)).2
  · rw [HolAtlas.del, loc_smul]
    exact (hsmul _ c (differentiableAt_coef A hα x)).1
  · rw [HolAtlas.dbar, loc_smul]
    exact (hsmul _ c (differentiableAt_coef A hα x)).2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetInvariantDiffIsoHodgeLineBundleStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.detInvariantDiff_iso_hodgeLineBundle : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), (GlobalTheory.FlagMod.detOm Y).IsLB → LBIso (GlobalTheory.FlagMod.detOm Y) (GlobalTheory.SiegelTor.hodge Y.t.G (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))) := by
  first | exact @GlobalTheory.UMin.lbIso_detOm_hodge | exact GlobalTheory.UMin.lbIso_detOm_hodge | (intros; apply GlobalTheory.UMin.lbIso_detOm_hodge <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfNormProdAevalEqStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_norm_prod_aeval_eq' : ∀ (l : ℕ) [Fact l.Prime] (P Q : Polynomial ℚ_[l]), P.Monic → Q.Monic → P.natDegree = Q.natDegree → (∀ F : Polynomial ℤ, ‖((P.aroots (PadicAlgCl l)).map (fun a => Polynomial.aeval a F)).prod‖ = ‖((Q.aroots (PadicAlgCl l)).map (fun a => Polynomial.aeval a F)).prod‖) → P = Q := by
  first | exact @GlobalTheory.PadicRootNorm.eq_of_norm_prod_aeval_eq | exact GlobalTheory.PadicRootNorm.eq_of_norm_prod_aeval_eq | (intros; apply GlobalTheory.PadicRootNorm.eq_of_norm_prod_aeval_eq; all_goals assumption)
end

