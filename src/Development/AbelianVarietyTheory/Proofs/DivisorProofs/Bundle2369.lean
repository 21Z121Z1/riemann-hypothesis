import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2204
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2365
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2190
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnchoredWeightIndefiniteLiftGaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2310
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2355
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1088
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLocalSubringGenericPoint
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnchorBoundStatement
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovTop.AnchorRd

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem anchor_eq (P : ParameterChoice' D L) (t : D.what₂.Tau) (τ : Psi p.T.Q.H) (hτ : τ.1 = DV.tauEmb D t) :
    (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℤ) =
      ⌊Formalism.L2.NTheta.lamAt (D.hc t) (D.R.k - 2) + (D.hc t).e i -
        (((D.R.sigW ((i : ℕ) + 1)).1 : ℚ) - ((D.R.k - 2 : ℕ) + 1)) - ((D.R.t : ℚ) + 1) / 2⌋ +
        (((p.κ i).n / 2 : ℕ) : ℤ) := by
  have hk := D.R.m_add_three_le_k
  have hmain := GlobalTheory.CovTop.WtRead.main D p.T p.fw.laws i (p.κ i)
  have hsw : (D.R.sigW ((i : ℕ) + 1)).1 = D.R.k + (i : ℕ) := by simp only [Ranks.sigW]; omega
  have hpq : (dat p i).p = (D.R.sigW ((i : ℕ) + 1)).1 := hmain.1
  have hlt : D.R.k - 1 - 1 < (dat p i).p + (dat p i).q := by omega
  have hj : D.R.k - 2 < (D.R.sigW ((i : ℕ) + 1)).1 := by omega
  obtain ⟨-, hnn⟩ := GlobalTheory.RecGaps.bigEnt p P i t (D.R.k - 2) hj
  unfold anchor
  rw [dif_pos hlt, GlobalTheory.CovTop.WtRead.laOf_big D p.T p.fw.laws i (p.κ i) t τ hτ _ ⟨D.R.k - 2, hj⟩ (by simp; omega),
    (p.fw.kap i t).1 ⟨D.R.k - 2, hj⟩]
  rw [GlobalTheory.RecGaps.sig_Wc]
  unfold aPl
  rw [if_pos hj, Int.toNat_of_nonneg hnn]

theorem abs_anchor_sub_le (P : ParameterChoice' D L) (t : D.what₂.Tau) (τ : Psi p.T.Q.H) (hτ : τ.1 = DV.tauEmb D t) :
    |((anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℤ) : ℝ) - (((D.hc t).e i : ℚ) : ℝ)| ≤
      L.Sc + D.R.nV + D.R.m + D.R.t + 2 := by
  have hk := D.R.m_add_three_le_k
  have ha := anchor_eq p i P t τ hτ
  have hn : (p.κ i).n = D.R.nV := (p.fw.kap i t).2.2
  have hv : Formalism.L2.NTheta.lamAt (D.hc t) (D.R.k - 2) = (D.hc t).v ⟨D.R.k - 2, by omega⟩ := by
    unfold Formalism.L2.NTheta.lamAt; rw [dif_pos (by omega)]
  have hc := L.cloud_v t ⟨D.R.k - 2, by omega⟩
  have hsw : ((D.R.sigW ((i : ℕ) + 1)).1 : ℚ) - ((D.R.k - 2 : ℕ) + 1) = (i : ℚ) + 1 := by
    rw [show (D.R.sigW ((i : ℕ) + 1)).1 = D.R.k + (i : ℕ) by simp only [Ranks.sigW]; omega,
      Nat.cast_sub (by omega : 2 ≤ D.R.k)]
    push_cast; ring
  rw [hsw, hv] at ha
  rw [ha, hn]
  have h1 := Int.floor_le ((D.hc t).v ⟨D.R.k - 2, by omega⟩ + (D.hc t).e i - ((i : ℚ) + 1) - ((D.R.t : ℚ) + 1) / 2)
  have h2 := Int.lt_floor_add_one ((D.hc t).v ⟨D.R.k - 2, by omega⟩ + (D.hc t).e i - ((i : ℚ) + 1) - ((D.R.t : ℚ) + 1) / 2)
  have h1' : ((⌊(D.hc t).v ⟨D.R.k - 2, by omega⟩ + (D.hc t).e i - ((i : ℚ) + 1) - ((D.R.t : ℚ) + 1) / 2⌋ : ℤ) : ℝ) ≤
      (((D.hc t).v ⟨D.R.k - 2, by omega⟩ + (D.hc t).e i - ((i : ℚ) + 1) - ((D.R.t : ℚ) + 1) / 2 : ℚ) : ℝ) := by
    exact_mod_cast h1
  have h2' : (((D.hc t).v ⟨D.R.k - 2, by omega⟩ + (D.hc t).e i - ((i : ℚ) + 1) - ((D.R.t : ℚ) + 1) / 2 : ℚ) : ℝ) <
      ((⌊(D.hc t).v ⟨D.R.k - 2, by omega⟩ + (D.hc t).e i - ((i : ℚ) + 1) - ((D.R.t : ℚ) + 1) / 2⌋ : ℤ) : ℝ) + 1 := by
    exact_mod_cast h2
  have hnv : ((D.R.nV / 2 : ℕ) : ℝ) ≤ D.R.nV := by exact_mod_cast Nat.div_le_self _ _
  have hnv0 : (0 : ℝ) ≤ ((D.R.nV / 2 : ℕ) : ℝ) := by positivity
  have hi : ((i : ℕ) : ℝ) + 1 ≤ D.R.m := by exact_mod_cast i.2
  have ht : (0 : ℝ) ≤ D.R.t := by positivity
  rw [Int.cast_add, Int.cast_natCast]
  push_cast at h1' h2'
  rw [abs_le]
  constructor <;> linarith [hc.1, hc.2]

set_option maxHeartbeats 1000000 in

theorem anchorAt_of {PP A : ℝ} (P : ParameterChoice' D L) (hw : WtNum p i PP) (hh : HostNum D L PP A 1) : AnchorAt p i 100 := by
  have hk := D.R.m_add_three_le_k
  have hm2 := D.R.two_le_m
  obtain ⟨hp, hq, hcard, -, -, E, hE, -⟩ := GlobalTheory.CovTop.WtRead.main D p.T p.fw.laws i (p.κ i)
  have hL10 := hh.big.2.1
  have hLx := hh.big.2.2.1
  have hll := hh.big.2.2.2
  have hxA : 1 ≤ L.sc.x ^ A := Real.one_le_rpow (by linarith) (by linarith [hh.poly.1])
  have hb : L.sc.x ^ A ≤ L.sc.b := by simpa using hh.room
  have hb1 : 1 ≤ L.sc.b := hxA.trans hb
  have hf : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hh.f8
  have hm : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm2
  have hunit := hw.unit
  have hom := hw.om
  have hanc : ∀ τ, |((anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℤ) : ℝ)| ≤ 4 * L.sc.b := by
    intro τ
    unfold anchor
    split_ifs with h
    · exact hw.up τ _
    · simp only [Int.cast_zero, abs_zero]; linarith

  have hpr : ((dat p i).p : ℝ) + (dat p i).q = D.R.r := by
    rw [hp, hq]; exact_mod_cast GlobalTheory.CovTop.WtRead.sigW_add D i
  have hp0 : (0 : ℝ) ≤ (dat p i).p := by positivity
  have hq0 : (0 : ℝ) ≤ (dat p i).q := by positivity
  have hcr : |((dat p i).p : ℝ) - (dat p i).q| ≤ D.R.r := abs_le.2 ⟨by linarith, by linarith⟩
  have hqm : ((dat p i).q : ℝ) ≤ D.R.m := by
    rw [hq]; exact_mod_cast (by simp only [Ranks.sigW]; omega : (D.R.sigW ((i : ℕ) + 1)).2 ≤ D.R.m)
  have hc_eq : ((D.R.k : ℝ) + (((i : ℕ) + 1 : ℕ) : ℝ) - 1) - ((D.R.m : ℝ) - (((i : ℕ) + 1 : ℕ) : ℝ)) =
      ((dat p i).p : ℝ) - (dat p i).q := by
    rw [hp, hq]
    simp only [Ranks.sigW]
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast; ring

  have hmainS : mainT p i = ∑ t : D.what₂.Tau, (((dat p i).p : ℝ) - (dat p i).q) * (((D.hc t).e i : ℚ) : ℝ) *
      (ofRecord D L p.Del p.h0).logOm := by
    show ∑ ρ : RPl D.R, (((D.R.k : ℝ) + (((i : ℕ) + 1 : ℕ) : ℝ) - 1) - ((D.R.m : ℝ) - (((i : ℕ) + 1 : ℕ) : ℝ))) *
      (ofRecord D L p.Del p.h0).w ((i : ℕ) + 1) ρ * (ofRecord D L p.Del p.h0).logOm = _
    rw [hc_eq, ← (tauPl_bijective D).sum_comp (fun t => (((dat p i).p : ℝ) - (dat p i).q) * (((D.hc t).e i : ℚ) : ℝ) *
      (ofRecord D L p.Del p.h0).logOm)]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    congr 2
    simp only [NumDatum.w, NumDatum.eQ]
    rw [dif_pos ⟨by omega, by omega⟩]
    congr 3
  have hancS : ∑ τ : Psi p.T.Q.H, (((dat p i).p : ℝ) - (dat p i).q) *
      ((anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℤ) : ℝ) * (ofRecord D L p.Del p.h0).logOm =
      ∑ t : D.what₂.Tau, (((dat p i).p : ℝ) - (dat p i).q) *
        ((anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) (E t) : ℤ) : ℝ) * (ofRecord D L p.Del p.h0).logOm :=
    (Equiv.sum_comp E (fun τ => (((dat p i).p : ℝ) - (dat p i).q) *
      ((anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℤ) : ℝ) * (ofRecord D L p.Del p.h0).logOm)).symm
  have hcardT : (Fintype.card D.what₂.Tau : ℝ) = D.R.f := by exact_mod_cast Formalism.MainNotions.Lnk.card_Tau D

  have hne : Nonempty D.what₂.Tau := Fintype.card_pos_iff.1 (by rw [Formalism.MainNotions.Lnk.card_Tau]; have := hh.f8; omega)
  obtain ⟨t0⟩ := hne
  have hw'' : L.sc.w'' D.R.n ≤ 8 * L.sc.b := by
    have a1 := hw.low (E t0)
    have a2 := (abs_le.1 (hanc (E t0))).2
    linarith
  have hr2k : (D.R.r : ℝ) ≤ 2 * D.R.k := by exact_mod_cast (by unfold Ranks.r; omega : D.R.r ≤ 2 * D.R.k)
  have hSc0 : 0 ≤ L.Sc := L.Sc_pos.le
  have hrS : (D.R.r : ℝ) * L.Sc ≤ 16 * L.sc.b := by
    have a1 := P.kS_le
    have a2 : (D.R.r : ℝ) * L.Sc ≤ 2 * D.R.k * L.Sc := mul_le_mul_of_nonneg_right hr2k hSc0
    linarith
  have hnV : (D.R.nV : ℝ) = D.R.r + D.R.t := by unfold Ranks.nV; push_cast; ring
  have hmr : (D.R.m : ℝ) ≤ D.R.r := by exact_mod_cast (by unfold Ranks.r; omega : D.R.m ≤ D.R.r)
  have ht0 : (0 : ℝ) ≤ D.R.t := by positivity
  have hrnV : (D.R.r : ℝ) * D.R.nV ≤ L.sc.b := by
    have a1 := hh.poly.2.2
    have e0 : (0 : ℝ) ≤ (D.R.r : ℝ) * D.R.nV := by positivity
    have a2 : (D.R.r : ℝ) * D.R.nV * 1 ≤ (D.R.r : ℝ) * D.R.nV * (D.R.f * L.sc.L) :=
      mul_le_mul_of_nonneg_left (one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)) e0
    calc (D.R.r : ℝ) * D.R.nV = (D.R.r : ℝ) * D.R.nV * 1 := by ring
      _ ≤ (D.R.r : ℝ) * D.R.nV * (D.R.f * L.sc.L) := a2
      _ = D.R.f * D.R.r * D.R.nV * L.sc.L := by ring
      _ ≤ L.sc.x ^ A := a1
      _ ≤ L.sc.b := hb
  have hB : (D.R.r : ℝ) * (L.Sc + D.R.nV + D.R.m + D.R.t + 2) ≤ 20 * L.sc.b := by
    have e1 : (D.R.r : ℝ) * (D.R.nV + D.R.m + D.R.t + 2) ≤ 4 * ((D.R.r : ℝ) * D.R.nV) := by
      calc (D.R.r : ℝ) * (D.R.nV + D.R.m + D.R.t + 2) ≤ (D.R.r : ℝ) * (4 * D.R.nV) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = 4 * ((D.R.r : ℝ) * D.R.nV) := by ring
    calc (D.R.r : ℝ) * (L.Sc + D.R.nV + D.R.m + D.R.t + 2) =
          (D.R.r : ℝ) * L.Sc + (D.R.r : ℝ) * (D.R.nV + D.R.m + D.R.t + 2) := by ring
      _ ≤ 16 * L.sc.b + 4 * L.sc.b := add_le_add hrS (by linarith)
      _ = 20 * L.sc.b := by ring
  refine ⟨?_, ?_, hh.poly.2.2.trans hb⟩
  · rw [hmainS, hancS, ← Finset.sum_sub_distrib]
    have hterm : ∀ t : D.what₂.Tau, |(((dat p i).p : ℝ) - (dat p i).q) * (((D.hc t).e i : ℚ) : ℝ) *
        (ofRecord D L p.Del p.h0).logOm - (((dat p i).p : ℝ) - (dat p i).q) *
        ((anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) (E t) : ℤ) : ℝ) * (ofRecord D L p.Del p.h0).logOm| ≤
        (D.R.r : ℝ) * (L.Sc + D.R.nV + D.R.m + D.R.t + 2) * (3 * L.sc.L) := by
      intro t
      have a1 := abs_anchor_sub_le p i P t (E t) (hE t)
      rw [show (((dat p i).p : ℝ) - (dat p i).q) * (((D.hc t).e i : ℚ) : ℝ) * (ofRecord D L p.Del p.h0).logOm -
          (((dat p i).p : ℝ) - (dat p i).q) * ((anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) (E t) : ℤ) : ℝ) *
          (ofRecord D L p.Del p.h0).logOm = -((((dat p i).p : ℝ) - (dat p i).q) *
          (((anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) (E t) : ℤ) : ℝ) - (((D.hc t).e i : ℚ) : ℝ)) *
          (ofRecord D L p.Del p.h0).logOm) by ring, abs_neg, abs_mul, abs_mul]
      exact mul_le_mul (mul_le_mul hcr a1 (abs_nonneg _) (by positivity)) hom (abs_nonneg _) (by positivity)
    calc _ ≤ ∑ t : D.what₂.Tau, (D.R.r : ℝ) * (L.Sc + D.R.nV + D.R.m + D.R.t + 2) * (3 * L.sc.L) :=
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun t _ => hterm t)
      _ = D.R.f * ((D.R.r : ℝ) * (L.Sc + D.R.nV + D.R.m + D.R.t + 2)) * (3 * L.sc.L) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcardT]; ring
      _ ≤ D.R.f * (20 * L.sc.b) * (3 * L.sc.L) := by gcongr
      _ ≤ 100 * unitE p := by
          rw [hunit]
          have e1 : (0 : ℝ) ≤ D.R.f * L.sc.b * L.sc.L := by positivity
          have e2 : D.R.f * L.sc.b * L.sc.L * 1 ≤ D.R.f * L.sc.b * L.sc.L * (D.R.m * Real.log (Real.log L.sc.x)) :=
            mul_le_mul_of_nonneg_left (one_le_mul_of_one_le_of_one_le (by linarith) hll) e1
          have e3 : (D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.L * Real.log (Real.log L.sc.x) =
              D.R.f * L.sc.b * L.sc.L * (D.R.m * Real.log (Real.log L.sc.x)) := by ring
          have e4 : (D.R.f : ℝ) * (20 * L.sc.b) * (3 * L.sc.L) = 60 * (D.R.f * L.sc.b * L.sc.L * 1) := by ring
          rw [e3, e4]
          linarith
  · have hsum : ∑ τ : Psi p.T.Q.H, |((anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℤ) : ℝ)| ≤
        D.R.f * (4 * L.sc.b) := by
      calc _ ≤ ∑ τ : Psi p.T.Q.H, 4 * L.sc.b := Finset.sum_le_sum fun τ _ => hanc τ
        _ = _ := by rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, hcard, nsmul_eq_mul]
    calc (∑ τ : Psi p.T.Q.H, |((anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℤ) : ℝ)|) *
          ((dat p i).q : ℝ) * L.sc.L ≤ D.R.f * (4 * L.sc.b) * D.R.m * L.sc.L := by gcongr
      _ ≤ 100 * unitE p := by
          rw [hunit]
          have e1 : (0 : ℝ) ≤ D.R.f * L.sc.b * D.R.m * L.sc.L := by positivity
          have e2 : D.R.f * L.sc.b * D.R.m * L.sc.L * 1 ≤ D.R.f * L.sc.b * D.R.m * L.sc.L * Real.log (Real.log L.sc.x) :=
            mul_le_mul_of_nonneg_left hll e1
          have e3 : (D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.L * Real.log (Real.log L.sc.x) =
              D.R.f * L.sc.b * D.R.m * L.sc.L * Real.log (Real.log L.sc.x) := by ring
          have e4 : (D.R.f : ℝ) * (4 * L.sc.b) * D.R.m * L.sc.L = 4 * (D.R.f * L.sc.b * D.R.m * L.sc.L * 1) := by ring
          rw [e3, e4]
          linarith

end GlobalTheory.CovTop.AnchorRd

namespace GlobalTheory.CovTop

theorem anchor_holds : Anchor := by
  refine Closed.imp (Closed.and WtShape.wtN (Sizes.hostN 1)) ?_
  rintro eps Fm CH - ⟨⟨C1, -, hW⟩, ⟨A, -, hH⟩⟩
  obtain ⟨x0, h⟩ := EvTied.and hW hH
  exact ⟨100, by norm_num, x0, fun x hx hle ι p hp i =>
    AnchorRd.anchorAt_of p i (Fm.params x hx ι) ((h x hx hle ι p hp).1 i) ((h x hx hle ι p hp).2 i)⟩

end GlobalTheory.CovTop
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanExistenceOfComplexIsomorphicFieldStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanExistence_of_complex_isomorphic_field : ∀ κ : Rule, Funct κ → Arch κ → ArchF κ := by
  first | exact @GlobalTheory.MBLow.archF_of_arch | exact GlobalTheory.MBLow.archF_of_arch | (intros; apply GlobalTheory.MBLow.archF_of_arch <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticHeightTensorAdditiveOnCurves
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic

namespace GlobalTheory.HtTensCurve

theorem topSelf_one_tens {κ : Type} [Field κ] {Z : Scheme.{0}} [Algebra κ Γ(Z, ⊤)]
    (hp : IsProjOver (strHom κ Z)) (hd : topologicalKrullDim Z = 1) {A B : LB Z} (hA : A.IsLB)
    (hB : B.IsLB) : topSelfIntersection κ (CechPic.tens A B) 1 = topSelfIntersection κ A 1 + topSelfIntersection κ B 1 := by
  have HD := diffVanish_chiPic_of_isProjOver (f := strHom κ Z) (algebraMap_eq_strHom κ Z)
    (structureModule Z) hp (d := 1) (by rw [QCoh.suppDim_structureModule, hd]; rfl)
  have e := HD.interNum_update_tens (ι := Fin 1) (L := fun _ => A) (by simp) (fun _ => hA) 0 hA hB
  have hu (N : LB Z) : Function.update (fun _ : Fin 1 => A) 0 N = fun _ => N :=
    funext fun j => by fin_cases j; simp
  simpa only [topSelf_def, hu] using e

theorem topSelf_one_pull_tens {κ : Type} [Field κ] {X Z : Scheme.{0}} [Algebra κ Γ(Z, ⊤)]
    (hp : IsProjOver (strHom κ Z)) (hd : topologicalKrullDim Z = 1) (i : Z ⟶ X) {A B : LB X}
    (hA : A.IsLB) (hB : B.IsLB) :
    topSelfIntersection κ ((CechPic.tens A B).pull i) 1 = topSelfIntersection κ (A.pull i) 1 + topSelfIntersection κ (B.pull i) 1 := by
  have hA' := LB.isLB_pull hA i
  have hB' := LB.isLB_pull hB i
  rw [← topSelf_one_tens hp hd hA' hB', topSelf_def, topSelf_def]
  refine interNum_congr_cls κ _ (fun _ => LB.isLB_pull (isLB_tens hA hB) i)
    (fun _ => isLB_tens hA' hB') fun _ => ?_
  rw [cls_pull (isLB_tens hA hB) i, cls_tens hA hB, cls_tens hA' hB', cls_pull hA i, cls_pull hB i,
    map_add]

end GlobalTheory.HtTensCurve

namespace GlobalTheory.HtTensCurve

theorem height_tens_curve : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    {D : ℕ}, GlobalTheory.IsArithVar p D → ∀ (L M : GlobalTheory.HermLB p) (h h' h'' : X → ℝ), L.IsArithHeight h →
    M.IsArithHeight h' → (L.tens M).IsArithHeight h'' → ∀ (Z : Scheme.{0}) (i : Z ⟶ X)
    [IsClosedImmersion i] [IsIntegral Z], topologicalKrullDim Z = 1 →
    h'' (i (genericPoint Z)) = h (i (genericPoint Z)) + h' (i (genericPoint Z)) := by
  intro k _ X _ p D hX L M h h' h'' H H' H'' Z i _ _ hd
  have := hX.isNoetherian_sub i
  rcases hX.vertical_or_horizontal i with ⟨ℓ, _, ⟨_⟩⟩ | ⟨hc, -⟩
  · have : Module.Finite ℤ k := hX.finite
    have : IsProper p := (isProper_and_exists_isAmpleLB_of_isProjOver hX.isProjOver).1
    have hproj : IsProjOver (strHom (ZMod ℓ) Z) := by
      have : IsFinite (spMap (Int.castRingHom k)) := by
        rw [spMap, IsFinite.SpecMap_iff]
        exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
      have e : strHom (ZMod ℓ) Z ≫ spMap (Int.castRingHom (ZMod ℓ)) =
          i ≫ p ≫ spMap (Int.castRingHom k) := specZIsTerminal.hom_ext _ _
      have : IsProper (strHom (ZMod ℓ) Z ≫ spMap (Int.castRingHom (ZMod ℓ))) := by
        rw [e]; infer_instance
      have : IsProper (strHom (ZMod ℓ) Z) := IsProper.of_comp _ (spMap (Int.castRingHom (ZMod ℓ)))
      exact ProperCurve.isProjOver_of_isProper _ hd
    rw [H''.vertical Z i (ZMod ℓ) 1 hd, H.vertical Z i (ZMod ℓ) 1 hd, H'.vertical Z i (ZMod ℓ) 1 hd,
      ← add_mul]
    congr 1
    exact_mod_cast topSelf_one_pull_tens hproj hd i L.isLB M.isLB
  · exact PtHtComb.height_tens hX H H' H'' (HtSelfInter.isAlgPt_genericPoint i hc hd)

end GlobalTheory.HtTensCurve
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSigmaMapBasicProperties
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem Obs.sig_basic : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (B B₀ : Type) [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] (p : B →+* B₀) (hs : SemiHom π p) (hp : Function.Surjective p) (hker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) (σ : R₁ ⊗[R₀] B₀ →+ B), α.IsSig p σ → (∀ y, σ y ∈ I.map (algebraMap R B)) ∧ (∀ b y, σ ((1 ⊗ₜ p b) * y) = b * σ y) ∧ (∀ b₀ : B₀, σ (1 ⊗ₜ b₀) = 0) ∧ ∀ x ∈ I.map (algebraMap R B), ∃ y, α.KerQ y ∧ σ y = x := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α B B₀ _ _ _ _ p hs hp hker σ hσ
  have h2 : ∀ b y, σ ((1 ⊗ₜ p b) * y) = b * σ y := by
    intro b y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul y' b₀ =>
      obtain ⟨b', rfl⟩ := hp b₀
      rw [Algebra.TensorProduct.tmul_mul_tmul, _root_.one_mul, ← map_mul, hσ, hσ, mul_smul_comm]
    | add x y hx hy => rw [mul_add, map_add, map_add, hx, hy, mul_add]
  refine ⟨?_, h2, ?_, ?_⟩
  · intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul y' b₀ =>
      obtain ⟨b', rfl⟩ := hp b₀
      rw [hσ, Algebra.smul_def]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (α.mem y'))
    | add x y hx hy => rw [map_add]; exact Ideal.add_mem _ hx hy
  · intro b₀
    obtain ⟨b', rfl⟩ := hp b₀
    rw [hσ, α.one, zero_smul]
  · intro x hx
    rw [Ideal.map, Ideal.span] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      obtain ⟨y, hy0, hyk⟩ := α.surj i hi
      refine ⟨y ⊗ₜ 1, ?_, ?_⟩
      · simp [Obs.Aug.KerQ, hy0]
      · rw [← map_one p, hσ, hyk, Algebra.smul_def, _root_.mul_one]
    | zero => exact ⟨0, by simp [Obs.Aug.KerQ], by simp⟩
    | add x x' _ _ hx hx' =>
      obtain ⟨y, hy, rfl⟩ := hx
      obtain ⟨y', hy', rfl⟩ := hx'
      refine ⟨y + y', ?_, by rw [map_add]⟩
      simp only [Obs.Aug.KerQ, map_add] at *; rw [hy, hy', add_zero]
    | smul b x _ hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      refine ⟨(1 ⊗ₜ p b) * y, ?_, by rw [h2, smul_eq_mul]⟩
      simp only [Obs.Aug.KerQ, map_mul] at *; rw [hy, mul_zero]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSigmaMapInjectiveOfFlat
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Obs.SigInj

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀}
  {R₁ : Type} [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁)

def jj (i : I) : R₁ := Classical.choose (α.surj i.1 i.2)

theorem jj_q (i : I) : α.q (jj α i) = 0 := (Classical.choose_spec (α.surj i.1 i.2)).1

theorem jj_k (i : I) : α.k (jj α i) = i := (Classical.choose_spec (α.surj i.1 i.2)).2

theorem eq_jj {y : R₁} {i : I} (hq : α.q y = 0) (hk : α.k y = i) : y = jj α i := by
  have h := α.inj (y - jj α i) (by rw [map_sub, hq, jj_q, sub_zero]) (by rw [map_sub, hk, jj_k, sub_self])
  exact sub_eq_zero.mp h

theorem jj_add (i i' : I) : jj α (i + i') = jj α i + jj α i' :=
  (eq_jj α (by rw [map_add, jj_q, jj_q, add_zero]) (by rw [map_add, jj_k, jj_k]; rfl)).symm

theorem jj_smul (r : R) (i : I) : jj α (r • i) = π r • jj α i :=
  (eq_jj α (by rw [map_smul, jj_q, smul_zero]) (by rw [α.smul, jj_k]; rfl)).symm

variable {B B₀ : Type} [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] (p : B →+* B₀)

def tau (hs : SemiHom π p) : I ⊗[R] B →+ R₁ ⊗[R₀] B₀ :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun i ↦ AddMonoidHom.mk' (fun b ↦ jj α i ⊗ₜ[R₀] p b)
      (fun b b' ↦ by rw [map_add, TensorProduct.tmul_add]))
      (fun i i' ↦ by ext b; simp [jj_add, TensorProduct.add_tmul]))
    (fun r i b ↦ by
      simp only [AddMonoidHom.mk'_apply]
      rw [jj_smul, hs r b, TensorProduct.smul_tmul])

theorem tau_tmul (hs : SemiHom π p) (i : I) (b : B) : tau α p hs (i ⊗ₜ b) = jj α i ⊗ₜ[R₀] p b := by
  simp [tau, TensorProduct.liftAddHom_tmul]

end GlobalTheory.Obs.SigInj

open GlobalTheory.Obs.SigInj in
theorem GlobalTheory.Obs.sig_inj_of_flat : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (B B₀ : Type) [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] (p : B →+* B₀) (hs : SemiHom π p) (hp : Function.Surjective p) (hker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) [Module.Flat R B] (σ : R₁ ⊗[R₀] B₀ →+ B), α.IsSig p σ → ∀ y, α.KerQ y → σ y = 0 → y = 0 := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α B B₀ _ _ _ _ p hs hp hker _ σ hσ y hy h0
  have hrange : ∀ y : R₁ ⊗[R₀] B₀, ∃ z, tau α p hs z =
      y - (1 : R₁) ⊗ₜ[R₀] TensorProduct.lid R₀ B₀ (Algebra.TensorProduct.map α.q (AlgHom.id R₀ B₀) y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul x b₀ =>
      obtain ⟨b, rfl⟩ := hp b₀
      have hq' : α.q (x - algebraMap R₀ R₁ (α.q x)) = 0 := by simp
      refine ⟨⟨α.k (x - algebraMap R₀ R₁ (α.q x)), α.mem _⟩ ⊗ₜ b, ?_⟩
      rw [tau_tmul, ← eq_jj α hq' rfl, Algebra.TensorProduct.map_tmul, TensorProduct.lid_tmul,
        ← TensorProduct.smul_tmul, TensorProduct.sub_tmul, Algebra.algebraMap_eq_smul_one]
      rfl
    | add a c ha hc =>
      obtain ⟨za, hza⟩ := ha
      obtain ⟨zc, hzc⟩ := hc
      exact ⟨za + zc, by rw [map_add, hza, hzc, map_add, map_add, TensorProduct.tmul_add]; abel⟩
  obtain ⟨z, hz⟩ := hrange y
  rw [show Algebra.TensorProduct.map α.q (AlgHom.id R₀ B₀) y = 0 from hy, map_zero,
    TensorProduct.tmul_zero, sub_zero] at hz
  have hμ : ∀ z, σ (tau α p hs z) = TensorProduct.lid R B (LinearMap.rTensor B I.subtype z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul i b => rw [tau_tmul, hσ, jj_k]; simp
    | add a c ha hc => rw [map_add, map_add, map_add, map_add, ha, hc]
  have hinj : Function.Injective (fun z ↦ TensorProduct.lid R B (LinearMap.rTensor B I.subtype z)) :=
    (TensorProduct.lid R B).injective.comp
      (Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective)
  have hz0 : z = 0 := hinj (by
    show TensorProduct.lid R B (LinearMap.rTensor B I.subtype z) =
      TensorProduct.lid R B (LinearMap.rTensor B I.subtype 0)
    rw [map_zero, map_zero, ← hμ, hz, h0])
  rw [← hz, hz0, map_zero]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSigmaMapNatural
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs

theorem sig_natural : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (B B₀ : Type) [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] (p : B →+* B₀) (hs : SemiHom π p) (hp : Function.Surjective p) (hker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) (B' B₀' : Type) [CommRing B'] [Algebra R B'] [CommRing B₀'] [Algebra R₀ B₀'] (p' : B' →+* B₀') (hs' : SemiHom π p') (hp' : Function.Surjective p') (hker' : ∀ b, p' b = 0 ↔ b ∈ I.map (algebraMap R B')) (ρ : B →ₐ[R] B') (φ : B₀ →ₐ[R₀] B₀'), (∀ b, p' (ρ b) = φ (p b)) → ∀ (σ : R₁ ⊗[R₀] B₀ →+ B) (σ' : R₁ ⊗[R₀] B₀' →+ B'), α.IsSig p σ → α.IsSig p' σ' → (∀ y, ρ (σ y) = σ' (extHom R₁ φ y)) ∧ ∀ y, α.KerQ y → α.KerQ (extHom R₁ φ y) := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α B B₀ _ _ _ _ p hs hp hker B' B₀' _ _ _ _ p' hs' hp' hker' ρ φ hρ σ σ' hσ hσ'
  refine ⟨fun y => ?_, fun y hy => ?_⟩
  · induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r b₀ =>
      obtain ⟨b, rfl⟩ := hp b₀
      rw [hσ r b]
      simp only [extHom, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      rw [← hρ b, hσ' r (ρ b), map_smul]
    | add x z hx hz => simp only [map_add, hx, hz]
  · have key : ∀ y : R₁ ⊗[R₀] B₀,
        Algebra.TensorProduct.map α.q (AlgHom.id R₀ B₀') (extHom R₁ φ y) =
          Algebra.TensorProduct.map (AlgHom.id R₀ R₀) φ (Algebra.TensorProduct.map α.q (AlgHom.id R₀ B₀) y) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul r b₀ => simp [extHom]
      | add x z hx hz => simp only [map_add, hx, hz]
    unfold Aug.KerQ at hy ⊢
    rw [key, hy, map_zero]

end GlobalTheory.Obs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLocusExponentTwistingSectionMulLeStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseLocusExponent_twistingSection_mul_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (x : ℝ) (G G₀ : WTZ E), Even G.2 → ∀ (cst k : ℝ) (q : ℕ), q.Prime → ∀ t : ∀ Z : Comp Xo c, TwSec U x Z G₀, (∀ Z (w : HeightOneSpectrum (𝓞 c.F)), ((q : ℕ) : 𝓞 c.F) ∈ w.asIdeal → (t Z).hi w - (⌊(t Z).lo w⌋ : ℝ) ≤ k * (vAdd w (q : c.F) : ℝ)) → refExp_vp U cst (G + G₀) q ≤ refExp_vp U cst G q + (k : EReal) := by
  first | exact @GlobalTheory.RefTwist.refExp_vp_add_le | exact GlobalTheory.RefTwist.refExp_vp_add_le | (intros; apply GlobalTheory.RefTwist.refExp_vp_add_le <;> assumption)
end

