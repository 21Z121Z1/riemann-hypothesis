import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0005
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1840
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1833
import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.Bundle0007
import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.Bundle0002
import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.LogSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1918
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1777
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1796
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1967
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUgReindex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTransportAdelicSchwartzThetaTrans
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1423
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1971
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1711
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1903
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1972
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1714
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1876
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1973
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0361
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0040
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.MemRangeOfIsAlgebraicRatFun
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0229
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1181
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousComplEquivSymm

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumEqualSignKernelLossesBounded
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem GlobalTheory.SumSize.TopSize.depSum {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) :
    ∃ S : Finset ℕ, GlobalTheory.NormSum.Exponents S (fun l => if l.Prime then (depL G l : ℝ) else 0) (sig G) := by
  classical
  let c : HeightOneSpectrum (𝓞 D.host.F) → ℕ := fun v => ringChar (𝓞 D.host.F ⧸ v.asIdeal)
  have key : ∀ l : ℕ, l.Prime → depL G l = 0 ∨ ∃ v ∈ G.pl.S0, c v = l ∧ l ≤ Ideal.absNorm v.asIdeal ∧
      depL G l = G.pl.depth sc v := by
    intro l hl
    rcases (G.pl.W0.filter fun PP => (l : 𝓞 D.host.E) ∈ PP.asIdeal).eq_empty_or_nonempty with h | h
    · left; unfold depL; rw [h]; rfl
    · right
      obtain ⟨PP, hPP, e⟩ := Finset.exists_mem_eq_sup _ h (depthAt G)
      obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hPP
      have h1' : ∃ v ∈ G.pl.S0, G.pl.w v = PP := by
        unfold Places.W0 at h1; simpa only [Finset.mem_image] using h1
      obtain ⟨v, hv, rfl⟩ := h1'
      have hlv : (l : 𝓞 D.host.F) ∈ v.asIdeal := by
        rw [← G.pl.under_w hv]
        change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) l ∈ (G.pl.w v).asIdeal
        rwa [map_natCast]
      haveI := v.isPrime
      haveI : Finite (𝓞 D.host.F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
      have h0 : ((l : ℕ) : 𝓞 D.host.F ⧸ v.asIdeal) = 0 := by
        rw [← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem]; exact hlv
      have hc : c v = l := CharP.ringChar_of_prime_eq_zero hl h0
      refine ⟨v, hv, hc, ?_, ?_⟩
      · have h3 : ((Nat.card (𝓞 D.host.F ⧸ v.asIdeal) : ℕ) : 𝓞 D.host.F ⧸ v.asIdeal) = 0 := by
          haveI := Fintype.ofFinite (𝓞 D.host.F ⧸ v.asIdeal)
          rw [Nat.card_eq_fintype_card]; exact Nat.cast_card_eq_zero _
        rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, ← hc]
        exact Nat.le_of_dvd Nat.card_pos (ringChar.dvd h3)
      · rw [← (depthAt_w G hv).2, ← e]; unfold depL; congr
  refine ⟨(G.pl.S0.image c).filter Nat.Prime, fun l hl => (Finset.mem_filter.1 hl).2,
    fun l => by dsimp only; split_ifs <;> positivity, fun l hl => ?_, ?_⟩
  · dsimp only
    split_ifs with hp
    · rcases key l hp with h | ⟨v, hv, h, -⟩
      · rw [h, Nat.cast_zero]
      · exact absurd (Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨v, hv, h⟩, hp⟩) hl
    · rfl
  have hnn : ∀ v, 0 ≤ (G.pl.depth sc v : ℝ) * Real.log (Ideal.absNorm v.asIdeal) :=
    fun v => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
  unfold sig
  rw [← Finset.sum_fiberwise_of_maps_to (g := c) (t := G.pl.S0.image c) (fun w hw => Finset.mem_image_of_mem _ hw)]
  refine le_trans (Finset.sum_le_sum fun l hl => ?_) (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset Nat.Prime _)
    fun l _ _ => Finset.sum_nonneg fun v _ => hnn v)
  have hp := (Finset.mem_filter.1 hl).2
  dsimp only
  rw [if_pos hp]
  rcases key l hp with h | ⟨v, hv, h, h1, h2⟩
  · rw [h, Nat.cast_zero, zero_mul]; exact Finset.sum_nonneg fun v _ => hnn v
  · refine le_trans ?_ (Finset.single_le_sum (f := fun v => (G.pl.depth sc v : ℝ) * Real.log (Ideal.absNorm v.asIdeal))
      (fun v _ => hnn v) (Finset.mem_filter.2 ⟨hv, h⟩))
    rw [h2]
    exact mul_le_mul_of_nonneg_left (Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast h1)) (Nat.cast_nonneg _)

private theorem GlobalTheory.SumSize.TopSize.sum_le_of_exponents {S : Finset ℕ} {h : ℕ → ℝ} {B : ℝ} (hE : GlobalTheory.NormSum.Exponents S h B)
    (P : Finset ℕ) : ∑ p ∈ P, h p * Real.log p ≤ B := by
  obtain ⟨-, h0, hS, hB⟩ := hE
  calc ∑ p ∈ P, h p * Real.log p ≤ ∑ p ∈ P ∪ S, h p * Real.log p :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
          (fun p _ _ => mul_nonneg (h0 p) (Real.log_natCast_nonneg p))
    _ = ∑ p ∈ S, h p * Real.log p :=
        (Finset.sum_subset Finset.subset_union_right (fun x _ hxS => by rw [hS x hxS, zero_mul])).symm
    _ ≤ _ := hB

private theorem GlobalTheory.SumSize.TopSize.sum_nab_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) {X : ℝ} (hX : 0 ≤ X) :
    ∑ p ∈ P, (if (p : ℝ) ≤ X then Real.logb p X else 0) * Real.log p ≤ X * max (Real.log X) 0 := by
  simp only [ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  rcases lt_or_ge X 1 with h1 | h1
  · rw [Finset.filter_false_of_mem, Finset.sum_empty]
    · positivity
    · intro p hp hle
      have : (1 : ℝ) < p := by exact_mod_cast (hP p hp).one_lt
      linarith
  · rw [max_eq_left (Real.log_nonneg h1)]
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) fun p hp _ => ?_) (UpperTheory.WildA.logSum X h1)
    · obtain ⟨hp1, hp2⟩ := Finset.mem_filter.1 hp
      exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.le_floor hp2)), hP p hp1⟩
    · have hp' := (Finset.mem_filter.1 hp).2
      exact mul_nonneg (Real.logb_nonneg (by exact_mod_cast hp'.one_lt) h1) (Real.log_natCast_nonneg p)

private theorem GlobalTheory.SumSize.TopSize.d_le {D : D7} (large₂ : SizeData₂ D) (h : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂) :
    (D.host.d : ℝ) ≤ large₂.sc.b := by
  obtain ⟨-, -, -, hf, hm, -⟩ := GlobalTheory.SizesOfRows.sizes_of_sizeRows large₂ h
  obtain ⟨-, -, -, -, -, hb, -⟩ := h
  have hk : D.R.m + 3 ≤ D.R.k := D.R.m_add_three_le_k
  have hN1 : 1 ≤ D.R.N D.R.m := by simp only [Formalism.BasicNotions.Ranks.N]; omega
  have h1 : 1 ≤ D.R.m * D.R.f * D.R.N D.R.m ^ 2 := Nat.mul_pos (Nat.mul_pos (by omega) hf) (by positivity)
  have h2 : (1 : ℝ) ≤ (D.R.m : ℝ) * D.R.f * (D.R.N D.R.m : ℝ) ^ 2 := by exact_mod_cast h1
  exact (le_mul_of_one_le_left (Nat.cast_nonneg _) h2).trans hb

private theorem GlobalTheory.SumSize.TopSize.arith {C1 C f m N b lb sg s1 s2 s3 s4 : ℝ} (hC1 : 0 < C1)
    (hC : C1 * 26 + C1 ^ 2 * (|Real.log C1| + 1) ≤ C) (hf : 0 ≤ f) (hm : 0 ≤ m) (hN : 1 ≤ N) (hb : 0 ≤ b) (hlb : 1 ≤ lb)
    (hsg : 0 ≤ sg) (h1 : s1 ≤ lb / 100) (h2 : s2 ≤ lb) (h3 : s3 ≤ sg) (h4 : s4 ≤ C1 * b * (|Real.log C1| + lb)) :
    C1 * m * (13 * f * N * b) * s1 + C1 * m * (13 * f * N * b) * s2 + C1 * m * (13 * f * N * b) * s3 +
      C1 * m * (f * N ^ 2) * s4 ≤ C * f * m * N ^ 2 * (lb + sg) * b := by
  have hM0 : 0 ≤ f * m * N ^ 2 * b * (lb + sg) := by positivity
  have hNN : N ≤ N ^ 2 := by nlinarith
  have hT1 : C1 * m * (13 * f * N * b) * (s1 + s2 + s3) ≤ C1 * 26 * (f * m * N ^ 2 * b * (lb + sg)) := by
    calc C1 * m * (13 * f * N * b) * (s1 + s2 + s3) ≤ C1 * m * (13 * f * N * b) * (2 * (lb + sg)) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ ≤ C1 * m * (13 * f * N ^ 2 * b) * (2 * (lb + sg)) := by gcongr
      _ = _ := by ring
  have h5 : |Real.log C1| + lb ≤ (|Real.log C1| + 1) * (lb + sg) := by nlinarith [abs_nonneg (Real.log C1)]
  have hT2 : C1 * m * (f * N ^ 2) * s4 ≤ C1 ^ 2 * (|Real.log C1| + 1) * (f * m * N ^ 2 * b * (lb + sg)) := by
    calc C1 * m * (f * N ^ 2) * s4 ≤ C1 * m * (f * N ^ 2) * (C1 * b * (|Real.log C1| + lb)) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ ≤ C1 * m * (f * N ^ 2) * (C1 * b * ((|Real.log C1| + 1) * (lb + sg))) := by gcongr
      _ = _ := by ring
  have hC0 := mul_le_mul_of_nonneg_right hC hM0
  calc _ = C1 * m * (13 * f * N * b) * (s1 + s2 + s3) + C1 * m * (f * N ^ 2) * s4 := by ring
    _ ≤ (C1 * 26 + C1 ^ 2 * (|Real.log C1| + 1)) * (f * m * N ^ 2 * b * (lb + sg)) := by linarith
    _ ≤ C * (f * m * N ^ 2 * b * (lb + sg)) := hC0
    _ = _ := by ring

open GlobalTheory.SumSize.TopInt GlobalTheory.SumSize.TopSize in
private theorem GlobalTheory.SumSize.TopSize.core {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T)
    (large₂ : SizeData₂ D) (hs : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂) (hH : HostHyp D) (hc : sc.cGap = 1) {C1 C : ℝ} (hC1 : 0 < C1)
    (hC : C1 * 26 + C1 ^ 2 * (|Real.log C1| + 1) ≤ C) {S : Finset ℕ} {δ : ℕ → ℝ}
    (hδ : GlobalTheory.NormSum.Exponents S δ (Real.log D.host.rdE)) :
    Loss (topDl G δ C1 large₂.sc.b) (bOne G C large₂.sc.b) := by
  classical
  obtain ⟨Sd, hSd⟩ := depSum G
  obtain ⟨-, -, hN, -, -, -, hrd, hb12⟩ := GlobalTheory.SizesOfRows.sizes_of_sizeRows large₂ hs
  have hd := d_le large₂ hs
  have hker : ∀ j, j < D.R.m → ((∑ τ, ∑ a, (wt G (.top (j + 1)) τ).natW a : ℕ) : ℝ) +
      (D.R.f : ℝ) * (G.V (.top j)).rank * (G.V (.top (j + 1))).rank ≤ 13 * D.R.f * bigN D * large₂.sc.b :=
    fun j hj => UpperTheory.WildA.kerLe (G := G) large₂ hs hH hc (.top t j) hj
  generalize large₂.sc.b = b at *
  have hδ0 := hδ.2.1
  have hlb : 1 ≤ Real.log b := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hsig : 0 ≤ sig G := Finset.sum_nonneg fun v _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
  set h : ℕ → ℝ := fun l => if l.Prime then
    C1 * ∑ j ∈ Finset.range D.R.m, kerLoss G δ C1 b (.top j) (.top (j + 1)) l (depL G l) else 0 with hh
  set P : Finset ℕ := (S ∪ {D.host.d} ∪ Sd ∪ Finset.range (⌊C1 * b⌋₊ + 1)).filter Nat.Prime with hP
  have hPp : ∀ p ∈ P, p.Prime := fun p hp => (Finset.mem_filter.1 hp).2
  have e : topDl G δ C1 b = fun w : PlL D => (vw w ((primeUnder w : ℕ) : D.what₂.LL) : ℝ) * h (primeUnder w) := by
    funext w
    simp only [hh, if_pos (primeUnder_prime w), topDl, mul_assoc]
  rw [e]
  refine UpperTheory.WildA.expLoss D P h _ ⟨hPp, fun l => ?_, fun l hl => ?_, ?_⟩
  · simp only [hh]
    split_ifs with hl
    · exact mul_nonneg hC1.le (Finset.sum_nonneg fun j _ => kerLoss_nonneg G hδ0 C1 b _ _ hl _)
    · exact le_rfl
  · simp only [hh]
    split_ifs with hp
    · simp only [hP, Finset.mem_filter, hp, and_true, Finset.mem_union, Finset.mem_singleton, Finset.mem_range, not_or] at hl
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hl
      have e1 := hδ.2.2.1 l h1
      have e3 : (depL G l : ℝ) = 0 := by simpa only [if_pos hp] using hSd.2.2.1 l h3
      have e4 : ¬ (l : ℝ) ≤ C1 * b := fun h5 => h4 (Nat.lt_succ_of_le (Nat.le_floor h5))
      simp only [kerLoss, e1, e3, if_neg h2, if_neg e4, add_zero, mul_zero, Finset.sum_const_zero]
    · rfl
  have hKp : ∀ p ∈ P, h p * Real.log p ≤
      C1 * D.R.m * (13 * D.R.f * bigN D * b) * (δ p * Real.log p) +
        C1 * D.R.m * (13 * D.R.f * bigN D * b) * ((if p = D.host.d then (1 : ℝ) else 0) * Real.log p) +
        C1 * D.R.m * (13 * D.R.f * bigN D * b) * ((if p.Prime then (depL G p : ℝ) else 0) * Real.log p) +
        C1 * D.R.m * (D.R.f * (bigN D : ℝ) ^ 2) * ((if (p : ℝ) ≤ C1 * b then Real.logb p (C1 * b) else 0) * Real.log p) := by
    intro p hp
    have hM : 0 ≤ δ p + (if p = D.host.d then (1 : ℝ) else 0) + (depL G p : ℝ) := by
      have := hδ0 p
      have : 0 ≤ (if p = D.host.d then (1 : ℝ) else 0) := by split_ifs <;> norm_num
      positivity
    have hK := Finset.sum_le_card_nsmul (Finset.range D.R.m)
      (fun j => kerLoss G δ C1 b (.top j) (.top (j + 1)) p (depL G p))
      ((13 * D.R.f * bigN D * b) * (δ p + (if p = D.host.d then 1 else 0) + (depL G p : ℝ)) +
        D.R.f * (bigN D : ℝ) ^ 2 * (if (p : ℝ) ≤ C1 * b then Real.logb p (C1 * b) else 0)) (fun j hj => by
        unfold kerLoss
        exact add_le_add (mul_le_mul_of_nonneg_right (hker j (Finset.mem_range.1 hj)) hM) le_rfl)
    rw [Finset.card_range, nsmul_eq_mul] at hK
    have hlp : 0 ≤ Real.log p := Real.log_natCast_nonneg p
    simp only [hh, if_pos (hPp p hp)]
    refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK hC1.le) hlp).trans (le_of_eq ?_)
    ring
  have hs2 : ∑ p ∈ P, (if p = D.host.d then (1 : ℝ) else 0) * Real.log p ≤ Real.log b := by
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq']
    split_ifs with hdP
    · exact Real.log_le_log (by exact_mod_cast (hPp _ hdP).pos) hd
    · linarith
  have hs4 : ∑ p ∈ P, (if (p : ℝ) ≤ C1 * b then Real.logb p (C1 * b) else 0) * Real.log p ≤
      C1 * b * (|Real.log C1| + Real.log b) := by
    have h0 : 0 ≤ C1 * b := mul_nonneg hC1.le (by linarith)
    refine (sum_nab_le P hPp h0).trans (mul_le_mul_of_nonneg_left ?_ h0)
    rw [Real.log_mul hC1.ne' (by linarith)]
    exact max_le (by linarith [le_abs_self (Real.log C1)]) (by linarith [abs_nonneg (Real.log C1)])
  refine (Finset.sum_le_sum hKp).trans ?_
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  exact arith hC1 hC (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by exact_mod_cast hN) (by linarith) hlb hsig
    ((sum_le_of_exponents hδ P).trans hrd) hs2 (sum_le_of_exponents hSd P) hs4

theorem _root_.GlobalTheory.T.sum_equalSign_kernel_losses_bounded : ∀ C1 : ℝ, 0 < C1 → ∃ CF0 : ℝ, ∀ CF : ℝ, CF0 ≤ CF → ∃ C0 : ℝ, ∀ ε C : ℝ, C0 ≤ C → ∃ x₀ : ℝ,
      ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x →
      ∀ (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m)
      (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), HidaSetting large₂ R F →
      ∀ ch : Choice R, ch.Is → ch.AtScale CF large₂.sc.b → ch.FieldOK → GlobalTheory.NormSum.Inp D →
      ∀ (S : Finset ℕ) (δ : ℕ → ℝ), GlobalTheory.NormSum.Letters D S δ →
        Loss (GlobalTheory.SumSize.TopInt.topDl ch.G δ C1 large₂.sc.b) (bOne ch.G C large₂.sc.b) := by
  intro C1 hC1
  refine ⟨0, fun CF _ => ⟨C1 * 26 + C1 ^ 2 * (|Real.log C1| + 1), fun ε C hC => ⟨0, ?_⟩⟩⟩
  intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hSet ch _ hAt _ _ S δ hLet
  have hc : ch.sc.cGap = 1 := by rw [hAt]
  exact GlobalTheory.SumSize.TopSize.core ch.G A.μ0 large₂ hSet.size hSet.host hc hC1 hC ⟨hLet.1, hLet.2.1, hLet.2.2.1, hLet.2.2.2.1⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftEqIntegralRouteKernelFubini
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.BigRoute

theorem lift_eq_integral_kerBig : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (hWC : GlobalTheory.SquareSt.WeilConvergence) (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree) (hP : GlobalTheory.Published.CuspDecayBound) {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (hT : SquareTriple W t i j)
    (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ')
    (F : Fn G (.grid i (j + 1))) (hF : IsAutFunSm W.θ _ F) (hFc : IsCuspFun _ F) (hFl : G.IsListed W.θ _ F) (hA : TotConv W M _ Θ F) (g₁ : GA D (G.V (.grid (i + 1) j))),
    (∀ᵐ g ∂(M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1))),
      IntegrableOn (kerBig W Θ g g₁) (M.fd (.grid (i + 1) (j + 1))) (M.ν (.grid (i + 1) (j + 1)))) ∧
    liftT W M (routeBig t i j) Θ F g₁ = ∫ g in M.fd (.grid i (j + 1)), F g * ∫ u in M.fd (.grid (i + 1) (j + 1)),
      kerBig W Θ g g₁ u ∂M.ν (.grid (i + 1) (j + 1)) ∂M.ν (.grid i (j + 1)) := by
  intro D T L sc G hWC hK hP μ₀ hL W B ρ t i j hT M hM Θ Θ' hΘ F hF hFc hFl hA g₁
  classical
  have hσ : ∀ X : Node, X.InRange D.R.m → SigmaFinite (M.ν X) := fun X hX => by
    obtain ⟨h1, h2, -⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D (G.V X)
    haveI := (hM.vtx X hX).haar_fund.1
    infer_instance
  haveI := hσ (.grid i (j + 1)) ⟨i.2.le, j.2⟩
  haveI := hσ (.grid (i + 1) (j + 1)) ⟨i.2, j.2⟩
  have hK1 : ∀ g, IntegrableOn (kerBig W Θ g g₁) (M.fd (.grid (i + 1) (j + 1))) (M.ν (.grid (i + 1) (j + 1))) := GlobalTheory.T.bigRoute_kernel_integrableOn_unitary_quotient hWC hL W B ρ t i j hT M hM Θ Θ' hΘ g₁
  have hmeas : AEStronglyMeasurable (fun p : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid (i + 1) (j + 1))) =>
      kerBig W Θ p.1 g₁ p.2) (((M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1)))).prod
        ((M.ν (.grid (i + 1) (j + 1))).restrict (M.fd (.grid (i + 1) (j + 1))))) := GlobalTheory.T.aestronglyMeasurable_kernel_route_big_vertex hL W B ρ t i j M hM Θ Θ' hΘ g₁
  have hinv : ∀ γ ∈ GQ (G.V (.grid i (j + 1))), ∀ g, kerBig W Θ (γ * g) g₁ = kerBig W Θ g g₁ := GlobalTheory.T.kernel_route_big_vertex_rational_left_invariant hL W B ρ t i j Θ Θ' hΘ g₁
  have hgrow : GlobalTheory.Grow.ModGrowth (G.V (.grid i (j + 1))) (fun g => ∫ u in M.fd (.grid (i + 1) (j + 1)),
      ‖kerBig W Θ g g₁ u‖ ∂M.ν (.grid (i + 1) (j + 1))) := GlobalTheory.T.moderateGrowth_integral_norm_kernel_bigVertexRoute hWC hL W B ρ t i j hT M hM Θ Θ' hΘ g₁
  have hRD : GlobalTheory.Grow.RapidDec _ F := GlobalTheory.Grow.rapidDec_of_cuspForm (GlobalTheory.Grow.cuspRapidDecay_of_bound hP) W.θ_is hF hFc
  obtain ⟨hH, hfd⟩ := (hM.vtx (.grid i (j + 1)) ⟨i.2.le, j.2⟩).haar_fund
  have hkm : AEStronglyMeasurable (fun g => ((∫ u in M.fd (.grid (i + 1) (j + 1)), ‖kerBig W Θ g g₁ u‖
      ∂M.ν (.grid (i + 1) (j + 1)) : ℝ) : ℂ)) ((M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1)))) :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hmeas.norm.integral_prod_right'
  obtain ⟨C, A, hCA⟩ := hgrow
  have hkb : ∀ g, ‖((∫ u in M.fd (.grid (i + 1) (j + 1)), ‖kerBig W Θ g g₁ u‖ ∂M.ν (.grid (i + 1) (j + 1)) : ℝ) : ℂ)‖ ≤
      C * 2 ^ A * GlobalTheory.Grow.quotHeight _ g ^ A := fun g => by
    rw [Complex.norm_real]
    exact GlobalTheory.Grow.norm_le_quotHeight_pow (fun γ hγ g => by simp only [hinv γ hγ g]) hCA g
  have hkF := hRD.integrableOn_mul_of_le hH hfd hkm hkb
  have hJ : Integrable (fun p : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid (i + 1) (j + 1))) => F p.1 * kerBig W Θ p.1 g₁ p.2)
      (((M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1)))).prod
        ((M.ν (.grid (i + 1) (j + 1))).restrict (M.fd (.grid (i + 1) (j + 1))))) := by
    have hFm : AEStronglyMeasurable F ((M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1)))) :=
      hRD.continuous.aestronglyMeasurable
    have hm2 : AEStronglyMeasurable (fun p : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid (i + 1) (j + 1))) =>
        F p.1 * kerBig W Θ p.1 g₁ p.2) (((M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1)))).prod
          ((M.ν (.grid (i + 1) (j + 1))).restrict (M.fd (.grid (i + 1) (j + 1))))) :=
      hFm.comp_fst.mul hmeas
    refine (integrable_prod_iff hm2).2
      ⟨.of_forall fun g => (hK1 g).const_mul (F g), ?_⟩
    refine hkF.norm.congr (.of_forall fun g => ?_)
    simp only [Pi.mul_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs, integral_const_mul]
    rw [abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _), mul_comm]
  refine ⟨Filter.Eventually.of_forall hK1, ?_⟩
  have hpt : ∀ u, ∫ g in M.fd (.grid i (j + 1)), F g * kerBig W Θ g g₁ u ∂M.ν (.grid i (j + 1)) =
      Θ.sum fun d c => c * (W.kerA (.down t (i + 1) j) d.2 u g₁ *
        ∫ g in M.fd (.grid i (j + 1)), W.kerA (.right i (j + 1)) d.1.2 g u * F g ∂M.ν (.grid i (j + 1))) := by
    intro u
    have hint : ∀ d ∈ Θ.support, IntegrableOn (fun g => W.kerA (.right i (j + 1)) d.1.2 g u * F g)
        (M.fd (.grid i (j + 1))) (M.ν (.grid i (j + 1))) := fun d hd => (hA d hd).1.2 u
    have e : ∀ g, F g * kerBig W Θ g g₁ u = ∑ d ∈ Θ.support,
        Θ d * (W.kerA (.down t (i + 1) j) d.2 u g₁ * (W.kerA (.right i (j + 1)) d.1.2 g u * F g)) := by
      intro g
      simp only [kerBig, Finsupp.sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun d _ => by ring
    simp_rw [e]
    rw [integral_finset_sum _ fun d hd => ((hint d hd).const_mul _).const_mul _]
    simp only [integral_const_mul, Finsupp.sum]
  have hint2 : ∀ d ∈ Θ.support, Integrable (fun u => W.kerA (.down t (i + 1) j) d.2 u g₁ *
        ∫ g in M.fd (.grid i (j + 1)), W.kerA (.right i (j + 1)) d.1.2 g u * F g ∂M.ν (.grid i (j + 1)))
      ((M.ν (.grid (i + 1) (j + 1))).restrict (M.fd (.grid (i + 1) (j + 1)))) := fun d hd => (hA d hd).2 g₁
  symm
  calc ∫ g in M.fd (.grid i (j + 1)), F g * ∫ u in M.fd (.grid (i + 1) (j + 1)), kerBig W Θ g g₁ u ∂M.ν (.grid (i + 1) (j + 1))
        ∂M.ν (.grid i (j + 1))
      = ∫ g in M.fd (.grid i (j + 1)), ∫ u in M.fd (.grid (i + 1) (j + 1)), F g * kerBig W Θ g g₁ u ∂M.ν (.grid (i + 1) (j + 1))
        ∂M.ν (.grid i (j + 1)) := by simp_rw [integral_const_mul]
    _ = ∫ u in M.fd (.grid (i + 1) (j + 1)), ∫ g in M.fd (.grid i (j + 1)), F g * kerBig W Θ g g₁ u
        ∂M.ν (.grid i (j + 1)) ∂M.ν (.grid (i + 1) (j + 1)) := integral_integral_swap hJ
    _ = ∫ u in M.fd (.grid (i + 1) (j + 1)), (Θ.sum fun d c => c * (W.kerA (.down t (i + 1) j) d.2 u g₁ *
        ∫ g in M.fd (.grid i (j + 1)), W.kerA (.right i (j + 1)) d.1.2 g u * F g ∂M.ν (.grid i (j + 1))))
        ∂M.ν (.grid (i + 1) (j + 1)) := by
        simp_rw [hpt]
    _ = _ := by
        simp only [Finsupp.sum]
        rw [integral_finset_sum _ fun d hd => (hint2 d hd).const_mul _]
        simp_rw [integral_const_mul]
        simp only [liftT, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        rfl

end GlobalTheory.BigRoute

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportedWeilDatumDoubledTargetRestrictBoxTens
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.WeilSchrodinger.DblRestrict

set_option maxHeartbeats 2000000 in

theorem omp_diag_boxFun : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (hA : JA = T.gramᵀ),
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
          ∀ om : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
              GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →* Module.End ℂ ((κ → AF D.host.F) → ℂ),
            GlobalTheory.WeilSchrodinger.IsTransport ψ co ω om →
          ∀ ωd : GA D S × GA D (GlobalTheory.Doubling.dblSp T) →* Module.End ℂ (Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S (GlobalTheory.Doubling.dblSp T) χS 1 ωd →
          ∀ omp : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F ((GlobalTheory.Doubling.dblSp T).gramᵀ)) ×
              GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →*
                Module.End ℂ ((κ ⊕ κ → AF D.host.F) → ℂ),
            GlobalTheory.WeilSchrodinger.IsTransport ψ (GlobalTheory.WeilSchrodinger.DblTarget.coDbl hA co) ωd omp →
          ∀ (g : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA))
            (gd : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F ((GlobalTheory.Doubling.dblSp T).gramᵀ))),
            gd.1.1 = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks g.1.1 0 0 1) →
            ∀ φ₁ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ φ₂ ∈ GlobalTheory.WeilM.schA D.host.F κ,
              omp (gd, 1) (GlobalTheory.WeilM.boxFun φ₁ φ₂) = GlobalTheory.WeilM.boxFun (om (g, 1) φ₁) φ₂ := by
  intro D ψ hψ S T χS χT hS hT rS rT JA JB ξ hA hB κ _ co hrat ω hω om hom ωd hωd omp homp g gd hgd φ₁ hφ₁ φ₂ hφ₂
  let h : GA D T := ⟨g.1, GlobalTheory.ThetaTransform.mem_GA_target hA g⟩
  let hd : GA D (GlobalTheory.Doubling.dblSp T) := ⟨gd.1, GlobalTheory.ThetaTransform.mem_GA_target rfl gd⟩
  have hh : Formalism.L2.Theta.mt T h = g.1.1 := rfl
  have hhd : Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp T) hd = gd.1.1 := rfl
  have h1S : Formalism.L2.Theta.mt S 1 = ((1 : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB))⁻¹).1.1ᵀ := by
    simp [Formalism.L2.Theta.mt]
  obtain ⟨hB1, hΘ1⟩ := hom g 1 1 h hh h1S φ₁ hφ₁
  have hbox := GlobalTheory.SchwartzBox.boxFun_mem_schA D.host.F κ κ φ₁ hφ₁ φ₂ hφ₂
  obtain ⟨hA1, hΘA⟩ := homp gd 1 1 hd hhd h1S _ hbox
  have hφ₂' := GlobalTheory.ConjSch.star_mem_schA κ φ₂ hφ₂
  have bij := GlobalTheory.ThetaTransform.thetaTr_bij co hψ hA hB hrat
  have bijd := GlobalTheory.ThetaTransform.thetaTr_bij (GlobalTheory.WeilSchrodinger.DblTarget.coDbl hA co) hψ rfl hB
    (GlobalTheory.WeilSchrodinger.DblTarget.coDbl_rat hA co hrat)
  refine bijd.2.1 _ hA1 _ (GlobalTheory.SchwartzBox.boxFun_mem_schA D.host.F κ κ _ hB1 φ₂ hφ₂) ?_
  have e1 := GlobalTheory.T.thetaTransform_doubledCoords_boxProduct D ψ hψ S T JA JB ξ hA κ co _ hφ₁ _ hφ₂
  have e2 := GlobalTheory.T.thetaTransform_doubledCoords_boxProduct D ψ hψ S T JA JB ξ hA κ co _ hB1 _ hφ₂
  have hgd' : Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp T) hd =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (Formalism.L2.Theta.mt T h) 0 0 1) := hgd
  have key := GlobalTheory.T.doubledWeilDatum_diag_acts_on_externalProduct D ψ hψ S T χS χT ω hω ωd hωd (GlobalTheory.T.doubledWeilDatum_diag_thetaProduct_eq_scalar_smul D ψ hψ S T χS χT ω hω ωd hωd) h hd hgd' _ _
    ((bij.2.2 _).2 ⟨φ₁, hφ₁, rfl⟩) ((bij.2.2 _).2 ⟨_, hφ₂', rfl⟩)
  refine hΘA.trans ?_
  refine ((congrArg (ωd (1, hd)) e1).trans key).trans ?_
  refine Eq.trans ?_ e2.symm
  rw [hΘ1]

end GlobalTheory.WeilSchrodinger.DblRestrict

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleLatticeInvariantSchwartzLocalStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triple_lattice_invariant_schwartz_local : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (w : Pl F) (g : (Fin a' × Fin (a + a') → Fv F w) → ℂ), g ∈ SB (Fin a' × Fin (a + a') → Fv F w) →
    (∀ γ ∈ latAtV G.V' G.W w, ∀ c : ℂ, Acts (evFin F w) (G.M'.co.rho B.ψ γ) (G.M'.vac w) (c • G.M'.vac w) →
      Acts (evFin F w) (G.M'.co.rho B.ψ γ) g (c • g)) →
    ∃ r : ℂ, g = r • G.M'.vac w := by
  first | exact @GlobalTheory.VacLine.eigen_line | exact GlobalTheory.VacLine.eigen_line | (intros; apply GlobalTheory.VacLine.eigen_line <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightZeroConstFrameValueMemCoeffRangeStatement
section
open NumberField Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightZero_const_frameValue_mem_coeff_range : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 1 ≤ Dw.p + Dw.q → ∀ f ∈ sec Xo c 0 0, ∀ a : ℂ, (∀ k, ∀ x ∈ (U.X k).dom, rdU U f k x = a) → a ∈ σ.range := by
  first | exact @GlobalTheory.FlatLine.const_value_mem_range | exact GlobalTheory.FlatLine.const_value_mem_range | (intros; apply GlobalTheory.FlatLine.const_value_mem_range <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenBijectiveGoodModelStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_eigen_bijective_good_model : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, IsEv B M M₁ 1 1 ∅ e → Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) →
    ∀ l : Fn F n d →ₗ[ℂ] ℂ, l ∈ (adeleClass F).adm (Fin n × Fin d) ↔ l ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d) := by
  first | exact @GlobalTheory.ModelAdmUnconditional.model_admissible_iff_evaluation | exact GlobalTheory.ModelAdmUnconditional.model_admissible_iff_evaluation | (intros; apply GlobalTheory.ModelAdmUnconditional.model_admissible_iff_evaluation <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOrthogonalFiniteCoverStatement
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
open MeasureTheory

theorem _root_.GlobalTheory.T.exists_finset_pairing_trivial_imp_mem_open_subgroup : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ e, IsSplitIdemF σ e → ∀ U : AddSubgroup (WOF F E nS nT), IsOpen (U : Set (WOF F E nS nT)) →
        ∃ G : Finset (WOF F E nS nT), (∀ g ∈ G, ∀ i j, e * g i j = g i j) ∧
          ∀ y : WOF F E nS nT, (∀ i j, cAF σ e * y i j = y i j) →
            (∀ g ∈ G, B.ψ (symplOHF σ JS JT ξ₀ g y - symplOHF σ JS JT ξ₀ y g) = 1) → y ∈ U := by
  first | exact @GlobalTheory.SplitAnnF.exists_finset_ann_le | exact GlobalTheory.SplitAnnF.exists_finset_ann_le | (intros; apply GlobalTheory.SplitAnnF.exists_finset_ann_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaFunctionTransportLocalFieldIsoStatement
section
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitFlip GlobalTheory.FlipMatch GlobalTheory.FlipMatch.FieldTransport GlobalTheory.PureMatch.Transport

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zetaFunction_transport_localFieldIso : ∀ {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {j : k ≃+* k'} {A A' D A₂ A₂' D₂ : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D] [Fintype A₂] [DecidableEq A₂] [Fintype A₂'] [DecidableEq A₂'] [Fintype D₂] [DecidableEq D₂] [MeasurableSpace k] [BorelSpace k] [MeasurableSpace k'] [BorelSpace k'] (hj : IsLocIso j) (rA : A₂ ≃ A) (rA' : A₂' ≃ A') (cD : D₂ ≃ D) (μ₂ : Measure (GL A₂' k')) [μ₂.IsHaarMeasure] (σ₂ : A₂ ⊕ A₂' ≃ D₂) (σ : A ⊕ A' ≃ D), (∀ s, cD (σ₂ s) = σ (Sum.map rA rA' s)) → ∀ (ν₂ : k'ˣ →* ℂˣ) (ν : kˣ →* ℂˣ), (∀ x, ν x = ν₂ (Units.map (j : k →* k') x)) → ∀ (Ψ : Matrix A₂' D₂ k' → ℂ) (Z : Matrix A D k), fFun μ₂ σ₂ ν₂ Ψ (trM j rA cD Z) = fFun (pullMeas hj rA' μ₂) σ ν (fun Y => Ψ (trM j rA' cD Y)) Z := by
  first | exact @GlobalTheory.PureMatch.Transport.fFun_trM | exact GlobalTheory.PureMatch.Transport.fFun_trM | (intros; apply GlobalTheory.PureMatch.Transport.fFun_trM <;> assumption)
end

