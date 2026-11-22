import Formalism.LocalToGlobal.GlobalTheory.FamCol
import Formalism.LocalToGlobal.GlobalTheory.FamRecP
import Formalism.LocalToGlobal.GlobalTheory.ArithP
import Formalism.LocalToGlobal.GlobalTheory.HLatOpsP
import Formalism.SizeWindowBrackets.ChainSlopeWindows.SecondPriceSumWeightsUncovered
import Formalism.SizeWindowBrackets.ChainSlopeWindows.ChainLatticeSizesModelEventually
import Formalism.SizeWindowBrackets.ChainSlopeWindows.AnalyticFirstToLatticeDiscriminant
import Formalism.LocalToGlobal.GlobalTheory.PlacesP
import Formalism.LocalToGlobal.GlobalTheory.CloudNonneg
import Mathlib
import Formalism.GL3MeanSquares.HookFormulaTorsion.HilbertSchmidtHalfBound
import Formalism.GL3MeanSquares.HookFormulaTorsion.Bundle0006
import Formalism.LogVandermondeBounds.LogVandermondeProofs.LogRatioLowerBoundOfLogVandermondeGap
import Formalism.GL3MeanSquares.HookFormulaTorsion.IndicatorValueMemUnitInterval
import Formalism.LogVandermondeBounds.LogVandermondeProofs.UpperPlaceHolds
import Formalism.LogVandermondeBounds.LogVandermondeProofs.VandNSuccRight

-- bundled from Formalism.LocalToGlobal.GlobalTheory.FamColP
section
open Module NumberField IsDedekindDomain Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.FamCol

open Formalism Formalism.BasicNotions Formalism.HN Formalism.LFunctionChainParameters Formalism.L2.Col Formalism.L2.DIV

section One

variable {K : Type} [Field K] [NumberField K] [StarRing K] {I : Type}

variable {C : ColObj K I} {P : PlDat K I}

variable [IsTotallyComplex K] {m : ℕ} (R : RowArg C)

end One

section Two

variable {K : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] {I : Type} {m : ℕ}
  (C : ColIface K I) {P : PlDat K I} (R : RowArg C.toColObj)

theorem ColFacts.elim {C : ColObj K I} (h : ColFacts C) {p : ColObj K I → Prop}
    (hp : ∀ J : ColIface K I, p J.toColObj) : p C := by
  obtain ⟨J, rfl⟩ := h
  exact hp J

end Two

section Three

variable {K : Type} [Field K] [NumberField K] [StarRing K] {I : Type} {P : PlDat K I}

end Three

section Family

open Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
  Formalism.LFunctionChainParameters.LChain2

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} [∀ u0, Fintype (W u0)] {m : ℕ}

theorem Pt.du_pos {I : Type} (Q : Pt I) (h : ColFacts Q.C) (m : ℕ) (u : I) : 0 < (Q.fam m).du u := by
  show (0 : ℝ) < (Fintype.card (Q.C.M u).ι : ℝ)
  exact_mod_cast h.elim (p := fun C => 0 < Fintype.card (C.M u).ι) (fun J => J.rank_pos u)

theorem SameNumbers.symm {I : Type} [Fintype I] {m : ℕ} {F F' : Fam I m} (h : SameNumbers F F') : SameNumbers F' F where
  du u := (h.du u).symm
  dM u := (h.dM u).symm
  T u := (h.T u).symm
  muN u := (h.muN u).symm
  muMaxN u := (h.muMaxN u).symm
  h u := (h.h u).symm
  muM u := (h.muM u).symm
  muMaxM u := (h.muMaxM u).symm
  EeJ u j := (h.EeJ u j).symm
  muCC := h.muCC.symm
  muMinCC := h.muMinCC.symm
  Fo := h.Fo.symm
  Ga := h.Ga.symm
  Ta := h.Ta.symm
  IO := h.IO.symm
  del := h.del.symm
  e0 := h.e0.symm

end Family

section Rec

end Rec

section FamPt

open Formalism.MainNotions

variable {eps : ℝ} (Fm : FamP eps) {x : ℝ} (hx : Fm.x1 < x) (i : Fm.Ix x) {Del h0 : ℕ}

@[reducible] def plOfFam (Lv : Arith.Lev (Arith.datumOf (Fm.D x i) (Fm.L x i) Del h0)) (sd : (Fm.D x i).what₂.LL) :
    PlDat (Fm.D x i).what₂.LL (Fm.D x i).what₂.Word :=
  ⟨Arith.datumOf (Fm.D x i) (Fm.L x i) Del h0, Arith.cstOf Fm, Lv, sd, fun u => (Fm.D x i).s.letter u⟩

variable {Lv : Arith.Lev (Arith.datumOf (Fm.D x i) (Fm.L x i) Del h0)} {sd : (Fm.D x i).what₂.LL}

end FamPt

section Tied

open Formalism.MainNotions Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LHost

end Tied

section Conc

end Conc

section Dat

end Dat

section ConcNum

open Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain2

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

namespace GlobTied

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R} {num : ScNum} {G : Glob} {TT : Finset H}
  {a : H → ℝ} {w : Fin R.m → E0 × H → ℝ} (T : GlobTied W num G TT a w)

include T

theorem f_eq : X.f = (PhiSet (H := H)).card := by
  unfold Fields.f
  rw [Fintype.card_congr T.σ, Fintype.card_coe]

end GlobTied

end ConcNum

end Formalism.L2.GlobalTheoryTheory.FamCol

end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.PlacesMin
section
open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Places

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.HN Formalism.LFunctionChainParameters

theorem level_prime_division_of_statements {eps : ℝ} (Fm : FamP eps) (crystallineComparison : ℝ) (h10 : product_first_zeroth_parts.ConclusionOnFamily Fm crystallineComparison) (tSet : SettingEventually Fm) (hTu : TuSize Fm) :
    LocalQuadraticParts.LevelTFamily Fm := by
  obtain ⟨x0, h0⟩ := h10
  obtain ⟨x1, h1⟩ := tSet
  refine J.family_levelPrime_summary_closed Fm crystallineComparison hTu (dlSize eps Fm) ⟨max (max x0 x1) (Fm.x1 + 1), fun x hx i => ?_⟩
  have hx0 : x0 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx1 : x1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx2 : Fm.x1 < x := by
    have := le_trans (le_max_right _ _) hx
    linarith
  exact ⟨fun u => (h0 x hx0 i u (h1 x hx1 hx2 i u)).2.1, fun u => (h0 x hx0 i u (h1 x hx1 hx2 i u)).2.2.2.2.1⟩

theorem placesF_min' {eps : ℝ} (Fm : FamP eps) (h26 : LocalQuadraticParts.LevelTFamily Fm) (hNC : Lnk.NuCommensF Fm) (hTu : TuSize Fm)
    (hRank : J.MuRank Fm) (lG : LinkG Fm) (lMu : LinkMu Fm) : Lnk.PlacesF Fm := by
  have heps := Lnk.fam_eps_pos Fm
  obtain ⟨xNC, hNC⟩ := hNC
  obtain ⟨CT, xT, δ, hδ, hTa⟩ := G.TopChoiceBounds.tau_sum_family_of_mertens Fm (fun _ _ => mertens)
  obtain ⟨C26, x26, h26⟩ := h26
  obtain ⟨CMu, xMu, hMu⟩ := lMu
  obtain ⟨CG, xG, δG, -, hG⟩ := lG
  obtain ⟨xR, hRank⟩ := hRank
  obtain ⟨xU, hTu⟩ := hTu
  obtain ⟨xE, hE⟩ := Lnk.ev_pow_le_exp 1 eps 9 one_pos heps
  obtain ⟨xM, hM⟩ := flipTwoThree.le_rpow_for_large_x ((2 : ℝ) / 5) (by norm_num) 6
  obtain ⟨xD, hD⟩ : ∃ xD : ℝ, ∀ x ≥ xD, δ x ≤ 1 :=
    Filter.eventually_atTop.1 (hδ.eventually (Iic_mem_nhds zero_lt_one))
  refine ⟨max (max C26 CMu) 4,
    |xNC| + |xT| + |x26| + |xMu| + |xG| + |xR| + |xU| + |xE| + |xM| + |xD| + |Fm.x1| + 4 * |CT| + 5,
    le_max_right _ _, fun x hx i => ?_⟩
  have n1 := abs_nonneg xNC
  have n2 := abs_nonneg xT
  have n3 := abs_nonneg x26
  have n4 := abs_nonneg xMu
  have n5 := abs_nonneg xG
  have n6 := abs_nonneg xR
  have n7 := abs_nonneg xU
  have n8 := abs_nonneg xE
  have n9 := abs_nonneg xM
  have n10 := abs_nonneg xD
  have n11 := abs_nonneg Fm.x1
  have n12 := abs_nonneg CT
  have e1 : x ≥ xNC := by linarith [le_abs_self xNC]
  have e2 : x ≥ xT := by linarith [le_abs_self xT]
  have e3 : x ≥ x26 := by linarith [le_abs_self x26]
  have e4 : x ≥ xMu := by linarith [le_abs_self xMu]
  have e5 : x ≥ xG := by linarith [le_abs_self xG]
  have e6 : x ≥ xR := by linarith [le_abs_self xR]
  have e7 : x ≥ xU := by linarith [le_abs_self xU]
  have e8 : x ≥ xE := by linarith [le_abs_self xE]
  have e9 : xM ≤ x := by linarith [le_abs_self xM]
  have e10 : x ≥ xD := by linarith [le_abs_self xD]
  have hx1 : Fm.x1 < x := by linarith [le_abs_self Fm.x1]
  have hx5 : 5 ≤ x := by linarith
  have hxC : 4 * |CT| + 1 ≤ x := by linarith
  have hsx : (Fm.L x i).sc.x = x := Fm.L_x x i hx1
  have hse : (Fm.L x i).sc.eps = eps := Fm.L_eps x i
  have S := Fm.sizes x hx1 i
  have hb9 : (Fm.L x i).sc.x ^ 9 ≤ (Fm.L x i).sc.b := by
    have h := hE x e8 (by linarith)
    rw [one_mul] at h
    unfold Scale.b Scale.L
    rw [hsx, hse, ← Real.rpow_natCast x 9]
    exact_mod_cast h
  have hx5' : 5 ≤ (Fm.L x i).sc.x := by rw [hsx]; exact hx5
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9⟩ := sizes_at (Fm.L x i) S hx5' hb9
  have hb1 : 1 ≤ (Fm.L x i).sc.b := by linarith
  have hm6 : (6 : ℝ) ≤ ((Fm.D x i).R.m : ℝ) := by
    have z1 := (flipTwoThree.size_bounds_of_scale (Fm.L x i) S (by linarith)).1
    rw [hsx] at z1
    exact le_trans (hM x e9) z1
  have hTb : ∀ u, (Fm.L x i).sc.b ^ 3 ≤ (((Fm.D x i).mem u).A.T : ℝ) := by
    intro u
    refine le_trans ?_ ((hTu x e7 i).1 u)
    rw [← Real.rpow_natCast (Fm.L x i).sc.b 3]
    refine Real.rpow_le_rpow_of_exponent_le hb1 ?_
    push_cast
    linarith
  have hXT : ∀ u, (Fm.L x i).sc.X' ≤ (((Fm.D x i).mem u).A.T : ℝ) := by
    intro u
    have h3 : (Fm.L x i).sc.b ≤ (Fm.L x i).sc.b ^ 3 := by
      have : (Fm.L x i).sc.b ^ 3 = (Fm.L x i).sc.b * (Fm.L x i).sc.b ^ 2 := by ring
      rw [this]
      have h2 : (1 : ℝ) ≤ (Fm.L x i).sc.b ^ 2 := one_le_pow₀ hb1
      nlinarith
    linarith [hTb u]
  have hsz := fun u => size_alt ((Fm.D x i).R.f : ℝ) (Fm.L x i).sc.b (((Fm.D x i).mem u).A.T : ℝ)
    (Nat.cast_nonneg _) s8 s9 (hTb u)
  have hfill := Fm.fills x hx1 i
  refine ⟨Lnk.IOsum_nonneg (Fm.Gx x i) Fm.GK Fm.GK_nonneg (Fm.ex x hx1 i).kapI_def
    (fun w => (hfill w).2.2.2.2.2.1), ?_⟩
  refine places_at_of C26 CMu _ (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_trans (le_max_right _ _) (le_max_left _ _)) (Fm.nprimeDef x hx1 i) (Fm.nuDef x hx1 i) (hNC x e1 i)
    (hRank x e6 i) (h26 x e3 i) (hMu x e4 i)
    (fun u w hw => ⟨((hG x e5 i).1 u w hw).1, ((hG x e5 i).1 u w hw).2.1⟩)
    (fun w => by rw [(hfill w).2.2.2.2.1]; exact exists_tau_eq_natCast _ _ _ _ _)
    (fun w => by
      rw [(hfill w).2.2.2.2.2.1]
      exact Lnk.ioP_nonneg (Fm.Gx x i) Fm.GK Fm.GK_nonneg (Fm.ex x hx1 i).kapI_def _ _ _)
    (fun u w hw => by
      rw [(hfill w).2.2.2.2.1, hw]
      exact tau_eq_zero_of_le _ _ _ _ _ (hXT u))
    (fun u w hs => ?_)
    (ta_le (Fm.L x i) S hx5' hb9 CT (δ x) (by rw [hsx]; exact hxC) (hD x e10) (hTa x e2 i))
    (fun u => (hsz u).1) (fun u => (hsz u).2.1) (fun u => (hsz u).2.2)
  by_cases hw : (Fm.D x i).what₂.places.resChar w = ((Fm.D x i).mem u).A.T
  · exact Or.inl (lenLoc_atT_zero (Fm.ex x hx1 i).lat.atT (Fm.ex x hx1 i).err.edef u w hw hs)
  · refine Or.inr (Fm.lats0 x hx1 i w u (VV_empty_of_ge _ _ _ _ _ ?_) hw)
    have h1 : ¬ ((((Fm.D x i).what₂.places.resChar w : ℕ) : ℝ) ≤ (Fm.L x i).sc.X'' (Fm.D x i).R.n) :=
      fun h => hs (Fm.supp_sat x hx1 i w h)
    linarith [not_le.1 h1]

theorem placesF_of_via_min : PlaceConditionsFamily := by
  exact placesF_of

end Formalism.L2.GlobalTheoryTheory.Places

end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.VandNHcSeqEq
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.ColOpen

open Formalism.BasicNotions Formalism.L2.Col Formalism.LogVandermondeBounds.StandardLattice Formalism.HermitianLattices.FormalDegreeBoundsAlt Formalism.HermitianLatticesTheory Finset

variable {X : Fields} {Pr : Primes X} {R : Ranks}

theorem k_ge (R : Ranks) : 5 ≤ R.k := by
  have h1 := R.m_add_three_le_k
  have h2 := R.two_le_m
  omega

theorem one_lt_L (sc : Scale) : 1 < sc.L := Real.one_lt_rpow sc.one_lt_alt sc.eps_pos

section Shape

variable {W : Wts X Pr.Word R} {Δ S : ℝ} {c : X.Tau → ℝ} {code : Pr.Word → ℕ → ℕ}

theorem hcSeq_eq_colU (G : Grid W Δ S c code) (u : Pr.Word) (τ : X.Tau) {i : ℕ} (hi : i < R.k) :
    hcSeq W u τ i = colU R.k (c τ) Δ (code u) (hcSeq W u τ 0) (hcSeq W u τ (R.k - 1)) i := by
  unfold colU
  by_cases h0 : i = 0
  · rw [if_pos h0, h0]
  · rw [if_neg h0]
    by_cases h1 : i = R.k - 1
    · rw [if_pos h1, h1]
    · rw [if_neg h1]
      have hl : i - 1 < R.k - 2 := by omega
      have h2 := G.word u τ (i - 1) hl
      rw [show i - 1 + 1 = i by omega, G.cloud τ (i - 1) (by omega)] at h2
      rw [h2]
      rfl

theorem vandN_hcSeq_eq (G : Grid W Δ S c code) (u : Pr.Word) (τ : X.Tau) :
    vandN (hcSeq W u τ) R.k = vandN (colU R.k (c τ) Δ (code u) (hcSeq W u τ 0) (hcSeq W u τ (R.k - 1))) R.k :=
  Formalism.LogVandermondeBounds.StandardLattice.vandN_congr _ _ _ fun _ hi => hcSeq_eq_colU G u τ hi

theorem hcSeq_zero (W : Wts X Pr.Word R) (u : Pr.Word) (τ : X.Tau) :
    hcSeq W u τ 0 = (W.aTop u τ : ℝ) + ((R.k : ℝ) - 1) / 2 := by
  have h := aTop_eq_hc W u τ
  have hk := k_ge R
  unfold hcSeq
  rw [dif_pos (by omega)]
  exact h

theorem hcSeq_last (W : Wts X Pr.Word R) (u : Pr.Word) (τ : X.Tau) :
    hcSeq W u τ (R.k - 1) = -(W.bTop u τ : ℝ) - ((R.k : ℝ) - 1) / 2 := by
  have h := bTop_eq_hc W u τ
  have hk := k_ge R
  unfold hcSeq
  rw [dif_pos (by omega)]
  exact h

theorem hcSeq_zero_eq (hW : W.Ok) (u u' : Pr.Word) (τ : X.Tau) : hcSeq W u τ 0 = hcSeq W u' τ 0 := by
  have hk := k_ge R
  unfold hcSeq
  rw [dif_pos (by omega), dif_pos (by omega), hW.u_first u u' τ (by omega)]

theorem hcSeq_last_eq (hW : W.Ok) (u u' : Pr.Word) (τ : X.Tau) : hcSeq W u τ (R.k - 1) = hcSeq W u' τ (R.k - 1) := by
  have hk := k_ge R
  unfold hcSeq
  rw [dif_pos (by omega), dif_pos (by omega), hW.u_last u u' τ (by omega)]

end Shape

end Formalism.L2.GlobalTheoryTheory.ColOpen
end
end

