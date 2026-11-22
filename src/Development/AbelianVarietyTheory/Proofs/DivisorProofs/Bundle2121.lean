import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2087
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPrimeIdemOfInert
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0155
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0471
import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2105
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0291
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2097
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2095
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2098
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2091
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2099
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesSecond
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2100
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2068

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalElementsCommuteDistinctFinitePlaces
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LocComm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem ext_cmp {z₁ z₂ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E}
    (h : ∀ w, GlobalTheory.HeckeRowsCompare.cmp D w z₁ = GlobalTheory.HeckeRowsCompare.cmp D w z₂) : z₁ = z₂ := by
  refine (Algebra.TensorProduct.basis (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) (Module.finBasis D.host.F D.host.E)).ext_elem fun i => ?_
  refine FiniteAdeleRing.ext _ fun w => ?_
  have e := congrArg (fun z => (Algebra.TensorProduct.basis (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F w)
    (Module.finBasis D.host.F D.host.E)).repr z i) (h w)
  simp only [GlobalTheory.HeckeRowsCompare.cmp, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at e
  rw [GlobalTheory.HeckeRowsCompare.repr_map, GlobalTheory.HeckeRowsCompare.repr_map] at e
  exact e

theorem mul_comm_of_locAt (V : Formalism.BasicNotions.TH.HSp D) {v v' : HeightOneSpectrum (𝓞 D.host.F)} (hv : v ≠ v') {x y : Bridge.Gf V}
    (hx : GlobalTheory.IndefiniteRowSideFullHecke.HeckeIntertwinersInert.LocAt V v x) (hy : GlobalTheory.IndefiniteRowSideFullHecke.HeckeIntertwinersInert.LocAt V v' y) : x * y = y * x := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  apply ext_cmp
  intro w
  have hm : ∀ a b : Bridge.Gf V,
      GlobalTheory.HeckeRowsCompare.cmp D w ((a * b : Bridge.Gf V).1.1 i j) =
        ((a.1.1.map (GlobalTheory.HeckeRowsCompare.cmp D w)) * (b.1.1.map (GlobalTheory.HeckeRowsCompare.cmp D w))) i j := by
    intro a b
    rw [← Matrix.map_mul]
    rfl
  show GlobalTheory.HeckeRowsCompare.cmp D w ((x * y : Bridge.Gf V).1.1 i j) = GlobalTheory.HeckeRowsCompare.cmp D w ((y * x : Bridge.Gf V).1.1 i j)
  rw [hm, hm]
  by_cases hw : w = v
  · subst hw
    have h1 : y.1.1.map (GlobalTheory.HeckeRowsCompare.cmp D w) = 1 := hy w hv
    rw [h1, mul_one, one_mul]
  · have h1 : x.1.1.map (GlobalTheory.HeckeRowsCompare.cmp D w) = 1 := hx w hw
    rw [h1, mul_one, one_mul]

theorem mul_comm_of_isLocEnv : ∀ {D : D7} (V : Formalism.BasicNotions.TH.HSp D) {Pl0 : Type} (pl : Pl0 → Pl D.host.E) (ok : Set Pl0) (i i' : ok × ℕ)
    (x y : Bridge.Gf V), (pl i.1).under (𝓞 D.host.F) ≠ (pl i'.1).under (𝓞 D.host.F) → isLocEnv V pl ok i x →
      isLocEnv V pl ok i' y → x * y = y * x := by
  intro D V Pl0 pl ok i i' x y hv hx hy
  exact mul_comm_of_locAt V hv
    (GlobalTheory.Mem.R3.LiftInertChi.locAt_of_isLocElt V _ x ((GlobalTheory.Hk3Split.isLabElt_of_isTEnv V pl ok i x).2.1 hx))
    (GlobalTheory.Mem.R3.LiftInertChi.locAt_of_isLocElt V _ y ((GlobalTheory.Hk3Split.isLabElt_of_isTEnv V pl ok i' y).2.1 hy))

end GlobalTheory.LocComm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCmConstantAddLogDerivativeLeSquareTopBound
section
open GlobalTheory.SqTop GlobalTheory.FunObj.SqNum GlobalTheory.CMVal

noncomputable section

namespace GlobalTheory.SizesArch

open Formalism.BasicNotions NumberField

theorem log_gamma_nat_le (n : ℕ) (hn : 1 ≤ n) : Real.log (Real.Gamma n) ≤ n * Real.log n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hg : Real.Gamma ((m + 1 : ℕ) : ℝ) = (m.factorial : ℝ) := by
    rw [Nat.cast_succ, Real.Gamma_nat_eq_factorial]
  have hf : (m.factorial : ℝ) ≤ ((m + 1 : ℕ) : ℝ) ^ (m + 1) := by
    have h1 : m.factorial ≤ (m + 1) ^ (m + 1) :=
      (Nat.factorial_le_pow m).trans ((Nat.pow_le_pow_left (Nat.le_succ m) m).trans
        (Nat.pow_le_pow_right (Nat.succ_pos m) (Nat.le_succ m)))
    exact_mod_cast h1
  rw [hg, ← Real.log_pow]
  exact Real.log_le_log (by exact_mod_cast Nat.factorial_pos m) hf

theorem log_cmConst_le {Φ : Type} [Fintype Φ] (dF d : ℝ) (k : ℕ) (κ : Φ → ℕ) (hdF : 0 < dF) (hd : 1 ≤ d)
    (hk : 1 ≤ k) :
    Real.log (Formalism.PairingDivisionLocalBalance.cmConst dF d k κ) ≤ (((k : ℝ) - 1) / 2) * Real.log dF +
      ∑ τ, Real.log (Real.Gamma ((k : ℝ) + κ τ)) + (Formalism.PairingDivisionLocalBalance.absK κ : ℝ) * 8 := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hG : ∀ τ, 0 < Real.Gamma ((k : ℝ) + κ τ) := fun τ =>
    Real.Gamma_pos_of_pos (by have : (0 : ℝ) ≤ κ τ := Nat.cast_nonneg _; linarith)
  have hsd : 1 ≤ Real.sqrt d := by rw [Real.one_le_sqrt]; exact hd
  have hq : 0 < 2 * Real.pi / Real.sqrt d := div_pos (by positivity) (by linarith)
  unfold Formalism.PairingDivisionLocalBalance.cmConst
  rw [Real.log_mul (mul_ne_zero (Real.rpow_pos_of_pos hdF _).ne' (Finset.prod_ne_zero_iff.2 fun τ _ => (hG τ).ne'))
      (pow_ne_zero _ hq.ne'),
    Real.log_mul (Real.rpow_pos_of_pos hdF _).ne' (Finset.prod_ne_zero_iff.2 fun τ _ => (hG τ).ne'),
    Real.log_rpow hdF, Real.log_prod (fun τ _ => (hG τ).ne'), Real.log_pow]
  have h1 : Real.log (2 * Real.pi / Real.sqrt d) ≤ 8 := by
    have h3 := Real.log_le_sub_one_of_pos hq
    have h2 : 2 * Real.pi / Real.sqrt d ≤ 2 * Real.pi := div_le_self (by positivity) hsd
    linarith [Real.pi_le_four]
  have h0 : (0 : ℝ) ≤ Formalism.PairingDivisionLocalBalance.absK κ := Nat.cast_nonneg _
  have := mul_le_mul_of_nonneg_left h1 h0
  linarith

end GlobalTheory.SizesArch

namespace GlobalTheory.SizesArch

open Formalism.BasicNotions NumberField GlobalTheory.ChiGrid

theorem sizes : ∀ ε : ℝ, ∃ Cx x₁ : ℝ, ∀ (D : Formalism.BasicNotions.D7) (large₂ : Formalism.BasicNotions.SizeData₂ D), large₂.sc.eps = ε → x₁ ≤ large₂.sc.x →
    Rec large₂ → ∀ (i j : Fin D.R.m) (s : ℕ), 1 ≤ s → s ≤ halfRank D i j →
      Real.log (C0 D.host.E D.host.d (2 * s) (kap D 1 i j s)) +
        (Formalism.PairingDivisionLocalBalance.wtM (2 * s) (kap D 1 i j s) : ℝ) * ((Real.log D.host.d + |large₂.logDerivativeAtOne|) / 2) ≤
        bTH D Cx large₂.sc.x large₂.sc.b := by
  intro ε
  refine ⟨200, 0, fun D large₂ _ _ hR i j s hs1 hs2 => ?_⟩
  obtain ⟨-, -, hm4, hm, -, hmfNd, -, -, -, hrd1, hrd2, -, -, -⟩ := hR.size
  obtain ⟨hgb, hb675⟩ := GlobalTheory.BigTop.Fun.gap_le_b hR.size
  have hbL : Real.log large₂.sc.b = large₂.sc.L := by unfold Scale.b; exact Real.log_exp _
  have hL1 : 1 ≤ large₂.sc.L := by
    rw [← hbL, Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hx1 : 1 < large₂.sc.x := large₂.sc.one_lt_alt
  have hlogx : 0 ≤ Real.log large₂.sc.x := Real.log_nonneg hx1.le
  have hcard : Fintype.card D.what₂.Tau = D.R.f := Formalism.MainNotions.Lnk.card_Tau D
  have hf1n : 1 ≤ D.R.f := by
    have : 1 ≤ D.R.m ^ 4 := Nat.one_le_pow _ _ (by omega)
    omega
  have hf1 : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf1n

  have hsb : (s : ℝ) ≤ large₂.sc.b := by
    have h1 := GlobalTheory.BigTop.Fun.rankV_lt_gap (D := D) i.2 j.2
    have e := (ranks_exact D i j).2.2
    have h3 : rankV D i j ≤ rankV D (i + 1) (j + 1) := by unfold rankV; gcongr <;> omega
    have : s ≤ gap D 1 := by omega
    exact (by exact_mod_cast this : (s : ℝ) ≤ gap D 1).trans hgb

  have hκ : ∀ τ, (kap D 1 i j s τ : ℝ) ≤ 5 * large₂.sc.b := by
    intro τ
    obtain ⟨e0, e1⟩ := GlobalTheory.BigTop.Fun.numE_bounds hR.size τ j.2
    obtain ⟨c0, c1⟩ := GlobalTheory.BigTop.Fun.cen_bounds hR.size τ (i := D.R.m - i) (by omega) (by omega)
    have h : (kap D 1 i j s τ : ℤ) ≤ (num D 1 τ).e (j + 1) + cen D 1 τ (D.R.m - i) := by
      unfold kap; omega
    have h' : ((kap D 1 i j s τ : ℤ) : ℝ) ≤ ((num D 1 τ).e (j + 1) : ℝ) + (cen D 1 τ (D.R.m - i) : ℝ) := by
      exact_mod_cast h
    push_cast at h'
    linarith

  have hN1 : 1 ≤ D.R.N D.R.m := by unfold Ranks.N; have := D.R.m_add_three_le_k; omega
  have hd1 : (1 : ℝ) ≤ D.host.d := by exact_mod_cast D.host.hyp.2.1.one_lt.le
  have hdb : (D.host.d : ℝ) ≤ large₂.sc.b := by
    have hm1 : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (show 1 ≤ D.R.m by omega)
    have hN : (1 : ℝ) ≤ (D.R.N D.R.m : ℝ) := by exact_mod_cast hN1
    have h1 : (1 : ℝ) ≤ (D.R.m : ℝ) * D.R.f * (D.R.N D.R.m : ℝ) ^ 2 :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hm1 hf1) (one_le_pow₀ hN)
    exact (le_mul_of_one_le_left (by linarith) h1).trans hmfNd
  have hlogd : Real.log D.host.d ≤ large₂.sc.L := hbL ▸ Real.log_le_log (by linarith) hdb
  have hlogd0 : 0 ≤ Real.log D.host.d := Real.log_nonneg hd1
  have hdl : |large₂.logDerivativeAtOne| ≤ large₂.sc.L := hR.dlog

  have hdF : |(discr (maximalRealSubfield D.host.E) : ℝ)| = (2 * D.host.v) ^ D.R.f := by
    rw [← hR.hF]; exact GlobalTheory.CovDom.NormConst.abs_discr_F D
  have h2v : 2 * D.host.v = D.host.rdE := by show 2 * (D.host.rdE / 2) = D.host.rdE; ring
  have hdF0 : 0 < |(discr (maximalRealSubfield D.host.E) : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero _)
  have hlogdF : Real.log |(discr (maximalRealSubfield D.host.E) : ℝ)| ≤ (D.R.f : ℝ) * large₂.sc.L := by
    rw [hdF, Real.log_pow, h2v]
    have : Real.log D.host.rdE ≤ large₂.sc.L := by linarith
    exact mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)

  have hC := log_cmConst_le |(discr (maximalRealSubfield D.host.E) : ℝ)| (D.host.d : ℝ) (2 * s) (kap D 1 i j s) hdF0 hd1
    (by omega)
  have hC0 : C0 D.host.E D.host.d (2 * s) (kap D 1 i j s) =
      Formalism.PairingDivisionLocalBalance.cmConst |(discr (maximalRealSubfield D.host.E) : ℝ)| (D.host.d : ℝ) (2 * s) (kap D 1 i j s) := rfl
  rw [hC0]
  set b := large₂.sc.b
  set L := large₂.sc.L
  set F : ℝ := (D.R.f : ℝ) with hF
  have hb0 : 0 ≤ b := by linarith
  have hk : ((2 * s : ℕ) : ℝ) ≤ 2 * b := by push_cast; linarith
  have hk1 : (1 : ℝ) ≤ ((2 * s : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ 2 * s by omega)

  have T1 : (((2 * s : ℕ) : ℝ) - 1) / 2 * Real.log |(discr (maximalRealSubfield D.host.E) : ℝ)| ≤ 2 * (F * b * L) := by
    have a1 : 0 ≤ (((2 * s : ℕ) : ℝ) - 1) / 2 := by linarith
    have a2 := mul_le_mul_of_nonneg_left hlogdF a1
    have a3 : (((2 * s : ℕ) : ℝ) - 1) / 2 ≤ b := by linarith
    have a4 : 0 ≤ F * L := by positivity
    have a5 := mul_le_mul_of_nonneg_right a3 a4
    nlinarith

  have T2 : ∑ τ, Real.log (Real.Gamma (((2 * s : ℕ) : ℝ) + kap D 1 i j s τ)) ≤ 49 * (F * b * L) := by
    have each : ∀ τ, Real.log (Real.Gamma (((2 * s : ℕ) : ℝ) + kap D 1 i j s τ)) ≤ 49 * (b * L) := by
      intro τ
      have e : ((2 * s : ℕ) : ℝ) + kap D 1 i j s τ = ((2 * s + kap D 1 i j s τ : ℕ) : ℝ) := by push_cast; ring
      rw [e]
      have hn1 : 1 ≤ 2 * s + kap D 1 i j s τ := by omega
      refine (log_gamma_nat_le _ hn1).trans ?_
      have hn : ((2 * s + kap D 1 i j s τ : ℕ) : ℝ) ≤ 7 * b := by push_cast; linarith [hκ τ]
      have hn0 : (1 : ℝ) ≤ ((2 * s + kap D 1 i j s τ : ℕ) : ℝ) := by exact_mod_cast hn1
      have hl0 : 0 ≤ Real.log ((2 * s + kap D 1 i j s τ : ℕ) : ℝ) := Real.log_nonneg hn0
      have hl : Real.log ((2 * s + kap D 1 i j s τ : ℕ) : ℝ) ≤ 7 * L := by
        have l1 := Real.log_le_log (by linarith) hn
        rw [Real.log_mul (by norm_num) (by linarith), hbL] at l1
        have l2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 7 by norm_num)
        linarith
      have := mul_le_mul hn hl hl0 (by linarith)
      linarith
    refine (Finset.sum_le_sum fun τ _ => each τ).trans ?_
    rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
    linarith

  have hsumκ : (Formalism.PairingDivisionLocalBalance.absK (kap D 1 i j s) : ℝ) ≤ 5 * (F * b) := by
    unfold Formalism.PairingDivisionLocalBalance.absK
    push_cast
    refine (Finset.sum_le_sum fun τ _ => hκ τ).trans ?_
    rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
    linarith
  have hsumκ0 : (0 : ℝ) ≤ Formalism.PairingDivisionLocalBalance.absK (kap D 1 i j s) := Nat.cast_nonneg _
  have T3 : (Formalism.PairingDivisionLocalBalance.absK (kap D 1 i j s) : ℝ) * 8 ≤ 40 * (F * b * L) := by
    have : F * b ≤ F * b * L := le_mul_of_one_le_right (by positivity) hL1
    linarith

  have hM : (Formalism.PairingDivisionLocalBalance.wtM (2 * s) (kap D 1 i j s) : ℝ) ≤ 12 * (F * b) := by
    unfold Formalism.PairingDivisionLocalBalance.wtM
    push_cast
    rw [hcard]
    have : (2 * (s : ℝ)) * F ≤ 2 * b * F := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    push_cast at hsumκ
    linarith
  have T4 : (Formalism.PairingDivisionLocalBalance.wtM (2 * s) (kap D 1 i j s) : ℝ) * ((Real.log D.host.d + |large₂.logDerivativeAtOne|) / 2) ≤ 12 * (F * b * L) := by
    have a1 : (Real.log D.host.d + |large₂.logDerivativeAtOne|) / 2 ≤ L := by linarith
    have a2 : 0 ≤ (Real.log D.host.d + |large₂.logDerivativeAtOne|) / 2 := by positivity
    have := mul_le_mul hM a1 a2 (by positivity)
    linarith
  have hfin : 0 ≤ F * b * Real.log large₂.sc.x := by positivity
  unfold bTH
  rw [hbL]
  have e : 200 * (D.R.f : ℝ) * b * (L + Real.log large₂.sc.x) = 200 * (F * b * L) + 200 * (F * b * Real.log large₂.sc.x) := by
    rw [hF]; ring
  rw [e]
  have hP : 0 ≤ F * b * L := by positivity
  linarith

end GlobalTheory.SizesArch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerRankCuspFormsDetWeightOneComponent
section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

theorem GlobalTheory.ShareOn.lowerRank_oneComponent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : DataX E r) (Xa : ArchInM X.toData) (Fl : FlatM X.toData Xa), GlobalTheory.Shares.Margins X.toData Xa → 0 < X.p0 → X.p0 < r → GapsGe X.p0 Xa.L 1 → PairGe Xa.L (1.9 * Xa.T) → GapsGe X.p0 (Xa.Fp - kLog X.Ψ r - (nd X.toData + 2) • Xa.L) 0 → PairGe (Xa.Fp - kLog X.Ψ r - (nd X.toData + 2) • Xa.L) 1 → ∀ s : ℕ, Even s → s ≤ Xa.T → ∀ u : Frame X.Ψ r → ℂ, u ∈ X.SS (deMul X.Ψ r X.p0 s) → (∃ x ∈ X.dom, u x ≠ 0) → ∃ g : Fin (Fl.δ * (Xa.T + nd X.toData).choose (nd X.toData)) → Frame X.Ψ r → ℂ, (∀ q, g q ∈ X.SS (Xa.Fp + Xa.T • Xa.L - deMul X.Ψ r X.p0 s)) ∧ ∀ a : _ → ℂ, (∀ x ∈ X.dom, ∑ q, a q * g q x = 0) → a = 0 := by
  intro E _ _ _ r X Xa Fl hM hp0 hp0r hg1 hp1 hg2 hp2 s hs hsT u hu hune
  classical
  have hF := GlobalTheory.T.loweredWeight_interpolation_at_points E r X Xa Fl hM hp0 hp0r hg1 hp1 hg2 hp2 s hs hsT u hu hune
  choose F hFd hFval hFss using hF
  set M := ReciprocityTheory.ChartRestriction.G.AR.multiLt (nd X.toData) (Xa.T + 1) with hM'
  have hMcard : M.card = (Xa.T + nd X.toData).choose (nd X.toData) := by
    have e : M = ReciprocityTheory.L2DbarEstimates.Y.multiLe (nd X.toData) Xa.T := by
      ext α
      rw [ReciprocityTheory.ChartRestriction.G.AR.mem_multiLt_iff, ReciprocityTheory.L2DbarEstimates.Y.mem_multiLe_iff]
      omega
    rw [e]
    exact ReciprocityTheory.L2DbarEstimates.Y.ind_count (nd X.toData) Xa.T
  set PM := (Finset.univ : Finset (Fin Fl.δ)) ×ˢ M with hPM
  have hcard : PM.card = Fl.δ * (Xa.T + nd X.toData).choose (nd X.toData) := by
    rw [Finset.card_product, Finset.card_univ, Fintype.card_fin, hMcard]
  let e := (Finset.equivFinOfCardEq hcard).symm
  let f : Fin Fl.δ → (Fin (nd X.toData) → ℕ) → Frame X.Ψ r → ℂ :=
    fun j α x => F j x * monoM X.toData Fl.s α x * Fl.w0 x ^ (Xa.T - ∑ q, α q)
  have hαT : ∀ α ∈ M, ∑ q, α q ≤ Xa.T := fun α hα => by
    rw [hM', ReciprocityTheory.ChartRestriction.G.AR.mem_multiLt_iff] at hα
    omega
  refine ⟨fun q => f (e q).1.1 (e q).1.2, fun q => ?_, fun a ha => ?_⟩
  · exact hFss _ _ (hαT _ (Finset.mem_product.mp (e q).2).2)
  · let cc : (Fin (nd X.toData) → ℕ) → Fin Fl.δ → ℂ := fun α j =>
      if h : (j, α) ∈ PM then a (e.symm ⟨(j, α), h⟩) else 0
    have hc : ∀ q, cc (e q).1.2 (e q).1.1 = a q := by
      intro q
      have h : ((e q).1.1, (e q).1.2) ∈ PM := (e q).2
      simp only [cc, dif_pos h]
      exact congrArg a (e.symm_apply_apply q)
    have hlead : ∀ x ∈ X.dom, leadM X.toData Fl.s Fl.w0 F Xa.T (Xa.T + 1) cc x = 0 := by
      intro x hx
      have h1 : leadM X.toData Fl.s Fl.w0 F Xa.T (Xa.T + 1) cc x =
          ∑ p ∈ PM, cc p.2 p.1 * f p.1 p.2 x := by
        unfold leadM
        rw [hPM, Finset.sum_product, Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun α _ => ?_
        simp only [f]
        ring
      rw [h1, ← Finset.sum_coe_sort PM, ← e.sum_comp]
      rw [← ha x hx]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [hc q]
    have h7 := GlobalTheory.T.leadingMonomialProducts_linearIndependent E r X.toData Xa Fl F hFd hFval Xa.T cc hlead
    funext q
    rw [← hc q]
    exact h7 _ (Finset.mem_product.mp (e q).2).2 _
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapEqOneOfIsLocEnv
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EvLocal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem map_eq_zero_of_repr {F A E R ι : Type} [Field F] [CommRing A] [CommRing E] [Algebra F A] [Algebra F E] [CommRing R]
    [Fintype ι] (b : Module.Basis ι F E) (φ : A ⊗[F] E →+* R) (z : A ⊗[F] E)
    (hc : ∀ i, φ (((Algebra.TensorProduct.basis A b).repr z i) ⊗ₜ[F] 1) = 0) : φ z = 0 := by
  have hs : z = ∑ i, ((Algebra.TensorProduct.basis A b).repr z i ⊗ₜ[F] (1 : E)) * ((1 : A) ⊗ₜ[F] b i) := by
    conv_lhs => rw [← (Algebra.TensorProduct.basis A b).sum_repr z]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.smul_tmul', smul_eq_mul,
      one_mul]
  rw [hs, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [map_mul, hc i, zero_mul]

theorem ev_eq_zero {D : D7} {l : ℕ} [Fact l.Prime] {inc : D.host.E →+* PadicAlgCl l}
    {ev : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E →+* PadicAlgCl l} (hev : EvOk inc ev)
    (z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)
    (hz : ∀ w : HeightOneSpectrum (𝓞 D.host.F), ((l : ℕ) : 𝓞 D.host.F) ∈ w.asIdeal → GlobalTheory.HeckeRowsCompare.cmp D w z = 0) :
    ev z = 0 := by
  refine map_eq_zero_of_repr (A := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) (Module.finBasis D.host.F D.host.E) ev z fun i => ?_
  refine hev.2.2.1 _ fun w hw => ?_
  have e := congrArg (fun z => (Algebra.TensorProduct.basis (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F w)
    (Module.finBasis D.host.F D.host.E)).repr z i) (hz w hw)
  simp only [GlobalTheory.HeckeRowsCompare.cmp, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at e
  rw [GlobalTheory.HeckeRowsCompare.repr_map, map_zero] at e
  exact e

theorem map_eq_one_of_isLocEnv : ∀ {D : D7} (V : Formalism.BasicNotions.TH.HSp D) {Pl0 : Type} (pl : Pl0 → Pl D.host.E) (ok : Set Pl0) (i : ok × ℕ) (x : Bridge.Gf V) {l : ℕ} [Fact l.Prime] (inc : D.host.E →+* PadicAlgCl l) (ev : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E →+* PadicAlgCl l), EvOk inc ev → ((l : ℕ) : 𝓞 D.host.E) ∉ (pl i.1.1).asIdeal → isLocEnv V pl ok i x → ((x : GL (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)).val).map ev = 1 := by
  intro D V Pl0 pl ok i x l _ inc ev hev hl hx
  have hloc : GlobalTheory.IndefiniteRowSideFullHecke.HeckeIntertwinersInert.LocAt V ((pl i.1).under (𝓞 D.host.F)) x :=
    GlobalTheory.Mem.R3.LiftInertChi.locAt_of_isLocElt V _ x ((GlobalTheory.Hk3Split.isLabElt_of_isTEnv V pl ok i x).2.1 hx)
  ext a b
  have h0 : ev (x.1.1 a b - (1 : Matrix (Fin V.rank) (Fin V.rank) _) a b) = 0 := by
    refine ev_eq_zero hev _ fun w hw => ?_
    have hne : w ≠ (pl i.1).under (𝓞 D.host.F) := by
      rintro rfl
      apply hl
      have h2 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (l : 𝓞 D.host.F) ∈ (pl i.1.1).asIdeal := hw
      rwa [map_natCast] at h2
    have h1 : x.1.1.map (GlobalTheory.HeckeRowsCompare.cmp D w) = 1 := hloc w hne
    have h3 := congrFun (congrFun h1 a) b
    rw [Matrix.map_apply] at h3
    rw [map_sub, h3, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [map_sub, sub_eq_zero] at h0
  rw [Matrix.map_apply]
  refine h0.trans ?_
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

end GlobalTheory.EvLocal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompletedPairLatticeIffFrameMatrixIntegralOnHStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_completedPairLattice_iff_frameMatrix_integral_on_half : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m), VStd D i → ∀ (Q : Finset (Pl D.host.E)), (∃ t, Q ⊆ R.Q t) → ∀ eQ : AE D, IsIdemSum eQ Q → ∀ x : WO (Vc D i) (Wc D i), IsHalf eQ x → (IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (x)) ↔ x ∈ lattice₂ R i) := by
  first | exact @GlobalTheory.HalfLatInt.isIntM_iff_mem_latP | exact GlobalTheory.HalfLatInt.isIntM_iff_mem_latP | (intros; apply GlobalTheory.HalfLatInt.isIntM_iff_mem_latP <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelCuspFormsSpan
section
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn GlobalTheory.ShareOn.Reading

set_option autoImplicit false

namespace GlobalTheory.ShareOn.Reading

section Onto
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem ss_transport {X X' : Data E r} (hX : X = X') {Ψ : Finset (E →+* ℂ)} (h1 : X.Ψ = Ψ) (h2 : X'.Ψ = Ψ)
    (g : Frame Ψ r → ℂ) (la : Wt Ψ r) (la' : Wt X'.Ψ r)
    (hla : ∀ τ (t1 : τ ∈ Ψ) (t2 : τ ∈ X'.Ψ) a, la ⟨τ, t1⟩ a = la' ⟨τ, t2⟩ a)
    (hg : (fun x => g (castFrame h1 x)) ∈ X.SS (castWt h1 la)) :
    (fun y => g (castFrame h2 y)) ∈ X'.SS la' := by
  subst hX
  have hw : castWt h1 la = la' := by
    funext τ a
    exact hla τ.1 _ τ.2 a
  rw [← hw]
  exact hg

end Onto

theorem rdFun_onto {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} {p : PtAt ex Csz}
    {r : TwoRuns p.T p.P.Gp} (h : RunsOk (fw2 p) r) {i : Fin D.R.m} {C : Type} [MulAction p.P.Gp C]
    {M : TwoLevels D.host.E D.R.r p.P.Gp C} {ka : Wt M.Ψ D.R.r} {v : HeightOneSpectrum (𝓞 D.what₂.LL)}
    {e : C ≃ ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).Comp}
    (ha : ∀ c, (M.comp c).toData = ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c))
    (hb : ∀ c τ (h1 : τ ∈ M.Ψ) (h2 : τ ∈ (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)).Ψ) a,
      ka ⟨τ, h1⟩ a = laR (r.used v).full.toTop ((i : ℕ) + 1) (p.κ i) (e c) ⟨τ, h2⟩ a) :
    0 < badN D → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → ∀ (G : C → Frame M.Ψ D.R.r → ℂ), G ∈ M.SS ka →
      ∃ (m : ℕ) (α : Fin m → ℂ) (Fs : Fin m → (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i)),
        ∀ c, ∀ x ∈ M.dom, G c x = ∑ k, α k * rdFun h ha (Fs k) c x := by
  intro hN hnV G hG
  classical
  have ha' : ∀ k, (M.comp (e.symm k)).toData = ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X k := fun k => by
    rw [ha (e.symm k), e.apply_symm_apply]
  have hΨk : ∀ k, M.Ψ = (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X k).Ψ := fun k => by
    rw [← ha' k]; exact (M.comp_Ψ _).symm
  have hb' : ∀ k τ (h1 : τ ∈ M.Ψ) (h2 : τ ∈ (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X k).Ψ) a,
      ka ⟨τ, h1⟩ a = laR (r.used v).full.toTop ((i : ℕ) + 1) (p.κ i) k ⟨τ, h2⟩ a := by
    intro k
    obtain ⟨c, rfl⟩ := e.surjective k
    exact hb c

  have hf : 0 < D.R.f := lt_of_lt_of_le (lt_of_le_of_lt (Nat.zero_le _) i.2) D.R.m_le_f
  have hTau : Nonempty D.what₂.Tau := by
    rw [← Fintype.card_pos_iff, D.what₂.card_Tau]; exact hf
  obtain ⟨τ0⟩ := hTau
  have hn : 8 * D.R.f * D.R.r + 4 ≤ (p.κ i).n := by
    rw [(p.fw.kap i τ0).2.2]; exact hnV
  have hOnto : RdOnto (h.laws v).p ((i : ℕ) + 1) (p.κ i) :=
    GlobalTheory.Shares.rdOnto_rec GlobalTheory.chartIndependence_unconditional D (r.used v).full.toTop (h.laws v).p ((i : ℕ) + 1)
      (GlobalTheory.OnTies.inR_succ i) (h.laws v).sh
      (GlobalTheory.RunIn.gamAt_of_lawsCore D _ (h.laws v).p.toLawsCore) hN
      (GlobalTheory.Dict.gram_xi_eq_of_lawsFull (h.laws v)) (p.κ i) hn
      (ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.lastPos_wtA (h.laws v).p (GlobalTheory.OnTies.inR_succ i) _ (lastPos_kappa p i))
  let f : ∀ k : ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).Comp, Frame (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X k).Ψ D.R.r → ℂ := fun k y => G (e.symm k) (castFrame (hΨk k).symm y)
  have hfm : ∀ k, f k ∈ (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X k).SS (laR (r.used v).full.toTop ((i : ℕ) + 1) (p.κ i) k) := fun k =>
    ss_transport (ha' k) (M.comp_Ψ (e.symm k)) (hΨk k).symm (G (e.symm k)) ka _ (hb' k) (hG (e.symm k))
  obtain ⟨m, α, Fs, -, hsum⟩ := hOnto f hfm
  refine ⟨m, α, Fs, fun c x hx => ?_⟩
  have hy := (mem_dom_iff ha c x).2 hx
  have key := hsum (e c) _ hy
  have hl : f (e c) (castFrame (psi_eq ha c) x) = G c x := by
    show G (e.symm (e c)) (castFrame (hΨk (e c)).symm (castFrame (psi_eq ha c) x)) = G c x
    have hc : e.symm (e c) = c := e.symm_apply_apply c
    have hx' : castFrame (hΨk (e c)).symm (castFrame (psi_eq ha c) x) = x := rfl
    rw [hx', hc]
  rw [← hl, key]
  rfl

end GlobalTheory.ShareOn.Reading
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NumericalPointOfSizeStatement
section
open GlobalTheory.RefSum GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.numerical_point_of_size : Size → NumPt := by
  first | exact @GlobalTheory.RefSum.NumSizes.numPt_of_size | exact GlobalTheory.RefSum.NumSizes.numPt_of_size | (intros; apply GlobalTheory.RefSum.NumSizes.numPt_of_size <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesSecondStatement
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oscillator_model_values_second : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.Char F → TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ∀ cc, CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.U ((i : ℕ) + 1) O.s0) O.dict O.mu (T.x₀ ((i : ℕ) + 1) O.s0) (R.ωP i A.μ0) (R.vacP i) cc → ∀ u : ℂ, O.EquivAt (κ i) (u • cc) := by
  first | exact @GlobalTheory.FrameConstMove.equivAt_of_ccIs | exact GlobalTheory.FrameConstMove.equivAt_of_ccIs | (intros; apply GlobalTheory.FrameConstMove.equivAt_of_ccIs <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParameterHeightLtGenusStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parameter_height_lt_genus : GlobalTheory.BigOn.AtPts fun Fm x _ i _ => ∀ (j : Fin (Fm.D x i).R.m) a, (GlobalTheory.ExpTie.parOf (Fm.L x i) j).h < ((Fm.D x i).host.g a : ℝ) := by
  first | exact @GlobalTheory.ExpTie.atPts_h_lt_g | exact GlobalTheory.ExpTie.atPts_h_lt_g | (intros; apply GlobalTheory.ExpTie.atPts_h_lt_g <;> assumption)
end

