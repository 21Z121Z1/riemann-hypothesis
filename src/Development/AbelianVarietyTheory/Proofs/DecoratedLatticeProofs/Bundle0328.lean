import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0010
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CollSBound
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0054
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DegenerateConstant
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.ExponentInequalityNondegenerateMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BilinearVacuumNonzeroCuspForm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0263
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0253
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0254
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0285
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0322
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0319
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0227
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0325
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0083
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0048

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CorankSumsBoundWithExpLoss
section
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Deg

theorem rpow_le_rpow_both {x y u w : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) (hu : 0 ≤ u) (huw : u ≤ w) :
    x ^ u ≤ y ^ w :=
  (Real.rpow_le_rpow_of_exponent_le hx huw).trans
    (Real.rpow_le_rpow (by linarith) hxy (hu.trans huw))

theorem bigH_one_le (C : ℝ) (hC : 0 ≤ C) (m f : ℕ) {b : ℝ} (hb : 1 ≤ b) :
    1 ≤ Formalism.HermitianLatticeCounting.LatticeSumBounds.bigH C m f b := by
  unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.bigH
  exact Real.one_le_rpow hb (by positivity)

theorem bigH_mono {C D : ℝ} (hC : 0 ≤ C) (hCD : C ≤ D) (m f : ℕ) {b : ℝ} (hb : 1 ≤ b) :
    Formalism.HermitianLatticeCounting.LatticeSumBounds.bigH C m f b ≤ Formalism.HermitianLatticeCounting.LatticeSumBounds.bigH D m f b := by
  unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.bigH
  apply Real.rpow_le_rpow_of_exponent_le hb
  have : (0:ℝ) ≤ (m:ℝ)^2 * f := by positivity
  nlinarith

end GlobalTheory.Core.Deg

namespace GlobalTheory.Core.Deg

open Formalism.HermitianLatticeCounting.LatticeSumBounds in
theorem xiHyp_mono {C D : ℝ} (hC : 1 ≤ C) (hCD : C ≤ D) {k m f : ℕ} {b v NT : ℝ} {Xi : ℕ → ℝ}
    (hb : 1 ≤ b) (hNT : 1 ≤ NT) (h : XiHyp C k m f b v NT Xi) : XiHyp D k m f b v NT Xi := by
  have hC0 : (0:ℝ) ≤ C := by linarith
  have hD0 : (0:ℝ) ≤ D := by linarith
  have hH1 := bigH_one_le C hC0 m f hb
  have hHD1 := bigH_one_le D hD0 m f hb
  have hHm := bigH_mono hC0 hCD m f hb
  refine ⟨fun s hs hsk => ?_, fun s hs => ?_⟩
  · obtain ⟨h0, h1⟩ := h.1 s hs hsk
    refine ⟨h0, h1.trans ?_⟩
    have e1 : bigH C m f b ^ C ≤ bigH D m f b ^ D := rpow_le_rpow_both hH1 hHm hC0 hCD
    have e2 : C ^ (s * k * f) ≤ D ^ (s * k * f) := pow_le_pow_left₀ hC0 hCD _
    exact mul_le_mul e1 e2 (by positivity) (by positivity)
  · obtain ⟨h0, h1⟩ := h.2 s hs
    refine ⟨h0, h1.trans ?_⟩
    have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
    have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg m
    have e1 : (C * k) ^ (k * f) ≤ (D * k) ^ (k * f) :=
      pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hCD hk0) _
    have a1 : 1 ≤ bigH C m f b ^ (C * m) := Real.one_le_rpow hH1 (by positivity)
    have a2 : bigH C m f b ^ (C * m) ≤ bigH D m f b ^ (D * m) :=
      rpow_le_rpow_both hH1 hHm (by positivity) (mul_le_mul_of_nonneg_right hCD hm0)
    have e2 : (bigH C m f b ^ (C * m) * NT) ^ (C * k) ≤ (bigH D m f b ^ (D * m) * NT) ^ (D * k) := by
      apply rpow_le_rpow_both
      · nlinarith
      · exact mul_le_mul_of_nonneg_right a2 (by linarith)
      · positivity
      · exact mul_le_mul_of_nonneg_right hCD hk0
    exact mul_le_mul e1 e2 (by positivity) (by positivity)

open Formalism.HermitianLatticeCounting.LatticeSumBounds in
theorem params_mono {C D K K₀ : ℝ} (hC : 1 ≤ C) (hCD : C ≤ D) (hK : K ≤ K₀) {k m f : ℕ} {b g v NT : ℝ}
    (h : Params C K₀ k m f b g v NT 1) : Params D K k m f b g v NT 1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  have hlb : 0 ≤ Real.log b := Real.log_nonneg (by linarith)
  have hX : (0:ℝ) ≤ (m:ℝ) ^ 5 * f * Real.log b := by positivity
  refine ⟨h1, h2, h3, h4, h5, ?_, h7, h8, h9, ?_, le_rfl, ?_⟩
  · have := mul_le_mul_of_nonneg_right hK hX
    nlinarith
  · refine h10.trans (Real.rpow_le_rpow_of_exponent_le (by linarith) ?_)
    have : (0:ℝ) ≤ (m:ℝ) * f := by positivity
    nlinarith
  · have : (0:ℝ) ≤ D := by linarith
    exact Real.one_le_exp (by positivity)

end GlobalTheory.Core.Deg

namespace GlobalTheory.Core.Deg

theorem gam_absorb {C Gam : ℝ} (hC : 0 ≤ C) {k f : ℕ} (hf : 1 ≤ f) (hG : Gam ≤ Real.exp ((k : ℝ) / 8)) :
    C ^ (k * f) * Gam ≤ (Real.exp 1 * C) ^ (k * f) := by
  rw [mul_pow, ← Real.exp_nat_mul, mul_one, mul_comm (Real.exp _)]
  refine mul_le_mul_of_nonneg_left (hG.trans (Real.exp_le_exp.2 ?_)) (by positivity)
  have hf' : (1:ℝ) ≤ f := by exact_mod_cast hf
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
  push_cast
  nlinarith

open Formalism.HermitianLatticeCounting.LatticeSumBounds in
theorem ndRow_mono {C Gam : ℝ} (hC : 1 ≤ C) {k m f s : ℕ} {b g v : ℝ} {Xi : ℕ → ℝ}
    (hf : 1 ≤ f) (hb : 1 ≤ b) (hg : 0 < g) (hv : 0 ≤ v) (hXi : 0 ≤ Xi s)
    (hG : Gam ≤ Real.exp ((k : ℝ) / 8)) :
    ndRow C k m f s b g v Gam Xi ≤ ndRow (Real.exp 1 * C) k m f s b g v 1 Xi := by
  have hC0 : (0:ℝ) ≤ C := by linarith
  have hCD : C ≤ Real.exp 1 * C := le_mul_of_one_le_left hC0 (Real.one_le_exp (by norm_num))
  have hD0 : (0:ℝ) ≤ Real.exp 1 * C := by linarith
  have hH1 := bigH_one_le C hC0 m f hb
  have hHm := bigH_mono hC0 hCD m f hb
  have hHDpos : 0 < bigH (Real.exp 1 * C) m f b := lt_of_lt_of_le zero_lt_one (hH1.trans hHm)
  have hHCpos : 0 < bigH C m f b := lt_of_lt_of_le zero_lt_one hH1
  have e0 : 0 ≤ (2 / g) ^ ((s - 1) * k * f) * ((k : ℝ) * v) ^ (k * f) * Xi s := by positivity
  have eH : bigH C m f b ^ (C * ((s : ℝ) + m) * (m : ℝ) ^ 2) ≤
      bigH (Real.exp 1 * C) m f b ^ (Real.exp 1 * C * ((s : ℝ) + m) * (m : ℝ) ^ 2) := by
    apply rpow_le_rpow_both hH1 hHm (by positivity)
    have : (0:ℝ) ≤ ((s : ℝ) + m) * (m : ℝ) ^ 2 := by positivity
    nlinarith
  have eP : (C * s * f) ^ (6 * s * f) ≤ (Real.exp 1 * C * s * f) ^ (6 * s * f) := by
    apply pow_le_pow_left₀ (by positivity)
    have : (0:ℝ) ≤ (s : ℝ) * f := by positivity
    nlinarith
  have eG := gam_absorb hC0 hf hG (k := k)
  unfold ndRow
  calc (2 / g) ^ ((s - 1) * k * f) * ((k : ℝ) * v) ^ (k * f) * Xi s * C ^ (k * f) *
        bigH C m f b ^ (C * ((s : ℝ) + m) * (m : ℝ) ^ 2) * (C * s * f) ^ (6 * s * f) * Gam
      = ((2 / g) ^ ((s - 1) * k * f) * ((k : ℝ) * v) ^ (k * f) * Xi s) * (C ^ (k * f) * Gam) *
        bigH C m f b ^ (C * ((s : ℝ) + m) * (m : ℝ) ^ 2) * (C * s * f) ^ (6 * s * f) := by ring
    _ ≤ ((2 / g) ^ ((s - 1) * k * f) * ((k : ℝ) * v) ^ (k * f) * Xi s) * (Real.exp 1 * C) ^ (k * f) *
        bigH (Real.exp 1 * C) m f b ^ (Real.exp 1 * C * ((s : ℝ) + m) * (m : ℝ) ^ 2) *
        (Real.exp 1 * C * s * f) ^ (6 * s * f) := by
      have hH0 : 0 ≤ bigH C m f b ^ (C * ((s : ℝ) + m) * (m : ℝ) ^ 2) :=
        le_trans zero_le_one (Real.one_le_rpow hH1 (by positivity))
      gcongr
    _ = _ := by ring

open Formalism.HermitianLatticeCounting.LatticeSumBounds in
theorem degRow_mono {C Gam : ℝ} (hC : 1 ≤ C) {k m f s : ℕ} {b g v : ℝ} {Xi : ℕ → ℝ}
    (hf : 1 ≤ f) (hb : 1 ≤ b) (hg : 0 < g) (hv : 0 ≤ v) (hXi : 0 ≤ Xi s)
    (hG : Gam ≤ Real.exp ((k : ℝ) / 8)) :
    degRow C k m f s b g v Gam Xi ≤ degRow (Real.exp 1 * C) k m f s b g v 1 Xi := by
  have hC0 : (0:ℝ) ≤ C := by linarith
  have hCD : C ≤ Real.exp 1 * C := le_mul_of_one_le_left hC0 (Real.one_le_exp (by norm_num))
  have hD0 : (0:ℝ) ≤ Real.exp 1 * C := by linarith
  have hH1 := bigH_one_le C hC0 m f hb
  have hHm := bigH_mono hC0 hCD m f hb
  have hHDpos : 0 < bigH (Real.exp 1 * C) m f b := lt_of_lt_of_le zero_lt_one (hH1.trans hHm)
  have hHCpos : 0 < bigH C m f b := lt_of_lt_of_le zero_lt_one hH1
  have hlb : 0 ≤ Real.log b := Real.log_nonneg hb
  have e0 : 0 ≤ (2 / g) ^ ((s - 2) * k * f) * ((k : ℝ) * v) ^ (k * f) * Xi s := by positivity
  have eH : bigH C m f b ^ (C * ((s : ℝ) + m) * (m : ℝ) ^ 2) ≤
      bigH (Real.exp 1 * C) m f b ^ (Real.exp 1 * C * ((s : ℝ) + m) * (m : ℝ) ^ 2) := by
    apply rpow_le_rpow_both hH1 hHm (by positivity)
    have : (0:ℝ) ≤ ((s : ℝ) + m) * (m : ℝ) ^ 2 := by positivity
    nlinarith
  have eP : (C * s * f) ^ (6 * s * f) ≤ (Real.exp 1 * C * s * f) ^ (6 * s * f) := by
    apply pow_le_pow_left₀ (by positivity)
    have : (0:ℝ) ≤ (s : ℝ) * f := by positivity
    nlinarith
  have eE : Real.exp (C * (m : ℝ) ^ 6 * f * Real.log b) ≤
      Real.exp (Real.exp 1 * C * (m : ℝ) ^ 6 * f * Real.log b) := by
    apply Real.exp_le_exp.2
    have : (0:ℝ) ≤ (m : ℝ) ^ 6 * f * Real.log b := by positivity
    nlinarith
  have eQ : (C / k) ^ (k * f) ≤ (Real.exp 1 * C / k) ^ (k * f) := by
    apply pow_le_pow_left₀ (by positivity)
    exact div_le_div_of_nonneg_right hCD (Nat.cast_nonneg k)
  have eG := gam_absorb hC0 hf hG (k := k)
  have hH0 : 0 ≤ bigH C m f b ^ (C * ((s : ℝ) + m) * (m : ℝ) ^ 2) :=
    le_trans zero_le_one (Real.one_le_rpow hH1 (by positivity))
  unfold degRow
  calc (2 / g) ^ ((s - 2) * k * f) * ((k : ℝ) * v) ^ (k * f) * Xi s * C ^ (k * f) *
        bigH C m f b ^ (C * ((s : ℝ) + m) * (m : ℝ) ^ 2) * (C * s * f) ^ (6 * s * f) * Gam *
        Real.exp (C * (m : ℝ) ^ 6 * f * Real.log b) * (C / k) ^ (k * f)
      = ((2 / g) ^ ((s - 2) * k * f) * ((k : ℝ) * v) ^ (k * f) * Xi s) * (C ^ (k * f) * Gam) *
        bigH C m f b ^ (C * ((s : ℝ) + m) * (m : ℝ) ^ 2) * (C * s * f) ^ (6 * s * f) *
        Real.exp (C * (m : ℝ) ^ 6 * f * Real.log b) * (C / k) ^ (k * f) := by ring
    _ ≤ ((2 / g) ^ ((s - 2) * k * f) * ((k : ℝ) * v) ^ (k * f) * Xi s) * (Real.exp 1 * C) ^ (k * f) *
        bigH (Real.exp 1 * C) m f b ^ (Real.exp 1 * C * ((s : ℝ) + m) * (m : ℝ) ^ 2) *
        (Real.exp 1 * C * s * f) ^ (6 * s * f) *
        Real.exp (Real.exp 1 * C * (m : ℝ) ^ 6 * f * Real.log b) * (Real.exp 1 * C / k) ^ (k * f) := by
      gcongr
    _ = _ := by ring

end GlobalTheory.Core.Deg

namespace GlobalTheory.Core.Deg

open Formalism.HermitianLatticeCounting.LatticeSumBounds in

theorem corankSums_expLoss : ∀ C : ℝ, 1 ≤ C → ∃ K₀ : ℝ, ∀ (k m f : ℕ) (b g v NT Gam : ℝ) (Xi : ℕ → ℝ),
    Formalism.HermitianLatticeCounting.LatticeSumBounds.Params C K₀ k m f b g v NT 1 → Formalism.HermitianLatticeCounting.LatticeSumBounds.XiHyp C k m f b v NT Xi → 0 ≤ Gam →
    Gam ≤ Real.exp ((k : ℝ) / 8) →
    ∑ s ∈ Finset.Icc 2 k, Formalism.HermitianLatticeCounting.LatticeSumBounds.ndRow C k m f s b g v Gam Xi ≤ (Real.sqrt g)⁻¹ ^ (k * f) ∧
    ∑ s ∈ Finset.Icc 2 k, Formalism.HermitianLatticeCounting.LatticeSumBounds.degRow C k m f s b g v Gam Xi ≤
      Real.exp (-((k : ℝ) * f * Real.log k) / 2) := by
  intro C hC
  have hC0 : (0:ℝ) ≤ C := by linarith
  have hCD : C ≤ Real.exp 1 * C := le_mul_of_one_le_left hC0 (Real.one_le_exp (by norm_num))
  have hD : 1 ≤ Real.exp 1 * C := hC.trans hCD
  obtain ⟨K1, H1⟩ := Formalism.HermitianLatticeCounting.P.sumNondegenerateRowsLe (Real.exp 1 * C) hD
  obtain ⟨K2, H2⟩ := Formalism.HermitianLatticeCounting.P.sumDegenerateRowsLe (Real.exp 1 * C) hD
  refine ⟨max K1 K2, ?_⟩
  intro k m f b g v NT Gam Xi hP hXi _hG0 hG
  obtain ⟨hm4, hmf, hfk, hb2, hg8, -, hv1, -, hNT1, -⟩ := id hP
  have hb1 : (1:ℝ) ≤ b := by linarith
  have hf : 1 ≤ f := by omega
  have hk : (1:ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hkb : 0 < (k:ℝ) * b := mul_pos (by linarith) (by linarith)
  have hg : 0 < g := lt_of_lt_of_le (pow_pos hkb 8) hg8
  have hv : (0:ℝ) ≤ v := by linarith
  have P1 := params_mono hC hCD (le_max_left K1 K2) hP
  have P2 := params_mono hC hCD (le_max_right K1 K2) hP
  have X' := xiHyp_mono hC hCD hb1 hNT1 hXi
  have hXs : ∀ s ∈ Finset.Icc 2 k, 0 ≤ Xi s := by
    intro s hs
    rw [Finset.mem_Icc] at hs
    by_cases h2 : s + 2 ≤ k
    · exact (hXi.1 s hs.1 h2).1
    · exact (hXi.2 s (by omega)).1
  refine ⟨?_, ?_⟩
  · refine le_trans (Finset.sum_le_sum fun s hs => ?_) (H1 k m f b g v NT 1 Xi P1 X')
    exact ndRow_mono hC hf hb1 hg hv (hXs s hs) hG
  · have E2 := H2 k m f b g v NT 1 Xi P2 X'
    rw [one_pow, inv_one, mul_one] at E2
    refine le_trans (Finset.sum_le_sum fun s hs => ?_) E2
    exact degRow_mono hC hf hb1 hg hv (hXs s hs) hG

end GlobalTheory.Core.Deg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleLiftReductionToFockVectorsUniform
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CenAvg

theorem exists_central_average_uniform : ∀ (D : D7), BiAct D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A S A' : HSp D)
    (x : DefSp A) (y : DefSp S) (z : DefSp A'), x.Is → y.Is → z.Is → ∀ (k₀ : KerDat A S) (k₀' : KerDat S A'), k₀.Is ψ θ x y →
    k₀'.Is ψ θ y z → ∀ (χ : GA D A → ℂ) (C : WO A S → WO S A' → ℂ), IsBiVac ψ A S A' x.L y.L z.L C → IsBiSmooth C →
    (∃ φ₀ : GA D A → ℂ, IsContAut A φ₀ ∧ HasCen A χ φ₀ ∧ φ₀ ≠ 0) →
    ∃ (C₁ : WO A S → WO S A' → ℂ) (χ₁ : GA D A → ℂ), IsBiVac ψ A S A' x.L y.L z.L C₁ ∧ IsBiSmooth C₁ ∧
      (∀ a ∈ GinfC A, a ∈ Subgroup.center (GA D A) → ∀ v, k₀.om (a, 1) (fun u => C₁ u v) = χ₁ a • fun u => C₁ u v) ∧
      ∀ (k : KerDat A S) (k' : KerDat S A'), k.Is ψ θ x y → k'.Is ψ θ y z →
        (∀ a ∈ GinfC A, ∀ b ∈ GinfC S, ∀ f, IsThetaFunO ψ A S f → k.om (a, b) f = k₀.om (a, b) f) →
        ∀ φ, IsContAut A φ → HasCen A χ φ →
          biLift k.om k'.om x.vol y.vol φ (biComb ψ A S A' k.c k'.c C) =
            biLift k.om k'.om x.vol y.vol φ (biComb ψ A S A' k.c k'.c C₁) := by
  intro D hB ψ θ A S A' x y z hx hy hz k₀ k₀' hk₀ hk₀' χ C hv hs ⟨φ₀, hφ₀, hc₀, hne⟩
  obtain ⟨χA, χS, ha⟩ := hk₀.weil
  obtain ⟨χS', χA', hb⟩ := hk₀'.weil
  obtain ⟨i1, -, i3, i4, i5, -⟩ := GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D A
  let Z : Subgroup (GA D A) := GinfC A ⊓ Subgroup.center (GA D A)
  have hcl : IsClosed (Subgroup.center (GA D A) : Set (GA D A)) := by
    have : (Subgroup.center (GA D A) : Set (GA D A)) = ⋂ g, {a | g * a = a * g} := by
      ext a
      simp only [SetLike.mem_coe, Subgroup.mem_center_iff, Set.mem_iInter, Set.mem_setOf_eq]
    rw [this]
    exact isClosed_iInter fun g => isClosed_eq (continuous_const.mul continuous_id) (continuous_id.mul continuous_const)
  haveI : CompactSpace Z := isCompact_iff_compactSpace.mp ((GlobalTheory.T.isCompact_realPoints_of_definiteHermitianSpaceData D A x hx).inter_right hcl)
  let ν : Measure Z := GlobalTheory.haarProb Z
  obtain ⟨h₀, hh₀⟩ := Function.ne_iff.1 hne
  have hh : φ₀ h₀ ≠ 0 := hh₀
  have hmul : ∀ a b : Z, χ (a * b : Z) = χ a * χ b := by
    intro a b
    apply mul_right_cancel₀ hh
    rw [← hc₀ _ (a * b).2.1 (a * b).2.2, Subgroup.coe_mul, ← mul_assoc, hc₀ _ b.2.1 b.2.2, hc₀ _ a.2.1 a.2.2]
    ring
  have hone : χ 1 = 1 := by
    apply mul_right_cancel₀ hh
    rw [← hc₀ _ (one_mem _) (one_mem _), mul_one, one_mul]
  have hcont : Continuous fun a : Z => χ a := by
    have : (fun a : Z => χ a) = fun a : Z => φ₀ (h₀ * a) / φ₀ h₀ := by
      funext a
      rw [hc₀ _ a.2.1 a.2.2, mul_div_cancel_right₀ _ hh]
    rw [this]
    exact (hφ₀.2.comp (continuous_const.mul continuous_subtype_val)).div_const _
  have hj : ∀ a : Z, (a : GA D A) ∈ GinfC A := fun a => a.2.1
  have hC := GlobalTheory.FrComb.biTheta_of_vac hx.sd hy.sd hz.sd hv hs
  refine ⟨avg k₀.om ν Subtype.val (fun a => χ a) C, fun a => χ a⁻¹,
    isBiVac_avg ν ha hb hB continuous_subtype_val hj hcont hC hv,
    (isBiTheta_avg ν ha hb hB continuous_subtype_val hj hcont hC).smooth, fun a ha1 ha2 v => ?_, ?_⟩
  · funext u
    rw [om_avg ν ha hb hB continuous_subtype_val hj hcont hC]
    let a' : Z := ⟨a, ha1, ha2⟩
    simp only [Pi.smul_apply, smul_eq_mul, avg]
    rw [← integral_const_mul, ← integral_mul_left_eq_self (μ := ν)
      (fun b : Z => χ a⁻¹ * (χ b * k₀.om (b, 1) (fun u' => C u' v) u)) a']
    congr 1
    funext b
    have e : χ a⁻¹ * χ a = 1 := by
      have := hmul a'⁻¹ a'
      rw [inv_mul_cancel] at this
      exact this.symm.trans hone
    rw [hmul, ← mul_assoc, ← mul_assoc]
    change _ = χ a⁻¹ * χ a * χ b * k₀.om (a * b, 1) (fun u' => C u' v) u
    rw [e, one_mul]
  intro k k' hk hk' hag φ hφ hcφ
  obtain ⟨χA₁, χS₁, ha₁⟩ := hk.weil
  obtain ⟨χS₁', χA₁', hb₁⟩ := hk'.weil
  have eavg : avg k₀.om ν Subtype.val (fun a => χ a) C = avg k.om ν Subtype.val (fun a => χ a) C := by
    funext u v
    simp only [avg]
    congr 1
    funext a
    rw [hag a a.2.1 1 (GinfC S).one_mem _ (hv.left v).1]
  rw [eavg]
  have hG := GlobalTheory.FrComb.biTheta_combL ha₁.std (GlobalTheory.FrComb.biTheta_combR ha₁.std hC hk'.fin) hk.fin
  rw [biComb_avg ν ha₁ hb₁ hB continuous_subtype_val hj hcont hC hk.fin hk'.fin]
  change IsBiTheta ψ A S A' (biComb ψ A S A' k.c k'.c C) at hG
  generalize biComb ψ A S A' k.c k'.c C = G at hG
  funext h₂
  unfold biLift
  congr 1
  funext h₁
  have hF : IsContAut A fun h => φ h * k'.om (h₁, h₂) (fun v => k.om (h, h₁) (fun u => G u v) 0) 0 := by
    refine ⟨fun γ hγ g => ?_, hφ.2.mul ?_⟩
    · have : ∀ v, k.om (γ * g, h₁) (fun u => G u v) 0 = k.om (g, h₁) (fun u => G u v) 0 := fun v => by
        rw [← ha₁.om_aut γ hγ 1 (one_mem _) _ (ha₁.om_pres (g, h₁) _ (GlobalTheory.FrComb.slice_left hG v)), ← Module.End.mul_apply,
          ← map_mul, Prod.mk_mul_mk, one_mul]
      simp only [this, hφ.1 γ hγ g]
    · exact (hB ψ A S A' _ _ _ _ _ _ ha₁ hb₁ G hG).2.2.2.comp
        (show Continuous fun h : GA D A => ((h, h₁), (h₁, h₂), (0 : WO A S), (0 : WO S A')) from
          (continuous_id.prodMk continuous_const).prodMk continuous_const)
  rw [← integral_mean ν hx.cpt x.vol continuous_subtype_val hF]
  congr 1
  funext h
  rw [ker_avg ν ha₁ hb₁ hB continuous_subtype_val hj hcont hG, ← integral_const_mul]
  congr 1
  funext a
  rw [hcφ _ a.2.1 a.2.2]
  ring

end GlobalTheory.CenAvg

namespace GlobalTheory.SeeSaw

theorem fockRed_uniform : ∀ D : D7, BiAct D → CenFock D → LiftSum D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (A S A' : HSp D) (x : DefSp A) (y : DefSp S) (z : DefSp A'), x.Is → y.Is → z.Is → ∀ (k₀ : KerDat A S) (k₀' : KerDat S A'), k₀.Is ψ θ x y → k₀'.Is ψ θ y z → ∀ (χ : GA D A → ℂ) (C : WO A S → WO S A' → ℂ), IsBiVac ψ A S A' x.L y.L z.L C → IsBiSmooth C → ∃ (n : ℕ) (P : Fin n → PolF D S.rank A.rank) (P' : Fin n → PolF D A'.rank S.rank), ∀ (k : KerDat A S) (k' : KerDat S A'), k.Is ψ θ x y → k'.Is ψ θ y z → k.vac = k₀.vac → k'.vac = k₀'.vac → (∀ a ∈ GinfC A, ∀ b ∈ GinfC S, ∀ f, IsThetaFunO ψ A S f → k.om (a, b) f = k₀.om (a, b) f) → (∀ a ∈ GinfC S, ∀ b ∈ GinfC A', ∀ f, IsThetaFunO ψ S A' f → k'.om (a, b) f = k₀'.om (a, b) f) → ∀ φ, IsContAut A φ → HasCen A χ φ → biLift k.om k'.om x.vol y.vol φ (biComb ψ A S A' k.c k'.c C) = ∑ i, k'.lift ψ θ y z (P' i) (k.lift ψ θ x y (P i) φ) := by
  intro D hBi hCF hLS ψ θ hθ A S A' x y z hx hy hz k₀ k₀' hk₀ hk₀' χ C hC hsm
  by_cases h0 : ∃ φ₀ : GA D A → ℂ, IsContAut A φ₀ ∧ HasCen A χ φ₀ ∧ φ₀ ≠ 0
  · obtain ⟨C₁, χ₁, hC₁, hs₁, he₁, heq₁⟩ :=
      GlobalTheory.CenAvg.exists_central_average_uniform D hBi ψ θ A S A' x y z hx hy hz k₀ k₀' hk₀ hk₀' χ C hC hsm h0
    obtain ⟨χ₃, h₃⟩ := GlobalTheory.T.realCentre_acts_by_character_on_isotypic_slices D hBi hCF hLS ψ θ hθ A S A' x y z hx hy hz k₀ k₀' hk₀ hk₀' χ₁ C₁ hC₁ he₁
    obtain ⟨C₂, χ₂, hC₂, he₂, hf₂, heq₂⟩ :=
      GlobalTheory.T.exists_uniform_isotypic_average_real_centre D hBi hCF hLS ψ θ hθ A S A' x y z hx hy hz k₀ k₀' hk₀ hk₀' χ₁ χ₃ C₁ hC₁ hs₁ he₁ h₃
    obtain ⟨n, P, P', hp⟩ := GlobalTheory.T.centralEigen_realDatum_finite_sum_fockProducts D hCF ψ θ hθ A S A' x y z hx hy hz k₀ k₀' hk₀ hk₀' χ₁ χ₂ C₂ hC₂ he₂ hf₂
    refine ⟨n, P, P', fun k k' hk hk' hv hv' hag hag' φ hφ hcen => ?_⟩
    rw [heq₁ k k' hk hk' hag φ hφ hcen, heq₂ k k' hk hk' hag hag' φ hφ,
      GlobalTheory.T.doubleLift_fockSum_eq_sum_iteratedLifts D hBi hCF hLS ψ θ hθ A S A' x y z hx hy hz k k' hk hk' n P P' C₂ (by rw [hv, hv']; exact hp) φ hφ]
  · refine ⟨0, Fin.elim0, Fin.elim0, fun k k' _ _ _ _ _ _ φ hφ hcen => ?_⟩
    have e : φ = 0 := by
      by_contra hne
      exact h0 ⟨φ, hφ, hcen, hne⟩
    subst e
    funext h₂
    simp [biLift]

end GlobalTheory.SeeSaw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledCompactSubgroupConjHermitianSpace
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.LatMove

theorem stab_conj_iff {R ι : Type} [CommRing R] [Fintype ι] [DecidableEq ι] (M M' : Set (ι → R)) (B X : GL ι R)
    (hB : ∀ Y, Y ∈ M ↔ B.1 *ᵥ Y ∈ M') :
    (∀ Y, Y ∈ M' ↔ X.1 *ᵥ Y ∈ M') ↔ (∀ Y, Y ∈ M ↔ (B⁻¹ * X * B).1 *ᵥ Y ∈ M) := by
  have key : ∀ Y, B.1 *ᵥ ((B⁻¹ * X * B).1 *ᵥ Y) = X.1 *ᵥ (B.1 *ᵥ Y) := fun Y => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul,
      show B * (B⁻¹ * X * B) = X * B by group]
  constructor
  · intro h Y
    rw [hB Y, hB, key]
    exact h _
  · intro h Y
    have hY : B.1 *ᵥ ((B⁻¹).1 *ᵥ Y) = Y := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    have := h ((B⁻¹).1 *ᵥ Y)
    rw [hB, hB, key, hY] at this
    exact this

theorem map_conj_of_eq_one {G H : Type} [Group G] [Group H] (f : G →* H) {g : G} (hg : f g = 1) (x : G) :
    f (g⁻¹ * x * g) = f x := by
  rw [map_mul, map_mul, map_inv, hg, inv_one, one_mul, mul_one]

theorem map_conj' {G H : Type} [Group G] [Group H] (f : G →* H) (g x : G) :
    f (g⁻¹ * x * g) = (f g)⁻¹ * f x * f g := by
  rw [map_mul, map_mul, map_inv]

section General

open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E} {Q : Matrix (Fin (n + n)) (Fin (n + n)) E}

theorem mem_KFin_conj (h : Q = dblGram finSumFinEquiv J) {L L' : Submodule (𝓞 E) (Fin n → E)}
    {v : HeightOneSpectrum (𝓞 F)} (g : GLoc σ J v)
    (hg : ∀ z, z ∈ latLoc F L v ↔ (GlobalTheory.AdelicU.matHom _ σ J g).val *ᵥ z ∈ latLoc F L' v) (x : GLoc σ Q v) :
    x ∈ GlobalTheory.Doubling.KFin σ Q L' v ↔ (ioH _ σ h (g, g))⁻¹ * x * ioH _ σ h (g, g) ∈ GlobalTheory.Doubling.KFin σ Q L v := by
  refine mem_stabLoc.trans (Iff.trans ?_ mem_stabLoc.symm)
  rw [map_conj', matHom_ioH, latLoc_sumLat, latLoc_sumLat]
  refine stab_conj_iff (SetLike.coe (sumLat finSumFinEquiv (latLoc F L v) (latLoc F L v)))
    (SetLike.coe (sumLat finSumFinEquiv (latLoc F L' v) (latLoc F L' v))) _ _ fun Y => ?_
  rw [← pairVec_eta finSumFinEquiv Y, val_blkGL, blkMat_mulVec, SetLike.mem_coe, SetLike.mem_coe,
    pairVec_mem_sumLat, pairVec_mem_sumLat]
  exact and_congr (hg _) (hg _)

theorem mem_KAd_conj (h : Q = dblGram finSumFinEquiv J) {L L' : Submodule (𝓞 E) (Fin n → E)} (k : GAd σ J)
    (hk : k ∈ finPts σ J)
    (hL : ∀ (v : HeightOneSpectrum (𝓞 F)) z,
      z ∈ latLoc F L v ↔ (GlobalTheory.AdelicU.matHom _ σ J (proj σ J v k)).val *ᵥ z ∈ latLoc F L' v)
    (a : GL (Fin n) (AF F ⊗[F] E)) (x : GAd σ Q) :
    x ∈ KAd σ Q L' a ↔ (ioH _ σ h (k, k))⁻¹ * x * ioH _ σ h (k, k) ∈ KAd σ Q L a := by
  refine mem_KAd.trans (Iff.trans (and_congr (forall_congr' fun v => ?_) (forall_congr' fun w => ?_)) mem_KAd.symm)
  · rw [map_conj', proj_ioH]
    exact mem_KFin_conj h _ (hL v) _
  · rw [map_conj_of_eq_one _ (by rw [projArch_ioH, mem_finPts_iff_forall.1 hk w, ioH_one])]

end General

theorem mem_KAd_io_conj : ∀ (D : D7) (A : HSp D) (L L' : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (k : GA D A), k ∈ GfC A →
    (∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (z : Fin A.rank → TensorProduct D.host.F (Fv D.host.F v) D.host.E),
      z ∈ latLoc D.host.F L v ↔
        (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig A.gram (proj D.sp.cm.sig A.gram v k)).val *ᵥ z ∈ latLoc D.host.F L' v) →
    ∀ (a : GL (Fin A.rank) (AE D)) (x : GA D (dblSp A)), x ∈ KAd D.sp.cm.sig (dblSp A).gram L' a ↔
      (io A (k, k))⁻¹ * x * io A (k, k) ∈ KAd D.sp.cm.sig (dblSp A).gram L a :=
  fun D A _ _ k hk hL a x => mem_KAd_conj (σ := D.sp.cm.sig) (gram_hdbl A) k hk hL a x

end GlobalTheory.LatMove
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockVectorPureTensorCoefficientSplitsTrivialPlacStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockVector_pureTensor_coefficient_splits_trivial_place : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (x : Place D → WO S T → ℂ), (∀ τ, x (.inr τ) = f₀) → ∀ (v : FinPl D) (P : MvPolynomial (FVar D T.rank S.rank) ℂ) (g : GA D S), gAt S (.inl v) g = 1 → ∃ C : ℂ, ∀ (x₁ x₂ : Place D → WO S T → ℂ) (f₁ f₂ : WO S T → ℂ), (∀ p, p ≠ .inl v → x₁ p = x p) → (∀ p, p ≠ .inl v → x₂ p = x p) → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x₁ f₁ → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x₂ f₂ → ipO μ 𝓕 (om (g, 1) (pureTensorO ψ θ S T sS sT BS BT f₁ P)) (pureTensorO ψ θ S T sS sT BS BT f₂ P) = C * ipO μ 𝓕 (x₁ (.inl v)) (x₂ (.inl v)) := by
  first | exact @GlobalTheory.FockCoeffSplit.coeff_split | exact GlobalTheory.FockCoeffSplit.coeff_split | (intros; apply GlobalTheory.FockCoeffSplit.coeff_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsJointlySmoothBiThetaWeilRepFirstVariable
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BiTransfer

theorem isBiTheta_act_left : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (χA χS : (AE D)ˣ →* Circle) (oma : Om A S), IsWeilDatumO ψ A S χA χS oma → ∀ C, IsBiTheta ψ A S A' C → ∀ p, IsBiTheta ψ A S A' fun u v => oma p (fun u' => C u' v) u := by
  intro D ψ A S A' χA χS oma H C hC p
  let d := sumDec A (GlobalTheory.ChiGrid.negSp A')
  have h := (GlobalTheory.T.weil_operator_commutes_superposition_slices_source D ψ _ A _ S d χA χS oma H _ (isThetaFunO_join d hC) Unit 0 (fun _ => 0) (fun _ => 0)
    measurable_const (integrable_zero _ _ _) p).1
  simp only [join_symm] at h
  exact isBiTheta_of_join d h

end GlobalTheory.BiTransfer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KernelExpansionAbsoluteConvergenceEqualWordsStatement
section
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 GlobalTheory.Core.Diag GlobalTheory.Core.Deg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_expansion_absolute_convergence_equal_words : Formalism.L2.SG.ThmSOwn.KExpTied ∧ AbsConvTied := by
  first | exact @GlobalTheory.Core.Diag.kExp_absConv_tied | exact GlobalTheory.Core.Diag.kExp_absConv_tied | (intros; apply GlobalTheory.Core.Diag.kExp_absConv_tied <;> assumption)
end

