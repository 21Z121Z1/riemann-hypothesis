import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0005
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1791
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1958
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1983
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1842
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1846
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2051
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2034
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2049
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundCmFrameNonvanishingStatement
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair
import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.Bundle0002
import Formalism.LocalToGlobal.Divisibility.EigenvalueSumLeClosedOf
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle0001
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsIsDeepOfField
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0117
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0153
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Definitions.Divisors.RealisedChainTorusEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureUAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2043
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1809
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1892
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1912
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1796
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfiniteClassBound
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim

namespace GlobalTheory.ClassCount

set_option maxHeartbeats 2000000 in

theorem infClassK : GlobalTheory.FunPr.Hypotheses₂ → InfClassK := by
  intro _
  obtain ⟨c1, hT1⟩ := GlobalTheory.T.principalCongruence_le_topLevel_classSum
  obtain ⟨c2, hR1⟩ := GlobalTheory.T.classSum_vertexLevels_contain_principalCongruence
  refine ⟨max c1 c2, fun CF hCF => ⟨144, fun ε C hC => ?_⟩⟩
  obtain ⟨x1, hx1⟩ := hT1 CF ((le_max_left _ _).trans hCF) ε
  obtain ⟨x2, hx2⟩ := hR1 CF ((le_max_right _ _).trans hCF) ε
  refine ⟨max x1 x2, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hIs hAt hFO => ?_⟩
  have hTop := hx1 D large₂ he ((le_max_left _ _).trans hx) Γ Pl0 T A Ks R F hS ch hIs hAt hFO
  have hRow := hx2 D large₂ he ((le_max_right _ _).trans hx) Γ Pl0 T A Ks R F hS ch hIs hAt hFO
  obtain ⟨hNb, hfb, hN1, hf1, hm2, hrd1, hlrd, hb12⟩ := GlobalTheory.T.parameterSizeConditions_numericBounds large₂ hS.size
  set b := large₂.sc.b with hb
  set N := bigN D with hNdef
  have hsig : 0 ≤ sig ch.G := Finset.sum_nonneg fun v _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
  have hb0 : 0 < b := by linarith
  have hlb : 0 ≤ Real.log b := Real.log_nonneg (by linarith)
  have hrd0 : 0 < D.host.rdE := by linarith
  have hN0 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hf0 : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf1

  set base := 12 * (D.R.f : ℝ) ^ 2 * (N : ℝ) ^ 4 * D.host.rdE ^ 2 with hbase
  have hbase1 : 1 ≤ base := by
    have : (1 : ℝ) ≤ (D.R.f : ℝ) ^ 2 := one_le_pow₀ hf0
    have : (1 : ℝ) ≤ (N : ℝ) ^ 4 := one_le_pow₀ hN0
    have : (1 : ℝ) ≤ D.host.rdE ^ 2 := one_le_pow₀ hrd1
    have : (1 : ℝ) ≤ 12 * (D.R.f : ℝ) ^ 2 := by nlinarith
    have : (1 : ℝ) ≤ 12 * (D.R.f : ℝ) ^ 2 * (N : ℝ) ^ 4 := by nlinarith
    nlinarith
  have hlbase : Real.log base ≤ 8 * Real.log b := by
    have h12 : Real.log 12 ≤ Real.log b := Real.log_le_log (by norm_num) hb12
    have hlf : Real.log (D.R.f:ℝ) ≤ Real.log b := Real.log_le_log (by linarith) hfb
    have hlN : Real.log N ≤ Real.log b := Real.log_le_log (by linarith) hNb
    have e : Real.log base = Real.log 12 + 2 * Real.log (D.R.f:ℝ) + 4 * Real.log N + 2 * Real.log D.host.rdE := by
      rw [hbase, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow]
      push_cast; ring
    rw [e]; nlinarith

  set M := hBd D N * Real.exp (2 * sig ch.G) ^ (N ^ 2) with hM
  have hM0 : 0 ≤ M := by rw [hM, hBd]; positivity
  have factor : ∀ (n : ℕ), n ≤ N → ∀ a : ℝ, 0 ≤ a → a ≤ Real.exp (2 * sig ch.G) → hBd D n * a ^ (n ^ 2) ≤ M := by
    intro n hn a ha0 ha
    have h1 : hBd D n ≤ hBd D N := hBd_mono hn hbase1 hrd0.le
    have h2 : a ^ (n ^ 2) ≤ Real.exp (2 * sig ch.G) ^ (N ^ 2) :=
      (pow_le_pow_left₀ ha0 ha _).trans (pow_le_pow_right₀ (Real.one_le_exp (by linarith)) (by gcongr))
    exact mul_le_mul h1 h2 (by positivity) (by rw [hBd]; positivity)
  have hmod := GlobalTheory.T.absNorm_gridModulus_le_exp_depthLogNormSum ch.G hS.hF
  have fin : ∀ (X : Node), DefNode D.R.m X → ∀ K : Subgroup (GL (Fin (ch.G.V X).rank) (Lev.EAf D)),
      congLev D.sp.cm (ch.G.V X).gram (ch.G.Λ X) ch.G.modul ≤ K → (Nat.card (FinCl (ch.G.V X) K) : ℝ) ≤ M := fun X hX K hK =>
    (GlobalTheory.T.definiteVertexClasses_card_le_principalCongruence ch.G ch.S.N X hX _ (ch.G.pl.modul_ne_bot _) K hK).trans
      (factor _ (GlobalTheory.T.definiteKernelNode_rank_le_totalRank ch.G X hX) _ (Nat.cast_nonneg _) hmod)

  set K0 := 48 * (D.R.f:ℝ) * (N : ℝ) ^ 2 * Real.log b + 2 * (N : ℝ) ^ 2 * sig ch.G with hK0
  have hK00 : 0 ≤ K0 := by positivity
  have hMK : M ≤ Real.exp K0 := by
    have e1 : hBd D N ≤ Real.exp ((6 * D.R.f * N ^ 2 : ℕ) * (8 * Real.log b)) := by
      rw [Real.exp_nat_mul]
      refine pow_le_pow_left₀ (by positivity) ?_ _
      rw [← Real.log_le_iff_le_exp (by positivity)]
      exact hlbase
    have e2 : Real.exp (2 * sig ch.G) ^ (N ^ 2) = Real.exp ((N ^ 2 : ℕ) * (2 * sig ch.G)) := (Real.exp_nat_mul _ _).symm
    rw [hM, e2, hK0]
    calc _ ≤ Real.exp ((6 * D.R.f * N ^ 2 : ℕ) * (8 * Real.log b)) * Real.exp ((N ^ 2 : ℕ) * (2 * sig ch.G)) :=
          mul_le_mul_of_nonneg_right e1 (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; push_cast; ring_nf

  have hm0 : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm2
  have key : ((2 * D.R.m + 1 : ℕ) : ℝ) * K0 ≤ D.R.m * aOne ch.G C b := by
    have hm00 : (0 : ℝ) ≤ D.R.m := by linarith
    have h3 : ((2 * D.R.m + 1 : ℕ) : ℝ) * K0 ≤ 3 * D.R.m * K0 :=
      mul_le_mul_of_nonneg_right (by push_cast; linarith) hK00
    refine h3.trans ?_
    have hX : 0 ≤ (D.R.f : ℝ) * N * Real.log b := by positivity
    have t1 : 144 * (D.R.f : ℝ) * (N : ℝ) ^ 2 * Real.log b ≤ C * D.R.f * N * b * Real.log b :=
      calc 144 * (D.R.f : ℝ) * (N : ℝ) ^ 2 * Real.log b = 144 * ((D.R.f * N * Real.log b) * N) := by ring
        _ ≤ 144 * ((D.R.f * N * Real.log b) * b) := by gcongr
        _ ≤ C * ((D.R.f * N * Real.log b) * b) := by gcongr
        _ = C * D.R.f * N * b * Real.log b := by ring
    have hCm : (6 : ℝ) ≤ C * D.R.m := by
      have := mul_le_mul hC hm0 (by norm_num) (by linarith)
      linarith
    have t2 : 6 * ((N : ℝ) ^ 2 * sig ch.G) ≤ (C * D.R.m) * ((N : ℝ) ^ 2 * sig ch.G) :=
      mul_le_mul_of_nonneg_right hCm (by positivity)
    calc 3 * (D.R.m : ℝ) * K0 = D.R.m * (144 * (D.R.f : ℝ) * (N : ℝ) ^ 2 * Real.log b + 6 * ((N : ℝ) ^ 2 * sig ch.G)) := by
          rw [hK0]; ring
      _ ≤ D.R.m * (C * D.R.f * N * b * Real.log b + (C * D.R.m) * ((N : ℝ) ^ 2 * sig ch.G)) :=
          mul_le_mul_of_nonneg_left (add_le_add t1 t2) hm00
      _ = D.R.m * aOne ch.G C b := by rw [aOne]; ring
  have hexp : Real.exp K0 ^ (2 * D.R.m + 1) ≤ Real.exp (D.R.m * aOne ch.G C b) := by
    rw [← Real.exp_nat_mul]; exact Real.exp_le_exp.2 key
  refine ⟨?_, fun Φ β hβ => ?_⟩
  ·
    have h := (GlobalTheory.T.card_topVertexClasses_le_classNumberBound_norm_pow ch.G ch.S.N).trans
      (factor _ (GlobalTheory.T.definiteKernelNode_rank_le_totalRank ch.G (.top 0) (by simp [DefNode])) _ (Nat.cast_nonneg _) hmod)
    refine h.trans (hMK.trans ((le_self_pow₀ (Real.one_le_exp hK00) (by omega)).trans hexp))
  ·
    rw [GridChoice.Classes, Nat.card_prod, Nat.card_pi, Nat.card_pi]
    push_cast
    have hT : ∏ j : Fin D.R.m, (Nat.card (FinCl (ch.G.V (.top j)) (ch.S.levTop A.μ0 Φ β j j.2)) : ℝ) ≤ M ^ D.R.m := by
      calc _ ≤ ∏ _j : Fin D.R.m, M := Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) fun j _ =>
            fin (.top j) (by simp [DefNode]) _
            (hTop Φ β hβ j)
        _ = _ := by simp
    have hR : ∏ i : Fin (D.R.m + 1), (Nat.card (FinCl (ch.G.V (.grid i D.R.m))
        (ch.S.levRow A.μ0 i (Nat.le_of_lt_succ i.2))) : ℝ) ≤ M ^ (D.R.m + 1) := by
      calc _ ≤ ∏ _i : Fin (D.R.m + 1), M := Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) fun i _ =>
            fin (.grid i D.R.m) (by simp [DefNode]; omega) _
            (hRow i)
        _ = _ := by simp
    calc _ ≤ M ^ D.R.m * M ^ (D.R.m + 1) := mul_le_mul hT hR (by positivity) (by positivity)
      _ = M ^ (2 * D.R.m + 1) := by rw [← pow_add]; congr 1; omega
      _ ≤ Real.exp K0 ^ (2 * D.R.m + 1) := pow_le_pow_left₀ hM0 hMK _
      _ ≤ _ := hexp

end GlobalTheory.ClassCount

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralOfCompletedLatticeSelfDualRankOneStatement
section
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio
open scoped nonZeroDivisors
open GlobalTheory.CosetOrth

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_of_completedLattice_selfDual_rankOne : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (r : D.host.E) (LB : Lat T) (n : ℕ), IsStdChar D ψ (-1) →
  S.gram = 1 → T.gram = 1 → IsSelfDualC S (stdLat S) → IsSelfDualC T LB → r ≠ 0 →
  (∀ u ∈ (latO S T (stdLat S) LB fun _ => True), HatPt ((n : D.host.E) * r) 1 u) →
  ∀ (p : Fin T.rank) (q : Fin S.rank) (c : AE D), infPart D c = 0 →
  (∀ t : AE D, infPart D t = 0 → InHat 1 (fe D t) →
    ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * (incA D (star r⁻¹) * (t * c)))) = 1) →
  InHat 1 (algebraMap D.host.E (FA D) ((n : D.host.E) * n * r) * fe D c) := by
  first | exact @GlobalTheory.CosetOrth.inHat_of_char_dual | exact GlobalTheory.CosetOrth.inHat_of_char_dual | (intros; apply GlobalTheory.CosetOrth.inHat_of_char_dual <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KroneckerCharacterFrameFirstStatement
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kronecker_character_frame_first : GlobalTheory.UCls.MassBound → GlobalTheory.UCls.TorusBound → ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ [NeZero H.d] (χ : DirichletCharacter ℂ H.d), GlobalTheory.IsKroneckerChar χ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ F : cuspW Xo c U (wtZ a n), F ∈ latW U (wtZ a n) → F ≠ 0 → (∀ σ, 0 < normW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n) σ F) ∧ -lamPet D.host.E D.R.r Dw.q D.host.d l.M (GlobalTheory.CM.logOm D.host.E χ).re ((absA Dw a : ℕ) : ℝ) ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) ≤ (∑ σ : c.F →+* ℂ, Real.log (normW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n) σ F)) / (Module.finrank ℚ c.F : ℝ) := by
  first | exact @GlobalTheory.LamPet.mean_log_petersson_ge | exact GlobalTheory.LamPet.mean_log_petersson_ge | (intros; apply GlobalTheory.LamPet.mean_log_petersson_ge <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LambdaLowGivesFirstIdentity
section
open Formalism.BasicNotions Formalism.MainNotions NumberField Formalism.L2.Indef Formalism.L2.Indef.Tree GlobalTheory.BigTop GlobalTheory.BigTop.Fun

noncomputable section

namespace GlobalTheory.BigTop.Fun.IPbProof

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem one_le_b {D : D7} (L : SizeData₂ D) : 1 ≤ L.sc.b := by
  have hx := L.sc.one_lt_alt
  have h0 : 0 ≤ L.sc.L := Real.rpow_nonneg (by linarith) _
  unfold Scale.b
  exact Real.one_le_exp h0

theorem La_le_three {D : D7} (L : SizeData₂ D) (hS : SizesAt L) : L.La ≤ 3 * L.sc.L := by
  obtain ⟨hN, -, -, -, hT, hC, hQ, -⟩ := hS
  obtain ⟨-, -, -, -, -, -, hr1, hr2⟩ := hQ
  have hx := L.sc.one_lt_alt
  have hn : (1 : ℝ) ≤ (D.R.n : ℝ) := by
    have : 1 ≤ D.R.n := D.R.n_pos'
    exact_mod_cast this
  have hq : (1 : ℝ) ≤ (D.host.q : ℝ) := by exact_mod_cast D.host.hyp.1.one_le
  have hd : (1 : ℝ) ≤ (D.host.d : ℝ) := by exact_mod_cast D.host.hyp.2.1.one_le
  have hqd : (1 : ℝ) ≤ (D.host.q : ℝ) * D.host.d := by nlinarith
  have hb := one_le_b L
  have hnc : (D.R.n : ℝ) ≤ szCond L := by
    have h := D.host.four_ord_le_condN
    have h' : D.R.n ≤ D.host.QS * D.host.q * D.host.d := by rw [D.R.n_eq_ord]; omega
    unfold szCond; exact_mod_cast h'
  have hc1 : 1 ≤ szCond L := hn.trans hnc
  have hcb : szCond L ≤ L.sc.b := by
    have h1 : szCond L ≤ szCond L ^ 36 := le_self_pow₀ hc1 (by norm_num)
    have h2 : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 150 := one_le_pow₀ hT.1
    have h3 : Real.sqrt L.sc.b ≤ L.sc.b := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
    have h4 : szCond L ^ 36 ≤ szCond L ^ 36 * (D.R.t : ℝ) ^ 150 := le_mul_of_one_le_right (by positivity) h2
    have h5 : szCond L ^ 36 * (D.R.t : ℝ) ^ 150 ≤ Real.sqrt L.sc.b := hC
    linarith
  have hxn : L.sc.x ≤ (D.R.n : ℝ) := by
    refine le_trans ?_ hN.1
    have he := L.sc.eps_pos
    calc L.sc.x = L.sc.x ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx.le (by unfold szTh; linarith)
  have hs : Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ (D.host.q : ℝ) * D.host.d :=
    Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  have hxb : L.sc.x ≤ L.sc.b := (hxn.trans hnc).trans hcb
  have hrb : D.host.rdE ≤ L.sc.b := (UpperTheory.Ram.Rd.rdE_le_cond D.host).trans hcb
  have hlb : Real.log L.sc.b = L.sc.L := Real.log_exp _
  have l1 := Real.log_le_log (by linarith) hxb
  have l2 := Real.log_le_log (by linarith) hrb
  have hx0 : 0 < L.sc.x := by linarith
  have hr0 : 0 < D.host.rdE := by linarith
  have e : L.La = Real.log L.sc.x + L.sc.L + Real.log D.host.rdE := by
    unfold SizeData₂.La Scale.a Scale.b
    rw [Real.log_mul (by positivity) hr0.ne', Real.log_mul hx0.ne' (Real.exp_pos _).ne', Real.log_exp]
  rw [e]
  linarith

end GlobalTheory.BigTop.Fun.IPbProof

namespace GlobalTheory.BigTop.Fun

open GlobalTheory.BigTop.Fun.IPbProof

theorem ipb_of_lamLow : GlobalTheory.BigTop.LamLow → IPb := by
  intro hL
  refine ⟨0, fun CF _ => hL.imp fun Fm CH _ h _ => ?_⟩
  refine ⟨max 0 (max Fm.Csz 0 * (3 + 2 * Fm.CYL + (max Fm.Ct 5 + 3))), fun C hC => ?_⟩
  obtain ⟨x0, hx0⟩ := h
  refine ⟨max x0 9, fun x hx hle i p hp d _ => ?_⟩
  have h6 := hx0 x hx (le_of_max_le_left hle) i p hp C
  have hC0 : 0 ≤ C := (le_max_left _ _).trans hC
  have hC1 : max Fm.Csz 0 * (3 + 2 * Fm.CYL + (max Fm.Ct 5 + 3)) ≤ C := (le_max_right _ _).trans hC
  have hb : 1 ≤ p.Z.b := one_le_b (Fm.L x i)
  have hlb : Real.log p.Z.b = (Fm.L x i).sc.L := Real.log_exp _
  have hL0 : 0 ≤ (Fm.L x i).sc.L := by rw [← hlb]; exact Real.log_nonneg hb
  set P5 := Fm.params x hx i
  have hS := Fm.sizes x hx i
  have hx9 : 9 ≤ (Fm.L x i).sc.x := by rw [Fm.L_x x i hx]; exact le_of_max_le_right hle
  have hLp := Formalism.L2.DIV.Arith4S.Lp_le_La (Fm.L x i) p.Del p.h0 P5 hS hx9
  rw [Formalism.L2.DIV.ofRecord_La, Fm.params_CYL x hx i, Fm.Ct_eq x i] at hLp
  have hLa := La_le_three (Fm.L x i) hS
  have hY : 0 < Fm.CYL := (Fm.params_CYL x hx i) ▸ P5.CYL_pos
  set c : ℝ := 3 + 2 * Fm.CYL + (max Fm.Ct 5 + 3) with hc
  have hc0 : 0 ≤ c := by have := le_max_right Fm.Ct 5; rw [hc]; linarith
  set Lp := (Formalism.L2.DIV.ofRecord (Fm.D x i) (Fm.L x i) p.Del p.h0).Lp
  have hLp0 : 0 ≤ Lp := Formalism.L2.DIV.NumDatum.Lp_nonneg _
  have hLp3 : Lp ≤ 3 * c * (Fm.L x i).sc.L := by nlinarith
  have hNV : ((Fm.D x i).R.nV : ℝ) ≤ (d.O.N : ℝ) := by
    have hm := (Fm.D x i).R.two_le_m
    have h1 : (Fm.D x i).R.t + ((Fm.D x i).R.k + (Fm.D x i).R.m + 5) + 1 ≤
        (Fm.D x i).R.m * ((Fm.D x i).R.t + ((Fm.D x i).R.k + (Fm.D x i).R.m + 5) + 1) :=
      Nat.le_mul_of_pos_left _ (by omega)
    have h2 : (Fm.D x i).R.nV ≤ d.O.N := by
      show (Fm.D x i).R.k + (Fm.D x i).R.m - 1 + (Fm.D x i).R.t ≤
        (Fm.D x i).R.k + (Fm.D x i).R.m * ((Fm.D x i).R.t + ((Fm.D x i).R.k + (Fm.D x i).R.m + 5) + 1)
      omega
    exact_mod_cast h2
  have hf0 : (0 : ℝ) ≤ ((Fm.D x i).R.f : ℝ) := Nat.cast_nonneg _
  have hnv0 : (0 : ℝ) ≤ ((Fm.D x i).R.nV : ℝ) := Nat.cast_nonneg _
  have hsq : ((Fm.D x i).R.nV : ℝ) ^ 2 ≤ (d.O.N : ℝ) ^ 2 := pow_le_pow_left₀ hnv0 hNV 2
  have hA0 : 0 ≤ ((Fm.D x i).R.f : ℝ) * ((Fm.D x i).R.nV : ℝ) ^ 2 * Lp := by positivity
  have hA : ((Fm.D x i).R.f : ℝ) * ((Fm.D x i).R.nV : ℝ) ^ 2 * Lp ≤
      ((Fm.D x i).R.f : ℝ) * (d.O.N : ℝ) ^ 2 * (3 * c * (Fm.L x i).sc.L) := by
    gcongr
  have hB0 : 0 ≤ ((Fm.D x i).R.f : ℝ) * (d.O.N : ℝ) ^ 2 * (Fm.L x i).sc.L := by positivity
  have hcs : Fm.Csz * (((Fm.D x i).R.f : ℝ) * ((Fm.D x i).R.nV : ℝ) ^ 2 * Lp) ≤
      3 * C * ((Fm.D x i).R.f : ℝ) * (d.O.N : ℝ) ^ 2 * (Fm.L x i).sc.L := by
    have e1 : Fm.Csz * (((Fm.D x i).R.f : ℝ) * ((Fm.D x i).R.nV : ℝ) ^ 2 * Lp) ≤
        max Fm.Csz 0 * (((Fm.D x i).R.f : ℝ) * ((Fm.D x i).R.nV : ℝ) ^ 2 * Lp) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hA0
    have e2 : max Fm.Csz 0 * (((Fm.D x i).R.f : ℝ) * ((Fm.D x i).R.nV : ℝ) ^ 2 * Lp) ≤
        max Fm.Csz 0 * (((Fm.D x i).R.f : ℝ) * (d.O.N : ℝ) ^ 2 * (3 * c * (Fm.L x i).sc.L)) :=
      mul_le_mul_of_nonneg_left hA (le_max_right _ _)
    have e3 : max Fm.Csz 0 * c * (((Fm.D x i).R.f : ℝ) * (d.O.N : ℝ) ^ 2 * (Fm.L x i).sc.L) ≤
        C * (((Fm.D x i).R.f : ℝ) * (d.O.N : ℝ) ^ 2 * (Fm.L x i).sc.L) :=
      mul_le_mul_of_nonneg_right hC1 hB0
    nlinarith
  refine GlobalTheory.InfinitePlacesProbe.clauseB_of_lifts (p.S false) (p.S true) (p.N C CH) d.O hC0 hb ⟨rfl, rfl, rfl⟩ h6
    (by simp; rfl) fun j => ?_
  have hm0 : 0 ≤ ∑ ρ : Formalism.L2.DIV.RPl (Fm.D x i).R,
      (Formalism.L2.DIV.ofRecord (Fm.D x i) (Fm.L x i) p.Del p.h0).logHook
        (((Equiv.refl _ : p.P.A3.fam3.base3.J ≃ Fin (Fm.D x i).R.m) j).1 + 1) ρ :=
    Finset.sum_nonneg fun ρ _ => Real.log_natCast_nonneg _
  have e : (p.N C CH).l6 j = (∑ ρ : Formalism.L2.DIV.RPl (Fm.D x i).R,
      (Formalism.L2.DIV.ofRecord (Fm.D x i) (Fm.L x i) p.Del p.h0).logHook
        (((Equiv.refl _ : p.P.A3.fam3.base3.J ≃ Fin (Fm.D x i).R.m) j).1 + 1) ρ) -
      Fm.Csz * (((Fm.D x i).R.f : ℝ) * ((Fm.D x i).R.nV : ℝ) ^ 2 * Lp) - C * 0 := rfl
  rw [e, hlb]
  show -(3 * C * ((Fm.D x i).R.f : ℝ) * (d.O.N : ℝ) ^ 2 * (Fm.L x i).sc.L) ≤ _
  linarith

end GlobalTheory.BigTop.Fun

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevPhInjectiveOfLevDetNonZeroDivisor
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory.AllWt (cuspW latW GoodW rankW)
open GlobalTheory.LevDesc (levDet secRing pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)

namespace GlobalTheory

theorem levPh_injective_of_levDet_nonZeroDivisor : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) (S : Subgroup (LevelAut Dw l)), 1 ≤ Dw.p + Dw.q → l.A.Coprime l.M → ∀ (χ : S →* (c.F)ˣ) (u : Rul Xo c), u ∈ secRing Xo c → (∀ f ∈ secRing Xo c, levDet Xo c S u * f = 0 → f = 0) → ∀ f ∈ secRing Xo c, (∀ h : S, GlobalTheory.LevDesc.levPh Xo c S χ u f h = 0) → f = 0 := by
  classical
  intro E _ _ _ H Dw l Xo c S hpq hA χ u hu hdet f hf hph
  have hact := GlobalTheory.LevDesc.isRightAct_pullSecOn (Xo := Xo) (c := c) (S := S) hpq hA
  have hdet' : (Matrix.of fun h g : S => GlobalTheory.LevDesc.pullSecOn Xo c S hpq hA (h * g) ⟨u, hu⟩).det ∈
      nonZeroDivisors (secRing Xo c) := by
    have h1 := GlobalTheory.LevDesc.coe_det_pullSecOn (Xo := Xo) (c := c) (S := S) hpq hA ⟨u, hu⟩
    have hl : ∀ x : secRing Xo c,
        (Matrix.of fun h g : S => GlobalTheory.LevDesc.pullSecOn Xo c S hpq hA (h * g) ⟨u, hu⟩).det * x = 0 → x = 0 := by
      intro x hx
      have h2 := congrArg Subtype.val hx
      simp only [Subalgebra.coe_mul, Subalgebra.coe_zero] at h2
      apply Subtype.ext
      refine hdet x x.2 ?_
      rw [← h1]
      exact h2
    rw [mem_nonZeroDivisors_iff]
    exact ⟨hl, fun x hx => hl x (by rw [mul_comm]; exact hx)⟩
  have key := (GlobalTheory.twistedTrace_equivariant_and_injective_of_groupDet S c.F (secRing Xo c)
    (GlobalTheory.LevDesc.pullSecOn Xo c S hpq hA) hact.1 hact.2 χ ⟨u, hu⟩ hdet').2.1 ⟨f, hf⟩ (fun h => by
      have h3 := GlobalTheory.LevDesc.coe_tr_pullSecOn (Xo := Xo) (c := c) (S := S) hpq hA χ
        (⟨f, hf⟩ * GlobalTheory.LevDesc.pullSecOn Xo c S hpq hA h ⟨u, hu⟩)
      rw [GlobalTheory.LevDesc.tr_apply] at h3
      apply Subtype.ext
      rw [h3]
      exact hph h)
  exact congrArg Subtype.val key

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftAdjointEigenvalueLowerBoundBaseEmbeddingStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftAdjoint_eigenvalue_lower_bound_base_embedding : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), ∀ (s : ℕ) (b : ℝ), AdelC R F → GlobalTheory.Hk3.Core R F → A.fam.Ok s → PrimeToHost R A.μ0 → (∀ i, Sizes D i b) → GlobalTheory.BigOn.LowTop R b := by
  first | exact @GlobalTheory.LowTopCore.lowTop_ofCore | exact GlobalTheory.LowTopCore.lowTop_ofCore | (intros; apply GlobalTheory.LowTopCore.lowTop_ofCore <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftEMulEq
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HoweLocal
open scoped TensorProduct Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.HoweLocal.WeilImpl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem liftE_mul_eq (v : Pl F) (z : Fv F v ⊗[F] E) (M : AE F E) :
    liftE v z * M = liftE v (z * compFin F E v M) := by
  have h1 : GlobalTheory.LatVac.liftV v 1 • liftE (E := E) v z = liftE v z := by
    rw [GlobalTheory.HoweLocal.LocCoords.liftV_one_smul, GlobalTheory.HoweLocal.LocCoords.compFin_liftE]
  rw [← h1, smul_mul_assoc, GlobalTheory.HoweLocal.LocCoords.liftV_one_smul, map_mul,
    GlobalTheory.HoweLocal.LocCoords.compFin_liftE]

theorem at_liftE (v : Pl F) (z : Fv F v ⊗[F] E) : At (evFin F v) (liftE (E := E) v z) := by
  intro u hu
  have h1 : GlobalTheory.LatVac.liftV v 1 • liftE (E := E) v z = liftE v z := by
    rw [GlobalTheory.HoweLocal.LocCoords.liftV_one_smul, GlobalTheory.HoweLocal.LocCoords.compFin_liftE]
  rw [← h1, smul_smul, mul_comm, GlobalTheory.HoweLocal.LocCoords.liftV_mul, hu, mul_zero, map_zero, zero_smul]

end GlobalTheory.HoweLocal.WeilImpl

namespace GlobalTheory.HoweLocal.WeilImpl

theorem impl_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (a b : ℕ)
    (JA : Matrix (Fin a) (Fin a) E) (B : Spc F E b) (κ : Type) [Fintype κ]
    (dA : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JA) (incM F B.J)) κ) (ψ : AddChar (AF F) ℂ)
    (omB : UA σ B.J →* Module.End ℂ ((κ → AF F) → ℂ)),
    IsStd ψ → IsUSplitting (adeleClass F) ψ dA (actB (cA σ)) omB →
    ∀ v : Pl F, IsEmpty (E →ₐ[F] Fv F v) → ∀ [Invertible (2 : Fv F v)],
    ∀ (eB : UAtGrp σ B (evFin F v) ≃* UG (GlobalTheory.HoweLocal.cv σ v) (GlobalTheory.HoweLocal.Jv v B.J)),
      GlobalTheory.HoweLocal.IsCompIso σ B v eB →
    ∀ omL : UG (GlobalTheory.HoweLocal.cv σ v) (GlobalTheory.HoweLocal.Jv v B.J) →* Module.End ℂ ((κ → Fv F v) → ℂ),
      (∀ g, ∀ φ ∈ SB (κ → Fv F v), omL g φ ∈ SB (κ → Fv F v) ∧
        Acts (evFin F v) (omB (eB.symm g).1) φ (omL g φ)) →
    ∀ co : Darboux (symp (R := Fv F v) (GlobalTheory.HoweLocal.cv σ v) (-1) (GlobalTheory.HoweLocal.Jv v JA)
        (GlobalTheory.HoweLocal.Jv v B.J)) κ,
      (∀ x, co.e x = GlobalTheory.LatVac.locCo dA v (x.map (GlobalTheory.HoweLocal.liftE v))) →
    ∀ g w, ∀ φ ∈ SB (κ → Fv F v), omL g (co.rho (GlobalTheory.LatVac.psiAt ψ v) w φ) =
      co.rho (GlobalTheory.LatVac.psiAt ψ v) (actB (GlobalTheory.HoweLocal.cv σ v) g w) (omL g φ) := by
  intro F E _ _ _ _ _ σ a b JA B κ _ dA ψ omB hstd hW v _hv inst2 eB hcomp omL hL co hco g w φ hφ
  classical
  have hat : ∀ x : Matrix (Fin a) (Fin b) (Fv F v ⊗[F] E), At (evFin F v) (x.map (liftE v)) := by
    intro x u hu; funext i j; exact at_liftE v (x i j) u hu
  have hrho : ∀ (x : Matrix (Fin a) (Fin b) (Fv F v ⊗[F] E)) (φ₀ : (κ → Fv F v) → ℂ),
      Acts (evFin F v) (dA.rho ψ (x.map (liftE v))) φ₀ (co.rho (GlobalTheory.LatVac.psiAt ψ v) x φ₀) := by
    intro x φ₀
    have h := GlobalTheory.VacBridge.rho_acts_locCo dA ψ v _ (hat x) φ₀
    rw [← hco x] at h
    convert h using 2
    simp only [Darboux.rho]
    first | rfl | (congr 1; exact Subsingleton.elim _ _) | congr
  have hSB : ∀ x, ∀ φ₀ ∈ SB (κ → Fv F v), co.rho (GlobalTheory.LatVac.psiAt ψ v) x φ₀ ∈ SB (κ → Fv F v) := by
    intro x φ₀ h0
    have := GlobalTheory.SchrSB.schr_mem_SB ψ hstd.1 v (co.e x) φ₀ h0
    convert this using 2
    simp only [Darboux.rho]
    first | rfl | (congr 1; exact Subsingleton.elim _ _) | congr
  have hpresR : ∀ x, ∀ Φ ∈ schA F κ, dA.rho ψ x Φ ∈ schA F κ := by
    intro x Φ hΦ
    exact GlobalTheory.SchrKeepsSchA.schr_mem_schA F ψ hstd κ _ Φ hΦ
  have hm : (((g : UG (GlobalTheory.HoweLocal.cv σ v) (GlobalTheory.HoweLocal.Jv v B.J)) : GL (Fin b) (Fv F v ⊗[F] E)) : Matrix (Fin b) (Fin b) (Fv F v ⊗[F] E)) = (mat ((eB.symm g : UAtGrp σ B (evFin F v)) : UA σ B.J)).map (compFin F E v) := by
    have := hcomp.1 (eB.symm g)
    rw [MulEquiv.apply_symm_apply] at this
    exact this
  have hact : actB (cA σ) (eB.symm g).1 (w.map (liftE v)) = (actB (GlobalTheory.HoweLocal.cv σ v) g w).map (liftE v) := by
    funext i j
    simp only [actB, Matrix.map_apply, Matrix.mul_apply, Matrix.transpose_apply, map_sum, hm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [liftE_mul_eq]; rfl
  have h1 := GlobalTheory.ThK.LocalOps.acts_comp v (hpresR (w.map (liftE v))) (hrho w φ) (hL g _ (hSB w φ hφ)).2
  have h2 := GlobalTheory.ThK.LocalOps.acts_comp v (fun Φ hΦ => hW.pres (eB.symm g).1 Φ hΦ) (hL g φ hφ).2
    (hrho (actB (GlobalTheory.HoweLocal.cv σ v) g w) (omL g φ))
  have h2' : Acts (evFin F v) (omB (eB.symm g).1 ∘ dA.rho ψ (w.map (liftE v))) φ
      (co.rho (GlobalTheory.LatVac.psiAt ψ v) (actB (GlobalTheory.HoweLocal.cv σ v) g w) (omL g φ)) := by
    intro r hr
    have := h2 r hr
    simp only [Function.comp_apply] at this ⊢
    rw [hW.impl (eB.symm g).1 (w.map (liftE v)) _ hr.2, hact]
    exact this
  exact GlobalTheory.HoweLocal.LocOpsW.acts_uniq v _ hφ h1 h2'

end GlobalTheory.HoweLocal.WeilImpl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModificationLineBundleGlobalSectionsDimPullEqStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic
open GlobalTheory.ThickeningDetermines (secIdeal)
open scoped TensorProduct
open NumberField Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.HSApp
open GlobalTheory.AllWt (wtOf cuspOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modification_globalSectionsDim_pull_eq : ∀ (k : Type) [Field k] (Y : Scheme.{0}) [IsIntegral Y] (p : Y ⟶ Sp k) (U : Y.Opens) (D : ℕ), SmoothOfRelativeDimension D p → IsProjOver p → ∀ (M : Modif p U D) [IsIntegral M.X] (B : LB Y), B.IsLB → letI := algebraΓOfHom p; letI := algebraΓOfHom M.str; lbH0 k (B.pull M.σ) = lbH0 k B := by
  first | exact @GlobalTheory.ModifSections.modification_lineBundleGlobalSectionsDim_pull_eq | exact GlobalTheory.ModifSections.modification_lineBundleGlobalSectionsDim_pull_eq | (intros; apply GlobalTheory.ModifSections.modification_lineBundleGlobalSectionsDim_pull_eq <;> assumption)
end

