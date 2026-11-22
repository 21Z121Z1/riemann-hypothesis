import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0316
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0323
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0325
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0332
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0342
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0028
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0158
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0365
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0177
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0188
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0126
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.UnitaryPointsRankZeroSubsingleton
import Formalism.LocalToGlobal.IndefiniteReal.RankZerothComponentEq
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0116
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0134
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0312
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0271
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0025
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0317
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RadicalNoFixedVectors
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0012
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0124
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0214
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsKProjectorFiniteDim
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0011

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConvolutionRightInvariantOpenStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory Set Filter NumberField
open scoped Topology ContDiff TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.convolution_right_invariant_open : ∀ {D : D7} {V : HSp D} (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {f : GA D V → ℂ}, f ∈ GlobalTheory.Orb.CcGA V → ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ F : GlobalTheory.AutomorphicL2Unitary.DividedPowerChartLift V μ, ∀ k ∈ U, k ∈ GfC V → ∀ g, GlobalTheory.AutomorphicL2Unitary.convR μ f (GlobalTheory.AutomorphicL2Unitary.lift (GQ V) F) (g * k) = GlobalTheory.AutomorphicL2Unitary.convR μ f (GlobalTheory.AutomorphicL2Unitary.lift (GQ V) F) g := by
  first | exact @GlobalTheory.ConvLevel.convR_level | exact GlobalTheory.ConvLevel.convR_level | (intros; apply GlobalTheory.ConvLevel.convR_level <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalOfContinuousRepresentative
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S

namespace GlobalTheory.CuspRep

theorem isCuspFun_of_mem_L2cusp : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], ∀ F ∈ GlobalTheory.Cusp.L2cusp V μ, ∀ ψ : GA D V → ℂ, Continuous ψ → LeftInv (GQ V) ψ → lift (GQ V) F =ᵐ[μ] ψ → IsCuspFun V ψ := by
  intro D V μ _ _ F hF ψ hψc hψl hFψ
  refine (GlobalTheory.Cusp.isCuspFun_iff hψl).2 fun W hW => ?_
  have hc := GlobalTheory.Cusp.cocompact_single (D := D) hW
  have := hc.isProbabilityMeasure
  have hm : StronglyMeasurable (lift (GQ V) F) := (Lp.stronglyMeasurable F).comp_measurable measurable_mk
  have h1 : GlobalTheory.Cusp.constTermOn (GQ V) (GlobalTheory.Cusp.NA (.single hW)) (lift (GQ V) F) =ᵐ[μ] 0 := by
    refine GlobalTheory.CuspAE.constTermOn_ae_eq_zero hc (closure_mono ?_ hF)
    rintro F' ⟨φ, hφ, e⟩
    exact ⟨φ, hφ.1, hφ.2.1, (GlobalTheory.Cusp.isCuspFun_iff hφ.2.1).1 hφ.2.2 W hW, e⟩
  have hcont := hc.continuous_constTermOn hψl hψc
  have h2 : GlobalTheory.Cusp.constTermOn (GQ V) (GlobalTheory.Cusp.NA (.single hW)) ψ =ᵐ[μ] 0 := by
    refine ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero' hcont.locallyIntegrable fun S hS => ?_
    rw [GlobalTheory.CuspAE.setIntegral_constTermOn hc hψl hψc.stronglyMeasurable hψc.locallyIntegrable hS]
    calc _ = ∫ q, ∫ y in S, lift (GQ V) F (((q.out : GlobalTheory.Cusp.NA (.single hW)) : GA D V) * y) ∂μ
            ∂GlobalTheory.Cusp.probMeasure (GQ V) (GlobalTheory.Cusp.NA (.single hW)) :=
          integral_congr_ae (.of_forall fun q => integral_congr_ae (ae_restrict_of_ae
            ((measurePreserving_mul_left μ ((q.out : GlobalTheory.Cusp.NA (.single hW)) : GA D V)).quasiMeasurePreserving.ae
              hFψ.symm)))
      _ = ∫ y in S, GlobalTheory.Cusp.constTermOn (GQ V) (GlobalTheory.Cusp.NA (.single hW)) (lift (GQ V) F) y ∂μ :=
          (GlobalTheory.CuspAE.setIntegral_constTermOn hc (leftInv_lift F) hm (GlobalTheory.CuspAE.locallyIntegrable_lift F) hS).symm
      _ = 0 := by rw [integral_congr_ae (ae_restrict_of_ae h1)]; simp
  exact (hcont.ae_eq_iff_eq μ continuous_const).1 h2

end GlobalTheory.CuspRep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowStableWittProjectionsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depthLatticeGridRow_stable_witt_projections : OnStd fun {D} _ _ {sc} {G} _ F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (_ : 2 * σ + 2 ≤ D.R.m), ∀ u ∈ latRow G (2 * σ + 2), u * ((F.dJ (σ + 1) h).jX * (F.dJ (σ + 1) h).pX) ∈ latRow G (2 * σ + 2) ∧ u * ((F.dJ (σ + 1) h).jY * (F.dJ (σ + 1) h).pY) ∈ latRow G (2 * σ + 2) := by
  first | exact @GlobalTheory.ProjLat.latRow_proj | exact GlobalTheory.ProjLat.latRow_proj | (intros; apply GlobalTheory.ProjLat.latRow_proj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesMultiplicity
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.TestFnCusp

theorem hypH_of_noFixed {D : D7} {V : HSp D} (T : TypeDataG V) (h : NoFixed T) :
    GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.HypH (k := fun v : T.S => ResF v.1) T.τ := by
  intro a ha har
  obtain ⟨v, hv⟩ := h.2 a ha har
  refine ⟨v, fun y hy => hv y fun g hg => hy g ?_⟩
  intro i j hij
  by_contra hc
  exact hij (hg i j hc)

theorem isCuspidalOp_tensor : (∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed.CuspidalOperators V μ) → GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing.ParabolicAndConstTerm → ∀ (D : D7) (V : HSp D) (lam : D.what₂.Tau → Fin V.rank → ℤ) (S : D.what₂.Tau → SPar) (M : DSModel V S) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), IsTestData V lam M T U μa μf μ fa ff → GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed.IsCuspidalOp V μ (tensor D.sp.cm.sig V.gram fa ff) := by
  intro hCO hPC D V lam S M T U μa μf μ _ _ fa ff hTD
  obtain ⟨hodd, -, -, hnf, hμ, ha, hb⟩ := hTD
  haveI : ∀ w, (μa w).IsHaarMeasure := hμ.haar_arch
  haveI : ∀ v, (μf v).IsHaarMeasure := hμ.haar_loc
  have hT : IsTestFnG M T U μa μf (tensor D.sp.cm.sig V.gram fa ff) := ⟨fa, ff, ha, hb, rfl⟩
  have hf : tensor D.sp.cm.sig V.gram fa ff ∈ CcGA V := hT.isPureTensor.2
  have hU := hPC.2 D V hodd S M T (hypH_of_noFixed T hnf) U μa μf _ hT
  refine hCO D V μ _ hf ?_ ?_
  · intro 𝔉 h𝔉 ν hν x y
    exact ((hU 𝔉 h𝔉).1 ν x y).2
  · intro 𝔉 h𝔉 ν hν x y
    exact ((hU 𝔉 h𝔉).2 ν x y).2

end GlobalTheory.TestFnCusp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesTestDataLargeGapsIntegrable
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DSGapData

theorem two_mul_rkR_le {n : ℕ} (ε : Fin n → Bool) : 2 * GlobalTheory.Count.rkR ε ≤ n := by
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n))) (fun a => ε a = true)
  simp only [Bool.not_eq_true, Finset.card_univ, Fintype.card_fin] at h
  unfold GlobalTheory.Count.rkR
  omega

theorem rank_bound (n q : ℕ) (hq : 2 * q ≤ n) :
    120 * (n : ℝ) * ((q : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ 100 * (n : ℝ) ^ 4 := by
  rcases Nat.eq_zero_or_pos q with h0 | h0
  · subst h0
    rw [Nat.cast_zero, Real.zero_rpow (by norm_num), mul_zero]
    positivity
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast h0
  have hq2 : (2 : ℝ) * q ≤ n := by exact_mod_cast hq
  have hn : (2 : ℝ) ≤ n := by linarith
  have e : ((q : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ (q : ℝ) ^ 2 := by
    have := Real.rpow_le_rpow_of_exponent_le hq1 (show (3 : ℝ) / 2 ≤ 2 by norm_num)
    simpa using this
  have h1 : 4 * (q : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by nlinarith
  have h2 : 120 * (n : ℝ) * ((q : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ 120 * (n : ℝ) * (q : ℝ) ^ 2 := by
    have : (0 : ℝ) ≤ 120 * n := by positivity
    exact mul_le_mul_of_nonneg_left e this
  have h3 : 120 * (n : ℝ) * (q : ℝ) ^ 2 ≤ 30 * (n : ℝ) ^ 3 := by nlinarith
  have h4 : 30 * (n : ℝ) ^ 3 ≤ 100 * (n : ℝ) ^ 4 := by nlinarith [pow_nonneg (show (0 : ℝ) ≤ n by linarith) 3]
  linarith

theorem big_bound (n q : ℕ) (hq : 2 * q ≤ n) :
    40 * (n : ℝ) ^ 2 * Real.sqrt q ≤ 100 * (n : ℝ) ^ 4 := by
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0
    have : q = 0 := by omega
    subst this; simp
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast h0
  have hqn : (q : ℝ) ≤ (n : ℝ) ^ 2 := by
    have : q ≤ n ^ 2 := by nlinarith
    exact_mod_cast this
  have hs : Real.sqrt q ≤ n := Real.sqrt_le_iff.2 ⟨by positivity, hqn⟩
  have h1 : 40 * (n : ℝ) ^ 2 * Real.sqrt q ≤ 40 * (n : ℝ) ^ 2 * n :=
    mul_le_mul_of_nonneg_left hs (by positivity)
  have h2 : 40 * (n : ℝ) ^ 2 * n ≤ 100 * (n : ℝ) ^ 4 := by nlinarith [pow_nonneg (show (0 : ℝ) ≤ n by linarith) 3]
  linarith

theorem gap_numeric' {n : ℕ} (ε : Fin n → Bool) (h : ℝ)
    (hh : 120 * (n : ℝ) * ((GlobalTheory.Count.rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) :
    GlobalTheory.Count.rkR ε = 0 ∨ 8 * Real.sqrt (GlobalTheory.Count.rkR ε) * (0 + 4 * n * GlobalTheory.Count.rkR ε) < h := by
  rcases Nat.eq_zero_or_pos (GlobalTheory.Count.rkR ε) with h0 | h0
  · exact Or.inl h0
  right
  have hq : (0 : ℝ) < GlobalTheory.Count.rkR ε := by exact_mod_cast h0
  have hn : (0 : ℝ) < n := by
    have := two_mul_rkR_le ε
    exact_mod_cast (show 0 < n by omega)
  have e : ((GlobalTheory.Count.rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) = Real.sqrt (GlobalTheory.Count.rkR ε) * GlobalTheory.Count.rkR ε := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add_one hq.ne']
    norm_num
  rw [e] at hh
  have hp : 0 < (n : ℝ) * (Real.sqrt (GlobalTheory.Count.rkR ε) * GlobalTheory.Count.rkR ε) := by positivity
  nlinarith

theorem lamAt_gap {D : D7} (hH : HostHyp D) (τ : D.what₂.Tau) (i : ℕ) :
    ∀ j, i < j → j < D.R.r →
      100 * (D.R.r : ℚ) ^ 4 ≤ Formalism.L2.NTheta.lamAt (D.hc τ) i - Formalism.L2.NTheta.lamAt (D.hc τ) j := by
  intro j
  induction j with
  | zero => intro h; omega
  | succ j ih =>
    intro hij hj
    have g := hH.gapR τ j hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | h
    · have := ih h (by omega)
      have h0 : (0 : ℚ) ≤ 100 * (D.R.r : ℚ) ^ 4 := by positivity
      linarith
    · subst h; exact g

theorem isHCParam_cast {n m : ℕ} (h : n = m) (lam : Fin m → ℝ) (hl : Formalism.QuantumDeterminants.IsHCParam lam) :
    Formalism.QuantumDeterminants.IsHCParam (fun i : Fin n => lam (Fin.cast h i)) := by
  subst h; simpa using hl

theorem dsData_gap_integrable : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D), HostHyp D → GlobalTheory.Count.IsDSData X.B X.dv ∧ GlobalTheory.Dec.LocDec X.B (100 * (D.R.r : ℝ) ^ 4) ∧ GlobalTheory.Dec.HBig X.B 40 (100 * (D.R.r : ℝ) ^ 4) ∧ (∀ v, 120 * (X.B.I.n : ℝ) * ((GlobalTheory.Count.rkR (X.B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ 100 * (D.R.r : ℝ) ^ 4) ∧ Integrable X.ph (Formalism.L2.SG.ProjRows.muInf X.B.I) ∧ ∀ v, Integrable (Formalism.L2.SG.ProjRows.phLoc (ε := X.B.I.ε v) (X.B.σ v) (X.B.w v) (X.dv v)) (Formalism.REAL.muG (X.B.I.ε v)) := by
  intro D X hH
  have hn : (X.B.I.n : ℝ) = (D.R.r : ℝ) := by exact_mod_cast X.n_eq

  have hds : GlobalTheory.Count.IsDSData X.B X.dv := by
    intro v
    have e : X.B.lam v = fun i => Formalism.MainNotions.S.lamS D.R (D.hc (X.pl v)) (Fin.cast X.n_eq i) := funext (X.lam_eq v)
    refine ⟨?_, X.ds v, X.low v, ?_⟩
    · rw [e]
      exact isHCParam_cast X.n_eq _ (Formalism.MainNotions.S.Inh.aut_isHCParam_lamS D.R (D.hc (X.pl v)))
    · obtain ⟨d, hd⟩ := GlobalTheory.Mem.Vol.exists_isFdeg_smul_of_isDS _ _ _ _ _ (X.ds v) 1 one_pos
      rw [ENNReal.coe_one, one_smul] at hd
      have hw : X.B.w v ≠ 0 := by
        intro h0
        have h1 := (X.low v).1
        rw [h0, norm_zero] at h1
        exact zero_ne_one h1
      have e2 : X.dv v = d := Formalism.L2.SG.Pf.RowDictPf.fdegOf_eq hd hw
      rw [e2]
      exact hd

  have hgap : GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) := by
    intro v a b hab
    have hne : (a : ℕ) ≠ (b : ℕ) := fun h => hab (by rw [Fin.ext h])
    rw [X.lam_eq, X.lam_eq, Formalism.IndefR.ModelConjugation.lamS_eq, Formalism.IndefR.ModelConjugation.lamS_eq]
    simp only [Fin.val_cast]
    rcases lt_or_gt_of_ne hne with h | h
    · have g := lamAt_gap hH (X.pl v) a b h (by have := b.2; have := X.n_eq; omega)
      have g' : (100 * (D.R.r : ℝ) ^ 4) ≤ ((Formalism.L2.NTheta.lamAt (D.hc (X.pl v)) a : ℚ) : ℝ) -
          ((Formalism.L2.NTheta.lamAt (D.hc (X.pl v)) b : ℚ) : ℝ) := by exact_mod_cast g
      exact le_abs.2 (Or.inl g')
    · have g := lamAt_gap hH (X.pl v) b a h (by have := a.2; have := X.n_eq; omega)
      have g' : (100 * (D.R.r : ℝ) ^ 4) ≤ ((Formalism.L2.NTheta.lamAt (D.hc (X.pl v)) b : ℚ) : ℝ) -
          ((Formalism.L2.NTheta.lamAt (D.hc (X.pl v)) a : ℚ) : ℝ) := by exact_mod_cast g
      exact le_abs.2 (Or.inr (by linarith))

  have hh : ∀ v, 120 * (X.B.I.n : ℝ) * ((GlobalTheory.Count.rkR (X.B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤
      100 * (D.R.r : ℝ) ^ 4 := by
    intro v
    rw [← hn]
    exact rank_bound _ _ (two_mul_rkR_le _)
  have hbig : GlobalTheory.Dec.HBig X.B 40 (100 * (D.R.r : ℝ) ^ 4) := by
    intro v
    rw [← hn]
    exact big_bound _ _ (two_mul_rkR_le _)

  have hD := GlobalTheory.DecGapBound.decGap_of_formulaGap GlobalTheory.Jet.FormGapFree.formulaGap
  have hloc : GlobalTheory.Dec.LocDec X.B (100 * (D.R.r : ℝ) ^ 4) :=
    GlobalTheory.Dec.locDec_of_decGap_gapGe hD X.B X.dv _ hds hgap hh
  obtain ⟨hc, hle, hint⟩ := GlobalTheory.Dec.PhMajProof.phMaj X.B X.dv _ hds hloc
  have hI := hint 0 le_rfl fun v => gap_numeric' _ _ (hh v)
  have hph : Integrable (GlobalTheory.Count.ph X.B X.dv) (GlobalTheory.Dec.muInf X.B.I) := by
    refine hI.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall fun g => ?_)
    simpa using hle g
  have hph' : Integrable X.ph (Formalism.L2.SG.ProjRows.muInf X.B.I) := hph
  exact ⟨hds, hloc, hbig, hh, hph', GlobalTheory.ProdFactor.integrable_phLoc_of_integrable_ph D X hph'⟩

end GlobalTheory.DSGapData
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsBoundMatrixBySymplecticFormHomAtRealPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bound_matrix_by_symplecticFormHomAtRealPlace : ∀ (D : D7) (S T : HSp D) (τ : D.what₂.Tau), ∃ (n : ℕ) (zs : Fin n → Matrix (Fin T.rank) (Fin S.rank) ℂ) (κ : ℝ), ∀ X : Matrix (Fin T.rank) (Fin S.rank) ℂ, ∑ i, ∑ j, ‖X i j‖ ≤ κ * ∑ l, |GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt S T τ (zs l) X| := by
  first | exact @GlobalTheory.SymplBound.bound | exact GlobalTheory.SymplBound.bound | (intros; apply GlobalTheory.SymplBound.bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCompactFiniteComponentsOfAnnihilatorOpenSuStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compact_finiteComponents_of_annihilator_openSubgroup : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (U : AddSubgroup (WO S T)), IsOpen (U : Set (WO S T)) → ∃ Q : Set (WO S T), IsCompact Q ∧ ∀ w : WO S T, (∀ u ∈ U, u.map (infPart D) = 0 → ψ (symplO S T w u) = 1) → GlobalTheory.Unf.InBox Q w := by
  first | exact @GlobalTheory.AnnihMat.annihilator_inBox_full | exact GlobalTheory.AnnihMat.annihilator_inBox_full | (intros; apply GlobalTheory.AnnihMat.annihilator_inBox_full <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteGroupActionPrincipalLevelFixedVector
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.PrinFixedRep

variable {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank}
  {W : Type} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (GfC V) W}

theorem mem_fixed_iff {x : W} :
    x ∈ GlobalTheory.PRep.fixed σ ((levG V β (flag1L L)).subgroupOf (GfC V)) ↔
      ∀ h : GfC V, (h : GA D V) ∈ levG V β (flag1L L) → σ h x = x := by
  unfold GlobalTheory.PRep.fixed GlobalTheory.PRep.eig
  simp only [Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq,
    MonoidHom.one_apply, Units.val_one, one_smul]
  constructor
  · intro H h hh
    exact H ⟨h, (Subgroup.mem_subgroupOf).2 hh⟩
  · intro H h
    exact H h ((Subgroup.mem_subgroupOf).1 h.2)

theorem act_eq_of_lifts {g0 : G0 L.Pg L.r} {κ κ' : GfC V} (hκ : IsLevelLift V β L g0 κ)
    (hκ' : IsLevelLift V β L g0 κ') {x : W}
    (hx : x ∈ GlobalTheory.PRep.fixed σ ((levG V β (flag1L L)).subgroupOf (GfC V))) : σ κ' x = σ κ x := by
  have hm : ((κ⁻¹ * κ' : GfC V) : GA D V) ∈ levG V β (flag1L L) := by
    simpa using lift_div_mem hκ hκ'
  have e : κ' = κ * (κ⁻¹ * κ') := by group
  rw [e, map_mul, Module.End.mul_apply, (mem_fixed_iff.1 hx) _ hm]

theorem act_mem_fixed {g0 : G0 L.Pg L.r} {κ : GfC V} (hκ : IsLevelLift V β L g0 κ) {x : W}
    (hx : x ∈ GlobalTheory.PRep.fixed σ ((levG V β (flag1L L)).subgroupOf (GfC V))) :
    σ κ x ∈ GlobalTheory.PRep.fixed σ ((levG V β (flag1L L)).subgroupOf (GfC V)) := by
  rw [mem_fixed_iff] at hx ⊢
  intro h hh
  have hc := (GlobalTheory.FlagAction.conj_mem_flag1 hκ hh).1
  have hc' : ((κ⁻¹ * (h * κ) : GfC V) : GA D V) ∈ levG V β (flag1L L) := by simpa using hc
  have e : h * κ = κ * (κ⁻¹ * (h * κ)) := by group
  rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, hx _ hc']

theorem main : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank),
    LiftsExist V β L → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W),
    ∃ ρ : Representation ℂ (G0 L.Pg L.r) (GlobalTheory.PRep.fixed σ ((levG V β (flag1L L)).subgroupOf (GfC V))),
      ∀ (g0 : G0 L.Pg L.r) (κ : GfC V), IsLevelLift V β L g0 κ → ∀ x, (ρ g0 x : W) = σ κ x := by
  intro D V β L hl W _ _ σ
  let lift : G0 L.Pg L.r → GfC V := fun g0 => ⟨(hl g0).choose, (hl g0).choose_spec.1⟩
  have hlift : ∀ g0, IsLevelLift V β L g0 (lift g0) := fun g0 => (hl g0).choose_spec
  let F := GlobalTheory.PRep.fixed σ ((levG V β (flag1L L)).subgroupOf (GfC V))
  have hs : ∀ g0, ∀ x ∈ F, σ (lift g0) x ∈ F := fun g0 x hx => act_mem_fixed (hlift g0) hx
  let ρ : Representation ℂ (G0 L.Pg L.r) F :=
    { toFun := fun g0 => (σ (lift g0)).restrict (hs g0)
      map_one' := LinearMap.ext fun x => Subtype.ext (by
        show σ (lift 1) x = x
        have h1 : IsLevelLift V β L 1 ((1 : GfC V) : GA D V) :=
          GlobalTheory.FlagAction.isLift_one_of_mem (Subgroup.one_mem _)
        rw [act_eq_of_lifts h1 (hlift 1) x.2, map_one, Module.End.one_apply])
      map_mul' := fun g g' => LinearMap.ext fun x => Subtype.ext (by
        show σ (lift (g * g')) x = σ (lift g) (σ (lift g') x)
        have hm : IsLevelLift V β L (g * g') ((lift g * lift g' : GfC V) : GA D V) :=
          GlobalTheory.FlagAction.isLift_mul (hlift g) (hlift g')
        rw [act_eq_of_lifts hm (hlift (g * g')) x.2, map_mul, Module.End.mul_apply]) }
  refine ⟨ρ, fun g0 κ hκ x => ?_⟩
  show σ (lift g0) x = σ κ x
  exact act_eq_of_lifts hκ (hlift g0) x.2

end GlobalTheory.PrinFixedRep

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInequivalentRepresentativesThroughMember
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S

namespace GlobalTheory.TrUnion

theorem exists_reps_through : ∀ (G : Type) [Group G] [TopologicalSpace G] (m : ℕ) (W : Fin m → Type) [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)] (σ : ∀ i, Representation ℂ G (W i)), ∀ i₀ : Fin m, ∃ (n : ℕ) (s : Fin n → Fin m), (∀ i j, i ≠ j → IsEmpty ((σ (s i)).Equiv (σ (s j)))) ∧ (∃ j, s j = i₀) ∧ ∀ i, ∃ j, Nonempty ((σ i).Equiv (σ (s j))) := by
  intro G _ _ m W _ _ σ i₀
  classical
  let R : Fin m → Fin m → Prop := fun i j => Nonempty ((σ i).Equiv (σ j))
  have hrefl : ∀ i, R i i := fun i => ⟨Representation.Equiv.refl _⟩
  have hsymm : ∀ {i j}, R i j → R j i := fun ⟨e⟩ => ⟨e.symm⟩
  have htrans : ∀ {i j k}, R i j → R j k → R i k := fun ⟨e⟩ ⟨e'⟩ => ⟨e.trans e'⟩
  let S : Setoid (Fin m) := ⟨R, ⟨hrefl, hsymm, htrans⟩⟩
  let f : Fin m → Fin m := fun i => if R i i₀ then i₀ else (Quotient.mk S i).out
  have hf : ∀ i, R (f i) i := by
    intro i
    by_cases h : R i i₀
    · simp only [f, if_pos h]; exact hsymm h
    · simp only [f, if_neg h]; exact Quotient.mk_out (s := S) i
  have hfc : ∀ i j, R i j → f i = f j := by
    intro i j hij
    by_cases h : R i i₀
    · have h' : R j i₀ := htrans (hsymm hij) h
      simp only [f, if_pos h, if_pos h']
    · have h' : ¬ R j i₀ := fun h' => h (htrans hij h')
      simp only [f, if_neg h, if_neg h']
      rw [Quotient.sound (s := S) hij]
  let T : Finset (Fin m) := Finset.univ.image f
  let e : T ≃ Fin T.card := T.equivFin
  refine ⟨T.card, fun k => (e.symm k).1, ?_, ?_, ?_⟩
  · intro k l hkl
    refine ⟨fun hR => ?_⟩
    apply hkl
    obtain ⟨x, -, hx⟩ := Finset.mem_image.1 (e.symm k).2
    obtain ⟨y, -, hy⟩ := Finset.mem_image.1 (e.symm l).2
    have hxy : R x y := by
      have h1 : R (f x) (f y) := by rw [hx, hy]; exact ⟨hR⟩
      exact htrans (hsymm (hf x)) (htrans h1 (hf y))
    have : (e.symm k).1 = (e.symm l).1 := by rw [← hx, ← hy]; exact hfc x y hxy
    exact e.symm.injective (Subtype.ext this)
  · have hmem : i₀ ∈ T := Finset.mem_image.2 ⟨i₀, Finset.mem_univ _, by simp only [f, if_pos (hrefl i₀)]⟩
    exact ⟨e ⟨i₀, hmem⟩, by simp⟩
  · intro i
    have hmem : f i ∈ T := Finset.mem_image_of_mem f (Finset.mem_univ i)
    refine ⟨e ⟨f i, hmem⟩, ?_⟩
    show R i (e.symm (e ⟨f i, hmem⟩)).1
    rw [Equiv.symm_apply_apply]
    exact hsymm (hf i)

end GlobalTheory.TrUnion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsKProjectorFiniteDimStatement
section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_K_projector_finite_dim : GlobalTheory.Published.IrreducibleUnitaryAdmissible → ∀ (n : ℕ) (ε : Fin n → Bool) (U : Type) [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U] (π : UJ ε →* (U →L[ℂ] U)), IsUnitaryRep π → IsTopIrreducible π → ∀ S : Submodule ℂ U, FiniteDimensional ℂ S → (∀ k ∈ KG ε, ∀ u ∈ S, π k u ∈ S) → ∃ φ : KG ε → ℂ, Continuous φ ∧ (∀ s ∈ S, ∫ k, φ k • π k s ∂(muK ε) = s) ∧ FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun u : U => ∫ k, φ k • π k u ∂(muK ε))) := by
  first | exact @GlobalTheory.KAvgFinite.fix_and_finite_range | exact GlobalTheory.KAvgFinite.fix_and_finite_range | (intros; apply GlobalTheory.KAvgFinite.fix_and_finite_range <;> assumption)
end

