import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUgReindex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1867
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0140
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0173
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1696
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1842
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1714
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1783
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1726
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1721
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1847
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1833
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1816
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1865
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0258
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0354
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeUnitNormSqNonneg
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0278
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1063
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaVacuaConjugatesCmPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1852
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0296
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstJetOperatorNormCauchyBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1848
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1849
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0533
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1378
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0174
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0244

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledWeilDatumDiagActsOnExternalProduct
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DblRestrictChar

open Formalism.IndefR.Datum

set_option maxHeartbeats 1000000 in

theorem dbl_diag_box : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
      (ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ)),
      Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
      ∀ ωd : GA D S × GA D (GlobalTheory.Doubling.dblSp T) →* Module.End ℂ (Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) → ℂ),
        Formalism.IndefR.Datum.IsWeilDatumO ψ S (GlobalTheory.Doubling.dblSp T) χS 1 ωd →
        (∀ (h : GA D T) (hd : GA D (GlobalTheory.Doubling.dblSp T)),
          Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp T) hd =
            Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (Formalism.L2.Theta.mt T h) 0 0 1) →
          ∃ c : ℂ, ∀ f₁ f₂ : Formalism.IndefR.Datum.WO S T → ℂ,
            Formalism.IndefR.Datum.IsThetaFunO ψ S T f₁ → Formalism.IndefR.Datum.IsThetaFunO ψ S T f₂ →
              ωd (1, hd) (fun w : Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) => f₁ (w.submatrix (finSumFinEquiv ∘ Sum.inl) id) * star (f₂ (w.submatrix (finSumFinEquiv ∘ Sum.inr) id))) = c • (fun w : Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) => ω (1, h) f₁ (w.submatrix (finSumFinEquiv ∘ Sum.inl) id) * star (f₂ (w.submatrix (finSumFinEquiv ∘ Sum.inr) id)))) →
        ∀ (h : GA D T) (hd : GA D (GlobalTheory.Doubling.dblSp T)),
          Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp T) hd =
            Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (Formalism.L2.Theta.mt T h) 0 0 1) →
          ∀ f₁ f₂ : Formalism.IndefR.Datum.WO S T → ℂ,
            Formalism.IndefR.Datum.IsThetaFunO ψ S T f₁ → Formalism.IndefR.Datum.IsThetaFunO ψ S T f₂ →
              ωd (1, hd) (fun w : Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) => f₁ (w.submatrix (finSumFinEquiv ∘ Sum.inl) id) * star (f₂ (w.submatrix (finSumFinEquiv ∘ Sum.inr) id))) = (fun w : Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) => ω (1, h) f₁ (w.submatrix (finSumFinEquiv ∘ Sum.inl) id) * star (f₂ (w.submatrix (finSumFinEquiv ∘ Sum.inr) id))) := by
  intro D ψ hψ S T χS χT ω hω ωd hωd _ h hd hhd f₁ f₂ hf₁ hf₂
  obtain ⟨ωB, hB⟩ := GlobalTheory.WeilExist.exists_isWeilDatumO D ψ hψ S (GlobalTheory.ChiGrid.negSp T) χS χT⁻¹
    (GlobalTheory.WeilParts.exists_isEtaTilde_unramified D) hω.hecS (GlobalTheory.HeckeCharsOfSquare.isHeckeChar_inv hω.hecT) hω.resS
    (resEta_inv hω.resT)
  let d := GlobalTheory.BiTransfer.sumDec T (GlobalTheory.ChiGrid.negSp T)
  have hωd' : IsWeilDatumO ψ S (GlobalTheory.Doubling.hsum T (GlobalTheory.ChiGrid.negSp T)) χS (χT * χT⁻¹) ωd := by
    rw [mul_inv_cancel]; exact hωd
  have key := (GlobalTheory.TensorTargetRule.tensorTarget D ψ hψ _ T (GlobalTheory.ChiGrid.negSp T) d S).om_box χS χT χT⁻¹ ωd ω ωB
    hωd' hω hB 1 h 1 f₁ (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f₂) hf₁ (GlobalTheory.CjNeg.theta_negT hψ hf₂)
  have e1 : d.emb (h, 1) = hd := by
    apply GlobalTheory.MixModel.mt_injective (GlobalTheory.Doubling.hsum T (GlobalTheory.ChiGrid.negSp T))
    rw [GlobalTheory.SeesawSumTarget.emb_sumDec, GlobalTheory.SquareComm.mt_blk]
    refine Eq.trans ?_ hhd.symm
    rw [GlobalTheory.Doubling.blkMat, Matrix.reindex_apply, GlobalTheory.AdelicLatMove.mt_one]
  have e2 : ωB ((1 : GA D S), (1 : GA D (GlobalTheory.ChiGrid.negSp T))) = 1 := map_one ωB
  rw [e1, e2, Module.End.one_apply, GlobalTheory.SeesawSumTarget.boxT_sumDec, GlobalTheory.SeesawSumTarget.boxT_sumDec] at key
  exact key

end GlobalTheory.DblRestrictChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

open scoped Classical

namespace GlobalTheory.TensUniq

theorem exists_sInf_ne_zero (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    ∃ f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ, f 0 ≠ 0 := by
  let b : ContDiffBump (0 : κ → mixedEmbedding.mixedSpace F) := ⟨1, 2, one_pos, one_lt_two⟩
  have hc : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) := b.hasCompactSupport.comp_left Complex.ofReal_zero
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fun x => ((b x : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp b.contDiff
  refine ⟨hc.toSchwartzMap hd, ?_⟩
  have h1 : b 0 = 1 := b.one_of_mem_closedBall (by simp [b])
  show ((b 0 : ℝ) : ℂ) ≠ 0
  rw [h1]; exact one_ne_zero

theorem pure_mem_schA {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ)
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F v) → ℂ) (hSB : ∀ v, φ v ∈ GlobalTheory.WeilM.SB _)
    (hstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ GlobalTheory.WeilM.schA F κ := by
  have hg : (fun y : κ → FiniteAdeleRing (𝓞 F) F => ∏ᶠ v, φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) ∈
      GlobalTheory.WeilM.SB _ :=
    ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV φ hSB hstd, GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ hSB hstd⟩
  exact Submodule.subset_span ⟨f, _, hg, rfl⟩

end GlobalTheory.TensUniq

namespace GlobalTheory.TensUniq

theorem eq_of_tens_eq : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)
    (φ φ₁ φ₂ : (κ → Fv F v) → ℂ), φ ∈ GlobalTheory.WeilM.SB _ →
    (∀ r, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin F v) φ r → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ₁ r = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ₂ r) →
    φ₁ = φ₂ := by
  intro F _ _ κ _ v φ φ₁ φ₂ hφ h
  obtain ⟨f, hf⟩ := exists_sInf_ne_zero F κ
  let φs : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F w) → ℂ :=
    fun w => Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1
  have hstd : ∀ᶠ w in Filter.cofinite, φs w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 :=
    Filter.Eventually.of_forall fun _ => rfl
  obtain ⟨r, hr, hrt⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φs hstd
  have hRest : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin F v) φ r := by
    refine ⟨hr, ?_⟩
    rw [hrt φ]
    refine pure_mem_schA f _ (fun w => ?_) (GlobalTheory.PureFactor.update_eventually φs v φ hstd)
    by_cases hw : w = v
    · subst hw; rw [Function.update_self]; exact hφ
    · rw [Function.update_of_ne hw]; exact GlobalTheory.StdVacuum.indicator_mem_SB w
  have hr0 : r 0 ≠ 0 := by
    have e := congrFun (hrt (fun _ => 1)) 0
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, one_mul] at e
    rw [e]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
    have hI : (fun i : κ => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F ((0 : κ → AF F) i)) = 0 := by
      funext i
      show (InfiniteAdeleRing.ringEquiv_mixedSpace F) (0 : AF F).1 = 0
      exact map_zero _
    have hP : (∏ᶠ w, Function.update φs v (fun _ => 1) w fun i => evFin F w ((0 : κ → AF F) i)) = 1 := by
      refine finprod_eq_one_of_forall_eq_one fun w => ?_
      by_cases hw : w = v
      · subst hw; rw [Function.update_self]
      · rw [Function.update_of_ne hw]
        simp only [φs, Pi.zero_apply, map_zero]
        rw [Set.indicator_of_mem (by intro i; exact zero_mem _)]
        rfl
    rw [hI, hP, mul_one]
    exact hf
  funext y
  let z : κ → AF F := fun i => GlobalTheory.LatVac.liftV v (y i)
  have hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z := by
    intro u hu
    funext i
    exact GlobalTheory.LatVac.at_liftV v (y i) u hu
  have hrz : r z = r 0 := by
    have := hr 0 z hz
    rwa [zero_add] at this
  have hev : (fun i => evFin F v (z i)) = y := by
    funext i; exact GlobalTheory.LatVac.evFin_liftV v (y i)
  have e := congrFun (h r hRest) z
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, hev, hrz] at e
  exact mul_right_cancel₀ hr0 e

end GlobalTheory.TensUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfIsFiniteAdelicPointSameStatement
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_isFiniteAdelicPoint_same : ∀ {D : D7} (V : HSp D) {n : ℕ} (g g' : GA D V) (x : Formalism.MainNotions.StandardLatticesGL3.GA D n),
  IsFinPt V g x → IsFinPt V g' x → g = g' := by
  first | exact @GlobalTheory.FinPtUnique.eq_of_isFinPt | exact GlobalTheory.FinPtUnique.eq_of_isFinPt | (intros; apply GlobalTheory.FinPtUnique.eq_of_isFinPt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyParameterSizesTestChoicesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_parameterSizes_testChoices : BigC fun {D} _ _ _ _ _ A _ _ _ _ _ _ ch _ b => 3 ≤ b ∧ 1 ≤ bigN D ∧ (bigN D : ℝ) ≤ b ∧ 1 ≤ D.R.f ∧ (D.R.f : ℝ) ≤ b ∧
  Fintype.card D.what₂.Tau ≤ D.R.f ∧ 0 ≤ D.host.rdE ∧ D.host.rdE ≤ b ∧ ∀ j : ℕ, j ≤ D.R.m →
    (ch.G.V (.top j)).rank ≤ bigN D ∧ ∀ τ i, ((wt ch.G (.top j) τ).natW i : ℝ) ≤ 8 * b := by
  first | exact @GlobalTheory.KerConjMean.TopSizes.sizesK | exact GlobalTheory.KerConjMean.TopSizes.sizesK | (intros; apply GlobalTheory.KerConjMean.TopSizes.sizesK <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmissibleFormConvergentThetaIntegral
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open Filter Topology
open scoped ENNReal

noncomputable section

namespace GlobalTheory.ThetaIntAdm

theorem exists_clm_integral {S Ω : Type} [AddCommGroup S] [Module ℂ S] [TopologicalSpace S] [IsTopologicalAddGroup S]
    [FirstCountableTopology S] [BarrelledSpace ℂ S] [MeasurableSpace Ω] (μ : Measure Ω) (T : Ω → S →L[ℂ] ℂ)
    (hint : ∀ f, Integrable (fun x => T x f) μ) : ∃ L : S →L[ℂ] ℂ, ∀ f, L f = ∫ x, T x f ∂μ := by
  let q : Seminorm ℂ S := Seminorm.of (fun f => ∫ x, ‖T x f‖ ∂μ)
    (fun f g => by
      have hf := (hint f).norm
      have hg := (hint g).norm
      have hfg := (hint (f + g)).norm
      rw [← integral_add hf hg]
      exact integral_mono hfg (hf.add hg) fun x => by simp only [map_add]; exact norm_add_le _ _)
    (fun c f => by
      rw [← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun x => by simp [map_smul, norm_mul]))
  have hq : ∀ f, q f = ∫ x, ‖T x f‖ ∂μ := fun f => rfl
  have hlsc : LowerSemicontinuous q := by
    rw [lowerSemicontinuous_iff_isClosed_preimage]
    intro c
    apply IsSeqClosed.isClosed
    intro y y₀ hy hlim
    have hc : 0 ≤ c := le_trans (apply_nonneg _ _) (hy 0)
    show q y₀ ≤ c
    rw [hq, integral_norm_eq_lintegral_enorm (hint y₀).aestronglyMeasurable]
    apply ENNReal.toReal_le_of_le_ofReal hc
    have hpt : ∀ x, Tendsto (fun n => ‖T x (y n)‖ₑ) atTop (𝓝 ‖T x y₀‖ₑ) := fun x =>
      ((T x).continuous.enorm.continuousAt.tendsto).comp hlim
    calc ∫⁻ x, ‖T x y₀‖ₑ ∂μ = ∫⁻ x, liminf (fun n => ‖T x (y n)‖ₑ) atTop ∂μ := by
          congr 1; funext x; exact (hpt x).liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ x, ‖T x (y n)‖ₑ ∂μ) atTop :=
          lintegral_liminf_le' fun n => (hint (y n)).aestronglyMeasurable.enorm
      _ ≤ liminf (fun _ : ℕ => ENNReal.ofReal c) atTop := by
          refine liminf_le_liminf (Eventually.of_forall fun n => ?_)
          show ∫⁻ x, ‖T x (y n)‖ₑ ∂μ ≤ ENNReal.ofReal c
          rw [← ofReal_integral_norm_eq_lintegral_enorm (hint (y n))]
          exact ENNReal.ofReal_le_ofReal (hy n)
      _ = ENNReal.ofReal c := liminf_const _
  have hqc : Continuous q := Seminorm.continuous_of_lowerSemicontinuous _ hlsc
  let L : S →ₗ[ℂ] ℂ :=
    { toFun := fun f => ∫ x, T x f ∂μ
      map_add' := fun f g => by simp only [map_add]; exact integral_add (hint f) (hint g)
      map_smul' := fun c f => by simp only [map_smul, smul_eq_mul, RingHom.id_apply]; exact integral_const_mul c _ }
  have hL0 : ContinuousAt L 0 := by
    rw [ContinuousAt, map_zero]
    refine squeeze_zero_norm (a := fun f => q f) (fun f => ?_) ?_
    · exact norm_integral_le_integral_norm _
    · have := hqc.tendsto 0
      rwa [map_zero] at this
  exact ⟨⟨L, continuous_of_continuousAt_zero L.toAddMonoidHom hL0⟩, fun f => rfl⟩

end GlobalTheory.ThetaIntAdm

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (theta)
open scoped Classical

theorem GlobalTheory.ThetaIntAdm.exists_admissible_form_convergent_thetaIntegral : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {Y : Spc F E d} (M : Model σ X Y)
    (ψ : AddChar (AF F) ℂ) (χX χY : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : Rep σ X Y), M.IsWeil ψ χX χY om →
    (∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), M.Conv om Φ) →
    ∃ l ∈ (GlobalTheory.WeilM.adeleClass F).adm (Fin n × Fin d), ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), l Φ = M.I om Φ 1 := by
  intro F E _ _ _ _ _ σ n d X Y M ψ χX χY om hW hC
  obtain ⟨l₀, hl₀, hl₀e⟩ := GlobalTheory.T.exists_admitted_form_eq_adelicThetaDistribution F (Fin n × Fin d)
  have hS := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hW
  have pres : ∀ p, ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), om p Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d) :=
    hS.pres
  have adm : ∀ p, ∀ l ∈ (GlobalTheory.WeilM.adeleClass F).adm (Fin n × Fin d),
      l ∘ₗ om p ∈ (GlobalTheory.WeilM.adeleClass F).adm (Fin n × Fin d) := hS.adm
  have th : ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), ∀ g, theta om Φ g 1 = l₀ (om (g, 1) Φ) :=
    fun Φ hΦ g => (hl₀e _ (pres _ Φ hΦ)).symm
  let fI : GlobalTheory.WeilM.schA F (Fin n × Fin d) →ₗ[ℂ] ℂ :=
    { toFun := fun Φ => M.I om Φ.1 1
      map_add' := fun Φ Ψ => by
        have e : (fun g => theta om (Φ + Ψ).1 g 1) = fun g => theta om Φ.1 g 1 + theta om Ψ.1 g 1 := by
          funext g
          rw [th _ (Φ + Ψ).2, th _ Φ.2, th _ Ψ.2, Submodule.coe_add, map_add, map_add]
        show ∫ g in M.dom, theta om (Φ + Ψ).1 g 1 ∂M.μ = ∫ g in M.dom, theta om Φ.1 g 1 ∂M.μ + ∫ g in M.dom, theta om Ψ.1 g 1 ∂M.μ
        rw [e]
        exact integral_add (hC _ Φ.2 1) (hC _ Ψ.2 1)
      map_smul' := fun c Φ => by
        have e : (fun g => theta om (c • Φ).1 g 1) = fun g => c * theta om Φ.1 g 1 := by
          funext g
          rw [th _ (c • Φ).2, th _ Φ.2, Submodule.coe_smul, map_smul, map_smul, smul_eq_mul]
        show ∫ g in M.dom, theta om (c • Φ).1 g 1 ∂M.μ = c • ∫ g in M.dom, theta om Φ.1 g 1 ∂M.μ
        rw [e, smul_eq_mul]
        exact integral_const_mul c _ }
  obtain ⟨l, hl⟩ := LinearMap.exists_extend fI
  have hlΦ : ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), l Φ = M.I om Φ 1 :=
    fun Φ hΦ => LinearMap.congr_fun hl ⟨Φ, hΦ⟩
  refine ⟨l, ?_, hlΦ⟩
  intro g₀ hg₀
  have mem : ∀ f : SchwartzMap (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ, GlobalTheory.WeilM.pureA F f g₀ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d) :=
    fun f => Submodule.subset_span ⟨f, g₀, hg₀, rfl⟩
  choose T hT using fun x : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J => adm (x, 1) l₀ hl₀ g₀ hg₀
  have eT : ∀ f : SchwartzMap (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ, (fun x => T x f) = fun x => theta om (GlobalTheory.WeilM.pureA F f g₀) x 1 := fun f => by
    funext x
    rw [← hT x f, th _ (mem f)]
    rfl
  haveI := GlobalTheory.T.schwartzMap_barrelledSpace' (Fin n × Fin d → mixedEmbedding.mixedSpace F)
  obtain ⟨L, hL⟩ := GlobalTheory.ThetaIntAdm.exists_clm_integral (M.μ.restrict M.dom) T
    (fun f => by rw [eT f]; exact hC _ (mem f) 1)
  refine ⟨L, fun f => ?_⟩
  rw [hlΦ _ (mem f), hL, eT f]
  rfl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgebraicNumbersExtensionCurveFieldConjLat
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean

namespace GlobalTheory.ConjExtend

theorem exists_extension_of_le (M : IntermediateField ℚ ℂ) (hle : M ≤ Qbar) (ρ : M →ₐ[ℚ] ℂ) :
    ∃ ρ' : Qbar →ₐ[ℚ] ℂ, ∀ x ∈ M, ρ' (TaylorLogMetric.liftM Qbar x) = ρ (TaylorLogMetric.liftM M x) := by
  let _ : Algebra M Qbar := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  have : IsScalarTower ℚ M Qbar := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have : Algebra.IsAlgebraic ℚ Qbar := algebraicClosure.isAlgebraic ℚ ℂ
  have : Algebra.IsAlgebraic M Qbar := Algebra.IsAlgebraic.tower_top (K := ℚ) M
  obtain ⟨φ, hφ⟩ := IsAlgClosed.surjective_domRestrict_of_isAlgebraic (K := ℚ) (L := M) (M := ℂ)
    (E := Qbar) ρ
  refine ⟨φ, fun x hx => ?_⟩
  rw [← hφ]
  unfold TaylorLogMetric.liftM
  rw [dif_pos hx, dif_pos (hle hx)]
  rfl

theorem fld_le (D : D7) (hI : GlobalTheory.NormSum.Inp D) (δ t0 : ℂ) (hc : Crv D D.host.ccK δ)
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D D.host.ccK δ) t0) : GlobalTheory.KerConjMean.fld D δ t0 ≤ Qbar := by
  obtain ⟨hdata, htor⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hI.g1).2 _ δ hc
  have hwp : wpF (lamOf D D.host.ccK δ) t0 ∈ Qbar := by
    refine (htor t0 ⟨2, two_pos, by exact_mod_cast ht.1⟩ fun h0 => ?_).1
    obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
    have h1 := GlobalTheory.ArchNorm.mul_mem_lamOf D _ δ a h0
    rw [ha, mul_comm] at h1
    exact ht.2.1 h1
  unfold GlobalTheory.KerConjMean.fld
  rw [IntermediateField.adjoin_le_iff]
  rintro y (⟨x, rfl⟩ | rfl | rfl | rfl)
  · exact mem_algebraicClosure_iff.2
      ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom D.what₂.embLL.toRatAlgHom)
  · exact hdata.2.1
  · exact hdata.2.2
  · exact hwp

theorem exists_extension_conj : ∀ (D : D7), GlobalTheory.NormSum.Inp D → ∀ (δ t0 : ℂ), Crv D D.host.ccK δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D D.host.ccK δ) t0 →
    ∀ (σ : D.what₂.LL →+* ℂ), ∀ ρ ∈ GlobalTheory.KerConjMean.ext D δ t0 σ, ∃ ρ' : Qbar →ₐ[ℚ] ℂ,
      (∀ x, Formalism.MainNotions.StandardLatticesGL3.cj Qbar ρ' (D.what₂.embLL x) = σ x) ∧
      lamConj Qbar ρ' (lamOf D D.host.ccK δ) = lamConj (GlobalTheory.KerConjMean.fld D δ t0) ρ (GlobalTheory.KerConjMean.lat D δ) := by
  intro D hI δ t0 hc ht σ ρ hρ
  obtain ⟨ρ', h⟩ := exists_extension_of_le _ (fld_le D hI δ t0 hc ht) ρ
  refine ⟨ρ', fun x => ?_, ?_⟩
  · unfold Formalism.MainNotions.StandardLatticesGL3.cj
    rw [h _ (GlobalTheory.KerConjMean.embLL_mem D δ t0 x), ← hρ x]
    unfold TaylorLogMetric.liftM
    rw [dif_pos (GlobalTheory.KerConjMean.embLL_mem D δ t0 x)]
  · have h2 : g2 (lamOf D D.host.ccK δ) ∈ GlobalTheory.KerConjMean.fld D δ t0 :=
      IntermediateField.subset_adjoin ℚ _ (Or.inr (by simp))
    have h3 : g3 (lamOf D D.host.ccK δ) ∈ GlobalTheory.KerConjMean.fld D δ t0 :=
      IntermediateField.subset_adjoin ℚ _ (Or.inr (by simp))
    unfold lamConj
    rw [h _ h2, h _ h3]

end GlobalTheory.ConjExtend
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstJetOperatorNormCauchyBoundStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_const_jetOperatorNorm_cauchyBound : ∃ K : ℝ, 0 ≤ K ∧ ∀ (D : D7) (a b : ℕ) (lam : D.what₂.Tau → DomWeight a) (lam' : D.what₂.Tau → DomWeight b)
  (n : D.what₂.Tau → ℕ), Formalism.L2.Ker.JetInVV ℂ lam lam' n → (∀ v, 0 ≤ nrm lam (fun _ => 1) v) ∧
  ∃ Kx : ℝ, 0 < Kx ∧ Real.log Kx ≤ K * ((∑ τ, ∑ i, ((lam τ).natW i : ℝ)) + (∑ τ, ∑ i, ((lam' τ).natW i : ℝ)) +
      (Fintype.card D.what₂.Tau : ℝ) * ((a : ℝ) + b) ^ 2 + 1) *
      Real.log (2 + (∑ τ, ∑ i, ((lam τ).natW i : ℝ)) + (∑ τ, ∑ i, ((lam' τ).natW i : ℝ)) + a + b + Fintype.card D.what₂.Tau) ∧
    ∀ (H : VC D a b → ℂ) (S A : ℝ), 0 < A → 0 ≤ S → Differentiable ℂ H →
      (∀ z, ‖H z‖ ^ 2 ≤ S * Real.exp (Real.pi * (∑ τ, ∑ i, ∑ j, ‖z τ i j‖ ^ 2) / A)) → ∀ v,
      nrm lam' (fun _ => 1) (Formalism.L2.Ker.jetOp lam lam' (fun m => GL3Theta.applyAt0 D (MvPolynomial.monomial m 1) H) n v) ≤
        S * Kx * max 1 A⁻¹ ^ (∑ τ, ∑ i, (lam' τ).natW i) * nrm lam (fun _ => 1) v := by
  first | exact @GlobalTheory.FockJetBound.jetOp_norm_le | exact GlobalTheory.FockJetBound.jetOp_norm_le | (intros; apply GlobalTheory.FockJetBound.jetOp_norm_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicEmbeddingStandardUnitaryGroupStatement
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteAdelicEmbedding_standardUnitaryGroup : ∀ {D : D7} (V : HSp D) (n : ℕ), V.gram = 1 → V.rank = n → ∃ ι : Formalism.MainNotions.StandardLatticesGL3.GA D n →* GA D V,
  (∀ x, IsFinPt V (ι x) x) ∧ Function.Injective ι ∧ ι.range = GfC V ∧
    ∀ x, (∃ γ ∈ GQ V, finHom V γ = finHom V (ι x)) ↔ x ∈ ratG D n := by
  first | exact @GlobalTheory.FinEmbStd.exists_finEmb | exact GlobalTheory.FinEmbStd.exists_finEmb | (intros; apply GlobalTheory.FinEmbStd.exists_finEmb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGramMatricesCmUnitaryShimuraObjectStatement
section
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.FlatCM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_gramMatrices_cmUnitaryShimuraObject : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p q : ℕ) (X : CMObj H K ρ σ₁ p q), ∃ gP gQ, IsGram X gP gQ := by
  first | exact @GlobalTheory.FlatCM.GramExists.exists_isGram | exact GlobalTheory.FlatCM.GramExists.exists_isGram | (intros; apply GlobalTheory.FlatCM.GramExists.exists_isGram <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarFundamentalDomainUnitaryQuotientVolume
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)

noncomputable section

namespace GlobalTheory.RowTest.BottomMeas

theorem exists_haar_fd_volQ_ne_zero : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} (W : G.Weil) (i j : Fin D.R.m)
    (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X →
    ∃ (ν : Measure (GA D WW)) (𝓕 : Set (GA D WW)), ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ WW) 𝓕 ν ∧ volQ WW ν ≠ 0 := by
  intro D T L sc G W i j A A' WW X _
  obtain ⟨ν, 𝓕, hν, h𝓕⟩ := GlobalTheory.ConstRatio.exists_meas WW
  have : BorelSpace (GA D WW) := ⟨rfl⟩
  refine ⟨ν, 𝓕, hν, h𝓕, ?_⟩
  haveI := GlobalTheory.RegSch.Ibp.isFiniteMeasure_autMeasure (V := WW) ν
  rw [(GlobalTheory.QuotFundDom.volQ_and_integrable_iff D WW ν 𝓕 hν h𝓕).1]
  refine ENNReal.toReal_ne_zero.2 ⟨h𝓕.measure_ne_zero (NeZero.ne ν), ?_⟩
  exact (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol WW ν _ hν h𝓕).ne

end GlobalTheory.RowTest.BottomMeas

end
end

