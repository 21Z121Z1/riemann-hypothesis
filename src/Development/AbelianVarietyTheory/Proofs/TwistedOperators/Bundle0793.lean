import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0393
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0033
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0174
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0606
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0222
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0265
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0036
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0005
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0031
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0791
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0174
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0016
import Development.AutomorphicArithmetic.LocalEmbeddings.Bundle0003
import Development.AutomorphicArithmetic.LocalEmbeddings.JetsTest
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0537
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0790
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0575
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Formalism.LocalToGlobal.Columns.PolyFnLemmas
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkMapInitMinor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0780
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumFinitePairVacuumAlgebraicCombination
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0533
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0841
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0558
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableScalarActionMultiplicityMapValues
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ValAct

theorem integral_mul_multT_eq : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ t ∈ MultT θ M J χ, ∀ (w : M.Vec) (m : Measure (GinfC V)), m.IsHaarMeasure → ∀ (α : GinfC V → ℂ) (c : ℂ), Integrable α m → (∀ b : ∀ τ, M.H τ, ∫ h, α h * coefR θ M b (fun τ => w τ) h ∂m = c * ∏ τ, ⟪b τ, (w τ : M.H τ)⟫_ℂ) → ∀ x, ∫ h, α h * t (PiTensorProduct.tprod ℂ w) (x * h) ∂m = c * t (PiTensorProduct.tprod ℂ w) x := by
  intro hP D θ hθ V S M J χ t ht w m hm α c hα hc
  obtain rfl := Formalism.IndefR.Eqv.eq_thetaC D hθ
  obtain ⟨i1, i2, i3, i4, i5⟩ := Formalism.IndefR.Eqv.ga_facts D V
  obtain ⟨-, -, -, -, -, j6, j7, j8⟩ := GlobalTheory.RealMeasOne.ginfC_facts V
  haveI := hm
  haveI := Formalism.IndefR.Eqv.gQ_countable D V
  have hT : PiTensorProduct.lift.symm t ∈ Mult (Formalism.IndefR.Eqv.thetaC D) M J χ := (mem_multT _ M J χ t).1 ht
  have hTv : ∀ (v : M.Vec) g, (PiTensorProduct.lift.symm t) v g = t (PiTensorProduct.tprod ℂ v) g := fun v g => rfl
  have hEq := Formalism.IndefR.AutomorphicEvaluation.eqCont_of_mem hT
  obtain ⟨haut, hcusp, -⟩ := GlobalTheory.ChainOnto.MultRapid.multT_apply_rapidDec hP D V S M _ hθ J χ t ht (PiTensorProduct.tprod ℂ w)
  obtain ⟨B, hB⟩ := GlobalTheory.CuspDecay.bounded_of_cuspForm hP hθ haut hcusp
  have hφc : Continuous (t (PiTensorProduct.tprod ℂ w)) := GlobalTheory.BaseChain.multT_apply_continuous _ M J χ t ht _
  have htr : ∀ (h : GinfC V) y, t (PiTensorProduct.tprod ℂ w) (y * h) =
      t (PiTensorProduct.tprod ℂ (Formalism.L2.SG.EvalTEquiv.transl M h w)) y := fun h y => by
    have := Formalism.L2.SG.EvalTEquiv.equiv_ginf hθ hEq h.2 w y
    rwa [hTv, hTv] at this
  let μ : Measure (GA D V) := Measure.haar
  obtain ⟨𝓕, -, h𝓕⟩ := Formalism.IndefR.Eqv.fundDomExists_holds D V
  have hfd := h𝓕 μ
  have hfin : μ 𝓕 < ⊤ := GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol V μ 𝓕 inferInstance hfd
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.schurMult_multiplicitySpaces_of_rapidDecay hP D _ hθ V S M J χ μ 𝓕 inferInstance hfd hθ inferInstance hfd _ hT _ hT
  have hS : ∀ v v' : M.Vec, ∫ g in 𝓕, star (t (PiTensorProduct.tprod ℂ v) g) * t (PiTensorProduct.tprod ℂ v') g ∂μ =
      κ * ∏ τ, ⟪(v τ : M.H τ), (v' τ : M.H τ)⟫_ℂ := fun v v' => by
    have := (hκ v v').2
    simp only [hTv] at this
    exact this
  have hcoef : ∀ (b : ∀ τ, M.H τ) (h : GinfC V), coefR (Formalism.IndefR.Eqv.thetaC D) M b (fun τ => w τ) h =
      ∏ τ, ⟪b τ, (Formalism.L2.SG.EvalTEquiv.transl M h w τ : M.H τ)⟫_ℂ := fun b h => by
    simp only [coefR, Formalism.L2.SG.EvalTEquiv.transl_apply]
  refine GlobalTheory.T.rightConv_eq_smul_of_inner_translates_eq (GQ V) μ 𝓕 hfd hfin m α hα _ hφc B hB
    (GlobalTheory.BaseChain.multT_apply_left _ M J χ t ht _) c fun h' => ?_
  have hψc : Continuous fun x => star (t (PiTensorProduct.tprod ℂ w) (x * (h' : GA D V))) :=
    (hφc.comp (continuous_id.mul continuous_const)).star
  rw [(GlobalTheory.T.integral_fundamentalDomain_convolution_comm_of_bounded μ 𝓕 hfin m α hα _ _ hψc hφc B B (fun g => by rw [norm_star]; exact hB _) hB).2.2]
  have e1 : ∀ h : GinfC V, ∫ x in 𝓕, star (t (PiTensorProduct.tprod ℂ w) (x * (h' : GA D V))) *
      t (PiTensorProduct.tprod ℂ w) (x * (h : GA D V)) ∂μ =
      κ * ∏ τ, ⟪(Formalism.L2.SG.EvalTEquiv.transl M h' w τ : M.H τ), (Formalism.L2.SG.EvalTEquiv.transl M h w τ : M.H τ)⟫_ℂ := by
    intro h
    simp only [htr]
    exact hS _ _
  simp_rw [e1]
  have e2 : ∫ x in 𝓕, star (t (PiTensorProduct.tprod ℂ w) (x * (h' : GA D V))) * t (PiTensorProduct.tprod ℂ w) x ∂μ =
      κ * ∏ τ, ⟪(Formalism.L2.SG.EvalTEquiv.transl M h' w τ : M.H τ), (w τ : M.H τ)⟫_ℂ := by
    simp only [htr]
    exact hS _ _
  rw [e2]
  have e3 := hc (fun τ => (Formalism.L2.SG.EvalTEquiv.transl M h' w τ : M.H τ))
  simp only [hcoef] at e3
  simp_rw [mul_left_comm _ κ]
  rw [integral_const_mul, e3]

end GlobalTheory.ValAct

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsTripleFactorStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matched_maps_triple_factor : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs G Xc om om' →
    ∀ (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    ∃ K, GlobalTheory.CoinvKer.IsThetaSub om Bs.emb (GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb) K ∧
      K ≠ GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb ∧
      ∀ ΦD ∈ GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb, (ΦD ∈ K ↔ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs G Xc R Rf ΦD 0) := by
  first | exact @GlobalTheory.PolKer.polMatch_zero_thetaSub | exact GlobalTheory.PolKer.polMatch_zero_thetaSub | (intros; apply GlobalTheory.PolKer.polMatch_zero_thetaSub <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TermVolumeClassSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

section
open GlobalTheory.DefStep GlobalTheory.JetsOne GlobalTheory.ExpansionInvariance

private theorem last_ok {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {μ0 : T} (hL : L.Is μ0) (Λ : Module.Dual ℂ (VV ℂ (wt G (.top D.R.m))))
    (Λ' : Module.Dual ℂ (VV ℂ (wt G (.grid D.R.m D.R.m)))) :
    ∃ (c : ℂ) (s : GA D (G.V (.grid D.R.m D.R.m)) →* GA D (G.V (.top D.R.m))), (∀ h, stabilizerEmbedding G.sp.topDec h = s h) ∧
      LastOK (realAct W.θ S.N.fr (.top D.R.m)) Λ (realAct W.θ S.N.fr (.grid D.R.m D.R.m)) Λ' s (finEmb G.sp.topDec)
        (c • brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m))) := by
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V (.grid D.R.m D.R.m))
  have hSC := hT.2.1
  have hB := hT.2.2.2.1
  have hG := hT.2.2.2.2.1
  have hdef := GlobalTheory.TopIntegral.isDefinite_last G
  haveI : CompactSpace (GinfC (G.V (.grid D.R.m D.R.m))) := isCompact_iff_compactSpace.1 (Eqv.isCompact_GinfC hdef.1 hdef.2)
  obtain ⟨κ₀, k1, k2⟩ := exists_haar _ hdef
  obtain ⟨c, hc⟩ := GlobalTheory.TopIntegral.real_average W.θ_is S.N Λ Λ' κ₀
  obtain ⟨s, h1, h2, h3⟩ := GlobalTheory.TopIntegral.exists_orthogonal_summand_embedding_hom G.sp.topDec
  refine ⟨c, s, h2, hdef, posDef_grid hL le_rfl, fun g hg => realAct_fin _ _ _ hg, fun g hg => realAct_fin _ _ _ hg, h1, h3,
    fun z => (h2 _).symm.trans (GlobalTheory.RealType.Emb_fin _ z), fun k hk => h2 k ▸ GlobalTheory.RealType.Emb_mem_inf _ hk,
    fun u u' => ?_, fun κ a1 a2 u u' => ?_⟩
  · simp only [← h2]
    exact (GlobalTheory.TopIntegral.continuous_integrand W.θ_is S.N Λ Λ' u u').comp continuous_subtype_val
  · obtain rfl : κ = κ₀ := Measure.isHaarMeasure_eq_of_isProbabilityMeasure κ κ₀
    simp only [← h2]
    exact hc u u'

private theorem pair_eq {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {t : T} (τ : PureDat G t →₀ ℂ) (c : ℂ) (Ψ : FinPt G (.top 0) → VV ℂ (wt G (.top 0)))
    (F : FinPt G (.grid 0 D.R.m) → VV ℂ (listedWt G (.grid 0 D.R.m))) (X : ∀ j, FinPt G (.top j))
    (Y : ∀ i, FinPt G (.grid i D.R.m)) :
    c * pairPts S τ X Y (Ψ (X 0)) (F (Y 0)) = τ.sum fun d a => a *
      GlobalTheory.JetsOne.pairP (V := fun j => G.V (.top j)) (V' := fun j => G.V (.grid j D.R.m)) (Mo := fun j => VV ℂ (wt G (.top j)))
        (Mo' := fun j => VV ℂ (wt G (.grid j D.R.m))) (colComp S d) (fun x => rhoVr (tauE D) _ (S.N.fr (.top 0))⁻¹ (Ψ x))
        (rowComp S d) (fun x => rhoVr (tauE D) (wt G (.grid 0 D.R.m)) (S.N.fr (.grid 0 D.R.m))⁻¹
          (funOf (listedWt G (.grid 0 D.R.m)) (F x))) D.R.m
        (c • brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m))) X Y := by
  rw [pairPts, Finsupp.sum, Finsupp.sum, LinearMap.sum_apply, LinearMap.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  refine (mul_left_comm c (τ d) _).trans (congrArg (τ d * ·) ?_)
  exact (congrArg₂ (fun a b => (c • brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m))) a b)
    (ptV_eq_chainTo (V := fun j => G.V (.top j)) (Mo := fun j => VV ℂ (wt G (.top j))) (colComp S d)
      (fun x => rhoVr (tauE D) _ (S.N.fr (.top 0))⁻¹ (Ψ x)) X D.R.m)
    (ptV_eq_chainTo (V := fun j => G.V (.grid j D.R.m)) (Mo := fun j => VV ℂ (wt G (.grid j D.R.m))) (rowComp S d)
      (fun x => rhoVr (tauE D) (wt G (.grid 0 D.R.m)) (S.N.fr (.grid 0 D.R.m))⁻¹ (funOf (listedWt G (.grid 0 D.R.m)) (F x)))
      Y D.R.m)).symm

end

theorem _root_.GlobalTheory.T.term_volume_class_sum : GlobalTheory.FunPr.Hypotheses₂ → SumOKK → Big fun ch => ∀ P : PolCol ch.G × PolRow ch.G, ∃ κ : ℂ, ∀ t a, ∀ β ∈ ch.S.supp t (ch.Phi a), ∀ M τ, IsTermVol t ch.S.toGridChoice (ch.Phi a) β M → ch.S.IsExpansion t (ch.Phi a) β τ → ∀ y, defTot t ch.S.toGridChoice M (Finsupp.single P 1) τ (colFn ch a) (formTop ch t y) = κ * ch.S.classSum (ch.Phi a) β τ (psiC (ch.Psi a)) (ch.S.formC t y) := by
  intro hP hS
  obtain ⟨C0, H⟩ := Big.and hS (GlobalTheory.FirstRowLaw.first_level_invariance hP hS)
  refine ⟨C0, fun ε CF hC => ?_⟩
  obtain ⟨x₀, H⟩ := H ε CF hC
  refine ⟨x₀, fun D large₂ e hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch hi hsc P => ?_⟩
  obtain ⟨hOK, h0⟩ := H D large₂ e hx Γ Pl0 T A Ks R F s ch hi hsc
  have hL : R.toLevCh.Is A.μ0 := s.core.lev
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  obtain ⟨Λ0, hΛ0⟩ := GlobalTheory.JetsOne.col_real ch
  obtain ⟨Λ0', hΛ0'⟩ := GlobalTheory.JetsOne.form_real ch s.core.models.cX
  obtain ⟨Λ, rfl, hΛ⟩ := GlobalTheory.JetsOne.col_chain ch.S.toGridChoice hL P Λ0
  obtain ⟨Λ', rfl, hΛ'⟩ := GlobalTheory.JetsOne.row_chain ch.S.toGridChoice hL P Λ0'
  obtain ⟨c, σ, hσ, hlast⟩ := last_ok ch.S.toGridChoice hL (Λ D.R.m) (Λ' D.R.m)
  refine ⟨c, fun t a β hβ M τ hM hτ y => ?_⟩
  have hv := (hOK t a).vec β τ hτ
  obtain ⟨v1, v2⟩ := TermVolDef.isMeasDef_of_isTermVol ch.S.toGridChoice hL t _ β M hM
  obtain ⟨i1, i2, i3, i4⟩ := GlobalTheory.T.normalisedKernelExpansionSum_levelInvariant ch.S.toGridChoice hL (GlobalTheory.FlipIntegrand.pde_ne_q_of_setting s) (hi.guard t)
    (Set.mem_univ t) hβ hτ hv (psiC (ch.Psi a)) (ch.S.formC t y)
  have hK0 : ∀ h : 0 < D.R.m, ch.S.levTop t (ch.Phi a) β 0 h = ch.G.Kplus := fun _ => rfl
  have key := GlobalTheory.JetsOne.glue (V := fun j => ch.G.V (.top j)) (V' := fun j => ch.G.V (.grid j D.R.m)) τ
    (fun d hd => hΛ t (Set.mem_univ t) d (hv d hd).1) (hΛ0 a) (GlobalTheory.JetsOne.col_left ch a)
    (fun d hd => GlobalTheory.JetsOne.col_near _ P d (hv d hd).1 (GlobalTheory.JetsOne.col_fix ch a (v1 0 hm).2.1))
    (fun d hd => hΛ' t (Set.mem_univ t) d (hv d hd).2) (hΛ0' t y) (GlobalTheory.JetsOne.form_aut s ch t y).1
    (fun d hd => GlobalTheory.JetsOne.row_near _ P d (hv d hd).2 (GlobalTheory.JetsOne.form_aut s ch t y).2) hlast
    (fun n hn => posDef_top ch.G hn.le) (fun n hn => posDef_grid hL hn)
    (fun j => M.ν (.top j)) (fun j => M.fd (.top j)) (ch.S.levTop t (ch.Phi a) β) (fun n hn => (v1 n hn).2)
    (fun j => M.ν (.grid j D.R.m)) (fun j => M.fd (.grid j D.R.m)) (ch.S.levRow t) (fun n hn => (v2 n hn).2)
    (fun X Y => c * GlobalTheory.ExpansionInvariance.pairPts ch.S.toGridChoice τ X Y (psiC (ch.Psi a) (X 0)) (ch.S.formC t y (Y 0)))
    (pair_eq ch.S.toGridChoice τ c _ _)
    (fun X Y j hj k hk => by
      rcases j with _ | j
      · have := i2 (GlobalTheory.JetsOne.psiC_right ch a) X Y k hk
        beta_reduce
        rw [Function.update_self, this]
      · exact congrArg _ (i1 X Y _ j.succ_pos hj k hk))
    (fun X Y j hj k hk => by
      rcases j with _ | j
      · have := h0 t a β hβ τ hτ y (psiC (ch.Psi a) (X 0)) X Y k hk
        beta_reduce
        rw [Function.update_self, this]
      · exact congrArg _ (i3 X Y _ j.succ_pos hj k hk))
    (fun X Y k h1 hk => congrArg _ (i4 X Y k h1 hk))
  rw [defTot, Finsupp.sum_single_index (by simp)]
  simp only [one_mul, GlobalTheory.JetsOne.defPer_eq, hσ]
  refine key.trans ?_
  rw [GridChoice.classSum, mul_finsum]
  exact finsum_congr fun c' => mul_left_comm _ _ _
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TopRowNormalisedKernelChainPreservesCoeffs
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.RowTest.ColField

open MvPolynomial

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Coeff

variable {ι : Type} [Fintype ι] {n : ℕ}

theorem coeff_bVV_mem (A : Subfield ℂ) (lam : ι → DomWeight n) (i : VVIdx lam) (m) :
    coeff m ((bVV ℂ lam i : VV ℂ lam) : Pol ℂ ι n) ∈ A := by
  obtain ⟨P, hP⟩ := bVVfun_int ℂ lam i
  rw [bVV_coe, hP, coeff_map]
  exact intCast_mem A _

theorem coeff_mem_of_repr_mem (A : Subfield ℂ) (lam : ι → DomWeight n) (v : VV ℂ lam)
    (h : ∀ i, (bVV ℂ lam).repr v i ∈ A) (m) : coeff m (v : Pol ℂ ι n) ∈ A := by
  have e := congrArg (fun x : VV ℂ lam => coeff m (x : Pol ℂ ι n)) ((bVV ℂ lam).sum_repr v)
  simp only [Submodule.coe_sum, Submodule.coe_smul, coeff_sum, coeff_smul, smul_eq_mul] at e
  rw [← e]
  exact sum_mem fun i _ => mul_mem (h i) (coeff_bVV_mem A lam i m)

theorem repr_mem_of_coeff_mem (A : Subfield ℂ) (lam : ι → DomWeight n) (v : VV ℂ lam)
    (h : ∀ m, coeff m (v : Pol ℂ ι n) ∈ A) (i : VVIdx lam) : (bVV ℂ lam).repr v i ∈ A := by
  classical
  choose P hP using fun j => bVVfun_int ℂ lam j
  let s : A →+* ℂ := A.subtype
  let b' : VVIdx lam → MvPolynomial (ι × Fin n × Fin n) A := fun j => map (Int.castRingHom A) (P j)
  have hb' : ∀ j, map s (b' j) = ((bVV ℂ lam j : VV ℂ lam) : Pol ℂ ι n) := fun j => by
    rw [bVV_coe, hP, map_map]
    congr 1
  obtain ⟨v', hv'⟩ : ∃ v' : MvPolynomial (ι × Fin n × Fin n) A, map s v' = (v : Pol ℂ ι n) := by
    obtain ⟨F', hF'⟩ := (mem_range_map_iff_coeffs_subset (f := s)).2 (fun c hc => by
      obtain ⟨m, -, rfl⟩ := mem_coeffs_iff.1 hc
      exact ⟨⟨_, h m⟩, rfl⟩)
    exact ⟨F', hF'⟩
  have hliC : LinearIndependent ℂ fun j => ((bVV ℂ lam j : VV ℂ lam) : Pol ℂ ι n) :=
    (bVV ℂ lam).linearIndependent.map' (VV ℂ lam).subtype (Submodule.ker_subtype _)
  have hli : LinearIndependent A b' := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have e := congrArg (map s) hg
    simp only [map_sum, map_zero, smul_eq_C_mul, map_mul, map_C, hb'] at e
    have e' : ∑ k, (s (g k)) • ((bVV ℂ lam k : VV ℂ lam) : Pol ℂ ι n) = 0 := by
      simpa only [smul_eq_C_mul] using e
    have := Fintype.linearIndependent_iff.1 hliC (fun k => s (g k)) e' j
    exact Subtype.ext this
  have hspan : v' ∈ Submodule.span A (Set.range b') := by
    by_contra hn
    have hopt : LinearIndependent A (fun o : Option (VVIdx lam) => Option.casesOn' o v' b') :=
      (linearIndependent_option' (x := v') (v := b')).2 ⟨hli, hn⟩
    have hC := Formalism.L2.Col.linearIndependent_map s _ hopt
    have hC' : LinearIndependent ℂ (fun o : Option (VVIdx lam) =>
        Option.casesOn' o (map s v') fun j => map s (b' j)) := by
      convert hC using 1
      funext o
      cases o <;> rfl
    obtain ⟨-, hnot⟩ := (linearIndependent_option' (x := map s v') (v := fun j => map s (b' j))).1 hC'
    apply hnot
    rw [hv']
    have hvs := congrArg (fun x : VV ℂ lam => (x : Pol ℂ ι n)) ((bVV ℂ lam).sum_repr v)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hvs
    rw [← hvs]
    exact sum_mem fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hb' j⟩)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun A).1 hspan
  have hvc : v = ∑ j, (s (c j)) • bVV ℂ lam j := by
    apply Subtype.ext
    rw [← hv', ← hc, map_sum, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Submodule.coe_smul, ← hb', smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C]
  rw [hvc, (bVV ℂ lam).repr_sum_self]
  exact (c i).2

theorem coeff_map_mem {ι' : Type} [Fintype ι'] {n' : ℕ} (A : Subfield ℂ) (lam : ι → DomWeight n)
    (mu : ι' → DomWeight n') (f : VV ℂ lam →ₗ[ℂ] VV ℂ mu)
    (hf : ∀ a b, LinearMap.toMatrix (bVV ℂ lam) (bVV ℂ mu) f a b ∈ A) (v : VV ℂ lam)
    (hv : ∀ m, coeff m (v : Pol ℂ ι n) ∈ A) (m) : coeff m ((f v : VV ℂ mu) : Pol ℂ ι' n') ∈ A := by
  classical
  refine coeff_mem_of_repr_mem A mu (f v) (fun a => ?_) m
  rw [← LinearMap.toMatrix_mulVec_repr (bVV ℂ lam) (bVV ℂ mu) f v, Matrix.mulVec, dotProduct]
  exact sum_mem fun b _ => mul_mem (hf a b) (repr_mem_of_coeff_mem A lam v hv b)

theorem coeff_rhoVr_mem {E : Type} [Field E] (emb : ι → E →+* ℂ) (lam : ι → DomWeight n) (A : Subfield ℂ)
    (hA : ∀ τ x, emb τ x ∈ A) (γE : GL (Fin n) E) (v : VV ℂ lam) (hv : ∀ m, coeff m (v : Pol ℂ ι n) ∈ A) (m) :
    coeff m ((rhoVr emb lam γE v : VV ℂ lam) : Pol ℂ ι n) ∈ A := by
  classical
  let R₀ : Subring (Pol ℂ ι n) := (MvPolynomial.map A.subtype).range
  have memR : ∀ F : Pol ℂ ι n, F ∈ R₀ ↔ ∀ m, coeff m F ∈ A := by
    intro F
    constructor
    · rintro ⟨F', rfl⟩ m
      rw [coeff_map]
      exact (coeff m F').2
    · intro h
      obtain ⟨F', hF'⟩ := (mem_range_map_iff_coeffs_subset (f := A.subtype)).2 (fun c hc => by
        obtain ⟨m, -, rfl⟩ := mem_coeffs_iff.1 hc
        exact ⟨⟨_, h m⟩, rfl⟩)
      exact ⟨F', hF'⟩
  have hblock : ∀ M : ι → Matrix (Fin n) (Fin n) ℂ, (∀ τ a b, M τ a b ∈ A) → ∀ F ∈ R₀,
      Formalism.GradedWeylDivisibility.blockAct ℂ M F ∈ R₀ := by
    intro M hM F hF
    obtain ⟨F', rfl⟩ := hF
    induction F' using MvPolynomial.induction_on with
    | C a =>
      rw [map_C, Formalism.GradedWeylDivisibility.blockAct, aeval_C]
      exact ⟨C a, by rw [map_C]; rfl⟩
    | add p q hp hq =>
      rw [map_add, map_add]
      exact add_mem hp hq
    | mul_X p w hp =>
      rw [map_mul, map_mul, map_X]
      refine mul_mem hp ?_
      rw [Formalism.GradedWeylDivisibility.blockAct, aeval_X]
      exact sum_mem fun b _ => mul_mem ⟨C ⟨_, hM _ _ _⟩, by rw [map_C]; rfl⟩ ⟨X _, map_X _ _⟩
  have hent : ∀ τ a b, ((invTrK (embGL emb γE) τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) a b ∈ A := by
    intro τ a b
    show ((((Formalism.UG.bc (emb τ) γE)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)) b a ∈ A
    rw [← map_inv]
    exact hA τ _
  have hdet : ∀ τ, ((invTrK (embGL emb γE) τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).det ∈ A := by
    intro τ
    have e := RingHom.map_det A.subtype (Matrix.of fun a b => (⟨_, hent τ a b⟩ : A))
    rw [show A.subtype.mapMatrix (Matrix.of fun a b => (⟨_, hent τ a b⟩ : A)) =
      ((invTrK (embGL emb γE) τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) from Matrix.ext fun a b => rfl] at e
    rw [← e]
    exact SetLike.coe_mem _
  have hdt : detTwK lam (invTrK (embGL emb γE)) ∈ A := by
    unfold detTwK
    refine prod_mem fun τ _ => ?_
    unfold Formalism.BasicNotions.detPow
    rw [Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply]
    exact zpow_mem (hdet τ) _
  have htr : Formalism.L2.DIV.trAct (invTrK (embGL emb γE)) (v : Pol ℂ ι n) ∈ R₀ :=
    hblock _ (fun τ a b => hent τ b a) _ ((memR _).2 hv)
  show coeff m (Formalism.L2.DIV.actP lam (invTrK (embGL emb γE)) (v : Pol ℂ ι n)) ∈ A
  rw [Formalism.L2.DIV.actP, LinearMap.smul_apply, coeff_smul, smul_eq_mul]
  exact mul_mem hdt ((memR _).1 htr m)

end Coeff

theorem chainTo_preserves {V : ℕ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)] (k : ∀ j, V j →ₗ[ℂ] V (j + 1))
    (P : ∀ j, V j → Prop) (hk : ∀ j v, P j v → P (j + 1) (k j v)) : ∀ N v, P 0 v → P N (GlobalTheory.FunObj.chainTo k N v)
  | 0, _, hv => hv
  | N + 1, v, hv => hk N _ (chainTo_preserves k P hk N v hv)

end GlobalTheory.RowTest.ColField

namespace GlobalTheory.RowTest.ColField

open MvPolynomial

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem colMap_coeff_mem : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ch.Is → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ch.S.SumOK t Φ → ∀ β ∈ ch.S.supp t Φ, ∀ τ, IsCosetExpansion ch.S.toGridChoice t Φ β (expDepth ch.S.toGridChoice t Φ β) τ → ∀ d ∈ τ.support, ∀ (c : ch.S.Classes t Φ β) (u : VV ℂ (wt ch.G (.top 0))), (∀ m, MvPolynomial.coeff m u.1 ∈ Set.range D.what₂.embLL) → ∀ m, MvPolynomial.coeff m (ch.S.colMap d (ch.S.ptTop c) u).1 ∈ Set.range D.what₂.embLL := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch large₂ F _ _ hF t Φ _ β hβ τ hτ d hd c u hu
  let K : Subfield ℂ := D.what₂.embLL.fieldRange
  have memK : ∀ z : ℂ, z ∈ K ↔ z ∈ Set.range D.what₂.embLL := fun z => Iff.rfl
  have hE : ∀ (σ : D.what₂.Tau) (x : D.host.E), tauE D σ x ∈ K := fun σ x =>
    ⟨labLL D σ x, GlobalTheory.Mem.R3.BrgRead.embLL_labLL_eq σ x⟩
  have hrat := (hF.isRatAt hβ hτ hd c).1
  have hu' : ∀ m, coeff m (u : Pol ℂ D.what₂.Tau (ch.G.V (.top 0)).rank) ∈ K := fun m => (memK _).2 (hu m)
  have h0 := coeff_rhoVr_mem (tauE D) (wt ch.G (.top 0)) K hE (ch.S.N.fr (.top 0))⁻¹ u hu'
  have hchain := chainTo_preserves (V := fun j => VV ℂ (wt ch.G (.top j)))
    (fun j => if h : j < D.R.m then ch.S.Z.kkMap 1 (d.1 ⟨j, h⟩) (ch.S.ptTop c j) (ch.S.ptTop c (j + 1)) else 0)
    (fun j v => ∀ m, coeff m (v : Pol ℂ D.what₂.Tau (ch.G.V (.top j)).rank) ∈ K) (fun j v hv => by
      by_cases h : j < D.R.m
      · simp only [dif_pos h]
        exact coeff_map_mem K _ _ _ (fun a b => (memK _).2 (hrat ⟨j, h⟩ a b)) v hv
      · simp only [dif_neg h, LinearMap.zero_apply, ZeroMemClass.coe_zero, coeff_zero]
        exact fun _ => zero_mem K) D.R.m _ h0
  intro m
  exact (memK _).1 (hchain m)

end GlobalTheory.RowTest.ColField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumFinitePairVacuumAlgebraicCombinationStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilDatum_finite_pair_vacuum_algebraic_combination : ∀ {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {v : WO S T → ℂ}
    {χS χT : (Formalism.L2.Theta.AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}, IsVacO ψ θ S T sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) v → IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → IsWeilDatumO ψ S T χS χT om →
    ∀ x ∈ GfC S, ∀ h ∈ GfC T, ∃ (κ : ℂ) (F : WO S T → ℂ), GlobalTheory.MovedAlg.IsAlgComb ψ S T v F ∧ om (x, h) v = κ • F := by
  first | exact @GlobalTheory.FinWeilAlg.om_vac_algComb | exact GlobalTheory.FinWeilAlg.om_vac_algComb | (intros; apply GlobalTheory.FinWeilAlg.om_vac_algComb <;> assumption)
end

