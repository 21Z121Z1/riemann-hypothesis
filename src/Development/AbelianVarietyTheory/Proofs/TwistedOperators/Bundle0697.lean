import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0217
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspAlongOfPairLifts
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0523
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0555
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0679
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0660
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0514
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0685
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0692
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0684
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0518
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0020
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridParameterRegularCardEqRankFormula
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubledWeilSplitPlaceVacuumEigenfunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0680
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ChainParSucc
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0674
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0037
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0681
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsVEqOne
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0499
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0393
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0682
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspFormUniformHeightApprox
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size

noncomputable section
open scoped ENNReal

theorem GlobalTheory.CuspApproxAll.cusp_approx_weighted : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → GlobalTheory.FunPr.Hypotheses₂ → ∀ (N : GlobalTheory.Grid.Node D) (φ : GA D N.V → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N φ → ∀ (A : ℕ) (ε : ℝ), 0 < ε → ∃ (n : ℕ) (F : Fin n → N.Maps) (v : Fin n → Formalism.IndefR.Links.SmT N.M), (∀ l, F l ∈ N.Cusp θ) ∧ ∀ g, ‖φ g - ∑ l, F l (v l) g‖ * GlobalTheory.Grow.quotHeight N.V g ^ A ≤ ε := by
  intro D θ hθ hP N φ hφ A ε hε
  obtain ⟨hA, hc, -⟩ := id hφ
  obtain ⟨U, hU, hlev⟩ := hA.level
  obtain ⟨d, C, hC⟩ := hP.cuspDecaySobolev D θ hθ N.V U hU 0 A
  have hφg : GlobalTheory.CuspApproxAll.Good θ N.V φ := ⟨GlobalTheory.Size.rapidDecSm_of_cuspForm hP.cuspRapidDecay hθ hA hc, hc⟩
  have hη : 0 < ε / ((C : ℝ) + 1) := div_pos hε (by positivity)
  obtain ⟨e, he, hgrow⟩ := GlobalTheory.T.exists_KFinite_iteratedCompactAverage_approx D θ hθ N φ hφg.1 (Finset.univ : Finset D.what₂.Tau).toList (Finset.nodup_toList _) d _ hη
  obtain ⟨n, F, v, hF, hFlev, hsum⟩ := GlobalTheory.T.cusp_form_K_finite_approx D θ hθ hP N φ hφ U hU hlev e he
    (Finset.univ : Finset D.what₂.Tau).toList (fun τ => Finset.mem_toList.2 (Finset.mem_univ τ))
  rw [hsum] at hgrow
  refine ⟨n, F, v, hF, fun g => ?_⟩
  set ψ : GA D N.V → ℂ := φ - ∑ j, F j (v j) with hψ
  have hsg : GlobalTheory.CuspApproxAll.Good θ N.V (∑ j, F j (v j)) :=
    Finset.sum_induction _ (GlobalTheory.CuspApproxAll.Good θ N.V) (fun _ _ => GlobalTheory.CuspApproxAll.good_add)
      (GlobalTheory.CuspApproxAll.good_zero θ N.V) fun j _ => GlobalTheory.CuspApproxAll.good_value hP.cuspRapidDecay hθ N (hF j) (v j)
  have hg : GlobalTheory.CuspApproxAll.Good θ N.V ψ := by
    have := GlobalTheory.CuspApproxAll.good_add hφg (GlobalTheory.CuspApproxAll.good_smul (-1) hsg)
    rwa [neg_one_smul, ← sub_eq_add_neg] at this
  have hψlev : ∀ k ∈ U, k ∈ GfC N.V → ∀ x, ψ (x * k) = ψ x := fun k hk hk' x => by
    simp only [hψ, Pi.sub_apply, Finset.sum_apply, hlev k hk hk' x, hFlev _ k hk hk' x]
  have h1 := hC ψ hg.1.toIsAutFun hψlev hg.1.smooth (GlobalTheory.CuspApproxAll.growthSob_zero_ne_top hg.1) hg.2
  have h2 : decaySize N.V A ψ ≤ ENNReal.ofReal ε := by
    have h4 : (C : ℝ≥0∞) * growthSob θ N.V d 0 ψ ≤ C * ENNReal.ofReal (ε / ((C : ℝ) + 1)) := by gcongr
    refine h1.trans (h4.trans ?_)
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith [NNReal.coe_nonneg C]
  have h3 : ENNReal.ofReal (‖ψ g‖ * quotHeight N.V g ^ A) ≤ ENNReal.ofReal ε := (le_iSup (fun x => ENNReal.ofReal (‖ψ x‖ * quotHeight N.V x ^ A)) g).trans h2
  rw [ENNReal.ofReal_le_ofReal_iff hε.le] at h3
  simpa [hψ, Finset.sum_apply] using h3
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalAlongDownGridArrows
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.FlipRun

theorem ga_eq_of_match {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : Consts}
    {G' : GridData R.toLevCh sc} {W : G'.Weil} {G : GlobalTheory.Grid.GridPre R} (hM : GlobalTheory.GridJoin.Match G W) {i j : ℕ}
    (hi : i ≤ D.R.m) (hj : j ≤ D.R.m) : GA D (G.V i j).V = GA D (G'.V (.grid i j)) := by
  obtain ⟨L, h1, h2, e⟩ := (hM.1.vert i j hi hj).sp
  rw [e]; rfl

theorem cuspStep_down_big : (∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidalSmoothAt D) → GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch =>
  ∀ (t : T) (M : Vol ch.G), M.Is t → ∀ a : Arrow T, IsGridArrow D.R.m t a → (∃ i j, a = Arrow.down t i j) →
    ∀ e, IsIdemSum e (locPl ch.G t) → ∀ φ f, IsLocVec ch.W a.pair e (vacOf ch.rm a) φ f →
    ∀ (Q : PolF D (ch.G.pT a.pair).rank (ch.G.pS a.pair).rank) (F : Fn ch.G a.src), IsCuspListed ch.W.θ a.src F →
      LiftConv ch.W M a (ch.W.fock a.pair f Q) F ∧ IsCuspListed ch.W.θ a.tgt (liftA ch.W M a (ch.W.fock a.pair f Q) F) := by
  intro hS hP
  refine ⟨0, fun ε CF _ => ⟨0, ?_⟩⟩
  intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hset ch hch hsc t M hMt a ha hdown e he φ f hf Q Fn hFn
  obtain ⟨i, j, rfl⟩ := hdown
  have hgap : ch.sc.cGap = 1 := by rw [hsc]
  obtain ⟨hi, hj⟩ : i ≤ D.R.m ∧ j < D.R.m := by
    rcases ha with ⟨_, _, _, _, h⟩ | ⟨i', j', h1, h2, h⟩
    · cases h
    · cases h; exact ⟨h1, h2⟩
  obtain ⟨G, hG, hMa⟩ := GlobalTheory.GridJoin.exists_gridPre hP.discreteSeriesUpqExists hP.discreteSeriesCover
    hP.harishChandraModules hset.host hset.size hset.core hgap ch.W hch.weil
  have hRB : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R :=
    ⟨hset.core.lev, hset.core.models.inf, hset.core.models.νY, hset.core.models.νY', hset.core.models.νX⟩
  have hCS := hS D (GlobalTheory.RowSizes.sizes_of_sizeRows large₂ hset.size) Γ Pl0 T A Ks R G hRB hG
  have eA := ga_eq_of_match hMa hi (Nat.succ_le_of_lt hj)
  have eB := ga_eq_of_match hMa hi hj.le
  have hΨ := GlobalTheory.T.isThetaFunction_fock_vector_downward_arrow ch.rm t i j hi hj he hf Q
  obtain ⟨Φ, hΦ, hK⟩ := GlobalTheory.T.thetaKernel_downward_testGrid_eq_sender_grid ch.W hch.weil G hG hMa t i j hi hj eA eB _ hΨ
  have hF' := (GlobalTheory.T.isCuspTyped_testGrid_iff_sender_grid_conj hset hgap ch.W hch.weil G hG hMa i (j + 1) hi (Nat.succ_le_of_lt hj) eA Fn).1 hFn
  obtain ⟨hint, hcusp⟩ := hCS.th t i j hi hj Φ hΦ _ hF'
  have hθ : ch.W.θ = R.θ := hch.weil.θ
  have hinv : ∀ h, ∀ γ ∈ GQ (ch.G.V (.grid i (j + 1))), ∀ g,
      (fun g => ch.W.kerA (.down t i j) (ch.W.fock (.mu t i j) f Q) g h * Fn g) (γ * g) =
      (fun g => ch.W.kerA (.down t i j) (ch.W.fock (.mu t i j) f Q) g h * Fn g) g := fun h γ hγ g => by
    simp only [GlobalTheory.T.thetaKernel_downward_arrow_left_invariant ch.W t i j hi hj _ hΨ h γ hγ g, hFn.1.toIsAutFun.left γ hγ g]
  have key := fun h => GlobalTheory.T.testGrid_measure_domain_downward_eq_sender hset hgap ch.W hch.weil G hG hMa M t hMt i j hi hj eA
    (fun g => ch.W.kerA (.down t i j) (ch.W.fock (.mu t i j) f Q) g h * Fn g) (hinv h)
  have hcb : ∀ h : GA D (ch.G.V (.grid i j)), cast eB (cast eB.symm h) = h := fun h => cast_cast _ _ h
  refine ⟨fun h => ?_, ?_⟩
  · rw [← hcb h]
    refine (key _).1.1 ?_
    simpa only [hK] using hint (cast eB.symm h)
  · refine (GlobalTheory.T.isCuspTyped_testGrid_iff_sender_grid_conj hset hgap ch.W hch.weil G hG hMa i j hi hj.le eB _).2 ?_
    convert hcusp using 2 with h
    rw [liftA_apply, ← (key _).2]
    simp only [hK]

end GlobalTheory.FlipRun
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalAlongRightGridArrows
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.RightArrowCusp

theorem vert_par : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}, GlobalTheory.Hk3.Core R F → ∀ G : GlobalTheory.Grid.GridPre R, G.Is → ∀ i j : ℕ, i ≤ D.R.m → j ≤ D.R.m → (G.V i j).S = GlobalTheory.Grid.parV D i j := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R F _ G hG i j hi hj
  cases i with
  | zero =>
    rw [GlobalTheory.Grid.parV_zero D hj]
    rcases j with _ | j
    · rfl
    · show (if j + 1 < D.R.m then GlobalTheory.Grid.nodeY R (j + 1) else GlobalTheory.Grid.nodeX R).S = _
      split_ifs with h
      · simp [Nat.min_eq_left hj]
      · have : j + 1 = D.R.m := by omega
        rw [this]
  | succ i => exact (hG.spaces.vert i j hi hj).par

theorem meas_haar_fund : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}, GlobalTheory.Hk3.Core R F → ∀ G : GlobalTheory.Grid.GridPre R, G.Is → ∀ (t : T) (i j : ℕ), i ≤ D.R.m → j ≤ D.R.m → (G.meas t i j).ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ (G.V i j).V) (G.meas t i j).fd (G.meas t i j).ν := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R F hC G hG t i j hi hj
  have aux : ∀ {N : GlobalTheory.Grid.Node D} (m : N.MeasDat) (df : Prop) K, m.Is df K →
      m.ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ N.V) m.fd m.ν := by
    intro N m df K h
    by_cases hd : df
    · exact ⟨(h.1 hd).1.1, (h.1 hd).2⟩
    · exact ⟨(h.2 hd).1.1, (h.2 hd).2⟩
  have cst : ∀ {S S' : GlobalTheory.Grid.Node D} (e : S = S') (m : S.MeasDat),
      m.ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ S.V) m.fd m.ν →
      (GlobalTheory.Grid.Node.MeasDat.cast e m).ν.IsHaarMeasure ∧
        IsFundamentalDomain (GQ S'.V) (GlobalTheory.Grid.Node.MeasDat.cast e m).fd (GlobalTheory.Grid.Node.MeasDat.cast e m).ν := by
    intro S S' e m h
    subst e
    exact h
  rcases i with _ | i
  · rcases j with _ | j
    · exact aux _ _ _ (hG.meas.col 0 (Nat.zero_le _))
    · show (GlobalTheory.Grid.meas0 R t j).ν.IsHaarMeasure ∧
        IsFundamentalDomain (GQ (GlobalTheory.Grid.row0 R (j + 1)).V) (GlobalTheory.Grid.meas0 R t j).fd (GlobalTheory.Grid.meas0 R t j).ν
      unfold GlobalTheory.Grid.meas0
      split_ifs with h
      · apply cst
        by_cases h2 : j + 1 + 1 < D.R.m
        · have := hC.models.νY t (j + 1) h2
          exact ⟨this.1.1, this.2⟩
        · have := hC.models.νY' t
          have e : D.R.m - 1 = j + 1 := by omega
          rw [e] at this
          exact ⟨this.1.1, this.2⟩
      · apply cst
        have := hC.models.νX t
        exact ⟨this.1.1, this.2⟩
  · rcases j with _ | j
    · exact aux _ _ _ (hG.meas.col (i + 1) hi)
    · exact aux _ _ _ (hG.meas.vert i j hi hj)

theorem thetaKO_eq_kerA : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : Consts} {G' : GridData R.toLevCh sc} (W : G'.Weil) (i j : ℕ) (Ls : Submodule (𝓞 D.host.E) (G'.V (.grid i j)).V) (hs1 : Submodule.IsLattice D.host.E Ls) (hs2 : Formalism.HermitianLatticesTheory.IsUnimodular (G'.V (.grid i j)).hT Ls) (Lt : Submodule (𝓞 D.host.E) (G'.V (.grid (i + 1) j)).V) (ht1 : Submodule.IsLattice D.host.E Lt) (ht2 : Formalism.HermitianLatticesTheory.IsUnimodular (G'.V (.grid (i + 1) j)).hT Lt) (ω : GlobalTheory.Grid.WRep (GlobalTheory.VolRatioCompare.reLat (G'.V (.grid (i + 1) j)) Lt ht1 ht2) (GlobalTheory.VolRatioCompare.reLat (G'.V (.grid i j)) Ls hs1 hs2)), HEq (ω.toSgn true) (W.om (.chi i j)) → ∀ (Φ : Sch G' (.right i j)) (g : GA D (G'.V (.grid i j))) (h : GA D (G'.V (.grid (i + 1) j))), thetaKO ω h g Φ = W.kerA (.right i j) Φ g h := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc G' W i j Ls hs1 hs2 Lt ht1 ht2 ω hω Φ g h
  have e : ω.toSgn true = W.om (.chi i j) := eq_of_heq hω
  show (ω (h, g)) Φ 0 = (W.om (.chi i j) (negGA _ h, g)) Φ 0
  rw [← e]
  rfl

theorem isThetaFunO_neg_reLat : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S U : HSp D) (L : Submodule (𝓞 D.host.E) S.V) (h1 : Submodule.IsLattice D.host.E L) (h2 : Formalism.HermitianLatticesTheory.IsUnimodular S.hT L) (L' : Submodule (𝓞 D.host.E) U.V) (h1' : Submodule.IsLattice D.host.E L') (h2' : Formalism.HermitianLatticesTheory.IsUnimodular U.hT L') (Φ : WO (negSp S) U → ℂ), IsThetaFunO ψ (negSp S) U Φ → IsThetaFunO ψ (GlobalTheory.Grid.neg (GlobalTheory.VolRatioCompare.reLat S L h1 h2)) (GlobalTheory.VolRatioCompare.reLat U L' h1' h2') Φ := by
  intro D ψ S U L h1 h2 L' h1' h2' Φ h
  exact ⟨h.1, h.2, h.3, h.4⟩

theorem isCuspListed_smul : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (θ : InfFam D) (X : Node) (c : ℂ) (F : Fn G X), IsCuspListed θ X F → IsCuspListed θ X (c • F) := by
  intro D T L sc G θ X c F ⟨h1, h2, h3⟩
  refine ⟨Formalism.IndefR.Mult.isAutFunSm_smul _ _ h1 c, Formalism.IndefR.Mult.isCuspFun_smul _ h2 c, ?_⟩
  rcases X with ⟨i, j⟩ | i | j
  · intro τ
    have e : (fun g => star ((c • F) g)) = star c • fun g => star (F g) := by
      funext g; simp [Pi.smul_apply, smul_eq_mul, star_mul', mul_comm]
    show IsTypeAt _ _ _ _ fun g => star ((c • F) g)
    rw [e]
    exact GlobalTheory.Mem.Th.isTypeAt_smul _ (h3 τ)
  · intro τ; exact GlobalTheory.Mem.Th.isTypeAt_smul c (h3 τ)
  · intro τ; exact GlobalTheory.Mem.Th.isTypeAt_smul c (h3 τ)

theorem kerA_mul_left_invariant : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : Consts} {G' : GridData R.toLevCh sc} (W : G'.Weil) (i j : ℕ), i < D.R.m → j ≤ D.R.m → ∀ Φ : Sch G' (.right i j), IsThetaFunO W.ψ (G'.pS (.chi i j)) (G'.pT (.chi i j)) Φ → ∀ F : Fn G' (.grid i j), IsCuspListed W.θ (.grid i j) F → ∀ h, ∀ γ ∈ GQ (G'.V (.grid i j)), ∀ g, W.kerA (.right i j) Φ (γ * g) h * F (γ * g) = W.kerA (.right i j) Φ g h * F g := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc G' W i j hi hj Φ hΦ F hF h γ hγ g
  have hω := W.om_is (.chi i j) (by first | exact ⟨hi, hj⟩ | exact ⟨hj, hi⟩ | simpa using ⟨hi, hj⟩)
  show thetaKO (W.om (.chi i j)) (negGA _ h) (γ * g) Φ * F (γ * g) = thetaKO (W.om (.chi i j)) (negGA _ h) g Φ * F g
  rw [GlobalTheory.UpArrowConv.thetaKO_left_snd hω hΦ _ γ hγ g, hF.1.left γ hγ g]

theorem isAutFunSm_reLat_iff : ∀ {D : D7} (θ : InfFam D) (V : HSp D) (L : Submodule (𝓞 D.host.E) V.V) (h1 : Submodule.IsLattice D.host.E L) (h2 : Formalism.HermitianLatticesTheory.IsUnimodular V.hT L) (φ : GA D V → ℂ), IsAutFunSm θ (GlobalTheory.VolRatioCompare.reLat V L h1 h2) φ ↔ IsAutFunSm θ V φ := by
  intro D θ V L h1 h2 φ
  exact ⟨fun h => ⟨⟨h.left, h.level, h.cont⟩, h.smooth, h.zfin, h.growth⟩,
    fun h => ⟨⟨h.left, h.level, h.cont⟩, h.smooth, h.zfin, h.growth⟩⟩

theorem isCuspOfType_iff_isCuspListed : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : Consts}, sc.cGap = 1 → ∀ {G' : GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ (i j : ℕ), i ≤ D.R.m → j ≤ D.R.m → ∀ (L : Submodule (𝓞 D.host.E) (G'.V (.grid i j)).V) (h1 : Submodule.IsLattice D.host.E L) (h2 : Formalism.HermitianLatticesTheory.IsUnimodular (G'.V (.grid i j)).hT L) (Mo : Formalism.IndefR.Mult.DSModel (GlobalTheory.VolRatioCompare.reLat (G'.V (.grid i j)) L h1 h2) (GlobalTheory.Grid.parV D i j)) (Λ : Submodule (𝓞 D.host.E) (Fin (GlobalTheory.VolRatioCompare.reLat (G'.V (.grid i j)) L h1 h2).rank → D.host.E)) (β : GL (Fin (GlobalTheory.VolRatioCompare.reLat (G'.V (.grid i j)) L h1 h2).rank) (Lev.EAf D)) (φ : Fn G' (.grid i j)), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ ⟨GlobalTheory.VolRatioCompare.reLat (G'.V (.grid i j)) L h1 h2, GlobalTheory.Grid.parV D i j, Mo, Λ, β⟩ φ ↔ IsCuspListed W.θ (.grid i j) φ := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc hsc G' W hW i j hi hj L h1 h2 Mo Λ β φ
  rw [hW.θ]
  refine and_congr (isAutFunSm_reLat_iff R.θ _ L h1 h2 φ) (and_congr Iff.rfl ?_)
  show (∀ τ, IsTypeAt R.θ (GlobalTheory.VolRatioCompare.reLat (G'.V (.grid i j)) L h1 h2) τ (GlobalTheory.Grid.parV D i j τ) φ) ↔
    ∀ τ, IsTypeAt R.θ (G'.V (.grid i j)) τ (Node.par D sc.cGap (.grid i j) τ) fun g => star (φ g)
  refine forall_congr' fun τ => ?_
  rw [hsc]
  have hp : GlobalTheory.Grid.parV D i j τ = Formalism.IndefR.Mult.dualPar (GlobalTheory.ChiGrid.parV D 1 i j τ) := by
    unfold GlobalTheory.Grid.parV GlobalTheory.ChiGrid.parV
    rw [GlobalTheory.GridParDCount.grid_eq_num D τ]
  rw [hp]
  exact GlobalTheory.T.isTypeAt_dualPar_iff_star_isTypeAt R.θ (G'.V (.grid i j)) τ _ φ

open GlobalTheory.GridJoin in

theorem lift_right_of_smooth {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : Consts} (hsc : sc.cGap = 1) {G' : GridData R.toLevCh sc} (W : G'.Weil)
    (hW : W.Over R) (ρ : RealMatch W) (hρ : RealMatch.Over R ρ) (M : Vol G') (t : T) (hM : M.Is t) (i j : ℕ) (hi : i < D.R.m)
    (hj : j ≤ D.R.m) (Ns Nt : GlobalTheory.Grid.Node D) (hs : SameSp (G'.V (.grid i j)) Ns.V) (ht : SameSp (G'.V (.grid (i + 1) j)) Nt.V)
    (hSs : Ns.S = GlobalTheory.Grid.parV D i j) (hSt : Nt.S = GlobalTheory.Grid.parV D (i + 1) j) (m : Ns.MeasDat) (hm1 : m.ν.IsHaarMeasure)
    (hm2 : IsFundamentalDomain (GQ Ns.V) m.fd m.ν) (ω : GlobalTheory.Grid.WRep Nt.V Ns.V) (hω : HEq (ω.toSgn true) (W.om (.chi i j)))
    (H : ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg Nt.V) Ns.V Φ →
      GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsSmooth R.θ (A := Ns) (B := Nt) m fun h g => thetaKO ω h g Φ) :
    ∀ e, IsIdemSum e (locPl G' t) → ∀ φ f, IsLocVec W (.chi i j) e (vacOf ρ (.right i j)) φ f →
      ∀ (Q : PolF D (G'.pT (.chi i j)).rank (G'.pS (.chi i j)).rank) (F : Fn G' (.grid i j)), IsCuspListed W.θ (.grid i j) F →
        LiftConv W M (.right i j) (W.fock (.chi i j) f Q) F ∧
          IsCuspListed W.θ (.grid (i + 1) j) (liftA W M (.right i j) (W.fock (.chi i j) f Q) F) := by
  obtain ⟨Vs, Ss, Ms, Λs, βs⟩ := Ns
  obtain ⟨Vt, St, Mt, Λt, βt⟩ := Nt
  obtain ⟨Ls, hs1, hs2, rfl⟩ := hs
  obtain ⟨Lt, ht1, ht2, rfl⟩ := ht
  dsimp only at hSs hSt
  subst hSs hSt
  intro e he φ f hf Q F hF
  have hΦ0 := GlobalTheory.T.isThetaFunction_fock_vector_rightward_arrow hW ρ hρ t i j hi hj e he φ f hf Q
  have hΦ : IsThetaFunO R.ψ (GlobalTheory.Grid.neg (GlobalTheory.VolRatioCompare.reLat (G'.V (.grid (i + 1) j)) Lt ht1 ht2))
      (GlobalTheory.VolRatioCompare.reLat (G'.V (.grid i j)) Ls hs1 hs2) (W.fock (.chi i j) f Q) :=
    hW.ψ ▸ isThetaFunO_neg_reLat W.ψ _ _ Lt ht1 ht2 Ls hs1 hs2 _ hΦ0
  have hK := thetaKO_eq_kerA W i j Ls hs1 hs2 Lt ht1 ht2 ω hω (W.fock (.chi i j) f Q)
  have hFs := (isCuspOfType_iff_isCuspListed hsc W hW i j hi.le hj Ls hs1 hs2 Ms Λs βs F).2 hF
  obtain ⟨hI, hT⟩ := H _ hΦ F hFs
  have hMX := (hM.vtx (.grid i j) ⟨hi.le, hj⟩).haar_fund
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_const_setIntegral_haar_fundamentalDomains_unitary (M.ν (.grid i j)) m.ν (M.fd (.grid i j)) m.fd hMX.1 hm1 hMX.2 hm2
  have key := fun h => hc (fun g => W.kerA (.right i j) (W.fock (.chi i j) f Q) g h * F g) (kerA_mul_left_invariant W i j hi hj _ hΦ0 F hF h)
  have e2 : ∀ h, (fun g => thetaKO ω h g (W.fock (.chi i j) f Q) * F g) =
      fun g => W.kerA (.right i j) (W.fock (.chi i j) f Q) g h * F g := fun h => funext fun g => by rw [hK g h]
  refine ⟨fun h => (key h).1.2 (e2 h ▸ hI h), ?_⟩
  have e : liftA W M (.right i j) (W.fock (.chi i j) f Q) F =
      c • fun h => ∫ g in m.fd, thetaKO ω h g (W.fock (.chi i j) f Q) * F g ∂m.ν := by
    funext h
    rw [liftA_apply, (key h).2]
    exact congrArg (c * ·) (congrArg (fun φ : GA D (G'.V (.grid i j)) → ℂ => ∫ g in m.fd, φ g ∂m.ν) (e2 h).symm)
  rw [e]
  exact isCuspListed_smul _ _ c _ ((isCuspOfType_iff_isCuspListed hsc W hW (i + 1) j hi hj Lt ht1 ht2 Mt Λt βt _).1 hT)

theorem cuspStep_right : (∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidalSmoothAt D) → GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch =>
  ∀ (t : T) (M : Vol ch.G), M.Is t → ∀ a : Arrow T, IsGridArrow D.R.m t a → (∃ i j, a = Arrow.right i j) →
    ∀ e, IsIdemSum e (locPl ch.G t) → ∀ φ f, IsLocVec ch.W a.pair e (vacOf ch.rm a) φ f →
    ∀ (Q : PolF D (ch.G.pT a.pair).rank (ch.G.pS a.pair).rank) (F : Fn ch.G a.src), IsCuspListed ch.W.θ a.src F →
      LiftConv ch.W M a (ch.W.fock a.pair f Q) F ∧ IsCuspListed ch.W.θ a.tgt (liftA ch.W M a (ch.W.fock a.pair f Q) F) := by
  intro hLS hP
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hSet ch hch hsc => ?_⟩⟩
  intro t M hM a ha hr e he φ f hf Q F' hF
  obtain ⟨i, j, rfl⟩ := hr
  obtain ⟨i', j', hi, hj, h'⟩ | ⟨_, _, _, _, _, h'⟩ := ha
  · cases h'
    have hcg : ch.sc.cGap = 1 := by rw [hsc]
    obtain ⟨G, hG, hMa⟩ := GlobalTheory.GridJoin.exists_gridPre hP.discreteSeriesUpqExists hP.discreteSeriesCover
      hP.harishChandraModules hSet.host hSet.size hSet.core hcg ch.W hch.weil
    have hRB : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R :=
      ⟨hSet.core.lev, hSet.core.models.inf, hSet.core.models.νY, hSet.core.models.νY', hSet.core.models.νX⟩
    have hSm := (hLS D (GlobalTheory.RowSizes.sizes_of_sizeRows large₂ hSet.size) Γ Pl0 T A Ks R G hRB hG).X t i j hi hj
    have hgm := meas_haar_fund hSet.core G hG t i j hi.le hj
    exact lift_right_of_smooth hcg ch.W hch.weil ch.rm hch.vac M t hM i j hi hj (G.V i j) (G.V (i + 1) j)
      (hMa.1.vert i j hi.le hj).sp (hMa.1.vert (i + 1) j hi hj).sp (vert_par hSet.core G hG i j hi.le hj)
      (vert_par hSet.core G hG (i + 1) j hi hj) (G.meas t i j) hgm.1 hgm.2 (G.X i j).ω (hMa.2.omX i j hi hj) hSm
      e he φ f hf Q F' hF

end GlobalTheory.RightArrowCusp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubledWeilSplitPlaceVacuumEigenfunctionStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledWeil_split_place_vacuum_eigenfunction : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), (∀ w : HeightOneSpectrum (𝓞 E), ¬ Formalism.UG.IsInertAt F E v w) → v ∉ X.T → PsiUnr B.ψ v →
    ∀ (dd : Darboux (symp (cA σ) (-1 : AE F E) (incM F G.V.J) (dbl (incM F G.W.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a'))))
      (omd : GlobalTheory.DblVac.UD σ G.W →* Module.End ℂ (((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → AF F) → ℂ)),
    IsDblCoord (cA σ) (-1 : AE F E) (incM F G.V.J) (incM F G.W.J) G.M.co dd →
    IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1 : AE F E) (incM F G.V.J) (dbl (incM F G.W.J)) dd X.β (diagCols (Fin (a + a'))) omd →
    ∀ r : (Fin a × Fin (a + a') → AF F) → ℂ, Rest (evFin F v) (G.M.vac v) r →
    ∀ g ∈ GlobalTheory.DblVac.KD σ G.W v, ∃ μ : ℂ,
      omd g (boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x))) =
        μ • boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x)) := by
  first | exact @GlobalTheory.DblVacAny.split_eigen | exact GlobalTheory.DblVacAny.split_eigen | (intros; apply GlobalTheory.DblVacAny.split_eigen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaStepRealZetaNonvanishingStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evenThetaStep_realZeta_nonvanishing : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ D : D7, RealZeta D := by
  first | exact @GlobalTheory.EvenOntoRealZeta.realZeta | exact GlobalTheory.EvenOntoRealZeta.realZeta | (intros; apply GlobalTheory.EvenOntoRealZeta.realZeta <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCombinationOperatorColumnProductStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_combinationOperator_columnProduct : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ c : Combs ch.G, ∃ Tc : (ColPt ch.G → ℂ) →ₗ[ℂ] (ColPt ch.G → ℂ), ∀ C : BiFam ch.G, (fun u => evT (combC ch.W c C) 1 u 0) = Tc (fun u => evT C 1 u 0) := by
  first | exact @GlobalTheory.LocAsm.exists_comb_op | exact GlobalTheory.LocAsm.exists_comb_op | (intros; apply GlobalTheory.LocAsm.exists_comb_op <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCompletionPlaceDataStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_completionPlaceData : ∀ (D : D7) (w : Pl D.host.E) (e : AE D), IsIdemSum e {w} → ∃ p : Place D (Kw w), IsPlc w p ∧ p.e = e := by
  first | exact @GlobalTheory.PlcAtW.exists_plc | exact GlobalTheory.PlcAtW.exists_plc | (intros; apply GlobalTheory.PlcAtW.exists_plc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLocalModelMovedFramesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localModel_movedFrames : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT ω → ∀ (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (Z Z' : Type) [Fintype Z] [DecidableEq Z] [Fintype Z'] [DecidableEq Z'] (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) Tm, p.IsModel ψ FS FT Tm → ∀ (a : GA D S) (b : GA D T) (εS : GL Y' k) (εT : GL Y k) (σS : Z' ≃ Y') (σT : Z ≃ Y), ∃ Tm', p.IsModel ψ (mvFr p a FS εS σS) (mvFr p b FT εT σT) Tm' ∧ ∀ (Φ : SB (Matrix Y Y' k)) (Φ' : SB (Matrix Z Z' k)), (∀ x, Φ.1 x = Φ'.1 (((εT⁻¹).val * x * εS.val).submatrix σT σS)) → Tm' Φ' = ω (a, b) (Tm Φ) := by
  first | exact @GlobalTheory.FlatPlace.exists_isModel_mvFr | exact GlobalTheory.FlatPlace.exists_isModel_mvFr | (intros; apply GlobalTheory.FlatPlace.exists_isModel_mvFr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLocalModelOfSplitPlaceThetaFunStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localModel_of_splitPlaceThetaFun : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : Frame k S.rank Y') (FT : Frame k T.rank Y), (∀ x, p.up FS FT x ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True) ↔ ∀ a b, x a b ∈ Valuation.integer (ValuativeRel.valuation k)) → ∀ f₀ φ f : WO S T → ℂ, IsThetaFunO ψ S T f₀ → IsSBHalf p.e (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) φ → IsThetaAt ψ (symplO S T) (heisO ψ S T) p.e (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) 1 f₀ φ f → ∃ Tm, p.IsModel ψ FS FT Tm ∧ (∀ O, IsOne O → Tm O = f₀) ∧ ∃ Φ : SB (Matrix Y Y' k), (∀ x, Φ.1 x = φ (p.up FS FT x)) ∧ Tm Φ = f := by
  first | exact @GlobalTheory.LocMod.Witness.exists_isModel_of_isThetaAt | exact GlobalTheory.LocMod.Witness.exists_isModel_of_isThetaAt | (intros; apply GlobalTheory.LocMod.Witness.exists_isModel_of_isThetaAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRowPlacementFiniteElementMatchesLevels
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem rowPlacement_iota_eq {D : D7} {I : Formalism.MainNotions.S.AutInst} (h : I = Formalism.IndefR.RationalEmbedding.inst D)
    (ι : GA D (Yc D 0) ≃* I.GA) (hι : HEq ι (Formalism.IndefR.RationalEmbedding.iota D).toMulEquiv) :
    ι = ((Formalism.IndefR.RationalEmbedding.iota D).trans (Formalism.L2.SG.RowsJoinPinned.castGA h.symm)).toMulEquiv := by
  subst h
  have := eq_of_heq hι
  subst this
  rfl

theorem rowPlacement_exists : GlobalTheory.Published.DiscreteSeriesClassification → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Gd : GoodOp X) (h : X.B.I = Formalism.IndefR.RationalEmbedding.inst D) (ι : GA D (Yc D 0) ≃* X.B.I.GA) (tS : GA D (Yc D 0)) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → IdempotentRealFixed D → HEq ι (Formalism.IndefR.RationalEmbedding.iota D).toMulEquiv → (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∃ (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1), (∀ kv, ((plg kv : R.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) ∧ (∀ g, D.what₂.embLL ((idemOf A.X).coeff g) = D.ntypes.e0.coeff ((R.eG.trans cG) g)) ∧ (∀ kv, R.C.P.Div kv.1 (plg kv).1) ∧ ∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) ((R.eG.trans cG) g kv)) → tS ∈ GfC (Yc D 0) → ((∃ t ∈ GfC (Yc D 0), ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (ι ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 (ι k).2)) ∧ RowLevelMatchAt R F X h t) → ConjLevel (tS)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (ι ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 (ι k).2)) ∧ RowLevelMatchAt R F X h tS) → (∃ t ∈ GfC (Yc D 0), ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (ι ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 (ι k).2)) ∧ RowLevelMatchAt R F X h t) ∧ ∃ c' : ℝ, EvalTieT (R.MY 0) R.ν0 R.fd0 (R.EEat (R.levR F true)) X Gd ι tS c' := by
  intro hDS D G _ _ Pl0 T A Ks _ _ _ R F X Gd h ι tS cG hlev hgrp hmod hhost hE0 hι hιE hpin htS hmove
  have hιeq : ι = (iotaX X h).toMulEquiv := rowPlacement_iota_eq h ι hι
  subst hιeq
  have hfirst : ∃ t ∈ GfC (Yc D 0), ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true)))
      (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true)))
      ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2})
      (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) ∧ RowLevelMatchAt R F X h t := by
    obtain ⟨t, ht, hconj, hframe⟩ := GlobalTheory.T.exists_finite_element_conj_rowLevel_character R F X h hlev hgrp hmod
    exact ⟨t, ht, hconj, GlobalTheory.T.rowLevelMatchAt_of_levelConjugation R F X h hlev hgrp hmod cG t hιE hpin hE0 ht hconj hframe⟩
  obtain ⟨hconjS, hmatchS⟩ := hmove hfirst
  exact ⟨hfirst, GlobalTheory.T.goodRows_compare_by_levelMatching_evaluation hDS R F X h hlev hgrp hmod hhost hιE Gd tS htS hconjS hmatchS⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatDictionaryScalarLargeDepthStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatDictionaryScalar_largeDepth : Big fun ch => ScalP ch := by
  first | exact @GlobalTheory.FlatScal.scal | exact GlobalTheory.FlatScal.scal | (intros; apply GlobalTheory.FlatScal.scal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatMapHeisenbergAndHomTransformationStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatMap_heisenberg_and_hom_transformation : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (s : Step ψ V V₀ W W₀ ρ σ) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (y : Mx D V₀.rank σ), LinearIndependent D.host.E x₀.transpose → ∀ f, IsThetaFunO ψ V W f → (∀ N : Mx D ρ ρ, (∀ i j, j ≤ i → N i j = 0) → flatS dV dW s (rat x₀) y (heisO ψ V W (dV.extX W ((rat x₀ : Mx D W.rank ρ) ⬝ N)) f) = psiE ψ (upSum N) • flatS dV dW s (rat x₀) y f) ∧ ∀ ξ : Mx D σ V₀.rank, flatS dV dW s (rat x₀) y (heisO ψ V W (dV.ext0 W (dW.incX V₀ ξ)) f) = ψ (symplO V₀ W (dW.incAdj V₀ y) (dW.incX V₀ ξ)) • flatS dV dW s (rat x₀) y f := by
  first | exact @GlobalTheory.AscFlatLaws.flatS_laws | exact GlobalTheory.AscFlatLaws.flatS_laws | (intros; apply GlobalTheory.AscFlatLaws.flatS_laws <;> assumption)
end

