import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0097
import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0054
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0028
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0339
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0341
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0956
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MulAntiOfUnitary
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDimensionalModel
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsBesPosOfBesselTied
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsPlacesSingleton
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0781
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0345
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0305
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0027
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.DiagSmall
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ToGlob0
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0028
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0024
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0010
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CollSBound
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0083
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0048
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0344
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompIncAAlgebraMap
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod
open NumberField IsDedekindDomain
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocMod.SplitCompl

open GlobalTheory.FinPl GlobalTheory.FinPl.SplitPoint GlobalTheory.IdemModTwo GlobalTheory.SplitIdem GlobalTheory.SplitChart GlobalTheory.SplitHecke

variable {D : D7}

theorem incA_algebraMap (t : D.host.F) :
    incA D (algebraMap D.host.F D.host.E t) = algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) t) := by
  rw [← IsScalarTower.algebraMap_apply]
  exact (Algebra.TensorProduct.includeRight (R := D.host.F) (A := AF D.host.F) (B := D.host.E)).commutes t

theorem comp_incA_algebraMap {v : Pl D} {e : AE D} (he : SplitAt D v e) (t : D.host.F) :
    comp he (incA D (algebraMap D.host.F D.host.E t)) = algebraMap D.host.F (Fv D.host.F v) t := by
  rw [incA_algebraMap, comp_algebraMap]
  rfl

def emb {v : Pl D} {e : AE D} (he : SplitAt D v e) : D.host.E →ₐ[D.host.F] Fv D.host.F v :=
  { (comp he).comp (incA D) with commutes' := comp_incA_algebraMap he }

theorem comp_sec {v : Pl D} {e : AE D} (he : SplitAt D v e) (a : Fv D.host.F v) : comp he (sec D v e a) = a := by
  rw [sec_apply, map_mul, comp_fj, comp_self, mul_one, evalV_singleV_same]

theorem sec_comp {v : Pl D} {e : AE D} (he : SplitAt D v e) (x : AE D) : sec D v e (comp he x) = e * x :=
  (sc_spec he x).symm

theorem int_iff_sec {v : Pl D} {e : AE D} (he : SplitAt D v e) (a : Fv D.host.F v) :
    a ∈ 𝒪[Fv D.host.F v] ↔ finPart D (sec D v e a) ∈ intAE D := by
  have h1 := (chart_comp he).2.2.2 (sec D v e a)
  rw [← sec_comp he, comp_sec he] at h1
  rw [h1, isInt_Ov, mem_integer_iff]

def splitPt {v : Pl D} {e : AE D} (h : IsSplitIdem D e) (he : SplitAt D v e)
    (hab : ∃ ε, IsPlaceIdem D v ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε) : SplitPt D (Fv D.host.F v) where
  v := v
  e := e
  split := h
  above := hab
  pr := comp he
  sec := sec D v e
  pr_sec := comp_sec he
  sec_pr := sec_comp he
  cont_pr := continuous_comp he
  cont_sec := continuous_sec
  int_iff := int_iff_sec he

theorem emb_apply {v : Pl D} {e : AE D} (he : SplitAt D v e) (a : D.host.E) : emb he a = comp he (incA D a) := rfl

theorem splitPrime_emb {v : Pl D} {e : AE D} (he : SplitAt D v e) (PP : HeightOneSpectrum (𝓞 D.host.E))
    (h : Formalism.L2.NTheta.IsIdemAt e PP) : GlobalTheory.AdelicU.splitPrime (emb he) = PP := by
  refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
  by_cases hx : x = 0
  · subst hx; simp only [Submodule.zero_mem]
  rw [GlobalTheory.AdelicU.mem_splitPrime, h.2 x hx, ← sec_comp he, ← emb_apply]
  have h0 : emb he (x : D.host.E) ≠ 0 :=
    (map_ne_zero _).2 (RingOfIntegers.coe_ne_zero_iff.2 hx)
  rw [← int_iff_sec he, mem_integer_iff, HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, map_inv₀, not_le,
    one_lt_inv₀ (zero_lt_iff.2 ((map_ne_zero _).2 h0))]

theorem exists_place : ∀ (D : D7) (PP : Formalism.L2.DIV.Pl D.host.E) (e : AE D), Formalism.L2.NTheta.IsIdemAt e PP → ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k) (_ : IsNonarchimedeanLocalField k) (q : GlobalTheory.FinPl.SplitPt D k), q.e = e ∧ q.v = PP.under (NumberField.RingOfIntegers D.host.F) ∧ (∀ a, (ofSplit q).pr a ∈ 𝒪[k] ↔ Formalism.L2.Col.IntAt PP a) ∧ DenseRange (ofSplit q).pr := by
  intro D PP e h
  obtain ⟨-, -, v, ε, hε, hs⟩ := h.1
  have he : SplitAt D v e := splitAt_of h.1 hε hs
  have hP := splitPrime_emb he PP h
  refine ⟨Fv D.host.F v, inferInstance, inferInstance, inferInstance, inferInstance, splitPt h.1 he ⟨ε, hε, hs⟩, rfl, ?_, ?_, ?_⟩
  · show v = _
    rw [← hP, GlobalTheory.AdelicU.splitPrime_under]
  · intro a
    change emb he a ∈ _ ↔ _
    rw [mem_integer_iff, HeightOneSpectrum.mem_adicCompletionIntegers, GlobalTheory.AdelicU.valued_apply_eq_valuation, hP,
      GlobalTheory.Proof.IntegralPowerExpansion.intAt_iff_val]
  · change DenseRange (emb he)
    refine Dense.mono ?_ (HeightOneSpectrum.denseRange_algebraMap D.host.F v)
    rintro _ ⟨t, rfl⟩
    exact ⟨algebraMap D.host.F D.host.E t, (emb he).commutes t⟩
end GlobalTheory.LocMod.SplitCompl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateVectorCentralTwist
section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop

namespace GlobalTheory.MiTop

set_option maxHeartbeats 1000000 in

theorem anchor_pairs : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), BotHyp W → PuNZ D → ∀ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) → ∀ v : (W.Q.Rl.MY 0).Vec, ConjVec W.S.X W.Q.instEq W.Q.Rl.θ (W.Q.Rl.MY 0) v → ∀ u, (∀ φ, ∃ C, IsCol W u C φ) ∧ (∀ T ∈ ThetaLiftSpaceZero W, ∀ C, ∃ b, IsPair W u (z * (show GA D (D.sp.Y 0) from W.Q.tS)) (T (PiTensorProduct.tprod ℂ v)) C b) ∧ ∃ (φ : D.what₂.Mu u) (C : _) (b : ℂ), ∃ T ∈ ThetaLiftSpaceZero W, IsCol W u C φ ∧ IsPair W u (z * (show GA D (D.sp.Y 0) from W.Q.tS)) (T (PiTensorProduct.tprod ℂ v)) C b ∧ b ≠ 0 := by
  intro hDS hCR D L hT Gi Gl Kc Yd cX ex W hB hPu z hzf hzc v hv u
  obtain ⟨-, hInf, -, hMatch, -, -⟩ := GlobalTheory.T.bottom_hypothesis_matching_central W hB
  have hEv := GlobalTheory.T.evalAll_and_norm_eq_one_of_conjVec hDS hCR D W.S.X W.Q.instEq W.Q.Rl.θ _ (W.Q.Rl.MY 0) (rJ W) (rChi W)
    (z * (show GA D (D.sp.Y 0) from W.Q.tS)) v (by simp) hInf hB.gap hB.idE (hMatch z hzf hzc) hv
  obtain ⟨⟨j, hjbij, hj⟩, -⟩ := hEv
  have hF := hB.fin
  have hram : (D.mem u).A.Mram ≤ (D.mem u).A.Mu0 := inf_le_left
  have hpair : ∀ (Tm : MultT W.Q.Rl.θ (W.Q.Rl.MY 0) (rJ W) (rChi W)) (C : Cu W.S.X u W.S.Y.hK),
      IsPair W u (z * (show GA D (D.sp.Y 0) from W.Q.tS)) (Tm.1 (PiTensorProduct.tprod ℂ v)) C
        ⟪((j Tm : HHX W.S.X) : L2X W.S.X), PuFun W.S.X u W.S.Y.hK (W.S.Y.Dt u) C⟫_ℂ := by
    intro Tm C
    unfold IsPair
    let g : L2X W.S.X := ((j Tm : HHX W.S.X) : L2X W.S.X)
    have hg : (g : W.S.X.B.I.GA → ℂ) =ᵐ[muX W.S.X] fun x => star (evS W.S.X W.Q.instEq (z * (show GA D (D.sp.Y 0) from W.Q.tS)) (Tm.1 (PiTensorProduct.tprod ℂ v)) x) := hj Tm
    refine ⟨star g, ?_, ?_⟩
    · have h1 : ((star g : L2X W.S.X) : W.S.X.B.I.GA → ℂ) =ᵐ[muX W.S.X] star (g : W.S.X.B.I.GA → ℂ) := MeasureTheory.Lp.coeFn_star g
      refine h1.trans ((hg.fun_comp star).trans (Filter.EventuallyEq.of_eq ?_))
      funext x
      exact star_star _
    · rw [star_star]
  refine ⟨fun φ => ?_, fun T hT C => ⟨_, hpair ⟨T, hT⟩ C⟩, ?_⟩
  · obtain ⟨C, hC⟩ := (W.S.bij u).2 (D.eMu u φ).1 (hram (D.eMu u φ).2)
    exact ⟨C, hC⟩
  · obtain ⟨φr, hφr⟩ := hPu u
    let x := (D.s_Cu u).symm ⟨φr.1, φr.2.1⟩
    let C : Cu W.S.X u W.S.Y.hK := (W.S.hI hF).eCu u x
    have hpin := W.S.colPin hF u x
    have hC : IsCol W u C ((D.eMu u).symm φr) := by
      show Formalism.L2.SG.ColDict.colDictL W.S.X (W.S.tr u) W.S.Y.hK C = _
      rw [LinearEquiv.apply_symm_apply, ← Formalism.L2.SG.ColDict.colDict_apply W.S.X (W.S.tr u) W.S.Y.hK (W.S.into u) (W.S.bij u)]
      have hpin' : Formalism.L2.SG.ColDict.colDict W.S.X (W.S.tr u) W.S.Y.hK (W.S.into u) (W.S.bij u) C = D.s_Cu u x := hpin
      rw [hpin', LinearEquiv.apply_symm_apply]
    let P : HHX W.S.X := (Formalism.L2.SG.PackageTie2.sOf hF).Pu u C
    have hP : P ≠ 0 := by
      have e := (W.S.hI hF).Pu_eq u x
      intro h0
      apply hφr
      have : (W.S.hI hF).eHH (D.s.Pu u x) = 0 := e.trans h0
      exact (LinearIsometryEquiv.map_eq_zero_iff _).1 this
    obtain ⟨Tm, hTm⟩ := hjbij.2 P
    refine ⟨(D.eMu u).symm φr, C, _, Tm.1, Tm.2, hC, hpair Tm C, ?_⟩
    rw [hTm]
    have hPv : ((P : HHX W.S.X) : L2X W.S.X) = PuFun W.S.X u W.S.Y.hK (W.S.Y.Dt u) C := rfl
    rw [hPv]
    refine inner_self_ne_zero.2 ?_
    rw [← hPv]
    exact fun h => hP (Subtype.ext h)

end GlobalTheory.MiTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DefiniteScalarComponentIsCuspAndCongruenceFixedA
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh

noncomputable section

namespace GlobalTheory.DownLift.DefiniteComp

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem extV_mul_inf (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H)
    {k : GA D (Vc D i)} (hk : k ∈ GinfC (Vc D i)) (h : GA D (Vc D i)) :
    R.extV i t y (h * k) = (R.cV i).ρ k⁻¹ (R.extV i t y h) := by
  have hr : (finHom (Vc D i)).rangeRestrict (h * k) = (finHom (Vc D i)).rangeRestrict h := by
    apply Subtype.ext
    simp [MonoidHom.mem_ker.1 hk]
  show (R.cV i).ρ (h * k)⁻¹ ((R.HV i t).e y ((finHom (Vc D i)).rangeRestrict (h * k))) =
    (R.cV i).ρ k⁻¹ ((R.cV i).ρ h⁻¹ ((R.HV i t).e y ((finHom (Vc D i)).rangeRestrict h)))
  refine (congrArg ((R.cV i).ρ (h * k)⁻¹) (congrArg ((R.HV i t).e y) hr)).trans ?_
  have e : (R.cV i).ρ (h * k)⁻¹ = (R.cV i).ρ k⁻¹ * (R.cV i).ρ h⁻¹ := by rw [_root_.mul_inv_rev, map_mul]
  exact congrArg (fun f : Module.End ℂ (R.cV i).W => f ((R.HV i t).e y ((finHom (Vc D i)).rangeRestrict h))) e

theorem extV_mul_Kg (R : RealDat D A Ks) (hM : R.IsModels) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H)
    {κ : GA D (Vc D i)} (hκ : κ ∈ GfC (Vc D i))
    (hK : finE (Vc D i) κ ∈ Kg D.sp.cm (Vc D i).gram (R.βV i) (R.Pg ∪ R.Q t)) (h : GA D (Vc D i)) :
    R.extV i t y (h * κ) = R.extV i t y h := by
  have h2 : Kg D.sp.cm (Vc D i).gram (R.βV i) (R.Pg ∪ R.Q t) ≤
      lev D.sp.cm (Vc D i).gram (R.βV i) (flag1L (R.datVt i t)) :=
    Kg_le_lev (D := flag1L (R.datVt i t)) Finset.subset_union_left Finset.subset_union_right
  have hlev : κ ∈ levG (Vc D i) (R.βV i) (flag1L (R.datVt i t)) := mem_levA.2 ⟨hκ, h2 hK⟩
  have hred : ∀ PP ∈ R.Pg ∪ R.Q t, redFn (R.βV i) PP (finE (Vc D i) κ) = 1 := fun PP hP =>
    (mem_princAt.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hK.2 PP) hP)).2
  have hfn : levFn (R.βV i) (flag1L (R.datVt i t)) (finE (Vc D i) κ) = 1 :=
    GlobalTheory.ThetaIntegrand.levFn_eq_one (R.βV i) _ (flag1L (R.datVt i t))
      (fun PP hP => hred PP (Finset.mem_union_left _ hP)) (fun PP hP => hred PP (Finset.mem_union_right _ hP))
  have hchi : levChi (Vc D i) (R.βV i) (flag1L (R.datVt i t)) κ = 1 :=
    (congrArg (fun u : ℂˣ => (u : ℂ)) hfn).trans Units.val_one
  exact (GlobalTheory.DownLift.GenFinite.extV_type R hM i t y κ hlev h).trans (by simp only [hchi, one_smul])

def compL (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) :
    ((R.cV i).W →ₗ[ℂ] ℂ) →ₗ[ℂ] (GA D (Vc D i) → ℂ) :=
  LinearMap.pi fun g => LinearMap.applyₗ (R := ℂ) (R.extV i t y g)

theorem mul_inf_mem_range (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (l : (R.cV i).W →ₗ[ℂ] ℂ)
    {k : GA D (Vc D i)} (hk : k ∈ GinfC (Vc D i)) :
    (fun g => l (R.extV i t y (g * k))) ∈ LinearMap.range (compL R i t y) :=
  ⟨l ∘ₗ (R.cV i).ρ k⁻¹, funext fun g => (congrArg l (extV_mul_inf R i t y hk g)).symm⟩

theorem definiteScalarComponent_isCusp_and_congruence_fixed : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t cA a, Defin R.θ (Vc D i) cA a → ∀ (y : (R.HV i t).H) (l : (R.cV i).W →ₗ[ℂ] ℂ), (fun g => l (R.extV i t y g)) ∈ GlobalTheory.Cusp.A0 R.θ (Vc D i) cA ∧ ∀ κ ∈ prin (Vc D i) (R.βV i) (R.Pg ∪ R.Q t), ∀ g, l (R.extV i t y (g * κ)) = l (R.extV i t y g) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG _ i t cA a hd y l
  have hM : R.IsModels := hG.core.models
  have hf : (R.HV i t).e y ∈ Formalism.IndefR.Bridge.AdForms (Formalism.IndefR.Bridge.ratF (Vc D i)) (R.cV i).coef.ρ
      (levEnv _ (R.βV i) (R.datVt i t)).J (levEnv _ (R.βV i) (R.datVt i t)).χ :=
    (hM.HV i t).2.1.le (LinearMap.mem_range_self _ y)
  have hcont : Continuous fun g => l (R.extV i t y g) :=
    (LinearMap.continuous_of_finiteDimensional l).comp
      (GlobalTheory.ThetaIntegrand.ext_continuous (R.cV i) (hM.cV i) (R.βV i) (R.datVt i t) hf)
  have hleft : ∀ γ ∈ GQ (Vc D i), ∀ g, l (R.extV i t y (γ * g)) = l (R.extV i t y g) := fun γ hγ g =>
    congrArg l (GlobalTheory.ThetaIntegrand.ext_invariant (R.cV i) hf γ hγ g)
  have hlevel : ∃ U : Subgroup (GA D (Vc D i)), IsOpen (U : Set (GA D (Vc D i))) ∧
      ∀ k ∈ U, k ∈ GfC (Vc D i) → ∀ g, l (R.extV i t y (g * k)) = l (R.extV i t y g) :=
    ⟨_, GlobalTheory.DefiniteEnd.isOpen_Kg (Vc D i) (R.βV i) (R.Pg ∪ R.Q t), fun k hk hkf g =>
      congrArg l (extV_mul_Kg R hM i t y hkf hk g)⟩
  have hkfin : FiniteDimensional ℂ (Submodule.span ℂ {ψ : GA D (Vc D i) → ℂ |
      ∃ k ∈ GinfC (Vc D i), ψ = rTr (Vc D i) k fun g => l (R.extV i t y g)}) :=
    Submodule.finiteDimensional_of_le (Submodule.span_le.2 (by
      rintro _ ⟨k, hk, rfl⟩
      exact mul_inf_mem_range R i t y l hk))
  have hdef : IsAutFunDef (Vc D i) fun g => l (R.extV i t y g) := ⟨⟨hleft, hlevel, hcont⟩, hkfin⟩
  have hdefn : (Vc D i).IsDefinite := fun τ => Or.inl (hd.pos τ)
  have hsm := ((GlobalTheory.DefiniteForms.autFunDefIffSm D) R.θ hd.inf (Vc D i) hd.sig hdefn _).1 hdef
  have hcusp : IsCuspFun (Vc D i) fun g => l (R.extV i t y g) := fun r C hC =>
    absurd hC (GlobalTheory.Per.isAniso_of_posDef hd.sig hd.pos r C)
  have hK : GlobalTheory.Doubling.IsKFinite (GlobalTheory.Cusp.Kinf R.θ (Vc D i) cA) fun g => l (R.extV i t y g) :=
    GlobalTheory.Doubling.isKFinite_iff.2 ⟨LinearMap.range (compL R i t y), inferInstance, fun k hk =>
      mul_inf_mem_range R i t y l (GlobalTheory.Cusp.Kinf_le hk)⟩
  refine ⟨GlobalTheory.Cusp.mem_cuspForms.2 ⟨⟨hsm, hcusp⟩, hK⟩, fun κ hκ g => ?_⟩
  have h1 := mem_levA.1 hκ
  have h2 : finE (Vc D i) κ ∈ Kg D.sp.cm (Vc D i).gram (R.βV i) (R.Pg ∪ R.Q t) :=
    (Model.lev_prinDat (Vc D i) (R.βV i) (R.Pg ∪ R.Q t)) ▸ h1.2
  exact congrArg l (extV_mul_Kg R hM i t y h1.1 h2 g)

end GlobalTheory.DownLift.DefiniteComp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DescentDataStepLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

noncomputable section

namespace GlobalTheory.MidVacLat

variable {D : D7}

theorem mt_mul' (V : HSp D) (g h : GA D V) : mt V (g * h) = mt V g * mt V h := rfl

theorem mt_one' (V : HSp D) : mt V 1 = 1 := rfl

theorem mt_mul_inv_mulVec (V : HSp D) (g : GA D V) (y : Fin V.rank → AE D) : mt V g *ᵥ (mt V g⁻¹ *ᵥ y) = y := by
  rw [Matrix.mulVec_mulVec, ← mt_mul', mul_inv_cancel, mt_one', Matrix.one_mulVec]

theorem mulVec_mem_idAt {n : ℕ} (A : Matrix (Fin n) (Fin n) (AE D)) {P : GlobalTheory.FinPl.Pl D → Prop} {y : Fin n → AE D}
    (hy : ∀ i, y i ∈ GlobalTheory.FinPl.idAt D P) (i : Fin n) : (A *ᵥ y) i ∈ GlobalTheory.FinPl.idAt D P := by
  simp only [Matrix.mulVec, dotProduct]
  exact sum_mem fun j _ => Ideal.mul_mem_left _ _ (hy j)

theorem moves_inv {S : HSp D} {g : GA D S} {L M : GlobalTheory.FinPl.Lat S} {P : GlobalTheory.FinPl.Pl D → Prop}
    (h : GlobalTheory.FinPl.Moves S g L M P) : GlobalTheory.FinPl.Moves S g⁻¹ M L P := by
  intro y hy
  have e := h (mt S g⁻¹ *ᵥ y) (mulVec_mem_idAt _ hy)
  rw [mt_mul_inv_mulVec] at e
  exact e.symm

theorem smul_mem_latA {S : HSp D} {L : GlobalTheory.FinPl.Lat S} {P : GlobalTheory.FinPl.Pl D → Prop} {a : D.host.E} (ha : a ∈ D.host.AA)
    {y : Fin S.rank → AE D} (hy : y ∈ GlobalTheory.FinPl.latV S L P) :
    ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) • y ∈ GlobalTheory.FinPl.latA S L P := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβi, hβ, c, hc, x, hx, rfl⟩ := hz
    rw [Set.mem_singleton_iff] at hc
    subst hc
    refine AddSubgroup.subset_closure ⟨β, hβi, hβ, a, ha, x, hx, ?_⟩
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [smul_add]; exact add_mem hz hz'
  | neg z _ hz => rw [smul_neg]; exact neg_mem hz

theorem mulVec_mem_latA {S : HSp D} {g : GA D S} {L M : GlobalTheory.FinPl.Lat S} {P : GlobalTheory.FinPl.Pl D → Prop}
    (h : GlobalTheory.FinPl.Moves S g L M P) {z : Fin S.rank → AE D} (hz : z ∈ GlobalTheory.FinPl.latA S L P) :
    mt S g *ᵥ z ∈ GlobalTheory.FinPl.latA S M P := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨β, hβi, hβ, a, ha, x, hx, rfl⟩ := hy
    set y' : Fin S.rank → AE D := fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i) with hy'
    have hy'm : y' ∈ GlobalTheory.FinPl.latV S L P := AddSubgroup.subset_closure ⟨β, hβi, hβ, 1, rfl, x, hx, rfl⟩
    have hsplit : (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * x i)) = ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) • y' := by
      funext i
      simp only [hy', Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [hsplit, Matrix.mulVec_smul]
    exact smul_mem_latA ha ((h y' (GlobalTheory.FinPl.FrameLat.latV_supp hy'm)).1 hy'm)
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact add_mem hz hz'
  | neg z _ hz => rw [Matrix.mulVec_neg]; exact neg_mem hz

theorem actO_mem_latO {S T : HSp D} {Λ M : GlobalTheory.FinPl.Lat S} {Λ' M' : GlobalTheory.FinPl.Lat T} (hΛ : IsSelfDualC S Λ)
    (hM : IsSelfDualC S M) (hΛ' : IsSelfDualC T Λ') (hM' : IsSelfDualC T M') {P : GlobalTheory.FinPl.Pl D → Prop} {g : GA D S}
    {h : GA D T} (hg : GlobalTheory.FinPl.Moves S g Λ M P) (hh : GlobalTheory.FinPl.Moves T h Λ' M' P) {u : WO S T}
    (hu : u ∈ latO S T (Λ : Set _) (Λ' : Set _) P) : actO S T g h u ∈ latO S T (M : Set _) (M' : Set _) P := by
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D S T Λ Λ' hΛ hΛ' P] at hu
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D S T M M' hM hM' P]
  obtain ⟨hmx, hmap⟩ := hu
  refine ⟨fun i j => ?_, fun y hy => ?_⟩
  · show (HMul.hMul (HMul.hMul (mt T h) (u : Matrix (Fin T.rank) (Fin S.rank) (AE D))) (mt S g⁻¹)) i j ∈ _
    rw [Matrix.mul_apply]
    refine sum_mem fun l _ => Ideal.mul_mem_right _ _ ?_
    rw [Matrix.mul_apply]
    exact sum_mem fun k _ => Ideal.mul_mem_left _ _ (hmx k l)
  · change (HMul.hMul (HMul.hMul (mt T h) (u : Matrix (Fin T.rank) (Fin S.rank) (AE D))) (mt S g⁻¹)) *ᵥ y ∈ _
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have h1 : mt S g⁻¹ *ᵥ y ∈ GlobalTheory.FinPl.latV S Λ P :=
      (moves_inv hg y (GlobalTheory.FinPl.FrameLat.latV_supp hy)).1 hy
    exact mulVec_mem_latA hh (hmap _ h1)

theorem actO_smul_left {S T : HSp D} (g : GA D S) (h : GA D T) (e : AE D) (x : WO S T) :
    actO S T g h (e • x) = e • actO S T g h x := by
  simp only [actO, Matrix.mul_smul, Matrix.smul_mul]

theorem actO_two_nsmul {S T : HSp D} (g : GA D S) (h : GA D T) (x : WO S T) :
    actO S T g h (2 • x) = 2 • actO S T g h x := by
  simp only [two_nsmul, actO, Matrix.mul_add, Matrix.add_mul]

theorem isHalf_actO {S T : HSp D} (g : GA D S) (h : GA D T) {e : AE D} {x : WO S T} (hx : IsHalf e x) :
    IsHalf e (actO S T g h x) := by
  have hx' : e • x = x := by
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul]
    exact hx i j
  intro i j
  have := congrFun (congrFun (actO_smul_left g h e x) i) j
  rw [hx'] at this
  rw [Matrix.smul_apply, smul_eq_mul] at this
  exact this.symm

theorem actO_actO_inv {S T : HSp D} (g : GA D S) (h : GA D T) (x : WO S T) :
    actO S T g h (actO S T g⁻¹ h⁻¹ x) = x := by
  show HMul.hMul (HMul.hMul (mt T h) (HMul.hMul (HMul.hMul (mt T h⁻¹) (x : Matrix (Fin T.rank) (Fin S.rank) (AE D))) (mt S g⁻¹⁻¹))) (mt S g⁻¹) = x
  rw [inv_inv, Matrix.mul_assoc, Matrix.mul_assoc, ← mt_mul' S g g⁻¹, mul_inv_cancel,
    mt_one', Matrix.mul_one, ← Matrix.mul_assoc, ← mt_mul' T h h⁻¹, mul_inv_cancel,
    mt_one', Matrix.one_mul]

theorem isLatVac_move {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T}
    (hW : IsWeilDatumO ψ S T χS χT om) {Λ M : GlobalTheory.FinPl.Lat S} {Λ' M' : GlobalTheory.FinPl.Lat T} (hΛ : IsSelfDualC S Λ)
    (hM : IsSelfDualC S M) (hΛ' : IsSelfDualC T Λ') (hM' : IsSelfDualC T M') {b : GA D S} {b' : GA D T}
    (hb : GlobalTheory.FinPl.Moves S b Λ M fun _ => True) (hb' : GlobalTheory.FinPl.Moves T b' Λ' M' fun _ => True) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (hv : IsLatVac (heisO ψ S T) (latO S T (Λ : Set _) (Λ' : Set _) fun _ => True) f) :
    IsLatVac (heisO ψ S T) (latO S T (M : Set _) (M' : Set _) fun _ => True) (om (b, b') f) := by
  have key : ∀ u, u ∈ latO S T (M : Set _) (M' : Set _) (fun _ => True) → actO S T b⁻¹ b'⁻¹ u ∈ latO S T (Λ : Set _) (Λ' : Set _) fun _ => True :=
    fun u hu => actO_mem_latO hM hΛ hM' hΛ' (moves_inv hb) (moves_inv hb') hu
  refine ⟨fun u hu => ?_, fun e he u hu hh => ?_⟩
  · have hw := key u hu
    have h2 : 2 • u = actO S T b b' (2 • actO S T b⁻¹ b'⁻¹ u) := by
      rw [actO_two_nsmul, actO_actO_inv]
    rw [h2, ← hW.om_heis b b' _ f hf, hv.1 _ hw]
  · have hw := key u hu
    have h1 : u = actO S T b b' (actO S T b⁻¹ b'⁻¹ u) := (actO_actO_inv b b' u).symm
    rw [h1, ← hW.om_heis b b' _ f hf, hv.2 e he _ hw (isHalf_actO _ _ hh)]

theorem main : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : RealPack ex) (u : D.what₂.Word) (f : FamCh W u), PkHyp W → f.RowOK → ∀ v : VCom f.c, v.Is → VTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (pk W).Pg), GPin G → GRead f G pl → ∀ j, j + 1 < D.R.m → ∀ d₀, IsDG W j ((pk W).MY (j + 1)) ((pk W).ΛY (j + 1)) ((pk W).βY (j + 1)) ((pk W).vac j) d₀ → ∃ (M : GlobalTheory.FinPl.Lat (Yc D j)) (M' : GlobalTheory.FinPl.Lat (Yc D (j + 1))), IsSelfDualC (Yc D j) M ∧ IsSelfDualC (Yc D (j + 1)) M' ∧ GlobalTheory.FinPl.Moves (Yc D j) (f.g.b j) ((pk W).ΛY j) M (fun _ => True) ∧ GlobalTheory.FinPl.Moves (Yc D (j + 1)) (f.g.b (j + 1)) ((pk W).ΛY (j + 1)) M' (fun _ => True) ∧ GlobalTheory.FinPl.Vac f.c.ψ _ _ M M' (fun _ => True) ((pk W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((pk W).vac j)) := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hPk hRow v hv hVT n G pl hGP hGR j hj d₀ hd₀
  have hLev := hPk.bot.hyp.2.2.2.1.lev
  have sd0 : IsSelfDualC (Yc D j) ((pk W).ΛY j) :=
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hLev.βY j (by omega))
  have sd1 : IsSelfDualC (Yc D (j + 1)) ((pk W).ΛY (j + 1)) :=
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hLev.βY (j + 1) hj)
  obtain ⟨M, hM, hmv⟩ := (GlobalTheory.T.selfDual_image_adelicPoint_wittCore D _ _ sd0).1 (f.g.b j)
  obtain ⟨M', hM', hmv'⟩ := (GlobalTheory.T.selfDual_image_adelicPoint_wittCore D _ _ sd1).1 (f.g.b (j + 1))
  have hWe := W.Q.charW.base.chain.ωY W.P.A3.A.μ0 j hj
  have hvth := hd₀.2.1.2.theta
  have hvlat := hd₀.2.1.2.lat
  exact ⟨M, M', hM, hM', hmv _, hmv' _, hWe.om_pres _ _ hvth,
    isLatVac_move hWe sd0 hM sd1 hM' (hmv _) (hmv' _) hvth hvlat⟩

end GlobalTheory.MidVacLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DescentDataStepSelfDual
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

noncomputable section

namespace GlobalTheory.Fam.OffLevel

open GlobalTheory.FinPl GlobalTheory.FinPl.KSplit

variable {D : D7}

theorem mem_latV_at_iff_all (S : HSp D) (L : Lat S) (p : Pl D) {z : Fin S.rank → AE D}
    (hz : ∀ i, z i ∈ idAt D (· = p)) : z ∈ latV S L (· = p) ↔ z ∈ latV S L (fun _ => True) := by
  constructor
  · exact fun h => latV_mono S L (fun _ _ => trivial) h
  · intro h
    have h1 := ((mem_latV_iff_parts S L (fun _ => True) {p}
      (fun i => idAt_mono (fun _ _ => trivial) (hz i))).1 h).1
    have e : eQ {p} • z = z := funext fun i =>
      eQ_mul_of_in (P := fun _ => True) {p}
        (idAt_mono (fun w hw => ⟨trivial, Finset.mem_singleton.2 hw⟩) (hz i))
    rw [e] at h1
    exact latV_mono S L (fun w hw => Finset.mem_singleton.1 hw.2) h1

theorem latV_eq_of_moves (S : HSp D) (g : GA D S) (Λ N M : Lat S) (p : Pl D)
    (hN : Moves S g Λ N (· = p)) (hM : Moves S g Λ M (fun _ => True)) :
    latV S N (· = p) = latV S M (· = p) := by
  have key : ∀ z : Fin S.rank → AE D, (∀ i, z i ∈ idAt D (· = p)) →
      (z ∈ latV S N (· = p) ↔ z ∈ latV S M (· = p)) := by
    intro z hz
    set y := mt S g⁻¹ *ᵥ z with hy
    have hys : ∀ i, y i ∈ idAt D (· = p) := mulVec_mem S _ hz
    have hgy : mt S g *ᵥ y = z := by
      rw [hy, Matrix.mulVec_mulVec, ← KSplit.mt_mul, mul_inv_cancel]
      exact Matrix.one_mulVec z
    rw [← hgy, ← hN y hys, mem_latV_at_iff_all S M p (by rw [hgy]; exact hz),
      ← hM y (fun i => idAt_mono (fun _ _ => trivial) (hys i)), mem_latV_at_iff_all S Λ p hys]
  ext z
  constructor
  · intro h; exact (key z (GlobalTheory.FinPlLoc.latV_idAt h)).1 h
  · intro h; exact (key z (GlobalTheory.FinPlLoc.latV_idAt h)).2 h

end GlobalTheory.Fam.OffLevel

end

open GlobalTheory.Fam.OffLevel in
theorem GlobalTheory.Fam.latV_N_eq_off_level : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : RealPack ex) (u : D.what₂.Word) (f : FamCh W u), PkHyp W → f.RowOK → ∀ v : VCom f.c, v.Is → VTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (pk W).Pg), GPin G → GRead f G pl → ∀ j, j + 1 < D.R.m → ∀ (M : GlobalTheory.FinPl.Lat (Yc D j)) (M' : GlobalTheory.FinPl.Lat (Yc D (j + 1))), GlobalTheory.FinPl.Moves (Yc D j) (f.g.b j) ((pk W).ΛY j) M (fun _ => True) → GlobalTheory.FinPl.Moves (Yc D (j + 1)) (f.g.b (j + 1)) ((pk W).ΛY (j + 1)) M' (fun _ => True) → ∀ p, p ∉ v.gP → GlobalTheory.FinPl.latV (Yc D j) (v.N j) (· = p) = GlobalTheory.FinPl.latV (Yc D j) M (· = p) ∧ GlobalTheory.FinPl.latV (Yc D (j + 1)) (v.N (j + 1)) (· = p) = GlobalTheory.FinPl.latV (Yc D (j + 1)) M' (· = p) := by
  intro D L hT Gi Gl Kc Yd cX ex W u f _ _ v _ hv n G pl _ _ j hj M M' hM hM' p hp
  have hP : ∀ q, (· = p) q → q ∉ v.gP := fun q hq => hq ▸ hp
  exact ⟨latV_eq_of_moves _ _ _ _ _ p (hv.moves j (by omega) _ hP) hM,
    latV_eq_of_moves _ _ _ _ _ p (hv.moves (j + 1) hj _ hP) hM'⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqualIdentificationPairPriceLeSixFifthsStatement
section
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 GlobalTheory.Core.Diag GlobalTheory.Core.Deg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equalIdentificationPairPrice_le_six_fifths : ∀ (C' Cl Cg cb Cw cT CT C0 : ℝ) (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X), Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → PgC Y ≤ 6 / 5 := by
  first | exact @GlobalTheory.Core.Deg.pgC_le_six_fifths | exact GlobalTheory.Core.Deg.pgC_le_six_fifths | (intros; apply GlobalTheory.Core.Deg.pgC_le_six_fifths <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsLocalModelCreationWeilActionMovedFramesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.StepData NumberField
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLocalModel_creation_weilAction_moved_frames : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS GS : Frame k S.rank Y') (FT GT : Frame k T.rank Y) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsInfFam θ → IsWeilDatumO ψ S T χS χT ω → ∀ (g : GA D S) (h : GA D T), GS.β = (Formalism.L2.Theta.mt S g).map p.π * FS.β → GT.β = (Formalism.L2.Theta.mt T h).map p.π * FT.β → ∀ sS sT BS BT P T₁, p.IsModel ψ FS FT T₁ → ∃ T₂, p.IsModel ψ GS GT T₂ ∧ ∀ Φ, T₂ Φ = ω (g, h) (pureTensorO ψ θ S T sS sT BS BT (T₁ Φ) P) := by
  first | exact @GlobalTheory.LocModMove.isModel_move | exact GlobalTheory.LocModMove.isModel_move | (intros; apply GlobalTheory.LocModMove.isModel_move <;> assumption)
end

