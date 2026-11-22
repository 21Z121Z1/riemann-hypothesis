import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0218
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0270
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0197
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0475
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0263
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0479
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0469
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteOrderChartsMiddleSteps
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemberStepCharts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartLastStepTwistBasePoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0287
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0069
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0181
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0372
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0448
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0270
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0201
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0028
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0481
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0479
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0344
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDatumCarriedBackToBaseVacuum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0307
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0305
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0164
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0480
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0036
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0035
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0439
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0222
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0458
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0484
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0462
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0371
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0355
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0483
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsContAutRTrans
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Mi.BotPin

variable {D : D7}

theorem isContAut_zero (V : HSp D) : IsContAut V (0 : GA D V → ℂ) :=
  ⟨fun _ _ _ => rfl, continuous_const⟩

theorem isContAut_add {V : HSp D} {f g : GA D V → ℂ} (hf : IsContAut V f) (hg : IsContAut V g) :
    IsContAut V (f + g) :=
  ⟨fun γ hγ x => by simp only [Pi.add_apply, hf.1 γ hγ x, hg.1 γ hγ x], hf.2.add hg.2⟩

theorem isContAut_smul {V : HSp D} {f : GA D V → ℂ} (hf : IsContAut V f) (c : ℂ) : IsContAut V (c • f) :=
  ⟨fun γ hγ x => by simp only [Pi.smul_apply, hf.1 γ hγ x], hf.2.const_smul c⟩

theorem isContAut_rTrans {V : HSp D} {f : GA D V → ℂ} (h : GA D V) (hf : IsContAut V f) : IsContAut V (rTrans h f) :=
  ⟨fun γ hγ x => by simp only [rTrans, mul_assoc, hf.1 γ hγ], hf.2.comp (continuous_mul_const h)⟩

theorem isContAut_multT {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S} {J : Set (GA D V)}
    {χ : GA D V → ℂ} {G : SmT M →ₗ[ℂ] (GA D V → ℂ)} (hG : G ∈ MultT θ M J χ) (x : SmT M) : IsContAut V (G x) := by
  obtain ⟨T, hT, rfl⟩ := hG
  induction hT using Submodule.span_induction generalizing x with
  | mem T hT =>
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      rw [map_smul, LinearEquiv.coe_coe, PiTensorProduct.lift.tprod]
      exact isContAut_smul ⟨(hT.aut v).left, (hT.aut v).cont⟩ r
    | add x y hx hy => rw [map_add]; exact isContAut_add hx hy
  | zero => simpa using isContAut_zero V
  | add T₁ T₂ _ _ h₁ h₂ => rw [map_add, LinearMap.add_apply]; exact isContAut_add (h₁ x) (h₂ x)
  | smul c T _ h => rw [map_smul, LinearMap.smul_apply]; exact isContAut_smul (h x) c

theorem per_congr {ρ : ℕ} {ψ : AddChar (AF D.host.F) ℂ} {B₁ B₂ : BesLev D ρ} (h : B₁ = B₂) (φ₁ : GA D B₁.A → ℂ)
    (φ₂ : GA D B₂.A → ℂ) (hφ : HEq φ₁ φ₂) (f₁ : GA D B₁.V → ℂ) (f₂ : GA D B₂.V → ℂ) (hf : HEq f₁ f₂) :
    B₁.per ψ φ₁ f₁ = B₂.per ψ φ₂ f₂ := by
  subst h; cases hφ; cases hf; rfl

end GlobalTheory.Core.Mi.BotPin

set_option maxHeartbeats 1000000 in
open GlobalTheory.Core.Mi.BotPin in

theorem GlobalTheory.Core.Mi.bot_of_pinBot : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (u : D.what₂.Word) (F₀ : ∀ u, Formalism.L2.Forms.Forms0 D u) (S : STrue D F₀) (d : GlobalTheory.SeeSaw.Dat D u), GlobalTheory.Core.Mi.IdE S.X → GlobalTheory.Count.GapGe S.X.B (100 * (D.R.r : ℝ) ^ 4) → PinBot S d → d.Base → d.Bot := by
  intro hDS hCR D u F₀ S d hIdE hGap hPin hBase
  obtain ⟨h0, B, a₀, a, hBlev, hAd, hH0, haf, hac, hMatch, hrd⟩ := hPin
  obtain ⟨R, hRinj, hR⟩ := GlobalTheory.T.bessel_column_form_central_translation D S.X S.inst u d.c.ψ (D.sp.X 0) B S.Y.hK a hIdE haf hac
  obtain ⟨ξ, hξspan, hξ⟩ := GlobalTheory.T.dictionaryColumnScalarForm_eq_traceColumnForm D S.X S.inst u d.c.ψ B (F₀ u) (S.tr u) S.Y.hK d.c.θ a₀ hBase.com.inf hIdE
    hAd hH0 (S.lev u)
  have hram : (D.mem u).A.Mram ≤ (D.mem u).A.Mu0 := inf_le_left
  let e := Formalism.L2.SG.ColDict.colDict S.X (S.tr u) S.Y.hK (S.into u) (S.bij u)
  let T0 : (D.mem u).A.Mram →ₗ[ℂ] Cu S.X u S.Y.hK := e.symm.toLinearMap ∘ₗ Submodule.inclusion hram
  let V : (D.mem u).A.Mram →ₗ[ℂ] D.s.Cu u :=
    ((S.hI S.hF).eCu u).symm.toLinearEquiv.toLinearMap ∘ₗ R ∘ₗ T0
  refine ⟨V, ?_, ?_⟩
  · exact ((S.hI S.hF).eCu u).symm.injective.comp
      (hRinj.comp (e.symm.injective.comp (Submodule.inclusion_injective hram)))

  · intro φ hvan
    let T : Cu S.X u S.Y.hK := T0 φ
    have hφT : Formalism.L2.SG.ColDict.colDictL S.X (S.tr u) S.Y.hK T = φ.1 := by
      have := congrArg Subtype.val (e.apply_symm_apply (Submodule.inclusion hram φ))
      exact this
    have hm : 0 < D.R.m := by omega
    have hst := hBase.st 0 hm
    have hcontT : ∀ ξ', IsContAut (D.sp.X 0) (B.colForm T.1 ξ') :=
      (GlobalTheory.T.fourier_coefficient_bessel D S.X S.inst u d.c.ψ (D.sp.X 0) B S.Y.hK T).1
    have hcontR : ∀ ξ', IsContAut (D.sp.X 0) (B.colForm (R T).1 ξ') :=
      (GlobalTheory.T.fourier_coefficient_bessel D S.X S.inst u d.c.ψ (D.sp.X 0) B S.Y.hK (R T)).1
    let t : GA D (D.sp.Y 0) := ((iotaX S.X S.inst).symm (1, S.X.xu u))⁻¹ * embA B.d B.o (a₀ * a) *
      (show GA D (D.sp.Y 0) from d.t 0)
    have hvan' : ∀ G ∈ MultT d.c.θ (d.st 0).M (d.lev 0) (levChi (D.sp.Y 0) d.bot.β d.bot.L), ∀ ξ' x,
        B.lev.per d.c.ψ (B.colForm (R T).1 ξ') (rTrans ((iotaX S.X S.inst).symm (1, S.X.xu u) * t) (G x)) = 0 := by
      intro G hG ξ' x
      have hf : IsContAut (D.sp.Y 0) (rTrans ((iotaX S.X S.inst).symm (1, S.X.xu u) * t) (G x)) :=
        isContAut_rTrans _ (isContAut_multT hG x)
      have hy : ∀ y, B.lev.per d.c.ψ (B.colForm (R T).1 (ξ y))
          (rTrans ((iotaX S.X S.inst).symm (1, S.X.xu u) * t) (G x)) = 0 := by
        intro y
        have h1 := hvan D.R.rS h0 ⟨G, hG⟩ y x
        have h3 := GlobalTheory.T.bessel_period_right_translation_invariant D d.c.ψ D.R.rS B.lev (rTrans a₀⁻¹ (B.colForm T.1 (ξ y))) (rTrans (d.t 0) (G x)) (a₀ * a)
          hBase.com.std (isContAut_rTrans _ (hcontT (ξ y))) (isContAut_rTrans _ (isContAut_multT hG x))
        have e1 : B.colForm (R T).1 (ξ y) = rTrans (a₀ * a) (rTrans a₀⁻¹ (B.colForm T.1 (ξ y))) := by
          rw [hR T (ξ y)]
          funext g
          simp only [rTrans]
          congr 1
          rw [Subgroup.mem_center_iff.1 hac a₀]
          group
        have e2 : rTrans ((iotaX S.X S.inst).symm (1, S.X.xu u) * t) (G x) =
            rTrans (embA B.d B.o (a₀ * a)) (rTrans (d.t 0) (G x)) := by
          funext g
          show G x (g * ((iotaX S.X S.inst).symm (1, S.X.xu u) * t)) =
            G x (g * embA B.d B.o (a₀ * a) * (show GA D (D.sp.Y 0) from d.t 0))
          refine congrArg (G x) ?_
          change g * ((iotaX S.X S.inst).symm (1, S.X.xu u) * (((iotaX S.X S.inst).symm (1, S.X.xu u))⁻¹ *
            embA B.d B.o (a₀ * a) * (show GA D (D.sp.Y 0) from d.t 0))) = _
          rw [mul_assoc ((iotaX S.X S.inst).symm (1, S.X.xu u))⁻¹ (embA B.d B.o (a₀ * a)), mul_inv_cancel_left]
          exact (mul_assoc _ _ _).symm
        have e4 : rTrans a₀⁻¹ (B.colForm T.1 (ξ y)) = d.rd 0 φ.1 y := by
          rw [hrd, ← hφT]
          funext g
          exact (hξ T y g).symm
        have e3 : B.lev.per d.c.ψ (rTrans a₀⁻¹ (B.colForm T.1 (ξ y))) (rTrans (d.t 0) (G x)) = 0 := by
          rw [e4]
          exact (per_congr hBlev _ _ HEq.rfl _ _ HEq.rfl).trans h1
        rw [e1, e2]
        exact h3.trans e3
      have hmem : ξ' ∈ Submodule.span ℂ (Set.range ξ) := by rw [hξspan]; exact Submodule.mem_top
      obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hmem
      have hlin : B.colForm (R T).1 ξ' = ∑ i ∈ c.support, c i • B.colForm (R T).1 (ξ i) := by
        rw [← hc]
        funext g
        simp only [SBes.colForm, Finsupp.sum, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply]
      rw [hlin, GlobalTheory.T.period_sum_holds D d.c.ψ hBase.com.std D.R.rS B.lev _ hf _ c.support c (fun i => B.colForm (R T).1 (ξ i))
        (fun i _ => hcontR (ξ i))]
      exact Finset.sum_eq_zero fun i _ => by rw [hy i, mul_zero]
    have hP := GlobalTheory.T.puFun_eq_zero_of_per_colForm_eq_zero hDS hCR D S.X S.inst u d.c.ψ (D.sp.X 0) B S.Y d.c.θ (d.st 0).par (d.st 0).M (d.lev 0)
      (levChi (D.sp.Y 0) d.bot.β d.bot.L) t hst.par hBase.com.inf hBase.com.std hGap hIdE hMatch (S.hF.inHH u) (R T) hvan'
    have hPu := (S.hI S.hF).Pu_eq u (V φ)
    have e5 : (S.hI S.hF).eCu u (V φ) = R T := LinearIsometryEquiv.apply_symm_apply _ _
    rw [e5] at hPu
    have e6 : (Formalism.L2.SG.PackageTie2.sOf S.hF).Pu u (R T) = 0 := Subtype.ext hP
    rw [e6] at hPu
    exact (LinearIsometryEquiv.map_eq_zero_iff _).1 hPu
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastStepChartBasePointCarriesStdPointStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastStepChartBasePoint_carries_stdPoint : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) {C : Type} (chOf : (I.stp u a B.R.m).Cl → C) (Lb : C → Submodule (𝓞 B.host.E) (Fin (B.R.N B.R.m) → B.host.E)) (U : C → Subgroup (TC.GA B (B.R.N B.R.m))) (chi : ∀ β, U β →* ℂˣ) (y : (I.stp u a B.R.m).Cl → TC.GA B (B.R.N B.R.m)) (st : ∀ c, (I.stp u a B.R.m).Stab c → GL (Fin (B.R.N B.R.m)) B.host.E) (k : C → TC.GA B (B.R.N B.R.m)), I.Reads u a B.R.m chOf Lb U chi y st k → (∀ β, I.TopPt l Z u a (k β)) → ∀ β, (∃ q : Formalism.L2.Col.ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u B.R.m, TC.PtOf (k β) q) ∧ ∀ P ∈ I.SQ, P ∉ I.Q a → (k β).1.map (adAt B.host.F P) = 1 := by
  first | exact @GlobalTheory.Mem.Col2.TopBase.topBase_ok | exact GlobalTheory.Mem.Col2.TopBase.topBase_ok | (intros; apply GlobalTheory.Mem.Col2.TopBase.topBase_ok <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelStepVectorEqHeisenbergCombinationVacuum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StepComb

variable {D : D7}

theorem idem_mem_idAt {es : AE D} {PP : Pl D.host.E} (h : Formalism.L2.NTheta.IsIdemAt es PP) :
    es ∈ GlobalTheory.FinPl.idAt D (· = PP.under (𝓞 D.host.F)) := by
  have h' := h
  obtain ⟨⟨a1, a2, w, ε, hε, a3⟩, -⟩ := h'
  have hw := GlobalTheory.IdemUnder.under_eq_of_isIdemAt D es PP w ε h hε a3
  have hε' := hε
  obtain ⟨α, rfl, -, h0⟩ := hε'
  have hm : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) ∈ GlobalTheory.FinPl.idAt D (· = w) :=
    GlobalTheory.FinPl.LatMem.tmul_mem_idAt (P := (· = w)) (fun v hv => h0 v hv) 1
  have e1 : es = es * (es + cA D es) := by rw [mul_add, a1, a2, add_zero]
  rw [e1, a3, hw]
  exact Ideal.mul_mem_left _ _ hm

theorem idemSum_mem_idAt {e : AE D} {Z : Finset (Pl D.host.E)} (h : IsIdemSum e Z) :
    e ∈ GlobalTheory.FinPl.idAt D (fun p => ∃ PP ∈ Z, p = PP.under (𝓞 D.host.F)) := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := h
  exact Ideal.sum_mem _ fun PP hPP =>
    GlobalTheory.FinPl.KSplit.idAt_mono (fun w hw => ⟨PP, hPP, hw⟩) (idem_mem_idAt (hes PP hPP))

theorem mxAt_of_mem_half {S T : HSp D} {a : AE D} {P : GlobalTheory.FinPl.Pl D → Prop} (ha : a ∈ GlobalTheory.FinPl.idAt D P)
    {u : WO S T} (hu : u ∈ GlobalTheory.PlaceModel.half S T a) : GlobalTheory.FinPl.MxAt P u := by
  intro i j
  rw [← (GlobalTheory.PlaceModel.isHalf_iff S T).2 hu i j]
  exact Ideal.mul_mem_right _ _ ha

theorem isSBHalf_stepDatumQ (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D))
    (βT : GL (Fin T.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ S.rank) (χ ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (Q : Finset (Pl D.host.E)) (e : AE D) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    (he : IsIdemSum e (L.Pg ∪ Q)) :
    IsSBHalf e (latO S T ΛS ΛT fun _ => True) (fun x : WO S T =>
      if IsHalf e x ∧ IsIntM (frMapO S T βS βT x) then
        omegaG L χ (fun PP => redM PP (frMapO S T βS βT x)) * omegaQ Q L.r ξ 1 (fun PP => redM PP (frMapO S T βS βT x))
      else 0) := by
  have hinf := GlobalTheory.PlaceDatum.infPart_idemSum he
  obtain ⟨K, hK, hC⟩ := GlobalTheory.PlaceDatum.exists_nsmul_of_frMapO hS.1 hT.1 βS βT
  exact GlobalTheory.PlaceDatum.isSBHalf_of_red e _ (frMapO S T βS βT) (GlobalTheory.PlaceDatum.frMapO_add βS βT)
    (GlobalTheory.PlaceDatum.exists_den_frMapO hS.1.fg hT.1.fg βS βT)
    ⟨K, hK, fun t ht => hC t (GlobalTheory.PlaceDatum.infPart_of_half hinf ht)⟩ (L.Pg ∪ Q)
    (fun y => omegaG L χ y * omegaQ Q L.r ξ 1 y) fun y y' h => by
      rw [GlobalTheory.PlaceDatum.omegaG_congr L χ y y' fun PP hP => h PP (Finset.mem_union_left _ hP),
        GlobalTheory.PlaceDatum.omegaQ_congr Q L.r ξ 1 y y' fun PP hP => h PP (Finset.mem_union_right _ hP)]

theorem comb_add' (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (c c' : WO S T →₀ ℂ) (f : WO S T → ℂ) :
    comb ψ S T (c + c') f = comb ψ S T c f + comb ψ S T c' f := by
  rw [GlobalTheory.FinPl.DatumBack.comb_eq_lc, GlobalTheory.FinPl.DatumBack.comb_eq_lc, GlobalTheory.FinPl.DatumBack.comb_eq_lc, map_add]

theorem comb_smul' (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (a : ℂ) (c : WO S T →₀ ℂ) (f : WO S T → ℂ) :
    comb ψ S T (a • c) f = a • comb ψ S T c f := by
  rw [GlobalTheory.FinPl.DatumBack.comb_eq_lc, GlobalTheory.FinPl.DatumBack.comb_eq_lc, map_smul]

theorem comb_zero' (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (f : WO S T → ℂ) :
    comb ψ S T 0 f = 0 := by
  rw [GlobalTheory.FinPl.DatumBack.comb_eq_lc, map_zero]

theorem comb_single' (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (u : WO S T) (a : ℂ) (f : WO S T → ℂ) :
    comb ψ S T (Finsupp.single u a) f = a • heisO ψ S T u f := by
  rw [GlobalTheory.FinPl.DatumBack.comb_eq_lc, Finsupp.linearCombination_single]

theorem mem_of_mem_support_add {S T : HSp D} {H : Set (WO S T)} {c c' : WO S T →₀ ℂ} (hc : ∀ u ∈ c.support, u ∈ H)
    (hc' : ∀ u ∈ c'.support, u ∈ H) : ∀ u ∈ (c + c').support, u ∈ H := by
  intro u hu
  by_contra hn
  have h1 : c u = 0 := by
    by_contra h
    exact hn (hc u (Finsupp.mem_support_iff.2 h))
  have h2 : c' u = 0 := by
    by_contra h
    exact hn (hc' u (Finsupp.mem_support_iff.2 h))
  exact Finsupp.mem_support_iff.1 hu (by rw [Finsupp.add_apply, h1, h2, add_zero])

theorem mem_of_mem_support_smul {S T : HSp D} {H : Set (WO S T)} (a : ℂ) {c : WO S T →₀ ℂ}
    (hc : ∀ u ∈ c.support, u ∈ H) : ∀ u ∈ (a • c).support, u ∈ H := by
  intro u hu
  by_contra hn
  have h1 : c u = 0 := by
    by_contra h
    exact hn (hc u (Finsupp.mem_support_iff.2 h))
  exact Finsupp.mem_support_iff.1 hu (by rw [Finsupp.smul_apply, h1, smul_zero])

set_option maxHeartbeats 1000000 in
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Core.Rk GlobalTheory.AdForm GlobalTheory.PlaceModel GlobalTheory.PlaceDatum in

theorem exists_comb_of_isThetaAt {S T : HSp D} (ψ : AddChar (AF D.host.F) ℂ)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (e : AE D) (f₀ Φ f : WO S T → ℂ) (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    (he : e * e = e) (hec : e * cA D e = 0) (hinf : infPart D e = 0)
    (hΦ : IsSBHalf e (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) Φ)
    (hθ : IsThetaAt ψ (symplO S T) (heisO ψ S T) e
      (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) 1 f₀ Φ f) :
    ∃ d : WO S T →₀ ℂ, (∀ u ∈ d.support, u ∈ half S T (e + cA D e)) ∧ f = comb ψ S T d f₀ := by
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hθ
  rw [hall Tm hTm]
  clear hall
  have hce : cA D e * e = 0 := by rw [mul_comm, hec]
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hψ hS hT).1
  have hfin := GlobalTheory.LatFinMod.latO_finite_mod D S T _ _ hS.1.fg hT.1.fg fun _ => True
  have he' : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, he]
  have hsm : ∀ a : AE D, a * a = a → ∀ u ∈ latO S T ΛS ΛT fun _ => True,
      a • u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T a := fun a ha u hu =>
    AddSubgroup.mem_inf.2 ⟨GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ a
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, ha])) u hu, by rw [mem_half, smul_smul, ha]⟩
  have hLL' : ∀ u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e,
      ∀ y ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T (cA D e), ψ (symplO S T u y) = 1 := fun u hu y hy =>
    (hdual u (infPart_of_half hinf ((isHalf_iff S T).2 hu.2))).1 hu.1 y hy.1
  have hX : ∀ x ∈ half S T e, (∀ y ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T (cA D e), ψ (symplO S T x y) = 1) →
      x ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e := fun x hx h => by
    refine ⟨(hdual x (infPart_of_half hinf ((isHalf_iff S T).2 hx))).2 fun u hu => ?_, hx⟩
    have := h _ (hsm _ he' u hu)
    rwa [← symplO_smul, (mem_half S T).1 hx] at this
  have hfin' : ∀ k : ℕ, 0 < k → ∃ R : Set (WO S T), R.Finite ∧
      ∀ t ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e, ∃ r ∈ R,
        ∃ u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e, t = r + k • u := fun k hk => by
    obtain ⟨R, hR, h⟩ := hfin k hk
    refine ⟨(fun r => e • r) '' R, hR.image _, fun t ht => ?_⟩
    obtain ⟨r, hr, u, hu, htr⟩ := h t ht.1
    refine ⟨_, ⟨r, hr, rfl⟩, e • u, hsm e he u hu, ?_⟩
    have := (mem_half S T).1 ht.2
    rw [← this, htr, smul_add, smul_comm e k u]
  have hden : ∀ y ∈ half S T (cA D e), ∃ k : ℕ, 0 < k ∧ k • y ∈ (latO S T ΛS ΛT fun _ => True) := fun y hy =>
    exists_nsmul_mem_latO' hS.1 hT.1 y (infPart_of_half (infPart_cA hinf) ((isHalf_iff S T).2 hy))
  have tf : ∀ k : ℕ, 0 < k → Function.Injective fun t : WO S T => k • t := fun k hk a b hab => by
    rw [← inv_smul_nsmul S T hk a, ← inv_smul_nsmul S T hk b]
    exact congrArg _ hab
  have hb := isBichar_symplO S T ψ
  have hm : Φ ∈ waveSpan (fun x y : WO S T => ψ (symplO S T x y)) (half S T e) (half S T (cA D e))
      ((latO S T ΛS ΛT fun _ => True) ⊓ half S T e) := by
    obtain ⟨h1, k, hk, h2, h3⟩ := hΦ
    exact mem_waveSpan hb inf_le_right inf_le_right hLL' hX (half_div S T e) (half_div S T _) tf hfin' Φ
      (fun t ht => (isHalf_iff S T).1 (h1 t ht)) k hk (fun u hu => h2 u hu.1 ((isHalf_iff S T).2 hu.2))
      fun t ht => ⟨h3 t ht, (half S T e).nsmul_mem ((isHalf_iff S T).1 (h1 t ht)) _⟩
  clear hΦ
  induction hm using Submodule.span_induction with
  | mem _ hh =>
    obtain ⟨x, hx, y, hy, rfl⟩ := hh
    have s0 := GlobalTheory.isSBHalf_halfInd e (latO S T ΛS ΛT fun _ => True)
    have s1 : IsSBHalf e (latO S T ΛS ΛT fun _ => True)
        fun t => ψ (symplO S T t y) * halfInd e (latO S T ΛS ΛT fun _ => True) t := by
      obtain ⟨k, hk, hk'⟩ := hden y hy
      obtain ⟨a1, k', hk1, a2, a3⟩ := s0
      refine ⟨fun t ht => a1 t (right_ne_zero_of_mul ht), k * k', Nat.mul_pos hk hk1, fun u hu hh t => ?_,
        fun t ht => ?_⟩
      · have e1 : halfInd e (latO S T ΛS ΛT fun _ => True) (t + (k * k') • u) =
            halfInd e (latO S T ΛS ΛT fun _ => True) t := by
          rw [mul_nsmul]
          exact a2 _ (nsmul_mem hu k) ((isHalf_iff S T).2 (nsmul_mem ((isHalf_iff S T).1 hh) k)) t
        have e2 : ψ (symplO S T ((k * k') • u) y) = 1 := by
          rw [mul_nsmul']
          exact (hb.nsmul k _ y).trans
            (hLL' _ (nsmul_mem (AddSubgroup.mem_inf.2 ⟨hu, (isHalf_iff S T).1 hh⟩) k') _ ⟨hk', nsmul_mem hy k⟩)
        simp only [e1, symplO_add_left, AddChar.map_add_eq_mul, e2, mul_one]
      · rw [mul_nsmul']
        exact nsmul_mem (a3 t (right_ne_zero_of_mul ht)) k
    have e1 : wave (fun x y : WO S T => ψ (symplO S T x y)) ((latO S T ΛS ΛT fun _ => True) ⊓ half S T e) x y =
        fun t => (fun t => ψ (symplO S T t y) * halfInd e (latO S T ΛS ΛT fun _ => True) t) (t + x) := by
      rw [halfInd_eq_ind]; rfl
    have v1 := hTm.vac
    rw [one_smul] at v1
    rw [e1, hTm.trans _ s1 x ((isHalf_iff S T).2 hx), hTm.modul _ s0 y ((isHalf_iff S T).2 hy), v1]
    have hxy := heisL_heisL S T ψ x y f₀
    change heisO ψ S T x (heisO ψ S T y f₀) = ψ (symplOH S T x y) • heisO ψ S T (x + y) f₀ at hxy
    rw [hxy]
    refine ⟨Finsupp.single (x + y) (ψ (symplOH S T x y)), fun u hu => ?_, ?_⟩
    · rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hu)]
      exact add_mem (GlobalTheory.FinPl.DatumBack.half_le_sum hce hx) (GlobalTheory.FinPl.DatumBack.half_le_sum' hec hy)
    · rw [comb_single']
  | zero =>
    exact ⟨0, fun u hu => absurd hu (Finsupp.notMem_support_iff.2 rfl), by rw [LinearMap.map_zero, comb_zero']⟩
  | add g g' _ _ hg hg' =>
    obtain ⟨c, hc, hc'⟩ := hg
    obtain ⟨c', hd, hd'⟩ := hg'
    refine ⟨c + c', mem_of_mem_support_add hc hd, ?_⟩
    rw [LinearMap.map_add, hc', hd', comb_add']
  | smul a g _ hg =>
    obtain ⟨c, hc, hc'⟩ := hg
    refine ⟨a • c, mem_of_mem_support_smul a hc, ?_⟩
    rw [LinearMap.map_smul, hc', comb_smul']

theorem exists_comb_of_isStepVecOf : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (LS : LevDat D.host.E ℂ S.rank) (χj : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (f₀ f : WO S T → ℂ), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT LS χj Q ξ f₀ f → ∃ d : WO S T →₀ ℂ, GlobalTheory.FinPl.CombAt (fun p => ∃ PP ∈ LS.Pg ∪ Q, p = PP.under (𝓞 D.host.F)) d ∧ f = comb ψ S T d f₀ := by
  intro D ψ θ S T sS sT ΛS ΛT βS βT LS χj Q ξ f₀ f hS hT _ _ hv
  obtain ⟨hvac, e, he, hθ⟩ := hv
  have hSB := isSBHalf_stepDatumQ S T ΛS ΛT βS βT LS χj ξ Q e hS hT he
  obtain ⟨d, hd, hf⟩ := exists_comb_of_isThetaAt ψ ΛS ΛT e f₀ _ f hvac.1 hS hT
    (GlobalTheory.PlaceDatum.idemSum_mul_self he) he.2 (GlobalTheory.PlaceDatum.infPart_idemSum he) hSB hθ
  have hI := idemSum_mem_idAt he
  exact ⟨d, fun u hu => mxAt_of_mem_half (add_mem hI (GlobalTheory.LastOpPf.cA_mem_idAt hI)) (hd u hu), hf⟩

end GlobalTheory.StepComb

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentAtSplitPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_component_at_split_place : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b : ∀ j, GA D (Yc D j)) (v : VCom (commOf (pk W) u (mkGeo m b))), (commOf (pk W) u (mkGeo m b)).Is → v.τ = y.τ → v.NT = a.LT → ∀ (PP : Pl D.host.E), QAll W PP → ∀ (l : LocX a (pk W).βX PP), LocY l y v.N (pk W).βY b (fun _ _ _ => 1) → (∀ j hj, IsStdFr GlobalTheory.SymBridge.xPos (l.FX j hj)) → IsStdFr GlobalTheory.SymBridge.zPos l.FT → ∃ G : GlobalTheory.QTw.QGeo v (baseOf (pk W) (lvP W) u (mkGeo m b)) PP, (∀ j hj, IsStdFr GlobalTheory.SymBridge.xPos (G.FX j hj)) ∧ IsStdFr GlobalTheory.SymBridge.zPos G.FT ∧ G.z₀ = fun r => (ofSplit G.q).pr (a.ζ₀ r) := by
  first | exact @GlobalTheory.QGeoAt.geo_of_frames | exact GlobalTheory.QGeoAt.geo_of_frames | (intros; apply GlobalTheory.QGeoAt.geo_of_frames <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureEquation
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitAtPlaces

theorem splitAt_places : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b₀ : ∀ j, GA D (Yc D j)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v : VCom (commOf (pk W) u (mkGeo m b₀))) (o : TDat (commOf (pk W) u (mkGeo m b₀)) k ι) (l : ∀ PP, PP ∈ (pk W).Pg ∨ QAll W PP → LocX a (pk W).βX PP) (bas : ∀ PP h j c, j + c = (l PP h).s + 1 → GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c) (l PP h).k), (commOf (pk W) u (mkGeo m b₀)).Is → y.Tau (-D.host.xi0 ^ (D.R.m / 2)) → star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = (((D.mem u).A.T : ℕ) : D.host.E) → v.τ = y.τ → v.NT = a.LT → o.ζ₀ = a.ζ₀ → IsSelfDualC D.sp.X' a.LT → (∀ p, p ∈ v.gP ↔ ∃ PP ∈ (pk W).Pg, p = PP.under (𝓞 D.host.F)) → (∀ p, p ∈ v.tP ↔ (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal) → Disjoint v.gP v.tP → PreT v o → (∀ n (h : n = D.R.m) x, x ∉ v.tP → ∃ LZ : GlobalTheory.FinPl.Lat a.Lz, IsSelfDualC _ LZ ∧ GlobalTheory.FinPl.OrthAt (a.oT n h) (a.x n).L a.LT LZ x) → (∀ PP h, PP ∉ (pk W).Pg → ∀ j c hc, bas PP h j c hc = 1) → ∀ (FY : ∀ PP h, FYFam (l PP h)) (sc : ∀ PP h, ℕ → (l PP h).k), (∀ PP h, IsNormalFr (l PP h) y (FY PP h) (sc PP h)) → ∀ (N₁ : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)) (M₁ : ∀ j ρ h, GlobalTheory.FinPl.Lat (y.bes j ρ h).V₀), (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (N₁ j)) → (∀ PP h j c hc, IntIn (l PP h).q (Yc D j) (FY PP h j c hc) (N₁ j)) → (∀ j ρ h, IsSelfDualC (y.bes j ρ h).V₀ (M₁ j ρ h)) → (∀ PP hP j ρ h (hj : j ≤ (l PP hP).s + 1) (F₀ : Frame (l PP hP).k ((y.bes j ρ h).lev (a.x j).vol).V₀.rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Unit)), (ofSplit (l PP hP).q).IsCoreFrame ((y.bes j ρ h).lev (a.x j).vol) (sc PP hP j) ((l PP hP).FX j hj) F₀ → IntIn (l PP hP).q _ F₀ (M₁ j ρ h)) → ∀ PP (hP : PP ∈ (pk W).Pg ∨ QAll W PP), SplitAt { v with N := N₁ } { o with M := M₁ } (PP.under (𝓞 D.host.F)) := by
  intro D L hT Gi Gl Kc Yd cX ex W u hW a y m b₀ k _ _ _ _ ι v o l bas hIs hTau hz hvτ hNT hoζ hsdT hgP htP hdisj hpre hLZ hbas FY sc hFY N₁ M₁ hN₁ hFYN hM₁ hcore PP hP
  have hq : (l PP hP).q.v = PP.under (𝓞 D.host.F) := (l PP hP).under
  obtain ⟨hsc, hstep, hhz, -, -, hτ⟩ := hFY PP hP
  have hξ : valuation (l PP hP).k (ofSplit (l PP hP).q).xi = 1 := by
    have h1 := hsc (0 + 1 + 1)
    rw [hstep 0, map_mul, hsc 0, one_mul] at h1
    exact h1
  have hxi : (ofSplit (l PP hP).q).xi ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hξ
    exact zero_ne_one hξ

  have key : ∀ j ρ (h : j + 2 * ρ + 2 = D.R.m), ∃ LL : GlobalTheory.FinPl.Lat (y.bes j ρ h).L, IsSelfDualC _ LL ∧
      GlobalTheory.FinPl.OrthAt (y.bes j ρ h).o (M₁ j ρ h) (a.x j).L LL (l PP hP).q.v ∧
      ∀ t : (l PP hP).k, (t ∈ 𝒪[(l PP hP).k] ↔ (fun i => (l PP hP).q.sec
        ((fun i => sc PP hP j * (ofSplit (l PP hP).q).pr ((y.bes j ρ h).ζ i)) i * t)) ∈ GlobalTheory.FinPl.latV _ LL (· = (l PP hP).q.v)) := by
    intro j ρ h
    have hj : j ≤ (l PP hP).s + 1 := by have := (l PP hP).hs; omega
    have hs0 : sc PP hP j ≠ 0 := by
      intro h0
      have h1 := hsc j
      rw [h0, map_zero] at h1
      exact zero_ne_one h1
    obtain ⟨F₀, hF₀⟩ := ((GlobalTheory.T.exists_normal_frames_and_base_point_split_place D (l PP hP).k (ofSplit (l PP hP).q) hxi).1 _ ρ ((y.bes j ρ h).lev (a.x j).vol)
      (sc PP hP j) ((l PP hP).FX j hj) hs0).1
    have hIntM := hcore PP hP j ρ h hj F₀ hF₀
    have hA : IsSelfDualC (D.sp.X j) (a.x j).L := (hIs.x j (by omega)).sd
    refine GlobalTheory.T.exists_selfDualLineLattice_splitting_sum D (l PP hP).k (l PP hP).q (y.bes j ρ h).V₀ (D.sp.X j) (y.bes j ρ h).L (y.bes j ρ h).o (M₁ j ρ h)
      (a.x j).L _ ((l PP hP).FX j hj) F₀ _ (hM₁ j ρ h) hA ⟨_, GlobalTheory.LineSelfDual.isSelfDualC_selfDualLatticeCoordsInFrame D _⟩ hF₀.1 (fun r => ?_)
      hIntM ((l PP hP).latX j hj)
    rw [hF₀.2 r]
    simp only [GlobalTheory.MixPer.vecB, Matrix.mulVec, dotProduct, Matrix.map_apply, GlobalTheory.LocMod.Place.pr, map_sum, map_mul,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hx : PP.under (𝓞 D.host.F) ∉ v.tP := by
    rcases hP with hP' | hP'
    · intro ht
      exact Finset.disjoint_left.1 hdisj ((hgP _).2 ⟨PP, hP', rfl⟩) ht
    · exact GlobalTheory.tuplePlace_under_not_mem_tP W u hW a y m b₀ k ι v o l bas hIs hTau hz hvτ hNT hoζ hsdT hgP htP hdisj hpre hLZ
        hbas FY sc hFY PP hP'
  refine ⟨fun j ρ h => ?_, fun j h => ?_⟩
  · obtain ⟨LL, hLL, hO, -⟩ := key j ρ h
    exact ⟨LL, hLL, hq ▸ hO⟩
  · have hjs : j = (l PP hP).s := by have := (l PP hP).hs; omega
    subst hjs
    obtain ⟨LL, hLL, hO, hLLw⟩ := key _ 0 h
    obtain ⟨LZ₀, hLZ₀, -⟩ := hLZ _ h (l PP hP).q.v (hq ▸ hx)
    obtain ⟨LZ, hLZsd, hLZO, hLZw⟩ := GlobalTheory.T.exists_selfDualLineLattice_splitting_sum D (l PP hP).k (l PP hP).q (D.sp.X ((l PP hP).s + 1 + 1)) D.sp.X' a.Lz
      (a.oT _ h) (a.x ((l PP hP).s + 1 + 1)).L a.LT _ (l PP hP).FT (l PP hP).FM
      (fun i => (ofSplit (l PP hP).q).pr (a.ζ₀ i)) (hIs.x _ (by omega)).sd hsdT ⟨LZ₀, hLZ₀⟩
      (fun r b => by rw [(l PP hP).last]; rfl) (fun r => by rw [(l PP hP).last]; rfl) (l PP hP).latM (l PP hP).latT
    refine ⟨LL, LZ, hLL, hLZsd, hq ▸ hO, hNT ▸ hq ▸ hLZO, ?_⟩
    intro w hw
    rw [← hq] at hw ⊢
    rw [hvτ]
    have hmap := GlobalTheory.T.splitPlace_line_similitude_maps_selfDual_lattice D (l PP hP).k (l PP hP).q (y.bes _ 0 h).L a.Lz (y.τ _ h) LL LZ _ _ (-(ofSplit (l PP hP).q).xi)
      (l PP hP).unit hLL hLZsd (y.bes _ 0 h).line.1 hpre.line.1 hLLw hLZw (by rw [Valuation.map_neg]; exact hξ)
      (by rw [hτ h]; funext i; simp only [Pi.smul_apply, smul_eq_mul]; ring) (hTau _ h).1
    exact GlobalTheory.T.lineHomAdjointTwist_mem_completedHomLattice D (l PP hP).k (l PP hP).q (D.sp.X ((l PP hP).s + 1)) (y.bes _ 0 h).L a.Lz (y.τ _ h)
      (a.x ((l PP hP).s + 1)).L LL LZ (l PP hP).unit (hIs.x _ (by omega)).sd hLL hLZsd hmap w hw

end GlobalTheory.SplitAtPlaces
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticesConjugateAtFinitePlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDualLattices_conjugate_at_finitePlace : ∀ (D : D7) (V : HSp D) (L M : Lat V), IsSelfDualC V L → IsSelfDualC V M → ∀ x : Pl D, ∃ g ∈ grpAt V (· = x), Moves V g L M (· = x) := by
  first | exact @GlobalTheory.FinPl.SelfDualConj.conj_at_place | exact GlobalTheory.FinPl.SelfDualConj.conj_at_place | (intros; apply GlobalTheory.FinPl.SelfDualConj.conj_at_place <;> assumption)
end

