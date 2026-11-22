import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0398
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0033
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0358
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0399
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0365
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0405
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0390
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CenterAdelicUnitaryGroupFinitePartScalar
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0168
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0197
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0392
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalFrameHermitianIdeal
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LatNotSelfDual
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0163
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0747
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0415
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.AlternatingFormStandardHermitian
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThCLeftStab
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0401
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelsOverOfFamily
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0404

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ArchimedeanLevelVolumeMulRelIndexStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanLevelVolume_mul_relIndex : ∀ (D : D7) (V : HSp D) (v : GlobalTheory.Unf.Vol V) (U U' : Subgroup (GA D V)), U ≤ U' → U' ≤ GfC V → IsCompact (U' : Set (GA D V)) → IsOpen ((U.subgroupOf (GfC V) : Subgroup (GfC V)) : Set (GfC V)) → volLev v U * (U.relIndex U' : ℝ) = volLev v U' := by
  first | exact @GlobalTheory.LevVol.volLev_mul_relIndex | exact GlobalTheory.LevVol.volLev_mul_relIndex | (intros; apply GlobalTheory.LevVol.volLev_mul_relIndex <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseChainStepThetaLift
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.BaseChain.thetaKO_sum_smul_act {D : D7} {S T : HSp D} {ι : Type} (s : Finset ι) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
    (g : GA D S) (h : GA D T) (c : ι → ℂ) (κ : ι → GA D S) (f : WO S T → ℂ) :
    thetaKO om g h (∑ p ∈ s, c p • om (κ p, 1) f) = ∑ p ∈ s, c p * thetaKO om (g * κ p) h f := by
  simp only [thetaKO, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  congr 1
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.BaseChain.stepY_integrable_and_eq {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (hW : PkHyp W) (t) (j) (hj : j + 1 < D.R.m) (F : CP (pk W) (lvP W) t (j + 1)) (hF : F.1 ∈ (pk W).CC t (j + 1)) (v) (hv : IsStepVecOf (pk W).ψ (pk W).θ (Yc D j) (Yc D (j + 1)) (cart ((pk W).MY j)) (cart ((pk W).MY (j + 1))) ((pk W).ΛY j) ((pk W).ΛY (j + 1)) ((pk W).βY j) ((pk W).βY (j + 1)) ((pk W).datYt t j (lvP W)) ((pk W).chi (j + 1)) ((pk W).Q t) ((pk W).xiR t) ((pk W).vac j) v) (Q x g) :
  IntegrableOn (fun h => thetaKO ((pk W).ωY t j) g h (pureTensorO (pk W).ψ (pk W).θ (Yc D j) (Yc D (j + 1)) (cart ((pk W).MY j)) (cart ((pk W).MY (j + 1))) (onb ((pk W).MY j)) (onb ((pk W).MY (j + 1))) v Q) * F.1 x h) ((pk W).fdY t (j + 1)) ((pk W).νY t (j + 1)) ∧
  (∫ y in (pk W).fdY t (j + 1), thetaKO ((pk W).ωY t j) g y (pureTensorO (pk W).ψ (pk W).θ (Yc D j) (Yc D (j + 1)) (cart ((pk W).MY j)) (cart ((pk W).MY (j + 1))) (onb ((pk W).MY j)) (onb ((pk W).MY (j + 1))) v Q) * F.1 x y ∂((pk W).νY t (j + 1))) = (Nat.card (lvP W).H : ℂ) * ((pk W).ioY t j ⟨F.1, hF⟩).1 ((pk W).ItY j Q x) g := by
  have hio : Lift.IsIo ((pk W).νY t (j + 1)) ((pk W).fdY t (j + 1)) (thetaKO ((pk W).ωY t j)) ((pk W).ptY t j)
      ((pk W).ItY j) ((pk W).CC t (j + 1)) ((pk W).CC t j) ((pk W).ioY t j) :=
    hW.bot.hyp.2.2.2.1.chain.ioY t j (by omega)
  have hfin : ∀ PP : (pk W).Pg, Finite (kP PP.1) := fun PP => Ideal.finiteQuotientOfFreeOfNeBot _ PP.1.ne_bot
  haveI : Fintype (lvP W).H := Fintype.ofFinite _
  obtain ⟨κ, hκ, hsum⟩ := GlobalTheory.T.exists_level_elements_step_vector W hW t j hj
  rw [hsum v hv Q]
  simp_rw [GlobalTheory.BaseChain.thetaKO_sum_smul_act]
  have hint : ∀ p ∈ (Finset.univ : Finset (lvP W).H), IntegrableOn (fun h => (levChi (Yc D j) ((pk W).βY j) ((pk W).datYt t j (lvP W)) (κ p))⁻¹ * thetaKO ((pk W).ωY t j) (g * κ p) h ((pk W).ptY t j Q) * F.1 x h) ((pk W).fdY t (j + 1)) ((pk W).νY t (j + 1)) := by
    intro p _
    simp_rw [mul_assoc]
    exact (hio.integ ⟨F.1, hF⟩ Q x (g * κ p)).const_mul _
  simp_rw [Finset.sum_mul]
  refine ⟨integrable_finset_sum _ hint, ?_⟩
  rw [integral_finset_sum _ hint]
  have e : ∀ p ∈ (Finset.univ : Finset (lvP W).H), ∫ h in (pk W).fdY t (j + 1), (levChi (Yc D j) ((pk W).βY j) ((pk W).datYt t j (lvP W)) (κ p))⁻¹ * thetaKO ((pk W).ωY t j) (g * κ p) h ((pk W).ptY t j Q) * F.1 x h ∂(pk W).νY t (j + 1) =
      ((pk W).ioY t j ⟨F.1, hF⟩).1 ((pk W).ItY j Q x) g := by
    intro p _
    simp_rw [mul_assoc]
    rw [integral_const_mul]
    have h1 := hio.eq ⟨F.1, hF⟩ Q x (g * κ p)
    simp only [Lift.liftInt] at h1
    rw [h1, GlobalTheory.T.chain_projection_level_character W hW t j hj ⟨F.1, hF⟩ F.2 (κ p) (hκ p) Q x g]
    rw [← mul_assoc, inv_mul_cancel₀ (Lev.levChi_ne_zero (V := Yc D j) (β := (pk W).βY j) ((pk W).datYt t j (lvP W)) (κ p)), one_mul]
  rw [Finset.sum_congr rfl e, Finset.sum_const, Finset.card_univ]
  simp only [Nat.card_eq_fintype_card, nsmul_eq_mul]

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.BaseChain.stepY_isIo : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word) (f : FamCh W u), PkHyp W → f.RowOK → ∀ j, j + 1 < D.R.m → Lift.IsIo (GlobalTheory.BaseChain.stageY W (j + 1)).ν (GlobalTheory.BaseChain.stageY W (j + 1)).fd (thetaKO (GlobalTheory.BaseChain.stepY f j).ω) (GlobalTheory.BaseChain.stepY f j).pt (GlobalTheory.BaseChain.stepY f j).It ((GlobalTheory.BaseChain.stageY W (j + 1)).CC (GlobalTheory.BaseChain.com W)) ((GlobalTheory.BaseChain.stageY W j).CC (GlobalTheory.BaseChain.com W)) (GlobalTheory.BaseChain.stepY f j).io := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hW hf j hj
  have hrow := hf.row W.P.A3.A.μ0
  have hfin : ∀ PP : (pk W).Pg, Finite (kP PP.1) := fun PP => Ideal.finiteQuotientOfFreeOfNeBot _ PP.1.ne_bot
  have hc : Nat.card (lvP W).H ≠ 0 := Nat.card_pos.ne'
  have hne : GlobalTheory.BaseChain.cH W ≠ ⊤ := ENNReal.inv_ne_top.2 (Nat.cast_ne_zero.2 hc)
  refine ⟨fun F φ v g => ?_, fun F φ v g => ?_⟩
  · obtain ⟨h, hio⟩ := hrow.io j hj F
    have hI := (GlobalTheory.BaseChain.stepY_integrable_and_eq W hW W.P.A3.A.μ0 j hj F h _ (hrow.vP j hj) φ v g).1.smul_measure hne
    rw [← Measure.restrict_smul] at hI
    exact hI
  · obtain ⟨h, hio⟩ := hrow.io j hj F
    have e := (GlobalTheory.BaseChain.stepY_integrable_and_eq W hW W.P.A3.A.μ0 j hj F h _ (hrow.vP j hj) φ v g).2
    have hk : (GlobalTheory.BaseChain.cH W).toReal • (Nat.card (lvP W).H : ℂ) = 1 := by
      rw [Complex.real_smul, GlobalTheory.BaseChain.cH, ENNReal.toReal_inv, ENNReal.toReal_natCast, Complex.ofReal_inv, Complex.ofReal_natCast,
        inv_mul_cancel₀ (Nat.cast_ne_zero.2 hc)]
    show (∫ y in (pk W).fdY W.P.A3.A.μ0 (j + 1), thetaKO ((pk W).ωY W.P.A3.A.μ0 j) g y (pureTensorO (pk W).ψ (pk W).θ (Yc D j) (Yc D (j + 1)) (cart ((pk W).MY j)) (cart ((pk W).MY (j + 1))) (onb ((pk W).MY j)) (onb ((pk W).MY (j + 1))) ((f.row W.P.A3.A.μ0).vP j) φ) * F.1 v y ∂(GlobalTheory.BaseChain.cH W • (pk W).νY W.P.A3.A.μ0 (j + 1))) = ((f.row W.P.A3.A.μ0).io j F).1 ((pk W).ItY j φ v) g
    rw [hio, Measure.restrict_smul, integral_smul_measure]
    exact (congrArg (fun z => (GlobalTheory.BaseChain.cH W).toReal • z) e).trans (by rw [← smul_mul_assoc, hk, one_mul])
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseChartDecorationLevelPrimeFunctionalEqConjMul
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PhiOneVal

namespace GlobalTheory.PhiOneVal

theorem base_deco_fn : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι)
    (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ i, i ≤ B.R.m → ∀ (β : Ch i) (P : (B.primes X).vT u)
    (x : Formalism.L2.Col.Sp B.fields.E (B.R.N i)), x ∈ Formalism.L2.Col.stdLat B.fields.E (B.R.N i) → ∀ r : Fin (B.R.N i), r.1 + 1 = B.R.N i →
    ∀ c : 𝓞 B.fields.E, algebraMap (𝓞 B.fields.E) B.fields.E c = x r →
      (A.p0 i β).1.1.deco.1.f P x = Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO (X.piT u) * c) := by
  intro B X I l Z u a Ch A hA i hi β P x hx r hr c hc
  choose y hy using (Formalism.L2.Col.mem_stdLat x).1 hx
  have hxy : x = fun j => (y j : B.fields.E) := funext fun j => (hy j).symm
  have hyc : y r = c := NumberField.RingOfIntegers.coe_injective ((hy r).trans hc.symm)
  rw [hxy, ← hyc]
  exact GlobalTheory.BaseFn.fn_eq (hA.base i hi β).1 (hA.base i hi β).2 P r hr _ (fun j => (hA.reads i hi).k_T β P r j hr) y

end GlobalTheory.PhiOneVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLevelLineVectorPrimitiveRowLatticeNormStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselLevelLineVector_primitive_rowLattice_norm : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (μ lam : D.host.E), GlobalTheory.Core.Mi.IdE X → B.FrameAt μ lam → (∀ t : D.host.E, t • vecB B.o B.ζ ∈ coreLat B.d (latS D) ↔ μ * t ∈ (1 : FI D)) ∧ star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ = -(μ * star μ * (((D.mem u).A.T : ℕ) : D.host.E)) ∧ vecB B.o B.ζ ≠ 0 := by
  first | exact @GlobalTheory.Core.Mi.LatMatch.sz_tied | exact GlobalTheory.Core.Mi.LatMatch.sz_tied | (intros; apply GlobalTheory.Core.Mi.LatMatch.sz_tied <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselUnfoldingOrbitMemParabolicMulStabiliserStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselUnfolding_orbit_mem_parabolic_mul_stabiliser : ∀ (D : D7) (σ : ℕ) (B : BesLev D σ) (L : Lat B.V) (L₀ : Lat B.V₀) (v : Pl D), MonoAt B.d L L₀ v → ∀ n ∈ flagN B.d, n ∈ grpAt B.V (· = v) → ∀ a ∈ grpAt B.A (· = v), ∀ κ₀, InK B.V₀ L₀ (· = v) κ₀ → ∀ κ, InK B.V L (· = v) κ → ∃ r ∈ besGrp B.d B.o, r ∈ grpAt B.V (· = v) ∧ ∃ κ', InK B.V L (· = v) κ' ∧ n * B.d.emb0 (B.o.emb (a, 1) * κ₀) * κ = r * κ' := by
  first | exact @GlobalTheory.FinPl.OrbitCoset.orbit_coset | exact GlobalTheory.FinPl.OrbitCoset.orbit_coset | (intros; apply GlobalTheory.FinPl.OrbitCoset.orbit_coset <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CenterAdelicUnitaryGroupFinitePartScalarStatement
section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.center_adelicUnitaryGroup_finitePart_scalar : ∀ {D : D7} (V : Formalism.BasicNotions.TH.HSp D) (z : GA D V), z ∈ Subgroup.center (GA D V) → z ∈ GfC V → ∃ c : Formalism.IndefR.Lev.EAf D, (Formalism.IndefR.Lev.finE V z).val = c • (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) := by
  first | exact @GlobalTheory.CentreScalar.finE_center_scalar | exact GlobalTheory.CentreScalar.finE_center_scalar | (intros; apply GlobalTheory.CentreScalar.finE_center_scalar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CenterAdelicUnitaryGroupScalarAtFinitePlaceStatement
section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.center_adelicUnitaryGroup_scalar_at_finitePlace : ∀ (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (z : GA D V), z ∈ Subgroup.center (GA D V) → ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), ∃ ζ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E, (GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) D.sp.cm.sig V.gram (GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v z)).val = ζ • (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E)) := by
  first | exact @GlobalTheory.UnitaryCentreLoc.scalar_at_finite_place | exact GlobalTheory.UnitaryCentreLoc.scalar_at_finite_place | (intros; apply GlobalTheory.UnitaryCentreLoc.scalar_at_finite_place <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CenterLocalUnitaryGroupFinitePlaceScalarStatement
section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.center_localUnitaryGroup_finitePlace_scalar : ∀ (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F)) (g : GlobalTheory.AdelicU.GLoc D.sp.cm.sig V.gram v), g ∈ Subgroup.center (GlobalTheory.AdelicU.GLoc D.sp.cm.sig V.gram v) → ∃ c : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E, (GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) D.sp.cm.sig V.gram g).1 = c • (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E)) := by
  first | exact @GlobalTheory.CenterLocU.center_scalar_loc | exact GlobalTheory.CenterLocU.center_scalar_loc | (intros; apply GlobalTheory.CenterLocU.center_scalar_loc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CharacterUnramifiedAwayLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MuUnrOff

theorem mu_charUnramAt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → ∀ (t : W.P.T) (n : ℕ) (x : HeightOneSpectrum (𝓞 D.host.F)), 1 ≤ n → n ≤ D.R.m → (∀ PP ∈ (pk W).Pg, PP.under (𝓞 D.host.F) ≠ x) → (∀ PP ∈ (pk W).Q t, PP.under (𝓞 D.host.F) ≠ x) → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D ((pk W).toLevCh.mu t n) x := by
  intro D L hT Gi Gl Kc Yd cX ex W hP t n x h1 h2 hPg hQ
  have hL := hP.bot.hyp.2.2.2.1.lev
  refine GlobalTheory.SeeSaw.LevelTest.charUnramAt_of fun w hw => ?_
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  have hj : j < D.R.m := by omega
  show GlobalTheory.LFun.UnrAt ((pk W).toLevCh.mu0 (j + 1) * (pk W).toLevCh.xi t) w
  refine GlobalTheory.LFun.UnrAt.mul ?_ ?_
  · refine (GlobalTheory.LFun.unrAt_iff_of_chrEq (hL.mu0 ⟨j, hj⟩) w).2 (((pk W).toLevCh.C.isMu0 ⟨j, hj⟩).unr w fun k hk => ?_)
    rcases GlobalTheory.ConjOverQuad.div_or_conj_div D (pk W).toLevCh.C.P k w hk with h | ⟨w', h, hc⟩
    · exact hPg w ((hL.Pg w).2 ⟨k, h⟩) hw
    · refine hPg w' ((hL.Pg w').2 ⟨k, h⟩) (Eq.trans ?_ hw)
      ext a
      show algebraMap _ _ a ∈ w'.asIdeal ↔ algebraMap _ _ a ∈ w.asIdeal
      rw [hc, Formalism.L2.Col.mem_conjIdeal]
      have : Formalism.L2.Col.cO D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) = algebraMap _ _ a := by
        apply RingOfIntegers.ext
        exact (D.sp.cm.fixed _).2 ⟨a, rfl⟩
      rw [this]
  · refine (GlobalTheory.LFun.unrAt_iff_of_chrEq (hL.xi t) w).2 ?_
    by_contra hu
    rcases (hL.Q_ram t w).1 hu with h | ⟨P', hP', hc⟩
    · exact hQ w h hw
    · exact hQ P' hP' ((GlobalTheory.LevelPlaces.under_eq_of_isConjPl hc).trans hw)

end GlobalTheory.MuUnrOff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CocRZeroLeft
section
open NumberField IsDedekindDomain Formalism.L2.Ker

noncomputable section

namespace GlobalTheory.SemiTwist

variable {E : Type} [Field E] [NumberField E] [StarRing E] {ι : Type} [Fintype ι] {a b : ℕ}
  (emb : ι → E →+* ℂ) (δ : ℂ) (d : ℕ) (sc : ℝ)

def cocR (x y : Formalism.L2.Col.HomE E a b) : ℝ :=
  (Real.sqrt d * (HV (ι := ι) sc (embH emb δ x) (embH emb δ y)).re +
    Formalism.L2.Th1.H.altE (HV sc) (embH emb δ x) (embH emb δ y)) / 2

theorem cocR_add_left (x y z : Formalism.L2.Col.HomE E a b) :
    cocR emb δ d sc (x + y) z = cocR (ι := ι) emb δ d sc x z + cocR emb δ d sc y z := by
  simp only [cocR, Formalism.L2.Th1.H.altE, map_add, LinearMap.add_apply, Complex.add_re, Complex.add_im]; ring

theorem cocR_zero_left (z : Formalism.L2.Col.HomE E a b) : cocR (ι := ι) emb δ d sc 0 z = 0 := by
  simp [cocR, Formalism.L2.Th1.H.altE]

theorem hv_embH_smul (hconj : ∀ τ x, emb τ (star x) = starRingEnd ℂ (emb τ x)) (r : E) (x y : Formalism.L2.Col.HomE E a b) :
    HV (ι := ι) sc (embH emb δ (r • x)) (embH emb δ y) = HV sc (embH emb δ x) (embH emb δ (star r • y)) := by
  simp only [HV, LinearMap.mk₂'ₛₗ_apply, embH, AddMonoidHom.coe_mk, ZeroHom.coe_mk, LinearMap.smul_apply, Pi.smul_apply,
    smul_eq_mul, map_mul, hconj, Complex.conj_conj]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem cocR_smul (hconj : ∀ τ x, emb τ (star x) = starRingEnd ℂ (emb τ x)) (r : E) (x y : Formalism.L2.Col.HomE E a b) :
    cocR (ι := ι) emb δ d sc (r • x) y = cocR emb δ d sc x (star r • y) := by
  simp only [cocR, Formalism.L2.Th1.H.altE, hv_embH_smul emb δ sc hconj]

theorem semiChar_twO : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (ι : Type) [Fintype ι] [Nonempty ι] (a b : ℕ) (emb : ι → E →+* ℂ) (δ : ℂ) (d : ℕ) (sc : ℝ) (M : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b)) (c : ℕ) (e : HeightOneSpectrum (𝓞 E) → ℤ), δ ≠ 0 → (∀ (τ : ι) (x : E), emb τ (star x) = starRingEnd ℂ (emb τ x)) → 0 < c → (∀ Q, e (Formalism.L2.Col.conjPrime₂ Q) = -e Q) → (∀ Q, e Q = 1 ∨ e Q = 0 ∨ e Q = -1) → Formalism.L2.Th1.H.IsSelfDual (HV sc) (laV emb δ M) → Formalism.L2.Th1.H.IsSemiChar (HV sc) (laV emb δ M) (alV d sc) → Formalism.L2.Th1.H.IsSemiChar (HV sc) (laV emb δ (twist₂ M c e)) (alV d sc) := by
  intro E _ _ _ ι _ _ a b emb δ d sc M c e _ hconj hc he _ _ hM
  have hH : Formalism.L2.Th1.H.IsHerm (HV (ι := ι) (a := a) (b := b) sc) := fun x y => by
    simp [Formalism.L2.Ker.HV, map_sum, mul_comm]
  have h0 : ∀ x ∈ M, ∀ y ∈ M, ∃ n : ℤ, cocR emb δ d sc x y = n := fun x hx y hy =>
    (GlobalTheory.KerLaw.semi_iff hH (Real.sqrt d) _).1 hM (embH emb δ x) ⟨x, hx, rfl⟩ (embH emb δ y) ⟨y, hy, rfl⟩
  refine (GlobalTheory.KerLaw.semi_iff hH (Real.sqrt d) _).2 ?_
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  change ∃ n : ℤ, cocR emb δ d sc x y = n
  let I : Ideal (𝓞 E) :=
    { carrier := {r | ∀ s : 𝓞 E, ∃ n : ℤ, cocR emb δ d sc ((s * r) • x) y = n}
      zero_mem' := fun s => ⟨0, by simp [cocR_zero_left]⟩
      add_mem' := fun {r r'} hr hr' s => by
        obtain ⟨n, hn⟩ := hr s
        obtain ⟨m, hm⟩ := hr' s
        exact ⟨n + m, by rw [mul_add, add_smul, cocR_add_left, hn, hm, Int.cast_add]⟩
      smul_mem' := fun t r hr s => by
        rw [smul_eq_mul, ← mul_assoc]
        exact hr _ }
  have hI : I = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    let Q : HeightOneSpectrum (𝓞 E) :=
      ⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField E)⟩
    obtain ⟨u, hu, hx⟩ := (Formalism.L2.Col.mem_locP _ _ _).1 ((GlobalTheory.KerLaw.mem_tw _ _ _ _).1 hx Q)
    obtain ⟨v, hv, hy⟩ := (Formalism.L2.Col.mem_locP _ _ _).1 ((GlobalTheory.KerLaw.mem_tw _ _ _ _).1 hy (Formalism.L2.Col.conjPrime₂ Q))
    rw [he, zpow_neg, inv_inv] at hy
    have hmem : u * Formalism.L2.Col.cO E v ∈ I := by
      intro s
      obtain ⟨n, hn⟩ := h0 _ (Submodule.smul_mem _ s hx) _ hy
      refine ⟨n, ?_⟩
      rw [← hn]
      have e1 : (s * (u * Formalism.L2.Col.cO E v)) • x =
          (star (algebraMap (𝓞 E) E v) * (c : E) ^ e Q) • (s • u • ((c : E) ^ e Q)⁻¹ • x) := by
        rw [← algebraMap_smul E s, ← algebraMap_smul E u, ← algebraMap_smul E (s * _), smul_smul, smul_smul, smul_smul,
          map_mul, map_mul, Formalism.L2.Col.algebraMap_cO]
        congr 1
        have hk : (c : E) ^ e Q ≠ 0 := zpow_ne_zero _ (Nat.cast_ne_zero.2 hc.ne')
        field_simp
      rw [e1, cocR_smul emb δ d sc hconj, star_mul', star_star, star_zpow₀, star_natCast, mul_smul, algebraMap_smul]
    rcases hm.isPrime.mem_or_mem (hle hmem) with h' | h'
    · exact hu h'
    · exact hv h'
  have : (1 : 𝓞 E) ∈ I := hI ▸ Submodule.mem_top
  simpa using this 1

end GlobalTheory.SemiTwist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CoeffAtNegOneZetaOfEisCoeffAt
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

open Filter Topology Set Metric GlobalTheory.Eis

namespace GlobalTheory.Eis.Residue

theorem isExtAt_sub (a s₀ : ℂ) : IsExtAt (fun s : ℂ => s - a) s₀ fun s => s - a :=
  (isMerExt_self isRightDomain_univ fun s _ => (MeromorphicAt.id s).sub (MeromorphicAt.const a s)).isExtAt trivial

theorem coeffAt_neg_one_of_holValueAt {h : ℂ → ℂ} {a c : ℂ} (hv : HolValueAt (fun s => (s - a) * h s) a c) :
    CoeffAt h a (-1) c := by
  obtain ⟨H, hx, han, hH⟩ := hv
  have hx' : IsExtAt h a fun s => H s / (s - a) := by
    refine (hx.div (isExtAt_sub a a)).congr ⟨a.re, fun s hs => ?_⟩
    have : s - a ≠ 0 := sub_ne_zero.2 (by rintro rfl; exact lt_irrefl _ (mem_rightOf.1 hs))
    simp only
    field_simp
  have t : Tendsto (fun s => (s - a) ^ (1 : ℕ) * (H s / (s - a))) (𝓝[≠] a) (𝓝 c) := by
    refine (hH ▸ han.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have : s - a ≠ 0 := sub_ne_zero.2 hs
    field_simp
  simpa using hx'.coeffAt_of_tendsto t

theorem cont_sub_mul {h : ℂ → ℂ} (hc : Continues h) (a s : ℂ) (hs : ContinuousAt (cont h) s) :
    cont (fun t => (t - a) * h t) s = (s - a) * cont h s := by
  obtain ⟨E, hE⟩ := hc
  have hx := hE.isExtAt (s₀ := s) trivial
  have hv : HolValueAt h s (cont h s) :=
    hx.holValueAt_iff.2 ((hs.tendsto.mono_left nhdsWithin_le_nhds).congr' hx.cont_eventuallyEq)
  have hl : HolValueAt (fun t : ℂ => t - a) s (s - a) := ⟨_, isExtAt_sub a s, by fun_prop, rfl⟩
  exact (hl.mul hv).valueAt.cont_eq

variable {D : D7} {V : HSp D} {Φ : ℂ → GA D (dblSp V) → ℂ}

theorem eisSer_sub_smul (s₀ : ℂ) (g : GA D (dblSp V)) :
    eisSer V ((fun s => s - s₀) • Φ) g = fun s => (s - s₀) * eisSer V Φ g s := by
  funext s
  show eis V ((s - s₀) • Φ s) g = _
  rw [eis_smul]; rfl

theorem isZetaFamily_sub_smul {μ : (AE D)ˣ →* Circle} {m : Measure (GA D V)} {f₁ f₂ : GA D V → ℂ}
    (hZ : IsZetaFamily V μ m Φ f₁ f₂) (s₀ : ℂ) : IsZetaFamily V μ m ((fun s => s - s₀) • Φ) f₁ f₂ := by
  refine ⟨hZ.1.smul _, fun s hs => ?_⟩
  obtain ⟨hl, hi⟩ := hZ.2 s hs
  have e1 : eis V (((fun s => s - s₀) • Φ) s) = (s - s₀) • eis V (Φ s) := eis_smul _ _
  have e2 : dblIntegrand V μ ((s - s₀) • eis V (Φ s)) f₁ f₂ = fun q => (s - s₀) * dblIntegrand V μ (eis V (Φ s)) f₁ f₂ q :=
    funext fun q => by simp only [dblIntegrand, Pi.smul_apply, smul_eq_mul]; ring
  have e3 : dblIntegrandQ V μ ((s - s₀) • eis V (Φ s)) f₁ f₂ =
      fun q => (s - s₀) * dblIntegrandQ V μ (eis V (Φ s)) f₁ f₂ q :=
    funext fun q => by simp only [dblIntegrandQ, e2]
  rw [e1]
  refine ⟨fun γ hγ g => ?_, ?_⟩
  · rw [e2]; exact congrArg _ (hl γ hγ g)
  · rw [e3]; exact hi.const_mul _

theorem eisContinues_sub_smul (hE : EisContinues V Φ) (s₀ : ℂ) : EisContinues V ((fun s => s - s₀) • Φ) := by
  refine ⟨hE.1.smul _, fun g => ?_⟩
  obtain ⟨E, hE'⟩ := hE.2 g
  rw [eisSer_sub_smul]
  exact ⟨fun s => (s - s₀) * E s, isRightDomain_univ,
    fun s _ => ((MeromorphicAt.id s).sub (MeromorphicAt.const s₀ s)).mul (hE'.2.1 s trivial),
    (EqRight.refl (fun s : ℂ => s - s₀)).map₂ (· * ·) hE'.2.2⟩

theorem eisRegularAt_sub_smul (hE : EisContinues V Φ) (s₀ s₁ : ℂ) {k : ℕ} (h : EisRegularAt V Φ s₁ k) :
    EisRegularAt V ((fun s => s - s₀) • Φ) s₁ k := by
  obtain ⟨r, H, hr, e, hd, hc, C, N, hb⟩ := h
  have hcont : ∀ s ∈ ball s₁ r, s ≠ s₁ → ∀ g,
      eisCont V ((fun s => s - s₀) • Φ) s g = (s - s₀) * eisCont V Φ s g := by
    intro s hs h0 g
    simp only [eisCont, eisSer_sub_smul]
    refine cont_sub_mul (hE.2 g) s₀ s ?_
    have hU : ball s₁ r \ {s₁} ∈ 𝓝 s := (isOpen_ball.sdiff isClosed_singleton).mem_nhds ⟨hs, h0⟩
    have ht : ContinuousAt (fun t => H t g / (t - s₁) ^ k) s :=
      ((hd g).continuousOn.continuousAt (isOpen_ball.mem_nhds hs)).div (by fun_prop)
        (pow_ne_zero _ (sub_ne_zero.2 h0))
    refine ht.congr ?_
    filter_upwards [hU] with t ht'
    rw [e t ht'.1 ht'.2 g]
    exact mul_div_cancel_left₀ _ (pow_ne_zero _ (sub_ne_zero.2 ht'.2))
  refine ⟨r, fun s g => (s - s₀) * H s g, hr, fun s hs h0 g => ?_, fun g => (differentiableOn_id.sub_const _).mul (hd g),
    (by fun_prop : ContinuousOn (fun x : ℂ × GA D (dblSp V) => x.1 - s₀) _).mul hc, (‖s₁ - s₀‖ + r) * C, N,
    fun s hs g => ?_⟩
  · show (s - s₀) * H s g = _
    rw [hcont s hs h0 g, e s hs h0 g]; ring
  · rw [norm_mul, mul_assoc]
    have h1 : ‖s - s₀‖ ≤ ‖s₁ - s₀‖ + r := by
      calc ‖s - s₀‖ = ‖(s - s₁) + (s₁ - s₀)‖ := by ring_nf
        _ ≤ ‖s - s₁‖ + ‖s₁ - s₀‖ := norm_add_le _ _
        _ ≤ ‖s₁ - s₀‖ + r := by linarith [(mem_ball_iff_norm.1 hs).le]
    exact mul_le_mul h1 (hb s hs g) (norm_nonneg _) (add_nonneg (norm_nonneg _) hr.le)

theorem eisValueAt_sub_smul {s₀ : ℂ} {E₁ : GA D (dblSp V) → ℂ} (hp : EisPoleLE V Φ s₀ 1)
    (hc : EisCoeffAt V Φ s₀ (-1) E₁) : EisValueAt V ((fun s => s - s₀) • Φ) s₀ E₁ := by
  refine ⟨hp.1.smul _, fun g => ?_⟩
  obtain ⟨E, hx, -⟩ := id (hp.2 g)
  have t := hx.tendsto_of_poleLE (hp.2 g) (c := E₁ g) (by simpa using hc.2 g)
  rw [eisSer_sub_smul]
  exact ((isExtAt_sub s₀ s₀).mul hx).holValueAt_iff.2 (by simpa using t)

end GlobalTheory.Eis.Residue

namespace GlobalTheory.Eis

open GlobalTheory.Eis.Residue

theorem coeffAt_neg_one_zeta_of_eisCoeffAt : ∀ (D : D7) (V : HSp D) (μ : (AE D)ˣ →* Circle), IsHeckeChar D μ → ∀ (m : Measure (GA D V)), m.IsHaarMeasure → ∀ (Φ : ℂ → GA D (dblSp V) → ℂ), GlobalTheory.Eis.EisContinues V Φ → (∀ g, AnalyticOnNhd ℂ (GlobalTheory.Eis.eisSer V Φ g) (rightOf (V.rank / 2))) → (∀ s₀, ∃ k, GlobalTheory.Eis.EisRegularAt V Φ s₀ k) → ∀ f₁ f₂ : GA D V → ℂ, GlobalTheory.Grow.RapidDec V f₁ → GlobalTheory.Grow.RapidDec V f₂ → GlobalTheory.Eis.IsZetaFamily V μ m Φ f₁ f₂ → ∀ (s₀ : ℂ) (E₁ : GA D (dblSp V) → ℂ), GlobalTheory.Eis.EisPoleLE V Φ s₀ 1 → GlobalTheory.Eis.EisCoeffAt V Φ s₀ (-1) E₁ → CoeffAt (GlobalTheory.Eis.zeta V μ m Φ f₁ f₂) s₀ (-1) (GlobalTheory.Eis.dblInt V μ m E₁ f₁ f₂) := by
  intro D V μ hμ m hm Φ hE ha hreg f₁ f₂ h₁ h₂ hZ s₀ E₁ hp hc
  have han : ∀ g, AnalyticOnNhd ℂ (eisSer V ((fun s => s - s₀) • Φ) g) (rightOf (V.rank / 2)) := fun g => by
    rw [eisSer_sub_smul]
    exact fun s hs => (analyticAt_id.sub analyticAt_const).mul (ha g s hs)
  have hv := (zetaHolValueAt_of_eisValueAt D V μ hμ m hm ((fun s => s - s₀) • Φ) (eisContinues_sub_smul hE s₀) han
    (fun s₁ => let ⟨k, h⟩ := hreg s₁; ⟨k, eisRegularAt_sub_smul hE s₀ s₁ h⟩) f₁ f₂ h₁ h₂
    (isZetaFamily_sub_smul hZ s₀) s₀ E₁ (eisValueAt_sub_smul hp hc)).2.2
  have ez : zeta V μ m ((fun s => s - s₀) • Φ) f₁ f₂ = fun s => (s - s₀) * zeta V μ m Φ f₁ f₂ s := funext fun s => by
    have e2 := dblInt_smul (V := V) (μ := μ) (m := m) (E := eis V (Φ s)) (f₁ := f₁) (f₂ := f₂) (s - s₀) 1 1
    simp only [one_smul, map_one, mul_one] at e2
    show dblInt V μ m (eis V ((s - s₀) • Φ s)) f₁ f₂ = _
    rw [eis_smul, e2]; rfl
  rw [ez] at hv
  exact coeffAt_neg_one_of_holValueAt hv

end GlobalTheory.Eis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColMatchAll
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2
attribute [local instance] GlobalTheory.Mem.Col2.starE

noncomputable section

namespace GlobalTheory.Core.Ht2

theorem colMatchAll : ColMatchAll := by
  intro B X I h hX l Z hJ u a
  have KO := GlobalTheory.Mem.Col2.KerRat.kernelsOver_of_family I l Z h hJ (GlobalTheory.Core.Ht2.family_laws I h hX l Z) u a
  refine ⟨?_, fun c x φ F z hx hF => ?_⟩
  · obtain ⟨⟨b⟩, hb⟩ := KO.period
    obtain ⟨hY, hK, hF, -, -⟩ := hb b
    exact ⟨⟨b, hY, hK, hF⟩⟩
  · obtain ⟨hY, hK, hF', hM, heq⟩ := KO.period.2 c.b
    have ex : x = GlobalTheory.Mem.Col2.KerRat.colForm I l h u a φ := Subtype.ext (funext hx)
    have eF : F = GlobalTheory.Mem.Col2.KerRat.rowForm I l h u a z := by
      apply Subtype.ext; funext t p; exact hF p
    subst ex; subst eF
    rw [heq φ z]
    rfl

end GlobalTheory.Core.Ht2

end
end

