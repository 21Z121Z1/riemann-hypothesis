import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0027
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IdxMatNF
import Formalism.LocalToGlobal.KernelLattices.KerHypAll
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsHalfPtIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelsOverOfFamily
import Formalism.LocalToGlobal.Columns.KernelEquivCharacterTrivialTuple
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0072
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ToLinNfMatEqSumNfGen
import Formalism.LocalToGlobal.Columns.ChainTwOk
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0287
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0150
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormOneDetIdealTransportedLattice
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.RatKDeg
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.RkEqcar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0105
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0372
import Formalism.LocalToGlobal.GlobalTheory.GL3.PLinkThIndep
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ExistsIntegralMulOrderElement
import Formalism.LocalToGlobal.KernelLattices.ColumnData.Smooth
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0102
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0021
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
import Formalism.LocalToGlobal.IndefiniteReal.BridgeColPts
import Formalism.LocalToGlobal.Columns.Bundle0017
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0424
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0416
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0426
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0421
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0503
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0499
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCutQGrp
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0031
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0026
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0500
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0471
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0450
import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvaluationDatumOkBaseTuple
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC.RcHyp

theorem n1_span_unitary {D : D7} (z : unitary D.host.E) : TaylorLogMetric.N1 D (Submodule.span (𝓞 D.host.E) {(z : D.host.E)}) := by
  refine (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.CU.normOne_ideal_iff_mul_conj (D := D) _).2 ?_
  rw [Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.CU.cS_span (D := D), Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.CU.span_singleton_mul_span_singleton_host (D := D)]
  have hz : (z : D.host.E) * D.host.conj (z : D.host.E) = 1 := by
    rw [← Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.CU.star_conj (D := D)]
    exact Unitary.mul_star_self_of_mem z.2
  rw [hz, ← Submodule.one_eq_span]

end GlobalTheory.Mem.Col2.TC.RcHyp

noncomputable section
namespace GlobalTheory.Mem.Col2.TC.RcHyp

variable {B : Base} {X : PreX B.toPre}

theorem n1_detStd (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) {n : ℕ}
    {N : Submodule (𝓞 B.fields.E) (Sp B.fields.E n)} (hN : IsSdLat N) :
    TaylorLogMetric.N1 (I.rec7 l Z) (TaylorLogMetric.detId (I.rec7 l Z) (StandardLatticesGL3.stdL (I.rec7 l Z) n) N) := by
  have h := GlobalTheory.CharValCompare.normOne_detIdeal_transportedLattice (seamOf_ok B (I.cols l) Z.W Z.V Z.S Z.N Z.G) hN
  rwa [seamOf_lat] at h

set_option maxHeartbeats 1000000 in

theorem jetsRat_chi (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (hJ : ColIn.JetsIn I)
    (χ : Submodule (𝓞 B.host.E) B.host.E → ℂ) (hχ : ∀ 𝔞, TaylorLogMetric.N1 (I.rec7 l Z) 𝔞 → χ 𝔞 = I.chi 𝔞) (a : I.ι) (u : B.Word)
    (i : ℕ) (hi : i < B.R.m) :
    (I.J.amb B χ).JetsRatDeg (B.R.N i) (B.R.N (i + 1)) (Sall (Pr := B.primes X) I.sel (I.tup a) u)
      (cAof (Pr := B.primes X) I.sel (I.tup a) (I.cst a) * cBof (Pr := B.primes X) I.sel (I.tup a) (I.cst a) u)
      (stepDeg (Pr := B.primes X) B.wts u i) := by
  intro N N' c x hx m hm
  have hf : Th.chiFac B.host χ (B.R.N i) (B.R.N (i + 1)) N N' = Th.chiFac B.host I.chi (B.R.N i) (B.R.N (i + 1)) N N' := by
    unfold Th.chiFac
    rw [hχ (Th.detId B.host (Th.stdL B.host _) N) (n1_detStd I l Z hx.1),
      hχ (Th.detId B.host (Th.stdL B.host _) N') (n1_detStd I l Z hx.2.1)]
  have e3 : (I.J.amb B χ).e (B.R.N i) (B.R.N (i + 1)) N N' = I.A.e (B.R.N i) (B.R.N (i + 1)) N N' := by
    show I.J.V.eNat χ _ _ N N' = I.J.V.eNat I.chi _ _ N N'
    unfold Th.VacIn.eNat
    rw [hf]
  have e4 : (I.J.amb B χ).thInd (Sall (Pr := B.primes X) I.sel (I.tup a) u) N N' c x =
      I.A.thInd (Sall (Pr := B.primes X) I.sel (I.tup a) u) N N' c x := by
    funext z
    unfold Amb.thInd
    rw [e3]
    rfl
  obtain ⟨y, hy⟩ := hJ a u i hi N N' c x hx m fun τ => by
    show ((degAt m τ : ℕ) : ℤ) = _
    rw [hm τ]
    exact chain_degree_eq B.fields (B.primes X) B.R B.wts u i hi τ
  refine ⟨y, ?_⟩
  rw [e4]
  exact hy.trans (by rw [show I.A.chiF (B.R.N i) (B.R.N (i + 1)) N N' = (I.J.amb B χ).chiF (B.R.N i) (B.R.N (i + 1)) N N' from hf.symm]; rfl)

end GlobalTheory.Mem.Col2.TC.RcHyp

namespace GlobalTheory.Mem.Col2.TC.RcHyp

variable {B : Base} {X : PreX B.toPre}

theorem idxMatNF_of_isTw (I : TC B X) (h : I.Ok) (ht : I.IsTw) (a : I.ι) : GlobalTheory.QNF.IdxMatNF (I.idx a) := by
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  have hm : B.R.m = (B.R.m - 2) + 2 := h.hm
  have hD := ht.deep
  have hK : TwCstQ (Pr := B.primes X) I.sel (I.tup a) I.glob :=
    twCstQ_of (fun P _ => degOne_of_ok h a P) (root_of_ok h hD a) (fun P _ => sqrt_of_ok h a P) (fun P _ => (h.idx_ok a).xiUnitAtPrime P)
  have hN := twNormAt_all (twNormDC_of (unfoldingNonvanishingDoubleCoset_holds (Ch := I.Ch) I.glob hm hK)) (fun P _ => degOne_of_ok h a P)
  rw [ht.idx_eq a]
  intro j b v hv hj1 hj2
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have H := twSt_cand (Ch := I.Ch) (sel := I.sel) (mu := I.tup a) (by omega) (hN i (by omega)) b v hv
  exact GlobalTheory.Proof.TwistedNormalForms.twNF_imp_matNF _ _ _ _ _ hv _ H.2.1

theorem evaluationDatum_ok_baseTuple (I : TC B X) (u : B.Word) :
    (evGSD (Pr := B.primes X) B.wts I.Ch I.sel (I.tup I.mu0) I.Ps u).Ok := by
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  have := hX.cplxK
  exact GlobalTheory.CoreHt.evGSD_ok_of_eq_one B.fields hX (B.primes X) B.R B.wts I.Ch I.sel I.S (I.tup I.mu0) I.Ps u hPr I.trueColumn_tuple_trivial_eq_one

end GlobalTheory.Mem.Col2.TC.RcHyp

namespace GlobalTheory.Mem.Col2.TC.RcHyp

variable {B : Base} {X : PreX B.toPre}

set_option maxHeartbeats 1000000 in

theorem chTh_ok_chi (I : TC B X) (h : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (hJ : ColIn.JetsIn I) (χ : Submodule (𝓞 B.host.E) B.host.E → ℂ) (hχ : ∀ 𝔞, TaylorLogMetric.N1 (I.rec7 l Z) 𝔞 → χ 𝔞 = I.chi 𝔞)
    (a : I.ι) (u : B.Word) :
    ChTh.Ok (Ch := I.Ch) (I.cst a) (chTh (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.J.amb B χ) u (B.R.m - 2)) := by
  obtain ⟨hX, hPr, hW, -⟩ := base_fields_primes_ok B X
  have hX1 : B.fields.AbelianUnramifiedExtensionConditions := (GlobalTheory.Mem.FieldsLaws.fields_satisfy_definite_laws B).1
  have hm : B.R.m = (B.R.m - 2) + 2 := h.hm
  have hL := h.idx_ok a
  have hs := seamOf_ok B (I.cols l) Z.W Z.V Z.S Z.N Z.G
  have hδ := ((I.J.ok_iff B (I.cols l) Z.W Z.V Z.S Z.N Z.G).1 h.amb_ok).1
  have hcc : TaylorLogMetric.IsCurveIdeal (I.rec7 l Z) ⊤ := ⟨top_ne_bot, by simp⟩
  have hχ0 : TaylorLogMetric.IsChi (I.rec7 l Z) I.chi := GlobalTheory.Mem.ChiIdeal.isChi_chiId _ _ I.C.isChi
  have hχ1 : TaylorLogMetric.IsChi (I.rec7 l Z) χ := by
    refine ⟨fun 𝔞 𝔟 h𝔞 h𝔟 => ?_, fun z => ?_⟩
    · rw [hχ _ h𝔞, hχ _ h𝔟, hχ _ (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.CU.normOne_ideal_mul (D := I.rec7 l Z) h𝔞 h𝔟)]
      exact hχ0.1 𝔞 𝔟 h𝔞 h𝔟
    · rw [hχ _ (n1_span_unitary (D := I.rec7 l Z) z)]
      exact hχ0.2 z
  have he : ∀ k, Even (B.R.N k) := fun k => Formalism.L2.Ker.even_rankN B.R k
  have hg : XiOffG (B.primes X) (I.tup a : Chr B.fields.F B.fields.E B.fields.K) := xiOffG_of_mem hPr h.g_mem
  have hTies : LawTies B.wts I.Ch I.sel (I.tup a) (I.cst a) I.glob :=
    lawTies_of_ok B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.glob (B.R.m - 2) hL hW ⟨I.C.eta, h.ch_tied⟩
  have hLa : ∀ i, (I.J.amb B χ).LaHyp (B.R.N i) (B.R.N (i + 1)) (ColIn.Sb I a u) := fun i => by
    have bad := GlobalTheory.ThetaMove.BadPrimes.bad_primes B.fields (B.primes X) I.sel I.S (I.tup a) u hX hPr h.sel_ok (h.T_mem u) h.g_mem
    have hL0 := Formalism.L2.Ker.laHyp_ambOf_top (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) χ I.J.cD (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G)
      hs hδ (he i) (he (i + 1)) ∅ (fun P hP => absurd hP (Finset.notMem_empty P)) (fun P hP => absurd hP (Finset.notMem_empty P))
    rw [AmbIn.amb_eq_ambOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G]
    exact ⟨hL0.1, hL0.2.1, fun P hP => (bad P hP).1, fun P hP => GlobalTheory.PeriodIdealUnit.locP_AA_eq_one _ _ _ _ _ _ _ _ P (bad P hP).2.1
      (bad P hP).2.2.1 (by simp), hL0.2.2.2.2⟩
  have hSm : ∀ i, (I.J.amb B χ).ESmooth (B.R.N i) (B.R.N (i + 1)) := fun i => by
    rw [AmbIn.amb_eq_ambOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G]
    exact Formalism.L2.Ker.Cd.ambOf_eSmooth (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G).toCar (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G).toCar χ I.J.cD hs hcc hδ I.J.δ_ne_zero (he i) (he (i + 1))
  have hRat := jetsRat_chi I l Z hJ χ hχ a u
  have hst : ∀ i, i < B.R.m → ThEquivP (stepT (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.J.amb B χ) u i (B.wts.lamTrue u (i + 1)))
      (Sall (Pr := B.primes X) I.sel (I.tup a) u) (cAof (Pr := B.primes X) I.sel (I.tup a) (I.cst a) * cBof (Pr := B.primes X) I.sel (I.tup a) (I.cst a) u)
      (colValF (Pr := B.primes X) B.wts I.sel (I.tup a) u i).rho (colValF (Pr := B.primes X) B.wts I.sel (I.tup a) u (i + 1)).rho := fun i hi => by
    choose e he' using fun τ => (B.hc τ).e_int ⟨i, hi⟩
    have hLa' := hLa i
    have hRat' := hRat i hi
    rw [AmbIn.amb_eq_ambOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G] at hLa' hRat' ⊢
    exact Cd.CarC.thEquivP_ambOf_tiesD (X := B.fields) (Pr := B.primes X) (R := B.R) (W := B.wts) (Ch := I.Ch) (sel := I.sel)
      (mu := I.tup a) (cst := I.cst a) (G := I.glob) u (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G).toCar (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G).toCar χ I.J.cD hs hcc hδ hχ1 hX1 hPr h.sel_ok hg hTies
      (hPr.T_prime u).pos hi e (fun τ => (he' τ).symm) hLa' hRat'
  have hlaws := chThT_laws_of (Pr := B.primes X) (W := B.wts) (Ch := I.Ch) (sel := I.sel) (mu := I.tup a) (cst := I.cst a)
    (A := I.J.amb B χ) (u := u) hm hst
  have hTh : ThHypD (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.J.amb B χ) u (B.R.m - 2) := by
    refine ⟨fun i hi => ⟨hLa i, hSm i, hRat i (by omega)⟩, ?_, hlaws.1, hlaws.2⟩
    have e' : B.R.N B.R.m = B.R.N (B.R.m - 2 + 1 + 1) := by rw [← hm]
    rw [e']
    exact ⟨hLa _, hSm _, hRat _ (by omega)⟩
  exact chTh_ok_ambD (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.J.amb B χ) u (B.R.m - 2) (by omega) (hPr.T_prime u).pos
    (muqTie_of_ok I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) hL) hTh

end GlobalTheory.Mem.Col2.TC.RcHyp

namespace GlobalTheory.Mem.Col2.TC.RcHyp

theorem hyps_of_isTw : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), I.IsTw → ColIn.JetsIn I → ∀ (χ : Submodule (𝓞 B.host.E) B.host.E → ℂ), (∀ 𝔞, TaylorLogMetric.N1 (I.rec7 l Z) 𝔞 → χ 𝔞 = I.chi 𝔞) → ∀ (a : I.ι) (u : B.Word), (∀ j, (chF (Pr := B.primes X) B.wts I.sel (I.tup a) (I.idx a) u j).Ok) ∧ (evGSD (Pr := B.primes X) B.wts I.Ch I.sel (I.tup I.mu0) I.Ps u).Ok ∧ GlobalTheory.QNF.IdxMatNF (I.idx a) ∧ ∀ b hY, KerEquivC (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) (I.J.amb B χ) u (B.R.m - 2) b hY I.Ps := by
  intro B X I h _ l Z ht hJ χ hχ a u
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  exact ⟨ht.chF_ok h B.wts a u, evaluationDatum_ok_baseTuple I u, idxMatNF_of_isTw I h ht a, fun b hY =>
    KerRat.kerEquivC (Pr := B.primes X) B.wts (I.J.amb B χ) u hX hPr h.sel_ok ⟨h.T_mem u, h.g_mem⟩ (h.idx_ok a) (h.sharp a)
      (chTh_ok_chi I h l Z hJ χ hχ a u) b hY⟩

end GlobalTheory.Mem.Col2.TC.RcHyp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonCoefficientMapLiftPresentation
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.Mem.R3.LiftPresStd

theorem vv_cast_equiv : ∀ {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [StarRing K] {ι : Type} [Fintype ι]
    (emb : ι → E →+* K) {n n' : ℕ} (h : n = n') (lam : ι → DomWeight n) (lam' : ι → DomWeight n'),
    (∀ τ a, (lam τ).w a = (lam' τ).w (Fin.cast h a)) →
    ∃ e : VV K lam ≃ₗ[K] VV K lam',
      (∀ (g : GL (Fin n') E) v, e (rhoVr emb lam (LiftBrg.castGL h.symm g) v) = rhoVr emb lam' g (e v)) ∧
      (∀ (J : Matrix (Fin n) (Fin n) E) x y,
        pairVr emb lam' (J.reindex (finCongr h) (finCongr h)) (e x) (e y) = pairVr emb lam J x y) ∧
      (∀ N : Submodule (𝓞 E) (Fin n → E), (nabAtr emb lam N).map (e.toLinearMap.restrictScalars (𝓞 K)) =
        nabAtr emb lam' (N.map (LinearEquiv.funCongrLeft (𝓞 E) E (finCongr h).symm).toLinearMap)) ∧
      (∀ N : Submodule (𝓞 E) (Fin n → E), (delAtr emb lam N).map (e.toLinearMap.restrictScalars (𝓞 K)) =
        delAtr emb lam' (N.map (LinearEquiv.funCongrLeft (𝓞 E) E (finCongr h).symm).toLinearMap)) ∧
      (∀ i j, (bVV K lam').repr (e (bVV K lam i)) j ∈ Formalism.DivisionValues.cmMax K) ∧
      (∀ (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (σ : K →+* ℂ) (c0 : VV K lam' →ₛₗ[σ] W),
        LinearIndependent ℂ (fun i => c0 (bVV K lam' i)) → Submodule.span ℂ (Set.range fun i => c0 (bVV K lam' i)) = ⊤ →
        LinearIndependent ℂ (fun i => c0 (e (bVV K lam i))) ∧ Submodule.span ℂ (Set.range fun i => c0 (e (bVV K lam i))) = ⊤) := by
  intro E K _ _ _ _ _ ι _ emb n n' h lam lam' hl
  subst h
  have hlam : lam = lam' := by
    funext τ
    have h1 := hl τ
    rcases hw : lam τ with ⟨w, hw1⟩
    rcases hw' : lam' τ with ⟨w', hw1'⟩
    rw [hw, hw'] at h1
    have : w = w' := funext fun a => by simpa using h1 a
    subst this
    rfl
  subst hlam
  have hN : ∀ N : Submodule (𝓞 E) (Fin n → E),
      N.map (LinearEquiv.funCongrLeft (𝓞 E) E (finCongr (rfl : n = n)).symm).toLinearMap = N := by
    intro N
    ext x
    simp only [Submodule.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      convert hy using 1
      funext a
      rfl
    · intro hx
      exact ⟨x, hx, rfl⟩
  refine ⟨LinearEquiv.refl K _, fun g v => ?_, fun J x y => ?_, fun N => ?_, fun N => ?_, fun i j => ?_, fun W _ _ σ c0 h1 h2 => ⟨h1, h2⟩⟩
  · have : LiftBrg.castGL (rfl : n = n).symm g = g := by ext a b; simp [LiftBrg.castGL]
    rw [this]; rfl
  · have : J.reindex (finCongr (rfl : n = n)) (finCongr (rfl : n = n)) = J := by ext a b; simp
    rw [this]; rfl
  · rw [hN]; exact Submodule.map_id _
  · rw [hN]; exact Submodule.map_id _
  · show (bVV K lam).repr (bVV K lam i) j ∈ Formalism.DivisionValues.cmMax K
    rw [Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _

theorem ufGL_ratHom : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) (γ : Formalism.L2.Col.URat hc n),
    Formalism.L2.Col.ufGL E n (Formalism.L2.Col.ratHom hc n γ) = (γ : GL (Fin n) E) := by
  intro F E _ _ _ _ _ _ hc n γ
  apply Units.ext
  ext a b
  simp [Formalism.L2.Col.ufGL, Formalism.L2.Col.toGLm, Formalism.L2.Col.ratHom, Formalism.UG.glEquiv, Matrix.GeneralLinearGroup.toLin, LinearMap.GeneralLinearGroup.generalLinearEquiv]

theorem formRho_colGl {X : Formalism.L2.Col.Fields} {n : ℕ} [NeZero n] {SG : Finset (HeightOneSpectrum (𝓞 X.E))} (hc : Formalism.BasicNotions.CMData X.F X.E)
    (C : Formalism.L2.Col.CoefPk X n (Formalism.L2.Col.DecoSet X.E n ∅ SG)) (Λ : Formalism.L2.Col.LevFam X.E X.K n SG)
    (γ : Formalism.L2.Col.URat hc n) (k : Bridge.colJ hc n ∅ SG Λ.grp) (v : C.V) :
    (Formalism.L2.Col.formGSD C Λ).ρ (Bridge.colGl (Formalism.L2.Col.rf_onDeco C Λ) (γ, k)) v =
      ((Λ.chr (Formalism.L2.Col.redH hc n ∅ SG Λ.grp ((Bridge.colJEquiv hc n ∅ SG Λ.grp).symm k)) : X.Kˣ) : X.K) •
        C.rho (Formalism.L2.Col.ratHom hc n γ) v := rfl

theorem castGL_symm_castGL {R : Type} [CommRing R] {m n : ℕ} (h : m = n) (g : GL (Fin m) R) :
    LiftBrg.castGL h.symm (LiftBrg.castGL h g) = g := by
  subst h
  ext a b
  simp [LiftBrg.castGL]

theorem exists_oneCoef_presStd : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m)
    (c0L : VV X.toD7.what₂.LL (fun τ => Bridge.lamLdef (Vc X.toD7 i).rank ((i : ℕ) + 1) τ) →ₛₗ[X.toD7.what₂.embLL] (cV i).W),
    (cV i).Is → Bridge.CoefMapTie (Vc X.toD7 i) (cV i).coef c0L (rhoVr (labLL X.toD7) _) →
    (∀ x y, inner ℂ (c0L x) (c0L y) = X.toD7.what₂.embLL (pairVr (labLL X.toD7) _
      (if X.toD7.sp.Vneg ((i : ℕ) + 1) then -(Vc X.toD7 i).gram else (Vc X.toD7 i).gram) x y)) →
    L.βV i = 1 → (Vc X.toD7 i).gram = 1 →
    ∃ c : VV X.B.fields.K (X.B.wts.lamV ((i : ℕ) + 1)) →ₛₗ[X.B.embLL] (cV i).W, (∀ (γ : GQ (Vc X.toD7 i)) (γE : GL (Fin (Vc X.toD7 i).rank) X.toD7.host.E), Bridge.IsRatMat (Vc X.toD7 i) γ γE →
      ∀ v, c (rhoVr X.B.fields.emb (X.B.wts.lamV ((i : ℕ) + 1)) (LiftBrg.castGL (LiftBrg.rkEq X i).symm γE) v) = (cV i).coef.ρ γ (c v)) ∧
      ∀ t : TupU I U, ∃ P : LiftBrg.PresL X I hX U Xg tr L cV i t, LiftBrg.ReadsStd X I hX U Xg tr L cV i t 1 1 P ∧
        (∀ v, P.coef v = c v) ∧ Bridge.CoefTie (X.toD7.sp.V ((i : ℕ) + 1)) (cV i).coef P (fun τ => Bridge.lamLdef (Vc X.toD7 i).rank ((i : ℕ) + 1) τ) c0L
        (pairVr (labLL X.toD7) _
          (if X.toD7.sp.Vneg ((i : ℕ) + 1) then -(X.toD7.sp.V ((i : ℕ) + 1)).gram else (X.toD7.sp.V ((i : ℕ) + 1)).gram))
        (nabAtr (labLL X.toD7) _) (delAtr (labLL X.toD7) _) := by
  intro X px I hX U Xg tr L eG0 hI hV hL hG cV i c0L hcV hmap hin hβ hgram
  obtain ⟨e0, he_rho, he_pair, he_nab, he_del, he_rat, he_li⟩ :=
    vv_cast_equiv X.B.fields.emb (LiftBrg.rkEq X i) (X.B.wts.lamV ((i : ℕ) + 1))
      (fun τ => Bridge.lamLdef (D := X.toD7) (Vc X.toD7 i).rank ((i : ℕ) + 1) τ) (GlobalTheory.T.baseWeight_eq_forcedLiftWeight X i)
  let c : VV X.B.fields.K (X.B.wts.lamV ((i : ℕ) + 1)) →ₛₗ[X.B.embLL] (cV i).W :=
    { toFun := fun v => c0L (e0 v)
      map_add' := fun v w => by show c0L (e0 (v + w)) = c0L (e0 v) + c0L (e0 w); rw [map_add]; exact c0L.map_add _ _
      map_smul' := fun a v => by show c0L (e0 (a • v)) = _; rw [LinearEquiv.map_smul]; exact c0L.map_smulₛₗ a (e0 v) }
  have hc : ∀ v, c v = c0L (e0 v) := fun v => rfl
  have hint : ∀ (γ : GQ (Vc X.toD7 i)) (γE : GL (Fin (Vc X.toD7 i).rank) X.toD7.host.E), Bridge.IsRatMat (Vc X.toD7 i) γ γE →
      ∀ v, c (rhoVr X.B.fields.emb (X.B.wts.lamV ((i : ℕ) + 1)) (LiftBrg.castGL (LiftBrg.rkEq X i).symm γE) v) = (cV i).coef.ρ γ (c v) := by
    intro γ γE h v
    exact (congrArg c0L (he_rho γE v)).trans (hmap.1 γ γE h (e0 v))
  refine ⟨c, hint, fun t => ?_⟩
  obtain ⟨eG, eΓ, hchar, hι, hrat⟩ := GlobalTheory.T.exists_unitaryGroups_equiv_unitForm_gram_one X i hgram
  obtain ⟨hJ, hχ⟩ := GlobalTheory.T.liftAdelicForm_level_type_eq_columnLevel X px I U L hI hV hL i t eG hchar

  letI : Algebra X.toD7.host.F X.B.fields.E := inferInstanceAs (Algebra X.toD7.host.F X.toD7.host.E)
  have hneg : X.toD7.sp.Vneg ((i : ℕ) + 1) = false := X.B.V_pos _ (by omega) i.2
  have hgr : (if X.toD7.sp.Vneg ((i : ℕ) + 1) then -(Vc X.toD7 i).gram else (Vc X.toD7 i).gram) =
      (1 : Matrix (Fin X.B.R.nV) (Fin X.B.R.nV) X.toD7.host.E).reindex (finCongr (LiftBrg.rkEq X i)) (finCongr (LiftBrg.rkEq X i)) := by
    rw [hneg, if_neg (by simp), hgram]
    ext a b
    simp [Matrix.one_apply]
  have hSG : Formalism.L2.Col.DecoPtSurj X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) :=
    Formalism.L2.Col.decoPtSurj_of _ _ _ _ (Formalism.L2.Col.unimodGenus_holds _ _) Formalism.L2.DIV.reduction_surjective_bis
      (by classical convert GlobalTheory.T.rowFormLevelPrimes_isSplitSet X px I U L hI hL t using 1; exact Finset.empty_union _) (Finset.disjoint_empty_left _)
  let o := Formalism.L2.Col.rf_onDeco (X := X.B.fields) (n := X.B.R.nV) (ST := ∅) (SG := LiftBrg.sgL X I U t)
    (Formalism.L2.Col.mtVal (Pr := X.B.primes px) X.B.wts ((i : ℕ) + 1) _) (Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv
  have hmem : ∀ k : Bridge.colJ X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) (Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.grp,
      (eG.toMonoidHom.comp (Subgroup.subtype _)) k ∈ (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).J := fun k => by
    rw [hJ]; exact Subgroup.mem_map_of_mem _ k.2
  let χc := (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).χ.comp ((eG.toMonoidHom.comp (Subgroup.subtype _)).codRestrict _ hmem)
  have hχc : ∀ k, ((χc k)⁻¹ : ℂˣ) = Units.map X.toD7.what₂.embLL.toMonoidHom ((Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.chr
      (Formalism.L2.Col.redH X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) _
        ((Bridge.colJEquiv X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) _).symm k))) := fun k => (hχ k (hmem k)).1
  have hK1 : ∀ k : Bridge.colJ X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) (Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.grp,
      (k : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV) ∈ Bridge.principalCongruenceSubgroup X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) → χc k = 1 :=
    fun k hk => (hχ k (hmem k)).2 hk
  have hli := he_li (cV i).W X.toD7.what₂.embLL c0L hmap.2.1 hmap.2.2
  have hpair : ∀ x x', inner ℂ (c x) (c x') = X.toD7.what₂.embLL ((Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).pair x x') := by
    intro x x'
    refine (hin (e0 x) (e0 x')).trans ?_
    congr 1
    rw [hgr]
    exact he_pair 1 x x'
  have hgl : ∀ (γ : Formalism.L2.Col.URat X.toD7.sp.cm X.B.R.nV) k (v : (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).V),
      c ((Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).ρ (Bridge.colGl o (γ, k)) v) =
        ((χc k)⁻¹ : ℂˣ) • ((cV i).coef.ρ.comp eΓ.toMonoidHom) γ (c v) := by
    intro γ k v
    rw [show (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).ρ (Bridge.colGl o (γ, k)) v = _ from
      formRho_colGl (X := X.B.fields) X.toD7.sp.cm _ _ γ k v]
    refine (c.map_smulₛₗ _ _).trans ?_
    have e3 : (Formalism.L2.Col.mtVal (Pr := X.B.primes px) X.B.wts ((i : ℕ) + 1) (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1)).rho
        (Formalism.L2.Col.ratHom X.toD7.sp.cm X.B.R.nV γ) v =
        rhoVr X.B.fields.emb (X.B.wts.lamV ((i : ℕ) + 1))
          (LiftBrg.castGL (LiftBrg.rkEq X i).symm (LiftBrg.castGL (LiftBrg.rkEq X i) (γ : GL (Fin X.B.R.nV) X.toD7.host.E))) v := by
      show rhoVr X.B.fields.emb (X.B.wts.lamV ((i : ℕ) + 1))
        (Formalism.L2.Col.ufGL X.toD7.host.E X.B.R.nV (Formalism.L2.Col.ratHom X.toD7.sp.cm X.B.R.nV γ)) v = _
      rw [ufGL_ratHom]
      exact congrArg (fun g => rhoVr X.B.fields.emb (X.B.wts.lamV ((i : ℕ) + 1)) g v) (castGL_symm_castGL (LiftBrg.rkEq X i) _).symm
    have e2 := hint (eΓ γ) _ (hrat γ) v
    have e4 := (congrArg c e3).trans e2
    rw [hχc k, Units.smul_def]
    erw [e4]
    rfl

  let A := Bridge.colAdPts o hSG
  let P0 := Bridge.colClassPres (hc := X.toD7.sp.cm) o hSG (Formalism.L2.Col.mtKOk X.B.wts I.Ch I.sel t.1 hX ((i : ℕ) + 1)) X.toD7.what₂.embLL
    ((cV i).coef.ρ.comp eΓ.toMonoidHom) χc c hli.1 hli.2 hpair hK1 hgl
  let P : LiftBrg.PresL X I hX U Xg tr L cV i t :=
    P0.transport eG eΓ hι (fun _ => rfl) hJ (fun k hk => rfl)
  refine ⟨P, ?_, fun v => rfl, e0, he_rat, fun x => rfl, ?_, ?_, ?_⟩

  · intro f g
    have h5 := GlobalTheory.T.transportedClassSetPresentation_reads_equivariant (ι' := Bridge.ratF (Vc X.toD7 i)) (ρ' := (cV i).coef.ρ) (J' := (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).J)
      (χ' := (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).χ) A (Formalism.L2.Col.mtKOk X.B.wts I.Ch I.sel t.1 hX ((i : ℕ) + 1)) X.toD7.what₂.embLL
      ((cV i).coef.ρ.comp eΓ.toMonoidHom) χc c hli.1 hli.2 hpair hK1 hgl eG eΓ hι (fun _ => rfl) hJ (fun k hk => rfl) f g
    refine h5.trans ?_
    have hq : A.q (eG.symm g) = LiftBrg.ptL X I U i t 1 1 g := by
      show Formalism.L2.Col.decoPt X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) (QuotientGroup.mk (eG.symm g)) = _
      rw [Formalism.L2.Col.decoPt_mk]
      unfold LiftBrg.ptL
      congr 1
      have := hchar (eG.symm g)
      rw [MulEquiv.apply_symm_apply] at this
      rw [this]
      simp
    erw [hq]
    rfl
  · intro x x'
    rw [hgr]
    exact he_pair 1 x x'
  · intro cl
    have h6 := GlobalTheory.T.translatedStdLattice_eq_decoratedLattice_reindexed X i (L.ΛV i) (by rw [← hβ]; exact hL.is.βV i) (LiftBrg.sgL X I U t) eG hchar (A.y cl)
    have hy := A.q_y cl
    have hy' : Formalism.L2.Col.decoPt X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) (QuotientGroup.mk (A.y cl)) =
        (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).outSec.rep cl := hy
    refine Eq.trans ?_ (congrArg (nabAtr (labLL X.toD7) (fun τ => Bridge.lamLdef (D := X.toD7) (Vc X.toD7 i).rank ((i : ℕ) + 1) τ)) h6).symm
    rw [hy']
    exact he_nab _
  · intro cl
    have h6 := GlobalTheory.T.translatedStdLattice_eq_decoratedLattice_reindexed X i (L.ΛV i) (by rw [← hβ]; exact hL.is.βV i) (LiftBrg.sgL X I U t) eG hchar (A.y cl)
    have hy := A.q_y cl
    have hy' : Formalism.L2.Col.decoPt X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) (QuotientGroup.mk (A.y cl)) =
        (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).outSec.rep cl := hy
    refine Eq.trans ?_ (congrArg (delAtr (labLL X.toD7) (fun τ => Bridge.lamLdef (D := X.toD7) (Vc X.toD7 i).rank ((i : ℕ) + 1) τ)) h6).symm
    rw [hy']
    exact he_del _

end GlobalTheory.Mem.R3.LiftPresStd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjugatedChartDataLocalLevelAtQStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conjugated_chartData_localLevel_at_Q : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {ST SG Q : Finset (Pl E)} {K : Type} [Field K] (Hw : ∀ w : SG, Subgroup (GL (Fin n) (𝓞 E ⧸ w.1.asIdeal))) {π : 𝓞 E} {T f : ℕ} (hB : BasePi ST π) (hTπ : π * cO E π = (T : 𝓞 E)) (hST : ∀ P : Pl E, P ∈ ST ↔ π ∈ P.asIdeal) (hcard : ∀ P ∈ ST, Nat.card (𝓞 E ⧸ P.asIdeal) = T) (hSG : ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∈ v.asIdeal → v ∉ plUnder F SG) (hidx : (baseLb E n ST).toAddSubgroup.relIndex (Submodule.span (𝓞 E) (Formalism.BasicNotions.dualSet (hc.sig : E →+* E) (1 : Matrix (Fin n) (Fin n) E) (baseLb E n ST))).toAddSubgroup = T ^ (2 * f)) (lam : (Subgroup.pi Set.univ Hw : Subgroup (GLG E n SG)) →* ℂˣ) {Θ : LevQFam E K n Q} (q : QLoc hc n Q Θ) (hO : QOpen q) (hQT : ∀ P : Q, (T : 𝓞 F) ∉ (qv F P.1).asIdeal) (σ₀ : K →+* ℂ) (b : GL (Fin n) (AfE F E)) (hbU : b ∈ UAd hc n) (hbV : ∀ v, bc (prV (E := E) v) b ∈ levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST)) (hbL : ∀ x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F, b.1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (baseLb E n ST) ↔ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (baseLb E n ST)) (hbT : ∀ v, v ∈ plUnder F ST → (levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) ⊓ stabFun (baseDualV hc n ST v) (fLoc hc n ST v)).map (MulAut.conj (bc (prV (E := E) v) b)).toMonoidHom = levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) ⊓ stabFun (baseDualV hc n ST v) (fLoc hc n ST v)) (hbO : ∀ v, v ∉ badQ' (F := F) SG Q → (T : 𝓞 F) ∉ v.asIdeal → bc (prV (E := E) v) b = 1) (J : Matrix (Fin n) (Fin n) E) (hJ : J = 1) (bad : Set (HeightOneSpectrum (𝓞 F))) (hb : bad = badQ' (F := F) SG Q) {cl : Type} (stab : cl → Type) [∀ c, Group (stab c)] (lat : cl → Submodule (𝓞 E) (Fin n → E)) (s : cl → DecoF E n ST SG Q) (y : cl → GL (Fin n) (AfE F E)) (hy : ∀ c, y c ∈ UAd hc n) (hd : ∀ c, FrOver q (y c) (s c)) (hs : Function.Bijective fun c => (Quotient.mk'' (s c) : DecoFCl (K := K) n ST SG Q (Subgroup.pi Set.univ Hw) Θ)) (hlat : ∀ c, lat c = (s c).deco.1.L) (st : ∀ c, stab c →* GL (Fin n) E) (hinj : ∀ c, Function.Injective (st c)) (hr : ∀ c γ, γ ∈ (st c).range ↔ ∃ g : UF E n × ↥(Subgroup.pi Set.univ Hw : Subgroup (GLG E n SG)) × ↥Θ.grp, ufGL E n g.1 = γ ∧ g • s c = s c) (hchr : ∀ P : Q, ∃ m : ℕ, 0 < m ∧ ∀ k, q.chr P k ^ m = 1), ∃ (lev : StepLevel F E hc.sig J T f bad) (Y : cl → UPts hc.sig J (FiniteAdeleRing (𝓞 F) F)) (SI : ∀ c, stab c →* UJ (hc.sig : E →+* E) J), Function.Bijective (fun c => (Quotient.mk'' (Y c) : Cls lev)) ∧ (∀ c (x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F), x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (lat c) ↔ ((Y c).1⁻¹).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) lev.Lb) ∧ (∀ c, Function.Injective (SI c)) ∧ (∀ c (γ : UJ (hc.sig : E →+* E) J), γ ∈ (SI c).range ↔ bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ.1 ∈ lev.U.map (MulAut.conj (Y c).1).toMonoidHom) ∧ lev.Lb = baseLb E n ST ∧ lev.U = (levUQ hc n ST SG Q (Subgroup.pi Set.univ Hw) q).map (MulAut.conj b).toMonoidHom ∧ (∀ (x : lev.U) (z : levUQ hc n ST SG Q (Subgroup.pi Set.univ Hw) q), x.1 = b * z.1 * b⁻¹ → lev.chi x = ((levTyp lam).comp (Subgroup.inclusion (levUQ_le q _)) * (chiQ q _ σ₀)⁻¹ : levUQ hc n ST SG Q (Subgroup.pi Set.univ Hw) q →* ℂˣ) z) ∧ (∃ m : ℕ, 0 < m ∧ ∀ κ, lev.chi κ ^ m = 1) ∧ (∀ c, (Y c).1 = y c * b⁻¹) ∧ ∀ c a, (SI c a).1 = st c a := by
  first | exact @GlobalTheory.Mem.Col2.ChEx.chartQ_exists | exact GlobalTheory.Mem.Col2.ChEx.chartQ_exists | (intros; apply GlobalTheory.Mem.Col2.ChEx.chartQ_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteRepresentativesRowFiniteTypesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_representatives_rowFiniteTypes : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Inputs D → Pins R F cG → Holds R F → ∀ (y : Hd R.toRealDat), ∃ (Φ : Type) (rep : Φ → Formalism.L2.NG.FinTyp D.host.E D.R.r), Reps y F.lv2 rep := by
  first | exact @GlobalTheory.RowTypeReps.reps_exist | exact GlobalTheory.RowTypeReps.reps_exist | (intros; apply GlobalTheory.RowTypeReps.reps_exist <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIdentificationTypeRepresentativesClasses
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw.RepCls

theorem reps_classes : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (y : Hd R), ∀ (Φ : Type) (rep : Φ → Formalism.L2.NG.FinTyp D.host.E D.R.r), Reps y F rep → ∃ e : Φ ≃ principalLevelFrame.FTR R.θ y.PY (R.MY 0) (fun b => levS _ (R.βY 0) (R.dat0 (R.levR F b))) (fun b => levChi _ (R.βY 0) (R.dat0 (R.levR F b))) (fun _ => R.e0), ∀ π, (principalLevelFrame.rowRepR R.θ (e π)).Iso (rep π) ∧ (∀ b, y.prtE F b (principalLevelFrame.rowRepR R.θ (e π)) = y.prtE F b (rep π)) ∧ (∀ i, y.prtW F i (principalLevelFrame.rowRepR R.θ (e π)) = y.prtW F i (rep π)) ∧ ∃ b, y.prtE F b (rep π) ≠ ⊥ ∧ y.prtE F b (rep π) ≤ (y.C F).EEc b := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F y Φ rep hR
  let f : Φ → principalLevelFrame.FTR R.θ y.PY (R.MY 0) (fun b => levS _ (R.βY 0) (R.dat0 (R.levR F b)))
      (fun b => levChi _ (R.βY 0) (R.dat0 (R.levR F b))) (fun _ => R.e0) :=
    fun π => Quotient.mk _ ⟨rep π, hR.mem π⟩
  have hinj : Function.Injective f := by
    intro π π' h
    exact hR.inj π π' (Quotient.exact h)
  have hsurj : Function.Surjective f := by
    intro c
    obtain ⟨π, hπ⟩ := hR.all (Formalism.L2.Col.finTypRep _ c) (Formalism.L2.Col.finTypRep_mem _ c)
    refine ⟨π, ?_⟩
    rw [← Quotient.out_eq c]
    exact Quotient.sound hπ
  refine ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, fun π => ?_⟩
  have hiso : (principalLevelFrame.rowRepR R.θ (Equiv.ofBijective f ⟨hinj, hsurj⟩ π)).Iso (rep π) :=
    Formalism.L2.Col.finTypRep_mk_iso ⟨rep π, hR.mem π⟩
  refine ⟨hiso, fun b => ?_, fun i => ?_, ?_⟩
  · unfold Hd.prtE principalLevelFrame.isotE
    rw [principalLevelFrame.isotL_iso _ _ _ _ _ _ (principalLevelFrame.conjT_iso hiso)]
  · unfold Hd.prtW
    rw [principalLevelFrame.isotL_iso _ _ _ _ _ _ hiso]
  · obtain ⟨b, hb⟩ := hR.mem π
    refine ⟨b, ?_, ?_⟩
    · intro h
      apply hb
      unfold Hd.prtE at h
      rw [eq_bot_iff] at h ⊢
      intro x hx
      have h0 := h (Submodule.mem_map_of_mem hx)
      rw [Submodule.mem_bot] at h0 ⊢
      exact (LinearEquiv.map_eq_zero_iff _).1 h0
    · exact Submodule.map_mono inf_le_left

end GlobalTheory.Mem.R3.Rw.RepCls
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRationalFramesNearAdelicAtBadPrimesStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_frames_near_adelic_at_bad_primes : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (a : I.ι) (n : ℕ) (k : GL (Fin n) (AfE (I.rec7 l Z).host.F (I.rec7 l Z).host.E)), ∃ fb : SBof I a → GL (Fin n) (I.rec7 l Z).host.E, FrNear I l Z a k fb := by
  first | exact @GlobalTheory.Mem.Col2.AdT.frNear_exists | exact GlobalTheory.Mem.Col2.AdT.frNear_exists | (intros; apply GlobalTheory.Mem.Col2.AdT.frNear_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsLatticeAtClassIffTwistedPolynomialStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formsLattice_atClass_iff_twistedPolynomial : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → ∀ (u : B.Word) (μ : I.ι) (w : (I.rec7 l Z).what₂.places.Pl), LevFree Y u μ w → ∀ (i : ℕ) (hi : i < B.R.m) (eY : (I.chain l u μ).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi.le), I.IdY l Z u μ i hi.le eY → ∀ (c : (I.stp u μ i).Cl) (f : (I.chain l u μ).Y i → ℂ), (∃ P ∈ Formalism.L2.Forms.RatSpan (I.rec7 l Z) ((I.fm l u μ).lam i), ∀ z, f z = fnOf (gramC (gramN (I.rec7 l Z) i hi.le) (embT (I.rec7 l Z))) (shiftOf (lamTG (I.fm l u μ) i)) 1 P (eY z)) → ∀ Bm : GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E, Formalism.L2.Forms.IsLocBasis ((I.rec7 l Z).what₂.places.resChar w) (((I.stp u μ i).rep c).1.1.deco.1.N : Set (Sp B.fields.E (B.R.N i))) Bm → ((∃ P ∈ Formalism.L2.Forms.IntSpan (I.rec7 l Z) w ((I.fm l u μ).lam i), ∀ z, f z = fnOf (gramC (gramN (I.rec7 l Z) i hi.le) (embT (I.rec7 l Z))) (shiftOf (lamTG (I.fm l u μ) i)) (atInf (embT (I.rec7 l Z)) ((Bm⁻¹ : GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E) : Matrix (Fin ((I.rec7 l Z).R.N i)) (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E)) P (eY z)) ↔ ∃ v : ValQ O u μ i, evC O u μ i v = f ∧ ∀ J : KM.ColChoice ((I.rec7 l Z).R.N i) (nuD (I.rec7 l Z) u i), ‖prSC Pl O Bs u μ w i c v (MvPolynomial.map (Int.castRingHom _) (KM.nablaX ((I.rec7 l Z).R.N i) (nuD (I.rec7 l Z) u i) J))‖ ≤ 1) := by
  first | exact @GlobalTheory.LatSCore.latS_at_class | exact GlobalTheory.LatSCore.latS_at_class | (intros; apply GlobalTheory.LatSCore.latS_at_class <;> assumption)
end

