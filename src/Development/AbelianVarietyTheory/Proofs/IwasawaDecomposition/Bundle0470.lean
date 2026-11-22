import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0459
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0452
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0463
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.KppFwdPf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0460
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0453
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralSpanIffPadicWeylDualLattice
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0027
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.Bundle0001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0450
import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
import Formalism.UnipotentAdelicQuotients.Bundle0002
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0016
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0022
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.Bundle0007
import Formalism.LocalToGlobal.RatioJoints.CharacterProductEqOne
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0031
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Formalism.LocalToGlobal.Columns.Bundle0032
import Formalism.LocalToGlobal.Columns.Bundle0030
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0438
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0456
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0397
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0461
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0447
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0462
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodProjectorSmallestSpaceForms
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0005
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianZ0SymmetricFrameStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_z0_symmetric_frame : ∀ (D : D7) (X : HidaSetting D) (kv : Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal → ∀ (j : Fin D.R.r), hA X.B.I X.z0 (GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2) j) - (if j.val = D.R.rS + D.R.k then -1 else 0) ∈ GlobalTheory.Mem.SymChar.wInt X (D.naut.plGw kv.1 kv.2) := by
  first | exact @GlobalTheory.Mem.SymChar.ZPair.hA_z0_symVec | exact GlobalTheory.Mem.SymChar.ZPair.hA_z0_symVec | (intros; apply GlobalTheory.Mem.SymChar.ZPair.hA_z0_symVec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMemPlaceIdealSpanOfNeOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SymChar.EwZero

variable {D : D7}

open Formalism.L2.SG.Pf.KppRedW Formalism.L2.SG.Pf.AllRowsRedKerA Formalism.L2.SG.Pf.RowDictPf in

theorem Wq_le_wInt (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) :
    Wq X.B.I (wB X w) ≤ GlobalTheory.Mem.SymChar.wInt X w := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨a, ha, rfl⟩
  refine Submodule.subset_span ⟨a, ⟨RingOfIntegers.mapRingEquiv X.ιE a, ha, by simp⟩, rfl⟩

open Formalism.L2.SG.Pf.KppRedW Formalism.L2.SG.Pf.AllRowsRedKerA Formalism.L2.SG.Pf.RowDictPf in

theorem Lq_le_wLf (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) :
    Lq X.B.I (wB X w) ≤ wLf X w := by
  show Formalism.MainNotions.S.lamAf (F := X.B.I.F) (wLat0 X.B.I (wB X w)) ≤ Formalism.MainNotions.S.lamAf (F := X.B.I.F) (wLat X w)
  rw [wLat_eq]

theorem ew_mem_wInt (D : D7) (X : HidaSetting D) (kv : Σ k : Fin 2, D.nd.PlG k)
    (hw : ¬ GlobalTheory.Mem.SymFrame.EwAt X (D.naut.plGw kv.1 kv.2)) :
    X.ew ∈ GlobalTheory.Mem.SymChar.wInt X (D.naut.plGw kv.1 kv.2) := by
  obtain ⟨ob, h1, -⟩ := Formalism.L2.SG.Pf.KppFwdPf.ew_res X kv
  cases ob with
  | false =>
    simp only [Bool.false_eq_true, if_false, sub_zero] at h1
    exact Wq_le_wInt X _ h1
  | true =>
    simp only [if_true] at h1
    exfalso
    apply hw
    intro y hy
    have h2 : 1 - X.ew ∈ Formalism.L2.SG.Pf.KppRedW.Wq X.B.I (Formalism.L2.SG.Pf.RowDictPf.wB X (D.naut.plGw kv.1 kv.2)) := by
      have := neg_mem h1
      rwa [neg_sub] at this
    exact Lq_le_wLf X _ (Formalism.L2.SG.Pf.KppRedW.Wq_smul h2 hy)

end GlobalTheory.Mem.SymChar.EwZero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InModIffForallPlaceMemSpanModuloStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inMod_iff_forall_place_memSpanModulo : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (S : Set (VA X.B.I)), S ⊆ X.B.I.Lf → ∀ y ∈ X.B.I.Lf, (InMod X.B.I X.B.g S y ↔ ∀ w : HeightOneSpectrum (𝓞 D.host.E), ((X.B.g : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal → GlobalTheory.Mem.GroupLoc.ModW X w S y) := by
  first | exact @GlobalTheory.Mem.GroupLoc.Crt.inMod_iff_forall_modW | exact GlobalTheory.Mem.GroupLoc.Crt.inMod_iff_forall_modW | (intros; apply GlobalTheory.Mem.GroupLoc.Crt.inMod_iff_forall_modW <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralSpanIffPadicWeylDualLatticeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IntegralityCompare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralSpan_iff_padic_weylDualLattice : ∀ (D : D7) (Pl : Examples₂.EntPl D) (w : D.what₂.places.Pl) {n : ℕ} (lam : D.what₂.Tau → DomWeight n)
    (R : MvPolynomial (D.what₂.Tau × Fin n × Fin n) D.what₂.LL),
    MvPolynomial.map D.what₂.embLL R ∈ Formalism.L2.Forms.RatSpan D lam →
    (MvPolynomial.map D.what₂.embLL R ∈ Formalism.L2.Forms.IntSpan D w lam ↔
      polFun (MvPolynomial.map (Pl.iL w) R) ∈ WeylLatticeDuality.DelW (D.what₂.places.resChar w) D.what₂.Tau n (fun τ => (lam τ).natW)) := by
  first | exact @GlobalTheory.IntSpanCmp.intSpan_iff_delW | exact GlobalTheory.IntSpanCmp.intSpan_iff_delW | (intros; apply GlobalTheory.IntSpanCmp.intSpan_iff_delW <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDetLiftLocal
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.JointsTrue

open Formalism.L2 Formalism.L2.Host ReciprocityTheory.Neutral.Bridge.HCFR

set_option maxHeartbeats 1000000 in

theorem isDetLift_local (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Theta.AE D) (he : JoinChr.IsPlIdem D e P)
    (k : D.host.Eˣ) (y : Theta.AE D) (hy : Joints.IsRatioAt D e (k : D.host.E) y) (x : Herm.unitaryOneFiniteAdeles D.sp.cm)
    (hx : ((Matrix.GeneralLinearGroup.det (x : GL (Fin 1) (D.host.E ⊗[D.host.F] Herm.Af D.host.F)) :
        (D.host.E ⊗[D.host.F] Herm.Af D.host.F)ˣ) : D.host.E ⊗[D.host.F] Herm.Af D.host.F) = Joints.finE D y) :
    IsDetLift D.sp.cm x.1 (Neutral.B1.localIdele D.host.E P (Formalism.L2.Host.atFin P k)) := by
  let φ : Theta.AE D →+* AfE D.host.F D.host.E := Joints.finE D
  have hinc : ∀ a : D.host.E, φ (Theta.incA D a) = a ⊗ₜ[D.host.F] 1 := fun a => rfl
  have hc : ∀ z, φ (Theta.cA D z) = Formalism.UG.sigR D.sp.cm.sig _ (φ z) := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => rw [(Theta.cA D).map_zero, φ.map_zero, RingHom.map_zero]
    | tmul a b => rfl
    | add a b ha hb => rw [(Theta.cA D).map_add, φ.map_add, φ.map_add, ha, hb, RingHom.map_add]
  have h1 : (finAf D.host.F D.host.E (Neutral.B1.localIdele _ P (Formalism.L2.Host.atFin P k)) : AfE D.host.F D.host.E) = φ (JoinChr.locE D e k) := by
    rw [GlobalTheory.Core.Cls.JointsStd.finAf_localIdele (e := φ e) (by rw [← φ.map_mul, he.1]) (fun a ha => ?_) k, JoinChr.locE, φ.map_add,
      φ.map_mul, φ.map_sub, φ.map_one, hinc]
    rw [he.2.2 a ha, ← hinc, ← φ.map_mul]
    exact not_congr (GlobalTheory.HostAdeleIso.mem_intAE_iff_comm D _)
  have h2 := congrArg φ hy
  rw [φ.map_mul, hc, ← h1] at h2
  unfold IsDetLift h90
  rw [MonoidHom.div_apply, div_eq_iff_eq_mul]
  exact Units.ext (h2.symm.trans (by rw [Units.val_mul, hx]; rfl))

set_option maxHeartbeats 1000000 in

theorem jointsS_true : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (T : Formalism.L2.LinkedFamilyData ex), I.StdC l Z T.cols → I.StdDt l Z T.full.1.base.dt → T.n.cf = I.cf l Z → (∀ a, T.chrDt.eDt a = (QuotientGroup.mk a : DtQ B.host I.SQ)) → Nonempty (Formalism.L2.Host.DivisorCharacterCompatibility (I.rec7 l Z) T.n.cf ex.nch T.n.tp Y) → Formalism.L2.Theta.IsStdChar (I.rec7 l Z) T.theta.W.ψ (-1) → Formalism.L2.JointsS T := by
  intro B X I hOk hP l Z L hT Gi Gl K Y cX ex T hC hD hcf he hdiv hψ
  refine ⟨fun P e hi k y hy x hx => ?_, fun k => ?_, fun k v h a n hn ha => ?_, fun k v h ε hε c y hc => ?_, hdiv⟩
  · exact (hD x _ (isDetLift_local (I.rec7 l Z) P e hi k y hy x hx)).trans (he _).symm
  · rw [hcf, show (T.cols.forms (I.rec7 l Z).u₀).gl.piG = X.piG from (hC _).gl.piG]
    exact GlobalTheory.Core.Cls.JointsStd.piBar_std I hOk k
  · rw [hcf]
    exact GlobalTheory.Core.Cls.JointsStd.om_std I hOk l Z _ (hC _).gl k v h a n hn ha
  · have hy : algebraMap (I.rec7 l Z).host.F (v.adicCompletion (I.rec7 l Z).host.F) (y : (I.rec7 l Z).host.F) ∈
        v.adicCompletionIntegers (I.rec7 l Z).host.F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, valued_algebraMap]
      exact HeightOneSpectrum.valuation_le_one v y
    have e1 := GlobalTheory.Mem.TypePrimes.psiG_true I hOk hP l Z _ (hC (I.rec7 l Z).u₀).gl _ hψ k v h ε hε c y hc ⟨_, hy⟩ rfl
    unfold Joints.redV
    rw [dif_pos hy]
    exact e1

end GlobalTheory.Mem.JointsTrue

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsMatrixModPlaceInFamilyInvStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isMatrixModPlaceInFamily_inv : ∀ (D : D7) (X : HidaSetting D) (kv : Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal → ∀ (u : Fin D.R.r → VA X.B.I), (∀ i, u i ∈ X.B.I.Lf) → ∀ k ∈ X.B.I.Kset, ∀ N : GL (Fin D.R.r) (ZMod (D.host.g kv.1)), GlobalTheory.Mem.SymFrame.IsMatIn X (D.naut.plGw kv.1 kv.2) u k (N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) → GlobalTheory.Mem.SymFrame.IsMatIn X (D.naut.plGw kv.1 kv.2) u k⁻¹ ((N⁻¹ : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) := by
  first | exact @GlobalTheory.Mem.SymFrame.isMatIn_inv | exact GlobalTheory.Mem.SymFrame.isMatIn_inv | (intros; apply GlobalTheory.Mem.SymFrame.isMatIn_inv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPointOfDecoratedLatticeSplicedAtPlace
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.UG.P Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.Col2.Splice

theorem isPtOf_splice : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG Q Q0 Q1 : Finset (HeightOneSpectrum (𝓞 E))) (v : HeightOneSpectrum (𝓞 F)) (g0 h : GL (Fin n) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))) (p0 : DecoF E n ST SG Q0) (p1 : DecoF E n ST SG Q1) (q : DecoF E n ST SG Q), GlobalTheory.Mem.Col2.IsPtOf hc g0 p0 → GlobalTheory.Mem.Col2.IsPtOf hc h p1 → (∀ P ∈ Q, ¬ IsOver v P) → (∀ w ∈ SG, ¬ IsOver v w) → Deco.SameOff ST SG v q.deco.1 p1.deco.1 → (∀ P : HeightOneSpectrum (𝓞 E), IsOver v P → localization₂ P.asIdeal q.deco.1.N = localization₂ P.asIdeal p0.deco.1.N) → (∀ P : ST, IsOver v P.1 → q.deco.1.f P = p0.deco.1.f P) → (∀ P : Q, ∃ P' : Q1, P'.1 = P.1 ∧ p1.fr P' = q.fr P) → GlobalTheory.Mem.Col2.IsPtOf hc (h * rll_put n v (bc (prV (E := E) v) (h⁻¹ * g0))) q := by
  intro F E _ _ _ _ _ _ hc n _ ST SG Q Q0 Q1 v g0 h p0 p1 q h0 h1 hQ hSG hoff hN hf hfr
  obtain ⟨⟨hg0, hd0⟩, -⟩ := (ChTwRead.isPtOf_iff hc g0 p0).1 h0
  obtain ⟨⟨hh, hd1⟩, hfr1⟩ := (ChTwRead.isPtOf_iff hc h p1).1 h1
  set m := h * rll_put n v (bc (prV (E := E) v) (h⁻¹ * g0)) with hm
  have hv : bc (prV (E := E) v) m = bc (prV (E := E) v) g0 := by
    rw [hm, map_mul, rll_put_self, ← map_mul, mul_inv_cancel_left]
  have hne : ∀ P : HeightOneSpectrum (𝓞 E), ¬ IsOver v P → P.under (𝓞 F) ≠ v := by
    rintro P hP rfl
    exact hP rfl
  have hw : ∀ P : HeightOneSpectrum (𝓞 E), ¬ IsOver v P →
      bc (prV (E := E) (P.under (𝓞 F))) m = bc (prV (E := E) (P.under (𝓞 F))) h := by
    intro P hP
    rw [hm, map_mul, rll_put_ne n v _ (hne P hP), mul_one]
  have hmU : m ∈ UAd hc n :=
    mul_mem hh (rll_put_mem_UAd hc n v (afsplit_bc_mem hc.sig 1 v _ (mul_mem (inv_mem hh) hg0)))
  refine (ChTwRead.isPtOf_iff hc m q).2 ⟨⟨hmU, ?_⟩, fun P i j => ?_⟩
  · ext1
    · refine Formalism.L2.DIV.eq_of_forall_localized_eq fun P => ?_
      by_cases hP : IsOver v P
      · rw [hN P hP, hd0]
        exact (updn_mem_loc hP hv).symm
      · rw [hoff.N P hP, hd1]
        exact (updn_mem_loc (v := P.under (𝓞 F)) rfl (hw P hP)).symm
    · funext P
      by_cases hP : IsOver v P.1
      · rw [hf P hP, hd0]
        exact (updn_f_loc ST SG P hP hv).symm
      · rw [hoff.f P hP, hd1]
        exact (updn_f_loc ST SG (v := P.1.under (𝓞 F)) P rfl (hw P.1 hP)).symm
    · funext w
      have hP := hSG w.1 w.2
      rw [hoff.be w hP, hd1]
      exact (updn_be_loc ST SG (v := w.1.under (𝓞 F)) w rfl (hw w.1 hP)).symm
  · obtain ⟨⟨P1, hP1⟩, hP', e⟩ := hfr P
    have hPv := hQ P.1 P.2
    simp only at hP'
    subst hP'
    rw [← e, ← hfr1 ⟨_, hP1⟩ i j]
    refine ChTwRead.adAt_congr_prV P.1 ?_
    have := congrArg (fun g : GL (Fin n) (E ⊗[F] (P.1.under (𝓞 F)).adicCompletion F) =>
      g.val i j) (hw P.1 hPv)
    exact this

end GlobalTheory.Mem.Col2.Splice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProdLevelStdFrameTwoBlockUnipotentLevelStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isProdLevel_stdFrame_twoBlockUnipotentLevel : ∀ (D : D7) (n : ℕ) (hr : D.R.r ≤ n) (Pg Q : Finset (Pl D.host.E)) (ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) (chi xi : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), NG.IsProdLevel (stdJ (datV D n hr Pg Q (P0 Pg D.R.r ψ) chi xi)) := by
  first | exact @GlobalTheory.MtInProd.main | exact GlobalTheory.MtInProd.main | (intros; apply GlobalTheory.MtInProd.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelChoicesStandardTrueColumnsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelChoices_standard_trueColumns : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), I.StdKerTie l Z t → ex.errX.piT = X.piT → t.ChTie ∧ t.MemSideU ∧ t.MtTwTie ∧ ∀ a, (t.cst a).sharp = true := by
  first | exact @GlobalTheory.Mem.Col2.TC.k_pins_tie | exact GlobalTheory.Mem.Col2.TC.k_pins_tie | (intros; apply GlobalTheory.Mem.Col2.TC.k_pins_tie <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelEntriesCompatibleTrueColumnsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelEntries_compatible_trueColumns : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (E : KerEnt (I.rec7 l Z) Y ex.tw), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → EntOk E O → (∀ u w h, ThAtServed (ex.ker u w h) E) → ∃ t : KerEntTied ex, I.StdKerTie l Z t ∧ t.O = O ∧ t.Adapted ∧ t.TopPinned := by
  first | exact @GlobalTheory.Mem.Col2.TC.kerEntTied_true | exact GlobalTheory.Mem.Col2.TC.kerEntTied_true | (intros; apply GlobalTheory.Mem.Col2.TC.kerEntTied_true <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LastThetaStepKeepsFaceLevelStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastThetaStep_keeps_faceLevel : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Pins R F cG → Holds R F → GlobalTheory.Mem.R3.DTheta.TopLev R.toRealDat F.lv2  := by
  first | exact @GlobalTheory.Mem.R3.DTheta.topLev_holds | exact GlobalTheory.Mem.R3.DTheta.topLev_holds | (intros; apply GlobalTheory.Mem.R3.DTheta.topLev_holds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LayeredAutomorphicDataExistsOfTwoPassesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.layeredAutomorphicData_exists_of_twoPasses : (∀ D : D7, Formalism.L2.Theta.VolTieG D → StandardLattice.VolumeEqMass₂ D) → ∀ (KP : GroupRetwisting.BaseP) (Q Q' : V4.Slot), GroupRetwisting.BaseCond KP → GroupRetwisting.FirstG KP Q → GroupRetwisting.ExportF KP Q → GroupRetwisting.SecondG KP Q Q' → RecAtG (fun K D Y => GroupRetwisting.FromCoreAt Q' K D Y ∧ DQ.TupUsedAt D ∧ DQ.TwAllAt D Y.nch Y.xd ∧ DQ.MtStableAt D) := by
  first | exact @GlobalTheory.Mem.Top.GroupRetwisting.recAtG_of_two_passes | exact GlobalTheory.Mem.Top.GroupRetwisting.recAtG_of_two_passes | (intros; apply GlobalTheory.Mem.Top.GroupRetwisting.recAtG_of_two_passes <;> assumption)
end

