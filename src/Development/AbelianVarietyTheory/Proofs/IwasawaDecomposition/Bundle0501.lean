import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0492
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0279
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodProjectorSmallestSpaceForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0487
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.LocalRingCardinality.SpanPowerMembership.TwCore
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JetMapFrameEqApplyQAdaptedCoordinates
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0027
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.Bundle0001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008
import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle0007
import Formalism.LocalRingCardinality.FactDelDualNabla
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0475
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0471
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0496
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelElementAtBadPrimesIntegralAndNear
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0493
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0397
import Formalism.UnipotentAdelicQuotients.Bundle0002
import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0452
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0453
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimPartsAtIffBadAndOff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0470
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0483

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ISupIndepFiniteTypeComponentsThetaLiftFormsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iSupIndep_finiteTypeComponents_thetaLiftForms : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ i : Fin D.R.m, iSupIndep (fun σ : D.what₂.FT => D.what₂.isot ((i : ℕ) + 1) σ) := by
  first | exact @GlobalTheory.Mem.R3.IsotIndep.isot_iSupIndep | exact GlobalTheory.Mem.R3.IsotIndep.isot_iSupIndep | (intros; apply GlobalTheory.Mem.R3.IsotIndep.isot_iSupIndep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerThetaStepsPreserveFaceLevelStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.innerThetaSteps_preserve_faceLevel : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Pins R F cG → Holds R F → GlobalTheory.Mem.R3.DTheta.StepLev R.toRealDat F.lv2 := by
  first | exact @GlobalTheory.Mem.R3.DTheta.stepLev_holds | exact GlobalTheory.Mem.R3.DTheta.stepLev_holds | (intros; apply GlobalTheory.Mem.R3.DTheta.stepLev_holds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InstBack
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Df GlobalTheory.Mem.Db NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Db.DivTr

section GyGen

variable {D : D7} (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ)

@[reducible] def ledBack (L : SizeData₂ (setDiv D N h)) : SizeData₂ D := { L with }

@[reducible] def instBack {L : SizeData₂ (setDiv D N h)} (X : G.Inst (setDiv D N h) L) : G.Inst D (ledBack N h L) := { X with }

end GyGen

variable {B : Base} {f : Fr B.toPre} {T : TwDat B}
variable (w : ColW B f T) (Z : w.Lt) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ)

def kerTr {t : ColT w Z} {Gy : G.LatInst (w.D Z)} (ker : KerFam (w.D Z) t.Gt t.cmp (w.tw Z) Gy) :
    KerFam (w.D (setDivZ Z N h)) (colTTr w Z N h t).Gt (colTTr w Z N h t).cmp (w.tw (setDivZ Z N h)) (latTr (D := w.D Z) N h Gy) :=
  fun u v g => { ker u v g with }

set_option maxHeartbeats 4000000 in

def ktTr {t : ColT w Z} {X : DivX (w.D Z)} {Gy : G.LatInst (w.D Z)} {ker : KerFam (w.D Z) t.Gt t.cmp (w.tw Z) Gy}
    (kt : KerT t X Gy ker) :
    KerT (colTTr w Z N h t) (divTr (D := w.D Z) N h X) (latTr (D := w.D Z) N h Gy) (kerTr w Z N h ker) :=
  { kt with
    O := fun u a => { kt.O u a with }
    E := { kt.E with }
    std := { kt.std with }
    ok := ⟨⟨fun u μ v hv => { (kt.ok.1.choose u μ v hv) with }, fun u μ v hv => kt.ok.1.choose_spec u μ v hv⟩, kt.ok.2⟩ }

set_option maxHeartbeats 8000000 in

theorem entC_tr {t : ColT w Z} {X : DivX (w.D Z)} {Gy : G.LatInst (w.D Z)} {ker : KerFam (w.D Z) t.Gt t.cmp (w.tw Z) Gy}
    (kt : KerT t X Gy ker)
    (H : ∃ (Pl : Examples₂.EntPl (w.D Z)) (Bs : Formalism.L2.Ker.PlaceMatrixFamily (w.D Z)) (hh : Formalism.L2.Ker.KerEntHyp Pl kt.O Bs X (w.tw Z)),
      kt.E = Formalism.L2.Ker.kerEntC Pl kt.O Bs hh) :
    ∃ (Pl : Examples₂.EntPl (w.D (setDivZ Z N h))) (Bs : Formalism.L2.Ker.PlaceMatrixFamily (w.D (setDivZ Z N h)))
      (hh : Formalism.L2.Ker.KerEntHyp Pl (ktTr w Z N h kt).O Bs (divTr (D := w.D Z) N h X) (w.tw (setDivZ Z N h))),
      (ktTr w Z N h kt).E = Formalism.L2.Ker.kerEntC Pl (ktTr w Z N h kt).O Bs hh := by
  obtain ⟨Pl, Bs, hh, e⟩ := H
  exact ⟨{ Pl with }, Bs, { hh with },
    congrArg (fun E => ({ E with } : Formalism.BasicNotions.KerEnt (w.D (setDivZ Z N h)) (divTr (D := w.D Z) N h X) (w.tw (setDivZ Z N h)))) e⟩

end GlobalTheory.Mem.Db.DivTr

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JetMapFrameEqApplyQAdaptedCoordinatesStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jetMap_frame_eq_applyQ_adapted_coordinates : ∀ (D : D7) {p : ℕ} [Fact p.Prime] (N0 N1 : ℕ) (hN : N0 ≤ N1)
    (T : MvPowerSeries (D.what₂.Tau × Fin N1 × Fin N0) ℂ_[p]) (s : D.what₂.Tau → ℂ_[p])
    (B : D.what₂.Tau → Matrix (Fin N0) (Fin N0) ℂ_[p]) (B' : D.what₂.Tau → Matrix (Fin N1) (Fin N1) ℂ_[p])
    (hB : ∀ τ, (B τ).det ≠ 0) (P : MvPolynomial (GL3Theta.FrV D N0) ℂ_[p]) (y' : D.what₂.Tau → Matrix (Fin N1) (Fin N1) ℂ_[p]), MvPolynomial.eval (fun k : GL3Theta.FrV D N1 => (B' k.1 * y' k.1) k.2.1 k.2.2)
      (jetMap (fun m => (m.prod fun k n => s k.1 ^ n) * (m.prod fun _ n => (n.factorial : ℂ_[p])) * MvPowerSeries.coeff m T)
        (fun _ => 0) P) =
    GL3Columns.applyQ p N0 N1
      (atLin (fun (k : D.what₂.Tau × Fin N1 × Fin N0) (j : (Bool × HH D) × Fin N0 × Fin N1) =>
          if tauPl D j.1 = k.1 then 1 * s k.1 * B' k.1 k.2.1 j.2.2 * (B k.1)⁻¹ j.2.1 k.2.2 else 0)
        (fun j => MvPowerSeries.X j) T)
      (MvPolynomial.aeval (fun k : GL3Theta.FrV D N0 => ∑ a : Fin N0,
          MvPolynomial.C (B k.1 k.2.1 a) * MvPolynomial.X ((Equiv.ofBijective (tauPl D) (tauPl_bij D)).symm k.1, a, (k.2.2 : ℕ))) P)
      (fun z => GL3Columns.colsOf (y' (tauPl D z))) := by
  first | exact @GlobalTheory.JetChain.jetMap_frame_eq_applyQ | exact GlobalTheory.JetChain.jetMap_frame_eq_applyQ | (intros; apply GlobalTheory.JetChain.jetMap_frame_eq_applyQ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JetMapIdentityTransportComplexToPadicStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jetMap_identity_transport_complex_to_padic : ∀ (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {a b : ℕ}
    (J : (DVar D.what₂.Tau a b →₀ ℕ) → ℂ) (J' : (DVar D.what₂.Tau a b →₀ ℕ) → ℂ_[p]) (n : D.what₂.Tau → ℕ) (r : Qbar)
    (A : MvPolynomial (GL3Theta.FrV D b) Qbar) (P : MvPolynomial (GL3Theta.FrV D a) Qbar)
    (hJ : ∀ m : DVar D.what₂.Tau a b →₀ ℕ, (∀ τ, ∑ β, ∑ α, m (τ, β, α) = n τ) → ∃ x : Qbar, (x : ℂ) = J m ∧ lam x = J' m)
    (hP : ∀ e ∈ P.support, ∀ τ, ∑ α, ∑ s, e (τ, α, s) = n τ)
    (h : MvPolynomial.map (algebraMap Qbar ℂ) A = MvPolynomial.C (r : ℂ) * jetMap J (fun _ => 0) (MvPolynomial.map (algebraMap Qbar ℂ) P)), MvPolynomial.map lam A = MvPolynomial.C (lam r) * jetMap J' (fun _ => 0) (MvPolynomial.map lam P) := by
  first | exact @GlobalTheory.jetMapTransport | exact GlobalTheory.jetMapTransport | (intros; apply GlobalTheory.jetMapTransport <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelFormComplexPolynomialIdentityStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelForm_complex_polynomial_identity : ∀ (D : D7) (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)) (u : D.what₂.Word) (μ : D.what₂.Tup) (i : ℕ) (hi : i < D.R.m)
    (hU : UnfIsAll (O u μ) i) (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)) (v : ValQ O u μ i) (v' : ValQ O u μ (i + 1))
    (h : evC O u μ (i + 1) v' = (D.chTw u μ).Kmap i c c' (evC O u μ i v)), MvPolynomial.map D.what₂.embLL (secC O u μ (i + 1) v' : MvPolynomial (GL3Theta.FrV D (D.R.N (i + 1))) D.what₂.LL) =
      MvPolynomial.C (((GL3Theta.rhoOf D (O u μ).mt i ((O u μ).dt i c) : ℂˣ) : ℂ) * ((GL3Theta.rhoOf' D (O u μ).mt i ((O u μ).dt (i + 1) c') : ℂˣ) : ℂ)) *
        jetMap (jetC (O u μ).dgen ((O u μ).Th i c c')) (fun _ => 0)
          (MvPolynomial.map D.what₂.embLL (srcPol u μ i (secC O u μ i v : MvPolynomial (GL3Theta.FrV D (D.R.N i)) D.what₂.LL))) := by
  first | exact @GlobalTheory.Mem.KerForm.complex_kform | exact GlobalTheory.Mem.KerForm.complex_kform | (intros; apply GlobalTheory.Mem.KerForm.complex_kform <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LastStepCharacterInverseTypeAtLifts
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT

theorem chr_mul_prod_top_core {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (a : I.ι)
    (Λ : LevFam B.fields.E B.fields.K (B.R.N B.R.m) (B.primes X).vGs)
    (hΛ : ∀ w, Λ w = levDiag (Nat.sub_le _ 1) (rowTyG I.Ch (rPsymF I.Ch) w))
    (Θ : LevQFam B.fields.E B.fields.K (B.R.N B.R.m) (I.Q a))
    (hΘ : ∀ Q, Θ Q = levCong (N_m_succ B.R) Q.1 (topDep B.R (I.cst a).M)
      (rowTyQ B.R (I.tup a : Chr B.fields.F B.fields.E B.fields.K) (I.Q a) Q))
    (x : Λ.grp) (y : Θ.grp)
    (g g' : SBof I a → Sp B.fields.E (B.R.N B.R.m) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N B.R.m)) (z : SBof I a → B.fields.K)
    (H : ∀ P, GlobalTheory.TwU.TopLev (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) B.R.m P (g P) (z P) ∧
      (g' P ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N B.R.m) P.1 ∧
        (∀ h : P.1 ∈ (B.primes X).vGs, ∀ v ∈ stdAt B.fields.E (B.R.N B.R.m) P.1,
          redV P.1 (g' P v) = ((x.1 ⟨P.1, h⟩)⁻¹).1.mulVec (redV P.1 v)) ∧
        ∀ h : P.1 ∈ I.Q a, g' P = ((y.1 ⟨P.1, h⟩)⁻¹).1) ∧
      CongE P.1 (GlobalTheory.TwU.topDep I.sel (I.tup a) (I.cst a) P) (g P) (g' P)) :
    (((Λ.chr x * Θ.chr y : B.fields.Kˣ) : B.fields.K)) * ∏ P, z P = 1 := by
  classical
  have hd : Disjoint (B.primes X).vGs (I.Q a) :=
    Finset.disjoint_left.2 fun P h1 h2 => Q_notMem_of_ok hOk a P h2 h1
  have e2 : ∏ P, z P = (∏ w : (B.primes X).vGs, z ⟨w.1, Finset.mem_union_left _ w.2⟩) *
      ∏ Q : I.Q a, z ⟨Q.1, Finset.mem_union_right _ Q.2⟩ := by
    rw [← Fintype.prod_equiv (Equiv.Finset.union _ _ hd) _ _ (fun _ => rfl), Fintype.prod_sum_type]
    rfl
  rw [e2, LevFam.chr_apply, levQ_chr_apply, Units.val_mul, Units.coe_prod, Units.coe_prod]
  have hG : ∀ w : (B.primes X).vGs, (((Λ w).lam ⟨x.1 w, x.2 w (Set.mem_univ w)⟩ : B.fields.Kˣ) : B.fields.K) *
      z ⟨w.1, Finset.mem_union_left _ w.2⟩ = 1 := by
    intro w
    obtain ⟨⟨g'', hg''m, hpr, -, hz⟩, ⟨hg'G, hred, -⟩, hc⟩ := H ⟨w.1, Finset.mem_union_left _ w.2⟩
    have key : ∀ (l : Lev (𝓞 B.fields.E ⧸ w.1.asIdeal) B.fields.K (B.R.N B.R.m)),
        l = levDiag (Nat.sub_le _ 1) (rowTyG I.Ch (rPsymF I.Ch) w) → ∀ A (hA : A ∈ l.H),
        ∃ h0, ∃ hh0 : h0 ∈ (rowTyG I.Ch (rPsymF I.Ch) w).H, A = diagEmb _ (Nat.sub_le (B.R.N B.R.m) 1) h0 ∧
          l.lam ⟨A, hA⟩ = (rowTyG I.Ch (rPsymF I.Ch) w).lam ⟨h0, hh0⟩ := by
      intro l hl A hA
      subst hl
      obtain ⟨h0, hh0, rfl⟩ := hA
      exact ⟨h0, hh0, rfl, levDiag_lam _ _ rfl _ hh0⟩
    obtain ⟨h0, hh0, eA, elam⟩ := key _ (hΛ w) _ (x.2 w (Set.mem_univ w))
    rw [elam]
    have hmem : g'' ∈ LocE.JGsym w.1 (qOf w.1) B.R.k B.R.rS B.R.r B.R.t (B.R.N B.R.m - 1) 0 := by
      have h1 := hg''m
      unfold GlobalTheory.TwU.rowLevTop at h1
      rwa [if_pos w.2, hOk.sharp a, if_pos rfl] at h1
    have hz' : z ⟨w.1, Finset.mem_union_left _ w.2⟩ = LocE.lamGBS (qOf w.1) (psi0P I.Ch w.1) (chiP I.Ch w.1)
        B.R.k B.R.r B.R.t B.R.m (B.R.N B.R.m - 1) 0 g''.toLinearMap := by
      rw [hz]
      unfold GlobalTheory.TwU.rowChrTop
      rw [if_pos w.2, hOk.sharp a, if_pos rfl]
    have eA' : x.1 ⟨w.1, w.2⟩ = diagEmb _ (Nat.sub_le (B.R.N B.R.m) 1) h0 := eA
    have hred' : ∀ v ∈ stdAt B.fields.E (B.R.N B.R.m) w.1, redV w.1 (g' ⟨w.1, Finset.mem_union_left _ w.2⟩ v) =
        ((diagEmb (𝓞 B.fields.E ⧸ w.1.asIdeal) (Nat.sub_le (B.R.N B.R.m) 1) h0)⁻¹ : GL (Fin (B.R.N B.R.m)) _).1.mulVec (redV w.1 v) := by
      intro v hv
      rw [hred w.2 v hv, eA']
    have hc' : CongE w.1 1 (g ⟨w.1, Finset.mem_union_left _ w.2⟩) (g' ⟨w.1, Finset.mem_union_left _ w.2⟩) := by
      have h1 := hc
      unfold GlobalTheory.TwU.topDep at h1
      rwa [if_pos w.2] at h1
    rw [mul_comm, hz']
    exact GlobalTheory.T.typePrime_rowType_topRestriction_mul_levelChar_eq_one I.Ch w h0 hh0 _ _ g'' hmem hpr hg'G hred' hc'
  have hQ : ∀ Q : I.Q a, (((Θ Q).lam ⟨y.1 Q, y.2 Q (Set.mem_univ Q)⟩ : B.fields.Kˣ) : B.fields.K) *
      z ⟨Q.1, Finset.mem_union_right _ Q.2⟩ = 1 := by
    intro Q
    obtain ⟨⟨g'', hg''m, hpr, -, hz⟩, ⟨-, -, hgy⟩, hc⟩ := H ⟨Q.1, Finset.mem_union_right _ Q.2⟩
    have hnot : Q.1 ∉ (B.primes X).vGs := Q_notMem_of_ok hOk a Q.1 Q.2
    have key : ∀ (l : LevI B.fields.E B.fields.K (B.R.N B.R.m) Q.1),
        l = levCong (N_m_succ B.R) Q.1 (topDep B.R (I.cst a).M) (rowTyQ B.R (I.tup a : Chr B.fields.F B.fields.E B.fields.K) (I.Q a) Q) →
        ∀ k (hk : k ∈ l.H), ∃ hk' : k ∈ (levCong (N_m_succ B.R) Q.1 (topDep B.R (I.cst a).M)
          (rowTyQ B.R (I.tup a : Chr B.fields.F B.fields.E B.fields.K) (I.Q a) Q)).H,
          l.lam ⟨k, hk⟩ = (levCong (N_m_succ B.R) Q.1 (topDep B.R (I.cst a).M)
            (rowTyQ B.R (I.tup a : Chr B.fields.F B.fields.E B.fields.K) (I.Q a) Q)).lam ⟨k, hk'⟩ := by
      intro l hl k hk
      subst hl
      exact ⟨hk, rfl⟩
    obtain ⟨hk', elam⟩ := key _ (hΘ Q) _ (y.2 Q (Set.mem_univ Q))
    rw [elam]
    have hmem : g'' ∈ LocE.JQ Q.1 (qOf Q.1) B.R.r (B.R.N B.R.m - 1) 0 := by
      have h1 := hg''m
      unfold GlobalTheory.TwU.rowLevTop at h1
      rwa [if_neg hnot] at h1
    have hz' : z ⟨Q.1, Finset.mem_union_right _ Q.2⟩ = LocE.lamQB (resChar (I.tup a : Chr B.fields.F B.fields.E B.fields.K) Q.1)
        B.R.r (B.R.N B.R.m - 1) g''.toLinearMap := by
      rw [hz]
      unfold GlobalTheory.TwU.rowChrTop
      rw [if_neg hnot]
    have hc' : CongE Q.1 (2 * (I.cst a).M) (g ⟨Q.1, Finset.mem_union_right _ Q.2⟩) ((y.1 Q)⁻¹).1 := by
      have h1 := hc
      unfold GlobalTheory.TwU.topDep at h1
      rw [if_neg hnot, hgy Q.2] at h1
      exact h1
    rw [mul_comm, hz']
    exact GlobalTheory.T.twistPrime_rowType_topRestriction_mul_levelChar_eq_one (I.tup a : Chr B.fields.F B.fields.E B.fields.K) (I.Q a) Q _ _ (hOk.idx_ok a).cst_ok.M_pos (y.1 Q) hk' _ g'' hmem hpr hc'
  calc _ = (∏ w : (B.primes X).vGs, (((Λ w).lam ⟨x.1 w, x.2 w (Set.mem_univ w)⟩ : B.fields.Kˣ) : B.fields.K) *
        z ⟨w.1, Finset.mem_union_left _ w.2⟩) * ∏ Q : I.Q a, (((Θ Q).lam ⟨y.1 Q, y.2 Q (Set.mem_univ Q)⟩ : B.fields.Kˣ) : B.fields.K) *
      z ⟨Q.1, Finset.mem_union_right _ Q.2⟩ := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]; ring
    _ = 1 := by
        rw [Finset.prod_eq_one fun w _ => hG w, Finset.prod_eq_one fun Q _ => hQ Q, one_mul]

theorem chr_mul_prod_topVal : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ), i = B.R.m → ∀ (b : (I.stp u a i).β) (κ : (I.stp u a i).G b) (g g' : SBof I a → Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) (z : SBof I a → B.fields.K), (∀ P, GlobalTheory.TwU.TopLev (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) i P (g P) (z P) ∧ LiftsInv I κ P (g' P) ∧ CongE P.1 (GlobalTheory.TwU.topDep I.sel (I.tup a) (I.cst a) P) (g P) (g' P)) → (((I.stp u a i).chr b κ : B.fields.Kˣ) : B.fields.K) * ∏ P, z P = 1 := by
  intro B X I hOk u a i hi b κ g g' z H
  subst hi
  rcases b with ⟨_ | b1, hb⟩
  swap
  · exact absurd (hb.1 rfl) (lt_irrefl _)
  exact chr_mul_prod_top_core I hOk a _ (fun w => congrFun (topLevAt_levG_m I.Ch I.sel (I.tup a) I.Ps _) w) _
    (fun Q => congrFun (topLevAt_levQ_m I.Ch I.sel (I.tup a) I.Ps _) Q) κ.2.1 κ.2.2 g g' z H

end GlobalTheory.Mem.Col2.AdT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelElementAtBadPrimesIntegralAndNearStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelElement_at_bad_primes_integral_and_near : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : Charts I l Z u a i hi bad chOf) (k : Ch → GA B (B.R.N i)), ReadsAt I l Z K k → ∀ (c : (I.stp u a i).Cl) (x : GA B (B.R.N i)) (κ' : (I.stp u a i).G c.1), (I.stp u a i).gam c.1 κ' = 1 → PtOf ((show GA B (B.R.N i) from ((K (chOf c)).y ⟨c, rfl⟩).1) * x * k (chOf c)) ((I.stp u a i).act c.1 κ' ((I.stp u a i).rep c)).1.1 → ∀ P : SBof I a, (∀ r s, IntAtA (F := B.host.F) (show HeightOneSpectrum (𝓞 B.host.E) from GlobalTheory.TwU.seamP (sm I l Z) P.1) ((((k (chOf c))⁻¹ * x * k (chOf c) : GA B (B.R.N i)) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (AfE B.host.F B.host.E)) r s)) ∧ (∀ r s, IntAtA (F := B.host.F) (show HeightOneSpectrum (𝓞 B.host.E) from GlobalTheory.TwU.seamP (sm I l Z) P.1) (((((k (chOf c))⁻¹ * x * k (chOf c))⁻¹ : GA B (B.R.N i)) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (AfE B.host.F B.host.E)) r s)) ∧ ∀ g : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i), LiftsInv I κ' P g → GlobalTheory.TwU.NearAt (show HeightOneSpectrum (𝓞 B.host.E) from GlobalTheory.TwU.seamP (sm I l Z) P.1) ((I.cst a).D P) ((k (chOf c))⁻¹ * x * k (chOf c)) (GlobalTheory.TwU.seamGL (sm I l Z) g) := by
  first | exact @GlobalTheory.Mem.Col2.AdT.ReadBad.main | exact GlobalTheory.Mem.Col2.AdT.ReadBad.main | (intros; apply GlobalTheory.Mem.Col2.AdT.ReadBad.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelUnipotentGenericCharTypePlaceStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelUnipotent_genericChar_typePlace : ∀ (D : D7) (T : Type) (L : LevCh D T) (μ0 : T), L.Is μ0 → (∀ PP, PP ∈ L.Pg ↔ ∃ k v, PP = D.naut.plGw k v) → ∀ (i : Fin D.R.m) (t : T) (hr : D.R.r ≤ D.R.nV) (ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ), IsGenericPsi L.Pg ψ → ∀ s : ReciprocityTheory.Aut.SplitPlace D.host.E, s.w ∈ L.Pg → ∃ (ψ₀ : AddChar (s.v.adicCompletion (maximalRealSubfield D.host.E)) ℂ) (ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ), NG.IsPsi0 s ψ₀ ∧ NG.IsCompAt (L.C.mu0 i * L.xiH t) s ξ ∧ NG.LevelUni (stdJ (datV D D.R.nV hr L.Pg (L.Q t) (P0 L.Pg D.R.r ψ) (L.chi ((i : ℕ) + 1)) (L.xiR t))) (stdX (datV D D.R.nV hr L.Pg (L.Q t) (P0 L.Pg D.R.r ψ) (L.chi ((i : ℕ) + 1)) (L.xiR t))) s D.R.r ψ₀ ξ := by
  first | exact @GlobalTheory.TypeLevelUni.levelUni_typePlace | exact GlobalTheory.TypeLevelUni.levelUni_typePlace | (intros; apply GlobalTheory.TypeLevelUni.levelUni_typePlace <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalBasisAndEmbeddedBasisDifferByUnimodularInteStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localBasis_and_embeddedBasis_differ_by_unimodular_integral : ∀ (D : D7) {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (Bm : GL (Fin N) D.host.E) (M : Matrix (Fin N) (Fin N) ℂ_[p]), Formalism.L2.Forms.IsLocBasis p (L : Set (Fin N → D.host.E)) Bm → GL3Columns.BasR D lam τ L M → ∃ g : Matrix (Fin N) (Fin N) ℂ_[p], (∀ a b, ‖g a b‖ ≤ 1) ∧ ‖g.det‖ = 1 ∧ M = (Bm : Matrix (Fin N) (Fin N) D.host.E).map (TaylorLogMetric.tauEmb D lam τ) * g := by
  first | exact @GlobalTheory.LocBasisBasR.main | exact GlobalTheory.LocBasisBasR.main | (intros; apply GlobalTheory.LocBasisBasR.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalGroupElementEqLevelComponentBadPrime
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT.LocSplice

theorem adAt_eq_of_prV {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (P : HeightOneSpectrum (𝓞 E)) {z z' : AfE F E}
    (h : Formalism.UG.prV (E := E) (P.under (𝓞 F)) z = Formalism.UG.prV (E := E) (P.under (𝓞 F)) z') :
    adAt F P z = adAt F P z' := by
  set v := P.under (𝓞 F)
  have h3 : adAt F P (Formalism.UG.P.afsplitEps E v) = 1 :=
    GlobalTheory.Mem.Col2.FullDt.adAt_eq_one_of_prV P (Formalism.UG.P.afsplit_prV_eps v)
  have e : ∀ w : AfE F E, adAt F P w =
      adAt F P (Formalism.UG.P.afsplitIE v (Formalism.UG.prV (E := E) v w)) := fun w => by
    rw [Formalism.UG.P.afsplit_decomp, map_mul, h3, one_mul]
  rw [e z, e z', h]

theorem map_conj_inv_mul {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {n : ℕ} (w w' A C : GL (Fin n) R)
    (h : ∀ r s, φ (w.1 r s) = φ (w'.1 r s)) (r s : Fin n) :
    φ ((((A⁻¹ * w * A)⁻¹ * C : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) r s) =
      φ ((((A⁻¹ * w' * A)⁻¹ * C : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) r s) := by
  have hΦ : Matrix.GeneralLinearGroup.map (n := Fin n) φ w = Matrix.GeneralLinearGroup.map φ w' := by
    apply Units.ext
    exact Matrix.ext h
  have h2 : Matrix.GeneralLinearGroup.map (n := Fin n) φ ((A⁻¹ * w * A)⁻¹ * C) =
      Matrix.GeneralLinearGroup.map φ ((A⁻¹ * w' * A)⁻¹ * C) := by
    simp only [map_mul, map_inv, hΦ]
  exact congrArg (fun z : GL (Fin n) S => (z : Matrix (Fin n) (Fin n) S) r s) h2

theorem main : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (a : I.ι) (T i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) T (I.rec7 l Z).R.f bad) (P : SBof I a) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) → ∀ κ ∈ UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), bc (prV (E := (I.rec7 l Z).host.E) v) κ ∈ S.Uloc v → ∃ x ∈ S.U, ∀ (fb : SBof I a → GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E) (dep : SBof I a → ℕ) (g : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)), GlobalTheory.TwU.InFrame (i := i) (sm I l Z) fb dep P x g → GlobalTheory.TwU.InFrame (i := i) (sm I l Z) fb dep P κ g := by
  intro B X I hOk l Z a T i hi bad S P v hv κ hκ hloc
  refine ⟨Formalism.UG.P.afsplitU v (bc (prV (E := (I.rec7 l Z).host.E) v) κ) 1, ?_, ?_⟩
  · rw [S.U_eq]
    refine ⟨Formalism.UG.P.afsplitU_mem v _ _ _ _ (Formalism.UG.P.afsplit_bc_mem _ _ v κ hκ) (one_mem _), fun w => ?_⟩
    by_cases hw : w = v
    · subst hw
      rw [Formalism.UG.P.afsplit_right1]
      exact hloc
    · have h1 : bc (prV (E := (I.rec7 l Z).host.E) w) (Formalism.UG.P.afsplitU v (bc (prV (E := (I.rec7 l Z).host.E) v) κ) 1) = 1 := by
        apply Units.ext
        rw [Formalism.UG.P.afsplit_coe_bc_prV, Formalism.UG.P.afsplitU_coe, Formalism.UG.P.afsplitC_prV_ne v w hw]
        simp
      rw [h1]
      exact one_mem _
  · intro fb dep g hx
    have hseam := (GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion I hOk l Z a 0 0 P 1).1
    have hdict := fun z => (GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion I hOk l Z a ((I.rec7 l Z).R.N i) (dep P) P z).2.2
    have hvP : P.1.under (𝓞 B.host.F) = v := by
      apply HeightOneSpectrum.ext
      rw [hseam] at hv
      exact hv.symm
    unfold GlobalTheory.TwU.InFrame GlobalTheory.TwU.NearAt at hx ⊢
    have h1 := (hdict _).1 hx
    refine (hdict _).2 (fun r s => ?_)
    have h2 := h1 r s
    convert h2 using 3
    refine (map_conj_inv_mul _ _ _ _ _ (fun r s => ?_) r s).symm
    · apply adAt_eq_of_prV
      rw [hvP]
      exact congrFun (congrFun (Formalism.UG.P.afsplitC_prV (E := (I.rec7 l Z).host.E) v _ _) r) s

end GlobalTheory.Mem.Col2.AdT.LocSplice
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemDeeperLevelIffMatricesModPlaceSymmetric
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.GroupLoc

theorem membership_iff_unipSym : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal) → ∀ k ∈ X.B.I.Kset, ∀ Ns : G0g D.nd, (∀ kv : (Σ k : Fin 2, D.nd.PlG k), GlobalTheory.Mem.SymFrame.IsMatIn X (D.naut.plGw kv.1 kv.2) (GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2)) k (((Ns kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))))) → (k ∈ X.K2 ↔ ∀ kv : (Σ k : Fin 2, D.nd.PlG k), Ns kv ∈ unipSym (ZMod (D.host.g kv.1)) D.R.r D.R.rS D.R.k) := by
  intro D X h hE hg k hk Ns hNs
  have hK2 : k ∈ X.K2 ↔ K2cong X.B.I X.B.g X.e0 X.z0 X.bw k := ⟨fun hm => hm.2, fun hm => ⟨hk, hm⟩⟩
  have hLf : ∀ y ∈ X.B.I.Lf, (X.B.I.fmat k - 1) *ᵥ y ∈ X.B.I.Lf := by
    intro y hy
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    exact sub_mem ((hk y).1 hy) hy
  have hS1 : ∀ a : Fin D.R.rS, X.e0 '' {b | b.1 < a.1} ⊆ X.B.I.Lf := by
    rintro a _ ⟨b, -, rfl⟩; exact (X.vectorsInLattice.1 b).1
  have hS2 : Set.range X.e0 ⊆ X.B.I.Lf := by
    rintro _ ⟨b, rfl⟩; exact (X.vectorsInLattice.1 b).1
  have hS3 : ∀ i : Fin D.R.k, Set.range X.e0 ∪ X.bw '' {j | j.1 < i.1} ⊆ X.B.I.Lf := by
    rintro i _ (⟨b, rfl⟩ | ⟨j, -, rfl⟩)
    · exact (X.vectorsInLattice.1 b).1
    · exact (X.vectorsInLattice.2.2 j).1
  have hK : K2cong X.B.I X.B.g X.e0 X.z0 X.bw k ↔
      ∀ w : HeightOneSpectrum (𝓞 D.host.E), ((X.B.g : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal → CondAt X w k := by
    have e1 := fun a => GlobalTheory.T.inMod_iff_forall_place_memSpanModulo D X h hE _ (hS1 a) _ (hLf _ (X.vectorsInLattice.1 a).1)
    have e2 := GlobalTheory.T.inMod_iff_forall_place_memSpanModulo D X h hE _ hS2 _ (hLf _ X.vectorsInLattice.2.1)
    have e3 := fun i => GlobalTheory.T.inMod_iff_forall_place_memSpanModulo D X h hE _ (hS3 i) _ (hLf _ (X.vectorsInLattice.2.2 i).1)
    constructor
    · rintro ⟨h1, h2, h3⟩ w hw
      exact ⟨fun a => (e1 a).1 (h1 a) w hw, e2.1 h2 w hw, fun i => (e3 i).1 (h3 i) w hw⟩
    · intro H
      exact ⟨fun a => (e1 a).2 fun w hw => (H w hw).1 a, e2.2 fun w hw => (H w hw).2.1,
        fun i => (e3 i).2 fun w hw => (H w hw).2.2 i⟩
  have hgE : ((X.B.g : ℕ) : 𝓞 D.host.E) = ((D.host.g 0 : ℕ) : 𝓞 D.host.E) * ((D.host.g 1 : ℕ) : 𝓞 D.host.E) := by
    rw [X.g_eq, Nat.cast_mul]
  have hgw : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((X.B.g : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal := by
    rintro ⟨kk, v⟩
    rw [hgE]
    fin_cases kk
    · exact Ideal.mul_mem_right _ _ (hg ⟨0, v⟩)
    · exact Ideal.mul_mem_left _ _ (hg ⟨1, v⟩)
  have hP : (∀ w : HeightOneSpectrum (𝓞 D.host.E), ((X.B.g : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal → CondAt X w k) ↔
      ∀ kv : (Σ k : Fin 2, D.nd.PlG k), CondAt X (D.naut.plGw kv.1 kv.2) k ∧
        CondAt X (GlobalTheory.DimPartsCompare.cPl (D.naut.plGw kv.1 kv.2)) k := by
    constructor
    · intro H kv
      refine ⟨H _ (hgw kv), H _ ?_⟩
      rw [GlobalTheory.DimPartsCompare.mem_cPl, map_natCast]
      exact hgw kv
    · intro H w hw
      rw [hgE] at hw
      rcases w.isPrime.mem_or_mem hw with h0 | h1
      · obtain ⟨v, rfl | rfl⟩ := GlobalTheory.DimPartsCompare.cover 0 w h0
        · exact (H ⟨0, v⟩).1
        · exact (H ⟨0, v⟩).2
      · obtain ⟨v, rfl | rfl⟩ := GlobalTheory.DimPartsCompare.cover 1 w h1
        · exact (H ⟨1, v⟩).1
        · exact (H ⟨1, v⟩).2
  rw [hK2, hK, hP]
  exact forall_congr' fun kv => (GlobalTheory.T.symmetricPositionColumnCond_iff_congruence_conj D X h hE hg k hk kv).symm.trans (GlobalTheory.T.symmetricFrame_matrix_mem_unipotent_iff_column_span D X h hE hg k hk kv (Ns kv) (hNs kv)).symm

end GlobalTheory.Mem.GroupLoc
end

