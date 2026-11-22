import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0498
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartWiden
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0471
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsPreDataDyadicFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0443
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0502
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0299
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0330
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0031
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0399
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0412
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0406
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodProjectorSmallestSpaceForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0501
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0470
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0465
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0499
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0404
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Formalism.LocalToGlobal.Divisibility.DivisionHeightBoundColumns
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsHalfPtIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsColumnInputAssembled
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DegreeEqTotDeg

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseRowCountEqFinrankTypePartBaseLevelStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseRowCount_eq_finrank_typePart_baseLevel : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → HostHyp D → ∀ π : D.what₂.FT, D.what₂.nRows0 π = Module.finrank ℂ (principalLevelFrame.isotE R.toRealDat.θ Y.PY (R.toRealDat.MY 0) (levS _ (R.toRealDat.βY 0) (R.toRealDat.dat0 (R.toRealDat.levR F.lv2 false))) (levChi _ (R.toRealDat.βY 0) (R.toRealDat.dat0 (R.toRealDat.levR F.lv2 false))) R.toRealDat.e0 (principalLevelFrame.rowRepR R.toRealDat.θ (Y.eFT π))) := by
  first | exact @GlobalTheory.BaseRowCount.nRows0_eq_finrank_isotE | exact GlobalTheory.BaseRowCount.nRows0_eq_finrank_isotE | (intros; apply GlobalTheory.BaseRowCount.nRows0_eq_finrank_isotE <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartLocalGroupContainsPrincipalCongruenceStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_local_group_contains_principal_congruence : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Ch0 : B.Word → ℕ → Type) (chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (h1 : 1 ≤ B.R.m - 1) (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) (g : Ch → Ch0 u (B.R.m - 1)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u)) → (∀ u j v h, (F u).glevJ.fr j v h = 1) → (∃ k : Ch → GA B (B.R.N (B.R.m - 1)), I.Reads u a (B.R.m - 1) chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1) → (∀ β, ∀ v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) → (∀ β (κ : (K β).lev.U) (κ' : ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.chi κ') → ∀ (Lb0 : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin ((I.rec7 l Z).sp.X (B.R.m - 1)).rank → (I.rec7 l Z).host.E)), (F u).levJ.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) Lb0 → ∀ β v, v ∈ Q → ∃ n : ℕ, 0 < n ∧ ∀ x, Formalism.L2.Herm.InPrinc (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X (B.R.m - 1)) v n Lb0 x → x ∈ ((K β).lev.Uloc v).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom := by
  first | exact @GlobalTheory.Mem.Col2.AdT.LevQ.chart_contains_princ | exact GlobalTheory.Mem.Col2.AdT.LevQ.chart_contains_princ | (intros; apply GlobalTheory.Mem.Col2.AdT.LevQ.chart_contains_princ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartReadsAtClassGLStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_reads_at_class_GL : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : Charts I l Z u a i hi bad chOf) (k : Ch → GA B (B.R.N i)), ReadsAt I l Z K k → ∀ (c : (I.stp u a i).Cl) (fb : SBof I a → GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E), FrNear I l Z a (k (chOf c)) fb → ∀ P : SBof I a, GlobalTheory.TwU.NearAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) ((I.cst a).D P) (((K (chOf c)).y ⟨c, rfl⟩).1 * GlobalTheory.TwU.ratA (I.rec7 l Z).host.F (fb P)) (GlobalTheory.TwU.seamGL (sm I l Z) (frsF I.sel (I.tup a) ((I.stp u a i).rep c).1.1 P)) := by
  first | exact @GlobalTheory.Mem.Col2.AdT.FrameMove.frame_near | exact GlobalTheory.Mem.Col2.AdT.FrameMove.frame_near | (intros; apply GlobalTheory.Mem.Col2.AdT.FrameMove.frame_near <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartTiedLevelChainHost
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DnMove

set_option maxHeartbeats 4000000

theorem gl_inv_map_mul_map {n : ℕ} {E : Type} [Field E] (φ : E →+* ℂ) (A : GL (Fin n) E) (y : Matrix (Fin n) (Fin n) ℂ) :
    ((A⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map φ * ((A : Matrix (Fin n) (Fin n) E).map φ * y) = y := by
  rw [← Matrix.mul_assoc, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]

theorem tr_eq_of_isTr {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m)
    (eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) (hY : I.IdY l Z u a i hi eY) (b : (I.stp u a i).β) (g0 : (I.stp u a i).G b)
    (γ : UJ (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) i hi))
    (hγ : (γ.1 : GL (Fin (B.R.N i)) B.fields.E) = (I.stp u a i).gam b g0) (h : (I.chain l u a).Y i → ℂ) (s s' : (I.chain l u a).Y i)
    (hT : IsTr (atInf (embT (I.rec7 l Z)) γ.1.1) (eY s') (eY s)) :
    (I.stp u a i).tr B.fields.emb B.embLL b g0 h s = B.embLL (((I.stp u a i).chr b g0 : B.LLˣ) : B.LL) * h s' := by
  show B.embLL _ * h (frMul B.fields.emb B.embLL ((I.stp u a i).gam b g0)⁻¹ s) = _
  congr 2
  apply Subtype.ext
  funext τ
  have h1 := hT τ
  rw [hY, hY] at h1
  show (((I.stp u a i).gam b g0)⁻¹ : GL (Fin (B.R.N i)) B.fields.E).1.map _ * s.1 τ = s'.1 τ
  have h2 : atInf (embT (I.rec7 l Z)) (γ.1.1) τ = (((I.stp u a i).gam b g0 : GL (Fin (B.R.N i)) B.fields.E) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.fields.E).map (embAt B.embLL B.fields.emb τ) := by
    rw [← hγ]
    show (γ.1.1).map (embT (I.rec7 l Z) τ) = (γ.1.1).map (embAt B.embLL B.fields.emb τ)
    congr 1
    ext x
    show B.host.emb τ x = B.embLL (B.tauLL τ x)
    rw [← GlobalTheory.Mem.PreXModel.embLL_tauLL]
    rfl
  rw [h1, h2]
  exact gl_inv_map_mul_map _ _ _

theorem dnNatTieG_cols : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) (eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) (eV : (I.atT l u a).vT ≃ {v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) // (B.T u : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal}) (L : LevelCompatibleLattices (D := (I.rec7 l Z)) (I.fm l u a) (B.T u) (I.resT l u a) i hi fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c)), I.ReadsK l Z u a i hi chOf K → I.IdY l Z u a i hi eY → I.IdV l u a eV → I.IdL l Z u a i hi L → DnNatTieG L eY eV K := by
  intro B X I hOk hP l Z u a i hi bad Ch chOf K eY eV L hK hY hV hL
  intro v β c g hg
  have hβ := GlobalTheory.T.move_down_level_prime_keeps_chart I hOk hP l Z u a i hi bad Ch chOf K eY eV L hK hY hV hL v β c g hg
  obtain ⟨γ, η, κ, hγ, hη, hrel, hchi⟩ := GlobalTheory.T.moveDown_levelPrime_adelic_factorisation I hOk hP l Z u a i hi bad Ch chOf K eY eV L hK hY hV hL v β c g hg hβ
  refine ⟨hβ, γ, η, κ, hη, hrel, GlobalTheory.T.downMove_localDualLattice_eq_levelPrime I hOk hP l Z u a i hi bad Ch chOf K eY eV L hK hY hV hL v β c g hg γ hγ,
    GlobalTheory.T.move_down_level_functional_eq I hOk hP l Z u a i hi bad Ch chOf K eY eV L hK hY hV hL v β c g hg γ hγ, ?_⟩
  intro h s s' hT
  show (I.stp u a i).trTo B.fields.emb B.embLL c.1.1 (((I.atIn u a).A i).dnPt v c.1 g) h s = _
  rw [hchi]
  exact tr_eq_of_isTr I l Z u a i hi eY hY _ _ γ hγ h s s' hT

end GlobalTheory.DnMove

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassSumComplexRowFormColumnsLevelEq
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI GlobalTheory.Mem.Col2.starE
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.CsumForm

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.R3 GlobalTheory.Mem.ColTie

section Gen

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs) (hX : X.Ok)

theorem ipK_zOf_eq (x y : Fin (dimP W Ch sel mu P hX) → X.K) :
    ipK W Ch sel mu P hX (zOf W Ch sel mu P hX x) (zOf W Ch sel mu P hX y) =
      (csdK W Ch sel mu hX).csum (formK W Ch sel mu P hX x).1 (formK W Ch sel mu P hX y).1 := by
  have e : ∀ x, (fun c => (zOf W Ch sel mu P hX x).1 ((mtildeKGSD W Ch sel mu).outSec.rep c)) =
      ((formK W Ch sel mu P hX x).1 : _ → _) := by
    intro x
    funext c
    rw [zOf_val, ← GSD.resOf_apply _ (mtildeKOk W Ch sel mu hX) (mtildeKGSD W Ch sel mu).outSec]
    show (((resK W Ch sel mu hX) ((resK W Ch sel mu hX).symm (formK W Ch sel mu P hX x))).1 : _ → _) c = _
    rw [LinearEquiv.apply_symm_apply]
  unfold ipK GSD.ip GSD.ipOf
  rw [e, e]

theorem ipLev_zOf_eq (x y : Fin (dimP W Ch sel mu P hX) → X.K) :
    ipLev W Ch sel mu P hX (zOf W Ch sel mu P hX x) (zOf W Ch sel mu P hX y) =
      Formalism.DivisionValues.hform ((csdK W Ch sel mu hX).lvlH (actK W Ch sel mu hX) P.grp P.chr) x y := by
  have hP : (Nat.card P.grp : X.K) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  refine mul_left_cancel₀ hP ?_
  rw [← ipK_eq_card_mul_ipLev W Ch sel mu P hX, ipK_zOf_eq]
  exact LiftForms.csum_lvlForm _ _ _ _ x y

end Gen

section TC

variable {B : Base} {px : PreX B.toPre} (I : ColIn B px) (hX : B.fields.Ok) (a : I.ι)

theorem cSum_toCx (x : Formalism.L2.Col.MtildeV (Pr := B.primes px) B.wts I.Ch I.sel (I.tup a) (TC.Ps I))
    (x' : Formalism.L2.Col.MtildeV (Pr := B.primes px) B.wts I.Ch I.sel (I.tup a) (TC.Ps I)) :
    Df.cSum I hX a (Df.toCx I hX a x) (Df.toCx I hX a x') =
      B.embLL (ipLev (Pr := B.primes px) B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX x x') := by
  rw [Df.cSum_apply]
  unfold ipLev GSD.ip GSD.ipOf CSD.csum
  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  unfold Df.cTerm
  rw [map_mul, map_inv₀, map_natCast, GSD.wt_eq]
  congr 1
  exact (map_pairV_one _ _ (sig B) (fun x => B.starLL_cx x) _ _).symm

end TC

theorem cSum_toCx_rowForm : ∀ (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hX : X.B.fields.Ok)
    (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (a : I.ι) (y : Fin (mAU X I hX Xg tr true a).n → X.B.LL)
    (x : Formalism.L2.Col.MtildeV (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I)),
    IsFormOf (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX (TC.Ps I) x
      (rowForm (D := X.toD7) (famR X I hX Set.univ Xg tr).A (lev1 I) (chr1 I) (tAll I a) y) →
    Df.cSum I hX a (Df.toCx I hX a x) (Df.toCx I hX a x) = X.B.embLL (Formalism.DivisionValues.hform (mAU X I hX Xg tr true a).H y y) := by
  intro X px I hX Xg tr a y x hx
  obtain ⟨F, h, hF, rfl⟩ := hx
  have e1 : ColTie.resK (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX F =
      ColTie.formK (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX y := eq_of_heq hF
  have e2 : (⟨F.1, h⟩ : Formalism.L2.Col.MtildeV (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I)) =
      ColTie.zOf (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX y := by
    apply Subtype.ext
    show F.1 = ((ColTie.resK (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX).symm
      (ColTie.formK (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX y)).1
    rw [← e1, LinearEquiv.symm_apply_apply]
  rw [cSum_toCx, e2]
  exact congrArg X.B.embLL (ipLev_zOf_eq (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX y y)

end GlobalTheory.Mem.CsumForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompositeIntertwinerEqThetaLiftGoodProjector
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.R3.DTheta

set_option maxHeartbeats 4000000 in

theorem composite_eq_lift : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → (∀ t x, (Y.Ish.jE (D.what₂.iota (Y.tup t) (Y.jA t x))).1 = PiTensorProduct.lift (R.HE.e (R.Th t (R.jX t (rowForm A3.A F.P1 F.ψ1 t x))))) ∧ ∀ t x, (Y.Iz.jE (X0.s.iota (Y.tup t) (Y.jA0 t x))).1 = PiTensorProduct.lift (R.HE.e (R.Th t (R.jX t (rowForm A3.A F.P0 F.ψ0 t x)))) := by
  intro hC D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hPins hHolds
  have hch : R.toRealDat.IsChain := RealDat.chain_of_weak hPins.char.base.chain hHolds.aux.ex
  have hS : StepLev R.toRealDat F.lv2 := GlobalTheory.T.innerThetaSteps_preserve_faceLevel hC D G Pl0 I0 T A3 Ks R F cG hPins hHolds
  have hT : TopLev R.toRealDat F.lv2 := GlobalTheory.T.lastThetaStep_keeps_faceLevel hC D G Pl0 I0 T A3 Ks R F cG hPins hHolds
  have hP : RowProj R.toRealDat F.lv2 := rowProj_holds hC.2.2.2.2 D G Pl0 I0 T A3 Ks R F cG hPins hHolds
  have hUsed : ∀ t, Used0 D (Y.tup t) := by
    intro t
    rcases hPins.char.tup.mu_used t with h | ⟨w, hw⟩
    · left
      rw [h]
      exact Y.tup0
    · right
      refine ⟨D.plEq.symm w, ?_⟩
      rw [Y.muAt, Equiv.apply_symm_apply, hw]
  refine ⟨fun t x => ?_, fun t x => ?_⟩
  · rw [iota_sharp]
    exact iota_eq_real' R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop hch hS hT hP (RowSide.sharp D) true Y.Ish Y.tied.sharp
      (Y.tup t) (hUsed t) (Y.jA t x) t (Y.tupT_tup t) _ (Y.topRead t (hUsed t) x)
  · exact iota_eq_real' R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop hch hS hT hP X0.s false Y.Iz Y.tied.base
      (Y.tup t) (hUsed t) (Y.jA0 t x) t (Y.tupT_tup t) _ (Y.topRead0 t (hUsed t) x)

end GlobalTheory.Mem.R3.DTheta
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CongruentAutomorphismsLiftStepGroupElementsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.congruent_automorphisms_lift_step_group_elements : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i < B.R.m) (b : (I.stp u a i).β) (P : SBof I a) (g : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) (z : B.fields.K), MidAt I hi b P g z → g ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1 ∧ ∀ g' ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1, CongE P.1 ((I.cst a).D P) g g' → ∃ κ : (I.stp u a i).G b, (I.stp u a i).gam b κ = 1 ∧ LiftsInv I κ P g' ∧ ∀ P', P' ≠ P → LiftsInv I κ P' 1 := by
  first | exact @GlobalTheory.Mem.Col2.AdT.midAt_lifts | exact GlobalTheory.Mem.Col2.AdT.midAt_lifts | (intros; apply GlobalTheory.Mem.Col2.AdT.midAt_lifts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecoratedRowLatticesFlagLevelRightTranslationStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.decoratedRowLattices_flagLevel_rightTranslation : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r),
    I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG →
    ∀ (t : TupU I U) (q : (levEnv X.toD7.sp.X' L.βX (L.datXt t)).Q),
    ∃ u : ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp,
      (∀ h : Bridge.Gf X.toD7.sp.X', RowAd.decoAd X I t (h * (q : Bridge.Gf X.toD7.sp.X')) =
        ((1 : Formalism.L2.Col.UF X.B.fields.E (X.B.R.N X.B.R.m - 1)),
          (u : Formalism.L2.Col.GLG X.B.fields.E (X.B.R.N X.B.R.m - 1) (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1)) *
            (Formalism.L2.Col.unipotentGroupBlockEmbedding (X.B.primes px) I.sel t.1 (Formalism.L2.Col.r_le_X' X.B.R)
              (eG.symm (rTup L.βX (L.datXt t) (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf X.toD7.sp.X') : GL _ _)))))⁻¹) •
          RowAd.decoAd X I t h) ∧
      X.toD7.what₂.embLL (((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv.chr u : X.B.fields.Kˣ) : X.B.fields.K) =
        (((levEnv X.toD7.sp.X' L.βX (L.datXt t)).ch q : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.Mem.R3.RowDeco.deco_tie | exact GlobalTheory.Mem.R3.RowDeco.deco_tie | (intros; apply GlobalTheory.Mem.R3.RowDeco.deco_tie <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteFormsAllTuplesCoordinateLaws
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw.Mats

section Gen

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]

omit [NumberField K] in

theorem isConjAt_mk {σ : K →+* ℂ} (hσ : ∀ a, σ (star a) = starRingEnd ℂ (σ a)) :
    Formalism.DivisionValues.IsConjAt (InfinitePlace.mk σ) := fun a => by
  rcases InfinitePlace.embedding_mk_eq σ with e | e
  · rw [e]
    exact hσ a
  · rw [e, ComplexEmbedding.conjugate_coe_eq, ComplexEmbedding.conjugate_coe_eq, hσ a]

omit [NumberField K] [StarRing K] in

theorem posDef_of_mk {n : ℕ} {σ : K →+* ℂ} {H : Matrix (Fin n) (Fin n) K}
    (h : (H.map (InfinitePlace.mk σ).embedding).PosDef) : (H.map σ).PosDef := by
  rcases InfinitePlace.embedding_mk_eq σ with e | e
  · rwa [e] at h
  · rw [e] at h
    have h1 := h.isHermitian
    have e2 : H.map σ = (H.map (ComplexEmbedding.conjugate σ))ᵀ := by
      ext i j
      have := h1.apply j i
      simp only [Matrix.map_apply, ComplexEmbedding.conjugate_coe_eq, Matrix.transpose_apply] at this ⊢
      rw [← this]
      simp
    rw [e2]
    exact h.transpose

omit [NumberField K] in

theorem hform_eq_dot {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) :
    Formalism.DivisionValues.hform H x y = star x ⬝ᵥ H.mulVec y := by
  unfold Formalism.DivisionValues.hform
  rw [Matrix.toLinearMapₛₗ₂'_apply]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, starRingEnd_apply, RingHom.id_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

omit [NumberField K] in

theorem hform_sa {n : ℕ} {H A : Matrix (Fin n) (Fin n) K} (h : Aᴴ * H = H * A) (x y : Fin n → K) :
    Formalism.DivisionValues.hform H (A.mulVec x) y = Formalism.DivisionValues.hform H x (A.mulVec y) := by
  rw [hform_eq_dot, hform_eq_dot, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]

omit [NumberField K] [StarRing K] [Fintype G] in

theorem zero_laws [NumberField K] [StarRing K] (σ : K →+* ℂ) {e : MonoidAlgebra K G}
    (hc : e ∈ Subalgebra.center K (MonoidAlgebra K G)) (hi : IsIdempotentElem e) : (Mat1.zero K G).Laws σ e where
  pos := by
    show ((0 : Matrix (Fin 0) (Fin 0) K).map σ).PosDef
    rw [Subsingleton.elim ((0 : Matrix (Fin 0) (Fin 0) K).map σ) 1]
    exact Matrix.PosDef.one
  lat := by
    show Submodule.IsLattice K (⊤ : Submodule (𝓞 K) (Fin 0 → K))
    refine ⟨?_, Subsingleton.elim _ _⟩
    rw [Subsingleton.elim (⊤ : Submodule (𝓞 K) (Fin 0 → K)) ⊥]
    exact Submodule.fg_bot
  add _ _ := Subsingleton.elim (α := Matrix (Fin 0) (Fin 0) K) _ _
  smul _ _ := Subsingleton.elim (α := Matrix (Fin 0) (Fin 0) K) _ _
  one := Subsingleton.elim (α := Matrix (Fin 0) (Fin 0) K) _ _
  mul _ _ _ _ := Subsingleton.elim (α := Matrix (Fin 0) (Fin 0) K) _ _
  E_eq := rfl
  cen := hc
  idem := hi
  sa x y := by
    rw [hform_eq_dot, hform_eq_dot]
    rfl

def lvlMat (S : CSD K) (r : Representation K G S.Forms) (P : Subgroup G) (ψ : P →* Kˣ) (e : MonoidAlgebra K G) : Mat1 K G :=
  ⟨S.lvlDim r P ψ, S.lvlH r P ψ, S.lvlOp r P ψ e, S.lvlNab r P ψ, fun a => S.lvlOp r P ψ a⟩

theorem lvlMat_laws {σ : K →+* ℂ} (hσ : ∀ a, σ (star a) = starRingEnd ℂ (σ a)) (S : CSD K) {s : ℕ} (hS : S.Good s)
    (hpos : ∀ v : InfinitePlace K, (S.H.map v.embedding).PosDef) (r : Representation K G S.Forms) (hr : S.ActGood r)
    (hrat : S.ActRat r) (P : Subgroup G) (ψ : P →* Kˣ) (X : Finset (G → K)) (hX : ∀ χ ∈ X, IsAbsIrrChar χ) :
    (lvlMat S r P ψ (idemOf X)).Laws σ (idemOf X) := by
  have h0 := isConjAt_mk hσ
  have hP := (level_idempotent_spec K _ h0 G P ψ).1
  have hI := idempotent_spec K _ h0 G X hX
  have hinj : Function.Injective (S.lvlE r P ψ).mulVec := (image_idempotent_spec K _ _).1
  have hE : ∀ i j, S.lvlE r P ψ i j ∈ Formalism.DivisionValues.cmMax K :=
    image_idempotent_rational K S.dim (S.gaMat r (lvlIdem P ψ)) (gaMat_rat S r hrat _ hP.rat)
  have hproj := (orthogonal_projection_spec K _ h0 S (hpos _) G r hr _ hP.idem hP.selfAdj).1.1
  have hop := level_operator_spec K _ h0 S (hpos _) G r hr P ψ
  refine ⟨posDef_of_mk (cut_posDef S.H (S.lvlE r P ψ) hinj hE (Nat.card P) Nat.card_pos _ (hpos _)),
    Formalism.DivisionValues.exponent_index_lattice.cut_isLattice _ (fun _ _ hxy => hinj hxy) _ (S.lf_nabLat_isLattice hS), fun a b => ?_, fun c a => ?_, ?_,
    fun a _ b hb => (hop b (Subalgebra.mem_center_iff.1 hb _).symm).2 a, rfl, Subalgebra.mem_center_iff.2 hI.2, hI.1.idem,
    hform_sa ?_⟩
  · show S.lvlOp r P ψ (a + b) = S.lvlOp r P ψ a + S.lvlOp r P ψ b
    unfold CSD.lvlOp
    rw [CSD.gaMat_eq_lift, CSD.gaMat_eq_lift, CSD.gaMat_eq_lift, map_add, Matrix.mul_add, Matrix.add_mul]
  · show S.lvlOp r P ψ (c • a) = c • S.lvlOp r P ψ a
    unfold CSD.lvlOp
    rw [CSD.gaMat_eq_lift, CSD.gaMat_eq_lift, map_smul, Matrix.mul_smul, Matrix.smul_mul]
  · show S.lvlOp r P ψ 1 = 1
    unfold CSD.lvlOp
    rw [(group_action_matrix_hom K S G r).1, Matrix.mul_one]
    exact hproj
  · have h1 := (hop (idemOf X) (hI.2 _).symm).1
    have h2 := group_action_matrix_adjoint K S G r hr (idemOf X)
    rw [hI.1.selfAdj] at h2
    show (S.lvlOp r P ψ (idemOf X))ᴴ * ((Nat.card P : K)⁻¹ • ((S.lvlE r P ψ)ᴴ * S.H * S.lvlE r P ψ)) =
      ((Nat.card P : K)⁻¹ • ((S.lvlE r P ψ)ᴴ * S.H * S.lvlE r P ψ)) * S.lvlOp r P ψ (idemOf X)
    rw [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, h1,
      Matrix.conjTranspose_mul, Matrix.mul_assoc (S.lvlE r P ψ)ᴴ, h2, Matrix.mul_assoc _ (S.lvlE r P ψ), h1]
    simp only [Matrix.mul_assoc]

end Gen

section Col

variable {X : Formalism.L2.Col.Fields} {Pr : Formalism.L2.Col.Primes X} {R : Ranks} (W : Formalism.L2.Col.Wts X Pr.Word R) (Ch : Formalism.L2.Col.Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (hX : X.Ok) (v0 : InfinitePlace X.K)
  (TU : Finset (Tup X.F X.E X.K S)) (Xg : Finset (Formalism.L2.Col.G0 X.E Pr.vGs R.r → X.K)) (S0 : Set (HeightOneSpectrum (𝓞 X.E)))
  (xiVal : Tup X.F X.E X.K S → HeightOneSpectrum (𝓞 X.E) → X.Kˣ) {σ : X.K →+* ℂ} (hσ : ∀ a, σ (star a) = starRingEnd ℂ (σ a))
  (hirr : ∀ χ ∈ Xg, IsAbsIrrChar χ) (P : Subgroup (Formalism.L2.Col.G0 X.E Pr.vGs R.r)) (ψ : P →* X.Kˣ)

include hσ hirr

theorem rows_laws (τ : TupF TU) :
    (lvlMat ((colIn W Ch sel hX v0 TU Xg S0 xiVal).MtildeCSD τ) ((colIn W Ch sel hX v0 TU Xg S0 xiVal).leftGroupActionRight τ) P ψ
      (idemOf Xg)).Laws σ (idemOf Xg) :=
  lvlMat_laws hσ _ (Formalism.L2.Col.MtildeKCSD_good W Ch sel τ.1 hX _) (fun v => (Formalism.L2.Col.mtildeK_rat W Ch sel τ.1 hX).posH _ v) _
    (Formalism.L2.Col.unipotentActionForms_good W Ch sel τ.1 hX _) (Formalism.L2.Col.unipotentActionForms_rational W Ch sel τ.1 hX _) P ψ Xg hirr

theorem lifts_laws (j : Fin R.m) (τ : TupF TU) :
    (lvlMat ((colIn W Ch sel hX v0 TU Xg S0 xiVal).MtCSD j τ) ((colIn W Ch sel hX v0 TU Xg S0 xiVal).leftGroupActionLift j τ) P ψ
      (idemOf Xg)).Laws σ (idemOf Xg) :=
  lvlMat_laws hσ _ (Formalism.L2.Col.MtKCSD_good W Ch sel τ.1 hX (j.1 + 1) _)
    (fun v => (Formalism.L2.Col.mtK_rat W Ch sel τ.1 hX (j.1 + 1)).posH _ v) _
    (Formalism.L2.Col.unipotentActionClassSum_good W Ch sel τ.1 hX (j.1 + 1) _) (Formalism.L2.Col.unipotentActionClassSum_rational W Ch sel τ.1 hX (j.1 + 1) _) P ψ Xg hirr

end Col

section Fam

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} (A : FamIn D.what₂.LL G Pl0 T D.R.m)
  (P : Subgroup G) (ψ : P →* D.what₂.LLˣ)

theorem rMat_eq (t : T) : rMat A P ψ t = lvlMat (A.MtildeCSD t) (A.leftGroupActionRight t) P ψ (idemOf A.X) := rfl

theorem lMat_eq (i : Fin D.R.m) (t : T) : lMat A P ψ i t = lvlMat (A.MtCSD i t) (A.leftGroupActionLift i t) P ψ⁻¹ (idemOf A.X) := rfl

end Fam

theorem mats_laws : ∀ (X : Stages) (px : PreX X.B.toPre) (I : ColIn X.B px) (hX : X.B.fields.Ok) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px), I.Ok → (∀ χ ∈ Xg, IsAbsIrrChar χ) → (∀ b a, (mAU X I hX Xg tr b a).Laws X.toD7.what₂.embLL (idemOf Xg)) ∧ ∀ a j, (mLU X I hX Xg tr a j).Laws X.toD7.what₂.embLL (idemOf Xg) := by
  intro X px I hX Xg tr _ hirr
  refine ⟨fun b a => ?_, fun a j => ?_⟩
  · unfold mAU
    rw [rMat_eq]
    exact rows_laws (X := X.B.fields) (Pr := X.B.primes px) X.B.wts I.Ch I.sel hX (InfinitePlace.mk X.B.embLL) (tuOf I Set.univ) Xg ∅
      (xiValOf I) (σ := X.B.embLL) X.B.starLL_cx hirr _ _ (tAll I a)
  · unfold mLU
    split_ifs with h
    · rw [lMat_eq]
      exact lifts_laws (X := X.B.fields) (Pr := X.B.primes px) X.B.wts I.Ch I.sel hX (InfinitePlace.mk X.B.embLL) (tuOf I Set.univ) Xg ∅
        (xiValOf I) (σ := X.B.embLL) X.B.starLL_cx hirr _ _ _ (tAll I a)
    · have hI := idempotent_central X.B.LL (Gc X.B px) Xg hirr
      exact zero_laws _ (Subalgebra.mem_center_iff.2 hI.2) hI.1

end GlobalTheory.Mem.R3.Rw.Mats

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBaseLevelRowOfNonzeroGoodRowsPartStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_baseLevelRow_of_nonzero_goodRowsPart : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Inputs D → Pins R F cG → Holds R F → GlobalTheory.CuspMult.MultEq R.toRealDat → (∀ χ ∈ A3.A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0) → ∀ p, R.EEp3 p ≠ ⊥ → (R.toCx3 F).EEp p ⊓ (R.toCx3 F).EEl false ≠ ⊥ := by
  first | exact @GlobalTheory.RowsAtBase.exists_base_row_of_pins | exact GlobalTheory.RowsAtBase.exists_base_row_of_pins | (intros; apply GlobalTheory.RowsAtBase.exists_base_row_of_pins <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsColInJetsIn
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Col2

namespace JetEx

theorem hasLetters_of_over {K : Ctx} {P : Pre} (h : K.Over P) : StagesInhab.HasLetters P := by
  obtain ⟨sp, hT, hY, hA, hV, hz, rfl, -⟩ := h
  have hx : 0 < K.s.x := zero_lt_one.trans K.s.one_lt_alt
  refine ⟨(Delv K.s K.cD : ℚ), K.c, Nat.cast_pos.2 (Nat.ceil_pos.2 (Real.rpow_pos_of_pos hx _)), K.ok.inj,
    fun w τ l hl => ?_, K.ok.code⟩
  have h1 := (K.ok.hc w).1 τ
  change l + 1 < K.P.R.k - 1 at hl
  show (K.P.hcW w τ).v ⟨l, by omega⟩ - (K.P.hcW w τ).v ⟨l + 1, hl⟩ = _
  rw [h1, h1, show K.P.R.k - 2 - l = K.P.R.k - 2 - (l + 1) + 1 by omega]
  push_cast
  ring

theorem lg_gens (K : Ctx) : large₂ K fun B f T => ∀ z ∈ gens B.toPre f.chiPsi (T.set f), z ∈ B.embLL.fieldRange :=
  ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun P f _ _ Ξ => gens P f.chiPsi Ξ, by simp,
    fun P f _ _ Ξ => gens_algebraic P f.chiPsi Ξ, fun _ _ _ _ h _ _ => h.2⟩

end JetEx

theorem exists_bound_jetsIn : ∃ Z : ∀ P : Pre, HChar P.host.E → Set (HChar P.host.E) → Finset ℂ,
    (∀ P χ Ξ, ∀ z ∈ Z P χ Ξ, IsAlgebraic ℚ z) ∧
    ∀ (B : Base) (X : PreX B.toPre) (I : ColIn B X), StagesInhab.HasLetters B.toPre → I.Ok →
      (∀ z ∈ Z B.toPre I.C.chiPsi (Set.range I.xi), z ∈ B.embLL.fieldRange) →
      ∃ I' : ColIn B X, I'.Ok ∧ I'.JetsIn ∧ I'.C = I.C ∧ I'.S = I.S ∧ Set.range I'.xi = Set.range I.xi :=
  ⟨JetEx.gens, JetEx.gens_algebraic, fun _ _ _ hL h hK => JetEx.exists_jetsIn hL h hK⟩

end GlobalTheory.Mem.Col2

end
end

