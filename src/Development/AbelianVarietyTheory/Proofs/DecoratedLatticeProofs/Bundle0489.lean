import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0470
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0037
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0035
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0473
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0355
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0105
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0136
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0463
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1143
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0474
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0553
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0254
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0177
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0327
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TruePackTwistPlacePropertyStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_pack_twist_place_property : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (t : W.P.T) (PP : Formalism.L2.DIV.Pl (I.rec7 l Z).host.E), PP ∈ (pk W).Q t → ∀ j, j < (I.rec7 l Z).R.m → (∃ N, IsSDFrame (Yc (I.rec7 l Z) j) ((pk W).βY j) ((pk W).ΛY j) N) ∧ ∀ PP' ∈ (pk W).Pg, PP'.under (𝓞 (I.rec7 l Z).host.F) ≠ PP.under (𝓞 (I.rec7 l Z).host.F) := by
  first | exact @GlobalTheory.PkFrame.pk_frame_places | exact GlobalTheory.PkFrame.pk_frame_places | (intros; apply GlobalTheory.PkFrame.pk_frame_places <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TupleFreeLevelLeCompact
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel

noncomputable section
namespace GlobalTheory.PenLev

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : B.Word}
  {a : GeoAll W u} {t : W.P.T}

def relax (J : QJ a t) (j : ℕ) (hj : j + 1 = B.R.m) (α : J.Ch j) : Subgroup (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)) :=
  (J.A.U j (J.ι j α) ⊔ GlobalTheory.FinPl.grpAt _ (GlobalTheory.PenBridge.plF J)) ⊓ GfC _ ⊓
    (Subgroup.pi Set.univ fun i =>
      KO (J.G i).k (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) ((J.G i).s + 1) ⊕ Fin 0)).comap (GlobalTheory.PenBridge.rd J j hj)

def U0 (a : GeoAll W u) (j : ℕ) (hj : j + 1 = B.R.m) : Subgroup (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)) :=
  if h : ∃ t, ∃ J : QJ a t, J.Reads ∧ Nonempty (J.Ch j) then
    relax h.choose_spec.choose j hj h.choose_spec.choose_spec.2.some
  else ⊥

theorem relax_le (J : QJ a t) (j : ℕ) (hj : j + 1 = B.R.m) (α : J.Ch j) : relax J j hj α ≤ GfC _ :=
  fun _ hg => (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hg).1).2

theorem tuple_free_level_le_compact (a : GeoAll W u) (j : ℕ) (hj : j + 1 = B.R.m) : U0 a j hj ≤ GfC _ := by
  unfold U0
  split_ifs
  · exact relax_le _ _ _ _
  · exact bot_le

theorem mem_relax_iff (J : QJ a t) (j : ℕ) (hj : j + 1 = B.R.m) (α : J.Ch j) (g : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)) :
    g ∈ relax J j hj α ↔ g ∈ J.A.U j (J.ι j α) ⊔ GlobalTheory.FinPl.grpAt _ (GlobalTheory.PenBridge.plF J) ∧ g ∈ GfC _ ∧
      ∀ i, GlobalTheory.PenBridge.rd J j hj g i ∈ KO (J.G i).k _ := by
  simp only [relax, Subgroup.mem_inf, Subgroup.mem_comap, Subgroup.mem_pi, Set.mem_univ, true_implies, and_assoc]

theorem tuple_free_level_eq_relaxed (J : QJ a t) (j : ℕ) (hj : j + 1 = B.R.m) (hJ : J.Reads) (α : J.Ch j) :
    ∃ (t₀ : W.P.T) (J₀ : QJ a t₀) (α₀ : J₀.Ch j), J₀.Reads ∧ U0 a j hj = relax J₀ j hj α₀ := by
  have h : ∃ t, ∃ J : QJ a t, J.Reads ∧ Nonempty (J.Ch j) := ⟨t, J, hJ, ⟨α⟩⟩
  refine ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.2.some, h.choose_spec.choose_spec.1, ?_⟩
  unfold U0
  rw [dif_pos h]

end GlobalTheory.PenLev
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedThetaChainStepAdjointScalarStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedThetaChain_step_adjoint_scalar : ∀ D : D7, SoftQ D → UpParQ D → UpQ D → QOfVal D → UpVal D → StepExactNS D → LFull D → Restore D → StepLam D := by
  first | exact @GlobalTheory.ChainTw.stepLam_of_ns | exact GlobalTheory.ChainTw.stepLam_of_ns | (intros; apply GlobalTheory.ChainTw.stepLam_of_ns <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypePrimesDisjointStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.type_primes_disjoint : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ u : B.Word, Disjoint ((B.primes X).vT u) (B.primes X).vGs := by
  first | exact @GlobalTheory.Mem.Col2.DisjProof.vT_disjoint_vGs | exact GlobalTheory.Mem.Col2.DisjProof.vT_disjoint_vGs | (intros; apply GlobalTheory.Mem.Col2.DisjProof.vT_disjoint_vGs <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitNormVectorsOneOrbitSelfDualLatticeSplit
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
open GlobalTheory.Grow GlobalTheory.Unf NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.SplitOrbit

variable {D : D7}

theorem hermAt_eq (S : HSp D) (x y : Fin S.rank → AE D) :
    hermAt S x y = (fun i => cA D (y i)) ⬝ᵥ (gA S *ᵥ x) := by
  simp only [hermAt, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hermAt_mulVec (S : HSp D) {k : ℕ} (a : Mx D S.rank k) (x : Fin S.rank → AE D) (y : Fin k → AE D) :
    hermAt S x (a *ᵥ y) = (fun i => cA D (y i)) ⬝ᵥ ((adj a ⬝ gA S) *ᵥ x) := by
  have h : (fun i => cA D ((a *ᵥ y) i)) = (fun i => cA D (y i)) ᵥ* adj a := by
    funext i
    simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, map_sum, map_mul]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [hermAt_eq, h, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec _ (adj a)]

theorem hermAt_unitary (S : HSp D) (g : GA D S) (x y : Fin S.rank → AE D) :
    hermAt S (mt S g *ᵥ x) (mt S g *ᵥ y) = hermAt S x y := by
  rw [hermAt_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, mt_unitary, hermAt_eq]

theorem hermAt_jB {S A B : HSp D} (o : OrthDec S A B) (y : Fin S.rank → AE D) (l : Fin B.rank → AE D) :
    hermAt S y (o.jB *ᵥ l) = hermAt B (o.pB *ᵥ y) l := by
  rw [hermAt_mulVec, hermAt_eq, Matrix.mulVec_mulVec, o.pB_eq, ← Matrix.mul_assoc (gA B), gA_mul_giA, Matrix.one_mul]

theorem hermAt_jA {S A B : HSp D} (o : OrthDec S A B) (x : Fin A.rank → AE D) (y : Fin S.rank → AE D) :
    hermAt S (o.jA *ᵥ x) y = hermAt A x (o.pA *ᵥ y) := by
  have h : gA S ⬝ o.jA = adj o.pA ⬝ gA A := by
    rw [o.gA_eq]
    simp only [Matrix.add_mul, Matrix.mul_assoc, o.pA_jA, o.pB_jA, Matrix.mul_one, Matrix.mul_zero, add_zero]
  rw [hermAt_mulVec, hermAt_eq, Matrix.mulVec_mulVec, h]

theorem exists_den {P : Pl D → Prop} {m n : ℕ} (X : Matrix (Fin m) (Fin n) (AE D)) :
    ∃ N : ℕ, 0 < N ∧ ∀ y : Fin n → AE D, (∀ i, y i ∈ intAt D P) → ∀ i, ((N : AE D) • (X *ᵥ y)) i ∈ intAt D P := by
  choose k hk hX using fun p : Fin m × Fin n => GlobalTheory.LatMatch.exists_nat_smul_intAE (finPart D (X p.1 p.2))
  refine ⟨∏ p, k p, Finset.prod_pos fun p _ => hk p, fun y hy i => ⟨?_, ?_⟩⟩
  · exact Ideal.mul_mem_left _ _ (mulVec_mem_idAt X (fun j => (hy j).1) i)
  · simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Finset.mul_sum, map_sum]
    refine sum_mem fun j _ => ?_
    rw [← mul_assoc, map_mul]
    refine GlobalTheory.LatMatch.mul_mem_intAE' D ?_ (hy j).2
    rw [map_mul, map_natCast, ← nsmul_eq_mul, ← Finset.prod_erase_mul _ _ (Finset.mem_univ (i, j)), mul_smul]
    exact nsmul_mem (hX (i, j)) _

def pre {m n : ℕ} (X : Matrix (Fin m) (Fin n) (AE D)) (Λ : AddSubgroup (Fin m → AE D)) : AddSubgroup (Fin n → AE D) :=
  Λ.comap (Matrix.mulVecLin X).toAddMonoidHom

theorem mem_pre {m n : ℕ} {X : Matrix (Fin m) (Fin n) (AE D)} {Λ : AddSubgroup (Fin m → AE D)} {y : Fin n → AE D} :
    y ∈ pre X Λ ↔ X *ᵥ y ∈ Λ := Iff.rfl

theorem pre_den {P : Pl D → Prop} {m n : ℕ} (X : Matrix (Fin m) (Fin n) (AE D)) {Λ : AddSubgroup (Fin m → AE D)}
    (h : ∃ N : ℕ, 0 < N ∧ ∀ y : Fin m → AE D, (∀ i, y i ∈ intAt D P) → (N : AE D) • y ∈ Λ) :
    ∃ N : ℕ, 0 < N ∧ ∀ y : Fin n → AE D, (∀ i, y i ∈ intAt D P) → (N : AE D) • y ∈ pre X Λ := by
  obtain ⟨N, hN, h⟩ := h
  obtain ⟨N', hN', h'⟩ := exists_den (P := P) X
  refine ⟨N * N', Nat.mul_pos hN hN', fun y hy => ?_⟩
  rw [mem_pre, Matrix.mulVec_smul, Nat.cast_mul, mul_smul]
  exact h _ (h' y hy)

theorem isSDAt_pre_unitary {S : HSp D} {v : Pl D} {Λ : AddSubgroup (Fin S.rank → AE D)} (h : IsSDAt S v Λ) (g : GA D S) :
    IsSDAt S v (pre (mt S g) Λ) := by
  have e : ∀ y, mt S g⁻¹ *ᵥ (mt S g *ᵥ y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, ← mt_mul, inv_mul_cancel, mt_one, Matrix.one_mulVec]
  have e' : ∀ y, mt S g *ᵥ (mt S g⁻¹ *ᵥ y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, ← mt_mul, mul_inv_cancel, mt_one, Matrix.one_mulVec]
  refine ⟨fun y hy => ?_, pre_den _ h.2.1, fun y hy => ?_⟩
  · rw [← e y]; exact mulVec_mem_idAt _ (h.1 _ hy)
  · rw [mem_pre, h.2.2 _ (mulVec_mem_idAt _ hy)]
    constructor
    · intro H x hx
      rw [← hermAt_unitary S g]; exact H _ hx
    · intro H x hx
      rw [← e' x, hermAt_unitary]
      exact H _ (by rw [mem_pre, e']; exact hx)

theorem split_of_le {S A B : HSp D} (o : OrthDec S A B) {v : Pl D} {M : AddSubgroup (Fin S.rank → AE D)}
    {Λ : AddSubgroup (Fin B.rank → AE D)} (hM : IsSDAt S v M) (hΛ : IsSDAt B v Λ) (hle : ∀ l ∈ Λ, o.jB *ᵥ l ∈ M) :
    IsSDAt A v (pre o.jA M) ∧ ∀ y, y ∈ M ↔ o.pA *ᵥ y ∈ pre o.jA M ∧ o.pB *ᵥ y ∈ Λ := by
  have hsum : ∀ y, o.jA *ᵥ (o.pA *ᵥ y) + o.jB *ᵥ (o.pB *ᵥ y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, o.sum_eq_one, Matrix.one_mulVec]
  have eA : ∀ x, o.pA *ᵥ (o.jA *ᵥ x) = x := fun x => by rw [Matrix.mulVec_mulVec, o.pA_jA, Matrix.one_mulVec]
  have hB : ∀ y ∈ M, o.pB *ᵥ y ∈ Λ := fun y hy => by
    rw [hΛ.2.2 _ (mulVec_mem_idAt _ (hM.1 y hy))]
    intro l hl
    rw [← hermAt_jB]
    exact (hM.2.2 y (hM.1 y hy)).1 hy _ (hle l hl)
  have hA : ∀ y ∈ M, o.pA *ᵥ y ∈ pre o.jA M := fun y hy => by
    rw [mem_pre, eq_sub_of_add_eq (hsum y)]
    exact sub_mem hy (hle _ (hB y hy))
  refine ⟨⟨fun x hx => ?_, pre_den _ hM.2.1, fun x hx => ?_⟩, fun y => ⟨fun hy => ⟨hA y hy, hB y hy⟩, fun hy => ?_⟩⟩
  · rw [← eA x]; exact mulVec_mem_idAt _ (hM.1 _ hx)
  · rw [mem_pre, hM.2.2 _ (mulVec_mem_idAt _ hx)]
    constructor
    · intro H x' hx'
      rw [← eA x', ← hermAt_jA]; exact H _ hx'
    · intro H y hy
      rw [hermAt_jA]; exact H _ (hA y hy)
  · rw [← hsum y]; exact add_mem hy.1 (hle _ hy.2)

theorem smul_mem_latA {S : HSp D} {L : Lat S} {P : Pl D → Prop} {a : D.host.E} (ha : a ∈ D.host.AA)
    {y : Fin S.rank → AE D} (hy : y ∈ latV S L P) : incA D a • y ∈ latA S L P := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, h0, b, hb, x, hx, rfl⟩ := hy
    obtain rfl : b = 1 := hb
    refine AddSubgroup.subset_closure ⟨α, hα, h0, a, ha, x, hx, funext fun i => ?_⟩
    change ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (_ ⊗ₜ[D.host.F] _) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem smul_mem_latV {S : HSp D} {L : Lat S} {P : Pl D → Prop} {b : D.host.E} (hb : b ∈ D.host.AA⁻¹)
    {y : Fin S.rank → AE D} (hy : y ∈ latA S L P) : incA D b • y ∈ latV S L P := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, h0, a, ha, x, hx, rfl⟩ := hy
    have h1 : a * b ∈ D.host.AA * D.host.AA⁻¹ := FractionalIdeal.mul_mem_mul ha hb
    rw [mul_inv_cancel₀ (GlobalTheory.ModelLatticeCheck.AA_ne_zero D)] at h1
    obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff _).1 h1
    refine AddSubgroup.subset_closure ⟨α, hα, h0, 1, rfl, c • x, L.smul_mem c hx, funext fun i => ?_⟩
    change ((1 : AF D.host.F) ⊗ₜ[D.host.F] b) * (_ ⊗ₜ[D.host.F] _) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul, Pi.smul_apply, Algebra.smul_def c, hc, ← mul_assoc, mul_comm b]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem mem_latV_of_forall {S : HSp D} {L : Lat S} {P : Pl D → Prop} {y : Fin S.rank → AE D}
    (h : ∀ a ∈ D.host.AA, incA D a • y ∈ latA S L P) : y ∈ latV S L P := by
  have key : ∀ c ∈ ((D.host.AA : Submodule (𝓞 D.host.E) D.host.E) * (D.host.AA⁻¹ : FractionalIdeal _ D.host.E)),
      incA D c • y ∈ latV S L P := by
    intro c hc
    refine Submodule.mul_induction_on hc (fun a ha b hb => ?_) fun c c' h1 h2 => ?_
    · rw [mul_comm, map_mul, mul_smul]
      exact smul_mem_latV hb (h a ha)
    · rw [map_add, add_smul]; exact add_mem h1 h2
  have := key 1 (by
    rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ (GlobalTheory.ModelLatticeCheck.AA_ne_zero D)]
    exact FractionalIdeal.one_mem_one _)
  rwa [map_one, one_smul] at this

theorem exists_eq_smul {L : HSp D} {ζ : Fin L.rank → D.host.E} (h : IsLineVec L ζ) (l : Fin L.rank → AE D) :
    ∃ a : AE D, l = a • ratV ζ := by
  have hs : ∀ i j : Fin L.rank, i = j := fun i j => Fin.ext (by have := h.1; omega)
  obtain ⟨i, hi⟩ : ∃ i, ζ i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply h.2
    rw [show ζ = 0 from funext hcon]
    simp
  refine ⟨l i * incA D (ζ i)⁻¹, funext fun j => ?_⟩
  rw [hs j i, Pi.smul_apply, smul_eq_mul, ratV, mul_assoc, ← map_mul, inv_mul_cancel₀ hi, map_one, mul_one]

theorem ratV_vecB {S A L : HSp D} (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) :
    ratV (vecB o ζ) = o.jB *ᵥ ratV ζ :=
  funext fun i => RingHom.map_mulVec (incA D) o.iB ζ i

theorem emb_mem_grpAt {S A B : HSp D} (o : OrthDec S A B) {P : Pl D → Prop} {a : GA D A} (ha : a ∈ grpAt A P) :
    o.emb (a, 1) ∈ grpAt S P := by
  have ha' := (mem_congGrp_iff A (idAt D P) a).1 ha
  refine (mem_congGrp_iff S (idAt D P) _).2 fun i j => ?_
  have e : mt S (o.emb (a, 1)) - 1 = o.jA ⬝ (mt A a - 1) ⬝ o.pA := by
    rw [o.mt_emb, ← o.sum_eq_one, Matrix.mul_sub, Matrix.sub_mul, mt_one, Matrix.mul_one, Matrix.mul_one]
    abel
  rw [← Matrix.sub_apply, e, Matrix.mul_apply]
  refine Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ ?_
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (by rw [Matrix.sub_apply]; exact ha' l k)

theorem line_le {S A L : HSp D} (o : OrthDec S A L) {ζ : Fin L.rank → D.host.E} (hζ : IsLineVec L ζ) {L₀ : Lat S} {LA : Lat A}
    {LL : Lat L} {v : Pl D} (hO : OrthAt o L₀ LA LL v) (g : Mx D S.rank S.rank)
    (hz : ∀ a : AE D, a • ratV (vecB o ζ) ∈ latA S L₀ (· = v) → g *ᵥ (a • ratV (vecB o ζ)) ∈ latA S L₀ (· = v))
    (l : Fin L.rank → AE D) (hl : l ∈ latV L LL (· = v)) : o.jB *ᵥ l ∈ pre g (latV S L₀ (· = v)) := by
  have h1 : o.jB *ᵥ l ∈ latV S L₀ (· = v) := by
    refine (hO _).2 ?_
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, o.pA_jB, o.pB_jB, Matrix.zero_mulVec, Matrix.one_mulVec]
    exact ⟨zero_mem _, hl⟩
  obtain ⟨c, rfl⟩ := exists_eq_smul hζ l
  rw [Matrix.mulVec_smul, ← ratV_vecB] at h1 ⊢
  refine mem_pre.2 (mem_latV_of_forall fun a ha => ?_)
  have h2 := smul_mem_latA ha h1
  rw [smul_smul] at h2
  rw [← Matrix.mulVec_smul, smul_smul]
  exact hz _ h2

theorem moves_of_split {S A B : HSp D} (o : OrthDec S A B) {L₀ : Lat S} {LA : Lat A} {LB : Lat B} {v : Pl D}
    (hO : OrthAt o L₀ LA LB v) (γ : GA D S) (a : GA D A) {Λ : AddSubgroup (Fin A.rank → AE D)}
    (hsplit : ∀ y, y ∈ pre (mt S γ⁻¹) (latV S L₀ (· = v)) ↔ o.pA *ᵥ y ∈ Λ ∧ o.pB *ᵥ y ∈ latV B LB (· = v))
    (hmv : ∀ y : Fin A.rank → AE D, (∀ i, y i ∈ idAt D (· = v)) → (y ∈ latV A LA (· = v) ↔ mt A a *ᵥ y ∈ Λ)) :
    Moves S ((o.emb (a, 1))⁻¹ * γ) L₀ L₀ (· = v) := by
  intro y hy
  obtain ⟨z, hzdef⟩ : ∃ z, z = mt S ((o.emb (a, 1))⁻¹ * γ) *ᵥ y := ⟨_, rfl⟩
  rw [← hzdef]
  have hzI : ∀ i, z i ∈ idAt D (· = v) := by rw [hzdef]; exact mulVec_mem_idAt _ hy
  have hw : y = mt S γ⁻¹ *ᵥ (mt S (o.emb (a, 1)) *ᵥ z) := by
    rw [hzdef, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← mt_mul, ← mt_mul]
    have : γ⁻¹ * o.emb (a, 1) * ((o.emb (a, 1))⁻¹ * γ) = 1 := by group
    rw [this, mt_one, Matrix.one_mulVec]
  have key := hsplit (mt S (o.emb (a, 1)) *ᵥ z)
  rw [mem_pre, ← hw] at key
  rw [key, hO z, Matrix.mulVec_mulVec, o.pA_emb, Matrix.mulVec_mulVec, o.pB_emb, mt_one, Matrix.one_mul,
    ← Matrix.mulVec_mulVec, ← hmv _ (mulVec_mem_idAt _ hzI)]

theorem orbitSplit : ∀ D : D7, GlobalTheory.FinPl.OrbitSplit D := by
  intro D σ B L₀ v hT hL₀ ⟨LA, LL, hLA, hLL, hO⟩ γ hγ hz
  have hM := isSDAt_pre_unitary (GlobalTheory.T.isSelfDualLatticeAtPlace_latticeCompletion D B.V₀ L₀ v hL₀) γ⁻¹
  obtain ⟨hA, hsplit⟩ := split_of_le B.o hM (GlobalTheory.T.isSelfDualLatticeAtPlace_latticeCompletion D B.L LL v hLL) (line_le B.o B.line hO _ hz)
  obtain ⟨a, ha, hmv⟩ := GlobalTheory.T.selfDualLattices_single_orbit_tamePlace D B.A v _ _ hT (GlobalTheory.T.isSelfDualLatticeAtPlace_latticeCompletion D B.A LA v hLA) hA
  exact ⟨a, ha, (B.o.emb (a, 1))⁻¹ * γ, ⟨mul_mem (inv_mem (emb_mem_grpAt B.o ha)) hγ,
    moves_of_split B.o hO γ a hsplit hmv⟩, (mul_inv_cancel_left _ _).symm⟩

end GlobalTheory.FinPl.SplitOrbit

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedConjugatePlaceInverseUniformizerValueStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_conjugate_place_inverse_uniformizer_value : ∀ (D : D7) (χ : (AE D)ˣ →* Circle), ResEta D χ 0 → ∀ w w' : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = w'.under (𝓞 D.host.F) → w ≠ w' → GlobalTheory.LFun.UnrAt (F := D.host.F) χ w → GlobalTheory.LFun.UnrAt (F := D.host.F) χ w' ∧ GlobalTheory.LFun.val (F := D.host.F) χ w' = (GlobalTheory.LFun.val (F := D.host.F) χ w)⁻¹ := by
  first | exact @GlobalTheory.SplitUnr.unrAt_and_val_inv | exact GlobalTheory.SplitUnr.unrAt_and_val_inv | (intros; apply GlobalTheory.SplitUnr.unrAt_and_val_inv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumInertPlaceStandardCayleyPairStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilDatum_inertPlace_standard_cayley_pair : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsInertAt D.host.F D.host.E v w → UnrAt χS w → UnrAt χT w → ∀ c ϖ eS eT, IsUnramInv ϖ c (qV D.host.F v) → IsInertChart D.sp.cm.sig S.gram (frameLat S) h c eS → IsInertChart D.sp.cm.sig T.gram (frameLat T) h c eT → ∀ f, VacFin ψ S T v f → f ≠ 0 → ∃ (δ : w.adicCompletion D.host.E) (ψ' : AddChar (w.adicCompletion D.host.E) ℂ) (M : Submodule ℂ (WO S T → ℂ)) (ρ : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E) → Module.End ℂ M) (ω : GU c S.rank × GU c T.rank →* Module.End ℂ M) (s : M), IsStd ϖ c (qV D.host.F v) δ ψ' ρ ω s ∧ (s : WO S T → ℂ) = f ∧ (∀ g g' (m : M), ((ω (g, g') m : M) : WO S T → ℂ) = om (embV S v (eS.symm g), embV T v (eT.symm g')) m) ∧ CayleyRule (qV D.host.F v) T.rank ρ (ω.comp (MonoidHom.inl _ _)) s ∧ CayleyRule (qV D.host.F v) S.rank ρ (ω.comp (MonoidHom.inr _ _)) s := by
  first | exact @GlobalTheory.ChainOnto.std_cayley_of_inert | exact GlobalTheory.ChainOnto.std_cayley_of_inert | (intros; apply GlobalTheory.ChainOnto.std_cayley_of_inert <;> assumption)
end

