import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0028
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ComparisonZeroEmbedding
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0483
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepLevelContainsDeepCongruenceAtBadPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0471
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0486
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCutQGrp
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0027
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.Bundle0001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008
import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle0007
import Formalism.LocalRingCardinality.FactDelDualNabla
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0475
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0452
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymmetricPositionColumnCondIffCongruenceConj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0453
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimPartsAtIffBadAndOff
import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypePrimeRowTypeTopRestrictionMulLevelCharEqOne

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceEmbeddingAtOrbitPositionEqInduced
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.KerOne

theorem splitPlace_embedding_at_orbitPosition_eq_induced : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (_ : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∀ (q : Fin ((w.D Z).gat u v hg).P.nV) (s : Fin (((w.D Z).gat u v hg).P.n' q)) (x : (w.D Z).host.E),
        ((w.D Z).gat u v hg).P.ι q ((((w.D Z).gat u v hg).P.σ q ^ s.val) (GlobalTheory.Mem.Top.KerOne.iw0 t.full.1.g u v hg q x)) =
          t.cmp.embW u v hg (tauLL (w.D Z) (t.Gt.gat_pos u v hg ⟨q, s⟩) (if s.val % 2 = 1 then (w.D Z).host.conj x else x)) := by
  intro K B f T w _ _ _ Z t _ _ _ _ _ _ _ _ _ _ _ u v hg
  haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
  intro q s x
  have h := (t.g.cmp.tie u v hg).pos_emb q s x
  have key : ∀ (X : Formalism.L2.Herm.Herm0 (w.D Z)) (Bm : GL (Fin (w.D Z).R.k) (w.D Z).host.E), X = t.full.1.to0 →
      (Formalism.L2.G.Cmp.locAt X u v hg Bm).iw q x = iw0 t.full.1.g u v hg q x := by
    rintro X Bm rfl; rfl
  rw [key _ _ t.herm_eq] at h
  rw [← h]
  have h3 : Formalism.L2.Forms.sigD (w.D Z) x = (w.D Z).host.conj x := Formalism.BasicNotions.bridge_star_holds (w.D Z).R (w.D Z).host x
  rw [h3]
  show _ = (t.cmp.embW u v hg) (Formalism.L2.G.Cmp.tEL (w.D Z) _ _)
  congr 2
  by_cases hs : s.val % 2 = 1
  · have : ¬ Even s.val := by rw [Nat.not_even_iff_odd, Nat.odd_iff]; exact hs
    simp [hs, this]
  · have : Even s.val := by rw [Nat.even_iff]; omega
    simp [hs, this]

end GlobalTheory.Mem.Top.KerOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepLevelContainsDeepCongruenceAtBadPrimeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepLevel_contains_deep_congruence_at_bad_prime : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (a : I.ι) (T i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) T (I.rec7 l Z).R.f bad) (P : SBof I a) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) → ∃ N : ℕ, ∀ z ∈ UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), (∀ v', v' ≠ v → bc (prV (E := (I.rec7 l Z).host.E) v') z = 1) → GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) N z → z ∈ S.U := by
  first | exact @GlobalTheory.Mem.Col2.AdT.Opn.level_contains_deep | exact GlobalTheory.Mem.Col2.AdT.Opn.level_contains_deep | (intros; apply GlobalTheory.Mem.Col2.AdT.Opn.level_contains_deep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepPointDeterminedByLatticeInvariantsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepPoint_determined_by_latticeInvariants : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}, (∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs) → (∀ w ∈ Pr.vGs, ((Formalism.L2.Col.qOf w : ℕ) : 𝓞 X.E) ∉ w.asIdeal ^ 2) → GlobalTheory.Mem.Col2.ChEx.PtDet (GlobalTheory.Mem.Col2.ChEx.cqOf (R := R) (cst := cst) (u := u) (j := j) : PtAt R sel mu cst u j → _) := by
  first | exact @GlobalTheory.Mem.Col2.ChEx.ptDet_cqOf | exact GlobalTheory.Mem.Col2.ChEx.ptDet_cqOf | (intros; apply GlobalTheory.Mem.Col2.ChEx.ptDet_cqOf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportDegreeEqOfMemWeightPolynomials
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.WtHomog

open MvPolynomial

theorem coeff_aeval_diag {K : Type} [Field K] {σ : Type} (c : σ → K) (Q : MvPolynomial σ K)
    (e : σ →₀ ℕ) :
    MvPolynomial.coeff e (aeval (fun v => C (c v) * X v) Q : MvPolynomial σ K)
      = (e.prod fun v k => c v ^ k) * MvPolynomial.coeff e Q := by
  classical
  induction Q using MvPolynomial.induction_on' generalizing e with
  | monomial u a =>
    have h : (aeval (fun v => C (c v) * X v) (monomial u a) : MvPolynomial σ K)
        = monomial u ((u.prod fun v k => c v ^ k) * a) := by
      rw [aeval_monomial]
      simp only [mul_pow, Finsupp.prod_mul, ← map_pow]
      rw [show (u.prod fun v k => (C (c v ^ k) : MvPolynomial σ K))
            = C (u.prod fun v k => c v ^ k) from (map_finsuppProd C _ _).symm]
      rw [show (u.prod fun v k => (X v : MvPolynomial σ K) ^ k) = monomial u 1 from
        (monomial_eq (s := u) (a := (1 : K))).symm ▸ by simp]
      rw [algebraMap_eq, ← mul_assoc, ← C_mul, C_mul_monomial]
      simp [mul_comm]
    rw [h, coeff_monomial, coeff_monomial]
    by_cases hue : u = e
    · subst hue; simp
    · simp [hue]
  | add p q hp hq =>
    rw [map_add, coeff_add, coeff_add, hp, hq, mul_add]

theorem deg_eq_of_mem_wtPol : ∀ {K : Type} [Field K] [CharZero K] {ι : Type} [Fintype ι] {n : ℕ} (ν : ι → Fin n → ℕ)
    (Q : MvPolynomial (ι × Fin n × Fin n) K) (hQ : Q ∈ WtPol K ν), ∀ e ∈ Q.support, ∀ τ, ∑ α, ∑ s, e (τ, α, s) = ∑ r, ν τ r := by
  intro K _ _ ι _ n ν Q hQ e he τ
  classical
  set c : ι → K := fun σ => if σ = τ then 2 else 1 with hc
  set β : ι → Matrix (Fin n) (Fin n) K := fun σ => c σ • (1 : Matrix (Fin n) (Fin n) K) with hβ
  have hc0 : ∀ σ, c σ ≠ 0 := by
    intro σ; simp only [hc]; split_ifs <;> norm_num
  have hbor : IsBor β := by
    intro σ
    refine ⟨fun r s hsr => ?_, fun r => ?_⟩
    · simp [hβ, Matrix.one_apply, (ne_of_lt hsr).symm]
    · simpa [hβ] using hc0 σ
  have hsub : colSub β = aeval (fun v : ι × Fin n × Fin n => C (c v.1) * X v) := by
    unfold colSub
    congr 1
    funext v
    obtain ⟨σ, α, s⟩ := v
    simp only [hβ, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single s]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  have hw := hQ β hbor
  rw [hsub] at hw
  have hcoef := congrArg (MvPolynomial.coeff e) hw
  rw [coeff_aeval_diag, coeff_smul] at hcoef
  have hne : MvPolynomial.coeff e Q ≠ 0 := mem_support_iff.mp he
  have hL : (e.prod fun v k => c v.1 ^ k) = (2 : K) ^ (∑ α, ∑ s, e (τ, α, s)) := by
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type,
      Finset.prod_eq_single τ]
    · rw [Fintype.prod_prod_type]
      simp only [hc, if_true, Finset.prod_pow_eq_pow_sum]
    · intro σ _ hσ
      simp [hc, hσ]
    · simp
  have hR : (∏ σ, ∏ r, β σ r r ^ ν σ r) = (2 : K) ^ (∑ r, ν τ r) := by
    rw [Finset.prod_eq_single τ]
    · simp [hβ, hc, Finset.prod_pow_eq_pow_sum]
    · intro σ _ hσ
      simp [hβ, hc, hσ]
    · simp
  rw [hL, hR, smul_eq_mul] at hcoef
  have heq := mul_right_cancel₀ hne hcoef
  have h2 : ((2 : ℕ) ^ (∑ α, ∑ s, e (τ, α, s))) = (2 : ℕ) ^ (∑ r, ν τ r) := by
    exact_mod_cast heq
  exact Nat.pow_right_injective (le_refl 2) h2

end GlobalTheory.Mem.WtHomog
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymmetricCharResidueConjEqWeightedUnipotentSumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricCharResidue_conj_eq_weightedUnipotentSum : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal) → ∀ (kv : Σ k : Fin 2, D.nd.PlG k), ∀ k ∈ X.B.I.Kset, ∀ N : GL (Fin D.R.r) (ZMod (D.host.g kv.1)), GlobalTheory.Mem.SymFrame.IsMatIn X (D.naut.plGw kv.1 kv.2) (GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2)) k (N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) → N ∈ unipSym (ZMod (D.host.g kv.1)) D.R.r D.R.rS D.R.k → GlobalTheory.Mem.SymChar.ModW X (D.naut.plGw kv.1 kv.2) (sigA X.B.I (GlobalTheory.Mem.SymChar.argS X k)) (∑ i, ∑ j, if symEdge D.R.rS D.R.k i j then ((GlobalTheory.Mem.SymChar.wtB D.R.rS D.R.k (GlobalTheory.Mem.SymChar.side X (D.naut.plGw kv.1 kv.2)) i j : ℤ) : ZMod (D.host.g kv.1)) * (N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) i j else 0) := by
  first | exact @GlobalTheory.Mem.SymChar.ResBar.resBar | exact GlobalTheory.Mem.SymChar.ResBar.resBar | (intros; apply GlobalTheory.Mem.SymChar.ResBar.resBar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymmetricPositionColumnCondIffCongruenceConjStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricPositionColumnCond_iff_congruence_conj : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal) → ∀ k ∈ X.B.I.Kset, ∀ kv : (Σ k : Fin 2, D.nd.PlG k), (GlobalTheory.Mem.GroupLoc.ColCond X (D.naut.plGw kv.1 kv.2) k ↔ GlobalTheory.Mem.GroupLoc.CondAt X (D.naut.plGw kv.1 kv.2) k ∧ GlobalTheory.Mem.GroupLoc.CondAt X (GlobalTheory.DimPartsCompare.cPl (D.naut.plGw kv.1 kv.2)) k) := by
  first | exact @GlobalTheory.Mem.GroupLoc.Dual.colCond_iff_condAt | exact GlobalTheory.Mem.GroupLoc.Dual.colCond_iff_condAt | (intros; apply GlobalTheory.Mem.GroupLoc.Dual.colCond_iff_condAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TargetPairingSizesInCoefficientFieldValueGroup
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.KerVal
open MvPolynomial

theorem deX_map {Lt k k' : Type} [Fintype Lt] [CommRing k] [CommRing k'] (f : k →+* k') (N : ℕ) (nu : Lt → YoungDiagram)
    (y : Lt → Fin N → ℕ → k) : MvPolynomial.map f (GL3Columns.DeX N nu y) = GL3Columns.DeX N nu (fun s a j => f (y s a j)) := by
  unfold GL3Columns.DeX
  simp only [map_prod, RingHom.map_det]
  refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => congrArg Matrix.det ?_
  ext i j
  simp [map_sum, map_mul, map_C, map_X]

theorem dual_map_eval {σ V k : Type} [Field k] (χ : Module.Dual k (MvPolynomial σ k)) (p : MvPolynomial σ (MvPolynomial V k)) (x : V → k) :
    MvPolynomial.eval x (∑ m ∈ p.support, coeff m p * C (χ (monomial m 1))) = χ (MvPolynomial.map (MvPolynomial.eval x) p) := by
  conv_rhs => rw [p.as_sum]
  rw [map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, eval_C, map_monomial]
  rw [show monomial m (MvPolynomial.eval x (coeff m p)) = (MvPolynomial.eval x (coeff m p)) • (monomial m 1 : MvPolynomial σ k) by
    rw [smul_monomial, smul_eq_mul, mul_one]]
  rw [map_smul, smul_eq_mul]

end GlobalTheory.KerVal

namespace GlobalTheory.KerVal
open MvPolynomial Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.G

variable {D : D7} (w : D.what₂.places.Pl) (N : ℕ) (nu : Bool × HH D → YoungDiagram)

def uFr : Bool × HH D → Fin N → ℕ → MvPolynomial (GL3Theta.FrV D N) (Cw D w) :=
  fun s a j => if h : j < N then X (tauPl D s, a, ⟨j, h⟩) else 0

def canPol (χ : Module.Dual (Cw D w) (MvPolynomial ((Bool × HH D) × ℕ × Fin N) (Cw D w))) : MvPolynomial (GL3Theta.FrV D N) (Cw D w) :=
  ∑ m ∈ (GL3Columns.DeX N nu (uFr w N)).support, coeff m (GL3Columns.DeX N nu (uFr w N)) * C (χ (monomial m 1))

theorem canM_apply (χ : Module.Dual (Cw D w) (MvPolynomial ((Bool × HH D) × ℕ × Fin N) (Cw D w))) (y : FrP D w N) :
    canM D w N nu χ y = χ (GL3Columns.DeX N nu fun s => GL3Columns.colsOf (y (tauPl D s))) := rfl

theorem canM_eq_eval (χ : Module.Dual (Cw D w) (MvPolynomial ((Bool × HH D) × ℕ × Fin N) (Cw D w))) (y : FrP D w N) :
    canM D w N nu χ y = MvPolynomial.eval (fun v : GL3Theta.FrV D N => y v.1 v.2.1 v.2.2) (canPol w N nu χ) := by
  have e1 : (fun s a j => MvPolynomial.eval (fun v : GL3Theta.FrV D N => y v.1 v.2.1 v.2.2) (uFr w N s a j)) =
      fun s => GL3Columns.colsOf (y (tauPl D s)) := by
    funext s a j
    unfold uFr GL3Columns.colsOf
    split_ifs <;> simp
  unfold canPol
  rw [dual_map_eval, deX_map, e1, canM_apply]

theorem canM_ker (hfit : ∀ s c, (nu s).colLen c ≤ N) (χ : Module.Dual (Cw D w) (MvPolynomial ((Bool × HH D) × ℕ × Fin N) (Cw D w)))
    (h0 : ∀ y, canM D w N nu χ y = 0) (J : KM.ColChoice N nu) :
    χ (MvPolynomial.map (Int.castRingHom _) (KM.nablaX N nu J)) = 0 := by
  refine GL3Columns.wwInj_holds D (D.what₂.places.resChar w) N nu χ (fun y => ?_) J
  let e := Equiv.ofBijective (tauPl D) (Formalism.L2.DIV.tauPl_bijective D)
  have h1 : χ (GL3Columns.DeX N nu fun s => GL3Columns.colsOf ((fun τ (a b : Fin N) => y (e.symm τ) a (b : ℕ)) (tauPl D s))) = 0 :=
    h0 (fun τ (a b : Fin N) => y (e.symm τ) a (b : ℕ))
  refine Eq.trans (congrArg χ ?_) h1
  unfold GL3Columns.DeX
  refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => congrArg Matrix.det ?_
  ext i j
  have hj : (j : ℕ) < N := lt_of_lt_of_le j.2 (hfit s c)
  have hs : e.symm (tauPl D s) = s := e.symm_apply_apply s
  simp only [Matrix.of_apply, GL3Columns.colsOf, dif_pos hj, hs]

end GlobalTheory.KerVal

namespace GlobalTheory.KerVal
open MvPolynomial Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.G

variable {D : D7} (P : Examples₂.EntPl D) (w : D.what₂.places.Pl) (N : ℕ) (nu : Bool × HH D → YoungDiagram)

theorem colsOf_map {k k' : Type} [CommRing k] [CommRing k'] (f : k →+* k') {M : ℕ} (Y : Matrix (Fin M) (Fin M) k) (a : Fin M) (j : ℕ) :
    f (GL3Columns.colsOf Y a j) = GL3Columns.colsOf (Y.map f) a j := by
  unfold GL3Columns.colsOf
  split_ifs <;> simp

theorem onMin_canInv_mem (hfit : ∀ s c, (nu s).colLen c ≤ N) (F : FrP D w N → Cw D w) (hF : F ∈ LinearMap.range (canM D w N nu))
    (hrat : ∀ y : D.what₂.Tau → Matrix (Fin N) (Fin N) D.what₂.LL, ∃ x, F (fun τ => (y τ).map (P.iL w)) = P.iL w x)
    (J : KM.ColChoice N nu) : ∃ b : D.what₂.LL, onMin D w N nu (canInv D w N nu F) J = P.iL w b := by
  set ψ := canInv D w N nu F with hψdef
  have hψ : canM D w N nu ψ = F := canInv_spec D w N nu F hF
  letI : Algebra D.what₂.LL (Cw D w) := (P.iL w).toAlgebra
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap D.what₂.LL (Cw D w))
    (LinearMap.ker_eq_bot.2 (P.iL w).injective)
  let ρ : Cw D w → Cw D w := fun z => P.iL w (π z)
  have ρ_add : ∀ a b, ρ (a + b) = ρ a + ρ b := fun a b => by
    simp only [ρ, map_add]
  have ρ_mul : ∀ x z, ρ (P.iL w x * z) = P.iL w x * ρ z := fun x z => by
    have : P.iL w x * z = x • z := by rw [Algebra.smul_def]; rfl
    simp only [ρ, this, map_smul, smul_eq_mul, map_mul]
  have ρ_fix : ∀ x, ρ (P.iL w x) = P.iL w x := fun x => by
    have := LinearMap.congr_fun hπ x
    simp only [ρ]
    exact congrArg (P.iL w) this
  let ψ' : Module.Dual (Cw D w) (MvPolynomial ((Bool × HH D) × ℕ × Fin N) (Cw D w)) :=
    (MvPolynomial.basisMonomials _ (Cw D w)).constr (Cw D w) fun m => ρ (ψ (monomial m 1))
  have ψ'_mon : ∀ m, ψ' (monomial m 1) = ρ (ψ (monomial m 1)) := fun m => by
    have := (MvPolynomial.basisMonomials ((Bool × HH D) × ℕ × Fin N) (Cw D w)).constr_basis (Cw D w)
      (fun m => ρ (ψ (monomial m 1))) m
    rw [MvPolynomial.coe_basisMonomials] at this
    exact this
  have key : ∀ q : MvPolynomial ((Bool × HH D) × ℕ × Fin N) D.what₂.LL,
      ψ' (MvPolynomial.map (P.iL w) q) = ρ (ψ (MvPolynomial.map (P.iL w) q)) := by
    intro q
    induction q using MvPolynomial.induction_on' with
    | monomial m x =>
      have e : MvPolynomial.map (P.iL w) (monomial m x) = P.iL w x • (monomial m 1 : MvPolynomial _ (Cw D w)) := by
        rw [map_monomial, smul_monomial, smul_eq_mul, mul_one]
      rw [e, map_smul, map_smul, smul_eq_mul, smul_eq_mul, ρ_mul, ψ'_mon]
    | add p q hp hq =>
      rw [map_add, map_add, map_add, hp, hq, ρ_add]
  have hpt : ∀ y : D.what₂.Tau → Matrix (Fin N) (Fin N) D.what₂.LL,
      canM D w N nu ψ' (fun τ => (y τ).map (P.iL w)) = canM D w N nu ψ (fun τ => (y τ).map (P.iL w)) := by
    intro y
    have e : (GL3Columns.DeX N nu fun s => GL3Columns.colsOf ((fun τ => (y τ).map (P.iL w)) (tauPl D s))) =
        MvPolynomial.map (P.iL w) (GL3Columns.DeX N nu fun s => GL3Columns.colsOf (y (tauPl D s))) := by
      rw [deX_map]
      congr 1
      funext s a j
      rw [colsOf_map]
    rw [canM_apply, canM_apply, e, key, ← e]
    change ρ (canM D w N nu ψ (fun τ => (y τ).map (P.iL w))) = canM D w N nu ψ (fun τ => (y τ).map (P.iL w))
    obtain ⟨x, hx⟩ := hrat y
    rw [hψ, hx, ρ_fix]
  have hCZ : Set.Infinite (Set.range (Nat.cast : ℕ → Cw D w)) := Set.infinite_range_of_injective Nat.cast_injective
  have hpol : canPol w N nu (ψ' - ψ) = 0 := by
    refine MvPolynomial.funext_set (fun _ => Set.range (Nat.cast : ℕ → Cw D w)) (fun _ => hCZ) fun x hx => ?_
    choose n hn using fun v => hx v (Set.mem_univ v)
    have e : (fun v : GL3Theta.FrV D N => x v) = fun v => ((fun τ => (Matrix.of fun a b => ((n (τ, a, b) : ℕ) : D.what₂.LL)).map (P.iL w)) :
        FrP D w N) v.1 v.2.1 v.2.2 := by
      funext v
      simp [hn]
    have h1 := canM_eq_eval w N nu (ψ' - ψ) (fun τ => (Matrix.of fun a b => ((n (τ, a, b) : ℕ) : D.what₂.LL)).map (P.iL w))
    simp only [map_sub, Pi.sub_apply, hpt, sub_self] at h1
    rw [map_zero, show x = _ from e]
    exact h1.symm
  have h0 : ∀ y, canM D w N nu (ψ' - ψ) y = 0 := fun y => by
    rw [canM_eq_eval, hpol, map_zero]
  have hJ := canM_ker w N nu hfit (ψ' - ψ) h0 J
  have eJ : MvPolynomial.map (Int.castRingHom (Cw D w)) (KM.nablaX N nu J) =
      MvPolynomial.map (P.iL w) (MvPolynomial.map (Int.castRingHom D.what₂.LL) (KM.nablaX N nu J)) := by
    rw [MvPolynomial.map_map, RingHom.ext_int ((P.iL w).comp (Int.castRingHom _)) (Int.castRingHom _)]
  rw [LinearMap.sub_apply, sub_eq_zero, eJ, key] at hJ
  exact ⟨π (ψ (MvPolynomial.map (Int.castRingHom (Cw D w)) (KM.nablaX N nu J))), by
    show ψ (MvPolynomial.map (Int.castRingHom (Cw D w)) (KM.nablaX N nu J)) = _
    rw [eJ]
    exact hJ.symm⟩

end GlobalTheory.KerVal

namespace GlobalTheory.KerVal
open MvPolynomial Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.G

theorem colLen_le_of_fits {D : D7} {N : ℕ} {nu : Bool × HH D → YoungDiagram} {ν : D.what₂.Tau → Fin N → ℕ} (h : NuFits D nu ν) :
    ∀ s c, (nu s).colLen c ≤ N := by
  intro s c
  by_contra hc
  have hm : (N, c) ∈ nu s := (nu s).mem_iff_lt_colLen.2 (lt_of_not_ge hc)
  have h1 := (nu s).mem_iff_lt_rowLen.1 hm
  rw [h.2 s N le_rfl] at h1
  exact Nat.not_lt_zero _ h1

theorem tgtFun_rat {D : D7} (P : Examples₂.EntPl D) (Bs : PlaceMatrixFamily D) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl) (i : ℕ)
    (c' : (D.chTw u μ).cls (i + 1)) (hE : ∀ τ j k, ∃ x : D.what₂.LL, Bs u μ w (i + 1) c' τ j k = P.iL w x) (v : polV D u (i + 1))
    (y : D.what₂.Tau → Matrix (Fin (D.R.N (i + 1))) (Fin (D.R.N (i + 1))) D.what₂.LL) :
    ∃ x, tgtFun P Bs u μ w i c' v (fun τ => (y τ).map (P.iL w)) = P.iL w x := by
  choose B' hB' using hE
  have hB : Bs u μ w (i + 1) c' = fun τ => (Matrix.of (B' τ)).map (P.iL w) := by
    funext τ
    ext j k
    exact hB' τ j k
  refine ⟨(∏ τ, (Matrix.of (B' τ)).det ^ (-(D.chTw u μ).sDiv i τ)) *
    MvPolynomial.eval (fun k : GL3Theta.FrV D (D.R.N (i + 1)) => (Matrix.of (B' k.1) * y k.1) k.2.1 k.2.2)
      (v : MvPolynomial (GL3Theta.FrV D (D.R.N (i + 1))) D.what₂.LL), ?_⟩
  show (∏ τ, (Bs u μ w (i + 1) c' τ).det ^ (-(D.chTw u μ).sDiv i τ)) *
    MvPolynomial.eval (fun k : GL3Theta.FrV D (D.R.N (i + 1)) => (Bs u μ w (i + 1) c' k.1 * (y k.1).map (P.iL w)) k.2.1 k.2.2)
      (MvPolynomial.map (P.iL w) (v : MvPolynomial (GL3Theta.FrV D (D.R.N (i + 1))) D.what₂.LL)) = _
  rw [hB, map_mul, map_prod]
  congr 1
  · refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_zpow₀, RingHom.map_det]
    rfl
  · have h2 := MvPolynomial.eval₂_comp_left (P.iL w) (RingHom.id D.what₂.LL)
      (fun k : GL3Theta.FrV D (D.R.N (i + 1)) => (Matrix.of (B' k.1) * y k.1) k.2.1 k.2.2)
      (v : MvPolynomial (GL3Theta.FrV D (D.R.N (i + 1))) D.what₂.LL)
    refine Eq.trans ?_ h2.symm
    rw [MvPolynomial.eval_map, RingHom.comp_id]
    congr 1
    funext k
    rw [Function.comp_apply, ← Matrix.map_mul]
    rfl

end GlobalTheory.KerVal

theorem GlobalTheory.KerVal.prTC_val : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → ColIn.JetsIn I → ∀ u μ w, LevFree Y u μ w → ∀ i, i < (I.rec7 l Z).R.m → ∀ (c' : ((I.rec7 l Z).chTw u μ).cls (i + 1)) (v' : ValQ O u μ (i + 1)) (J : KM.ColChoice ((I.rec7 l Z).R.N (i + 1)) (nuD (I.rec7 l Z) u i)), ∃ b : (I.rec7 l Z).what₂.LL, ‖prTC Pl O Bs u μ w i c' v' J‖ = ‖Pl.iL w b‖ := by
  intro B X I _ _ l Z _ Y O Pl Bs _ _ _ hEnt _ _ u μ w hw i hi c' v' J
  obtain ⟨b, hb⟩ := GlobalTheory.KerVal.onMin_canInv_mem Pl w _ _
    (GlobalTheory.KerVal.colLen_le_of_fits (nuFits_tgt (I.rec7 l Z) u i hi))
    (tgtFun Pl Bs u μ w i c' (secC O u μ (i + 1) v'))
    (canT_of Pl Bs (GlobalTheory.T.toy_entPl_canOnto _ Pl) u μ w i hi c' (secC O u μ (i + 1) v'))
    (GlobalTheory.KerVal.tgtFun_rat Pl Bs u μ w i c' (hEnt u μ w hw (i + 1) hi c') (secC O u μ (i + 1) v')) J
  exact ⟨b, congrArg norm hb⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistPrimeRowTypeTopRestrictionMulLevelCharEqOneStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistPrime_rowType_topRestriction_mul_levelChar_eq_one : ∀ {X : Fields} {R : Ranks} (ξ : Chr X.F X.E X.K) (Q : Finset (HeightOneSpectrum (𝓞 X.E))) (P : Q) (c M : ℕ), 1 ≤ M →
    ∀ (k : Formalism.L2.Col.GLint X.E (R.N R.m) P.1) (hk : k ∈ (levCong (N_m_succ R) P.1 c (rowTyQ R ξ Q P)).H)
    (g : Sp X.E (R.N R.m) ≃ₗ[X.E] Sp X.E (R.N R.m)) (g'' : Sp X.E ((R.N R.m - 1) + 0) ≃ₗ[X.E] Sp X.E ((R.N R.m - 1) + 0)),
    g'' ∈ LocE.JQ P.1 (qOf P.1) R.r (R.N R.m - 1) 0 →
    prXpG X.E (R.N R.m) ∘ₗ g.toLinearMap = g''.toLinearMap ∘ₗ prXpG X.E (R.N R.m) →
    CongE P.1 (2 * M) g (k⁻¹).1 →
    LocE.lamQB (resChar ξ P.1) R.r (R.N R.m - 1) g''.toLinearMap *
      (((levCong (N_m_succ R) P.1 c (rowTyQ R ξ Q P)).lam ⟨k, hk⟩ : X.Kˣ) : X.K) = 1 := by
  first | exact @GlobalTheory.TopRowsQ.lamQB_mul_levCong | exact GlobalTheory.TopRowsQ.lamQB_mul_levCong | (intros; apply GlobalTheory.TopRowsQ.lamQB_mul_levCong <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypePrimeRowTypeTopRestrictionMulLevelCharEqOneStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.typePrime_rowType_topRestriction_mul_levelChar_eq_one : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (w : {w // w ∈ Pr.vGs})
    (h0 : GL (Fin (R.N R.m - 1)) (𝓞 X.E ⧸ w.1.asIdeal)) (hh0 : h0 ∈ (rowTyG Ch (rPsymF Ch) w).H)
    (g g' : Sp X.E (R.N R.m) ≃ₗ[X.E] Sp X.E (R.N R.m)) (g'' : Sp X.E ((R.N R.m - 1) + 0) ≃ₗ[X.E] Sp X.E ((R.N R.m - 1) + 0)),
    g'' ∈ LocE.JGsym w.1 (qOf w.1) R.k R.rS R.r R.t (R.N R.m - 1) 0 →
    prXpG X.E (R.N R.m) ∘ₗ g.toLinearMap = g''.toLinearMap ∘ₗ prXpG X.E (R.N R.m) →
    g' ∈ Formalism.L2.Col.GLint X.E (R.N R.m) w.1 →
    (∀ x ∈ stdAt X.E (R.N R.m) w.1, redV w.1 (g' x) =
      ((diagEmb (𝓞 X.E ⧸ w.1.asIdeal) (Nat.sub_le (R.N R.m) 1) h0)⁻¹ : GL (Fin (R.N R.m)) (𝓞 X.E ⧸ w.1.asIdeal)).1.mulVec (redV w.1 x)) →
    CongE w.1 1 g g' →
    LocE.lamGBS (qOf w.1) (psi0P Ch w.1) (chiP Ch w.1) R.k R.r R.t R.m (R.N R.m - 1) 0 g''.toLinearMap *
      (((rowTyG Ch (rPsymF Ch) w).lam ⟨h0, hh0⟩ : X.Kˣ) : X.K) = 1 := by
  first | exact @GlobalTheory.Mem.Col2.AdT.lamGBS_top_mul_lam_eq_one | exact GlobalTheory.Mem.Col2.AdT.lamGBS_top_mul_lam_eq_one | (intros; apply GlobalTheory.Mem.Col2.AdT.lamGBS_top_mul_lam_eq_one <;> assumption)
end

