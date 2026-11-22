import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0452
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0005
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RationalRootsDef
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0387
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0396
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0441
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UfGLRatHom
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0270
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0295
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEmbFIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianFormLastCoordinateUniformizerVectorSelf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0328
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0454
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NeZeroTop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0445
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0158
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
import Formalism.LocalToGlobal.GlobalTheory.CoordinateLengths.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0455
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle0007
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
import Formalism.GradedWeylDivisibility.FinalD
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.LocalRingCardinality.FactDelDualNabla
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0053

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymEdgeConjWeightedSumEqFlagAndUnipotentPairs
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SymChar.Comb

def cw (ρ k : ℕ) (s : Bool) (i : ℕ) : ℤ :=
  if ρ ≤ i ∧ i + 1 ≠ ρ + k then (if i + 1 < ρ + k then (if s then 0 else -1) else if i = ρ + k then 1 else -1) else 0

theorem term_eq {R : Type} [CommRing R] (ρ k : ℕ) (s : Bool) {r : ℕ} (M : Matrix (Fin r) (Fin r) R) (i j : Fin r) :
    (if symEdge ρ k i j then ((GlobalTheory.Mem.SymChar.wtB ρ k s i j : ℤ) : R) * M i j else 0) =
      if j.val = i.val + 1 then ((cw ρ k s i.val : ℤ) : R) * M i j else 0 := by
  unfold symEdge GlobalTheory.Mem.SymChar.wtB cw
  simp only [Int.cast_ite, Int.cast_zero, Int.cast_one, Int.cast_neg]
  split_ifs <;> first | rfl | omega | (simp_all; done) | simp

theorem row_sum {R : Type} [CommRing R] {r : ℕ} (M : Matrix (Fin r) (Fin r) R) (c : R) (i : Fin r) :
    (∑ j : Fin r, if j.val = i.val + 1 then c * M i j else 0) =
      c * (if h : i.val + 1 < r then M i ⟨i.val + 1, h⟩ else 0) := by
  by_cases h : i.val + 1 < r
  · rw [dif_pos h]
    have : ∀ j : Fin r, (j.val = i.val + 1) ↔ j = ⟨i.val + 1, h⟩ := fun j => by simp [Fin.ext_iff]
    simp only [this]
    rw [Finset.sum_ite_eq']
    simp
  · rw [dif_neg h, mul_zero]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [if_neg]; omega

theorem nat_id {R : Type} [CommRing R] (ρ k : ℕ) (s : Bool) (F : ℕ → R) :
    (∑ i ∈ Finset.range (2 * ρ + k), ((cw ρ k s i : ℤ) : R) * F i) =
      (∑ a ∈ Finset.range ρ, if a + 1 < ρ then -F (2 * ρ + k - a - 1) else F (ρ + k)) +
        (if s then 0 else ∑ i ∈ Finset.range k, if i + 1 < k then -F (ρ + k - 2 - i) else 0) := by
  rw [← Finset.sum_range_add_sum_Ico _ (show ρ + k ≤ 2 * ρ + k by omega),
    ← Finset.sum_range_add_sum_Ico _ (show ρ ≤ ρ + k by omega),
    Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
  have h0 : (∑ i ∈ Finset.range ρ, ((cw ρ k s i : ℤ) : R) * F i) = 0 :=
    Finset.sum_eq_zero fun i hi => by
      simp only [Finset.mem_range] at hi
      simp [cw, show ¬ ρ ≤ i by omega]
  have h1 : (∑ t ∈ Finset.range (2 * ρ + k - (ρ + k)), ((cw ρ k s (ρ + k + t) : ℤ) : R) * F (ρ + k + t)) =
      ∑ a ∈ Finset.range ρ, if a + 1 < ρ then -F (2 * ρ + k - a - 1) else F (ρ + k) := by
    rw [show 2 * ρ + k - (ρ + k) = ρ by omega, ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun t ht => ?_
    simp only [Finset.mem_range] at ht
    unfold cw
    by_cases h : t + 1 < ρ
    · rw [if_pos h, if_pos (show ρ ≤ ρ + k + (ρ - 1 - t) ∧ ρ + k + (ρ - 1 - t) + 1 ≠ ρ + k by omega),
        if_neg (show ¬ (ρ + k + (ρ - 1 - t) + 1 < ρ + k) by omega),
        if_neg (show ¬ (ρ + k + (ρ - 1 - t) = ρ + k) by omega),
        show ρ + k + (ρ - 1 - t) = 2 * ρ + k - t - 1 by omega]
      simp
    · rw [if_neg h, if_pos (show ρ ≤ ρ + k + (ρ - 1 - t) ∧ ρ + k + (ρ - 1 - t) + 1 ≠ ρ + k by omega),
        if_neg (show ¬ (ρ + k + (ρ - 1 - t) + 1 < ρ + k) by omega),
        if_pos (show ρ + k + (ρ - 1 - t) = ρ + k by omega),
        show ρ + k + (ρ - 1 - t) = ρ + k by omega]
      simp
  have h2 : (∑ t ∈ Finset.range (ρ + k - ρ), ((cw ρ k s (ρ + t) : ℤ) : R) * F (ρ + t)) =
      if s then 0 else ∑ i ∈ Finset.range k, if i + 1 < k then -F (ρ + k - 2 - i) else 0 := by
    rw [show ρ + k - ρ = k by omega]
    cases s
    · simp only [Bool.false_eq_true, if_false]
      rw [← Finset.sum_range_reflect (fun i => if i + 1 < k then -F (ρ + k - 2 - i) else 0) k]
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; simp
      · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        rw [Finset.sum_range_succ, Finset.sum_range_succ']
        have e1 : ((cw ρ (k' + 1) false (ρ + k') : ℤ) : R) * F (ρ + k') = 0 := by
          unfold cw; rw [if_neg (by omega)]; simp
        have e2 : (if k' + 1 - 1 - 0 + 1 < k' + 1 then -F (ρ + (k' + 1) - 2 - (k' + 1 - 1 - 0)) else 0) = (0 : R) := by
          rw [if_neg (by omega)]
        rw [e1, e2, add_zero, add_zero]
        refine Finset.sum_congr rfl fun t ht => ?_
        simp only [Finset.mem_range] at ht
        rw [if_pos (show k' + 1 - 1 - (t + 1) + 1 < k' + 1 by omega),
          show ρ + (k' + 1) - 2 - (k' + 1 - 1 - (t + 1)) = ρ + t by omega]
        simp [cw, show ρ ≤ ρ + t ∧ ρ + t + 1 ≠ ρ + (k' + 1) by omega, show ρ + t + 1 < ρ + (k' + 1) by omega]
    · simp only [if_true]
      refine Finset.sum_eq_zero fun t ht => ?_
      simp only [Finset.mem_range] at ht
      unfold cw
      split_ifs <;> first | omega | simp_all
  rw [h0, h1, h2, zero_add, add_comm]

theorem weighted_sum_eq : ∀ {R : Type} [CommRing R] (ρ k r : ℕ) (hr : r = 2 * ρ + k + 1) (s : Bool) (M : Matrix (Fin r) (Fin r) R), (∑ i, ∑ j, if symEdge ρ k i j then ((GlobalTheory.Mem.SymChar.wtB ρ k s i j : ℤ) : R) * M i j else 0) = (∑ a : Fin ρ, if h : a.val + 1 < ρ then -M ⟨2 * ρ + k - a.val - 1, by omega⟩ ⟨2 * ρ + k - a.val, by omega⟩ else M ⟨ρ + k, by omega⟩ ⟨ρ + k + 1, by omega⟩) + (if s then 0 else ∑ i : Fin k, if h : i.val + 1 < k then -M ⟨ρ + k - 2 - i.val, by omega⟩ ⟨ρ + k - 1 - i.val, by omega⟩ else 0) := by
  intro R _ ρ k r hr s M
  subst hr
  let F : ℕ → R := fun i => if h : i + 1 < 2 * ρ + k + 1 then M ⟨i, by omega⟩ ⟨i + 1, h⟩ else 0
  have hFv : ∀ i j (hi : i < 2 * ρ + k + 1) (hj : j < 2 * ρ + k + 1), j = i + 1 → F i = M ⟨i, hi⟩ ⟨j, hj⟩ := by
    intro i j hi hj e; subst e; simp only [F]; rw [dif_pos hj]
  have hL : (∑ i : Fin (2 * ρ + k + 1), ∑ j : Fin (2 * ρ + k + 1), if symEdge ρ k i j then
      ((GlobalTheory.Mem.SymChar.wtB ρ k s i j : ℤ) : R) * M i j else 0) =
      ∑ i : Fin (2 * ρ + k + 1), ((cw ρ k s i.val : ℤ) : R) * F i.val := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [term_eq]
    rw [row_sum]
  rw [hL, Fin.sum_univ_eq_sum_range (fun i => ((cw ρ k s i : ℤ) : R) * F i), Finset.sum_range_succ,
    show F (2 * ρ + k) = 0 from dif_neg (by omega), mul_zero, add_zero, nat_id]
  congr 1
  · refine (Fin.sum_univ_eq_sum_range (fun a => if a + 1 < ρ then -F (2 * ρ + k - a - 1) else F (ρ + k)) ρ).symm.trans
      (Finset.sum_congr rfl fun a _ => ?_)
    beta_reduce
    split_ifs with h
    · rw [hFv _ (2 * ρ + k - a.val) (by omega) (by omega) (by omega)]
    · rw [hFv _ (ρ + k + 1) (by omega) (by omega) (by omega)]
  · cases s
    · simp only [Bool.false_eq_true, if_false]
      refine (Fin.sum_univ_eq_sum_range (fun i => if i + 1 < k then -F (ρ + k - 2 - i) else 0) k).symm.trans
        (Finset.sum_congr rfl fun i _ => ?_)
      beta_reduce
      split_ifs with h
      · rw [hFv _ (ρ + k - 1 - i.val) (by omega) (by omega) (by omega)]
      · rfl
    · rfl

end GlobalTheory.Mem.SymChar.Comb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupTiedOfMuIsW
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Top.TupTieW

theorem tupTied_of_muIsW : ∀ (X : Stages) (f : Fr X.B.toPre) (T : TwDat X.B) (Wt : Set X.B.places.Pl) (xi : X.C.Tup → HChar X.B.host.E), V4.MuIsW X f T Wt xi → (∀ w, X.toD7.what₂.muAt w ≠ X.toD7.what₂.mu0 ↔ w ∈ Wt) ∧ Wt.Finite ∧ (∀ w ∈ Wt, X.B.places.conj w ∈ Wt) ∧ ∀ nch : NChoice X.toD7, (∀ w ∈ Wt, nch.Q w = T.Q w) → ∃ tp : TupTied X.toD7 (Fr.at X f) nch, tp.xi = xi ∧ tp.psi = T.psi := by
  intro X f T Wt xi h
  have key : ∀ w, X.toD7.what₂.muAt w ≠ X.toD7.what₂.mu0 ↔ w ∈ Wt := by
    intro w
    constructor
    · intro hw
      by_contra hn
      exact hw (h.off w hn)
    · intro hw he
      have he' : X.W.muAt w = X.C.mu0 := he
      rw [h.on w hw] at he'
      have h1 := h.tw w
      rw [he', h.mu0] at h1
      exact (TwFin.tw_fin X.B f T).2.1 w h1.symm
  have hfin : Wt.Finite :=
    Set.Finite.subset (TwFin.tw_fin X.B f T).2.2.2 fun w hw => h.sub w hw
  have hconj : ∀ w ∈ Wt, X.B.places.conj w ∈ Wt := by
    intro w hw
    refine (key _).1 ?_
    have hc : X.toD7.what₂.muAt (X.toD7.what₂.places.conj w) = X.toD7.what₂.muAt w :=
      X.toD7.what₂.muAt_conj w
    intro he
    exact (key w).2 hw (hc.symm.trans he)
  refine ⟨key, hfin, hconj, fun nch hQ => ?_⟩
  have hg : ∀ μ, TupTie.Good X.B.host.F (xi μ) :=
    fun μ => TupTie.good_set f T (h.range ▸ Set.mem_range_self μ)
  refine ⟨⟨xi, h.inj, fun μ => (hg μ).1, fun μ => (hg μ).2.1, fun μ => (hg μ).2.2, T.psi, h.mu0, h.star, h.star', h.tw,
    fun w hw => ?_, fun w hw => ?_⟩, rfl, rfl⟩
  · rw [hQ w ((key w).1 hw)]
    exact T.psi_is w
  · exact h.supp w fun hn => (key w).2 hn hw

end GlobalTheory.Mem.Top.TupTieW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupleChainComplexFormsEqAlgebraicModularForms
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TwP

open GlobalTheory.Mem.Col2.RowTie

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ptC_tw : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (I.fm l u a) (badQ (I.rec7 l Z) Q)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ v ∈ Q, ((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal ∧ ∀ j, ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal) → I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → ∀ z : (I.per l u a).Wrow, z ∈ (I.fm l u a).ptC ↔ GlobalTheory.Mem.Col2.TwP.eWt I l Z u a z ∈ FiC K.lev (Formalism.L2.Forms.embT (I.rec7 l Z)) (sgTG (I.fm l u a)) K.y := by
  intro B X I hI hP l Z u a Q K hQ hQ' hR z
  have hemb : Formalism.L2.Forms.embT (I.rec7 l Z) = embAt B.embLL B.fields.emb := by
    funext τ
    ext y
    show B.host.φ₀ _ = _
    rw [← B.embE_φ₀]
    rfl
  have hsg : (I.perIn u a).sgT = (sgTG (D := I.rec7 l Z) (I.fm l u a) : B.fields.Tau → DomWeight (B.R.N B.R.m - 1)) := by
    funext τ
    obtain ⟨a, ha⟩ := B.R.t_odd
    have e1 : B.R.m * (B.R.t + 1) / 2 = B.R.m * (a + 1) := by
      rw [ha, show B.R.m * (2 * a + 1 + 1) = 2 * (B.R.m * (a + 1)) by ring]; omega
    have e2 : (B.R.t + 1) / 2 = a + 1 := by omega
    show GlobalTheory.Mem.Col2.shW (B.wts.sgW τ) (-((B.R.m : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ))) =
      Formalism.L2.Forms.shW (B.wts.sgW τ) ((B.R.m * (B.R.t + 1) / 2 : ℕ) : ℤ)
    rw [e1, e2]
    unfold GlobalTheory.Mem.Col2.shW Formalism.L2.Forms.shW
    congr 1
  have hc : ∀ c (s : (I.stX a).Stab c) (κ : K.lev.U), (K.y c).1 =
      bc (inclE (F := (I.rec7 l Z).host.F) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) (K.stabI c s).1 * (K.y c).1 * κ.1 →
      ((K.lev.chi κ : ℂˣ) : ℂ) = B.embLL (((I.stX a).chr c.1 s.1 : B.LLˣ) : B.LL) := by
    intro c s κ e
    let κ0 : (I.stX a).G c.1 := (1, s.1.2.1, s.1.2.2)
    have hgam : (I.stX a).gam c.1 κ0 = 1 := map_one (ufGL B.fields.E (B.R.N B.R.m - 1))
    have hp := GlobalTheory.Mem.Col2.TilX.isPtOf_rat (hR.pt c) (s.1.1)⁻¹
    have hact : ((I.stX a).act c.1 κ0 ((I.stX a).rep c)).1.1 = (((s.1.1)⁻¹, 1, 1) : UF B.fields.E (B.R.N B.R.m - 1) ×
        GLG B.fields.E (B.R.N B.R.m - 1) (B.primes X).vGs × GLQ B.fields.E (B.R.N B.R.m - 1) (QE I.sel (I.tup a : Chr B.fields.F B.fields.E B.fields.K))) •
        ((I.stX a).rep c).1.1 := by
      have e1 : FrmG.incl _ _ s.1 • ((I.stX a).rep c).1.1 = ((I.stX a).rep c).1.1 :=
        congrArg (fun d : (I.stX a).D c.1 => d.1.1) s.2
      conv_rhs => rw [← e1]
      refine Eq.trans ?_ (smul_smul _ _ _).symm
      have e2 : FrmG.incl _ _ κ0 = (((s.1.1)⁻¹, 1, 1) : UF B.fields.E (B.R.N B.R.m - 1) ×
          GLG B.fields.E (B.R.N B.R.m - 1) (B.primes X).vGs × GLQ B.fields.E (B.R.N B.R.m - 1) (QE I.sel (I.tup a : Chr B.fields.F B.fields.E B.fields.K))) *
          FrmG.incl _ _ s.1 := by
        refine Prod.ext ?_ (Prod.ext ?_ ?_)
        · exact (inv_mul_cancel _).symm
        · exact (one_mul _).symm
        · exact (one_mul _).symm
      exact congrArg (fun t => t • ((I.stX a).rep c).1.1) e2
    have hst := hR.stab c s
    let yc : GA B (B.R.N B.R.m - 1) := (K.y c).1
    let kk : GA B (B.R.N B.R.m - 1) := κ.1
    have e' : yc = bc (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F)) ((I.stX a).gam c.1 s.1) * yc * kk := by
      have h0 := e
      rw [show (K.stabI c s).1 = (I.stX a).gam c.1 s.1 from hst] at h0
      exact h0
    have hyk : yc * kk = ratAd B.host.F (s.1.1)⁻¹ * yc := by
      have e3 : ratAd B.host.F (s.1.1)⁻¹ =
          (bc (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F)) ((I.stX a).gam c.1 s.1))⁻¹ := by
        unfold ratAd
        rw [map_inv, map_inv]
        rfl
      rw [e3]
      conv_rhs => rw [e']
      group
    have hq : PtOf (yc * kk) ((I.stX a).act c.1 κ0 ((I.stX a).rep c)).1.1 := by
      rw [hyk, hact]
      exact hp
    exact hR.chr c κ κ0 hgam hq
  letI : Algebra (I.rec7 l Z).host.F B.fields.E := (inferInstance : Algebra (I.rec7 l Z).host.F (I.rec7 l Z).host.E)
  exact mem_Fi_iff (I.stX a) B.fields.emb B.embLL (I.perIn u a).sgT K.lev hemb hsg K.y K.y_bij K.stabI
    (fun c γ => K.stabI_range c γ) (fun c s => hR.stab c s) hc z

end GlobalTheory.Mem.Col2.TwP

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupleChainFormsRationalIffFrameValues
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TwP

open GlobalTheory.Mem.Col2.RowTie

theorem ptEmb_iff_rat : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι), ∀ z : (I.per l u a).Wrow, (∃ x, (I.fm l u a).ptEmb x = z) ↔ z ∈ (I.fm l u a).ptC ∧ ∀ c, ∃ Pc ∈ RatSpan (I.rec7 l Z) (I.fm l u a).sg, GlobalTheory.Mem.Col2.TwP.eWt I l Z u a z c = fnOf _ (shiftOf (sgTG (I.fm l u a))) 1 Pc := by
  intro B X I hI hP l Z u a z
  have hsg : sgTG (D := I.rec7 l Z) (I.fm l u a) = (I.perIn u a).sgT := by
    funext τ
    obtain ⟨k, hk⟩ := B.R.t_odd
    have e1 : B.R.m * (B.R.t + 1) / 2 = B.R.m * (k + 1) := by
      rw [hk, show B.R.m * (2 * k + 1 + 1) = 2 * (B.R.m * (k + 1)) by ring]; omega
    have e2 : (B.R.t + 1) / 2 = k + 1 := by omega
    show Formalism.L2.Forms.shW (B.wts.sgW τ) ((B.R.m * (B.R.t + 1) / 2 : ℕ) : ℤ) =
      GlobalTheory.Mem.Col2.shW (B.wts.sgW τ) (-((B.R.m : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ)))
    rw [e1, e2]
    unfold GlobalTheory.Mem.Col2.shW Formalism.L2.Forms.shW
    congr 1
  have hsh : shiftOf (sgTG (D := I.rec7 l Z) (I.fm l u a)) = shiftOf (I.perIn u a).sgT := congrArg shiftOf hsg
  exact rat_iff (I.stX a) B.fields.emb B.embLL (I.perIn u a).sgT (l.fmL u a).famP (VV_shW B.wts.sgW _) hsh z

end GlobalTheory.Mem.Col2.TwP

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistLocalConditionConjIffFrameChangeTrivial
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TC.ChTw GlobalTheory.Mem.Col2.TC.ChTw.Match Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.Col2.TC.ChTw.Match

variable {B : Base} {X : PreX B.toPre}

theorem bc_prV_entry {B : Base} (v : HeightOneSpectrum (𝓞 B.host.F)) {n : ℕ} (m : GA B n)
    (h : bc (prV (E := B.host.E) v) m = 1) (r j : Fin n) :
    prV (E := B.host.E) v ((m : Matrix (Fin n) (Fin n) _) r j) = if r = j then 1 else 0 := by
  have := congrArg (fun g : GL (Fin n) (TensorProduct (↥B.host.F) B.host.E (HeightOneSpectrum.adicCompletion (↥B.host.F) v)) =>
    (g.1 : Matrix (Fin n) (Fin n) _) r j) h
  simpa [bc, Matrix.one_apply] using this

theorem natCast_not_mem_of_goodPl {F : Type} [Field F] [NumberField F] (E : Type) [Field E] [Algebra F E]
    {S : Set ℕ} {w : HeightOneSpectrum (𝓞 F)} (hw : GoodPl E S w) {g : ℕ} (hg : Nat.Prime g) (hgS : g ∈ S) :
    ((g : 𝓞 F) ∉ w.asIdeal) := by
  intro hmem
  have h0 : ((g : 𝓞 F ⧸ w.asIdeal)) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk w.asIdeal), Ideal.Quotient.eq_zero_iff_mem]; exact hmem
  have hdvd : ringChar (𝓞 F ⧸ w.asIdeal) ∣ g := ringChar.dvd h0
  haveI : Nontrivial (𝓞 F ⧸ w.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr w.isPrime.ne_top
  have hne : ringChar (𝓞 F ⧸ w.asIdeal) ≠ 1 := CharP.ringChar_ne_one
  rcases (Nat.dvd_prime hg).1 hdvd with h | h
  · exact hne h
  · apply hw.2.2
    show ringChar (𝓞 F ⧸ w.asIdeal) ∈ S
    rw [h]; exact hgS

theorem locCQ_conj_iff_eq_one : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (u : B.Word) (a : I.ι)
    (Q : Finset (HeightOneSpectrum (𝓞 B.host.F))), (∀ v, v ∈ Q ↔ I.UnderQ a v) → ∀ (n : ℕ) (t s : GA B n) (θ : GLQ B.fields.E n (I.Q a)),
    (∀ v : HeightOneSpectrum (𝓞 B.host.F), ((B.T u : 𝓞 B.host.F) ∈ v.asIdeal ∨ ∀ j, (B.host.g j : 𝓞 B.host.F) ∉ v.asIdeal) →
      bc (prV (E := B.host.E) v) t = 1) →
    (∀ v ∈ Q, bc (prV (E := B.host.E) v) s = 1) →
    (LocCQ (I.Q a) n (t⁻¹ * s * t) θ ↔ θ = 1) := by
  intro B X I hI l u a Q hQ n t s θ ht hs
  have key : ∀ (P : I.Q a) (r j : Fin n),
      adAt B.host.F P.1 (((t⁻¹ * s * t : GA B n) : Matrix (Fin n) (Fin n) _) r j) = if r = j then 1 else 0 := by
    intro P r j
    have hvQ : HeightOneSpectrum.under (𝓞 B.host.F) P.1 ∈ Q := (hQ _).2 ⟨P.1, P.2, rfl⟩
    obtain ⟨w, -, hsel, hgood⟩ := ColIn.exists_of_mem_Q I P.2
    have hvw : HeightOneSpectrum.under (𝓞 B.host.F) P.1 = w := by
      ext1
      have := hI.sel_ok w
      rw [hsel] at this
      exact this
    have htv : bc (prV (E := B.host.E) w) t = 1 :=
      ht w (Or.inr fun j => natCast_not_mem_of_goodPl B.fields.E hgood (B.host.g_prime j) (hI.g_mem j))
    have hsv : bc (prV (E := B.host.E) w) s = 1 := hs w (hvw ▸ hvQ)
    have hm : bc (prV (E := B.host.E) w) (t⁻¹ * s * t) = 1 := by
      rw [MonoidHom.map_mul, MonoidHom.map_mul, MonoidHom.map_inv, htv, hsv, inv_one, one_mul, one_mul]
    have entry := bc_prV_entry w _ hm r j
    split_ifs with hrj
    · exact GlobalTheory.Mem.Col2.FullDt.adAt_eq_one_of_prV P.1 (by rw [hvw, entry, if_pos hrj])
    · exact GlobalTheory.Mem.Col2.TilX.adAt_eq_zero_of_prV P.1 _ (by rw [hvw, entry, if_neg hrj])
  constructor
  · intro hL
    funext P
    show θ P = 1
    rw [← inv_eq_one]
    apply Subtype.ext
    apply (Pi.basisFun B.fields.E (Fin n)).ext'
    intro j
    funext r
    have h1 := hL P r j
    rw [key P r j] at h1
    have h2 : algebraMap B.host.E (HeightOneSpectrum.adicCompletion B.host.E P.1)
        ((((θ P)⁻¹ : ↥(GLint B.fields.E n P.1)).1) (Pi.single j 1) r) =
        algebraMap B.host.E _ ((Pi.single j (1 : B.host.E) : Fin n → B.host.E) r) := by
      rw [← h1, Pi.single_apply]; split_ifs <;> simp
    have h3 := (algebraMap B.host.E (HeightOneSpectrum.adicCompletion B.host.E P.1)).injective h2
    simpa [Pi.basisFun_apply] using h3
  · rintro rfl
    intro P r j
    rw [key P r j]
    simp [Pi.single_apply]

end GlobalTheory.Mem.Col2.TC.ChTw.Match
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistPrimesAwayLevelAndTypePrimesStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistPrimes_away_level_and_type_primes : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → (I.Q I.mu0 = ∅) ∧ ∀ (u : B.Word) (a : I.ι), ∀ P ∈ I.Q a, (P ∉ (B.primes X).vT u ∧ P ∉ (B.primes X).vGs ∧ conjPrime₂ P ∉ (B.primes X).vT u ∧ conjPrime₂ P ∉ (B.primes X).vGs ∧ conjPrime₂ P ∉ I.Q a) ∧ X.piT u ∉ P.asIdeal ∧ (B.T u : 𝓞 B.host.F) ∉ (P.under (𝓞 B.host.F)).asIdeal := by
  first | exact @GlobalTheory.Mem.Col2.TwistPrimes.twist_primes_away | exact GlobalTheory.Mem.Col2.TwistPrimes.twist_primes_away | (intros; apply GlobalTheory.Mem.Col2.TwistPrimes.twist_primes_away <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistPrimesReferenceTupleEqEmptyStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.FullDt ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.q_mu0_eq_empty : ∀ (B : Base) (X : PreX B.toPre) (I : ColIn B X), I.Q I.mu0 = ∅ := by
  first | exact @GlobalTheory.Mem.Col2.RefTup.twistPrimes_reference_tuple_eq_empty | exact GlobalTheory.Mem.Col2.RefTup.twistPrimes_reference_tuple_eq_empty | (intros; apply GlobalTheory.Mem.Col2.RefTup.twistPrimes_reference_tuple_eq_empty <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedEmbeddingMatrixSubstitutionMemRatSpan
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IntegralityCompare

namespace GlobalTheory.IntegralityCompare

open MvPolynomial

theorem twSub_eq_subP (D : D7) {n : ℕ} (M : GL (Fin n) D.host.E) (s : D.what₂.Tau → ℤ)
    (P : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ) :
    twSub (embT D) M s P = C (∏ τ, (embT D τ (M : Matrix (Fin n) (Fin n) D.host.E).det) ^ (s τ)) *
      Formalism.L2.Forms.subP (fun τ => (M : Matrix (Fin n) (Fin n) D.host.E).map (embT D τ)) P := by
  rfl

theorem twSub_mem_ratSpan : ∀ (D : D7) {n : ℕ} (lam : D.what₂.Tau → DomWeight n) (M : GL (Fin n) D.host.E) (s : D.what₂.Tau → ℤ)
    (P0 : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ),
    P0 ∈ Formalism.L2.Forms.RatSpan D lam → twSub (embT D) M s P0 ∈ Formalism.L2.Forms.RatSpan D lam := by
  classical
  intro D n lam M s P0 hP
  let A : Matrix (Fin n) (Fin n) D.host.E := (M : Matrix (Fin n) (Fin n) D.host.E)
  let ML : D.what₂.Tau → Matrix (Fin n) (Fin n) D.what₂.LL := fun τ => A.map (Formalism.L2.G.Cmp.tEL D τ)
  have hoM : ∀ τ, A.map (embT D τ) = (ML τ).map D.what₂.embLL := fun τ => by
    ext a b
    exact (Formalism.L2.G.Cmp.tEL_emb D τ _).symm
  have hdetA : A.det ≠ 0 := (Matrix.isUnits_det_units M).ne_zero
  have hMdet : ∀ τ, (ML τ).det ≠ 0 := by
    intro τ h
    apply hdetA
    have : Formalism.L2.G.Cmp.tEL D τ A.det = 0 := by
      rw [RingHom.map_det]; exact h
    exact (map_eq_zero _).1 this
  have hc : (∏ τ, (embT D τ A.det) ^ (s τ)) =
      D.what₂.embLL (∏ τ, (ML τ).det ^ s τ) := by
    rw [map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_zpow₀, RingHom.map_det, RingHom.mapMatrix_apply, hoM τ, RingHom.map_det D.what₂.embLL, RingHom.mapMatrix_apply]
  rw [twSub_eq_subP]
  show C (∏ τ, (embT D τ A.det) ^ (s τ)) * Formalism.L2.Forms.subP (fun τ => A.map (embT D τ)) P0 ∈ _
  rw [hc, MvPolynomial.C_mul']
  induction hP using AddSubgroup.closure_induction with
  | mem p hp =>
    obtain ⟨r, f, hf, rfl⟩ := hp
    rw [map_smul, Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.substitution_tensor, smul_smul, ← map_mul]
    apply Formalism.L2.GlobalTheoryTheory.LemB.rat_ten D _ Finset.univ
    · intro τ _
      rw [hoM τ]
      exact Formalism.L2.GlobalTheoryTheory.LemB.rat_rowAct_mem D _ (Formalism.L2.DIV.natW_antitone _) (ML τ) (hMdet τ) _
        (Submodule.subset_span ⟨f τ, hf τ, rfl⟩)
    · intro τ hτ
      exact absurd (Finset.mem_univ τ) hτ
  | zero => rw [map_zero, smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add, smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg, smul_neg]; exact neg_mem hx

end GlobalTheory.IntegralityCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightPolynomialFramesMemSpanBideterminantProducStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem.CanonicalSurjection

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightPolynomial_frames_mem_span_bideterminantProducts : ∀ (K L : Type) [Field K] [Field L] [Infinite K] (φ : K →+* L) (ι : Type) [Fintype ι] (N : ℕ)
    (ν : ι → Fin N → ℕ) (M : ι → Matrix (Fin N) (Fin N) L), ∀ Q ∈ WtPol K ν,
    (fun y : ι → Matrix (Fin N) (Fin N) L =>
      MvPolynomial.eval (fun k : ι × Fin N × Fin N => (M k.1 * y k.1) k.2.1 k.2.2) (MvPolynomial.map φ Q)) ∈
    Submodule.span L {F | ∃ g : ι → Matrix (Fin N) (Fin N) L → L, (∀ τ, g τ ∈ bideterminantFunctionsOfShape L N (ν τ)) ∧
      F = fun y => ∏ τ, g τ (y τ)} := by
  first | exact @GlobalTheory.Mem.WeightBideterminants.weightPolynomial_mem_span_bideterminantProducts | exact GlobalTheory.Mem.WeightBideterminants.weightPolynomial_mem_span_bideterminantProducts | (intros; apply GlobalTheory.Mem.WeightBideterminants.weightPolynomial_mem_span_bideterminantProducts <;> assumption)
end

