import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0107
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0100
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TraceInverseGramConjSmulEq
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IndicatorFunctionIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0974
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0287
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0288
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0155
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KappaConjugateHalfPointTranslatesLastColumn
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.LineAct.ColTrans

open GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule (ofAdj)

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem adelicConj_adelicConj_eq_self (x : AE D) : cA D (cA D x) = x := by
  have := congrFun (congrFun (adj_adj (D := D) (m := 1) (n := 1) (Matrix.of fun _ _ => x)) 0) 0
  simpa [adj] using this

theorem e_mul_sec (p : SplitPt D k) (x : k) : p.e * p.sec x = p.sec x := by
  rw [← p.sec_pr, p.pr_sec]

theorem map_pr_rat (p : SplitPt D k) {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) :
    (rat M : Mx D m n).map p.pr = M.map (iota p) := by
  ext i j; rfl

theorem matrix_mul_replicateCol_eq_replicateCol_mulVec {R : Type} [CommRing R] {m l : Type} [Fintype l] (A : Matrix m l R) (x : l → R) :
    A * replicateCol (Fin 1) x = replicateCol (Fin 1) (A *ᵥ x) := by
  ext i j; simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]

variable {n : Type} [Fintype n] [DecidableEq n]

theorem adj_wCol (p : SplitPt D k) {W₀ L' : HSp D} (ζ' : Fin L'.rank → D.host.E) (β : Frame p W₀ n) (t : n → k) :
    adj (wCol p ζ' β t) = Matrix.of fun i j => p.sec (dualPick ((L'.gram.map (iota p)) *ᵥ fun i => iota p (ζ' i)) j *
      ((iota p D.host.xi0)⁻¹ * ((W₀.gram.map (iota p)) *ᵥ (β.b *ᵥ t)) i)) := by
  ext i j
  simp only [adj, wCol, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply, adelicConj_adelicConj_eq_self]

end GlobalTheory.FinPl.LineAct.ColTrans

namespace GlobalTheory.FinPl.LineAct
open GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule (ofAdj)
open GlobalTheory.FinPl.LineAct.ColTrans

set_option maxHeartbeats 2000000 in

theorem kappa_wCol_translate : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ρ : ℕ) (B : BesLev D ρ) (L' W₀ : HSp D) (ζ' : Fin L'.rank → D.host.E) (l : Link B L' ζ'), IsLineVec L' ζ' → ∀ (α : Frame p B.A n') (α₀ : Frame p B.V₀ (n' ⊕ Fin 1)) (β : Frame p W₀ n), IsSumFrame B.o B.ζ α α₀ → ∀ t : n → k, IsHalf p.e ((B.o.resS W₀).symm (0, l.κ W₀ (GlobalTheory.FinPl.LineAct.wCol p ζ' β t))) ∧ ∀ i j, rd α₀ β ((B.o.resS W₀).symm (0, l.κ W₀ (GlobalTheory.FinPl.LineAct.wCol p ζ' β t))) i j = Sum.elim (fun _ => 0) (fun _ => -t i) j := by
  intro D k _ _ _ _ p n n' _ _ _ _ ρ B L' W₀ ζ' l hL α α₀ β hsum t
  set ι := iota p with hι
  set g' : Fin L'.rank → k := (L'.gram.map ι) *ᵥ fun i => ι (ζ' i) with hg'
  set v : Fin W₀.rank → k := fun j => (ι D.host.xi0)⁻¹ * ((W₀.gram.map ι) *ᵥ (β.b *ᵥ t)) j with hv
  have hadj : adj (wCol p ζ' β t) = Matrix.of fun i j => p.sec (dualPick g' j * v i) := adj_wCol p ζ' β t
  have hu : (B.o.resS W₀).symm (0, l.κ W₀ (wCol p ζ' β t)) =
      (incA D (-D.host.xi0⁻¹) • giA W₀) ⬝ adj (wCol p ζ' β t) ⬝ (adj (rat l.τ) ⬝ gA B.L ⬝ B.o.pB) := by
    rw [OrthDec.resS_symm_apply, Matrix.zero_mul, zero_add, Link.κ, ofAdj, adj_mul]
    simp only [Matrix.smul_mul, Matrix.mul_assoc]
  rw [hu]
  constructor
  · have hA : p.e • adj (wCol p ζ' β t) = adj (wCol p ζ' β t) := by
      rw [hadj]; ext i j; simp [e_mul_sec]
    intro i j
    have : p.e • ((incA D (-D.host.xi0⁻¹) • giA W₀) ⬝ adj (wCol p ζ' β t) ⬝ (adj (rat l.τ) ⬝ gA B.L ⬝ B.o.pB)) =
        (incA D (-D.host.xi0⁻¹) • giA W₀) ⬝ adj (wCol p ζ' β t) ⬝ (adj (rat l.τ) ⬝ gA B.L ⬝ B.o.pB) := by
      conv_rhs => rw [← hA]
      rw [Matrix.mul_smul (incA D (-D.host.xi0⁻¹) • giA W₀) p.e (adj (wCol p ζ' β t)),
        Matrix.smul_mul p.e ((incA D (-D.host.xi0⁻¹) • giA W₀) ⬝ adj (wCol p ζ' β t))]
    exact congrFun (congrFun this i) j
  · generalize hUdef : (incA D (-D.host.xi0⁻¹) • giA W₀) ⬝ adj (wCol p ζ' β t) ⬝
        (adj (rat l.τ) ⬝ gA B.L ⬝ B.o.pB) = U
    replace hUdef := hUdef.symm
    have hR : adj (rat l.τ) ⬝ gA B.L ⬝ B.o.pB = rat (l.τᴴ * B.L.gram * B.o.qB) := by
      rw [← rat_conjTranspose, gA, OrthDec.pB, ← rat_mul, ← rat_mul]
    have hX : (incA D (-D.host.xi0⁻¹) • giA W₀ : Mx D W₀.rank W₀.rank).map p.pr =
        ι (-D.host.xi0⁻¹) • (W₀.gram⁻¹).map ι := by
      ext i j; simp [giA, rat, hι, iota]
    have hW : (adj (wCol p ζ' β t)).map p.pr = vecMulVec v (dualPick g') := by
      rw [hadj]; ext i j; simp [vecMulVec, p.pr_sec, mul_comm]
    have hUm : U.map p.pr = (ι (-D.host.xi0⁻¹) • (W₀.gram⁻¹).map ι) * vecMulVec v (dualPick g') *
        (l.τᴴ * B.L.gram * B.o.qB).map ι := by
      rw [hUdef, hR, Matrix.map_mul, Matrix.map_mul, hX, hW, map_pr_rat]
    have hUA : U ⬝ B.o.jA = 0 := by
      simp only [hUdef, Matrix.mul_assoc, OrthDec.pB_jA, Matrix.mul_zero]

    have hrat : (l.τᴴ * B.L.gram * B.o.qB) *ᵥ vecB B.o B.ζ =
        -((D.host.xi0 * star D.host.xi0) • (L'.gram *ᵥ ζ')) := by
      have hz : B.ζ = -(l.τ *ᵥ ζ') := by rw [l.map, neg_neg]
      rw [vecB, Matrix.mulVec_mulVec, Matrix.mul_assoc, B.o.qB_iB, Matrix.mul_one, hz, Matrix.mulVec_neg,
        Matrix.mulVec_mulVec, Matrix.mul_assoc, GlobalTheory.Unf.Model.tau_gram l hL, Matrix.smul_mulVec]
    have hgi : ∀ i, g' i = ι ((L'.gram *ᵥ ζ') i) := fun i => (RingHom.map_mulVec ι _ _ i).symm
    have hg0 : g' ≠ 0 := by
      intro h0
      apply hL.2
      have h1 : L'.gram *ᵥ ζ' = 0 := by
        funext i
        apply ι.injective
        rw [← hgi, h0, Pi.zero_apply, Pi.zero_apply, map_zero]
      rw [h1, dotProduct_zero]
    have hxi : ι D.host.xi0 ≠ 0 := fun h => GlobalTheory.Unf.Inhab.cmHost_imaginaryGenerator_ne_zero D ((iota p).injective (h.trans (map_zero _).symm))
    have hGG : (W₀.gram⁻¹).map ι * W₀.gram.map ι = 1 := by
      rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (gram_isUnit_det W₀), Matrix.map_one _ (map_zero _) (map_one _)]
    have hcol : U.map p.pr *ᵥ (fun i => p.pr (ratV (vecB B.o B.ζ) i)) = -(β.b *ᵥ t) := by
      have h1 : (fun i => p.pr (ratV (vecB B.o B.ζ) i)) = ι ∘ vecB B.o B.ζ := rfl
      have h2 : (l.τᴴ * B.L.gram * B.o.qB).map ι *ᵥ (ι ∘ vecB B.o B.ζ) =
          (-(ι (D.host.xi0 * star D.host.xi0))) • g' := by
        funext i
        rw [← RingHom.map_mulVec, hrat, Pi.smul_apply, hgi]
        simp [map_neg, map_mul]
      have h3 : vecMulVec v (dualPick g') *ᵥ g' = v := by
        rw [Matrix.vecMulVec_mulVec, dualPick_dot g' hg0, MulOpposite.op_one, one_smul]
      have h4 : v = (ι D.host.xi0)⁻¹ • ((W₀.gram.map ι) *ᵥ (β.b *ᵥ t)) := rfl
      rw [h1, hUm, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h2, Matrix.mulVec_smul, h3, h4,
        Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.smul_mulVec, Matrix.mulVec_mulVec, hGG, Matrix.one_mulVec,
        smul_smul, smul_smul, ← neg_one_smul k (β.b *ᵥ t)]
      congr 1
      have hs : ι (star D.host.xi0) = -ι D.host.xi0 := by rw [GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, map_neg]
      rw [map_mul, hs, map_neg, map_inv₀]
      field_simp
    have hrd : rd α₀ β U = fromCols 0 (replicateCol (Fin 1) (-t)) := by
      have hb : α₀.b = _ := hsum
      rw [rd, hb, Matrix.mul_assoc, Matrix.mul_fromCols, Matrix.mul_fromCols, ← Matrix.mul_assoc (U.map p.pr),
        ← Matrix.map_mul, hUA, Matrix.map_zero _ (map_zero _), Matrix.zero_mul, Matrix.mul_zero, matrix_mul_replicateCol_eq_replicateCol_mulVec,
        matrix_mul_replicateCol_eq_replicateCol_mulVec, hcol, Matrix.mulVec_neg, Matrix.mulVec_mulVec, β.b'b, Matrix.one_mulVec]
    intro i j
    rw [hrd]
    cases j with
    | inl j => simp
    | inr j => simp

end GlobalTheory.FinPl.LineAct

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KappaSplitHalfPointMultipliesByCharacter
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KappaRowChar

variable {D : D7}

theorem half_mul_right {m n r : ℕ} {f : AE D} {M : Mx D m n} (h : IsHalf f M) (N : Mx D n r) : IsHalf f (M ⬝ N) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum, ← mul_assoc, h i _]

theorem half_mul_left {m n r : ℕ} {f : AE D} {M : Mx D n r} (N : Mx D m n) (h : IsHalf f M) : IsHalf f (N ⬝ M) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_left_comm, h k j]

theorem half_smul {m n : ℕ} {f : AE D} {M : Mx D m n} (c : AE D) (h : IsHalf f M) : IsHalf f (c • M) := by
  intro i j
  rw [Matrix.smul_apply, smul_eq_mul, mul_left_comm, h i j]

theorem half_adj {m n : ℕ} {f : AE D} {M : Mx D m n} (h : IsHalf f M) : IsHalf (cA D f) (adj M) := by
  intro i j
  show cA D f * cA D (M j i) = cA D (M j i)
  rw [← map_mul, h j i]

theorem trace_half {n : ℕ} {f : AE D} {M : Mx D n n} (h : IsHalf f M) : f * M.trace = M.trace := by
  simp only [Matrix.trace, Matrix.diag, Finset.mul_sum, h _ _]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem e_mul_sec (p : GlobalTheory.FinPl.SplitPt D k) (a : k) : p.e * p.sec a = p.sec a := by
  rw [← p.sec_pr, p.pr_sec]

theorem wRow_half {n : Type} [Fintype n] [DecidableEq n] (p : GlobalTheory.FinPl.SplitPt D k) {W₀ L' : HSp D}
    (ζ' : Fin L'.rank → D.host.E) (β : GlobalTheory.FinPl.Frame p W₀ n) (t : n → k) :
    IsHalf p.e (GlobalTheory.FinPl.LineAct.wRow p ζ' β t) := by
  intro i j
  exact e_mul_sec p _

theorem trace_vecMulVec_mul {R : Type} [CommRing R] {a b c : Type} [Fintype a] [Fintype b] [Fintype c]
    (u : a → R) (v : b → R) (X : Matrix b c R) (J : Matrix c a R) :
    (vecMulVec u v * X * J).trace = v ⬝ᵥ (X *ᵥ (J *ᵥ u)) := by
  rw [Matrix.mul_assoc, Matrix.mulVec_mulVec]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, vecMulVec_apply, dotProduct, mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

end GlobalTheory.KappaRowChar

end

namespace GlobalTheory.KappaRowChar

open GlobalTheory.FinPl.LineAct (iota)

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem pr_trace {n : Type} [Fintype n] [DecidableEq n] (p : GlobalTheory.FinPl.SplitPt D k) {W₀ L' : HSp D} {a b : ℕ}
    (τ : Matrix (Fin a) (Fin L'.rank) D.host.E) (ζ' : Fin L'.rank → D.host.E) (ζ : Fin a → D.host.E) (hτ : τ *ᵥ ζ' = -ζ)
    (β : GlobalTheory.FinPl.Frame p W₀ n) (t : n → k) (x : Mx D W₀.rank b) (iB : Matrix (Fin b) (Fin a) D.host.E) :
    p.pr (((rat τ : Mx D a L'.rank) ⬝ GlobalTheory.FinPl.LineAct.wRow p ζ' β t) ⬝ (x ⬝ (rat iB : Mx D b a))).trace =
      -(t ⬝ᵥ (β.b' *ᵥ (x.map p.pr *ᵥ (iB.map (iota p) *ᵥ fun i => iota p (ζ i))))) := by
  rw [show p.pr (((rat τ : Mx D a L'.rank) ⬝ GlobalTheory.FinPl.LineAct.wRow p ζ' β t) ⬝ (x ⬝ (rat iB : Mx D b a))).trace =
      ((((rat τ : Mx D a L'.rank) ⬝ GlobalTheory.FinPl.LineAct.wRow p ζ' β t) ⬝ (x ⬝ (rat iB : Mx D b a))).map p.pr).trace from by
    simp only [Matrix.trace, Matrix.diag, map_sum]; rfl]
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_mul]
  have hτm : (rat τ : Mx D a L'.rank).map p.pr = τ.map (iota p) := rfl
  have hwm : (GlobalTheory.FinPl.LineAct.wRow p ζ' β t).map p.pr = vecMulVec (fun i => iota p (ζ' i)) (t ᵥ* β.b') := by
    ext i j
    simp only [Matrix.map_apply, GlobalTheory.FinPl.LineAct.wRow, Matrix.of_apply, p.pr_sec, vecMulVec_apply]
  have hjm : (rat iB : Mx D b a).map p.pr = iB.map (iota p) := rfl
  have ha : τ.map (iota p) *ᵥ (fun i => iota p (ζ' i)) = -(fun i => iota p (ζ i)) := by
    funext i
    have h := RingHom.map_mulVec (iota p) τ ζ' i
    rw [hτ] at h
    simp only [Pi.neg_apply, map_neg] at h ⊢
    exact h.symm
  rw [hτm, hwm, hjm, Matrix.mul_vecMulVec, ← Matrix.mul_assoc, trace_vecMulVec_mul, ha, Matrix.mulVec_neg,
    Matrix.mulVec_neg, dotProduct_neg, Matrix.dotProduct_mulVec t]

end GlobalTheory.KappaRowChar

namespace GlobalTheory.KappaRowChar

open GlobalTheory.FinPl.LineAct (iota)

set_option maxHeartbeats 1600000 in

theorem kappa_wRow_char : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ) (χ : AddChar k Circle), p.IsChar ψ χ → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ρ : ℕ) (B : BesLev D ρ) (L' W₀ : HSp D) (ζ' : Fin L'.rank → D.host.E) (l : Link B L' ζ') (α : Frame p B.A n') (α₀ : Frame p B.V₀ (n' ⊕ Fin 1)) (β : Frame p W₀ n), IsSumFrame B.o B.ζ α α₀ → ∀ t : n → k, IsHalf (cA D p.e) ((B.o.resS W₀).symm (0, l.κ W₀ (GlobalTheory.FinPl.LineAct.wRow p ζ' β t))) ∧ ∀ x : WO B.V₀ W₀, IsHalf p.e x → ψ (symplO B.V₀ W₀ x ((B.o.resS W₀).symm (0, l.κ W₀ (GlobalTheory.FinPl.LineAct.wRow p ζ' β t)))) = (χ (-(t ⬝ᵥ fun i => rd α₀ β x i (Sum.inr 0))) : ℂ) := by
  intro D k _ _ _ _ p ψ χ hχ n n' _ _ _ _ ρ B L' W₀ ζ' l α α₀ β hsum t
  have hwh : IsHalf p.e (GlobalTheory.FinPl.LineAct.wRow p ζ' β t) := wRow_half p ζ' β t
  have hmh : IsHalf p.e ((rat l.τ : Mx D B.L.rank L'.rank) ⬝ GlobalTheory.FinPl.LineAct.wRow p ζ' β t) := half_mul_left _ hwh
  have hk : l.κ W₀ (GlobalTheory.FinPl.LineAct.wRow p ζ' β t) = incA D (-D.host.xi0⁻¹) •
      (giA W₀ ⬝ (adj ((rat l.τ : Mx D B.L.rank L'.rank) ⬝ GlobalTheory.FinPl.LineAct.wRow p ζ' β t) ⬝ gA B.L)) := rfl
  have hu : (B.o.resS W₀).symm (0, l.κ W₀ (GlobalTheory.FinPl.LineAct.wRow p ζ' β t)) =
      l.κ W₀ (GlobalTheory.FinPl.LineAct.wRow p ζ' β t) ⬝ B.o.pB := by
    rw [OrthDec.resS_symm_apply, Matrix.zero_mul, zero_add]
  refine ⟨?_, fun x _ => ?_⟩
  · rw [hu, hk]
    exact half_mul_right (half_smul _ (half_mul_left _ (half_mul_right (half_adj hmh) _))) _
  · have h0 : symplO B.A W₀ ((B.o.resS W₀) x).1 0 = 0 := by simp [symplO, hO]
    have hxi : incA D D.host.xi0 * cA D (incA D (-D.host.xi0⁻¹)) = 1 := by
      have hne := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
      rw [GlobalTheory.DualPairCheck.cA_incA, ← map_mul, star_neg, star_inv₀, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, neg_inv, neg_neg,
        mul_inv_cancel₀ hne, map_one]
    have hxi' : ∀ T : AE D, incA D D.host.xi0 * (cA D (incA D (-D.host.xi0⁻¹)) * T) = T := fun T => by
      rw [← mul_assoc, hxi, one_mul]
    have hs : symplO B.V₀ W₀ x ((B.o.resS W₀).symm (0, l.κ W₀ (GlobalTheory.FinPl.LineAct.wRow p ζ' β t))) =
        Algebra.trace (AF D.host.F) (AE D)
          (((rat l.τ : Mx D B.L.rank L'.rank) ⬝ GlobalTheory.FinPl.LineAct.wRow p ζ' β t) ⬝ (x ⬝ B.o.jB)).trace := by
      rw [OrthDec.symplO_resS, AddEquiv.apply_symm_apply, h0, zero_add, symplO, hO_eq_trace, hk]
      simp only [adj_smul, adj_mul, adj_adj, adj_gA, adj_giA, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc,
        giA_gA_cancel, trace_smul, smul_eq_mul, OrthDec.resS_apply]
      rw [hxi']
    rw [hs, show B.o.jB = (rat B.o.iB : Mx D B.V₀.rank B.L.rank) from rfl]
    have hc := trace_half (half_mul_right hmh (x ⬝ (rat B.o.iB : Mx D B.V₀.rank B.L.rank)))
    have hsec : p.sec (p.pr (((rat l.τ : Mx D B.L.rank L'.rank) ⬝ GlobalTheory.FinPl.LineAct.wRow p ζ' β t) ⬝
        (x ⬝ (rat B.o.iB : Mx D B.V₀.rank B.L.rank))).trace) =
        (((rat l.τ : Mx D B.L.rank L'.rank) ⬝ GlobalTheory.FinPl.LineAct.wRow p ζ' β t) ⬝
          (x ⬝ (rat B.o.iB : Mx D B.V₀.rank B.L.rank))).trace := by
      rw [p.sec_pr]; exact hc
    show psiE ψ _ = _
    rw [← hsec, ← hχ, pr_trace p l.τ ζ' B.ζ l.map β t x B.o.iB]
    have hb : ∀ r, α₀.b r (Sum.inr 0) = (B.o.iB.map (iota p) *ᵥ fun i => iota p (B.ζ i)) r := by
      intro r
      rw [hsum]
      simp only [fromCols_apply_inr, replicateCol_apply, ratV, vecB]
      exact RingHom.map_mulVec (iota p) B.o.iB B.ζ r
    have hcol : (fun i => rd α₀ β x i (Sum.inr 0)) =
        β.b' *ᵥ (x.map p.pr *ᵥ (B.o.iB.map (iota p) *ᵥ fun i => iota p (B.ζ i))) := by
      funext i
      rw [Matrix.mulVec_mulVec]
      simp only [rd, Matrix.mul_apply, hb]
      rfl
    rw [hcol]

end GlobalTheory.KappaRowChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastKernelDatumInLastLineFrameAtLevelPrime
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl

noncomputable section
namespace GlobalTheory.LastKerRep
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n₂ : Type} [Fintype n] [DecidableEq n] [Fintype n₂] [DecidableEq n₂]

theorem hasVal_transport {Q : Pair k n} {R : Pair k n₂} (G : Matrix n₂ n k) (G' : Matrix n n₂ k) (hGG : G * G' = 1)
    {e : n₂ → k} (he : R.HasVal e 1) (hker : ∀ y, y ∈ Q.ker ↔ G *ᵥ y ∈ R.ker) {s : 𝓀[k]ˣ}
    (hs : Q.HasVal (G' *ᵥ e) s) (y : n → k) (a : 𝓀[k]) :
    Q.HasVal y a ↔ R.HasVal (G *ᵥ y) (((s⁻¹ : 𝓀[k]ˣ) : 𝓀[k]) * a) := by
  have hGe : ∀ (r : 𝒪[k]) (z : n → k), G *ᵥ (z - r • (G' *ᵥ e)) = G *ᵥ z - r • e := by
    intro r z
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hGG, Matrix.one_mulVec]
  obtain ⟨r, hr⟩ := residue_surjective (R := 𝒪[k]) (((s⁻¹ : 𝓀[k]ˣ) : 𝓀[k]) * a)
  have hsr : residue 𝒪[k] r * (s : 𝓀[k]) = a := by
    rw [hr, mul_comm, ← mul_assoc, Units.mul_inv, one_mul]
  constructor
  · intro hy
    have h1 := hy.sub (hs.smul r)
    rw [hsr, sub_self] at h1
    have h2 := Pair.mem_ker.1 ((hker _).1 (Pair.mem_ker.2 h1))
    rw [hGe] at h2
    have h3 := h2.add (he.smul r)
    rw [sub_add_cancel, zero_add, mul_one, hr] at h3
    exact h3
  · intro hy
    have h1 := hy.sub (he.smul r)
    rw [mul_one, hr, sub_self, ← hGe] at h1
    have h2 := Pair.mem_ker.1 ((hker _).2 (Pair.mem_ker.2 h1))
    have h3 := h2.add (hs.smul r)
    rw [sub_add_cancel, zero_add, hsr] at h3
    exact h3

theorem maps_transport {Q : Pair k n₂} {R : Pair k n} {n₁ : Type} [Fintype n₁] [DecidableEq n₁]
    (P : Pair k n₁) (G : Matrix n n₂ k) (s : 𝓀[k]ˣ)
    (hT : ∀ y a, Q.HasVal y a ↔ R.HasVal (G *ᵥ y) (((s⁻¹ : 𝓀[k]ˣ) : 𝓀[k]) * a)) (x : Matrix n₂ n₁ k) :
    Maps (s⁻¹ • P) R (G * x) ↔ Maps P Q x := by
  simp only [maps_iff_hasVal, Pair.dia_hasVal, inv_inv]
  constructor
  · intro H y a hy
    rw [hT, Matrix.mulVec_mulVec]
    apply H
    rwa [← mul_assoc, Units.mul_inv, one_mul]
  · intro H y a hy
    have := (hT _ _).1 (H y _ hy)
    rwa [← mul_assoc, Units.inv_mul, one_mul, Matrix.mulVec_mulVec] at this

theorem phiOne_transport {Q : Pair k n₂} {R : Pair k n} {n₁ : Type} [Fintype n₁] [DecidableEq n₁]
    (P : Pair k n₁) (G : Matrix n n₂ k) (s : 𝓀[k]ˣ)
    (hT : ∀ y a, Q.HasVal y a ↔ R.HasVal (G *ᵥ y) (((s⁻¹ : 𝓀[k]ˣ) : 𝓀[k]) * a)) (x : Matrix n₂ n₁ k) :
    phiOne (s⁻¹ • P) R (G * x) = phiOne P Q x := by
  classical
  unfold phiOne
  exact if_congr (maps_transport P G s hT x) rfl rfl

section Frames
variable {D : D7} {p : SplitPt D k} {S T : HSp D} {n' : Type} [Fintype n'] [DecidableEq n']

theorem extFun_eq_of (α : Frame p S n') (β : Frame p T n₂) (β' : Frame p T n) (Ψ : Matrix n₂ n' k → ℂ)
    (Ψ' : Matrix n n' k → ℂ) (hΨ : ∀ x, Ψ' ((β'.b' * β.b) * x) = Ψ x) : extFun α β Ψ = extFun α β' Ψ' := by
  funext t
  unfold extFun
  split_ifs
  · rw [← hΨ]
    congr 1
    unfold rd
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc β.b β.b', β.bb', Matrix.one_mul]
  · rfl

end Frames

section Lists
variable {D : D7} {ι : Type} {p : ι → SplitPt D k} {n' : Type} [Fintype n'] [DecidableEq n']

theorem overAll_of_extFun_eq (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (α : ∀ i, Frame (p i) S n')
    (β : ∀ i, Frame (p i) T n₂) (β' : ∀ i, Frame (p i) T n) (LS : Lat S) (LT : Lat T) (Ψ : ι → Matrix n₂ n' k → ℂ)
    (Ψ' : ι → Matrix n n' k → ℂ) (h : ∀ i, extFun (α i) (β i) (Ψ i) = extFun (α i) (β' i) (Ψ' i))
    (hSB : ∀ i, Ψ' i ∈ SB (Matrix n n' k)) :
    ∀ (l : List ι) (f f' : WO S T → ℂ), OverAll ψ α β LS LT Ψ l f f' → OverAll ψ α β' LS LT Ψ' l f f'
  | [], _, _, hf => hf
  | i :: l, f, f', hf => by
    obtain ⟨g, hg, hov⟩ : ∃ g, OverAll ψ α β LS LT Ψ l f g ∧ Over ψ (α i) (β i) LS LT g (Ψ i) f' := hf
    obtain ⟨h1, h2, h3, -, h5⟩ := hov
    refine ⟨g, overAll_of_extFun_eq ψ α β β' LS LT Ψ Ψ' h hSB l f g hg, h1, h2, h3, hSB i, ?_⟩
    rw [← h i]
    exact h5

end Lists

theorem isLattice_of_lastKer {m : Type} [Fintype m] [DecidableEq m] {Q : Pair k n₂} (G : Matrix (m ⊕ Fin 1) n₂ k)
    (G' : Matrix n₂ (m ⊕ Fin 1) k) (hGG : G * G' = 1) (L : Submodule 𝒪[k] (m → k))
    (hker : ∀ y, y ∈ Q.ker ↔ G *ᵥ y ∈ GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.lastKer L) : L.IsLattice k := by
  let e : (m → k) →ₗ[k] (m ⊕ Fin 1 → k) :=
    { toFun := fun x => Sum.elim x 0
      map_add' := by intro x y; ext (i | i) <;> simp
      map_smul' := by intro c x; ext (i | i) <;> simp }
  let f : (m → k) →ₗ[k] (n₂ → k) := (Matrix.mulVecLin G').comp e
  have hGf : ∀ x, G *ᵥ f x = Sum.elim x 0 := by
    intro x
    simp only [f, e, LinearMap.coe_comp, Function.comp_apply, Matrix.mulVecLin_apply, LinearMap.coe_mk, AddHom.coe_mk,
      Matrix.mulVec_mulVec, hGG, Matrix.one_mulVec]
  have hf : Function.Injective f := by
    intro x y hxy
    have := congrArg (G *ᵥ ·) hxy
    simp only [hGf] at this
    funext i
    exact congrFun this (Sum.inl i)
  have hL : L = Q.ker.comap (f.restrictScalars 𝒪[k]) := by
    ext x
    rw [Submodule.mem_comap, LinearMap.restrictScalars_apply, hker, hGf, GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer]
    simp
  rw [hL]
  exact GlobalTheory.GoodLat.isLattice_comap Q.ker Q.ker_isLat f hf

end GlobalTheory.LastKerRep

open GlobalTheory.LastKerRep in

theorem GlobalTheory.SeeSaw.lastKernel_reps : ∀ (D : D7) (c : Comm D) (v : VCom c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι), c.Is → v.Is → ShapeOff v o → ∀ j (h : j + 2 * 0 + 2 = D.R.m), ∃ (Λ : ι → Submodule 𝒪[k] (Fin c.T.rank → k)) (hΛ : ∀ i, (Λ i).IsLattice k) (u : ι → 𝓀[k]ˣ), (∀ i, (o.γ i).IsLat v.NT (Λ i)) ∧ Reps c.ψ (o.β (j + 1)) (o.γ₀ (j + 1 + 1) h) (c.x (j + 1)).L (c.x (j + 1 + 1)).L (fun i => haveI := hΛ i; phiOne (u i • o.Q (j + 1) i) (GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.lastPair o.q (Λ i))) o.I (· ∈ v.tP) (v.dT (j + 1)) := by
  intro D c v k _ _ _ _ ι o hc hv hS j h
  have htop := fun i => (hS.pre.topT (j + 1 + 1) h i).2
  choose Λ s hLat hKer hVal using htop
  have hGG : ∀ i, ((o.γ₀ (j + 1 + 1) h i).b' * (o.β (j + 1 + 1) i).b) * ((o.β (j + 1 + 1) i).b' * (o.γ₀ (j + 1 + 1) h i).b) = 1 := by
    intro i
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (o.β (j + 1 + 1) i).b, (o.β (j + 1 + 1) i).bb', Matrix.one_mul, (o.γ₀ (j + 1 + 1) h i).b'b]
  have hΛ : ∀ i, (Λ i).IsLattice k := fun i => isLattice_of_lastKer _ _ (hGG i) (Λ i) (hKer i)
  refine ⟨Λ, hΛ, fun i => (s i)⁻¹, hLat, (hv.atT (j + 1)).1, fun f hf => ?_⟩
  refine overAll_of_extFun_eq c.ψ (o.β (j + 1)) (o.β (j + 1 + 1)) (o.γ₀ (j + 1 + 1) h) _ _ _ _ (fun i => ?_) (fun i => ?_)
    o.I f _ (hS.rep (j + 1) (by omega) f hf)
  · haveI := hΛ i
    apply extFun_eq_of
    intro x
    exact phiOne_transport _ _ _ (hasVal_transport _ _ (hGG i)
      (glue_hasVal (GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.isGlue_last o.q (Λ i)))
      (fun y => (hKer i y).trans (by rw [glue_ker])) (hVal i)) x
  · haveI := hΛ i
    exact GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOne_mem _ _

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawDatumIsTwoVariableThetaFunctionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastSeeSaw_datum_isTwoVariableThetaFunction : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V₀ A L S X T L'' : HSp D) (o : OrthDec V₀ A L) (o'' : OrthDec X T L'') (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E), τᴴ * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram → ∀ (Ξ : WO V₀ S → ℂ) (Φ₂ : WO S T → ℂ), IsThetaFunO ψ V₀ S Ξ → IsThetaFunO ψ S T Φ₂ → IsBiTheta ψ A S X (lastBi o o'' τ Ξ Φ₂) := by
  first | exact @GlobalTheory.LastBiTheta.isBiTheta_lastBi | exact GlobalTheory.LastBiTheta.isBiTheta_lastBi | (intros; apply GlobalTheory.LastBiTheta.isBiTheta_lastBi <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelCharacterOnParahoricChartImageStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_character_on_parahoric_chart_image : ∀ (D : D7) (c : Com D) (w : Twist D), w.Is c → ∀ j ≤ D.R.m, ∀ s : PiLocalization₂ D, IsStage c w j s → ∀ PP ∈ w.Q, ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP → ∀ ι, IsChart s j φ ι → ∀ ξl, LiftsChar φ PP ξl (w.ξ PP) → ∀ y ∈ parahoric (Fv D.host.F v) (Fin D.R.r) (Blocks j D.R.t), ∀ d : (Fv D.host.F v)ˣ, (d : Fv D.host.F v) = y.1.toBlocks₂₂.det → Lev.levChi s.V s.β s.L (ι y) = (((ξl d)⁻¹ : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.ChartChi.levChi_chart | exact GlobalTheory.ChartChi.levChi_chart | (intros; apply GlobalTheory.ChartChi.levChi_chart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalModelWeilOperatorTrivialAtPlaceIsModelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos SymDbl OneDbl comb)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_model_weil_operator_trivialAtPlace_isModel : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
  ∀ (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (ω : Om V W), IsWeilDatumO ψ V W χV χW ω →
  ∀ (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FV : Frame k V.rank Y') (FW : Frame k W.rank Y)
    (Tm : SB (Matrix Y Y' k) →ₗ[ℂ] (WO V W → ℂ)), (ofSplit q).IsModel ψ FV FW Tm →
  ∀ g ∈ GlobalTheory.FinPl.grpOff V (· = q.v), ∀ h ∈ GlobalTheory.FinPl.grpOff W (· = q.v), (ofSplit q).IsModel ψ FV FW ((ω (g, h)) ∘ₗ Tm) := by
  first | exact @GlobalTheory.LocModMove.isModel_weil_off | exact GlobalTheory.LocModMove.isModel_weil_off | (intros; apply GlobalTheory.LocModMove.isModel_weil_off <;> assumption)
end

