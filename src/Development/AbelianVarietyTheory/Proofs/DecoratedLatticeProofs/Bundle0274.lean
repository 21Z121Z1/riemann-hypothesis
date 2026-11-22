import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0261
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittHyperbolicRankZeroProjMulEmb
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0252
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0241
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0262
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0224
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0259
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0189
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0258
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0024

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtensionFunctionIncZero
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel IsLocalRing
open GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.StepData (XIx Ix latOf box LatFrame)
open GlobalTheory.LocMod (GAt PinGBy ofSplit MovedTo)
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (CharUnramAt)
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastPair lastKer)
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedLocalFrameSequences (IsFockOver StepsAll vec atW IsMoved InAt InvOnUnits IsBesFrame IsJacFrame FrameMapsPrefix jacLat ptBF ptFB)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RouteCompare
open GlobalTheory.Mem.Isom

namespace GlobalTheory.OverTgt

variable {D : D7}

def colRow (S T : HSp D) (r : Fin S.rank → AE D) : (Fin T.rank → AE D) →+ WO S T where
  toFun y := Matrix.of fun i j => y i * r j
  map_zero' := by ext i j; simp
  map_add' y y' := by ext i j; simp [add_mul]

theorem mul_colRow {S T T' : HSp D} (M : Mx D T'.rank T.rank) (r : Fin S.rank → AE D) (y : Fin T.rank → AE D) :
    HMul.hMul M (colRow S T r y) = colRow S T' r (M *ᵥ y) := by
  ext i j
  simp [colRow, Matrix.mul_apply, Matrix.mulVec, dotProduct, Finset.sum_mul, mul_assoc]

theorem gen_eq_colRow {S T : HSp D} (α : AF D.host.F) (a : D.host.E) (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) :
    (Matrix.of fun i j => α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) : WO S T) =
      colRow S T (fun j => incA D (a * ∑ k, star (s k) * S.gram k j)) (fun i => α ⊗ₜ[D.host.F] (1 * t i)) := by
  ext i j
  simp only [colRow, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.of_apply]
  change _ = (α ⊗ₜ[D.host.F] (1 * t i)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] _)
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  congr 1
  ring

theorem colRow_mem_latO {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Lat T} {P : GlobalTheory.FinPl.Pl D → Prop}
    {a : D.host.E} (ha : a ∈ D.host.AA) {s : Fin S.rank → D.host.E} (hs : s ∈ LS) {y : Fin T.rank → AE D}
    (hy : y ∈ latV T LT P) :
    colRow S T (fun j => incA D (a * ∑ k, star (s k) * S.gram k j)) y ∈ latO S T LS (LT : Set _) P := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβi, hβ, c, hc, x, hx, rfl⟩ := hz
    rw [Set.mem_singleton_iff] at hc
    subst hc
    rw [← gen_eq_colRow]
    exact AddSubgroup.subset_closure ⟨β, hβi, hβ, a, ha, s, hs, x, hx, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [map_add]; exact add_mem hz hz'
  | neg z _ hz => rw [map_neg]; exact neg_mem hz

theorem mul_mem_latO {S T T' : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Lat T} {LT' : Lat T'}
    {P : GlobalTheory.FinPl.Pl D → Prop} (M : Mx D T'.rank T.rank) (hM : ∀ y ∈ latV T LT P, M *ᵥ y ∈ latV T' LT' P) {w : WO S T}
    (hw : w ∈ latO S T LS (LT : Set _) P) : HMul.hMul M w ∈ latO S T' LS (LT' : Set _) P := by
  induction hw using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨α, hαi, hα, a, ha, s, hs, t, ht, rfl⟩ := hz
    rw [gen_eq_colRow, mul_colRow]
    exact colRow_mem_latO ha hs (hM _ (AddSubgroup.subset_closure ⟨α, hαi, hα, 1, rfl, t, ht, rfl⟩))
  | zero => rw [Matrix.mul_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [Matrix.mul_add]; exact add_mem hz hz'
  | neg z _ hz => rw [Matrix.mul_neg]; exact neg_mem hz

theorem isHalf_mul {m n l : ℕ} {e : AE D} (M : Mx D m l) {u : Mx D l n} (h : IsHalf e u) : IsHalf e (HMul.hMul M u) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_left_comm, h k j]

section Isometry

variable {V V' : HSp D} (I : IsoMat V V') (S : HSp D)

def conjOp (Tm : (WO S V → ℂ) →ₗ[ℂ] (WO S V → ℂ)) : (WO S V' → ℂ) →ₗ[ℂ] (WO S V' → ℂ) :=
  LinearMap.funLeft ℂ ℂ (I.phi S).symm ∘ₗ Tm ∘ₗ LinearMap.funLeft ℂ ℂ (I.phi S)

variable {Λ : AddSubgroup (WO S V)} {Λ' : AddSubgroup (WO S V')} (hΛ : ∀ u, u ∈ Λ ↔ I.phi S u ∈ Λ')
include hΛ

end Isometry

section Frames

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : SplitPt D k}
  {S T T₀ : HSp D} (d : HypDec T T₀ 0) {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  (α : GlobalTheory.FinPl.Frame p S n') (β : GlobalTheory.FinPl.Frame p T n) (β₀ : GlobalTheory.FinPl.Frame p T₀ n)

end Frames

end GlobalTheory.OverTgt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatBesselToFourierJacobiRowMulLaws
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FlatRow

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)

def prH : D.host.E →+* k := p.π.comp (incA D)

theorem pr_eq : p.pr = prH p := rfl

theorem e_mul_ι (x : k) : p.e * p.ι x = p.ι x := by rw [← p.ι_π, p.π_ι]

theorem e_smul_map {m n : Type} (K : Matrix m n k) : p.e • K.map p.ι = K.map p.ι := by
  funext i j; exact e_mul_ι p (K i j)

theorem map_ι_π {m n : Type} (K : Matrix m n k) : (K.map p.ι).map p.π = K := by
  funext i j; exact p.π_ι (K i j)

theorem xi_ne : p.xi ≠ 0 := (map_ne_zero (prH p)).2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)

theorem hz_ne {ρ : ℕ} (B : BesLev D ρ) : p.hz B ≠ 0 := (map_ne_zero (prH p)).2 B.line.2

theorem char_half {ψ : AddChar (AF D.host.F) ℂ} {ψk : AddChar k Circle} (h : p.IsChar ψ ψk) {a : AE D} (ha : p.e * a = a) :
    ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * a)) = ψk (p.π a) := by
  rw [h, p.ι_π, ha]; rfl

theorem infPart_conj_e : infPart D (cA D p.e) = 0 := by
  obtain ⟨h1, h2, v, ε, ⟨α, rfl, -⟩, h3⟩ := p.split
  have h4 : cA D p.e * cA D p.e = cA D p.e := by rw [← map_mul, h1]
  have h5 : cA D p.e = cA D p.e * (p.e + cA D p.e) := by rw [mul_add, mul_comm (cA D p.e) p.e, h2, h4, zero_add]
  have h6 : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = 0 :=
    TensorProduct.zero_tmul _ _
  rw [h5, h3, map_mul, h6, mul_zero]

def xiPt (S : HSp D) {ρ : ℕ} (K : Matrix (Fin S.rank) (Fin ρ) k) : Mx D ρ S.rank :=
  adj (gA S ⬝ K.map p.ι)

theorem smul_xiPt (S : HSp D) {ρ : ℕ} (K : Matrix (Fin S.rank) (Fin ρ) k) : cA D p.e • xiPt p S K = xiPt p S K := by
  rw [xiPt, ← adj_smul, ← Matrix.mul_smul, e_smul_map]

theorem mxAt_xiPt (S : HSp D) {ρ : ℕ} (K : Matrix (Fin S.rank) (Fin ρ) k) : GlobalTheory.FinPl.MxAt (fun _ => True) (xiPt p S K) := by
  intro i j
  refine ⟨?_, ?_⟩
  · have h : cA D p.e * xiPt p S K i j = xiPt p S K i j := congrFun (congrFun (smul_xiPt p S K) i) j
    change infPart D _ = 0
    rw [← h, map_mul, infPart_conj_e, zero_mul]
  · exact Ideal.mem_iInf.2 fun w => (w.2 trivial).elim

section Pair

variable {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (K : Matrix (Fin V₀.rank) (Fin σ) k)

theorem isHalf_xiPt : IsHalf (cA D p.e) (dV.ext0 W (dW.incX V₀ (xiPt p V₀ K))) := by
  have h : cA D p.e • (dW.jX ⬝ xiPt p V₀ K ⬝ dV.p0) = dW.jX ⬝ xiPt p V₀ K ⬝ dV.p0 := by
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, smul_xiPt]
  intro i j
  exact congrFun (congrFun h i) j

theorem hO_xiPt (x : WO V W) :
    hO V W x (dV.ext0 W (dW.incX V₀ (xiPt p V₀ K))) = (dV.j0 ⬝ (K.map p.ι ⬝ (dW.pY ⬝ x))).trace := by
  rw [hO_eq_trace, HypDec.matrixExtendByZero_apply, HypDec.incX_apply, xiPt, dV.p0_eq, dW.pY_eq]
  simp only [adj_mul, adj_adj, adj_gA, adj_giA, Matrix.mul_assoc, giA_gA_cancel]

theorem hO_incAdj_xiPt (y : Mx D V₀.rank σ) :
    hO V₀ W (dW.incAdj V₀ y) (dW.incX V₀ (xiPt p V₀ K)) =
      (K.map p.ι ⬝ (incA D (-D.host.xi0⁻¹) • (adj y ⬝ gA V₀))).trace := by
  rw [hO_eq_trace, HypDec.incAdj_apply, HypDec.incY_apply, HypDec.incX_apply, xiPt]
  simp only [adj_mul, adj_adj, adj_gA, Matrix.mul_assoc, giA_gA_cancel, cancel₃ dW.gram_XY, Matrix.one_mul]

variable {ψ : AddChar (AF D.host.F) ℂ} {ψk : AddChar k Circle}

theorem char_up (h : p.IsChar ψ ψk) {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
    (FV : Frame k V.rank Y') (FW : Frame k W.rank Y) (t : Matrix Y Y' k) :
    ψ (symplO V W (p.up FV FW t) (dV.ext0 W (dW.incX V₀ (xiPt p V₀ K)))) =
      ψk ((FV.γ * (dV.j0.map p.π * K) * (dW.pY.map p.π * FW.β) * t).trace) := by
  rw [symplO, hO_xiPt, char_half p h]
  · congr 2
    rw [AddMonoidHom.map_trace, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, map_ι_π, Place.up, map_ι_π]
    simp only [← Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]
    simp only [← Matrix.mul_assoc]
  · rw [← smul_eq_mul, ← Matrix.trace_smul, ← Matrix.mul_smul, ← Matrix.smul_mul, e_smul_map]

theorem char_incAdj (h : p.IsChar ψ ψk) (y : Mx D V₀.rank σ) :
    ψ (symplO V₀ W (dW.incAdj V₀ y) (dW.incX V₀ (xiPt p V₀ K))) =
      ψk (-p.xi⁻¹ * (K * (adj y ⬝ gA V₀).map p.π).trace) := by
  rw [symplO, hO_incAdj_xiPt, char_half p h]
  · congr 2
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, map_mul, AddMonoidHom.map_trace, Matrix.map_mul, map_ι_π]
    congr 1
    change prH p _ = -(prH p _)⁻¹
    rw [map_neg, map_inv₀]
  · rw [← smul_eq_mul, ← Matrix.trace_smul, ← Matrix.smul_mul, e_smul_map]

end Pair

theorem mul_col {l m n Y : Type} [Fintype m] {P : Matrix l m k} {X : Matrix m n k} {M : Matrix m Y k} {j : Y} {i : n} {a : k}
    (h : ∀ r, M r j = a * X r i) (i₀ : l) : (P * M) i₀ j = a * (P * X) i₀ i := by
  simp only [Matrix.mul_apply, h, Finset.mul_sum, mul_left_comm]

theorem jac_row {ρ : ℕ} {J : JacLev D ρ} {s hh : k} {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
    {G₀ : Frame k J.W₀.rank n} {FW : Frame k J.W.rank (n ⊕ Fin c)} (h : p.IsJacFrame J s hh G₀ FW) (i : Fin ρ) (l : Fin c)
    (hl : l.val + i.val + 1 = 2 * ρ) (r : n ⊕ Fin c) :
    (J.d.pY.map p.π * FW.β) i r = if r = Sum.inr l then s * (hh / p.xi) * (-1 / p.xi) ^ (ρ - 1 - i.val) else 0 := by
  obtain ⟨hc, h0, hX, hY⟩ := h
  rcases r with a | j
  · rw [if_neg Sum.inl_ne_inr, mul_col (a := 1) (X := J.d.j0.map p.π * G₀.β) (i := a) (fun r => by rw [one_mul]; exact h0 r a),
      ← Matrix.mul_assoc, ← Matrix.map_mul, J.d.pY_j0]
    simp
  · by_cases hj : j.val < ρ
    · have hne : (Sum.inr j : n ⊕ Fin c) ≠ Sum.inr l := fun e => by
        have := congrArg Fin.val (Sum.inr_injective e); omega
      rw [if_neg hne, mul_col (X := J.d.jX.map p.π) (i := ⟨j.val, hj⟩) (hX ⟨j.val, hj⟩ j rfl), ← Matrix.map_mul, J.d.pY_jX]
      simp
    · have hj' : 2 * ρ - 1 - j.val < ρ := by have := j.2; omega
      rw [mul_col (X := J.d.jY.map p.π) (i := ⟨_, hj'⟩) (hY ⟨_, hj'⟩ j (by have := j.2; simp only; omega)), ← Matrix.map_mul,
        J.d.pY_jY, Matrix.map_apply, Matrix.one_apply]
      by_cases e : j = l
      · have e' : i = ⟨_, hj'⟩ := Fin.ext (by subst e; simp only; omega)
        rw [if_pos e', if_pos (congrArg _ e), map_one, mul_one, ← e']
      · have e' : i ≠ ⟨_, hj'⟩ := fun e' => e (Fin.ext (by have := congrArg Fin.val e'; have := j.2; simp only at *; omega))
        rw [if_neg e', if_neg (fun x => e (Sum.inr_injective x)), map_zero, mul_zero]

theorem core_val {ρ : ℕ} {B : BesLev D ρ} {s : k} {n : Type} [Fintype n] [DecidableEq n] {FA : Frame k B.A.rank n}
    {F₀ : Frame k B.V₀.rank (n ⊕ Unit)} (h : p.IsCoreFrame B s FA F₀) (i : Fin ρ) (q : n ⊕ Unit) :
    ((adj (yZero B.V₀ ρ (vecB B.o B.ζ)) ⬝ gA B.V₀).map p.π * F₀.β) i q =
      if i.val + 1 = ρ ∧ q = Sum.inr () then -(s * p.hz B) else 0 := by
  have h1 : ∀ x, (adj (yZero B.V₀ ρ (vecB B.o B.ζ)) ⬝ gA B.V₀).map p.π i x =
      -(if i.val + 1 = ρ then 1 else 0) * prH p ((star B.ζ ᵥ* (B.o.iBᴴ * B.V₀.gram)) x) := by
    intro x
    rw [← Matrix.vecMul_vecMul, ← Matrix.star_mulVec]
    simp only [Matrix.map_apply, Matrix.mul_apply, adj, yZero, zEll, Matrix.transpose_apply, Matrix.neg_apply,
      Matrix.vecMulVec_apply, ell, ratV, Matrix.vecMul, dotProduct, map_sum, Finset.mul_sum, gA, rat]
    refine Finset.sum_congr rfl fun d _ => ?_
    split_ifs
    · rw [mul_one, map_neg, GlobalTheory.DualPairCheck.cA_incA, neg_mul, ← map_mul, map_neg, neg_one_mul]; rfl
    · simp
  rw [Matrix.mul_apply]
  simp only [h1, mul_assoc, ← Finset.mul_sum]
  rcases q with a | ⟨⟨⟩⟩
  · have h2 : ∀ y, ∑ x, prH p ((star B.ζ ᵥ* (B.o.iBᴴ * B.V₀.gram)) x) * prH p (B.o.iA x y) = 0 := by
      intro y
      have : ((star B.ζ ᵥ* (B.o.iBᴴ * B.V₀.gram)) ᵥ* B.o.iA) y = 0 := by
        rw [Matrix.vecMul_vecMul, B.o.orth, Matrix.vecMul_zero]; rfl
      simp only [← map_mul, ← map_sum]
      rw [← map_zero (prH p), ← this]; rfl
    have h3 : ∑ x, prH p ((star B.ζ ᵥ* (B.o.iBᴴ * B.V₀.gram)) x) * F₀.β x (Sum.inl a) = 0 := by
      have e : ∀ x, F₀.β x (Sum.inl a) = ∑ y, prH p (B.o.iA x y) * FA.β y a := fun x => h.1 x a
      simp only [e, Finset.mul_sum, ← mul_assoc]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_mul, h2, zero_mul, Finset.sum_const_zero]
    rw [h3]; simp
  · have h3 : ∑ x, prH p ((star B.ζ ᵥ* (B.o.iBᴴ * B.V₀.gram)) x) * F₀.β x (Sum.inr ()) = s * p.hz B := by
      have : star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ = (star B.ζ ᵥ* (B.o.iBᴴ * B.V₀.gram)) ⬝ᵥ vecB B.o B.ζ := by
        rw [← B.o.isoB, vecB, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
      rw [Place.hz, this, pr_eq, dotProduct, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [h.2, map_mul, pr_eq]; ring
    rw [h3]; by_cases e : i.val + 1 = ρ <;> simp [e]

theorem core_col {ρ : ℕ} {B : BesLev D ρ} {s : k} {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} {FA : Frame k B.A.rank n}
    {F₀ : Frame k B.V₀.rank (n ⊕ Unit)} {FV : Frame k B.V.rank (n ⊕ Fin c)} (h₀ : p.IsCoreFrame B s FA F₀)
    (h : p.IsBesFrame B s FA FV) (q : n ⊕ Fin c) (hq : ∀ i, q = Sum.inr i → i.val = ρ) (x : Fin B.V.rank) :
    (B.d.j0.map p.π * F₀.β) x (q.map id fun _ => ()) = FV.β x q := by
  rcases q with a | i
  · rw [h.2.1, pr_eq, Matrix.map_mul, Matrix.mul_assoc,
      mul_col (a := 1) (X := B.o.iA.map (prH p) * FA.β) (i := a) (fun r => by rw [one_mul]; exact h₀.1 r a), one_mul]
    rfl
  · rw [h.2.2.2.1 i (hq i rfl), pr_eq, Matrix.mulVec, dotProduct, map_sum, Finset.mul_sum, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [map_mul, mul_left_comm]
    exact congrArg _ (h₀.2 y)

theorem trace_single {m n l : Type} [Fintype m] [Fintype n] [DecidableEq n] [Fintype l] [DecidableEq l] (M : Matrix m n k) (q : n)
    (i : l) (a : k) (N : Matrix l m k) : (M * Matrix.single q i a * N).trace = a * (N * M) i q := by
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.trace_single_mul, smul_eq_mul]

theorem flatBF_mul_row : ∀ (D : D7), FlatLaw D → GlobalTheory.FinPl.FlatLaws D → OmLoc D → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (p : Place D k) (ν : Measure k), ν.IsAddHaarMeasure → ∀ (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (st : StepBF ψ B J) (s : k), s ≠ 0 → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FV : Frame k B.V.rank (n' ⊕ Fin (c + 1))) (G₀ : Frame k J.W₀.rank n) (FW : Frame k J.W.rank (n ⊕ Fin c)), p.IsCoreFrame B s FA F₀ → p.IsBesFrame B s FA FV → p.IsJacFrame J s (p.hz B) G₀ FW → ∀ (Tm : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] (WO B.V J.W → ℂ)), p.IsModel ψ FV FW Tm → ∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), (∃ l, r = Sum.inr l ∧ ρ ≤ l.val ∧ ∀ i, q = Sum.inr i → i.val = ρ) → ∀ (b : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = (ψk (b * (t r q - GlobalTheory.RootEx.basePt c (0 : Matrix n n' k) r q)) : ℂ) * Φ.1 t) → flatBF st (Tm Φ') = flatBF st (Tm Φ) := by
  intro D hF hL _ k _ _ _ _ _ _ p ν _ ψ ψk hch ρ B J st s hs n n' _ _ _ _ c FA F₀ FV G₀ FW h₀ hB hJ Tm hT r q hr b Φ Φ' hΦ
  obtain ⟨l, rfl, hl, hq⟩ := hr
  have hc := hJ.1
  have hi : 2 * ρ - 1 - l.val < ρ := by have := l.2; omega
  obtain ⟨i, hli⟩ : ∃ i : Fin ρ, l.val + i.val + 1 = 2 * ρ := ⟨⟨_, hi⟩, by have := l.2; simp only; omega⟩
  have hxi := xi_ne p
  have hhz := hz_ne p B
  obtain ⟨κ, hκ⟩ : ∃ κ, κ = s * (p.hz B / p.xi) * (-1 / p.xi) ^ (ρ - 1 - i.val) := ⟨_, rfl⟩
  have hκ0 : κ ≠ 0 := by
    rw [hκ]; exact mul_ne_zero (mul_ne_zero hs (div_ne_zero hhz hxi)) (pow_ne_zero _ (div_ne_zero (by simp) hxi))
  obtain ⟨K, hK⟩ : ∃ K, K = F₀.β * Matrix.single (q.map id fun _ => ()) i (b / κ) := ⟨_, rfl⟩
  have h1 : ∀ t, ψ (symplO B.V J.W (p.up FV FW t) (B.d.ext0 J.W (J.d.incX B.V₀ (xiPt p B.V₀ K)))) =
      ψk (b * t (Sum.inr l) q) := by
    intro t
    have e : FV.γ * (B.d.j0.map p.π * K) * (J.d.pY.map p.π * FW.β) * t =
        FV.γ * (B.d.j0.map p.π * F₀.β) * Matrix.single (q.map id fun _ => ()) i (b / κ) * (J.d.pY.map p.π * FW.β * t) := by
      simp only [hK, Matrix.mul_assoc]
    rw [char_up p B.d J.d K hch, e, trace_single, ← Matrix.mul_assoc _ FV.γ,
      mul_col (a := 1) (X := FV.β) (i := q) (fun x => by rw [one_mul]; exact core_col p h₀ hB q hq x), one_mul,
      Matrix.mul_assoc _ FV.γ, FV.γβ, Matrix.mul_one, Matrix.mul_apply]
    simp only [jac_row p hJ i l hli, ← hκ, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← mul_assoc, div_mul_cancel₀ _ hκ0]
  have h2 : ψ (symplO B.V₀ J.W (J.d.incAdj B.V₀ (yZero B.V₀ ρ (vecB B.o B.ζ))) (J.d.incX B.V₀ (xiPt p B.V₀ K))) =
      ψk (b * GlobalTheory.RootEx.basePt c (0 : Matrix n n' k) (Sum.inr l) q) := by
    rw [char_incAdj p J.d K hch, hK, trace_single, core_val p h₀]
    congr 2
    rcases q with a | j
    · simp [GlobalTheory.RootEx.basePt]
    · have hj := hq j rfl
      by_cases e : i.val + 1 = ρ
      · have e1 : l.val = j.val := by omega
        have e2 : ρ - 1 - i.val = 0 := by omega
        rw [e2, pow_zero, mul_one] at hκ
        simp only [GlobalTheory.RootEx.basePt, e, e1, Sum.map_inr, and_self, if_true, fromBlocks_apply₂₂, of_apply, hκ]
        field_simp
      · have e1 : l.val ≠ j.val := by omega
        simp [GlobalTheory.RootEx.basePt, e, e1]
  obtain ⟨a, ha⟩ : ∃ a : ℂ, a = ψk (b * GlobalTheory.RootEx.basePt c (0 : Matrix n n' k) (Sum.inr l) q) := ⟨_, rfl⟩
  have ha0 : a ≠ 0 := by rw [ha]; exact Circle.coe_ne_zero _
  have h3 := hT.modul _ (isHalf_xiPt p B.d J.d K) Φ (a • Φ') fun t => by
    rw [h1, Submodule.coe_smul, Pi.smul_apply, hΦ, smul_eq_mul, ← mul_assoc, ha, ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
    congr 3
    ring
  have h4 := ((hL ψ fun _ => True).1 ρ B J st).Heisenberg₂.iso _ (hT.theta Φ) _ (mxAt_xiPt p B.V₀ K)
  rw [← h3, h2, ← ha, map_smul, (GlobalTheory.FlatLin.flatBF_linear D hF ψ ρ B J st _ _ a (hT.theta Φ') (hT.theta Φ')).2] at h4
  exact smul_right_injective _ ha0 h4

end GlobalTheory.FlatRow

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatFourierJacobiToBesselColumnMulLaws
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.StepData

noncomputable section

namespace GlobalTheory.FlatColLawFB

open GlobalTheory.FlatColLaw

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem frame_col (p : Place D k) {σ : ℕ} (B : BesLev D σ) (s : k) {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
    (FA : Frame k B.A.rank n) (FV : Frame k B.V.rank (n ⊕ Fin c)) (hB : p.IsBesFrame B (s * p.xi) FA FV)
    (j : Fin (σ + 1)) (l : Fin c) (hl : l.val = j.val) (x : Fin B.V.rank) :
    FV.β x (Sum.inr l) = s * p.xi ^ (σ + 1 - j.val) * ((xLast B.d (vecB B.o B.ζ)).map p.π) x j := by
  obtain ⟨-, -, hX, hz, -⟩ := hB
  induction j using Fin.lastCases with
  | last =>
    rw [hz l hl x]
    simp only [xLast, Matrix.map_apply, Matrix.of_apply, Fin.snoc_last, Fin.val_last, Nat.add_sub_cancel_left, pow_one]
    congr 1
    simp only [Place.pr, Matrix.mulVec, dotProduct, map_sum, map_mul]
    rfl
  | cast j =>
    rw [hX j l hl x]
    have hj := j.isLt
    simp only [xLast, Matrix.map_apply, Matrix.of_apply, Fin.snoc_castSucc, Fin.val_castSucc]
    rw [show σ + 1 - j.val = (σ - j.val) + 1 by omega, pow_succ', ← mul_assoc]
    rfl

theorem flatFB_mulcol : ∀ (D : D7), GlobalTheory.FinPl.FlatLaws D → OmLoc D → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (st : StepFB ψ J B) (s : k), s ≠ 0 → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (G₀ : Frame k J.W₀.rank n') (FW : Frame k J.W.rank (n' ⊕ Fin (c + 1))) (FA : Frame k B.A.rank n) (F₀ : Frame k B.V₀.rank (n ⊕ Unit)) (FV : Frame k B.V.rank (n ⊕ Fin c)), p.IsJacFrame J s (-p.xi ^ 2 * p.hz B) G₀ FW → p.IsCoreFrame B (s * p.xi) FA F₀ → p.IsBesFrame B (s * p.xi) FA FV → ∀ Tm, p.IsModel ψ FW FV Tm → ∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), (∃ i, q = Sum.inr i ∧ i.val ≤ σ ∧ ¬ Free (σ + 1) (r, q)) → ∀ (b : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = (ψk (b * (t r q - basePt c (0 : Matrix n n' k) r q)) : ℂ) * Φ.1 t) → flatFB st (Tm Φ') = flatFB st (Tm Φ) := by
  intro D hFL _ k _ _ _ _ _ _ p ψ ψk hχ σ J B st s hs n n' _ _ _ _ c G₀ FW FA F₀ FV hjac _ hbes Tm hTm r q hq b Φ Φ' hΦ'
  obtain ⟨i, rfl, hi, hfree⟩ := hq
  have hc : c = 2 * σ + 1 := hbes.1
  have hκ : ∀ m : ℕ, s * p.xi ^ m ≠ 0 := fun m => mul_ne_zero hs (pow_ne_zero _ (xi_ne p))
  let i₀ : Fin (σ + 1) := ⟨i.val, by omega⟩
  let zk : Matrix (Fin (σ + 1)) (Fin B.V.rank) k :=
    Matrix.of fun i' β => if i' = i₀ then b * (s * p.xi ^ (σ + 1 - i.val)) * FV.γ r β else 0
  let a : Mx D B.V.rank (σ + 1) := giA B.V ⬝ adj (zk.map p.ι : Mx D (σ + 1) B.V.rank)
  have ha : IsHalf (cA D p.e) a := isHalf_mul_left _ (isHalf_adj p zk)
  have hy : IsHalf (cA D p.e) (J.d.extY B.V a) := isHalf_mul_right _ ha
  have hW : ∀ j : Fin (σ + 1), (FV.γ * (xLast B.d (vecB B.o B.ζ)).map p.π) r j = (s * p.xi ^ (σ + 1 - j.val))⁻¹ *
      (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r (Sum.inr ⟨j.val, by omega⟩) := fun j => by
    rw [← FV.γβ]
    exact col_mul _ _ _ _ _ (hκ _) (frame_col p B s FA FV hbes j ⟨j.val, by omega⟩ rfl) r
  have hB : ∀ t, ψ (symplO J.W B.V (p.up FW FV t) (J.d.extY B.V a)) = (ψk (b * t r (Sum.inr i)) : ℂ) := fun t => by
    rw [psi_sympl_extY p hχ, trace_row_mul, Place.up, map_iota_mul, map_iota_pi, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, FV.γβ, Matrix.one_mul,
      col_mul _ _ FW.β i₀ (Sum.inr i) (hκ _) (hjac.2.2.1 i₀ i rfl), Matrix.mul_assoc, FW.γβ, Matrix.mul_one, mul_assoc,
      mul_inv_cancel_left₀ (hκ _)]
  have hD : ψ (symplO J.W B.V (J.d.extX B.V (xLast B.d (vecB B.o B.ζ))) (J.d.extY B.V a)) =
      (ψk (b * basePt c (0 : Matrix n n' k) r (Sum.inr i)) : ℂ) := by
    rw [psi_sympl_extY p hχ, trace_row_mul, HypDec.extX_apply, Matrix.mul_assoc, HypDec.pX_jX, Matrix.mul_one, hW,
      mul_assoc, mul_inv_cancel_left₀ (hκ _)]
    congr 3
    rcases r with r | r
    · simp [basePt]
    · simp [basePt, Matrix.one_apply, Fin.ext_iff, i₀]
  have hU : GlobalTheory.FinPl.UInv B.V (xLast B.d (vecB B.o B.ζ)) a := fun u => by
    rw [pairS_giA_adj, pairS_giA_adj, ← Matrix.mul_assoc]
    refine trace_mul_uni _ (fun i' j hj => ?_) u
    rw [map_iota_mul, Matrix.map_apply, row_mul]
    split_ifs with h
    · subst h
      rw [hW, Matrix.one_apply_ne, mul_zero, mul_zero, map_zero]
      rintro rfl
      exact hfree hj
    · exact map_zero _
  obtain ⟨v, hv⟩ := exists_mxAt p
  have hlaw := ((hFL ψ (· = v)).2 σ J B st).Heisenberg₂.dual _ (hTm.theta Φ) a (hv _ _ a ha) hU
  have hmod := hTm.modul _ hy Φ ((ψk (b * basePt c (0 : Matrix n n' k) r (Sum.inr i)) : ℂ) • Φ') fun t => by
    rw [hB, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, hΦ', ← mul_assoc, ← Circle.coe_mul, ← AddChar.map_add_eq_mul,
      ← mul_add, add_sub_cancel]
  rw [← hmod, hD, map_smul, GlobalTheory.HandHom.flatFB_smul] at hlaw
  exact smul_right_injective _ (Circle.coe_ne_zero _) hlaw

end GlobalTheory.FlatColLawFB

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapIntertwinesCoreHeisenbergOperators
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

namespace GlobalTheory.FlatHeis

theorem flatAt_heisO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (vS : VolM D W.rank ρ) (vT : VolM D σ V₀.rank) (vU : VolU D ρ) (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ) (Ψ : WO V W → ℂ), IsThetaFunO ψ V W Ψ → (∀ w, evalAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 (heisO ψ V W (dV.ext0 W (dW.inc0 V₀ w)) Ψ) x y = heisO ψ V₀ W₀ w (evalAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 Ψ x y)) ∧ (∀ w, flatAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 vU.ν x y (heisO ψ V W (dV.ext0 W (dW.inc0 V₀ w)) Ψ) = heisO ψ V₀ W₀ w (flatAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 vU.ν x y Ψ)) ∧ ∀ γ, flatAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 vU.ν x y Ψ (ratW W₀ V₀ γ) = flatAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 vU.ν x y Ψ 0 := by
  intro D ψ hψ V V₀ W W₀ ρ σ dV dW vS vT vU x y Ψ hΨ
  have hMV := GlobalTheory.T.mixedCoordinates_of_thetaFunction_are_thetaFunctions D ψ hψ
  have hHT := GlobalTheory.T.heisenbergThetaMixedModelTarget_of_mixedModel D ψ hψ
  have hS : ∀ x', IsThetaFunO ψ V₀ W (dV.mixS W ψ vS.μ vS.𝓕 Ψ x') := fun x' =>
    hMV.1 V V₀ W ρ dV vS.μ vS.𝓕 vS.covol Ψ hΨ x'
  have hE : ∀ x', IsThetaFunO ψ V₀ W₀ (evalAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 Ψ x' y) := fun x' =>
    hMV.2 V₀ W W₀ σ dW vT.μ vT.𝓕 vT.covol _ (hS x') y
  have h1 : ∀ x' w, evalAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 (heisO ψ V W (dV.ext0 W (dW.inc0 V₀ w)) Ψ) x' y =
      heisO ψ V₀ W₀ w (evalAt ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 Ψ x' y) := by
    intro x' w
    have a := (GlobalTheory.T.heisenbergOperator_thetaFunctional_mixedSourceModel D ψ hψ V V₀ W ρ dV vS Ψ hΨ).2.2.1 x' (dW.inc0 V₀ w)
    have b := (hHT V₀ W W₀ σ dW vT.μ vT.𝓕 vT.covol _ (hS x')).2.1 w y
    unfold evalAt
    rw [a, b]
  refine ⟨fun w => h1 x w, fun w => ?_, fun γ => ?_⟩
  · funext w'
    show ∫ u, flatFun ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 x y (heisO ψ V W (dV.ext0 W (dW.inc0 V₀ w)) Ψ) w' u ∂vU.ν =
      ψ (symplOH V₀ W₀ w' w) * ∫ u, flatFun ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 x y Ψ (w' + w) u ∂vU.ν
    rw [← integral_const_mul]
    refine congrArg (fun F : UX D ρ → ℂ => ∫ u, F u ∂vU.ν) (funext fun u => ?_)
    simp only [flatFun, h1, heisO]
    ring
  · show ∫ u, flatFun ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 x y Ψ (ratW W₀ V₀ γ) u ∂vU.ν =
      ∫ u, flatFun ψ dV dW vS.μ vS.𝓕 vT.μ vT.𝓕 x y Ψ 0 u ∂vU.ν
    refine congrArg (fun F : UX D ρ → ℂ => ∫ u, F u ∂vU.ν) (funext fun u => ?_)
    have q := (hE (x ⬝ u.1.1)).quasi γ 0
    rw [add_zero, symplOH_zero_right, neg_zero, AddChar.map_zero_eq_one, one_mul] at q
    unfold flatFun
    rw [q]

end GlobalTheory.FlatHeis

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergBasisDerivEqOfUniformLimitsStatement
section
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergBasisDeriv_eq_of_uniform_limits : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S T : HSp D) (G : ℕ → WO S T → ℂ) (F F' : WO S T → ℂ), (∀ j, IsThetaFunO ψ S T (G j)) → TendstoUniformly G F Filter.atTop → ∀ a : (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool), TendstoUniformly (fun j => GlobalTheory.Size.heisDer ψ θ a (G j)) F' Filter.atTop → GlobalTheory.Size.heisDer ψ θ a F = F' := by
  first | exact @GlobalTheory.ThetaLimDeriv.heisDer_of_tendstoUniformly | exact GlobalTheory.ThetaLimDeriv.heisDer_of_tendstoUniformly | (intros; apply GlobalTheory.ThetaLimDeriv.heisDer_of_tendstoUniformly <;> assumption)
end

