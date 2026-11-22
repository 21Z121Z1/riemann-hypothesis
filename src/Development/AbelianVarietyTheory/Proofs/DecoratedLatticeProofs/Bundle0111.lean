import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0105
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0099
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitarySupportedAtPlaceOfDualIsotropicFram
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

namespace GlobalTheory.IwaPlace.BuildQ

variable {D : D7}

theorem mulVec_colMul {m n k : ℕ} (M : Mx D m n) (X : Mx D n k) (i : Fin k) (a : AE D) :
    M *ᵥ colMul X i a = fun r => a * (M ⬝ X) r i := by
  funext r
  simp only [colMul, Matrix.mulVec, dotProduct, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem adj_diagonal {n : ℕ} (f : Fin n → AE D) :
    adj (Matrix.diagonal f) = Matrix.diagonal (fun i => cA D (f i)) := by
  ext i j; simp [adj, Matrix.diagonal_apply]; split_ifs <;> simp_all [eq_comm]

theorem mul_tail {a m n k : ℕ} {A : Mx D a m} {B : Mx D m n} {C : Mx D a n} (h : A ⬝ B = C) (X : Mx D n k) :
    A ⬝ (B ⬝ X) = C ⬝ X := by
  rw [← Matrix.mul_assoc, h]

theorem mul_tail₃ {a m n p k : ℕ} {A : Mx D a m} {B : Mx D m n} {B' : Mx D n p} {C : Mx D a p}
    (h : A ⬝ (B ⬝ B') = C) (X : Mx D p k) :
    A ⬝ (B ⬝ (B' ⬝ X)) = C ⬝ X := by
  rw [← h]; simp only [Matrix.mul_assoc]

theorem mul_tail₄ {a m n p q k : ℕ} {A : Mx D a m} {B : Mx D m n} {B' : Mx D n p} {B'' : Mx D p q} {C : Mx D a q}
    (h : A ⬝ (B ⬝ (B' ⬝ B'')) = C) (X : Mx D q k) :
    A ⬝ (B ⬝ (B' ⬝ (B'' ⬝ X))) = C ⬝ X := by
  rw [← h]; simp only [Matrix.mul_assoc]

end GlobalTheory.IwaPlace.BuildQ

namespace GlobalTheory.IwaPlace.BuildQ

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

theorem gXX {k : ℕ} (X : Mx D ρ k) : adj d.jX ⬝ (gA S ⬝ (d.jX ⬝ X)) = 0 := by
  rw [mul_tail₃ d.gram_XX, Matrix.zero_mul]
theorem gYY {k : ℕ} (X : Mx D ρ k) : adj d.jY ⬝ (gA S ⬝ (d.jY ⬝ X)) = 0 := by
  rw [mul_tail₃ d.gram_YY, Matrix.zero_mul]
theorem gYX {k : ℕ} (X : Mx D ρ k) : adj d.jY ⬝ (gA S ⬝ (d.jX ⬝ X)) = X := by
  rw [mul_tail₃ d.gram_YX, Matrix.one_mul]
theorem gXY {k : ℕ} (X : Mx D ρ k) : adj d.jX ⬝ (gA S ⬝ (d.jY ⬝ X)) = X := by
  rw [mul_tail₃ d.gram_XY, Matrix.one_mul]
theorem g0X {k : ℕ} (X : Mx D ρ k) : adj d.j0 ⬝ (gA S ⬝ (d.jX ⬝ X)) = 0 := by
  rw [mul_tail₃ d.gram_0X, Matrix.zero_mul]
theorem g0Y {k : ℕ} (X : Mx D ρ k) : adj d.j0 ⬝ (gA S ⬝ (d.jY ⬝ X)) = 0 := by
  rw [mul_tail₃ d.gram_0Y, Matrix.zero_mul]
theorem adjoint_jX_gram_j_zero_eq_zero {k : ℕ} (X : Mx D S₀.rank k) : adj d.jX ⬝ (gA S ⬝ (d.j0 ⬝ X)) = 0 := by
  rw [mul_tail₃ d.wittDecomp_gram_X_anisotropic, Matrix.zero_mul]
theorem g00 {k : ℕ} (X : Mx D S₀.rank k) : adj d.j0 ⬝ (gA S ⬝ (d.j0 ⬝ X)) = gA S₀ ⬝ X :=
  mul_tail₃ d.gram_00 X

end GlobalTheory.IwaPlace.BuildQ

namespace GlobalTheory.IwaPlace.BuildQ

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

theorem smul_eq_of_mem {P : Pl D → Prop} {ε : AE D} (hε : ∀ a, a ∈ idAt D P ↔ ε * a = a)
    {m n : ℕ} {x : Mx D m n} (hx : ∀ i j, x i j ∈ idAt D P) : ε • x = x := by
  ext i j; rw [Matrix.smul_apply, smul_eq_mul, (hε _).1 (hx i j)]

theorem one_sub_mul_self {ε : AE D} (hεε : ε * ε = ε) : (1 - ε) * ε = 0 := by
  rw [sub_mul, one_mul, hεε, sub_self]

theorem one_sub_sq {ε : AE D} (hεε : ε * ε = ε) : (1 - ε) * (1 - ε) = 1 - ε := by
  rw [mul_sub, mul_one, one_sub_mul_self hεε, sub_zero]

theorem kill_left {ε : AE D} (hεε : ε * ε = ε) {m n k : ℕ} {x : Mx D m n} (hx : ε • x = x) (X : Mx D n k) :
    (1 - ε) • (x ⬝ X) = 0 := by
  rw [← Matrix.smul_mul, ← hx, smul_smul, one_sub_mul_self hεε, zero_smul, Matrix.zero_mul]

theorem kill_right {ε : AE D} (hεε : ε * ε = ε) {m n k : ℕ} {x : Mx D n k} (hx : ε • x = x) (X : Mx D m n) :
    (1 - ε) • (X ⬝ x) = 0 := by
  rw [← Matrix.mul_smul, ← hx, smul_smul, one_sub_mul_self hεε, zero_smul, Matrix.mul_zero]

theorem diag_absorb {ε : AE D} {n : ℕ} {α : Fin n → AE D} (hαε : ∀ i, ε * α i = α i) :
    ε • Matrix.diagonal α = Matrix.diagonal α := by
  ext i j
  simp only [Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]
  split_ifs with h
  · exact hαε i
  · rw [mul_zero]

theorem diag_const {ε : AE D} {n : ℕ} {α β : Fin n → AE D} (hαβ : ∀ i, α i * β i = ε) :
    (Matrix.diagonal fun i => α i * β i) = ε • (1 : Mx D n n) := by
  have : (fun i => α i * β i) = fun _ => ε := funext hαβ
  rw [this]
  ext i j
  by_cases h : i = j
  · subst h; simp
  · simp [h]

set_option maxHeartbeats 1000000 in
theorem imYX {ε : AE D} (hεε : ε * ε = ε) (hεc : cA D ε = ε) {α β : Fin ρ → AE D} (hαε : ∀ i, ε * α i = α i)
    (hαβ : ∀ i, α i * β i = ε) {b : Mx D ρ ρ} (hb : ε • b = b) {c' : Mx D S.rank ρ} (hc : ε • c' = c')
    (H1 : adj c' ⬝ (gA S ⬝ (d.jX ⬝ b)) = ε • (1 : Mx D ρ ρ)) :
    adj (c' ⬝ Matrix.diagonal (fun i => cA D (α i)) + (1 - ε) • d.jY) ⬝
      (gA S ⬝ (d.jX ⬝ (b ⬝ Matrix.diagonal β + (1 - ε) • (1 : Mx D ρ ρ)))) = 1 := by
  have hcA1 : cA D (1 - ε) = 1 - ε := by rw [map_sub, map_one, hεc]
  have hadjc : ε • adj c' = adj c' := by
    conv_rhs => rw [← hc]
    rw [adj_smul, hεc]
  simp only [adj_add, adj_mul, adj_smul, adj_diagonal, cA_cA, hcA1, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  simp only [mul_tail₄ H1, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.one_mul, gYX d, d.gram_YX, kill_left hεε (diag_absorb hαε), kill_left hεε hb, add_zero, smul_smul]
  rw [zero_add, Matrix.diagonal_mul_diagonal, one_sub_sq hεε]
  rw [diag_const hαβ, smul_smul, hεε, ← add_smul, add_sub_cancel, one_smul]

end GlobalTheory.IwaPlace.BuildQ

namespace GlobalTheory.IwaPlace.BuildQ

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

theorem kill_mid₂ {ε : AE D} (hεε : ε * ε = ε) {m n p q k : ℕ} {x : Mx D p q} (hx : ε • x = x)
    (A : Mx D m n) (B : Mx D n p) (X : Mx D q k) : (1 - ε) • (A ⬝ (B ⬝ (x ⬝ X))) = 0 := by
  rw [← Matrix.mul_smul, ← Matrix.mul_smul, kill_left hεε hx, Matrix.mul_zero, Matrix.mul_zero]

theorem absorb_mul {ε : AE D} {m n k : ℕ} {x : Mx D m n} (hx : ε • x = x) (X : Mx D n k) :
    x ⬝ (ε • X) = x ⬝ X := by
  rw [Matrix.mul_smul, ← Matrix.smul_mul, hx]

theorem imXX {ε : AE D} {β : Fin ρ → AE D} {b : Mx D ρ ρ} :
    adj (d.jX ⬝ (b ⬝ Matrix.diagonal β + (1 - ε) • (1 : Mx D ρ ρ))) ⬝
      (gA S ⬝ (d.jX ⬝ (b ⬝ Matrix.diagonal β + (1 - ε) • (1 : Mx D ρ ρ)))) = 0 := by
  rw [adj_mul, Matrix.mul_assoc, gXX, Matrix.mul_zero]

set_option maxHeartbeats 1000000 in
theorem imYY {ε : AE D} (hεε : ε * ε = ε) (hεc : cA D ε = ε) {α : Fin ρ → AE D} (hαε : ∀ i, ε * α i = α i)
    {c' : Mx D S.rank ρ} (hc : ε • c' = c') (H2 : adj c' ⬝ (gA S ⬝ c') = 0) :
    adj (c' ⬝ Matrix.diagonal (fun i => cA D (α i)) + (1 - ε) • d.jY) ⬝
      (gA S ⬝ (c' ⬝ Matrix.diagonal (fun i => cA D (α i)) + (1 - ε) • d.jY)) = 0 := by
  have hcA1 : cA D (1 - ε) = 1 - ε := by rw [map_sub, map_one, hεc]
  have hadjc : ε • adj c' = adj c' := by
    conv_rhs => rw [← hc]
    rw [adj_smul, hεc]
  simp only [adj_add, adj_mul, adj_smul, adj_diagonal, cA_cA, hcA1, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  simp only [mul_tail₃ H2, Matrix.mul_zero, Matrix.smul_mul, Matrix.mul_smul, smul_smul, d.gram_YY, smul_zero,
    kill_mid₂ hεε hc, kill_left hεε (diag_absorb hαε), add_zero, Matrix.zero_mul]

set_option maxHeartbeats 1000000 in
theorem imOO {b : Mx D ρ ρ} {c' : Mx D S.rank ρ} :
    adj (d.j0 - (d.jX ⬝ b) ⬝ (adj c' ⬝ (gA S ⬝ d.j0))) ⬝ (gA S ⬝ (d.j0 - (d.jX ⬝ b) ⬝ (adj c' ⬝ (gA S ⬝ d.j0)))) = gA S₀ := by
  simp only [adj_sub, adj_mul, adj_gA, adj_adj, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, d.gram_00, d.wittDecomp_gram_X_anisotropic,
    gXX, g0X, Matrix.mul_zero, sub_zero]

set_option maxHeartbeats 1000000 in
theorem imOX {ε : AE D} {β : Fin ρ → AE D} {b : Mx D ρ ρ} {c' : Mx D S.rank ρ} :
    adj (d.j0 - (d.jX ⬝ b) ⬝ (adj c' ⬝ (gA S ⬝ d.j0))) ⬝ (gA S ⬝ (d.jX ⬝ (b ⬝ Matrix.diagonal β + (1 - ε) • (1 : Mx D ρ ρ)))) = 0 := by
  simp only [adj_sub, adj_mul, Matrix.sub_mul, Matrix.mul_assoc, gXX, g0X, Matrix.mul_zero, sub_zero]

set_option maxHeartbeats 1000000 in
theorem imOY {ε : AE D} (hεε : ε * ε = ε) (hεc : cA D ε = ε) {α : Fin ρ → AE D} {b : Mx D ρ ρ} (hb : ε • b = b)
    {c' : Mx D S.rank ρ} (hc : ε • c' = c')
    (H1 : adj c' ⬝ (gA S ⬝ (d.jX ⬝ b)) = ε • (1 : Mx D ρ ρ)) :
    adj (d.j0 - (d.jX ⬝ b) ⬝ (adj c' ⬝ (gA S ⬝ d.j0))) ⬝ (gA S ⬝ (c' ⬝ Matrix.diagonal (fun i => cA D (α i)) + (1 - ε) • d.jY)) = 0 := by
  have adjH1 : adj b ⬝ (adj d.jX ⬝ (gA S ⬝ c')) = ε • (1 : Mx D ρ ρ) := by
    have := congrArg adj H1
    simpa only [adj_mul, adj_gA, adj_adj, adj_smul, adj_one, hεc, Matrix.mul_assoc] using this
  simp only [adj_sub, adj_mul, adj_gA, adj_adj, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_assoc]
  rw [mul_tail₄ adjH1, Matrix.smul_mul, Matrix.one_mul, absorb_mul hc, sub_self, zero_add]
  simp only [Matrix.mul_smul, d.gram_0Y, d.gram_XY, Matrix.mul_one, smul_zero, kill_mid₂ hεε hc, sub_zero]

end GlobalTheory.IwaPlace.BuildQ

namespace GlobalTheory.IwaPlace.BuildQ

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

set_option maxHeartbeats 1000000 in

theorem smul_sub_one {ε : AE D} (M : Mx D S.rank S.rank)
    (hX : ε • (M ⬝ d.jX - d.jX) = M ⬝ d.jX - d.jX) (h0 : ε • (M ⬝ d.j0 - d.j0) = M ⬝ d.j0 - d.j0)
    (hY : ε • (M ⬝ d.jY - d.jY) = M ⬝ d.jY - d.jY) : ε • (M - 1) = M - 1 := by
  have e : M - 1 = (M ⬝ d.jX - d.jX) ⬝ d.pX + (M ⬝ d.j0 - d.j0) ⬝ d.p0 + (M ⬝ d.jY - d.jY) ⬝ d.pY := by
    have e1 : M - 1 = (M - 1) ⬝ (d.jX ⬝ d.pX + d.j0 ⬝ d.p0 + d.jY ⬝ d.pY) := by
      rw [d.sum_eq_one, Matrix.mul_one]
    rw [e1]
    simp only [Matrix.mul_add, ← Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul]
  rw [e, smul_add, smul_add, ← Matrix.smul_mul, ← Matrix.smul_mul, ← Matrix.smul_mul, hX, h0, hY]

theorem smul_shift {ε : AE D} (hεε : ε * ε = ε) {m n : ℕ} {x : Mx D m n} (hx : ε • x = x) (y : Mx D m n) :
    ε • (x + (1 - ε) • y - y) = x + (1 - ε) • y - y := by
  have e : x + (1 - ε) • y - y = x - ε • y := by
    rw [sub_smul, one_smul]; abel
  rw [e, smul_sub, hx, smul_smul, hεε]

theorem scalar_X {R : Type*} [CommRing R] {ε a b x y : R} (ha : ε * a = a) (hab : a * b = ε) (hx : ε * x = x) :
    a * (x * b + (1 - ε) * y) = x := by
  linear_combination x * hab + hx - y * ha

end GlobalTheory.IwaPlace.BuildQ

open GlobalTheory.IwaPlace.BuildQ in
set_option maxHeartbeats 1000000 in

theorem GlobalTheory.IwaPlace.exists_grpAt_of_dual_frames : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : Pl D) (ε : AE D) (hεε : ε * ε = ε) (hεc : cA D ε = ε) (hεI : ε ∈ intAt D (· = v)) (hε : ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) (α β : Fin ρ → AE D) (b : Mx D ρ ρ) (c' : Mx D S.rank ρ), (∀ i, α i ∈ idAt D (· = v)) → (∀ i, β i ∈ idAt D (· = v)) → (∀ i, α i * β i = ε) → (∀ i j, b i j ∈ idAt D (· = v)) → (∀ i j, c' i j ∈ idAt D (· = v)) → adj c' ⬝ (gA S ⬝ (d.jX ⬝ b)) = ε • (1 : Mx D ρ ρ) → adj c' ⬝ (gA S ⬝ c') = 0 → ∃ q ∈ grpAt S (· = v), mt S q ⬝ d.jX = d.jX ⬝ (b ⬝ Matrix.diagonal β + (1 - ε) • (1 : Mx D ρ ρ)) ∧ (∀ i, mt S q *ᵥ colMul d.jX i (α i) = fun k => (d.jX ⬝ b) k i) ∧ (∀ i, mt S q *ᵥ colMul d.jY i (cA D (β i)) = fun k => c' k i) := by
  intro D S S₀ ρ d v ε hεε hεc _ hε α β b c' hα hβ hαβ hb hc' H1 H2
  have hb' : ε • b = b := smul_eq_of_mem hε hb
  have hc : ε • c' = c' := smul_eq_of_mem hε hc'
  have hαε : ∀ i, ε * α i = α i := fun i => (hε _).1 (hα i)
  have hβε : ∀ i, ε * β i = β i := fun i => (hε _).1 (hβ i)
  have h : HypDec.Images S S₀ (d.jX ⬝ (b ⬝ Matrix.diagonal β + (1 - ε) • (1 : Mx D ρ ρ)))
      (d.j0 - (d.jX ⬝ b) ⬝ (adj c' ⬝ (gA S ⬝ d.j0)))
      (c' ⬝ Matrix.diagonal (fun i => cA D (α i)) + (1 - ε) • d.jY) :=
    ⟨imXX d, imYY d hεε hεc hαε hc H2, imYX d hεε hεc hαε hαβ hb' hc H1, imOO d, imOX d, imOY d hεε hεc hb' hc H1⟩
  have hjb : ε • (d.jX ⬝ b) = d.jX ⬝ b := by rw [← Matrix.mul_smul, hb']
  have hE : d.jX ⬝ (b ⬝ Matrix.diagonal β + (1 - ε) • (1 : Mx D ρ ρ))
      = (d.jX ⬝ b) ⬝ Matrix.diagonal β + (1 - ε) • d.jX := by
    rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_assoc]
  refine ⟨d.ofImages _ _ _ h, ?_, d.ofImages_jX h, fun i => ?_, fun i => ?_⟩
  · have key := smul_sub_one d (ε := ε) (Formalism.L2.Theta.mt S (d.ofImages _ _ _ h))
      (by rw [d.ofImages_jX h, hE]; exact smul_shift hεε (by rw [← Matrix.smul_mul, hjb]) _)
      (by rw [d.wittDecomp_ofImages_inclAnisotropic h, sub_sub_cancel_left, smul_neg, ← Matrix.smul_mul, hjb])
      (by rw [d.ofImages_jY h]; exact smul_shift hεε (by rw [← Matrix.smul_mul, hc]) _)
    refine (mem_congGrp_iff S _ _).2 fun i j => (hε _).2 ?_
    exact congrFun (congrFun key i) j
  · rw [mulVec_colMul, d.ofImages_jX h, hE]
    funext k
    rw [Matrix.add_apply, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul]
    exact scalar_X (hαε i) (hαβ i) (congrFun (congrFun hjb k) i)
  · rw [mulVec_colMul, d.ofImages_jY h]
    funext k
    rw [Matrix.add_apply, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul]
    refine scalar_X ?_ ?_ (congrFun (congrFun hc k) i)
    · rw [← hεc, ← map_mul, hβε]
    · rw [← map_mul, mul_comm, hαβ, hεc]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockPartitionRowsNumericDatumMemIcc
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2 GlobalTheory.CoreHt
open GlobalTheory.ColumnNormCompare (numDatumOfParameters codeRec plRec)
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.CoreHt.RowsRangeS

variable {D : D7}

variable {D : D7}

theorem one_le_scL (L : SizeData₂ D) : 1 ≤ L.sc.L :=
  Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le

theorem one_le_b (L : SizeData₂ D) : 1 ≤ L.sc.b :=
  Real.one_le_exp (by linarith [one_le_scL L])

theorem b'_pos (L : SizeData₂ D) : 0 < L.sc.b' := by
  have := L.sc.one_lt_alt
  have := one_le_b L
  unfold Scale.b' Scale.a Scale.X'
  positivity

theorem one_le_n (D : D7) : (1 : ℝ) ≤ D.R.n := by
  have : 1 ≤ D.R.n := by unfold Ranks.n; exact Nat.succ_le_of_lt (by positivity)
  exact_mod_cast this

theorem exists_top {τ : D.what₂.Tau} (h : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces) :
    ∃ t : D.host.TT, (D.eTau τ : D.R.GG) = D.R.tau1 t := by
  unfold Host.topPlaces at h
  obtain ⟨t, ht, hte⟩ := Finset.mem_image.1 h
  exact ⟨⟨t, ht⟩, hte.symm⟩

theorem uW_numRec (large₂ : SizeData₂ D) (hD : ∃ n : ℕ, D.s.Del = n) (u : D.what₂.Word) (z : RPl D.R) (i : Fin D.R.k) :
    (numDatumOfParameters D large₂).uW (codeRec large₂ u) z i = (D.hcW u (tauPl D z)).u i := by
  obtain ⟨n, hn⟩ := hD
  obtain ⟨r, hr⟩ := i
  unfold NumDatum.uW
  split_ifs with h h1
  · obtain ⟨l, rfl⟩ : ∃ l, r = l + 1 := ⟨r - 1, by have := h.1; simp only at this; omega⟩
    have h' : l < D.R.k - 2 := by have := h.2; simp only at this; omega
    have a := D.s.u_letter u (tauPl D z) l h'
    have h2 : D.s.letter u ⟨l, h'⟩ = true := h1
    rw [if_pos h2, D.hcW_v] at a
    have h3 : (((numDatumOfParameters D large₂).Del : ℕ) : ℚ) = D.s.Del := by
      show ((⌊D.s.Del⌋₊ : ℕ) : ℚ) = D.s.Del
      rw [hn, Nat.floor_natCast]
    rw [a, h3]
    rfl
  · obtain ⟨l, rfl⟩ : ∃ l, r = l + 1 := ⟨r - 1, by have := h.1; simp only at this; omega⟩
    have h' : l < D.R.k - 2 := by have := h.2; simp only at this; omega
    have a := D.s.u_letter u (tauPl D z) l h'
    have h2 : ¬ D.s.letter u ⟨l, h'⟩ = true := h1
    rw [if_neg h2, D.hcW_v] at a
    rw [a]
    rfl
  · by_cases h0 : r = 0
    · subst h0
      exact (D.hcW_first u _ hr).symm
    · obtain rfl : r = D.R.k - 1 := by simp only at h; omega
      exact (D.hcW_last u _ (by omega)).symm

theorem nu_numRec (large₂ : SizeData₂ D) (hD : ∃ n : ℕ, D.s.Del = n) (u : D.what₂.Word) (j : ℕ) (z : RPl D.R) (i : ℕ) :
    (((numDatumOfParameters D large₂).nu (codeRec large₂ u) j z i : ℚ) : ℝ) = DV.nuRow D u j (tauPl D z) i := by
  have e1 : (numDatumOfParameters D large₂).srcPar (codeRec large₂ u) z i = DV.srcPar D u (tauPl D z) i := by
    unfold NumDatum.srcPar DV.srcPar
    by_cases h : i < D.R.k
    · rw [dif_pos h, dif_pos h]
      exact uW_numRec large₂ hD u z ⟨i, h⟩
    · rw [dif_neg h, dif_neg h, D.hcW_e]
  have e2 : (((numDatumOfParameters D large₂).eQ j z : ℚ) : ℝ) = DV.wSz D j (tauPl D z) := by
    unfold NumDatum.eQ DV.wSz
    by_cases h : 1 ≤ j ∧ j ≤ D.R.m
    · rw [dif_pos h, dif_pos h]
    · rw [dif_neg h, dif_neg h, Rat.cast_zero]
  unfold NumDatum.nu DV.nuRow
  rw [e1, ← e2]
  push_cast
  rfl

theorem nuRow_zero_le_three_mul (large₂ : SizeData₂ D) (P : ParameterChoice' D large₂) (hb : ∀ t, (large₂.bT t : ℝ) ≤ 2 * large₂.sc.b')
    (hT : ThickUp large₂) (u : D.what₂.Word) (i : ℕ) (hi : i < D.R.m) (τ : D.what₂.Tau) :
    DV.nuRow D u (i + 1) τ 0 ≤ 3 * large₂.sc.a := by
  have hm := D.R.two_le_m
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hk0 : 0 < D.R.k := by omega
  have hk' : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hk
  have hm' : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm
  have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have hkN : (D.R.k : ℝ) ≤ D.R.N i := by
    have : D.R.k ≤ D.R.N i := by unfold Ranks.N; omega
    exact_mod_cast this
  have hx := large₂.sc.one_lt_alt
  have hb1 := one_le_b large₂
  have hb' := b'_pos large₂
  have hba : large₂.sc.b ≤ large₂.sc.a := le_mul_of_one_le_left (by linarith) hx.le
  have hX : 2 ≤ large₂.sc.X' := by
    have h1 : 1 ≤ large₂.sc.x ^ (large₂.sc.eps / 3) := Real.one_le_rpow hx.le (by linarith [large₂.sc.eps_pos])
    have h2 := Real.add_one_le_exp (large₂.sc.x ^ (large₂.sc.eps / 3))
    unfold Scale.X'
    linarith
  have hb'a : large₂.sc.b' ≤ large₂.sc.a / 2 := div_le_div_of_nonneg_left (by linarith) (by norm_num) hX
  have hw : large₂.sc.w'' D.R.n ≤ large₂.sc.b' :=
    div_le_self hb'.le (one_le_mul_of_one_le_of_one_le hx.le (one_le_n D))
  have he := large₂.etaSz_pos
  have hS := large₂.Sc_pos
  have heta : 2 * large₂.etaSz ≤ large₂.sc.b' := by
    have h1 : (2 : ℝ) ≤ D.R.m * ((D.R.t : ℝ) + 1) := by nlinarith
    linarith [P.mteta, mul_le_mul_of_nonneg_right h1 he.le]
  have hSc : 5 * large₂.Sc ≤ large₂.sc.b' := by
    linarith [P.kS_le, mul_le_mul_of_nonneg_right hk' hS.le]
  have hwj : wj D (i + 1) τ = (((D.hc τ).e ⟨i, hi⟩ : ℚ) : ℝ) := by
    unfold wj
    rw [dif_pos (by simpa using hi)]
    rfl
  rw [RowWeightLemmas.nuRow_head D u i hi τ 0 hk0, D.hcW_first u τ hk0, D.hcW_e]
  push_cast
  rw [← hwj]
  by_cases ha : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
  · obtain ⟨t, htt⟩ := exists_top ha
    rw [(large₂.top_u τ t hk0 htt).1]
    have a1 := (large₂.win_top (i + 1) (by omega) hi τ t htt).2
    have a2 := (large₂.aT_win t).2
    have a3 : (5 : ℝ) ≤ (D.R.k : ℝ) * large₂.sc.x ^ (Scale.A / 2) :=
      hk'.trans (le_mul_of_one_le_right (by linarith) (Real.one_le_rpow hx.le (by unfold Scale.A; norm_num)))
    have a4 : large₂.sc.a / ((D.R.k : ℝ) * large₂.sc.x ^ (Scale.A / 2)) ≤ large₂.sc.a / 5 :=
      div_le_div_of_nonneg_left (by linarith) (by norm_num) a3
    have a5 : large₂.sc.b' / large₂.sc.x ≤ large₂.sc.b' := div_le_self hb'.le hx.le
    linarith [hb t]
  · have h1 := P.cloud_place_bound τ (by omega) ha
    have h2 := (large₂.cloud_v τ ⟨0, by omega⟩).2
    push_cast at h1
    by_cases hc : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
    · have a1 := hT (i + 1) (by omega) hi τ hc
      linarith
    · have a1 := (large₂.win_thin (i + 1) (by omega) hi τ ⟨(D.eTau τ).2, ha, hc⟩).2
      linarith

theorem nu_numRec_mem : ∀ (D : D7) (L : SizeData₂ D) (CY : ℝ), HtRowsS L CY → ∀ (u : D.what₂.Word), ∀ j ∈ (numDatumOfParameters D L).lifts, ∀ z,
    ∀ i < D.R.N (j - 1), 0 ≤ (numDatumOfParameters D L).nu (codeRec L u) j z i ∧
      (((numDatumOfParameters D L).nu (codeRec L u) j z i : ℚ) : ℝ) ≤ 3 * L.sc.a := by
  rintro D large₂ CY ⟨⟨P⟩, -, -, hN, hD, hT⟩ u j hj z r hr
  obtain ⟨j1, j2⟩ := Finset.mem_Icc.1 hj
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hi : i < D.R.m := j2
  have hr' : r < D.R.N i := hr
  have e := nu_numRec large₂ hD u (i + 1) z r
  constructor
  · have h := (RowWeightLemmas.nuRow_pos D u i hi (tauPl D z) r hr').le
    rw [← e] at h
    exact_mod_cast h
  · rw [e]
    exact (RowWeightLemmas.nuRow_anti' D u i hi _ r 0 (Nat.zero_le _) hr').trans
      (nuRow_zero_le_three_mul large₂ P hN.2.2.2.2 hT u i hi _)

end GlobalTheory.CoreHt.RowsRangeS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiInvariantFunctionIntegrable
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

open scoped Pointwise

namespace GlobalTheory.Unf

theorem vol_fund_lt_top {D : D7} {V : HSp D} (hc : CoCpt V) (v : Vol V) : v.μ v.𝓕 < ⊤ := by
  obtain ⟨_, _, _, _, _, _, hΓc⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := v.haar
  obtain ⟨K, hKc, hKcov⟩ := hc
  have hcover : v.𝓕 ⊆ ⋃ g : GQ V, (g • K) := by
    intro h _
    obtain ⟨γ, hγ, hk⟩ := hKcov h
    refine Set.mem_iUnion.2 ⟨⟨γ, hγ⟩⁻¹, ?_⟩
    refine Set.mem_smul_set.2 ⟨γ * h, hk, ?_⟩
    simp [Subgroup.smul_def]
  have hle : v.μ v.𝓕 ≤ v.μ K := by
    calc v.μ v.𝓕 = v.μ ((⋃ g : GQ V, (g • K)) ∩ v.𝓕) := by rw [Set.inter_eq_right.2 hcover]
      _ = v.μ (⋃ g : GQ V, (g • K ∩ v.𝓕)) := by rw [Set.iUnion_inter]
      _ ≤ ∑' g : GQ V, v.μ (g • K ∩ v.𝓕) := measure_iUnion_le _
      _ = v.μ K := (v.fund.measure_eq_tsum K).symm
  exact hle.trans_lt hKc.measure_lt_top

theorem jac_bound (D : D7) (ρ : ℕ) (J : JacLev D ρ) (K : GA D J.W → ℂ) (hK : Continuous K)
    (hinv : ∀ γ ∈ GQ J.W ⊓ jacGrp J.d, ∀ h, K (γ * h) = K h) (h : GA D J.W) :
    ∃ C, ∀ (n : flagN J.d) (h' : GA D J.W₀), ‖K (n.1 * J.d.emb0 h' * h)‖ ≤ C := by
  have hcont := J.d.continuous_embed
  obtain ⟨-, -, -, -, hnorm, -, -⟩ := GlobalTheory.MixPer.flag_jacobi_structure D J.W J.W₀ ρ J.d
  obtain ⟨⟨Kn, hKn, hcov⟩, -⟩ := GlobalTheory.Mem.UnipCocompact.radicals_cocompact D J.W ρ J.d.e (isIsoSub_e J.d)
  obtain ⟨K₀, hK₀, hcov₀⟩ := J.cpt
  obtain ⟨-, -, -, -, htop, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D J.W
  let f : flagN J.d × GA D J.W₀ → GA D J.W := fun p => p.1.1 * J.d.emb0 p.2 * h
  have hf : Continuous f :=
    ((continuous_subtype_val.comp continuous_fst).mul (hcont.comp continuous_snd)).mul continuous_const
  have hS : IsCompact (f '' (Kn ×ˢ K₀)) := (hKn.prod hK₀).image hf
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hK.continuousOn
  refine ⟨C, fun n h' => ?_⟩
  obtain ⟨γ₀, hγ₀, hk₀⟩ := hcov₀ h'
  have hemb : J.d.emb0 γ₀ ∈ GQ J.W := J.d.wittDecomp_anisotropicEmbedding_mem_rationalPoints hγ₀
  let n' : flagN J.d := ⟨J.d.emb0 γ₀ * n.1 * (J.d.emb0 γ₀)⁻¹, hnorm n.1 n.2 γ₀⟩
  obtain ⟨γ, hγ, k, hk, hn'⟩ := hcov n'
  have hδ : (J.d.emb0 γ₀)⁻¹ * γ.1 ∈ GQ J.W ⊓ jacGrp J.d :=
    Subgroup.mem_inf.2 ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hemb) (Subgroup.mem_subgroupOf.1 hγ),
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_right (MonoidHom.mem_range.2 ⟨γ₀, rfl⟩)))
        (Subgroup.mem_sup_left γ.2)⟩
  have h1 : γ.1 * k.1 = J.d.emb0 γ₀ * n.1 * (J.d.emb0 γ₀)⁻¹ := (congrArg Subtype.val hn').symm
  have heq : n.1 * J.d.emb0 h' * h = ((J.d.emb0 γ₀)⁻¹ * γ.1) * (k.1 * J.d.emb0 (γ₀ * h') * h) := by
    rw [map_mul, show ((J.d.emb0 γ₀)⁻¹ * γ.1) * (k.1 * (J.d.emb0 γ₀ * J.d.emb0 h') * h) =
      (J.d.emb0 γ₀)⁻¹ * (γ.1 * k.1) * J.d.emb0 γ₀ * J.d.emb0 h' * h by simp only [mul_assoc], h1]
    simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
  rw [heq, hinv _ hδ]
  exact hC _ ⟨(k, γ₀ * h'), ⟨hk, hk₀⟩, rfl⟩

theorem jac_absConv : ∀ (D : D7) (ρ : ℕ) (J : JacLev D ρ) (K : GA D J.W → ℂ), Continuous K →
    (∀ γ ∈ GQ J.W ⊓ jacGrp J.d, ∀ h, K (γ * h) = K h) → ∀ h,
      AbsConv J.v0.μ J.v0.𝓕 J.vN.ν J.vN.𝓝 fun h' n => K (n.1 * J.d.emb0 h' * h) := by
  intro D ρ J K hK hinv h
  obtain ⟨C, hC⟩ := jac_bound D ρ J K hK hinv h
  have hcont := J.d.continuous_embed
  obtain ⟨-, h2W, -, hbW, htW, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D J.W
  obtain ⟨-, h20, -, hb0, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D J.W₀
  have hμ : J.v0.μ J.v0.𝓕 < ⊤ := vol_fund_lt_top J.cpt J.v0
  have hν : J.vN.ν J.vN.𝓝 < ⊤ := by rw [J.vN.unit.2.2]; exact ENNReal.one_lt_top
  haveI : IsFiniteMeasure (J.v0.μ.restrict J.v0.𝓕) := isFiniteMeasure_restrict.2 hμ.ne
  haveI : IsFiniteMeasure (J.vN.ν.restrict J.vN.𝓝) := isFiniteMeasure_restrict.2 hν.ne
  unfold AbsConv
  refine Integrable.of_bound ?_ C (Filter.Eventually.of_forall fun p => hC p.2 p.1)
  exact (hK.comp (((continuous_subtype_val.comp continuous_snd).mul (hcont.comp continuous_fst)).mul
    continuous_const)).aestronglyMeasurable

end GlobalTheory.Unf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiKernelEqWeilRepresentationApplyStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierJacobiKernel_eq_weilRepresentation_apply : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (W W₀ V₀ A L : HSp D) (ρ : ℕ) (dW : HypDec W W₀ ρ) (o : OrthDec V₀ A L) (ζ : Fin L.rank → D.host.E) (χ χ' : ((AE D)ˣ →* Circle)) (om : Om V₀ W₀), IsWeilDatumO ψ V₀ W₀ χ χ' om → ∀ Ξ, IsThetaFunO ψ V₀ W₀ Ξ → ∀ h₀ n h, fjKer ψ dW o ζ om Ξ h₀ n h = ψ (cenT dW L (yZero L ρ ζ) n) * om (o.emb (h₀, 1), h) Ξ ((o.resS W₀).symm (0, ptT dW L (yZero L ρ ζ) n)) := by
  first | exact @GlobalTheory.Unf.fjKer_eq_om_apply | exact GlobalTheory.Unf.fjKer_eq_om_apply | (intros; apply GlobalTheory.Unf.fjKer_eq_om_apply <;> assumption)
end

