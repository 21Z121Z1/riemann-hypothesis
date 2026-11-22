import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0224
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateCharacterCellFactorization
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0039
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0043
import GroundTheory.GlobalFields.CompletionAtPlace
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0007
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0013
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0037
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0040
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0012
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0035
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0026

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.CompAtMulOfOne
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 100000

namespace PositivityTheory.Rg.Sw.Glob.AW

variable {D : D7} {n : ℕ}

def AG (θ : InfFam D) (τ : D.what₂.Tau) (x : G D n) : Prop :=
  IsTrivAt θ τ x ∧ ((∃ b, mat x = blk4 1 b 0 1) ∨ (∃ a d, mat x = blk4 a 0 0 d) ∨ (∃ c, mat x = blk4 1 0 c 1))

def AgreeAway {m k : ℕ} (θ : InfFam D) (τ : D.what₂.Tau) (x x' : Mx D m k) : Prop :=
  (∀ τ', τ' ≠ τ → compAt θ τ' x = compAt θ τ' x') ∧ x.map (finPart D) = x'.map (finPart D)

theorem mem_closure_AG (hG : GenA) (hDA : DecompAway) {θ : InfFam D} {τ : D.what₂.Tau} {ι : GR n →* G D n}
    (hθ : IsInfFam θ) (hι : IsPlaceEmb θ τ ι) (x : G D n) (hx : IsTrivAt θ τ x) :
    x ∈ Submonoid.closure {x : G D n | AG θ τ x} :=
  closure_triv hG hDA hθ hι x hx

theorem exists_w (D : D7) (n : ℕ) : ∃ w : G D n, mat w = blk4 0 1 (-1) 0 := by
  obtain ⟨g, hg⟩ := GlobalTheory.SiegelCells.exists_wPart (D := D) (n := n) n
  refine ⟨g, hg.trans ?_⟩
  have hL : GlobalTheory.SiegelCells.lastDiag (AE D) n n = 1 := by
    unfold GlobalTheory.SiegelCells.lastDiag
    rw [← Matrix.diagonal_one]
    congr 1; funext i; simp
  rw [GlobalTheory.SiegelCells.wMat, hL, sub_self]

theorem compAt_b_zero {θ : InfFam D} {τ : D.what₂.Tau} {x : G D n} {b : Mx D n n} (hx : IsTrivAt θ τ x)
    (h : mat x = blk4 1 b 0 1) : compAt θ τ b = 0 := by
  have h1 : compAt θ τ (mat x) = blk4 1 (compAt θ τ b) 0 1 := by rw [h, component_block_matrix, compAt_one', compAt_zero']
  have h2 : (blk4 1 0 0 1 : Matrix (Fin (n + n)) (Fin (n + n)) ℂ) = blk4 1 (compAt θ τ b) 0 1 := by
    rw [GlobalTheory.StdUnn.Model.block_matrix_one, ← h1]; exact hx.symm
  exact (GlobalTheory.StdUnn.Model.blockMatrixTwoByTwoFin_injective h2).2.1.symm

theorem compAt_a_one {θ : InfFam D} {τ : D.what₂.Tau} {x : G D n} {a d : Mx D n n} (hx : IsTrivAt θ τ x)
    (h : mat x = blk4 a 0 0 d) : compAt θ τ a = 1 := by
  have h1 : compAt θ τ (mat x) = blk4 (compAt θ τ a) 0 0 (compAt θ τ d) := by rw [h, component_block_matrix, compAt_zero']
  have h2 : (blk4 1 0 0 1 : Matrix (Fin (n + n)) (Fin (n + n)) ℂ) = blk4 (compAt θ τ a) 0 0 (compAt θ τ d) := by
    rw [GlobalTheory.StdUnn.Model.block_matrix_one, ← h1]; exact hx.symm
  exact (GlobalTheory.StdUnn.Model.blockMatrixTwoByTwoFin_injective h2).1.symm

theorem compAt_mul_of_one {θ : InfFam D} {τ : D.what₂.Tau} {m k : ℕ} (x : Mx D m k) (a : Mx D k k)
    (ha : compAt θ τ a = 1) : compAt θ τ (x ⬝ a : Mx D m k) = compAt θ τ x := by
  rw [compAt_mul', ha, Matrix.mul_one]

theorem agree_mul_right {θ : InfFam D} {τ : D.what₂.Tau} {m k : ℕ} {x x' : Mx D m k} (a : Mx D k k)
    (h : AgreeAway θ τ x x') : AgreeAway θ τ (x ⬝ a : Mx D m k) (x' ⬝ a : Mx D m k) := by
  refine ⟨fun τ' hτ' => ?_, ?_⟩
  · rw [compAt_mul', compAt_mul', h.1 τ' hτ']
  · rw [Matrix.map_mul, Matrix.map_mul, h.2]

theorem unipArg_away {θ : InfFam D} {τ : D.what₂.Tau} (hθ : IsInfFam θ) (V : HSp D) {b : Mx D n n}
    (hb : compAt θ τ b = 0) {x x' : Mx D V.rank n} (h : AgreeAway θ τ x x') :
    halfTr (Matrix.trace (b ⬝ inner V x x : Mx D n n)) = halfTr (Matrix.trace (b ⬝ inner V x' x' : Mx D n n)) := by
  have htr : ∀ (R : Type) [CommRing R] (f : AE D →+* R) (M : Mx D n n), f (Matrix.trace M) = Matrix.trace (M.map f) := by
    intro R _ f M
    simp only [Matrix.trace, Matrix.diag, Matrix.map_apply]
    exact map_sum f _ _
  have hinner : ∀ τ'', τ'' ≠ τ → compAt θ τ'' (inner V x x) = compAt θ τ'' (inner V x' x') := by
    intro τ'' hτ''
    have hx := h.1 τ'' hτ''
    have hadj : compAt θ τ'' (adj x) = compAt θ τ'' (adj x') := by
      ext i j
      have := congrFun (congrFun hx j) i
      simp only [compAt_eq, Matrix.map_apply] at this ⊢
      simp only [adj, Matrix.transpose_apply, Matrix.map_apply]
      rw [cθ_cA hθ, cθ_cA hθ, this]
    simp only [GlobalTheory.StdUnn.inner]
    rw [compAt_mul', compAt_mul', compAt_mul', compAt_mul', hadj, hx]
  have hfin : (inner V x x).map (finPart D) = (inner V x' x').map (finPart D) := by
    have hadj : (adj x).map (finPart D) = (adj x').map (finPart D) := by
      ext i j
      have := congrFun (congrFun h.2 j) i
      simp only [Matrix.map_apply] at this ⊢
      simp only [adj, Matrix.transpose_apply, Matrix.map_apply]
      rw [finPart_cA, finPart_cA, this]
    simp only [GlobalTheory.StdUnn.inner]
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, hadj, h.2]
  congr 1
  apply ae_ext hθ
  · intro τ''
    rw [htr, htr, ← compAt_eq, ← compAt_eq, compAt_mul', compAt_mul']
    by_cases hτ : τ'' = τ
    · subst hτ; rw [hb, Matrix.zero_mul, Matrix.zero_mul]
    · rw [hinner τ'' hτ]
  · rw [htr, htr, Matrix.map_mul, Matrix.map_mul, hfin]

theorem exists_change_tau {θ : InfFam D} {τ : D.what₂.Tau} (hθ : IsInfFam θ) {m k : ℕ} (xs x0 : Mx D m k) :
    ∃ x1 : Mx D m k, compAt θ τ x1 = compAt θ τ x0 ∧ AgreeAway θ τ x1 xs := by
  obtain ⟨-, hfin, hcomp⟩ := GlobalTheory.WeilVacMove.isLineAt_lineAt (D := D) hθ τ (compAt θ τ x0 - compAt θ τ xs)
  refine ⟨xs + lineAt θ τ (compAt θ τ x0 - compAt θ τ xs) 1, ?_, fun τ' hτ' => ?_, ?_⟩
  · rw [compAt_add', hcomp 1 τ, if_pos rfl]; simp
  · rw [compAt_add', hcomp 1 τ', if_neg hτ', add_zero]
  · rw [Matrix.map_add _ (map_add (finPart D)), hfin 1, add_zero]

theorem levi_blocks (g : G D n) {a d : Mx D n n} (h : mat g = blk4 a 0 0 d) :
    ∃ a' : GL (Fin n) (AE D), a'.1 = a ∧ d = adj (a'⁻¹).1 := by
  obtain ⟨-, h2, -, -⟩ := GlobalTheory.CompanionTheory.SwUnf.SmallCell.unitary_rel g h
  simp only [adj_zero, Matrix.zero_mul, neg_zero, zero_add] at h2
  have h3 : adj d * a = 1 := by
    have := congrArg adj h2
    rwa [adj_mul, adj_adj, adj_one] at this
  have h4 : a * adj d = 1 := mul_eq_one_comm.mp h3
  refine ⟨⟨a, adj d, h4, h3⟩, rfl, ?_⟩
  show d = adj (adj d)
  rw [adj_adj]

theorem mat_w_conj {w x : G D n} (hw : mat w = blk4 0 1 (-1) 0) {c : Mx D n n} (hx : mat x = blk4 1 0 c 1) :
    mat (w⁻¹ * x * w) = blk4 1 (-c) 0 1 := by
  rw [GlobalTheory.StdUnn.LeftInvSect.mat_mul, GlobalTheory.StdUnn.LeftInvSect.mat_mul, GlobalTheory.CompanionTheory.SwUnf.SmallCell.mat_inv w hw, hx, hw]
  simp [adj_zero, adj_one, adj_neg, GlobalTheory.StdUnn.Model.submatrix_fromBlocks_mul]

theorem trivAt_conj {θ : InfFam D} {τ : D.what₂.Tau} {x : G D n} (w : G D n) (hx : IsTrivAt θ τ x) :
    IsTrivAt θ τ (w⁻¹ * x * w) := by
  unfold IsTrivAt at *
  have hw : compAt θ τ (mat w⁻¹) * compAt θ τ (mat w) = 1 := by
    rw [← compAt_mul', ← GlobalTheory.StdUnn.LeftInvSect.mat_mul, inv_mul_cancel, GlobalTheory.StdUnn.LeftInvSect.mat_one, compAt_one']
  rw [GlobalTheory.StdUnn.LeftInvSect.mat_mul, GlobalTheory.StdUnn.LeftInvSect.mat_mul, compAt_mul', compAt_mul', hx, Matrix.mul_one, hw]

theorem exists_compAt {θ : InfFam D} {τ : D.what₂.Tau} (hθ : IsInfFam θ) {m k : ℕ} (M : Matrix (Fin m) (Fin k) ℂ) :
    ∃ x : Mx D m k, compAt θ τ x = M := by
  obtain ⟨-, -, hcomp⟩ := GlobalTheory.WeilVacMove.isLineAt_lineAt (D := D) hθ τ M
  exact ⟨lineAt θ τ M 1, by rw [hcomp 1 τ, if_pos rfl]; simp⟩

theorem exists_sch_ne {m k : ℕ} (u0 : Fin m → Fin k → ℂ) : ∃ f : (Fin m → Fin k → ℂ) → ℂ, IsSch f ∧ f u0 ≠ 0 := by
  let b : ContDiffBump u0 := ⟨1, 2, one_pos, one_lt_two⟩
  refine ⟨fun u => ((b u : ℝ) : ℂ), ?_, ?_⟩
  · have hc : HasCompactSupport (fun u => ((b u : ℝ) : ℂ)) := b.hasCompactSupport.comp_left Complex.ofReal_zero
    have hs : ContDiff ℝ (⊤ : ℕ∞) (fun u => ((b u : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp b.contDiff
    exact ⟨hc.toSchwartzMap hs, rfl⟩
  · have : b u0 = 1 := b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)
    simp [this]

end PositivityTheory.Rg.Sw.Glob.AW
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DerivationOfQuadraticForm
section
noncomputable section

open Filter Topology MvPolynomial

namespace PositivityTheory.Rg.Sw.Glob.SchDH

variable {m n : ℕ}

def Dv (X : Matrix (Fin m) (Fin m) ℂ) : Derivation ℂ (PX m n) (PX m n) :=
  MvPolynomial.mkDerivation ℂ (fun k : Fin m × Fin n × Bool => xyP X k.1 k.2.1 k.2.2)

theorem Dv_X (X : Matrix (Fin m) (Fin m) ℂ) (k : Fin m × Fin n × Bool) :
    Dv X (MvPolynomial.X k : PX m n) = xyP X k.1 k.2.1 k.2.2 :=
  MvPolynomial.mkDerivation_X _ _ _

theorem Dv_eq (X : Matrix (Fin m) (Fin m) ℂ) (P : PX m n) :
    Dv X P = ∑ k : Fin m × Fin n × Bool, xyP X k.1 k.2.1 k.2.2 * pderiv k P := by
  let D₂ : Derivation ℂ (PX m n) (PX m n) :=
    ∑ k : Fin m × Fin n × Bool, xyP X k.1 k.2.1 k.2.2 • pderiv k
  have hs : ∀ Q : PX m n, D₂ Q = ∑ k : Fin m × Fin n × Bool, xyP X k.1 k.2.1 k.2.2 * pderiv k Q := by
    intro Q
    show (Derivation.coeFnAddMonoidHom (R := ℂ) (A := PX m n) (M := PX m n)
      (∑ k : Fin m × Fin n × Bool, xyP X k.1 k.2.1 k.2.2 • (pderiv k : Derivation ℂ (PX m n) (PX m n)))) Q = _
    rw [map_sum, Finset.sum_apply]
    simp only [Derivation.coeFnAddMonoidHom_apply, Derivation.smul_apply, smul_eq_mul]
  have h : Dv X P = D₂ P := by
    refine MvPolynomial.derivation_eq_of_forall_mem_vars (fun i _ => ?_)
    rw [hs, Dv_X]
    simp [pderiv_X, Pi.single_apply]
  rw [h, hs]

def Q2 (m n : ℕ) : PX m n := ∑ a, ∑ i, MvPolynomial.X (a, i, false) * MvPolynomial.X (a, i, true)

theorem derivation_quadraticForm_eq_sum (X : Matrix (Fin m) (Fin m) ℂ) :
    Dv X (Q2 m n) = ∑ a, ∑ i, (MvPolynomial.X (a, i, false) * xyP X a i true + MvPolynomial.X (a, i, true) * xyP X a i false) := by
  simp only [Q2, map_sum, Derivation.leibniz, Dv_X, smul_eq_mul]

theorem vfX_eq_Dv (c : ℝ) (X : Matrix (Fin m) (Fin m) ℂ) (P : PX m n) :
    vfX c X P = Dv X P - C (c : ℂ) * Dv X (Q2 m n) * P := by
  rw [Dv_eq, derivation_quadraticForm_eq_sum, vfX]
  simp only [Fintype.sum_prod_type]
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Fintype.sum_bool]
  ring

theorem eval_xyP (X : Matrix (Fin m) (Fin m) ℂ) (u : Fin m → Fin n → ℂ) (a : Fin m) (i : Fin n) (b : Bool) :
    MvPolynomial.eval (fun k => GlobalTheory.CompanionTheory.PolyGaussSchwartz.coord k u) (xyP X a i b) =
      if b then star (matL X u a i) else matL X u a i := by
  cases b <;> simp [xyP, GlobalTheory.CompanionTheory.PolyGaussSchwartz.coord, matL_apply, star_sum, star_mul']

theorem gs_eq (c : ℝ) (u : Fin m → Fin n → ℂ) :
    gs c u = Complex.exp (-(c : ℂ) * MvPolynomial.eval (fun k => GlobalTheory.CompanionTheory.PolyGaussSchwartz.coord k u) (Q2 m n)) := by
  rw [gs]
  congr 1
  simp only [Q2, map_sum, map_mul, MvPolynomial.eval_X, GlobalTheory.CompanionTheory.PolyGaussSchwartz.coord]
  push_cast
  simp [Complex.mul_conj, Complex.normSq_eq_norm_sq, Finset.mul_sum]

private theorem hasDerivAt_clm_comp_of_tendsto_slope {σ : Type*} [Fintype σ] (g : ℝ → σ → ℂ) (g' : σ → ℂ)
    (hg : ∀ k, HasDerivAt (fun t => g t k) (g' k) 0) (Q : MvPolynomial σ ℂ) :
    HasDerivAt (fun t => MvPolynomial.eval (g t) Q)
      (∑ k, g' k * MvPolynomial.eval (g 0) (pderiv k Q)) 0 := by
  classical
  refine MvPolynomial.induction_on
    (motive := fun Q => HasDerivAt (fun t => MvPolynomial.eval (g t) Q)
      (∑ k, g' k * MvPolynomial.eval (g 0) (pderiv k Q)) 0) Q ?_ ?_ ?_
  · intro a
    simpa using hasDerivAt_const (0 : ℝ) a
  · intro p q hp hq
    refine ((hp.fun_add hq).congr_deriv ?_).congr_of_eventuallyEq ?_
    · simp [mul_add, Finset.sum_add_distrib]
    · exact Filter.Eventually.of_forall (fun t => by simp)
  · intro p k hp
    refine ((hp.fun_mul (hg k)).congr_deriv ?_).congr_of_eventuallyEq ?_
    · simp [Derivation.leibniz, pderiv_X, Pi.single_apply, mul_add, Finset.sum_add_distrib,
        apply_ite, Finset.sum_ite_eq]
      rw [add_comm]
      congr 1
      · ring
      · rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun _ _ => by ring)
    · exact Filter.Eventually.of_forall (fun t => by simp)

theorem hasDerivAt_curve (c : ℝ) (X : Matrix (Fin m) (Fin m) ℂ) (P : PX m n) (x : Fin m → Fin n → ℂ) :
    HasDerivAt (fun t : ℝ => fP c P (matL (NormedSpace.exp ((t : ℂ) • X)) x)) (fP c (vfX c X P) x) 0 := by
  set u : ℝ → (Fin m → Fin n → ℂ) := fun t => matL (NormedSpace.exp ((t : ℂ) • X)) x with hu
  have hu0 : u 0 = x := by simp [hu, matL_one]
  clear_value u
  rw [show (fun t : ℝ => fP c P (matL (NormedSpace.exp ((t : ℂ) • X)) x)) =
    fun t => fP c P (u t) by rw [hu]]
  let e : (Fin m → Fin n → ℂ) → Fin m × Fin n × Bool → ℂ :=
    fun v k => GlobalTheory.CompanionTheory.PolyGaussSchwartz.coord k v
  have hg : ∀ k, HasDerivAt (fun t => e (u t) k) (MvPolynomial.eval (e x) (xyP X k.1 k.2.1 k.2.2)) 0 := by
    rintro ⟨a, i, b⟩
    have hlin : HasDerivAt (fun t => u t a i) (matL X x a i) 0 := by
      have hs := HasDerivAt.fun_sum (u := Finset.univ)
        (fun c (_ : c ∈ Finset.univ) => (hasDerivAt_entry X a c).mul_const (x c i))
      simpa only [hu, matL_apply] using hs
    rw [eval_xyP]
    cases b
    · simpa [e, GlobalTheory.CompanionTheory.PolyGaussSchwartz.coord] using hlin
    · simpa [e, GlobalTheory.CompanionTheory.PolyGaussSchwartz.coord] using hlin.star
  have hf : (fun t : ℝ => fP c P (u t)) = fun t => MvPolynomial.eval (e (u t)) P *
      Complex.exp (-(c : ℂ) * MvPolynomial.eval (e (u t)) (Q2 m n)) := by
    funext t
    rw [fP, gs_eq]
    rfl
  have hx : fP c (vfX c X P) x = MvPolynomial.eval (e x) (vfX c X P) *
      Complex.exp (-(c : ℂ) * MvPolynomial.eval (e x) (Q2 m n)) := by
    rw [fP, gs_eq]
    rfl
  rw [hf, hx, vfX_eq_Dv, Dv_eq X P, Dv_eq X (Q2 m n)]
  have hP := hasDerivAt_clm_comp_of_tendsto_slope (fun t => e (u t)) _ hg P
  have hQ := hasDerivAt_clm_comp_of_tendsto_slope (fun t => e (u t)) _ hg (Q2 m n)
  have H := hP.fun_mul ((hQ.const_mul (-(c : ℂ))).cexp)
  rw [hu0] at H
  refine H.congr_deriv ?_
  simp only [map_sub, map_mul, map_sum, MvPolynomial.eval_C]
  ring

end PositivityTheory.Rg.Sw.Glob.SchDH
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.InvEqWww
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open Formalism.IndefR.Eqv (psiT eq_thetaC)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.FTH

open PositivityTheory.Rg.Sw.Glob.FTP PositivityTheory.Rg.Sw.Glob.PlaceFactsH
open Classical

variable {D : D7} {n m : ℕ}

theorem Aw_away {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau}
    {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hdet : IsUnit fr.det) (ψ : AddChar (AF D.host.F) ℂ)
    (μ : Measure (Mx D V.rank n)) (Ψ : Mx D V.rank n → ℂ) (x x' : Mx D V.rank n)
    (hx : ∀ τ', τ' ≠ τ → compAt θ τ' x = compAt θ τ' x') (hf : x.map (finPart D) = x'.map (finPart D)) :
    Aw ψ V θ τ fr μ Ψ x = Aw ψ V θ τ fr μ Ψ x' := by
  have e : Bw ψ V θ τ fr Ψ x = Bw ψ V θ τ fr Ψ x' := by
    funext y
    unfold Bw
    rw [inner_away hθ x x' _ hx hf (compAt_sub_sIns hθ hdet y)]
  unfold Aw
  rw [e]

set_option maxHeartbeats 800000 in
theorem mat_ww (w : G D n) (hw : mat w = blk4 0 1 (-1) 0) : mat (w * w) = blk4 (-1) 0 0 (-1) := by
  rw [mat_mul', hw, submatrix_fromBlocks_mul]
  simp

set_option maxHeartbeats 800000 in
theorem inv_eq_www (w : G D n) (hw : mat w = blk4 0 1 (-1) 0) : w⁻¹ = w * w * w := by
  apply mat_inj
  rw [GlobalTheory.CompanionTheory.EisCovar.Weyl.mat_inv_eq w hw, mat_mul', mat_ww w hw, hw, submatrix_fromBlocks_mul]
  simp

end PositivityTheory.Rg.Sw.Glob.FTH
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocInstTop
section
namespace PositivityTheory.Rg.Sw.Glob

theorem locInst_of_cell_kvac (hc : LIcell) (hk : LIkvac) (hT : TensMem) : LocInst :=
  locInst_of hT lIl lIlin lIlaw hc lIcont lIrho lIkact lIvac hk

theorem locInst_of_cell (hc : LIcell) (hT : TensMem) : LocInst := locInst_of_cell_kvac hc lIkvac hT

theorem locInst_of_away (hA : AwayAct) (hT : TensMem) : LocInst :=
  locInst_of_cell (lIcell_of' hA lIcont lIlaw lIvac) hT

end PositivityTheory.Rg.Sw.Glob
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.WeightFactorEqAutomorphy
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.GaussH

variable {n : ℕ}

theorem weight_factor_eq_automorphy (p q : ℕ) (e : ℤ) (y : GR n) : F0 p q e y = jF e p q y (Complex.I • 1) := by
  simp only [F0, f0, jF, u1, u2, conj_I_smul_one, Matrix.mul_neg, mul_I_smul_one]
  push_cast
  ring

end PositivityTheory.Rg.Sw.Glob.GaussH

namespace PositivityTheory.Rg.Sw.Glob

open GaussH

theorem lawM_of : TensInj → LawM := by
  intro hTI D n V ψ χ θ μ ω H l s ν τ ε fr ι hC L hL
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hC.hθ
  obtain ⟨k, ⟨j, hj⟩, hk⟩ := LocLawH.chi_exp hC.hθ hC.hχ hC.hη τ
  refine ⟨k - j, fun y a ha hy f hf => ?_⟩
  set A : GL (Fin n) ℂ := Matrix.GeneralLinearGroup.mkOfDetNeZero a ha.ne_zero with hAdef
  have hAv : A.1 = a := rfl
  have hAi : (A⁻¹).1 = a⁻¹ := by rw [Matrix.coe_units_inv, hAv]
  have hyA : y = LocLawH.mOf A := by
    apply GR_ext
    rw [hy, LocLawH.mR_mOf, hAv, hAi, Matrix.conjTranspose_nonsing_inv]
    rfl
  have hy0 : (mR (LocLawH.mOf A)).toBlocks₂₁ = 0 := by simp [LocLawH.mR_mOf]
  have haOf : LocLawH.aOf (LocLawH.mOf A) hy0 = A := Units.ext (by rw [LocLawH.aOf_val, LocLawH.mR_mOf]; simp)
  have hsc := LocLawH.scal hC.hθ hσ k j hk hj (cnt (epsT (tLoc l τ) ε) true) (cnt (epsT (tLoc l τ) ε) false)
    (cnt_add _) (LocLawH.mOf A) hy0
  rw [haOf] at hsc
  refine hTI D n V ψ χ θ μ ω H l s ν τ ε fr ι hC _ _ fun Ψ hΨ => ?_
  rw [← hL.2 y Ψ hΨ f hf]
  funext x
  rw [hyA, hC.hω.levi _ (LocLawH.unitAt hσ τ A) (LocLawH.mat_mOf hσ hC.hι A), hsc, weight_factor_eq_automorphy,
    siegelP_jF _ hy0, cnt_add]
  have hbl : (mR (LocLawH.mOf A)).toBlocks₁₁ = a := by rw [LocLawH.mR_mOf]; simp [hAv]
  rw [hbl]
  have hΨx : Ψ (HMul.hMul x (LocLawH.unitAt hσ τ A).1 : Mx D V.rank n) = Ψ x := by
    refine hΨ.1 _ _ (fun τ' h => ?_) ?_
    · rw [LocLawH.unitAt_val, LocLawH.compAt_mulM, LocLawH.component_adelic_point_ne hσ h, Matrix.mul_one]
    · rw [LocLawH.unitAt_val, Matrix.map_mul, LocLawH.finite_part_adelic_point_matrix hσ, Matrix.mul_one]
  simp only [tens, hΨx, levF]
  rw [LocLawH.unitAt_val, LocLawH.compAt_mulM, LocLawH.component_adelic_point_matrix hσ, hAv, ← Matrix.mul_assoc]
  have hof : (Matrix.of (fr⁻¹ * compAt θ τ x) : Matrix (Fin V.rank) (Fin n) ℂ) = fr⁻¹ * compAt θ τ x := rfl
  rw [hof]
  ring

end PositivityTheory.Rg.Sw.Glob
end
end

