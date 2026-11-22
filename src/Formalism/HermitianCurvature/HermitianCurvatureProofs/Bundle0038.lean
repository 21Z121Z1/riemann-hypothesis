import Formalism.HermitianCurvature.CompositeFormulaLevelZero
import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0006
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0080
import Formalism.HermitianCurvature.LetterProductDoubleDegreeCount

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftMemMatrixAlgebra
section
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T

section MatSub

variable {A : Type} [Ring A] [Algebra ℂ A]

def matSub (C : Subalgebra ℂ A) (n : Type) [Fintype n] [DecidableEq n] : Subalgebra ℂ (Matrix n n A) where
  carrier := {M | ∀ i j, M i j ∈ C}
  mul_mem' := by
    intro M N hM hN i j
    rw [Matrix.mul_apply]
    exact Subalgebra.sum_mem _ fun k _ => Subalgebra.mul_mem _ (hM i k) (hN k j)
  add_mem' := by
    intro M N hM hN i j
    exact Subalgebra.add_mem _ (hM i j) (hN i j)
  algebraMap_mem' := by
    intro c i j
    rw [Matrix.algebraMap_matrix_apply]
    split_ifs
    · exact C.algebraMap_mem c
    · exact C.zero_mem

theorem mem_matSub {C : Subalgebra ℂ A} {n : Type} [Fintype n] [DecidableEq n] {M : Matrix n n A} :
    M ∈ matSub C n ↔ ∀ i j, M i j ∈ C := by
  exact Iff.rfl

variable {S : Type} [Fintype S] [DecidableEq S] (C : Subalgebra ℂ A)

theorem eU_mem (a : S) (i j : Fin 2) : (eU a i j : SlopeTestRemainingChoices S A) ∈ matSub C (Ix S) := by
  rw [mem_matSub]
  intro x y
  simp only [eU, Matrix.of_apply]
  split_ifs
  · exact C.one_mem
  · exact C.zero_mem

theorem io_mem {x : A} (hx : x ∈ C) : (io x : SlopeTestRemainingChoices S A) ∈ matSub C (Ix S) := by
  rw [mem_matSub]
  intro i j
  simp only [io, Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs
  · exact hx
  · exact C.zero_mem

theorem lift_mem_matrix_algebra {M : M2 A} (hM : ∀ i j, M i j ∈ C) :
    (lift0 M : M2 (SlopeTestRemainingChoices S A)) ∈ matSub (matSub C (Ix S)) (Fin 2) := by
  rw [mem_matSub]
  intro i j
  simp only [lift0, Matrix.map_apply]
  exact io_mem C (hM i j)

theorem ins_mem (a : S) {M : M2 (SlopeTestRemainingChoices S A)} (hM : M ∈ matSub (matSub C (Ix S)) (Fin 2)) :
    ins a M ∈ matSub C (Ix S) := by
  unfold ins
  refine Subalgebra.sum_mem _ fun i _ => Subalgebra.sum_mem _ fun j _ => Subalgebra.mul_mem _ (eU_mem C a i j) ?_
  exact mem_matSub.1 hM i j

theorem transpose_mem {n : Type} [Fintype n] [DecidableEq n] {C' : Subalgebra ℂ A} {M : Matrix n n A}
    (hM : M ∈ matSub C' n) : Mᵀ ∈ matSub C' n := by
  exact mem_matSub.2 fun i j => mem_matSub.1 hM j i

theorem Rh0_mem (a : S) (D : ℂ) : (Rh0 a D : M2 (SlopeTestRemainingChoices S A)) ∈ matSub (matSub C (Ix S)) (Fin 2) := by
  have hP : (P0 a : M2 (SlopeTestRemainingChoices S A)) ∈ matSub (matSub C (Ix S)) (Fin 2) :=
    mem_matSub.2 fun i j => eU_mem C a j i
  unfold Rh0
  exact Subalgebra.smul_mem _ (Subalgebra.sub_mem _ (Subalgebra.smul_mem _ (Subalgebra.one_mem _) D) hP) _

theorem Rht0_mem (a : S) (D : ℂ) : (Rht0 a D : M2 (SlopeTestRemainingChoices S A)) ∈ matSub (matSub C (Ix S)) (Fin 2) := by
  have hQ : (Q0 a : M2 (SlopeTestRemainingChoices S A)) ∈ matSub (matSub C (Ix S)) (Fin 2) :=
    mem_matSub.2 fun i j => eU_mem C a i j
  unfold Rht0
  exact Subalgebra.smul_mem _ (Subalgebra.sub_mem _ (Subalgebra.smul_mem _ (Subalgebra.one_mem _) D) hQ) _

theorem TTw_mem {QQ : ℂ → M2 A} (hQ : ∀ Y i j, QQ Y i j ∈ C) (w : List (Letter ℂ S)) (Y : ℂ) :
    TTw QQ w Y ∈ matSub (matSub C (Ix S)) (Fin 2) := by
  induction w generalizing Y with
  | nil =>
    simp only [TTw]
    exact lift_mem_matrix_algebra C (hQ Y)
  | cons l w ih =>
    simp only [TTw]
    split_ifs
    · exact Subalgebra.mul_mem _ (ih Y) (Rh0_mem C _ _)
    · exact Subalgebra.mul_mem _ (Rht0_mem C _ _) (ih Y)

theorem RRw_mem {QQ : ℂ → M2 A} (hQ : ∀ Y i j, QQ Y i j ∈ C) (w : List (Letter ℂ S)) :
    RRw QQ w ∈ matSub C (Ix S) := by
  induction w with
  | nil =>
    simp only [RRw]
    exact Subalgebra.one_mem _
  | cons l w ih =>
    simp only [RRw]
    refine Subalgebra.mul_mem _ ih (ins_mem C _ ?_)
    split_ifs
    · exact TTw_mem C hQ w _
    · exact transpose_mem (TTw_mem C hQ w _)

theorem commute_io {f : A} {M : SlopeTestRemainingChoices S A} (hM : M ∈ matSub (Subalgebra.centralizer ℂ {f}) (Ix S)) :
    Commute (io f : SlopeTestRemainingChoices S A) M := by
  have h : ∀ i j, f * M i j = M i j * f := by
    intro i j
    have hm := mem_matSub.1 hM i j
    rw [Subalgebra.mem_centralizer_iff] at hm
    exact hm f (Set.mem_singleton f)
  show (io f : SlopeTestRemainingChoices S A) * M = M * io f
  ext i j
  simp only [io, Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  exact h i j

end MatSub

section Act

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]

theorem pr_fst_sum {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} (s : Finset ι) (g : ι → Pr V) :
    (∑ i ∈ s, g i).1 = ∑ i ∈ s, (g i).1 := by
  first
    | exact Prod.fst_sum (s := s) (f := g)
    | (classical
       induction s using Finset.induction_on with
       | empty => simp only [Finset.sum_empty]; rfl
       | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]; rfl)

theorem pr_fst_mul {V : Type} [AddCommGroup V] [Module ℂ V] (m n : Pr V) : (m * n).1 = m.1 * n.1 := rfl

theorem pr_fst_zero {V : Type} [AddCommGroup V] [Module ℂ V] : (0 : Pr V).1 = 0 := rfl

theorem act_mul (M N : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))) (x : Ix S → RadSp k r z z' π π') :
    act (M * N) x = act M (act N x) := by
  funext a
  simp only [act, Matrix.mul_apply, pr_fst_sum, pr_fst_mul, LinearMap.sum_apply, Module.End.mul_apply,
    map_sum]
  exact Finset.sum_comm

theorem act_io (f : Pr (RadSp k r z z' π π')) (x : Ix S → RadSp k r z z' π π') (a : Ix S) :
    act (io f) x a = f.1 (x a) := by
  simp only [act, io, Matrix.scalar_apply, Matrix.diagonal_apply]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    rw [if_neg (Ne.symm hb), pr_fst_zero, LinearMap.zero_apply]
  · intro h
    exact absurd (Finset.mem_univ a) h

end Act

section Wave

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]

theorem hsInner_smul_left (a : ℂ) (U V : Wq →L[ℂ] Wp) : B.hsInner (a • U) V = a * B.hsInner U V := by
  have e : Formalism.FourierDecayAlt.B.hsVec (a • U) = a • Formalism.FourierDecayAlt.B.hsVec U := by
    unfold Formalism.FourierDecayAlt.B.hsVec
    rw [← WithLp.toLp_smul]
    first
      | rfl
      | (congr 1; funext i; simp)
  unfold Formalism.FourierDecayAlt.B.hsInner
  rw [e, inner_smul_right]

theorem pairAt_mulOp (μ : Measure (Mt k r)) (l : Fin r) (s : ℂ) (Wv : Module.End ℂ (RadSp k r z z' π π'))
    (hW : multiplicationOperator Wv (fun c _ => fsv s (c l))) (Φ Ψ : RadSp k r z z' π π') (c : Fin r → ℂ) :
    pairAt μ (Wv Φ) Ψ c = fsv s (c l) * pairAt μ Φ Ψ c := by
  unfold pairAt
  simp_rw [hW Φ c, hsInner_smul_left]
  exact MeasureTheory.integral_const_mul _ _

theorem glue_succ_update (l : Fin r) (c : Fin r → ℂ) (t : ℂ) (c' : Cf r l.succ) :
    glue l.succ (Function.update c l t) c' l = t := by
  simp only [glue]
  rw [dif_neg (by rw [Fin.val_succ]; omega)]
  simp

theorem form_mulOp (μ : Measure (Mt k r)) (l : Fin r) (s : ℂ) (Wv Wv' : Module.End ℂ (RadSp k r z z' π π'))
    (hW : multiplicationOperator Wv (fun c _ => fsv s (c l))) (u y : Ix S → RadSp k r z z' π π') (c : Fin r → ℂ) (t : ℂ) :
    form μ l.succ (act (io (mkP Wv Wv')) u) y (Function.update c l t) =
      fsv s t * form μ l.succ u y (Function.update c l t) := by
  unfold form
  have h : ∀ (c' : Cf r l.succ) (a : Ix S), pairAt μ (act (io (mkP Wv Wv')) u a) (y a) (glue l.succ (Function.update c l t) c') =
      fsv s t * pairAt μ (u a) (y a) (glue l.succ (Function.update c l t) c') := by
    intro c' a
    rw [act_io]
    have e : (mkP Wv Wv' : Pr (RadSp k r z z' π π')).1 = Wv := rfl
    rw [e, pairAt_mulOp μ l s Wv hW, glue_succ_update]
  simp_rw [h, ← Finset.mul_sum, mul_left_comm _ (fsv s t)]
  exact MeasureTheory.integral_const_mul _ _

end Wave

section StepParts

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]
variable (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
  (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
  (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π')))
  (K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')) (l0 : ℕ)

theorem stepTwistFromParts : StepTwistFromParts (S := S) P z z' π π' X μ L st K l0 := by
  intro hD hPW hWS hWC hWK w hw l s Wv Wv' hW hW' x y hx hy c _
  refine ⟨hWK w hw l s Wv Wv' hW hW' x hx, fun t _ => ?_⟩
  obtain ⟨hwave, hc1, hc2, hp⟩ := hWS hD.2.2.1 l s Wv Wv' hW hW'
  have hbT : bTl L l w * Vw (mkP Wv Wv') s w = io (mkP Wv Wv') * bTl L l w :=
    hPW ℂ _ S (site L l) (mkP Wv Wv') (mkP Wv' Wv) s w hwave hc1 hc2 hp hw.1.1
  have hQ : ∀ Y i j, QQi L st l.succ Y i j ∈ Subalgebra.centralizer ℂ {mkP Wv Wv'} := by
    intro Y i j
    rw [Subalgebra.mem_centralizer_iff]
    rintro g rfl
    exact (hWC l s Wv Wv' hW hW' Y i j).eq
  have hcomm : io (mkP Wv Wv') * RRi L st l.succ w = RRi L st l.succ w * io (mkP Wv Wv') :=
    (commute_io (RRw_mem _ hQ w)).eq
  simp only [P5.ph, RRform]
  rw [← act_mul (bTl L l w) (Vw (mkP Wv Wv') s w) x, hbT, act_mul (io (mkP Wv Wv')) (bTl L l w) x,
    ← act_mul (RRi L st l.succ w) (io (mkP Wv Wv')), ← hcomm, act_mul (io (mkP Wv Wv')), form_mulOp μ l s Wv Wv' hW]
  ring

end StepParts

end Formalism.FourierDecayAlt.P5
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.NormBallVolumes
section
open Matrix MeasureTheory Filter Topology Metric
open scoped ComplexConjugate ENNReal NNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.NormBallVolumes

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem gnLower : GNLower := fun _ _ _ hg => Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hg

theorem gN_meas (k r : ℕ) : Measurable fun g : Mt k r => gN (Matrix.of g) := by
  unfold gN
  apply Measurable.sqrt
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
  have h1 : Measurable fun g : Mt k r => g i j := (measurable_pi_apply j).comp (measurable_pi_apply i)
  exact Complex.continuous_normSq.measurable.comp h1

theorem ae_mem {k r : ℕ} {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) :
    ∀ᵐ g ∂μ, Matrix.of g ∈ U := by
  rw [ae_iff]
  exact h.conc

theorem one_mem (k r : ℕ) : (1 : Mat k r) ∈ GV k r := by
  show (1 : Mat k r)ᴴ * Hpk k r * 1 = Hpk k r
  simp

def iv {k r : ℕ} (g : Mat k r) : Mat k r := Hpk k r * gᴴ * Hpk k r

theorem iv_mul {k r : ℕ} {g : Mat k r} (hg : g ∈ GV k r) : iv g * g = 1 := by
  have h : gᴴ * Hpk k r * g = Hpk k r := hg
  unfold iv
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, h]
  exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.Hsq k r

theorem iv_mem {k r : ℕ} {g : Mat k r} (hg : g ∈ GV k r) : iv g ∈ GV k r := by
  rw [← Matrix.inv_eq_left_inv (iv_mul hg)]
  exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_inv hg

theorem sigmaFinite_of_haar {k r : ℕ} {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) : SigmaFinite μ := by
  have : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => h.finite_compact K hK⟩
  infer_instance

theorem lmulM_cont {k r : ℕ} (a : Mat k r) : Continuous (lmulM a : Mt k r → Mt k r) := by
  have hof : Continuous (fun x : Mt k r => (Matrix.of x : Mat k r)) := continuous_id
  exact (continuous_const (y := a)).matrix_mul hof

theorem volCrude : VolCrude :=
  _root_.UpperTheory.Reformulated.B.LiftingTheory.volCrude

theorem shellInt : ShellInt := by
  intro X _ μ N C d A hN h1 hd hV hA
  have hA0 : 0 < A := lt_of_le_of_lt hd hA
  let S : ℕ → Set X := fun j => {x | N x ≤ (2 : ℝ) ^ (j + 1)}
  let c : ℕ → ℝ := fun j => ((2 : ℝ) ^ j) ^ (-A)
  have hSm : ∀ j, MeasurableSet (S j) := fun j => measurableSet_le hN measurable_const
  have hpt : ∀ᵐ x ∂μ, ENNReal.ofReal (N x ^ (-A)) ≤ ∑' j, (S j).indicator (fun _ => ENNReal.ofReal (c j)) x := by
    filter_upwards [h1] with x hx
    obtain ⟨j, hj1, hj2⟩ := exists_nat_pow_near hx one_lt_two
    refine le_trans ?_ (ENNReal.le_tsum j)
    rw [Set.indicator_of_mem (show x ∈ S j from hj2.le)]
    apply ENNReal.ofReal_le_ofReal
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hj1 (by linarith)
  have hterm : ∀ j : ℕ, c j * (C * ((2 : ℝ) ^ (j + 1)) ^ d) = C * (2 : ℝ) ^ d * ((2 : ℝ) ^ (d - A)) ^ j := by
    intro j
    have h2 : (0 : ℝ) < 2 := two_pos
    have e1 : c j = (2 : ℝ) ^ ((j : ℝ) * (-A)) := by
      show ((2 : ℝ) ^ j) ^ (-A) = _
      rw [← Real.rpow_natCast 2 j, ← Real.rpow_mul h2.le]
    have e2 : ((2 : ℝ) ^ (j + 1)) ^ d = (2 : ℝ) ^ (((j : ℝ) + 1) * d) := by
      rw [← Real.rpow_natCast 2 (j + 1), ← Real.rpow_mul h2.le]
      push_cast
      rfl
    have e3 : ((2 : ℝ) ^ (d - A)) ^ j = (2 : ℝ) ^ ((d - A) * (j : ℝ)) := by
      rw [Real.rpow_mul_natCast h2.le]
    rw [e1, e2, e3]
    have e4 : (2 : ℝ) ^ ((j : ℝ) * (-A)) * (2 : ℝ) ^ (((j : ℝ) + 1) * d) = (2 : ℝ) ^ d * (2 : ℝ) ^ ((d - A) * (j : ℝ)) := by
      rw [← Real.rpow_add h2, ← Real.rpow_add h2]
      congr 1
      ring
    calc (2 : ℝ) ^ ((j : ℝ) * (-A)) * (C * (2 : ℝ) ^ (((j : ℝ) + 1) * d))
        = C * ((2 : ℝ) ^ ((j : ℝ) * (-A)) * (2 : ℝ) ^ (((j : ℝ) + 1) * d)) := by ring
      _ = _ := by rw [e4]; ring
  have hsum : Summable fun j : ℕ => c j * (C * ((2 : ℝ) ^ (j + 1)) ^ d) := by
    simp only [hterm]
    apply Summable.mul_left
    exact summable_geometric_of_lt_one (Real.rpow_nonneg two_pos.le _)
      (Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith))
  calc (∫⁻ x, ENNReal.ofReal (N x ^ (-A)) ∂μ)
      ≤ ∫⁻ x, ∑' j, (S j).indicator (fun _ => ENNReal.ofReal (c j)) x ∂μ := lintegral_mono_ae hpt
    _ = ∑' j, ∫⁻ x, (S j).indicator (fun _ => ENNReal.ofReal (c j)) x ∂μ :=
        lintegral_tsum fun j => (measurable_const.indicator (hSm j)).aemeasurable
    _ = ∑' j, ENNReal.ofReal (c j) * μ (S j) := by
        congr 1
        funext j
        exact lintegral_indicator_const (hSm j) _
    _ ≤ ∑' j, ENNReal.ofReal (c j) * ENNReal.ofReal (C * ((2 : ℝ) ^ (j + 1)) ^ d) := by
        refine ENNReal.tsum_le_tsum fun j => ?_
        gcongr
        exact hV _ (one_le_pow₀ one_le_two)
    _ = ∑' j, ENNReal.ofReal (c j * (C * ((2 : ℝ) ^ (j + 1)) ^ d)) := by
        congr 1
        funext j
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _)]
    _ < ∞ := hsum.tsum_ofReal_lt_top

end Formalism.FourierDecayAlt.P.NormBallVolumes

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.NormBallVolumes

theorem norm_power_integrable_crude_of_volume : Formalism.FourierDecayAlt.B2.GNIntCrudeFromVol := by
  intro hS hL hV k r μG A hμ hA
  obtain ⟨C, hC⟩ := hV k r μG hμ
  refine hS (Mt k r) μG (fun g => gN (Matrix.of g)) C _ A (gN_meas k r) ?_ (by positivity) hC hA
  filter_upwards [ae_mem hμ] with g hg using hL k r _ hg

theorem matrix_coefficient_bound_by_norm : Formalism.FourierDecayAlt.B2.CCFromGN := by
  intro k r Wp Wq _ _ _ _ D A h F c _ hb
  have hae : ∀ᵐ g ∂D.μG, ‖F (Matrix.of g)‖ₑ ≤ ENNReal.ofReal |c| * ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) := by
    filter_upwards [ae_mem D.haarG] with g hg
    have h1 := hb _ hg
    have hpos : 0 < gN (Matrix.of g) := lt_of_lt_of_le one_pos (gnLower k r _ hg)
    have hp : 0 < gN (Matrix.of g) ^ A := Real.rpow_pos_of_pos hpos A
    rw [← ENNReal.ofReal_mul (abs_nonneg c), ← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    rw [Real.rpow_neg hpos.le, ← div_eq_mul_inv, le_div_iff₀ hp]
    calc ‖F (Matrix.of g)‖ * gN (Matrix.of g) ^ A = gN (Matrix.of g) ^ A * ‖F (Matrix.of g)‖ := mul_comm _ _
      _ ≤ c := h1
      _ ≤ |c| := le_abs_self c
  calc (∫⁻ g : Mt k r, ‖F (Matrix.of g)‖ₑ ∂D.μG)
      ≤ ∫⁻ g : Mt k r, ENNReal.ofReal |c| * ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) ∂D.μG := lintegral_mono_ae hae
    _ = ENNReal.ofReal |c| * ∫⁻ g : Mt k r, ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) ∂D.μG :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top h

theorem matrix_coefficient_integrable_of_parts : Formalism.FourierDecayAlt.B2.AssembleCCInt := by
  intro h1 h2 k r Wp Wq _ _ _ _ D A hA
  exact h1 k r Wp Wq D A (h2 k r D.μG A D.haarG hA)

theorem matrix_coefficient_integrable_double : Formalism.FourierDecayAlt.B2.CCIntDouble := by
  intro hX k r Wp Wq _ _ _ _ _ _ D A hA
  by_cases hT : ∃ T : Wq →L[ℂ] Wp, T ≠ 0
  · obtain ⟨T, hT0⟩ := hT
    apply matrix_coefficient_bound_by_norm k r Wp Wq D A
    have hA1 : AB k r ≤ A / 2 := by linarith
    obtain ⟨Ξ, ⟨C, hC⟩, _⟩ := hX k r Wp Wq D (A / 2) hA1
    set F : Mat k r → (Wq →L[ℂ] Wp) := fun g => ((gN g ^ (-(A / 2)) : ℝ) : ℂ) • T with hF
    have hm : AEStronglyMeasurable (fun g : Mt k r => F (Matrix.of g)) D.μG := by
      have h1 : Measurable fun g : Mt k r => ((gN (Matrix.of g) ^ (-(A / 2)) : ℝ) : ℂ) :=
        Complex.measurable_ofReal.comp ((gN_meas k r).pow_const _)
      exact h1.aestronglyMeasurable.smul_const T
    have hn : ∀ g : Mat k r, 0 < gN g → ‖F g‖ = gN g ^ (-(A / 2)) * ‖T‖ := by
      intro g hg
      simp only [hF, norm_smul, Complex.norm_real]
      rw [Real.norm_of_nonneg (Real.rpow_nonneg hg.le _)]
    have hb : ∀ g ∈ GV k r, gN g ^ (A / 2) * ‖F g‖ ≤ ‖T‖ := by
      intro g hg
      have hpos : 0 < gN g := lt_of_lt_of_le one_pos (gnLower k r g hg)
      rw [hn g hpos, ← mul_assoc, ← Real.rpow_add hpos]
      simp
    have hmain := hC F F ‖T‖ ‖T‖ hm hm hb hb 1 (one_mem k r) 1 (one_mem k r)
    have key : ∀ᵐ g ∂D.μG, ‖T‖ₑ * ‖T‖ₑ * ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) =
        ‖F ((1 : Mat k r)⁻¹ * Matrix.of g * 1)‖ₑ * ‖F (Matrix.of g)‖ₑ := by
      filter_upwards [ae_mem D.haarG] with g hg
      have hpos : 0 < gN (Matrix.of g) := lt_of_lt_of_le one_pos (gnLower k r _ hg)
      have e1 : (1 : Mat k r)⁻¹ * Matrix.of g * 1 = Matrix.of g := by simp
      rw [e1, ← ofReal_norm (F (Matrix.of g)), hn _ hpos, ← ofReal_norm T,
        ← ENNReal.ofReal_mul (norm_nonneg T), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      have : gN (Matrix.of g) ^ (-A) = gN (Matrix.of g) ^ (-(A / 2)) * gN (Matrix.of g) ^ (-(A / 2)) := by
        rw [← Real.rpow_add hpos]; congr 1; ring
      rw [this]; ring
    have hfin : (∫⁻ g : Mt k r, ‖T‖ₑ * ‖T‖ₑ * ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) ∂D.μG) < ∞ := by
      rw [lintegral_congr_ae key]
      refine lt_of_le_of_lt hmain ?_
      exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.coe_lt_top) ENNReal.coe_lt_top
    have hc : ‖T‖ₑ * ‖T‖ₑ ≠ ∞ := ENNReal.mul_ne_top enorm_ne_top enorm_ne_top
    rw [lintegral_const_mul' _ _ hc] at hfin
    rcases ENNReal.mul_lt_top_iff.mp hfin with h | h | h
    · exact h.2
    · exfalso
      have : ‖T‖ₑ = 0 := by
        rcases mul_eq_zero.mp h with h | h <;> exact h
      exact hT0 (enorm_eq_zero.mp this)
    · rw [h]; exact ENNReal.zero_lt_top
  · simp only [not_exists, not_not] at hT
    intro F c _ _
    simp [hT]

theorem matrix_coefficient_integrable_crude_all : Formalism.FourierDecayAlt.B2.CCIntCrudeAll := by
  intro k r Wp Wq _ _ _ _ D A hA
  exact matrix_coefficient_bound_by_norm k r Wp Wq D A
    (norm_power_integrable_crude_of_volume shellInt gnLower volCrude k r D.μG A D.haarG hA)

end Formalism.FourierDecayAlt.P

namespace Formalism.FourierDecayAlt.P.NormBallVolumes

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

end Formalism.FourierDecayAlt.P.NormBallVolumes
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ThirdCountLemmaVariant
section
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P

theorem hermitian_curvature_degree_count : C7.DegreeCount2 := by
  intro k r N M dl Dl hk hN hM h1 h2
  unfold C7.Nprime C7.nOf at *
  have hn : 2 ≤ k + 2 * r + 1 := by omega
  have b2 : 2 * M * Dl ≤ 2 * (3 * (N + 1)) * ((r + 1) * (2 * (k + 2 * r + 1) + 2)) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 2 hM) h2
  have b3 : 2 * (3 * (N + 1)) * ((r + 1) * (2 * (k + 2 * r + 1) + 2)) ≤
      6 * (r + 1) * (3 * (N + 1)) * (k + 2 * r + 1) := by
    have e1 : 2 * (3 * (N + 1)) * ((r + 1) * (2 * (k + 2 * r + 1) + 2)) =
        (6 * (r + 1) * (N + 1)) * (2 * (k + 2 * r + 1) + 2) := by ring
    have e2 : 6 * (r + 1) * (3 * (N + 1)) * (k + 2 * r + 1) =
        (6 * (r + 1) * (N + 1)) * (3 * (k + 2 * r + 1)) := by ring
    rw [e1, e2]; exact Nat.mul_le_mul_left _ (by omega)
  have a2 : 1 ≤ (r + 1) * (k + 2 * r + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  refine ⟨Nat.mul_le_mul (Nat.mul_le_mul_left 2 hM) h1, b2.trans b3, by nlinarith, by nlinarith⟩

theorem third_count_lemma_variant : C7.LetterProductDoubleDegreeCount := by
  intro k r N d D hk h1 h2
  unfold C7.Dstar C7.Nprime C7.nOf at *
  have hn : 2 ≤ k + 2 * r + 1 := by omega
  have h3 : 3 * (r + 1) * d ≤ 3 * (r + 1) * ((N + 1) * (k + 2 * r + 1)) := Nat.mul_le_mul_left _ h1
  constructor
  · have e1 : (N + 1) * (r + 1) * (2 * (k + 2 * r + 1) + 2) + 3 * (r + 1) * ((N + 1) * (k + 2 * r + 1)) =
        ((r + 1) * (N + 1)) * (5 * (k + 2 * r + 1) + 2) := by ring
    have e2 : 6 * (r + 1) * (N + 1) * (k + 2 * r + 1) = ((r + 1) * (N + 1)) * (6 * (k + 2 * r + 1)) := by ring
    have h4 : ((r + 1) * (N + 1)) * (5 * (k + 2 * r + 1) + 2) ≤ ((r + 1) * (N + 1)) * (6 * (k + 2 * r + 1)) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  · have e2 : 6 * (r + 1) * (N + 1) * (k + 2 * r + 1) = ((r + 1) * (k + 2 * r + 1)) * (6 * (N + 1)) := by ring
    have e3 : 5 * (r + 1) * (3 * (N + 1) + 1) * (k + 2 * r + 1) =
        ((r + 1) * (k + 2 * r + 1)) * (5 * (3 * (N + 1) + 1)) := by ring
    rw [e2, e3]; exact Nat.mul_le_mul_left _ (by omega)

end Formalism.FourierDecayAlt.P
end

