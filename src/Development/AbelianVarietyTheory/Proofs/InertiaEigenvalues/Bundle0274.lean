import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0256
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqTopOfSpanImage
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0250

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceMirabolicDetAverageEqHarishChandraRestricti
section
open GlobalTheory.GLq GlobalTheory.MirAvg Polynomial

namespace GlobalTheory.ResTr
variable {g : ℕ} [Fact g.Prime]
open Formalism.MainNotions.ArithmeticCylinders

open Classical in
theorem coeff_mirEl {r : ℕ} (θ : (ZMod g)ˣ →* ℂˣ) (a : Fin r → ZMod g) (b : Bool) (h : Gn g r) :
    (mirEl θ a b).coeff h = if mirSet a b h then ((θ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) else 0 := by
  unfold mirEl
  simp [MonoidAlgebra.coeff_single, Finsupp.single_apply]

theorem sum_gl1 (M : Mt g 1) (d : (ZMod g)ˣ) (hM : M.det = d) (F : (ZMod g)ˣ → ℂ) :
    (∑ x : Gn g 1, if M = (x : Mt g 1) then F (Matrix.GeneralLinearGroup.det x) else 0) = F d := by
  have hU : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).2 (by rw [hM]; exact d.isUnit)
  have key : ∀ x : Gn g 1, (M = (x : Mt g 1)) ↔ x = hU.unit := by
    intro x
    rw [Units.ext_iff, IsUnit.unit_spec]
    exact eq_comm
  simp_rw [key]
  rw [Finset.sum_ite_eq' Finset.univ hU.unit, if_pos (Finset.mem_univ _)]
  congr 1
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, IsUnit.unit_spec, hM]

theorem tl_last {n : ℕ} (M : Mt g (n + 1)) (i j : Fin n) : tl n M i j = M i.castSucc j.castSucc := by
  unfold tl entN
  rw [dif_pos ⟨by omega, by omega⟩]
  rfl

theorem br_last {n : ℕ} (M : Mt g (n + 1)) (i j : Fin 1) : br n 1 M i j = M (Fin.last n) (Fin.last n) := by
  unfold br entN
  rw [dif_pos ⟨by omega, by omega⟩]
  congr 1 <;> ext <;> simp [Fin.fin_one_eq_zero]

theorem br_succ {n : ℕ} (M : Mt g (n + 1)) (i j : Fin n) : br 1 n M i j = M i.succ j.succ := by
  unfold br entN
  rw [dif_pos ⟨by omega, by omega⟩]
  congr 1 <;> ext <;> simp [add_comm]

theorem tl_zero {n : ℕ} (M : Mt g (n + 1)) (i j : Fin 1) : tl 1 M i j = M 0 0 := by
  unfold tl entN
  rw [dif_pos ⟨by omega, by omega⟩]
  congr 1 <;> ext <;> simp [Fin.fin_one_eq_zero]

def ColsId {n : ℕ} (M : Mt g (n + 1)) : Prop :=
  ∀ i j : Fin (n + 1), j ≠ Fin.last n → M i j = if i = j then 1 else 0

def RowsId {n : ℕ} (M : Mt g (n + 1)) : Prop :=
  ∀ i j : Fin (n + 1), i ≠ 0 → M i j = if i = j then 1 else 0

theorem mulVec_of_id {N : ℕ} (M : Mt g N) (x : Fin N → ZMod g) (i : Fin N)
    (h : ∀ j, x j ≠ 0 → M i j = if i = j then 1 else 0) : M.mulVec x i = x i := by
  rw [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single i]
  · by_cases hx : x i = 0
    · rw [hx, mul_zero]
    · rw [h i hx, if_pos rfl, one_mul]
  · intro j _ hji
    by_cases hx : x j = 0
    · rw [hx, mul_zero]
    · rw [h j hx, if_neg (Ne.symm hji), zero_mul]
  · intro hi; exact absurd (Finset.mem_univ i) hi

theorem mirSet_last_iff {n : ℕ} (h : Gn g (n + 1)) :
    mirSet (Pi.single (Fin.last n) 1) false h ↔ ColsId (h : Mt g (n + 1)) := by
  unfold mirSet
  simp only [Bool.false_eq_true, if_false]
  constructor
  · intro H i j hj
    have := congrFun (H (Pi.single j 1) (by simp [single_dotProduct, Pi.single_apply, Ne.symm hj])) i
    rw [Matrix.mulVec_single_one] at this
    simpa [Pi.single_apply] using this
  · intro H x hx
    have hx' : x (Fin.last n) = 0 := by simpa [single_dotProduct] using hx
    funext i
    apply mulVec_of_id
    intro j hj
    exact H i j (fun e => hj (e ▸ hx'))

theorem mirSet_zero_iff {n : ℕ} (h : Gn g (n + 1)) :
    mirSet (Pi.single 0 1) true h ↔ RowsId (h : Mt g (n + 1)) := by
  unfold mirSet
  simp only [if_true]
  constructor
  · intro H i j hi
    obtain ⟨c, hc⟩ := H (Pi.single j 1)
    have := congrFun hc i
    rw [Matrix.mulVec_single_one] at this
    simp [Pi.single_apply, hi] at this
    rw [sub_eq_zero] at this
    simpa [Pi.single_apply] using this
  · intro H x
    refine ⟨((h : Mt g (n + 1)).mulVec x - x) 0, ?_⟩
    funext i
    by_cases hi : i = 0
    · subst hi; simp
    · have : (h : Mt g (n + 1)).mulVec x i = x i := mulVec_of_id _ _ _ (fun j _ => H i j hi)
      simp [this, hi]

theorem parTl_iff {n : ℕ} (M : Mt g (n + 1)) : (InPar n M ∧ tl n M = 1) ↔ ColsId M := by
  constructor
  · rintro ⟨hP, hT⟩ i j hj
    obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.2 hj
    induction i using Fin.lastCases with
    | last =>
      rw [if_neg (Fin.castSucc_ne_last j).symm]
      exact hP _ _ (by simp) (by simp)
    | cast i =>
      have := congrFun (congrFun hT i) j
      rw [tl_last] at this
      rw [this, Matrix.one_apply]
      simp [Fin.castSucc_inj]
  · intro H
    refine ⟨fun i j hj hi => ?_, ?_⟩
    · have hne : j ≠ Fin.last n := fun e => by rw [e] at hj; simp at hj
      rw [H i j hne, if_neg]
      intro e; rw [e] at hi; omega
    · ext i j
      rw [tl_last, H _ _ (Fin.castSucc_ne_last j), Matrix.one_apply]
      simp [Fin.castSucc_inj]

theorem parBr_iff {n : ℕ} (M : Mt g (n + 1)) : (InPar 1 M ∧ br 1 n M = 1) ↔ RowsId M := by
  constructor
  · rintro ⟨hP, hB⟩ i j hi
    obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.2 hi
    induction j using Fin.cases with
    | zero =>
      rw [if_neg (Fin.succ_ne_zero i)]
      exact hP _ _ (by simp) (by simp)
    | succ j =>
      have := congrFun (congrFun hB i) j
      rw [br_succ] at this
      rw [this, Matrix.one_apply]
      simp [Fin.succ_inj]
  · intro H
    refine ⟨fun i j hj hi => ?_, ?_⟩
    · have hne : i ≠ 0 := fun e => by rw [e] at hi; simp at hi
      rw [H i j hne, if_neg]
      intro e; rw [e] at hi; omega
    · ext i j
      rw [br_succ, H _ _ (Fin.succ_ne_zero i), Matrix.one_apply]
      simp [Fin.succ_inj]

theorem det_colsId {n : ℕ} (M : Mt g (n + 1)) (H : ColsId M) : M.det = M (Fin.last n) (Fin.last n) := by
  have hT : M.BlockTriangular id := by
    intro i j hij
    have hj : j ≠ Fin.last n := fun e => by
      rw [e] at hij; exact absurd hij (not_lt.2 (Fin.le_last i))
    simp only [id] at hij
    rw [H i j hj, if_neg (ne_of_gt hij)]
  rw [Matrix.det_of_upperTriangular hT, Fin.prod_univ_castSucc]
  rw [Finset.prod_eq_one, one_mul]
  intro i _
  rw [H _ _ (Fin.castSucc_ne_last i), if_pos rfl]

theorem det_rowsId {n : ℕ} (M : Mt g (n + 1)) (H : RowsId M) : M.det = M 0 0 := by
  have hT : M.BlockTriangular id := by
    intro i j hij
    have hi : i ≠ 0 := fun e => by
      rw [e] at hij; exact absurd hij (not_lt.2 (Fin.zero_le j))
    simp only [id] at hij
    rw [H i j hi, if_neg (ne_of_gt hij)]
  rw [Matrix.det_of_upperTriangular hT, Fin.prod_univ_succ]
  rw [Finset.prod_eq_one, mul_one]
  intro i _
  rw [H _ _ (Fin.succ_ne_zero i), if_pos rfl]

theorem det_br_last {n : ℕ} (h : Gn g (n + 1)) (H : ColsId (h : Mt g (n + 1))) :
    (br n 1 (h : Mt g (n + 1))).det = ((Matrix.GeneralLinearGroup.det h : (ZMod g)ˣ) : ZMod g) := by
  rw [Matrix.det_unique, br_last, Matrix.GeneralLinearGroup.val_det_apply, det_colsId _ H]

theorem det_tl_zero {n : ℕ} (h : Gn g (n + 1)) (H : RowsId (h : Mt g (n + 1))) :
    (tl 1 (h : Mt g (n + 1))).det = ((Matrix.GeneralLinearGroup.det h : (ZMod g)ˣ) : ZMod g) := by
  rw [Matrix.det_unique, tl_zero, Matrix.GeneralLinearGroup.val_det_apply, det_rowsId _ H]

open Classical in

theorem trace_mir (g : ℕ) [Fact g.Prime] (n : ℕ) (ψ : Gn g (n + 1) → ℂ) (θ : (ZMod g)ˣ →* ℂˣ) :
    tr (mirEl θ (Pi.single (Fin.last n) 1) false) ψ =
        (g : ℂ) ^ n * ∑ x : Gn g 1, ((θ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * res n 1 ψ 1 x ∧
      tr (mirEl θ (Pi.single 0 1) true) ψ =
        (g : ℂ) ^ n * ∑ x : Gn g 1, ((θ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * res 1 n ψ x 1 := by
  have hg : (g : ℂ) ^ n ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : g.Prime).ne_zero)
  have hc : ∀ a t : ℂ, (g : ℂ) ^ n * (a * (((g : ℂ) ^ n)⁻¹ * t)) = a * t := fun a t => by
    rw [mul_left_comm, mul_inv_cancel_left₀ hg]
  constructor
  · unfold tr res
    simp_rw [coeff_mirEl, mul_one, Finset.mul_sum, hc]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun h _ => ?_)
    by_cases H : ColsId (h : Mt g (n + 1))
    · obtain ⟨hP, hT⟩ := (parTl_iff _).2 H
      rw [if_pos ((mirSet_last_iff h).2 H)]
      simp only [Units.val_one, hP, hT, true_and, mul_ite, mul_zero]
      rw [sum_gl1 _ _ (det_br_last h H) (fun d => ((θ d : ℂˣ) : ℂ) * ψ h)]
    · rw [if_neg (fun e => H ((mirSet_last_iff h).1 e)), zero_mul]
      refine (Finset.sum_eq_zero (fun x _ => ?_)).symm
      rw [if_neg (fun e => H ((parTl_iff _).1 ⟨e.1, by simpa using e.2.1⟩)), mul_zero]
  · unfold tr res
    simp_rw [coeff_mirEl, one_mul, Finset.mul_sum, hc]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun h _ => ?_)
    by_cases H : RowsId (h : Mt g (n + 1))
    · obtain ⟨hP, hB⟩ := (parBr_iff _).2 H
      rw [if_pos ((mirSet_zero_iff h).2 H)]
      simp only [Units.val_one, hP, hB, true_and, and_true, mul_ite, mul_zero]
      rw [sum_gl1 _ _ (det_tl_zero h H) (fun d => ((θ d : ℂˣ) : ℂ) * ψ h)]
    · rw [if_neg (fun e => H ((mirSet_zero_iff h).1 e)), zero_mul]
      refine (Finset.sum_eq_zero (fun x _ => ?_)).symm
      rw [if_neg (fun e => H ((parBr_iff _).1 ⟨e.1, by simpa using e.2.2⟩)), mul_zero]
end GlobalTheory.ResTr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceMirabolicDetCharacterAverageVectorIndep
section
open GlobalTheory.GLq GlobalTheory.MirAvg Polynomial

noncomputable section

namespace GlobalTheory.MirAvg

open Matrix

variable {g : ℕ} [Fact g.Prime]

theorem exists_gl_mulVec_single_eq {r : ℕ} (i : Fin r) {a : Fin r → ZMod g} (ha : a ≠ 0) :
    ∃ y : Gn g r, (y : Mt g r) *ᵥ Pi.single i 1 = a := by
  have he : (Pi.single i (1 : ZMod g) : Fin r → ZMod g) ≠ 0 := by
    intro h; have := congrFun h i; simp at this
  let f := (LinearEquiv.toSpanNonzeroSingleton (ZMod g) (Fin r → ZMod g) _ he).symm.trans
    (LinearEquiv.toSpanNonzeroSingleton (ZMod g) (Fin r → ZMod g) a ha)
  obtain ⟨e, hef⟩ := Submodule.exists_linearEquiv_restrict_eq f
  have h1 : e (Pi.single i 1) = a := by
    have := hef ⟨_, Submodule.mem_span_singleton_self _⟩
    rw [← this]
    simp only [f, LinearEquiv.trans_apply]
    rw [← LinearEquiv.toSpanNonzeroSingleton_one (ZMod g) (Fin r → ZMod g) _ he, LinearEquiv.symm_apply_apply,
      LinearEquiv.toSpanNonzeroSingleton_one]
  refine ⟨⟨LinearMap.toMatrix' e.toLinearMap, LinearMap.toMatrix' e.symm.toLinearMap, ?_, ?_⟩, ?_⟩
  · rw [← LinearMap.toMatrix'_comp]; simp
  · rw [← LinearMap.toMatrix'_comp]; simp
  · show LinearMap.toMatrix' e.toLinearMap *ᵥ _ = a
    rw [LinearMap.toMatrix'_mulVec]; exact h1

theorem mirSet_true_conj {r : ℕ} (a : Fin r → ZMod g) (y z : Gn g r) :
    mirSet a true (y * z * y⁻¹) ↔ mirSet ((↑y⁻¹ : Mt g r) *ᵥ a) true z := by
  have hAB : (y : Mt g r) * (↑y⁻¹ : Mt g r) = 1 := y.mul_inv
  have hBA : (↑y⁻¹ : Mt g r) * (y : Mt g r) = 1 := y.inv_mul
  simp only [mirSet, if_true, Units.val_mul]
  constructor
  · intro h x
    obtain ⟨c, hc⟩ := h ((y : Mt g r) *ᵥ x)
    refine ⟨c, ?_⟩
    have := congrArg (fun v => (↑y⁻¹ : Mt g r) *ᵥ v) hc
    simp only [mulVec_sub, mulVec_smul, mulVec_mulVec, ← Matrix.mul_assoc, hBA, Matrix.one_mul] at this
    rw [Matrix.mul_assoc, hBA, Matrix.mul_one, one_mulVec] at this
    exact this
  · intro h x
    obtain ⟨c, hc⟩ := h ((↑y⁻¹ : Mt g r) *ᵥ x)
    refine ⟨c, ?_⟩
    have := congrArg (fun v => (y : Mt g r) *ᵥ v) hc
    simp only [mulVec_sub, mulVec_smul, mulVec_mulVec, ← Matrix.mul_assoc, hAB, Matrix.one_mul, one_mulVec] at this
    rw [← this]

theorem mirSet_false_conj {r : ℕ} (a : Fin r → ZMod g) (y z : Gn g r) :
    mirSet a false (y * z * y⁻¹) ↔ mirSet (a ᵥ* (y : Mt g r)) false z := by
  have hAB : (y : Mt g r) * (↑y⁻¹ : Mt g r) = 1 := y.mul_inv
  have hBA : (↑y⁻¹ : Mt g r) * (y : Mt g r) = 1 := y.inv_mul
  simp only [mirSet, Bool.false_eq_true, if_false, Units.val_mul]
  constructor
  · intro h x hx
    rw [← dotProduct_mulVec] at hx
    have := h _ hx
    have := congrArg (fun v => (↑y⁻¹ : Mt g r) *ᵥ v) this
    simp only [mulVec_mulVec, ← Matrix.mul_assoc, hBA, Matrix.one_mul] at this
    rw [Matrix.mul_assoc, hBA, Matrix.mul_one, one_mulVec] at this
    exact this
  · intro h x hx
    have h2 : (a ᵥ* (y : Mt g r)) ⬝ᵥ ((↑y⁻¹ : Mt g r) *ᵥ x) = 0 := by
      rw [← dotProduct_mulVec, mulVec_mulVec, hAB, one_mulVec]; exact hx
    have := h _ h2
    have := congrArg (fun v => (y : Mt g r) *ᵥ v) this
    simp only [mulVec_mulVec, hAB, one_mulVec] at this
    rw [Matrix.mul_assoc]; exact this

open Classical in
theorem mirEl_coeff {r : ℕ} (θ : (ZMod g)ˣ →* ℂˣ) (a : Fin r → ZMod g) (b : Bool) (x : Gn g r) :
    (mirEl θ a b).coeff x = if mirSet a b x then ((θ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) else 0 := by
  unfold mirEl
  rw [MonoidAlgebra.coeff_sum, Finset.sum_apply', Finset.sum_eq_single x]
  · simp [MonoidAlgebra.coeff_single]
  · intro h _ hne; simp [MonoidAlgebra.coeff_single, Finsupp.single_apply, hne]
  · intro h; exact absurd (Finset.mem_univ x) h

theorem tr_mirEl_conj {r : ℕ} (ψ : Gn g r → ℂ) (hψ : IsClass ψ) (θ : (ZMod g)ˣ →* ℂˣ)
    (a a' : Fin r → ZMod g) (b : Bool) (y : Gn g r) (H : ∀ z, mirSet a b (y * z * y⁻¹) ↔ mirSet a' b z) :
    tr (mirEl θ a b) ψ = tr (mirEl θ a' b) ψ := by
  classical
  unfold tr
  simp only [mirEl_coeff]
  rw [← Equiv.sum_comp (MulAut.conj y).toEquiv]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]
  have hd : Matrix.GeneralLinearGroup.det (y * z * y⁻¹) = Matrix.GeneralLinearGroup.det z := by
    rw [map_mul, map_mul, map_inv, mul_comm (Matrix.GeneralLinearGroup.det y), mul_inv_cancel_right]
  rw [hd, hψ z y]
  simp only [H z]

end GlobalTheory.MirAvg

open GlobalTheory.GLq GlobalTheory.MirAvg Matrix in

theorem GlobalTheory.MirAvg.tr_mirEl_indep : ∀ (g : ℕ) [Fact g.Prime] (n : ℕ) (ψ : Gn g (n + 1) → ℂ), IsClass ψ → ∀ (θ : (ZMod g)ˣ →* ℂˣ)
    (a : Fin (n + 1) → ZMod g), a ≠ 0 → ∀ b : Bool,
      tr (mirEl θ a b) ψ = tr (mirEl θ (if b then Pi.single 0 1 else Pi.single (Fin.last n) 1) b) ψ := by
  intro g _ n ψ hψ θ a ha b
  cases b with
  | true =>
    obtain ⟨y, hy⟩ := exists_gl_mulVec_single_eq (0 : Fin (n + 1)) ha
    refine tr_mirEl_conj ψ hψ θ a _ true y fun z => ?_
    rw [mirSet_true_conj, if_pos rfl, ← hy, mulVec_mulVec, y.inv_mul, one_mulVec]
  | false =>
    obtain ⟨P, hP⟩ := exists_gl_mulVec_single_eq (Fin.last n) ha
    let y : Gn g (n + 1) := ⟨(↑P⁻¹ : Mt g (n + 1))ᵀ, (P : Mt g (n + 1))ᵀ,
      by rw [← transpose_mul, P.mul_inv, transpose_one], by rw [← transpose_mul, P.inv_mul, transpose_one]⟩
    refine tr_mirEl_conj ψ hψ θ a _ false y fun z => ?_
    rw [mirSet_false_conj]
    have : a ᵥ* (y : Mt g (n + 1)) = Pi.single (Fin.last n) 1 := by
      show a ᵥ* (↑P⁻¹ : Mt g (n + 1))ᵀ = _
      rw [vecMul_transpose, ← hP, mulVec_mulVec, P.inv_mul, one_mulVec]
    rw [this]; rfl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitForOfTie
section
noncomputable section

namespace GlobalTheory.WachUnit

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}

theorem unitFor_of_tie (hO : Function.Injective (algebraMap O LL))
    (E : EtTie W RA RW inclR φR gR πA)
    (hm : ∀ m : Ideal W.EE, m.IsMaximal → m.map E.ioE.toRingHom ≠ ⊤) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts.UnitFor E := by
  intro e₀ h₀
  obtain ⟨e₁, f₀, hf₀, hj, hN⟩ := E.one_e
  obtain ⟨u, hu, hT⟩ := W.one_line
  have huT : u ∈ W.one.L.T := by rw [hT]; exact Submodule.mem_span_singleton_self u
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (hf₀ ▸ Submodule.mem_top : e₀ ∈ Submodule.span O {f₀})
  obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.1 (h₀ ▸ Submodule.mem_top : f₀ ∈ Submodule.span O {e₀})
  have hje : E.jD W.one (c • e₁) = (1 : RW) ⊗ₜ[O] e₀ := by
    rw [map_smul, hj, ← hc, TensorProduct.tmul_smul]
  have hde : d • (c • e₁) = e₁ := by
    apply E.jD_inj
    rw [map_smul, hje, hj, ← hd, TensorProduct.tmul_smul]
  refine ⟨c • e₁, hje, ⟨fun x y hxy => ?_, ?_⟩, ?_, fun g => ?_, ?_⟩
  · have h1 := congrArg (E.jD W.one) hxy
    simp only at h1
    rw [E.jD_smul, E.jD_smul, hje, TensorProduct.smul_tmul', TensorProduct.smul_tmul',
      smul_eq_mul, smul_eq_mul, mul_one, mul_one] at h1
    exact GlobalTheory.EtaleExact.ioE_injective E
      (GlobalTheory.Cyc.Decomp.tmul_gen_cancel hO W.one u hu huT e₀ h₀ _ _ h1)
  · have htop : Submodule.span W.EE {c • e₁} = ⊤ := by
      refine GlobalTheory.EtaleExact.eq_top_DD E hm W.one _ ?_
      rw [eq_top_iff]
      rintro z -
      have h1 : ((1 : RW) ⊗ₜ[O] e₀ : TW RW W.one) ∈ Submodule.span RW
          (E.jD W.one '' (Submodule.span W.EE {c • e₁} : Submodule W.EE (W.DD W.one))) :=
        Submodule.subset_span ⟨c • e₁, Submodule.mem_span_singleton_self _, hje⟩
      induction z using TensorProduct.induction_on with
      | zero => exact Submodule.zero_mem _
      | add a b ha hb => exact Submodule.add_mem _ ha hb
      | tmul r t =>
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1
          (h₀ ▸ Submodule.mem_top : t ∈ Submodule.span O {e₀})
        have h2 : (r ⊗ₜ[O] (a • e₀) : TW RW W.one) = (a • r) • ((1 : RW) ⊗ₜ[O] e₀) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, TensorProduct.smul_tmul]
        rw [h2]
        exact Submodule.smul_mem _ _ h1
    intro z
    exact Submodule.mem_span_singleton.1 (htop ▸ Submodule.mem_top : z ∈ Submodule.span W.EE {c • e₁})
  · apply E.jD_inj
    rw [E.jD_φ, hje]
    simp [TWmap]
  · obtain ⟨g, rfl⟩ := W.resΓ_onto g
    apply E.jD_inj
    have hact : W.one.actT g e₀ = e₀ := Subtype.ext (W.one_triv g e₀)
    rw [E.jD_act, hje]
    simp [TWact, hact]
  · rw [hN]
    apply le_antisymm
    · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
      exact ⟨algebraMap O (LetA O n) d, by rw [algebraMap_smul, hde]⟩
    · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
      exact ⟨algebraMap O (LetA O n) c, by rw [algebraMap_smul]⟩

end Generic

theorem unitPart : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (H : LocHW l P)
    (F : LocFon l P AI H), GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts.UnitPart l P AI H F := by
  intro l _ P AI H F K s LL h
  haveI := GlobalTheory.EtaleExact.finite_OL LL
  haveI : IsNoetherianRing ↥(OL LL) := IsNoetherianRing.of_finite ℤ_[l] ↥(OL LL)
  have hp : (P.PD K).p = l := P.PD_p K
  refine unitFor_of_tie Subtype.val_injective _
    (GlobalTheory.EtaleExact.map_ne_top_of_tie (F.E K s LL h).tie ?_ ?_)
  · rw [hp]
    exact GlobalTheory.EtaleExact.isUnit_or_dvd_pow P LL
  · rw [hp]
    exact GlobalTheory.EtaleExact.sep_RW LL

end GlobalTheory.WachUnit
end
end

