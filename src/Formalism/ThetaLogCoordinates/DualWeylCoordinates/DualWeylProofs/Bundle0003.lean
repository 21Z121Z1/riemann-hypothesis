import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.Bundle0002

-- bundled from Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.BCoreT
section
noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ}

lemma qb_evGL_algebraMap {R : Type} [CommRing R] (g : GL (Fin n) R) (P : MvPolynomial (Fin n × Fin n) ℤ) :
    evGL g (algebraMap _ (GLCoord ℤ n) P) =
      MvPolynomial.eval₂Hom (Int.castRingHom R) (fun ab : Fin n × Fin n => g.val ab.1 ab.2) P :=
  IsLocalization.Away.lift_eq _ _ _

lemma qb_evGL_minorC {R : Type} [CommRing R] (g : GL (Fin n) R) {h : ℕ} (J I : Finset (Fin n))
    (hJ : J.card = h) (hI : I.card = h) :
    evGL g (minorC J I hJ hI) =
      Matrix.det (Matrix.of fun a b : Fin h => g.val (J.orderEmbOfFin hJ a) (I.orderEmbOfFin hI b)) := by
  unfold minorC
  rw [qb_evGL_algebraMap, RingHom.map_det]
  congr 1
  ext a b
  simp [genMat]

lemma qb_evGL_detU {R : Type} [CommRing R] (g : GL (Fin n) R) : evGL g (detU n : GLCoord ℤ n) = g.val.det := by
  have : ((detU n : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) = algebraMap _ (GLCoord ℤ n) (genMat ℤ n).det := rfl
  rw [this, qb_evGL_algebraMap, RingHom.map_det, genMat_map_eval]

lemma qb_evGL_detU_zpow {R : Type} [CommRing R] (g : GL (Fin n) R) (u : Rˣ) (hu : (u : R) = g.val.det) (z : ℤ) :
    evGL g ((detU n ^ z : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) = ((u ^ z : Rˣ) : R) := by
  have : Units.map (evGL g : GLCoord ℤ n →* R) (detU n) = u := Units.ext (by
    rw [Units.coe_map, hu]; exact qb_evGL_detU g)
  rw [← this, ← map_zpow, Units.coe_map]
  rfl

lemma qb_minor_diagonal {R : Type} [CommRing R] (d : Fin n → R) {h : ℕ} (J I : Finset (Fin n))
    (hJ : J.card = h) (hI : I.card = h) :
    Matrix.det (Matrix.of fun a b : Fin h => Matrix.diagonal d (J.orderEmbOfFin hJ a) (I.orderEmbOfFin hI b)) =
      if J = I then ∏ x ∈ J, d x else 0 := by
  split_ifs with hJI
  · subst hJI
    have : (Matrix.of fun a b : Fin h => Matrix.diagonal d (J.orderEmbOfFin hJ a) (J.orderEmbOfFin hI b)) =
        Matrix.diagonal fun a => d (J.orderEmbOfFin hJ a) := by
      ext a b
      simp [Matrix.diagonal_apply]
    rw [this, Matrix.det_diagonal]
    conv_rhs => rw [← map_orderEmbOfFin_univ J hJ]
    rw [prod_map]
    rfl
  · have : ∃ x ∈ J, x ∉ I := by
      by_contra hc
      push Not at hc
      exact hJI (eq_of_subset_of_card_le hc (by rw [hJ, hI]))
    obtain ⟨x, hxJ, hxI⟩ := this
    rw [← map_orderEmbOfFin_univ J hJ, mem_map] at hxJ
    obtain ⟨a, -, rfl⟩ := hxJ
    apply Matrix.det_eq_zero_of_row_eq_zero a
    intro b
    rw [Matrix.of_apply, Matrix.diagonal_apply_ne]
    intro hab
    apply hxI
    have := orderEmbOfFin_mem I hI b
    rw [← hab] at this
    exact this

lemma qb_prod_single {κ G : Type*} [AddCommMonoid G] (s : Finset κ) (f : κ → G) :
    ∏ x ∈ s, (AddMonoidAlgebra.single (f x) (1 : ℤ)) = AddMonoidAlgebra.single (∑ x ∈ s, f x) 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [AddMonoidAlgebra.one_def]
  | insert a s ha ih => rw [prod_insert ha, sum_insert ha, ih, AddMonoidAlgebra.single_mul_single, one_mul]

def qb_sU (w : Fin n → ℤ) : (AddMonoidAlgebra ℤ (Fin n → ℤ))ˣ :=
  Units.map (AddMonoidAlgebra.of ℤ (Fin n → ℤ)) (toUnits (Multiplicative.ofAdd w))

lemma qb_sU_val (w : Fin n → ℤ) : ((qb_sU w : (AddMonoidAlgebra ℤ (Fin n → ℤ))ˣ) : AddMonoidAlgebra ℤ (Fin n → ℤ)) =
    AddMonoidAlgebra.single w 1 := rfl

lemma qb_sU_zpow (w : Fin n → ℤ) (z : ℤ) : qb_sU w ^ z = qb_sU (z • w) := by
  unfold qb_sU
  rw [← map_zpow, ← map_zpow, ofAdd_zsmul]

variable [NeZero n]

theorem qb_evGL_torus_TMat (mu : Fin n → ℤ) (J I : TIdx mu) :
    evGL (torusPt n) (TMat mu J I) = if J = I then AddMonoidAlgebra.single (qb_wtT mu I) 1 else 0 := by
  unfold TMat
  rw [map_mul, map_prod]
  have hdet : ((qb_sU (∑ a : Fin n, Pi.single a (1 : ℤ)) : (AddMonoidAlgebra ℤ (Fin n → ℤ))ˣ) :
      AddMonoidAlgebra ℤ (Fin n → ℤ)) = (torusPt n).val.det := by
    rw [qb_sU_val]
    change _ = Matrix.det (Matrix.diagonal _)
    rw [Matrix.det_diagonal, qb_prod_single]
  rw [qb_evGL_detU_zpow (torusPt n) _ hdet, qb_sU_zpow, qb_sU_val]
  have hm : ∀ c : ↥(TCols mu), evGL (torusPt n) (minorC (J c).1 (I c).1 (J c).2 (I c).2) =
      if (J c).1 = (I c).1 then AddMonoidAlgebra.single (∑ x ∈ (J c).1, Pi.single x (1 : ℤ)) 1 else 0 := by
    intro c
    rw [qb_evGL_minorC]
    change Matrix.det (Matrix.of fun a b => Matrix.diagonal _ _ _) = _
    rw [qb_minor_diagonal, qb_prod_single]
  simp only [hm]
  split_ifs with hJI
  · subst hJI
    simp only [if_true]
    rw [qb_prod_single, AddMonoidAlgebra.single_mul_single, one_mul]
    congr 1
    funext a
    simp only [qb_wtT, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, Pi.single_apply, card_filter,
      Nat.cast_sum, smul_eq_mul]
    simp
  · have : ∃ c, (J c).1 ≠ (I c).1 := by
      by_contra hc
      push Not at hc
      exact hJI (funext fun c => Subtype.ext (hc c))
    obtain ⟨c, hc⟩ := this
    rw [prod_eq_zero (mem_univ c) (if_neg hc), mul_zero]

lemma qb_equiv_apply {M : GLMod n} (CF : ColFam M) (j : CF.J) (i : M.ι) (K : TIdx (CF.mu j)) :
    ∑ k, M.A i k * (CF.ph j k K : GLCoord ℤ n) = ∑ K', (CF.ph j i K' : GLCoord ℤ n) * TMat (CF.mu j) K' K :=
  congrFun (congrFun (CF.equiv j) i) K

theorem qb_prMu_ph {M : GLMod n} (CF : ColFam M) (j : CF.J) (nu : Fin n → ℤ) (i : M.ι) (K : TIdx (CF.mu j)) :
    ∑ k, prMu M nu i k * CF.ph j k K = if qb_wtT (CF.mu j) K = nu then CF.ph j i K else 0 := by
  have h := congrArg (evGL (torusPt n)) (qb_equiv_apply CF j i K)
  simp only [map_sum, map_mul, Int.coe_castRingHom, map_intCast,
    qb_evGL_torus_TMat, mul_ite, mul_zero, sum_ite_eq', mem_univ, if_true] at h
  have h2 := congrArg (fun x => x.coeff nu) h
  simp only [← zsmul_eq_mul', ← zsmul_eq_mul, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, AddMonoidAlgebra.coeff_single, Finsupp.single_apply,
    smul_eq_mul] at h2
  have hp : ∀ i k, prMu M nu i k = (evGL (torusPt n) (M.A i k)).coeff nu := fun _ _ => rfl
  simp only [hp]
  rw [mul_ite, mul_one, mul_zero] at h2
  rw [← h2]
  exact sum_congr rfl fun k _ => mul_comm _ _

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

-- bundled from Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.LaplaceExpansionColumn
section
noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ}

def ql_sr (R : Type*) [CommRing R] (A K : Finset (Fin n)) : R :=
  ∏ a ∈ A, ∏ k ∈ K, (if k < a then (-1 : R) else 1)

def wedgeSign (R : Type*) [CommRing R] (A K : Finset (Fin n)) : R := if Disjoint A K then ql_sr R A K else 0

def ql_w (R : Type*) [CommRing R] (A K I : Finset (Fin n)) : R := if A ∪ K = I then wedgeSign R A K else 0

variable {R : Type*} [CommRing R]

lemma ql_sr_union_left {A B : Finset (Fin n)} (h : Disjoint A B) (C : Finset (Fin n)) :
    ql_sr R (A ∪ B) C = ql_sr R A C * ql_sr R B C := prod_union h

lemma ql_sr_union_right (A : Finset (Fin n)) {B C : Finset (Fin n)} (h : Disjoint B C) :
    ql_sr R A (B ∪ C) = ql_sr R A B * ql_sr R A C := by
  simp only [ql_sr, prod_union h, prod_mul_distrib]

lemma ql_s_assoc (A B C : Finset (Fin n)) :
    wedgeSign R A B * wedgeSign R (A ∪ B) C = wedgeSign R B C * wedgeSign R A (B ∪ C) := by
  unfold wedgeSign
  by_cases hAB : Disjoint A B <;> by_cases hAC : Disjoint A C <;> by_cases hBC : Disjoint B C <;>
    simp only [disjoint_union_left, disjoint_union_right, hAB, hAC, hBC, if_true, if_false, and_true,
      and_false, and_self, mul_zero, zero_mul]
  rw [ql_sr_union_left hAB, ql_sr_union_right _ hBC]; ring

lemma ql_sr_single (A : Finset (Fin n)) (m : Fin n) : ql_sr R A {m} = ((qs_sg A m : ℤ) : R) := by
  simp only [ql_sr, prod_singleton, qs_sg]
  rw [prod_ite]; simp

lemma ql_sr_isUnit (A K : Finset (Fin n)) : IsUnit (ql_sr R A K) := by
  unfold ql_sr
  refine Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one fun a _ => ?_
  refine Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one fun k _ => ?_
  split_ifs
  · exact isUnit_one.neg
  · exact isUnit_one

lemma ql_s_isUnit {A K : Finset (Fin n)} (h : Disjoint A K) : IsUnit (wedgeSign R A K) := by
  rw [wedgeSign, if_pos h]; exact ql_sr_isUnit A K

lemma ql_sr_cast (A K : Finset (Fin n)) : ((ql_sr ℤ A K : ℤ) : R) = ql_sr R A K := by
  simp only [ql_sr, Int.cast_prod]
  refine prod_congr rfl fun a _ => prod_congr rfl fun k _ => ?_
  split_ifs <;> simp

lemma ql_s_cast (A K : Finset (Fin n)) : ((wedgeSign ℤ A K : ℤ) : R) = wedgeSign R A K := by
  unfold wedgeSign; split_ifs
  · exact ql_sr_cast A K
  · simp

lemma ql_w_cast (A K I : Finset (Fin n)) : ((ql_w ℤ A K I : ℤ) : R) = ql_w R A K I := by
  unfold ql_w; split_ifs
  · exact ql_s_cast A K
  · simp

lemma ql_sum_w (A K : Finset (Fin n)) (f : Finset (Fin n) → R) :
    ∑ I, f I * ql_w R A K I = wedgeSign R A K * f (A ∪ K) := by
  simp [ql_w, mul_comm]

lemma ql_w_assoc (A B C I : Finset (Fin n)) :
    ∑ M, ql_w R A B M * ql_w R M C I = ∑ M, ql_w R B C M * ql_w R A M I := by
  have h1 : ∑ M, ql_w R A B M * ql_w R M C I = wedgeSign R A B * ql_w R (A ∪ B) C I := by
    rw [← ql_sum_w A B (fun M => ql_w R M C I)]; exact sum_congr rfl fun _ _ => mul_comm _ _
  have h2 : ∑ M, ql_w R B C M * ql_w R A M I = wedgeSign R B C * ql_w R A (B ∪ C) I := by
    rw [← ql_sum_w B C (fun M => ql_w R A M I)]; exact sum_congr rfl fun _ _ => mul_comm _ _
  rw [h1, h2, ql_w, ql_w, union_assoc]
  split_ifs
  · exact ql_s_assoc A B C
  · simp

lemma ql_w_single (M I : Finset (Fin n)) (k : Fin n) :
    ql_w R M {k} I = if M = I.erase k then (if k ∈ I then ((qs_sg (I.erase k) k : ℤ) : R) else 0) else 0 := by
  by_cases hM : M = I.erase k
  · subst hM
    rw [if_pos rfl]
    by_cases hk : k ∈ I
    · have : I.erase k ∪ {k} = I := by
        rw [union_comm, ← insert_eq, insert_erase hk]
      rw [if_pos hk, ql_w, if_pos this, wedgeSign, if_pos (by simp), ql_sr_single]
    · rw [if_neg hk, ql_w, if_neg]
      intro h; exact hk (h ▸ mem_union_right _ (mem_singleton_self k))
  · rw [if_neg hM, ql_w]
    split_ifs with h
    · rw [wedgeSign, if_neg]
      intro hd
      apply hM
      rw [← h, union_comm, ← insert_eq, erase_insert (by simpa using hd)]
    · rfl

lemma sum_four_comm_form {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] (F : α → β → γ → δ → R) :
    ∑ a, ∑ b, ∑ c, ∑ d, F a b c d = ∑ c, ∑ d, ∑ b, ∑ a, F a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, F a b c d = ∑ a, ∑ c, ∑ b, ∑ d, F a b c d := sum_congr rfl fun a _ => sum_comm
    _ = ∑ c, ∑ a, ∑ b, ∑ d, F a b c d := sum_comm
    _ = ∑ c, ∑ a, ∑ d, ∑ b, F a b c d := sum_congr rfl fun c _ => sum_congr rfl fun a _ => sum_comm
    _ = ∑ c, ∑ d, ∑ a, ∑ b, F a b c d := sum_congr rfl fun c _ => sum_comm
    _ = ∑ c, ∑ d, ∑ b, ∑ a, F a b c d := sum_congr rfl fun c _ => sum_congr rfl fun d _ => sum_comm

variable (g : Matrix (Fin n) (Fin n) R)

lemma laplace_expansion_column (B I : Finset (Fin n)) (m : Fin n) :
    ∑ M, ∑ k, qs_mn g M B * g k m * ql_w R M {k} I = wedgeSign R B {m} * qs_mn g I (B ∪ {m}) := by
  rw [sum_comm]
  have h1 : ∀ k, ∑ M, qs_mn g M B * g k m * ql_w R M {k} I =
      if k ∈ I then ((qs_sg (I.erase k) k : ℤ) : R) * qs_mn g (I.erase k) B * g k m else 0 := by
    intro k
    simp only [ql_w_single, mul_ite, mul_zero, sum_ite_eq', mem_univ, if_true]
    split_ifs
    · ring
    · rfl
  simp only [h1]
  rw [sum_ite_mem, univ_inter, qs_laplace_col, wedgeSign]
  by_cases hm : m ∈ B
  · rw [if_pos hm, if_neg (by simpa using hm), zero_mul]
  · rw [if_neg hm, if_pos (by simpa using hm), ql_sr_single, union_comm, ← insert_eq]

lemma ql_mn_empty (K : Finset (Fin n)) : qs_mn g K ∅ = if K = ∅ then 1 else 0 := by
  split_ifs with h
  · subst h; rw [qs_mn_eq g ∅ ∅ (h := 0) rfl rfl]; simp
  · exact qs_mn_ne g (by simpa using h)

lemma ql_s_empty (A : Finset (Fin n)) : wedgeSign R A ∅ = 1 := by simp [wedgeSign, ql_sr]

lemma ql_s_max {K : Finset (Fin n)} {m : Fin n} (h : ∀ x ∈ K, x < m) : wedgeSign R K {m} = 1 := by
  rw [wedgeSign, if_pos (by simpa using fun hm => lt_irrefl _ (h m hm)), ql_sr]
  refine prod_eq_one fun a ha => ?_
  rw [prod_singleton, if_neg (not_lt.2 (h a ha).le)]

theorem ql_lap (A K I : Finset (Fin n)) :
    ∑ A', ∑ K', qs_mn g A' A * qs_mn g K' K * ql_w R A' K' I = wedgeSign R A K * qs_mn g I (A ∪ K) := by
  induction K using Finset.induction_on_max generalizing I with
  | empty =>
    simp only [ql_mn_empty, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, sum_ite_eq', mem_univ, if_true,
      ql_s_empty, one_mul, union_empty]
    simp [ql_w, ql_s_empty]
  | insert m K0 hmax ih =>
    have e1 : ∀ K', qs_mn g K' (insert m K0) = ∑ M, ∑ k, qs_mn g M K0 * g k m * ql_w R M {k} K' := by
      intro K'; rw [laplace_expansion_column, ql_s_max hmax, one_mul, union_comm, ← insert_eq]
    have h1 : ∀ A', ∑ K', qs_mn g A' A * qs_mn g K' (insert m K0) * ql_w R A' K' I =
        ∑ M, ∑ k, qs_mn g A' A * qs_mn g M K0 * g k m * ∑ K', ql_w R M {k} K' * ql_w R A' K' I := by
      intro A'
      simp only [e1, mul_sum, sum_mul]
      rw [sum_comm]; refine sum_congr rfl fun M _ => ?_
      rw [sum_comm]; exact sum_congr rfl fun k _ => sum_congr rfl fun K' _ => by ring
    have h2 : ∑ M', ∑ k, (∑ A', ∑ M, qs_mn g A' A * qs_mn g M K0 * ql_w R A' M M') * g k m * ql_w R M' {k} I =
        ∑ A', ∑ M, ∑ k, qs_mn g A' A * qs_mn g M K0 * g k m * ∑ M', ql_w R A' M M' * ql_w R M' {k} I := by
      simp only [mul_sum, sum_mul]
      rw [sum_four_comm_form]
      exact sum_congr rfl fun A' _ => sum_congr rfl fun M _ => sum_congr rfl fun k _ =>
        sum_congr rfl fun M' _ => by ring
    calc ∑ A', ∑ K', qs_mn g A' A * qs_mn g K' (insert m K0) * ql_w R A' K' I
        = ∑ A', ∑ M, ∑ k, qs_mn g A' A * qs_mn g M K0 * g k m * ∑ K', ql_w R M {k} K' * ql_w R A' K' I :=
          sum_congr rfl fun A' _ => h1 A'
      _ = ∑ A', ∑ M, ∑ k, qs_mn g A' A * qs_mn g M K0 * g k m * ∑ M', ql_w R A' M M' * ql_w R M' {k} I :=
          sum_congr rfl fun A' _ => sum_congr rfl fun M _ => sum_congr rfl fun k _ => by rw [ql_w_assoc]
      _ = ∑ M', ∑ k, (wedgeSign R A K0 * qs_mn g M' (A ∪ K0)) * g k m * ql_w R M' {k} I := by
          rw [← h2]; simp only [ih]
      _ = wedgeSign R A K0 * ∑ M', ∑ k, qs_mn g M' (A ∪ K0) * g k m * ql_w R M' {k} I := by
          simp only [mul_sum, mul_assoc]
      _ = wedgeSign R A (insert m K0) * qs_mn g I (A ∪ insert m K0) := by
          rw [laplace_expansion_column, ← mul_assoc, ql_s_assoc, ql_s_max hmax, one_mul, union_assoc, union_comm K0, ← insert_eq]

theorem ql_lapT (A K I : Finset (Fin n)) :
    ∑ A', ∑ K', qs_mn g A A' * qs_mn g K K' * ql_w R A' K' I = ∑ I', ql_w R A K I' * qs_mn g I' I := by
  have h := ql_lap g.transpose A K I
  simp only [qs_mn_transpose] at h
  rw [h, ← ql_sum_w A K (fun I' => qs_mn g I' I)]
  exact sum_congr rfl fun _ _ => mul_comm _ _

theorem ql_lapM (A K I : Finset (Fin n)) :
    ∑ A', ∑ K', qs_mn g A' A * qs_mn g K' K * ql_w R A' K' I = ∑ I', qs_mn g I I' * ql_w R A K I' := by
  rw [ql_lap, ql_sum_w A K (fun I' => qs_mn g I I')]

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

-- bundled from Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QcColHSuccLe
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

lemma qc_colH_succ_le {n : ℕ} (mu : Fin n → ℤ) (c : ℤ) : colH mu (c + 1) ≤ colH mu c := by
  apply Finset.card_le_card
  intro m hm
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm ⊢
  omega

lemma qc_canT_std {n : ℕ} [NeZero n] (mu : Fin n → ℤ) : StdT (canT mu) := by
  intro c hc t
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  intro x hx
  simp only [canT, Finset.mem_map, Finset.mem_univ, true_and] at hx ⊢
  obtain ⟨a, rfl⟩ := hx
  exact ⟨⟨a.1, lt_of_lt_of_le a.2 (qc_colH_succ_le mu c)⟩, rfl⟩

section SMu

variable {n : ℕ} [NeZero n] {M : GLMod n} {mu : Fin n → ℤ} {β : M.ι → GLCoord ℤ n}

lemma qc_prim (hS : SBasis) (hmu : Dominant mu) (hβ : IsSMu M mu β)
    (ph : Matrix M.ι (TIdx mu) ℤ) (hph : ∀ I, ∑ i, ph i I • β i = brk mu I) (m : ℤ)
    (hm : ∀ i, m ∣ ph i (canT mu)) : m ∣ 1 := by
  classical
  have : Fintype {I : TIdx mu // StdT I} := Fintype.ofFinite _
  choose q hq using hm
  have hy : ∑ i, q i • β i ∈ Submodule.span ℤ (Set.range fun I : {I : TIdx mu // StdT I} => brk mu I.1) := by
    rw [(hS n mu hmu).2, ← hβ.2.1]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hy
  have hcan : brk mu (canT mu) = m • ∑ i, q i • β i := by
    rw [← hph]
    simp only [zsmul_eq_mul, Finset.mul_sum, hq, Int.cast_mul, mul_assoc]
  let c0 : {I : TIdx mu // StdT I} := ⟨canT mu, qc_canT_std mu⟩
  have h0 : ∑ I : {I : TIdx mu // StdT I}, ((if I = c0 then 1 else 0) - m * r I) • brk mu I.1 = 0 := by
    have h2 : ∀ I : {I : TIdx mu // StdT I}, ((if I = c0 then 1 else 0) - m * r I) • brk mu I.1 =
        (if I = c0 then brk mu I.1 else 0) - (m : GLCoord ℤ n) * (r I • brk mu I.1) := by
      intro I
      split_ifs <;> simp [zsmul_eq_mul, sub_mul, mul_assoc]
    simp only [h2, Finset.sum_sub_distrib, ← Finset.mul_sum, hr, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [sub_eq_zero, ← zsmul_eq_mul]
    exact hcan
  have h1 := Fintype.linearIndependent_iff.1 (hS n mu hmu).1 _ h0 c0
  simp only [if_true] at h1
  exact ⟨r c0, by linarith⟩

theorem qc_colFam_SMu (hA : LemmaA) (hS : SBasis) (hmu : Dominant mu) (hβ : IsSMu M mu β) :
    Nonempty (ColFam M) := by
  classical
  have hex : ∀ I : TIdx mu, ∃ c : M.ι → ℤ, ∑ i, c i • β i = brk mu I := fun I =>
    (Submodule.mem_span_range_iff_exists_fun ℤ).1 (by rw [hβ.2.1]; exact Submodule.subset_span ⟨I, rfl⟩)
  choose c hc using hex
  let ph : Matrix M.ι (TIdx mu) ℤ := fun i I => c I i
  have hph : ∀ I, ∑ i, ph i I • β i = brk mu I := hc
  have hpr := qc_prim hS hmu hβ ph hph
  refine ⟨{ J := Unit, mu := fun _ => mu, dom := fun _ => hmu, ph := fun _ => ph,
            equiv := fun _ => qc_equiv hA hS hmu hβ ph hph, indepP := ?_, indepQ := ?_, rank := ?_ }⟩
  · intro p hp nu
    have := Fact.mk hp
    rw [linearIndependent_subsingleton_index_iff]
    intro j h0
    have h1 := hpr (p : ℤ) fun i => (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 (congrFun h0 i)
    have h2 : p ∣ 1 := by exact_mod_cast h1
    exact hp.one_lt.ne' (Nat.dvd_one.1 h2)
  · intro nu
    rw [linearIndependent_subsingleton_index_iff]
    intro j h0
    have h1 := hpr 0 fun i => by
      have := congrFun h0 i
      simp only [Pi.zero_apply, Int.cast_eq_zero] at this
      rw [this]
    simp at h1
  · simp [qc_card_eq hS hmu hβ]

end SMu

theorem qc_colFam_triv {n : ℕ} [NeZero n] (M : GLMod n) (h1 : Fintype.card M.ι = 1) (hA : ∀ i j, M.A i j = 1) :
    Nonempty (ColFam M) := by
  classical
  have hE : IsEmpty ↥(TCols (0 : Fin n → ℤ)) :=
    ⟨fun x => by simpa [TCols] using x.2⟩
  obtain ⟨i0, hi0⟩ := Fintype.card_eq_one_iff.1 h1
  have hU : Unique M.ι := ⟨⟨i0⟩, hi0⟩
  refine ⟨{ J := Unit, mu := fun _ => 0, dom := fun _ => fun _ _ _ => le_rfl, ph := fun _ => fun _ _ => 1,
            equiv := ?_, indepP := ?_, indepQ := ?_, rank := ?_ }⟩
  · intro _
    ext i I
    show (∑ k, M.A i k * (Int.castRingHom (GLCoord ℤ n)) 1) =
      ∑ K : TIdx (0 : Fin n → ℤ), (Int.castRingHom (GLCoord ℤ n)) 1 * TMat 0 K I
    simp [hA, TMat]
  · intro p hp nu
    have := Fact.mk hp
    rw [linearIndependent_subsingleton_index_iff]
    intro j h0
    simpa using congrFun h0 i0
  · intro nu
    rw [linearIndependent_subsingleton_index_iff]
    intro j h0
    simpa using congrFun h0 i0
  · have : Unique {I : TIdx (0 : Fin n → ℤ) // StdT I} :=
      ⟨⟨⟨canT 0, qc_canT_std 0⟩⟩, fun I => Subtype.ext (Subsingleton.elim _ _)⟩
    simp [h1, dMu]

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

