import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantMetricIsometry.ColChoiceFintype
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantMetricIsometry.Bundle0001

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantMetricIsometry.HermitianVectorMap
section
noncomputable section

open Matrix Finset PI.IsoInvMetric

namespace PI.IsoInvMetricW

theorem sum_prod_cc {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N : ℕ} {nu : Lt → YoungDiagram}
    (F : ∀ (s : Lt) (c : Fin ((nu s).rowLen 0)), (Fin ((nu s).colLen c) ↪o Fin N) → ℂ) :
    ∑ J : ColChoice N nu, ∏ s, ∏ c, F s c (J s c) = ∏ s, ∏ c, ∑ K, F s c K := by
  simp_rw [Fintype.prod_sum]
  rfl

theorem hermitian_vector_map : HvMap := by
  intro Lt _ _ N nu f x
  funext I
  simp only [VnuMap, hvC, minY, fr]
  rw [finsum_eq_sum_of_fintype]
  simp_rw [← Finset.prod_mul_distrib]
  refine (sum_prod_cc (fun s c K =>
      (Matrix.of fun i k : Fin ((nu s).colLen c) => f s (I s c i) (K k)).det *
      (Matrix.of fun i j : Fin ((nu s).colLen c) => x s (K i) (j : ℕ)).det)).trans ?_
  refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => ?_
  have hcb := metric_constant_bound _ _ (Matrix.of fun (i : Fin ((nu s).colLen c)) (b : Fin N) => f s (I s c i) b)
    (Matrix.of fun (b : Fin N) (j : Fin ((nu s).colLen c)) => x s b (j : ℕ))
  calc _ = ∑ K : Fin ((nu s).colLen c) ↪o Fin N,
        ((Matrix.of fun (i : Fin ((nu s).colLen c)) (b : Fin N) => f s (I s c i) b).submatrix id K).det *
        ((Matrix.of fun (b : Fin N) (j : Fin ((nu s).colLen c)) => x s b (j : ℕ)).submatrix K id).det := rfl
    _ = _ := hcb.symm
    _ = _ := by
      congr 1

theorem metric_mul : EMul := by
  intro Lt _ _ N nu f g I K
  simp only [E]
  simp_rw [← Finset.prod_mul_distrib]
  refine (sum_prod_cc (fun s c J =>
      (Matrix.of fun i k : Fin ((nu s).colLen c) => f s (I s c i) (J k)).det *
      (Matrix.of fun i k : Fin ((nu s).colLen c) => g s (J i) (K s c k)).det)).trans ?_
  refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => ?_
  have hcb := metric_constant_bound _ _ (Matrix.of fun (i : Fin ((nu s).colLen c)) (b : Fin N) => f s (I s c i) b)
    (Matrix.of fun (b : Fin N) (k : Fin ((nu s).colLen c)) => g s b (K s c k))
  calc _ = ∑ J : Fin ((nu s).colLen c) ↪o Fin N,
        ((Matrix.of fun (i : Fin ((nu s).colLen c)) (b : Fin N) => f s (I s c i) b).submatrix id J).det *
        ((Matrix.of fun (b : Fin N) (k : Fin ((nu s).colLen c)) => g s b (K s c k)).submatrix J id).det := rfl
    _ = _ := hcb.symm
    _ = _ := by
      congr 1

end PI.IsoInvMetricW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantMetricIsometry.VnuMapZero
section
noncomputable section

open Matrix Classical

namespace PI.IsoInvMetricW

open PI.IsoInvMetric

section
variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N : ℕ} {nu : Lt → YoungDiagram}

theorem vnuMap_eq (f : Lt → Matrix (Fin N) (Fin N) ℂ) (φ : LaC N nu) (I : ColChoice N nu) :
    VnuMap nu f φ I = ∑ J, E nu f I J * φ J := by
  unfold VnuMap
  rw [finsum_eq_sum_of_fintype]
  rfl

theorem vnuMap_add (f : Lt → Matrix (Fin N) (Fin N) ℂ) (φ ψ : LaC N nu) :
    VnuMap nu f (φ + ψ) = VnuMap nu f φ + VnuMap nu f ψ := by
  funext I
  simp only [vnuMap_eq, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem vnuMap_smul (f : Lt → Matrix (Fin N) (Fin N) ℂ) (a : ℂ) (φ : LaC N nu) :
    VnuMap nu f (a • φ) = a • VnuMap nu f φ := by
  funext I
  simp only [vnuMap_eq, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun J _ => by ring

theorem vnuMap_zero (f : Lt → Matrix (Fin N) (Fin N) ℂ) : VnuMap nu f (0 : LaC N nu) = 0 := by
  funext I
  simp [vnuMap_eq]

theorem eStar (k : Lt → Matrix (Fin N) (Fin N) ℂ) (I J : ColChoice N nu) :
    starRingEnd ℂ (E nu k I J) = E nu (fun s => star (k s)) J I := by
  unfold E
  simp only [map_prod]
  refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => ?_
  rw [starRingEnd_apply, ← Matrix.det_conjTranspose]
  congr 1

theorem e_one (g : Lt → Matrix (Fin N) (Fin N) ℂ) (hg : ∀ s, g s = 1) (I J : ColChoice N nu) :
    E nu g I J = if I = J then 1 else 0 := by
  have : g = fun s => Matrix.diagonal (fun _ => (1 : ℂ)) := by
    funext s
    rw [hg, Matrix.diagonal_one]
  rw [this, metric_diagonal]
  split_ifs <;> simp
end

theorem stab_of (hM : HvMap) : Stab := by
  intro Lt _ _ N nu f φ hφ
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, rfl⟩ := hx
    rw [hM]
    exact Submodule.subset_span ⟨_, rfl⟩
  | zero => rw [vnuMap_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [vnuMap_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [vnuMap_smul]; exact Submodule.smul_mem _ a hx

theorem hvCols_of (hM : HvMap) : HvCols := by
  intro Lt _ _ N nu k
  unfold u0
  rw [hM]
  congr 1
  funext s a j
  unfold fr colsOf
  by_cases hj : j < N
  · simp [hj, Matrix.one_apply]
  · simp [hj]

theorem unit_of (hE : EMul) : Unit := by
  intro Lt _ _ N nu k hk φ ψ
  have hkk : ∀ z, star (k z) * k z = 1 := fun z => Matrix.mem_unitaryGroup_iff'.mp (hk z)
  have h1 : ∀ J J' : ColChoice N nu,
      ∑ I, starRingEnd ℂ (E nu k I J) * E nu k I J' = if J = J' then 1 else 0 := by
    intro J J'
    simp only [eStar]
    rw [hE]
    exact e_one _ hkk J J'
  have step : ∀ J J' : ColChoice N nu, ∑ I, star (E nu k I J * φ J) * (E nu k I J' * ψ J') =
      star (φ J) * ψ J' * (if J = J' then 1 else 0) := by
    intro J J'
    rw [← h1 J J', Finset.mul_sum]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [star_mul', starRingEnd_apply]
    ring
  unfold ipl
  simp only [vnuMap_eq]
  calc ∑ I, star (∑ J, E nu k I J * φ J) * ∑ J', E nu k I J' * ψ J'
      = ∑ I, ∑ J, ∑ J', star (E nu k I J * φ J) * (E nu k I J' * ψ J') := by
        refine Finset.sum_congr rfl fun I _ => ?_
        rw [star_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun J _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ J, ∑ J', ∑ I, star (E nu k I J * φ J) * (E nu k I J' * ψ J') := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun J _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ J, star (φ J) * ψ J := by
        refine Finset.sum_congr rfl fun J _ => ?_
        simp only [step, mul_ite, mul_one, mul_zero]
        rw [Finset.sum_ite_eq]
        simp

theorem invK_of (hE : EMul) : InvK := by
  intro Lt _ _ N nu k hk φ
  have hkk : ∀ z, k z * star (k z) = 1 := fun z => Matrix.mem_unitaryGroup_iff.mp (hk z)
  funext I
  have h1 : ∀ K, ∑ J, E nu k I J * E nu (fun z => star (k z)) J K = if I = K then 1 else 0 := by
    intro K
    rw [hE]
    exact e_one _ hkk I K
  simp only [vnuMap_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [← mul_assoc, ← Finset.sum_mul, h1, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp

end PI.IsoInvMetricW
end
end

