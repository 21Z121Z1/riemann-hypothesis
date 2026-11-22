import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantMetricIsometry.ColChoiceFintype
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MonomialFrameSpan.DetSubmatrixFun

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantMetricIsometry.MetricConstantBound
section
noncomputable section

open Matrix Finset

namespace PI.IsoInvMetricW

theorem metric_constant_bound : CB := by
  intro h N A B
  classical
  rw [GenFrameSpan.det_mul_rect]
  have hR : ∀ J : Fin h ↪o Fin N, (A.submatrix id J).det * (B.submatrix J id).det
      = ∑ σ : Equiv.Perm (Fin h), (∏ i, B (J (σ i)) i) * (A.submatrix id (J ∘ σ)).det := by
    intro J
    rw [det_apply (B.submatrix J id), Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have hA : A.submatrix id (J ∘ σ) = (A.submatrix id J).submatrix id σ := by
      ext i k; simp
    rw [hA, det_permute']
    simp only [Units.smul_def, zsmul_eq_mul, submatrix_apply, id]
    ring
  rw [Finset.sum_congr rfl (fun J _ => hR J), ← Fintype.sum_prod_type']
  symm
  refine Finset.sum_bij_ne_zero (fun p _ _ => (p.1 : Fin h → Fin N) ∘ p.2)
    (fun _ _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ _ => rfl)
  · rintro ⟨J, σ⟩ _ _ ⟨J', σ'⟩ _ _ heq
    have hr : Set.range J = Set.range J' := by
      have h1 : Set.range ((J : Fin h → Fin N) ∘ σ) = Set.range J :=
        σ.surjective.range_comp _
      have h2 : Set.range ((J' : Fin h → Fin N) ∘ σ') = Set.range J' :=
        σ'.surjective.range_comp _
      rw [← h1, ← h2]
      exact congrArg Set.range heq
    have hJ : J = J' := OrderEmbedding.range_inj.mp hr
    subst hJ
    have hσ : σ = σ' := by
      ext i
      have := congrFun heq i
      simp only [Function.comp_apply] at this
      rw [J.injective this]
    rw [hσ]
  · intro f _ hf
    have hinj : Function.Injective f := by
      by_contra hni
      apply hf
      have : ∃ i j, f i = f j ∧ i ≠ j := by
        by_contra hc
        push Not at hc
        exact hni fun i j e => hc i j e
      obtain ⟨i, j, hij, hne⟩ := this
      rw [Matrix.det_zero_of_column_eq hne (by intro r; simp [hij]), mul_zero]
    set s : Finset (Fin N) := Finset.univ.image f with hs
    have hcard : s.card = h := by
      rw [hs, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    have hmem : ∀ i, f i ∈ s := fun i => Finset.mem_image_of_mem f (Finset.mem_univ i)
    let g : Fin h → Fin h := fun i => (s.orderIsoOfFin hcard).symm ⟨f i, hmem i⟩
    have hg : ∀ i, s.orderEmbOfFin hcard (g i) = f i := by
      intro i
      rw [← Finset.coe_orderIsoOfFin_apply]
      simp [g]
    have ginj : Function.Injective g := by
      intro i j e
      apply hinj
      rw [← hg i, ← hg j, e]
    let σ : Equiv.Perm (Fin h) := Equiv.ofBijective g (Finite.injective_iff_bijective.mp ginj)
    refine ⟨(s.orderEmbOfFin hcard, σ), Finset.mem_univ _, ?_, ?_⟩
    · have hfi : ∀ i, (s.orderEmbOfFin hcard) (σ i) = f i := fun i => by simp [σ, hg]
      have : ((s.orderEmbOfFin hcard : Fin h ↪o Fin N) : Fin h → Fin N) ∘ σ = f := by
        funext i; exact hfi i
      rw [this]; dsimp only; simp only [hfi]; exact hf
    · funext i; simp [σ, hg]

end PI.IsoInvMetricW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantMetricIsometry.OeEqOfRangeSub
section
noncomputable section

open Matrix Classical

namespace PI.IsoInvMetricW

open PI.IsoInvMetric

theorem oe_eq_of_range_sub {h N : ℕ} (I J : Fin h ↪o Fin N) (hs : ∀ i, ∃ k, J k = I i) :
    I = J := by
  classical
  have h1 : Finset.univ.image I ⊆ Finset.univ.image J := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx ⊢
    obtain ⟨i, rfl⟩ := hx
    exact hs i
  have h2 : Finset.univ.image I = Finset.univ.image J :=
    Finset.eq_of_subset_of_card_le h1 (by
      rw [Finset.card_image_of_injective _ J.injective,
        Finset.card_image_of_injective _ I.injective])
  apply OrderEmbedding.range_inj.mp
  have := congrArg (fun s : Finset (Fin N) => (s : Set (Fin N))) h2
  simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ] using this

theorem metric_diagonal : EDiag := by
  intro Lt _ _ N nu d I J
  unfold E
  split_ifs with hIJ
  · subst hIJ
    refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => ?_
    have : (Matrix.of fun i k : Fin ((nu s).colLen c) =>
        Matrix.diagonal (d s) (I s c i) (I s c k)) = Matrix.diagonal (fun i => d s (I s c i)) := by
      ext i k
      simp [Matrix.diagonal_apply, (I s c).injective.eq_iff]
    rw [this, Matrix.det_diagonal]
  · have : ∃ s c, I s c ≠ J s c := by
      by_contra hne
      push_neg at hne
      exact hIJ (funext fun s => funext fun c => hne s c)
    obtain ⟨s, c, hsc⟩ := this
    have : ∃ i, ∀ k, J s c k ≠ I s c i := by
      by_contra hne
      push_neg at hne
      exact hsc (oe_eq_of_range_sub _ _ hne)
    obtain ⟨i, hi⟩ := this
    apply Finset.prod_eq_zero (Finset.mem_univ s)
    apply Finset.prod_eq_zero (Finset.mem_univ c)
    apply Matrix.det_eq_zero_of_row_eq_zero i
    intro k
    simp [Matrix.diagonal_apply_ne _ (hi k).symm]

def J0 {Lt : Type} {N : ℕ} (nu : Lt → YoungDiagram) (hle : ∀ z, (nu z).colLen 0 ≤ N) :
    ColChoice N nu :=
  fun s c => Fin.castLEOrderEmb (le_trans ((nu s).colLen_anti 0 c (Nat.zero_le _)) (hle s))

theorem unitVector_val_eq {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N : ℕ} (nu : Lt → YoungDiagram)
    (hle : ∀ z, (nu z).colLen 0 ≤ N) (J : ColChoice N nu) :
    u0 N nu J = if J = J0 nu hle then 1 else 0 := by
  have e : u0 N nu J = E nu (fun _ => Matrix.diagonal (fun _ => (1 : ℂ))) J (J0 nu hle) := by
    unfold u0 hvC minY E
    refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => ?_
    congr 1
    ext i k
    have hk : (k : ℕ) < N := lt_of_lt_of_le k.2
      (le_trans ((nu s).colLen_anti 0 c (Nat.zero_le _)) (hle s))
    simp only [Matrix.of_apply, colsOf, hk, dite_true, Matrix.diagonal_one, J0]
    rfl
  rw [e, metric_diagonal]
  split_ifs <;> simp

theorem norm1' : Norm1 := by
  intro Lt _ _ N nu hle
  unfold l2
  rw [finsum_eq_sum_of_fintype]
  simp [unitVector_val_eq nu hle, apply_ite (fun x : ℂ => ‖x‖ ^ 2)]

end PI.IsoInvMetricW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantMetricIsometry.QuotientRank
section
noncomputable section

open Matrix

namespace PI.IsoInvMetricW

open InnerProductSpace

theorem quotient_rank : QR := by
  intro N X
  let f : Fin N → EuclideanSpace ℂ (Fin N) := fun j => (WithLp.equiv 2 _).symm (fun a => X a j)
  have hd : Module.finrank ℂ (EuclideanSpace ℂ (Fin N)) = Fintype.card (Fin N) := finrank_euclideanSpace
  let b := gramSchmidtOrthonormalBasis hd f
  let k : Matrix (Fin N) (Fin N) ℂ := Matrix.of fun a j => b j a
  have hinner : ∀ i j, ∑ a, star (b i a) * (f j) a = inner ℂ (b i) (f j) := by
    intro i j
    simp [PiLp.inner_apply, mul_comm]
  have hinner' : ∀ i j, ∑ a, star (b i a) * b j a = inner ℂ (b i) (b j) := by
    intro i j
    simp [PiLp.inner_apply, mul_comm]
  refine ⟨k, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff']
    ext i j
    have ho := orthonormal_iff_ite.mp b.orthonormal i j
    simp only [Matrix.mul_apply, Matrix.star_apply, k, Matrix.of_apply, Matrix.one_apply]
    rw [hinner', ho]
  · intro a j hja
    have := gramSchmidtOrthonormalBasis_inv_triangular hd f hja
    simp only [Matrix.mul_apply, Matrix.star_apply, k, Matrix.of_apply]
    rw [← this, ← hinner]
    rfl

end PI.IsoInvMetricW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantMetricIsometry.SymmetricMeasureL2NormEqResolutionL2
section
noncomputable section

open Matrix

namespace PI.IsoInvMetricW

open PI.IsoInvMetric

variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N : ℕ} {nu : Lt → YoungDiagram}

theorem symmetricMeasure_l2Norm_eq_resolutionL2 (φ : LaC N nu) : ((l2 φ : ℝ) : ℂ) = ipl φ φ := by
  unfold l2 ipl
  rw [finsum_eq_sum_of_fintype]
  push_cast
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [Complex.star_def, Complex.conj_mul']

theorem ipl_zero_left (ψ : LaC N nu) : ipl 0 ψ = 0 := by
  simp [ipl]

theorem ipl_add_left (φ φ' ψ : LaC N nu) : ipl (φ + φ') ψ = ipl φ ψ + ipl φ' ψ := by
  simp [ipl, add_mul, Finset.sum_add_distrib]

theorem ipl_smul_left (c : ℂ) (φ ψ : LaC N nu) : ipl (c • φ) ψ = starRingEnd ℂ c * ipl φ ψ := by
  simp [ipl, Finset.mul_sum, mul_assoc]

theorem isoInvMetric_of (hU : Unit) (hI : InvK) (hS : Stab) (hH : HvCols) (hN : Norm1)
    (hG : Gen) (hW : HW) : IsoInvMetric := by
  intro Lt _ _ N nu
  refine ⟨fun k hk => ⟨fun φ hφ => ⟨hS Lt N nu k φ hφ, ?_⟩, fun hle => ?_⟩, fun ip hip => ?_⟩
  · apply Complex.ofReal_injective
    rw [symmetricMeasure_l2Norm_eq_resolutionL2, symmetricMeasure_l2Norm_eq_resolutionL2, hU Lt N nu k hk]
  · rw [hH Lt N nu k]
    apply Complex.ofReal_injective
    rw [symmetricMeasure_l2Norm_eq_resolutionL2, hU Lt N nu k hk, ← symmetricMeasure_l2Norm_eq_resolutionL2, hN Lt N nu hle]
  · have hu : u0 N nu ∈ Vnu N nu := Submodule.subset_span ⟨_, rfl⟩
    have key : ∀ φ ∈ Vnu N nu, ∀ ψ ∈ Vnu N nu, ip φ ψ = ipl φ ψ := by
      intro φ hφ ψ hψ
      induction hφ using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨y, rfl⟩ := hx
        obtain ⟨k, hk, c, hc⟩ := hG Lt N nu y
        obtain ⟨ψ', hψ', e1⟩ : ∃ ψ', ψ' ∈ Vnu N nu ∧ ψ = VnuMap nu k ψ' :=
          ⟨_, hS Lt N nu _ ψ hψ, (hI Lt N nu k hk ψ).symm⟩
        have h2 : ip (VnuMap nu k (u0 N nu)) (VnuMap nu k ψ') =
            ipl (VnuMap nu k (u0 N nu)) (VnuMap nu k ψ') := by
          rw [(hip k hk).1 _ hu _ hψ', hW Lt N nu ip hip ψ' hψ', hU Lt N nu k hk]
        rw [hc, hH Lt N nu k, LinearMap.map_smulₛₗ₂, ipl_smul_left, e1, h2, smul_eq_mul]
      | zero => simp [ipl_zero_left]
      | add x y _ _ hx hy => rw [LinearMap.map_add₂, hx, hy, ipl_add_left]
      | smul a x _ hx => rw [LinearMap.map_smulₛₗ₂, hx, ipl_smul_left, smul_eq_mul]
    intro φ hφ
    rw [symmetricMeasure_l2Norm_eq_resolutionL2]
    exact key φ hφ φ hφ

end PI.IsoInvMetricW
end
end

