import Mathlib

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TransferIndices.AsAlgebraHomMemSpan
section
noncomputable section

namespace PI.Dv.TIW

section Span

variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G] {W : Type} [AddCommGroup W] [Module K W]
  [FiniteDimensional K W]

theorem exists_dual_one (w : W) (hw : w ≠ 0) : ∃ φ : Module.Dual K W, φ w = 1 := by
  by_contra h
  push_neg at h
  apply hw
  rw [← Module.forall_dual_apply_eq_zero_iff K w]
  intro φ
  by_contra hφ
  exact h ((φ w)⁻¹ • φ) (by simp [inv_mul_cancel₀ hφ])

theorem asAlgebraHom_mem_span (τ : Representation K G W) (z : MonoidAlgebra K G) (w : W) :
    τ.asAlgebraHom z w ∈ Submodule.span K (Set.range fun x => τ x w) := by
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, LinearMap.add_apply]; exact add_mem ha hb
  | single x r =>
    rw [Representation.asAlgebraHom_single, LinearMap.smul_apply]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)

theorem exists_end_map (w u : W) (hw : w ≠ 0) : ∃ M : Module.End K W, M w = u := by
  obtain ⟨φ, hφ⟩ := exists_dual_one (K := K) w hw
  exact ⟨φ.smulRight u, by rw [LinearMap.smulRight_apply, hφ, one_smul]⟩

theorem span_orbit (τ : Representation K G W) (hirr : Function.Surjective τ.asAlgebraHom) (w : W) (hw : w ≠ 0) :
    Submodule.span K (Set.range fun x => τ x w) = ⊤ := by
  rw [eq_top_iff]
  intro u _
  obtain ⟨M, hM⟩ := exists_end_map (K := K) w u hw
  obtain ⟨z, hz⟩ := hirr M
  have := asAlgebraHom_mem_span τ z w
  rwa [hz, hM] at this

theorem finrank_le_card (τ : Representation K G W) (hirr : Function.Surjective τ.asAlgebraHom)
    [Nontrivial W] : Module.finrank K W ≤ Fintype.card G := by
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  rw [← finrank_top, ← span_orbit τ hirr w hw]
  exact finrank_range_le_card _

end Span

section Select

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem select_li {ι : Type} (F : ι → V) (hF : Submodule.span K (Set.range F) = ⊤) :
    ∃ g : Fin (Module.finrank K V) → ι, LinearIndependent K (F ∘ g) := by
  obtain ⟨κ, a, -, hsp, hli⟩ := exists_linearIndependent'.{0} K F
  rw [hF] at hsp
  let b := Module.Basis.mk hli (by rw [hsp])
  letI := FiniteDimensional.fintypeBasisIndex b
  have hc : Fintype.card κ = Module.finrank K V := (Module.finrank_eq_card_basis b).symm
  let e := Fintype.equivFinOfCardEq hc
  refine ⟨a ∘ e.symm, ?_⟩
  have := hli.comp e.symm e.symm.injective
  simpa [Function.comp_assoc] using this

theorem li_span_top {n : ℕ} (u : Fin n → V) (hu : LinearIndependent K u) (hn : n = Module.finrank K V) :
    Submodule.span K (Set.range u) = ⊤ := by
  have h := linearIndependent_iff_card_eq_finrank_span.mp hu
  apply Submodule.eq_top_of_finrank_eq
  show Set.finrank K (Set.range u) = _
  rw [← h, Fintype.card_fin, hn]

theorem dual_span {ι : Type} (ψ : ι → Module.Dual K V) (h : ∀ v, (∀ i, ψ i v = 0) → v = 0) :
    Submodule.span K (Set.range ψ) = ⊤ := by
  by_contra hne
  obtain ⟨f, hf0, hle⟩ := (Submodule.span K (Set.range ψ)).exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr hne)
  set v := (Module.evalEquiv K V).symm f with hvd
  have hv : ∀ φ : Module.Dual K V, f φ = φ v := by
    intro φ
    have : Module.evalEquiv K V v = f := by rw [hvd, LinearEquiv.apply_symm_apply]
    rw [← this]
    rfl
  have hv0 : v = 0 := h v (fun i => by rw [← hv]; exact hle (Submodule.subset_span ⟨i, rfl⟩))
  apply hf0
  ext φ
  rw [hv, hv0, map_zero]
  rfl

end Select

end PI.Dv.TIW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TransferIndices.GrpNorm
section
noncomputable section

namespace PI.Dv.TIW

open Matrix

theorem root_pow_eq_one {d : Type} [Fintype d] [DecidableEq d] (M : Matrix d d ℂ) (m : ℕ) (hM : M ^ m = 1)
    (μ : ℂ) (hμ : μ ∈ M.charpoly.roots) : μ ^ m = 1 := by
  have hroot : M.charpoly.IsRoot μ := (Polynomial.mem_roots (Matrix.charpoly_monic M).ne_zero).mp hμ
  rw [Polynomial.IsRoot, Matrix.eval_charpoly] at hroot
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hroot
  have hMv : M *ᵥ v = μ • v := by
    rw [Matrix.sub_mulVec, sub_eq_zero] at hv
    rw [← hv]
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal, funext_iff, Pi.smul_apply, smul_eq_mul]
  have hpow : ∀ k : ℕ, (M ^ k) *ᵥ v = μ ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, hMv, Matrix.mulVec_smul, ih, smul_smul, pow_succ, mul_comm]
  have := hpow m
  rw [hM, Matrix.one_mulVec] at this
  have h2 : (μ ^ m - 1) • v = 0 := by rw [sub_smul, one_smul, ← this, sub_self]
  rcases smul_eq_zero.mp h2 with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hv0

theorem trace_finite_order {d : Type} [Fintype d] [DecidableEq d] (M : Matrix d d ℂ) (m : ℕ) (hm : 0 < m)
    (hM : M ^ m = 1) : ‖M.trace‖ ≤ Fintype.card d ∧ IsIntegral ℤ M.trace := by
  rw [Matrix.trace_eq_sum_roots_charpoly]
  have hroots : ∀ μ ∈ M.charpoly.roots, μ ^ m = 1 := root_pow_eq_one M m hM
  constructor
  · calc ‖M.charpoly.roots.sum‖ ≤ (M.charpoly.roots.map norm).sum := norm_multiset_sum_le _
      _ = (M.charpoly.roots.map (fun _ => (1 : ℝ))).sum := by
          congr 1
          exact Multiset.map_congr rfl fun μ hμ => Complex.norm_eq_one_of_pow_eq_one (hroots μ hμ) hm.ne'
      _ = Multiset.card M.charpoly.roots := by simp
      _ ≤ M.charpoly.natDegree := by exact_mod_cast Polynomial.card_roots' _
      _ = Fintype.card d := by rw [Matrix.charpoly_natDegree_eq_dim]
  · have : ∀ μ ∈ M.charpoly.roots, μ ∈ integralClosure ℤ ℂ := fun μ hμ =>
      IsIntegral.of_pow hm (by rw [hroots μ hμ]; exact isIntegral_one)
    exact Subalgebra.multiset_sum_mem _ this

theorem trace_end_finite_order {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (f : Module.End K W) (m : ℕ) (hm : 0 < m) (hf : f ^ m = 1) (σ : K →+* ℂ) :
    ‖σ (LinearMap.trace K W f)‖ ≤ Module.finrank K W ∧ IsIntegral ℤ (LinearMap.trace K W f) := by
  set b := Module.finBasis K W
  set A := LinearMap.toMatrixAlgEquiv b f with hA
  have htr : LinearMap.trace K W f = A.trace := by
    rw [LinearMap.trace_eq_matrix_trace K b f, hA]; rfl
  have hAm : A ^ m = 1 := by rw [hA, ← map_pow, hf, map_one]
  set B := σ.mapMatrix A with hB
  have hBm : B ^ m = 1 := by rw [hB, ← map_pow, hAm, map_one]
  have hσtr : σ (A.trace) = B.trace := by
    simp [Matrix.trace, hB, map_sum]
  obtain ⟨h1, h2⟩ := trace_finite_order B m hm hBm
  rw [htr, hσtr]
  refine ⟨by simpa using h1, ?_⟩
  rw [← hσtr] at h2
  exact (isIntegral_algHom_iff σ.toIntAlgHom σ.injective).mp h2

end PI.Dv.TIW
end
end

