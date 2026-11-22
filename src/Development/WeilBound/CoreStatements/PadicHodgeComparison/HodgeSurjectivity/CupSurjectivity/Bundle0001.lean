import Mathlib

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CupSurjectivity.OntoLA
section
namespace CrystallineSemistableComparison.Onto

open scoped BigOperators

theorem onto_la {k0 L V J : Type*} [Field k0] [Field L] [AddCommGroup V] [Module k0 V]
    [FiniteDimensional k0 V] (F : J → V → L)
    (hInj : ∀ {k : ℕ} (b : Module.Basis (Fin k) k0 V) (z : Fin k → L),
      (∀ j, ∑ i, z i * F j (b i) = 0) → z = 0)
    {m : ℕ} (u : Fin m → V) (hu : LinearIndependent k0 u) (t : Fin m → L) :
    ∃ (S : Finset J) (c : J → L), ∀ s, ∑ j ∈ S, c j * F j (u s) = t s := by
  classical
  have hs : LinearIndepOn k0 id (Set.range u) := (linearIndepOn_id_range_iff hu.injective).2 hu
  let B := Module.Basis.extend hs
  have : Finite (hs.extend (Set.subset_univ _)) := Module.Finite.finite_basis B
  obtain ⟨k, ⟨eqv⟩⟩ := Finite.exists_equiv_fin (hs.extend (Set.subset_univ _))
  let b : Module.Basis (Fin k) k0 V := B.reindex eqv
  let e : Fin m → Fin k := fun s => eqv ⟨u s, hs.subset_extend _ ⟨s, rfl⟩⟩
  have hbe : ∀ s, b (e s) = u s := by
    intro s
    simp [b, e, B, Module.Basis.reindex_apply, Module.Basis.extend_apply_self]
  have he : Function.Injective e := by
    intro s s' h
    apply hu.injective
    rw [← hbe s, ← hbe s', h]
  let vec : J → Fin k → L := fun j i => F j (b i)
  have hW : Submodule.span L (Set.range vec) = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hle⟩ := (Submodule.span L (Set.range vec)).exists_le_ker_of_lt_top
      (lt_top_iff_ne_top.2 hne)
    let z : Fin k → L := fun i => f (fun j => if i = j then 1 else 0)
    have hz : z = 0 := by
      apply hInj b z
      intro j
      have h1 : f (vec j) = 0 := hle (Submodule.subset_span ⟨j, rfl⟩)
      rw [LinearMap.pi_apply_eq_sum_univ f (vec j)] at h1
      rw [← h1]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp [z, vec, smul_eq_mul, mul_comm]
    apply hf0
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.pi_apply_eq_sum_univ f x]
    have : ∀ i, f (fun j => if i = j then (1 : L) else 0) = 0 := fun i => congrFun hz i
    simp [this]
  have hT : Function.extend e t 0 ∈ Submodule.span L (Set.range vec) := by
    rw [hW]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hT
  refine ⟨c.support, c, fun s => ?_⟩
  have h2 := congrFun hc (e s)
  rw [he.extend_apply] at h2
  rw [← h2, Finsupp.sum, Finset.sum_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp [vec, hbe s]

end CrystallineSemistableComparison.Onto
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CupSurjectivity.SumCoordBasisDual
section
namespace CrystallineSemistableComparison.Onto

theorem la_kill {K V U W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup U] [Module K U] [AddCommGroup W] [Module K W] (f : V →ₗ[K] W) (g : U →ₗ[K] W) (Θ : Module.Dual K V) (h : ∀ C u, f C = g u → Θ C = 0) : ∃ φ : Module.Dual K W, φ ∘ₗ f = Θ ∧ φ ∘ₗ g = 0 := by
  let F : (V × U) →ₗ[K] W := f.coprod (-g)
  let Θ' : Module.Dual K (V × U) := Θ ∘ₗ LinearMap.fst K V U
  have hmem : Θ' ∈ (LinearMap.ker F).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    rintro ⟨C, u⟩ hx
    rw [LinearMap.mem_ker] at hx
    have hx' : f C + -g u = 0 := by simpa [F] using hx
    have hfg : f C = g u := by
      rw [← sub_eq_add_neg] at hx'
      exact sub_eq_zero.mp hx'
    simpa [Θ'] using h C u hfg
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hmem
  obtain ⟨φ, hφ⟩ := hmem
  refine ⟨φ, ?_, ?_⟩
  · ext C
    have := congrArg (fun ψ : Module.Dual K (V × U) => ψ (C, 0)) hφ
    simpa [F, Θ', LinearMap.dualMap_apply] using this
  · ext u
    have := congrArg (fun ψ : Module.Dual K (V × U) => ψ (0, u)) hφ
    simpa [F, Θ', LinearMap.dualMap_apply] using this

theorem sum_coord_basis_dual {K C V : Type*} [Field K] [CommRing C] [AddCommGroup V] [Module K V] (κ : K →+* C) (h : Module.Dual K V →+ C) (l : ∀ (k : K) φ, h (k • φ) = κ k * h φ) {m : ℕ} (b : Module.Basis (Fin m) K V) (F : Module.Dual K V) : ∑ s, h (b.coord s) * κ (F (b s)) = h F := by
  conv_rhs => rw [← b.sum_dual_apply_smul_coord F]
  rw [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [l, mul_comm]

theorem gen2 {K C V₁ V₂ W₁ W₂ : Type*} [Field K] [CommRing C] [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂] [Module K V₂] [AddCommGroup W₁] [Module K W₁] [AddCommGroup W₂] [Module K W₂] (κ : K →+* C) (h₁ : Module.Dual K V₁ →+ C) (h₁' : Module.Dual K W₁ →+ C) (h₂ : Module.Dual K V₂ →+ C) (h₂' : Module.Dual K W₂ →+ C) (l₁ : ∀ (k : K) φ, h₁ (k • φ) = κ k * h₁ φ) (l₁' : ∀ (k : K) φ, h₁' (k • φ) = κ k * h₁' φ) (l₂ : ∀ (k : K) φ, h₂ (k • φ) = κ k * h₂ φ) (l₂' : ∀ (k : K) φ, h₂' (k • φ) = κ k * h₂' φ) (ι₁ : W₁ →ₗ[K] V₁) (ι₂ : W₂ →ₗ[K] V₂) (n₁ : ∀ F, h₁ F = h₁' (F ∘ₗ ι₁)) (n₂ : ∀ F, h₂ F = h₂' (F ∘ₗ ι₂)) (B : V₁ →ₗ[K] V₂ →ₗ[K] K) {m₁ m₂ k₁ k₂ : ℕ} (B₁ : Module.Basis (Fin m₁) K V₁) (B₂ : Module.Basis (Fin m₂) K V₂) (b₁ : Module.Basis (Fin k₁) K W₁) (b₂ : Module.Basis (Fin k₂) K W₂) : ∑ σ, ∑ σ', h₁ (B₁.coord σ) * h₂ (B₂.coord σ') * κ (B (B₁ σ) (B₂ σ')) = ∑ s, ∑ s', h₁' (b₁.coord s) * h₂' (b₂.coord s') * κ (B (ι₁ (b₁ s)) (ι₂ (b₂ s'))) := by
  calc ∑ σ, ∑ σ', h₁ (B₁.coord σ) * h₂ (B₂.coord σ') * κ (B (B₁ σ) (B₂ σ'))
      = ∑ σ, h₁ (B₁.coord σ) * h₂ (B (B₁ σ)) := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [← sum_coord_basis_dual κ h₂ l₂ B₂ (B (B₁ σ)), Finset.mul_sum]
        refine Finset.sum_congr rfl fun σ' _ => ?_
        ring
    _ = ∑ σ, ∑ s', h₁ (B₁.coord σ) * h₂' (b₂.coord s') * κ (B (B₁ σ) (ι₂ (b₂ s'))) := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [n₂, ← sum_coord_basis_dual κ h₂' l₂' b₂ (B (B₁ σ) ∘ₗ ι₂), Finset.mul_sum]
        refine Finset.sum_congr rfl fun s' _ => ?_
        simp only [LinearMap.comp_apply]
        ring
    _ = ∑ s', h₂' (b₂.coord s') * h₁ (B.flip (ι₂ (b₂ s'))) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun s' _ => ?_
        rw [← sum_coord_basis_dual κ h₁ l₁ B₁ (B.flip (ι₂ (b₂ s'))), Finset.mul_sum]
        refine Finset.sum_congr rfl fun σ _ => ?_
        simp only [LinearMap.flip_apply]
        ring
    _ = ∑ s', ∑ s, h₁' (b₁.coord s) * h₂' (b₂.coord s') * κ (B (ι₁ (b₁ s)) (ι₂ (b₂ s'))) := by
        refine Finset.sum_congr rfl fun s' _ => ?_
        rw [n₁, ← sum_coord_basis_dual κ h₁' l₁' b₁ (B.flip (ι₂ (b₂ s')) ∘ₗ ι₁), Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        simp only [LinearMap.comp_apply, LinearMap.flip_apply]
        ring
    _ = ∑ s, ∑ s', h₁' (b₁.coord s) * h₂' (b₂.coord s') * κ (B (ι₁ (b₁ s)) (ι₂ (b₂ s'))) :=
        Finset.sum_comm

end CrystallineSemistableComparison.Onto
end

