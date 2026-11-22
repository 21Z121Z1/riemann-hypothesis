import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.UnfoldAbs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle0001

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LintFibre
section
noncomputable section

namespace PI.VolStabSW

open MeasureTheory Set
open scoped ENNReal Pointwise

section Abs2

variable {G Y : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableInv G]
  [MulAction G Y]

theorem lint_fibre {Γ H : Subgroup G} [Countable Γ] (μ' : Measure H) [μ'.IsMulLeftInvariant]
    [μ'.IsInvInvariant] (y0 : Y) (hH : ∀ k : G, k ∈ H ↔ k • y0 = y0) [Countable (orbS Γ y0)]
    {A : Set G} (hA : MeasurableSet A)
    (𝓕' : Set H) (h𝓕' : IsFundamentalDomain ((Γ ⊓ H).subgroupOf H) 𝓕' μ')
    (ρ : G → ℝ≥0∞) (hρ : Measurable ρ) (hρi : ∀ γ ∈ Γ, ∀ g, ρ (γ * g) = ρ g) (s : G) :
    ∫⁻ k, cfun Γ A y0 (s * (k : G)) * ρ ((s * (k : G))⁻¹) ∂μ' =
      ∫⁻ k in 𝓕', cntN Γ A ((k : G) * s⁻¹) * ρ ((k : G) * s⁻¹) ∂μ' := by
  haveI : Countable ((Γ ⊓ H).subgroupOf H) := countable_subgroupOf
  have memΓ : ∀ δ : (Γ ⊓ H).subgroupOf H, ((δ : H) : G) ∈ Γ := fun δ =>
    (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 δ.2)).1
  have h1 : ∀ (δ : (Γ ⊓ H).subgroupOf H) (k : H),
      cfun Γ A y0 (s * (((δ • k)⁻¹ : H) : G)) * ρ ((s * (((δ • k)⁻¹ : H) : G))⁻¹) =
        (∑' x : orbS Γ y0, A.indicator (fun _ => (1 : ℝ≥0∞))
          (repO Γ y0 x * ((δ : H) : G) * ((k : G) * s⁻¹))) * ρ ((k : G) * s⁻¹) := by
    intro δ k
    have e : (((δ • k)⁻¹ : H) : G) = (k : G)⁻¹ * ((δ : H) : G)⁻¹ := by
      show ((((δ : H) * k)⁻¹ : H) : G) = _
      rw [Subgroup.coe_inv, Subgroup.coe_mul, mul_inv_rev]
    rw [e]
    have eρ : ρ ((s * ((k : G)⁻¹ * ((δ : H) : G)⁻¹))⁻¹) = ρ ((k : G) * s⁻¹) := by
      rw [show (s * ((k : G)⁻¹ * ((δ : H) : G)⁻¹))⁻¹ = ((δ : H) : G) * ((k : G) * s⁻¹) by group]
      exact hρi _ (memΓ δ) _
    rw [eρ]
    congr 1
    unfold cfun
    refine tsum_congr fun x => ?_
    congr 1
    group
  have hm : ∀ δ : (Γ ⊓ H).subgroupOf H, Measurable fun k : H =>
      (∑' x : orbS Γ y0, A.indicator (fun _ => (1 : ℝ≥0∞))
          (repO Γ y0 x * ((δ : H) : G) * ((k : G) * s⁻¹))) * ρ ((k : G) * s⁻¹) := fun δ =>
    (Measurable.ennreal_tsum fun _ => (measurable_const.indicator hA).comp
      ((measurable_const_mul _).comp ((measurable_mul_const _).comp measurable_subtype_coe))).mul
      (hρ.comp ((measurable_mul_const _).comp measurable_subtype_coe))
  calc ∫⁻ k, cfun Γ A y0 (s * (k : G)) * ρ ((s * (k : G))⁻¹) ∂μ'
      = ∫⁻ k, cfun Γ A y0 (s * ((k⁻¹ : H) : G)) * ρ ((s * ((k⁻¹ : H) : G))⁻¹) ∂μ' :=
        (lintegral_inv_eq_self
          (fun k : H => cfun Γ A y0 (s * (k : G)) * ρ ((s * (k : G))⁻¹))).symm
    _ = ∑' δ : (Γ ⊓ H).subgroupOf H, ∫⁻ k in 𝓕',
          cfun Γ A y0 (s * (((δ • k)⁻¹ : H) : G)) * ρ ((s * (((δ • k)⁻¹ : H) : G))⁻¹) ∂μ' :=
        h𝓕'.lintegral_eq_tsum'' _
    _ = ∑' δ : (Γ ⊓ H).subgroupOf H, ∫⁻ k in 𝓕',
          (∑' x : orbS Γ y0, A.indicator (fun _ => (1 : ℝ≥0∞))
            (repO Γ y0 x * ((δ : H) : G) * ((k : G) * s⁻¹))) * ρ ((k : G) * s⁻¹) ∂μ' :=
        tsum_congr fun δ => lintegral_congr fun k => h1 δ k
    _ = ∫⁻ k in 𝓕', ∑' δ : (Γ ⊓ H).subgroupOf H,
          (∑' x : orbS Γ y0, A.indicator (fun _ => (1 : ℝ≥0∞))
            (repO Γ y0 x * ((δ : H) : G) * ((k : G) * s⁻¹))) * ρ ((k : G) * s⁻¹) ∂μ' :=
        (lintegral_tsum fun δ => (hm δ).aemeasurable).symm
    _ = ∫⁻ k in 𝓕', cntN Γ A ((k : G) * s⁻¹) * ρ ((k : G) * s⁻¹) ∂μ' := by
        refine lintegral_congr fun k => ?_
        rw [ENNReal.tsum_mul_right, ENNReal.tsum_comm]
        congr 1
        exact sum_rep_eq y0 hH (fun g => A.indicator (fun _ => (1 : ℝ≥0∞)) (g * ((k : G) * s⁻¹)))

end Abs2

end PI.VolStabSW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensCntQ
section
noncomputable section

namespace PI.VolStabSW

open Polynomial

theorem exists_quadAlg (k : Type) [Field k] [Finite k] (h2 : (2 : k) ≠ 0) (D : k) (hD : D ≠ 0) :
    ∃ (K : Type) (_ : CommRing K) (_ : Algebra k K) (σ' : K ≃ₐ[k] K) (r : K),
      IsQuadInv k K σ' ∧ r * r = algebraMap k K D ∧ σ' r = -r ∧
      Function.Bijective (fun p : k × k => algebraMap k K p.1 + algebraMap k K p.2 * r) := by
  classical
  by_cases hsq : ∃ c : k, c * c = D
  · obtain ⟨c, hc⟩ := hsq
    have hc0 : c ≠ 0 := by rintro rfl; exact hD (by rw [← hc, mul_zero])
    let σ' : (k × k) ≃ₐ[k] (k × k) :=
      { RingEquiv.prodComm with commutes' := fun r => rfl }
    have hσ : ∀ x : k × k, σ' x = x.swap := fun x => rfl
    refine ⟨k × k, inferInstance, inferInstance, σ', (c, -c), ⟨fun x => by simp [hσ], Or.inr
      ⟨AlgEquiv.refl, fun x => by simp [hσ]⟩⟩, ?_, ?_, ?_⟩
    · ext <;> simp [hc]
    · ext <;> simp [hσ]
    · have h2c : (2 : k) * c ≠ 0 := mul_ne_zero h2 hc0
      constructor
      · rintro ⟨x1, y1⟩ ⟨x2, y2⟩ h
        simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.fst_mul, Prod.snd_mul,
          Prod.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] at h
        obtain ⟨h1, h2'⟩ := h
        have hy : y1 = y2 := by
          have : (2 * c) * (y1 - y2) = 0 := by linear_combination h1 - h2'
          exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left h2c)
        subst hy
        have hx : x1 = x2 := by linear_combination h1
        rw [hx]
      · rintro ⟨u, w⟩
        refine ⟨((u + w) / 2, (u - w) / (2 * c)), ?_⟩
        simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.fst_mul, Prod.snd_mul,
          Prod.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
        constructor
        · field_simp
          ring
        · field_simp
          ring
  · push Not at hsq
    let f : k[X] := X ^ 2 - C D
    have hfdeg : f.natDegree = 2 := natDegree_X_pow_sub_C
    have hnr : ∀ x, ¬ IsRoot f x := by
      intro x hx
      apply hsq x
      have : x ^ 2 - D = 0 := by simpa [f] using hx
      linear_combination this
    have hirr : Irreducible f :=
      irreducible_of_degree_le_three_of_not_isRoot (by rw [hfdeg]; decide) hnr
    have : Fact (Irreducible f) := ⟨hirr⟩
    have hf0 : f ≠ 0 := hirr.ne_zero
    let K := AdjoinRoot f
    let r : K := AdjoinRoot.root f
    have hr2 : r * r = algebraMap k K D := by
      have h := AdjoinRoot.eval₂_root f
      simp only [f, eval₂_sub, eval₂_X_pow, eval₂_C] at h
      rw [← sq, show algebraMap k K D = AdjoinRoot.of f D from rfl]
      linear_combination h
    have hneg : f.eval₂ (Algebra.ofId k K) (-r) = 0 := by
      simp only [f, eval₂_sub, eval₂_X_pow, eval₂_C, neg_sq]
      have h := AdjoinRoot.eval₂_root f
      simp only [f, eval₂_sub, eval₂_X_pow, eval₂_C] at h
      exact h
    let τ : K →ₐ[k] K := AdjoinRoot.liftAlgHom f (Algebra.ofId k K) (-r) hneg
    have hτr : τ r = -r := AdjoinRoot.liftAlgHom_root _ _ _ _
    have hττ : τ.comp τ = AlgHom.id k K := by
      apply AdjoinRoot.algHom_ext
      show τ (τ r) = r
      rw [hτr, map_neg, hτr, neg_neg]
    let σ' : K ≃ₐ[k] K := AlgEquiv.ofAlgHom τ τ hττ hττ
    have hσr : σ' r = -r := hτr
    have hr0 : r ≠ 0 := by
      intro h
      rw [h, mul_zero] at hr2
      exact hD ((algebraMap k K).injective (by rw [← hr2, map_zero]))
    have h2K : (2 : K) ≠ 0 := by
      intro h
      apply h2
      apply (algebraMap k K).injective
      rw [map_ofNat, h, map_zero]
    have hfin : Module.finrank k K = 2 := by
      rw [(AdjoinRoot.powerBasis hf0).finrank, AdjoinRoot.powerBasis_dim, hfdeg]
    refine ⟨K, inferInstance, inferInstance, σ', r, ⟨fun x => ?_, Or.inl ⟨Field.toIsField K, hfin,
      fun h => ?_⟩⟩, hr2, hσr, ?_⟩
    · show τ (τ x) = x
      exact congrArg (fun g : K →ₐ[k] K => g x) hττ
    · have h1 : σ' r = r := by rw [h]; rfl
      rw [hσr] at h1
      have : (2 : K) * r = 0 := by linear_combination -h1
      exact hr0 ((mul_eq_zero.1 this).resolve_left h2K)
    · have hinj : Function.Injective
          (fun p : k × k => algebraMap k K p.1 + algebraMap k K p.2 * r) := by
        rintro ⟨x1, y1⟩ ⟨x2, y2⟩ h
        simp only at h
        by_cases hy : y1 = y2
        · subst hy
          have : algebraMap k K x1 = algebraMap k K x2 := by linear_combination h
          rw [(algebraMap k K).injective this]
        · exfalso
          have hy' : y1 - y2 ≠ 0 := sub_ne_zero.2 hy
          have hyK : algebraMap k K (y1 - y2) ≠ 0 := by
            rw [Ne, map_eq_zero_iff _ (algebraMap k K).injective]; exact hy'
          have hm : algebraMap k K (y1 - y2) * r = algebraMap k K (x2 - x1) := by
            rw [map_sub, map_sub]; linear_combination h
          have hrr : r = algebraMap k K ((x2 - x1) / (y1 - y2)) := by
            rw [map_div₀, eq_div_iff hyK, mul_comm]
            exact hm
          apply hsq ((x2 - x1) / (y1 - y2))
          apply (algebraMap k K).injective
          rw [map_mul, ← hrr, hr2]
      have hKm : Module.Finite k K := (AdjoinRoot.powerBasis hf0).finite
      have hKf : Finite K := Module.finite_of_finite k
      refine hinj.bijective_of_nat_card_le ?_
      letI := Fintype.ofFinite k
      letI := Fintype.ofFinite K
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := k),
        hfin, Fintype.card_prod, sq]

end PI.VolStabSW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensFFHS
section
noncomputable section

namespace PI.VolStabSW.FFHS

open Module

variable {K : Type} [Field K] {σ : K →+* K}

structure IsSq {V : Type} [AddCommGroup V] [Module K V] (σ : K →+* K) (h : V → V → K) :
    Prop where
  add_right : ∀ x y z, h x (y + z) = h x y + h x z
  smul_right : ∀ (c : K) x y, h x (c • y) = c * h x y
  herm : ∀ x y, h y x = σ (h x y)

structure IsHS {V : Type} [AddCommGroup V] [Module K V] (σ : K →+* K) (h : V → V → K) : Prop
    extends IsSq σ h where
  nondeg : ∀ x, (∀ y, h x y = 0) → x = 0

section basic

variable {V : Type} [AddCommGroup V] [Module K V] {h : V → V → K}

def IsSq.lin (hs : IsSq σ h) (x : V) : V →ₗ[K] K where
  toFun := h x
  map_add' := hs.add_right x
  map_smul' c y := by simp [hs.smul_right]

theorem IsSq.lin_apply (hs : IsSq σ h) (x y : V) : hs.lin x y = h x y := rfl

theorem IsSq.add_left (hs : IsSq σ h) (x y z : V) : h (x + y) z = h x z + h y z := by
  rw [hs.herm z (x + y), hs.add_right, map_add, ← hs.herm, ← hs.herm]

theorem IsSq.smul_left (hs : IsSq σ h) (c : K) (x y : V) : h (c • x) y = σ c * h x y := by
  rw [hs.herm y (c • x), hs.smul_right, map_mul, ← hs.herm]

theorem IsSq.zero_right (hs : IsSq σ h) (x : V) : h x 0 = 0 := by
  have h0 := hs.smul_right 0 x 0
  simpa using h0

theorem IsSq.zero_left (hs : IsSq σ h) (y : V) : h 0 y = 0 := by
  rw [hs.herm y 0, hs.zero_right, map_zero]

theorem IsSq.sub_right (hs : IsSq σ h) (x y z : V) : h x (y - z) = h x y - h x z := by
  rw [sub_eq_add_neg, hs.add_right, ← neg_one_smul K z, hs.smul_right]
  ring

theorem IsSq.self_fixed (hs : IsSq σ h) (x : V) : σ (h x x) = h x x := by
  exact (hs.herm x x).symm

theorem IsSq.ext_basis {h' : V → V → K} (hs : IsSq σ h) (hs' : IsSq σ h') {ι : Type}
    (b : Basis ι K V) (hb : ∀ i j, h (b i) (b j) = h' (b i) (b j)) (x y : V) : h x y = h' x y := by
  have h1 : ∀ i y, h (b i) y = h' (b i) y := by
    intro i y
    have e := b.ext (f₁ := hs.lin (b i)) (f₂ := hs'.lin (b i)) (fun j => hb i j)
    exact LinearMap.congr_fun e y
  have h3 : ∀ x y, h y x = h' y x := by
    intro x y
    have e := b.ext (f₁ := hs.lin y) (f₂ := hs'.lin y) (fun i => by
      simp only [IsSq.lin_apply]
      rw [hs.herm (b i) y, hs'.herm (b i) y, h1])
    exact LinearMap.congr_fun e x
  exact h3 y x

theorem exists_aniso (h2 : (2 : K) ≠ 0) (hs : IsHS σ h) (x : V) (hx : x ≠ 0) :
    ∃ e, h e e ≠ 0 := by
  by_contra H
  push_neg at H
  obtain ⟨y, hy⟩ : ∃ y, h x y ≠ 0 := by
    by_contra H'
    push_neg at H'
    exact hx (hs.nondeg x H')
  have key : ∀ c : K, c * h x y + σ (c * h x y) = 0 := by
    intro c
    have e1 : h (x + c • y) (x + c • y) = h x x + h x (c • y) + (h (c • y) x + h (c • y) (c • y)) := by
      rw [hs.add_right, IsSq.add_left hs.toIsSq, IsSq.add_left hs.toIsSq]
      ring
    rw [H, H, H, hs.herm x (c • y), hs.smul_right] at e1
    linear_combination -e1
  have ha : h x y + σ (h x y) = 0 := by simpa using key 1
  by_cases hσ : ∃ c, σ c ≠ c
  · obtain ⟨c, hc⟩ := hσ
    have e2 := key c
    rw [map_mul] at e2
    have hsa : σ (h x y) = -(h x y) := by linear_combination ha
    rw [hsa] at e2
    have e3 : (c - σ c) * h x y = 0 := by linear_combination e2
    rcases mul_eq_zero.1 e3 with h0 | h0
    · exact hc (by linear_combination -h0)
    · exact hy h0
  · push_neg at hσ
    rw [hσ] at ha
    have e3 : (2 : K) * h x y = 0 := by linear_combination ha
    rcases mul_eq_zero.1 e3 with h0 | h0
    · exact h2 h0
    · exact hy h0

def perp (hs : IsSq σ h) (e : V) : Submodule K V := LinearMap.ker (hs.lin e)

theorem mem_perp (hs : IsSq σ h) (e w : V) : w ∈ perp hs e ↔ h e w = 0 := by
  exact LinearMap.mem_ker

theorem perp_isHS (hs : IsHS σ h) (e : V) (he : h e e ≠ 0) :
    IsHS σ (fun w w' : perp hs.toIsSq e => h w w') where
  add_right x y z := hs.add_right x y z
  smul_right c x y := hs.smul_right c x y
  herm x y := hs.herm x y
  nondeg w hw := by
    have hq := hs.toIsSq
    apply Subtype.ext
    apply hs.nondeg
    intro y
    have hm : y - ((h e e)⁻¹ * h e y) • e ∈ perp hq e := by
      have : (h e e)⁻¹ * h e y * h e e = h e y := by
        rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ he, one_mul]
      rw [mem_perp, hq.sub_right, hq.smul_right, this, sub_self]
    have h1 := hw ⟨_, hm⟩
    have hwe : h w e = 0 := by rw [hq.herm e w, (mem_perp hq e w).1 w.2, map_zero]
    calc h w y = h w (((h e e)⁻¹ * h e y) • e + (y - ((h e e)⁻¹ * h e y) • e)) := by
          rw [add_sub_cancel]
      _ = ((h e e)⁻¹ * h e y) * h w e + h w (y - ((h e e)⁻¹ * h e y) • e) := by
          rw [hq.add_right, hq.smul_right]
      _ = 0 := by rw [hwe, h1]; ring

theorem finrank_perp [FiniteDimensional K V] (hs : IsSq σ h) (e : V) (he : h e e ≠ 0) :
    finrank K (perp hs e) + 1 = finrank K V := by
  have hsurj : LinearMap.range (hs.lin e) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro c
    refine ⟨(c / h e e) • e, ?_⟩
    rw [IsSq.lin_apply, hs.smul_right, div_mul_cancel₀ _ he]
  have e1 := LinearMap.finrank_range_add_finrank_ker (hs.lin e)
  rw [hsurj, finrank_top, Module.finrank_self] at e1
  unfold perp
  omega

theorem linIndep_orth (hs : IsSq σ h) {n : ℕ} (f : Fin n → V)
    (h1 : ∀ i j, i ≠ j → h (f i) (f j) = 0) (h2 : ∀ i, h (f i) (f i) ≠ 0) :
    LinearIndependent K f := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have e1 := congrArg (hs.lin (f i)) hg
  rw [map_sum, map_zero] at e1
  simp only [map_smul, IsSq.lin_apply, smul_eq_mul] at e1
  rw [Finset.sum_eq_single i] at e1
  · exact (mul_eq_zero.1 e1).resolve_right (h2 i)
  · intro j _ hji
    rw [h1 i j (Ne.symm hji), mul_zero]
  · simp

theorem decomp_val (hs : IsSq σ h) (e w : V) (hw : h e w = 0) (s : K) :
    h (s • e + w) (s • e + w) = σ s * s * h e e + h w w := by
  have hwe : h w e = 0 := by rw [hs.herm e w, hw, map_zero]
  rw [hs.add_right, IsSq.add_left hs, IsSq.add_left hs, IsSq.smul_left hs, IsSq.smul_left hs, hs.smul_right,
    hs.smul_right, hw, hwe]
  ring

end basic

theorem exists_orth (h2 : (2 : K) ≠ 0) : ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (h : V → V → K), IsHS σ h → finrank K V = m →
    ∃ f : Fin m → V, (∀ i j, i ≠ j → h (f i) (f j) = 0) ∧ ∀ i, h (f i) (f i) ≠ 0 := by
  intro m
  induction m with
  | zero =>
    intro V _ _ _ h hs hm
    exact ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ n ih =>
    intro V _ _ _ h hs hm
    obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.mp (by omega : 0 < finrank K V)
    obtain ⟨e, he⟩ := exists_aniso h2 hs x hx
    have hp := perp_isHS hs e he
    have hr := finrank_perp hs.toIsSq e he
    obtain ⟨g, hg1, hg2⟩ := ih (perp hs.toIsSq e) (fun w w' => h w w') hp (by omega)
    refine ⟨Fin.cons e (fun i => (g i : V)), ?_, ?_⟩
    · intro i j hij
      induction i using Fin.cases <;> induction j using Fin.cases
      · exact absurd rfl hij
      · simp only [Fin.cons_zero, Fin.cons_succ]
        exact (mem_perp hs.toIsSq e _).1 (g _).2
      · simp only [Fin.cons_zero, Fin.cons_succ]
        rw [hs.herm e, (mem_perp hs.toIsSq e _).1 (g _).2, map_zero]
      · simp only [Fin.cons_succ]
        exact hg1 _ _ (fun h' => hij (by rw [h']))
    · intro i
      induction i using Fin.cases
      · simpa using he
      · simpa using hg2 _

end PI.VolStabSW.FFHS
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensSAInt
section
noncomputable section

open NumberField
open scoped nonZeroDivisors

namespace PI.VolStabSW

private theorem addHom_eq_zero_of_integralBasis_mul {F : Type} [Field F] [NumberField F] (g : F →+ ℂ)
    {y : F} (hy : y ≠ 0) (h0 : ∀ i, g (integralBasis F i * y) = 0) (w : F) : g w = 0 := by
  have hw : w = (∑ i, (integralBasis F).repr (w * y⁻¹) i • integralBasis F i) * y := by
    rw [(integralBasis F).sum_repr, mul_assoc, inv_mul_cancel₀ hy, mul_one]
  rw [hw, Finset.sum_mul, map_sum]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [smul_mul_assoc, map_rat_smul, h0 i, smul_zero]

private theorem exists_mul_integers_of_fg {F : Type} [Field F] [NumberField F]
    (Λ : Submodule (𝓞 F) F) (hfg : (Λ.restrictScalars ℤ).FG) :
    ∃ c : F, c ≠ 0 ∧ ∀ a ∈ Λ, ∃ r : 𝓞 F, a = c * r := by
  obtain ⟨s, hs⟩ := hfg
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (M := (𝓞 F)⁰) (S := F) s
  have hB0 : algebraMap (𝓞 F) F b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  let T : Submodule ℤ F :=
    { carrier := {a | ∃ r : 𝓞 F, algebraMap (𝓞 F) F b * a = algebraMap (𝓞 F) F r}
      add_mem' := by
        rintro a a' ⟨r, hr⟩ ⟨r', hr'⟩
        exact ⟨r + r', by rw [mul_add, hr, hr', map_add]⟩
      zero_mem' := ⟨0, by rw [mul_zero, map_zero]⟩
      smul_mem' := by
        rintro n a ⟨r, hr⟩
        exact ⟨n • r, by rw [mul_smul_comm, hr, map_zsmul]⟩ }
  have hsT : Submodule.span ℤ (s : Set F) ≤ T := by
    rw [Submodule.span_le]
    intro a ha
    obtain ⟨r, hr⟩ := hb a ha
    exact ⟨r, by rw [hr, Algebra.smul_def]⟩
  refine ⟨(algebraMap (𝓞 F) F b)⁻¹, inv_ne_zero hB0, fun a ha => ?_⟩
  have has : a ∈ Submodule.span ℤ (s : Set F) := by rw [hs]; exact ha
  obtain ⟨r, hr⟩ := hsT has
  refine ⟨r, ?_⟩
  have hrr : ((r : 𝓞 F) : F) = algebraMap (𝓞 F) F r := by
    rfl
  rw [hrr, ← hr, ← mul_assoc, inv_mul_cancel₀ hB0, one_mul]

private theorem fg_of_addHom_intValued {F : Type} [Field F] [NumberField F] (Λ : Submodule (𝓞 F) F)
    (g : F →+ ℂ) (hg : ∀ a ∈ Λ, ∃ n : ℤ, g a = n) (hne : ∃ w, g w ≠ 0) :
    (Λ.restrictScalars ℤ).FG := by
  classical
  let φ : F →ₗ[ℤ] (Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℂ) :=
    { toFun := fun y i => g (integralBasis F i * y)
      map_add' := fun y y' => by funext i; simp only [mul_add, map_add, Pi.add_apply]
      map_smul' := fun n y => by
        funext i; simp only [mul_smul_comm, map_zsmul, RingHom.id_apply, Pi.smul_apply] }
  let ψ : (Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℤ) →ₗ[ℤ]
      (Module.Free.ChooseBasisIndex ℤ (𝓞 F) → ℂ) :=
    { toFun := fun z i => (z i : ℂ)
      map_add' := fun z z' => by funext i; simp only [Pi.add_apply, Int.cast_add]
      map_smul' := fun n z => by
        funext i
        simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul, RingHom.id_apply, zsmul_eq_mul] }
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    by_contra hy0
    obtain ⟨w, hw⟩ := hne
    exact hw (addHom_eq_zero_of_integralBasis_mul g hy0 (fun i => congrFun hy i) w)
  have hrange : (Λ.restrictScalars ℤ).map φ ≤ LinearMap.range ψ := by
    rintro _ ⟨y, hy, rfl⟩
    have hmem : ∀ i, integralBasis F i * y ∈ Λ := fun i => by
      have h := Λ.smul_mem (RingOfIntegers.basis F i) hy
      rwa [Algebra.smul_def, ← integralBasis_apply] at h
    choose n hn using fun i => hg _ (hmem i)
    exact ⟨n, funext fun i => (hn i).symm⟩
  have hQ : (((Λ.restrictScalars ℤ).map φ).comap ψ).FG := IsNoetherian.noetherian _
  have hmap : (((Λ.restrictScalars ℤ).map φ).comap ψ).map ψ = (Λ.restrictScalars ℤ).map φ := by
    apply le_antisymm
    · rintro x ⟨z, hz, rfl⟩
      exact hz
    · intro x hx
      obtain ⟨z, rfl⟩ := hrange hx
      exact ⟨z, hx, rfl⟩
  have hfg := hQ.map ψ
  rw [hmap] at hfg
  exact Submodule.fg_of_fg_map_injective φ hφ hfg

theorem addIntF_holds : AddIntF := by
  intro F _ _ Λ _ hnp g hg
  by_contra hall
  obtain ⟨c, hc0, hc⟩ := exists_mul_integers_of_fg Λ (fg_of_addHom_intValued Λ g hg (not_forall.mp hall))
  exact hnp c hc0 hc

theorem chInf_of_lift (hL : ChLift) : ChInf :=
  chInf_of hL addIntF_holds

end PI.VolStabSW
end
end

