import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0012
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarTraceConjEqConstMulKernelImage
import Formalism.SatakeDualWeyl.Statement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumCosetsEulerProduct
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0008
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0012
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0009

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarMapConjNormalizingLatticeEqSelf
section
open MeasureTheory Function
open scoped Pointwise

namespace GlobalTheory.UnfoldNormal

def conjEquiv {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (N : Subgroup H)
    (γ : H) (h1 : ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) (h2 : ∀ n ∈ N, γ⁻¹ * n * γ⁻¹⁻¹ ∈ N) : N ≃ₜ* N where
  toFun n := ⟨γ * n * γ⁻¹, h1 n n.2⟩
  invFun n := ⟨γ⁻¹ * n * γ⁻¹⁻¹, h2 n n.2⟩
  left_inv n := by ext; simp [mul_assoc]
  right_inv n := by ext; simp [mul_assoc]
  map_mul' a b := by ext; simp [mul_assoc]
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const

theorem map_conj_eq_self (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H]
    (Γ N : Subgroup H) (hΓ : Countable Γ) (hNc : IsClosed (N : Set H))
    (hN : ∀ γ ∈ Γ, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) (κ : Measure N) (𝓝 : Set N) (hκ : κ.IsHaarMeasure)
    (h𝓝 : IsFundamentalDomain (Γ.subgroupOf N) 𝓝 κ) (hfin : κ 𝓝 ≠ ⊤)
    (γ : H) (hγ : γ ∈ Γ) :
    κ.map (fun n : N => (⟨γ * n * γ⁻¹, hN γ hγ n n.2⟩ : N)) = κ := by
  haveI : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology (N : Set H)
  haveI : LocallyCompactSpace N := hNc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : Countable (Γ.subgroupOf N) := by
    refine Function.Injective.countable (f := fun x : Γ.subgroupOf N => (⟨(x : N), x.2⟩ : Γ)) ?_
    intro a b hab
    apply Subtype.ext; apply Subtype.ext
    simpa using congrArg Subtype.val hab
  set e := conjEquiv N γ (hN γ hγ) (hN γ⁻¹ (Γ.inv_mem hγ)) with he_def
  have hfun : (fun n : N => (⟨γ * n * γ⁻¹, hN γ hγ n n.2⟩ : N)) = ⇑e := rfl
  rw [hfun]
  haveI : (κ.map e).IsHaarMeasure := e.isHaarMeasure_map κ
  have hsm : κ.map e = Measure.haarScalarFactor (κ.map e) κ • κ :=
    Measure.isMulLeftInvariant_eq_smul (κ.map e) κ
  set c := Measure.haarScalarFactor (κ.map e) κ

  have hqmp : Measure.QuasiMeasurePreserving e κ κ :=
    ⟨e.continuous.measurable, by rw [hsm]; exact Measure.smul_absolutelyContinuous⟩
  have hpre : IsFundamentalDomain (Γ.subgroupOf N) (e ⁻¹' 𝓝) κ := by
    refine h𝓝.preimage_of_equiv hqmp (e := fun g : Γ.subgroupOf N =>
      (⟨⟨γ⁻¹ * (g : H) * γ⁻¹⁻¹, hN γ⁻¹ (Γ.inv_mem hγ) _ (g : N).2⟩,
        by
          show γ⁻¹ * (g : H) * γ⁻¹⁻¹ ∈ Γ
          exact Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hγ) g.2) (Γ.inv_mem (Γ.inv_mem hγ))⟩ : Γ.subgroupOf N)) ?_ ?_
    · constructor
      · intro a b hab
        apply Subtype.ext; apply Subtype.ext
        have := congrArg (fun x : Γ.subgroupOf N => ((x : N) : H)) hab
        simpa using this
      · intro g
        refine ⟨⟨⟨γ * (g : H) * γ⁻¹, hN γ hγ _ (g : N).2⟩, ?_⟩, ?_⟩
        · show γ * (g : H) * γ⁻¹ ∈ Γ
          exact Γ.mul_mem (Γ.mul_mem hγ g.2) (Γ.inv_mem hγ)
        · apply Subtype.ext; apply Subtype.ext; simp [mul_assoc]
    · intro g x
      apply Subtype.ext
      simp [he_def, conjEquiv, Subgroup.smul_def, mul_assoc]
  have hmeq : κ (e ⁻¹' 𝓝) = κ 𝓝 := hpre.measure_eq h𝓝
  have hmap : κ.map e 𝓝 = κ (e ⁻¹' 𝓝) := by
    have := e.toHomeomorph.toMeasurableEquiv.map_apply (μ := κ) 𝓝
    exact this
  have hne : κ 𝓝 ≠ 0 := h𝓝.measure_ne_zero (NeZero.ne κ)
  have hc : (c : ENNReal) * κ 𝓝 = 1 * κ 𝓝 := by
    have h' : (c • κ) 𝓝 = κ 𝓝 := by rw [← hsm, hmap, hmeq]
    rw [one_mul]
    conv_rhs => rw [← h']
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  have hc1 : (c : ENNReal) = 1 := (ENNReal.mul_left_inj hne hfin).1 hc
  have : c = 1 := by exact_mod_cast hc1
  rw [hsm, this, one_smul]

end GlobalTheory.UnfoldNormal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarTraceConjEqConstMulKernelImageStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_trace_conj_eq_const_mul_kernel_image : ∀ {X Y : Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [MeasurableSpace X] [BorelSpace X]
    [Group Y] [TopologicalSpace Y] [IsTopologicalGroup Y] [MeasurableSpace Y] [BorelSpace Y]
    (R N K : Subgroup X) (π : R →* Y) (σ : Y →* R),
    IsClosed (R : Set X) → IsClosed (N : Set X) → N ≤ R → IsOpen (K : Set X) → IsCompact (K : Set X) →
    Continuous π → Continuous σ → (∀ y, π (σ y) = y) → (∀ r : R, π r = 1 ↔ r.1 ∈ N) →
    ∀ ρ : Measure R, ρ.IsHaarMeasure →
    ∃ (κ : ℝ) (la : Measure N) (ν : Measure Y), 0 < κ ∧ la.IsHaarMeasure ∧ ν.IsHaarMeasure ∧ ∀ b : X,
      ρ.real {r : R | b⁻¹ * r.1 * b ∈ K} = κ * la.real {n : N | b⁻¹ * n.1 * b ∈ K} * ν.real (π '' {r : R | b⁻¹ * r.1 * b ∈ K}) := by
  first | exact @GlobalTheory.RowFubini.haar_trace_conj_eq | exact GlobalTheory.RowFubini.haar_trace_conj_eq | (intros; apply GlobalTheory.RowFubini.haar_trace_conj_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSignatureFstUniqueSylvester
section
namespace GlobalTheory.SylvesterInertia

open Matrix Module
open scoped ComplexOrder

variable {n : Type} [Fintype n] [DecidableEq n]

def qf (J : Matrix n n ℂ) (x : n → ℂ) : ℂ := star x ⬝ᵥ J *ᵥ x

def inlMap (a b : ℕ) : (Fin a → ℂ) →ₗ[ℂ] (Fin a ⊕ Fin b → ℂ) where
  toFun z := Sum.elim z 0
  map_add' x y := by ext k; cases k <;> simp
  map_smul' c x := by ext k; cases k <;> simp

def inrMap (a b : ℕ) : (Fin b → ℂ) →ₗ[ℂ] (Fin a ⊕ Fin b → ℂ) where
  toFun z := Sum.elim 0 z
  map_add' x y := by ext k; cases k <;> simp
  map_smul' c x := by ext k; cases k <;> simp

lemma inlMap_injective (a b : ℕ) : Function.Injective (inlMap a b) := by
  intro z z' h; funext i; exact congrFun h (Sum.inl i)

lemma inrMap_injective (a b : ℕ) : Function.Injective (inrMap a b) := by
  intro z z' h; funext i; exact congrFun h (Sum.inr i)

def chg {a b : ℕ} (e : n ≃ Fin a ⊕ Fin b) (P : GL (Fin a ⊕ Fin b) ℂ) :
    (Fin a ⊕ Fin b → ℂ) →ₗ[ℂ] (n → ℂ) :=
  LinearMap.funLeft ℂ ℂ e ∘ₗ (P : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ).mulVecLin

lemma chg_apply {a b : ℕ} (e : n ≃ Fin a ⊕ Fin b) (P : GL (Fin a ⊕ Fin b) ℂ) (y : Fin a ⊕ Fin b → ℂ) :
    chg e P y = ((P : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ) *ᵥ y) ∘ e := rfl

lemma chg_injective {a b : ℕ} (e : n ≃ Fin a ⊕ Fin b) (P : GL (Fin a ⊕ Fin b) ℂ) :
    Function.Injective (chg e P) := by
  intro y y' h
  have h1 : (P : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ) *ᵥ y = (P : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ) *ᵥ y' := by
    have := congrArg (fun v => v ∘ e.symm) h
    simpa [chg_apply, Function.comp_def] using this
  have h2 := congrArg (fun v => ((P⁻¹ : GL (Fin a ⊕ Fin b) ℂ) : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ) *ᵥ v) h1
  simpa [mulVec_mulVec] using h2

lemma qf_chg {a b : ℕ} (J : Matrix n n ℂ) (e : n ≃ Fin a ⊕ Fin b) (P : GL (Fin a ⊕ Fin b) ℂ)
    (h : Formalism.UG.cT (starRingEnd ℂ) (P : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ) * J.reindex e e *
      (P : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ) = Formalism.UG.Jpq a b) (y : Fin a ⊕ Fin b → ℂ) :
    qf J (chg e P y) = star y ⬝ᵥ Formalism.UG.Jpq a b *ᵥ y := by
  set M : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ := (P : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ)
  have hc : Formalism.UG.cT (starRingEnd ℂ) M = Mᴴ := by ext i j; rfl
  rw [← h, hc]
  set w := M *ᵥ y
  have h1 : J *ᵥ (w ∘ e) = (J.reindex e e *ᵥ w) ∘ e := by
    rw [reindex_apply, submatrix_mulVec_equiv]
    ext i; simp [Function.comp_def]
  have h2 : qf J (chg e P y) = star w ⬝ᵥ (J.reindex e e *ᵥ w) := by
    rw [qf, chg_apply, h1]
    simp only [dotProduct, Function.comp_apply, Pi.star_apply]
    exact Fintype.sum_equiv e _ _ (fun _ => rfl)
  rw [h2]
  simp only [w, star_mulVec, ← mulVec_mulVec, dotProduct_mulVec, Matrix.mul_assoc]

lemma jpq_inl (a b : ℕ) (z : Fin a → ℂ) :
    star (inlMap a b z) ⬝ᵥ Formalism.UG.Jpq a b *ᵥ inlMap a b z = star z ⬝ᵥ z := by
  simp [inlMap, Formalism.UG.Jpq, fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type, Function.comp_def]

lemma jpq_inr (a b : ℕ) (z : Fin b → ℂ) :
    star (inrMap a b z) ⬝ᵥ Formalism.UG.Jpq a b *ᵥ inrMap a b z = -(star z ⬝ᵥ z) := by
  simp [inrMap, Formalism.UG.Jpq, fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type, Function.comp_def, neg_mulVec, Finset.sum_neg_distrib]

lemma pos_of_mem {a b : ℕ} {J : Matrix n n ℂ} {e : n ≃ Fin a ⊕ Fin b} {P : GL (Fin a ⊕ Fin b) ℂ}
    (h : Formalism.UG.cT (starRingEnd ℂ) (P : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ) * J.reindex e e *
      (P : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ) = Formalism.UG.Jpq a b)
    {x : n → ℂ} (hx : x ∈ LinearMap.range (chg e P ∘ₗ inlMap a b)) (hx0 : x ≠ 0) : 0 < qf J x := by
  obtain ⟨z, rfl⟩ := hx
  have hz : z ≠ 0 := by rintro rfl; exact hx0 (map_zero _)
  rw [LinearMap.comp_apply, qf_chg J e P h, jpq_inl]
  exact dotProduct_star_self_pos_iff.mpr hz

lemma nonpos_of_mem {a b : ℕ} {J : Matrix n n ℂ} {e : n ≃ Fin a ⊕ Fin b} {P : GL (Fin a ⊕ Fin b) ℂ}
    (h : Formalism.UG.cT (starRingEnd ℂ) (P : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ) * J.reindex e e *
      (P : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ) = Formalism.UG.Jpq a b)
    {x : n → ℂ} (hx : x ∈ LinearMap.range (chg e P ∘ₗ inrMap a b)) : qf J x ≤ 0 := by
  obtain ⟨z, rfl⟩ := hx
  rw [LinearMap.comp_apply, qf_chg J e P h, jpq_inr]
  exact neg_nonpos.mpr (dotProduct_star_self_nonneg z)

theorem fst_le_of_hasSignature {J : Matrix n n ℂ} {a b a' b' : ℕ}
    (h : Formalism.UG.HasSignature J a b) (h' : Formalism.UG.HasSignature J a' b') : a ≤ a' := by
  obtain ⟨e, P, hP⟩ := h
  obtain ⟨e', P', hP'⟩ := h'
  by_contra hlt
  push_neg at hlt
  set U := LinearMap.range (chg e P ∘ₗ inlMap a b)
  set N := LinearMap.range (chg e' P' ∘ₗ inrMap a' b')
  have hU : finrank ℂ U = a := by
    rw [LinearMap.finrank_range_of_inj (by rw [LinearMap.coe_comp]; exact (chg_injective e P).comp (inlMap_injective a b))]
    simp
  have hN : finrank ℂ N = b' := by
    rw [LinearMap.finrank_range_of_inj (by rw [LinearMap.coe_comp]; exact (chg_injective e' P').comp (inrMap_injective a' b'))]
    simp
  have hcard : Fintype.card n = a' + b' := by simpa using Fintype.card_congr e'
  have hsup : finrank ℂ ↥(U ⊔ N) ≤ Fintype.card n := by
    have := Submodule.finrank_le (U ⊔ N)
    simpa using this
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq U N
  have hinf : U ⊓ N ≠ ⊥ := by
    intro hb
    rw [hb, finrank_bot] at hsum
    omega
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hinf
  have h1 := pos_of_mem hP (Submodule.mem_inf.1 hx).1 hx0
  have h2 := nonpos_of_mem hP' (Submodule.mem_inf.1 hx).2
  exact lt_irrefl _ (lt_of_lt_of_le h1 h2)

theorem hasSignature_fst_unique : ∀ {n : ℕ} {J : Matrix (Fin n) (Fin n) ℂ} {a b a' b' : ℕ},
    Formalism.UG.HasSignature J a b → Formalism.UG.HasSignature J a' b' → a = a' :=
  fun h h' => le_antisymm (fst_le_of_hasSignature h h') (fst_le_of_hasSignature h' h)

end GlobalTheory.SylvesterInertia
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumCosetsEulerProductStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_cosets_eulerProduct_alt : ∀ {G ι : Type} [Group G] {L : ι → Type} [∀ v, Group (L v)] (e : ∀ v, L v →* G) (p : ∀ v, G →* L v) (K : ∀ v, Subgroup (L v)) (J H : Subgroup G), J ≤ H → (∀ v a, p v (e v a) = a) → (∀ u v, u ≠ v → ∀ a, p u (e v a) = 1) → (∀ v a, e v a ∈ H) → (∀ v a g, p v g = 1 → Commute (e v a) g) → (∀ g ∈ H, g ∈ J ↔ ∀ v, p v g ∈ K v) → (∀ g ∈ H, {v | p v g ∉ K v}.Finite) → ∀ (Ψ : G → ℂ) (Φ : G → ℝ) (Z : ι → ℂ) (A : ι → ℝ) (z : ℂ), (∀ g ∈ H, ∀ k ∈ J, Ψ (g * k) = Ψ g) → (∀ g ∈ H, ∀ k ∈ J, Φ (g * k) = Φ g) → (∀ g ∈ H, ‖Ψ g‖ ≤ Φ g) → (∀ v, ∀ g ∈ H, p v g = 1 → HasSum (fun a : L v ⧸ K v => Ψ (g * e v a.out)) (Z v * Ψ g)) → (∀ v, ∀ g ∈ H, p v g = 1 → HasSum (fun a : L v ⧸ K v => Φ (g * e v a.out)) (A v * Φ g)) → Summable (fun v => A v - 1) → HasProd Z z → HasSum (fun y : H ⧸ J.subgroupOf H => Ψ (y.out : H)) (z * Ψ 1) := by
  first | exact @GlobalTheory.CosetEuler.hasSum_cosets_eulerProduct | exact GlobalTheory.CosetEuler.hasSum_cosets_eulerProduct | (intros; apply GlobalTheory.CosetEuler.hasSum_cosets_eulerProduct <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumCosetsSmallerLevelRelIndexMulStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_cosets_smaller_level_relIndex_mul_alt : ∀ {G : Type} [Group G] (K J H Γ : Subgroup G), K ≤ J → J ≤ H → H ≤ Γ → K.relIndex J ≠ 0 → ∀ (Ψ : G → ℂ) (z : ℂ), (∀ g ∈ Γ, g ∉ H → Ψ g = 0) → (∀ g ∈ Γ, ∀ k ∈ J, Ψ (g * k) = Ψ g) → HasSum (fun y : H ⧸ J.subgroupOf H => Ψ (y.out : H)) z → HasSum (fun y : Γ ⧸ K.subgroupOf Γ => Ψ (y.out : Γ)) ((K.relIndex J : ℂ) * z) := by
  first | exact @GlobalTheory.hasSum_cosets_smaller_level_relIndex_mul | exact GlobalTheory.hasSum_cosets_smaller_level_relIndex_mul | (intros; apply GlobalTheory.hasSum_cosets_smaller_level_relIndex_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumEqSumOfMatchingFamilyStatement
section
open Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_sum_of_hasSum_of_bijective_matching : ∀ (C : Type 1) (n : ℕ) (m : C → ℕ) (t : C → ℂ) (m' : Fin n → ℕ) (c : Fin n → ℂ) (R : C → Fin n → Prop) (s : ℂ), HasSum (fun x => (m x : ℂ) * t x) s → (∀ x, m x ≠ 0 → t x ≠ 0 → ∃ i, R x i) → (∀ i, m' i ≠ 0 → ∃ x, R x i) → (∀ x i, R x i → m x = m' i ∧ t x = c i) → (∀ x i j, R x i → R x j → i = j) → (∀ x y i, R x i → R y i → x = y) → s = ∑ i, (m' i : ℂ) * c i := by
  first | exact @GlobalTheory.hasSum_eq_sum_of_matching_family | exact GlobalTheory.hasSum_eq_sum_of_matching_family | (intros; apply GlobalTheory.hasSum_eq_sum_of_matching_family <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumQuotientTransportStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_quotient_of_hasSum_mulEquiv_quotient : ∀ (G H : Type) [Group G] [Group H] (e : G ≃* H) (K : Subgroup G) (K' : Subgroup H), (∀ g, g ∈ K ↔ e g ∈ K') → ∀ f : G → ℂ, (∀ g, ∀ k ∈ K, f (g * k) = f g) → ∀ s : ℂ, HasSum (fun b : H ⧸ K' => f (e.symm b.out)) s → HasSum (fun a : G ⧸ K => f a.out) s := by
  first | exact @GlobalTheory.hasSum_quotient_transport | exact GlobalTheory.hasSum_quotient_transport | (intros; apply GlobalTheory.hasSum_quotient_transport <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergSmoothRapidSuperpositionTranslates
section
open MeasureTheory Complex
open scoped ContDiff Real

noncomputable section

namespace GlobalTheory.RealWeil

namespace Superpos

variable {V Y B : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]

def ph (om : V →L[ℝ] V →L[ℝ] ℝ) (ι : Y →L[ℝ] V) (v : V) (y : Y) : ℂ :=
  cexp (2 * π * I * (om v (ι y) : ℂ))

def Mom (ν : Measure Y) (h : Y → ℂ) : Prop :=
  Continuous h ∧ ∀ n : ℕ, Integrable (fun y => ‖y‖ ^ n * ‖h y‖) ν

def itg (om : V →L[ℝ] V →L[ℝ] ℝ) (ρ : V → B →L[ℂ] B) (ι : Y →L[ℝ] V) (h : Y → ℂ) (g : V → B) (v : V) (y : Y) : B :=
  (h y * ph om ι v y) • ρ (ι y) (g v)

theorem norm_ph (om : V →L[ℝ] V →L[ℝ] ℝ) (ι : Y →L[ℝ] V) (v : V) (y : Y) : ‖ph om ι v y‖ = 1 := by
  unfold ph
  rw [show (2 * π * I * (om v (ι y) : ℂ)) = ((2 * π * om v (ι y) : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem continuous_ph (om : V →L[ℝ] V →L[ℝ] ℝ) (ι : Y →L[ℝ] V) (v : V) : Continuous (ph om ι v) :=
  Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp ((om v).continuous.comp ι.continuous)))

variable {om : V →L[ℝ] V →L[ℝ] ℝ} {ρ : V → B →L[ℂ] B} {ι : Y →L[ℝ] V} {ν : Measure Y}

theorem continuous_itg (hρ : IsHeis (fun x y => om x y) ρ) {h : Y → ℂ} (hh : Continuous h) (g : V → B) (v : V) :
    Continuous (itg om ρ ι h g v) :=
  (hh.mul (continuous_ph om ι v)).smul ((hρ.2.2.2 (g v)).comp ι.continuous)

theorem norm_itg (hρ : IsHeis (fun x y => om x y) ρ) (h : Y → ℂ) (g : V → B) (v : V) (y : Y) :
    ‖itg om ρ ι h g v y‖ = ‖h y‖ * ‖g v‖ := by
  simp [itg, norm_smul, norm_ph, hρ.2.2.1]

theorem integrable_itg (hρ : IsHeis (fun x y => om x y) ρ) {h : Y → ℂ} (hh : Mom ν h) (g : V → B) (v : V) :
    Integrable (itg om ρ ι h g v) ν := by
  refine Integrable.mono' ((hh.2 0).mul_const ‖g v‖) (continuous_itg hρ hh.1 g v).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  rw [norm_itg hρ]; simp

def dh (om : V →L[ℝ] V →L[ℝ] ℝ) (ι : Y →L[ℝ] V) (h : Y → ℂ) (z : V) (y : Y) : ℂ :=
  h y * (2 * π * I * (om z (ι y) : ℂ))

theorem mom_dh {h : Y → ℂ} (hh : Mom ν h) (z : V) : Mom ν (dh om ι h z) := by
  refine ⟨hh.1.mul (continuous_const.mul (Complex.continuous_ofReal.comp ((om z).continuous.comp ι.continuous))),
    fun n => ?_⟩
  refine Integrable.mono' ((hh.2 (n + 1)).const_mul (2 * π * ‖om‖ * ‖z‖ * ‖ι‖))
    ((continuous_norm.pow n).mul (continuous_norm.comp (hh.1.mul (continuous_const.mul
      (Complex.continuous_ofReal.comp ((om z).continuous.comp ι.continuous)))))).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  have e1 : ‖om z (ι y)‖ ≤ ‖om‖ * ‖z‖ * (‖ι‖ * ‖y‖) :=
    (om.le_opNorm₂ z (ι y)).trans (by gcongr; exact ι.le_opNorm y)
  have e2 : ‖(2 * π * I : ℂ)‖ = 2 * π := by simp [abs_of_pos Real.pi_pos]
  rw [Real.norm_of_nonneg (by positivity), dh, norm_mul, norm_mul (2 * π * I : ℂ), e2, Complex.norm_real]
  have := Real.pi_pos
  have hy := norm_nonneg y
  have hhy := norm_nonneg (h y)
  calc ‖y‖ ^ n * (‖h y‖ * (2 * π * ‖om z (ι y)‖)) ≤ ‖y‖ ^ n * (‖h y‖ * (2 * π * (‖om‖ * ‖z‖ * (‖ι‖ * ‖y‖)))) := by
        gcongr
    _ = 2 * π * ‖om‖ * ‖z‖ * ‖ι‖ * (‖y‖ ^ (n + 1) * ‖h y‖) := by ring

def dI (om : V →L[ℝ] V →L[ℝ] ℝ) (ρ : V → B →L[ℂ] B) (ι : Y →L[ℝ] V) (h : Y → ℂ) (g : V → B) (v : V) (y : Y) :
    V →L[ℝ] B :=
  (h y * ph om ι v y) • (((ρ (ι y)).restrictScalars ℝ).comp (fderiv ℝ g v)) +
    (h y • (ph om ι v y • ((2 * π * I : ℂ) • (Complex.ofRealCLM.comp (om.flip (ι y)))))).smulRight (ρ (ι y) (g v))

theorem dI_apply (h : Y → ℂ) (g : V → B) (v : V) (y : Y) (z : V) :
    dI om ρ ι h g v y z = itg om ρ ι (dh om ι h z) g v y + itg om ρ ι h (fun w => fderiv ℝ g w z) v y := by
  simp only [dI, itg, dh, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.smulRight_apply,
    Complex.ofRealCLM_apply, ContinuousLinearMap.flip_apply, smul_eq_mul, smul_smul]
  rw [add_comm]
  congr 2
  ring

theorem hasFDerivAt_itg {g : V → B} (hg : Differentiable ℝ g) (h : Y → ℂ) (v : V) (y : Y) :
    HasFDerivAt (fun w => itg om ρ ι h g w y) (dI om ρ ι h g v y) v := by
  have b1 : HasFDerivAt (fun w : V => ((om w (ι y) : ℝ) : ℂ)) (Complex.ofRealCLM.comp (om.flip (ι y))) v :=
    (Complex.ofRealCLM.comp (om.flip (ι y))).hasFDerivAt
  have b2 := ((b1.const_mul (2 * π * I : ℂ)).cexp).const_mul (h y)
  have b3 : HasFDerivAt (fun w => ρ (ι y) (g w)) (((ρ (ι y)).restrictScalars ℝ).comp (fderiv ℝ g v)) v :=
    ((ρ (ι y)).restrictScalars ℝ).hasFDerivAt.comp v (hg v).hasFDerivAt
  exact b2.smul b3

theorem norm_dh_le (h : Y → ℂ) (z : V) (y : Y) :
    ‖dh om ι h z y‖ ≤ 2 * π * ‖om‖ * ‖ι‖ * ‖y‖ * ‖z‖ * ‖h y‖ := by
  have e1 : ‖om z (ι y)‖ ≤ ‖om‖ * ‖z‖ * (‖ι‖ * ‖y‖) :=
    (om.le_opNorm₂ z (ι y)).trans (by gcongr; exact ι.le_opNorm y)
  have e2 : ‖(2 * π * I : ℂ)‖ = 2 * π := by simp [abs_of_pos Real.pi_pos]
  rw [dh, norm_mul, norm_mul (2 * π * I : ℂ), e2, Complex.norm_real]
  have := Real.pi_pos
  have hhy := norm_nonneg (h y)
  calc ‖h y‖ * (2 * π * ‖om z (ι y)‖) ≤ ‖h y‖ * (2 * π * (‖om‖ * ‖z‖ * (‖ι‖ * ‖y‖))) := by gcongr
    _ = 2 * π * ‖om‖ * ‖ι‖ * ‖y‖ * ‖z‖ * ‖h y‖ := by ring

theorem continuous_dI (hρ : IsHeis (fun x y => om x y) ρ) {h : Y → ℂ} (hh : Continuous h) (g : V → B) (v : V) :
    Continuous (dI om ρ ι h g v) := by
  refine continuous_clm_apply.2 fun z => ?_
  simp only [dI_apply]
  exact (continuous_itg hρ (hh.mul (continuous_const.mul
    (Complex.continuous_ofReal.comp ((om z).continuous.comp ι.continuous)))) g v).add (continuous_itg hρ hh _ v)

theorem exists_bound (hρ : IsHeis (fun x y => om x y) ρ) {h : Y → ℂ} (hh : Mom ν h) {g : V → B}
    (hg : ContDiff ℝ ∞ g) (v₀ : V) : ∃ bd : Y → ℝ, Integrable bd ν ∧
      ∀ y, ∀ v ∈ Metric.closedBall v₀ 1, ‖dI om ρ ι h g v y‖ ≤ bd y := by
  obtain ⟨Cg, hCg⟩ := (isCompact_closedBall v₀ 1).exists_bound_of_continuousOn hg.continuous.continuousOn
  obtain ⟨Cd, hCd⟩ :=
    (isCompact_closedBall v₀ 1).exists_bound_of_continuousOn (hg.continuous_fderiv (by simp)).continuousOn
  have hCg0 : 0 ≤ Cg := (norm_nonneg _).trans (hCg v₀ (Metric.mem_closedBall_self zero_le_one))
  have hCd0 : 0 ≤ Cd := (norm_nonneg _).trans (hCd v₀ (Metric.mem_closedBall_self zero_le_one))
  have hK : 0 ≤ 2 * π * ‖om‖ * ‖ι‖ * Cg := by have := Real.pi_pos; positivity
  refine ⟨fun y => ‖h y‖ * (Cd + 2 * π * ‖om‖ * ‖ι‖ * Cg * ‖y‖), ?_, fun y v hv => ?_⟩
  · refine (((hh.2 0).const_mul Cd).add ((hh.2 1).const_mul (2 * π * ‖om‖ * ‖ι‖ * Cg))).congr
      (Filter.Eventually.of_forall fun y => ?_)
    simp only [Pi.add_apply, pow_zero, pow_one]
    ring
  · refine ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg (norm_nonneg _) (add_nonneg hCd0 (mul_nonneg hK (norm_nonneg _)))) fun z => ?_
    rw [dI_apply]
    refine (norm_add_le _ _).trans ?_
    rw [norm_itg hρ, norm_itg hρ]
    have hDz : ‖fderiv ℝ g v z‖ ≤ Cd * ‖z‖ :=
      ((fderiv ℝ g v).le_opNorm z).trans (mul_le_mul_of_nonneg_right (hCd v hv) (norm_nonneg _))
    calc ‖dh om ι h z y‖ * ‖g v‖ + ‖h y‖ * ‖fderiv ℝ g v z‖
        ≤ (2 * π * ‖om‖ * ‖ι‖ * ‖y‖ * ‖z‖ * ‖h y‖) * Cg + ‖h y‖ * (Cd * ‖z‖) :=
          add_le_add (mul_le_mul (norm_dh_le h z y) (hCg v hv) (norm_nonneg _) (by have := Real.pi_pos; positivity))
            (mul_le_mul_of_nonneg_left hDz (norm_nonneg _))
      _ = ‖h y‖ * (Cd + 2 * π * ‖om‖ * ‖ι‖ * Cg * ‖y‖) * ‖z‖ := by ring

theorem hasFDerivAt_int (hρ : IsHeis (fun x y => om x y) ρ) {h : Y → ℂ} (hh : Mom ν h) {g : V → B}
    (hg : ContDiff ℝ ∞ g) (v₀ : V) :
    HasFDerivAt (fun v => ∫ y, itg om ρ ι h g v y ∂ν) (∫ y, dI om ρ ι h g v₀ y ∂ν) v₀ := by
  obtain ⟨bd, hbd, hb⟩ := exists_bound hρ hh hg v₀
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (Metric.closedBall_mem_nhds v₀ one_pos)
    (Filter.Eventually.of_forall fun v => (continuous_itg hρ hh.1 g v).aestronglyMeasurable)
    (integrable_itg hρ hh g v₀) (continuous_dI hρ hh.1 g v₀).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y v hv => hb y v hv) hbd
    (Filter.Eventually.of_forall fun y v _ => hasFDerivAt_itg (hg.differentiable (by simp)) h v y)

theorem fderiv_int_apply (hρ : IsHeis (fun x y => om x y) ρ) {h : Y → ℂ} (hh : Mom ν h) {g : V → B}
    (hg : ContDiff ℝ ∞ g) (v z : V) :
    fderiv ℝ (fun v => ∫ y, itg om ρ ι h g v y ∂ν) v z =
      (∫ y, itg om ρ ι (dh om ι h z) g v y ∂ν) + ∫ y, itg om ρ ι h (fun w => fderiv ℝ g w z) v y ∂ν := by
  obtain ⟨bd, hbd, hb⟩ := exists_bound hρ hh hg v
  have hi : Integrable (dI om ρ ι h g v) ν := hbd.mono' (continuous_dI hρ hh.1 g v).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => hb y v (Metric.mem_closedBall_self zero_le_one))
  rw [(hasFDerivAt_int hρ hh hg v).fderiv, ContinuousLinearMap.integral_apply hi]
  simp only [dI_apply]
  exact integral_add (integrable_itg hρ (mom_dh hh z) g v) (integrable_itg hρ hh _ v)

theorem contDiff_int (hρ : IsHeis (fun x y => om x y) ρ) (n : ℕ) : ∀ h : Y → ℂ, Mom ν h → ∀ g : V → B,
    ContDiff ℝ ∞ g → ContDiff ℝ n fun v => ∫ y, itg om ρ ι h g v y ∂ν := by
  induction n with
  | zero =>
    intro h hh g hg
    exact contDiff_zero.2 (Differentiable.continuous fun v => (hasFDerivAt_int hρ hh hg v).differentiableAt)
  | succ n ih =>
    intro h hh g hg
    rw [Nat.cast_succ, contDiff_succ_iff_fderiv_apply]
    refine ⟨fun v => (hasFDerivAt_int hρ hh hg v).differentiableAt, by simp, fun z => ?_⟩
    simp only [fderiv_int_apply hρ hh hg]
    have hg' : ContDiff ℝ ∞ fun w => fderiv ℝ g w z :=
      (hg.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    exact (ih _ (mom_dh hh z) g hg).add (ih h hh _ hg')

end Superpos

theorem sm_superpos : ∀ (V Y : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] [MeasurableSpace Y] [BorelSpace Y] (ν : MeasureTheory.Measure Y) (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (om : V →L[ℝ] V →L[ℝ] ℝ) (ρ : V → B →L[ℂ] B), (∀ x, om x x = 0) → GlobalTheory.RealWeil.IsHeis (fun x y => om x y) ρ → ∀ (ι : Y →L[ℝ] V) (c : Y → ℂ), Continuous c → (∀ n : ℕ, MeasureTheory.Integrable (fun y => ‖y‖ ^ n * ‖c y‖) ν) → ∀ f : B, GlobalTheory.RealWeil.Sm ρ f → GlobalTheory.RealWeil.Sm ρ (∫ y, c y • ρ (ι y) f ∂ν) := by
  intro V Y _ _ _ _ _ _ _ _ ν B _ _ _ om ρ hom hρ ι c hc hm f hf
  have skew : ∀ v w, om w v = -om v w := by
    intro v w
    have := hom (v + w)
    simp only [map_add, ContinuousLinearMap.add_apply, hom] at this
    linarith
  have comm : ∀ v w b, ρ v (ρ w b) = cexp (2 * π * I * (om v w : ℂ)) • ρ w (ρ v b) := by
    intro v w b
    rw [hρ.2.1 v w, hρ.2.1 w v, smul_smul, ← Complex.exp_add, add_comm w v]
    simp only [skew v w]
    congr 2
    push_cast
    ring
  have hint : Integrable (fun y => c y • ρ (ι y) f) ν := by
    refine Integrable.mono' ((hm 0).mul_const ‖f‖) (hc.smul ((hρ.2.2.2 f).comp ι.continuous)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    simp [norm_smul, hρ.2.2.1]
  have e : (fun v => ρ v (∫ y, c y • ρ (ι y) f ∂ν)) =
      fun v => ∫ y, Superpos.itg om ρ ι c (fun w => ρ w f) v y ∂ν := by
    funext v
    rw [← ContinuousLinearMap.integral_comp_comm _ hint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [Superpos.itg, Superpos.ph, map_smul, comm v (ι y), smul_smul]
  unfold Sm
  rw [e]
  exact contDiff_infty.2 fun n => Superpos.contDiff_int hρ n c ⟨hc, hm⟩ _ hf

end GlobalTheory.RealWeil
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InjectiveSumOfLinIndepIntertwinersStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.injective_sum_of_linIndep_intertwiners : ∀ (G : Type) [Group G] (N X : Type) [AddCommGroup N] [Module ℂ N]
    [AddCommGroup X] [Module ℂ X] (π : Representation ℂ G N) (ρ : Representation ℂ G X), π.IsIrreducible →
    (∀ φ : π.IntertwiningMap π, ∃ c : ℂ, φ.toLinearMap = c • LinearMap.id) →
    ∀ (m : ℕ) (φ : Fin m → π.IntertwiningMap ρ), LinearIndependent ℂ φ →
    Function.Injective (fun w : Fin m → N => ∑ j, φ j (w j)) := by
  first | exact @GlobalTheory.intertwiners_indep_injective | exact GlobalTheory.intertwiners_indep_injective | (intros; apply GlobalTheory.intertwiners_indep_injective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InnerMapEqConstMulProdInnerStatement
section
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inner_multilinearMap_eq_mul_prod_inner : ∀ {ι : Type} [Fintype ι] {Xs : ι → Type} [∀ i, NormedAddCommGroup (Xs i)] [∀ i, InnerProductSpace ℂ (Xs i)] {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (f : MultilinearMap ℂ Xs E) (K : ℝ), (∀ x, ‖f x‖ ^ 2 = K * ∏ i, ‖x i‖ ^ 2) → ∀ x y, ⟪f x, f y⟫_ℂ = (K : ℂ) * ∏ i, ⟪x i, y i⟫_ℂ := by
  first | exact @GlobalTheory.MultilinearMap.inner_map_eq_const_mul_prod_inner | exact GlobalTheory.MultilinearMap.inner_map_eq_const_mul_prod_inner | (intros; apply GlobalTheory.MultilinearMap.inner_map_eq_const_mul_prod_inner <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOfTsumTranslateNormLeStatement
section
open MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_of_tsum_norm_translate_le : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [Countable Γ] (μ : Measure G), μ.IsAddLeftInvariant → ∀ 𝓕 : Set G, IsAddFundamentalDomain Γ 𝓕 μ → μ 𝓕 < ⊤ → ∀ c : G → ℂ, Continuous c → ∀ C : ℝ, (∀ w : G, Summable (fun γ : Γ => ‖c ((γ : G) + w)‖) ∧ ∑' γ : Γ, ‖c ((γ : G) + w)‖ ≤ C) → Integrable c μ := by
  first | exact @GlobalTheory.integrable_of_tsum_translate_norm_le | exact GlobalTheory.integrable_of_tsum_translate_norm_le | (intros; apply GlobalTheory.integrable_of_tsum_translate_norm_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralContinuousMultilinearMapPiMeasureStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_continuousMultilinearMap_pi_measure : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (X : ι → Type) [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)] (E : ι → Type) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)] [∀ i, CompleteSpace (E i)] (F : Type) [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] (Φ : ContinuousMultilinearMap ℂ E F) (g : ∀ i, X i → E i), (∀ i, Integrable (g i) (μ i)) → Integrable (fun x : ∀ i, X i => Φ fun i => g i (x i)) (Measure.pi μ) ∧ ∫ x, Φ (fun i => g i (x i)) ∂Measure.pi μ = Φ fun i => ∫ y, g i y ∂μ i := by
  first | exact @GlobalTheory.MultilinFubini.integral_multilinear_pi | exact GlobalTheory.MultilinFubini.integral_multilinear_pi | (intros; apply GlobalTheory.MultilinFubini.integral_multilinear_pi <;> assumption)
end

