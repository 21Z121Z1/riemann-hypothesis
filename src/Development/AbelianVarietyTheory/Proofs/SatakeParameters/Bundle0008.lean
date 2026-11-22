import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ResidueDegreeOneOfLinearMem
section
namespace GlobalTheory

theorem residue_degree_one_of_linear_mem : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (P : Ideal B) [P.IsPrime] (θ : B) (D a b : A), (P.comap (algebraMap A B)).IsMaximal → (∀ y : B, ∃ u v : A, algebraMap A B D * y = algebraMap A B u + algebraMap A B v * θ) → algebraMap A B D ∉ P → algebraMap A B b ∉ P → algebraMap A B a + algebraMap A B b * θ ∈ P → ∀ y : B, ∃ u : A, y - algebraMap A B u ∈ P := by
  intro A B _ _ _ P _ θ D a b hmax hgen hD hb hab y
  obtain ⟨b', i, hi, hbi⟩ := hmax.exists_inv (x := b) (by rwa [Ideal.mem_comap])
  obtain ⟨D', j, hj, hDj⟩ := hmax.exists_inv (x := D) (by rwa [Ideal.mem_comap])
  rw [Ideal.mem_comap] at hi hj
  obtain ⟨u, v, hy⟩ := hgen y
  have hbi' := congrArg (algebraMap A B) hbi
  have hDj' := congrArg (algebraMap A B) hDj
  simp only [map_add, map_mul, map_one] at hbi' hDj'
  refine ⟨D' * (u - v * a * b'), ?_⟩
  have key : y - algebraMap A B (D' * (u - v * a * b')) =
      algebraMap A B D' * algebraMap A B v * algebraMap A B b' * (algebraMap A B a + algebraMap A B b * θ)
      + (algebraMap A B D' * algebraMap A B v * θ) * algebraMap A B i + y * algebraMap A B j := by
    simp only [map_sub, map_mul]
    linear_combination algebraMap A B D' * hy - y * hDj' - algebraMap A B D' * algebraMap A B v * θ * hbi'
  rw [key]
  exact P.add_mem (P.add_mem (P.mul_mem_left _ hab) (P.mul_mem_left _ hi)) (P.mul_mem_left _ hj)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SegmentEigenvalueSumFormula
section
namespace GlobalTheory

theorem multiset_mem_list_sum' {α : Type*} (l : List (Multiset α)) (x : α) :
    x ∈ l.sum ↔ ∃ m ∈ l, x ∈ m := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.sum_cons, Multiset.mem_add, ih]

theorem multiset_le_list_sum' {α : Type*} (l : List (Multiset α)) (m : Multiset α) (h : m ∈ l) :
    m ≤ l.sum := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    rw [List.sum_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact Multiset.le_add_right _ _
    · exact (ih h).trans (Multiset.le_add_left _ _)

theorem norm_natCast_cpow_ofReal {q : ℕ} (hq : 0 < q) (s : ℝ) :
    ‖(q : ℂ) ^ ((s : ℝ) : ℂ)‖ = (q : ℝ) ^ s := by
  rw [Complex.norm_natCast_cpow_of_pos hq]
  simp

theorem rpow_exponent_inj_of_one_lt {b : ℝ} (hb : 1 < b) {x y : ℝ} (h : b ^ x = b ^ y) : x = y := by
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · exact absurd h (ne_of_lt (Real.rpow_lt_rpow_of_exponent_lt hb hxy))
  · exact hxy
  · exact absurd h (ne_of_gt (Real.rpow_lt_rpow_of_exponent_lt hb hxy))

theorem longest_segment_unique_of_bounded_remainder :
    ∀ (q t : ℕ) (L : List (ℕ × Multiset ℂ)) (Rw : Multiset ℂ) (c : ℂ), 1 < q → 1 ≤ t → ‖c‖ = 1 → (∀ x ∈ Rw, ‖x‖ < (q : ℝ) ^ (((t : ℝ) - 1) / 2)) → (∀ e ∈ L, 1 ≤ e.1 ∧ e.2 ≠ 0 ∧ ∀ α ∈ e.2, ‖α‖ = 1) → (L.map fun e => ((List.range e.1).map fun k => e.2.map (· * (q : ℂ) ^ (((((e.1 : ℝ) - 1) / 2 - (k : ℝ) : ℝ)) : ℂ))).sum).sum = Rw + ((List.range t).map fun k => ({c * (q : ℂ) ^ (((((t : ℝ) - 1) / 2 - (k : ℝ) : ℝ)) : ℂ)} : Multiset ℂ)).sum → (∃ e ∈ L, t ≤ e.1) ∧ ∀ e ∈ L, t ≤ e.1 → e.1 = t ∧ e.2 = {c} := by
  intro q t L Rw c hq ht hc hRw hL hsum
  have hq0 : 0 < q := by omega
  have hq1 : (1:ℝ) < q := by exact_mod_cast hq
  have nm : ∀ s : ℝ, ‖(q : ℂ) ^ ((s : ℝ) : ℂ)‖ = (q : ℝ) ^ s := norm_natCast_cpow_ofReal hq0
  have Pne : ∀ s : ℝ, (q : ℂ) ^ ((s : ℝ) : ℂ) ≠ 0 := by
    intro s h0
    have h := nm s
    rw [h0, norm_zero] at h
    exact (Real.rpow_pos_of_pos (by positivity) s).ne' h.symm
  simp only [bind_pure_comp, List.map_eq_map, List.map_map, Function.comp_def] at hsum
  obtain ⟨n, rfl⟩ : ∃ n, t = n + 1 := ⟨t - 1, by omega⟩
  have hright : ((List.range (n+1)).map fun (k : ℕ) => ({c * (q : ℂ) ^ (((((n+1:ℕ) : ℝ) - 1) / 2 - (k : ℝ) : ℝ) : ℂ)} : Multiset ℂ)).sum
      = {c * (q : ℂ) ^ (((((n+1:ℕ) : ℝ) - 1) / 2 : ℝ) : ℂ)} + ((List.range n).map fun (k : ℕ) => ({c * (q : ℂ) ^ (((((n+1:ℕ) : ℝ) - 1) / 2 - ((k:ℝ) + 1) : ℝ) : ℂ)} : Multiset ℂ)).sum := by
    rw [List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
    congr 2
    · simp
    · apply List.map_congr_left
      intro k _
      simp
  rw [hright] at hsum
  have hsmall : ∀ x ∈ Rw + ((List.range n).map fun (k : ℕ) => ({c * (q : ℂ) ^ (((((n+1:ℕ) : ℝ) - 1) / 2 - ((k:ℝ) + 1) : ℝ) : ℂ)} : Multiset ℂ)).sum,
      ‖x‖ < (q : ℝ) ^ ((((n+1:ℕ) : ℝ) - 1) / 2) := by
    intro x hx
    rcases Multiset.mem_add.1 hx with hx | hx
    · exact hRw x hx
    · obtain ⟨m, hm, hxm⟩ := (multiset_mem_list_sum' _ _).1 hx
      obtain ⟨k, _, rfl⟩ := List.mem_map.1 hm
      rw [Multiset.mem_singleton] at hxm
      subst hxm
      rw [norm_mul, hc, nm, one_mul]
      exact Real.rpow_lt_rpow_of_exponent_lt hq1 (by have := Nat.cast_nonneg (α := ℝ) k; linarith)
  have hsum' : (L.map fun e => ((List.range e.1).map fun k => e.2.map (· * (q : ℂ) ^ (((((e.1 : ℝ) - 1) / 2 - (k : ℝ) : ℝ)) : ℂ))).sum).sum
      = {c * (q : ℂ) ^ (((((n+1:ℕ) : ℝ) - 1) / 2 : ℝ) : ℂ)} + (Rw + ((List.range n).map fun (k : ℕ) => ({c * (q : ℂ) ^ (((((n+1:ℕ) : ℝ) - 1) / 2 - ((k:ℝ) + 1) : ℝ) : ℂ)} : Multiset ℂ)).sum) := by
    rw [hsum, add_left_comm]
  clear hsum hright
  constructor
  · have hmem := hsum' ▸ Multiset.mem_add.2 (Or.inl (Multiset.mem_singleton_self _))
    obtain ⟨m, hm, hxm⟩ := (multiset_mem_list_sum' _ _).1 hmem
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hm
    obtain ⟨m', hm', hxm'⟩ := (multiset_mem_list_sum' _ _).1 hxm
    obtain ⟨k, _, rfl⟩ := List.mem_map.1 hm'
    obtain ⟨α, hα, hαeq⟩ := Multiset.mem_map.1 hxm'
    have hn := congrArg norm hαeq
    rw [norm_mul, norm_mul, (hL e he).2.2 α hα, hc, nm, nm, one_mul, one_mul] at hn
    have hx := rpow_exponent_inj_of_one_lt hq1 hn
    refine ⟨e, he, ?_⟩
    have : ((n + 1 : ℕ) : ℝ) ≤ (e.1 : ℝ) := by
      have hk : (0:ℝ) ≤ k := by positivity
      push_cast at hx ⊢
      linarith
    exact_mod_cast this
  · intro e he hte
    obtain ⟨hd1, hE0, hEn⟩ := hL e he
    have hle : e.2.map (· * (q : ℂ) ^ (((((e.1 : ℝ) - 1) / 2 - ((0:ℕ) : ℝ) : ℝ)) : ℂ))
        ≤ {c * (q : ℂ) ^ (((((n+1:ℕ) : ℝ) - 1) / 2 : ℝ) : ℂ)} + (Rw + ((List.range n).map fun (k : ℕ) => ({c * (q : ℂ) ^ (((((n+1:ℕ) : ℝ) - 1) / 2 - ((k:ℝ) + 1) : ℝ) : ℂ)} : Multiset ℂ)).sum) := by
      rw [← hsum']
      refine (multiset_le_list_sum' ((List.range e.1).map fun (k : ℕ) => e.2.map (· * (q : ℂ) ^ (((((e.1 : ℝ) - 1) / 2 - (k : ℝ) : ℝ)) : ℂ))) _ ?_).trans (multiset_le_list_sum' _ _ ?_)
      · exact List.mem_map.2 ⟨0, List.mem_range.2 (by omega), rfl⟩
      · exact List.mem_map.2 ⟨e, he, rfl⟩
    have h1 := Multiset.filter_le_filter (fun x : ℂ => (q : ℝ) ^ ((((n+1:ℕ) : ℝ) - 1) / 2) ≤ ‖x‖) hle
    rw [Multiset.filter_eq_self.2, Multiset.filter_add, Multiset.filter_eq_nil.2 (fun x hx => not_le.2 (hsmall x hx)), add_zero] at h1
    swap
    · intro x hx
      obtain ⟨α, hα, rfl⟩ := Multiset.mem_map.1 hx
      rw [norm_mul, hEn α hα, nm, one_mul]
      apply Real.rpow_le_rpow_of_exponent_le hq1.le
      have : ((n + 1 : ℕ) : ℝ) ≤ (e.1 : ℝ) := by exact_mod_cast hte
      push_cast at this ⊢
      linarith
    have h2 := h1.trans (Multiset.filter_le _ _)
    have hcard : Multiset.card ({c * (q : ℂ) ^ (((((n+1:ℕ) : ℝ) - 1) / 2 : ℝ) : ℂ)} : Multiset ℂ) ≤ Multiset.card (e.2.map (· * (q : ℂ) ^ (((((e.1 : ℝ) - 1) / 2 - ((0:ℕ) : ℝ) : ℝ)) : ℂ))) := by
      rw [Multiset.card_singleton, Multiset.card_map]
      exact Multiset.card_pos.2 hE0
    have h3 := Multiset.eq_of_le_of_card_le h2 hcard
    obtain ⟨α, hEα, hαeq⟩ := Multiset.map_eq_singleton.1 h3
    have hα : α ∈ e.2 := by rw [hEα]; exact Multiset.mem_singleton_self _
    have hn := congrArg norm hαeq
    rw [norm_mul, norm_mul, hEn α hα, hc, nm, nm, one_mul, one_mul] at hn
    have hx := rpow_exponent_inj_of_one_lt hq1 hn
    have hd : e.1 = n + 1 := by
      have : (e.1 : ℝ) = ((n + 1 : ℕ) : ℝ) := by push_cast at hx ⊢; linarith
      exact_mod_cast this
    refine ⟨hd, ?_⟩
    rw [hEα]
    congr 1
    simp only [hd, Nat.cast_zero, sub_zero] at hαeq
    exact mul_right_cancel₀ (Pne _) hαeq

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanExtendScalarsInfEqBotOfInfEqBot
section
namespace GlobalTheory

theorem span_map_inf_eq_bot_of_inf_eq_bot : ∀ {k : Type} [Field k] {L : Type} [Field L] (f : k →+* L)
    {a : ℕ} (W₁ W₂ : Submodule k (Fin a → k)), W₁ ⊓ W₂ = ⊥ →
    Submodule.span L ((fun v => f ∘ v) '' (W₁ : Set (Fin a → k))) ⊓
      Submodule.span L ((fun v => f ∘ v) '' (W₂ : Set (Fin a → k))) = ⊥ := by
  intro k _ L _ f a W₁ W₂ h
  have hker : LinearMap.ker (W₂.mkQ ∘ₗ W₁.subtype) = ⊥ := by
    refine LinearMap.ker_eq_bot'.mpr ?_
    intro w hw
    have hw2 : (w : Fin a → k) ∈ W₂ := by
      simpa [Submodule.Quotient.mk_eq_zero] using hw
    have hw12 : (w : Fin a → k) ∈ W₁ ⊓ W₂ := ⟨w.2, hw2⟩
    rw [h] at hw12
    exact Subtype.ext (by simpa using hw12)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hker
  let p : (Fin a → k) →ₗ[k] (Fin a → k) := W₁.subtype ∘ₗ g ∘ₗ W₂.mkQ
  have hp1 : ∀ w ∈ W₁, p w = w := by
    intro w hw
    have := LinearMap.congr_fun hg (⟨w, hw⟩ : W₁)
    have h2 : g (W₂.mkQ w) = ⟨w, hw⟩ := by simpa using this
    simp only [p, LinearMap.comp_apply, h2]
    rfl
  have hp2 : ∀ w ∈ W₂, p w = 0 := by
    intro w hw
    have h2 : W₂.mkQ w = 0 := by simpa [Submodule.Quotient.mk_eq_zero] using hw
    simp [p, h2]
  let P : (Fin a → L) →ₗ[L] (Fin a → L) := Matrix.mulVecLin ((LinearMap.toMatrix' p).map f)
  have hP : ∀ v : Fin a → k, P (f ∘ v) = f ∘ (p v) := by
    intro v
    funext i
    have := RingHom.map_mulVec f (LinearMap.toMatrix' p) v i
    simpa [P, LinearMap.toMatrix'_mulVec] using this.symm
  have hS1 : ∀ x ∈ Submodule.span L ((fun v => f ∘ v) '' (W₁ : Set (Fin a → k))), P x = x := by
    intro x hx
    have heq : Set.EqOn P (LinearMap.id : (Fin a → L) →ₗ[L] (Fin a → L))
        ((fun v => f ∘ v) '' (W₁ : Set (Fin a → k))) := by
      rintro _ ⟨v, hv, rfl⟩
      simp only [LinearMap.id_apply]
      rw [hP, hp1 v hv]
    exact LinearMap.eqOn_span heq hx
  have hS2 : ∀ x ∈ Submodule.span L ((fun v => f ∘ v) '' (W₂ : Set (Fin a → k))), P x = 0 := by
    intro x hx
    have heq : Set.EqOn P (0 : (Fin a → L) →ₗ[L] (Fin a → L))
        ((fun v => f ∘ v) '' (W₂ : Set (Fin a → k))) := by
      rintro _ ⟨v, hv, rfl⟩
      simp only [LinearMap.zero_apply]
      rw [hP, hp2 v hv]
      funext i
      simp
    exact LinearMap.eqOn_span heq hx
  refine (Submodule.eq_bot_iff _).mpr ?_
  rintro x ⟨hx1, hx2⟩
  rw [← hS1 x hx1, hS2 x hx2]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TraceMulEq
section
open Polynomial

attribute [local instance 100] LieRing.ofAssociativeRing

namespace GlobalTheory.AugmentationNilpotent

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]

theorem isNilpotent_of_trace_pow [CharZero K] [FiniteDimensional K V] (x : Module.End K V)
    (h : ∀ n : ℕ, LinearMap.trace K V (x ^ (n + 1)) = 0) : IsNilpotent x := by
  have hp : ∀ a : K[X], LinearMap.trace K V (aeval x (a * X)) = 0 := by
    intro a
    induction a using Polynomial.induction_on' with
    | add p q hp hq => rw [add_mul, map_add, map_add, hp, hq, add_zero]
    | monomial n c =>
      rw [monomial_mul_X, aeval_monomial, ← Algebra.smul_def, map_smul, h, smul_zero]
  obtain ⟨q, hq, hnd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd x.charpoly
    x.charpoly_monic.ne_zero 0
  set k := rootMultiplicity 0 x.charpoly
  rw [C_0, sub_zero] at hq hnd
  have hc : IsCoprime ((X : K[X]) ^ (k + 1)) q :=
    ((irreducible_X.coprime_iff_not_dvd).2 hnd).pow_left
  obtain ⟨a, b, hab⟩ := hc
  have h0 : aeval x (X ^ k * q) = 0 := by rw [← hq]; exact x.aeval_self_charpoly
  have hidem : IsIdempotentElem (aeval x (a * X ^ (k + 1))) := by
    unfold IsIdempotentElem
    rw [← map_mul]
    have : a * X ^ (k + 1) * (a * X ^ (k + 1)) = a * X ^ (k + 1) - (a * b * X) * (X ^ k * q) := by
      linear_combination (a * X ^ (k + 1)) * hab
    rw [this, map_sub, map_mul _ (a * b * X), h0, mul_zero, sub_zero]
  have he : aeval x (a * X ^ (k + 1)) = 0 := by
    apply (LinearMap.IsIdempotentElem.trace_eq_zero_iff hidem).1
    rw [pow_succ, ← mul_assoc]
    exact hp _
  refine ⟨k, ?_⟩
  have : (X : K[X]) ^ k = X ^ k * (a * X ^ (k + 1)) + b * (X ^ k * q) := by
    linear_combination (-X ^ k) * hab
  have h2 := congrArg (aeval x) this
  rw [map_add, map_mul _ (X ^ k), he, map_mul _ b, h0, map_pow, aeval_X] at h2
  simpa using h2

variable {Γ : Type} [Group Γ] (ρ : Representation K Γ V) (H : Subgroup Γ)

def aug : Submodule K (Module.End K V) := Submodule.span K {x | ∃ s ∈ H, x = ρ s - 1}

theorem sub_one_mem {s : Γ} (hs : s ∈ H) : ρ s - 1 ∈ aug ρ H := Submodule.subset_span ⟨s, hs, rfl⟩

theorem aug_mul {x y : Module.End K V} (hx : x ∈ aug ρ H) (hy : y ∈ aug ρ H) :
    x * y ∈ aug ρ H := by
  induction hx, hy using Submodule.span_induction₂ with
  | mem_mem x y hx hy =>
    obtain ⟨s, hs, rfl⟩ := hx
    obtain ⟨t, ht, rfl⟩ := hy
    have : (ρ s - 1) * (ρ t - 1) = (ρ (s * t) - 1) - (ρ s - 1) - (ρ t - 1) := by
      rw [map_mul]; noncomm_ring
    rw [this]
    exact sub_mem (sub_mem (sub_one_mem ρ H (mul_mem hs ht)) (sub_one_mem ρ H hs))
      (sub_one_mem ρ H ht)
  | zero_left => simp
  | zero_right => simp
  | add_left x y z _ _ _ h1 h2 => rw [add_mul]; exact add_mem h1 h2
  | add_right x y z _ _ _ h1 h2 => rw [mul_add]; exact add_mem h1 h2
  | smul_left r x y _ _ h => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ h
  | smul_right r x y _ _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ h

def augLie : LieSubalgebra K (Module.End K V) :=
  { aug ρ H with
    lie_mem' := fun {x y} hx hy => by
      rw [LieRing.of_associative_ring_bracket]
      exact (aug ρ H).sub_mem (aug_mul ρ H hx hy) (aug_mul ρ H hy hx) }

end GlobalTheory.AugmentationNilpotent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TraceQuotientEqOfProjective
section
namespace GlobalTheory

open IsLocalRing Module nonZeroDivisors IsLocalization.AtPrime

attribute [local instance] Ideal.Quotient.field

theorem trace_quotient_eq_of_projective (R S : Type) [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [CommRing S] [IsDomain S] [IsIntegrallyClosed S] [Algebra R S]
    [Module.IsTorsionFree R S] [Module.Finite R S] [Module.Projective R S] (p : Ideal R)
    [p.IsMaximal] (x : S) :
    Algebra.trace (R ⧸ p) (S ⧸ p.map (algebraMap R S)) (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk p (Algebra.intTrace R S x) := by
  let Rₚ := Localization.AtPrime p
  let Sₚ := Localization (Algebra.algebraMapSubmonoid S p.primeCompl)
  let : Algebra Rₚ Sₚ := localizationAlgebra p.primeCompl S
  have hp0 : p.primeCompl ≤ R⁰ := p.primeCompl_le_nonZeroDivisors
  have : IsDomain Rₚ := IsLocalization.isDomain_of_le_nonZeroDivisors _ hp0
  have : IsIntegrallyClosed Rₚ := isIntegrallyClosed_of_isLocalization _ _ hp0
  have : IsScalarTower R Rₚ Sₚ := IsScalarTower.of_algebraMap_eq'
    (by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp, ← IsScalarTower.algebraMap_eq])
  have : IsLocalization (Submonoid.map (algebraMap R S) (Ideal.primeCompl p)) Sₚ :=
    inferInstanceAs (IsLocalization (Algebra.algebraMapSubmonoid S p.primeCompl) Sₚ)
  have e : Algebra.algebraMapSubmonoid S p.primeCompl ≤ S⁰ :=
    Submonoid.map_le_of_le_comap _ <| p.primeCompl_le_nonZeroDivisors.trans
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (FaithfulSMul.algebraMap_injective _ _))
  have : IsDomain Sₚ := IsLocalization.isDomain_of_le_nonZeroDivisors _ e
  have : IsTorsionFree Rₚ Sₚ := by
    rw [isTorsionFree_iff_algebraMap_injective]
    exact IsLocalization.map_injective_of_injective p.primeCompl Rₚ Sₚ
      (FaithfulSMul.algebraMap_injective R S)
  have : Module.Finite Rₚ Sₚ := .of_isLocalization R S p.primeCompl
  have : IsIntegrallyClosed Sₚ := isIntegrallyClosed_of_isLocalization _ _ e
  have : Module.Flat Rₚ Sₚ :=
    Module.Flat.of_isLocalizedModule Rₚ p.primeCompl (IsScalarTower.toAlgHom R S Sₚ).toLinearMap
  have : Module.Free Rₚ Sₚ := Module.free_of_flat_of_isLocalRing
  apply (equivQuotMaximalIdeal p Rₚ).injective
  rw [trace_quotient_eq_trace_localization_quotient S p Rₚ Sₚ, IsScalarTower.algebraMap_eq S Sₚ,
    RingHom.comp_apply, Ideal.Quotient.algebraMap_eq, Algebra.trace_quotient_mk,
    RingEquiv.apply_symm_apply, ← Algebra.intTrace_eq_trace,
    ← Algebra.intTrace_eq_of_isLocalization R S p.primeCompl (Aₘ := Rₚ) (Bₘ := Sₚ) x,
    ← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
  simp only [equivQuotMaximalIdeal, RingHom.quotientKerEquivOfSurjective, RingEquiv.coe_trans,
    Function.comp_apply, Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfRightInverse.apply,
    RingHom.kerLift_mk]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TraceRMulPowEqZero
section
namespace GlobalTheory.TraceExpSmul

open Finset

variable {K : Type*} {n : Type*} [Field K] [Fintype n] [DecidableEq n]

theorem pow_mul_eq {R N : Matrix n n K} {d : K} (h : N * R = d • (R * N)) :
    ∀ j : ℕ, N ^ j * R = d ^ j • (R * N ^ j) := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, mul_assoc, h, mul_smul_comm, ← mul_assoc, ih, smul_mul_assoc, smul_smul,
      mul_assoc, ← pow_succ, pow_succ' d]

theorem pow_R_mul (R N : Matrix n n K) {d : K} (h : N * R = d • (R * N)) (k : ℕ) :
    ∀ m : ℕ, ∃ c : K, (R * N ^ k) ^ m = c • (R ^ m * N ^ (k * m)) := by
  intro m
  induction m with
  | zero => exact ⟨1, by simp⟩
  | succ m ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨c * d ^ (k * m), ?_⟩
    rw [pow_succ, hc, smul_mul_assoc, mul_assoc, ← mul_assoc (N ^ (k * m)), pow_mul_eq h,
      smul_mul_assoc, mul_smul_comm, smul_smul, ← mul_assoc, ← mul_assoc, ← pow_succ,
      mul_assoc, ← pow_add, Nat.mul_succ]

theorem trace_R_mul_pow_eq_zero {R N : Matrix n n K} (hN : IsNilpotent N) {d : K}
    (h : N * R = d • (R * N)) (k : ℕ) (hk : 1 ≤ k) : Matrix.trace (R * N ^ k) = 0 := by
  obtain ⟨p, hp⟩ := hN
  have hnil : IsNilpotent (R * N ^ k) := by
    obtain ⟨c, hc⟩ := pow_R_mul R N h k p
    refine ⟨p, ?_⟩
    rw [hc, pow_eq_zero_of_le (Nat.le_mul_of_pos_left p hk) hp, mul_zero, smul_zero]
  exact (Matrix.isNilpotent_trace_of_isNilpotent hnil).eq_zero

theorem trace_mul_exp_smul.{u, v} : ∀ {K : Type u} {n : Type v} [inst : Field K] [inst_1 : CharZero K] [inst_2 : Fintype n] [inst_3 : DecidableEq n] {R N : Matrix n n K}, IsNilpotent N → ∀ {d : K}, N * R = d • (R * N) → ∀ (s : K), Matrix.trace (R * IsNilpotent.exp (s • N)) = Matrix.trace R := by
  intro K n _ _ _ _ R N hN d h s
  obtain ⟨p, hp⟩ := id hN
  have hsN : (s • N) ^ (p + 1) = 0 := by
    rw [smul_pow, pow_succ N, hp, zero_mul, smul_zero]
  rw [IsNilpotent.exp_eq_sum hsN, mul_sum, Matrix.trace_sum, sum_range_succ']
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, mul_one]
  rw [add_eq_right]
  refine sum_eq_zero fun i _ => ?_
  rw [mul_smul_comm, Matrix.trace_smul, smul_pow, mul_smul_comm, Matrix.trace_smul,
    trace_R_mul_pow_eq_zero hN h (i + 1) (by omega), smul_zero, smul_zero]

end GlobalTheory.TraceExpSmul
end

