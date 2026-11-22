import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumOrbitFibreSwap
section
open scoped BigOperators

namespace GlobalTheory
namespace OrbitFibre

open MulAction Function

theorem finsum_sigma_iter {ι : Type} {κ : ι → Type} (f : (Σ i, κ i) → ℂ)
    (hf : (support f).Finite) : ∑ᶠ p, f p = ∑ᶠ i, ∑ᶠ k, f ⟨i, k⟩ := by
  classical
  set s := hf.toFinset with hs
  let t : Finset ι := s.image Sigma.fst
  let u : ∀ i, Finset (κ i) := fun i => s.preimage (Sigma.mk i) sigma_mk_injective.injOn
  have hsub : s ⊆ t.sigma u := by
    intro p hp
    rw [Finset.mem_sigma]
    exact ⟨Finset.mem_image_of_mem _ hp, by simpa [u] using hp⟩
  rw [finsum_eq_sum f hf, ← hs, Finset.sum_subset hsub ?_, Finset.sum_sigma]
  · rw [finsum_eq_sum_of_support_subset _ (s := t) ?_]
    · apply Finset.sum_congr rfl
      intro i _
      rw [finsum_eq_sum_of_support_subset _ (s := u i)]
      intro k hk
      simpa [u, hs] using hk
    · intro i hi
      rw [Function.mem_support] at hi
      by_contra hit
      apply hi
      have : ∀ k, f ⟨i, k⟩ = 0 := by
        intro k
        by_contra hk
        apply hit
        exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨⟨i, k⟩, by simpa [hs] using hk, rfl⟩)
      simp [this]
  · intro p _ hp
    simpa [hs] using hp

variable {Γ A B J : Type} [Group Γ] [MulAction Γ A] [MulAction Γ B]

noncomputable def toOrbit (τ : J → B)
    (p : Σ j : J, orbitRel.Quotient (stabilizer Γ (τ j)) A) : orbitRel.Quotient Γ (A × B) :=
  Quotient.mk'' (Quotient.out p.2, τ p.1)

def liftW (Ψ : A → B → ℂ) (hΨ : ∀ (g : Γ) a b, Ψ (g • a) (g • b) = Ψ a b) :
    orbitRel.Quotient Γ (A × B) → ℂ :=
  Quotient.lift (fun p => Ψ p.1 p.2) (by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h' : (a, b) ∈ orbit Γ (a', b') := h
    obtain ⟨g, hg⟩ := mem_orbit_iff.mp h'
    rw [Prod.smul_mk, Prod.mk.injEq] at hg
    obtain ⟨h1, h2⟩ := hg
    simp only
    rw [← h1, ← h2, hΨ])

variable (Γ A B) in

def swapQ : orbitRel.Quotient Γ (B × A) ≃ orbitRel.Quotient Γ (A × B) :=
  Quotient.congr (Equiv.prodComm B A) (by
    rintro ⟨b, a⟩ ⟨b', a'⟩
    change (b, a) ∈ orbit Γ (b', a') ↔ (a, b) ∈ orbit Γ (a', b')
    simp only [mem_orbit_iff, Prod.smul_mk, Prod.mk.injEq]
    exact ⟨fun ⟨g, h1, h2⟩ => ⟨g, h2, h1⟩, fun ⟨g, h1, h2⟩ => ⟨g, h2, h1⟩⟩)

end OrbitFibre

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumRegroupFibreBij
section
namespace GlobalTheory

theorem finsum_regroup_fibre_bij {α ι : Type} {κ : ι → Type} (U : α → ℂ)
    (W : (i : ι) → κ i → ℂ) (π : α → ι) (Φ : (i : ι) → α → κ i)
    (hU : (Function.support U).Finite)
    (hval : ∀ a, U a ≠ 0 → W (π a) (Φ (π a) a) = U a)
    (hinj : ∀ a a', U a ≠ 0 → U a' ≠ 0 → π a' = π a → Φ (π a) a = Φ (π a) a' → a = a')
    (hsurj : ∀ i c, W i c ≠ 0 → ∃ a, π a = i ∧ U a ≠ 0 ∧ Φ i a = c) :
    ∑ᶠ a, U a = ∑ᶠ i, ∑ᶠ c, W i c := by
  classical
  set S : Finset α := hU.toFinset with hS
  have hmem : ∀ a, a ∈ S ↔ U a ≠ 0 := fun a => by simp [hS]
  have hin : ∀ i, ∑ᶠ c, W i c = ∑ a ∈ S.filter (fun a => π a = i), U a := by
    intro i
    have h1 : Function.support (W i) ⊆
        ((S.filter (fun a => π a = i)).image (Φ i) : Finset (κ i)) := by
      intro c hc
      obtain ⟨a, ha, hUa, hac⟩ := hsurj i c hc
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_filter]
      exact ⟨a, ⟨(hmem a).2 hUa, ha⟩, hac⟩
    rw [finsum_eq_sum_of_support_subset _ h1, Finset.sum_image]
    · refine Finset.sum_congr rfl fun a ha => ?_
      obtain ⟨ha1, ha2⟩ := Finset.mem_filter.1 ha
      subst ha2
      exact hval a ((hmem a).1 ha1)
    · intro a ha a' ha' h
      obtain ⟨ha1, ha2⟩ := Finset.mem_filter.1 ha
      obtain ⟨ha1', ha2'⟩ := Finset.mem_filter.1 ha'
      subst ha2
      exact hinj a a' ((hmem a).1 ha1) ((hmem a').1 ha1') ha2' h
  simp only [hin]
  have h2 : Function.support (fun i => ∑ a ∈ S.filter (fun a => π a = i), U a) ⊆
      (S.image π : Finset ι) := by
    intro i hi
    obtain ⟨a, ha, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi
    obtain ⟨ha1, ha2⟩ := Finset.mem_filter.1 ha
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
    exact ⟨a, ha1, ha2⟩
  rw [finsum_eq_sum_of_support_subset _ h2, finsum_eq_sum U hU,
    Finset.sum_fiberwise_of_maps_to (fun a ha => Finset.mem_image_of_mem π ha)]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumRestrictedProductCount
section
open Filter
open scoped Classical

namespace GlobalTheory.LocalGrouping

open Function

theorem ne_zero_of_finprod_mem_ne_zero {ι : Type} (S : Set ι) (h : ι → ℂ)
    (hf : (mulSupport h).Finite) (hne : ∏ᶠ i ∈ S, h i ≠ 0) : ∀ i ∈ S, h i ≠ 0 := by
  intro i hi hzero
  apply hne
  have hfin : (S ∩ mulSupport h).Finite := hf.subset Set.inter_subset_right
  rw [← finprod_mem_inter_mulSupport, finprod_mem_eq_finite_toFinset_prod _ hfin]
  apply Finset.prod_eq_zero (i := i)
  · simp [Set.Finite.mem_toFinset, hi, Function.mem_mulSupport, hzero]
  · exact hzero

theorem finprod_finsum_eq (I : Type) (D : I → Type) (S : Set I) (B : ∀ i, D i → ℂ)
    (T : Finset I) (u : ∀ i, D i) (hTS : (T : Set I) ⊆ S)
    (hfin : ∀ i ∈ S, (support (B i)).Finite)
    (hind : ∀ i ∈ S, i ∉ T → ∀ d, B i d = if d = u i then 1 else 0) :
    ∏ᶠ i ∈ S, ∑ᶠ d, B i d = ∑ᶠ f : (∀ i : T, D i), ∏ i : T, B i (f i) := by
  have hone : ∀ i ∈ S, i ∉ T → ∑ᶠ d, B i d = 1 := by
    intro i hi hT
    rw [finsum_eq_single _ (u i)]
    · simp [hind i hi hT]
    · intro d hd; simp [hind i hi hT, hd]
  rw [finprod_mem_eq_prod_of_subset _ (t := T) ?_ hTS]
  swap
  · rintro i ⟨hiS, hi⟩
    by_contra hT
    exact hi (hone i hiS hT)
  let P : ∀ i : T, Finset (D i) := fun i => (hfin i (hTS i.2)).toFinset
  have hsum : ∀ i : T, ∑ᶠ d, B i d = ∑ d ∈ P i, B i d := fun i =>
    finsum_eq_sum_of_support_subset _ (by simp [P])
  rw [← Finset.prod_coe_sort T, Finset.prod_congr rfl (fun i _ => hsum i), Finset.prod_univ_sum]
  symm
  apply finsum_eq_sum_of_support_subset
  intro f hf
  rw [Function.mem_support, Finset.prod_ne_zero_iff] at hf
  rw [Finset.mem_coe, Fintype.mem_piFinset]
  intro i
  simpa [P] using hf i (Finset.mem_univ _)

end GlobalTheory.LocalGrouping

namespace GlobalTheory.LocalGrouping

open Function

theorem finsum_fibres_eq (I R : Type) (D : I → Type) (S : Set I) (B : ∀ i, D i → ℂ)
    (ℓ : R → ∀ i, D i) (A : Set R) (k m : ℕ)
    (T : Finset I) (u : ∀ i, D i) (hTS : (T : Set I) ⊆ S)
    (hfin : ∀ i ∈ S, (support (B i)).Finite)
    (hind : ∀ i ∈ S, i ∉ T → ∀ d, B i d = if d = u i then 1 else 0)
    (H3 : ∀ c ∈ A, ∀ᶠ i in cofinite, B i (ℓ c i) = 1)
    (H4 : ∀ e : ∀ i, D i, (∀ i ∈ S, B i (e i) ≠ 0) →
      Nat.card {c : R // c ∈ A ∧ ∀ i ∈ S, ℓ c i = e i} * 2 ^ k = 2 ^ m) :
    (∑ᶠ c : R, if c ∈ A then ∏ᶠ i ∈ S, B i (ℓ c i) else 0) * (2 : ℂ) ^ k =
      (2 : ℂ) ^ m * ∑ᶠ f : (∀ i : T, D i), ∏ i : T, B i (f i) := by
  let F : (∀ i : T, D i) → ℂ := fun f => ∏ i : T, B i (f i)
  have hFfin : (support F).Finite := by
    apply (Set.Finite.pi (t := fun i : T => support (B i)) (fun i => hfin i (hTS i.2))).subset
    intro f hf
    rw [mem_support, Finset.prod_ne_zero_iff] at hf
    intro i _
    exact hf i (Finset.mem_univ _)
  let E : (∀ i : T, D i) → ∀ i, D i := fun f i => if h : i ∈ T then f ⟨i, h⟩ else u i
  let Fib : (∀ i : T, D i) → Set R := fun f => {c | c ∈ A ∧ ∀ i ∈ S, ℓ c i = E f i}
  have hEnz : ∀ f, F f ≠ 0 → ∀ i ∈ S, B i (E f i) ≠ 0 := by
    intro f hf i hi
    by_cases hT : i ∈ T
    · simp only [E, hT, dite_true]
      rw [Finset.prod_ne_zero_iff] at hf
      exact hf ⟨i, hT⟩ (Finset.mem_univ _)
    · simp [E, hT, hind i hi hT]
  have hcard : ∀ f, F f ≠ 0 → (Nat.card (Fib f) : ℂ) * 2 ^ k = 2 ^ m := by
    intro f hf
    have h := H4 (E f) (hEnz f hf)
    exact_mod_cast h
  have hFibfin : ∀ f, F f ≠ 0 → (Fib f).Finite := by
    intro f hf
    have h := H4 (E f) (hEnz f hf)
    have hne : Nat.card (Fib f) ≠ 0 := by
      intro h0
      change Nat.card {c : R // c ∈ A ∧ ∀ i ∈ S, ℓ c i = E f i} = 0 at h0
      rw [h0, zero_mul] at h
      exact (pow_ne_zero m two_ne_zero) h.symm
    exact Set.finite_coe_iff.mp (Nat.finite_of_card_ne_zero hne)
  have hpt : ∀ c, (if c ∈ A then ∏ᶠ i ∈ S, B i (ℓ c i) else 0) =
      ∑ f ∈ hFfin.toFinset, if c ∈ Fib f then F f else 0 := by
    intro c
    by_cases hcA : c ∈ A
    swap
    · simp [hcA, Fib]
    rw [if_pos hcA]
    by_cases hex : ∃ f ∈ hFfin.toFinset, c ∈ Fib f
    · obtain ⟨f, hf, hcf⟩ := hex
      rw [Finset.sum_eq_single f]
      · rw [if_pos hcf]
        rw [finprod_mem_eq_prod_of_subset _ (t := T) ?_ hTS]
        · rw [← Finset.prod_coe_sort T]
          apply Finset.prod_congr rfl
          intro i _
          rw [hcf.2 i (hTS i.2)]
          simp [E]
        · rintro i ⟨hiS, hi⟩
          by_contra hT
          apply hi
          show B i (ℓ c i) = 1
          have hT' : i ∉ T := hT
          rw [hcf.2 i hiS]
          simp [E, hT', hind i hiS hT']
      · intro g _ hgf
        rw [if_neg]
        intro hcg
        apply hgf
        funext i
        have h1 := hcf.2 i (hTS i.2)
        have h2 := hcg.2 i (hTS i.2)
        simp [E] at h1 h2
        rw [← h1, ← h2]
      · intro hf'; exact absurd hf hf'
    · rw [Finset.sum_eq_zero]
      swap
      · intro f hf
        rw [if_neg]
        intro hcf; exact hex ⟨f, hf, hcf⟩
      by_contra hne
      have hmf : (mulSupport fun i => B i (ℓ c i)).Finite := Filter.eventually_cofinite.mp (H3 c hcA)
      have hall := ne_zero_of_finprod_mem_ne_zero S _ hmf hne
      apply hex
      refine ⟨fun i => ℓ c i, ?_, hcA, ?_⟩
      · rw [Set.Finite.mem_toFinset, mem_support, Finset.prod_ne_zero_iff]
        intro i _
        exact hall i (hTS i.2)
      · intro i hi
        by_cases hT : i ∈ T
        · simp [E, hT]
        · have := hall i hi
          rw [hind i hi hT] at this
          simp only [E, hT, dite_false]
          by_contra h; exact this (if_neg h)
  have hinner : ∀ f ∈ hFfin.toFinset,
      (∑ᶠ c, if c ∈ Fib f then F f else 0) * (2 : ℂ) ^ k = 2 ^ m * F f := by
    intro f hf
    rw [Set.Finite.mem_toFinset, mem_support] at hf
    have e1 : (∑ᶠ c, if c ∈ Fib f then F f else 0) = ∑ᶠ c ∈ Fib f, F f := by
      rw [finsum_mem_def]
      apply finsum_congr
      intro c
      simp [Set.indicator_apply]
    rw [e1, finsum_mem_eq_finite_toFinset_sum _ (hFibfin f hf), Finset.sum_const,
      ← Nat.card_eq_card_finite_toFinset, nsmul_eq_mul, mul_right_comm, hcard f hf]
  rw [finsum_congr hpt, finsum_sum_comm, Finset.sum_mul, Finset.sum_congr rfl hinner,
    ← Finset.mul_sum]
  · congr 1
    symm
    exact finsum_eq_sum_of_support_subset F (by simp)
  · intro f hf
    rw [Set.Finite.mem_toFinset, mem_support] at hf
    apply (hFibfin f hf).subset
    intro c hc
    by_contra h
    exact hc (if_neg h)

end GlobalTheory.LocalGrouping

namespace GlobalTheory

open Function

theorem finsum_finprod_mul_two_pow_eq :
    ∀ (I R : Type) (D : I → Type) (S : Set I) (B : ∀ i, D i → ℂ) (ℓ : R → ∀ i, D i) (A : Set R)
      (k m : ℕ), (∀ i, Nonempty (D i)) → (∀ i ∈ S, (Function.support (B i)).Finite) →
      (∀ᶠ i in cofinite, ∃ u : D i, ∀ d, B i d = if d = u then 1 else 0) →
      (∀ c ∈ A, ∀ᶠ i in cofinite, B i (ℓ c i) = 1) →
      (∀ e : ∀ i, D i, (∀ i ∈ S, B i (e i) ≠ 0) →
        Nat.card {c : R // c ∈ A ∧ ∀ i ∈ S, ℓ c i = e i} * 2 ^ k = 2 ^ m) →
      (∑ᶠ c : R, if c ∈ A then ∏ᶠ i ∈ S, B i (ℓ c i) else 0) * (2 : ℂ) ^ k =
        (2 : ℂ) ^ m * ∏ᶠ i ∈ S, ∑ᶠ d, B i d := by
  intro I R D S B ℓ A k m H0 H1 H2 H3 H4
  have hbad : {i | ¬ ∃ u : D i, ∀ d, B i d = if d = u then 1 else 0}.Finite :=
    Filter.eventually_cofinite.mp H2
  let T : Finset I := (hbad.inter_of_left S).toFinset
  let u : ∀ i, D i := fun i =>
    if h : ∃ u : D i, ∀ d, B i d = if d = u then 1 else 0 then h.choose else (H0 i).some
  have hTS : (T : Set I) ⊆ S := by
    intro i hi
    simp only [T, Set.Finite.coe_toFinset] at hi
    exact hi.2
  have hind : ∀ i ∈ S, i ∉ T → ∀ d, B i d = if d = u i then 1 else 0 := by
    intro i hi hT
    have hgood : ∃ u : D i, ∀ d, B i d = if d = u then 1 else 0 := by
      by_contra h
      apply hT
      rw [Set.Finite.mem_toFinset]
      exact ⟨h, hi⟩
    intro d
    simp only [u, hgood, dite_true]
    exact hgood.choose_spec d
  rw [LocalGrouping.finprod_finsum_eq I D S B T u hTS H1 hind]
  exact LocalGrouping.finsum_fibres_eq I R D S B ℓ A k m T u hTS H1 hind H3 H4

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiveElementaryInequalitiesEventually
section
open Filter Real

namespace GlobalTheory

theorem eventually_const_mul_rpow_le_rpow (a b c : ℝ) (h : a < b) :
    ∀ᶠ x : ℝ in atTop, c * x ^ a ≤ x ^ b := by
  have ht := tendsto_rpow_atTop (sub_pos.2 h)
  filter_upwards [ht.eventually_ge_atTop c, eventually_gt_atTop (0 : ℝ)] with x hx hx0
  have e : x ^ b = x ^ (b - a) * x ^ a := by
    rw [← Real.rpow_add hx0]; ring_nf
  rw [e]
  exact mul_le_mul_of_nonneg_right hx (Real.rpow_nonneg hx0.le _)

theorem sqrt_mul_rpow_neg_eq (eps x : ℝ) (hx : 0 < x) :
    Real.sqrt (x * x ^ (-(eps / 8))) = x ^ (1 / 2 - eps / 16) := by
  have h1 : x * x ^ (-(eps / 8)) = x ^ (1 - eps / 8) := by
    rw [sub_eq_add_neg, Real.rpow_add hx, Real.rpow_one]
  rw [h1, Real.sqrt_eq_rpow, ← Real.rpow_mul hx.le]
  ring_nf

theorem five_elementary_inequalities_eventually :
    ∀ eps : ℝ, 0 < eps → eps < 1 → ∀ᶠ x : ℝ in Filter.atTop,
      x ^ (eps / 4) + x ^ (eps / 3) + 1 + 3 * Real.log x ≤ x ^ eps / 5 ∧
      11 ≤ x ^ (eps / 5) ∧ 8 * Real.log x ^ 2 < x ^ 2 ∧
      2 * x ^ (eps / 5 + eps / 100) ≤ Real.sqrt (x * x ^ (-(eps / 8))) ∧
      44 ≤ Real.sqrt (x * x ^ (-(eps / 8))) := by
  intro eps he he1
  have h1 := eventually_const_mul_rpow_le_rpow (eps / 4) eps 20 (by linarith)
  have h2 := eventually_const_mul_rpow_le_rpow (eps / 3) eps 20 (by linarith)
  have h3 := eventually_const_mul_rpow_le_rpow 0 eps 20 he
  have h4 := (isLittleO_log_rpow_atTop he).bound (show (0:ℝ) < 1 / 60 by norm_num)
  have h5 := eventually_const_mul_rpow_le_rpow 0 (eps / 5) 11 (by linarith)
  have h6 := Real.isLittleO_log_id_atTop.bound (show (0:ℝ) < 1 / 4 by norm_num)
  have h7 := eventually_const_mul_rpow_le_rpow (eps / 5 + eps / 100) (1 / 2 - eps / 16) 2
    (by linarith)
  have h8 := eventually_const_mul_rpow_le_rpow 0 (1 / 2 - eps / 16) 44 (by linarith)
  filter_upwards [h1, h2, h3, h4, h5, h6, h7, h8, eventually_gt_atTop (0 : ℝ)]
    with x h1 h2 h3 h4 h5 h6 h7 h8 hx
  rw [Real.rpow_zero] at h3 h5 h8
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hx _)] at h4
  rw [Real.norm_eq_abs, Real.norm_eq_abs, id, abs_of_pos hx] at h6
  rw [sqrt_mul_rpow_neg_eq eps x hx]
  have hl := le_abs_self (Real.log x)
  refine ⟨by linarith, by linarith, ?_, h7, by linarith⟩
  nlinarith [abs_nonneg (Real.log x), sq_abs (Real.log x)]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedFieldKerToPermFiniteIsGaloisFinrankDvd
section
open IntermediateField

namespace GlobalTheory

theorem fixedField_ker_toPerm_finite_isGalois_finrank_dvd (Ω K : Type) [Field Ω] [Field K]
    [Algebra Ω K] [IsAlgClosure Ω K] [CharZero Ω] (n : ℕ)
    (φ : (K ≃ₐ[Ω] K) →* Equiv.Perm (Fin n)) :
    FiniteDimensional Ω (IntermediateField.fixedField φ.ker) ∧
      IsGalois Ω (IntermediateField.fixedField φ.ker) ∧
      Module.finrank Ω (IntermediateField.fixedField φ.ker) ∣ n.factorial := by
  haveI : Algebra.IsAlgebraic Ω K := IsAlgClosure.isAlgebraic
  haveI : Normal Ω K := IsAlgClosure.normal Ω K
  haveI : IsGalois Ω K := ⟨⟩
  set E : IntermediateField Ω K := fixedField φ.ker with hE
  have hHF : φ.ker ≤ E.fixingSubgroup := (IntermediateField.le_iff_le _ _).1 le_rfl
  have hker : φ.ker.index ∣ n.factorial := by
    rw [Subgroup.index_ker]
    have h := Subgroup.card_subgroup_dvd_card φ.range
    rwa [Nat.card_perm, Nat.card_fin] at h
  have hF : E.fixingSubgroup.index ∣ n.factorial :=
    (Subgroup.index_dvd_of_le hHF).trans hker
  haveI : E.fixingSubgroup.FiniteIndex :=
    ⟨fun h => (Nat.factorial_pos n).ne' (Nat.eq_zero_of_zero_dvd (h ▸ hF))⟩
  have hopen : IsOpen (E.fixingSubgroup : Set (K ≃ₐ[Ω] K)) :=
    Subgroup.isOpen_of_isClosed_of_finiteIndex _ (InfiniteGalois.fixingSubgroup_isClosed E)
  haveI hfin : FiniteDimensional Ω E := (InfiniteGalois.isOpen_iff_finite E).1 hopen
  have hnorm : E.fixingSubgroup.Normal := by
    constructor
    intro σ hσ g
    rw [IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
    intro x hx
    have hx' : g⁻¹ x ∈ E := by
      rw [hE, IntermediateField.mem_fixedField_iff] at hx ⊢
      intro h hh
      have hc : g * h * g⁻¹ ∈ φ.ker := (MonoidHom.normal_ker φ).conj_mem h hh g
      have := hx _ hc
      calc h (g⁻¹ x) = g⁻¹ ((g * h * g⁻¹) x) := by simp [AlgEquiv.mul_apply]
        _ = g⁻¹ x := by rw [this]
    have h2 := hσ _ hx'
    simp only [AlgEquiv.mul_apply]
    change g (σ (g⁻¹ x)) = x
    rw [h2]
    exact g.apply_symm_apply x
  haveI hgal : IsGalois Ω E := (InfiniteGalois.normal_iff_isGalois E).1 hnorm
  refine ⟨hfin, hgal, ?_⟩
  rw [IntermediateField.finrank_eq_fixingSubgroup_index]
  exact hF

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatOfForallFinsetSubsetFlat
section
open TensorProduct LinearMap

namespace GlobalTheory

theorem flat_of_forall_finset_subset_flat :
    ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M],
      (∀ s : Finset M, ∃ N : Submodule R M, (↑s : Set M) ⊆ ↑N ∧ Module.Flat R ↥N) →
        Module.Flat R M := by
  intro R M _ _ _ h
  refine Module.Flat.iff_lTensor_injective'.mpr fun I => ?_
  refine (injective_iff_map_eq_zero _).mpr fun x hx => ?_
  obtain ⟨J, hfg, y, rfl⟩ := Submodule.exists_fg_le_eq_rTensor_subtype (R := R) (M := ↥I) x
  obtain ⟨s, hs⟩ := hfg
  obtain ⟨N, hsN, hN⟩ := h s
  have hJN : J ≤ N := hs ▸ Submodule.span_le.mpr hsN
  obtain ⟨y', hy'⟩ : ∃ y' : ↥N ⊗[R] ↥I, y' = rTensor (↥I) (Submodule.inclusion hJN) y := ⟨_, rfl⟩
  have hxy : rTensor (↥I) J.subtype y = rTensor (↥I) N.subtype y' := by
    rw [hy', ← rTensor_comp_apply]; rfl
  rw [hxy] at hx ⊢
  have hcomm : lTensor M I.subtype (rTensor (↥I) N.subtype y') =
      rTensor R N.subtype (lTensor (↥N) I.subtype y') := by
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, lTensor_comp_rTensor, rTensor_comp_lTensor]
  rw [hcomm] at hx
  have hinj1 : Function.Injective (rTensor R N.subtype) :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := R) N.subtype Subtype.val_injective
  have h0 : lTensor (↥N) I.subtype y' = 0 := hinj1 (by rw [hx, map_zero])
  have hinj2 : Function.Injective (lTensor (↥N) I.subtype) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := ↥N) I.subtype Subtype.val_injective
  have : y' = 0 := hinj2 (by rw [h0, map_zero])
  rw [this, map_zero]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSubschemeOfQuotientFlatAffine
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace GlobalTheory

theorem closedSub_flat_of_quotient_flat : ∀ (V : Type) [CommRing V] (X : Scheme.{0}) [IsAffine X] (p : X ⟶ Spec (CommRingCat.of V)) (J : X.IdealSheafData), ((Ideal.Quotient.mk (J.ideal ⟨⊤, isAffineOpen_top X⟩)).comp (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom)).Flat → Flat (J.subschemeι ≫ p) := by
  intro V _ X _ p J h
  have : IsAffine J.subscheme := isAffine_of_isAffineHom J.subschemeι
  rw [HasRingHomProperty.iff_of_isAffine (P := @Flat)]
  set U : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  have e : (J.subschemeι ≫ p).appTop.hom =
      (J.subschemeObjIso U).inv.hom.comp
        (((Ideal.Quotient.mk (J.ideal U)).comp (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom)).comp
          (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom) := by
    have h2 := J.subschemeι_app U
    have h3 : J.subschemeι.appTop = CommRingCat.ofHom (Ideal.Quotient.mk (J.ideal U)) ≫ (J.subschemeObjIso U).inv := h2
    rw [Scheme.Hom.comp_appTop, h3]
    ext x
    change (J.subschemeObjIso U).inv.hom (Ideal.Quotient.mk (J.ideal U) (p.appTop.hom x)) =
      (J.subschemeObjIso U).inv.hom (Ideal.Quotient.mk (J.ideal U) (p.appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom x))))
    rw [Iso.hom_inv_id_apply]
  rw [e]
  refine RingHom.Flat.comp ?_ (RingHom.Flat.of_bijective (J.subschemeObjIso U).commRingCatIsoToRingEquiv.symm.bijective)
  refine RingHom.Flat.comp (RingHom.Flat.of_bijective (Scheme.ΓSpecIso (CommRingCat.of V)).commRingCatIsoToRingEquiv.bijective) h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsTerTail
section
namespace GlobalTheory.AbelianSumIdentityFirst

theorem main : ∀ {ι : Type} {z : ℂ}, z ≠ (0 : ℂ) → ∀ (s : Finset ι) (a : ι → ℤ),
    z ^ ∑ i ∈ s, a i = ∏ i ∈ s, z ^ a i := by
  intro ι z hz s a
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj, zpow_add₀ hz, ih]

end GlobalTheory.AbelianSumIdentityFirst
end

