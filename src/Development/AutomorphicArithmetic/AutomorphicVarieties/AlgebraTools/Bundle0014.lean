import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0003
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0008
import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0010
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0048
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0005

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.LagTriangular
section
open Polynomial Matrix IsLocalRing TensorProduct UpperTheory.V.AlgebraTools

private theorem left_unit {R E : Type} [CommRing R] [Ring E] [Algebra R E] (f : E) (L : List E)
    (h : ∀ x ∈ L, ∃ u : R, IsUnit u ∧ f * x = u • f) :
    ∃ u : R, IsUnit u ∧ f * L.prod = u • f := by
  induction L with
  | nil => exact ⟨1, isUnit_one, by simp⟩
  | cons x L ih =>
    obtain ⟨u, hu, e⟩ := h x (by simp)
    obtain ⟨v, hv, e'⟩ := ih (fun y hy => h y (by simp [hy]))
    exact ⟨u * v, hu.mul hv, by
      rw [List.prod_cons, ← mul_assoc, e, smul_mul_assoc, e', smul_smul]⟩

private theorem right_unit {R E : Type} [CommRing R] [Ring E] [Algebra R E] (f : E) (L : List E)
    (h : ∀ x ∈ L, ∃ u : R, IsUnit u ∧ x * f = u • f) :
    ∃ u : R, IsUnit u ∧ L.prod * f = u • f := by
  induction L with
  | nil => exact ⟨1, isUnit_one, by simp⟩
  | cons x L ih =>
    obtain ⟨u, hu, e⟩ := h x (by simp)
    obtain ⟨v, hv, e'⟩ := ih (fun y hy => h y (by simp [hy]))
    exact ⟨v * u, hv.mul hu, by
      rw [List.prod_cons, mul_assoc, e', mul_smul_comm, e, smul_smul]⟩

private theorem mid_zero {R E : Type} [CommRing R] [Ring E] [Algebra R E] {n : ℕ} (f g : E)
    (F : Fin n → E) (i : Fin n)
    (hf : ∀ j, j < i → ∃ u : R, IsUnit u ∧ f * F j = u • f)
    (hg : ∀ j, i < j → ∃ u : R, IsUnit u ∧ F j * g = u • g)
    (h0 : (List.ofFn F).prod = 0) : f * F i * g = 0 := by
  have hlen : (List.ofFn F).length = n := List.length_ofFn
  have hsplit : List.ofFn F = (List.ofFn F).take i ++ F i :: (List.ofFn F).drop (i + 1) := by
    conv_lhs => rw [← List.take_append_drop i (List.ofFn F)]
    congr 1
    rw [List.drop_eq_getElem_cons (by rw [hlen]; exact i.2)]
    simp
  have hT : ∀ x ∈ (List.ofFn F).take i, ∃ u : R, IsUnit u ∧ f * x = u • f := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hx
    simp only [List.length_take, hlen] at hk
    rw [List.getElem_take, List.getElem_ofFn]
    exact hf ⟨k, by omega⟩ (by rw [Fin.lt_def]; simp; omega)
  have hD : ∀ x ∈ (List.ofFn F).drop (i + 1), ∃ u : R, IsUnit u ∧ x * g = u • g := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hx
    simp only [List.length_drop, hlen] at hk
    rw [List.getElem_drop, List.getElem_ofFn]
    exact hg ⟨i + 1 + k, by omega⟩ (by rw [Fin.lt_def]; simp; omega)
  obtain ⟨u, hu, hA⟩ := left_unit (R := R) f _ hT
  obtain ⟨v, hv, hB⟩ := right_unit (R := R) g _ hD
  have key : f * (List.ofFn F).prod * g = (u * v) • (f * F i * g) := by
    rw [hsplit, List.prod_append, List.prod_cons]
    calc f * (((List.ofFn F).take i).prod * (F i * ((List.ofFn F).drop (i + 1)).prod)) * g
        = (f * ((List.ofFn F).take i).prod) * F i * (((List.ofFn F).drop (i + 1)).prod * g) := by
          simp only [mul_assoc]
      _ = (u • f) * F i * (v • g) := by rw [hA, hB]
      _ = (u * v) • (f * F i * g) := by
          rw [smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [h0, mul_zero, zero_mul] at key
  exact ((hu.mul hv).smul_eq_zero).1 key.symm

theorem UpperTheory.V.AlgebraTools.lag_triangular :
    ∀ {R Λ E : Type} [CommRing R] [Ring Λ] [Algebra R Λ] [Ring E] [Algebra R E] {n : ℕ} (ρ : Λ →ₐ[R] E) (χ : Fin n → Λ →ₐ[R] R) (z : Λ), (∀ y : Fin n → Λ, (List.ofFn fun i => ρ (y i) - algebraMap R E (χ i (y i))).prod = 0) → (∀ i j, i ≠ j → IsUnit (χ i z - χ j z)) → CompleteOrthogonalIdempotents (lag (fun i => χ i z) (ρ z)) ∧ (∀ (y : Λ) (a b : Fin n), b < a → lag (fun i => χ i z) (ρ z) a * ρ y * lag (fun i => χ i z) (ρ z) b = 0) ∧ ∀ (y : Λ) (i : Fin n), lag (fun i => χ i z) (ρ z) i * ρ y * lag (fun i => χ i z) (ρ z) i = χ i y • lag (fun i => χ i z) (ρ z) i := by
  intro R Λ E _ _ _ _ _ n ρ χ z hprod hu
  have hzero : aeval (ρ z) (∏ i, (X - C ((fun i => χ i z) i))) = 0 := by
    rw [← List.prod_ofFn, map_list_prod, List.map_ofFn]
    simpa [Function.comp_def] using hprod (fun _ => z)
  obtain ⟨hcoi, hP, -, hcomm⟩ := lag_coi (fun i => χ i z) (ρ z) hu hzero
  have hl : ∀ c j, lag (fun i => χ i z) (ρ z) c * (ρ z - algebraMap R E (χ j z)) =
      (χ c z - χ j z) • lag (fun i => χ i z) (ρ z) c := by
    intro c j
    rw [mul_sub, ← (hcomm (ρ z) c (Commute.refl _)).eq, hP, ← Algebra.commutes,
      ← Algebra.smul_def, sub_smul]
  have hr : ∀ c j, (ρ z - algebraMap R E (χ j z)) * lag (fun i => χ i z) (ρ z) c =
      (χ c z - χ j z) • lag (fun i => χ i z) (ρ z) c := by
    intro c j
    rw [sub_mul, hP, ← Algebra.smul_def, sub_smul]
  have key : ∀ (y : Λ) (c d i : Fin n), (∀ j, j < i → j ≠ c) → (∀ j, i < j → j ≠ d) →
      lag (fun i => χ i z) (ρ z) c * (ρ y - algebraMap R E (χ i y)) *
        lag (fun i => χ i z) (ρ z) d = 0 := by
    intro y c d i h1 h2
    have h := mid_zero (R := R) (lag (fun i => χ i z) (ρ z) c) (lag (fun i => χ i z) (ρ z) d)
      (fun j => ρ (Function.update (fun _ => z) i y j) -
        algebraMap R E (χ j (Function.update (fun _ => z) i y j))) i ?_ ?_ (hprod _)
    · simpa using h
    · intro j hj
      refine ⟨_, hu c j (h1 j hj).symm, ?_⟩
      simp only [Function.update_apply, if_neg (ne_of_lt hj)]
      exact hl c j
    · intro j hj
      refine ⟨_, hu d j (h2 j hj).symm, ?_⟩
      simp only [Function.update_apply, if_neg (ne_of_gt hj)]
      exact hr d j
  have hmid : ∀ (r : R) (c d : Fin n), lag (fun i => χ i z) (ρ z) c * algebraMap R E r *
      lag (fun i => χ i z) (ρ z) d =
        r • (lag (fun i => χ i z) (ρ z) c * lag (fun i => χ i z) (ρ z) d) := by
    intro r c d
    rw [← Algebra.commutes, ← Algebra.smul_def, smul_mul_assoc]
  refine ⟨hcoi, ?_, ?_⟩
  · intro y a b hba
    have h := key y a b a (fun j hj => ne_of_lt hj) (fun j hj => ne_of_gt (hba.trans hj))
    rw [mul_sub, sub_mul, hmid, hcoi.ortho (ne_of_gt hba), smul_zero, sub_zero] at h
    exact h
  · intro y i
    have h := key y i i i (fun j hj => ne_of_lt hj) (fun j hj => ne_of_gt hj)
    rw [mul_sub, sub_mul, hmid, (hcoi.idem i).eq, sub_eq_zero] at h
    exact h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.OneAddPowSubOneMem
section
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

private theorem UpperTheory.V.AlgebraTools.prime_pow_dvd_choose (l : ℕ) (hl : l.Prime) (e j s : ℕ) (hj : j ≤ e)
    (hs : s + 1 < l ^ (e - j)) : l ^ j ∣ (l ^ e).choose (s + 1) := by
  have hm : s + 1 ≤ l ^ e :=
    le_of_lt (lt_of_lt_of_le hs (Nat.pow_le_pow_right hl.pos (Nat.sub_le e j)))
  have hC : (l ^ e).choose (s + 1) ≠ 0 := (Nat.choose_pos hm).ne'
  have hv : (s + 1).factorization l < e - j := by
    have h1 : l ^ (s + 1).factorization l ≤ s + 1 :=
      Nat.le_of_dvd (Nat.succ_pos s) (Nat.ordProj_dvd (s + 1) l)
    exact (Nat.pow_lt_pow_iff_right hl.one_lt).1 (lt_of_le_of_lt h1 hs)
  rw [hl.pow_dvd_iff_le_factorization hC, Nat.factorization_choose_prime_pow hl hm (Nat.succ_ne_zero s)]
  omega

theorem UpperTheory.V.AlgebraTools.one_add_pow_sub_one_mem :
    ∀ (R : Type) [CommRing R] (l : ℕ), l.Prime → ∀ (y : R) (e j k : ℕ), j ≤ e → k ≤ l ^ (e - j) →
      (1 + y) ^ l ^ e - 1 ∈ Ideal.span {y ^ k} ⊔ Ideal.span {(l : R) ^ j} := by
  intro R _ l hl y e j k hj hk
  have hN : (1 + y) ^ l ^ e - 1 =
      ∑ s ∈ Finset.range (l ^ e), y ^ (s + 1) * ((l ^ e).choose (s + 1) : R) := by
    rw [add_comm, add_pow, Finset.sum_range_succ']
    simp
  rw [hN]
  refine Ideal.sum_mem _ fun s _ => ?_
  by_cases hks : k ≤ s + 1
  · apply Ideal.mem_sup_left
    rw [Ideal.mem_span_singleton]
    exact Dvd.dvd.mul_right (pow_dvd_pow y hks) _
  · apply Ideal.mem_sup_right
    rw [Ideal.mem_span_singleton]
    obtain ⟨c, hc⟩ := UpperTheory.V.AlgebraTools.prime_pow_dvd_choose l hl e j s hj (by omega)
    exact ⟨y ^ (s + 1) * c, by rw [hc]; push_cast; ring⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.QRegPS
section
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

section SlopeTestRemainingChoices

open MvPowerSeries

private theorem mem_span_X {O σ : Type} [CommRing O] [Fintype σ] (f : MvPowerSeries σ O)
    (hf : constantCoeff f = 0) : f ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ O)) :=
  _root_.UpperTheory.Reformulated.B.MemSpanVariable.mem_span_X f hf

private theorem order_of_mem_pow {O σ : Type} [CommRing O] (n : ℕ) :
    ∀ g ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ O)) ^ n, (n : ℕ∞) ≤ g.order := by
  have h1 : ∀ g ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ O)),
      ((1 : ℕ) : ℕ∞) ≤ g.order := by
    intro g hg
    have hle : Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ O)) ≤
        RingHom.ker (constantCoeff : MvPowerSeries σ O →+* O) := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      simp
    refine nat_le_order fun d hd => ?_
    have hd0 : d = 0 := by
      rw [← Finsupp.degree_eq_zero_iff]
      omega
    subst hd0
    simpa using hle hg
  induction n with
  | zero => intro g _; simp
  | succ n ih =>
    intro g hg
    rw [pow_succ] at hg
    refine Submodule.mul_induction_on hg (fun x hx y hy => ?_) (fun x y hx hy => ?_)
    · refine le_trans ?_ le_order_mul
      rw [Nat.cast_add]
      exact add_le_add (ih x hx) (h1 y hy)
    · exact le_trans (le_min hx hy) min_order_le_add

private theorem coeff_mem_of_mem_map {O σ : Type} [CommRing O] (I : Ideal O) (g : MvPowerSeries σ O)
    (hg : g ∈ I.map (MvPowerSeries.C : O →+* MvPowerSeries σ O)) (d : σ →₀ ℕ) : coeff d g ∈ I := by
  have hle : I.map (MvPowerSeries.C : O →+* MvPowerSeries σ O) ≤
      RingHom.ker (MvPowerSeries.map (σ := σ) (Ideal.Quotient.mk I)) := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    simp [Ideal.Quotient.eq_zero_iff_mem.2 ha]
  have h := congrArg (coeff d) (RingHom.mem_ker.1 (hle hg))
  rw [coeff_map, map_zero] at h
  exact Ideal.Quotient.eq_zero_iff_mem.1 h

private theorem monoVal_X_eq {O σ : Type} [CommRing O] (α : σ →₀ ℕ) :
    GlobalTheory.monoVal (MvPowerSeries.X : σ → MvPowerSeries σ O) α = monomial α 1 := by
  simp only [GlobalTheory.monoVal, Finsupp.prod, X_pow_eq, prod_monomial, Finset.prod_const_one]
  congr 2
  exact Finsupp.sum_single α

private theorem eq_of_le_of_degree_eq {σ : Type} {α β : σ →₀ ℕ} (h : β ≤ α)
    (hd : β.degree = α.degree) : β = α := by
  obtain ⟨γ, rfl⟩ := exists_add_of_le h
  rw [map_add] at hd
  have : γ = 0 := by
    rw [← Finsupp.degree_eq_zero_iff]
    omega
  simp [this]

end SlopeTestRemainingChoices

theorem UpperTheory.V.AlgebraTools.qRegAt_mvPowerSeries :
    ∀ (Λ σ : Type) [CommRing Λ] [Finite σ] (I : Ideal Λ) (a : ℕ),
      QRegAt (MvPowerSeries σ Λ) (MvPowerSeries.X : σ → MvPowerSeries σ Λ) (I.map (MvPowerSeries.C : Λ →+* MvPowerSeries σ Λ)) a := by
  intro Λ σ _ _ I a c hc α
  classical
  haveI := Fintype.ofFinite σ
  rw [smul_eq_mul, Ideal.mul_top] at hc ⊢
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 hc
  have h0 : MvPowerSeries.coeff α.1 u = 0 := by
    refine MvPowerSeries.coeff_of_lt_order (lt_of_lt_of_le ?_ (order_of_mem_pow _ u hu))
    rw [α.2]
    exact_mod_cast Nat.lt_succ_self a
  have h1 : MvPowerSeries.coeff α.1 (u + v) = MvPowerSeries.constantCoeff (c α) := by
    rw [huv, map_sum, Finset.sum_eq_single α]
    · rw [monoVal_X_eq, smul_eq_mul, MvPowerSeries.coeff_monomial_mul]
      simp
    · intro β _ hβ
      rw [monoVal_X_eq, smul_eq_mul, MvPowerSeries.coeff_monomial_mul, if_neg]
      intro hle
      exact hβ (Subtype.ext (eq_of_le_of_degree_eq hle (β.2.trans α.2.symm)))
    · simp
  have h2 : MvPowerSeries.constantCoeff (c α) ∈ I := by
    rw [← h1, map_add, h0, zero_add]
    exact coeff_mem_of_mem_map I v hv _
  have h3 : c α = (c α - MvPowerSeries.C (MvPowerSeries.constantCoeff (c α))) +
      MvPowerSeries.C (MvPowerSeries.constantCoeff (c α)) := by ring
  rw [h3]
  exact Submodule.add_mem_sup (mem_span_X _ (by simp)) (Ideal.mem_map_of_mem _ h2)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.QRegScal
section
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

private theorem mem_map_smul_top_iff {S R M : Type} [CommRing S] [CommRing R] [Algebra S R]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower S R M] (K : Ideal S) (m : M) :
    m ∈ (K.map (algebraMap S R) • ⊤ : Submodule R M) ↔ m ∈ (K • ⊤ : Submodule S M) := by
  have h := Submodule.restrictScalars_map_smul_eq K (⊤ : Submodule R M)
  rw [Submodule.restrictScalars_top] at h
  rw [← h, Submodule.restrictScalars_mem]

private theorem map_mem_smul_top {S M M' : Type} [CommRing S] [AddCommGroup M] [Module S M]
    [AddCommGroup M'] [Module S M'] (f : M →ₗ[S] M') (K : Ideal S) {m : M}
    (h : m ∈ (K • ⊤ : Submodule S M)) : f m ∈ (K • ⊤ : Submodule S M') := by
  have h2 : f m ∈ (K • ⊤ : Submodule S M).map f := Submodule.mem_map_of_mem h
  rw [Submodule.map_smul''] at h2
  exact Submodule.smul_mono (le_refl K) le_top h2

private theorem mem_of_smul_mem {S M M' : Type} [CommRing S] (T : Submonoid S) [AddCommGroup M] [Module S M]
    [AddCommGroup M'] [Module S M'] (f : M →ₗ[S] M') [IsLocalizedModule T f] (K : Ideal S) (t : T) {x : M'}
    (h : (t : S) • x ∈ (K • ⊤ : Submodule S M')) : x ∈ (K • ⊤ : Submodule S M') := by
  have hu := IsLocalizedModule.map_units f t
  have e := LinearMap.congr_fun hu.unit.inv_mul x
  rw [Module.End.mul_apply, IsUnit.unit_spec, Module.End.one_apply, Module.algebraMap_end_apply] at e
  rw [← e]
  exact map_mem_smul_top _ K h

private theorem exists_smul_mem {S M M' : Type} [CommRing S] (T : Submonoid S) [AddCommGroup M] [Module S M]
    [AddCommGroup M'] [Module S M'] (f : M →ₗ[S] M') [IsLocalizedModule T f] (K : Ideal S) {m : M}
    (h : f m ∈ (K • ⊤ : Submodule S M')) : ∃ t : T, (t : S) • m ∈ (K • ⊤ : Submodule S M) := by
  have key : ∀ x ∈ (K • ⊤ : Submodule S M'), ∃ (s : T) (m' : M),
      m' ∈ (K • ⊤ : Submodule S M) ∧ (s : S) • x = f m' := by
    intro x hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro k hk x _
      obtain ⟨⟨m0, s⟩, hs⟩ := IsLocalizedModule.surj T f x
      simp only at hs
      refine ⟨s, k • m0, Submodule.smul_mem_smul hk Submodule.mem_top, ?_⟩
      rw [map_smul, ← hs, Submonoid.smul_def, smul_comm]
    · intro x y hx hy
      obtain ⟨s1, m1, hm1, h1⟩ := hx
      obtain ⟨s2, m2, hm2, h2⟩ := hy
      refine ⟨s1 * s2, (s2 : S) • m1 + (s1 : S) • m2,
        Submodule.add_mem _ (Submodule.smul_mem _ _ hm1) (Submodule.smul_mem _ _ hm2), ?_⟩
      rw [map_add, map_smul, map_smul, ← h1, ← h2, smul_add, Submonoid.coe_mul, mul_smul, mul_smul,
        smul_comm (s1 : S) (s2 : S) x]
  obtain ⟨s, m', hm', he⟩ := key _ h
  rw [← map_smul] at he
  obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := T) he
  refine ⟨c * s, ?_⟩
  simp only [Submonoid.smul_def] at hc
  rw [Submonoid.coe_mul, mul_smul, hc]
  exact Submodule.smul_mem _ _ hm'

theorem UpperTheory.V.AlgebraTools.qRegAt_map :
    ∀ (S R σ : Type) [CommRing S] [CommRing R] [Algebra S R] [Finite σ] (y : σ → S) (J : Ideal S) (a : ℕ),
      (∀ (M : Type) [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower S R M],
        QRegAt M y J a ↔ QRegAt M (fun s => algebraMap S R (y s)) (J.map (algebraMap S R)) a) ∧
      (∀ (T : Submonoid S) (M : Type) [AddCommGroup M] [Module S M] (M' : Type) [AddCommGroup M'] [Module S M'] (f : M →ₗ[S] M') [IsLocalizedModule T f], QRegAt M y J a → QRegAt M' y J a) := by
  intro S R σ _ _ _ _ y J a
  constructor
  · intro M _ _ _ _
    have hv : ∀ α, GlobalTheory.monoVal (fun s => algebraMap S R (y s)) α = algebraMap S R (GlobalTheory.monoVal y α) :=
      fun α => (GlobalTheory.map_monoVal _ _ _).symm
    have e1 : Ideal.span (Set.range fun s => algebraMap S R (y s)) =
        (Ideal.span (Set.range y)).map (algebraMap S R) := by
      rw [Ideal.map_span, ← Set.range_comp]
      rfl
    unfold QRegAt
    simp only [hv, algebraMap_smul, e1, ← Ideal.map_pow, ← Ideal.map_sup, mem_map_smul_top_iff]
  · intro T M _ _ M' _ _ f _ hM
    unfold QRegAt at hM ⊢
    intro c' hc' α
    obtain ⟨s, hs⟩ := IsLocalizedModule.exist_integer_multiples_of_finite T f c'
    have hs' : ∀ i, ∃ m, f m = (s : S) • c' i := fun i => LinearMap.mem_range.1 (hs i)
    choose c hc using hs'
    have h1 : f (∑ β : GlobalTheory.MonoDeg σ a, GlobalTheory.monoVal y (β : σ →₀ ℕ) • c β) ∈
        ((Ideal.span (Set.range y) ^ (a + 1) ⊔ J) • ⊤ : Submodule S M') := by
      simp only [map_sum, map_smul, hc]
      have e : (∑ β : GlobalTheory.MonoDeg σ a, GlobalTheory.monoVal y (β : σ →₀ ℕ) • ((s : S) • c' β)) =
          (s : S) • ∑ β : GlobalTheory.MonoDeg σ a, GlobalTheory.monoVal y (β : σ →₀ ℕ) • c' β := by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun β _ => smul_comm _ _ _
      rw [e]
      exact Submodule.smul_mem _ _ hc'
    obtain ⟨t, ht⟩ := exists_smul_mem T f _ h1
    rw [Finset.smul_sum] at ht
    have h2 := hM (fun β => (t : S) • c β) (by
      rw [show (∑ β : GlobalTheory.MonoDeg σ a, GlobalTheory.monoVal y (β : σ →₀ ℕ) • ((t : S) • c β)) =
          ∑ β : GlobalTheory.MonoDeg σ a, (t : S) • (GlobalTheory.monoVal y (β : σ →₀ ℕ) • c β) from
        Finset.sum_congr rfl fun β _ => smul_comm _ _ _]
      exact ht)
    have h3 := map_mem_smul_top f _ (h2 α)
    rw [map_smul, hc, smul_smul] at h3
    exact mem_of_smul_mem T f _ (t * s) (by rwa [Submonoid.coe_mul])
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.QRegTower
section
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.isQuasiRegularSeq_of_tower :
    ∀ (R σ : Type) [CommRing R] [Finite σ] (y : σ → R) (M : Type) [AddCommGroup M] [Module R M] (P : ℕ → Type) [∀ i, AddCommGroup (P i)] [∀ i, Module R (P i)] (q : ∀ k, M →ₗ[R] P k),
      (∀ k, Function.Surjective (q k)) → (∀ k, LinearMap.ker (q k) = Ideal.span (Set.range y) ^ k • ⊤) →
      (∀ a k, a < k → QRegAt (P k) y ⊥ a) → GlobalTheory.IsQuasiRegularSeq M y := by
  intro R σ _ _ y M _ _ P _ _ q hs hk hq
  rw [isQuasiRegularSeq_iff_qRegAt]
  intro a c hc α
  simp only [sup_bot_eq] at hc ⊢
  have h := hq a (a + 1) (Nat.lt_succ_self a) (fun β => q (a + 1) (c β)) (by
    rw [← hk, LinearMap.mem_ker, map_sum] at hc
    simp only [map_smul] at hc
    rw [hc]
    exact zero_mem _) α
  simp only [sup_bot_eq] at h
  have htop : (⊤ : Submodule R (P (a + 1))) = Submodule.map (q (a + 1)) ⊤ := by
    rw [Submodule.map_top, LinearMap.range_eq_top.2 (hs _)]
  rw [htop, ← Submodule.map_smul''] at h
  have h2 : c α ∈ Submodule.comap (q (a + 1))
      (Submodule.map (q (a + 1)) (Ideal.span (Set.range y) • ⊤ : Submodule R M)) := h
  rw [Submodule.comap_map_eq, hk] at h2
  have hle : (Ideal.span (Set.range y) ^ (a + 1) • ⊤ : Submodule R M) ≤ Ideal.span (Set.range y) • ⊤ :=
    Submodule.smul_mono_left (Ideal.pow_le_self (Nat.succ_ne_zero a))
  rwa [sup_eq_left.2 hle] at h2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.SmulPowLeOfStep
section
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.smul_pow_le_of_step :
    ∀ (R : Type) [CommRing R] (𝔞 I 𝔶 : Ideal R) (f : R),
      (∀ (X : Type) [AddCommGroup X] [Module R X] (X₀ : Type) [AddCommGroup X₀] [Module R X₀] (φ : X₀ →ₗ[R] X) (ψ : X →ₗ[R] X₀) (n : R), (∀ x, φ (ψ x) = n • x) → n ∣ f →
        (𝔞 • ⊤ : Submodule R X₀) ≤ I • ⊤ → ((Ideal.span {f} * 𝔞) • ⊤ : Submodule R X) ≤ I • ⊤) ∧
      (∀ (M : Type) [AddCommGroup M] [Module R M], ((Ideal.span {f} * 𝔞) • ⊤ : Submodule R M) ≤ (I ⊔ 𝔶) • ⊤ →
        ∀ k : ℕ, ((Ideal.span {f ^ k} * 𝔞 ^ k) • ⊤ : Submodule R M) ≤ (I ⊔ 𝔶 ^ k) • ⊤) := by
  intro R _ 𝔞 I 𝔶 f
  refine ⟨?_, ?_⟩
  · intro X _ _ X₀ _ _ φ ψ n hn hnf h
    obtain ⟨c, rfl⟩ := hnf
    refine Submodule.smul_le.2 ?_
    intro r hr x _
    obtain ⟨a, ha, rfl⟩ := Ideal.mem_span_singleton_mul.1 hr
    have h1 : a • ψ x ∈ (I • ⊤ : Submodule R X₀) :=
      h (Submodule.smul_mem_smul ha Submodule.mem_top)
    have h2 : φ (a • ψ x) ∈ (I • ⊤ : Submodule R X) := by
      have h3 : φ (a • ψ x) ∈ (I • ⊤ : Submodule R X₀).map φ := Submodule.mem_map_of_mem h1
      rw [Submodule.map_smul''] at h3
      exact Submodule.smul_mono le_rfl le_top h3
    have h4 : (n * c * a) • x = c • φ (a • ψ x) := by
      rw [map_smul, hn, smul_smul, smul_smul]
      congr 1
      ring
    rw [h4]
    exact Submodule.smul_mem _ c h2
  · intro M _ _ h k
    rw [← Ideal.span_singleton_pow, ← mul_pow]
    generalize Ideal.span {f} * 𝔞 = b at h
    induction k with
    | zero => simp
    | succ k ih =>
      have hle : (I ⊔ 𝔶 ^ k) * (I ⊔ 𝔶) ≤ I ⊔ 𝔶 ^ (k + 1) := by
        rw [Ideal.sup_mul, Ideal.mul_sup (𝔶 ^ k), pow_succ]
        refine sup_le (le_sup_of_le_left Ideal.mul_le_left) (sup_le (le_sup_of_le_left Ideal.mul_le_right) le_sup_right)
      calc (b ^ (k + 1) • ⊤ : Submodule R M) = b • (b ^ k • ⊤) := by
            rw [pow_succ', mul_smul]
        _ ≤ b • ((I ⊔ 𝔶 ^ k) • ⊤) := smul_mono_right b ih
        _ = (I ⊔ 𝔶 ^ k) • (b • ⊤) := by
            rw [← mul_smul, ← mul_smul, mul_comm]
        _ ≤ (I ⊔ 𝔶 ^ k) • ((I ⊔ 𝔶) • ⊤) := smul_mono_right _ h
        _ = ((I ⊔ 𝔶 ^ k) * (I ⊔ 𝔶)) • ⊤ := by rw [mul_smul]
        _ ≤ (I ⊔ 𝔶 ^ (k + 1)) • ⊤ := Submodule.smul_mono_left hle
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.TnIdem
section
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.exists_idem_topNil :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (κ : Type) (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M] (T : κ → Module.End R M), (∀ i j, Commute (T i) (T j)) →
      ∃ e ∈ Algebra.adjoin R (Set.range T), IsIdempotentElem e ∧ LinearMap.range e = topNil (IsLocalRing.maximalIdeal R) T := by
  intro R _ _ _ _ κ M _ _ _ T hT
  classical
  let S := Algebra.adjoin R (Set.range T)
  haveI : Module.Finite R S := by
    haveI : IsNoetherian R (Subalgebra.toSubmodule S) := inferInstance
    exact (inferInstance : Module.Finite R (Subalgebra.toSubmodule S))
  letI : CommRing S := Algebra.adjoinCommRingOfComm R (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact hT i j)
  let t : κ → S := fun i => ⟨T i, Algebra.subset_adjoin ⟨i, rfl⟩⟩
  obtain ⟨e, he, -, hx⟩ := topNil_eq_idem R S κ t
  have hfun : (fun i => (Algebra.lsmul R R M) (t i)) = T := by
    funext i
    rfl
  have he' : IsIdempotentElem (e : Module.End R M) := congrArg Subtype.val he
  refine ⟨(e : Module.End R M), e.2, he', ?_⟩
  ext x
  have h := hx M x
  rw [hfun] at h
  rw [h]
  constructor
  · rintro ⟨y, rfl⟩
    exact LinearMap.congr_fun he' y
  · intro h2
    exact ⟨x, h2⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ULimScal
section
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.ULim.scal_eq :
    ∀ (R ι : Type) [CommRing R] (F : Filter ι) (I : ℕ → Ideal R) (M : ι → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)],
      (∀ (r : ι → R) (s : R), (∀ j, ∀ᶠ N in F, ∀ x : M N, (r N - s) • x ∈ (I j • ⊤ : Submodule R (M N))) →
        ∀ x : ULim F I M, ULim.scal F I M r x = s • x) ∧
      (∀ s : R, (∀ j, ∀ᶠ N in F, ∀ x : M N, s • x ∈ (I j • ⊤ : Submodule R (M N))) → ∀ x : ULim F I M, s • x = 0) ∧
      (∀ (M' : ι → Type) [∀ i, AddCommGroup (M' i)] [∀ i, Module R (M' i)] (f : ∀ i, M i →ₗ[R] M' i) (g : ∀ i, M' i →ₗ[R] M i) (r : ι → R), (∀ i x, g i (f i x) = r i • x) →
        ∀ x : ULim F I M, ULim.map F (fun _ => le_rfl) g (ULim.map F (I' := I) (fun _ => le_rfl) f x) = ULim.scal F I M r x) := by
  intro R ι _ F I M _ _
  have hs : ∀ (r : ι → R) (p : ∀ i, M i), ULim.scal F I M r (ULim.mk F I M p) = ULim.mk F I M (fun i => r i • p i) := by
    intro r p
    simp only [ULim.scal, ULim.map_mk, LinearMap.smul_apply, LinearMap.id_apply]
  have hc : ∀ (s : R) (p : ∀ i, M i), s • ULim.mk F I M p = ULim.mk F I M (fun i => s • p i) := by
    intro s p
    rw [← map_smul]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · intro r s h x
    obtain ⟨p, rfl⟩ := ULim.mk_surjective F I M x
    rw [← sub_eq_zero, hs, hc, ← map_sub, ULim.mk_eq_zero]
    intro j
    filter_upwards [h j] with N hN
    simpa [sub_smul] using hN (p N)
  · intro s h x
    obtain ⟨p, rfl⟩ := ULim.mk_surjective F I M x
    rw [hc, ULim.mk_eq_zero]
    intro j
    filter_upwards [h j] with N hN
    exact hN (p N)
  · intro M' _ _ f g r hfg x
    obtain ⟨p, rfl⟩ := ULim.mk_surjective F I M x
    rw [ULim.map_mk, ULim.map_mk, hs]
    simp only [hfg]
end

