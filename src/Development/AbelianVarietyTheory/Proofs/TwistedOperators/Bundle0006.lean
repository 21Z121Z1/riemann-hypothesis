import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExpandPiOfExpandEach
section
namespace GlobalTheory

theorem expand_pi_of_expand_each {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type} (K : ∀ i, Set (X i)) (m : ι → ℕ)
    (k : ∀ i, Fin (m i) → X i) (hk : ∀ i j, k i j ∈ K i) (c : ∀ i, Fin (m i) → X i → ℂ)
    (f : (∀ i, X i) → ℂ)
    (hf : ∀ i (g : ∀ i, X i), (∀ i, g i ∈ K i) → f g = ∑ j, f (Function.update g i (k i j)) * c i j (g i))
    (g : ∀ i, X i) (hg : ∀ i, g i ∈ K i) :
    f g = ∑ J : (∀ i, Fin (m i)), f (fun i => k i (J i)) * ∏ i, c i (J i) (g i) := by
  classical
  by_cases hm : ∃ i, m i = 0
  · obtain ⟨i0, hi0⟩ := hm
    have h1 : f g = 0 := by
      rw [hf i0 g hg]
      apply Finset.sum_eq_zero
      intro j _
      exact absurd j.2 (by omega)
    haveI : IsEmpty (∀ i, Fin (m i)) := ⟨fun J => by have := (J i0).2; omega⟩
    rw [h1, Finset.univ_eq_empty, Finset.sum_empty]
  push_neg at hm
  let j0 : ∀ i, Fin (m i) := fun i => ⟨0, Nat.pos_of_ne_zero (hm i)⟩
  let T : Finset ι → ∀ i, Finset (Fin (m i)) := fun s i => if i ∈ s then Finset.univ else {j0 i}
  let H : Finset ι → (∀ i, Fin (m i)) → (∀ i, X i) → (∀ i, X i) :=
    fun s J g i => if i ∈ s then k i (J i) else g i
  have hmem : ∀ s (J : ∀ i, Fin (m i)), J ∈ Fintype.piFinset (T s) ↔ ∀ i, i ∉ s → J i = j0 i := by
    intro s J
    rw [Fintype.mem_piFinset]
    apply forall_congr'
    intro i
    by_cases hi : i ∈ s <;> simp [T, hi]
  have key : ∀ s : Finset ι, ∀ g : ∀ i, X i, (∀ i, g i ∈ K i) →
      f g = ∑ J ∈ Fintype.piFinset (T s), f (H s J g) * ∏ i ∈ s, c i (J i) (g i) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro g hg
      have hT : T ∅ = fun i => {j0 i} := by funext i; simp [T]
      rw [hT, Fintype.piFinset_singleton, Finset.sum_singleton, Finset.prod_empty, mul_one]
      congr 1
    | insert a s ha ih =>
      intro g hg
      have hHK : ∀ J, ∀ i, H s J g i ∈ K i := by
        intro J i
        simp only [H]
        split_ifs
        exacts [hk _ _, hg i]
      rw [ih g hg]
      have step : ∀ J ∈ Fintype.piFinset (T s), f (H s J g) * ∏ i ∈ s, c i (J i) (g i)
          = ∑ j, f (H (insert a s) (Function.update J a j) g)
              * ∏ i ∈ insert a s, c i (Function.update J a j i) (g i) := by
        intro J _
        rw [hf a _ (hHK J), Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        have e1 : Function.update (H s J g) a (k a j) = H (insert a s) (Function.update J a j) g := by
          funext i
          by_cases hia : i = a
          · subst hia
            simp [H]
          · simp [H, Function.update_of_ne hia, Finset.mem_insert, hia]
        have e2 : H s J g a = g a := by simp [H, ha]
        rw [e1, e2, Finset.prod_insert ha, Function.update_self]
        have e3 : ∏ i ∈ s, c i (Function.update J a j i) (g i) = ∏ i ∈ s, c i (J i) (g i) := by
          refine Finset.prod_congr rfl fun i hi => ?_
          have : i ≠ a := fun h => ha (h ▸ hi)
          rw [Function.update_of_ne this]
        rw [e3]
        ring
      rw [Finset.sum_congr rfl step, ← Finset.sum_product']
      refine Finset.sum_nbij' (fun p => Function.update p.1 a p.2)
        (fun J' => (Function.update J' a (j0 a), J' a)) ?_ ?_ ?_ ?_ ?_
      · rintro ⟨J, j⟩ hp
        simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_product, hmem] at hp
        simp only [Finset.mem_coe, hmem]
        intro i hi
        rw [Finset.mem_insert, not_or] at hi
        rw [Function.update_of_ne hi.1]
        exact hp.1 i hi.2
      · intro J' hJ'
        simp only [Finset.mem_coe, hmem] at hJ'
        simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_product,
          Finset.mem_univ, and_true, hmem]
        intro i hi
        by_cases hia : i = a
        · subst hia
          simp
        · rw [Function.update_of_ne hia]
          exact hJ' i (by simp [hia, hi])
      · rintro ⟨J, j⟩ hp
        simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_product, hmem] at hp
        simp only [Function.update_idem, Function.update_self, Prod.mk.injEq, and_true]
        funext i
        by_cases hia : i = a
        · subst hia
          rw [Function.update_self]
          exact (hp.1 _ ha).symm
        · rw [Function.update_of_ne hia]
      · intro J' _
        simp only [Function.update_idem, Function.update_eq_self]
      · rintro ⟨J, j⟩ _
        rfl
  rw [key Finset.univ g hg]
  have hTu : T Finset.univ = fun _ => Finset.univ := by funext i; simp [T]
  rw [hTu, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun J _ => ?_
  congr 2
  funext i
  simp [H]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteAndNcardMinpolyCoeffHeightLe
section
open NumberField Polynomial

namespace GlobalTheory.MinpolyHeightCount

theorem finite_and_ncard_le_of_fibres {α β : Type*} {S : Set α} {T : Set β} {f : α → β}
    (hT : T.Finite) (hf : Set.MapsTo f S T) (m : ℕ)
    (hfib : ∀ t ∈ T, (S ∩ f ⁻¹' {t}).Finite ∧ (S ∩ f ⁻¹' {t}).ncard ≤ m) :
    S.Finite ∧ S.ncard ≤ m * T.ncard := by
  classical
  have hS : S.Finite := by
    refine (hT.biUnion fun t ht => (hfib t ht).1).subset fun x hx => ?_
    exact Set.mem_biUnion (hf hx) ⟨hx, rfl⟩
  refine ⟨hS, ?_⟩
  rw [Set.ncard_eq_toFinset_card _ hS, Set.ncard_eq_toFinset_card _ hT]
  refine Finset.card_le_mul_card_image_of_maps_to (f := f)
    (fun a ha => by simpa using hf (by simpa using ha)) m fun t ht => ?_
  have h := (hfib t (by simpa using ht)).2
  have e : (({a ∈ hS.toFinset | f a = t} : Finset α) : Set α) = S ∩ f ⁻¹' {t} := by
    ext a; simp
  rw [← Set.ncard_coe_finset, e]
  exact h

theorem finite_and_ncard_le_of_eval_eq_zero {L : Type*} [Field L] {S : Set L} {p : L[X]}
    (hp : p ≠ 0) (hS : ∀ x ∈ S, p.eval x = 0) : S.Finite ∧ S.ncard ≤ p.natDegree := by
  classical
  have hsub : S ⊆ (p.roots.toFinset : Set L) := fun x hx => by
    simp [Multiset.mem_toFinset, mem_roots hp, IsRoot.def, hS x hx]
  refine ⟨(Finset.finite_toSet _).subset hsub, ?_⟩
  calc S.ncard ≤ (p.roots.toFinset : Set L).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = p.roots.toFinset.card := Set.ncard_coe_finset _
    _ ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
    _ ≤ p.natDegree := card_roots' p

theorem finite_and_ncard_le_of_fibres_roots {L β : Type*} [Field L] {S : Set L} {T : Set β}
    {f : L → β} (hT : T.Finite) (hf : Set.MapsTo f S T) (m : ℕ)
    (hfib : ∀ t ∈ T, ∃ p : L[X], p ≠ 0 ∧ p.natDegree ≤ m ∧ ∀ x ∈ S, f x = t → p.eval x = 0) :
    S.Finite ∧ S.ncard ≤ m * T.ncard := by
  refine finite_and_ncard_le_of_fibres hT hf m fun t ht => ?_
  obtain ⟨p, hp, hdeg, hroot⟩ := hfib t ht
  obtain ⟨h1, h2⟩ := finite_and_ncard_le_of_eval_eq_zero (S := S ∩ f ⁻¹' {t}) hp
    fun x hx => hroot x hx.1 hx.2
  exact ⟨h1, h2.trans hdeg⟩

section Integral

variable (K : Type) [Field K] [NumberField K]

theorem natDegree_minpoly_int_le {x : K} (hx : IsIntegral ℤ x) :
    (minpoly ℤ x).natDegree ≤ Module.finrank ℚ K := by
  rw [← (minpoly.monic hx).natDegree_map (algebraMap ℤ ℚ),
    ← minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hx]
  exact minpoly.natDegree_le x

theorem abs_coeff_minpoly_int_le {x : K} (hx : IsIntegral ℤ x) {R : ℝ}
    (h : ∀ φ : K →+* ℂ, ‖φ x‖ ≤ R) (i : ℕ) :
    (|(minpoly ℤ x).coeff i| : ℝ) ≤ max R 1 ^ Module.finrank ℚ K *
      (Module.finrank ℚ K).choose (Module.finrank ℚ K / 2) := by
  refine Eq.trans_le ?_ (Embeddings.coeff_bdd_of_norm_le h i)
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hx, coeff_map, eq_intCast,
    Int.norm_cast_rat, Int.norm_eq_abs]

theorem finite_and_ncard_integral_le (R : ℝ) :
    {x : K | IsIntegral ℤ x ∧ ∀ φ : K →+* ℂ, ‖φ x‖ ≤ R}.Finite ∧
    (({x : K | IsIntegral ℤ x ∧ ∀ φ : K →+* ℂ, ‖φ x‖ ≤ R}.ncard : ℕ) : ℝ) ≤
      Module.finrank ℚ K * (2 * (max R 1 ^ Module.finrank ℚ K *
        (Module.finrank ℚ K).choose (Module.finrank ℚ K / 2)) + 3) ^
          (Module.finrank ℚ K + 1) := by
  classical
  set d := Module.finrank ℚ K with hd
  set M : ℝ := max R 1 ^ d * (d.choose (d / 2) : ℝ) with hM
  set C : ℕ := ⌈M⌉₊ with hC
  set T : Set (Fin (d + 1) → ℤ) :=
    ((Fintype.piFinset fun _ : Fin (d + 1) => Finset.Icc (-(C : ℤ)) C : Finset (Fin (d + 1) → ℤ)) :
      Set (Fin (d + 1) → ℤ)) with hTdef
  set f : K → Fin (d + 1) → ℤ := fun x i => (minpoly ℤ x).coeff i with hfdef
  have hT : T.ncard = (2 * C + 1) ^ (d + 1) := by
    rw [hTdef, Set.ncard_coe_finset, Fintype.card_piFinset, Finset.prod_const, Int.card_Icc,
      Finset.card_univ, Fintype.card_fin]
    congr 1
    omega
  have hmaps : Set.MapsTo f {x : K | IsIntegral ℤ x ∧ ∀ φ : K →+* ℂ, ‖φ x‖ ≤ R} T := by
    intro x hx
    rw [hTdef, Finset.mem_coe, Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    have h1 := abs_coeff_minpoly_int_le K hx.1 hx.2 i
    have h2 : (|(minpoly ℤ x).coeff i| : ℝ) ≤ (C : ℝ) := h1.trans (Nat.le_ceil _)
    have h3 : |(minpoly ℤ x).coeff i| ≤ (C : ℤ) := by exact_mod_cast h2
    exact abs_le.mp h3
  obtain ⟨hfin, hcard⟩ := finite_and_ncard_le_of_fibres_roots (Finset.finite_toSet _) hmaps d
    (by
      intro t _
      by_cases h : ∃ x0 ∈ {x : K | IsIntegral ℤ x ∧ ∀ φ : K →+* ℂ, ‖φ x‖ ≤ R}, f x0 = t
      · obtain ⟨x0, hx0, hfx0⟩ := h
        refine ⟨(minpoly ℤ x0).map (algebraMap ℤ K), ((minpoly.monic hx0.1).map _).ne_zero, ?_, ?_⟩
        · rw [(minpoly.monic hx0.1).natDegree_map]
          exact natDegree_minpoly_int_le K hx0.1
        · intro y hy hfy
          have heq : minpoly ℤ y = minpoly ℤ x0 := by
            ext i
            by_cases hi : i < d + 1
            · exact congrFun (hfy.trans hfx0.symm) ⟨i, hi⟩
            · rw [coeff_eq_zero_of_natDegree_lt ((natDegree_minpoly_int_le K hy.1).trans_lt
                (by omega)), coeff_eq_zero_of_natDegree_lt
                ((natDegree_minpoly_int_le K hx0.1).trans_lt (by omega))]
          rw [eval_map_algebraMap, ← heq]
          exact minpoly.aeval ℤ y
      · refine ⟨1, one_ne_zero, by simp, fun x hx hfx => (h ⟨x, hx, hfx⟩).elim⟩)
  refine ⟨hfin, ?_⟩
  have hM0 : 0 ≤ M := by positivity
  have hC' : (C : ℝ) ≤ M + 1 := (Nat.ceil_lt_add_one hM0).le
  rw [hT] at hcard
  calc (({x : K | IsIntegral ℤ x ∧ ∀ φ : K →+* ℂ, ‖φ x‖ ≤ R}.ncard : ℕ) : ℝ)
      ≤ ((d * (2 * C + 1) ^ (d + 1) : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = (d : ℝ) * (2 * (C : ℝ) + 1) ^ (d + 1) := by push_cast; ring
    _ ≤ (d : ℝ) * (2 * M + 3) ^ (d + 1) := by
      have h23 : 2 * (C : ℝ) + 1 ≤ 2 * M + 3 := by linarith
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h23 _) (by positivity)

end Integral

section Height

variable {K : Type} [Field K] [NumberField K]

theorem norm_embedding_le_mulHeight₁ (φ : K →+* ℂ) (c : K) : ‖φ c‖ ≤ Height.mulHeight₁ c := by
  classical
  set w := InfinitePlace.mk φ
  have hw : w c = ‖φ c‖ := InfinitePlace.apply φ c
  rw [← hw, NumberField.mulHeight₁_eq]
  have h1 : ∀ v : InfinitePlace K, 1 ≤ max (v c) 1 ^ v.mult :=
    fun v => one_le_pow₀ (le_max_right _ _)
  calc w c ≤ max (w c) 1 := le_max_left _ _
    _ ≤ max (w c) 1 ^ w.mult := le_self_pow₀ (le_max_right _ _) w.mult_ne_zero
    _ ≤ ∏ v : InfinitePlace K, max (v c) 1 ^ v.mult := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ w)]
      exact le_mul_of_one_le_right (by positivity) (Finset.one_le_prod fun v _ => h1 v)
    _ ≤ _ := le_mul_of_one_le_right (Finset.prod_nonneg fun v _ => by positivity)
        (one_le_finprod fun _ => le_max_right _ _)

variable (K) in

theorem exists_ncard_mulHeight₁_le : ∃ (C : ℝ) (k : ℕ), ∀ B : ℝ, 1 ≤ B →
    {c : K | Height.mulHeight₁ c ≤ B}.Finite ∧
      (({c : K | Height.mulHeight₁ c ≤ B}.ncard : ℕ) : ℝ) ≤ C * B ^ k := by
  classical
  set d := Module.finrank ℚ K with hd
  refine ⟨d * (2 * (d.choose (d / 2) : ℝ) + 3) ^ (d + 1), 1 + 2 * d * (d + 1), fun B hB => ?_⟩
  refine ⟨finite_setOfPred_mulHeight₁_le K B, ?_⟩
  choose n hn0 hnle hint using fun c : K => exists_nat_le_mulHeight₁ c
  set A := {x : K | IsIntegral ℤ x ∧ ∀ φ : K →+* ℂ, ‖φ x‖ ≤ B ^ 2} with hAdef
  obtain ⟨hAfin, hAcard⟩ := finite_and_ncard_integral_le K (B ^ 2)
  set P : Set (ℕ × K) := (↑(Finset.Icc 1 ⌊B⌋₊) : Set ℕ) ×ˢ A with hPdef
  have hP : P.Finite := (Finset.finite_toSet _).prod hAfin
  have hle : {c : K | Height.mulHeight₁ c ≤ B}.ncard ≤ P.ncard := by
    refine Set.ncard_le_ncard_of_injOn (fun c => (n c, (n c : K) * c)) ?_ ?_ hP
    · intro c hc
      have hc' : Height.mulHeight₁ c ≤ B := hc
      refine Set.mk_mem_prod ?_ ⟨hint c, fun φ => ?_⟩
      · rw [Finset.mem_coe, Finset.mem_Icc]
        exact ⟨Nat.one_le_iff_ne_zero.mpr (hn0 c), Nat.le_floor ((hnle c).trans hc')⟩
      · rw [map_mul, norm_mul, map_natCast, Complex.norm_natCast, sq]
        exact mul_le_mul ((hnle c).trans hc') ((norm_embedding_le_mulHeight₁ φ c).trans hc')
          (norm_nonneg _) (by linarith)
    · intro c _ c' _ h
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      rw [h1] at h2
      exact mul_left_cancel₀ (by exact_mod_cast hn0 c') h2
  have hPcard : P.ncard = ⌊B⌋₊ * A.ncard := by
    rw [hPdef, Set.ncard_prod, Set.ncard_coe_finset, Nat.card_Icc, Nat.add_sub_cancel]
  have hfl : (⌊B⌋₊ : ℝ) ≤ B := Nat.floor_le (by linarith)
  have hmax : max (B ^ 2) 1 = B ^ 2 := max_eq_left (by nlinarith)
  rw [hmax] at hAcard
  have hX : 1 ≤ B ^ (2 * d) := one_le_pow₀ hB
  have hch : (0 : ℝ) ≤ (d.choose (d / 2) : ℝ) := Nat.cast_nonneg _
  have hstep : 2 * ((B ^ 2) ^ d * (d.choose (d / 2) : ℝ)) + 3 ≤
      (2 * (d.choose (d / 2) : ℝ) + 3) * B ^ (2 * d) := by
    rw [← pow_mul]; nlinarith
  calc (({c : K | Height.mulHeight₁ c ≤ B}.ncard : ℕ) : ℝ) ≤ (P.ncard : ℝ) := by
        exact_mod_cast hle
    _ = (⌊B⌋₊ : ℝ) * (A.ncard : ℝ) := by rw [hPcard]; push_cast; ring
    _ ≤ B * (d * (2 * ((B ^ 2) ^ d * (d.choose (d / 2) : ℝ)) + 3) ^ (d + 1)) :=
        mul_le_mul hfl hAcard (Nat.cast_nonneg _) (by linarith)
    _ ≤ B * (d * ((2 * (d.choose (d / 2) : ℝ) + 3) * B ^ (2 * d)) ^ (d + 1)) := by
        gcongr
    _ = _ := by rw [mul_pow, ← pow_mul, pow_add B 1, pow_one]; ring

end Height

theorem finite_and_ncard_minpoly_height_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E], ∃ (C : ℝ) (k : ℕ), ∀ B : ℝ, 1 ≤ B →
      {x : E | ∀ j, Height.mulHeight₁ ((minpoly F x).coeff j) ≤ B}.Finite ∧
      (({x : E | ∀ j, Height.mulHeight₁ ((minpoly F x).coeff j) ≤ B}.ncard : ℕ) : ℝ) ≤
        C * B ^ k := by
  intro F E _ _ _ _ _
  classical
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨C₁, k₁, h₁⟩ := exists_ncard_mulHeight₁_le F
  set m := Module.finrank F E with hm
  refine ⟨m * C₁ ^ (m + 1), k₁ * (m + 1), fun B hB => ?_⟩
  obtain ⟨hSfin, hScard⟩ := h₁ B hB
  set S := {c : F | Height.mulHeight₁ c ≤ B} with hSdef
  set X := {x : E | ∀ j, Height.mulHeight₁ ((minpoly F x).coeff j) ≤ B} with hXdef
  set T : Set (Fin (m + 1) → F) :=
    ((Fintype.piFinset fun _ : Fin (m + 1) => hSfin.toFinset : Finset (Fin (m + 1) → F)) :
      Set (Fin (m + 1) → F)) with hTdef
  set f : E → Fin (m + 1) → F := fun x j => (minpoly F x).coeff j with hfdef
  have hT : T.ncard = S.ncard ^ (m + 1) := by
    rw [hTdef, Set.ncard_coe_finset, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, Set.ncard_eq_toFinset_card _ hSfin]
  have hmaps : Set.MapsTo f X T := by
    intro x hx
    rw [hTdef, Finset.mem_coe, Fintype.mem_piFinset]
    intro j
    rw [Set.Finite.mem_toFinset]
    exact hx j
  obtain ⟨hXfin, hXcard⟩ := finite_and_ncard_le_of_fibres_roots (Finset.finite_toSet _) hmaps m
    (by
      intro t _
      by_cases h : ∃ x0 ∈ X, f x0 = t
      · obtain ⟨x0, -, hfx0⟩ := h
        have hi0 : IsIntegral F x0 := Algebra.IsIntegral.isIntegral x0
        refine ⟨(minpoly F x0).map (algebraMap F E), ((minpoly.monic hi0).map _).ne_zero, ?_, ?_⟩
        · rw [(minpoly.monic hi0).natDegree_map]; exact minpoly.natDegree_le x0
        · intro y _ hfy
          have heq : minpoly F y = minpoly F x0 := by
            ext i
            by_cases hi : i < m + 1
            · exact congrFun (hfy.trans hfx0.symm) ⟨i, hi⟩
            · rw [coeff_eq_zero_of_natDegree_lt ((minpoly.natDegree_le y).trans_lt (by omega)),
                coeff_eq_zero_of_natDegree_lt ((minpoly.natDegree_le x0).trans_lt (by omega))]
          rw [eval_map_algebraMap, ← heq]
          exact minpoly.aeval F y
      · exact ⟨1, one_ne_zero, by simp, fun x hx hfx => (h ⟨x, hx, hfx⟩).elim⟩)
  refine ⟨hXfin, ?_⟩
  rw [hT] at hXcard
  have h0 : (0 : ℝ) ≤ (S.ncard : ℝ) := Nat.cast_nonneg _
  calc ((X.ncard : ℕ) : ℝ) ≤ ((m * S.ncard ^ (m + 1) : ℕ) : ℝ) := by exact_mod_cast hXcard
    _ = (m : ℝ) * (S.ncard : ℝ) ^ (m + 1) := by push_cast; ring
    _ ≤ (m : ℝ) * (C₁ * B ^ k₁) ^ (m + 1) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 hScard _) (Nat.cast_nonneg _)
    _ = _ := by rw [mul_pow, ← pow_mul]; ring

end GlobalTheory.MinpolyHeightCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinrankEqCardMulAndTraceEqZeroOfFreeValues
section
namespace GlobalTheory

theorem trace_eq_zero_of_coord_move {X W : Type} [Fintype X] [DecidableEq X] [AddCommGroup W]
    [Module ℂ W] [FiniteDimensional ℂ W] (π : X → X) (hπ : ∀ c, π c ≠ c)
    (φ : X → Module.End ℂ W) (M : Module.End ℂ (X → W)) (hM : ∀ f c, M f c = φ c (f (π c))) :
    LinearMap.trace ℂ (X → W) M = 0 := by
  classical

  let b := Pi.basis (fun _ : X => Module.finBasis ℂ W)
  rw [LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, Pi.basis_repr, Pi.basis_apply, hM,
    Pi.single_eq_of_ne (hπ i.1), map_zero, map_zero, Finsupp.zero_apply]

theorem finrank_eq_card_mul_and_trace_eq_zero_of_free_values :
    ∀ (Y X B W : Type) [Finite X] [AddCommGroup B] [Module ℂ B] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (cls : Y → X) (ev : Y → (B →ₗ[ℂ] W)) (S : Submodule ℂ B), Function.Surjective cls → (∀ T : B, (∀ h, ev h T = 0) → T = 0) → (∀ h h', cls h = cls h' → ∃ φ : Module.End ℂ W, ∀ T ∈ S, ev h' T = φ (ev h T)) → (∀ h (ℓ : W), ∃ T ∈ S, ev h T = ℓ ∧ ∀ h', cls h' ≠ cls h → ev h' T = 0) → FiniteDimensional ℂ S ∧ Module.finrank ℂ S = Nat.card X * Module.finrank ℂ W ∧ ∀ (H : Type) [AddCommGroup H] [Module ℂ H] (e : H →ₗ[ℂ] B), Function.Injective e → LinearMap.range e = S → ∀ (A : Module.End ℂ H) (t : Y → Y), (∀ x h, ev h (e (A x)) = ev (t h) (e x)) → (∀ h, cls (t h) ≠ cls h) → LinearMap.trace ℂ H A = 0 := by
  intro Y X B W _ _ _ _ _ _ cls ev S hcls hinj hcls_eq hfree
  classical
  haveI : Fintype X := Fintype.ofFinite X

  obtain ⟨s, hs⟩ : ∃ s : X → Y, ∀ x, cls (s x) = x :=
    ⟨fun x => (hcls x).choose, fun x => (hcls x).choose_spec⟩

  let Φ : S →ₗ[ℂ] (X → W) := LinearMap.pi (fun x => (ev (s x)).comp S.subtype)
  have hΦ : ∀ (T : S) x, Φ T x = ev (s x) T := fun _ _ => rfl
  have hzero : ∀ T ∈ S, (∀ x, ev (s x) T = 0) → T = 0 := by
    intro T hT h0
    apply hinj
    intro h
    obtain ⟨φ, hφ⟩ := hcls_eq (s (cls h)) h (hs _)
    rw [hφ T hT, h0, map_zero]
  have hΦinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro T hT
    refine Subtype.ext (hzero T T.2 (fun x => ?_))
    have hx := congrFun hT x
    rw [hΦ] at hx
    exact hx
  have hΦsurj : Function.Surjective Φ := by
    intro g
    choose T hTS hTg hT0 using fun x => hfree (s x) (g x)
    refine ⟨⟨∑ x, T x, Submodule.sum_mem _ (fun x _ => hTS x)⟩, ?_⟩
    funext y
    show ev (s y) (∑ x, T x) = g y
    rw [map_sum, Finset.sum_eq_single y]
    · exact hTg y
    · intro x _ hxy
      apply hT0
      rw [hs, hs]
      exact Ne.symm hxy
    · intro h
      exact absurd (Finset.mem_univ y) h
  let Ψ : S ≃ₗ[ℂ] (X → W) := LinearEquiv.ofBijective Φ ⟨hΦinj, hΦsurj⟩
  have hfd : FiniteDimensional ℂ S := LinearEquiv.finiteDimensional Ψ.symm
  refine ⟨hfd, ?_, ?_⟩
  · rw [Ψ.finrank_eq, Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      Nat.card_eq_fintype_card]
  · intro H _ _ e he hrange A t hA ht

    let eS : H ≃ₗ[ℂ] S := (LinearEquiv.ofInjective e he).trans (LinearEquiv.ofEq _ _ hrange)
    let Θ : H ≃ₗ[ℂ] (X → W) := eS.trans Ψ
    have hΘ : ∀ x c, Θ x c = ev (s c) (e x) := fun _ _ => rfl
    haveI : FiniteDimensional ℂ H := LinearEquiv.finiteDimensional Θ.symm
    rw [← LinearMap.trace_conj' A Θ]
    choose φ hφ using fun c => hcls_eq (s (cls (t (s c)))) (t (s c)) (hs _)
    refine trace_eq_zero_of_coord_move (fun c => cls (t (s c)))
      (fun c => by have h := ht (s c); rwa [hs] at h) φ _ ?_
    intro g c
    obtain ⟨x, rfl⟩ := Θ.surjective g
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply, hΘ, hΘ, hA]
    have hmem : e x ∈ S := by
      rw [← hrange]
      exact LinearMap.mem_range_self e x
    exact hφ c (e x) hmem

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinsetFunctionsRecoveredFromValues
section
namespace GlobalTheory

open Module

theorem finset_functions_recovered_from_values {X : Type} (V : Submodule ℂ (X → ℂ)) (F : Finset (X → ℂ))
    (hF : ∀ u ∈ F, u ∈ V) :
    ∃ (s : Finset X) (E : X → X → ℂ), (∀ x, E x ∈ V) ∧ ∀ u ∈ F, u = ∑ x ∈ s, u x • E x := by
  classical
  set W : Submodule ℂ (X → ℂ) := Submodule.span ℂ (F : Set (X → ℂ)) with hWdef
  haveI : FiniteDimensional ℂ W := FiniteDimensional.span_finset ℂ F
  have hWV : W ≤ V := Submodule.span_le.mpr (fun u hu => hF u hu)
  let ev : X → Module.Dual ℂ W := fun x => (LinearMap.proj x).comp W.subtype
  have hev : ∀ x (w : W), ev x w = (w : X → ℂ) x := fun x w => rfl
  set S : Submodule ℂ (Module.Dual ℂ W) := Submodule.span ℂ (Set.range ev) with hSdef
  have hcoan : S.dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [Submodule.mem_dualCoannihilator] at hw
    have h0 : (w : X → ℂ) = 0 := by
      funext x
      have := hw (ev x) (Submodule.subset_span ⟨x, rfl⟩)
      simpa [hev] using this
    rw [Submodule.mem_bot]
    exact Subtype.ext h0
  have hS : S = ⊤ := by
    have := Subspace.dualCoannihilator_dualAnnihilator_eq (W := S)
    rw [← this, hcoan, Submodule.dualAnnihilator_bot]
  let b := Module.finBasis ℂ W
  have hμ : ∀ i, ∃ c : X →₀ ℂ, (c.sum fun x a => a • ev x) = b.coord i := by
    intro i
    have : b.coord i ∈ S := by rw [hS]; trivial
    exact Finsupp.mem_span_range_iff_exists_finsupp.mp this
  choose μ hμ using hμ
  set s : Finset X := Finset.univ.biUnion (fun i => (μ i).support) with hsdef
  have hsub : ∀ i, (μ i).support ⊆ s := fun i x hx => Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hx⟩
  refine ⟨s,
    fun x => ∑ i, μ i x • ((b i : W) : X → ℂ), ?_, ?_⟩
  · intro x
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (hWV (b i).2))
  · intro u hu
    let w : W := ⟨u, Submodule.subset_span hu⟩
    have hw : (w : X → ℂ) = u := rfl
    have hrep : ∀ i, b.repr w i = ∑ x ∈ s, μ i x * u x := by
      intro i
      have h1 : b.repr w i = b.coord i w := rfl
      rw [h1, ← hμ i, Finsupp.sum_of_support_subset (μ i) (hsub i)]
      · simp [LinearMap.sum_apply, hev, hw]
      · intro x _; simp
    calc u = ((∑ i, b.repr w i • b i : W) : X → ℂ) := by rw [b.sum_repr w]
      _ = ∑ i, b.repr w i • ((b i : W) : X → ℂ) := by
          rw [Submodule.coe_sum]; simp only [Submodule.coe_smul]
      _ = _ := by
        simp_rw [hrep, Finset.smul_sum, Finset.sum_smul, smul_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun i _ => ?_))
        rw [mul_comm]

end GlobalTheory
end

