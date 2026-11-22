import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompletedLocalisationInvariants
section
open PowerSeries

namespace GlobalTheory

namespace CompletedInvariants

theorem smodEq_iff {R : Type} [CommRing R] (q : R) (n : ℕ) (a b : R) :
    a ≡ b [SMOD ((Ideal.span {q}) ^ n • ⊤ : Submodule R R)] ↔ q ^ n ∣ a - b := by
  rw [SModEq.sub_mem, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top,
    Ideal.mem_span_singleton]

theorem eq_zero_of_dvd {R : Type} [CommRing R] (q : R) (h : IsAdicComplete (Ideal.span {q}) R)
    (z : R) (hz : ∀ k : ℕ, q ^ k ∣ z) : z = 0 := by
  refine IsHausdorff.haus h.toIsHausdorff z fun n => ?_
  rw [smodEq_iff, sub_zero]; exact hz n

theorem exists_lim {R : Type} [CommRing R] (q : R) (h : IsAdicComplete (Ideal.span {q}) R)
    (f : ℕ → R) (hf : ∀ m n, m ≤ n → q ^ m ∣ f m - f n) : ∃ L, ∀ n, q ^ n ∣ f n - L := by
  obtain ⟨L, hL⟩ := IsPrecomplete.prec h.toIsPrecomplete (f := f)
    (fun {m n} hmn => (smodEq_iff q m _ _).2 (hf m n hmn))
  exact ⟨L, fun n => (smodEq_iff q n _ _).1 (hL n)⟩

theorem map_dvd' {O R S : Type} [CommRing O] [CommRing R] [CommRing S] [Algebra O R] [Algebra O S]
    (f : R →ₐ[O] S) (p k : ℕ) {z : R} (h : (p : R) ^ k ∣ z) : (p : S) ^ k ∣ f z := by
  have := map_dvd f h
  simpa using this

end CompletedInvariants

open CompletedInvariants in

theorem completed_localisation_invariants : ∀ {O A A' E E' J : Type} [CommRing O] [CommRing A] [CommRing A'] [CommRing E] [CommRing E'] [Algebra O A] [Algebra O A'] [Algebra O E] [Algebra O E'] (p : ℕ) (x : A) (x' : A') (ι : A →ₐ[O] E) (ι' : A' →ₐ[O] E') (j : A →ₐ[O] A') (g : E →ₐ[O] E') (D : Finset J) (δA : J → (A' →ₐ[O] A')) (δE : J → (E' →ₐ[O] E')), (∀ a, g (ι a) = ι' (j a)) → (∀ d a, δE d (ι' a) = ι' (δA d a)) → IsUnit (ι x) → IsAdicComplete (Ideal.span {(p : E)}) E → IsAdicComplete (Ideal.span {(p : E')}) E' → (∀ (y : E) (k : ℕ), ∃ (a : A) (m : ℕ), (p : E) ^ k ∣ y * ι (x ^ m) - ι a) → (∀ (y : E') (k : ℕ), ∃ (a : A') (m : ℕ), (p : E') ^ k ∣ y * ι' (x' ^ m) - ι' a) → (∀ (a : A') (k : ℕ), (p : E') ^ k ∣ ι' a → (p : A') ^ k ∣ a) → (∀ (a : A) (k : ℕ), (p : A') ^ k ∣ j a → (p : A) ^ k ∣ a) → x' ∣ j x → IsUnit (D.card : O) → (∀ a', (∃ a, j a = a') ↔ ∀ d ∈ D, δA d a' = a') → (∀ a', ∀ d ∈ D, δA d (∑ d' ∈ D, δA d' a') = ∑ d' ∈ D, δA d' a') → Function.Injective g ∧ ∀ y, (∃ z, g z = y) ↔ ∀ d ∈ D, δE d y = y := by
  intro O A A' E E' J _ _ _ _ _ _ _ _ _ p x x' ι ι' j g D δA δE hg hδ hx hE hE' dE dE' sE' sj
    hxx hD hinv havg
  have hxm : ∀ m : ℕ, IsUnit (ι (x ^ m)) := fun m => by rw [map_pow]; exact hx.pow m
  have hfix : ∀ a, ∀ d ∈ D, δE d (g (ι a)) = g (ι a) := fun a d hd => by
    rw [hg, hδ, (hinv (j a)).1 ⟨a, rfl⟩ d hd]
  have sat : ∀ (z : E) (k : ℕ), (p : E') ^ k ∣ g z → (p : E) ^ k ∣ z := by
    intro z k hz
    obtain ⟨a, m, h⟩ := dE z k
    have h1 := map_dvd' g p k h
    rw [map_sub, map_mul] at h1
    have h2 : (p : E') ^ k ∣ g (ι a) := (dvd_sub_right (hz.mul_right _)).1 h1
    rw [hg] at h2
    have h3 := map_dvd' ι p k (sj a k (sE' _ k h2))
    have h4 : (p : E) ^ k ∣ z * ι (x ^ m) := by
      have := dvd_add h h3
      simpa using this
    exact (hxm m).dvd_mul_right.1 h4
  refine ⟨?_, fun y => ⟨?_, fun hy => ?_⟩⟩
  · rw [injective_iff_map_eq_zero]
    intro z hz
    exact eq_zero_of_dvd _ hE z fun k => sat z k (hz ▸ dvd_zero _)
  · rintro ⟨z, rfl⟩ d hd
    rw [← sub_eq_zero]
    refine eq_zero_of_dvd _ hE' _ fun k => ?_
    obtain ⟨a, m, h⟩ := dE z k
    have h1 := map_dvd' g p k h
    rw [map_sub, map_mul] at h1
    have h2 := map_dvd' (δE d) p k h1
    rw [map_sub, map_mul, hfix _ d hd, hfix _ d hd] at h2
    have h3 := dvd_sub h2 h1
    have hu : IsUnit (g (ι (x ^ m))) := (hxm m).map g
    refine hu.dvd_mul_right.1 ?_
    convert h3 using 1
    ring
  · have key : ∀ k : ℕ, ∃ z, (p : E') ^ k ∣ y - g z := by
      intro k
      obtain ⟨a', m, h⟩ := dE' y k
      obtain ⟨c, hc⟩ := hxx
      have h1 : (p : E') ^ k ∣ y * g (ι (x ^ m)) - ι' (a' * c ^ m) := by
        have := h.mul_right (ι' (c ^ m))
        convert this using 1
        rw [hg, map_pow j, hc, mul_pow, map_mul, map_mul]
        ring
      set b := a' * c ^ m
      have h2 : ∀ d ∈ D, (p : E') ^ k ∣ y * g (ι (x ^ m)) - ι' (δA d b) := fun d hd => by
        have := map_dvd' (δE d) p k h1
        rwa [map_sub, map_mul, hfix _ d hd, hy d hd, hδ] at this
      have h3 := Finset.dvd_sum h2
      obtain ⟨a, ha⟩ := (hinv _).2 (havg b)
      rw [Finset.sum_sub_distrib, ← map_sum, ← ha, ← hg, Finset.sum_const, nsmul_eq_mul] at h3
      obtain ⟨n, hn⟩ := hD.exists_left_inv
      obtain ⟨v, hv⟩ := (hxm m).exists_right_inv
      have hn' : algebraMap O E' n * (D.card : E') = 1 := by
        have := congrArg (algebraMap O E') hn
        simpa using this
      have hv' : g (ι (x ^ m)) * g v = 1 := by rw [← map_mul, hv, map_one]
      refine ⟨algebraMap O E n * ι a * v, ?_⟩
      have := h3.mul_right (algebraMap O E' n * g v)
      convert this using 1
      rw [map_mul, map_mul, AlgHom.commutes]
      linear_combination (-y) * hv' - y * (g (ι (x ^ m)) * g v) * hn'
    choose z hz using key
    obtain ⟨L, hL⟩ := exists_lim _ hE z fun m n hmn => sat _ _ (by
      have := dvd_sub ((pow_dvd_pow _ hmn).trans (hz n)) (hz m)
      convert this using 1
      rw [map_sub]; ring)
    refine ⟨L, ?_⟩
    rw [eq_comm, ← sub_eq_zero]
    refine eq_zero_of_dvd _ hE' _ fun k => ?_
    have := dvd_add (hz k) (map_dvd' g p k (hL k))
    convert this using 1
    rw [map_sub]; ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjSubMulNegMulOfNormOne
section
open Polynomial

namespace GlobalTheory

theorem conj_sub_mul_neg_mul_of_norm_one {x y : ℂ} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    (starRingEnd ℂ) (x - y) * (-(x * y)) = x - y := by
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx
  have hy0 : y ≠ 0 := by intro h; simp [h] at hy
  have cx : (starRingEnd ℂ) x = x⁻¹ := by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hx]; simp
  have cy : (starRingEnd ℂ) y = y⁻¹ := by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hy]; simp
  rw [map_sub, cx, cy]
  field_simp
  ring

theorem resultant_phase_unit_circle :
    ∀ (a b : ℕ) (α : Fin a → ℂ) (β : Fin b → ℂ), (∀ i, ‖α i‖ = 1) → (∀ j, ‖β j‖ = 1) →
      (∀ i j, α i ≠ β j) → ∀ k : ℤ, let R : ℂ := ∏ i, ∏ j, (α i - β j);
      (R / (‖R‖ : ℂ)) ^ (2 * k - 1) * (‖R‖ : ℂ) =
        (starRingEnd ℂ) R * ((-1 : ℂ) ^ (a * b) * (∏ i, α i) ^ b * (∏ j, β j) ^ a) ^ k := by
  intro a b α β hα hβ hne k R
  set D : ℂ := (-1 : ℂ) ^ (a * b) * (∏ i, α i) ^ b * (∏ j, β j) ^ a with hD
  have hR : R ≠ 0 := by
    simp only [R]
    rw [Finset.prod_ne_zero_iff]; intro i _
    rw [Finset.prod_ne_zero_iff]; intro j _
    exact sub_ne_zero.mpr (hne i j)
  have hDprod : D = ∏ i, ∏ j, (-(α i * β j)) := by
    simp only [hD, Finset.prod_neg, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, Finset.prod_pow, pow_mul]
    ring
  have hconj : (starRingEnd ℂ) R * D = R := by
    rw [hDprod]
    simp only [R, map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
    exact conj_sub_mul_neg_mul_of_norm_one (hα i) (hβ j)
  have hcR : (starRingEnd ℂ) R ≠ 0 := by simpa using hR
  have hr : ((‖R‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hR
  have hsq : ((‖R‖ : ℝ) : ℂ) ^ 2 = R * (starRingEnd ℂ) R := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  set u : ℂ := R / ((‖R‖ : ℝ) : ℂ) with hu
  have hu0 : u ≠ 0 := div_ne_zero hR hr
  have hu2 : u ^ 2 = D := by
    rw [hu, div_pow, hsq, pow_two, mul_div_mul_left _ _ hR, eq_comm]
    exact eq_div_of_mul_eq hcR (by rw [mul_comm]; exact hconj)
  have : u ^ (2 * k - 1) = D ^ k * u⁻¹ := by
    rw [zpow_sub₀ hu0, zpow_mul, zpow_one, zpow_two, ← pow_two, hu2, div_eq_mul_inv]
  rw [this, hu]
  field_simp
  linear_combination (D ^ k) * hsq
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoprimeAbsNormOfNatCastNotMem
section
namespace GlobalTheory.CoprimeAbsNorm

open NumberField IsDedekindDomain

theorem coprime_absNorm_of_natCast_notMem {E : Type} [Field E] [NumberField E]
    {P : HeightOneSpectrum (RingOfIntegers E)} {m : ℕ}
    (hm : (m : RingOfIntegers E) ∉ P.asIdeal) :
    Nat.Coprime m (Ideal.absNorm P.asIdeal) := by
  apply Nat.coprime_of_dvd
  intro p hp hpm hpN
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : P.asIdeal.IsPrime := P.isPrime
  haveI : Finite (RingOfIntegers E ⧸ P.asIdeal) :=
    Ideal.finiteQuotientOfFreeOfNeBot P.asIdeal P.ne_bot
  have hcard : p ∣ Nat.card (RingOfIntegers E ⧸ P.asIdeal) := by
    rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hpN
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' p hcard
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [addOrderOf_zero] at hx
    exact hp.one_lt.ne hx
  have hpx : (p : RingOfIntegers E ⧸ P.asIdeal) * x = 0 := by
    rw [← nsmul_eq_mul, ← hx]
    exact addOrderOf_nsmul_eq_zero x
  have hp0 : (p : RingOfIntegers E ⧸ P.asIdeal) = 0 :=
    (mul_eq_zero.mp hpx).resolve_right hx0
  have hpP : (p : RingOfIntegers E) ∈ P.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact hp0
  obtain ⟨k, rfl⟩ := hpm
  apply hm
  rw [Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ hpP

end GlobalTheory.CoprimeAbsNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetMemSpanAdjugate
section
open Matrix

namespace GlobalTheory.FitSquare

variable {R : Type} [CommRing R]

theorem exists_lift {ι N M : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup N] [Module R N]
    [AddCommGroup M] [Module R M] (h : (ι → R) →ₗ[R] M) (g : N →ₗ[R] M)
    (hh : ∀ y, ∃ z, g z = h y) : ∃ l : (ι → R) →ₗ[R] N, g ∘ₗ l = h := by
  choose z hz using hh
  refine ⟨(Pi.basisFun R ι).constr R (fun i => z (Pi.basisFun R ι i)), ?_⟩
  apply (Pi.basisFun R ι).ext
  intro i
  rw [LinearMap.comp_apply, Module.Basis.constr_basis, hz]

section blocks
variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

open Matrix in
variable {R : Type} [CommRing R] in
variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] in
private theorem det_updateRow_mem_span_adjugate_entries {α : Type} [Fintype α] [DecidableEq α]
    (Φ : Matrix α α R) (k : α) (w : α → R) :
    (Φ.updateRow k w).det ∈ Ideal.span (Set.range fun p : α × α => Φ.adjugate p.1 p.2) := by
  rw [← det_transpose, ← updateCol_transpose, ← cramer_apply, cramer_eq_adjugate_mulVec,
    ← adjugate_transpose]
  simp only [mulVec, dotProduct, transpose_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨(l, k), rfl⟩)

open Matrix in
variable {R : Type} [CommRing R] in
variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] in
private theorem det_mem_span_adjugate_entries {α : Type} [Fintype α] [DecidableEq α] [Nonempty α]
    (Φ : Matrix α α R) :
    Φ.det ∈ Ideal.span (Set.range fun p : α × α => Φ.adjugate p.1 p.2) := by
  obtain ⟨i⟩ := ‹Nonempty α›
  have h := det_updateRow_mem_span_adjugate_entries Φ i (Φ i)
  rwa [updateRow_eq_self] at h

open Matrix in
variable {R : Type} [CommRing R] in
variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] in
private theorem det_eq_mul_of_toBlocks₂₁_eq_zero {α β : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (M : Matrix (α ⊕ β) (α ⊕ β) R) (h : M.toBlocks₂₁ = 0) :
    M.det = M.toBlocks₁₁.det * M.toBlocks₂₂.det := by
  conv_lhs => rw [← fromBlocks_toBlocks M, h]
  exact det_fromBlocks_zero₂₁ _ _ _

open Matrix in
variable {R : Type} [CommRing R] in
variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] in
private theorem det_eq_mul_of_toBlocks₁₂_eq_zero {α β : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (M : Matrix (α ⊕ β) (α ⊕ β) R) (h : M.toBlocks₁₂ = 0) :
    M.det = M.toBlocks₁₁.det * M.toBlocks₂₂.det := by
  conv_lhs => rw [← fromBlocks_toBlocks M, h]
  exact det_fromBlocks_zero₁₂ _ _ _

open Matrix in
variable {R : Type} [CommRing R] in
variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] in

theorem _root_.GlobalTheory.FitSquare.relations_mem {M : Type} [AddCommGroup M] [Module R M]
    (π : (n → R) →ₗ[R] M) (hπ : Function.Surjective π) (Φ : Matrix n n R)
    (hΦ : ∀ y, π y = 0 → ∃ z, Φ *ᵥ z = y)
    (q : (m → R) →ₗ[R] M) (hq : Function.Surjective q) (T : Matrix m m R)
    (hT : ∀ y, q (T *ᵥ y) = 0) :
    T.det ∈ Ideal.span {Φ.det} ∧ (Nonempty n → ∀ i j, T.adjugate i j ∈
      Ideal.span (Set.range fun p : n × n => Φ.adjugate p.1 p.2)) := by
  choose a ha using fun j : m => hπ (q (Pi.single j 1))
  choose b hb using fun i : n => hq (π (Pi.single i 1))
  let A : Matrix n m R := Matrix.of fun i j => a j i
  let B : Matrix m n R := Matrix.of fun j i => b i j
  have hA : ∀ v, π (A *ᵥ v) = q v := by
    have h : π ∘ₗ A.mulVecLin = q := by
      ext j
      simp only [LinearMap.coe_comp, Function.comp_apply, mulVecLin_apply, LinearMap.single_apply,
        mulVec_single_one]
      rw [← ha j]
      rfl
    intro v
    exact LinearMap.congr_fun h v
  let U : Matrix (n ⊕ m) (n ⊕ m) R := fromBlocks 1 (-A) 0 1
  let D : Matrix (n ⊕ m) (n ⊕ m) R := fromBlocks Φ 0 0 1
  let N : Matrix (n ⊕ m) (n ⊕ m) R := fromBlocks 1 0 (-B) T
  have hker : ∀ u v, π u + q v = 0 → ∃ w, (U * D) *ᵥ w = Sum.elim u v := by
    intro u v h
    obtain ⟨z, hz⟩ := hΦ (u + A *ᵥ v) (by rw [map_add, hA, h])
    refine ⟨Sum.elim z v, ?_⟩
    rw [← mulVec_mulVec]
    simp [U, D, fromBlocks_mulVec, hz, neg_mulVec]
  have hcol : ∀ c, ∃ w, (U * D) *ᵥ w = fun r => N r c := by
    rintro (i | j)
    · obtain ⟨w, hw⟩ := hker (Pi.single i 1) (-b i) (by rw [map_neg, hb, add_neg_cancel])
      refine ⟨w, hw.trans ?_⟩
      ext (r | r) <;> simp [N, B, Pi.single_apply, one_apply]
    · obtain ⟨w, hw⟩ := hker 0 (fun r => T r j) (by
        have h := hT (Pi.single j 1)
        rw [mulVec_single_one] at h
        rw [map_zero, zero_add]
        exact h)
      refine ⟨w, hw.trans ?_⟩
      ext (r | r) <;> simp [N]
  choose w hw using hcol
  have hN : N = U * D * Matrix.of fun r c => w c r := by
    ext r c
    exact (congrFun (hw c) r).symm
  have hdetN : N.det = T.det := by simp [N, det_fromBlocks_zero₁₂]
  have hdetUD : (U * D).det = Φ.det := by simp [U, D, det_fromBlocks_zero₂₁, det_mul]
  refine ⟨?_, ?_⟩
  · rw [← hdetN, hN, det_mul, hdetUD]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  · intro hn p p'
    have hdetJ := det_mem_span_adjugate_entries Φ
    have hD : ∀ x y, D.adjugate x y ∈
        Ideal.span (Set.range fun p : n × n => Φ.adjugate p.1 p.2) := by
      intro x y
      rw [adjugate_apply]
      rcases y with k | k
      · rw [det_eq_mul_of_toBlocks₂₁_eq_zero]
        · have h : (D.updateRow (Sum.inl k) (Pi.single x 1)).toBlocks₁₁ =
              Φ.updateRow k (fun l => (Pi.single x 1 : n ⊕ m → R) (Sum.inl l)) := by
            ext s t
            by_cases hs : s = k <;> simp [D, toBlocks₁₁, updateRow_apply, hs]
          rw [h]
          exact Ideal.mul_mem_right _ _ (det_updateRow_mem_span_adjugate_entries _ _ _)
        · ext s t
          simp [D, toBlocks₂₁, updateRow_apply]
      · rw [det_eq_mul_of_toBlocks₁₂_eq_zero]
        · have h : (D.updateRow (Sum.inr k) (Pi.single x 1)).toBlocks₁₁ = Φ := by
            ext s t
            simp [D, toBlocks₁₁, updateRow_apply]
          rw [h]
          exact Ideal.mul_mem_right _ _ hdetJ
        · ext s t
          simp [D, toBlocks₁₂, updateRow_apply]
    have hadj : T.adjugate p p' = N.adjugate (Sum.inr p) (Sum.inr p') := by
      rw [adjugate_apply, adjugate_apply, det_eq_mul_of_toBlocks₁₂_eq_zero]
      · have h₁ : (N.updateRow (Sum.inr p') (Pi.single (Sum.inr p) 1)).toBlocks₁₁ = 1 := by
          ext s t
          simp [N, toBlocks₁₁, updateRow_apply]
        have h₂ : (N.updateRow (Sum.inr p') (Pi.single (Sum.inr p) 1)).toBlocks₂₂ =
            T.updateRow p' (Pi.single p 1) := by
          ext s t
          by_cases hs : s = p' <;> simp [N, toBlocks₂₂, updateRow_apply, hs, Pi.single_apply]
        rw [h₁, h₂, det_one, one_mul]
      · ext s t
        simp [N, toBlocks₁₂, updateRow_apply]
    rw [hadj, hN, adjugate_mul_distrib, adjugate_mul_distrib, mul_apply]
    refine Ideal.sum_mem _ fun x _ => Ideal.mul_mem_left _ _ ?_
    rw [mul_apply]
    exact Ideal.sum_mem _ fun y _ => Ideal.mul_mem_right _ _ (hD x y)

end blocks

open Matrix in
variable {R : Type} [CommRing R] in

theorem _root_.GlobalTheory.FitSquare.fitting_exact : ∀ (R : Type) [CommRing R] (M₁ M₂ M₃ : Type) [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃] (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃), Function.Exact f g → Function.Surjective g → ∀ (k : ℕ) (x : R) (v : Fin k → M₁), Submodule.span R (Set.range v) = ⊤ → (∀ m : M₁, x • m = 0) → ∀ (a b : ℕ) (Φ : Matrix (Fin a) (Fin a) R) (Ψ : Matrix (Fin b) (Fin b) R), Nonempty (M₂ ≃ₗ[R] ((Fin a → R) ⧸ LinearMap.range Φ.mulVecLin)) → Nonempty (M₃ ≃ₗ[R] ((Fin b → R) ⧸ LinearMap.range Ψ.mulVecLin)) → x ^ k * Ψ.det ∈ Ideal.span {Φ.det} ∧ (a = 0 ∨ ((∀ p q, x ^ k * Ψ.adjugate p q ∈ Ideal.span (Set.range fun p : Fin a × Fin a => Φ.adjugate p.1 p.2)) ∧ (b = 0 → x ^ k ∈ Ideal.span (Set.range fun p : Fin a × Fin a => Φ.adjugate p.1 p.2)))) := by
  intro R _ M₁ M₂ M₃ _ _ _ _ _ _ f g hfg hg k x v hv hx a b Φ Ψ ⟨e₂⟩ ⟨e₃⟩
  let π : (Fin a → R) →ₗ[R] M₂ := e₂.symm.toLinearMap ∘ₗ (LinearMap.range Φ.mulVecLin).mkQ
  have hπ : Function.Surjective π := e₂.symm.surjective.comp (Submodule.mkQ_surjective _)
  have hΦ : ∀ y, π y = 0 → ∃ z, Φ *ᵥ z = y := by
    intro y hy
    have hy' : (LinearMap.range Φ.mulVecLin).mkQ y = 0 := by
      simpa [π] using hy
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hy'
    obtain ⟨z, hz⟩ := hy'
    exact ⟨z, hz⟩
  let ρ : (Fin b → R) →ₗ[R] M₃ := e₃.symm.toLinearMap ∘ₗ (LinearMap.range Ψ.mulVecLin).mkQ
  have hρ : Function.Surjective ρ := e₃.symm.surjective.comp (Submodule.mkQ_surjective _)
  choose u hu using fun j : Fin b => hg (ρ (Pi.single j 1))
  let H : (Fin b → R) →ₗ[R] M₂ := Fintype.linearCombination R u
  have hgH : ∀ t, g (H t) = ρ t := by
    have h : g ∘ₗ H = ρ := by
      ext j
      simp [H, hu]
    exact fun t => LinearMap.congr_fun h t
  have hkerg : ∀ y, g y = 0 → ∃ c : Fin k → R, ∑ i, c i • f (v i) = y := by
    intro y hy
    obtain ⟨m₁, rfl⟩ := (hfg y).1 hy
    have hm : m₁ ∈ Submodule.span R (Set.range v) := hv ▸ Submodule.mem_top
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hm
    exact ⟨c, by simp [map_sum]⟩
  let q : (Fin k ⊕ Fin b → R) →ₗ[R] M₂ :=
    Fintype.linearCombination R (Sum.elim (fun i => f (v i)) u)
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨t, ht⟩ := hρ (g y)
    obtain ⟨c, hc⟩ := hkerg (y - H t) (by rw [map_sub, hgH, ht, sub_self])
    refine ⟨Sum.elim c t, ?_⟩
    rw [Fintype.linearCombination_apply, Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [hc]
    simp [H, Fintype.linearCombination_apply]
  have hcolΨ : ∀ j, ∃ c : Fin k → R, ∑ i, c i • f (v i) = H (fun r => Ψ r j) := by
    intro j
    apply hkerg
    rw [hgH]
    simp only [ρ, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      Submodule.mkQ_apply]
    rw [(Submodule.Quotient.mk_eq_zero _).2 (LinearMap.mem_range.2 ⟨Pi.single j 1, by
      rw [mulVecLin_apply, mulVec_single_one]; rfl⟩), map_zero]
  choose C hC using hcolΨ
  let T : Matrix (Fin k ⊕ Fin b) (Fin k ⊕ Fin b) R :=
    fromBlocks (x • 1) (-Matrix.of fun i j => C j i) 0 Ψ
  have hT : ∀ y, q (T *ᵥ y) = 0 := by
    have h0 : q ∘ₗ T.mulVecLin = 0 := by
      ext c
      simp only [LinearMap.coe_comp, Function.comp_apply, mulVecLin_apply,
        LinearMap.single_apply, mulVec_single_one, LinearMap.zero_apply]
      rw [Fintype.linearCombination_apply, Fintype.sum_sum_type]
      rcases c with i | j
      · simp [T, col, one_apply]
        rw [← map_smul, hx, map_zero]
      · have hCj := hC j
        simp only [H, Fintype.linearCombination_apply] at hCj
        simp [T, col, neg_smul, Finset.sum_neg_distrib, hCj]
    exact fun y => LinearMap.congr_fun h0 y
  obtain ⟨h₁, h₂⟩ := _root_.GlobalTheory.FitSquare.relations_mem π hπ Φ hΦ q hq T hT
  have hdetT : T.det = x ^ k * Ψ.det := by simp [T, det_fromBlocks_zero₂₁, det_smul]
  rw [hdetT] at h₁
  refine ⟨h₁, ?_⟩
  rcases Nat.eq_zero_or_pos a with ha | ha
  · exact Or.inl ha
  · right
    haveI : Nonempty (Fin a) := ⟨⟨0, ha⟩⟩
    refine ⟨fun p p' => ?_, fun hb0 => ?_⟩
    · have hadj : T.adjugate (Sum.inr p) (Sum.inr p') = x ^ k * Ψ.adjugate p p' := by
        rw [adjugate_apply, adjugate_apply, det_eq_mul_of_toBlocks₂₁_eq_zero]
        · have h₁₁ : (T.updateRow (Sum.inr p') (Pi.single (Sum.inr p) 1)).toBlocks₁₁ =
              x • 1 := by
            ext s t
            simp [T, toBlocks₁₁, updateRow_apply]
          have h₂₂ : (T.updateRow (Sum.inr p') (Pi.single (Sum.inr p) 1)).toBlocks₂₂ =
              Ψ.updateRow p' (Pi.single p 1) := by
            ext s t
            by_cases hs : s = p' <;> simp [T, toBlocks₂₂, updateRow_apply, hs, Pi.single_apply]
          rw [h₁₁, h₂₂, det_smul, det_one, mul_one, Fintype.card_fin]
        · ext s t
          simp [T, toBlocks₂₁, updateRow_apply]
      rw [← hadj]
      exact h₂ ‹_› _ _
    · subst hb0
      have h₃ : x ^ k ∈ Ideal.span {Φ.det} := by simpa [det_isEmpty] using h₁
      exact (Ideal.span_singleton_le_iff_mem _).2 (det_mem_span_adjugate_entries Φ) h₃

end GlobalTheory.FitSquare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DisjointFinsetSupOfSupIndepSup
section
namespace GlobalTheory

theorem disjoint_finset_sup_of_supIndep_sup :
    ∀ (R V ι : Type) [Ring R] [AddCommGroup V] [Module R V] (F : Finset ι) (G B : ι → Submodule R V),
      F.SupIndep (fun i => G i ⊔ B i) → (∀ i ∈ F, Disjoint (G i) (B i)) →
        Disjoint (F.sup G) (F.sup B) := by
  intro R V ι _ _ _ F G B hind hdis
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hs : s.SupIndep (fun i => G i ⊔ B i) := hind.subset (Finset.subset_insert _ _)
    have ih' := ih hs (fun i hi => hdis i (Finset.mem_insert_of_mem hi))
    have hA : Disjoint (G a ⊔ B a) (s.sup fun i => G i ⊔ B i) :=
      hind (Finset.subset_insert a s) (Finset.mem_insert_self a s) ha
    have hGs : s.sup G ≤ s.sup (fun i => G i ⊔ B i) := Finset.sup_mono_fun (fun i _ => le_sup_left)
    have hBs : s.sup B ≤ s.sup (fun i => G i ⊔ B i) := Finset.sup_mono_fun (fun i _ => le_sup_right)
    rw [Finset.sup_insert, Finset.sup_insert, Submodule.disjoint_def]
    intro x hxG hxB
    obtain ⟨g, hg, g', hg', rfl⟩ := Submodule.mem_sup.mp hxG
    obtain ⟨b, hb, b', hb', hbb⟩ := Submodule.mem_sup.mp hxB
    have h1 : g - b ∈ G a ⊔ B a := Submodule.sub_mem _ (Submodule.mem_sup_left hg) (Submodule.mem_sup_right hb)
    have h2 : g - b ∈ s.sup (fun i => G i ⊔ B i) := by
      have : g - b = b' - g' := by
        rw [sub_eq_sub_iff_add_eq_add, add_comm b' b, hbb]
      rw [this]
      exact Submodule.sub_mem _ (hBs hb') (hGs hg')
    have h3 : g - b = 0 := (Submodule.disjoint_def.mp hA) _ h1 h2
    have hgb : g = b := sub_eq_zero.mp h3
    have hg0 : g = 0 := (Submodule.disjoint_def.mp (hdis a (Finset.mem_insert_self a s))) g hg (hgb ▸ hb)
    have hg'b' : g' = b' := by
      subst hgb
      exact add_left_cancel hbb.symm
    have hg'0 : g' = 0 := (Submodule.disjoint_def.mp ih') g' hg' (hg'b' ▸ hb')
    rw [hg0, hg'0, add_zero]

end GlobalTheory
end

