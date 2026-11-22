import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlatMapColonIdeal
section
open IsLocalRing

namespace GlobalTheory

private lemma mem_colon_span_range_iff {B : Type*} [CommRing B] {P : Ideal B} {ι : Type*}
    (g : ι → B) (r : B) :
    r ∈ P.colon (Ideal.span (Set.range g) : Set B) ↔ ∀ i, r * g i ∈ P := by
  rw [Submodule.mem_colon', SetLike.coe_subset_coe]
  change Submodule.span B (Set.range g) ≤ _ ↔ _
  rw [Submodule.span_le, Set.range_subset_iff]
  simp [smul_eq_mul]

theorem _root_.GlobalTheory.ideal_map_colon_eq_of_flat : ∀ {A R : Type} [CommRing A] [IsNoetherianRing A] [CommRing R]
    (φ : A →+* R), φ.Flat → ∀ I J : Ideal A, (I.colon J).map φ = (I.map φ).colon (J.map φ) := by
  intro A R _ _ _ φ hφ I J
  obtain ⟨n, a, hJ⟩ := Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian J)
  obtain ⟨m, b, hI⟩ := Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian I)
  replace hJ : Ideal.span (Set.range a) = J := hJ
  replace hI : Ideal.span (Set.range b) = I := hI
  subst hJ hI
  rw [Ideal.map_span φ (Set.range a), ← Set.range_comp]
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, mem_colon_span_range_iff]
    rw [mem_colon_span_range_iff] at hr
    intro i
    simpa [map_mul] using Ideal.mem_map_of_mem φ (hr i)
  · intro s hs
    rw [mem_colon_span_range_iff] at hs
    have hmapI : (Ideal.span (Set.range b)).map φ = Ideal.span (Set.range (φ ∘ b)) := by
      rw [Ideal.map_span, ← Set.range_comp]
    choose c hc using fun i => Ideal.mem_span_range_iff_exists_fun.mp (hmapI ▸ hs i)
    letI := φ.toAlgebra
    haveI : Module.Flat A R := hφ
    let f : (Fin n → A) →ₗ[A] A × (Fin n × Fin m → A) :=
      LinearMap.prod (Fintype.linearCombination A a)
        (LinearMap.pi fun p => -(b p.2) • LinearMap.proj p.1)
    let x : A × (Fin n × Fin m → A) →ₗ[A] R :=
      LinearMap.coprod (LinearMap.toSpanSingleton A R s)
        (Fintype.linearCombination A fun p => c p.1 p.2)
    have hxf : x ∘ₗ f = 0 := by
      refine LinearMap.ext fun v => ?_
      simp [f, x, Algebra.smul_def, Fintype.sum_prod_type, Fintype.linearCombination_apply,
        LinearMap.pi_apply, map_sum, Finset.sum_mul]
      rw [← sub_eq_add_neg, sub_eq_zero]
      refine Finset.sum_congr rfl fun i _ => ?_
      have e : ∑ j, algebraMap A R (b j) * algebraMap A R (v i) * c i j
          = algebraMap A R (v i) * ∑ j, c i j * (φ ∘ b) j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [RingHom.algebraMap_toAlgebra, Function.comp_apply]
        ring
      rw [e, hc i]
      simp only [RingHom.algebraMap_toAlgebra, Function.comp_apply]
      ring
    obtain ⟨k, g, y, hxy, hgf⟩ := Module.Flat.exists_factorization_of_comp_eq_zero_of_free hxf
    have hdec : ∀ w : A × (Fin n × Fin m → A), g w = w.1 • g (1, 0) +
        ∑ p, w.2 p • g (0, fun q => if p = q then 1 else 0) := by
      intro w
      have hw : w = w.1 • ((1 : A), (0 : Fin n × Fin m → A)) + ((0 : A), w.2) := by
        ext <;> simp
      conv_lhs => rw [hw]
      rw [map_add, map_smul]
      congr 1
      exact LinearMap.pi_apply_eq_sum_univ (g ∘ₗ LinearMap.inr A A (Fin n × Fin m → A)) w.2
    have key : ∀ q, g (1, 0) q ∈
        (Ideal.span (Set.range b)).colon (Ideal.span (Set.range a) : Set A) := by
      intro q
      rw [mem_colon_span_range_iff]
      intro i
      set w := f (fun j => if i = j then 1 else 0) with hw
      have hw1 : w.1 = a i := by simp [hw, f, Fintype.linearCombination_apply]
      have hw2 : ∀ p, w.2 p ∈ Ideal.span (Set.range b) := by
        intro p
        simp only [hw, f, LinearMap.prod_apply, Pi.prod, LinearMap.pi_apply, LinearMap.smul_apply,
          LinearMap.proj_apply, smul_eq_mul]
        exact Ideal.mul_mem_right _ _ (neg_mem (Ideal.subset_span ⟨p.2, rfl⟩))
      have h0 := DFunLike.congr_fun (hdec w) q
      rw [show g w = 0 from LinearMap.congr_fun hgf _] at h0
      simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.coe_add, Pi.add_apply, Finsupp.coe_smul,
        Pi.smul_apply, smul_eq_mul, Finsupp.finset_sum_apply] at h0
      have h1 : g (1, 0) q * a i = -∑ p, w.2 p * g (0, fun q => if p = q then 1 else 0) q := by
        rw [← hw1]
        linear_combination -h0
      rw [h1]
      exact neg_mem (Ideal.sum_mem _ fun p _ => Ideal.mul_mem_right _ _ (hw2 p))
    have hs' : s = x (1, 0) := by simp [x]
    rw [hs', hxy, LinearMap.comp_apply, ← Finsupp.univ_sum_single (g (1, 0)), map_sum]
    refine Ideal.sum_mem _ fun q _ => ?_
    rw [← Finsupp.smul_single_one, map_smul, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem φ (key q))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaussianPairingMomentAlgebra
section
open Matrix
open scoped ComplexOrder

namespace GlobalTheory

theorem gaussian_pairing_moment_algebra : ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (S T : Matrix σ σ ℂ) (x y : σ → ℂ) (t f : ℂ) (p q : σ → ℂ) (m n : Matrix σ σ ℂ), Sᵀ = S → Tᵀ = T → IsUnit (1 - (t ^ 2) • (T * S)).det → p = t • (f • y + T *ᵥ q) → q = t • (f • x + S *ᵥ p) → m = (t * f) • (1 : Matrix σ σ ℂ) + t • vecMulVec y q + t • (T * n) → n = t • vecMulVec x q + t • (S * m) → let w : σ → ℂ := (1 - (t ^ 2) • (T * S))⁻¹ *ᵥ (y + t • T *ᵥ x); let u : σ → ℂ := x + t • S *ᵥ w; f * (x ⬝ᵥ y) + x ⬝ᵥ T *ᵥ q + y ⬝ᵥ S *ᵥ p + (S * m * Tᵀ).trace = f * (u ⬝ᵥ w + t * (T * S * (1 - (t ^ 2) • (T * S))⁻¹).trace) := by
  intro σ _ _ S T x y t f p q m n hS hT hA hp hq hm hn w u
  set A : Matrix σ σ ℂ := 1 - (t ^ 2) • (T * S) with hAdef
  have hKA : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hA
  have hAK : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hA
  have hAv : ∀ v : σ → ℂ, A *ᵥ v = v - (t ^ 2) • T *ᵥ (S *ᵥ v) := by
    intro v
    rw [hAdef, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.mulVec_mulVec]
  have hAp : A *ᵥ p = (t * f) • (y + t • T *ᵥ x) := by
    have h1 : p = t • (f • y + T *ᵥ (t • (f • x + S *ᵥ p))) := by rw [← hq]; exact hp
    rw [hAv]
    rw [Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul] at h1
    rw [sub_eq_iff_eq_add]
    refine h1.trans ?_
    module
  have hpw : p = (t * f) • w := by
    have : p = A⁻¹ *ᵥ (A *ᵥ p) := by rw [Matrix.mulVec_mulVec, hKA, Matrix.one_mulVec]
    rw [this, hAp, Matrix.mulVec_smul]
  have hqu : q = (t * f) • u := by
    rw [hq, hpw, Matrix.mulVec_smul]
    simp only [u]
    module
  have hAw : A *ᵥ w = y + t • T *ᵥ x := by
    simp only [w]
    rw [Matrix.mulVec_mulVec, hAK, Matrix.one_mulVec]
  have hw : w = y + t • T *ᵥ u := by
    rw [hAv, sub_eq_iff_eq_add] at hAw
    refine hAw.trans ?_
    simp only [u]
    rw [Matrix.mulVec_add, Matrix.mulVec_smul]
    module
  have hAm : A * m = (t * f) • (1 : Matrix σ σ ℂ) + t • vecMulVec (y + t • T *ᵥ x) q := by
    have h1 : m = (t * f) • (1 : Matrix σ σ ℂ) + t • vecMulVec y q
        + t • (T * (t • vecMulVec x q + t • (S * m))) := by rw [← hn]; exact hm
    rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_vecMulVec,
      ← Matrix.mul_assoc] at h1
    rw [hAdef, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, sub_eq_iff_eq_add,
      Matrix.add_vecMulVec, Matrix.smul_vecMulVec]
    refine h1.trans ?_
    module
  have hmK : m = (t * f) • A⁻¹ + t • vecMulVec w q := by
    have : m = A⁻¹ * (A * m) := by rw [← Matrix.mul_assoc, hKA, Matrix.one_mul]
    rw [this, hAm, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one,
      Matrix.mul_vecMulVec]
  have htr : (S * m * Tᵀ).trace
      = (t * f) * (T * S * A⁻¹).trace + t * ((S *ᵥ w) ⬝ᵥ (T *ᵥ q)) := by
    rw [hmK, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
      Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.trace_vecMulVec, Matrix.vecMul_transpose,
      hT, Matrix.trace_mul_comm (S * A⁻¹) T, Matrix.mul_assoc T S, smul_eq_mul, smul_eq_mul]
  have huw : u ⬝ᵥ w = x ⬝ᵥ y + t * (x ⬝ᵥ T *ᵥ u) + t * (y ⬝ᵥ S *ᵥ w)
      + t ^ 2 * ((S *ᵥ w) ⬝ᵥ (T *ᵥ u)) := by
    have h1 : u ⬝ᵥ w = (x + t • S *ᵥ w) ⬝ᵥ (y + t • T *ᵥ u) := by rw [← hw]
    rw [h1]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [dotProduct_comm (S *ᵥ w) y]
    ring
  rw [htr, huw, hqu, hpw]
  simp only [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaussianPhaseCriticalValueBlocksGeneral
section
open Matrix
open scoped ComplexOrder

namespace GlobalTheory

private lemma dot_transpose_mulVec' {m n : Type} [Fintype m] [Fintype n]
    (X : Matrix m n ℂ) (u : n → ℂ) (v : m → ℂ) : u ⬝ᵥ Xᵀ *ᵥ v = v ⬝ᵥ X *ᵥ u := by
  rw [mulVec_transpose, dotProduct_comm, ← dotProduct_mulVec]

theorem gaussian_phase_critical_value_blocks_general {m n : Type} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (C : Matrix n m ℂ) (B : Matrix m n ℂ)
    (a c : m → ℂ) (b d : n → ℂ) (hN : IsUnit (1 - C * B).det) :
    let S : Matrix (m ⊕ n) (m ⊕ n) ℂ := fromBlocks 0 Cᵀ C 0
    let T : Matrix (m ⊕ n) (m ⊕ n) ℂ := fromBlocks 0 B Bᵀ 0
    let w : m ⊕ n → ℂ := (1 - T * S)⁻¹ *ᵥ (Sum.elim c d + T *ᵥ Sum.elim a b)
    let u : m ⊕ n → ℂ := Sum.elim a b + S *ᵥ w
    1 / 2 * (Sum.elim a b ⬝ᵥ w + Sum.elim c d ⬝ᵥ u)
      = a ⬝ᵥ (1 - B * C)⁻¹ *ᵥ c + d ⬝ᵥ (1 - C * B)⁻¹ *ᵥ b
        + a ⬝ᵥ ((1 - B * C)⁻¹ * B) *ᵥ b + d ⬝ᵥ ((1 - C * B)⁻¹ * C) *ᵥ c := by
  intro S T w u
  have hM : IsUnit (1 - B * C).det := by rwa [det_one_sub_mul_comm]
  set M := (1 - B * C)⁻¹ with hMdef
  set N := (1 - C * B)⁻¹ with hNdef
  have hM1 : M * (1 - B * C) = 1 := nonsing_inv_mul _ hM
  have hM2 : (1 - B * C) * M = 1 := mul_nonsing_inv _ hM
  have hN1 : N * (1 - C * B) = 1 := nonsing_inv_mul _ hN
  have hN2 : (1 - C * B) * N = 1 := mul_nonsing_inv _ hN
  have hMB : B * N = M * B := by
    have h : B * (1 - C * B) = (1 - B * C) * B := by
      simp [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    calc B * N = M * ((1 - B * C) * B) * N := by
          rw [← Matrix.mul_assoc, hM1, Matrix.one_mul]
      _ = M * B := by
          rw [← h, Matrix.mul_assoc, Matrix.mul_assoc, hN2, Matrix.mul_one]
  have hCM : C * M = N * C := by
    have h : C * (1 - B * C) = (1 - C * B) * C := by
      simp [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    calc C * M = N * ((1 - C * B) * C) * M := by
          rw [← Matrix.mul_assoc, hN1, Matrix.one_mul]
      _ = N * C := by
          rw [← h, Matrix.mul_assoc, Matrix.mul_assoc, hM2, Matrix.mul_one]
  have hMBC : B * (N * C) = M - 1 := by
    rw [← Matrix.mul_assoc, hMB, ← hM1, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]
    abel
  have hNCB : N * C * B = N - 1 := by
    rw [← hN1, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]
    abel
  have hinv : (1 - T * S)⁻¹ = fromBlocks M 0 0 Nᵀ := by
    apply inv_eq_left_inv
    have h1 : (1 - T * S) = fromBlocks (1 - B * C) 0 0 (1 - C * B)ᵀ := by
      simp only [T, S, fromBlocks_multiply, ← fromBlocks_one]
      ext (i | i) (j | j) <;> simp [transpose_mul, one_apply, eq_comm]
    rw [h1, fromBlocks_multiply, ← transpose_mul, hM1, hN2]
    simp
  have hw : w = Sum.elim (M *ᵥ (c + B *ᵥ b)) (Nᵀ *ᵥ (d + Bᵀ *ᵥ a)) := by
    have h : Sum.elim c d + T *ᵥ Sum.elim a b = Sum.elim (c + B *ᵥ b) (d + Bᵀ *ᵥ a) := by
      simp only [T, fromBlocks_mulVec]
      ext (i | i) <;> simp
    simp only [w]
    rw [hinv, h, fromBlocks_mulVec]
    simp
  have hu : u = Sum.elim (a + (N * C)ᵀ *ᵥ (d + Bᵀ *ᵥ a)) (b + (N * C) *ᵥ (c + B *ᵥ b)) := by
    simp only [u, S]
    rw [hw, fromBlocks_mulVec]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr,
      mulVec_mulVec, ← transpose_mul, hCM]
    ext (i | i) <;> simp
  rw [hu, hw, sumElim_dotProduct_sumElim, sumElim_dotProduct_sumElim]
  simp only [dotProduct_add, mulVec_add, mulVec_mulVec, ← transpose_mul, dot_transpose_mulVec',
    hMB, hMBC, hNCB, sub_mulVec, one_mulVec, dotProduct_sub]
  rw [dotProduct_comm c a]
  ring

theorem gaussian_phase_critical_value_blocks :
    ∀ (P Q : ℕ) (A B : Matrix (Fin P) (Fin Q) ℂ) (a c : Fin P → ℂ) (b d : Fin Q → ℂ), IsUnit (1 - Aᴴ * B).det → let S : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ := fromBlocks 0 Aᴴᵀ Aᴴ 0; let T : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ := fromBlocks 0 B Bᵀ 0; let w : Fin P ⊕ Fin Q → ℂ := (1 - T * S)⁻¹ *ᵥ (Sum.elim c d + T *ᵥ Sum.elim a b); let u : Fin P ⊕ Fin Q → ℂ := Sum.elim a b + S *ᵥ w; 1 / 2 * (Sum.elim a b ⬝ᵥ w + Sum.elim c d ⬝ᵥ u) = a ⬝ᵥ (1 - B * Aᴴ)⁻¹ *ᵥ c + d ⬝ᵥ (1 - Aᴴ * B)⁻¹ *ᵥ b + a ⬝ᵥ ((1 - B * Aᴴ)⁻¹ * B) *ᵥ b + d ⬝ᵥ ((1 - Aᴴ * B)⁻¹ * Aᴴ) *ᵥ c :=
  fun _ _ A B a c b d h => gaussian_phase_critical_value_blocks_general Aᴴ B a c b d h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GermSectionsHalfPlaneGlobalSection
section
open Filter Topology

namespace GlobalTheory

theorem germSections_glue {Y ι : Type} (G : ℂ → (ℂ → Y) → Prop)
    (h1 : ∀ w s s', s =ᶠ[𝓝 w] s' → G w s → G w s') (i₀ : ι)
    (U : ι → Set ℂ) (s : ι → ℂ → Y) (hU : ∀ i, IsOpen (U i))
    (hs : ∀ i, ∀ z ∈ U i, G z (s i))
    (hag : ∀ i j, Set.EqOn (s i) (s j) (U i ∩ U j)) :
    ∃ t : ℂ → Y, ∀ i, ∀ z ∈ U i, G z t := by
  classical
  refine ⟨fun z => if h : ∃ i, z ∈ U i then s h.choose z else s i₀ z, fun i z hz => ?_⟩
  refine h1 z (s i) _ ?_ (hs i z hz)
  filter_upwards [(hU i).mem_nhds hz] with w hw
  have h : ∃ i, w ∈ U i := ⟨i, hw⟩
  rw [dif_pos h]
  exact hag i _ ⟨hw, h.choose_spec⟩

theorem germSections_halfPlane_global (Y : Type) (G : ℂ → (ℂ → Y) → Prop) (T : ℝ)
    (h1 : ∀ w s s', s =ᶠ[𝓝 w] s' → G w s → G w s')
    (h2 : ∀ w : ℂ, T < w.im → ∃ s, ∀ᶠ z in 𝓝 w, G z s)
    (h3 : ∀ (U : Set ℂ) (s s' : ℂ → Y), IsOpen U → Convex ℝ U → (∀ z ∈ U, T < z.im) →
      (∀ z ∈ U, G z s) → (∀ z ∈ U, G z s') → ∀ w ∈ U, s w = s' w → Set.EqOn s s' U)
    (h4 : ∀ (U : Set ℂ) (s s' : ℂ → Y), IsOpen U → Convex ℝ U → (∀ z ∈ U, T < z.im) →
      (∀ z ∈ U, G z s) → ∀ w ∈ U, G w s' → ∃ s'' : ℂ → Y, (∀ z ∈ U, G z s'') ∧ s'' w = s' w) :
    ∃ s : ℂ → Y, ∀ w : ℂ, T < w.im → G w s := by
  have hH : IsOpen {z : ℂ | T < z.im} := isOpen_lt continuous_const Complex.continuous_im

  have glue : ∀ {ι : Type} (_ : ι) (U : ι → Set ℂ) (p : ℂ), (∀ i, IsOpen (U i)) →
      (∀ i, Convex ℝ (U i)) → (∀ i, ∀ z ∈ U i, T < z.im) → (∀ i, p ∈ U i) →
      (∀ i, ∃ s, ∀ z ∈ U i, G z s) → ∃ t : ℂ → Y, ∀ i, ∀ z ∈ U i, G z t := by
    intro ι i₀ U p ho hc hT hp hs
    obtain ⟨s₀, hs₀⟩ := hs i₀
    have : ∀ i, ∃ s : ℂ → Y, (∀ z ∈ U i, G z s) ∧ s p = s₀ p := fun i => by
      obtain ⟨s, hs⟩ := hs i
      exact h4 (U i) s s₀ (ho i) (hc i) (hT i) hs p (hp i) (hs₀ p (hp i₀))
    choose s hs hsp using this
    refine germSections_glue G h1 i₀ U s ho hs fun i j => ?_
    exact h3 (U i ∩ U j) (s i) (s j) ((ho i).inter (ho j)) ((hc i).inter (hc j))
      (fun z hz => hT i z hz.1) (fun z hz => hs i z hz.1) (fun z hz => hs j z hz.2) p
      ⟨hp i, hp j⟩ ((hsp i).trans (hsp j).symm)
  have loc : ∀ w : ℂ, T < w.im → ∃ D : Set ℂ, IsOpen D ∧ Convex ℝ D ∧ (∀ z ∈ D, T < z.im) ∧
      w ∈ D ∧ ∃ s, ∀ z ∈ D, G z s := by
    intro w hw
    obtain ⟨s, hs⟩ := h2 w hw
    obtain ⟨ε, hε, hb⟩ := Metric.eventually_nhds_iff_ball.1 (hs.and (hH.mem_nhds hw))
    exact ⟨Metric.ball w ε, Metric.isOpen_ball, convex_ball w ε, fun z hz => (hb z hz).2,
      Metric.mem_ball_self hε, s, fun z hz => (hb z hz).1⟩
  set p : ℂ := ((T + 1 : ℝ) : ℂ) * Complex.I with hpdef
  have hp : T < p.im := by simp [hpdef]
  let good : ℂ → Prop := fun w => ∃ U : Set ℂ, IsOpen U ∧ Convex ℝ U ∧ (∀ z ∈ U, T < z.im) ∧
      p ∈ U ∧ w ∈ U ∧ ∃ s, ∀ z ∈ U, G z s
  have hgood : ∀ w : ℂ, T < w.im → good w := by
    intro w hw
    let γ : ℝ →ᵃ[ℝ] ℂ := AffineMap.lineMap p w
    have hγc : Continuous γ := AffineMap.lineMap_continuous
    have hγ0 : γ 0 = p := AffineMap.lineMap_apply_zero p w
    have hγ1 : γ 1 = w := AffineMap.lineMap_apply_one p w
    have hγH : ∀ t ∈ Set.Icc (0 : ℝ) 1, T < (γ t).im := by
      intro t ht
      have hc := ((convex_halfSpace_im_gt T).affine_preimage γ).ordConnected
      exact hc.out (x := 0) (y := 1) (by simpa [hγ0] using hp) (by simpa [hγ1] using hw) ht
    have step : ∀ D : Set ℂ, IsOpen D → Convex ℝ D → (∀ z ∈ D, T < z.im) →
        (∃ s, ∀ z ∈ D, G z s) → ∀ a b : ℝ, 0 ≤ b → γ a ∈ D → γ b ∈ D →
        good (γ a) → good (γ b) := by
      rintro D hDo hDc hDT hDs a b hb ha hbD ⟨U, hUo, hUc, hUT, hpU, haU, hUs⟩
      obtain ⟨t, ht⟩ := glue true (fun i : Bool => cond i U D) (γ a)
        (by rintro (_ | _) <;> assumption) (by rintro (_ | _) <;> assumption)
        (by rintro (_ | _) <;> assumption) (by rintro (_ | _) <;> assumption)
        (by rintro (_ | _) <;> assumption)
      have hK : IsCompact (γ '' Set.Icc 0 b) := isCompact_Icc.image hγc
      have hKc : Convex ℝ (γ '' Set.Icc 0 b) := (convex_Icc 0 b).affine_image γ
      have hsub : γ '' Set.Icc 0 b ⊆ U ∪ D := by
        rintro _ ⟨r, hr, rfl⟩
        rcases le_total r a with h | h
        · left
          exact (hUc.affine_preimage γ).ordConnected.out (x := 0) (y := a)
            (by simpa [hγ0] using hpU) haU ⟨hr.1, h⟩
        · right
          exact (hDc.affine_preimage γ).ordConnected.out (x := a) (y := b) ha hbD ⟨h, hr.2⟩
      obtain ⟨δ, hδ, hth⟩ := hK.exists_thickening_subset_open (hUo.union hDo) hsub
      refine ⟨Metric.thickening δ (γ '' Set.Icc 0 b), Metric.isOpen_thickening,
        hKc.thickening δ, fun z hz => ?_, ?_, ?_, t, fun z hz => ?_⟩
      · rcases hth hz with h | h
        · exact hUT z h
        · exact hDT z h
      · exact Metric.self_subset_thickening hδ _ ⟨0, ⟨le_rfl, hb⟩, hγ0⟩
      · exact Metric.self_subset_thickening hδ _ ⟨b, ⟨hb, le_rfl⟩, rfl⟩
      · rcases hth hz with h | h
        · exact ht true z h
        · exact ht false z h
    have key := (isPreconnected_Icc (a := (0 : ℝ)) (b := 1)).induction₂'
      (fun a b => good (γ a) → good (γ b)) (by
        intro x hx
        obtain ⟨D, hDo, hDc, hDT, hxD, hDs⟩ := loc (γ x) (hγH x hx)
        have : ∀ᶠ y in 𝓝 x, γ y ∈ D := hγc.continuousAt.eventually (hDo.mem_nhds hxD)
        filter_upwards [nhdsWithin_le_nhds this, self_mem_nhdsWithin] with y hy hyI
        exact ⟨step D hDo hDc hDT hDs x y hyI.1 hxD hy, step D hDo hDc hDT hDs y x hx.1 hy hxD⟩)
      (fun _ _ _ _ _ _ h h' hh => h' (h hh)) (x := 0) (y := 1) (by simp) (by simp)
    rw [hγ0, hγ1] at key
    apply key
    obtain ⟨D, hDo, hDc, hDT, hxD, hDs⟩ := loc p hp
    exact ⟨D, hDo, hDc, hDT, hxD, hxD, hDs⟩
  choose U hUo hUc hUT hpU hwU hUs using hgood
  obtain ⟨t, ht⟩ := glue (ι := {w : ℂ // T < w.im}) ⟨p, hp⟩ (fun w => U w.1 w.2) p
    (fun w => hUo w.1 w.2) (fun w => hUc w.1 w.2) (fun w => hUT w.1 w.2) (fun w => hpU w.1 w.2)
    (fun w => hUs w.1 w.2)
  exact ⟨t, fun w hw => ht ⟨w, hw⟩ w (hwU w hw)⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasFDerivAtSetIntegral
section
open MeasureTheory Metric Set
open scoped ContDiff

namespace GlobalTheory.SetIntegralSmoothness

theorem hasFDerivAt_setIntegral {X P E : Type} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] {K : Set X} (hK : IsCompact K)
    {a : X → E} (ha : Continuous a) {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Ψ : P × E → F) (hΨ : ContDiff ℝ ∞ Ψ) (p₀ : P) :
    HasFDerivAt (fun p : P => ∫ x in K, Ψ (p, a x) ∂μ)
      (∫ x in K, (fderiv ℝ Ψ (p₀, a x)).comp (ContinuousLinearMap.inl ℝ P E) ∂μ) p₀ := by
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hΨ1 : ContDiff ℝ 1 Ψ := hΨ.of_le (by exact_mod_cast le_top)
  have hdΨ : Continuous (fderiv ℝ Ψ) := hΨ1.continuous_fderiv one_ne_zero
  have hS : IsCompact (closedBall p₀ 1 ×ˢ (a '' K)) := (isCompact_closedBall p₀ 1).prod (hK.image ha)
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hdΨ.continuousOn
  have hcont : ∀ p : P, Continuous fun x : X => Ψ (p, a x) :=
    fun p => hΨ.continuous.comp (continuous_const.prodMk ha)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (μ := μ.restrict K) (x₀ := p₀)
    (F := fun p x => Ψ (p, a x)) (F' := fun p x => (fderiv ℝ Ψ (p, a x)).comp (ContinuousLinearMap.inl ℝ P E))
    (bound := fun _ => C * ‖ContinuousLinearMap.inl ℝ P E‖)
    (closedBall_mem_nhds p₀ one_pos) ?_ ?_ ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun p =>
      (hcont p).continuousOn.aestronglyMeasurable_of_isCompact hK hKm
  · exact (hcont p₀).continuousOn.integrableOn_compact hK
  · exact ((hdΨ.comp (continuous_const.prodMk ha)).clm_comp continuous_const).continuousOn.aestronglyMeasurable_of_isCompact hK hKm
  · refine (ae_restrict_iff' hKm).mpr (Filter.Eventually.of_forall fun x hx p hp => ?_)
    calc ‖(fderiv ℝ Ψ (p, a x)).comp (ContinuousLinearMap.inl ℝ P E)‖
        ≤ ‖fderiv ℝ Ψ (p, a x)‖ * ‖ContinuousLinearMap.inl ℝ P E‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ C * ‖ContinuousLinearMap.inl ℝ P E‖ :=
        mul_le_mul_of_nonneg_right (hC _ ⟨hp, mem_image_of_mem a hx⟩) (norm_nonneg _)
  · exact integrableOn_const hK.measure_ne_top
  · exact Filter.Eventually.of_forall fun x p _ =>
      ((hΨ1.differentiable one_ne_zero) (p, a x)).hasFDerivAt.comp p (hasFDerivAt_prodMk_left p (a x))

theorem contDiff_setIntegral {X P E : Type} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] {K : Set X} (hK : IsCompact K)
    {a : X → E} (ha : Continuous a) (m : ℕ) {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (Ψ : P × E → F) (hΨ : ContDiff ℝ ∞ Ψ) :
    ContDiff ℝ (m : WithTop ℕ∞) (fun p : P => ∫ x in K, Ψ (p, a x) ∂μ) := by
  induction m generalizing F with
  | zero =>
    rw [Nat.cast_zero, contDiff_zero]
    exact continuous_iff_continuousAt.mpr fun p₀ =>
      (hasFDerivAt_setIntegral μ hK ha Ψ hΨ p₀).continuousAt
  | succ m IH =>
    rw [show ((m + 1 : ℕ) : WithTop ℕ∞) = (m : WithTop ℕ∞) + 1 by norm_cast,
      contDiff_succ_iff_hasFDerivAt]
    refine ⟨fun p => ∫ x in K, (fderiv ℝ Ψ (p, a x)).comp (ContinuousLinearMap.inl ℝ P E) ∂μ, ?_,
      fun p₀ => hasFDerivAt_setIntegral μ hK ha Ψ hΨ p₀⟩
    have hΨ' : ContDiff ℝ ∞ fun q : P × E => (fderiv ℝ Ψ q).comp (ContinuousLinearMap.inl ℝ P E) :=
      (hΨ.fderiv_right (m := ∞) (by simp)).clm_comp contDiff_const
    exact IH (fun q : P × E => (fderiv ℝ Ψ q).comp (ContinuousLinearMap.inl ℝ P E)) hΨ'

end GlobalTheory.SetIntegralSmoothness
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeightComapFlatHeightOne
section
open IsLocalRing

namespace GlobalTheory

theorem height_comap_eq_one_of_flat :
    ∀ {A R : Type} [CommRing A] [IsDomain A] [CommRing R] (φ : A →+* R), φ.Flat →
      ∀ (Q : Ideal R) [Q.IsPrime], Q.height = 1 → Q.comap φ ≠ ⊥ → (Q.comap φ).height = 1 := by
  intro A R _ _ _ φ hφ Q _ hQ hne
  letI := φ.toAlgebra
  haveI : Module.Flat A R := hφ
  haveI : Algebra.HasGoingDown A R := Algebra.HasGoingDown.of_flat
  set p : Ideal A := Q.comap φ with hp
  haveI : p.IsPrime := Ideal.comap_isPrime φ Q
  haveI : Q.LiesOver p := ⟨rfl⟩
  apply le_antisymm
  · rw [show ((1 : ℕ∞)) = ((1 : ℕ) : ℕ∞) from rfl, Ideal.height_le_iff]
    intro q hq hqp
    by_contra hcon
    have hq0 : q ≠ ⊥ := by
      rintro rfl
      simp at hcon
    haveI := hq
    obtain ⟨P₁, hP₁Q, hP₁, hP₁o⟩ := Ideal.exists_ideal_lt_liesOver_of_lt (p := q) (q := p) Q hqp
    haveI := hP₁
    haveI : (⊥ : Ideal A).IsPrime := Ideal.bot_prime
    obtain ⟨P₀, hP₀P₁, hP₀, -⟩ := Ideal.exists_ideal_lt_liesOver_of_lt (p := ⊥) (q := q) P₁
      (bot_lt_iff_ne_bot.mpr hq0)
    haveI := hP₀
    have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hP₀P₁
    have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hP₁Q
    rw [hQ] at h2
    have h4 : (1 : ℕ∞) ≤ P₁.height := le_trans le_add_self h1
    have h3 : (1 : ℕ∞) + 1 ≤ 1 := le_trans (by gcongr) h2
    exact absurd h3 (by decide)
  · haveI : (⊥ : Ideal A).IsPrime := Ideal.bot_prime
    have := Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.mpr hne)
    simpa using this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ImportsAlt
section
namespace GlobalTheory.KeyLemmaTwo

lemma key {z : ℂ} (h : ∀ (n : ℕ), ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) (k : ℕ) :
    (3 / 2 : ℝ) ^ k * ‖z - 1‖ ≤ ‖z ^ (2 ^ k) - 1‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    set w := z ^ (2 ^ k) with hw
    have hw2 : z ^ (2 ^ (k + 1)) = w ^ 2 := by rw [hw, ← pow_mul, pow_succ]
    have hlt : ‖w - 1‖ < 1 / 2 := h _
    have hplus : (3 / 2 : ℝ) ≤ ‖w + 1‖ := by
      have e : w + 1 = (2 : ℂ) + (w - 1) := by ring
      have h2 : ‖(2 : ℂ)‖ = 2 := by simp
      have := norm_sub_norm_le (2 : ℂ) (-(w - 1))
      rw [e]
      have h3 : ‖(2 : ℂ) - -(w - 1)‖ = ‖(2 : ℂ) + (w - 1)‖ := by rw [sub_neg_eq_add]
      rw [norm_neg, h2, h3] at this
      linarith
    have fac : w ^ 2 - 1 = (w - 1) * (w + 1) := by ring
    rw [hw2, fac, norm_mul, pow_succ]
    have hn : 0 ≤ ‖w - 1‖ := norm_nonneg _
    calc (3 / 2 : ℝ) ^ k * (3 / 2) * ‖z - 1‖ = ((3 / 2 : ℝ) ^ k * ‖z - 1‖) * (3 / 2) := by ring
      _ ≤ ‖w - 1‖ * (3 / 2) := by gcongr
      _ ≤ ‖w - 1‖ * ‖w + 1‖ := by gcongr

theorem main : ∀ {z : ℂ}, (∀ (n : ℕ), ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) → z = (1 : ℂ) := by
  intro z h
  by_contra hne
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / 2 / ‖z - 1‖) (by norm_num : (1 : ℝ) < 3 / 2)
  have h1 := key h k
  have h2 := h (2 ^ k)
  rw [div_lt_iff₀ hpos] at hk
  linarith

end GlobalTheory.KeyLemmaTwo
end

