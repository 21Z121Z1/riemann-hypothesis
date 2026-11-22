import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0039
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0064
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0049

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwoDimRepQuadraticRelation
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

noncomputable section

namespace GlobalTheory.CayleyHamiltonId

theorem exists_decomp {E : Type} [Field E] {ι : Type} [Fintype ι] [DecidableEq ι] (i₀ : ι)
    {U : Type} [AddCommGroup U] [Module E U] [FiniteDimensional E U]
    (P : ι → ι → Module.End E U)
    (hP : ∀ i j k l, P i j * P k l = if j = k then P i l else 0)
    (h1 : ∑ i, P i i = 1) :
    ∃ (m : ℕ) (π : Fin m → U →ₗ[E] (ι → E)) (s : Fin m → (ι → E) →ₗ[E] U),
      (∀ i (M : Matrix ι ι E), π i ∘ₗ (∑ a, ∑ b, M a b • P a b) = Matrix.toLin' M ∘ₗ π i) ∧
      (∀ i (M : Matrix ι ι E), (∑ a, ∑ b, M a b • P a b) ∘ₗ s i = s i ∘ₗ Matrix.toLin' M) ∧
      (∀ i j, π i ∘ₗ s j = if i = j then LinearMap.id else 0) ∧
      ∑ i, s i ∘ₗ π i = LinearMap.id := by
  classical
  have hPa : ∀ i j k l u, P i j (P k l u) = if j = k then P i l u else 0 := by
    intro i j k l u
    have := LinearMap.congr_fun (hP i j k l) u
    rw [Module.End.mul_apply] at this
    rw [this]; split_ifs <;> rfl
  set W := LinearMap.range (P i₀ i₀)
  have hW : ∀ k u, P i₀ k u ∈ W := fun k u => ⟨P i₀ k u, by rw [hPa, if_pos rfl]⟩
  have hfix : ∀ w ∈ W, P i₀ i₀ w = w := by
    rintro _ ⟨u, rfl⟩; rw [hPa, if_pos rfl]
  let b := Module.finBasis E W
  let π : Fin (Module.finrank E W) → U →ₗ[E] (ι → E) :=
    fun i => LinearMap.pi fun k => (b.coord i).comp (LinearMap.codRestrict W (P i₀ k) (hW k))
  let s : Fin (Module.finrank E W) → (ι → E) →ₗ[E] U :=
    fun i => ∑ k, (LinearMap.proj k : (ι → E) →ₗ[E] E).smulRight (P k i₀ (b i))
  have hπ : ∀ i u k, π i u k = b.repr ⟨P i₀ k u, hW k u⟩ i := fun i u k => rfl
  have hs : ∀ i v, s i v = ∑ k, v k • P k i₀ (b i) := by
    intro i v; simp [s, LinearMap.sum_apply]
  have hrec : ∀ k u, ∑ i, b.repr ⟨P i₀ k u, hW k u⟩ i • (b i : U) = P i₀ k u := by
    intro k u
    have h' := congrArg Subtype.val (b.sum_repr ⟨P i₀ k u, hW k u⟩)
    rw [Submodule.coe_sum] at h'
    simpa only [Submodule.coe_smul] using h'
  refine ⟨Module.finrank E W, π, s, ?_, ?_, ?_, ?_⟩
  · intro i M
    ext u k
    simp only [LinearMap.comp_apply, Matrix.toLin'_apply, hπ]
    have e : (⟨P i₀ k ((∑ a, ∑ b', M a b' • P a b') u), hW k _⟩ : W)
        = ∑ b', M k b' • (⟨P i₀ b' u, hW b' u⟩ : W) := by
      apply Subtype.ext
      simp [LinearMap.sum_apply, map_sum, map_smul, hPa]
    rw [e, map_sum, Finsupp.finset_sum_apply]
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, hπ]
  · intro i M
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.comp_apply, Matrix.toLin'_apply, hs]
    simp [LinearMap.sum_apply, map_sum, map_smul, hPa, Matrix.mulVec, dotProduct, Finset.sum_smul,
      mul_smul]
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => by rw [mul_comm]
  · intro i j
    refine LinearMap.ext fun v => funext fun k => ?_
    simp only [LinearMap.comp_apply, hπ, hs]
    have e : (⟨P i₀ k (∑ l, v l • P l i₀ (b j)), hW k _⟩ : W) = v k • b j := by
      apply Subtype.ext
      simp [map_sum, map_smul, hPa, hfix _ (b j).2]
    rw [e]
    split_ifs with h
    · subst h; simp
    · simp [Finsupp.single_apply, Ne.symm h]
  · ext u
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, hs, hπ, LinearMap.id_apply]
    rw [Finset.sum_comm]
    have hk : ∀ k, ∑ x, b.repr ⟨P i₀ k u, hW k u⟩ x • P k i₀ (b x) = P k k u := by
      intro k
      have := congrArg (P k i₀) (hrec k u)
      rw [map_sum] at this
      simp only [map_smul] at this
      rw [this, hPa, if_pos rfl]
    simp only [hk]
    rw [← LinearMap.sum_apply, h1, Module.End.one_apply]

theorem isotypic_of_quadratic_relation : ∀ {E : Type} [Field E] [IsAlgClosed E], (2 : E) ≠ 0 → ∀ {G : Type} [Group G] (ρ : G →* GL (Fin 2) E), (∀ W : Submodule E (Fin 2 → E), (∀ g w, w ∈ W → (ρ g : Matrix (Fin 2) (Fin 2) E) *ᵥ w ∈ W) → W = ⊥ ∨ W = ⊤) → ∀ {U : Type} [AddCommGroup U] [Module E U] [FiniteDimensional E U] (σ : G →* Module.End E U), (∀ g, σ g * σ g - Matrix.trace (ρ g : Matrix (Fin 2) (Fin 2) E) • σ g + Matrix.det (ρ g : Matrix (Fin 2) (Fin 2) E) • (1 : Module.End E U) = 0) → ∃ (m : ℕ) (π : Fin m → U →ₗ[E] (Fin 2 → E)) (s : Fin m → (Fin 2 → E) →ₗ[E] U), (∀ i g, π i ∘ₗ σ g = Matrix.toLin' (ρ g : Matrix (Fin 2) (Fin 2) E) ∘ₗ π i) ∧ (∀ i g, σ g ∘ₗ s i = s i ∘ₗ Matrix.toLin' (ρ g : Matrix (Fin 2) (Fin 2) E)) ∧ (∀ i j, π i ∘ₗ s j = if i = j then LinearMap.id else 0) ∧ ∑ i, s i ∘ₗ π i = LinearMap.id := by
  intro E _ _ h2 G _ ρ hirr U _ _ _ σ hrel
  classical
  let R : G →* Matrix (Fin 2) (Fin 2) E := (Units.coeHom _).comp ρ
  have hRg : ∀ g, R g = (ρ g : Matrix (Fin 2) (Fin 2) E) := fun g => rfl
  have hspan := GlobalTheory.BurnsideMonoid.span_matrix_eq_top_of_isAlgClosed R (fun W hW => hirr W hW)
  let Φ : MonoidAlgebra E G →ₐ[E] Module.End E U := MonoidAlgebra.lift E (Module.End E U) G σ
  let Ψ : MonoidAlgebra E G →ₐ[E] Matrix (Fin 2) (Fin 2) E :=
    MonoidAlgebra.lift E (Matrix (Fin 2) (Fin 2) E) G R
  have hΦ : ∀ g c, Φ (MonoidAlgebra.single g c) = c • σ g := fun g c => MonoidAlgebra.lift_single _ _ _
  have hΨ : ∀ g c, Ψ (MonoidAlgebra.single g c) = c • R g := fun g c => MonoidAlgebra.lift_single _ _ _
  have hsurj : ∀ M, ∃ y, Ψ y = M := by
    intro M
    have hle : Submodule.span E (Set.range R) ≤ LinearMap.range Ψ.toLinearMap := by
      rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      exact ⟨MonoidAlgebra.single g 1, by simp [hΨ]⟩
    obtain ⟨y, hy⟩ := hle (hspan ▸ Submodule.mem_top : M ∈ Submodule.span E (Set.range R))
    exact ⟨y, hy⟩

  have hinv : ∀ g, (R g).det • σ g⁻¹ = (R g).trace • 1 - σ g := by
    intro g
    have h := congrArg (· * σ g⁻¹) (hrel g)
    have hgg : σ g * σ g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    simp only [sub_mul, add_mul, smul_mul_assoc, mul_assoc, hgg, mul_one, one_mul, zero_mul] at h
    rw [hRg]
    linear_combination (norm := module) h
  have hpair : ∀ g h, σ g * σ h + σ h * σ g - (R h).trace • σ g - (R g).trace • σ h
      + ((R g).trace * (R h).trace - (R g * R h).trace) • (1 : Module.End E U) = 0 := by
    intro g h
    have e1 := hinv (g * h)
    have e2 : (R (g*h)).det • σ (g*h)⁻¹ = ((R h).det • σ h⁻¹) * ((R g).det • σ g⁻¹) := by
      rw [_root_.mul_inv_rev, map_mul σ, map_mul R, det_mul, smul_mul_smul_comm, mul_comm (R g).det]
    rw [e2, hinv g, hinv h, map_mul σ, map_mul R] at e1
    simp only [mul_sub, sub_mul, smul_mul_smul_comm, one_mul, mul_one, smul_mul_assoc,
      mul_smul_comm] at e1
    linear_combination (norm := module) e1
  have hB : ∀ x y, Φ x * Φ y + Φ y * Φ x - (Ψ y).trace • Φ x - (Ψ x).trace • Φ y
      + ((Ψ x).trace * (Ψ y).trace - (Ψ x * Ψ y).trace) • (1 : Module.End E U) = 0 := by
    intro x y
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x₁ x₂ h₁ h₂ =>
      simp only [map_add, add_mul, mul_add, trace_add, add_smul, smul_add] at h₁ h₂ ⊢
      linear_combination (norm := module) h₁ + h₂
    | single g c =>
      induction y using MonoidAlgebra.induction_linear with
      | zero => simp
      | add y₁ y₂ h₁ h₂ =>
        simp only [map_add, add_mul, mul_add, trace_add, add_smul, smul_add] at h₁ h₂ ⊢
        linear_combination (norm := module) h₁ + h₂
      | single h d =>
        simp only [hΦ, hΨ, trace_smul, smul_mul_smul_comm, smul_eq_mul]
        linear_combination (norm := module) (c * d) • hpair g h

  have hanti : ∀ x y, Ψ x = 0 → Φ x * Φ y + Φ y * Φ x = (Ψ y).trace • Φ x := by
    intro x y hx
    have := hB x y
    simp only [hx, trace_zero, zero_mul, mul_zero, sub_self, zero_smul, add_zero, sub_zero] at this
    linear_combination (norm := module) this
  have h2c : ∀ X : Module.End E U, X + X = 0 → X = 0 := by
    intro X hX
    rw [← two_smul E X] at hX
    exact (smul_eq_zero.mp hX).resolve_left h2
  obtain ⟨y₁, hy₁⟩ := hsurj (Matrix.single 0 1 1)
  obtain ⟨y₂, hy₂⟩ := hsurj (Matrix.single 1 0 1)
  have hc : Ψ (y₁ * y₂ - y₂ * y₁) = !![1, 0; 0, -1] := by
    rw [map_sub, map_mul, map_mul, hy₁, hy₂]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply]
  have hc2 : Ψ ((y₁ * y₂ - y₂ * y₁) * (y₁ * y₂ - y₂ * y₁) - 1) = 0 := by
    rw [map_sub, map_mul, hc, map_one]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have ht1 : (Ψ y₁).trace = 0 := by rw [hy₁]; simp [Matrix.trace, Fin.sum_univ_two, Matrix.single_apply]
  have ht2 : (Ψ y₂).trace = 0 := by rw [hy₂]; simp [Matrix.trace, Fin.sum_univ_two, Matrix.single_apply]
  have htc : (Ψ (y₁ * y₂ - y₂ * y₁)).trace = 0 := by rw [hc]; simp [Matrix.trace, Fin.sum_univ_two]
  have hJ : ∀ x, Ψ x = 0 → Φ x = 0 := by
    intro x hx
    set N := Φ x
    set a := Φ y₁
    set b := Φ y₂
    have e1 : N * a = -(a * N) := eq_neg_of_add_eq_zero_left (by rw [hanti x y₁ hx, ht1, zero_smul])
    have e2 : N * b = -(b * N) := eq_neg_of_add_eq_zero_left (by rw [hanti x y₂ hx, ht2, zero_smul])
    have k1 : N * (a * b) = a * b * N := by
      rw [← mul_assoc, e1, neg_mul, mul_assoc, e2, mul_neg, neg_neg, mul_assoc]
    have k2 : N * (b * a) = b * a * N := by
      rw [← mul_assoc, e2, neg_mul, mul_assoc, e1, mul_neg, neg_neg, mul_assoc]
    have hC : Φ (y₁ * y₂ - y₂ * y₁) = a * b - b * a := by rw [map_sub, map_mul, map_mul]
    have hNC : N * (a * b - b * a) = 0 := by
      have h3 := hanti x (y₁ * y₂ - y₂ * y₁) hx
      rw [htc, zero_smul, hC] at h3
      apply h2c
      have : (a * b - b * a) * N = N * (a * b - b * a) := by rw [mul_sub, sub_mul, k1, k2]
      rw [this] at h3; exact h3
    set x' := (y₁ * y₂ - y₂ * y₁) * (y₁ * y₂ - y₂ * y₁) - 1
    have hN' : Φ x' * Φ x' = 0 := by
      apply h2c
      rw [hanti x' x' hc2, hc2, trace_zero, zero_smul]
    have hNN' : N * Φ x' = -N := by
      have hx' : Φ x' = (a * b - b * a) * (a * b - b * a) - 1 := by
        simp only [x']; rw [map_sub, map_mul, hC, map_one]
      rw [hx', mul_sub, mul_one, ← mul_assoc, hNC, zero_mul, zero_sub]
    have h5 : N * Φ x' * Φ x' = 0 := by rw [mul_assoc, hN', mul_zero]
    rw [hNN', neg_mul, hNN', neg_neg] at h5
    exact h5

  have hΦeq : ∀ x y, Ψ x = Ψ y → Φ x = Φ y := by
    intro x y h
    have := hJ (x - y) (by rw [map_sub, h, sub_self])
    rwa [map_sub, sub_eq_zero] at this
  choose yP hyP using fun i j : Fin 2 => hsurj (Matrix.single i j 1)
  let P : Fin 2 → Fin 2 → Module.End E U := fun i j => Φ (yP i j)
  have hP : ∀ i j k l, P i j * P k l = if j = k then P i l else 0 := by
    intro i j k l
    simp only [P, ← map_mul]
    split_ifs with h
    · subst h
      apply hΦeq
      rw [map_mul, hyP, hyP, hyP, Matrix.single_mul_single_same, mul_one]
    · rw [← map_zero Φ]
      apply hΦeq
      rw [map_mul, hyP, hyP, map_zero]
      simp [h]
  have hsum : ∑ i, P i i = 1 := by
    simp only [P]
    rw [← map_sum, ← map_one Φ]
    apply hΦeq
    rw [map_sum, map_one]
    simp only [hyP]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_two, Matrix.single_apply, Matrix.one_apply]
  have hσ : ∀ g, σ g = ∑ a, ∑ b, (R g) a b • P a b := by
    intro g
    have e : σ g = Φ (MonoidAlgebra.single g 1) := by rw [hΦ, one_smul]
    rw [e]
    simp only [P, ← map_smul, ← map_sum]
    apply hΦeq
    simp only [map_sum, map_smul, hΨ, hyP, one_smul, Matrix.smul_single, smul_eq_mul, mul_one]
    exact Matrix.matrix_eq_sum_single (R g)
  obtain ⟨m, π, s, k1, k2, k3, k4⟩ := exists_decomp (0 : Fin 2) P hP hsum
  refine ⟨m, π, s, fun i g => ?_, fun i g => ?_, k3, k4⟩
  · rw [hσ g]; exact k1 i (R g)
  · rw [hσ g]; exact k2 i (R g)

end GlobalTheory.CayleyHamiltonId
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationEqOneOfMemInvMem
section
open GlobalTheory.KCoh Polynomial

namespace GlobalTheory.K4

theorem kum_congr_base {K₁ K₂ Ω : Type*} [Field K₁] [Field K₂] [Field Ω] [Algebra K₁ Ω] [Algebra K₂ Ω] {N : ℕ}
    (ζ θ : Ω) (g : Ω ≃ₐ[K₁] Ω) (g' : Ω ≃ₐ[K₂] Ω) (h : ∀ x, g x = g' x) :
    GlobalTheory.NeedB.kum (N := N) ζ θ g = GlobalTheory.NeedB.kum (N := N) ζ θ g' := by
  have e : g θ = g' θ := h θ
  unfold GlobalTheory.NeedB.kum
  rw [e]

theorem valuation_eq_one_of_mem_inv_mem {Ω : Type*} [Field Ω] (B : ValuationSubring Ω) {x : Ω} (hx : x ∈ B)
    (hx' : x⁻¹ ∈ B) (h0 : x ≠ 0) : B.valuation x = 1 := by
  have h1 : B.valuation x ≤ 1 := (B.valuation_le_one_iff x).2 hx
  have h2 : B.valuation x⁻¹ ≤ 1 := (B.valuation_le_one_iff _).2 hx'
  have h3 : B.valuation x * B.valuation x⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ h0, map_one]
  refine le_antisymm h1 ?_
  calc (1 : _) = B.valuation x * B.valuation x⁻¹ := h3.symm
    _ ≤ B.valuation x * 1 := by gcongr
    _ = B.valuation x := mul_one _

theorem mem_of_isIntegral_of_le {R Ω : Type*} [CommRing R] [Field Ω] [Algebra R Ω] (B : ValuationSubring Ω)
    (hB : ∀ p : R, algebraMap R Ω p ∈ B) {x : Ω} (hx : IsIntegral R x) : x ∈ B := by
  obtain ⟨p, hpm, hp⟩ := hx
  let φ : R →+* B := (algebraMap R Ω).codRestrict B hB
  have hcomp : (algebraMap B Ω).comp φ = algebraMap R Ω := by
    ext r
    rfl
  have hB' : IsIntegral B x := ⟨p.map φ, hpm.map φ, by rw [Polynomial.eval₂_map, hcomp]; exact hp⟩
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := B) (K := Ω)).1 hB'
  rw [← hy]
  exact y.2

theorem thmA_on_open_geo : GlobalTheory.NeedB.ThmA → ∀ (k F Ω : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Field Ω] [Algebra F (RatFunc k)] [Algebra (RatFunc k) Ω] [Algebra F Ω] [IsScalarTower F (RatFunc k) Ω] [Algebra k[X] Ω] [IsScalarTower k[X] (RatFunc k) Ω] [IsAlgClosure (RatFunc k) Ω] [Algebra.IsAlgebraic F Ω] (N : ℕ) [NeZero N] (ζ : Ω), IsPrimitiveRoot ζ N → ∀ (U : Subgroup (Ω ≃ₐ[F] Ω)), IsOpen (U : Set (Ω ≃ₐ[F] Ω)) → ∀ α β : Ω, α ≠ 0 → β ≠ 0 → IsIntegral k[X] α → IsIntegral k[X] α⁻¹ → IsIntegral k[X] β → IsIntegral k[X] β⁻¹ →
 (∀ g ∈ U, g (α ^ N) = α ^ N ∧ g (β ^ N) = β ^ N) →
 ∃ η₀ : (Ω ≃ₐ[F] Ω) → ZMod N, IsLocallyConstant (fun g : ↥(GlobalTheory.K4.geo F (RatFunc k) Ω ⊓ U) => η₀ g) ∧
  (∀ g ∈ GlobalTheory.K4.geo F (RatFunc k) Ω ⊓ U, ∀ h ∈ GlobalTheory.K4.geo F (RatFunc k) Ω ⊓ U, GlobalTheory.NeedB.kum (N := N) ζ α g * GlobalTheory.NeedB.kum ζ β h = η₀ h - η₀ (g * h) + η₀ g) ∧
  ∀ r ∈ GlobalTheory.K4.geo F (RatFunc k) Ω ⊓ U, ∀ B : ValuationSubring Ω, (∀ p : k[X], algebraMap k[X] Ω p ∈ B) → GlobalTheory.NeedB.Inert B r → η₀ r = 0 ∧ r α = α ∧ r β = β := by
  intro hA k F Ω _ _ _ _ _ _ _ _ _ _ _ _ _ N _ ζ hζ U hU α β hα0 hβ0 hαi hαi' hβi hβi' hUfix
  classical
  obtain ⟨-, ⟨e, he, hec, -⟩, -, -, -⟩ := GlobalTheory.T.fixingSubgroupOfIntermediateField_properties F (RatFunc k) Ω
  let U' : Subgroup (Ω ≃ₐ[RatFunc k] Ω) :=
    U.comap ((GlobalTheory.K4.geo F (RatFunc k) Ω).subtype.comp e.toMonoidHom)
  have hU'mem : ∀ g, g ∈ U' ↔ ((e g : GlobalTheory.K4.geo F (RatFunc k) Ω) : Ω ≃ₐ[F] Ω) ∈ U := fun g => Iff.rfl
  have hU'open : IsOpen (U' : Set (Ω ≃ₐ[RatFunc k] Ω)) :=
    (continuous_subtype_val.comp hec).isOpen_preimage _ hU
  let K' : IntermediateField (RatFunc k) Ω := IntermediateField.fixedField U'
  have hfixle : U' ≤ K'.fixingSubgroup := (IntermediateField.le_iff_le U' K').1 le_rfl
  haveI : FiniteDimensional (RatFunc k) K' :=
    (InfiniteGalois.isOpen_iff_finite K').1 (Subgroup.isOpen_mono hfixle hU'open)
  haveI : IsScalarTower F K' Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower k[X] K' Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsAlgClosure K' Ω :=
    ⟨IsAlgClosure.isAlgClosed (RatFunc k), Algebra.IsAlgebraic.tower_top (K := RatFunc k) K'⟩
  obtain ⟨-, ⟨e', he', -, hesc'⟩, -, -, -⟩ := GlobalTheory.T.fixingSubgroupOfIntermediateField_properties F K' Ω
  have hφ : ∀ g (hg : g ∈ GlobalTheory.K4.geo F K' Ω) x, (e'.symm ⟨g, hg⟩) x = g x := by
    intro g hg x
    have := he' (e'.symm ⟨g, hg⟩) x
    rw [MulEquiv.apply_symm_apply] at this
    exact this.symm
  have hsub : ∀ g, g ∈ GlobalTheory.K4.geo F (RatFunc k) Ω ⊓ U → g ∈ GlobalTheory.K4.geo F K' Ω := by
    intro g hg
    rw [Subgroup.mem_inf] at hg
    rw [GlobalTheory.K4.TopW.mem_geo]
    intro x
    have h1 : e.symm ⟨g, hg.1⟩ ∈ U' := by
      rw [hU'mem, MulEquiv.apply_symm_apply]
      exact hg.2
    have h2 := (IntermediateField.mem_fixedField_iff U' (x : Ω)).1 x.2 _ h1
    have h3 : (e.symm ⟨g, hg.1⟩) (x : Ω) = g x := by
      have := he (e.symm ⟨g, hg.1⟩) (x : Ω)
      rw [MulEquiv.apply_symm_apply] at this
      exact this.symm
    rw [IntermediateField.algebraMap_apply, ← h3]
    exact h2
  have hfixK' : ∀ z : Ω, (∀ g ∈ U, g z = z) → z ∈ K' := by
    intro z hz
    refine (IntermediateField.mem_fixedField_iff U' z).2 fun f hf => ?_
    have := hz _ ((hU'mem f).1 hf)
    rw [he] at this
    exact this
  have hαK : α ^ N ∈ K' := hfixK' _ fun g hg => (hUfix g hg).1
  have hβK : β ^ N ∈ K' := hfixK' _ fun g hg => (hUfix g hg).2
  have hint : ∀ {θ : Ω} (hθ : θ ^ N ∈ K'), IsIntegral k[X] θ → IsIntegral k[X] θ⁻¹ →
      (⟨θ ^ N, hθ⟩ : K') ∈ FunctionField.ringOfIntegers k K' ∧
        (⟨θ ^ N, hθ⟩ : K')⁻¹ ∈ FunctionField.ringOfIntegers k K' := by
    intro θ hθ h1 h2
    constructor
    · refine (mem_integralClosure_iff _ _).2 ?_
      refine (isIntegral_algebraMap_iff (algebraMap K' Ω).injective).1 ?_
      exact h1.pow N
    · refine (mem_integralClosure_iff _ _).2 ?_
      refine (isIntegral_algebraMap_iff (algebraMap K' Ω).injective).1 ?_
      rw [map_inv₀, IntermediateField.algebraMap_apply, ← inv_pow]
      exact h2.pow N
  have hne : ∀ {θ : Ω} (hθ : θ ^ N ∈ K'), θ ≠ 0 → (⟨θ ^ N, hθ⟩ : K') ≠ 0 := by
    intro θ hθ h0 h
    exact pow_ne_zero N h0 (congrArg Subtype.val h)
  obtain ⟨-, -, -, -, η, hηlc, hηco, hηin⟩ :=
    hA k K' Ω N ζ (Nat.pos_of_ne_zero (NeZero.ne N)) hζ ⟨α ^ N, hαK⟩ ⟨β ^ N, hβK⟩ α β (hne hαK hα0) (hne hβK hβ0)
      (hint hαK hαi hαi').1 (hint hαK hαi hαi').2 (hint hβK hβi hβi').1 (hint hβK hβi hβi').2 rfl rfl
  obtain ⟨η₀, hη₀⟩ : ∃ η₀ : (Ω ≃ₐ[F] Ω) → ZMod N,
      ∀ g (hg : g ∈ GlobalTheory.K4.geo F K' Ω), η₀ g = η (e'.symm ⟨g, hg⟩) :=
    ⟨fun g => if hg : g ∈ GlobalTheory.K4.geo F K' Ω then η (e'.symm ⟨g, hg⟩) else 0, fun g hg => dif_pos hg⟩
  refine ⟨η₀, ?_, ?_, ?_⟩
  · have hfun : (fun g : ↥(GlobalTheory.K4.geo F (RatFunc k) Ω ⊓ U) => η₀ g) =
        η ∘ e'.symm ∘ (fun g : ↥(GlobalTheory.K4.geo F (RatFunc k) Ω ⊓ U) => (⟨g.1, hsub _ g.2⟩ : GlobalTheory.K4.geo F K' Ω)) := by
      funext g
      exact hη₀ _ _
    rw [hfun]
    exact hηlc.comp_continuous (hesc'.comp (continuous_subtype_val.subtype_mk _))
  · intro g hg h hh
    have hgh := mul_mem hg hh
    rw [hη₀ _ (hsub _ hg), hη₀ _ (hsub _ hh), hη₀ _ (hsub _ hgh),
      kum_congr_base ζ α g (e'.symm ⟨g, hsub _ hg⟩) (fun x => (hφ _ _ x).symm),
      kum_congr_base ζ β h (e'.symm ⟨h, hsub _ hh⟩) (fun x => (hφ _ _ x).symm)]
    have hm : e'.symm ⟨g * h, hsub _ hgh⟩ = e'.symm ⟨g, hsub _ hg⟩ * e'.symm ⟨h, hsub _ hh⟩ := by
      rw [← map_mul]
      rfl
    rw [hm]
    exact hηco _ _
  · intro r hr B hB hinert
    have hmemB : ∀ {x : Ω}, IsIntegral k[X] x → x ∈ B := fun hx => mem_of_isIntegral_of_le B hB hx
    have hNk : (N : k) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
    have hk : (N : k[X]) * C ((N : k)⁻¹) = 1 := by
      rw [← map_natCast C N, ← C_mul, mul_inv_cancel₀ hNk, C_1]
    have h1 : (N : Ω) * algebraMap k[X] Ω (C ((N : k)⁻¹)) = 1 := by
      rw [← map_natCast (algebraMap k[X] Ω) N, ← map_mul, hk, map_one]
    have hNΩ : (N : Ω) ≠ 0 := left_ne_zero_of_mul_eq_one h1
    have hvN : B.valuation (N : Ω) = 1 := by
      refine valuation_eq_one_of_mem_inv_mem B ?_ ?_ hNΩ
      · rw [← map_natCast (algebraMap k[X] Ω) N]
        exact hB _
      · rw [← eq_inv_of_mul_eq_one_right h1]
        exact hB _
    have hroot : ∀ θ : Ω, θ ≠ 0 → IsIntegral k[X] θ → IsIntegral k[X] θ⁻¹ → r (θ ^ N) = θ ^ N → r θ = θ := by
      intro θ h0 hi hi' hfix
      refine GlobalTheory.T.inert_apply_eq_of_pow_fixed_of_valuation_one F Ω B r N 1 θ (Nat.pos_of_ne_zero (NeZero.ne N)) hvN hinert (map_one r) one_ne_zero hfix ?_
      rw [one_pow, div_one]
      refine valuation_eq_one_of_mem_inv_mem B (hmemB (hi.pow N)) ?_ (pow_ne_zero N h0)
      rw [← inv_pow]
      exact hmemB (hi'.pow N)
    rw [Subgroup.mem_inf] at hr
    refine ⟨?_, hroot α hα0 hαi hαi' (hUfix r hr.2).1, hroot β hβ0 hβi hβi' (hUfix r hr.2).2⟩
    have hr' : r ∈ GlobalTheory.K4.geo F (RatFunc k) Ω ⊓ U := Subgroup.mem_inf.2 hr
    rw [hη₀ _ (hsub _ hr')]
    refine hηin B ?_ _ ?_
    · intro x hx
      refine hmemB ?_
      exact ((mem_integralClosure_iff _ _).1 hx).algebraMap
    · intro x hx
      rw [hφ]
      exact hinert x hx

end GlobalTheory.K4
end

