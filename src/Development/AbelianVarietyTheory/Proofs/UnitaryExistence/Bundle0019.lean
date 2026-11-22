import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HermFormConjDiag
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsTranslateJetNeZero
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle0004
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsImEqLattice
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifferentiableFderivApply
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameOfPeriodLinear
section
open NumberField Matrix
open scoped nonZeroDivisors ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.FramePeriod

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

omit [NumberField E] [IsCMField E] in

lemma eq_of_hermC_eq (τ : E →+* ℂ) (Gm : Matrix (Fin r) (Fin r) E) (hG : Gm.det ≠ 0)
    (v w : Fin r → ℂ) (h : ∀ u, FD.hermC τ Gm v u = FD.hermC τ Gm w u) : v = w := by
  classical
  have hd : (τ.mapMatrix Gm).det ≠ 0 := by
    rw [← RingHom.map_det]; exact (map_ne_zero τ).2 hG
  rw [← sub_eq_zero]
  apply Matrix.eq_zero_of_vecMul_eq_zero hd
  rw [sub_vecMul, sub_eq_zero]
  funext b
  have := h (Pi.single b 1)
  simpa [FD.hermC, Pi.single_apply, apply_ite, vecMul, dotProduct] using this

lemma loc_compare (τ : E →+* ℂ) (Gm : Matrix (Fin r) (Fin r) E) (hG : Gm.det ≠ 0) (q : ℕ)
    (M M' K : Matrix (Fin r) (Fin r) ℂ) (hM : M.det ≠ 0) (hM' : M'.det ≠ 0)
    (hK : ∀ a c : Fin r, ¬ ((a : ℕ) < q ↔ (c : ℕ) < q) → K a c = 0)
    (h : ∀ u, locPer τ Gm q M' u = K *ᵥ locPer τ Gm q M u) :
    (∀ a c : Fin r, (a : ℕ) < q → K a c = (M⁻¹ * M') c a) ∧
      ∀ a c : Fin r, q ≤ (a : ℕ) → K a c = (M⁻¹ * M')⁻¹ a c := by
  classical
  have hMu : IsUnit M.det := isUnit_iff_ne_zero.2 hM
  constructor
  · intro a c ha
    have h1 : FD.col M' a = ∑ e, K a e • FD.col M e := by
      apply eq_of_hermC_eq τ Gm hG
      intro u
      have := congrFun (h u) a
      rw [locPer_apply, if_pos ha] at this
      rw [this, FD.hermC_sum_left, mulVec, dotProduct]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [FD.hermC_smul_left, locPer_apply]
      by_cases he : (e : ℕ) < q
      · rw [if_pos he]
      · rw [hK a e (by simp [ha, he])]; simp
    rw [← FD.Data.mulVec_eq_sum_col] at h1
    have h2 : M⁻¹ *ᵥ FD.col M' a = K a := by
      rw [h1, mulVec_mulVec, Matrix.nonsing_inv_mul _ hMu, one_mulVec]
    rw [← h2]
    rfl
  · intro a c ha
    have ha' : ¬ (a : ℕ) < q := not_lt.2 ha
    rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hMu]
    have h1 := congrFun (h (M *ᵥ Pi.single c 1)) a
    rw [locPer_apply, if_neg ha', mulVec_mulVec] at h1
    have h2 : (K *ᵥ locPer τ Gm q M (M *ᵥ Pi.single c 1)) a = (K *ᵥ Pi.single c 1) a := by
      rw [mulVec, mulVec, dotProduct, dotProduct]
      refine Finset.sum_congr rfl fun e _ => ?_
      by_cases he : (e : ℕ) < q
      · rw [hK a e (by simp [ha', he])]; simp
      · rw [locPer_apply, if_neg he, mulVec_mulVec, Matrix.nonsing_inv_mul _ hMu, one_mulVec]
    rw [h2] at h1
    simpa using h1.symm

lemma allPer_scale {Ψ : Finset (E →+* ℂ)} (Gm : Matrix (Fin r) (Fin r) E) (q : ℕ) (x : FD.Frame Ψ r)
    {g : ℕ} (idx : Fin g ≃ Ψ × Fin r) (c : Ψ → ℂ) (y : Ψ → Fin r → ℂ) (k : Fin g) :
    allPer Gm q x idx (fun τ => c τ • y τ) k =
      (if ((idx k).2 : ℕ) < q then conj (c (idx k).1) else c (idx k).1) * allPer Gm q x idx y k := by
  rw [allPer_apply, allPer_apply, locPer_apply, locPer_apply]
  split_ifs
  · rw [FD.hermC_smul_right]
  · rw [mulVec_smul]; rfl

lemma block_of_allPer {Ψ : Finset (E →+* ℂ)} (Gm : Matrix (Fin r) (Fin r) E) (q : ℕ)
    (x x' : FD.Frame Ψ r) {g : ℕ} (idx : Fin g ≃ Ψ × Fin r) (h : Matrix (Fin g) (Fin g) ℂ)
    (hs : Function.Surjective (allPer Gm q x idx))
    (hh : ∀ y, allPer Gm q x' idx y = h *ᵥ allPer Gm q x idx y) (k k' : Fin g)
    (hk : ¬ ((idx k).1 = (idx k').1 ∧ (((idx k).2 : ℕ) < q ↔ ((idx k').2 : ℕ) < q))) : h k k' = 0 := by
  classical
  have key : ∀ c : Ψ → ℂ, ((if ((idx k).2 : ℕ) < q then conj (c (idx k).1) else c (idx k).1) -
      (if ((idx k').2 : ℕ) < q then conj (c (idx k').1) else c (idx k').1)) * h k k' = 0 := by
    intro c
    obtain ⟨y, hy⟩ := hs (Pi.single k' 1)
    have h1 := congrFun (hh (fun τ => c τ • y τ)) k
    rw [allPer_scale, hh, hy] at h1
    have h2 : allPer Gm q x idx (fun τ => c τ • y τ) = Pi.single k'
        (if ((idx k').2 : ℕ) < q then conj (c (idx k').1) else c (idx k').1) := by
      funext l
      rw [allPer_scale, hy]
      by_cases hl : l = k'
      · subst hl; simp
      · simp [hl]
    rw [h2] at h1
    simp only [mulVec_single, Pi.smul_apply, col_apply, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op, mul_one] at h1
    linear_combination h1
  by_cases h1 : (idx k).1 = (idx k').1
  · have h2 := key (fun _ => Complex.I)
    have hI : (2 * Complex.I) ≠ 0 := by simp
    by_cases ha : ((idx k).2 : ℕ) < q <;> by_cases hb : ((idx k').2 : ℕ) < q
    · exact absurd ⟨h1, by simp [ha, hb]⟩ hk
    · rw [if_pos ha, if_neg hb, Complex.conj_I] at h2
      apply mul_left_cancel₀ hI
      linear_combination -h2
    · rw [if_neg ha, if_pos hb, Complex.conj_I] at h2
      apply mul_left_cancel₀ hI
      linear_combination h2
    · exact absurd ⟨h1, by simp [ha, hb]⟩ hk
  · have h2 := key (Pi.single (idx k).1 1)
    simpa [Ne.symm h1] using h2

theorem frame_of_period_linear : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (r : ℕ) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (Ψ : Finset (E →+* ℂ)) (hΨ : ∀ τ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0) (g : ℕ) (idx : Fin g ≃ Ψ × Fin r) (ty : Fin g → (E →+* ℂ)) (hty : ∀ k, ty k = if ((idx k).2 : ℕ) < D.q then ComplexEmbedding.conjugate (idx k).1.1 else (idx k).1.1), FD.cc ξ = -ξ → (∀ τ ∈ Ψ, 0 < (τ ξ).im) → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, FD.cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm Gm (φ x) (φ y))) → ∀ (P : D.La →+ (Fin g → ℂ)), ∀ x ∈ FD.GG Ψ Gm D.q, ∀ x' ∈ FD.GG Ψ Gm D.q, (∀ v k, P v k = if ((idx k).2 : ℕ) < D.q then FD.hermC (idx k).1.1 Gm (FD.col (FD.mat x (idx k).1) (idx k).2) (FD.Data.emb (idx k).1.1 (φ v)) else ((FD.mat x (idx k).1)⁻¹ *ᵥ FD.Data.emb (idx k).1.1 (φ v)) (idx k).2) → ∀ (P' : D.La →+ (Fin g → ℂ)), (∀ v k, P' v k = if ((idx k).2 : ℕ) < D.q then FD.hermC (idx k).1.1 Gm (FD.col (FD.mat x' (idx k).1) (idx k).2) (FD.Data.emb (idx k).1.1 (φ v)) else ((FD.mat x' (idx k).1)⁻¹ *ᵥ FD.Data.emb (idx k).1.1 (φ v)) (idx k).2) → ∀ h : Matrix (Fin g) (Fin g) ℂ, (∀ v, P' v = h *ᵥ P v) → ∃ b : FD.Frame Ψ r, x' = FD.rmul x b ∧ (∀ τ (a c : Fin r), (c : ℕ) < D.q → D.q ≤ (a : ℕ) → b τ a c = 0) ∧ (∀ k k', (idx k).1 = (idx k').1 → ((idx k).2 : ℕ) < D.q → ((idx k').2 : ℕ) < D.q → h k k' = b (idx k).1 (idx k').2 (idx k).2) ∧ (∀ k k', (idx k).1 = (idx k').1 → D.q ≤ ((idx k).2 : ℕ) → D.q ≤ ((idx k').2 : ℕ) → h k k' = (FD.mat b (idx k).1)⁻¹ (idx k).2 (idx k').2) ∧ ∀ k k', ty k ≠ ty k' → h k k' = 0 := by
  classical
  intro E _ _ _ H D r ξ Gm φ Ψ hΨ g idx ty hty hξ hpos ⟨hφ, hspan, hG, hdet, hEF⟩ P x hx x' hx' hP P' hP' h hh
  have hcm := cmType H Ψ hΨ
  have hloc := fun τ : Ψ => (exists_loc τ.1 Gm hG D.q (FD.mat x τ) (hx τ).1 (hx τ).2).1
  have hbij := allPer_bijective Gm D.q x idx hloc
  have hQ : ∀ v, P v = allPer Gm D.q x idx (CMLattice.embAll Ψ r (φ v)) := fun v =>
    funext fun k => hP v k
  have hQ' : ∀ v, P' v = allPer Gm D.q x' idx (CMLattice.embAll Ψ r (φ v)) := fun v =>
    funext fun k => hP' v k
  have := D.fin
  obtain ⟨b, hb⟩ := CMLattice.exists_basis_of_cmType Ψ hcm r (LinearMap.range φ)
    (Module.Finite.iff_fg.1 inferInstance) (by rw [LinearMap.coe_range]; exact hspan)
  have hall : ∀ y, allPer Gm D.q x' idx y = h *ᵥ allPer Gm D.q x idx y := by
    have : allPer Gm D.q x' idx = (h.mulVecLin.restrictScalars ℝ) ∘ₗ allPer Gm D.q x idx := by
      apply b.ext
      intro i
      obtain ⟨_, ⟨v, rfl⟩, hv⟩ := (hb (b i)).1 (Submodule.subset_span ⟨i, rfl⟩)
      rw [← hv, ← hQ', hh, hQ]
      rfl
    intro y
    rw [this]; rfl
  have hblock := block_of_allPer Gm D.q x x' idx h hbij.2 hall
  let K : Ψ → Matrix (Fin r) (Fin r) ℂ := fun τ =>
    Matrix.of fun a c => h (idx.symm (τ, a)) (idx.symm (τ, c))
  have hK0 : ∀ τ (a c : Fin r), ¬ ((a : ℕ) < D.q ↔ (c : ℕ) < D.q) → K τ a c = 0 := by
    intro τ a c hac
    apply hblock
    simpa using hac
  have hK : ∀ (τ : Ψ) u, locPer τ.1 Gm D.q (FD.mat x' τ) u =
      K τ *ᵥ locPer τ.1 Gm D.q (FD.mat x τ) u := by
    intro τ u
    funext a
    have h1 := congrFun (allPer_symm Gm D.q x' idx (fun _ => u) τ) a
    rw [← h1, hall, mulVec, mulVec, dotProduct, dotProduct, ← idx.symm.sum_comp, Fintype.sum_prod_type,
      Finset.sum_eq_single τ]
    · refine Finset.sum_congr rfl fun c _ => ?_
      rw [← allPer_symm Gm D.q x idx (fun _ => u) τ]
      rfl
    · intro σ _ hσ
      refine Finset.sum_eq_zero fun c _ => ?_
      rw [hblock, zero_mul]
      simp [hσ.symm]
    · simp
  have hc := fun τ : Ψ => loc_compare τ.1 Gm hdet D.q (FD.mat x τ) (FD.mat x' τ) (K τ) (hx τ).1 (hx' τ).1
    (hK0 τ) (hK τ)
  have hhK : ∀ k k', (idx k).1 = (idx k').1 → h k k' = K (idx k).1 (idx k).2 (idx k').2 := by
    intro k k' e
    simp only [K, of_apply]
    conv_rhs => rw [Prod.mk.eta, e, Prod.mk.eta]
    simp
  refine ⟨fun τ => ((FD.mat x τ)⁻¹ * FD.mat x' τ : Matrix (Fin r) (Fin r) ℂ), ?_, ?_, ?_, ?_, ?_⟩
  · funext τ
    exact (Matrix.mul_nonsing_inv_cancel_left (FD.mat x τ) (FD.mat x' τ)
      (isUnit_iff_ne_zero.2 (hx τ).1)).symm
  · intro τ a c hcq ha
    exact ((hc τ).1 c a hcq).symm.trans (hK0 τ c a (by simp [hcq, ha]))
  · intro k k' e h1 _
    rw [hhK k k' e]
    exact (hc _).1 _ _ h1
  · intro k k' e h1 _
    rw [hhK k k' e]
    exact (hc _).2 _ _ h1
  · intro k k' hne
    apply hblock
    rintro ⟨e1, e2⟩
    apply hne
    rw [hty, hty, e1]
    simp only [e2]

end

end GlobalTheory.FramePeriod
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ImFormApply
section
namespace GlobalTheory.UpperHalfImaginaryForm

open ReciprocityTheory.ChartRestriction.G.I2

noncomputable section

variable {ι : Type} [Fintype ι]

def imForm : EuclideanSpace ℂ ι →ₗ[ℝ] EuclideanSpace ℂ ι →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => (Hf x y).im)
    (fun x y z => by simp [Hf, add_mul, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [Hf, PiLp.smul_apply, Complex.real_smul, mul_assoc, ← Finset.mul_sum, smul_eq_mul]
      simp)
    (fun x y z => by simp [Hf, mul_add, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [Hf, PiLp.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal,
        mul_left_comm _ (c : ℂ), ← Finset.mul_sum, smul_eq_mul]
      simp)

theorem imForm_apply (x y : EuclideanSpace ℂ ι) : imForm x y = (Hf x y).im := rfl

theorem imForm_swap (x y : EuclideanSpace ℂ ι) : imForm y x = -imForm x y := by
  have h : Hf y x = starRingEnd ℂ (Hf x y) := by
    simp [Hf, map_sum, mul_comm]
  rw [imForm_apply, imForm_apply, h, Complex.conj_im]

variable {n : ℕ}

def upper (b : Module.Basis (Fin n) ℝ (EuclideanSpace ℂ ι)) :
    EuclideanSpace ℂ ι →ₗ[ℝ] EuclideanSpace ℂ ι →ₗ[ℝ] ℝ :=
  b.constr ℝ fun i => b.constr ℝ fun j => if i < j then imForm (b i) (b j) else 0

theorem upper_basis (b : Module.Basis (Fin n) ℝ (EuclideanSpace ℂ ι)) (i j : Fin n) :
    upper b (b i) (b j) = if i < j then imForm (b i) (b j) else 0 := by
  simp only [upper, b.constr_basis]

theorem upper_sub (b : Module.Basis (Fin n) ℝ (EuclideanSpace ℂ ι)) (x y : EuclideanSpace ℂ ι) :
    imForm x y = upper b x y - upper b y x := by
  have key : imForm = upper b - (upper b).flip := by
    refine b.ext fun i => b.ext fun j => ?_
    simp only [LinearMap.sub_apply, LinearMap.flip_apply, upper_basis]
    rcases lt_trichotomy i j with h | h | h
    · simp [h, lt_asymm h]
    · subst h
      have := imForm_swap (b i) (b i)
      simp only [lt_irrefl, if_false, sub_zero]
      linarith
    · have := imForm_swap (b j) (b i)
      simp only [h, lt_asymm h, if_true, if_false, zero_sub]
      linarith
  rw [key]
  simp only [LinearMap.sub_apply, LinearMap.flip_apply]

theorem upper_int (b : Module.Basis (Fin n) ℝ (EuclideanSpace ℂ ι))
    (hint : ∀ x y : EuclideanSpace ℂ ι, x ∈ lat b → y ∈ lat b → ∃ k : ℤ, (Hf x y).im = k)
    {x y : EuclideanSpace ℂ ι} (hx : x ∈ lat b) (hy : y ∈ lat b) :
    ∃ k : ℤ, upper b x y = k := by
  have base : ∀ i j, ∃ k : ℤ, upper b (b i) (b j) = k := by
    intro i j
    rw [upper_basis]
    split_ifs
    · rw [imForm_apply]
      exact hint _ _ (Submodule.subset_span ⟨i, rfl⟩) (Submodule.subset_span ⟨j, rfl⟩)
    · exact ⟨0, by simp⟩
  have hrow : ∀ i, ∃ k : ℤ, upper b (b i) y = k := by
    intro i
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨j, rfl⟩ := hz
      exact base i j
    | zero => exact ⟨0, by simp⟩
    | add z w _ _ hz hw =>
      obtain ⟨k₁, h₁⟩ := hz
      obtain ⟨k₂, h₂⟩ := hw
      exact ⟨k₁ + k₂, by simp [map_add, h₁, h₂]⟩
    | smul n z _ hz =>
      obtain ⟨k₁, h₁⟩ := hz
      exact ⟨n * k₁, by simp [map_zsmul, h₁, zsmul_eq_mul]⟩
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨i, rfl⟩ := hz
    exact hrow i
  | zero => exact ⟨0, by simp⟩
  | add z w _ _ hz hw =>
    obtain ⟨k₁, h₁⟩ := hz
    obtain ⟨k₂, h₂⟩ := hw
    exact ⟨k₁ + k₂, by simp [map_add, LinearMap.add_apply, h₁, h₂]⟩
  | smul n z _ hz =>
    obtain ⟨k₁, h₁⟩ := hz
    exact ⟨n * k₁, by simp [map_zsmul, LinearMap.smul_apply, h₁, zsmul_eq_mul]⟩

theorem exists_coc {ι : Type} [Fintype ι]
    (b : Module.Basis (Fin (2 * Fintype.card ι)) ℝ (EuclideanSpace ℂ ι))
    (hint : ∀ x y : EuclideanSpace ℂ ι, x ∈ lat b → y ∈ lat b → ∃ k : ℤ, (Hf x y).im = k)
    (hperf : ∀ φ : lat b →+ ℤ, ∃ x ∈ lat b, ∀ y : lat b,
      (φ y : ℝ) = (Hf x (y : EuclideanSpace ℂ ι)).im) :
    ∃ Y : GT ι, Y.b = b ∧ FPw.Coc Y 1 := by
  refine ⟨⟨b, hint, hperf, fun x => Complex.exp (((Real.pi * upper b x x : ℝ) : ℂ) * Complex.I),
    fun x _ => Complex.norm_exp_ofReal_mul_I _⟩, rfl, ?_⟩
  intro γ hγ γ' hγ'
  obtain ⟨k, hk⟩ := upper_int b hint hγ hγ'
  have him : (Hf γ γ').im = upper b γ γ' - upper b γ' γ := by
    rw [← imForm_apply]
    exact upper_sub b γ γ'
  have hadd : upper b (γ + γ') (γ + γ') =
      upper b γ γ + upper b γ γ' + upper b γ' γ + upper b γ' γ' := by
    simp only [map_add, LinearMap.add_apply]
    ring
  dsimp only
  rw [← Complex.exp_add, ← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int]
  refine ⟨k, ?_⟩
  rw [hadd, him, hk]
  push_cast
  ring

end

end GlobalTheory.UpperHalfImaginaryForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThetaSqLawOfZero
section
noncomputable section

open Complex Matrix NumberField
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ThetaCharMult

variable {g : ℕ}

theorem sp_rel_transpose {γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hγ : γ ∈ Matrix.symplecticGroup (Fin g) ℤ) :
    ((cMat γ).toBlocks₁₂ * (cMat γ).toBlocks₂₁ᵀ - (cMat γ).toBlocks₁₁ * (cMat γ).toBlocks₂₂ᵀ = -1) ∧
    ((cMat γ).toBlocks₂₂ * (cMat γ).toBlocks₂₁ᵀ - (cMat γ).toBlocks₂₁ * (cMat γ).toBlocks₂₂ᵀ = 0) := by
  obtain ⟨-, r2, -, r4⟩ := sp_rel (SymplecticGroup.transpose_mem hγ)
  exact ⟨r2, r4⟩

theorem sp_rel_int {γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hγ : γ ∈ Matrix.symplecticGroup (Fin g) ℤ) :
    γ.toBlocks₁₁ * γ.toBlocks₂₂ᵀ = 1 + γ.toBlocks₁₂ * γ.toBlocks₂₁ᵀ := by
  have h := (sp_rel_transpose hγ).1
  have h' : (cMat γ).toBlocks₁₁ * (cMat γ).toBlocks₂₂ᵀ =
      1 + (cMat γ).toBlocks₁₂ * (cMat γ).toBlocks₂₁ᵀ := by
    rw [sub_eq_iff_eq_add] at h
    rw [h]; abel
  ext i j
  have := congrFun (congrFun h' i) j
  simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.one_apply, cMat, Matrix.toBlocks₁₁,
    Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.transpose_apply, Matrix.of_apply,
    Matrix.map_apply] at this ⊢
  exact_mod_cast this

theorem shift_algebra (A B C D τ σ J : Matrix (Fin g) (Fin g) ℂ) (hτ : τ.IsSymm) (hσ : σ.IsSymm)
    (h1 : J * (C * τ + D) = 1) (h2 : (C * τ + D) * J = 1) (hs : σ = (A * τ + B) * J)
    (hA : A - σ * C = Jᵀ) (hCD : D * Cᵀ - C * Dᵀ = 0) (a b z a' b' : Fin g → ℂ)
    (ha' : a' = Aᵀ *ᵥ a + Cᵀ *ᵥ b) (hb' : b' = Bᵀ *ᵥ a + Dᵀ *ᵥ b) :
    Jᵀ *ᵥ (z + τ *ᵥ a' + b') = Jᵀ *ᵥ z + σ *ᵥ a + b ∧
    (z + τ *ᵥ a' + b') ⬝ᵥ ((J * C) *ᵥ (z + τ *ᵥ a' + b')) +
        2 * (-(a' ⬝ᵥ (τ *ᵥ a')) / 2 - a' ⬝ᵥ (z + b')) =
      z ⬝ᵥ ((J * C) *ᵥ z) + (a ⬝ᵥ b - a' ⬝ᵥ b') +
        2 * (-(a ⬝ᵥ (σ *ᵥ a)) / 2 - a ⬝ᵥ (Jᵀ *ᵥ z + b)) := by
  set j := C * τ + D with hj
  have hjT : jᵀ = τ * Cᵀ + Dᵀ := by rw [hj, transpose_add, transpose_mul, hτ.eq]
  have hjσ : jᵀ * σ = τ * Aᵀ + Bᵀ := by
    conv_lhs => rw [← hσ.eq]
    rw [← transpose_mul, hs, Matrix.mul_assoc, h1, Matrix.mul_one, transpose_add, transpose_mul,
      hτ.eq]
  set p := σ *ᵥ a + b with hp
  set q := τ *ᵥ a' + b' with hq
  have hqp : jᵀ *ᵥ p = q := by
    rw [hp, hq, ha', hb', mulVec_add, mulVec_mulVec, hjσ, hjT]
    simp only [add_mulVec, mulVec_add, mulVec_mulVec]
    abel
  have hpq : Jᵀ *ᵥ q = p := by
    rw [← hqp, mulVec_mulVec, ← transpose_mul, h2, transpose_one, one_mulVec]
  have hM : (J * C).IsSymm := by
    have e : C * jᵀ = j * Cᵀ := by
      rw [hjT, hj, Matrix.mul_add, Matrix.add_mul, sub_eq_zero.mp hCD, Matrix.mul_assoc]
    show (J * C)ᵀ = J * C
    calc (J * C)ᵀ = (J * j) * Cᵀ * Jᵀ := by rw [h1, Matrix.one_mul, transpose_mul]
      _ = J * (C * jᵀ) * Jᵀ := by rw [e]; simp only [Matrix.mul_assoc]
      _ = J * C * (J * j)ᵀ := by rw [transpose_mul]; simp only [Matrix.mul_assoc]
      _ = J * C := by rw [h1, transpose_one, Matrix.mul_one]
  have hq1 : ∀ x, q ⬝ᵥ ((J * C) *ᵥ x) = a' ⬝ᵥ x - a ⬝ᵥ (Jᵀ *ᵥ x) := by
    intro x
    have e1 : q ⬝ᵥ ((J * C) *ᵥ x) = p ⬝ᵥ (C *ᵥ x) := by
      rw [← hpq, ← mulVec_mulVec, dotProduct_mulVec, mulVec_transpose]
    have e2 : a' ⬝ᵥ x = a ⬝ᵥ (A *ᵥ x) + b ⬝ᵥ (C *ᵥ x) := by
      rw [ha', add_dotProduct, mulVec_transpose, mulVec_transpose, dotProduct_mulVec,
        dotProduct_mulVec]
    have e3 : (σ *ᵥ a) ⬝ᵥ (C *ᵥ x) = a ⬝ᵥ (σ *ᵥ (C *ᵥ x)) := by
      rw [dot_mulVec_symm hσ, dotProduct_comm]
    rw [e1, e2, ← hA, sub_mulVec, dotProduct_sub, hp, add_dotProduct, e3, mulVec_mulVec]
    ring
  have hz : z + τ *ᵥ a' + b' = z + q := by rw [hq, add_assoc]
  rw [hz]
  refine ⟨by rw [mulVec_add, hpq, hp, add_assoc], ?_⟩
  have e4 := dot_mulVec_symm hM q z
  have e5 := hq1 z
  have e6 := hq1 q
  rw [hpq] at e6
  have e7 : a' ⬝ᵥ q = a' ⬝ᵥ (τ *ᵥ a') + a' ⬝ᵥ b' := by rw [hq, dotProduct_add]
  have e8 : a ⬝ᵥ p = a ⬝ᵥ (σ *ᵥ a) + a ⬝ᵥ b := by rw [hp, dotProduct_add]
  simp only [mulVec_add, add_dotProduct, dotProduct_add]
  rw [e4, e5, e6, e7, e8]
  ring

theorem dvd_mulVec {M : Matrix (Fin g) (Fin g) ℤ} {k : ℤ} (h : ∀ i j, k ∣ M i j) (v : Fin g → ℤ)
    (i : Fin g) : k ∣ (M *ᵥ v) i := by
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.dvd_sum fun j _ => (h i j).mul_right _

theorem dvd_dot_left {k : ℤ} {u : Fin g → ℤ} (h : ∀ i, k ∣ u i) (v : Fin g → ℤ) : k ∣ u ⬝ᵥ v :=
  Finset.dvd_sum fun j _ => (h j).mul_right _

theorem dvd_dot_right {k : ℤ} {v : Fin g → ℤ} (h : ∀ i, k ∣ v i) (u : Fin g → ℤ) : k ∣ u ⬝ᵥ v :=
  Finset.dvd_sum fun j _ => (h j).mul_left _

theorem phase_dvd {γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hγ : γ ∈ Matrix.symplecticGroup (Fin g) ℤ)
    (hB : ∀ i j, (8 : ℤ) ∣ γ.toBlocks₁₂ᵀ i j) (hC : ∀ i j, (8 : ℤ) ∣ γ.toBlocks₂₁ᵀ i j)
    (n n' : Fin g → ℤ) :
    (8 : ℤ) ∣ n ⬝ᵥ n' - (γ.toBlocks₁₁ᵀ *ᵥ n + γ.toBlocks₂₁ᵀ *ᵥ n') ⬝ᵥ
      (γ.toBlocks₁₂ᵀ *ᵥ n + γ.toBlocks₂₂ᵀ *ᵥ n') := by
  have e : (γ.toBlocks₁₁ᵀ *ᵥ n) ⬝ᵥ (γ.toBlocks₂₂ᵀ *ᵥ n') =
      n ⬝ᵥ n' + (γ.toBlocks₁₂ᵀ *ᵥ n) ⬝ᵥ (γ.toBlocks₂₁ᵀ *ᵥ n') := by
    rw [mulVec_transpose, mulVec_transpose γ.toBlocks₁₂, ← dotProduct_mulVec, ← dotProduct_mulVec,
      mulVec_mulVec, mulVec_mulVec, sp_rel_int hγ, add_mulVec, one_mulVec, dotProduct_add]
  have d1 := dvd_dot_left (dvd_mulVec hB n) (γ.toBlocks₂₁ᵀ *ᵥ n')
  have d2 := dvd_dot_right (dvd_mulVec hB n) (γ.toBlocks₁₁ᵀ *ᵥ n)
  have d3 := dvd_dot_left (dvd_mulVec hC n') (γ.toBlocks₁₂ᵀ *ᵥ n + γ.toBlocks₂₂ᵀ *ᵥ n')
  rw [add_dotProduct, dotProduct_add, e]
  omega

theorem half_mulVec (M : Matrix (Fin g) (Fin g) ℤ) (N : Matrix (Fin g) (Fin g) ℤ)
    (n n' : Fin g → ℤ) :
    ofRealVec (halfVec (M *ᵥ n + N *ᵥ n')) =
      M.map (fun x : ℤ => (x : ℂ)) *ᵥ ofRealVec (halfVec n) +
        N.map (fun x : ℤ => (x : ℂ)) *ᵥ ofRealVec (halfVec n') := by
  ext i
  simp [ofRealVec, halfVec, Matrix.mulVec, dotProduct, Finset.sum_div, mul_div_assoc, add_div]

theorem theta_zero_shift_sq (a b : Fin g → ℝ) (z : Fin g → ℂ) {τ : Matrix (Fin g) (Fin g) ℂ}
    (hτ : τ.IsSymm) :
    theta (halfVec 0) (halfVec 0) (z + τ *ᵥ ofRealVec a + ofRealVec b) τ ^ 2 =
      eC (2 * (-(ofRealVec a ⬝ᵥ (τ *ᵥ ofRealVec a)) / 2 - ofRealVec a ⬝ᵥ (z + ofRealVec b))) *
        theta a b z τ ^ 2 := by
  have h0 : halfVec (0 : Fin g → ℤ) = 0 := by ext i; simp [halfVec]
  have h00 : ofRealVec (0 : Fin g → ℝ) = 0 := by ext i; simp [ofRealVec]
  rw [h0, thetaRealTransl_holds (Fin g) 0 0 a b z τ hτ, mul_pow, eC_pow, h00, zero_add, zero_add,
    add_zero]
  norm_num

theorem theta_sq_law_of_zero : ∀ (g : ℕ) (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ), γ ∈ Matrix.symplecticGroup (Fin g) ℤ → (∀ i j, (8 : ℤ) ∣ γ (Sum.inl i) (Sum.inr j) ∧ (8 : ℤ) ∣ γ (Sum.inr i) (Sum.inl j)) → ∀ (c : ℂ) (n n' : Fin g → ℤ), (∀ τ ∈ SiegelH (Fin g), ∀ z : Fin g → ℂ, theta (halfVec 0) (halfVec 0) (zAct γ τ z) (spAct γ τ) ^ 2 = c * (jAut γ τ).det * eC (expArg γ τ z) * theta (halfVec 0) (halfVec 0) z τ ^ 2) → (∀ i, (2 : ℤ) ∣ (γ.toBlocks₁₁ᵀ *ᵥ n) i - n i) ∧ (∀ i, (2 : ℤ) ∣ (γ.toBlocks₂₂ᵀ *ᵥ n') i - n' i) → (∀ τ ∈ SiegelH (Fin g), ∀ z : Fin g → ℂ, theta (halfVec n) (halfVec n') (zAct γ τ z) (spAct γ τ) ^ 2 = c * (jAut γ τ).det * eC (expArg γ τ z) * theta (halfVec n) (halfVec n') z τ ^ 2) := by
  intro g γ hγ h8 c n n' h0 ⟨hn, hn'⟩ τ hτ z
  have hB : ∀ i j, (8 : ℤ) ∣ γ.toBlocks₁₂ᵀ i j := fun i j => (h8 j i).1
  have hC : ∀ i j, (8 : ℤ) ∣ γ.toBlocks₂₁ᵀ i j := fun i j => (h8 j i).2
  have hj := jAut_isUnit hγ hτ
  have hσ := spAct_isSymm hγ hτ.1 hj
  set m := γ.toBlocks₁₁ᵀ *ᵥ n + γ.toBlocks₂₁ᵀ *ᵥ n' with hm
  set m' := γ.toBlocks₁₂ᵀ *ᵥ n + γ.toBlocks₂₂ᵀ *ᵥ n' with hm'
  obtain ⟨k1, k2⟩ := shift_algebra (cMat γ).toBlocks₁₁ (cMat γ).toBlocks₁₂ (cMat γ).toBlocks₂₁
    (cMat γ).toBlocks₂₂ τ (spAct γ τ) (jAut γ τ)⁻¹ hτ.1 hσ (Matrix.nonsing_inv_mul _ hj)
    (Matrix.mul_nonsing_inv _ hj) rfl (sp_A hγ hτ.1 hj) (sp_rel_transpose hγ).2
    (ofRealVec (halfVec n)) (ofRealVec (halfVec n')) z (ofRealVec (halfVec m))
    (ofRealVec (halfVec m')) (half_mulVec _ _ n n') (half_mulVec _ _ n n')
  have h := h0 τ hτ (z + τ *ᵥ ofRealVec (halfVec m) + ofRealVec (halfVec m'))
  have hred : theta (halfVec m) (halfVec m') z τ ^ 2 = theta (halfVec n) (halfVec n') z τ ^ 2 := by
    rw [theta_sq_red m m', theta_sq_red n n']
    have e1 : (fun i => m i % 2) = fun i => n i % 2 := by
      funext i
      have a1 := hn i
      have a2 := dvd_mulVec hC n' i
      simp only [hm, Pi.add_apply]
      omega
    have e2 : (fun i => m' i % 2) = fun i => n' i % 2 := by
      funext i
      have a1 := hn' i
      have a2 := dvd_mulVec hB n i
      simp only [hm', Pi.add_apply]
      omega
    rw [e1, e2]
  obtain ⟨t, ht⟩ := phase_dvd hγ hB hC n n'
  have hph : ofRealVec (halfVec n) ⬝ᵥ ofRealVec (halfVec n') -
      ofRealVec (halfVec m) ⬝ᵥ ofRealVec (halfVec m') = ((2 * t : ℤ) : ℂ) := by
    have ht' : ((n ⬝ᵥ n' : ℤ) : ℂ) - ((m ⬝ᵥ m' : ℤ) : ℂ) = 8 * (t : ℂ) := by exact_mod_cast ht
    simp only [ofRealVec_halfVec, smul_dotProduct, dotProduct_smul, ofIntVec_dot, smul_eq_mul]
    push_cast
    linear_combination (1 / 4 : ℂ) * ht'
  rw [zAct, k1, theta_zero_shift_sq _ _ _ hσ, theta_zero_shift_sq _ _ _ hτ.1, hred, ← mul_assoc,
    mul_assoc (c * _), ← eC_add, expArg, k2, hph, eC_add, eC_add, eC_int, mul_one] at h
  have hne : ∀ x, eC x ≠ 0 := fun x => Complex.exp_ne_zero _
  refine mul_left_cancel₀ (hne _) (h.trans ?_)
  rw [expArg]
  ring

end GlobalTheory.ThetaCharMult
end
end

