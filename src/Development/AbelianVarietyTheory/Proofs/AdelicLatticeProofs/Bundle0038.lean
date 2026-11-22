import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0031
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0026
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0021
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0002
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0033
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0030

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SumHermitianLogGramEqZeroOfEnergyMinimum
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.HarmMin

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {ι : Type} [Fintype ι] [DecidableEq ι]

lemma log_herm {H A : Matrix ι ι ℂ} (h : IsLog H A) : Hᴴ = H := by
  obtain ⟨U, d, -, rfl, -⟩ := h
  have : (diagonal (fun i => (d i : ℂ)))ᴴ = diagonal (fun i => (d i : ℂ)) := by
    rw [diagonal_conjTranspose]; congr 1; ext i; simp
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, this, Matrix.mul_assoc]

lemma log_comm {H A : Matrix ι ι ℂ} (h : IsLog H A) : A * H = H * A := by
  obtain ⟨U, d, hU, rfl, rfl⟩ := h
  have hU' : Uᴴ * U = 1 := mul_eq_one_comm.1 hU
  have e : ∀ Z : Matrix ι ι ℂ, Uᴴ * (U * Z) = Z := fun Z => by rw [← Matrix.mul_assoc, hU', Matrix.one_mul]
  simp only [Matrix.mul_assoc, e]
  congr 1
  simp only [← Matrix.mul_assoc, diagonal_mul_diagonal]
  congr 2
  ext i
  ring

lemma exists_path (X : Matrix ι ι ℂ) (hX : Xᴴ = X) :
    ∃ P Q : ℝ → Matrix ι ι ℂ, P 0 = 1 ∧ Q 0 = 1 ∧ (∀ t, P t * Q t = 1) ∧ (∀ t, (P t)ᴴ = P t) ∧
      (∀ t, (Q t)ᴴ = Q t) ∧ HasDerivAt P X 0 ∧ HasDerivAt Q (-X) 0 := by
  refine ⟨fun t => NormedSpace.exp (t • X), fun t => NormedSpace.exp (t • (-X)), by simp, by simp, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    rw [← Matrix.exp_add_of_commute]
    · simp
    · simp
  · intro t
    rw [← Matrix.exp_conjTranspose]; simp [hX]
  · intro t
    rw [← Matrix.exp_conjTranspose]; simp [hX]
  · have := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
    rw [zero_smul, NormedSpace.exp_zero, one_mul] at this
    exact this
  · have := hasDerivAt_exp_smul_const (𝕂 := ℝ) (-X) (0 : ℝ)
    rw [zero_smul, NormedSpace.exp_zero, one_mul] at this
    exact this

lemma deriv_entry {Y : ℝ → Matrix ι ι ℂ} {D : Matrix ι ι ℂ} (h : HasDerivAt Y D 0) (i j : ι) :
    HasDerivAt (fun t => Y t i j) (D i j) 0 := by
  let L : Matrix ι ι ℂ →ₗ[ℝ] ℂ := Matrix.entryLinearMap ℝ ℂ i j
  exact (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h

lemma deriv_phi {Y : ℝ → Matrix ι ι ℂ} {D : Matrix ι ι ℂ} (h : HasDerivAt Y D 0) (h0 : Y 0 = 0)
    (M : Matrix ι ι ℂ) (C : ℝ) :
    HasDerivAt (fun t => 2 * (Matrix.trace (M * Y t)).re + C * ∑ i, ∑ j, ‖Y t i j‖ ^ 2)
      (2 * (Matrix.trace (M * D)).re) 0 := by
  let L : Matrix ι ι ℂ →ₗ[ℝ] ℝ := Complex.reLm ∘ₗ Matrix.traceLinearMap ι ℝ ℂ
  have h1 : HasDerivAt (fun t => (Matrix.trace (M * Y t)).re) (Matrix.trace (M * D)).re 0 :=
    (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (h.const_mul M)
  have h2 : HasDerivAt (fun t => ∑ i, ∑ j, ‖Y t i j‖ ^ 2) (∑ i : ι, ∑ j : ι, (0 : ℝ)) 0 := by
    refine HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ => ?_
    have := (deriv_entry h i j).norm_sq
    simpa [h0] using this
  have := (h1.const_mul 2).add (h2.const_mul C)
  simp only [Finset.sum_const_zero, mul_zero, add_zero] at this
  exact this

lemma trace_id {g g' H H' X : Matrix ι ι ℂ} (hg : g' * g = 1) (hc : (gᴴ * g) * H = H * (gᴴ * g))
    (hi : g * H = -(H' * g)) :
    Matrix.trace (H * (gᴴ * g)⁻¹ * (-X * (gᴴ * g) + gᴴ * X * g + gᴴ * X * g - (gᴴ * g) * X)) =
      -2 * Matrix.trace (H * X) - 2 * Matrix.trace (H' * X) := by
  have hg2 : g * g' = 1 := mul_eq_one_comm.1 hg
  have hg3 : g'ᴴ * gᴴ = 1 := by rw [← conjTranspose_mul, hg2, conjTranspose_one]
  have hA : (g' * g'ᴴ) * (gᴴ * g) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc g'ᴴ, hg3, Matrix.one_mul, hg]
  have hinv : (gᴴ * g)⁻¹ = g' * g'ᴴ := Matrix.inv_eq_left_inv hA
  have hA' : (gᴴ * g) * (g' * g'ᴴ) = 1 := mul_eq_one_comm.1 hA
  rw [hinv]
  have e1 : Matrix.trace (H * (g' * g'ᴴ) * (X * (gᴴ * g))) = Matrix.trace (H * X) := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc (gᴴ * g) H, hc,
      Matrix.mul_assoc H, hA', Matrix.mul_one]
  have e2 : Matrix.trace (H * (g' * g'ᴴ) * ((gᴴ * g) * X)) = Matrix.trace (H * X) := by
    rw [← Matrix.mul_assoc, Matrix.mul_assoc H, hA, Matrix.mul_one]
  have e3 : Matrix.trace (H * (g' * g'ᴴ) * (gᴴ * X * g)) = - Matrix.trace (H' * X) := by
    have : H * (g' * g'ᴴ) * (gᴴ * X * g) = (H * g' * X) * g := by
      calc _ = H * g' * (g'ᴴ * gᴴ) * X * g := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hg3, Matrix.mul_one]
    rw [this, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hi, Matrix.neg_mul,
      Matrix.mul_assoc H', hg2, Matrix.mul_one, Matrix.neg_mul, Matrix.trace_neg]
  rw [Matrix.neg_mul, Matrix.mul_sub, Matrix.mul_add, Matrix.mul_add, Matrix.mul_neg, Matrix.trace_sub,
    Matrix.trace_add, Matrix.trace_add, Matrix.trace_neg, e1, e2, e3]
  ring

theorem sum_log_eq_zero : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (σ : Type) [Fintype σ] (τ : σ ≃ σ) (g H : σ → Matrix ι ι ℂ), (∀ s, g (τ s) * g s = 1) → (∀ s, IsLog (H s) ((g s)ᴴ * g s)) → (∀ (P' : Matrix ι ι ℂ) (H' : σ → Matrix ι ι ℂ), IsUnit P'.det → (∀ s, IsLog (H' s) ((P' * g s * P'⁻¹)ᴴ * (P' * g s * P'⁻¹))) → ∑ s, (Matrix.trace (H s * H s)).re ≤ ∑ s, (Matrix.trace (H' s * H' s)).re) → ∑ s, H s = 0 := by
  intro ι _ _ σ _ τ g H hτ hH hmin
  set X := ∑ s, H s with hXdef
  have hX : Xᴴ = X := by
    rw [hXdef, conjTranspose_sum]; exact Finset.sum_congr rfl fun s _ => log_herm (hH s)
  obtain ⟨P, Q, hP0, hQ0, hPQ, hPh, hQh, hP, hQ⟩ := exists_path X hX
  choose C δ hδ hC using fun s => GlobalTheory.T.hermitian_log_trace_sq_first_variation_bound ι (H s) _ (hH s)
  let Y : σ → ℝ → Matrix ι ι ℂ := fun s t => Q t * (g s)ᴴ * P t * P t * g s * Q t - (g s)ᴴ * g s
  have hY0 : ∀ s, Y s 0 = 0 := fun s => by simp [Y, hP0, hQ0]
  have hY : ∀ s, HasDerivAt (Y s) (-X * ((g s)ᴴ * g s) + (g s)ᴴ * X * g s + (g s)ᴴ * X * g s
      - ((g s)ᴴ * g s) * X) 0 := by
    intro s
    have := (((((hQ.mul_const (g s)ᴴ).mul hP).mul hP).mul_const (g s)).mul hQ).sub_const ((g s)ᴴ * g s)
    refine HasDerivAt.congr_deriv this ?_
    simp only [Pi.mul_apply, hP0, hQ0]
    noncomm_ring
  have hinv : ∀ t, (P t)⁻¹ = Q t := fun t => Matrix.inv_eq_right_inv (hPQ t)
  have hPu : ∀ t, IsUnit (P t).det := fun t => Matrix.isUnit_det_of_right_inverse (hPQ t)
  have hQu : ∀ t, IsUnit (Q t).det := fun t => Matrix.isUnit_det_of_left_inverse (hPQ t)
  have hA : ∀ s t, (P t * g s * (P t)⁻¹)ᴴ * (P t * g s * (P t)⁻¹) = (g s)ᴴ * g s + Y s t := by
    intro s t
    simp only [hinv, Y, conjTranspose_mul, hPh, hQh, Matrix.mul_assoc]
    abel
  let φ : ℝ → ℝ := fun t => ∑ s, (2 * (Matrix.trace (H s * ((g s)ᴴ * g s)⁻¹ * Y s t)).re
    + C s * ∑ i, ∑ j, ‖Y s t i j‖ ^ 2)
  have hφ := HasDerivAt.fun_sum (u := Finset.univ) fun s _ =>
    deriv_phi (hY s) (hY0 s) (H s * ((g s)ᴴ * g s)⁻¹) (C s)
  have hloc : IsLocalMin φ 0 := by
    have hev : ∀ᶠ t in nhds (0 : ℝ), ∀ s i j, ‖Y s t i j‖ ≤ δ s := by
      simp only [Filter.eventually_all]
      intro s i j
      have hc := (deriv_entry (hY s) i j).continuousAt.norm
      refine hc.eventually (p := fun x => x ≤ δ s) ?_
      refine Filter.Eventually.mono (gt_mem_nhds (a := δ s) ?_) fun x hx => le_of_lt hx
      simp [hY0, hδ]
    filter_upwards [hev] with t ht
    have h0 : φ 0 = 0 := by simp [φ, hY0]
    have hu : ∀ s, IsUnit (P t * g s * (P t)⁻¹).det := fun s => by
      rw [hinv, det_mul, det_mul]
      exact ((hPu t).mul (Matrix.isUnit_det_of_left_inverse (hτ s))).mul (hQu t)
    choose H' hH' using fun s => GlobalTheory.T.exists_isHermitianLogOfPosDef_gram ι _ (hu s)
    have h1 := hmin (P t) H' (hPu t) hH'
    have h2 := Finset.sum_le_sum (s := Finset.univ) fun s _ => hC s (Y s t) (H' s) (ht s) (hA s t ▸ hH' s)
    simp only [add_assoc] at h2
    rw [Finset.sum_add_distrib] at h2
    rw [h0]
    show 0 ≤ ∑ s, _
    linarith
  have hz := hloc.hasDerivAt_eq_zero hφ
  have hid := fun s => trace_id (X := X) (hτ s) (log_comm (hH s))
    (GlobalTheory.T.mul_log_eq_neg_log_mul' ι (g s) (g (τ s)) (H s) (H (τ s)) (hH s) (hH (τ s)) (hτ s))
  simp only [hid] at hz
  have s1 : ∑ s, Matrix.trace (H s * X) = Matrix.trace (X * X) := by
    rw [← Matrix.trace_sum, ← Finset.sum_mul]
  have s2 : ∑ s, Matrix.trace (H (τ s) * X) = Matrix.trace (X * X) := by
    rw [← s1]; exact Equiv.sum_comp τ fun s => Matrix.trace (H s * X)
  rw [← Finset.mul_sum, ← Complex.re_sum, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    s1, s2] at hz
  have hre : (Matrix.trace (X * X)).re = 0 := by
    simp at hz
    linarith
  have hnn : 0 ≤ Matrix.trace (Xᴴ * X) := (Matrix.posSemidef_conjTranspose_mul_self X).trace_nonneg
  refine Matrix.trace_conjTranspose_mul_self_eq_zero_iff.1 ?_
  rw [hX] at hnn ⊢
  exact Complex.ext hre (Complex.le_def.1 hnn).2.symm

end GlobalTheory.ClassFin.HarmMin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryMatrixEqProdQuasiReflections
section
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

namespace GlobalTheory.UnRep.ReflGen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {c : E ≃ₐ[F] E} {n : ℕ} {G : Matrix (Fin n) (Fin n) E}

omit [NumberField F] [NumberField E] in
theorem isUnE_mul {a b : Matrix (Fin n) (Fin n) E} (ha : IsUnE c G a) (hb : IsUnE c G b) :
    IsUnE c G (a * b) := by
  intro x y
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ha, hb]

theorem isUnE_prod (hG : IsHermForm c G) (l : List ((Fin n → E) × E))
    (hl : ∀ p ∈ l, hermE c G p.1 p.1 ≠ 0 ∧ p.2 * c p.2 = 1) :
    IsUnE c G (l.map fun p => refl c G p.1 p.2).prod := by
  induction l with
  | nil => intro x y; simp
  | cons p l ih =>
    rw [List.map_cons, List.prod_cons]
    have hp := hl p List.mem_cons_self
    exact isUnE_mul ((GlobalTheory.T.unitaryQuasiReflection_laws F E c n G hG p.1 hp.1).2.2.2 p.2 hp.2)
      (ih fun q hq => hl q (List.mem_cons_of_mem _ hq))

theorem exists_inv (hG : IsHermForm c G) (l : List ((Fin n → E) × E))
    (hl : ∀ p ∈ l, hermE c G p.1 p.1 ≠ 0 ∧ p.2 * c p.2 = 1) :
    ∃ l' : List ((Fin n → E) × E), (∀ p ∈ l', hermE c G p.1 p.1 ≠ 0 ∧ p.2 * c p.2 = 1) ∧
      (l'.map fun p => refl c G p.1 p.2).prod * (l.map fun p => refl c G p.1 p.2).prod = 1 := by
  induction l with
  | nil => exact ⟨[], by simp, by simp⟩
  | cons p l ih =>
    obtain ⟨l', h1, h2⟩ := ih fun q hq => hl q (List.mem_cons_of_mem _ hq)
    have hp := hl p List.mem_cons_self
    obtain ⟨-, r1, r2, -⟩ := GlobalTheory.T.unitaryQuasiReflection_laws F E c n G hG p.1 hp.1
    refine ⟨l' ++ [(p.1, c p.2)], ?_, ?_⟩
    · intro q hq
      rcases List.mem_append.1 hq with hq | hq
      · exact h1 q hq
      · rw [List.mem_singleton] at hq
        subst hq
        refine ⟨hp.1, ?_⟩
        show c p.2 * c (c p.2) = 1
        rw [hG.1, mul_comm]
        exact hp.2
    · rw [List.map_append, List.prod_append, List.map_cons, List.map_cons, List.prod_cons,
        List.prod_cons, List.map_nil, List.prod_nil, mul_one, mul_assoc,
        ← mul_assoc (refl c G p.1 (c p.2)), r2, mul_comm (c p.2), hp.2, r1, one_mul, h2]

theorem prod_fix (hG : IsHermForm c G) (v : Fin n → E) (l : List ((Fin n → E) × E))
    (hl : ∀ p ∈ l, hermE c G p.1 p.1 ≠ 0 ∧ hermE c G v p.1 = 0) :
    (l.map fun p => refl c G p.1 p.2).prod *ᵥ v = v := by
  induction l with
  | nil => simp
  | cons p l ih =>
    have hp := hl p List.mem_cons_self
    rw [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec,
      ih fun q hq => hl q (List.mem_cons_of_mem _ hq),
      (GlobalTheory.T.unitaryQuasiReflection_laws F E c n G hG p.1 hp.1).1, hp.2]
    simp

omit [NumberField F] [NumberField E] in
theorem herm_span {v x z y : Fin n → E} (hx : hermE c G v x = 0) (hz : hermE c G v z = 0)
    (hy : y ∈ Submodule.span E {x, z}) : hermE c G v y = 0 := by
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hy
  have : hermE c G v (a • x + b • z) = c a * hermE c G v x + c b * hermE c G v z := by
    simp only [hermE, Finset.mul_sum, ← Finset.sum_add_distrib, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, map_add, map_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [this, hx, hz]
  simp

theorem exists_fix (hG : IsHermForm c G) {γ : Matrix (Fin n) (Fin n) E} (hγ : IsUnE c G γ)
    (x : Fin n → Fin n → E) (h1 : ∀ i, hermE c G (x i) (x i) ≠ 0)
    (h2 : ∀ i j, i ≠ j → hermE c G (x i) (x j) = 0) (k : ℕ) :
    ∃ l : List ((Fin n → E) × E), (∀ p ∈ l, hermE c G p.1 p.1 ≠ 0 ∧ p.2 * c p.2 = 1) ∧
      ∀ i : Fin n, i.val < k → ((l.map fun p => refl c G p.1 p.2).prod * γ) *ᵥ x i = x i := by
  induction k with
  | zero => exact ⟨[], by simp, by simp⟩
  | succ k ih =>
    obtain ⟨l, hl, hfix⟩ := ih
    by_cases hk : k < n
    · have hU := isUnE_mul (isUnE_prod hG l hl) hγ
      set δ := (l.map fun p => refl c G p.1 p.2).prod * γ with hδ
      obtain ⟨m, hm, hmx⟩ := GlobalTheory.T.exists_quasiReflection_prod_mulVec_eq F E c n G hG (x ⟨k, hk⟩) (δ *ᵥ x ⟨k, hk⟩) (h1 _) (hU _ _)
      refine ⟨m ++ l, ?_, ?_⟩
      · intro p hp
        rcases List.mem_append.1 hp with hp | hp
        · exact ⟨(hm p hp).1, (hm p hp).2.1⟩
        · exact hl p hp
      · intro i hi
        rw [List.map_append, List.prod_append, mul_assoc, ← hδ, ← Matrix.mulVec_mulVec]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
        · have hne : i ≠ ⟨k, hk⟩ := fun h => by simp [h] at hi
          rw [hfix i hi]
          refine prod_fix hG _ m fun p hp => ⟨(hm p hp).1, herm_span (h2 _ _ hne) ?_ (hm p hp).2.2⟩
          rw [← h2 _ _ hne, ← hU (x i) (x ⟨k, hk⟩), hfix i hi]
        · have : i = ⟨k, hk⟩ := Fin.ext hi
          rw [this]
          exact hmx
    · exact ⟨l, hl, fun i _ => hfix i (lt_of_lt_of_le i.2 (not_lt.1 hk))⟩

end GlobalTheory.UnRep.ReflGen

theorem GlobalTheory.UnRep.isUnE_eq_prod_refl : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G → ∀ γ, IsUnE c G γ → ∃ l : List ((Fin n → E) × E), (∀ p ∈ l, hermE c G p.1 p.1 ≠ 0 ∧ p.2 * c p.2 = 1) ∧ γ = (l.map fun p => refl c G p.1 p.2).prod := by
  intro F E _ _ _ _ _ c n G hG γ hγ
  obtain ⟨x, h1, h2, h3⟩ := GlobalTheory.T.exists_anisotropic_orthogonal_basis_hermitian F E c n G hG
  obtain ⟨l, hl, hfix⟩ := ReflGen.exists_fix hG hγ x h1 h2 n
  obtain ⟨l', hl', hinv⟩ := ReflGen.exists_inv hG l hl
  refine ⟨l', hl', ?_⟩
  have hone : (l.map fun p => refl c G p.1 p.2).prod * γ = 1 := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext_on_range h3 fun i => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hfix i i.2, Matrix.one_mulVec]
  rw [← one_mul γ, ← hinv, mul_assoc, hone, mul_one]
end

