import Mathlib

-- bundled from ReciprocityTheory.SemistableReduction.SemiContractA
section
namespace ReciprocityTheory.MultiplicativeHeights

open Matrix
open scoped ComplexOrder

private theorem one_lt_re_det_one_add_and_im_eq_zero_of_posDef {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]
    {Q : Matrix m m ℂ} (hQ : Q.PosDef) : 1 < ((1 + Q).det).re ∧ ((1 + Q).det).im = 0 := by
  have hsp := hQ.isHermitian.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hsp
  obtain ⟨U, hU⟩ : ∃ U : Matrix m m ℂ, U = (hQ.isHermitian.eigenvectorUnitary : Matrix m m ℂ) :=
    ⟨_, rfl⟩
  have hUU : U * star U = 1 := by
    rw [hU]
    exact Matrix.mem_unitaryGroup_iff.mp hQ.isHermitian.eigenvectorUnitary.2
  obtain ⟨d, hd⟩ : ∃ d : m → ℝ, d = hQ.isHermitian.eigenvalues := ⟨_, rfl⟩
  have hdpos : ∀ i, 0 < d i := fun i => by rw [hd]; exact hQ.eigenvalues_pos i
  rw [← hU, ← hd] at hsp

  have h1 : 1 + Q = U * (1 + diagonal (RCLike.ofReal ∘ d)) * star U := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hUU, ← hsp]
  have hdet : (1 + Q).det = ((∏ i, (1 + d i) : ℝ) : ℂ) := by
    rw [h1, det_mul, det_mul, mul_comm U.det, mul_assoc, ← det_mul, hUU, det_one, mul_one,
      ← diagonal_one, diagonal_add, det_diagonal]
    push_cast
    rfl
  rw [hdet, Complex.ofReal_re, Complex.ofReal_im]
  refine ⟨?_, rfl⟩
  calc (1 : ℝ) = ∏ _i : m, (1 : ℝ) := by simp
    _ < ∏ i, (1 + d i) := Finset.prod_lt_prod_of_nonempty (fun _ _ => one_pos)
        (fun i _ => by linarith [hdpos i]) Finset.univ_nonempty

theorem sc_one_add_det {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]
    {Q : Matrix m m ℂ} (hQ : Q.PosDef) : 1 < ((1 + Q).det).re := by
  exact (one_lt_re_det_one_add_and_im_eq_zero_of_posDef hQ).1

theorem sc_det_lt {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]
    {E S : Matrix m m ℂ} (hE : E.PosDef) (hSE : (S - E).PosDef) :
    0 < (E.det).re ∧ (E.det).re < (S.det).re := by
  have hEdet := hE.det_pos
  rw [Complex.lt_def] at hEdet
  simp only [Complex.zero_re, Complex.zero_im] at hEdet

  have hsp := hE.isHermitian.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hsp
  obtain ⟨U, hU⟩ : ∃ U : Matrix m m ℂ, U = (hE.isHermitian.eigenvectorUnitary : Matrix m m ℂ) :=
    ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : m → ℝ, d = hE.isHermitian.eigenvalues := ⟨_, rfl⟩
  have hdpos : ∀ i, 0 < d i := fun i => by rw [hd]; exact hE.eigenvalues_pos i
  rw [← hU, ← hd] at hsp
  obtain ⟨Dh, hDh⟩ : ∃ Dh : Matrix m m ℂ, Dh = diagonal (fun i => ((Real.sqrt (d i) : ℝ) : ℂ)) :=
    ⟨_, rfl⟩
  have hDD : Dh * Dh = diagonal (RCLike.ofReal ∘ d) := by
    rw [hDh, diagonal_mul_diagonal]
    congr 1
    funext i
    simp only [Function.comp_apply]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hdpos i).le]
    rfl
  have hDhH : Dhᴴ = Dh := by
    rw [hDh, diagonal_conjTranspose]
    congr 1
    funext i
    simp
  obtain ⟨B, hB⟩ : ∃ B : Matrix m m ℂ, B = Dh * star U := ⟨_, rfl⟩
  have hBB : Bᴴ * B = E := by
    rw [hB, conjTranspose_mul, hDhH, hsp, ← hDD]
    simp only [Matrix.mul_assoc, star_eq_conjTranspose, conjTranspose_conjTranspose]
  have hBdet : B.det ≠ 0 := by
    intro h0
    have h1 : E.det = 0 := by rw [← hBB, det_mul, h0, mul_zero]
    rw [h1] at hEdet
    simp at hEdet
  have hBu : IsUnit B.det := isUnit_iff_ne_zero.mpr hBdet
  have hinj : Function.Injective (B⁻¹).mulVec := by
    intro v w hvw
    have h := congrArg (fun z => B *ᵥ z) hvw
    simpa [mulVec_mulVec, mul_nonsing_inv B hBu] using h
  have hQ : ((B⁻¹)ᴴ * (S - E) * B⁻¹).PosDef := hSE.conjTranspose_mul_mul_same hinj
  have hS : Bᴴ * (1 + (B⁻¹)ᴴ * (S - E) * B⁻¹) * B = S := by
    have hinv : B⁻¹ * B = 1 := nonsing_inv_mul B hBu
    have e1 : Bᴴ * ((B⁻¹)ᴴ * (S - E) * B⁻¹) * B = (B⁻¹ * B)ᴴ * (S - E) * (B⁻¹ * B) := by
      rw [conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hBB, e1, hinv, conjTranspose_one,
      Matrix.one_mul, Matrix.mul_one]
    abel
  generalize (B⁻¹)ᴴ * (S - E) * B⁻¹ = Q at hQ hS
  have hdet : S.det = (1 + Q).det * E.det := by
    rw [← hS, det_mul, det_mul, ← hBB, det_mul]
    ring
  obtain ⟨hq1, hq2⟩ := one_lt_re_det_one_add_and_im_eq_zero_of_posDef hQ
  refine ⟨hEdet.1, ?_⟩
  rw [hdet, Complex.mul_re, hq2, ← hEdet.2]
  nlinarith [hEdet.1, hq1]

theorem sc_schur_posDef {k m : Type*} [Fintype k] [Fintype m] [DecidableEq k]
    {A : Matrix k k ℂ} (B : Matrix k m ℂ) (D : Matrix m m ℂ) (hA : A.PosDef)
    (h : (fromBlocks A B Bᴴ D).PosDef) : (D - Bᴴ * A⁻¹ * B).PosDef := by
  classical
  have hAu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA.det_pos.ne'
  obtain ⟨N, hN⟩ : ∃ N : Matrix (k ⊕ m) m ℂ, N = fromRows (-(A⁻¹ * B)) 1 := ⟨_, rfl⟩
  have hinj : Function.Injective N.mulVec := by
    intro v w hvw
    funext i
    have h1 := congrFun hvw (Sum.inr i)
    simpa [hN, fromRows_mulVec] using h1
  have hAA : A * A⁻¹ = 1 := mul_nonsing_inv A hAu
  have h1 : A * (-(A⁻¹ * B)) + B * (1 : Matrix m m ℂ) = 0 := by
    rw [Matrix.mul_neg, ← Matrix.mul_assoc, hAA, Matrix.one_mul, Matrix.mul_one, neg_add_cancel]
  have h2 : Bᴴ * (-(A⁻¹ * B)) + D * (1 : Matrix m m ℂ) = D - Bᴴ * A⁻¹ * B := by
    rw [Matrix.mul_neg, Matrix.mul_one, ← Matrix.mul_assoc]
    abel
  have key : Nᴴ * fromBlocks A B Bᴴ D * N = D - Bᴴ * A⁻¹ * B := by
    rw [hN, conjTranspose_fromRows_eq_fromCols_conjTranspose, ← fromRows_fromCols_eq_fromBlocks,
      fromCols_mul_fromRows, Matrix.add_mul]
    simp only [Matrix.mul_assoc]
    rw [fromCols_mul_fromRows, fromCols_mul_fromRows, h1, h2, Matrix.mul_zero, zero_add,
      conjTranspose_one, Matrix.one_mul, Matrix.mul_assoc]
  have hpd := h.conjTranspose_mul_mul_same hinj
  rwa [key] at hpd

theorem sc_quad_mul {r : Type*} [Fintype r] (H M : Matrix r r ℂ) (u : r → ℂ) :
    star u ⬝ᵥ ((Mᴴ * H * M) *ᵥ u) = star (M *ᵥ u) ⬝ᵥ (H *ᵥ (M *ᵥ u)) := by
  rw [star_mulVec, ← dotProduct_mulVec]
  simp only [mulVec_mulVec, Matrix.mul_assoc]

theorem sc_contr_posDef {r : Type*} [Fintype r] {H M : Matrix r r ℂ} (hH : H.PosDef)
    (hM : ∀ u : r → ℂ, u ≠ 0 → (star (M *ᵥ u) ⬝ᵥ (H *ᵥ (M *ᵥ u))).re < (star u ⬝ᵥ (H *ᵥ u)).re) :
    (H - Mᴴ * H * M).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos
    (hH.isHermitian.sub (isHermitian_conjTranspose_mul_mul M hH.isHermitian)) ?_
  intro x hx
  rw [sub_mulVec, dotProduct_sub, sc_quad_mul]
  have h1 : (star x ⬝ᵥ (H *ᵥ x)).im = 0 := hH.isHermitian.im_star_dotProduct_mulVec_self x
  have h2 : (star (M *ᵥ x) ⬝ᵥ (H *ᵥ (M *ᵥ x))).im = 0 :=
    hH.isHermitian.im_star_dotProduct_mulVec_self (M *ᵥ x)
  have h3 := hM x hx
  rw [Complex.lt_def, Complex.sub_re, Complex.sub_im, h1, h2, Complex.zero_re, Complex.zero_im]
  exact ⟨by linarith, by ring⟩

theorem sc_sigma {r k m : Type*} [Fintype r] [Fintype k] [Fintype m] [DecidableEq k]
    [DecidableEq m] [Nonempty m] {H M : Matrix r r ℂ} (hH : H.PosDef)
    (hM : ∀ u : r → ℂ, u ≠ 0 → (star (M *ᵥ u) ⬝ᵥ (H *ᵥ (M *ᵥ u))).re < (star u ⬝ᵥ (H *ᵥ u)).re)
    (Bm : Matrix r k ℂ) (Cm : Matrix r m ℂ) (hW : Function.Injective (fromCols Bm Cm).mulVec)
    (hMB : M * Bm = 0) (hMC : Function.Injective (M * Cm).mulVec) :
    0 < ((M * Cm)ᴴ * H * (M * Cm)).det.re ∧ ((M * Cm)ᴴ * H * (M * Cm)).det.re <
      (Cmᴴ * H * Cm - (Cmᴴ * H * Bm) * (Bmᴴ * H * Bm)⁻¹ * (Bmᴴ * H * Cm)).det.re := by
  have hBinj : Function.Injective Bm.mulVec := by
    intro v w hvw
    have h : (fromCols Bm Cm) *ᵥ (Sum.elim v 0) = (fromCols Bm Cm) *ᵥ (Sum.elim w 0) := by
      rw [fromCols_mulVec, fromCols_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inl,
        Sum.elim_comp_inr, Sum.elim_comp_inr, hvw]
    have h' := hW h
    funext i
    exact congrFun h' (Sum.inl i)
  obtain ⟨A, hAdef⟩ : ∃ A : Matrix k k ℂ, A = Bmᴴ * H * Bm := ⟨_, rfl⟩
  have hA : A.PosDef := by rw [hAdef]; exact hH.conjTranspose_mul_mul_same hBinj
  have hAu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA.det_pos.ne'
  obtain ⟨G, hG⟩ : ∃ G : Matrix k m ℂ, G = A⁻¹ * (Bmᴴ * H * Cm) := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : Matrix r m ℂ, N = Cm - Bm * G := ⟨_, rfl⟩
  have hNW : ∀ v, N *ᵥ v = (fromCols Bm Cm) *ᵥ (Sum.elim (-(G *ᵥ v)) v) := by
    intro v
    rw [hN, fromCols_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, sub_mulVec, mulVec_neg,
      mulVec_mulVec]
    abel
  have hNinj : Function.Injective N.mulVec := by
    intro v w hvw
    rw [hNW, hNW] at hvw
    have h := hW hvw
    funext i
    exact congrFun h (Sum.inr i)
  have hGA : A * G = Bmᴴ * H * Cm := by
    rw [hG, ← Matrix.mul_assoc, mul_nonsing_inv A hAu, Matrix.one_mul]
  have hx : Gᴴ * (Bmᴴ * (H * (Bm * G))) = Gᴴ * (Bmᴴ * (H * Cm)) := by
    have h := congrArg (fun X => Gᴴ * X) hGA
    simpa [hAdef, Matrix.mul_assoc] using h

  have key : Nᴴ * H * N = Cmᴴ * H * Cm - Cmᴴ * H * Bm * G := by
    rw [hN, conjTranspose_sub, conjTranspose_mul]
    simp only [Matrix.mul_assoc, Matrix.sub_mul, Matrix.mul_sub]
    rw [hx]
    abel
  have hT : Cmᴴ * H * Cm - (Cmᴴ * H * Bm) * (Bmᴴ * H * Bm)⁻¹ * (Bmᴴ * H * Cm) =
      Cmᴴ * H * Cm - Cmᴴ * H * Bm * G := by
    rw [hG, ← hAdef]
    simp only [Matrix.mul_assoc]
  have hMN : M * N = M * Cm := by
    rw [hN, Matrix.mul_sub, ← Matrix.mul_assoc, hMB, Matrix.zero_mul, sub_zero]
  have hdiff : (Cmᴴ * H * Cm - (Cmᴴ * H * Bm) * (Bmᴴ * H * Bm)⁻¹ * (Bmᴴ * H * Cm)) -
      (M * Cm)ᴴ * H * (M * Cm) = Nᴴ * (H - Mᴴ * H * M) * N := by
    rw [hT, ← key, ← hMN, conjTranspose_mul]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  have hpd := (sc_contr_posDef hH hM).conjTranspose_mul_mul_same hNinj
  refine sc_det_lt (hH.conjTranspose_mul_mul_same hMC) ?_
  rw [hdiff]
  exact hpd

end ReciprocityTheory.MultiplicativeHeights
end

-- bundled from ReciprocityTheory.SemistableReduction.TorsionNonvanishStatement
section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

def triChar {p : ℕ} (a : Fin p → ℕ) (b : Matrix (Fin p) (Fin p) ℂ) : ℂ :=
  ∏ i, b i i ^ a i

def IsTriEquivariant {p : ℕ} (a : Fin p → ℕ) (P : Matrix (Fin p) (Fin p) ℂ → ℂ) : Prop :=
  ∀ x b : Matrix (Fin p) (Fin p) ℂ, x.det ≠ 0 → b.det ≠ 0 → b.BlockTriangular id →
    P (x * b) = triChar a b * P x

def colNormSq {p : ℕ} (x : Matrix (Fin p) (Fin p) ℂ) (j : Fin p) : ℝ :=
  ∑ i, ‖x i j‖ ^ 2

def LemmaHStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (p : ι → ℕ) (a : ∀ s, Fin (p s) → ℕ)
    (P : (∀ s, Matrix (Fin (p s)) (Fin (p s)) ℂ) → ℂ) (C R : ℝ),
    (∀ (x : ∀ s, Matrix (Fin (p s)) (Fin (p s)) ℂ) (s : ι) (b : Matrix (Fin (p s)) (Fin (p s)) ℂ),
      (∀ t, (x t).det ≠ 0) → b.det ≠ 0 → b.BlockTriangular id →
      P (Function.update x s (x s * b)) = triChar (a s) b * P x) →
    (∀ k : ∀ s, Matrix (Fin (p s)) (Fin (p s)) ℂ,
      (∀ s, k s ∈ Matrix.unitaryGroup (Fin (p s)) ℂ) → ‖P k‖ ≤ C) → 0 ≤ R →
    ∀ x : ∀ s, Matrix (Fin (p s)) (Fin (p s)) ℂ, (∀ s, (x s).det ≠ 0) →
      (∀ s j, colNormSq (x s) j ≤ R ^ 2) → ‖P x‖ ≤ C * R ^ (∑ s, ∑ i, a s i)

def BalancedSchwarzStatement : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (s : Set E) (g : E → ℂ) (M : ℝ),
    IsOpen s → Balanced ℂ s → DifferentiableOn ℂ g s → (∀ w ∈ s, ‖g w‖ ≤ M) →
    ∀ z ∈ s, ‖g z - g 0‖ ≤ (M + ‖g 0‖) * gauge s z

def TorsionNonvanishStatement : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (θ : V → ℂ) (Λ : AddSubgroup V) (ρ : ℝ) (n : ℕ),
    Differentiable ℂ θ → (∃ z, θ z ≠ 0) →
    (∀ l ∈ Λ, ∀ z, ‖θ (z + l)‖ * Real.exp (-(Real.pi / 2) * ‖z + l‖ ^ 2) =
      ‖θ z‖ * Real.exp (-(Real.pi / 2) * ‖z‖ ^ 2)) →
    (∀ v : V, ∃ l ∈ Λ, ‖v - l‖ ≤ ρ) → 5 * ρ < n →
    ∃ l ∈ Λ, θ ((n : ℂ)⁻¹ • l) ≠ 0

def sgn (p : ℕ) {r : ℕ} (k : Fin r) : ℂ := if (k : ℕ) < p then 1 else -1

def jForm (p : ℕ) {r : ℕ} (x y : Fin r → ℂ) : ℂ :=
  ∑ k, sgn p k * (conj (x k) * y k)

def normSq {r : ℕ} (u : Fin r → ℂ) : ℝ := ∑ k, ‖u k‖ ^ 2

def posSq (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : ℝ :=
  ∑ k : Fin r, if (k : ℕ) < p then ‖u k‖ ^ 2 else 0

def negSq (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : ℝ :=
  ∑ k : Fin r, if (k : ℕ) < p then 0 else ‖u k‖ ^ 2

def approxR (r : ℕ) (μ ρ : ℝ) : ℝ := 4 * Real.sqrt r * μ / ρ

def ApproxGraphStatement : Prop :=
  ∀ (r p : ℕ) (μ ρ : ℝ) (X : Fin r → Fin r → ℂ), p ≤ r → 0 < μ → 0 < ρ → ρ ≤ 1 →
    (∀ j : Fin r, (j : ℕ) < p →
      normSq (X j - (approxR r μ ρ : ℂ) • (Pi.single j 1 : Fin r → ℂ)) ≤ μ ^ 2) →
    (∀ w : Fin r → ℂ, (∀ j : Fin r, p ≤ (j : ℕ) → w j = 0) →
      negSq p (∑ j, w j • X j) ≤ (ρ / 3) ^ 2 * posSq p (∑ j, w j • X j) ∧
      (w ≠ 0 → 0 < posSq p (∑ j, w j • X j))) ∧
    (∀ y : Fin r → ℂ, (∀ j : Fin r, (j : ℕ) < p → jForm p (X j) y = 0) → y ≠ 0 →
      (jForm p y y).re < 0) ∧
    (∀ v y : Fin r → ℂ, (∀ j : Fin r, (j : ℕ) < p → jForm p (X j) y = 0) →
      v - y ∈ Submodule.span ℂ (X '' {j | (j : ℕ) < p}) →
      ‖jForm p y y‖ ≤ 2 * normSq v)

structure HermForm (K : Type) [Field K] [NumberField K] (r : ℕ) where

  c : K →+* K
  c_invol : ∀ x, c (c x) = x
  c_emb : ∀ (σ : K →+* ℂ) (x : K), σ (c x) = conj (σ x)

  G : Matrix (Fin r) (Fin r) K
  G_herm : ∀ a b, c (G a b) = G b a

def HermForm.h {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) (x y : Fin r → K) : K :=
  ∑ a, ∑ b, S.c (x a) * S.G a b * y b

def embVec {K : Type} [Field K] [NumberField K] {r : ℕ} (σ : K →+* ℂ) (x : Fin r → K) : Fin r → ℂ := fun a => σ (x a)

def IsIntegralElt {K : Type} [Field K] [NumberField K] (x : K) : Prop := ∃ z : 𝓞 K, (z : K) = x

def IsLattice {K : Type} [Field K] [NumberField K] {r : ℕ} (L : Submodule (𝓞 K) (Fin r → K)) : Prop :=
  L.FG ∧ Submodule.span K (L : Set (Fin r → K)) = ⊤

def IsIntegralOn {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) (L : Submodule (𝓞 K) (Fin r → K)) : Prop :=
  ∀ x ∈ L, ∀ y ∈ L, IsIntegralElt (S.h x y)

def IsSelfDual {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) (L : Submodule (𝓞 K) (Fin r → K)) : Prop :=
  IsIntegralOn S L ∧ ∀ x, (∀ y ∈ L, IsIntegralElt (S.h x y)) → x ∈ L

def majSq {K : Type} [Field K] [NumberField K] {r : ℕ} {ι : Type} [Fintype ι] (σ : ι → K →+* ℂ) (Q : ι → Matrix (Fin r) (Fin r) ℂ)
    (v : Fin r → K) : ℝ :=
  ∑ i, normSq (Q i *ᵥ embVec (σ i) v)

def ApproxStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] [Nonempty ι] (r p : ℕ)
    (S : HermForm K r) (σ : ι → K →+* ℂ) (Q : ι → Matrix (Fin r) (Fin r) ℂ)
    (L : Submodule (𝓞 K) (Fin r → K)) (v : Fin r → Fin r → K) (μ ρ : ℝ),
    p ≤ r → 0 < μ → 0 < ρ → ρ ≤ 1 → (∀ i, (Q i).det ≠ 0) →
    (∀ i x y, σ i (S.h x y) = jForm p (Q i *ᵥ embVec (σ i) x) (Q i *ᵥ embVec (σ i) y)) →
    IsIntegralOn S L →
    (∀ w : ι → Fin r → ℂ, ∃ l ∈ L, ∑ i, normSq (Q i *ᵥ embVec (σ i) l - w i) ≤ μ ^ 2) →
    (∀ j, v j ∈ L) → LinearIndependent K v → (∀ j, majSq σ Q (v j) ≤ μ ^ 2) →
    ∃ la : Fin r → Fin r → K, (∀ j, la j ∈ L) ∧ LinearIndependent K la ∧
      (∀ j k : Fin r, (j : ℕ) < p → p ≤ (k : ℕ) → S.h (la j) (la k) = 0) ∧
      (∀ i (w : Fin r → ℂ), (∀ j : Fin r, p ≤ (j : ℕ) → w j = 0) →
        negSq p (Q i *ᵥ ∑ j, w j • embVec (σ i) (la j)) ≤
          (ρ / 3) ^ 2 * posSq p (Q i *ᵥ ∑ j, w j • embVec (σ i) (la j)) ∧
        (w ≠ 0 → 0 < (jForm p (Q i *ᵥ ∑ j, w j • embVec (σ i) (la j))
          (Q i *ᵥ ∑ j, w j • embVec (σ i) (la j))).re)) ∧
      (∀ i (w : Fin r → ℂ), (∀ j : Fin r, (j : ℕ) < p → w j = 0) → w ≠ 0 →
        (jForm p (Q i *ᵥ ∑ j, w j • embVec (σ i) (la j))
          (Q i *ᵥ ∑ j, w j • embVec (σ i) (la j))).re < 0) ∧
      (∀ i (j : Fin r), (j : ℕ) < p → ‖σ i (S.h (la j) (la j))‖ ≤ (2 * approxR r μ ρ) ^ 2) ∧
      (∀ i (j : Fin r), p ≤ (j : ℕ) →
        ‖σ i (S.h (la j) (la j))‖ ≤ (2 * approxR r μ ρ) ^ (4 * p) * (2 * μ ^ 2))

def OnePolyGrowthStatement : Prop :=
  ∀ (f : ℂ → ℂ) (B : Set ℂ) (A : ℝ) (k : ℕ), B.Finite → DifferentiableOn ℂ f Bᶜ →
    (∀ t ∉ B, ‖f t‖ ≤ A * (1 + ‖t‖) ^ k) →
    ∃ P : Polynomial ℂ, P.natDegree ≤ k ∧ ∀ t ∉ B, f t = P.eval t

def IsHoloGL {p : ℕ} (P : Matrix (Fin p) (Fin p) ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ (fun y : Fin p → Fin p → ℂ => P (Matrix.of y)) {y | (Matrix.of y).det ≠ 0}

def IsBW {p : ℕ} (a : Fin p → ℕ) (P : Matrix (Fin p) (Fin p) ℂ → ℂ) : Prop :=
  IsHoloGL P ∧ IsTriEquivariant a P ∧ ∀ x : Matrix (Fin p) (Fin p) ℂ, x.det = 0 → P x = 0

def leadMinor {p : ℕ} (x : Matrix (Fin p) (Fin p) ℂ) (i : Fin p) : ℂ :=
  (Matrix.of fun a b : Fin (i + 1) => x (Fin.castLE i.isLt a) (Fin.castLE i.isLt b)).det

def nextExp {p : ℕ} (a : Fin p → ℕ) (i : Fin p) : ℕ :=
  if h : (i : ℕ) + 1 < p then a ⟨i + 1, h⟩ else 0

def minorProd {p : ℕ} (a : Fin p → ℕ) (x : Matrix (Fin p) (Fin p) ℂ) : ℂ :=
  if x.det = 0 then 0 else ∏ i, leadMinor x i ^ (a i - nextExp a i)

def BWPolyStatement : Prop :=
  ∀ (p : ℕ) (a : Fin p → ℕ) (P : Matrix (Fin p) (Fin p) ℂ → ℂ), IsHoloGL P →
    IsTriEquivariant a P →
    ∃ F : MvPolynomial (Fin p × Fin p) ℂ, F.IsHomogeneous (∑ i, a i) ∧
      ∀ x : Matrix (Fin p) (Fin p) ℂ, x.det ≠ 0 → P x = MvPolynomial.eval (fun ij => x ij.1 ij.2) F

def BWIrredStatement : Prop :=
  ∀ (p : ℕ) (a : Fin p → ℕ),
    (Antitone a → IsBW a (minorProd a)) ∧
    ∀ S : Submodule ℂ (Matrix (Fin p) (Fin p) ℂ → ℂ), (∀ P ∈ S, IsBW a P) →
      (∀ g : Matrix (Fin p) (Fin p) ℂ, g.det ≠ 0 → ∀ P ∈ S, (fun x => P (g * x)) ∈ S) →
      S ≠ ⊥ → ∀ P, IsBW a P → P ∈ S

end ReciprocityTheory.MultiplicativeHeights
end
end

-- bundled from ReciprocityTheory.SemistableReduction.UnipotentA
section
namespace ReciprocityTheory.MultiplicativeHeights

open Polynomial Matrix

theorem unip_trace_aeval_zero {K : Type*} [Field K] {r : ℕ} (N : Matrix (Fin r) (Fin r) K)
    (hN : ∀ k, 1 ≤ k → k ≤ r → (N ^ k).trace = 0) (P : K[X]) (hP : P.natDegree ≤ r) :
    (aeval N P).trace = P.coeff 0 * r := by
  rw [Polynomial.aeval_eq_sum_range, Matrix.trace_sum, Finset.sum_range_succ', Finset.sum_eq_zero]
  · simp [Matrix.trace_one]
  · intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [Matrix.trace_smul, hN (i + 1) (by omega) (by omega), smul_zero]

theorem unip_idem_eq_zero {K : Type*} [Field K] [CharZero K] {r : ℕ} (E : Matrix (Fin r) (Fin r) K)
    (hE : E * E = E) (ht : E.trace = 0) : E = 0 := by
  set f := Matrix.toLin' E with hfdef
  have hf : LinearMap.IsProj (LinearMap.range f) f := by
    constructor
    · intro x
      exact LinearMap.mem_range_self f x
    · intro x hx
      obtain ⟨y, rfl⟩ := hx
      simp only [hfdef, Matrix.toLin'_apply, Matrix.mulVec_mulVec, hE]
  have htr : LinearMap.trace K _ f = E.trace := by
    rw [LinearMap.trace_eq_matrix_trace K (Pi.basisFun K (Fin r)),
      LinearMap.toMatrix_eq_toMatrix', hfdef, LinearMap.toMatrix'_toLin']
  have h0 : ((Module.finrank K (LinearMap.range f) : ℕ) : K) = 0 := by
    rw [← hf.trace, htr, ht]
  have h1 : Module.finrank K (LinearMap.range f) = 0 := by exact_mod_cast h0
  have h2 : LinearMap.range f = ⊥ := Submodule.finrank_eq_zero.mp h1
  have h3 : f = 0 := LinearMap.range_eq_bot.mp h2
  exact Matrix.toLin'.injective (h3.trans (map_zero _).symm)

theorem unip_pow_card_eq_zero {K : Type*} [Field K] [CharZero K] {r : ℕ} (N : Matrix (Fin r) (Fin r) K)
    (hN : ∀ k, 1 ≤ k → k ≤ r → (N ^ k).trace = 0) : N ^ r = 0 := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    exact Subsingleton.elim _ _
  have hint : IsIntegral K N := IsIntegral.of_finite K N
  set m := minpoly K N with hm
  have hmon : m.Monic := minpoly.monic hint
  have hm0 : aeval N m = 0 := minpoly.aeval K N
  have hmdeg : m.natDegree ≤ r := by
    have h2 := Polynomial.natDegree_le_of_dvd (Matrix.minpoly_dvd_charpoly N)
      (Matrix.charpoly_monic N).ne_zero
    rwa [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at h2
  have hrK : (r : K) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  have hmc : m.coeff 0 = 0 := by
    have h := unip_trace_aeval_zero N hN m hmdeg
    rw [hm0, Matrix.trace_zero] at h
    exact (mul_eq_zero.mp h.symm).resolve_right hrK
  have hXm : X ∣ m := Polynomial.X_dvd_iff.mpr hmc
  obtain ⟨q, hq, hXq⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd m hmon.ne_zero 0
  simp only [map_zero, sub_zero] at hq hXq
  set k := m.rootMultiplicity 0 with hkdef
  have hk : 1 ≤ k := by
    by_contra h
    have hk0 : k = 0 := by omega
    rw [hk0, pow_zero, one_mul] at hq
    exact hXq (hq ▸ hXm)
  have hcop : IsCoprime (X ^ k) q :=
    ((Polynomial.irreducible_X.coprime_iff_not_dvd).mpr hXq).pow_left
  obtain ⟨u, v, huv⟩ := hcop
  obtain ⟨P, hP⟩ : ∃ P : K[X], P = u * X ^ k := ⟨_, rfl⟩
  have hPP : aeval N P * aeval N P = aeval N P := by
    have hsub : P - 1 = -(v * q) := by rw [hP, ← huv]; ring
    have hfac : P * P - P = -(u * v) * m := by
      calc P * P - P = P * (P - 1) := by ring
        _ = -(u * v) * (X ^ k * q) := by rw [hsub, hP]; ring
        _ = -(u * v) * m := by rw [← hq]
    have h := congrArg (aeval N) hfac
    rw [map_sub, map_mul, map_mul, hm0, mul_zero] at h
    exact sub_eq_zero.mp h
  obtain ⟨P', hP'⟩ : ∃ P' : K[X], P' = P %ₘ m := ⟨_, rfl⟩
  have hdiv : P' + m * (P /ₘ m) = P := by
    rw [hP']
    first
      | exact Polynomial.modByMonic_add_div P hmon
      | exact Polynomial.modByMonic_add_div P m
  have hPeq : aeval N P' = aeval N P := by
    have h := congrArg (aeval N) hdiv
    rw [map_add, map_mul, hm0, zero_mul, add_zero] at h
    exact h
  have hP'deg : P'.natDegree ≤ r := by
    rw [hP']
    refine le_trans ?_ hmdeg
    first
      | exact Polynomial.natDegree_modByMonic_le P hmon
      | exact Polynomial.natDegree_modByMonic_le P m
  have hP'0 : P'.coeff 0 = 0 := by
    have h := congrArg (fun p => Polynomial.coeff p 0) hdiv
    simp only [Polynomial.coeff_add, Polynomial.mul_coeff_zero, hmc, zero_mul, add_zero] at h
    rw [h, hP, Polynomial.mul_coeff_zero, Polynomial.coeff_X_pow, if_neg (by omega), mul_zero]
  have htr : (aeval N P).trace = 0 := by
    rw [← hPeq, unip_trace_aeval_zero N hN P' hP'deg, hP'0, zero_mul]
  have hE : aeval N P = 0 := unip_idem_eq_zero _ hPP htr
  have hmP : m ∣ P := minpoly.dvd K N hE
  have hqu : q ∣ u := by
    rw [hq, hP, mul_comm u] at hmP
    exact (mul_dvd_mul_iff_left (pow_ne_zero k Polynomial.X_ne_zero)).mp hmP
  have hq1 : IsUnit q := by
    apply isUnit_of_dvd_one
    rw [← huv]
    exact (dvd_mul_of_dvd_left hqu _).add (dvd_mul_left q v)
  have hNk : N ^ k = 0 := by
    have h := hm0
    rw [hq, map_mul, map_pow, Polynomial.aeval_X] at h
    exact ((hq1.map (aeval N)).mul_left_eq_zero).mp h
  have hkm : k ≤ m.natDegree := by
    have h := Polynomial.natDegree_le_of_dvd ⟨q, hq⟩ hmon.ne_zero
    rwa [Polynomial.natDegree_X_pow] at h
  exact pow_eq_zero_of_le (le_trans hkm hmdeg) hNk

end ReciprocityTheory.MultiplicativeHeights
end

