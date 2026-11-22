import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SplitAnisotropic
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.AlgSplit

theorem det_blockOne {K : Type} [CommRing K] {M : ℕ} (t : K) (A : Matrix (Fin M) (Fin M) K) :
    (blockOne t A).det = t * A.det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  have hz : ∀ j : Fin M, blockOne t A 0 j.succ = 0 := by intro j; simp [blockOne]
  have h00 : blockOne t A 0 0 = t := by simp [blockOne]
  have h0 : (blockOne t A).submatrix Fin.succ Fin.succ = A := by
    ext i j; simp [blockOne]
  simp [hz, h00, h0]

theorem split_anisotropic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E), IsHermND σ J → ∀ (t : F) (x : Fin (M + 1) → E), t ≠ 0 → hE σ J x x = algebraMap F E t → ∃ (g : GL (Fin (M + 1)) E) (J₁ : Matrix (Fin M) (Fin M) E), IsHermND σ J₁ ∧ blockOne (algebraMap F E t) J₁ = cT (σ : E →+* E) (g : Matrix (Fin (M + 1)) (Fin (M + 1)) E) * J * g ∧ ∀ i, (g : Matrix (Fin (M + 1)) (Fin (M + 1)) E) i 0 = x i := by
  intro F E _ _ _ _ _ σ hCM M J hJ t x ht hx
  obtain ⟨-, -, -, hconj⟩ := hCM
  have hσ : ∀ e : E, σ (σ e) = e := by
    intro e
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hconj, hconj, star_star]
  have hherm : ∀ y z, σ (hE σ J y z) = hE σ J z y := by
    intro y z
    simp only [hE, hform, map_sum, map_mul, AlgHom.coe_toRingHom, RingHom.coe_coe, hσ]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hJ.1 i j]
    ring
  set s : E := algebraMap F E t with hs
  have hs0 : s ≠ 0 := (map_ne_zero _).2 ht
  let φ : (Fin (M + 1) → E) →ₗ[E] E :=
    { toFun := fun y => hE σ J x y
      map_add' := by
        intro y z
        simp [hE, hform, mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c y
        simp only [hE, hform, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring }
  have hφ : ∀ y, φ y = hE σ J x y := fun _ => rfl
  have hsurj : Function.Surjective φ := fun e =>
    ⟨(e / s) • x, by rw [map_smul, hφ, hx, smul_eq_mul]; field_simp⟩
  have hfr : Module.finrank E (LinearMap.ker φ) = M := by
    have h := LinearMap.finrank_range_add_finrank_ker φ
    rw [LinearMap.range_eq_top.2 hsurj, finrank_top] at h
    simp at h
    omega
  let b := Module.finBasisOfFinrankEq E (LinearMap.ker φ) hfr
  have hb : ∀ k, hE σ J x (b k : Fin (M + 1) → E) = 0 := fun k => (b k).2
  let col : Fin (M + 1) → Fin (M + 1) → E := Fin.cons x (fun k => (b k : Fin (M + 1) → E))
  let gm : Matrix (Fin (M + 1)) (Fin (M + 1)) E := Matrix.of fun i j => col j i
  have hG : ∀ i j, (cT (σ : E →+* E) gm * J * gm) i j = hE σ J (col i) (col j) := by
    intro i j
    simp only [cT, Matrix.mul_apply, hE, hform, gm, Matrix.transpose_apply, Matrix.map_apply,
      Matrix.of_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hdet : gm.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have hsum : v 0 • x + ∑ k : Fin M, v k.succ • (b k : Fin (M + 1) → E) = 0 := by
      rw [← hv]
      ext i
      simp [gm, col, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mul_comm]
    have hv00 : v 0 = 0 := by
      have h1 := congrArg φ hsum
      rw [map_add, map_smul, map_sum, map_zero, hφ, hx, smul_eq_mul] at h1
      have h2 : ∀ k : Fin M, φ (v k.succ • (b k : Fin (M + 1) → E)) = 0 := by
        intro k
        rw [map_smul, hφ, hb, smul_zero]
      simp only [h2, Finset.sum_const_zero, add_zero] at h1
      exact (mul_eq_zero.1 h1).resolve_right hs0
    have hker : ∑ k : Fin M, v k.succ • b k = 0 := by
      apply Subtype.ext
      rw [hv00, zero_smul, zero_add] at hsum
      simpa using hsum
    have hvs := Fintype.linearIndependent_iff.1 b.linearIndependent _ hker
    apply hv0
    ext i
    refine Fin.cases hv00 hvs i
  let J₁ : Matrix (Fin M) (Fin M) E := Matrix.of fun k l =>
    hE σ J (b k : Fin (M + 1) → E) (b l : Fin (M + 1) → E)
  have hblock : blockOne s J₁ = cT (σ : E →+* E) gm * J * gm := by
    ext i j
    rw [hG]
    refine Fin.cases ?_ (fun k => ?_) i <;> refine Fin.cases ?_ (fun l => ?_) j
    · simp [blockOne, col, hx, hs]
    · simp [blockOne, col, hb]
    · have h3 : hE σ J (b k : Fin (M + 1) → E) x = 0 := by
        rw [← hherm, hb, map_zero]
      simp [blockOne, col, h3]
    · simp [blockOne, col, J₁]
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero gm hdet, J₁, ⟨?_, ?_⟩, hblock, fun i => rfl⟩
  · intro k l
    exact hherm _ _
  · intro hJ0
    have h4 := congrArg Matrix.det hblock
    rw [det_blockOne, hJ0, mul_zero, Matrix.det_mul, Matrix.det_mul] at h4
    have h5 : (cT (σ : E →+* E) gm).det = σ gm.det := by
      rw [cT, Matrix.det_transpose]
      exact ((σ : E →+* E).map_det gm).symm
    rw [h5] at h4
    have h6 : σ gm.det ≠ 0 := (map_ne_zero _).2 hdet
    exact mul_ne_zero (mul_ne_zero h6 hJ.2) hdet h4.symm

end GlobalTheory.CompanionTheory.SW.AlgSplit
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StageData
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

def vec {K : Type} [Zero K] {M n : ℕ} (α : K) (c : Fin n → K) (X : Fin n → Fin M → K) :
    Fin (n + 1) → Fin (M + 1) → K :=
  Fin.cons (Fin.cons α (fun _ => 0)) (fun j => Fin.cons (c j) (X j))

def scl {K : Type} [Mul K] {N n : ℕ} (u : K) (y : Fin n → Fin N → K) : Fin n → Fin N → K :=
  fun a i => y a i * u

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

def s0 {n : ℕ} (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) : R :=
  algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (S 0 0)

def cvec {n : ℕ} (t : F) (a : R → Rˣ) (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) :
    Fin n → R ⊗[F] E :=
  fun j => ((((a (s0 R S))⁻¹ : Rˣ) : R) ⊗ₜ[F] (algebraMap F E t⁻¹)) * S 0 j.succ

def schurM (σ : E →ₐ[F] E) {n : ℕ} (t : F) (a : R → Rˣ)
    (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E) :=
  fun i j => S i.succ j.succ -
    sigR R σ (cvec R t a S i) * inclR R (algebraMap F E t) * cvec R t a S j

open Classical in

def schur (σ : E →ₐ[F] E) {n : ℕ} (t : F) (a : R → Rˣ) (S : HermR R σ (n + 1)) : HermR R σ n :=
  if h : schurM R σ t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ HermR R σ n then ⟨_, h⟩ else 0

theorem schur_coe (σ : E →ₐ[F] E) {n : ℕ} (t : F) (a : R → Rˣ) (S : HermR R σ (n + 1))
    (h : schurM R σ t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ HermR R σ n) :
    (schur R σ t a S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = schurM R σ t a S := by
  simp [schur, h]

def Bset (σ : E →ₐ[F] E) {n : ℕ} (t : F) (a : R → Rˣ) (B₀ : Set R) : Set (HermR R σ (n + 1)) :=
  {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀ ∧
    IsUnit (schur R σ t a S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det}

end Alg

section Meas

variable {F E : Type} [Field F] [Field E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (t : F) {n : ℕ}
  {R : Type} [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R]
  (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E))
  (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E))
  (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J))
  (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0)

def fibS (S : HermR R σ (n + 1)) : Measure (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) :=
  (Bset R σ t a B₀).indicator (fun S : HermR R σ (n + 1) =>
    (κ₁ (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) *
        cm (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) ^ n) •
      ((m₁ (hermScal R σ (algebraMap F R t))).prod (m' (schur R σ t a S))).map (fun p =>
        actW R σ (blockOne (algebraMap F E t) J) (s p.1)
          (vec (((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) : Rˣ) : R) ⊗ₜ[F] (1 : E))
            (cvec R t a S) p.2))) S

def Pint (φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞) (α : R) (c : Fin n → R ⊗[F] E)
    (S' : HermR R σ n) : ℝ≥0∞ :=
  ∫⁻ y₀, ∫⁻ X, φ (actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (α ⊗ₜ[F] (1 : E)) c X)) ∂(m' S')
    ∂(m₁ (hermScal R σ (algebraMap F R t)))

def Preal (φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ) (α : R) (c : Fin n → R ⊗[F] E)
    (S' : HermR R σ n) : ℝ :=
  ∫ y₀, ∫ X, φ (actW R σ (blockOne (algebraMap F E t) J) (s y₀) (vec (α ⊗ₜ[F] (1 : E)) c X)) ∂(m' S')
    ∂(m₁ (hermScal R σ (algebraMap F R t)))

def sTil (y : Fin 1 → Fin (M + 1) → R ⊗[F] E) : HA R σ (blockOne (algebraMap F E t) J) :=
  s (scl ((((a (s0 R (gramR R σ (blockOne (algebraMap F E t) J) y)))⁻¹ : Rˣ) : R) ⊗ₜ[F] (1 : E)) y)

def chi {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R)
    (φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞) (y : Fin 1 → Fin (M + 1) → R ⊗[F] E) : ℝ≥0∞ :=
  ∫⁻ c : Fin n → R ⊗[F] E, ∫⁻ X : Fin n → Fin M → R ⊗[F] E,
    φ (Fin.cons (y 0) (actW R σ (blockOne (algebraMap F E t) J) (sTil σ J t s a y)
      (fun j => Fin.cons (c j) (X j)))) ∂(coordW R b lam n M) ∂(Measure.pi fun _ => coordK R b lam)

def Uset (B₀ : Set R) (a : R → Rˣ) : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) :=
  gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' (Subtype.val '' Bset R σ t a B₀)

def Unt (R : Type) [CommRing R] [Algebra F R] (n : ℕ) : Set (HermR R σ n) :=
  {S | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det}

def Mid {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R)
    (φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ x in B₀, (κ₁ (a x) : ℝ≥0∞) * ∫⁻ c : Fin n → R ⊗[F] E, ∫⁻ S' in Unt σ R n,
    Pint σ J t m₁ m' s φ ((a x : Rˣ) : R) c S' ∂(coordHerm R σ b lam n)
    ∂(Measure.pi fun _ => coordK R b lam) ∂lam

end Meas

section Data

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

structure StageData (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ)
    {R : Type} [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R]
    {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R)
    (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E))
    (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E))
    (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J))
    (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0) : Prop where
  hCM : IsCMExt F E σ
  hJ : IsHermND σ J
  ht : t ≠ 0
  hR : IsLocR R
  hlam : lam.IsAddHaarMeasure
  hm₁ : IsGramFib R σ (blockOne (algebraMap F E t) J) 1 (coordW R b lam 1 (M + 1)) (coordHerm R σ b lam 1) m₁
  hm' : IsGramFib R σ J n (coordW R b lam n M) (coordHerm R σ b lam n) m'
  hs : Measurable s
  hsec : ∀ y, gramR R σ (blockOne (algebraMap F E t) J) y = (hermScal R σ (algebraMap F R t) : HermR R σ 1) →
    actW R σ _ (s y) (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)) = y
  hcpt : ∀ C : Set (Fin 1 → Fin (M + 1) → R ⊗[F] E), IsCompact C →
    ∃ C' : Set (HA R σ (blockOne (algebraMap F E t) J)), IsCompact C' ∧ ∀ y ∈ C,
      gramR R σ (blockOne (algebraMap F E t) J) y = (hermScal R σ (algebraMap F R t) : HermR R σ 1) → s y ∈ C'
  hB₀ : IsOpen B₀
  htB : algebraMap F R t ∈ B₀
  hac : ContinuousOn a B₀
  hoff : ∀ x, x ∉ B₀ → a x = 1
  hsq : ∀ x ∈ B₀, x = ((a x : Rˣ) : R) ^ 2 * algebraMap F R t
  ha1 : a (algebraMap F R t) = 1
  hκc : Continuous κ₁
  hκ1 : κ₁ 1 = 1
  hscale : ∀ u : Rˣ, m₁ (hermScal R σ ((u : R) ^ 2 * algebraMap F R t)) =
    κ₁ u • (m₁ (hermScal R σ (algebraMap F R t))).map (scl ((u : R) ⊗ₜ[F] (1 : E)))
  hcmc : Continuous cm
  hmod : ∀ u : Rˣ, (coordK R b lam).map (fun y => ((u : R) ⊗ₜ[F] (algebraMap F E t)) * y) = cm u • coordK R b lam

end Data

end GlobalTheory.CompanionTheory.SW.PiLocalization₂
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorInvolutionAlgebraProperties
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.KAlg

section Coord

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem exists_basis_one_delta (σ : E →ₐ[F] E) {δ : E} (hδ : σ δ = -δ) (h0 : δ ≠ 0)
    (hfr : Module.finrank F E = 2) (h2 : (2 : F) ≠ 0) :
    ∃ b : Module.Basis (Fin 2) F E, b 0 = 1 ∧ b 1 = δ := by
  have li : LinearIndependent F ![(1 : E), δ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 : s • (1 : E) + t • (-δ) = 0 := by
      have := congrArg σ hst
      simpa [map_add, map_smul, hδ] using this
    have hs : (2 * s) • (1 : E) = 0 := by
      have : (2 * s) • (1 : E) = (s • (1 : E) + t • δ) + (s • (1 : E) + t • (-δ)) := by module
      rw [this, hst, h1, add_zero]
    have hs0 : s = 0 := by
      rcases smul_eq_zero.1 hs with h | h
      · exact (mul_eq_zero.1 h).resolve_left h2
      · exact absurd h one_ne_zero
    subst hs0
    refine ⟨rfl, ?_⟩
    rcases smul_eq_zero.1 (by simpa using hst : t • δ = 0) with h | h
    · exact h
    · exact absurd h h0
  refine ⟨basisOfLinearIndependentOfCardEqFinrank li (by simp [hfr]), ?_, ?_⟩
  · simp
  · simp

variable {R : Type} [CommRing R] [Algebra F R]

theorem exists_coord (b : Module.Basis (Fin 2) F E) {δ : E} (hb0 : b 0 = 1) (hb1 : b 1 = δ)
    (y : R ⊗[F] E) : ∃ a c : R, y = a ⊗ₜ[F] (1 : E) + c ⊗ₜ[F] δ := by
  let B := Algebra.TensorProduct.basis R b
  refine ⟨B.repr y 0, B.repr y 1, ?_⟩
  have h := (B.sum_repr y).symm
  rw [Fin.sum_univ_two] at h
  have e0 : B 0 = (1 : R) ⊗ₜ[F] (1 : E) := by simp [B, hb0]
  have e1 : B 1 = (1 : R) ⊗ₜ[F] δ := by simp [B, hb1]
  rw [e0, e1, TensorProduct.smul_tmul', TensorProduct.smul_tmul'] at h
  simpa using h

theorem coord_inj (b : Module.Basis (Fin 2) F E) {δ : E} (hb0 : b 0 = 1) (hb1 : b 1 = δ)
    {a c a' c' : R} (h : a ⊗ₜ[F] (1 : E) + c ⊗ₜ[F] δ = a' ⊗ₜ[F] (1 : E) + c' ⊗ₜ[F] δ) :
    a = a' ∧ c = c' := by
  let B := Algebra.TensorProduct.basis R b
  have e : ∀ p q : R, p ⊗ₜ[F] (1 : E) + q ⊗ₜ[F] δ = p • B 0 + q • B 1 := by
    intro p q
    have e0 : B 0 = (1 : R) ⊗ₜ[F] (1 : E) := by simp [B, hb0]
    have e1 : B 1 = (1 : R) ⊗ₜ[F] δ := by simp [B, hb1]
    rw [e0, e1, TensorProduct.smul_tmul', TensorProduct.smul_tmul']
    simp
  rw [e, e] at h
  have h0 := congrArg (fun y => B.repr y 0) h
  have h1 := congrArg (fun y => B.repr y 1) h
  simp at h0 h1
  exact ⟨h0, h1⟩

theorem tmul_one_injective (b : Module.Basis (Fin 2) F E) {δ : E} (hb0 : b 0 = 1) (hb1 : b 1 = δ) :
    Function.Injective (Algebra.TensorProduct.includeLeft : R →ₐ[F] R ⊗[F] E) := by
  intro p q h
  have h' : p ⊗ₜ[F] (1 : E) + (0 : R) ⊗ₜ[F] δ = q ⊗ₜ[F] (1 : E) + (0 : R) ⊗ₜ[F] δ := by
    simpa using h
  exact (coord_inj b hb0 hb1 h').1

end Coord

theorem algebra_tensor_invol : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [IsArtinianRing R] [IsReduced R],
    IsArtinianRing (R ⊗[F] E) ∧ IsReduced (R ⊗[F] E) ∧ IsUnit (2 : R ⊗[F] E) ∧
      (∀ y, sigR R σ (sigR R σ y) = y) ∧ (∃ δ : R ⊗[F] E, IsUnit δ ∧ sigR R σ δ = -δ) ∧
      (∀ y : R ⊗[F] E, sigR R σ y = y → ∃ r : R, y = r ⊗ₜ[F] (1 : E)) ∧
      ∀ r : R, IsUnit (r ⊗ₜ[F] (1 : E) : R ⊗[F] E) ↔ IsUnit r := by
  intro F E _ _ _ _ _ σ h R _ _ _ _
  have hσσ : ∀ x, σ (σ x) = x := by
    intro x
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [h.2.2.2, h.2.2.2, star_star]
  have hne : ∃ x, σ x ≠ x := by
    by_contra hc
    push Not at hc
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have := h.2.1
    apply IsTotallyComplex.complexEmbedding_not_isReal τ
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have h' := h.2.2.2 τ x
    rw [hc] at h'
    simpa [ComplexEmbedding.conjugate_coe_eq] using h'.symm
  obtain ⟨x₀, hx₀⟩ := hne
  set δ : E := x₀ - σ x₀ with hδdef
  have hδ : σ δ = -δ := by simp [hδdef, hσσ]
  have hδ0 : δ ≠ 0 := fun e => hx₀ (sub_eq_zero.1 e).symm
  have h2F : (2 : F) ≠ 0 := two_ne_zero
  obtain ⟨b, hb0, hb1⟩ := exists_basis_one_delta σ hδ hδ0 h.2.2.1 h2F
  have : Module.Finite F E := Module.Finite.of_basis b
  have hsig : ∀ (a : R) (e : E), sigR R σ (a ⊗ₜ[F] e) = a ⊗ₜ[F] σ e := fun _ _ => rfl
  have h2R : IsUnit (2 : R) := by
    have := (IsUnit.mk0 (2 : F) h2F).map (algebraMap F R)
    rwa [map_ofNat] at this
  have half : ∀ a : R, a + a = 0 → a = 0 := fun a ha =>
    (h2R.mul_right_eq_zero).1 (by rw [two_mul, ha])
  have hnil : ∀ a : R, IsNilpotent (a ⊗ₜ[F] (1 : E) : R ⊗[F] E) → a = 0 := fun a ha =>
    ((IsNilpotent.map_iff (tmul_one_injective (R := R) b hb0 hb1)).1 ha).eq_zero
  have hδu : IsUnit ((1 : R) ⊗ₜ[F] δ : R ⊗[F] E) :=
    (IsUnit.mk0 δ hδ0).map (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E)
  refine ⟨IsArtinianRing.of_finite R _, ⟨fun x hx => ?_⟩, ?_, fun y => ?_, ⟨_, hδu, ?_⟩, fun y hy => ?_, fun r => ⟨?_, ?_⟩⟩
  · obtain ⟨a, c, rfl⟩ := exists_coord b hb0 hb1 x
    have hs := hx.map (sigR R σ)
    have hadd := (Commute.all _ _).isNilpotent_add hx hs
    have e1 : (a ⊗ₜ[F] (1 : E) + c ⊗ₜ[F] δ) + sigR R σ (a ⊗ₜ[F] (1 : E) + c ⊗ₜ[F] δ) =
        (a + a) ⊗ₜ[F] (1 : E) := by
      rw [map_add, hsig, hsig, map_one, hδ, TensorProduct.tmul_neg, TensorProduct.add_tmul]
      abel
    rw [e1] at hadd
    have ha : a = 0 := half a (hnil _ hadd)
    subst ha
    rw [TensorProduct.zero_tmul, zero_add] at hx ⊢
    have hm : IsNilpotent ((c ⊗ₜ[F] δ) * ((1 : R) ⊗ₜ[F] δ⁻¹) : R ⊗[F] E) :=
      (Commute.all _ _).isNilpotent_mul_right (show IsNilpotent (c ⊗ₜ[F] δ : R ⊗[F] E) from hx)
    have e2 : ((c ⊗ₜ[F] δ) * ((1 : R) ⊗ₜ[F] δ⁻¹) : R ⊗[F] E) = c ⊗ₜ[F] (1 : E) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_inv_cancel₀ hδ0]
    rw [e2] at hm
    rw [hnil c hm, TensorProduct.zero_tmul]
  · have := (IsUnit.mk0 (2 : F) h2F).map (algebraMap F (R ⊗[F] E))
    rwa [map_ofNat] at this
  · induction y using TensorProduct.induction_on with
    | zero => simp
    | add p q hp hq => simp only [map_add, hp, hq]
    | tmul a e => rw [hsig, hsig, hσσ]
  · rw [hsig, hδ, TensorProduct.tmul_neg]
  · obtain ⟨a, c, rfl⟩ := exists_coord b hb0 hb1 y
    rw [map_add, hsig, hsig, map_one, hδ, TensorProduct.tmul_neg, ← TensorProduct.neg_tmul] at hy
    have hc := (coord_inj b hb0 hb1 hy).2
    have : c = 0 := half c (by nth_rewrite 1 [← hc]; simp)
    exact ⟨a, by rw [this, TensorProduct.zero_tmul, add_zero]⟩
  · rintro ⟨u, hu⟩
    obtain ⟨a, c, hac⟩ := exists_coord b hb0 hb1 (u⁻¹ : (R ⊗[F] E)ˣ).val
    have e : (r * a) ⊗ₜ[F] (1 : E) + (r * c) ⊗ₜ[F] δ =
        (1 : R) ⊗ₜ[F] (1 : E) + (0 : R) ⊗ₜ[F] δ := by
      have : (u : R ⊗[F] E) * (u⁻¹ : (R ⊗[F] E)ˣ).val = 1 := u.mul_inv
      rw [hu, hac, mul_add, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
        one_mul, one_mul, Algebra.TensorProduct.one_def] at this
      rw [this, TensorProduct.zero_tmul, add_zero]
    exact IsUnit.of_mul_eq_one a (coord_inj b hb0 hb1 e).1
  · intro hr
    exact hr.map (Algebra.TensorProduct.includeLeft : R →ₐ[F] R ⊗[F] E)

end GlobalTheory.CompanionTheory.SW.KAlg
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.TopK

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

section

variable {F E : Type} [Field F] [Field E] [Algebra F E]
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]

omit [IsTopologicalRing R] in

theorem isModTop : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩

def coordHomeo {d : ℕ} (b : Module.Basis (Fin d) F E) : (R ⊗[F] E) ≃ₜ (Fin d → R) :=
  haveI : IsModuleTopology R (R ⊗[F] E) := isModTop R
  haveI : ContinuousAdd (R ⊗[F] E) := IsModuleTopology.toContinuousAdd R _
  { (Algebra.TensorProduct.basis R b).equivFun.toEquiv with
    continuous_toFun :=
      IsModuleTopology.continuous_of_linearMap (Algebra.TensorProduct.basis R b).equivFun.toLinearMap
    continuous_invFun :=
      IsModuleTopology.continuous_of_linearMap (Algebra.TensorProduct.basis R b).equivFun.symm.toLinearMap }

theorem isHomeomorph_coord {d : ℕ} (b : Module.Basis (Fin d) F E) :
    IsHomeomorph fun (y : R ⊗[F] E) (k : Fin d) => (Algebra.TensorProduct.basis R b).repr y k :=
  (coordHomeo R b).isHomeomorph

theorem isTopRing [Module.Finite F E] : IsTopologicalRing (R ⊗[F] E) :=
  haveI : IsModuleTopology R (R ⊗[F] E) := isModTop R
  IsModuleTopology.isTopologicalRing R (R ⊗[F] E)

omit [IsTopologicalRing R] in
theorem continuous_sigR (σ : E →ₐ[F] E) : Continuous (sigR R σ) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := isModTop R
  haveI : ContinuousAdd (R ⊗[F] E) := IsModuleTopology.toContinuousAdd R _
  exact IsModuleTopology.continuous_of_linearMap
    (Algebra.TensorProduct.map (AlgHom.id R R) σ).toLinearMap

theorem continuous_trace [Module.Finite F E] : Continuous (Algebra.trace R (R ⊗[F] E)) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := isModTop R
  exact IsModuleTopology.continuous_of_linearMap _

end

theorem topTens_props : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R], IsTopologicalRing (R ⊗[F] E) ∧ LocallyCompactSpace (R ⊗[F] E) ∧ SecondCountableTopology (R ⊗[F] E) ∧ T2Space (R ⊗[F] E) ∧ Continuous (sigR R σ) ∧ Continuous (Algebra.trace R (R ⊗[F] E)) ∧ (∀ (d : ℕ) (b : Module.Basis (Fin d) F E), IsHomeomorph fun (y : R ⊗[F] E) (k : Fin d) => (Algebra.TensorProduct.basis R b).repr y k) ∧ (∀ n M : ℕ, BorelSpace (Fin n → Fin M → R ⊗[F] E)) ∧ (∀ n : ℕ, IsClosed (HermR R σ n : Set (Matrix (Fin n) (Fin n) (R ⊗[F] E)))) ∧ (∀ (n M : ℕ) (J : Matrix (Fin M) (Fin M) E), Continuous (gramR R σ J : (Fin n → Fin M → R ⊗[F] E) → _)) := by
  intro F E _ _ _ _ _ σ _ R _ _ _ _ _ _ _
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have e := coordHomeo R (Module.finBasis F E)
  haveI h1 : IsTopologicalRing (R ⊗[F] E) := isTopRing R
  haveI h2 : LocallyCompactSpace (R ⊗[F] E) := e.isOpenEmbedding.locallyCompactSpace
  haveI h3 : SecondCountableTopology (R ⊗[F] E) := e.secondCountableTopology
  haveI h4 : T2Space (R ⊗[F] E) := e.isEmbedding.t2Space
  haveI h5 : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  have hs := continuous_sigR R σ
  refine ⟨h1, h2, h3, h4, hs, continuous_trace R, fun d b => isHomeomorph_coord R b,
    fun n M => inferInstance, fun n => ?_, fun n M J => ?_⟩
  · have : (HermR R σ n : Set (Matrix (Fin n) (Fin n) (R ⊗[F] E))) =
        ⋂ a, ⋂ b, {S | sigR R σ (S b a) = S a b} := by
      ext S
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
      rfl
    rw [this]
    refine isClosed_iInter fun a => isClosed_iInter fun b => isClosed_eq ?_ ?_
    · exact hs.comp (continuous_id.matrix_elem b a)
    · exact continuous_id.matrix_elem a b
  · refine continuous_pi fun a => continuous_pi fun b => ?_
    unfold gramR hR hform
    refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
    exact ((hs.comp ((continuous_apply i).comp (continuous_apply a))).mul continuous_const).mul
      ((continuous_apply j).comp (continuous_apply b))

end GlobalTheory.CompanionTheory.SW.TopK
end
end

