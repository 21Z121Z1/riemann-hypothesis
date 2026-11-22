import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0178
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0170
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoordOfMemXa
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LebesgueCommonStabilizerEqRadicalLeviMap
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0118
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0183
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0160

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalBlockFrameLocalSplit
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.RadCov.LocSplit

theorem biorth_decomp {K : Type} [CommRing K] {n m : ℕ} {r : ℕ → ℕ}
    {T : ∀ b, Matrix (Fin n) (Fin (r b)) K} {T' : ∀ b, Matrix (Fin (r b)) (Fin n) K}
    (h : Biorth r m T T') (y : Fin n → K) :
    y = ∑ b ∈ Finset.range m, T b *ᵥ (T' b *ᵥ y) := by
  have := congrArg (fun M : Matrix (Fin n) (Fin n) K => M *ᵥ y) h.2.2
  simp only [Matrix.one_mulVec, Matrix.sum_mulVec] at this
  simp only [Matrix.mulVec_mulVec]
  exact this.symm

theorem biorth_map {E K : Type} [CommRing E] [CommRing K] {n m : ℕ} {r : ℕ → ℕ}
    {T : ∀ b, Matrix (Fin n) (Fin (r b)) E} {T' : ∀ b, Matrix (Fin (r b)) (Fin n) E}
    (h : Biorth r m T T') (φ : E →+* K) {P : Matrix (Fin n) (Fin n) K} (hP : IsUnit P) :
    Biorth r m (fun b => P⁻¹ * (T b).map φ) (fun b => (T' b).map φ * P) := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hd
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hd
  have key : ∀ b b', (T' b).map φ * P * (P⁻¹ * (T b').map φ) = (T' b * T b').map φ := by
    intro b b'
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc P, h1, Matrix.one_mul, Matrix.map_mul]
  refine ⟨fun b => ?_, fun b b' hb => ?_, ?_⟩
  · rw [key, h.1 b, Matrix.map_one _ (map_zero φ) (map_one φ)]
  · rw [key, h.2.1 b b' hb, Matrix.map_zero _ (map_zero φ)]
  · have e : ∀ b, P⁻¹ * (T b).map φ * ((T' b).map φ * P)
        = P⁻¹ * φ.mapMatrix (T b * T' b) * P := by
      intro b
      rw [RingHom.mapMatrix_apply, Matrix.map_mul]
      simp only [Matrix.mul_assoc]
    simp only [e]
    rw [← Finset.sum_mul, ← Finset.mul_sum, ← map_sum, h.2.2, map_one, mul_one, h2]

theorem map_mulVec_comp {E K : Type} [CommRing E] [CommRing K] {n p : ℕ} (φ : E →+* K)
    (A : Matrix (Fin n) (Fin p) E) (y : Fin p → E) :
    A.map φ *ᵥ (fun l => φ (y l)) = fun l => φ ((A *ᵥ y) l) := by
  ext i
  exact (RingHom.map_mulVec φ A y i).symm

theorem block_mem {R K : Type} [CommRing R] [CommRing K] [Algebra R K] {n m : ℕ} {r : ℕ → ℕ}
    {F : ℕ → Submodule R (Fin n → K)}
    {T : ∀ b, Matrix (Fin n) (Fin (r b)) K} {T' : ∀ b, Matrix (Fin (r b)) (Fin n) K}
    {Λ : ∀ b, Submodule R (Fin (r b) → K)} (h : Biorth r m T T')
    (hF : ∀ k y, y ∈ F k ↔ ∀ b, T' b *ᵥ y ∈ Λ b ∧ (k ≤ b → T' b *ᵥ y = 0))
    {b k : ℕ} (hb : b < k) {v : Fin (r b) → K} (hv : v ∈ Λ b) : T b *ᵥ v ∈ F k := by
  rw [hF]
  intro b'
  rw [Matrix.mulVec_mulVec]
  by_cases e : b' = b
  · subst e
    rw [h.1, Matrix.one_mulVec]
    exact ⟨hv, fun hk => absurd hk (by omega)⟩
  · rw [h.2.1 _ _ e, Matrix.zero_mulVec]
    exact ⟨zero_mem _, fun _ => rfl⟩

theorem mem_locFlag_iff {E : Type} [Field E] [NumberField E] {n m : ℕ} {r : ℕ → ℕ}
    {F : ℕ → Submodule (𝓞 E) (Fin n → E)}
    {T : ∀ b, Matrix (Fin n) (Fin (r b)) E} {T' : ∀ b, Matrix (Fin (r b)) (Fin n) E}
    {Λ : ∀ b, Submodule (𝓞 E) (Fin (r b) → E)} (h : Biorth r m T T')
    (hΛ : ∀ b, Submodule.IsLattice E (Λ b))
    (hF : ∀ k y, y ∈ F k ↔ ∀ b, T' b *ᵥ y ∈ Λ b ∧ (k ≤ b → T' b *ᵥ y = 0))
    (φ : E →+* ℂ) {P : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) (k : ℕ) (y : Fin n → ℂ) :
    y ∈ locFlag φ P F k ↔ ∀ b, k ≤ b → ((T' b).map φ * P) *ᵥ y = 0 := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hd
  constructor
  · intro hy b hb
    unfold locFlag at hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, hz, rfl⟩ := hx
      have h0 := ((hF k z).1 hz b).2 hb
      rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, h1, Matrix.mul_one, map_mulVec_comp, h0]
      ext l
      simp
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.mulVec_add, hx, hy, add_zero]
    | smul c x _ hx => rw [Matrix.mulVec_smul, hx, smul_zero]
  · intro hy
    rw [biorth_decomp (biorth_map h φ hP) y]
    refine Submodule.sum_mem _ fun b _ => ?_
    by_cases hb : k ≤ b
    · simp only [hy b hb, Matrix.mulVec_zero]
      exact zero_mem _
    have A : ∀ v : Fin (r b) → E,
        (P⁻¹ * (T b).map φ) *ᵥ (fun l => φ (v l)) ∈ locFlag φ P F k := by
      intro v
      have hv : v ∈ Submodule.span E (Λ b : Set (Fin (r b) → E)) := by
        rw [(hΛ b).span_eq_top]; trivial
      induction hv using Submodule.span_induction with
      | mem x hx =>
        rw [← Matrix.mulVec_mulVec, map_mulVec_comp]
        exact Submodule.subset_span ⟨_, block_mem h hF (by omega) hx, rfl⟩
      | zero =>
        have : (fun l => φ ((0 : Fin (r b) → E) l)) = 0 := by ext l; simp
        rw [this, Matrix.mulVec_zero]
        exact zero_mem _
      | add x y _ _ hx hy =>
        have : (fun l => φ ((x + y) l)) = (fun l => φ (x l)) + fun l => φ (y l) := by ext l; simp
        rw [this, Matrix.mulVec_add]
        exact add_mem hx hy
      | smul c x _ hx =>
        have : (fun l => φ ((c • x) l)) = φ c • fun l => φ (x l) := by ext l; simp
        rw [this, Matrix.mulVec_smul]
        exact Submodule.smul_mem _ _ hx
    have B : ∀ u : Fin (r b) → ℂ, (P⁻¹ * (T b).map φ) *ᵥ u ∈ locFlag φ P F k := by
      intro u
      have e : u = ∑ j, u j • fun l => φ ((Pi.single j (1 : E) : Fin (r b) → E) l) := by
        ext l
        simp [Finset.sum_apply, Pi.single_apply, apply_ite φ]
      rw [e, Matrix.mulVec_sum]
      refine Submodule.sum_mem _ fun j _ => ?_
      rw [Matrix.mulVec_smul]
      exact Submodule.smul_mem _ _ (A _)
    exact B _

theorem exists_lowers_blocks {R K : Type} [CommRing R] [CommRing K] [Algebra R K] {n m : ℕ} {r : ℕ → ℕ}
    {F : ℕ → Submodule R (Fin n → K)}
    {T : ∀ b, Matrix (Fin n) (Fin (r b)) K} {T' : ∀ b, Matrix (Fin (r b)) (Fin n) K}
    {Λ : ∀ b, Submodule R (Fin (r b) → K)} (h : Biorth r m T T')
    (hF : ∀ k y, y ∈ F k ↔ ∀ b, T' b *ᵥ y ∈ Λ b ∧ (k ≤ b → T' b *ᵥ y = 0)) (c : ℕ)
    (Z : ∀ b : Fin m, Matrix (Fin (r b)) (Fin (r (b + c + 1))) K)
    (hZ : ∀ b : Fin m, ∀ y ∈ Λ (b + c + 1), Z b *ᵥ y ∈ Λ b) :
    ∃ Y ∈ lowers F c, ∀ b : Fin m, T' b * Y * T (b + c + 1) = Z b := by
  refine ⟨∑ b : Fin m, T b * Z b * T' (b + c + 1), fun a y hy => ?_, fun a => ?_⟩
  · rw [Matrix.sum_mulVec]
    refine Submodule.sum_mem _ fun b _ => ?_
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have h1 := (hF _ y).1 hy (b + c + 1)
    by_cases hb : (b : ℕ) < a
    · exact block_mem h hF hb (hZ b _ h1.1)
    · rw [h1.2 (by omega), Matrix.mulVec_zero, Matrix.mulVec_zero]
      exact zero_mem _
  · rw [Matrix.mul_sum, Matrix.sum_mul, Finset.sum_eq_single a]
    · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h.1, Matrix.one_mul, Matrix.mul_assoc, h.1,
        Matrix.mul_one]
    · intro b _ hb
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h.2.1 _ _ (fun e => hb (Fin.ext e.symm)),
        Matrix.zero_mul, Matrix.zero_mul, Matrix.zero_mul]
    · intro ha
      exact absurd (Finset.mem_univ a) ha

theorem locSplit : ∀ (E : Type) [Field E] [NumberField E] (n m : ℕ) (F : ℕ → Submodule (𝓞 E) (Fin n → E)) (r : ℕ → ℕ) (T : ∀ b, Matrix (Fin n) (Fin (r b)) E) (T' : ∀ b, Matrix (Fin (r b)) (Fin n) E) (Λ : ∀ b, Submodule (𝓞 E) (Fin (r b) → E)), Biorth r m T T' → (∀ b, Submodule.IsLattice E (Λ b)) → (∀ k y, y ∈ F k ↔ ∀ b, T' b *ᵥ y ∈ Λ b ∧ (k ≤ b → T' b *ᵥ y = 0)) → (∀ (φ : E →+* ℂ) (P : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Biorth r m (fun b => P⁻¹ * (T b).map φ) (fun b => (T' b).map φ * P) ∧ ∀ k y, y ∈ locFlag φ P F k ↔ ∀ b, k ≤ b → ((T' b).map φ * P) *ᵥ y = 0) ∧ ∀ c, (∀ Y ∈ lowers F c, ∀ b, ∀ y ∈ Λ (b + c + 1), (T' b * Y * T (b + c + 1)) *ᵥ y ∈ Λ b) ∧ ∀ Z : ∀ b : Fin m, Matrix (Fin (r b)) (Fin (r (b + c + 1))) E, (∀ b : Fin m, ∀ y ∈ Λ (b + c + 1), Z b *ᵥ y ∈ Λ b) → ∃ Y ∈ lowers F c, ∀ b : Fin m, T' b * Y * T (b + c + 1) = Z b := by
  intro E _ _ n m F r T T' Λ h hΛ hF
  refine ⟨fun φ P hP => ⟨biorth_map h φ hP, mem_locFlag_iff h hΛ hF φ hP⟩, fun c => ⟨?_, ?_⟩⟩
  · intro Y hY b y hy
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact ((hF (b + 1) _).1 (hY (b + 1) _ (block_mem h hF (by omega) hy)) b).1
  · exact exists_lowers_blocks h hF c

end GlobalTheory.RadCov.LocSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealComplexSpanOrthonormalSkewFamily
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.SkewSpan

theorem skew_conj {n : ℕ} (ε : Fin n → Bool) {B : Matrix (Fin n) (Fin n) ℂ}
    (h : Formalism.REAL.inG ε B) : Formalism.REAL.Jm ε * Bᴴ * Formalism.REAL.Jm ε = -B := by
  have h' : Bᴴ * Formalism.REAL.Jm ε = -(Formalism.REAL.Jm ε * B) := eq_neg_of_add_eq_zero_left h
  rw [Matrix.mul_assoc, h', Matrix.mul_neg, ← Matrix.mul_assoc, Formalism.REAL.Jm_mul_self,
    Matrix.one_mul]

theorem trace_twisted {n : ℕ} (ε : Fin n → Bool) {B : Matrix (Fin n) (Fin n) ℂ}
    (h : Formalism.REAL.inG ε B) (X : Matrix (Fin n) (Fin n) ℂ) :
    (Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε * Bᴴ).trace = - starRingEnd ℂ (X * Bᴴ).trace := by
  have h1 : (Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε * Bᴴ).trace
      = (Xᴴ * (Formalism.REAL.Jm ε * Bᴴ * Formalism.REAL.Jm ε)).trace := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have h2 : starRingEnd ℂ (X * Bᴴ).trace = (Xᴴ * B).trace := by
    rw [starRingEnd_apply, ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.trace_mul_comm]
  rw [h1, h2, skew_conj ε h, Matrix.mul_neg, Matrix.trace_neg]

theorem real_span (n d : ℕ) (ε : Fin n → Bool) (B : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (s : Set (Fin d)) (hB : ∀ i k, (B i * (B k)ᴴ).trace = if i = k then 1 else 0)
    (hG : ∀ i, Formalism.REAL.inG ε (B i)) :
    (∀ X, (X ∈ Submodule.span ℂ (B '' s) ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (B '' s)) ∧
    (∀ X ∈ Submodule.span ℂ (B '' s), ∀ i, i ∉ s → (X * (B i)ᴴ).trace = 0) ∧
    ∀ X i, (Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε * (B i)ᴴ).trace
      = - starRingEnd ℂ (X * (B i)ᴴ).trace := by
  have h2 : ∀ X ∈ Submodule.span ℂ (B '' s), ∀ i, i ∉ s → (X * (B i)ᴴ).trace = 0 := by
    intro X hX i hi
    induction hX using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      rw [hB, if_neg]
      rintro rfl
      exact hi hk
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.add_mul, Matrix.trace_add, hx, hy, add_zero]
    | smul c x _ hx => rw [Matrix.smul_mul, Matrix.trace_smul, hx, smul_zero]
  have hexp : ∀ X ∈ Submodule.span ℂ (B '' s), X = ∑ i, (X * (B i)ᴴ).trace • B i := by
    intro X hX
    induction hX using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      simp [hB]
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [Matrix.add_mul, Matrix.trace_add, add_smul, Finset.sum_add_distrib]
      rw [← hx, ← hy]
    | smul c x _ hx =>
      simp only [Matrix.smul_mul, Matrix.trace_smul, smul_assoc, ← Finset.smul_sum]
      rw [← hx]
  refine ⟨fun X => ⟨?_, ?_⟩, h2, fun X i => trace_twisted ε (hG i) X⟩
  · rintro ⟨hX, hXG⟩
    rw [hexp X hX]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hi : i ∈ s
    · have h3 := trace_twisted ε (hG i) X
      rw [skew_conj ε hXG, Matrix.neg_mul, Matrix.trace_neg, neg_inj] at h3
      have h4 : (X * (B i)ᴴ).trace = (((X * (B i)ᴴ).trace.re : ℝ) : ℂ) :=
        (Complex.conj_eq_iff_re.mp h3.symm).symm
      rw [h4, Complex.coe_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
    · rw [h2 X hX i hi, zero_smul]
      exact Submodule.zero_mem _
  · intro hX
    refine ⟨Submodule.span_le_restrictScalars ℝ ℂ _ hX, ?_⟩
    induction hX using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      exact hG k
    | zero => simp [Formalism.REAL.inG]
    | add x y _ _ hx hy =>
      unfold Formalism.REAL.inG at *
      rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, hx, hy,
        add_zero]
    | smul c x _ hx =>
      unfold Formalism.REAL.inG at *
      rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add,
        hx, smul_zero]

end GlobalTheory.SkewSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealFrameAutomorphismUnitriangularRowsCoords
section
noncomputable section
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov

namespace GlobalTheory.DegVol.RefCovTop

theorem upperIn_of_zero {r : ℕ} (β : Fin r → ℕ) : upperIn β 0 = 1 := by
  ext a b
  by_cases h : a < b
  · simp [upperIn, upper, h, ne_of_lt h]
  · simp [upperIn, upper, h, Matrix.one_apply]

private theorem uEmb_one' (k r : ℕ) : uEmb k r (1 : Matrix (Fin r) (Fin r) ℂ) = 1 := by
  ext i j
  unfold uEmb
  simp only [inv_one, Matrix.one_apply]
  split_ifs <;> simp_all [Fin.ext_iff]
  omega

theorem crd_of_zero {k r j : ℕ} (β : Fin r → ℕ) (q : (UTin β → ℂ) × PTop k r j) (h : q.1 = 0) :
    crd k r j β q = pTop k r j q.2 := by
  rw [crd, h, upperIn_of_zero, uEmb_one', Matrix.mul_one]

private theorem mulVec_bvec_lemma_2 {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    (M *ᵥ bvec j) i = M i j := by
  simp [Matrix.mulVec, dotProduct, bvec, Pi.single_apply]

private theorem eI_inj' {k r : ℕ} (a c : Fin r) : eI k r a = eI k r c ↔ a = c := by
  constructor
  · intro h
    have h' := congrArg Fin.val h
    exact Fin.ext h'
  · rintro rfl
    rfl

private theorem wI_ne_esI' {k r : ℕ} (l : Fin (k + 1)) (b : Fin r) : wI k r l ≠ esI k r b := by
  intro h
  have h0 := congrArg Fin.val h
  have h1 : (wI k r l).val = r + l.val := rfl
  have h2 : (esI k r b).val = 2 * r + k - b.val := rfl
  have := l.isLt
  have := b.isLt
  omega

private theorem pTop_mulVec_eq_of_vanishing {k r j : ℕ} (q : PTop k r j) (w : Fin (2 * r + k + 1) → ℂ)
    (hw : ∀ m : Fin (2 * r + k + 1), r ≤ m.val → w m = 0) : pTop k r j q *ᵥ w = w := by
  funext i
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single i]
  · simp [pTop, pOf, pEl]
  · intro m _ hmi
    by_cases hm : r ≤ m.val
    · simp [hw m hm]
    · have hz : pTop k r j q i m = 0 := by
        unfold pTop pOf pEl
        rw [if_neg (Ne.symm hmi), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega)]
      simp [hz]
  · simp

private theorem pTop_wI_esI_eq {k r j : ℕ} (q : PTop k r j) (b : Fin r) (hb : j ≤ b.val) (l : Fin (k + 1)) :
    pTop k r j q (wI k r l) (esI k r b) = q.1 ⟨b, hb⟩ l := by
  have h1 : (wI k r l).val = r + l.val := rfl
  have h2 : (esI k r b).val = 2 * r + k - b.val := rfl
  have := l.isLt
  have := b.isLt
  unfold pTop pOf pEl
  rw [if_neg (wI_ne_esI' l b), dif_neg (by omega), dif_pos (by omega)]
  have e1 : (⟨2 * r + k - (esI k r b).val, by omega⟩ : Fin r) = b := by
    apply Fin.ext
    show 2 * r + k - (2 * r + k - b.val) = b.val
    omega
  have e2 : (⟨(wI k r l).val - r, by omega⟩ : Fin (k + 1)) = l := by
    apply Fin.ext
    show r + l.val - r = l.val
    omega
  have hb' : j ≤ 2 * r + k - (esI k r b).val := by omega
  simp only [e1, e2, dif_pos hb']

private theorem crd_mulVec_bvec_eI_eq_upperIn {k r j : ℕ} (β : Fin r → ℕ) (q : (UTin β → ℂ) × PTop k r j) (a b : Fin r) :
    (crd k r j β q *ᵥ bvec (eI k r b)) (eI k r a) = upperIn β q.1 a b := by
  have ha : (eI k r a).val = a.val := rfl
  have hb : (eI k r b).val = b.val := rfl
  have := a.isLt
  have := b.isLt
  rw [crd, ← Matrix.mulVec_mulVec, pTop_mulVec_eq_of_vanishing, mulVec_bvec_lemma_2]
  · unfold uEmb
    rw [dif_pos (by omega)]
    rfl
  · intro m hm
    rw [mulVec_bvec_lemma_2]
    unfold uEmb
    have hne : m ≠ eI k r b := by
      intro h
      have := congrArg Fin.val h
      omega
    rw [dif_neg (by omega), dif_neg (by omega), if_neg hne]

theorem coords_top : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V) (r : ℕ) (N : NF H r) (k : ℕ) (σ : K →+* ℂ) (ρ : ℝ) (β : Fin r → ℕ) (Φ : V → Fin (2 * r + k + 1) → ℂ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mat k r), 0 < ρ → IsFrameOf N k σ ρ β Φ z z' g → ∀ (s : V ≃ₗ[K] V) (q : (UTin β → ℂ) × PTop k r N.j), (∀ x, crd k r N.j β q *ᵥ Φ x = Φ (s x)) → (∀ (i : UTin β) (u : Fin r → K), s (N.F.e i.1.1.2.castSucc) = N.F.e i.1.1.2.castSucc + ∑ c, u c • N.F.e c.castSucc → q.1 i = ((ρ ^ (i.1.1.2.val - i.1.1.1.val) : ℝ) : ℂ) * σ (u i.1.1.1)) ∧ (q.1 = 0 → ∀ a : Fin r, s (N.F.e a.castSucc) = N.F.e a.castSucc) ∧ (q.1 = 0 → ∀ (b : {a : Fin r // N.j ≤ a.val}) (y : V), s (N.ist b.1) - N.ist b.1 - y ∈ II N.F N.F' → q.2.1 b = ((ρ ^ (r - b.1.val) : ℝ) : ℂ) • fun l => Φ y (wI k r l)) := by
  intro K V _ _ _ _ _ _ _ _ H r N k σ ρ β Φ z z' g hρ hF s q hq
  obtain ⟨hR, -, -, -, -, hE, hI, -, -⟩ := hF
  obtain ⟨hadd, hsmul, -, -⟩ := id hR
  have hv : ∀ a : Fin r, Φ (N.F.e a.castSucc) = ((ρ ^ (r - a.val) : ℝ) : ℂ) • bvec (eI k r a) :=
    fun a => (hE a).1
  have hρc : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨⟨⟨a, b⟩, hab⟩, hβ⟩ u hsu
    dsimp only at hab hβ hsu ⊢
    have hab' : a.val < b.val := hab
    have hcol : upperIn β q.1 a b = q.1 ⟨⟨(a, b), hab⟩, hβ⟩ := by
      simp [upperIn, upper, hab, hβ]
    have key := congrFun (hq (N.F.e b.castSucc)) (eI k r a)
    rw [hsu, hadd, RealMat.phi_sum hR, hv b, Matrix.mulVec_smul, Pi.smul_apply, crd_mulVec_bvec_eI_eq_upperIn, hcol] at key
    simp only [hsmul, hv, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, bvec, Pi.single_apply,
      eI_inj', hab.ne, if_false, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      zero_add, Complex.ofReal_pow] at key
    have hne : (ρ : ℂ) ^ (r - b.val) ≠ 0 := pow_ne_zero _ hρc
    have hpow : (ρ : ℂ) ^ (r - a.val) = (ρ : ℂ) ^ (r - b.val) * (ρ : ℂ) ^ (b.val - a.val) := by
      rw [← pow_add]
      congr 1
      have := b.isLt
      omega
    push_cast
    apply mul_left_cancel₀ hne
    linear_combination key + σ (u a) * hpow
  · intro h0 a
    apply RealMat.phi_inj hR
    rw [← hq, crd_of_zero β q h0, hv a, Matrix.mulVec_smul, pTop_mulVec_eq_of_vanishing]
    intro m hm
    simp only [bvec, Pi.single_apply]
    rw [if_neg]
    intro h
    have h1 := congrArg Fin.val h
    have h2 : (eI k r a).val = a.val := rfl
    have := a.isLt
    omega
  · rintro h0 ⟨b, hb⟩ y hy
    dsimp only at hy ⊢
    funext l
    have hw : s (N.ist b) - N.ist b - y ∈ N.F.Xa r := (Submodule.mem_inf.mp hy).1
    have hz := RealMat.coord_of_mem_Xa hR (fun a => (hE a).1) hw (wI k r l)
      (by have : (wI k r l).val = r + l.val := rfl; omega)
    have key := congrFun (hq (N.ist b)) (wI k r l)
    have hsplit : s (N.ist b) = N.ist b + y + (s (N.ist b) - N.ist b - y) := by abel
    rw [hsplit, hadd, hadd, hI b hb, crd_of_zero β q h0, Matrix.mulVec_smul, Pi.smul_apply, mulVec_bvec_lemma_2,
      pTop_wI_esI_eq q.2 b hb l] at key
    simp only [Pi.add_apply, hz, add_zero, Pi.smul_apply, bvec, Pi.single_apply, wI_ne_esI' l b, if_false,
      smul_eq_mul, mul_zero, zero_add, Complex.ofReal_inv, Complex.ofReal_pow] at key
    simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_pow]
    have hne : (ρ : ℂ) ^ (r - b.val) ≠ 0 := pow_ne_zero _ hρc
    rw [← key, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]

end GlobalTheory.DegVol.RefCovTop
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPlacesMatchIsomorphicCMInstances
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

namespace GlobalTheory.LeviIso.Places

noncomputable def placeEquiv (I : AutInst) : InfinitePlace I.F ≃ InfinitePlace I.E :=
  (Equiv.ofBijective _ (GlobalTheory.Count.FrameMajorant.comap_bijective I)).symm

theorem placeEquiv_apply (I : AutInst) (v : InfinitePlace I.F) :
    placeEquiv I v = InfinitePlace.mk (I.φ v) := by
  have h : (I.φ v).comp (algebraMap I.F I.E) = v.embedding := RingHom.ext (I.φ_over v)
  rw [placeEquiv, Equiv.symm_apply_eq]
  show v = (InfinitePlace.mk (I.φ v)).comap (algebraMap I.F I.E)
  rw [InfinitePlace.comap_mk, h, InfinitePlace.mk_embedding]

noncomputable def comapEquiv {K L : Type} [Field K] [Field L] (e : K ≃+* L) :
    InfinitePlace L ≃ InfinitePlace K where
  toFun w := w.comap (e : K →+* L)
  invFun w := w.comap (e.symm : L →+* K)
  left_inv w := by
    beta_reduce; rw [← InfinitePlace.comap_comp]; simp [InfinitePlace.comap_id]
  right_inv w := by
    beta_reduce; rw [← InfinitePlace.comap_comp]; simp [InfinitePlace.comap_id]

theorem exists_twist {K : Type} [Field K] (φ ψ : K →+* ℂ)
    (h : InfinitePlace.mk φ = InfinitePlace.mk ψ) :
    ∃ τ : ℂ →+* ℂ, (τ = RingHom.id ℂ ∨ τ = starRingEnd ℂ) ∧ ∀ y, φ y = τ (ψ y) := by
  rcases InfinitePlace.mk_eq_iff.mp h with h' | h'
  · exact ⟨RingHom.id ℂ, Or.inl rfl, fun y => by rw [h', RingHom.id_apply]⟩
  · refine ⟨starRingEnd ℂ, Or.inr rfl, fun y => ?_⟩
    rw [← h', ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]

theorem places_match : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E), (∀ y, e (star y) = star (e y)) → ∃ (β : InfinitePlace I.F ≃ InfinitePlace I.E) (σ : InfinitePlace I.F ≃ InfinitePlace I₀.F) (τ τ₀ : InfinitePlace I.F → (ℂ →+* ℂ)), (∀ v, τ v = RingHom.id ℂ ∨ τ v = starRingEnd ℂ) ∧ (∀ v, τ₀ v = RingHom.id ℂ ∨ τ₀ v = starRingEnd ℂ) ∧ (∀ v y, I.φ v y = τ v ((β v).embedding y)) ∧ ∀ v y, I.φ v (e y) = τ₀ v (I₀.φ (σ v) y) := by
  intro I I₀ e _

  let σ : InfinitePlace I.F ≃ InfinitePlace I₀.F :=
    (placeEquiv I).trans ((comapEquiv e).trans (placeEquiv I₀).symm)
  have h1 : ∀ v : InfinitePlace I.F, ∃ τ : ℂ →+* ℂ, (τ = RingHom.id ℂ ∨ τ = starRingEnd ℂ) ∧
      ∀ y, I.φ v y = τ ((placeEquiv I v).embedding y) := fun v =>
    exists_twist _ _ (by rw [InfinitePlace.mk_embedding, placeEquiv_apply])
  have h2 : ∀ v : InfinitePlace I.F, ∃ τ : ℂ →+* ℂ, (τ = RingHom.id ℂ ∨ τ = starRingEnd ℂ) ∧
      ∀ y, I.φ v (e y) = τ (I₀.φ (σ v) y) := by
    intro v
    refine exists_twist ((I.φ v).comp (e : I₀.E →+* I.E)) (I₀.φ (σ v)) ?_
    rw [← placeEquiv_apply]
    simp only [σ, Equiv.trans_apply, Equiv.apply_symm_apply]
    rw [placeEquiv_apply]
    show _ = (InfinitePlace.mk (I.φ v)).comap (e : I₀.E →+* I.E)
    rw [InfinitePlace.comap_mk]
  choose τ hτ using h1
  choose τ₀ hτ₀ using h2
  exact ⟨placeEquiv I, σ, τ, τ₀, fun v => (hτ v).1, fun v => (hτ₀ v).1, fun v => (hτ v).2,
    fun v => (hτ₀ v).2⟩

end GlobalTheory.LeviIso.Places
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.VolumeGramConditionCodimTwoThreeStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.volume_gramCondition_codim_two_three : ∀ (k r : ℕ), 1 ≤ r → 2 * r + 6 ≤ k → ∀ m ∈ UH (Hb k), ∀ P₀ : Submodule ℂ (EuclideanSpace ℂ (Fin (k + 1))), (Module.finrank ℂ P₀ = k - 2 ∨ Module.finrank ℂ P₀ = k - 1) → volume {B : Fin r → Fin (k + 1) → ℂ | gramProj P₀ (fun b => m⁻¹ *ᵥ B b) = 0} = 0 ∧ ∀ R' y : ℝ, 1 ≤ R' → 0 < y → volume {B : Fin r → Fin (k + 1) → ℂ | (∀ b, eucl (m⁻¹ *ᵥ B b) ≤ R') ∧ y < gramProj P₀ (fun b => m⁻¹ *ᵥ B b) ∧ gramProj P₀ (fun b => m⁻¹ *ᵥ B b) ≤ 2 * y} ≤ ENNReal.ofReal ((Real.pi * R' ^ 2) ^ (3 * r) * 4 * R' ^ (2 * r ^ 2 + 2 * r) * Real.pi ^ (r ^ 2) * (Real.pi * Real.exp 1 / ((k - 2 - r : ℕ) : ℝ)) ^ (r * (k - 2 - r)) * (2 * y) ^ (2 * (k - 2 - r))) := by
  first | exact @GlobalTheory.Amp.GramVol.vol_gram_codim_three | exact GlobalTheory.Amp.GramVol.vol_gram_codim_three | (intros; apply GlobalTheory.Amp.GramVol.vol_gram_codim_three <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.VolumeProductOverGradingLayersStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.volume_product_over_grading_layers : ∀ (ι : Type) [Fintype ι] (d m : ℕ) (deg : Fin d → ℕ) (D : ∀ c : ℕ, Set (ι → {i : Fin d // deg i = c} → ℝ)), (ι → ∀ i, deg i < m) → (∀ c, MeasurableSet (D c)) → volume {x : ι → Fin d → ℝ | ∀ c < m, (fun v (i : {i : Fin d // deg i = c}) => x v i.1) ∈ D c} = ∏ c ∈ Finset.range m, volume (D c) := by
  first | exact @GlobalTheory.LayerBox.volume_layer_box | exact GlobalTheory.LayerBox.volume_layer_box | (intros; apply GlobalTheory.LayerBox.volume_layer_box <;> assumption)
end

