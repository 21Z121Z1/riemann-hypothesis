import Formalism.HermitianCurvature.StatementW
import Mathlib
import Formalism.HermitianCurvature.StatementTA

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.FirstEmbeddingOne
section
namespace Formalism.FourierDecayAlt.P.W

open Matrix Formalism.YangianSpanCharacter.T NumberField Formalism.FourierDecayAlt.W

section Words

variable {R B : Type} [CommRing R] [Ring B] [Algebra R B]

theorem first_embedding_mul (M N : Matrix (Fin 2) (Fin 2) B) : E1 (M * N) = E1 M * E1 N := by
  unfold Formalism.YangianSpanCharacter.T.E1
  ext ⟨i, k⟩ ⟨j, l⟩
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    simp [Matrix.mul_apply, Matrix.one_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

theorem entries_mem_mul (M N : Matrix (Fin 2) (Fin 2) B) : E2 (M * N) = E2 M * E2 N := by
  unfold Formalism.YangianSpanCharacter.T.E2
  ext ⟨i, k⟩ ⟨j, l⟩
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    simp [Matrix.mul_apply, Matrix.one_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

theorem first_embedding_one : E1 (1 : Matrix (Fin 2) (Fin 2) B) = 1 := by
  unfold Formalism.YangianSpanCharacter.T.E1
  ext ⟨i, k⟩ ⟨j, l⟩
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    simp [Matrix.mul_apply, Matrix.one_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

theorem entries_mem_one : E2 (1 : Matrix (Fin 2) (Fin 2) B) = 1 := by
  unfold Formalism.YangianSpanCharacter.T.E2
  ext ⟨i, k⟩ ⟨j, l⟩
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    simp [Matrix.mul_apply, Matrix.one_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

theorem first_second_embedding_commute (A C : Matrix (Fin 2) (Fin 2) B)
    (h : ∀ i j k l, A i j * C k l = C k l * A i j) : E1 A * E2 C = E2 C * E1 A := by
  unfold Formalism.YangianSpanCharacter.T.E1 Formalism.YangianSpanCharacter.T.E2
  ext ⟨i, k⟩ ⟨j, l⟩
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, h]

theorem transpose_mul_of_comm (A C : Matrix (Fin 2) (Fin 2) B)
    (h : ∀ i j k l, A i j * C k l = C k l * A i j) : (A * C)ᵀ = Cᵀ * Aᵀ := by
  ext i j
  simp [Matrix.mul_apply, Fin.sum_univ_two, h]

theorem isDet_iff (M : R → Matrix (Fin 2) (Fin 2) B) (q : R → R) :
    IsDet M q ↔ ∀ Y : R, (M (Y + 1))ᵀ * Formalism.YangianSpanCharacter.T.J B * M Y = q Y • Formalism.YangianSpanCharacter.T.J B ∧
      M Y * Formalism.YangianSpanCharacter.T.J B * (M (Y + 1))ᵀ = q Y • Formalism.YangianSpanCharacter.T.J B := by
  unfold Formalism.FourierDecayAlt.W.IsDet
  simp only [algebraMap_smul]

private theorem rtt_relation_mul_of_rtt_of_commute {A : Type*} [Ring A] (P a b c d : A) (hM : P * a * c = c * a * P)
    (hN : P * b * d = d * b * P) (c1 : b * c = c * b) (c2 : a * d = d * a) :
    P * (a * b) * (c * d) = c * d * (a * b) * P := by
  calc P * (a * b) * (c * d) = P * a * (b * c) * d := by simp only [mul_assoc]
    _ = P * a * (c * b) * d := by rw [c1]
    _ = (P * a * c) * b * d := by simp only [mul_assoc]
    _ = (c * a * P) * b * d := by rw [hM]
    _ = c * a * (P * b * d) := by simp only [mul_assoc]
    _ = c * a * (d * b * P) := by rw [hN]
    _ = c * (a * d) * b * P := by simp only [mul_assoc]
    _ = c * (d * a) * b * P := by rw [c2]
    _ = c * d * (a * b) * P := by simp only [mul_assoc]

theorem isRTT_mul (M N : R → Matrix (Fin 2) (Fin 2) B) (hM : IsRTT M) (hN : IsRTT N)
    (hc : EntriesCommute M N) : IsRTT (fun Y => M Y * N Y) := by
  unfold Formalism.FourierDecayAlt.W.IsRTT at *
  intro Y Y'
  simp only [first_embedding_mul, entries_mem_mul]
  exact rtt_relation_mul_of_rtt_of_commute _ _ _ _ _ (hM Y Y') (hN Y Y')
    (first_second_embedding_commute _ _ (fun i j k l => (hc Y Y' k l i j).symm)) (first_second_embedding_commute _ _ (fun i j k l => hc Y' Y i j k l))

private theorem mul_Jm_mul_eq_smul_of_Jm_similitudes_left {A : Type*} [Ring A] [Algebra R A] (a a' b b' Jm : A) (s t : R)
    (h1 : a' * Jm * a = s • Jm) (h3 : b' * Jm * b = t • Jm) : b' * a' * Jm * (a * b) = (s * t) • Jm := by
  calc b' * a' * Jm * (a * b) = b' * (a' * Jm * a) * b := by simp only [mul_assoc]
    _ = b' * (s • Jm) * b := by rw [h1]
    _ = s • (b' * Jm * b) := by rw [mul_smul_comm, smul_mul_assoc]
    _ = s • (t • Jm) := by rw [h3]
    _ = (s * t) • Jm := by rw [smul_smul]

private theorem mul_Jm_mul_eq_smul_of_Jm_similitudes_right {A : Type*} [Ring A] [Algebra R A] (a a' b b' Jm : A) (s t : R)
    (h2 : a * Jm * a' = s • Jm) (h4 : b * Jm * b' = t • Jm) : a * b * Jm * (b' * a') = (s * t) • Jm := by
  calc a * b * Jm * (b' * a') = a * (b * Jm * b') * a' := by simp only [mul_assoc]
    _ = a * (t • Jm) * a' := by rw [h4]
    _ = t • (a * Jm * a') := by rw [mul_smul_comm, smul_mul_assoc]
    _ = t • (s • Jm) := by rw [h2]
    _ = (s * t) • Jm := by rw [smul_smul, mul_comm]

theorem isDet_mul (M N : R → Matrix (Fin 2) (Fin 2) B) (q qN : R → R) (hM : IsDet M q)
    (hN : IsDet N qN) (hc : EntriesCommute M N) :
    IsDet (fun Y => M Y * N Y) (fun Y => q Y * qN Y) := by
  rw [isDet_iff] at hM hN ⊢
  intro Y
  obtain ⟨h1, h2⟩ := hM Y
  obtain ⟨h3, h4⟩ := hN Y
  have ht := transpose_mul_of_comm (M (Y + 1)) (N (Y + 1)) (fun i j k l => hc (Y + 1) (Y + 1) i j k l)
  try beta_reduce
  refine ⟨?_, ?_⟩
  · rw [ht]
    exact mul_Jm_mul_eq_smul_of_Jm_similitudes_left _ _ _ _ _ _ _ h1 h3
  · rw [ht]
    exact mul_Jm_mul_eq_smul_of_Jm_similitudes_right _ _ _ _ _ _ _ h2 h4

theorem entriesCommute_prod (M : R → Matrix (Fin 2) (Fin 2) B)
    (L : List ((R → Matrix (Fin 2) (Fin 2) B) × (R → R)))
    (h : ∀ y ∈ L, EntriesCommute M y.1) :
    EntriesCommute M (fun Y => (L.map (fun x => x.1 Y)).prod) := by
  unfold Formalism.FourierDecayAlt.W.EntriesCommute at *
  intro Y Y' i j k l
  induction L generalizing k l with
  | nil =>
    simp only [List.map_nil, List.prod_nil, Matrix.one_apply]
    split_ifs <;> simp
  | cons x t ih =>
    simp only [List.map_cons, List.prod_cons, Matrix.mul_apply]
    have hx := h x (by simp)
    have ht : ∀ y ∈ t, ∀ (Y Y' : R) (i j k l : Fin 2), M Y i j * y.1 Y' k l = y.1 Y' k l * M Y i j :=
      fun y hy => h y (by simp [hy])
    exact (Commute.sum_right _ _ _ (fun m _ => Commute.mul_right (hx Y Y' i j k m) (ih ht m l))).eq

set_option maxHeartbeats 800000 in

theorem wordFusion_list (L : List ((R → Matrix (Fin 2) (Fin 2) B) × (R → R)))
    (h : ∀ x ∈ L, IsRTT x.1 ∧ IsDet x.1 x.2)
    (hp : L.Pairwise (fun x y => EntriesCommute x.1 y.1)) :
    IsRTT (fun Y => (L.map (fun x => x.1 Y)).prod) ∧
      IsDet (fun Y => (L.map (fun x => x.1 Y)).prod) (fun Y => (L.map (fun x => x.2 Y)).prod) := by
  induction L with
  | nil =>
    refine ⟨?_, ?_⟩
    · unfold Formalism.FourierDecayAlt.W.IsRTT
      intro Y Y'
      simp [first_embedding_one, entries_mem_one]
    · rw [isDet_iff]
      intro Y
      simp
  | cons x t ih =>
    have hx := h x (by simp)
    have ht : ∀ y ∈ t, IsRTT y.1 ∧ IsDet y.1 y.2 := fun y hy => h y (by simp [hy])
    rw [List.pairwise_cons] at hp
    obtain ⟨ih1, ih2⟩ := ih ht hp.2
    have hc := entriesCommute_prod x.1 t hp.1
    have e1 := isRTT_mul x.1 _ hx.1 ih1 hc
    have e2 := isDet_mul x.1 _ x.2 _ hx.2 ih2 hc
    simp only [List.map_cons, List.prod_cons]
    refine ⟨?_, ?_⟩
    · first
      | exact e1
      | simpa using e1
    · first
      | exact e2
      | simpa using e2

end Words

section Norm

theorem absNorm_le_norm {E : Type} [Field E] [NumberField E]
    (b : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hb : b ≠ 0) (l : E) (hl : l ∈ b) (hl0 : l ≠ 0) :
    (FractionalIdeal.absNorm b : ℝ) ≤ |(Algebra.norm ℚ l : ℝ)| := by
  have hsp : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) l ≤ b :=
    FractionalIdeal.spanSingleton_le_iff_mem.mpr hl
  have hs0 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) l ≠ 0 := by
    rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]
    exact hl0
  have hbc : b * (b⁻¹ * FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) l) =
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) l := by
    rw [← mul_assoc, mul_inv_cancel₀ hb, one_mul]
  have hc1 : b⁻¹ * FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) l ≤ 1 := by
    calc b⁻¹ * FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) l ≤ b⁻¹ * b := by
          first
          | exact FractionalIdeal.mul_left_mono _ hsp
          | exact mul_le_mul_left' hsp _
          | exact mul_le_mul' le_rfl hsp
          | exact mul_le_mul_left hsp _
          | (rw [← FractionalIdeal.coe_le_coe, FractionalIdeal.coe_mul, FractionalIdeal.coe_mul]
             exact Submodule.mul_le_mul_right (FractionalIdeal.coe_le_coe.mpr hsp))
      _ = 1 := inv_mul_cancel₀ hb
  obtain ⟨I, hI⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hc1
  have hI0 : I ≠ ⊥ := by
    rintro rfl
    apply hs0
    rw [← hbc, ← hI]
    simp
  have key : FractionalIdeal.absNorm b * FractionalIdeal.absNorm
      (b⁻¹ * FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) l) = |Algebra.norm ℚ l| := by
    rw [← map_mul, hbc, FractionalIdeal.absNorm_span_singleton]
  have hx : (1 : ℚ) ≤ FractionalIdeal.absNorm
      (b⁻¹ * FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) l) := by
    rw [← hI, FractionalIdeal.coeIdeal_absNorm]
    have : Ideal.absNorm I ≠ 0 := fun h0 => hI0 (Ideal.absNorm_eq_zero_iff.mp h0)
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  have ha : (0 : ℚ) ≤ FractionalIdeal.absNorm b := FractionalIdeal.absNorm_nonneg b
  have hq : (FractionalIdeal.absNorm b : ℚ) ≤ |Algebra.norm ℚ l| := by
    calc (FractionalIdeal.absNorm b : ℚ) = FractionalIdeal.absNorm b * 1 := (mul_one _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hx ha
      _ = _ := key
  exact_mod_cast hq

end Norm

end Formalism.FourierDecayAlt.P.W

namespace Formalism.FourierDecayAlt.P

open NumberField

theorem word_fusion : Formalism.FourierDecayAlt.W.WordFusion := by
  unfold Formalism.FourierDecayAlt.W.WordFusion
  intro R B _ _ _ L h hp
  exact Formalism.FourierDecayAlt.P.W.wordFusion_list L h hp

theorem norm_lower_bound : Formalism.FourierDecayAlt.W.NormLower := by
  unfold Formalism.FourierDecayAlt.W.NormLower
  intro E _ _ _ aa l hl hl0
  have hb : aa ≠ 0 := by
    rintro rfl
    first
    | exact hl0 ((FractionalIdeal.mem_zero_iff _).mp hl)
    | exact hl0 (FractionalIdeal.mem_zero_iff.mp hl)
    | (simp at hl; exact hl0 hl)
  have h1 := Formalism.FourierDecayAlt.P.W.absNorm_le_norm aa hb l hl hl0
  have hsq : (∏ w : NumberField.InfinitePlace E, w l) ^ 2 =
      ∏ w : NumberField.InfinitePlace E, w l ^ w.mult := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl (fun w _ => ?_)
    have hc : ¬ w.IsReal :=
      NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr (NumberField.IsTotallyComplex.isComplex w)
    first
    | rw [NumberField.InfinitePlace.mult, if_neg hc]
    | simp [NumberField.InfinitePlace.mult, hc]
  have hprod : (∏ w : NumberField.InfinitePlace E, w l) ^ 2 = |(Algebra.norm ℚ l : ℝ)| := by
    rw [hsq, NumberField.InfinitePlace.prod_eq_abs_norm]
    first
    | rfl
    | simp
    | (push_cast; rfl)
  have hnn : 0 ≤ ∏ w : NumberField.InfinitePlace E, w l := by
    refine Finset.prod_nonneg (fun w _ => ?_)
    first
    | positivity
    | exact w.nonneg l
    | exact AbsoluteValue.nonneg _ _
  rw [← Real.sqrt_sq hnn, hprod]
  exact Real.sqrt_le_sqrt h1

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.GramConjugationNorm
section
namespace Formalism.FourierDecayAlt.P.GramConjugationNorm

open Finset Filter Topology Formalism.FourierDecayAlt.TA
open scoped InnerProductSpace ComplexConjugate

theorem isPt_PT {E : Type} [Field E] [DecidableEq E] (Sg : ℕ → ℕ → Finset E) (hNZ : NZSg Sg) :
    ∀ n p, p ∈ PT Sg n → IsPt n p := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro p hp
    cases n with
    | zero =>
      simp [PT] at hp; subst hp; exact ⟨by simp [lvl], by simp⟩
    | succ n =>
      rw [PT] at hp
      simp only [mem_biUnion, mem_attach, true_and, mem_image, Subtype.exists, mem_range] at hp
      obtain ⟨m, hm, h, hh, t, ht, rfl⟩ := hp
      have h0 := ih m (by omega) h hh
      refine ⟨?_, ?_⟩
      · have := h0.1
        simp only [lvl] at this
        simp [lvl, Formalism.FourierDecayAlt.TA.ext, this]; omega
      · intro b hb
        simp only [Formalism.FourierDecayAlt.TA.ext, List.mem_append, List.mem_singleton] at hb
        rcases hb with hb | rfl
        · exact h0.2 b hb
        · exact ⟨by simp; omega, hNZ _ _ t ht⟩

section gram
variable {E : Type} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem gram_re_nonneg (k : Pt E → Pt E → ℂ) (V : Pt E → H) (P : Finset (Pt E))
    (hk : PSDOn P k) : 0 ≤ (gram k V P).re := by
  classical
  let S : Submodule ℂ H := Submodule.span ℂ (V '' (P : Set (Pt E)))
  have : FiniteDimensional ℂ S :=
    FiniteDimensional.span_of_finite ℂ ((P.finite_toSet).image V)
  have hex : ∀ p, p ∈ P → ∃ v : S, (v : H) = V p :=
    fun p hp => ⟨⟨V p, Submodule.subset_span ⟨p, hp, rfl⟩⟩, rfl⟩
  choose! v hv using hex
  let b := stdOrthonormalBasis ℂ S
  have key : gram k V P =
      ∑ j, ∑ p ∈ P, ∑ p' ∈ P, conj (⟪b j, v p⟫_ℂ) * k p p' * ⟪b j, v p'⟫_ℂ := by
    unfold gram
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p hp => ?_
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p' hp' => ?_
    have h1 : ⟪V p, V p'⟫_ℂ = ⟪v p, v p'⟫_ℂ := by
      rw [← hv p hp, ← hv p' hp']; rfl
    rw [h1, ← b.sum_inner_mul_inner (v p) (v p'), Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_conj_symm]; ring
  rw [key, Complex.re_sum]
  exact Finset.sum_nonneg fun j _ => hk.2 (fun p => ⟪b j, v p⟫_ℂ)

theorem gram_conj (k : Pt E → Pt E → ℂ) (V : Pt E → H) (P : Finset (Pt E))
    (hk : PSDOn P k) : conj (gram k V P) = gram k V P := by
  unfold gram
  rw [map_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun p' hp' => ?_
  rw [map_mul, inner_conj_symm, hk.1 p hp p' hp']

theorem gram_norm (k : Pt E → Pt E → ℂ) (V : Pt E → H) (P : Finset (Pt E))
    (hk : PSDOn P k) : ‖gram k V P‖ = (gram k V P).re := by
  have h1 : (gram k V P).im = 0 := Complex.conj_eq_iff_im.1 (gram_conj k V P hk)
  have h2 : gram k V P = (((gram k V P).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [h1])
  rw [h2, Complex.norm_real, Complex.ofReal_re, Real.norm_eq_abs,
    abs_of_nonneg (gram_re_nonneg k V P hk)]

theorem gram_dom {ι : Type} (R : Finset ι) (c : ℝ) (k : Pt E → Pt E → ℂ)
    (T : ι → Pt E → Pt E → ℂ) (V : Pt E → H) (P : Finset (Pt E))
    (hk : PSDOn P (fun h h' => (c : ℂ) * k h h' - ∑ t ∈ R, T t h h')) :
    ∑ t ∈ R, (gram (T t) V P).re ≤ c * (gram k V P).re := by
  have h0 := gram_re_nonneg _ V P hk
  have h1 : gram (fun h h' => (c : ℂ) * k h h' - ∑ t ∈ R, T t h h') V P =
      (c : ℂ) * gram k V P - ∑ t ∈ R, gram (T t) V P := by
    unfold gram
    have h2 : ∑ t ∈ R, ∑ p ∈ P, ∑ p' ∈ P, T t p p' * ⟪V p, V p'⟫_ℂ =
        ∑ p ∈ P, ∑ p' ∈ P, ∑ t ∈ R, T t p p' * ⟪V p, V p'⟫_ℂ := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun p _ => Finset.sum_comm
    rw [h2, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p' _ => ?_
    rw [sub_mul, Finset.sum_mul, mul_assoc]
  rw [h1, Complex.sub_re, Complex.re_ofReal_mul, Complex.re_sum] at h0
  linarith

end gram

section words
variable {W : Type} [Fintype W]

theorem prob_le_wsup (len : W → ℕ) (B : ℕ) (th : W → ℝ) (hth : IsProb len B th) (g : W → ℝ) :
    ∑ w, th w * g w ≤ wsup len B g := by
  have h1 : ∀ w ∈ (Finset.univ : Finset W), th w * g w ≤ th w * wsup len B g := by
    intro w _
    by_cases h : th w = 0
    · simp [h]
    · exact mul_le_mul_of_nonneg_left
        (le_ciSup (f := fun w : {w // len w ≤ B} => g w.1) (Set.finite_range _).bddAbove
          ⟨w, hth.2.2 w h⟩) (hth.1 w)
  calc ∑ w, th w * g w ≤ ∑ w, th w * wsup len B g := Finset.sum_le_sum h1
    _ = wsup len B g := by rw [← Finset.sum_mul, hth.2.1, one_mul]

theorem avg_le {ι : Type} (R : Finset ι) (len : W → ℕ) (B : ℕ) (th : W → ℝ)
    (hth : IsProb len B th) (g : ι → W → ℝ) (S : W → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hdom : ∀ w', ∑ t0 ∈ R, g t0 w' ≤ c * S w') :
    ∑ t0 ∈ R, ∑ w', th w' * g t0 w' ≤ c * wsup len B S := by
  calc ∑ t0 ∈ R, ∑ w', th w' * g t0 w' = ∑ w', th w' * ∑ t0 ∈ R, g t0 w' := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun w' _ => (Finset.mul_sum _ _ _).symm
    _ ≤ ∑ w', th w' * (c * S w') :=
        Finset.sum_le_sum fun w' _ => mul_le_mul_of_nonneg_left (hdom w') (hth.1 w')
    _ = c * ∑ w', th w' * S w' := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun w' _ => by ring
    _ ≤ c * wsup len B S := mul_le_mul_of_nonneg_left (prob_le_wsup len B th hth S) hc

end words

end Formalism.FourierDecayAlt.P.GramConjugationNorm

namespace Formalism.FourierDecayAlt.P

open Finset Filter Topology Formalism.FourierDecayAlt.TA Formalism.FourierDecayAlt.P.GramConjugationNorm
open scoped InnerProductSpace ComplexConjugate

theorem cosets_last_block_size_ge_two : Formalism.FourierDecayAlt.TA.CosetsS := by
  intro E _ _ H _ _ W _ len Kl Nw D Sg Φ bd4 i s w R hNZ hs hsi hir hK hA hE hb hEst hw hR
  classical
  obtain ⟨th, hth, hest⟩ := hEst w hw
  obtain ⟨hA1, -, -, hA4⟩ := hA i s (by omega) hsi hir
  have hHd : ∀ h ∈ PT Sg (i - s), IsPt (i - s) h := isPt_PT Sg hNZ _
  have he : 0 ≤ 1 + D.e i := by have := (hE i (by omega) hir).1; linarith
  have step1 : Cosets D Sg Φ w i s R ≤
      ∑ t0 ∈ R, bd4 * ∑ w', th w' * (gram (D.Th i s t0) (Φ w') (PT Sg (i - s))).re := by
    unfold Cosets
    refine Finset.sum_le_sum fun t0 _ => ?_
    exact hest _ _ hHd (hA1 t0 _ hHd) t0 _ (fun t ht => by
      rw [Finset.mem_filter] at ht; exact ⟨hNZ _ _ t ht.1, ht.2⟩)
  have step2 := avg_le R len (len w + (s + 1) * Kl) th hth
    (fun t0 w' => (gram (D.Th i s t0) (Φ w') (PT Sg (i - s))).re)
    (fun w' => Slev D Sg Φ w' (i - s)) (1 + D.e i) he
    (fun w' => gram_dom R (1 + D.e i) (D.K (i - s)) (D.Th i s) (Φ w') _ (hA4 R _ hR hHd))
  calc Cosets D Sg Φ w i s R
      ≤ ∑ t0 ∈ R, bd4 * ∑ w', th w' * (gram (D.Th i s t0) (Φ w') (PT Sg (i - s))).re := step1
    _ = bd4 * ∑ t0 ∈ R, ∑ w', th w' * (gram (D.Th i s t0) (Φ w') (PT Sg (i - s))).re := by
        rw [Finset.mul_sum]
    _ ≤ bd4 * ((1 + D.e i) * wsup len (len w + (s + 1) * Kl) (fun w' => Slev D Sg Φ w' (i - s))) :=
        mul_le_mul_of_nonneg_left step2 hb
    _ = _ := by ring

theorem cosets_last_block_size_one : Formalism.FourierDecayAlt.TA.CosetsOne := by
  intro E _ _ H _ _ W _ len Kl Nw D Sg Φ tr Pat1 pat1 c1 ep1 i w R hNZ hi hir hK hA hE hP hEst hLat
    hw hR
  classical
  obtain ⟨th, hth, hest⟩ := hEst w hw
  obtain ⟨hA1, -, -, hA4⟩ := hA i 1 le_rfl hi hir
  have hHd : ∀ h ∈ PT Sg (i - 1), IsPt (i - 1) h := isPt_PT Sg hNZ _
  have he : 0 ≤ 1 + D.e i := by have := (hE i hi hir).1; linarith
  set Hd := PT Sg (i - 1) with hHdd
  set g : E → W → ℝ := fun t0 w' => (gram (D.Th i 1 t0) (Φ w') Hd).re with hg
  have hg0 : ∀ t0 w', 0 ≤ g t0 w' := fun t0 w' => gram_re_nonneg _ _ _ (hA1 t0 Hd hHd)
  have hdom : ∀ w', ∑ t0 ∈ R, g t0 w' ≤ (1 + D.e i) * Slev D Sg Φ w' (i - 1) :=
    fun w' => gram_dom R (1 + D.e i) (D.K (i - 1)) (D.Th i 1) (Φ w') _ (hA4 R _ hR hHd)
  set M : ℝ := wsup len (len w + Kl) (fun w' => Slev D Sg Φ w' (i - 1)) with hM
  have hM0 : 0 ≤ M :=
    Real.iSup_nonneg fun w' => gram_re_nonneg _ _ _ (hK.2 (i - 1) (by omega) Hd hHd)
  have hC0 : 0 ≤ (1 + D.e i) * M := mul_nonneg he hM0

  let f : E → E → ℝ := fun t0 l =>
    if l ∈ D.Lv i ∧ l ≠ 0 then c1 l * ∑ w', th (pat1 l) w' * g t0 w' else 0
  have hf0 : ∀ t0 l, 0 ≤ f t0 l := by
    intro t0 l
    simp only [f]
    split_ifs
    · exact mul_nonneg (hLat.1 l)
        (Finset.sum_nonneg fun w' _ => mul_nonneg ((hth _).1 w') (hg0 t0 w'))
    · exact le_rfl
  have hsumf : ∀ l, ∑ t0 ∈ R, f t0 l ≤
      if l ∈ D.Lv i ∧ l ≠ 0 then c1 l * ((1 + D.e i) * M) else 0 := by
    intro l
    simp only [f]
    split_ifs with h
    · rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (avg_le R len (len w + Kl) (th (pat1 l)) (hth _) g _ _ he hdom) (hLat.1 l)
    · simp
  have hpart : ∀ u : Finset E, ∑ l ∈ u, ∑ t0 ∈ R, f t0 l ≤ ep1 * ((1 + D.e i) * M) := by
    intro u
    calc ∑ l ∈ u, ∑ t0 ∈ R, f t0 l
        ≤ ∑ l ∈ u, if l ∈ D.Lv i ∧ l ≠ 0 then c1 l * ((1 + D.e i) * M) else 0 :=
          Finset.sum_le_sum fun l _ => hsumf l
      _ = (∑ l ∈ u.filter (fun l => l ∈ D.Lv i ∧ l ≠ 0), c1 l) * ((1 + D.e i) * M) := by
          rw [← Finset.sum_filter, Finset.sum_mul]
      _ ≤ ep1 * ((1 + D.e i) * M) :=
          mul_le_mul_of_nonneg_right
            (hLat.2 _ fun x hx => (Finset.mem_filter.1 hx).2) hC0
  have hsummable : ∀ t0 ∈ R, Summable (f t0) := by
    intro t0 ht0
    refine summable_of_sum_le (hf0 t0) (c := ep1 * ((1 + D.e i) * M)) fun u => ?_
    refine le_trans (Finset.sum_le_sum fun l _ => ?_) (hpart u)
    exact Finset.single_le_sum (f := fun t => f t l) (fun t _ => hf0 t l) ht0
  have hcls : ∀ t0 ∈ R, ∑ t ∈ (Sg i 1).filter (fun t => t - t0 ∈ D.La i 1),
      (Nst (Φ w) Hd (D.Th i 1 t0) 1 t t).re ≤ g t0 w + ∑' l, f t0 l := by
    intro t0 ht0
    have hpsd := hA1 t0 Hd hHd
    obtain ⟨h0, hl⟩ := hest Hd (D.Th i 1 t0) hHd hpsd
    have := hP w Hd (D.Th i 1 t0) hHd hpsd t0 ((Sg i 1).filter (fun t => t - t0 ∈ D.La i 1))
      (fun t ht => by rw [Finset.mem_filter] at ht; exact ⟨hNZ _ _ t ht.1, ht.2⟩)
      (∑' l, f t0 l) (fun L hL => by
        calc ∑ l ∈ L, ‖tr w Hd (D.Th i 1 t0) l‖ ≤ ∑ l ∈ L, f t0 l := by
              refine Finset.sum_le_sum fun l hlL => ?_
              simp only [f, if_pos (hL l hlL)]
              exact hl l (hL l hlL).1 (hL l hlL).2
          _ ≤ ∑' l, f t0 l := (hsummable t0 ht0).sum_le_tsum L (fun l _ => hf0 t0 l))
    rwa [h0, gram_norm _ _ _ hpsd] at this
  have htsum : ∑ t0 ∈ R, ∑' l, f t0 l ≤ ep1 * ((1 + D.e i) * M) := by
    rw [← Summable.tsum_finsetSum hsummable]
    exact Real.tsum_le_of_sum_le (fun l => Finset.sum_nonneg fun t0 _ => hf0 t0 l) hpart
  calc Cosets D Sg Φ w i 1 R ≤ ∑ t0 ∈ R, (g t0 w + ∑' l, f t0 l) := by
        unfold Cosets
        refine Finset.sum_le_sum fun t0 ht0 => ?_
        convert hcls t0 ht0
    _ = ∑ t0 ∈ R, g t0 w + ∑ t0 ∈ R, ∑' l, f t0 l := Finset.sum_add_distrib
    _ ≤ (1 + D.e i) * Slev D Sg Φ w (i - 1) + ep1 * ((1 + D.e i) * M) :=
        add_le_add (hdom w) htsum
    _ = _ := by ring

end Formalism.FourierDecayAlt.P
end

