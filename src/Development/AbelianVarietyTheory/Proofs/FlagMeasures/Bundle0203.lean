import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FirstSlotSliceSlotMixedCasimirZero
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0004
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0003
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactCasimirHighestWeight
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0171
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0178
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0159
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0146
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0164
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaDecompComplexifiedMaxCompact
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0176
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TranslatedLatticeAtInfinityFullCovolumeDual
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0183
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0133

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NotCdomAdd
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.Jet.KType

theorem cdom_step {n : ℕ} {ε : Fin n → Bool} {ν μ : Fin n → ℝ} (h : CDom ε ν μ) {a b : Fin n}
    (hab : a < b) (he : ε a = ε b) : CDom ε (ν - Formalism.REAL.root a b) μ := by
  obtain ⟨c, hc, hs⟩ := h
  refine ⟨fun i j => c i j + (if j = b then if i = a then 1 else 0 else 0), ?_, ?_⟩
  · intro i j hij
    by_cases h0 : c i j = 0
    · by_cases hj : j = b
      · by_cases hi : i = a
        · subst hi; subst hj; exact ⟨hab, he⟩
        · simp [h0, hi] at hij
      · simp [h0, hj] at hij
    · exact hc i j h0
  · have : μ - (ν - Formalism.REAL.root a b) = (μ - ν) + Formalism.REAL.root a b := by abel
    rw [this, hs]
    simp only [Nat.cast_add, add_smul, Finset.sum_add_distrib, Nat.cast_ite, Nat.cast_one,
      Nat.cast_zero, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem cdom_word {n : ℕ} {ε : Fin n → Bool} (μ : Fin n → ℝ) (w : List (Fin n × Fin n))
    (hw : ∀ p ∈ w, ε p.1 = ε p.2 ∧ p.2 < p.1) : CDom ε (μ + wordWeightShift w) μ := by
  induction w with
  | nil => exact ⟨fun _ _ => 0, by simp, by simp [wordWeightShift]⟩
  | cons p w ih =>
    have hp := hw p List.mem_cons_self
    have := cdom_step (ih (fun q hq => hw q (List.mem_cons_of_mem _ hq))) hp.2 hp.1.symm
    have e : μ + wordWeightShift (p :: w) = μ + wordWeightShift w - Formalism.REAL.root p.2 p.1 := by
      simp only [wordWeightShift, Formalism.REAL.root]; abel
    rw [e]; exact this

theorem not_cdom_add {n : ℕ} {ε : Fin n → Bool} (μ : Fin n → ℝ) {a b : Fin n} (hab : a < b) :
    ¬ CDom ε (μ + Pi.single a 1 - Pi.single b 1) μ := by
  rintro ⟨c, hc, hs⟩
  have e : μ - (μ + Pi.single a 1 - Pi.single b 1) = Pi.single b (1 : ℝ) - Pi.single a 1 := by abel
  rw [e] at hs
  have h1 := congrArg heightFunctional hs
  rw [height_functional_root] at h1
  have hsum : heightFunctional (∑ i, ∑ j, (c i j : ℝ) • Formalism.REAL.root i j) ≤ 0 := by
    refine Finset.sum_induction _ (fun v => heightFunctional v ≤ 0) ?_ (by simp [heightFunctional]) ?_
    · intro x y hx hy; rw [height_functional_add]; linarith
    · intro i _
      refine Finset.sum_induction _ (fun v => heightFunctional v ≤ 0) ?_ (by simp [heightFunctional]) ?_
      · intro x y hx hy; rw [height_functional_add]; linarith
      · intro j _
        have h2 : heightFunctional ((c i j : ℝ) • Formalism.REAL.root i j) = (c i j : ℝ) * ((i : ℝ) - j) := by
          rw [← height_functional_root i j]
          simp only [heightFunctional, Formalism.REAL.root, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
          exact Finset.sum_congr rfl (fun k _ => by ring)
        rw [h2]
        by_cases h0 : c i j = 0
        · simp [h0]
        · have : ((i : ℕ) : ℝ) < ((j : ℕ) : ℝ) := by exact_mod_cast (hc i j h0).1
          exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (by linarith)
  have : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
  linarith

theorem cdom_of_mem {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ} {ε : Fin n → Bool}
    {F : Fin n → Fin n → Module.End ℂ V} (hR : KRel ε F) (hU : KUnit ε F) {μ ν : Fin n → ℝ} {x y : V}
    (hx : KHighest ε F μ x) (hy : y ∈ kSpan ε F x) (hy0 : y ≠ 0) (hw : IsWeight F ν y) :
    CDom ε ν μ := by
  by_contra hn
  rw [compact_span_eq_lowering hR hx] at hy
  have : lowSpan ε F x ≤ (ℂ ∙ y)ᗮ := by
    refine Submodule.span_le.mpr ?_
    rintro u ⟨w, hw', rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]
    refine compact_weight_orthogonal V n ε F ν (μ + wordWeightShift w) y _ hU hw
      (word_action_weight hR hx.1 w (fun q hq => (hw' q hq).1)) ?_
    rintro rfl
    exact hn (cdom_word μ w hw')
  exact hy0 (inner_self_eq_zero.mp (Submodule.mem_orthogonal_singleton_iff_inner_right.mp (this hy)))

theorem kType_iff : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ V), IsURepOn (UJset ε) σ → IsDer ε σ V E → (∀ (μ : Fin n → ℝ) (u : V), u ≠ 0 → KHighest ε E μ u → FiniteDimensional ℂ (kSpan ε E u) → IsKTypeOf ε σ μ ((kSpan ε E u).map V.subtype)) ∧ ∀ (μ : Fin n → ℝ) (S : Submodule ℂ H) (u : V), IsKTypeOf ε σ μ S → S ≤ V → (u : H) ∈ S → u ≠ 0 → IsWtOn (Kset ε) σ μ (u : H) → KHighest ε E μ u ∧ (kSpan ε E u).map V.subtype = S ∧ FiniteDimensional ℂ (kSpan ε E u) := by
  intro n ε H _ _ _ σ V E hσ hD
  obtain ⟨-, hst, hwt⟩ := GlobalTheory.T.derivedModule_coefficients_and_stable_flows n ε H σ V E hσ hD
  have hR : KRel ε E := glRel_kRel ε E hD.1
  have hU : KUnit ε E := isUnitary_kUnit ε E hD.2.1
  have hIrr : KIrr := kIrr_of highestWeightExists_holds
    (kHiUniq_of compact_lowering_holds compact_weight_orthogonal (kOrth_of compact_lowering_holds compact_weight_orthogonal))
  have hmc : ∀ S : Submodule ℂ H, S ≤ V → (S.comap V.subtype).map V.subtype = S := by
    intro S hS
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hS]
  have hfd : ∀ S : Submodule ℂ H, S ≤ V → FiniteDimensional ℂ S →
      FiniteDimensional ℂ (S.comap V.subtype) := by
    intro S hS _
    exact (Submodule.comapSubtypeEquivOfLe hS).symm.finiteDimensional
  refine ⟨?_, ?_⟩
  · intro μ u hu0 hu hf
    have hfm : FiniteDimensional ℂ ((kSpan ε E u).map V.subtype) := inferInstance
    refine ⟨hfm, (hst _ hf).1 (compact_span_stable u), ?_, ?_, ?_⟩
    · intro S' hS' hK
      have hV : S' ≤ V := hS'.trans (Submodule.map_subtype_le V _)
      have hf' : FiniteDimensional ℂ S' := Submodule.finiteDimensional_of_le hS'
      have hk : KStable ε E (S'.comap V.subtype) :=
        (hst _ (hfd S' hV hf')).2 (by rw [hmc S' hV]; exact hK)
      have hle : S'.comap V.subtype ≤ kSpan ε E u := by
        have := Submodule.comap_mono (f := V.subtype) hS'
        rwa [Submodule.comap_map_eq_of_injective V.injective_subtype] at this
      rcases hIrr V n ε E μ u hf hR hU hu _ hle hk with h | h
      · left; rw [← hmc S' hV, h, Submodule.map_bot]
      · right; rw [← hmc S' hV, h]
    · exact ⟨u, ⟨u, mem_compact_span_self u, rfl⟩, fun h => hu0 (Subtype.ext h), (hwt μ u).1 hu.1⟩
    · rintro ν _ ⟨y, hy, rfl⟩ hy0 hw
      exact cdom_of_mem hR hU hu hy (fun h => hy0 (by rw [h]; rfl)) ((hwt ν y).2 hw)
  · rintro μ S u ⟨hf, hK, hI, -, hC⟩ hV huS hu0 hw
    have hw' : IsWeight E μ u := (hwt μ u).2 hw
    have hfc := hfd S hV hf
    have hk : KStable ε E (S.comap V.subtype) := (hst _ hfc).2 (by rw [hmc S hV]; exact hK)
    have hle : kSpan ε E u ≤ S.comap V.subtype := compact_span_le_stable huS hk
    have hfk : FiniteDimensional ℂ (kSpan ε E u) := Submodule.finiteDimensional_of_le hle
    refine ⟨⟨hw', ?_⟩, ?_, hfk⟩
    · intro a b hab he
      by_contra hne
      exact not_cdom_add μ hab (hC _ (E a b u : V) (hk a b he u huS) (fun h => hne (Subtype.ext h))
        ((hwt _ _).1 (compact_weight_shift hR hw' he)))
    · rcases hI _ (Submodule.map_le_iff_le_comap.mpr hle) ((hst _ hfk).1 (compact_span_stable u)) with h | h
      · exfalso
        have : (u : H) ∈ (kSpan ε E u).map V.subtype := ⟨u, mem_compact_span_self u, rfl⟩
        rw [h, Submodule.mem_bot] at this
        exact hu0 (Subtype.ext this)
      · exact h

end GlobalTheory.Jet.KType
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProdLayerHeightQuotientsEqSq
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.HtProd

theorem prod_shift_eq (N : ℕ) (F : ℕ → ℕ → ℝ) (hF : ∀ b b', N ≤ b' → F b b' = 1) :
    ∏ c ∈ Finset.range N, ∏ b ∈ Finset.range N, F b (b + c + 1) =
      ∏ b ∈ Finset.range N, ∏ b' ∈ Finset.range N, if b < b' then F b b' else 1 := by
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [← Finset.prod_filter]
  have h1 : ∏ c ∈ Finset.range N, F b (b + c + 1) = ∏ x ∈ Finset.Ico (b + 1) (b + 1 + N), F b x := by
    rw [Finset.prod_Ico_eq_prod_range]
    simp only [Nat.add_sub_cancel_left]
    refine Finset.prod_congr rfl fun c _ => ?_
    congr 1
    omega
  rw [h1]
  symm
  apply Finset.prod_subset
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at hx ⊢
    omega
  · intro x hx hx'
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at hx hx'
    exact hF _ _ (by omega)

theorem prod_range_split (a : ℕ) (g : ℕ → ℝ) :
    ∏ b ∈ Finset.range (2 * a + 1), g b = (∏ i : Fin a, g i) * g a * ∏ i : Fin a, g (2 * a - i) := by
  have e : 2 * a + 1 = (a + 1) + a := by omega
  rw [e, Finset.prod_range_add, Finset.prod_range_succ, Fin.prod_univ_eq_prod_range g a,
    Fin.prod_univ_eq_prod_range (fun i => g (2 * a - i)) a, ← Finset.prod_range_reflect (fun i => g (2 * a - i)) a]
  congr 1
  refine Finset.prod_congr rfl fun x hx => ?_
  rw [Finset.mem_range] at hx
  congr 1
  omega

theorem prod_symm_split {a : ℕ} (P : Fin a → Fin a → ℝ) (hP : ∀ i k, P i k = P k i) :
    ∏ i, ∏ k, P i k = (∏ i, ∏ k, if i < k then P i k else 1) ^ 2 * ∏ i, P i i := by
  have h1 : ∀ i k, P i k = (if i < k then P i k else 1) * (if k < i then P k i else 1) *
      (if i = k then P i k else 1) := by
    intro i k
    rcases lt_trichotomy i k with h | h | h
    · simp [h, h.ne, not_lt.mpr h.le]
    · simp [h]
    · simp [h, h.ne', not_lt.mpr h.le, hP i k]
  rw [Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun k _ => h1 i k]
  simp only [Finset.prod_mul_distrib]
  rw [Finset.prod_comm (f := fun i k => if k < i then P k i else 1), sq]
  simp

theorem htProd : ∀ (n f a : ℕ) (j : Fin a → ℕ) (r : ℕ → ℕ) (τ : Fin a → ℝ) (h : ℕ → ℝ),
    (∀ i : Fin a, r i = j i ∧ r (2 * a - i) = j i) → r a = n - 2 * ∑ i, j i →
    (∀ b, 2 * a + 1 ≤ b → r b = 0) →
    (∀ i : Fin a, 0 < τ i ∧ h i = τ i ^ (2 * f * j i) ∧ h (2 * a - i) = (τ i ^ (2 * f * j i))⁻¹) →
    h a = 1 → (∀ b, 2 * a + 1 ≤ b → h b = 1) →
    ∏ c ∈ Finset.range (2 * a + 1), ∏ b ∈ Finset.range (2 * a + 1),
      h b ^ r (b + c + 1) / h (b + c + 1) ^ r b = layerProd n f j τ id ^ 2 := by
  intro n f a j r τ h hr hra hr0 hτ ha h1
  rw [prod_shift_eq (2 * a + 1) (fun b b' => h b ^ r b' / h b' ^ r b)
    (fun b b' hb => by simp [hr0 b' hb, h1 b' hb])]
  unfold layerProd
  rw [← hra]
  simp only [prod_range_split, id]
  have c1 : ∀ i : Fin a, (i : ℕ) < a := fun i => i.2
  have c2 : ∀ i k : Fin a, (i : ℕ) < 2 * a - k := fun i k => by omega
  have c3 : ∀ k : Fin a, ¬ a < (k : ℕ) := fun k => by omega
  have c4 : ∀ k : Fin a, a < 2 * a - k := fun k => by omega
  have c5 : ∀ i k : Fin a, ¬ 2 * a - i < (k : ℕ) := fun i k => by omega
  have c6 : ∀ i : Fin a, ¬ 2 * a - i < a := fun i => by omega
  have c7 : ∀ i k : Fin a, (2 * a - i < 2 * a - k) ↔ k < i := fun i k => by
    rw [Fin.lt_def]; omega
  have c8 : ∀ i k : Fin a, ((i : ℕ) < k) ↔ i < k := fun i k => Iff.rfl
  simp only [c1, c2, c3, c4, c5, c6, c7, c8, lt_irrefl, if_true, if_false, ha,
    fun i => (hr i).1, fun i => (hr i).2, fun i => (hτ i).2.1, fun i => (hτ i).2.2,
    Finset.prod_const_one, one_mul, mul_one, one_pow, div_one, Finset.prod_mul_distrib,
    Finset.prod_filter]
  have d1 : ∀ i k : Fin a, (τ i ^ (2 * f * j i)) ^ j k / (τ k ^ (2 * f * j k)) ^ j i =
      (τ i / τ k) ^ (2 * j i * j k * f) := fun i k => by
    rw [div_pow, ← pow_mul, ← pow_mul]
    congr 2 <;> ring
  have d2 : ∀ i k : Fin a, (τ i ^ (2 * f * j i)) ^ j k / (τ k ^ (2 * f * j k))⁻¹ ^ j i =
      (τ i * τ k) ^ (2 * j i * j k * f) := fun i k => by
    rw [inv_pow, div_inv_eq_mul, mul_pow, ← pow_mul, ← pow_mul]
    congr 2 <;> ring
  have d3 : ∀ i k : Fin a, (τ i ^ (2 * f * j i))⁻¹ ^ j k / (τ k ^ (2 * f * j k))⁻¹ ^ j i =
      (τ k / τ i) ^ (2 * j k * j i * f) := fun i k => by
    rw [← d1, inv_pow, inv_pow, div_inv_eq_mul, mul_comm, div_eq_mul_inv]
  have d4 : ∀ i : Fin a, (τ i ^ (2 * f * j i)) ^ r a = τ i ^ (2 * j i * r a * f) := fun i => by
    rw [← pow_mul]
    congr 1
    ring
  have d5 : ∀ i : Fin a, 1 / (τ i ^ (2 * f * j i))⁻¹ ^ r a = τ i ^ (2 * j i * r a * f) := fun i => by
    rw [← d4, inv_pow, one_div, inv_inv]
  have d6 : ∀ i : Fin a, (τ i * τ i) ^ (2 * j i * j i * f) = ((τ i ^ 2) ^ (j i ^ 2 * f)) ^ 2 := fun i => by
    rw [← sq, ← pow_mul (τ i ^ 2)]
    congr 1
    ring
  simp only [d1, d2, d3, d4, d5]
  rw [Finset.prod_comm (f := fun i k => if k < i then (τ k / τ i) ^ (2 * j k * j i * f) else 1),
    prod_symm_split (fun i k => (τ i * τ k) ^ (2 * j i * j k * f))
      (fun i k => by rw [mul_comm (τ i)]; congr 1; ring)]
  simp only [d6, Finset.prod_pow]
  ring

end GlobalTheory.HtProd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiComplexifiedKEquivariance
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder

noncomputable section
namespace GlobalTheory.Dec.Equivar
variable {n : ℕ}

lemma diag_KC (ε : Fin n → Bool) {d : Fin n → ℂ} (hd : ∀ a, d a ≠ 0) : Matrix.diagonal d ∈ KC ε := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_diagonal]
    exact IsUnit.mk0 _ (Finset.prod_ne_zero_iff.2 fun a _ => hd a)
  · unfold Jm
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1; funext a; ring

lemma KC_mul {ε : Fin n → Bool} {a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ KC ε) (hb : b ∈ KC ε) :
    a * b ∈ KC ε := by
  refine ⟨ha.1.mul hb.1, ?_⟩
  rw [Matrix.mul_assoc, hb.2, ← Matrix.mul_assoc, ha.2, Matrix.mul_assoc]

lemma KC_inv {ε : Fin n → Bool} {a : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ KC ε) : a⁻¹ ∈ KC ε := by
  have hd := (Matrix.isUnit_iff_isUnit_det a).1 ha.1
  refine ⟨Matrix.isUnit_nonsing_inv_iff.2 ha.1, ?_⟩
  calc a⁻¹ * Jm ε = a⁻¹ * (Jm ε * a) * a⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ hd]
    _ = Jm ε * a⁻¹ := by rw [← ha.2, Matrix.nonsing_inv_mul_cancel_left _ _ hd]

lemma KC_conjT {ε : Fin n → Bool} {a : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ KC ε) : aᴴ ∈ KC ε := by
  refine ⟨by simpa [Matrix.star_eq_conjTranspose] using ha.1.star, ?_⟩
  have h := congrArg Matrix.conjTranspose ha.2
  simp only [Matrix.conjTranspose_mul, Jm_conjTranspose] at h
  exact h.symm

variable {ε : Fin n → Bool} {abelian₂ : Fin n → ℝ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  {τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)} {w : W}

lemma tau_diag (hτ : IsTau ε abelian₂ τ w) (r : Fin n → ℝ) :
    τ (Matrix.diagonal fun a => Complex.exp (r a)) w = Complex.exp (-((∑ a, abelian₂ a * r a : ℝ) : ℂ)) • w := by
  refine ext_inner_left ℂ fun u => ?_
  set c : ℂ := -((∑ a, abelian₂ a * r a : ℝ) : ℂ) with hc
  let f : ℂ → ℂ := fun s => ⟪u, τ (Matrix.diagonal fun a => Complex.exp (r a * s)) w⟫_ℂ
  let g : ℂ → ℂ := fun s => Complex.exp (c * s) * ⟪u, w⟫_ℂ
  have hf : Differentiable ℂ f := by
    have h1 : Differentiable ℂ (fun s : ℂ => fun i j : Fin n =>
        (Matrix.diagonal fun a => Complex.exp (r a * s)) i j) := by
      refine differentiable_pi.2 fun i => differentiable_pi.2 fun j => ?_
      by_cases h : i = j
      · subst h; simp only [Matrix.diagonal_apply_eq]; fun_prop
      · simp only [Matrix.diagonal_apply_ne _ h]; fun_prop
    have := (hτ.2.2.1 u w).comp (s := Set.univ) h1.differentiableOn
      (fun s _ => diag_KC ε fun a => Complex.exp_ne_zero _)
    exact differentiableOn_univ.1 this
  have hg : Differentiable ℂ g := by fun_prop
  have hfg : ∀ t : ℝ, f (t * Complex.I) = g (t * Complex.I) := by
    intro t
    have hmem : Matrix.diagonal (fun a => Complex.exp (((r a * t : ℝ) : ℂ) * Complex.I)) ∈ Kset ε := by
      refine ⟨?_, (diag_KC ε fun a => Complex.exp_ne_zero _).2⟩
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
        Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext a
      rw [Pi.star_apply, Complex.star_def, Complex.mul_conj', Complex.norm_exp_ofReal_mul_I]
      simp
    have h := hτ.2.2.2.2.2.2.1 (fun a => r a * t) hmem
    simp only [f, g]
    have e : (fun a => Complex.exp (r a * (t * Complex.I))) =
        (fun a => Complex.exp (((r a * t : ℝ) : ℂ) * Complex.I)) := by
      funext a; push_cast; rw [mul_assoc]
    rw [e, h, inner_smul_right, hc]
    congr 2
    simp only [Pi.neg_apply, ← mul_assoc, ← Finset.sum_mul, neg_mul, Finset.sum_neg_distrib]
    push_cast; ring
  have hfreq : ∃ᶠ z in nhdsWithin (0 : ℂ) {0}ᶜ, f z = g z := by
    have ht : Filter.Tendsto (fun t : ℝ => (t : ℂ) * Complex.I) (nhdsWithin 0 {0}ᶜ) (nhdsWithin 0 {0}ᶜ) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Continuous fun t : ℝ => (t : ℂ) * Complex.I := by fun_prop
        simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht
        simpa using ht
    exact ht.frequently (Filter.Frequently.of_forall hfg)
  have := AnalyticOnNhd.eq_of_frequently_eq (hf.differentiableOn.analyticOnNhd isOpen_univ)
    (hg.differentiableOn.analyticOnNhd isOpen_univ) hfreq
  have := congrFun this 1
  simpa [f, g, inner_smul_right] using this

lemma tau_lo (hτ : IsTau ε abelian₂ τ w) {b : Matrix (Fin n) (Fin n) ℂ} (hb : b ∈ KC ε) (hlo : IsLo b)
    (hpos : ∀ l, 0 < b l l) : τ b w = ((∏ l, ‖b l l‖ ^ (-(abelian₂ l)) : ℝ) : ℂ) • w := by
  have hne : ∀ l, b l l ≠ 0 := fun l => (hpos l).ne'
  have hn : ∀ l, 0 < ‖b l l‖ := fun l => norm_pos_iff.2 (hne l)
  have hexp : ∀ l, Complex.exp (Real.log ‖b l l‖ : ℝ) = b l l := fun l => by
    rw [← Complex.ofReal_exp, Real.exp_log (hn l)]
    exact Complex.norm_of_nonneg' (hpos l).le
  have hu : Matrix.diagonal (fun a => (b a a)⁻¹) * b ∈ KC ε :=
    KC_mul (diag_KC ε fun a => inv_ne_zero (hne a)) hb
  have hu1 : IsLoUni (Matrix.diagonal (fun a => (b a a)⁻¹) * b) := by
    intro i j
    refine ⟨fun h => by simp [Matrix.diagonal_mul, hlo i j h], fun h => ?_⟩
    subst h
    simp [Matrix.diagonal_mul, hne]
  have e : b = (Matrix.diagonal fun a => Complex.exp (Real.log ‖b a a‖ : ℝ)) *
      (Matrix.diagonal (fun a => (b a a)⁻¹) * b) := by
    simp only [hexp]
    ext i j
    simp [Matrix.diagonal_mul, hne]
  have h1 := hτ.2.1.2 _ (diag_KC ε (d := fun a => Complex.exp (Real.log ‖b a a‖ : ℝ))
    fun a => Complex.exp_ne_zero _) _ hu
  rw [← e] at h1
  rw [h1, ContinuousLinearMap.comp_apply, hτ.2.2.2.2.2.2.2 _ hu hu1, tau_diag hτ]
  congr 1
  rw [← Complex.ofReal_neg, ← Complex.ofReal_exp, ← Finset.sum_neg_distrib, Real.exp_sum]
  congr 1
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [Real.rpow_def_of_pos (hn l)]
  congr 1; ring

lemma tau_cont (hτ : IsTau ε abelian₂ τ w) (v : W) : ContinuousOn (fun k => τ k v) (Kset ε) := by
  have := hτ.1
  have e : (fun k => τ k v) = fun k => ∑ i, ⟪stdOrthonormalBasis ℂ W i, τ k v⟫_ℂ • stdOrthonormalBasis ℂ W i := by
    funext k
    rw [(stdOrthonormalBasis ℂ W).sum_repr']
  rw [e]
  refine continuousOn_finsetSum _ fun i _ => ContinuousOn.smul ?_ continuousOn_const
  exact (hτ.2.2.1 _ v).continuousOn.mono fun k hk => FormF.K_KC hk

lemma muInt_cast {lam : Fin n → ℝ} (hlam : IsHCParam lam) (ε : Fin n → Bool) (l : Fin n) :
    (muInt lam l : ℝ) = lowK ε lam l + 2 * rhoC ε l := by
  obtain ⟨m, hm⟩ := hlam.2 l
  have h1 := half_sum_roots_standard n ε l
  have h2 : lam l + Formalism.QuantumDeterminants.rhoStd n l = ((m + n - 1 - (l : ℕ) : ℤ) : ℝ) := by
    simp only [Formalism.QuantumDeterminants.rhoStd]; push_cast; linarith
  have h3 : (muInt lam l : ℝ) = lam l + Formalism.QuantumDeterminants.rhoStd n l := by
    rw [muInt, h2, Int.floor_intCast]
  rw [h3]
  simp only [lowK, Formalism.QuantumDeterminants.rhoStd, Pi.add_apply, Pi.sub_apply]
  linarith

lemma scalar_eq {lam : Fin n → ℝ} (hlam : IsHCParam lam) (ε : Fin n → Bool) {d : Fin n → ℂ} (hd : ∀ l, d l ≠ 0) :
    (∏ l, (d l * star (d l)) ^ (-(muInt lam l))) * ((∏ l, ‖d l‖ ^ (4 * rhoC ε l) : ℝ) : ℂ) =
      ((∏ l, ‖d l‖ ^ (-(lowK ε lam l)) : ℝ) : ℂ) * ((∏ l, ‖d l‖ ^ (-(lowK ε lam l)) : ℝ) : ℂ) := by
  simp only [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_zpow,
    ← Complex.ofReal_prod, ← Complex.ofReal_mul, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun l _ => ?_
  have hn : 0 < ‖d l‖ := norm_pos_iff.2 (hd l)
  rw [← Real.rpow_intCast, ← Real.rpow_natCast, ← Real.rpow_mul hn.le, ← Real.rpow_add hn, ← Real.rpow_add hn]
  congr 1
  push_cast
  rw [muInt_cast hlam ε]
  ring

theorem psEquiv_of (hT : PhiTri) (hP : PhiPos) (hI : IwasawaKC) (hH : IwasawaInt) : PsEquiv := by
  intro n ε lam W _ _ τ w hlam hτ x y hx hy
  have hyd := (Matrix.isUnit_iff_isUnit_det y).1 hy.1
  have hx' : (y * x * yᴴ).PosDef := hx.mul_mul_conjTranspose_same (Matrix.vecMul_injective_of_isUnit hy.1)
  obtain ⟨κ, β, hκ, -⟩ := hI n ε
  have hmem : ∀ k : KG ε, y⁻¹ * toMK k ∈ KC ε := fun k => KC_mul (KC_inv hy) (FormF.K_KC k.2)
  ext u
  refine ext_inner_left ℂ fun v => ?_
  have hadj : ∀ a : W, ⟪v, τ y a⟫_ℂ = ⟪τ yᴴ v, a⟫_ℂ := fun a => by
    rw [hτ.2.2.2.1 _ (KC_conjT hy), Matrix.conjTranspose_conjTranspose]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hadj,
    FormF.psEntry hP n ε lam W τ w hτ.1 (tau_cont hτ) _ hx', FormF.psEntry hP n ε lam W τ w hτ.1 (tau_cont hτ) _ hx]
  congr 1
  have hF : ContinuousOn (fun k : Matrix (Fin n) (Fin n) ℂ =>
      Phi lam (k⁻¹ * x * k) * (⟪τ yᴴ v, τ k w⟫_ℂ * ⟪τ k w, τ yᴴ u⟫_ℂ)) (Kset ε) := by
    refine ContinuousOn.mul ?_ ((ContinuousOn.inner (𝕜 := ℂ) continuousOn_const (tau_cont hτ w)).mul
      (ContinuousOn.inner (𝕜 := ℂ) (tau_cont hτ w) continuousOn_const))
    refine ContinuousOn.congr (f := fun k => Phi lam (kᴴ * x * k)) ?_ fun k hk => by simp only [FormF.K_inv hk]
    unfold Phi
    refine continuousOn_finsetProd _ fun i _ => ContinuousOn.zpow₀ ?_ _ fun k hk => Or.inl ?_
    · unfold leadMinor
      exact (((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
        continuous_id).matrix_submatrix _ _).matrix_det.continuousOn
    · exact (hP n lam _ (hx.conjTranspose_mul_mul_same
        (Matrix.mulVec_injective_of_isUnit (FormF.K_KC hk).1))).1 i
  rw [← hH n ε y⁻¹ (fun k => κ (y⁻¹ * toMK k)) (fun k => β (y⁻¹ * toMK k)) (KC_inv hy)
    (fun k => hκ _ (hmem k)) _ hF]
  congr 1
  funext k
  obtain ⟨h1, h2, h3, h4, h5⟩ := hκ _ (hmem k)
  have hk : toMK k ∈ Kset ε := k.2
  generalize κ (y⁻¹ * toMK k) = c at *
  generalize β (y⁻¹ * toMK k) = b at *
  generalize toMK k = g at *
  have hg : g = y * (c * b) := by rw [← h5, Matrix.mul_nonsing_inv_cancel_left _ _ hyd]
  have hgg : gᴴ * g = 1 := Unitary.star_mul_self_of_mem hk.1
  have hc : cᴴ = b * gᴴ * y := by
    rw [← FormF.K_inv h1]
    apply Matrix.inv_eq_left_inv
    have : gᴴ * y * c * b = 1 := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← hg, hgg]
    have := mul_eq_one_comm.1 this
    simpa only [Matrix.mul_assoc] using this
  have hz : c⁻¹ * x * c = b * (g⁻¹ * (y * x * yᴴ) * g) * bᴴ := by
    have : c = yᴴ * g * bᴴ := by
      rw [← Matrix.conjTranspose_conjTranspose c, hc]
      simp [Matrix.mul_assoc]
    rw [FormF.K_inv h1, FormF.K_inv hk, hc]
    conv_lhs => rw [this]
    simp only [Matrix.mul_assoc]
  have hne : ∀ l, b l l ≠ 0 := fun l => (h4 l).ne'
  have hΩ : g⁻¹ * (y * x * yᴴ) * g ∈ Omega n := by
    rw [FormF.K_inv hk]
    exact (hP n lam _ (hx'.conjTranspose_mul_mul_same
        (Matrix.mulVec_injective_of_isUnit (FormF.K_KC hk).1))).1
  have hΦ := (hT n lam b _ bᴴ h3 (fun i j h => by simp [h3 j i h]) (fun l => ⟨hne l, by simp [hne l]⟩) hΩ).2
  have hw : τ g w = ((∏ l, ‖b l l‖ ^ (-(lowK ε lam l)) : ℝ) : ℂ) • τ y (τ c w) := by
    conv_lhs => rw [hg]
    rw [hτ.2.1.2 _ hy _ (KC_mul (FormF.K_KC h1) h2), hτ.2.1.2 _ (FormF.K_KC h1) _ h2]
    simp only [ContinuousLinearMap.comp_apply]
    rw [tau_lo hτ h2 h3 h4, map_smul, map_smul]
  have hs := scalar_eq hlam ε (d := fun l => b l l) hne
  rw [hz, hΦ, hw, inner_smul_right, inner_smul_left, Complex.conj_ofReal, hadj, hτ.2.2.2.1 _ hy]
  simp only [Matrix.conjTranspose_apply]
  linear_combination (-(Phi lam (g⁻¹ * (y * x * yᴴ) * g) * (⟪τ yᴴ v, τ c w⟫_ℂ * ⟪τ c w, τ yᴴ u⟫_ℂ))) * hs

theorem psEquiv : PsEquiv := psEquiv_of GlobalTheory.PhiTriangular.phiTri GlobalTheory.Dec.phiPos GlobalTheory.Dec.iwasawaKC GlobalTheory.IwaInt.iwasawaInt

end GlobalTheory.Dec.Equivar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TranslatedLatticeAtInfinityFullCovolumeDualStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translatedLatticeAtInfinity_full_covolume_dual : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ j : ℕ, (∀ Λ : Submodule (𝓞 E) (Fin j → E), Submodule.IsLattice E Λ → ∃ κ : ℝ, 0 < κ ∧ ∀ g : MatInf E j, 0 < detNorm E j g → (∃ _ : DiscreteTopology (latAt E j Λ g), IsZLattice ℝ (latAt E j Λ g)) ∧ covAt E j (latAt E j Λ g) = κ / detNorm E j g ∧ covAt E j (dualAt E j (latAt E j Λ g)) = (covAt E j (latAt E j Λ g))⁻¹ ∧ dualAt E j (dualAt E j (latAt E j Λ g)) = latAt E j Λ g) ∧ covAt E j (latAt E j (Submodule.span (𝓞 E) (Set.range fun a => (Pi.single a 1 : Fin j → E))) fun _ a b => if a = b then 1 else 0) = Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * j) := by
  first | exact @GlobalTheory.LatFacts.lattice_facts | exact GlobalTheory.LatFacts.lattice_facts | (intros; apply GlobalTheory.LatFacts.lattice_facts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentRadicalBlockUnitriangularFlagStatement
section
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.CellDens
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotentRadical_block_unitriangular_flag : ∀ (k r : ℕ), ∀ g ∈ Nset k r, ∀ i j : Fin (2 * r + k + 1), lev k r j ≤ lev k r i → g i j = (1 : Mat k r) i j := by
  first | exact @GlobalTheory.CellDens.nset_block_unitriangular | exact GlobalTheory.CellDens.nset_block_unitriangular | (intros; apply GlobalTheory.CellDens.nset_block_unitriangular <;> assumption)
end

