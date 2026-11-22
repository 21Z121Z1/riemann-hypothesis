import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0236
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0233
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0231
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0232
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentRadicalInterConjugateClosedUnimodular
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NCoords
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0237

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaNMKIntegrationPiProduct
section
open MeasureTheory

namespace GlobalTheory.NMKProd

theorem lintegral_nmk {H : Type} [Mul H] [MeasurableSpace H] [MeasurableMul₂ H]
    (a b k : Measure H) [SFinite a] [SFinite b] [SFinite k] (d : H → ENNReal) (hd : Measurable d)
    (φ : H → ENNReal) (hφ : Measurable φ) :
    ∫⁻ g, φ g ∂(((a.prod (b.prod k)).withDensity fun x => d x.2.1).map
        fun x : H × H × H => x.1 * x.2.1 * x.2.2) =
      ∫⁻ u, ∫⁻ m, d m * ∫⁻ z, φ (u * m * z) ∂k ∂b ∂a := by
  have hmul : Measurable (fun x : H × H × H => x.1 * x.2.1 * x.2.2) :=
    (measurable_fst.mul measurable_snd.fst).mul measurable_snd.snd
  have hD : Measurable (fun x : H × H × H => d x.2.1) := hd.comp measurable_snd.fst
  have hφm : Measurable (fun x : H × H × H => φ (x.1 * x.2.1 * x.2.2)) := hφ.comp hmul
  rw [lintegral_map hφ hmul, lintegral_withDensity_eq_lintegral_mul _ hD hφm,
    lintegral_prod _ (hD.mul hφm).aemeasurable]
  refine lintegral_congr fun u => ?_
  have hin : Measurable (fun y : H × H => d y.1 * φ (u * y.1 * y.2)) :=
    (hd.comp measurable_fst).mul (hφ.comp ((measurable_const.mul measurable_fst).mul measurable_snd))
  simp only [Pi.mul_apply]
  rw [lintegral_prod _ hin.aemeasurable]
  refine lintegral_congr fun m => ?_
  have hz : Measurable (fun z : H => φ (u * m * z)) := hφ.comp (measurable_id.const_mul (u * m))
  exact lintegral_const_mul (d m) hz

private lemma indicator_pi_univ_eq_prod {ι : Type} [Fintype ι] {G : ι → Type} (s : ∀ i, Set (G i))
    (x : ∀ i, G i) :
    (Set.univ.pi s).indicator (1 : (∀ i, G i) → ENNReal) x =
      ∏ i, (s i).indicator (1 : G i → ENNReal) (x i) := by
  by_cases hx : x ∈ Set.univ.pi s
  · rw [Set.indicator_of_mem hx]
    rw [Set.mem_univ_pi] at hx
    simp [Set.indicator_of_mem (hx _)]
  · rw [Set.indicator_of_notMem hx]
    rw [Set.mem_univ_pi, not_forall] at hx
    obtain ⟨i, hi⟩ := hx
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm

theorem prod_formula : ∀ (ι : Type) [Fintype ι] (G : ι → Type) [∀ i, Group (G i)] [∀ i, MeasurableSpace (G i)] [∀ i, MeasurableMul₂ (G i)] (μ μN μM μK : ∀ i, Measure (G i)) [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (μN i)] [∀ i, SigmaFinite (μM i)] [∀ i, SigmaFinite (μK i)] (C c : ι → ENNReal) (δ : ∀ i, G i → ENNReal), (∀ i, C i ≠ 0) → (∀ i, C i ≠ ⊤) → (∀ i, Measurable (δ i)) → (∀ i, ∀ φ : G i → ENNReal, Measurable φ → C i * ∫⁻ g, φ g ∂(μ i) = c i * ∫⁻ u, ∫⁻ m, δ i m * ∫⁻ k, φ (u * m * k) ∂(μK i) ∂(μM i) ∂(μN i)) → ∀ φ : (∀ i, G i) → ENNReal, Measurable φ → (∏ i, C i) * ∫⁻ g, φ g ∂(Measure.pi μ) = (∏ i, c i) * ∫⁻ u, ∫⁻ m, (∏ i, δ i (m i)) * ∫⁻ k, φ (u * m * k) ∂(Measure.pi μK) ∂(Measure.pi μM) ∂(Measure.pi μN) := by
  intro ι _ G _ _ _ μ μN μM μK _ _ _ _ C c δ hC0 hCt hδ hrel φ hφ
  have hD : Measurable (fun m : ∀ i, G i => ∏ i, δ i (m i)) :=
    Finset.measurable_prod _ (fun i _ => (hδ i).comp (measurable_pi_apply i))
  have key := fun (ψ : (∀ i, G i) → ENNReal) (hψ : Measurable ψ) =>
    lintegral_nmk (Measure.pi μN) (Measure.pi μM) (Measure.pi μK)
      (fun m : ∀ i, G i => ∏ i, δ i (m i)) hD ψ hψ
  set R0 := (((Measure.pi μN).prod ((Measure.pi μM).prod (Measure.pi μK))).withDensity
      fun x => ∏ i, δ i (x.2.1 i)).map
    (fun x : (∀ i, G i) × (∀ i, G i) × (∀ i, G i) => x.1 * x.2.1 * x.2.2) with hR0
  have hC0' : (∏ i, C i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hC0 i
  have hCt' : (∏ i, C i) ≠ ⊤ := ENNReal.prod_ne_top fun i _ => hCt i
  have hpi : Measure.pi μ = (∏ i, C i)⁻¹ • ((∏ i, c i) • R0) := by
    refine Measure.pi_eq fun s hs => ?_
    have hX : ∀ i, C i * μ i (s i) = c i * ∫⁻ u, ∫⁻ m, δ i m *
        ∫⁻ k, (s i).indicator 1 (u * m * k) ∂(μK i) ∂(μM i) ∂(μN i) := by
      intro i
      have h := hrel i ((s i).indicator 1) (measurable_one.indicator (hs i))
      rwa [lintegral_indicator_one (hs i)] at h
    have hbox : R0 (Set.univ.pi s) = ∏ i, ∫⁻ u, ∫⁻ m, δ i m *
        ∫⁻ k, (s i).indicator 1 (u * m * k) ∂(μK i) ∂(μM i) ∂(μN i) := by
      rw [← lintegral_indicator_one (MeasurableSet.univ_pi hs),
        key _ (measurable_one.indicator (MeasurableSet.univ_pi hs))]
      have hK : ∀ u m : ∀ i, G i, ∫⁻ k, (Set.univ.pi s).indicator 1 (u * m * k) ∂(Measure.pi μK) =
          ∏ i, ∫⁻ k, (s i).indicator 1 (u i * m i * k) ∂(μK i) := by
        intro u m
        simp_rw [indicator_pi_univ_eq_prod]
        exact GlobalTheory.SnMass.Push.lintegral_fintype_prod (fun i k => (s i).indicator 1 (u i * m i * k))
          (fun i => (measurable_one.indicator (hs i)).comp (measurable_const.mul measurable_id))
      have hA : ∀ i (u' : G i), Measurable (fun m' : G i =>
          δ i m' * ∫⁻ k, (s i).indicator 1 (u' * m' * k) ∂(μK i)) := by
        intro i u'
        refine (hδ i).mul ?_
        exact Measurable.lintegral_prod_right' (f := fun y : G i × G i => (s i).indicator 1 (u' * y.1 * y.2))
          ((measurable_one.indicator (hs i)).comp ((measurable_const.mul measurable_fst).mul measurable_snd))
      have hB : ∀ i, Measurable (fun u' : G i => ∫⁻ m', δ i m' *
          ∫⁻ k, (s i).indicator 1 (u' * m' * k) ∂(μK i) ∂(μM i)) := by
        intro i
        refine Measurable.lintegral_prod_right' (f := fun y : G i × G i =>
          δ i y.2 * ∫⁻ k, (s i).indicator 1 (y.1 * y.2 * k) ∂(μK i)) ?_
        refine ((hδ i).comp measurable_snd).mul ?_
        exact Measurable.lintegral_prod_right' (f := fun z : (G i × G i) × G i =>
            (s i).indicator 1 (z.1.1 * z.1.2 * z.2))
          ((measurable_one.indicator (hs i)).comp
            ((measurable_fst.fst.mul measurable_fst.snd).mul measurable_snd))
      have hM : ∀ u : ∀ i, G i, ∫⁻ m, (∏ i, δ i (m i)) *
          ∫⁻ k, (Set.univ.pi s).indicator 1 (u * m * k) ∂(Measure.pi μK) ∂(Measure.pi μM) =
          ∏ i, ∫⁻ m', δ i m' * ∫⁻ k, (s i).indicator 1 (u i * m' * k) ∂(μK i) ∂(μM i) := by
        intro u
        simp_rw [hK u, ← Finset.prod_mul_distrib]
        exact GlobalTheory.SnMass.Push.lintegral_fintype_prod
          (fun i m' => δ i m' * ∫⁻ k, (s i).indicator 1 (u i * m' * k) ∂(μK i)) (fun i => hA i (u i))
      simp_rw [hM]
      exact GlobalTheory.SnMass.Push.lintegral_fintype_prod _ hB
    simp only [Measure.smul_apply, smul_eq_mul]
    rw [hbox, ← Finset.prod_mul_distrib, Finset.prod_congr rfl fun i _ => (hX i).symm,
      Finset.prod_mul_distrib, ← mul_assoc, ENNReal.inv_mul_cancel hC0' hCt', one_mul]
  rw [hpi, lintegral_smul_measure, lintegral_smul_measure, smul_eq_mul, smul_eq_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel hC0' hCt', one_mul, hR0]
  exact congrArg ((∏ i, c i) * ·) (key φ hφ)

end GlobalTheory.NMKProd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ReAntidiagonalEntryEqZeroOfFlagDepth
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN

theorem re_corner_eq_zero (k r : ℕ) (x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a : Fin r)
    (hx : x ∈ Nset k r) (hd : Dep k r (2 * r - 2 * a.val) (x - 1)) :
    (x (eI k r a) (esI k r a)).re = 0 := by
  have hsv : (esI k r a).val = 2 * r + k - a.val := rfl
  have hev : (eI k r a).val = a.val := rfl
  generalize esI k r a = s at *
  generalize eI k r a = e at *
  have ha := a.isLt

  have hcol : ∀ i : Fin (2 * r + k + 1), a.val < i.val → i ≠ s → x i s = 0 := by
    intro i hi hne
    have h0 := hd i s (by
      simp only [pos]
      split_ifs <;> first | rfl | omega | (exfalso; omega))
    rw [Matrix.sub_apply, Matrix.one_apply_ne hne, sub_zero] at h0; exact h0
  have hss : x s s = 1 := by
    have h0 := hd s s (by simp only [pos]; split_ifs <;> first | rfl | omega | (exfalso; omega))
    rw [Matrix.sub_apply, Matrix.one_apply_eq, sub_eq_zero] at h0; exact h0
  have hU := congrFun (congrFun hx.1 s) s
  have hH : Hpk k r s s = 0 := by
    simp only [Hpk, Fin.ext_iff, and_true]
    split_ifs <;> first | rfl | omega | (exfalso; omega)
  rw [hH] at hU
  have key : ∀ i j : Fin (2 * r + k + 1), star (x i s) * Hpk k r i j * x j s =
      (if i = s ∧ j = e then x j s else 0) + (if i = e ∧ j = s then star (x i s) else 0) := by
    intro i j
    by_cases h1 : i = s ∧ j = e
    · rw [h1.1, h1.2]
      have hes : e ≠ s := fun h => by have := congrArg Fin.val h; omega
      have : Hpk k r s e = 1 := by simp only [Hpk, Fin.ext_iff, and_true]; split_ifs <;> first | rfl | omega | (exfalso; omega)
      simp [hes, hes.symm, this, hss]
    by_cases h2 : i = e ∧ j = s
    · rw [h2.1, h2.2]
      have hes : e ≠ s := fun h => by have := congrArg Fin.val h; omega
      have : Hpk k r e s = 1 := by simp only [Hpk, Fin.ext_iff, and_true]; split_ifs <;> first | rfl | omega | (exfalso; omega)
      simp [hes, hes.symm, this, hss]
    rw [if_neg h1, if_neg h2, add_zero]
    have hi : i = s ∨ i.val ≤ a.val ∨ x i s = 0 := by
      by_cases h : i = s
      · exact Or.inl h
      by_cases h' : i.val ≤ a.val
      · exact Or.inr (Or.inl h')
      exact Or.inr (Or.inr (hcol i (by omega) h))
    have hj : j = s ∨ j.val ≤ a.val ∨ x j s = 0 := by
      by_cases h : j = s
      · exact Or.inl h
      by_cases h' : j.val ≤ a.val
      · exact Or.inr (Or.inl h')
      exact Or.inr (Or.inr (hcol j (by omega) h))
    have hI : ∀ i : Fin (2 * r + k + 1), i = s ↔ i.val = 2 * r + k - a.val := fun i =>
      ⟨fun h => h ▸ hsv, fun h => Fin.ext (h.trans hsv.symm)⟩
    have hE : ∀ i : Fin (2 * r + k + 1), i = e ↔ i.val = a.val := fun i =>
      ⟨fun h => h ▸ hev, fun h => Fin.ext (h.trans hev.symm)⟩
    rw [hI, hE] at h1 h2
    rcases hi with hi | hi | hi
    · rcases hj with hj | hj | hj
      · subst hi; subst hj; simp [hH]
      · have : Hpk k r i j = 0 := by
          rw [hI] at hi
          simp only [Hpk, Fin.ext_iff, and_true]; split_ifs <;> first | rfl | omega | (exfalso; omega)
        simp [this]
      · simp [hj]
    · rcases hj with hj | hj | hj
      · have : Hpk k r i j = 0 := by
          rw [hI] at hj
          simp only [Hpk, Fin.ext_iff, and_true]; split_ifs <;> first | rfl | omega | (exfalso; omega)
        simp [this]
      · have : Hpk k r i j = 0 := by
          simp only [Hpk, Fin.ext_iff, and_true]; split_ifs <;> first | rfl | omega | (exfalso; omega)
        simp [this]
      · simp [hj]
    · simp [hi]
  have hsum : (xᴴ * Hpk k r * x) s s = x e s + star (x e s) := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [key, Finset.sum_add_distrib]
    simp [ite_and, hss]
  rw [hsum] at hU
  have := congrArg Complex.re hU
  simp at this
  linarith

end GlobalTheory.SnMass.VolN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowEmbeddingMemIntegralOrthogonalGroup
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN.RowIso

section Alg
variable {E : Type} [Field E] (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem form_add_left (x x' y : Fin n → E) : form σ J (x + x') y = form σ J x y + form σ J x' y := by
  simp [form, Matrix.mulVec_add, dotProduct_add]

theorem form_sub_left (x x' y : Fin n → E) : form σ J (x - x') y = form σ J x y - form σ J x' y := by
  simp [form, Matrix.mulVec_sub, dotProduct_sub]

theorem form_smul_left (c : E) (x y : Fin n → E) : form σ J (c • x) y = c * form σ J x y := by
  simp [form, Matrix.mulVec_smul, dotProduct_smul]

theorem form_add_right (x y y' : Fin n → E) : form σ J x (y + y') = form σ J x y + form σ J x y' := by
  simp [form, dotProduct, add_mul, Finset.sum_add_distrib]

theorem form_sub_right (x y y' : Fin n → E) : form σ J x (y - y') = form σ J x y - form σ J x y' := by
  simp [form, dotProduct, sub_mul, Finset.sum_sub_distrib]

theorem form_neg_right (x y : Fin n → E) : form σ J x (-y) = -form σ J x y := by
  simp [form, dotProduct]

theorem form_neg_left (x y : Fin n → E) : form σ J (-x) y = -form σ J x y := by
  simp [form, Matrix.mulVec_neg]

theorem form_smul_right (c : E) (x y : Fin n → E) : form σ J x (c • y) = σ c * form σ J x y := by
  simp [form, dotProduct, Finset.mul_sum, mul_assoc]

theorem form_herm (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin n → E) :
    form σ J x y = σ (form σ J y x) := by
  simp only [form, dotProduct, mulVec, map_sum, map_mul, hσ, hJ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem rowE_mulVec (e y : Fin n → E) (t : E) (x : Fin n → E) :
    rowE σ J e y t *ᵥ x = x + form σ J x e • (y + t • e) - form σ J x y • e := by
  ext i
  simp only [rowE, mulVec, dotProduct, form, vecMul, add_mul, sub_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm (f := fun (a b : Fin n) => y i * (σ (e b) * (J b a * x a))),
    Finset.sum_comm (f := fun (a b : Fin n) => t * (e i * (σ (e b) * (J b a * x a)))),
    Finset.sum_comm (f := fun (a b : Fin n) => e i * (σ (y b) * (J b a * x a))), ← Finset.sum_add_distrib]
  congr 2
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  · funext a
    refine Finset.sum_congr rfl fun b _ => ?_
    ring

theorem isUn_of_form (g : Matrix (Fin n) (Fin n) E)
    (h : ∀ x x', form σ J (g *ᵥ x) (g *ᵥ x') = form σ J x x') : IsUn σ J g := by
  ext i j
  have := h (Pi.single j 1) (Pi.single i 1)
  simp only [form, dotProduct, mulVec, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, apply_ite σ, map_one, map_zero, ite_mul, one_mul, zero_mul] at this
  rw [← this]
  simp only [IsUn, cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

end Alg
end GlobalTheory.SnMass.VolN.RowIso

namespace GlobalTheory.SnMass.VolN.RowIso

section Iso
variable {E : Type} [Field E] {σ : E →+* E} (hσ : ∀ x, σ (σ x) = x) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
  (hJ : ∀ i j, σ (J j i) = J i j) {e y : Fin n → E} {t : E} (he : form σ J e e = 0)
  (hye : form σ J y e = 0) (ht : form σ J y y + t + σ t = 0)
include hσ hJ he hye ht

theorem form_rowE (x x' : Fin n → E) :
    form σ J (rowE σ J e y t *ᵥ x) (rowE σ J e y t *ᵥ x') = form σ J x x' := by
  have hey : form σ J e y = 0 := by rw [form_herm σ J hσ hJ, hye, map_zero]
  have h1 : form σ J y x' = σ (form σ J x' y) := form_herm σ J hσ hJ _ _
  have h2 : form σ J e x' = σ (form σ J x' e) := form_herm σ J hσ hJ _ _
  simp only [rowE_mulVec, form_add_left, form_sub_left, form_smul_left, form_add_right, form_sub_right,
    form_smul_right, map_add, map_sub, map_mul, hσ, he, hye, hey, h1, h2]
  linear_combination (form σ J x e * σ (form σ J x' e)) * ht

theorem rowE_inv (x : Fin n → E) :
    rowE σ J e y t *ᵥ (rowE σ J e (-y) (σ t) *ᵥ x) = x := by
  have hey : form σ J e y = 0 := by rw [form_herm σ J hσ hJ, hye, map_zero]
  have hα : form σ J (rowE σ J e (-y) (σ t) *ᵥ x) e = form σ J x e := by
    simp only [rowE_mulVec, form_add_left, form_sub_left, form_smul_left, form_neg_left, he, hye]
    ring
  have hβ : form σ J (rowE σ J e (-y) (σ t) *ᵥ x) y = form σ J x y - form σ J x e * form σ J y y := by
    simp only [rowE_mulVec, form_add_left, form_sub_left, form_smul_left, form_neg_left, form_neg_right, hey]
    ring
  rw [rowE_mulVec σ J e y t, hα, hβ, rowE_mulVec σ J e (-y) (σ t) x]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, form_neg_right]
  linear_combination (form σ J x e * e i) * ht

end Iso

section Lat
variable {E : Type} [Field E] [NumberField E]

open GlobalTheory.SnMass.FrameDual in

theorem rowE_mem {σ : E →+* E} (hσ : ∀ x, σ (σ x) = x) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    {Λ : Submodule (𝓞 E) (Fin n → E)} (hΛ : GlobalTheory.SgGlob.SelfDual σ J Λ) {𝔞 : FractionalIdeal (𝓞 E)⁰ E}
    (h0 : 𝔞 ≠ 0) (hs : Stab σ 𝔞) {e y : Fin n → E} {t : E} (he : ∀ c ∈ 𝔞, c • e ∈ Λ)
    (hy : ∀ c ∈ 𝔞⁻¹, c • y ∈ Λ) (ht : t ∈ 𝔞 * 𝔞) {v : Fin n → E} (hv : v ∈ Λ) :
    rowE σ J e y t *ᵥ v ∈ Λ := by
  have hO : ∀ w ∈ Λ, form σ J v w ∈ (algebraMap (𝓞 E) E).range := (hΛ.2 v).1 hv
  have hα : form σ J v e ∈ 𝔞⁻¹ := by
    rw [FractionalIdeal.mem_inv_iff h0]
    intro z hz
    have := hO _ (he _ (hs z hz))
    rw [form_smul_right, hσ, mul_comm] at this
    obtain ⟨d, hd⟩ := this
    exact (FractionalIdeal.mem_one_iff _).2 ⟨d, hd⟩
  have hβ : form σ J v y ∈ 𝔞 := by
    have h0' : 𝔞⁻¹ ≠ 0 := inv_ne_zero h0
    rw [← inv_inv 𝔞, FractionalIdeal.mem_inv_iff h0']
    intro z hz
    have := hO _ (hy _ (Stab.inv hσ hs h0 z hz))
    rw [form_smul_right, hσ, mul_comm] at this
    obtain ⟨d, hd⟩ := this
    exact (FractionalIdeal.mem_one_iff _).2 ⟨d, hd⟩
  have hγ : t * form σ J v e ∈ 𝔞 := by
    have := FractionalIdeal.mul_mem_mul ht hα
    rwa [mul_assoc, mul_inv_cancel₀ h0, mul_one] at this
  have hvec : rowE σ J e y t *ᵥ v =
      v + form σ J v e • y + (t * form σ J v e) • e - form σ J v y • e := by
    rw [rowE_mulVec, smul_add, smul_smul, mul_comm (form σ J v e) t, add_assoc]
  rw [hvec]
  exact Λ.sub_mem (Λ.add_mem (Λ.add_mem hv (hy _ hα)) (he _ hγ)) (he _ hβ)

end Lat

end GlobalTheory.SnMass.VolN.RowIso

namespace GlobalTheory.SnMass.VolN.RowIso

theorem form_col_col {E : Type} [Field E] (σ : E →+* E) {n m : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (P : Matrix (Fin n) (Fin m) E) (b c : Fin m) :
    form σ J (fun i => P i b) (fun i => P i c) = pairM σ J P P c b := by
  simp only [form, pairM, cT, Matrix.mul_apply, dotProduct, mulVec, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun d _ => ?_
  ring

open GlobalTheory.SnMass.FrameDual in

theorem rowE_mem_GN : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → ∀ (a : Fin r) (y : Fin (2 * r + k + 1) → E) (t : E), (∀ c : Fin r, c ≤ a → form (σ : E →+* E) J y (fun i => P i c.castSucc) = 0) → form (σ : E →+* E) J y y + t + σ t = 0 → (∀ c ∈ (dInv E (r - a.val))⁻¹, c • y ∈ Λ) → t ∈ dInv E (2 * (r - a.val)) → rowE (σ : E →+* E) J (fun i => P i a.castSucc) y t ∈ GN (σ : E →+* E) J Λ P := by
  intro F E _ _ _ _ _ σ k r J Λ P f T A s hV a y t hyc hyt hyΛ htI
  obtain ⟨hcm, -, hJ, hΛ, hP, -, htup, -⟩ := hV
  set σ' : E →+* E := (σ : E →+* E) with hσ'
  have hσ : ∀ x, σ' (σ' x) = x := by
    intro x
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    have h := hcm.2.2.2 τ
    simp only [hσ', AlgHom.coe_toRingHom, h, star_star]
  have hJ' : ∀ i j, σ' (J j i) = J i j := hJ.1
  have hyt' : form σ' J y y + t + σ' t = 0 := hyt
  set e : Fin (2 * r + k + 1) → E := fun i => P i a.castSucc with he_def
  set 𝔞 : FractionalIdeal (𝓞 E)⁰ E := dInv E (r - a.val) with h𝔞
  have heb : ∀ b c : Fin r, form σ' J (fun i => P i b.castSucc) (fun i => P i c.castSucc) = 0 := by
    intro b c
    rw [form_col_col, hP.2, TF, Matrix.diagonal_apply]
    split_ifs with h1 h2 <;> first | rfl | exact absurd h2 (Fin.castSucc_ne_last c)
  have hee : form σ' J e e = 0 := heb a a
  have hye : form σ' J y e = 0 := hyc a le_rfl
  have hyb : ∀ b : Fin r, b ≤ a → form σ' J (fun i => P i b.castSucc) y = 0 := by
    intro b hb
    rw [form_herm σ' J hσ hJ', hyc b hb, map_zero]
  have h0 : 𝔞 ≠ 0 := dInv_ne_zero _
  have hs : Stab σ' 𝔞 := stab_dInv hσ _
  have he𝔞 : ∀ c ∈ 𝔞, c • e ∈ Λ := by
    intro c hc
    refine htup (Submodule.subset_span ⟨Fin.castAdd r a.castSucc, c, ?_, ?_⟩)
    · rw [frameDualTupleIdeals_castAdd]; exact hc
    · funext i
      simp [sideM, he_def]
  have ht2 : t ∈ 𝔞 * 𝔞 := by
    rw [h𝔞, dInv, ← pow_add, ← two_mul]
    exact htI
  refine ⟨⟨isUn_of_form σ' J _ (form_rowE hσ hJ' hee hye hyt'), ?_, ?_⟩, ?_⟩
  · refine ⟨Matrix.of fun i j => (if i = j then 1 else 0) -
        (if i = a then form σ' J (fun l => P l j.castSucc) y else 0), ?_, ?_⟩
    · intro i j
      refine ⟨fun hji => ?_, fun hij => ?_⟩
      · have hne : i ≠ j := (ne_of_lt hji).symm
        by_cases hia : i = a
        · subst hia
          simp [hne, hyb j (le_of_lt hji)]
        · simp [hne, hia]
      · subst hij
        by_cases hia : i = a
        · subst hia
          simp [hyb i le_rfl]
        · simp [hia]
    · ext l j
      change (rowE σ' J e y t *ᵥ fun m => P m j.castSucc) l = ∑ i : Fin r, P l i.castSucc *
        ((if i = j then 1 else 0) - (if i = a then form σ' J (fun l => P l j.castSucc) y else 0))
      rw [rowE_mulVec, heb j a]
      simp only [Matrix.of_apply, eOf, Matrix.submatrix_apply, id, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true, Pi.add_apply, Pi.sub_apply,
        Pi.smul_apply, smul_eq_mul, zero_mul, add_zero, he_def]
      ring
  · intro v hv
    have hve : form σ' J v e = 0 := by
      have := congrFun hv a
      rw [← Matrix.mulVec_mulVec] at this
      simpa [form, cT, mulVec, dotProduct, eOf, he_def] using this
    refine ⟨Pi.single a (-form σ' J v y), ?_⟩
    rw [rowE_mulVec, hve, Matrix.mulVec_single]
    ext l
    simp [eOf, he_def] <;> ring
  · apply le_antisymm
    · rintro _ ⟨v, hv, rfl⟩
      exact rowE_mem hσ hΛ h0 hs he𝔞 hyΛ ht2 hv
    · intro v hv
      have hy' : ∀ c ∈ 𝔞⁻¹, c • (-y) ∈ Λ := fun c hc => by
        rw [smul_neg]; exact Λ.neg_mem (hyΛ c hc)
      refine ⟨rowE σ' J e (-y) (σ' t) *ᵥ v, rowE_mem hσ hΛ h0 hs he𝔞 hy' (hs.mul hs t ht2) hv, ?_⟩
      exact rowE_inv hσ hJ' hee hye hyt' v

end GlobalTheory.SnMass.VolN.RowIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualLatticeFrameEqStandardTranslate
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

namespace GlobalTheory.StdLat

theorem eq_img_lamStd : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ), ∀ (Fr : FrameD H r) (Λ : Submodule M.L.O V), H.IsSelfDual Λ → H.IsFrame Λ r Fr.f Fr.T → ∃ L : Submodule M.L.O (H.Wb Fr.f), Fr.IsInner L ∧ (L : Set (H.Wb Fr.f)) = H.Lset Λ Fr.f ∧ ∃ n ∈ Fr.N, (∀ b, n (Fr.f b) = Fr.f b) ∧ Λ = img n (Fr.LamStd L) := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r Fr Λ hSD hFr
  obtain ⟨y, hyΛ, hyf⟩ := GlobalTheory.T.exists_dual_family_in_selfDual_lattice M hM H r Fr Λ hSD hFr
  have hy0 : ∀ (a : Fin r) (b : Fin (r + 1)), H.h (y a.castSucc) (Fr.f b) = if b = a.castSucc then 1 else 0 :=
    fun a b => hyf b a.castSucc
  obtain ⟨y', hy'Λ, hy'f, hy'y⟩ := GlobalTheory.T.exists_totallyIsotropic_dual_family_in_lattice M hM H r Fr Λ hSD hFr (fun a : Fin r => y a.castSucc) (fun a : Fin r => hyΛ _) hy0
  obtain ⟨n, hnU, hnf, hnes, hnX⟩ := GlobalTheory.T.exists_unitary_frame_dual' M H r Fr y' hy'f hy'y
  obtain ⟨L, hLset, hLin⟩ := GlobalTheory.T.exists_innerLattice_image_frame_quotient M hM H r Fr Λ hSD hFr y' hy'Λ hy'f
  have heΛ : ∀ a : Fin r, Fr.f a.castSucc ∈ Λ := fun a => hFr.1.1 _
  refine ⟨L, hLin, hLset, n, ?_, hnf, ?_⟩
  · apply Subgroup.subset_closure
    refine ⟨hnU, ?_, hnX⟩
    intro j _ v hv
    have hle : Fr.Fj j ≤ LinearMap.ker ((n : V →ₗ[E] V) - LinearMap.id) := by
      rw [FrameD.Fj, Submodule.span_le]
      rintro _ ⟨a, _, rfl⟩
      simp [FrameD.e, hnf]
    have h1 := hle hv
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply] at h1
    rw [show n v - v = 0 from h1]
    exact zero_mem _
  · exact GlobalTheory.T.unitary_image_standardLattice_eq_selfDual_lattice M H r Fr Λ hSD heΛ L hLset n hnU (fun a => hnf _) (fun a => by rw [hnes]; exact hy'Λ a) hnX

end GlobalTheory.StdLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentRadicalInterConjugateClosedUnimodularStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.SnMass
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotentRadical_inter_conjugate_closed_unimodular : ∀ (k r : ℕ) (γ : Mat k r), γ ∈ GG k r → IsClosedSub k r (Rset k r γ) ∧ ∀ μ, IsHaarOn (Rset k r γ) μ → IsUnimod (Rset k r γ) μ := by
  first | exact @GlobalTheory.UnipUnimod.rset_unimodular | exact GlobalTheory.UnipUnimod.rset_unimodular | (intros; apply GlobalTheory.UnipUnimod.rset_unimodular <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitriangularChangeFrameUnipotentStatement
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitriangular_change_frame_unipotent : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ) (Fr : FrameD H r) (L : Submodule M.L.O (H.Wb Fr.f)), ∀ A : Matrix (Fin (r + 1)) (Fin (r + 1)) E, Uni A → (∀ a b, A a b ∈ M.L.O) → ∃ n ∈ Fr.N, (∀ c : Fin r, n (Fr.f c.castSucc) = ∑ a, A a c.castSucc • Fr.f a) ∧ n (Fr.f (Fin.last r)) = Fr.f (Fin.last r) ∧ img n (Fr.LamStd L) = Fr.LamStd L := by
  first | exact @GlobalTheory.LocOver.UnipLevi.levi_integral | exact GlobalTheory.LocOver.UnipLevi.levi_integral | (intros; apply GlobalTheory.LocOver.UnipLevi.levi_integral <;> assumption)
end

