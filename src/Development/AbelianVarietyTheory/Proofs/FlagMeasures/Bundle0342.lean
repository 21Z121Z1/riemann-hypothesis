import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0118
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0334
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0215
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0217
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0218
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0212
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0209
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0219
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0214
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0193
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0175
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0283
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0338
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0179
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagLeviRealPlacesProductMeasure
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase
open Formalism.REAL (Jm UJ muG)

noncomputable section

namespace GlobalTheory.LeviIso

theorem detNorm_pos_iff {E : Type} [Field E] [NumberField E] {j : ℕ} (x : MatInf E j) :
    0 < detNorm E j x ↔ ∀ w, (Matrix.of (x w)).det ≠ 0 := by
  unfold detNorm
  constructor
  · intro h w hw
    rw [Finset.prod_eq_zero (Finset.mem_univ w) (by rw [hw]; simp)] at h
    exact lt_irrefl _ h
  · intro h
    exact Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.2 (h w)) 2

theorem gram_place (I : AutInst) (v : InfinitePlace I.F) {p q : Type} (X : Matrix (Fin I.n) p I.E)
    (Y : Matrix (Fin I.n) q I.E) :
    ((I.P v)⁻¹ * X.map (I.φ v))ᴴ * Jm (I.ε v) * ((I.P v)⁻¹ * Y.map (I.φ v)) = (Xᴴ * I.J * Y).map (I.φ v) := by
  have hP : I.P v * (I.P v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v))
  have hX : (X.map (I.φ v))ᴴ = Xᴴ.map (I.φ v) := by
    ext r s
    exact (I.cm.cmUnram.2.1 (I.φ v) (X s r)).symm
  rw [← I.P_spec v, Matrix.map_mul, Matrix.map_mul, ← hX]
  calc _ = (I.P v * (I.P v)⁻¹ * X.map (I.φ v))ᴴ * I.J.map (I.φ v) * (I.P v * (I.P v)⁻¹ * Y.map (I.φ v)) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [hP, Matrix.one_mul, Matrix.one_mul]

theorem conjT_map {τ : ℂ →+* ℂ} (hτ : τ = RingHom.id ℂ ∨ τ = starRingEnd ℂ) {p q : Type} (X : Matrix p q ℂ) :
    (X.map τ)ᴴ = Xᴴ.map τ := by
  rcases hτ with rfl | rfl <;> ext r s <;> simp

theorem Jm_map {n : ℕ} (ε : Fin n → Bool) (τ : ℂ →+* ℂ) : (Jm ε).map τ = Jm ε := by
  ext r s
  simp only [Jm, Matrix.map_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem inv_map {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P) (τ : ℂ →+* ℂ) :
    P.map τ * P⁻¹.map τ = 1 := by
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)]
  simp

theorem exists_charts (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ)
    (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (Λ : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E))
    (x₀ : I₀.Gf) (T T' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E)
    (hj : ∀ i, 1 ≤ j i) (h : IsAdapted I I₀ e xf j S Λ x₀ T T' T₀) (v : InfinitePlace I.F)
    (v₀ : InfinitePlace I₀.F) (τ τ₀ : ℂ →+* ℂ) (hτ : τ = RingHom.id ℂ ∨ τ = starRingEnd ℂ)
    (hτ₀ : τ₀ = RingHom.id ℂ ∨ τ₀ = starRingEnd ℂ) (hv : ∀ y, I.φ v (e y) = τ₀ (I₀.φ v₀ y)) :
    ∃ θ, IsLeviChart (I.ε v) (I₀.ε v₀) (flagAt I S v) (fun i => (I.P v)⁻¹ * (T i).map (I.φ v))
      ((I.P v)⁻¹ * T₀.map (I.φ v) * (I₀.P v₀).map τ₀) τ τ₀ θ := by
  have hsat := GlobalTheory.T.isSaturatedIsotropicFlag_of_adaptedBasis I I₀ e xf a j S Λ x₀ T T' T₀ hj h
  have hsp := GlobalTheory.T.columnBlocksSpanFlag_flagAdaptedLatticeBasis I I₀ e xf a j S Λ x₀ T T' T₀ h v
  obtain ⟨-, hn, -, h1, h2, h3, -, -⟩ := h
  have hJ : I.Jᴴ = I.J := I.J_herm
  have sw : ∀ i k, (T' i)ᴴ * I.J * T k = ((T k)ᴴ * I.J * T' i)ᴴ := by
    intro i k
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJ, Matrix.mul_assoc]
  refine GlobalTheory.T.complementary_block_unitary_forms _ _ a j _ _ _ _ (fun i => ((I.P v)⁻¹ * (T' i).map (I.φ v))ᴴ * Jm (I.ε v)) _ τ τ₀ hτ hτ₀ hn
    (fun i => ?_) (fun i k hik => ?_) (fun i k => ?_) (fun i => ?_) ?_ hsp (GlobalTheory.T.isTotallyIsotropicFlag_complexified_saturatedFlag I _ a j S hsat v)
  · rw [gram_place, sw, (h2 i).1]
    simp
  · rw [gram_place, sw, (h1 k i).2.2 hik.symm]
    simp
  · rw [gram_place, (h1 i k).1]
    simp
  · rw [← Matrix.mul_assoc, gram_place, (h2 i).2.1]
    simp
  · have e1 : (I₀.J.map e).map (I.φ v) = (I₀.J.map (I₀.φ v₀)).map τ₀ := by
      ext r s
      exact hv _
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (Jm _),
      ← Matrix.mul_assoc _ _ ((I₀.P v₀).map τ₀), ← Matrix.mul_assoc _ (Jm _), gram_place, h3, e1,
      conjT_map hτ₀, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.mul_assoc, I₀.P_spec, Jm_map]

theorem size_solve {f k : ℕ} (hf : 1 ≤ f) (hk : 1 ≤ k) {s t D : ℝ} (hs : 0 < s) (ht : 0 < t) (hD : 0 < D)
    (h : t ^ f = s ^ f * D ^ (-(1 : ℝ) / (2 * k))) :
    t = (D / s ^ (2 * f * k)) ^ (-(1 / (2 * (f : ℝ) * k))) := by
  have hf' : (f : ℝ) ≠ 0 := by positivity
  have hk' : (k : ℝ) ≠ 0 := by positivity
  have h1 := congrArg Real.log h
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_rpow hD] at h1
  apply Real.log_injOn_pos ht (Real.rpow_pos_of_pos (by positivity) _)
  rw [Real.log_rpow (by positivity), Real.log_div hD.ne' (by positivity), Real.log_pow]
  push_cast
  field_simp
  field_simp at h1
  linarith

theorem ae_detNorm_pos (E : Type) [Field E] [NumberField E] {a : ℕ} (j : Fin a → ℕ) :
    ∀ᵐ z ∂(Measure.pi fun i => haarGL E (j i)), ∀ i, 0 < detNorm E (j i) (z i) := by
  have hσ : ∀ i, SigmaFinite (haarGL E (j i)) := fun i => by
    rw [GlobalTheory.T.infiniteGLHaarMeasure_eq_pi_local]
    exact inferInstanceAs (SigmaFinite (Measure.pi fun _ : InfinitePlace E => haarLoc (j i)))
  have h1 : ∀ i, ∀ᵐ x ∂(haarGL E (j i)), 0 < detNorm E (j i) x := by
    intro i
    rw [GlobalTheory.T.infiniteGLHaarMeasure_eq_pi_local]
    have h2 : ∀ᵐ x ∂(Measure.pi fun _ : InfinitePlace E => haarLoc (j i)), ∀ w, (Matrix.of (x w)).det ≠ 0 := by
      refine ae_all_iff.2 fun w => ?_
      have h3 : ∀ᵐ y ∂(haarLoc (j i)), (Matrix.of y).det ≠ 0 := by
        rw [ae_iff]
        simpa using (GlobalTheory.T.haarComplexGLMatrices_conj_and_singular_null (j i)).2
      exact (Measure.quasiMeasurePreserving_eval (fun _ : InfinitePlace E => haarLoc (j i)) w).ae h3
    exact h2.mono fun x hx => (detNorm_pos_iff x).2 hx
  exact ae_all_iff.2 fun i => (Measure.quasiMeasurePreserving_eval (fun i => haarGL E (j i)) i).ae (h1 i)

theorem levi_product : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (Λ : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E)) (x₀ : I₀.Gf) (T T' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E), (∀ i, 1 ≤ j i) → IsAdapted I I₀ e xf j S Λ x₀ T T' T₀ → ∀ (μM : ∀ v, Measure (Formalism.REAL.UJ (I.ε v))) [∀ v, SigmaFinite (μM v)] (c₀ : InfinitePlace I₀.F → ℝ), (∀ v, IsGaugeSub (flagM (I.ε v) (flagAt I S v)) ((I.n - 2 * ∑ i, j i) ^ 2 + 2 * ∑ i, j i ^ 2) (μM v)) → IsGaugeAll I₀ c₀ → ∃ (Θ : (∀ i, MatInf I.E (j i)) × I₀.Ginf → I.Ginf) (κ : Fin a → ℝ), Measurable Θ ∧ (∀ i, 0 < κ i) ∧ (∀ m : I.Ginf, (∀ v, m v ∈ flagM (I.ε v) (flagAt I S v)) ↔ ∃ z : ((∀ i, MatInf I.E (j i)) × I₀.Ginf), (∀ i, 0 < detNorm I.E (j i) (z.1 i)) ∧ Θ z = m) ∧ (∀ z z' : ((∀ i, MatInf I.E (j i)) × I₀.Ginf), (∀ i, z.1 i ∈ autGL I.E (j i) (Λ i)) → z.2 ∈ latGroup I₀ x₀ → (∀ i, 0 < detNorm I.E (j i) (z'.1 i)) → ∃ γ ∈ leviGroup I xf S, γ * Θ z' = Θ (fun i => z.1 i * z'.1 i, z.2 * z'.2)) ∧ (∀ z : ((∀ i, MatInf I.E (j i)) × I₀.Ginf), (∀ i, 0 < detNorm I.E (j i) (z.1 i)) → ∀ i, sizesAt I xf S (Θ z) i = (detNorm I.E (j i) (z.1 i) / κ i) ^ (-(1 / (2 * (I.f : ℝ) * j i)))) ∧ (∀ z z' : ((∀ i, MatInf I.E (j i)) × I₀.Ginf), (∀ i, 0 < detNorm I.E (j i) (z.1 i)) → (∀ i, 0 < detNorm I.E (j i) (z'.1 i)) → Θ z = Θ z' → z = z') ∧ ∀ φ : I.Ginf → ENNReal, Measurable φ → ∫⁻ m, φ m ∂(Measure.pi μM) = (∏ i, ENNReal.ofReal (2 ^ (I.f * j i ^ 2))) * ENNReal.ofReal (∏ v, c₀ v) * ∫⁻ z₁ in {z₁ | ∀ i, 0 < detNorm I.E (j i) (z₁ i)}, ∫⁻ z₂, φ (Θ (z₁, z₂)) ∂(Measure.pi fun v => Formalism.REAL.muG (I₀.ε v)) ∂(Measure.pi fun i => haarGL I.E (j i)) := by
  intro I I₀ e xf a j S Λ x₀ T T' T₀ hj h μM _ c₀ hμ hc₀
  have hsat := GlobalTheory.T.isSaturatedIsotropicFlag_of_adaptedBasis I I₀ e xf a j S Λ x₀ T T' T₀ hj h
  obtain ⟨β, σ, τ, τ₀, hτ, hτ₀, hβ, hσ⟩ := GlobalTheory.T.realPlaces_match_isomorphic_CM_instances I I₀ e h.1
  choose θ hθ using fun v => exists_charts I I₀ e xf a j S Λ x₀ T T' T₀ hj h v (σ v) (τ v) (τ₀ v) (hτ v) (hτ₀ v)
    (hσ v)
  have hcard : Fintype.card (InfinitePlace I.F) = I.f := GlobalTheory.Count.FrameMajorant.card_places I
  have hf : 1 ≤ I.f := Module.finrank_pos
  let R : (∀ i, MatInf I.E (j i)) × I₀.Ginf →
      ∀ v : InfinitePlace I.F, (∀ i, Fin (j i) → Fin (j i) → ℂ) × UJ (I₀.ε (σ v)) :=
    fun z v => (fun i => z.1 i (β v), z.2 (σ v))
  have hR := GlobalTheory.T.measurePreserving_rearrange_pi_prod_measures _ _ _ β σ a (fun i => Fin (j i) → Fin (j i) → ℂ) (fun w => UJ (I₀.ε w))
    (fun i => haarLoc (j i)) (fun w => muG (I₀.ε w)) (fun i => 2 ^ (j i ^ 2)) c₀ (fun i => by positivity)
    (fun w => ((GlobalTheory.T.riemannianHaarGauge_whole_group _ _).1 _ (hc₀ w)).1.le)
  have hRm : Measurable R := hR.measurable
  have hΘ : Measurable fun (z : (∀ i, MatInf I.E (j i)) × I₀.Ginf) v => θ v (R z v) :=
    measurable_pi_lambda _ fun v => (hθ v).1.comp ((measurable_pi_apply v).comp hRm)
  have hdet : ∀ z : (∀ i, MatInf I.E (j i)) × I₀.Ginf, (∀ i, 0 < detNorm I.E (j i) (z.1 i)) →
      ∀ v i, (Matrix.of ((R z v).1 i)).det ≠ 0 := fun z hz v i => (detNorm_pos_iff _).1 (hz i) (β v)
  have hM : ∀ z : (∀ i, MatInf I.E (j i)) × I₀.Ginf, (∀ i, 0 < detNorm I.E (j i) (z.1 i)) →
      ∀ v, θ v (R z v) ∈ flagM (I.ε v) (flagAt I S v) := fun z hz v =>
    ((hθ v).2.1 _).2 ⟨R z v, hdet z hz v, rfl⟩
  have hpos := fun g : I.Ginf => GlobalTheory.T.sizeQ_saturatedIsotropicFlag_pos I (g, xf) a j S hsat
  refine ⟨fun z v => θ v (R z v), fun i => sizesAt I xf S 1 i ^ (2 * I.f * j i), hΘ,
    fun i => pow_pos (hpos 1 i) _, fun m => ⟨fun hm => ?_, ?_⟩, fun z z' hz1 hz2 hz' => ?_, fun z hz i => ?_,
    fun z z' hz hz' hzz => ?_, fun φ hφ => ?_⟩
  · choose y hy1 hy2 using fun v => ((hθ v).2.1 (m v)).1 (hm v)
    refine ⟨(fun i w => (y (β.symm w)).1 i, Equiv.piCongrLeft (fun w => UJ (I₀.ε w)) σ fun v => (y v).2),
      fun i => (detNorm_pos_iff _).2 fun w => hy1 _ i, funext fun v => ?_⟩
    rw [← hy2 v]
    refine congrArg (θ v) (Prod.ext (funext fun i => ?_) ?_)
    · exact congrArg (fun u => (y u).1 i) (β.symm_apply_apply v)
    · exact Equiv.piCongrLeft_apply_apply (fun w => UJ (I₀.ε w)) σ (fun v => (y v).2) v
  · rintro ⟨z, hz, rfl⟩
    exact hM z hz
  · choose γ hγ1 hγ2 using hz1
    obtain ⟨g, hg, Γ, γ₀, g1, g2, g3, g4⟩ := GlobalTheory.T.exists_rational_flag_block_fixing_lattice I I₀ e xf a j S Λ x₀ T T' T₀ h γ hγ1 z.2 hz2
    have hz : ∀ i, 0 < detNorm I.E (j i) (z.1 i) := by
      intro i
      refine (detNorm_pos_iff _).2 fun w => ?_
      have : Matrix.of (z.1 i w) = (γ i : Matrix (Fin (j i)) (Fin (j i)) I.E).map w.embedding := by
        ext r s
        exact hγ2 i w r s
      rw [this]
      exact ((Matrix.isUnit_iff_isUnit_det _).1 ((γ i).isUnit.map w.embedding.mapMatrix)).ne_zero
    have hP : ∀ v, I.P v * (I.P v)⁻¹ = 1 := fun v =>
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v))
    have hact : ∀ (v) {p : Type} (X : Matrix (Fin I.n) p I.E),
        uMat (g v) * ((I.P v)⁻¹ * X.map (I.φ v)) = (I.P v)⁻¹ * (Γ * X).map (I.φ v) := by
      intro v p X
      rw [g1, Matrix.mul_assoc, ← Matrix.mul_assoc (I.P v), hP, Matrix.one_mul, Matrix.map_mul, Matrix.mul_assoc]
    have hA : ∀ v i, uMat (g v) * ((I.P v)⁻¹ * (T i).map (I.φ v)) =
        (I.P v)⁻¹ * (T i).map (I.φ v) * (Matrix.of ((R z v).1 i)).map (τ v) := by
      intro v i
      rw [hact, g3, Matrix.map_mul, Matrix.mul_assoc]
      congr 2
      ext r s
      exact (hβ v _).trans (congrArg (τ v) (hγ2 i (β v) r s).symm)
    have hA₀ : ∀ v, uMat (g v) * ((I.P v)⁻¹ * T₀.map (I.φ v) * (I₀.P (σ v)).map (τ₀ v)) =
        (I.P v)⁻¹ * T₀.map (I.φ v) * (I₀.P (σ v)).map (τ₀ v) * (uMat (R z v).2).map (τ₀ v) := by
      intro v
      have e1 : (γ₀.map e).map (I.φ v) = (γ₀.map (I₀.φ (σ v))).map (τ₀ v) := by
        ext r s
        exact hσ v _
      have e2 : uMat (R z v).2 = _ := g2 (σ v)
      rw [← Matrix.mul_assoc, hact, g4, Matrix.map_mul, e1, e2, Matrix.map_mul, Matrix.map_mul,
        Matrix.mul_assoc _ ((I₀.P (σ v)).map (τ₀ v)), ← Matrix.mul_assoc ((I₀.P (σ v)).map (τ₀ v)),
        ← Matrix.mul_assoc ((I₀.P (σ v)).map (τ₀ v)), inv_map _ (I₀.P_unit _), Matrix.one_mul]
      simp only [Matrix.mul_assoc]
    refine ⟨fun v => θ v (R z v), ⟨hM z hz, g, ⟨hg, fun v k y hy => ?_⟩, g * (fun v => θ v (R z v))⁻¹,
      fun v => ((hθ v).2.2.2.1 (R z v) (hdet z hz v)).2 (g v) (hA v) (hA₀ v), (inv_mul_cancel_right _ _).symm⟩,
      funext fun v => ((hθ v).2.2.1 (R z v) (R z' v) (hdet z hz v) (hdet z' hz' v)).1⟩
    have hsp := GlobalTheory.T.columnBlocksSpanFlag_flagAdaptedLatticeBasis I I₀ e xf a j S Λ x₀ T T' T₀ h v
    obtain ⟨u, hu, rfl⟩ := (hsp k y).1 hy
    refine (hsp k _).2 ⟨fun i => (Matrix.of ((R z v).1 i)).map (τ v) *ᵥ u i, fun i hi => ?_, ?_⟩
    · simp only [hu i hi, Matrix.mulVec_zero]
    · simp only [Matrix.mulVec_sum, Matrix.mulVec_mulVec, hA]
  · have h0 : ∀ v, uMat ((1 : I.Ginf) v) = 1 := fun v => rfl
    have h1 := GlobalTheory.T.gradedPieceSizes_unipotent_levi_compact_move I xf a j hj S hsat 1 (fun v => θ v (R z v)) 1
      (fun v => ⟨fun i y _ => by rw [h0]; simp, fun y _ => by rw [h0]; simp⟩) (hM z hz)
      (fun v => show (uMat ((1 : I.Ginf) v))ᴴ * uMat ((1 : I.Ginf) v) = 1 by rw [h0]; simp) i
    rw [one_mul, mul_one] at h1
    refine size_solve hf (hj i) (hpos 1 i) (hpos _ i) (hz i) (h1.trans ?_)
    congr 1
    simp only [fun v => ((hθ v).2.2.2.1 (R z v) (hdet z hz v)).1 i]
    have hj' : (j i : ℝ) ≠ 0 := by have := hj i; positivity
    rw [detNorm, ← Real.finset_prod_rpow _ _ (fun w _ => by positivity)]
    refine Fintype.prod_equiv β _ _ fun v => ?_
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
    congr 1
    push_cast
    field_simp
  · have h1 : ∀ v, R z v = R z' v := fun v =>
      ((hθ v).2.2.1 (R z v) (R z' v) (hdet z hz v) (hdet z' hz' v)).2 (congrFun hzz v)
    refine Prod.ext (funext fun i => funext fun w => ?_) (funext fun w => ?_)
    · obtain ⟨v, rfl⟩ := β.surjective w
      exact congrFun (congrArg Prod.fst (h1 v)) i
    · obtain ⟨v, rfl⟩ := σ.surjective w
      exact congrArg Prod.snd (h1 v)
  · have hd : I.n - 2 * ∑ i, j i = I₀.n := by rw [h.2.1]; omega
    rw [hd] at hμ
    have h1 := funext fun v => (hθ v).2.2.2.2 (μM v) (c₀ (σ v)) (hμ v) (hc₀ (σ v))
    have h2 := measurePreserving_pi _ μM (f := θ) fun v => ⟨(hθ v).1, (congrFun h1 v).symm⟩
    have h3 := (h2.comp hR).lintegral_comp hφ
    have h4 : (Measure.pi fun i => haarGL I.E (j i)).restrict {z₁ | ∀ i, 0 < detNorm I.E (j i) (z₁ i)} =
        Measure.pi fun i => haarGL I.E (j i) := Measure.restrict_eq_self_of_ae_mem (ae_detNorm_pos I.E j)
    rw [← h3, lintegral_smul_measure, h4, smul_eq_mul, hcard]
    simp only [GlobalTheory.T.infiniteGLHaarMeasure_eq_pi_local]
    congr 1
    · simp only [← pow_mul, mul_comm]
    · exact lintegral_prod _ (hφ.comp hΘ).aemeasurable

end GlobalTheory.LeviIso
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralInvOfSupport
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.IdemProj

section General

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] [SigmaFinite μ]

theorem integral_inv_of_support (K : Subgroup G) (hc : IsCompact (K : Set G)) (ho : IsOpen (K : Set G))
    (f : G → ℂ) (hf : Continuous f) (hs : ∀ x, f x ≠ 0 → x ∈ K) :
    ∫ x, f x⁻¹ ∂μ = ∫ x, f x ∂μ := by
  have hKcl : IsClosed (K : Set G) := K.isClosed_of_isOpen ho
  have hu : Continuous ((K : Set G).indicator fun _ => (1 : ℂ)) :=
    (IsClopen.continuous_indicator ⟨hKcl, ho⟩ continuous_const)
  set u : G → ℂ := (K : Set G).indicator fun _ => (1 : ℂ) with hu_def

  set Φ : G × G → ℂ := fun z => f z.2⁻¹ * u (z.1 * z.2) with hΦ_def
  have hΦc : Continuous Φ := (hf.comp continuous_snd.inv).mul (hu.comp continuous_mul)
  have hΦs : HasCompactSupport Φ := by
    refine HasCompactSupport.intro (hc.prod hc) fun z hz => ?_
    by_cases h2 : f z.2⁻¹ = 0
    · simp [hΦ_def, h2]
    · have hb : z.2 ∈ K := by simpa using K.inv_mem (hs _ h2)
      have ha : z.1 ∉ K := fun ha => hz ⟨ha, hb⟩
      have : z.1 * z.2 ∉ K := fun h => ha ((K.mul_mem_cancel_right hb).1 h)
      simp [hΦ_def, hu_def, this]
  have hΦi : Integrable Φ (μ.prod μ) := hΦc.integrable_of_hasCompactSupport hΦs
  have hT := measurePreserving_prod_inv_mul_swap μ μ
  have hΦTi : Integrable (fun z : G × G => Φ (z.2, z.2⁻¹ * z.1)) (μ.prod μ) :=
    (hT.integrable_comp hΦc.aestronglyMeasurable).2 hΦi
  have hswap : ∫ z, Φ (z.2, z.2⁻¹ * z.1) ∂(μ.prod μ) = ∫ z, Φ z ∂(μ.prod μ) := by
    conv_rhs => rw [← hT.map_eq]
    rw [integral_map hT.measurable.aemeasurable]
    rw [hT.map_eq]; exact hΦc.aestronglyMeasurable
  set c : ℂ := ∫ a, u a ∂μ with hc_def
  have hcne : c ≠ 0 := by
    rw [hc_def, hu_def, integral_indicator_const _ hKcl.measurableSet]
    have hpos : 0 < μ (K : Set G) := ho.measure_pos μ ⟨1, K.one_mem⟩
    have hfin : μ (K : Set G) ≠ ⊤ := hc.measure_lt_top.ne
    have : μ.real (K : Set G) ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hpos.ne', hfin⟩
    simpa [Complex.real_smul] using this
  have hleft : ∫ z, Φ z ∂(μ.prod μ) = (∫ b, f b⁻¹ ∂μ) * c := by
    rw [integral_prod_symm Φ hΦi, ← integral_mul_const]
    congr 1; funext b
    simp only [hΦ_def]
    rw [integral_const_mul]
    by_cases h2 : f b⁻¹ = 0
    · simp [h2]
    · have hb : b ∈ K := by simpa using K.inv_mem (hs _ h2)
      congr 1
      rw [hc_def]
      congr 1; funext a
      classical
      simp only [hu_def, Set.indicator_apply, SetLike.mem_coe, K.mul_mem_cancel_right hb]
  have hright : ∫ z, Φ (z.2, z.2⁻¹ * z.1) ∂(μ.prod μ) = (∫ x, f x ∂μ) * c := by
    rw [integral_prod _ hΦTi]
    simp only [hΦ_def, _root_.mul_inv_rev, inv_inv, mul_inv_cancel_left]
    rw [hc_def, ← integral_const_mul]
    congr 1; funext x
    rw [integral_mul_const, integral_mul_left_eq_self (fun y => f y) x⁻¹]
  have := hswap
  rw [hleft, hright] at this
  exact (mul_right_cancel₀ hcne this).symm

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

omit [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G]
  [BorelSpace G] in

theorem inner_rep (π : G → (H →L[ℂ] H)) (h1 : π 1 = 1) (hm : ∀ a b, π (a * b) = π a * π b)
    (hn : ∀ g v, ‖π g v‖ = ‖v‖) (g : G) (x y : H) : ⟪x, π g y⟫_ℂ = ⟪π g⁻¹ x, y⟫_ℂ := by
  have hback : π g (π g⁻¹ x) = x := by
    have := congrArg (fun S : H →L[ℂ] H => S x) (hm g g⁻¹)
    simp only [mul_inv_cancel, h1, ContinuousLinearMap.one_apply, ContinuousLinearMap.mul_apply] at this
    exact this.symm
  let U : H →ₗᵢ[ℂ] H := ⟨(π g).toLinearMap, hn g⟩
  calc ⟪x, π g y⟫_ℂ = ⟪U (π g⁻¹ x), U y⟫_ℂ := by
        show ⟪x, π g y⟫_ℂ = ⟪π g (π g⁻¹ x), π g y⟫_ℂ
        rw [hback]
    _ = ⟪π g⁻¹ x, y⟫_ℂ := U.inner_map_map _ _

theorem op_idem (K : Subgroup G) (hc : IsCompact (K : Set G))
    (π : G → (H →L[ℂ] H)) (h1 : π 1 = 1) (hm : ∀ a b, π (a * b) = π a * π b)
    (hn : ∀ g v, ‖π g v‖ = ‖v‖) (hπ : ∀ v, Continuous fun g => π g v)
    (e : G → ℂ) (he : Continuous e) (hs : ∀ x, e x ≠ 0 → x ∈ K)
    (hee : ∀ x, ∫ y, e y * e (y⁻¹ * x) ∂μ = e x) (T : H →L[ℂ] H)
    (hT : ∀ x y : H, ⟪x, T y⟫_ℂ = ∫ g, e g * ⟪x, π g y⟫_ℂ ∂μ) : T.comp T = T := by
  ext y
  refine ext_inner_left ℂ fun x => ?_
  rw [ContinuousLinearMap.comp_apply, hT x (T y)]
  have step : ∀ g, ⟪x, π g (T y)⟫_ℂ = ∫ h, e (g⁻¹ * h) * ⟪x, π h y⟫_ℂ ∂μ := by
    intro g
    have shift := integral_mul_left_eq_self (μ := μ) (fun h => e (g⁻¹ * h) * ⟪x, π h y⟫_ℂ) g
    simp only [inv_mul_cancel_left] at shift
    rw [inner_rep π h1 hm hn g, hT, ← shift]
    congr 1; funext h
    rw [hm, ContinuousLinearMap.mul_apply, inner_rep π h1 hm hn g]
  have hint : Integrable (Function.uncurry fun g h => e g * (e (g⁻¹ * h) * ⟪x, π h y⟫_ℂ))
      (μ.prod μ) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (he.comp continuous_fst).mul ((he.comp (continuous_fst.inv.mul continuous_snd)).mul
        (continuous_const.inner ((hπ y).comp continuous_snd)))
    · refine HasCompactSupport.intro (hc.prod hc) ?_
      rintro ⟨g, h⟩ hgh
      simp only [Function.uncurry_apply_pair]
      by_cases hg : g ∈ K
      · have hh : h ∉ K := fun hh => hgh ⟨hg, hh⟩
        have h0 : e (g⁻¹ * h) = 0 := by
          by_contra hne
          exact hh (by simpa using K.mul_mem hg (hs _ hne))
        simp [h0]
      · have h0 : e g = 0 := by
          by_contra hne
          exact hg (hs _ hne)
        simp [h0]
  calc ∫ g, e g * ⟪x, π g (T y)⟫_ℂ ∂μ
      = ∫ g, ∫ h, e g * (e (g⁻¹ * h) * ⟪x, π h y⟫_ℂ) ∂μ ∂μ := by
        congr 1; funext g
        rw [step g, integral_const_mul]
    _ = ∫ h, ∫ g, e g * (e (g⁻¹ * h) * ⟪x, π h y⟫_ℂ) ∂μ ∂μ := integral_integral_swap hint
    _ = ∫ h, e h * ⟪x, π h y⟫_ℂ ∂μ := by
        congr 1; funext h
        simp_rw [← mul_assoc]
        rw [integral_mul_const, hee]
    _ = ⟪x, T y⟫_ℂ := (hT x y).symm

theorem op_symm (K : Subgroup G) (hc : IsCompact (K : Set G)) (ho : IsOpen (K : Set G))
    (π : G → (H →L[ℂ] H)) (h1 : π 1 = 1) (hm : ∀ a b, π (a * b) = π a * π b)
    (hn : ∀ g v, ‖π g v‖ = ‖v‖) (hπ : ∀ v, Continuous fun g => π g v)
    (e : G → ℂ) (he : Continuous e) (hs : ∀ x, e x ≠ 0 → x ∈ K)
    (hst : ∀ x, e x⁻¹ = star (e x)) (T : H →L[ℂ] H)
    (hT : ∀ x y : H, ⟪x, T y⟫_ℂ = ∫ g, e g * ⟪x, π g y⟫_ℂ ∂μ) (x y : H) :
    ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ := by
  have hF : Continuous fun g => e g * ⟪x, π g y⟫_ℂ := he.mul (continuous_const.inner (hπ y))
  have hFs : ∀ g, e g * ⟪x, π g y⟫_ℂ ≠ 0 → g ∈ K := fun g hg => hs g (left_ne_zero_of_mul hg)
  conv_lhs => rw [← inner_conj_symm]
  rw [hT y x, ← integral_conj, hT x y, ← integral_inv_of_support μ K hc ho _ hF hFs]
  congr 1; funext g
  show (starRingEnd ℂ) (e g * ⟪y, π g x⟫_ℂ) = e g⁻¹ * ⟪x, π g⁻¹ y⟫_ℂ
  rw [map_mul, inner_conj_symm, starRingEnd_apply, ← hst g, inner_rep π h1 hm hn g⁻¹, inv_inv]

omit [T2Space G] in

theorem op_fixed (π : G → (H →L[ℂ] H)) (h1 : π 1 = 1) (hm : ∀ a b, π (a * b) = π a * π b)
    (hn : ∀ g v, ‖π g v‖ = ‖v‖) (e : G → ℂ) (T : H →L[ℂ] H)
    (hT : ∀ x y : H, ⟪x, T y⟫_ℂ = ∫ g, e g * ⟪x, π g y⟫_ℂ ∂μ) (k : G) (hk : ∀ h, e (k * h) = e h) :
    (π k).comp T = T := by
  ext y
  refine ext_inner_left ℂ fun x => ?_
  rw [ContinuousLinearMap.comp_apply, inner_rep π h1 hm hn k, hT, hT]
  have key : ∀ g, e g * ⟪π k⁻¹ x, π g y⟫_ℂ = e (k * g) * ⟪x, π (k * g) y⟫_ℂ := by
    intro g
    rw [hk g, hm, ContinuousLinearMap.mul_apply, inner_rep π h1 hm hn k]
  simp_rw [key]
  exact integral_mul_left_eq_self (fun h => e h * ⟪x, π h y⟫_ℂ) k

omit [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] in

theorem eventually_left_inv (K : Subgroup G) (hc : IsCompact (K : Set G)) (ho : IsOpen (K : Set G))
    (e : G → ℂ) (he : IsLocallyConstant e) (hs : ∀ x, e x ≠ 0 → x ∈ K) :
    ∀ᶠ k in nhds (1 : G), ∀ h, e (k * h) = e h := by
  have hloc : ∀ h ∈ (K : Set G), ∀ᶠ z : G × G in nhds ((1 : G), h), e (z.1 * z.2) = e z.2 := by
    intro h _
    have hfib : ∀ᶠ y in nhds h, e y = e h := he.eventually_eq h
    have ht : Filter.Tendsto (fun z : G × G => z.1 * z.2) (nhds ((1 : G), h)) (nhds h) := by
      simpa using (continuous_mul (M := G)).tendsto ((1 : G), h)
    have ha := ht.eventually hfib
    have hb : ∀ᶠ z : G × G in nhds ((1 : G), h), e z.2 = e h :=
      (continuous_snd.tendsto ((1 : G), h)).eventually hfib
    filter_upwards [ha, hb] with z hz1 hz2
    rw [hz1, hz2]
  have hK : ∀ᶠ k in nhds (1 : G), ∀ h ∈ (K : Set G), e (k * h) = e h :=
    hc.eventually_forall_of_forall_eventually hloc
  have hmem : ∀ᶠ k in nhds (1 : G), k ∈ (K : Set G) := ho.mem_nhds K.one_mem
  filter_upwards [hK, hmem] with k hk hkK h
  by_cases hh : h ∈ (K : Set G)
  · exact hk h hh
  · have e1 : e h = 0 := by
      by_contra hne
      exact hh (hs h hne)
    have e2 : e (k * h) = 0 := by
      by_contra hne
      exact hh (by simpa using K.mul_mem (K.inv_mem hkK) (hs _ hne))
    rw [e1, e2]

end General

theorem re_orth_proj : ∀ B : RowsAut, IsOrthProjOnto B.Re (LinearMap.range (B.Re : B.I.L2 B.μf B.fund →ₗ[ℂ] B.I.L2 B.μf B.fund)) ∧ (∀ g : B.I.Ginf, B.Re.comp (B.R (g, 1)) = (B.R (g, 1)).comp B.Re) ∧ ∃ g : ℕ, 1 ≤ g ∧ ∀ k ∈ B.I.Kg g, (B.R (1, k)).comp B.Re = B.Re := by
  intro B
  obtain ⟨hT2, -, hSC, hKc, hKo, ⟨K, hK⟩, -⟩ := GlobalTheory.CongTop.adelic_topology B.I
  obtain ⟨hR1, hRm, hRn, hRc, -⟩ := GlobalTheory.T.rightRegularRep_unitary_stronglyContinuous B
  obtain ⟨hlc, hconv, hst, -, hsupp, -, -⟩ := B.e_adm
  obtain ⟨-, hRe⟩ := B.Re_spec
  have hKc' : IsCompact (K : Set B.I.Gf) := by rw [hK]; exact hKc
  have hKo' : IsOpen (K : Set B.I.Gf) := by rw [hK]; exact hKo
  have hs : ∀ x, B.e x ≠ 0 → x ∈ K := by
    intro x hx
    rw [← SetLike.mem_coe, hK]
    exact hsupp x hx
  have h1 : B.R (1, 1) = 1 := hR1
  have hm : ∀ a b : B.I.Gf, B.R (1, a * b) = B.R (1, a) * B.R (1, b) := by
    intro a b
    rw [← hRm, Prod.mk_mul_mk, one_mul]
  have hn : ∀ (g : B.I.Gf) v, ‖B.R (1, g) v‖ = ‖v‖ := fun g v => hRn _ v
  have hπ : ∀ v, Continuous fun g : B.I.Gf => B.R (1, g) v :=
    fun v => (hRc v).comp (continuous_const.prodMk continuous_id)
  have he : Continuous B.e := hlc.continuous
  have hee : ∀ x, ∫ y, B.e y * B.e (y⁻¹ * x) ∂B.μf = B.e x := fun x => congrFun hconv x
  have hT : ∀ x y : B.I.L2 B.μf B.fund,
      ⟪x, B.Re y⟫_ℂ = ∫ g, B.e g * ⟪x, B.R (1, g) y⟫_ℂ ∂B.μf := hRe
  refine ⟨?_, ?_, ?_⟩
  · show B.Re.comp B.Re = B.Re ∧ (∀ x y, ⟪B.Re x, y⟫_ℂ = ⟪x, B.Re y⟫_ℂ) ∧ _
    exact ⟨op_idem B.μf K hKc' (fun g => B.R (1, g)) h1 hm hn hπ B.e he hs hee B.Re hT,
      fun x y => op_symm B.μf K hKc' hKo' (fun g => B.R (1, g)) h1 hm hn hπ B.e he hs hst B.Re hT x y,
      rfl⟩
  · intro g
    refine ContinuousLinearMap.ext fun y => ?_
    refine ext_inner_left ℂ fun x => ?_
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hT x,
      inner_rep B.R hR1 hRm hRn (g, 1) x, hT]
    congr 1; funext k
    have hcomm : ((1 : B.I.Ginf), k) * (g, 1) = (g, 1) * ((1 : B.I.Ginf), k) := by
      simp only [Prod.mk_mul_mk, one_mul, mul_one]
    rw [← inner_rep B.R hR1 hRm hRn (g, 1), ← ContinuousLinearMap.mul_apply,
      ← ContinuousLinearMap.mul_apply, ← hRm, ← hRm, hcomm]
  · obtain ⟨g, hg1, hgsub⟩ := B.I.topf_basis _ (eventually_left_inv K hKc' hKo' B.e hlc hs)
    exact ⟨g, hg1, fun k hk => op_fixed B.μf (fun g => B.R (1, g)) h1 hm hn B.e B.Re hT k
      (hgsub hk)⟩

end GlobalTheory.IdemProj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalMassLeGenericMassConstNine
section
namespace GlobalTheory

theorem localMass_le_genericMass_nine : ∀ k r : ℕ, 4 * r + 7 ≤ k → Formalism.L2.SG.FamDefs.LocalLowerBoundAllCosets k r 9 := by
  intro k r hk F _ _ _ E _ _ _ _ M hM V _ _ H hV P hP R d0 h0 d t ht Y0 hZ
  exact GlobalTheory.mass_pairingClass_bounds M hM H r k P hk hV hP R d0 h0 d t ht Y0 _ rfl hZ _ rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SkewLatticeInverseDifferentPowCovolumeStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.skewLattice_inverseDifferentPow_covolume : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.FormallyUnramified (𝓞 F) (𝓞 E) → ∀ (t : ℕ) (c : ℝ), 0 < c → HasDom volume (skewLat (σ : E →+* E) (dInv E (2 * t)) c : Set (InfinitePlace E → ℝ)) (ENNReal.ofReal (|(NumberField.discr F : ℝ)| ^ (1 / 2 - 2 * (t : ℝ)) * c ^ Fintype.card (InfinitePlace E))) := by
  first | exact @GlobalTheory.SnMass.SkewVol.skew_covol_dInv | exact GlobalTheory.SnMass.SkewVol.skew_covol_dInv | (intros; apply GlobalTheory.SnMass.SkewVol.skew_covol_dInv <;> assumption)
end

