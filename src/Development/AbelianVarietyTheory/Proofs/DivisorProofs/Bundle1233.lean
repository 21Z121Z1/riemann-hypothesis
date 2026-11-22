import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1192
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1171
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormEqOneOfIsUnit
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0127
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0081
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0233
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0228
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0232
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0407
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0430
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1193
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1084
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantIntegralUnipotentCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleTowerTrBasisAppendCoordinates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1194
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnCutoffTopChernFormSmoothGramStatement
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrableOn_cutoff_topChernForm_smoothGram : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (U K : Set (V n)) (G₀ : V n → Matrix r r ℂ) (ρ : V n → ℝ), IsOpen U → IsCompact K → K ⊆ U → (∀ v ∈ U, MContDiffAt ∞ G₀ v ∧ IsUnit (G₀ v).det) → ContDiffOn ℝ ∞ ρ U → (∀ v ∈ U, v ∉ K → ρ v = 0) → IntegrableOn (fun v => (ρ v : ℂ) * mixTop fun _ => curvAt G₀ v) U := by
  first | exact @GlobalTheory.GoodTop.integrableOn_cut_mixTop_smooth | exact GlobalTheory.GoodTop.integrableOn_cut_mixTop_smooth | (intros; apply GlobalTheory.GoodTop.integrableOn_cut_mixTop_smooth <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnPoincareAreaDensityPuncturedDisc
section
open MeasureTheory Filter Topology

namespace GlobalTheory.GoodTop

theorem integrableOn_poincare_disc :
    IntegrableOn (fun z : ℂ => (‖z‖ * |Real.log ‖z‖|)⁻¹ ^ 2) (Metric.closedBall 0 (1 / 2)) := by
  have h := GlobalTheory.T.integrableOn_inv_mul_log_sq_near_zero
  have key : Integrable (fun z : ℂ =>
      (Set.Iic (1 / 2 : ℝ)).indicator (fun t : ℝ => (t * |Real.log t|)⁻¹ ^ 2) ‖z‖) := by
    rw [integrable_fun_norm_addHaar (volume : Measure ℂ)
      (f := (Set.Iic (1 / 2 : ℝ)).indicator (fun t : ℝ => (t * |Real.log t|)⁻¹ ^ 2))]
    have h2 : IntegrableOn ((Set.Iic (1 / 2 : ℝ)).indicator
        (fun t : ℝ => t * (t * |Real.log t|)⁻¹ ^ 2)) (Set.Ioi 0) := by
      rw [IntegrableOn, integrable_indicator_iff measurableSet_Iic, IntegrableOn,
        Measure.restrict_restrict measurableSet_Iic, Set.Iic_inter_Ioi]
      exact h
    refine h2.congr_fun ?_ measurableSet_Ioi
    intro t _
    by_cases ht : t ∈ Set.Iic (1 / 2 : ℝ)
    · simp only [Set.indicator_of_mem ht, Complex.finrank_real_complex, smul_eq_mul]
      norm_num
    · simp only [Set.indicator_of_notMem ht, smul_zero]
  rw [← integrable_indicator_iff measurableSet_closedBall]
  refine key.congr (Eventually.of_forall fun z => ?_)
  by_cases hz : ‖z‖ ∈ Set.Iic (1 / 2 : ℝ)
  · have hz' : z ∈ Metric.closedBall (0 : ℂ) (1 / 2) := by
      rw [mem_closedBall_zero_iff]; exact hz
    simp only [Set.indicator_of_mem hz, Set.indicator_of_mem hz']
  · have hz' : z ∉ Metric.closedBall (0 : ℂ) (1 / 2) := by
      rw [mem_closedBall_zero_iff]; exact hz
    simp only [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz']

end GlobalTheory.GoodTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCharPolyCoeffBounded
section
open NumberField IsDedekindDomain Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC
open scoped Classical TensorProduct
open GlobalTheory.BCT

namespace GlobalTheory.BCT.GeoFin

theorem nrmL_mem_KGL {E : Type} [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E)
    (hL : IsLevel (thL n w) (GlobalTheory.LFun.KGL w n) (GlobalTheory.LFun.KGL w n)) {y : GLw n w}
    (hy : y ∈ GlobalTheory.LFun.KGL w n) : nrmL n w y ∈ GlobalTheory.LFun.KGL w n := by
  have ht := hL.2.2 y hy
  unfold nrmL
  unfold thL at ht
  split_ifs with hs
  · exact hy
  · rw [if_neg hs] at ht
    exact mul_mem hy ht

theorem charpoly_coeff_of_mem_KGL {E : Type} [Field E] [NumberField E] (n : ℕ) (w : Pl E)
    {z : GL (Fin n) (w.adicCompletion E)} (hz : z ∈ GlobalTheory.LFun.KGL w n) :
    (∀ i, Valued.v (z.val.charpoly.coeff i) ≤ 1) ∧ 1 ≤ Valued.v (z.val.charpoly.coeff 0) := by
  obtain ⟨g, rfl⟩ := hz
  set f := (Ov E w).subtype
  have hcp : (Formalism.UG.bc f g).val.charpoly = g.val.charpoly.map f := by
    rw [← Matrix.charpoly_map]
    rfl
  have hint : ∀ a : Ov E w, Valued.v (f a) ≤ 1 := fun a => a.2
  refine ⟨fun i => ?_, ?_⟩
  · rw [hcp, Polynomial.coeff_map]
    exact hint _
  · rw [hcp, Polynomial.coeff_map]
    have hdet : IsUnit (g.val.charpoly.coeff 0) := by
      have h1 : IsUnit g.val.det := (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
      rw [Matrix.det_eq_sign_charpoly_coeff] at h1
      exact isUnit_of_mul_isUnit_right h1
    obtain ⟨u, hu⟩ := hdet
    have hmul : f (u : Ov E w) * f ((u⁻¹ : (Ov E w)ˣ) : Ov E w) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have h2 : Valued.v (f (u : Ov E w)) * Valued.v (f ((u⁻¹ : (Ov E w)ˣ) : Ov E w)) = 1 := by
      rw [← map_mul, hmul, map_one]
    rw [← hu]
    calc (1 : _) = Valued.v (f (u : Ov E w)) * Valued.v (f ((u⁻¹ : (Ov E w)ˣ) : Ov E w)) := h2.symm
      _ ≤ Valued.v (f (u : Ov E w)) * 1 := mul_le_mul' le_rfl (hint _)
      _ = Valued.v (f (u : Ov E w)) := mul_one _

theorem charpoly_nrmL_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E),
    IsLevel (thL n w) (GlobalTheory.LFun.KGL w n) (GlobalTheory.LFun.KGL w n) → ∀ y ∈ GlobalTheory.LFun.KGL w n,
      (∀ i, Valued.v ((nrmL n w y).val.charpoly.coeff i) ≤ 1) ∧ 1 ≤ Valued.v ((nrmL n w y).val.charpoly.coeff 0) :=
  fun _ _ _ _ n w hL y hy => charpoly_coeff_of_mem_KGL n w (nrmL_mem_KGL n w hL hy)

end GlobalTheory.BCT.GeoFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralConjEtaleMemCentralizerMulIntegralGL
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SplitUniq

theorem splitUniq : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (w : HeightOneSpectrum (𝓞 E))
    (N g : GL (Fin n) (w.adicCompletion E)), N ∈ GlobalTheory.LFun.KGL w n →
    (∃ u v : (w.adicCompletion E)[X], (∀ i, u.coeff i ∈ w.adicCompletionIntegers E) ∧
      (∀ i, v.coeff i ∈ w.adicCompletionIntegers E) ∧ u * N.val.charpoly + v * derivative N.val.charpoly = 1) →
    g⁻¹ * N * g ∈ GlobalTheory.LFun.KGL w n → ∃ t : GL (Fin n) (w.adicCompletion E), t * N = N * t ∧ ∃ k ∈ GlobalTheory.LFun.KGL w n, g = t * k := by
  intro E _ _ n w N g hN hs hg
  letI : NontriviallyNormedField (w.adicCompletion E) := Valued.toNontriviallyNormedField _ _
  have key : ∀ x : w.adicCompletion E, ‖x‖ ≤ 1 ↔ x ∈ w.adicCompletionIntegers E := fun x => by
    rw [Valued.toNormedField.norm_le_one_iff, HeightOneSpectrum.mem_adicCompletionIntegers]
  have memK : ∀ h : GL (Fin n) (w.adicCompletion E), h ∈ GlobalTheory.LFun.KGL w n ↔
      (∀ i j, h.1 i j ∈ w.adicCompletionIntegers E) ∧ ∀ i j, (h⁻¹).1 i j ∈ w.adicCompletionIntegers E := fun h => by
    rw [GlobalTheory.LFun.KGL, GlobalTheory.AdelicU.mem_GLint_iff]; rfl
  obtain ⟨hN1, -⟩ := (memK N).1 hN
  obtain ⟨hg1, -⟩ := (memK _).1 hg
  obtain ⟨u, v, hu, hv, huv⟩ := hs
  have hconj : ((g⁻¹ * N * g : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) =
      (g : Matrix (Fin n) (Fin n) (w.adicCompletion E))⁻¹ * N * g := by
    rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv]
  obtain ⟨t, k, ht, htN, hk, hdet, hgtk⟩ := GlobalTheory.SplitLattice.split_place (w.adicCompletion E) n N.val g.val
    (fun i j => (key _).2 (hN1 i j)) ⟨u, v, fun i => (key _).2 (hu i), fun i => (key _).2 (hv i), huv⟩ g.isUnit
    (fun i j => (key _).2 (by rw [← hconj]; exact hg1 i j))
  set tU := ht.unit with htU
  refine ⟨tU, Units.ext htN, tU⁻¹ * g, ?_, by rw [mul_inv_cancel_left]⟩
  have hkv : ((tU⁻¹ * g : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = k := by
    have htt : (tU : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = t := ht.unit_spec
    rw [Units.val_mul, hgtk, ← htt, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  have hkI : ∀ i j, k i j ∈ w.adicCompletionIntegers E := fun i j => (key _).1 (hk i j)
  let M : Matrix (Fin n) (Fin n) (w.adicCompletionIntegers E) := Matrix.of fun i j => ⟨k i j, hkI i j⟩
  have hMk : M.map (w.adicCompletionIntegers E).subtype = k := by ext i j; rfl
  have hdetM : ((M.det : w.adicCompletionIntegers E) : w.adicCompletion E) = k.det := by
    rw [← hMk]
    exact (RingHom.map_det (w.adicCompletionIntegers E).subtype M)
  have hk0 : k.det ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hdet; exact zero_ne_one hdet
  have hMu : IsUnit M.det := by
    have h1 : M.det * ⟨(k.det)⁻¹, (key _).1 (by rw [norm_inv, hdet, inv_one])⟩ = 1 := by
      apply Subtype.ext
      show ((M.det : w.adicCompletionIntegers E) : w.adicCompletion E) * (k.det)⁻¹ = 1
      rw [hdetM, mul_inv_cancel₀ hk0]
    exact ⟨⟨_, _, h1, by rw [mul_comm]; exact h1⟩, rfl⟩
  have hMM : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hMu
  have hinv : k⁻¹ = M⁻¹.map (w.adicCompletionIntegers E).subtype := by
    apply Matrix.inv_eq_right_inv
    rw [← hMk, ← Matrix.map_mul, hMM, Matrix.map_one _ (map_zero _) (map_one _)]
  refine (memK _).2 ⟨fun i j => by rw [hkv]; exact hkI i j, fun i j => ?_⟩
  rw [Matrix.coe_units_inv, hkv, hinv]
  exact (M⁻¹ i j).2

end GlobalTheory.SplitUniq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralConjSetLocalUnitaryEqDoubleCoset
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.OrbitT

open GlobalTheory.LatOrb

theorem stable_of_conj {O K : Type} [CommRing O] [Field K] [Algebra O K] {n : ℕ} (g : GL (Fin n) K)
    (γ : Matrix (Fin n) (Fin n) K)
    (h : matLat O ((g⁻¹ : GL (Fin n) K).val * γ * g.val) (stdLat O n) = stdLat O n) :
    ∀ v ∈ matLat O g.val (stdLat O n), γ *ᵥ v ∈ matLat O g.val (stdLat O n) := by
  intro v hv
  have e : γ * g.val = g.val * ((g⁻¹ : GL (Fin n) K).val * γ * g.val) := by
    rw [← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul]
  have h2 : matLat O γ (matLat O g.val (stdLat O n)) = matLat O g.val (stdLat O n) := by
    rw [← matLat_mul, e, matLat_mul, h]
  rw [← h2]
  exact (mem_matLat _ _ _).2 ⟨v, hv, rfl⟩

theorem orbit_main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E),
    (∀ x, cj w (cj w x) = x) → (∀ x, Valued.v (cj w x) = Valued.v x) →
    ∀ P₀ : (w.adicCompletionIntegers E)[X], IsCoprime P₀ (derivative P₀) →
    ∀ γ : UL n w, γ.1.val.charpoly = P₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) →
    ∀ g₁ g₂ : UL n w, g₁⁻¹ * γ * g₁ ∈ KL n w → g₂⁻¹ * γ * g₂ ∈ KL n w →
    ∃ t ∈ twCent (MonoidHom.id (UL n w)) γ, ∃ k ∈ KL n w, g₂ = t * g₁ * k := by
  intro E _ _ _ n w hcc hcv P₀ hcop γ hγ g₁ g₂ h₁ h₂
  haveI := GlobalTheory.HenselSquare.isAdicComplete_integers E w
  have hσO : ∀ a : w.adicCompletionIntegers E, ∃ b : w.adicCompletionIntegers E,
      cj w (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E) a) =
        algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E) b := by
    intro a
    refine ⟨⟨cj w a, ?_⟩, rfl⟩
    have ha := a.2
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at ha ⊢
    rw [hcv]; exact ha
  have hK : ∀ h : UL n w, h ∈ KL n w ↔ matLat (w.adicCompletionIntegers E) h.1.val
      (stdLat (w.adicCompletionIntegers E) n) = stdLat (w.adicCompletionIntegers E) n := by
    intro h
    exact (Subgroup.mem_subgroupOf).trans (GlobalTheory.T.mem_GLint_iff_matrixImage_standardLattice_eq (w.adicCompletionIntegers E) n h.1)
  have st : ∀ g : UL n w, g⁻¹ * γ * g ∈ KL n w → ∀ v ∈ matLat (w.adicCompletionIntegers E) g.1.val
      (stdLat (w.adicCompletionIntegers E) n), γ.1.val *ᵥ v ∈ matLat (w.adicCompletionIntegers E) g.1.val
      (stdLat (w.adicCompletionIntegers E) n) := by
    intro g hg
    have h := (hK _).1 hg
    have e : ((g⁻¹ * γ * g : UL n w).1.val) = (g.1⁻¹ : GLw n w).val * γ.1.val * g.1.val := by simp
    rw [e] at h
    exact stable_of_conj g.1 γ.1.val h
  obtain ⟨t, htU, htc, htM⟩ : ∃ t : GLw n w, t ∈ UL n w ∧ t * γ.1 = γ.1 * t ∧
      matLat (w.adicCompletionIntegers E) t.val (matLat (w.adicCompletionIntegers E) g₁.1.val
        (stdLat (w.adicCompletionIntegers E) n)) = matLat (w.adicCompletionIntegers E) g₂.1.val
        (stdLat (w.adicCompletionIntegers E) n) := by
    obtain ⟨p, hpu, hp⟩ := GlobalTheory.T.exists_unit_eq_of_stable_lattices n P₀ hcop γ.1.val hγ _ _ (GlobalTheory.T.isFullRankLattice_image_standardLattice_GL n g₁.1) (GlobalTheory.T.isFullRankLattice_image_standardLattice_GL n g₂.1) (st g₁ h₁) (st g₂ h₂)
    by_cases hs : IsSplitAt w
    · refine ⟨hpu.unit, by simp [UL, hs], ?_, hp.symm⟩
      ext : 1
      simp only [Units.val_mul, IsUnit.unit_spec]
      have e1 : aeval γ.1.val p * γ.1.val = aeval γ.1.val (p * X) := by rw [map_mul, aeval_X]
      have e2 : γ.1.val * aeval γ.1.val p = aeval γ.1.val (X * p) := by rw [map_mul, aeval_X]
      rw [e1, e2, mul_comm]
    · have hUL : ∀ h : UL n w, ((h.1.val).map (cj w))ᵀ * h.1.val = 1 := by
        intro h
        have := h.2
        simp only [UL, hs, if_false] at this
        simpa [UJ, cT] using this
      have sd : ∀ g : UL n w, SelfDual (w.adicCompletionIntegers E) (cj w)
          (matLat (w.adicCompletionIntegers E) g.1.val (stdLat (w.adicCompletionIntegers E) n)) :=
        fun g => GlobalTheory.T.isSelfDual_image_standardLattice_unitary (cj w) hcc hσO n _ (hUL g)
      have hc := GlobalTheory.T.matrixImage_adjoint_mul_eq_of_selfDual_lattices (cj w) hcc n (aeval γ.1.val p) hpu _ (sd g₁) (hp ▸ sd g₂)
      obtain ⟨t, ht1, htc, htM⟩ := GlobalTheory.T.exists_unitary_adjoin_lattice_image_eq n P₀ hcop γ.1.val hγ (cj w) hcc hσO (hUL γ) _ (GlobalTheory.T.isFullRankLattice_image_standardLattice_GL n g₁.1)
        (st g₁ h₁) p hpu hc
      have htu : IsUnit t := (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_left_inverse ht1)
      refine ⟨htu.unit, ?_, ?_, by rw [hp]; exact htM⟩
      · show _ ∈ UL n w
        simp only [UL, hs, if_false]
        show cT (cj w) _ * 1 * _ = 1
        simpa [cT] using ht1
      · ext : 1
        simpa using htc
  refine ⟨⟨t, htU⟩, ?_, (⟨t, htU⟩ * g₁)⁻¹ * g₂, ?_, by group⟩
  · show (⟨t, htU⟩ : UL n w) * γ = γ * (⟨t, htU⟩ : UL n w)
    exact Subtype.ext htc
  · rw [hK]
    have e : (((⟨t, htU⟩ : UL n w) * g₁)⁻¹ * g₂ : UL n w).1.val =
        (g₁.1⁻¹ : GLw n w).val * ((t⁻¹ : GLw n w).val * g₂.1.val) := by simp [mul_assoc]
    rw [e, matLat_mul, matLat_mul, ← htM, ← matLat_mul (a := ((t⁻¹ : GLw n w).val)), Units.inv_mul, matLat_one,
      ← matLat_mul, Units.inv_mul, matLat_one]

end GlobalTheory.BCT.OrbitT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberSheafEqSumLengthMulCycleStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersectionNumber_sheaf_eq_sum_length_mul_cycle : ∀ (κ : Type) [Field κ] (X : Scheme.{0}) [Algebra κ Γ(X, ⊤)], IsProjOver (strHom κ X) → ∀ (ι : Type) [Fintype ι] (P : ι → LB X), (∀ i, (P i).IsLB) → ∀ (F : X.Modules) [GlobalTheory.QCoh.IsFiniteQC F], GlobalTheory.QCoh.suppDim F ≤ (Fintype.card ι : ℕ) → ∀ S : Finset X, (∀ w ∈ GlobalTheory.QCoh.support F, topologicalKrullDim (closure ({w} : Set X)) = (Fintype.card ι : ℕ) → w ∈ S) → interNum κ F P = ∑ w ∈ S, ((Module.length (X.presheaf.stalk w) (F.presheaf.stalk w :)).toNat : ℤ) * interNumRed κ (⟨closure {w}, isClosed_closure⟩ : Closeds _) P := by
  first | exact @GlobalTheory.SheafCycle.interNum_eq_sum_length_mul_interNumRed | exact GlobalTheory.SheafCycle.interNum_eq_sum_length_mul_interNumRed | (intros; apply GlobalTheory.SheafCycle.interNum_eq_sum_length_mul_interNumRed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantIntegralUnipotentCompactStatement
section
open ValuativeRel Matrix MeasureTheory
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GlobalTheory.GamMul DiscreteGroups.sglob.LConv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariant_integral_unipotent_compact : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] (N B K₀ : Subgroup G) (T : Set (G → ℂ)), (∀ F, F ∈ T ↔ (∀ u ∈ N, ∀ g, F (u * g) = F g) ∧ IsLocallyConstant F ∧ ∃ C : Set G, IsCompact C ∧ C ⊆ B ∧ ∀ g, F g ≠ 0 → ∃ u ∈ N, ∃ c ∈ C, g = u * c) → (∀ K : Subgroup G, K ≤ B → IsCompact (K : Set G) → IsOpen ((Subtype.val : B → G) ⁻¹' K) → IsClopen {g : G | ∃ u ∈ N, ∃ c ∈ K, g = u * c}) → (∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, K ≤ K₀ ∧ IsCompact (K : Set G) ∧ IsOpen ((Subtype.val : B → G) ⁻¹' K) ∧ (K : Set G) ⊆ U ∧ ∀ x ∈ K₀, ∀ y ∈ K, x * y * x⁻¹ ∈ K) → K₀ ≤ B → IsCompact (K₀ : Set G) → IsOpen ((Subtype.val : B → G) ⁻¹' K₀) → ∀ I : (G → ℂ) → ℂ, (∀ F ∈ T, ∀ F' ∈ T, ∀ c c' : ℂ, I (fun g => c * F g + c' * F' g) = c * I F + c' * I F') → (∀ F ∈ T, ∀ x ∈ B, I (fun g => F (g * x)) = I F) → I (Set.indicator {g : G | ∃ u ∈ N, ∃ c ∈ K₀, g = u * c} fun _ => (1 : ℂ)) = 0 → ∀ F ∈ T, I F = 0 := by
  first | exact @GlobalTheory.GamMul.Uniq.invariant_functional_eq_zero | exact GlobalTheory.GamMul.Uniq.invariant_functional_eq_zero | (intros; apply GlobalTheory.GamMul.Uniq.invariant_functional_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicMvPolynomialEvalAdjoinEtaleTowerCoord
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair.TowerTrdeg

theorem image_isAlgebraic : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (n r : ℕ) (R : Subring K) (T : Subring L)
    (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T) (x : Fin n → R),
  IsEtTower cK R cL T ι ψ τ → TrBasis cK (fun i => (x i : K)) →
  (letI := cL.toAlgebra; ∀ a : MvPolynomial (Fin r) R,
    IsAlgebraic (Algebra.adjoin ℂ (Set.range (Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L)))))
      ((MvPolynomial.eval₂Hom ι τ a : T) : L)) := by
  intro K L _ _ cK cL n r R T ι ψ τ x h hx
  letI := cL.toAlgebra
  intro a
  have hy : IsTranscendenceBasis ℂ (Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L))) :=
    trBasis_append cK cL n r R T ι ψ τ x h hx
  exact hy.isAlgebraic.isAlgebraic _

end GlobalTheory.FieldPair.TowerTrdeg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicOverMvPolynomialRangeEtaleTowerStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAlgebraic_over_mvPolynomial_range_etaleTower : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (r : ℕ) (R : Subring K) (T : Subring L)
    (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T),
  IsEtTower cK R cL T ι ψ τ → Function.Injective (MvPolynomial.eval₂Hom ι τ) →
  ∀ z : L, IsAlgebraic (T.subtype.comp (MvPolynomial.eval₂Hom ι τ)).range z := by
  first | exact @GlobalTheory.FieldPair.isAlgebraic_range_eval₂Hom_of_isEtTower | exact GlobalTheory.FieldPair.isAlgebraic_range_eval₂Hom_of_isEtTower | (intros; apply GlobalTheory.FieldPair.isAlgebraic_range_eval₂Hom_of_isEtTower <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBigLineBundlePullbackFieldExtensionIffStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isBigLineBundle_pullback_fieldExtension_iff : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (Y X : Scheme.{0}) (p : Y ⟶ Sp k) (q : X ⟶ Sp E) (π : X ⟶ Y), IsPullback π q p (spMap (algebraMap k E)) → IsProjOver p → IsProjOver q → topologicalKrullDim X = topologicalKrullDim Y → ∀ L : LB Y, L.IsLB → ((letI := algebraΓOfHom q; IsBig E (L.pull π)) ↔ (letI := algebraΓOfHom p; IsBig k L)) := by
  first | exact @GlobalTheory.BigFieldChange.isBig_pull_iff | exact GlobalTheory.BigFieldChange.isBig_pull_iff | (intros; apply GlobalTheory.BigFieldChange.isBig_pull_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBirationalModelIdAndCompStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isBirationalModel_id_and_comp : ∀ (X Y Z : Scheme.{0}) [IsIntegral X] [IsIntegral Y] [IsIntegral Z] (π : Y ⟶ X) (π' : Z ⟶ Y) (φ : X.functionField →+* Y.functionField) (φ' : Y.functionField →+* Z.functionField), IsModel (𝟙 X) (RingHom.id _) ∧ (IsModel π φ → IsModel π' φ' → IsModel (π' ≫ π) (φ'.comp φ)) := by
  first | exact @GlobalTheory.HSNef.isModel_id_and_comp | exact GlobalTheory.HSNef.isModel_id_and_comp | (intros; apply GlobalTheory.HSNef.isModel_id_and_comp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBirationalModelOfIsIsoOverNonemptyOpenStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isBirationalModel_of_isIso_over_nonempty_open : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (π : Y ⟶ X) (U : X.Opens), (U : Set X).Nonempty → IsIso (π ∣_ U) → ∃ φ : X.functionField →+* Y.functionField, IsModel π φ := by
  first | exact @GlobalTheory.HSNef.isModel_of_isIso_restrict | exact GlobalTheory.HSNef.isModel_of_isIso_restrict | (intros; apply GlobalTheory.HSNef.isModel_of_isIso_restrict <;> assumption)
end

