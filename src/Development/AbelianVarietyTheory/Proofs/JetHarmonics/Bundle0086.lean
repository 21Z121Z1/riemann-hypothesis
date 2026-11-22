import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.RealPlaceAnalysis.Bundle0003
import Formalism.RealPlaceAnalysis.Bundle0002
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0077
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0061
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0055
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0053
import Formalism.PeriodIntegrals.Bundle0015
import Formalism.PeriodIntegrals.Bundle0008
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0050
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0062
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0078
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0057
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0002
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiagonalTransferAction
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0076
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0047
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0052

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ProjectorEntryValueUnderLinearFunctional
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory
private theorem qminor_cast {M : Type} [AddCommGroup M] [Module ℂ M] {n a b : ℕ} (E : Fin n → Fin n → Module.End ℂ M)
    (h : a = b) (f g : Fin b → Fin n) (u : ℂ) :
    Formalism.REAL.qminor E (fun i : Fin a => f (Fin.cast h i)) (fun i : Fin a => g (Fin.cast h i)) u
      = Formalism.REAL.qminor E f g u := by
  subst h
  rfl
end GlobalTheory

namespace GlobalTheory

theorem capelli_projector_entry_value : ∀ (M Wp : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] [AddCommGroup Wp] [Module ℂ Wp] (k r : ℕ) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ M) (l : M →ₗ[ℂ] Wp) (p : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ) (τ : ℝ), 1 ≤ k → Formalism.REAL.GlRel E → (∀ a b : Fin (2 * r + k + 1), a < b → ¬ (r ≤ a.val ∧ b.val ≤ r + k) → (∀ v, l (E a b v) = p a b • l v) ∧ ‖p a b‖ = (if b.val = a.val + 1 ∧ (b.val < r ∨ r + k < a.val) then (1 : ℝ) else if (a.val + 1 = r ∧ b.val = r + k) ∨ (a.val = r + k ∧ b.val = r + k + 1) then τ else 0)) → ∀ (mu : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (Pop : Fin k → Fin k → Wp → Wp), Function.Injective mu → (∀ (Y : ℂ) (w : M), Formalism.REAL.qdet E (Y + ((((2 * r + k + 1) : ℕ) : ℂ) - 1) / 2) w = (∏ s, (Y + (mu s : ℂ))) • w) → (∀ i j v, l (E ((fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) i) ((fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) j) v) = Pop i j (l v)) → (∀ (w : ℂ) (x : Wp), Formalism.FourierDecayAlt.Q.qmF Pop id id w x = (∏ i ∈ Icc 1 k, (w - (k : ℂ) / 2 + 1 / 2 + (u i : ℂ))) • x) → ∀ s, ∃ c : ℂ, ‖c‖ = (if r = 0 then 1 else τ ^ 2) * ((∏ i ∈ Icc 1 k, |mu s - 1 / 2 - u i|) / ∏ t ∈ univ.erase s, |mu s - mu t|) ∧ ∀ (v : M) (y : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → M), (∀ t, splitCas E (y t) = ((-mu t + (1 - (((2 * r + k + 1) : ℕ) : ℝ)) / 2 : ℝ) : ℂ) • y t) → ∑ t, y t = Pi.single (Fin.last (2 * r + k)) v → l (y s (if r = 0 then Fin.last (2 * r + k) else 0)) = c • l v := by
  intro M Wp _ _ _ _ k r E l p τ hk hE hp mu u Pop hmu hq hP hW s
  set D : ℂ := ∏ t ∈ univ.erase s, ((mu t : ℂ) - mu s) with hD
  set N : ℂ := ∏ i ∈ Icc 1 k, (-(mu s : ℂ) + 1 / 2 + (u i : ℂ)) with hN
  have hDn : ‖D‖ = ∏ t ∈ univ.erase s, |mu s - mu t| := by
    rw [hD, norm_prod]
    refine Finset.prod_congr rfl fun t _ => ?_
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
  have hNn : ‖N‖ = ∏ i ∈ Icc 1 k, |mu s - 1 / 2 - u i| := by
    rw [hN, norm_prod]
    refine Finset.prod_congr rfl fun t _ => ?_
    have : (-(mu s : ℂ) + 1 / 2 + (u t : ℂ)) = ((-(mu s - 1 / 2 - u t) : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_neg]
  have hD0 : D ≠ 0 := by
    rw [hD, Finset.prod_ne_zero_iff]
    intro t ht h
    have h1 : mu t = mu s := by exact_mod_cast sub_eq_zero.mp h
    exact (Finset.mem_erase.mp ht).1 (hmu h1)
  have hinj : Function.Injective (fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) := by
    intro a b h
    have := congrArg Fin.val h
    simp only at this
    exact Fin.ext (by omega)
  have hblock : ∀ v, l (Formalism.REAL.qminor E (fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1)))
      (fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) (-(mu s : ℂ) + (k : ℂ) / 2) v) = N • l v := by
    intro v
    rw [GlobalTheory.T.quantumMinor_block_linearMap_intertwine M Wp _ k E l _ Pop hinj hP, hW, hN]
    congr 1
    refine Finset.prod_congr rfl fun t _ => ?_
    ring
  have hcof : ∀ (v : M) (y : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → M), (∀ t, splitCas E (y t) = ((-mu t + (1 - (((2 * r + k + 1) : ℕ) : ℝ)) / 2 : ℝ) : ℂ) • y t) → ∑ t, y t = Pi.single (Fin.last (2 * r + k)) v → ∀ i : Fin (2 * r + k + 1),
      D • l (y s i) = ((-1 : ℂ) ^ (i.val + (2 * r + k))) • l (Formalism.REAL.qminor E (Fin.succAbove (Fin.last (2 * r + k))) (Fin.succAbove i) (-(mu s : ℂ) + ((2 * r + k : ℕ) : ℂ) / 2) v) := by
    intro v y hy hs i
    have h := GlobalTheory.T.capelliComatrix_picks_splitCasimir_eigencomponent M (2 * r + k) E mu y hE hq hy s i
    have hj : ∀ j, ∑ t, y t j = (Pi.single (Fin.last (2 * r + k)) v : Fin (2 * r + k + 1) → M) j := by
      intro j
      rw [← hs, Finset.sum_apply]
    rw [Finset.sum_eq_single (Fin.last (2 * r + k))] at h
    · rw [hj, Pi.single_eq_same] at h
      rw [← map_smul, ← map_smul, hD, ← h]
      rfl
    · intro j _ hne
      rw [hj, Pi.single_eq_of_ne hne]
      simp
    · simp
  by_cases hr : r = 0
  · refine ⟨D⁻¹ * N, ?_, ?_⟩
    · rw [norm_mul, norm_inv, hDn, hNn, if_pos hr]; ring
    · intro v y hy hs
      rw [if_pos hr]
      have h := hcof v y hy hs (Fin.last _)
      subst hr
      have hm : Formalism.REAL.qminor E (Fin.succAbove (Fin.last (2 * 0 + k))) (Fin.succAbove (Fin.last (2 * 0 + k))) (-(mu s : ℂ) + ((2 * 0 + k : ℕ) : ℂ) / 2) = Formalism.REAL.qminor E (fun i : Fin k => (⟨0 + i.val, by omega⟩ : Fin (2 * 0 + k + 1)))
          (fun i : Fin k => (⟨0 + i.val, by omega⟩ : Fin (2 * 0 + k + 1))) (-(mu s : ℂ) + (k : ℂ) / 2) := by
        have := qminor_cast E (show k = 2 * 0 + k by omega) (Fin.succAbove (Fin.last (2 * 0 + k))) (Fin.succAbove (Fin.last (2 * 0 + k))) (-(mu s : ℂ) + (k : ℂ) / 2)
        have e : (fun i : Fin k => (⟨0 + i.val, by omega⟩ : Fin (2 * 0 + k + 1))) = fun i => Fin.succAbove (Fin.last (2 * 0 + k)) (Fin.cast (show k = 2 * 0 + k by omega) i) := by
          funext i
          apply Fin.ext
          simp
        rw [e, this]
        simp
      rw [hm, hblock] at h
      have hs1 : ((-1 : ℂ) ^ ((Fin.last (2 * 0 + k)).val + (2 * 0 + k))) = 1 := by
        rw [Fin.val_last, ← two_mul, pow_mul]; simp
      rw [hs1, one_smul] at h
      rw [mul_smul, ← h, smul_smul, inv_mul_cancel₀ hD0, one_smul]
  · have hr1 : 1 ≤ r := by omega
    obtain ⟨c1, hc1, h1⟩ := GlobalTheory.T.glRelation_row_steps_functional_eigen M Wp k r E l p τ hk hE hp hr1
    obtain ⟨c2, hc2, h2⟩ := GlobalTheory.T.besselColumnSteps_functional_eigen M Wp k r E l p τ hk hE hp hr1
    refine ⟨D⁻¹ * ((-1 : ℂ) ^ (2 * r + k) * (c1 * (c2 * N))), ?_, ?_⟩
    · rw [norm_mul, norm_inv, norm_mul, norm_mul, norm_mul, hDn, hNn, if_neg hr, hc1, hc2, norm_pow]
      simp only [norm_neg, norm_one, one_pow]
      ring
    · intro v y hy hs
      rw [if_neg hr]
      have h := hcof v y hy hs 0
      have e : (-(mu s : ℂ) + ((2 * r + k : ℕ) : ℂ) / 2) - (r : ℂ) = -(mu s : ℂ) + (k : ℂ) / 2 := by
        push_cast; ring
      rw [h1, h2, e, hblock, Fin.val_zero, zero_add] at h
      rw [mul_smul, mul_smul, mul_smul, mul_smul, ← h, smul_smul, inv_mul_cancel₀ hD0, one_smul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuotientMeasureIntegralRmulBesselGroup
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem quot_integral_rmul_of_measurable (hQ : PI.QuotInv) {m : ℕ} {G S : Set (Matrix (Fin m) (Fin m) ℂ)}
    {μG μS ν : Measure (PI.MtM m)} (h : PI.QuotientSetting G S μG μS ν) (F : PI.MtM m → ℂ) (hF : Measurable F)
    (hinv : ∀ s ∈ S, ∀ x : PI.MtM m, Matrix.of x ∈ G → F (fun i j => (s * Matrix.of x) i j) = F x)
    {g : Matrix (Fin m) (Fin m) ℂ} (hg : g ∈ G) :
    ∫ x, F (fun i j => (Matrix.of x * g) i j) ∂ν = ∫ x, F x ∂ν := by
  have hc : Continuous (fun x : PI.MtM m => (fun i j => (Matrix.of x * g) i j : PI.MtM m)) := by
    have h1 : Continuous (fun x : PI.MtM m => (Matrix.of x : Matrix (Fin m) (Fin m) ℂ)) := continuous_id
    exact h1.matrix_mul continuous_const
  have hF' : Measurable (fun x : PI.MtM m => F (fun i j => (Matrix.of x * g) i j)) := hF.comp hc.measurable
  have hmap : ν.map (fun x : PI.MtM m => F (fun i j => (Matrix.of x * g) i j)) = ν.map F := by
    ext A hA
    rw [Measure.map_apply hF' hA, Measure.map_apply hF hA, ← lintegral_indicator_one (hF' hA),
      ← lintegral_indicator_one (hF hA)]
    have key := hQ m G S μG μS ν h (fun x => A.indicator (1 : ℂ → ℝ≥0∞) (F x))
      ((measurable_one.indicator hA).comp hF) (fun s hs x hx => by simp only [hinv s hs x hx]) g hg
    exact key
  have e1 := integral_map (μ := ν) hF'.aemeasurable (f := fun y : ℂ => y) aestronglyMeasurable_id
  have e2 := integral_map (μ := ν) hF.aemeasurable (f := fun y : ℂ => y) aestronglyMeasurable_id
  rw [← e1, ← e2, hmap]

theorem quot_integral_rmul : ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (F : Mx k r → ℂ), SideG k r z π u μW μN μG νq → ContinuousOn F (GG k r) → (∀ s ∈ Formalism.QuantumDeterminants.Sset k r z, ∀ x ∈ GG k r, F (s * x) = F x) → Integrable (fun x : Formalism.QuantumDeterminants.Mt k r => F (Matrix.of x)) νq → ∀ g ∈ GG k r, ∫ x, F ((Matrix.of x) * g) ∂νq = ∫ x, F (Matrix.of x) ∂νq := by
  classical
  intro k r Wp _ _ _ _ z π u μW μN μG νq F hS hF hinv _ g hg
  obtain ⟨hz, hT, -, -, hW, hN, hG, hq⟩ := hS
  obtain ⟨hGG, hGH⟩ := GlobalTheory.T.isMatGroup_GG_and_haar_right_invariant k r
  obtain ⟨hGH1, hGH2⟩ := hGH μG hG
  obtain ⟨hSG, hsub, hS1, hS2⟩ := GlobalTheory.T.besselSubgroup_product_measure_isHaar k r z μW μN hz hT hW hN
  have hset : PI.QuotientSetting (GG k r) (Formalism.QuantumDeterminants.Sset k r z) μG (muSof μW μN) νq :=
    ⟨hGG, hSG, hsub, hGH1, hS1, hGH2, hS2, hq⟩
  obtain ⟨h0, h1⟩ := Formalism.FourierDecayAlt.P.DDSmoothness.muSof_facts hW hN
  have hae := Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot hG.2.2.1 h0 h1 hq
  set A : Set (Formalism.QuantumDeterminants.Mt k r) := {x | Matrix.of x ∈ GG k r} with hA
  have hAm : MeasurableSet A := by
    have := (Formalism.FourierDecayAlt.P.DDSmoothness.uh_measurableSet (k := k) (r := r)).compl
    convert this using 1
    ext x
    simp [hA]
  have hc : ContinuousOn (fun x : Formalism.QuantumDeterminants.Mt k r => F (Matrix.of x)) A := hF
  have hm : Measurable (A.piecewise (fun x : Formalism.QuantumDeterminants.Mt k r => F (Matrix.of x)) (fun _ => 0)) :=
    hc.measurable_piecewise continuousOn_const hAm
  have hval : ∀ x : Formalism.QuantumDeterminants.Mt k r, Matrix.of x ∈ GG k r →
      A.piecewise (fun x : Formalism.QuantumDeterminants.Mt k r => F (Matrix.of x)) (fun _ => 0) x = F (Matrix.of x) :=
    fun x hx => Set.piecewise_eq_of_mem _ _ _ hx
  have key := quot_integral_rmul_of_measurable GlobalTheory.T.quotientMeasure_right_invariant hset _ hm (fun s hs x hx => by
    rw [hval x hx]
    exact (hval (fun i j => (s * Matrix.of x) i j) (hGG.2.2.1 s (hsub hs) _ hx)).trans (hinv s hs _ hx)) hg
  calc ∫ x, F ((Matrix.of x) * g) ∂νq
      = ∫ x, A.piecewise (fun x : Formalism.QuantumDeterminants.Mt k r => F (Matrix.of x)) (fun _ => 0)
          (fun i j => (Matrix.of x * g) i j) ∂νq := by
        refine integral_congr_ae (hae.mono fun x hx => ?_)
        exact (hval (fun i j => (Matrix.of x * g) i j) (hGG.2.2.1 _ hx g hg)).symm
    _ = ∫ x, A.piecewise (fun x : Formalism.QuantumDeterminants.Mt k r => F (Matrix.of x)) (fun _ => 0) x ∂νq := key
    _ = ∫ x, F (Matrix.of x) ∂νq := integral_congr_ae (hae.mono fun x hx => hval x hx)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RadialPairConstantsPointwiseAdjointBounded
section
open scoped ComplexOrder InnerProductSpace

namespace GlobalTheory.HatNF

section abstract

variable {V E ι : Type} [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem ev_symm_of_nonneg (ev : V →ₗ[ℂ] E) (T : Module.End ℂ V) (h : ∀ v, 0 ≤ ⟪ev v, ev (T v)⟫_ℂ) (v w : V) :
    ⟪ev w, ev (T v)⟫_ℂ = ⟪ev (T w), ev v⟫_ℂ := by
  have hd : ∀ u, ⟪ev u, ev (T u)⟫_ℂ = ⟪ev (T u), ev u⟫_ℂ := by
    intro u
    rw [← inner_conj_symm (ev (T u)) (ev u)]
    exact (Complex.conj_eq_iff_im.mpr (Complex.nonneg_iff.mp (h u)).2.symm).symm
  have h1 := hd (v + w)
  have h2 := hd (v + Complex.I • w)
  have h3 := hd v
  have h4 := hd w
  simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    Complex.conj_I] at h1 h2
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination (1 / 2 : ℂ) * h1 + (Complex.I / 2) * h2 - (1 / 2 + Complex.I / 2) * h3
    - (1 / 2 + Complex.I / 2 * (-Complex.I * Complex.I)) * h4
    + (1 / 2 : ℂ) * (⟪ev w, ev (T v)⟫_ℂ - ⟪ev (T w), ev v⟫_ℂ - ⟪ev v, ev (T w)⟫_ℂ + ⟪ev (T v), ev w⟫_ℂ) * hI

variable [Fintype ι] [DecidableEq ι]

theorem ev_symm_single (ev : V →ₗ[ℂ] E) (K : (ι → ℂ) →ₐ[ℂ] Module.End ℂ V)
    (h : ∀ f : ι → ℂ, (∀ i, 0 < f i) → ∀ v, 0 ≤ ⟪ev v, ev (K f v)⟫_ℂ) (i : ι) (v w : V) :
    ⟪ev w, ev (K (Pi.single i 1) v)⟫_ℂ = ⟪ev (K (Pi.single i 1) w), ev v⟫_ℂ := by
  have hp : ∀ j, (0 : ℂ) < ((Pi.single i 1 : ι → ℂ) + 1) j := by
    intro j
    by_cases hj : j = i
    · subst hj
      simpa using add_pos (zero_lt_one' ℂ) (zero_lt_one' ℂ)
    · simp [hj]
  have h1 := ev_symm_of_nonneg ev _ (h _ hp) v w
  simp only [map_add, map_one, LinearMap.add_apply, Module.End.one_apply, inner_add_left, inner_add_right] at h1
  linear_combination h1

theorem algHom_apply_eq_sum (ev : V →ₗ[ℂ] E) (K : (ι → ℂ) →ₐ[ℂ] Module.End ℂ V) (f : ι → ℂ) (v : V) :
    ev (K f v) = ∑ i, f i • ev (K (Pi.single i 1) v) := by
  have hf : f = ∑ i, f i • (Pi.single i 1 : ι → ℂ) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hf]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]

theorem ev_adj (ev : V →ₗ[ℂ] E) (K : (ι → ℂ) →ₐ[ℂ] Module.End ℂ V)
    (h : ∀ f : ι → ℂ, (∀ i, 0 < f i) → ∀ v, 0 ≤ ⟪ev v, ev (K f v)⟫_ℂ) (f : ι → ℂ) (v w : V) :
    ⟪ev w, ev (K f v)⟫_ℂ = ⟪ev (K (fun i => star (f i)) w), ev v⟫_ℂ := by
  rw [algHom_apply_eq_sum, algHom_apply_eq_sum ev K (fun i => star (f i)), inner_sum, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_right, inner_smul_left, ev_symm_single ev K h]
  simp

theorem ev_single_le (ev : V →ₗ[ℂ] E) (K : (ι → ℂ) →ₐ[ℂ] Module.End ℂ V)
    (h : ∀ f : ι → ℂ, (∀ i, 0 < f i) → ∀ v, 0 ≤ ⟪ev v, ev (K f v)⟫_ℂ) (i : ι) (v : V) :
    ‖ev (K (Pi.single i 1) v)‖ ≤ ‖ev v‖ := by
  have hid : K (Pi.single i 1) (K (Pi.single i 1) v) = K (Pi.single i 1) v := by
    rw [← Module.End.mul_apply, ← map_mul, ← Pi.single_mul, mul_one]
  have h1 := ev_symm_single ev K h i v (K (Pi.single i 1) v)
  rw [hid] at h1
  set a := ev (K (Pi.single i 1) v)
  have h2 : ‖a‖ * ‖a‖ ≤ ‖a‖ * ‖ev v‖ := by
    calc ‖a‖ * ‖a‖ = ‖⟪a, a⟫_ℂ‖ := by
          rw [inner_self_eq_norm_sq_to_K]
          simp [sq]
      _ = ‖⟪a, ev v⟫_ℂ‖ := by rw [h1]
      _ ≤ _ := norm_inner_le_norm _ _
  rcases (norm_nonneg a).eq_or_lt with h0 | h0
  · rw [← h0]
    exact norm_nonneg _
  · exact le_of_mul_le_mul_left h2 h0

theorem ev_le (ev : V →ₗ[ℂ] E) (K : (ι → ℂ) →ₐ[ℂ] Module.End ℂ V)
    (h : ∀ f : ι → ℂ, (∀ i, 0 < f i) → ∀ v, 0 ≤ ⟪ev v, ev (K f v)⟫_ℂ) (f : ι → ℂ) (v : V) :
    ‖ev (K f v)‖ ≤ (∑ i, ‖f i‖) * ‖ev v‖ := by
  rw [algHom_apply_eq_sum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (ev_single_le ev K h i v) (norm_nonneg _)

end abstract

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory

theorem kappa_ptAdj_ptB : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ f : M.Ty P → ℂ, PtAdj P Bs (d.κ f) ∧ PtB P Bs (d.κ f) := by
  intro Wp Wq _ _ _ _ _ _ P Bs X μ L st l0 d hD hN f
  classical
  let ev : (Fin P.r → ℂ) × Q.Mx P.k P.r →
      Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' →ₗ[ℂ] PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp) := fun x =>
    { toFun := fun Φ => B.hsVec ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let K : (M.Ty P → ℂ) →ₐ[ℂ] Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :=
    (P5.Kfp.fstAlg _).comp d.κ
  have hpos : ∀ x, ∀ g : M.Ty P → ℂ, (∀ i, 0 < g i) → ∀ v, 0 ≤ ⟪ev x v, ev x (K g v)⟫_ℂ := fun x g hg v =>
    P5.kappaFibrePos Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hD.1 X d hN.1 hN.2.1 hN.2.2.1 hN.2.2.2 g hg v x.1 x.2
  refine ⟨fun Φ Ψ x _ => ?_, ∑ i, ‖f i‖, Finset.sum_nonneg fun _ _ => norm_nonneg _, fun Φ x _ => ?_⟩
  · rw [hN.2.2.1.1 f]
    exact ev_adj (ev x) K (hpos x) f Φ Ψ
  · exact ev_le (ev x) K (hpos x) f Φ

end GlobalTheory.HatNF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorDecompositionInjectiveParameters
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.TensOrth

variable {k r : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [DecidableEq ι] in
theorem hh_smul (Γ : Matrix ι ι ℂ) (R : Rep k r) (a b : ℂ) (x y : ι → R.H) :
    hh Γ R (fun c => a • x c) (fun c => b • y c) = a * star b * hh Γ R x y := by
  simp only [hh, inner_smul_left, inner_smul_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [RCLike.star_def]
  ring

omit [DecidableEq ι] [DecidableEq κ] in
theorem hh_sum_right (Γ : Matrix ι ι ℂ) (R : Rep k r) (x : ι → R.H) (y : κ → ι → R.H) :
    hh Γ R x (fun c => ∑ J, y J c) = ∑ J, hh Γ R x (y J) := by
  simp only [hh, sum_inner, Finset.mul_sum]
  rw [Finset.sum_comm (s := (univ : Finset κ))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

omit [DecidableEq ι] in
theorem hh_star (Γ : Matrix ι ι ℂ) (hΓ : Γᴴ = Γ) (R : Rep k r) (x y : ι → R.H) :
    star (hh Γ R x y) = hh Γ R y x := by
  simp only [hh, star_sum, star_mul']
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h : star (Γ j i) = Γ i j := by
    have := congrFun (congrFun hΓ i) j
    simpa [Matrix.conjTranspose_apply] using this
  rw [h]
  congr 1
  exact inner_conj_symm _ _

theorem eq_zero_of_hh (Γ : Matrix ι ι ℂ) (hΓ : Γ * Γ = 1) (R : Rep k r) (x : ι → R.H)
    (h : hh Γ R x (fun c => ∑ j, Γ c j • x j) = 0) (c : ι) : x c = 0 := by
  set z : ι → R.H := fun c => ∑ j, Γ c j • x j with hz
  have h1 : hh Γ R x z = ((∑ i, ‖z i‖ ^ 2 : ℝ) : ℂ) := by
    unfold hh
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    have : ⟪z i, z i⟫_ℂ = ∑ j, Γ i j * ⟪z i, x j⟫_ℂ := by
      conv_lhs => enter [3]; rw [hz]
      simp only [inner_sum, inner_smul_right]
    rw [← this, inner_self_eq_norm_sq_to_K]
    rfl
  rw [h1, Complex.ofReal_eq_zero] at h
  have h2 : ∀ i, z i = 0 := fun i => by
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖z i‖)).1 h i (mem_univ _)
    simpa using this
  have h3 : ∑ i, Γ c i • z i = x c := by
    simp only [hz, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, ← Matrix.mul_apply, hΓ, Matrix.one_apply]
    simp
  rw [← h3]
  simp [h2]

theorem SmMap_zero {R R' : Rep k r} {T : R.H → R'.H} (hT : SmMap R R' T) : T 0 = 0 := by
  have := hT.smul 0 0 R.smSub.zero_mem
  simpa using this

omit [DecidableEq ι] [DecidableEq κ] in
theorem raw_scale {ρ : Mx k r → Matrix ι ι ℂ} {R : Rep k r} {RI : κ → Rep k r}
    {io : ∀ I, ι → (RI I).H → R.H} {pr : ∀ I, ι → R.H → (RI I).H} (h : TensRaw ρ R RI io pr)
    (a : κ → ℂ) (ha : ∀ I, a I ≠ 0)
    (h1 : ∀ I c, SmMap (RI I) R (fun v => a I • io I c v))
    (h2 : ∀ I c, SmMap R (RI I) (fun v => (a I)⁻¹ • pr I c v)) :
    TensRaw ρ R RI (fun I c v => a I • io I c v) (fun I c v => (a I)⁻¹ • pr I c v) where
  io_sm := h1
  pr_sm := h2
  io_eq := fun I g hg y hy => by
    funext c
    have := congrFun (h.io_eq I g hg y hy) c
    simp only [act] at this ⊢
    rw [this, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_comm]
  pr_eq := fun I g hg x hx => by
    rw [← Finset.smul_sum, ← Finset.smul_sum, map_smul, h.pr_eq I g hg x hx]
  sum_io_pr := fun x hx c => by
    rw [← h.sum_io_pr x hx c]
    refine Finset.sum_congr rfl fun I _ => ?_
    have hm : ∑ d, pr I d (x d) ∈ (RI I).smSub :=
      Submodule.sum_mem _ fun d _ => (h.pr_sm I d).mem _ (hx d)
    rw [← Finset.smul_sum, (h.io_sm I c).smul _ _ hm, smul_smul, mul_inv_cancel₀ (ha I), one_smul]
  pr_io := fun I y hy => by
    conv_rhs => rw [← h.pr_io I y hy]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [(h.pr_sm I c).smul _ _ ((h.io_sm I c).mem _ hy), smul_smul, inv_mul_cancel₀ (ha I), one_smul]
  pr_io_ne := fun I J hIJ y hy => by
    have : ∀ c, (a I)⁻¹ • pr I c (a J • io J c y) = ((a I)⁻¹ * a J) • pr I c (io J c y) := fun c => by
      rw [(h.pr_sm I c).smul _ _ ((h.io_sm J c).mem _ hy), smul_smul]
    simp only [this]
    rw [← Finset.smul_sum, h.pr_io_ne I J hIJ y hy, smul_zero]

theorem tensH_of_raw : Hyps → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ), R.IsDS ε mu → (∀ I, (RI I).IsDS ε (muI I)) → Function.Injective muI → IsFRep ρ Γ d → TensRaw ρ R RI io pr → ∃ io' pr' ep, TensH ρ Γ R RI io' pr' ep := by
  intro hH k r ι κ _ _ _ _ ρ Γ d R RI io pr ε mu muI hR hRI hinj hF hT
  have hK : PI.KFinSmooth := hH.1.2.2.1
  have hP : Poulsen := hH.2.2.2.2.2.1
  have hform := GlobalTheory.TensForm.pulledBack_isInvForm hK k r ι κ ρ Γ d R RI io pr ε mu muI hR hRI hF hT
  have horth : ∀ I J, I ≠ J → ∀ y ∈ (RI I).sm, ∀ y' ∈ (RI J).sm,
      hh Γ R (fun c => io I c y) (fun c => io J c y') = 0 := by
    intro I J hIJ
    rcases (hP k r ε _ _ _ _ (hRI I) (hRI J)).2 _ (hform I J) with h | ⟨U, hU⟩
    · exact h
    · exact absurd (hinj (GlobalTheory.DSInequiv.param_eq_of_equiv hH k r ε _ _ _ _ (hRI I) (hRI J) U hU)) hIJ
  choose cI hc using fun I => (hP k r ε _ _ _ _ (hRI I) (hRI I)).1 _ (hform I I)
  have hunit : ∀ I, ∃ w ∈ (RI I).sm, ‖w‖ = 1 := fun I => by
    obtain ⟨-, -, -, -, h5, -, h7, ⟨w, hw, hwK, -⟩, -⟩ := GlobalTheory.T.discreteSeries_unitary_smooth_basic hK k r ε _ _ (hRI I)
    exact ⟨w, h5 w (h7 w hwK), hw⟩
  have hreal : ∀ I, ((cI I).re : ℂ) = cI I := fun I => by
    obtain ⟨w, hw, hn⟩ := hunit I
    have h1 := hc I w hw w hw
    have h2 := hh_star Γ hF.1 R (fun c => io I c w) (fun c => io I c w)
    rw [inner_self_eq_norm_sq_to_K, hn] at h1
    simp only [map_one, one_pow, mul_one] at h1
    rw [h1] at h2
    exact Complex.conj_eq_iff_re.1 h2
  have hne : ∀ I, cI I ≠ 0 := fun I h0 => by
    obtain ⟨w, hw, hn⟩ := hunit I
    have hx : ∀ c, (∑ j, Γ c j • io I j w) ∈ R.smSub := fun c =>
      Submodule.sum_mem _ fun j _ => R.smSub.smul_mem _ ((hT.io_sm I j).mem _ hw)
    have hz : hh Γ R (fun c => io I c w) (fun c => ∑ j, Γ c j • io I j w) = 0 := by
      have e : (fun c => ∑ j, Γ c j • io I j w) =
          fun c => ∑ J, io J c (∑ e, pr J e (∑ j, Γ e j • io I j w)) :=
        funext fun c => (hT.sum_io_pr _ hx c).symm
      rw [e, hh_sum_right]
      refine Finset.sum_eq_zero fun J _ => ?_
      have hm : ∑ e, pr J e (∑ j, Γ e j • io I j w) ∈ (RI J).smSub :=
        Submodule.sum_mem _ fun e _ => (hT.pr_sm J e).mem _ (hx e)
      by_cases hIJ : I = J
      · subst hIJ
        have := hc I w hw _ hm
        rw [h0, zero_mul] at this
        exact this
      · exact horth I J hIJ w hw _ hm
    have h0' := eq_zero_of_hh Γ hF.2.1 R _ hz
    have h1 := hT.pr_io I w hw
    simp only [h0', SmMap_zero (hT.pr_sm I _), Finset.sum_const_zero] at h1
    rw [← h1, norm_zero] at hn
    exact zero_ne_one hn
  have hre : ∀ I, (cI I).re ≠ 0 := fun I h => hne I (by rw [← hreal I, h]; simp)
  have hsc : ∀ (m m' : Fin (2 * r + k + 1) → ℝ) (S S' : Rep k r), S.IsDS ε m → S'.IsDS ε m' →
      ∀ (T : S.H → S'.H) (a : ℂ), SmMap S S' T → SmMap S S' (fun v => a • T v) := by
    intro m m' S S' hS hS' T a h
    have := (GlobalTheory.T.smooth_maps_closure hK k r ε _ _ _ S S' S' hS hS' hS').2.2.1 T T (a - 1) h h
    simpa only [sub_smul, one_smul, sub_add_cancel] using this
  set a : κ → ℂ := fun I => (((Real.sqrt |(cI I).re|)⁻¹ : ℝ) : ℂ) with ha
  have hane : ∀ I, a I ≠ 0 := fun I => by
    simp only [ha, ne_eq, Complex.ofReal_eq_zero, inv_eq_zero]
    exact (Real.sqrt_pos.2 (abs_pos.2 (hre I))).ne'
  refine ⟨fun I c v => a I • io I c v, fun I c v => (a I)⁻¹ • pr I c v,
    fun I => (cI I).re / |(cI I).re|, ⟨raw_scale hT a hane
      (fun I c => hsc _ _ _ _ (hRI I) hR _ _ (hT.io_sm I c))
      (fun I c => hsc _ _ _ _ hR (hRI I) _ _ (hT.pr_sm I c)), fun I => ?_, fun I y hy y' hy' => ?_,
      fun I J hIJ y hy y' hy' => ?_⟩⟩
  · rcases lt_or_gt_of_ne (hre I) with h | h
    · right
      rw [abs_of_neg h, div_neg, div_self (hre I)]
    · left
      rw [abs_of_pos h, div_self (hre I)]
  · have h1 := hc I y hy y' hy'
    rw [hh_smul, h1, ← mul_assoc]
    congr 1
    have h2 : (Real.sqrt |(cI I).re|)⁻¹ * (Real.sqrt |(cI I).re|)⁻¹ * (cI I).re = (cI I).re / |(cI I).re| := by
      rw [← mul_inv, Real.mul_self_sqrt (abs_nonneg _), div_eq_inv_mul]
    rw [← h2]
    simp only [ha, RCLike.star_def, Complex.conj_ofReal]
    rw [Complex.ofReal_mul, Complex.ofReal_mul, hreal I]
  · rw [hh_smul, horth I J hIJ y hy y' hy', mul_zero]

end GlobalTheory.TensOrth
end
end

