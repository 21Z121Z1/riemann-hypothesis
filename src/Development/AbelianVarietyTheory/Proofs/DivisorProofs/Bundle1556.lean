import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0229
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0239
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0328
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0301
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1485
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0222
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0238
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1465
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1468
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1493
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1517
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1528
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralCompactLe
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1445
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1469
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1503
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0056
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0166
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0031
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0129
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelFamilyTangentDimensionBound
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPointPrimitiveBundleEqTranslatePpav
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1533
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1320

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerIntertwinerL2Constant
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory GlobalTheory.RealWeil
open scoped Matrix ENNReal SchwartzMap

namespace GlobalTheory.SvNForm

theorem sympl_neg_self {n : ℕ} (w : Fin n ⊕ Fin n → ℝ) : sympl w (-w) = 0 := by
  have h1 : pPart (-w) = -pPart w := rfl
  have h2 : qPart (-w) = -qPart w := rfl
  simp only [sympl, h1, h2, inner_neg_right, real_inner_comm (pPart w) (qPart w)]
  ring

theorem rhoFun_neg_cancel {n : ℕ} (w : Fin n ⊕ Fin n → ℝ) (u : EuclideanSpace ℝ (Fin n) → ℂ) :
    rhoFun w (rhoFun (-w) u) = u := by
  rw [rhoFun_rhoFun, sympl_neg_self, add_neg_cancel, rhoFun_zero]
  simp

theorem step (n : ℕ) (B : Sch (Fin n) → Sch (Fin n) → ℂ)
    (hB : ∀ h', ∃ L : Sch (Fin n) →L[ℂ] ℂ, ∀ h, B h h' = L h)
    (f f' g g' : Sch (Fin n)) (G : (Fin n ⊕ Fin n → ℝ) → Sch (Fin n)) (hGc : Continuous G)
    (hG : ∀ w, ⇑(G w) = rhoFun w ⇑f)
    (hGb : ∀ k m : ℕ, ∃ (C : ℝ) (N : ℕ), ∀ w, SchwartzMap.seminorm ℂ k m (G w) ≤ C * (1 + ‖w‖) ^ N) :
    (∫ x, f x * starRingEnd ℂ (g x)) * B g' f' =
      ∫ w, starRingEnd ℂ (∫ t, rhoFun w ⇑g t * starRingEnd ℂ (g' t)) * B (G w) f' := by
  obtain ⟨L, hL⟩ := hB f'
  set ip : ℂ := ∫ x, f x * starRingEnd ℂ (g x) with hip
  set c : (Fin n ⊕ Fin n → ℝ) → ℂ := fun w => starRingEnd ℂ (∫ t, rhoFun w ⇑g t * starRingEnd ℂ (g' t)) with hc
  have hcc : Continuous c := Complex.continuous_conj.comp (GlobalTheory.T.matrix_coeff_continuous_rapid_decay n g g').1
  have hint : ∀ k m : ℕ, Integrable (fun w => ‖c w‖ * SchwartzMap.seminorm ℂ k m (G w)) := by
    intro k m
    obtain ⟨C, N, hC⟩ := hGb k m
    set d : ℕ := Module.finrank ℝ (Fin n ⊕ Fin n → ℝ)
    obtain ⟨C', hC'⟩ := (GlobalTheory.T.matrix_coeff_continuous_rapid_decay n g g').2 (N + (d + 1))
    have hsc : Continuous fun w => SchwartzMap.seminorm ℂ k m (G w) :=
      ((schwartz_withSeminorms ℂ (EuclideanSpace ℝ (Fin n)) ℂ).continuous_seminorm (k, m)).comp hGc
    have hI : Integrable (fun w : Fin n ⊕ Fin n → ℝ => (1 + ‖w‖) ^ (-((d + 1 : ℕ) : ℝ))) :=
      integrable_one_add_norm (by push_cast; linarith)
    refine (hI.const_mul (C' * |C|)).mono' ((hcc.norm.mul hsc).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun w => ?_)
    have hpos : 0 < 1 + ‖w‖ := by positivity
    have e1 : ‖c w‖ = ‖∫ t, rhoFun w ⇑g t * starRingEnd ℂ (g' t)‖ := by simp [hc]
    have h1 := hC' w
    have h2 := hC w
    have hs0 : 0 ≤ SchwartzMap.seminorm ℂ k m (G w) := apply_nonneg _ _
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), abs_of_nonneg hs0, e1]
    have hrp : (1 + ‖w‖) ^ (-((d + 1 : ℕ) : ℝ)) = ((1 + ‖w‖) ^ (d + 1))⁻¹ := by
      rw [Real.rpow_neg hpos.le, Real.rpow_natCast]
    rw [hrp]
    set M := ‖∫ t, rhoFun w ⇑g t * starRingEnd ℂ (g' t)‖
    have hM : 0 ≤ M := norm_nonneg _
    have hA : (0:ℝ) < (1 + ‖w‖) ^ N := by positivity
    have hB' : (0:ℝ) < (1 + ‖w‖) ^ (d + 1) := by positivity
    have h3 : SchwartzMap.seminorm ℂ k m (G w) ≤ |C| * (1 + ‖w‖) ^ N :=
      h2.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hA.le)
    rw [pow_add] at h1
    calc M * SchwartzMap.seminorm ℂ k m (G w) ≤ M * (|C| * (1 + ‖w‖) ^ N) := mul_le_mul_of_nonneg_left h3 hM
      _ = |C| * (M * ((1 + ‖w‖) ^ N * (1 + ‖w‖) ^ (d + 1))) * ((1 + ‖w‖) ^ (d + 1))⁻¹ := by
          field_simp
      _ ≤ |C| * C' * ((1 + ‖w‖) ^ (d + 1))⁻¹ := by
          gcongr
      _ = C' * |C| * ((1 + ‖w‖) ^ (d + 1))⁻¹ := by ring
  have hpt : ∀ x, (ip • g') x = ∫ w, c w * G w x := by
    intro x
    simp only [SchwartzMap.smul_apply, smul_eq_mul, hc, hG]
    rw [GlobalTheory.T.schrodinger_orthogonality_relation n f g g' x]
  have key := GlobalTheory.T.schwartz_functional_integral_comm (Fin n ⊕ Fin n → ℝ) volume n L G c (ip • g') hGc hcc hint hpt
  calc ip * B g' f' = B (ip • g') f' := by rw [hL, hL, map_smul, smul_eq_mul]
    _ = ∫ w, c w * L (G w) := by rw [hL]; exact key
    _ = ∫ w, c w * B (G w) f' := by simp only [hL]

theorem core : ∀ (n : ℕ) (B : GlobalTheory.RealWeil.Sch (Fin n) → GlobalTheory.RealWeil.Sch (Fin n) → ℂ),
    (∀ h', ∃ L : GlobalTheory.RealWeil.Sch (Fin n) →L[ℂ] ℂ, ∀ h, B h h' = L h) →
    (∀ h h', B h' h = starRingEnd ℂ (B h h')) → (∀ h, 0 ≤ (B h h).re) →
    (∀ (w : Fin n ⊕ Fin n → ℝ) (h h' g g' : GlobalTheory.RealWeil.Sch (Fin n)), ⇑g = GlobalTheory.RealWeil.rhoFun w ⇑h →
      ⇑g' = GlobalTheory.RealWeil.rhoFun w ⇑h' → B g g' = B h h') →
    ∃ c : ℝ, 0 ≤ c ∧ ∀ h h', B h h' = c * ∫ x, h x * starRingEnd ℂ (h' x) := by
  intro n B hB hherm hpos hinv
  refine GlobalTheory.T.hermitian_form_const_mul_inner n B hherm hpos fun f f' g g' => ?_
  obtain ⟨G, hGc, hG, hGb⟩ := GlobalTheory.T.schrodinger_rep_schwartz_polynomial_bound n f
  obtain ⟨G', hG'c, hG', hG'b⟩ := GlobalTheory.T.schrodinger_rep_schwartz_polynomial_bound n f'
  have s1 := step n B hB f f' g g' G hGc hG hGb
  have s2 := step n B hB f' f g' g G' hG'c hG' hG'b
  set mc : Sch (Fin n) → Sch (Fin n) → (Fin n ⊕ Fin n → ℝ) → ℂ :=
    fun u v w => ∫ t, rhoFun w ⇑u t * starRingEnd ℂ (v t) with hmc
  have pw : ∀ w, starRingEnd ℂ (mc g g' w) * B (G w) f' = mc g' g (-w) * starRingEnd ℂ (B (G' (-w)) f) := by
    intro w
    have e1 : B (G w) f' = B f (G' (-w)) :=
      hinv w f (G' (-w)) (G w) f' (hG w) (by rw [hG' (-w), rhoFun_neg_cancel])
    have e2 : mc g g' w = ∫ t, g t * starRingEnd ℂ (rhoFun (-w) ⇑g' t) := by
      simp only [hmc]
      conv_lhs => rw [← rhoFun_neg_cancel w ⇑g']
      exact GlobalTheory.T.schrodinger_rep_unitary n w ⇑g (rhoFun (-w) ⇑g')
    rw [e1, hherm, e2, ← integral_conj]
    simp only [hmc, map_mul, Complex.conj_conj]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp [mul_comm]
  rw [s1]
  have e3 : (∫ x, g' x * starRingEnd ℂ (f' x)) * B f g =
      starRingEnd ℂ ((∫ x, f' x * starRingEnd ℂ (g' x)) * B g f) := by
    rw [map_mul, ← integral_conj, hherm g f]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp [mul_comm]
  simp only [hmc] at pw
  rw [e3, s2, ← integral_conj]
  simp only [pw]
  have hneg := integral_neg_eq_self (fun w => (∫ t, rhoFun w ⇑g' t * starRingEnd ℂ (g t)) *
    starRingEnd ℂ (B (G' w) f)) (volume : Measure (Fin n ⊕ Fin n → ℝ))
  rw [hneg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp [map_mul]

theorem schrodinger_intertwiner_l2_const : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : mixedEmbedding.mixedSpace F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (mixedEmbedding.mixedSpace F) ℂ),
    (∀ a, ψ a = Complex.exp (-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) a : ℝ))) →
    ∀ (T : SInf F κ →L[ℂ] SInf F κ)
      (A : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F) →
        (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)),
      (∀ w (f g : SInf F κ), (g : (κ → mixedEmbedding.mixedSpace F) → ℂ) = schr ψ w f →
        (T g : (κ → mixedEmbedding.mixedSpace F) → ℂ) = schr ψ (A w) (T f)) →
      ∃ c : ℝ, 0 ≤ c ∧ ∀ μ : @Measure (κ → mixedEmbedding.mixedSpace F) (borel _),
        @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∀ f f' : SInf F κ,
          @integral _ ℂ _ _ (borel _) μ (fun x => T f x * starRingEnd ℂ (T f' x)) =
            (c : ℂ) * @integral _ ℂ _ _ (borel _) μ (fun x => f x * starRingEnd ℂ (f' x)) := GlobalTheory.T.rho_invariant_form_const_mul_inner core

end GlobalTheory.SvNForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SobolevBoundPeriodicSchwartz
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix ENNReal
open scoped Classical
open GlobalTheory.ArchDecay

noncomputable section

namespace GlobalTheory.ArchDecay

theorem schA_line (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] : ∀ g ∈ schA F κ, Continuous g ∧
    ∀ (v : κ → mixedEmbedding.mixedSpace F) (x : κ → AF F) (t : ℝ),
      HasDerivAt (fun s : ℝ => g (x + fun i => infAd F (s • v i))) (dD F v g (x + fun i => infAd F (t • v i))) t :=
  GlobalTheory.T.adelicSchwartz_continuous_hasDerivAt_archimedeanLine F κ

theorem slice_le {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [μ.IsAddLeftInvariant] {N : ℕ} (ι : (Fin N → ℝ) →+ G) (π : G →+ (Fin N → ℝ))
    (hι : Continuous ι) (hπ : Continuous π) (hπι : ∀ t, π (ι t) = t) (U : Set G)
    (hU : MeasurableSet {w | w - ι (π w) ∈ U})
    (hfin : ∀ A : Set (Fin N → ℝ), IsCompact A → μ (π ⁻¹' A ∩ {w | w - ι (π w) ∈ U}) ≠ ⊤)
    (φ : G → ℝ≥0∞) (hφ : Measurable φ) (hper : ∀ w, ∀ u ∈ U, φ (w + u) = φ w) (y : G) :
    μ (π ⁻¹' cube N ∩ {w | w - ι (π w) ∈ U}) * ∫⁻ t in cube N, φ (y + ι t) ≤ ∫⁻ w, φ w ∂μ :=
  GlobalTheory.T.lintegral_unitCube_translates_slabPeriodic_le μ ι π hι hπ hπι U hU hfin φ hφ hper y

theorem slab_top (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    (∀ m : ℕ, 0 < m → IsOpen (slab F κ m)) ∧ ∀ (μ : @Measure (κ → AF F) (borel _)),
      @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → 0 < μ (archOut F κ ⁻¹' cube (dimA F κ) ∩ slab F κ 1) ∧
        ∀ A : Set (Fin (dimA F κ) → ℝ), IsCompact A → μ (archOut F κ ⁻¹' A ∩ slab F κ 1) ≠ ⊤ :=
  GlobalTheory.T.archimedeanSlab_open_unitCube_haar_pos_finite F κ

theorem slab_cover (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    ∃ c : ℕ, ∀ m : ℕ, 0 < m → slab F κ m ⊆ slab F κ 1 ∧ ∃ R : Finset (κ → AF F), R.card ≤ m ^ c ∧
      (∀ r ∈ R, arch F r = 0) ∧ ∀ w ∈ slab F κ 1, ∃ r ∈ R, w - r ∈ slab F κ m :=
  GlobalTheory.T.archimedeanSlab_covered_by_translates_of_smaller_slab F κ

end GlobalTheory.ArchDecay

namespace GlobalTheory.ArchDecay

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem wordD_cons (v : κ → mixedEmbedding.mixedSpace F) (w : List (κ → mixedEmbedding.mixedSpace F))
    (f : (κ → AF F) → ℂ) : wordD F (v :: w) f = dD F v (wordD F w f) := rfl

theorem per_dD {m : ℕ} {f : (κ → AF F) → ℂ} (h : Per F m f) (v : κ → mixedEmbedding.mixedSpace F) :
    Per F m (dD F v f) := by
  intro x z hz
  unfold dD
  congr 1
  funext t
  rw [add_right_comm]
  exact h _ z hz

theorem per_wordD {m : ℕ} {f : (κ → AF F) → ℂ} (h : Per F m f) (w : List (κ → mixedEmbedding.mixedSpace F)) :
    Per F m (wordD F w f) := by
  induction w with
  | nil => exact h
  | cons v w ih => rw [wordD_cons]; exact per_dD ih v

theorem wordD_mem {f : (κ → AF F) → ℂ} (hf : f ∈ schA F κ) (w : List (κ → mixedEmbedding.mixedSpace F)) :
    wordD F w f ∈ schA F κ := by
  induction w with
  | nil => exact hf
  | cons v w ih => rw [wordD_cons]; exact GlobalTheory.T.archimedeanDecayOperatorApply_mem_adelicSchwartz F κ (Sum.inl v) _ ih

theorem archIn_single (j : Fin (dimA F κ)) (s : ℝ) :
    archIn F κ (Pi.single j s) = fun i => infAd F (s • ubasis F κ j i) := by
  funext i
  rw [archIn_apply]
  congr 1
  rw [Module.Basis.equivFun_symm_apply, Fintype.sum_eq_single j (fun c hc => by simp [Pi.single_apply, hc])]
  simp

theorem sobolev_schA {f : (κ → AF F) → ℂ} (hf : f ∈ schA F κ) (x : κ → AF F) (B : ℝ)
    (hB : ∀ w : List (κ → mixedEmbedding.mixedSpace F), w.length ≤ dimA F κ → (∀ v ∈ w, ∃ j, v = ubasis F κ j) →
      ∫ t in cube (dimA F κ), ‖wordD F w f (x + archIn F κ t)‖ ^ 2 ≤ B) :
    ‖f x‖ ^ 2 ≤ 4 ^ dimA F κ * B := by
  let A : ℕ → Set ((κ → AF F) → ℂ) := fun p =>
    {u | ∃ w : List (κ → mixedEmbedding.mixedSpace F), w.length ≤ p ∧ (∀ v ∈ w, ∃ j, v = ubasis F κ j) ∧
      u = wordD F w f}
  have hA : Monotone A := fun p q hpq u ⟨w, h1, h2, h3⟩ => ⟨w, h1.trans hpq, h2, h3⟩
  have key := GlobalTheory.ThetaGrowth.sobolev_iter (dimA F κ) 0 (fun j s => archIn F κ (Pi.single j s)) A B x
    (fun j => (continuous_archIn F κ).comp (continuous_single (A := fun _ : Fin (dimA F κ) => ℝ) j)) hA ?_ ?_ f ⟨[], by simp, by simp, rfl⟩
  · exact key
  · rintro p u ⟨w, h1, h2, rfl⟩
    have hmem := wordD_mem hf w
    refine ⟨(schA_line F κ _ hmem).1, fun j => ⟨wordD F (ubasis F κ j :: w) f,
      ⟨_, by simpa using h1, ?_, rfl⟩, fun y => ?_⟩⟩
    · intro v hv
      rcases List.mem_cons.1 hv with rfl | hv
      · exact ⟨j, rfl⟩
      · exact h2 v hv
    · have hd := (schA_line F κ _ hmem).2 (ubasis F κ j) y
      have hc : Continuous fun s : ℝ => y + fun i => infAd F (s • ubasis F κ j i) :=
        continuous_const.add (continuous_pi fun i => (continuous_infAd F).comp (continuous_id.smul continuous_const))
      have := GlobalTheory.sobolev_endpoint_one_variable ℂ (fun s => wordD F w f (y + fun i => infAd F (s • ubasis F κ j i)))
        (fun s => dD F (ubasis F κ j) (wordD F w f) (y + fun i => infAd F (s • ubasis F κ j i))) 1 one_pos
        (fun t _ => hd t)
        (((schA_line F κ _ (wordD_mem hf (ubasis F κ j :: w))).1.comp hc).continuousOn)
      simp only [archIn_single, wordD_cons]
      simpa [infAd_zero, ← Pi.zero_def] using this
  · rintro u ⟨w, h1, h2, rfl⟩
    have e : ∀ t : Fin (dimA F κ) → ℝ, ∑ j, archIn F κ (Pi.single j (t j)) = archIn F κ t := by
      intro t
      rw [← map_sum, Finset.univ_sum_single]
    simp only [e]
    exact hB w (by simpa using h1) h2

end GlobalTheory.ArchDecay

namespace GlobalTheory.ArchDecay

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem cube_bound (μ : @Measure (κ → AF F) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) :
    ∃ (C : ℝ) (c : ℕ), 0 ≤ C ∧ ∀ m : ℕ, 0 < m → ∀ φ : (κ → AF F) → ℂ, Continuous φ → Per F m φ → ∀ b : ℝ, 0 ≤ b →
      ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal b → ∀ y,
        ∫ t in cube (dimA F κ), ‖φ (y + archIn F κ t)‖ ^ 2 ≤ C * (m : ℝ) ^ c * b := by
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  haveI := hμ
  obtain ⟨hopen, hμ1⟩ := slab_top F κ
  obtain ⟨h0, hfin1⟩ := hμ1 μ hμ
  obtain ⟨c, hc⟩ := slab_cover F κ
  have hQc : IsCompact (cube (dimA F κ)) := isCompact_univ_pi fun _ => isCompact_Icc
  have hc₁ : μ (archOut F κ ⁻¹' cube (dimA F κ) ∩ slab F κ 1) ≠ ⊤ := hfin1 _ hQc
  refine ⟨(μ (archOut F κ ⁻¹' cube (dimA F κ) ∩ slab F κ 1)).toReal⁻¹, c, by positivity,
    fun m hm φ hφ hper b hb hL y => ?_⟩
  obtain ⟨hsub, R, hRc, hR0, hRcov⟩ := hc m hm
  have hcm : μ (archOut F κ ⁻¹' cube (dimA F κ) ∩ slab F κ 1) ≤
      (m : ℝ≥0∞) ^ c * μ (archOut F κ ⁻¹' cube (dimA F κ) ∩ slab F κ m) := by
    calc μ (archOut F κ ⁻¹' cube (dimA F κ) ∩ slab F κ 1)
        ≤ ∑ r ∈ R, μ ((fun w => r + w) '' (archOut F κ ⁻¹' cube (dimA F κ) ∩ slab F κ m)) := by
          refine (measure_mono ?_).trans (measure_biUnion_finset_le R _)
          rintro w ⟨hwQ, hw1⟩
          obtain ⟨r, hr, hwr⟩ := hRcov w hw1
          have hπr : archOut F κ r = 0 := by rw [archOut_apply, hR0 r hr, map_zero]
          refine Set.mem_biUnion hr ⟨w - r, ⟨?_, hwr⟩, by abel_nf⟩
          show archOut F κ (w - r) ∈ cube (dimA F κ)
          rw [map_sub, hπr, sub_zero]; exact hwQ
      _ = ∑ r ∈ R, μ (archOut F κ ⁻¹' cube (dimA F κ) ∩ slab F κ m) := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [Set.image_add_left, measure_preimage_add]
      _ = R.card * μ (archOut F κ ⁻¹' cube (dimA F κ) ∩ slab F κ m) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := by gcongr; exact_mod_cast hRc
  have hS := slice_le μ (archIn F κ) (archOut F κ) (continuous_archIn F κ) (continuous_archOut F κ)
    (archOut_archIn F κ) (perSet F κ m) (hopen m hm).measurableSet
    (fun A hA => ne_top_of_le_ne_top (hfin1 A hA) (measure_mono (Set.inter_subset_inter_right _ hsub)))
    (fun w => ‖φ w‖ₑ ^ 2) (hφ.measurable.enorm.pow_const 2)
    (fun w u hu => by simp only [hper w u hu]) y
  set X := ∫⁻ t in cube (dimA F κ), ‖φ (y + archIn F κ t)‖ₑ ^ 2
  have h1 : μ (archOut F κ ⁻¹' cube (dimA F κ) ∩ slab F κ 1) * X ≤ (m : ℝ≥0∞) ^ c * ENNReal.ofReal b :=
    calc _ ≤ (m : ℝ≥0∞) ^ c * μ (archOut F κ ⁻¹' cube (dimA F κ) ∩ slab F κ m) * X := by gcongr
      _ = (m : ℝ≥0∞) ^ c * (μ (archOut F κ ⁻¹' cube (dimA F κ) ∩ slab F κ m) * X) := by ring
      _ ≤ _ := by gcongr; exact hS.trans hL
  have hI : ∫ t in cube (dimA F κ), ‖φ (y + archIn F κ t)‖ ^ 2 = X.toReal := by
    have hcont : Continuous fun t => ‖φ (y + archIn F κ t)‖ ^ 2 :=
      (hφ.comp (continuous_const.add (continuous_archIn F κ))).norm.pow 2
    rw [integral_eq_lintegral_of_nonneg_ae (f := fun t => ‖φ (y + archIn F κ t)‖ ^ 2)
      (ae_of_all _ fun _ => by positivity) hcont.aestronglyMeasurable]
    congr 1
    refine lintegral_congr fun t => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  have h2 : (μ (archOut F κ ⁻¹' cube (dimA F κ) ∩ slab F κ 1)).toReal * X.toReal ≤ (m : ℝ) ^ c * b := by
    rw [← ENNReal.toReal_mul]
    refine (ENNReal.toReal_mono (by simp [ENNReal.mul_eq_top]) h1).trans_eq ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast, ENNReal.toReal_ofReal hb]
  have hpos : 0 < (μ (archOut F κ ⁻¹' cube (dimA F κ) ∩ slab F κ 1)).toReal := ENNReal.toReal_pos h0.ne' hc₁
  rw [hI, mul_assoc, ← div_eq_inv_mul, le_div_iff₀ hpos, mul_comm]
  exact h2

theorem sobolev_per : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (μ : @Measure (κ → AF F) (borel _)),
    @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∃ (P : ℕ) (C : ℝ) (c : ℕ), ∀ m : ℕ, 0 < m → ∀ f ∈ schA F κ,
      Per F m f → ∀ b : ℝ, 0 ≤ b → (∀ w : List (κ → mixedEmbedding.mixedSpace F), w.length ≤ P → (∀ v ∈ w, ‖v‖ ≤ 1) →
        ∫⁻ x, ‖wordD F w f x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal b) → ∀ x, ‖f x‖ ^ 2 ≤ C * (m : ℝ) ^ c * b := by
  intro F _ _ κ _ μ hμ
  obtain ⟨C₀, c, -, hb⟩ := cube_bound μ hμ
  refine ⟨dimA F κ, 4 ^ dimA F κ * C₀, c, fun m hm f hf hper b hb0 hw x => ?_⟩
  have := sobolev_schA hf x (C₀ * m ^ c * b) fun w hl hv =>
    hb m hm _ (schA_line F κ _ (wordD_mem hf w)).1 (per_wordD hper w) b hb0
      (hw w hl fun v hv' => by obtain ⟨j, rfl⟩ := hv v hv'; rw [norm_ubasis]) x
  calc _ ≤ _ := this
    _ = _ := by ring

end GlobalTheory.ArchDecay

example : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∃ (P : ℕ) (C : ℝ) (c : ℕ), ∀ m : ℕ, 0 < m → ∀ f ∈ schA F κ, Per F m f → ∀ b : ℝ, 0 ≤ b → (∀ w : List (κ → mixedEmbedding.mixedSpace F), w.length ≤ P → (∀ v ∈ w, ‖v‖ ≤ 1) → ∫⁻ x, ‖wordD F w f x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal b) → ∀ x, ‖f x‖ ^ 2 ≤ C * (m : ℝ) ^ c * b := GlobalTheory.ArchDecay.sobolev_per
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SobolevUniformBoundPeriodic
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDecay
open scoped TensorProduct NNReal Matrix
open scoped Classical

noncomputable section
namespace GlobalTheory.SobClass

theorem wordH_mem_sch {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) :
    ∀ l : List ((κ → AF F) × (κ → AF F)), (∀ w ∈ l, IsArch w) → ∀ Φ ∈ schA F κ, wordH ψ l Φ ∈ schA F κ := by
  intro l
  induction l with
  | nil => intro _ Φ hΦ; exact hΦ
  | cons w l ih =>
    intro hl Φ hΦ
    rw [wordH_cons]
    exact GlobalTheory.T.heisenberg_derivative_preserves_schwartz F κ ψ hψ w (hl w (by simp)) _ (ih (fun v hv => hl v (by simp [hv])) Φ hΦ)

theorem sqrt_bound (Q M B t : ℝ) (hQ : 0 ≤ Q) (hM : 1 ≤ M) (hB : 0 ≤ B) (ht : 0 ≤ t) (h : t ^ 2 ≤ Q * (M * B)) :
    t ≤ √Q * (M * (1 + B)) := by
  have h1 : M * B ≤ (M * (1 + B)) ^ 2 := by nlinarith [mul_nonneg (sub_nonneg.2 hM) hB]
  have h2 : t ≤ √(Q * (M * B)) := Real.le_sqrt_of_sq_le h
  calc t ≤ √(Q * (M * B)) := h2
    _ = √Q * √(M * B) := Real.sqrt_mul hQ _
    _ ≤ √Q * (M * (1 + B)) := by
        gcongr
        calc √(M * B) ≤ √((M * (1 + B)) ^ 2) := Real.sqrt_le_sqrt h1
          _ = M * (1 + B) := Real.sqrt_sq (by nlinarith)

theorem sob_class : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (N : ℕ) (ψ : AddChar (AF F) ℂ), IsStd ψ → ∃ (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ ∧ ∃ (ℓ a : ℕ) (C : ℝ), ∀ Ψ ∈ schA F κ, ∀ m : ℕ, 1 ≤ m → (∀ x a' : κ → AF F, (∀ i, evI F (a' i) = 0 ∧ ∀ v, evFin F v (a' i) ∈ v.adicCompletionIntegers F) → Ψ (x + (m : AF F) • a') = Ψ x) → ∀ B : ℝ, 0 ≤ B → (∀ l : List ((κ → AF F) × (κ → AF F)), l.length ≤ ℓ → (∀ w ∈ l, IsArchUnit w) → ∫⁻ x, ‖wordH ψ l Ψ x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal B) → ∀ x : κ → AF F, ‖Ψ x‖ * (1 + ∑ i, ‖evI F (x i)‖) ^ N ≤ C * (m : ℝ) ^ a * (1 + B) := by
  intro F _ _ κ _ N ψ hψ
  obtain ⟨μ, hμ, a, Cb, hB⟩ := GlobalTheory.T.measurable_periodic_arch_restriction F κ
  obtain ⟨Lw, K, hLw, hW⟩ := GlobalTheory.T.schwartz_polynomial_decay_words F κ ψ hψ N
  obtain ⟨L, D, Cs, hL, hS⟩ := GlobalTheory.T.sobolev_pointwise_bound_words F κ ψ hψ
  refine ⟨μ, hμ, D + N, a, max K 0 * Lw.card * √(max Cs 0 * L.card * max Cb 0),
    fun Ψ hΨ m hm hper B hB0 hwords x => ?_⟩
  have hm1 : (1 : ℝ) ≤ (m : ℝ) ^ a := one_le_pow₀ (by exact_mod_cast hm)
  have hQ : 0 ≤ max Cs 0 * L.card * max Cb 0 := by positivity
  have hterm : ∀ l ∈ Lw, ‖wordH ψ l Ψ x‖ ≤ √(max Cs 0 * L.card * max Cb 0) * ((m : ℝ) ^ a * (1 + B)) := by
    intro l hl
    have hmem : wordH ψ l Ψ ∈ schA F κ := wordH_mem_sch ψ hψ l (fun w hw => ((hLw l hl).2 w hw).1) Ψ hΨ
    have h2 : ∀ l' ∈ L, ∫⁻ y : κ → mixedEmbedding.mixedSpace F, ‖wordH ψ l' (wordH ψ l Ψ) (x + archInc F y)‖ₑ ^ 2 ≤
        ENNReal.ofReal (max Cb 0 * (m : ℝ) ^ a * B) := by
      intro l' hl'
      rw [← wordH_append]
      have hu : ∀ w ∈ l' ++ l, IsArchUnit w := by
        intro w hw
        rcases List.mem_append.1 hw with hw | hw
        · exact (hL l' hl').2 w hw
        · exact (hLw l hl).2 w hw
      have hmem' : wordH ψ (l' ++ l) Ψ ∈ schA F κ := wordH_mem_sch ψ hψ _ (fun w hw => (hu w hw).1) Ψ hΨ
      have hper' : PerM F m (wordH ψ (l' ++ l) Ψ) := wordH_perM ψ hper _ (fun w hw => (hu w hw).1)
      have hmeas : Measurable fun y : κ → mixedEmbedding.mixedSpace F => ‖wordH ψ (l' ++ l) Ψ (x + archInc F y)‖ₑ ^ 2 :=
        (continuous_slice hmem' x).measurable.enorm.pow_const 2
      have h5 := hB m hm (fun z => ‖wordH ψ (l' ++ l) Ψ z‖ₑ ^ 2) (fun z a' ha => by rw [hper' z a' ha]) x hmeas
      have hw := hwords (l' ++ l) (by rw [List.length_append]; have := (hL l' hl').1; have := (hLw l hl).1; omega) hu
      refine h5.trans ?_
      calc ENNReal.ofReal (Cb * (m : ℝ) ^ a) * ∫⁻ z, ‖wordH ψ (l' ++ l) Ψ z‖ₑ ^ 2 ∂μ
          ≤ ENNReal.ofReal (max Cb 0 * (m : ℝ) ^ a) * ENNReal.ofReal B := by
            gcongr
            exact le_max_left _ _
        _ = ENNReal.ofReal (max Cb 0 * (m : ℝ) ^ a * B) := (ENNReal.ofReal_mul (by positivity)).symm
    have h3 : ‖wordH ψ l Ψ x‖ₑ ^ 2 ≤ ENNReal.ofReal (max Cs 0 * L.card * max Cb 0 * ((m : ℝ) ^ a * B)) := by
      refine (hS _ hmem x).trans ?_
      calc ENNReal.ofReal Cs * ∑ l' ∈ L, ∫⁻ y : κ → mixedEmbedding.mixedSpace F, ‖wordH ψ l' (wordH ψ l Ψ) (x + archInc F y)‖ₑ ^ 2
          ≤ ENNReal.ofReal (max Cs 0) * ∑ _l' ∈ L, ENNReal.ofReal (max Cb 0 * (m : ℝ) ^ a * B) := by
            gcongr with l' hl'
            · exact le_max_left _ _
            · exact h2 l' hl'
        _ = ENNReal.ofReal (max Cs 0 * L.card * max Cb 0 * ((m : ℝ) ^ a * B)) := by
            rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
              ← ENNReal.ofReal_mul (by positivity)]
            congr 1
            ring
    have h4 : ‖wordH ψ l Ψ x‖ ^ 2 ≤ max Cs 0 * L.card * max Cb 0 * ((m : ℝ) ^ a * B) := by
      rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)] at h3
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h3
    exact sqrt_bound _ _ _ _ hQ hm1 hB0 (norm_nonneg _) (by simpa [mul_assoc] using h4)
  calc ‖Ψ x‖ * (1 + ∑ i, ‖evI F (x i)‖) ^ N ≤ K * ∑ l ∈ Lw, ‖wordH ψ l Ψ x‖ := hW Ψ x
    _ ≤ max K 0 * ∑ l ∈ Lw, ‖wordH ψ l Ψ x‖ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    _ ≤ max K 0 * ∑ _l ∈ Lw, √(max Cs 0 * L.card * max Cb 0) * ((m : ℝ) ^ a * (1 + B)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (le_max_right _ _)
    _ = max K 0 * Lw.card * √(max Cs 0 * L.card * max Cb 0) * (m : ℝ) ^ a * (1 + B) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

end GlobalTheory.SobClass
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricRigidTranslateLineBundleOfSquareDefect
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open MonoidalCategory CartesianMonoidalCategory MonObj Limits
open scoped CategoryTheory.Obj
open GlobalTheory.CechPic (Pic cls lam)

noncomputable section

namespace GlobalTheory.SymTranslate

theorem sym_rigTransl_of_sq : ∀ (K : Type) [Field K] (B : Over (Sp K)) [GrpObj B] [IsCommMonObj B] (L : LB B.left) (hL : L.IsLB), (∃ t : LB.Gen (Theta B L), t.IsGen) → ∀ a : 𝟙_ (Over (Sp K)) ⟶ B, CechPic.pull (GrpObj.inv : B ⟶ B).left (cls L hL) - cls L hL = lam (cls L hL) (toUnit B ≫ a ^ 2) (𝟙 B) → Out.Sym B (GlobalTheory.RigidTranslate.rigTransl L a) := by
  intro K _ B _ _ L hL _ a h
  have hc : ∀ x : 𝟙_ (Over (Sp K)) ⟶ B, CechPic.pull (toUnit B ≫ x).left (cls L hL) = 0 := fun x => by
    rw [Over.comp_left, CechPic.pull_comp,
      GlobalTheory.PrimitiveOverField.pic_field (CechPic.pull x.left (cls L hL))]
    exact map_zero _
  have h1 : CechPic.pull (1 : B ⟶ B).left (cls L hL) = 0 := hc _
  have h2 : CechPic.pull (GrpObj.inv : B ⟶ B).left (cls L hL) =
      CechPic.pull ((toUnit B ≫ a ^ 2) * 𝟙 B).left (cls L hL) := by
    rw [lam, hc, h1, Over.id_left, CechPic.pull_id, sub_zero, add_zero] at h
    exact sub_left_injective h
  have h3 := congrArg (CechPic.pull (𝟙 B * (toUnit B ≫ a)⁻¹).left) h2
  rw [← CechPic.pull_comp, ← CechPic.pull_comp, ← Over.comp_left, ← Over.comp_left] at h3
  have e1 : (𝟙 B * (toUnit B ≫ a)⁻¹) ≫ (GrpObj.inv : B ⟶ B) =
      (GrpObj.inv : B ⟶ B) ≫ (𝟙 B * (toUnit B ≫ a)) := by
    rw [← Hom.inv_def, MonObj.comp_mul, ← Category.assoc, comp_toUnit, Category.comp_id, mul_inv, inv_inv,
      Hom.inv_def, Category.id_comp]
  have e2 : (𝟙 B * (toUnit B ≫ a)⁻¹) ≫ ((toUnit B ≫ a ^ 2) * 𝟙 B) = 𝟙 B * (toUnit B ≫ a) := by
    rw [MonObj.comp_mul, ← Category.assoc, comp_toUnit, Category.comp_id, MonObj.comp_pow, sq,
      _root_.mul_comm (𝟙 B), _root_.mul_comm (𝟙 B), _root_.mul_assoc, mul_inv_cancel_left]
  rw [e1, e2, Over.comp_left, CechPic.pull_comp] at h3
  have hL' : (GlobalTheory.RigidTranslate.rigTransl L a).IsLB := LB.isLB_linComb hL _ _
  have h4 : cls _ hL' = CechPic.pull (𝟙 B * (toUnit B ≫ a)).left (cls L hL) := by
    rw [CechPic.cls_linComb hL, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hc, smul_zero, add_zero, one_smul]
    rfl
  exact GlobalTheory.RigSymSubring.sym_of_cls hL' (by rw [h4]; exact h3)

end GlobalTheory.SymTranslate
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalGradedIsotropicFlagLeStatement
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_radical_graded_isotropic_flag_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (S : Finset (Fin r)) (s : ℕ) (hs : s ≤ r), (∀ i : Fin r, i.val < s ↔ ∃ k ∈ S, i ≤ k) → ∀ d : Fin s → ℕ, (∀ i, d i = (S.filter (· < Fin.castLE hs i)).card) → GlobalTheory.UAut.unipFlag σ J (X.submatrix id (Fin.castLE hs)) d ≤ GlobalTheory.StdPar.unip σ J X S := by
  first | exact @GlobalTheory.TieStd.unipFlag_castLE_le_unip | exact GlobalTheory.TieStd.unipFlag_castLE_le_unip | (intros; apply GlobalTheory.TieStd.unipFlag_castLE_le_unip <;> assumption)
end

