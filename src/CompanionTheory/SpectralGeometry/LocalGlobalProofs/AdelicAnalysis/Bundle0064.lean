import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0058
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0062
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0006
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GlobalProductGramFiberRankOne
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0063
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0014
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0023

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicHaarMeasureLinearChange
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.Core.PiScale

section Abstract

variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [MeasurableSpace R]
  [BorelSpace R] [SecondCountableTopology R] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem continuous_mulVec_left (M : Matrix ι ι R) : Continuous (fun x : ι → R => M *ᵥ x) :=
  Continuous.matrix_mulVec continuous_const continuous_id

theorem image_mulVec_eq_preimage (M N : Matrix ι ι R) (h1 : M * N = 1) (h2 : N * M = 1)
    (s : Set (ι → R)) : (fun x => M *ᵥ x) '' s = (fun x => N *ᵥ x) ⁻¹' s := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [Matrix.mulVec_mulVec, h2] using hx
  · intro hy
    exact ⟨N *ᵥ y, hy, by simp [Matrix.mulVec_mulVec, h1]⟩

theorem pi_image_mul (lf : Measure R) [SigmaFinite lf] (u v : ι → R) (huv : ∀ i, u i * v i = 1)
    (c : ι → ℝ≥0)
    (hc : ∀ i (s : Set R), MeasurableSet s → lf ((fun x => u i * x) '' s) = (c i : ℝ≥0∞) * lf s)
    (s : Set (ι → R)) (hs : MeasurableSet s) :
    (Measure.pi fun _ : ι => lf) ((fun x i => u i * x i) '' s) =
      (∏ i, (c i : ℝ≥0∞)) * (Measure.pi fun _ : ι => lf) s := by
  have hT : Measurable (fun (x : ι → R) i => v i * x i) :=
    (continuous_pi fun i => continuous_const.mul (continuous_apply i)).measurable
  have himg : (fun (x : ι → R) i => u i * x i) '' s = (fun (x : ι → R) i => v i * x i) ⁻¹' s := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have : (fun i => v i * (u i * x i)) = x := by
        funext i
        rw [← mul_assoc, mul_comm (v i), huv, one_mul]
      simpa [this] using hx
    · intro hy
      refine ⟨_, hy, ?_⟩
      funext i
      show u i * (v i * y i) = y i
      rw [← mul_assoc, huv, one_mul]
  have hpre : ∀ i (t : Set R), (fun x => v i * x) ⁻¹' t = (fun x => u i * x) '' t := by
    intro i t
    ext y
    constructor
    · intro hy
      exact ⟨_, hy, by simp only; rw [← mul_assoc, huv, one_mul]⟩
    · rintro ⟨x, hx, rfl⟩
      have : v i * (u i * x) = x := by rw [← mul_assoc, mul_comm (v i), huv, one_mul]
      simpa [this] using hx
  have e1 : Measure.pi (fun i => c i • lf) =
      (Measure.pi fun _ : ι => lf).map (fun (x : ι → R) i => v i * x i) := by
    refine Measure.pi_eq fun t ht => ?_
    rw [Measure.map_apply hT (MeasurableSet.univ_pi ht)]
    have : (fun (x : ι → R) i => v i * x i) ⁻¹' Set.pi Set.univ t =
        Set.pi Set.univ fun i => (fun x => u i * x) '' t i := by
      ext x
      simp only [Set.mem_preimage, Set.mem_univ_pi, ← hpre]
    rw [this, Measure.pi_pi]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hc i _ (ht i)]
    rfl
  have e2 : Measure.pi (fun i => c i • lf) =
      (∏ i, (c i : ℝ≥0∞)) • (Measure.pi fun _ : ι => lf) := by
    refine Measure.pi_eq fun t ht => ?_
    rw [Measure.smul_apply, Measure.pi_pi, smul_eq_mul, ← Finset.prod_mul_distrib]
    rfl
  rw [himg, ← Measure.map_apply hT hs, ← e1, e2, Measure.smul_apply, smul_eq_mul]

theorem measurePreserving_transvection (lf : Measure R) [SigmaFinite lf] [lf.IsAddLeftInvariant]
    (i j : ι) (hij : i ≠ j) (c : R) :
    MeasurePreserving (fun x : ι → R => transvection i j c *ᵥ x)
      (Measure.pi fun _ : ι => lf) (Measure.pi fun _ : ι => lf) := by
  have ht : Measurable (fun x : ι → R => transvection i j c *ᵥ x) :=
    (continuous_mulVec_left _).measurable
  refine ⟨ht, ?_⟩
  refine (Measure.pi_eq fun s hs ↦ ?_).symm
  have h2s : MeasurableSet (Set.univ.pi s) := .pi Set.countable_univ fun i _ ↦ hs i
  simp_rw [← Measure.pi_pi, ← lintegral_indicator_one h2s]
  rw [lintegral_map (measurable_one.indicator h2s) ht]
  refine lintegral_eq_of_lmarginal_eq {i} ((measurable_one.indicator h2s).comp ht)
    (measurable_one.indicator h2s) ?_
  simp_rw [lmarginal_singleton]
  ext x
  have hup : ∀ xi : R, transvection i j c *ᵥ Function.update x i xi =
      Function.update x i (xi + c * x j) := by
    intro xi
    funext k
    by_cases hk : k = i
    · subst hk
      simp [transvection, add_mulVec, single_mulVec, hij.symm]
    · simp [transvection, add_mulVec, single_mulVec, hk, hij.symm]
  simp only [Function.comp_apply, hup]
  exact lintegral_add_right_eq_self
    (fun xᵢ ↦ Set.indicator (Set.univ.pi s) 1 (Function.update x i xᵢ)) (c * x j)

end Abstract

section Global

variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem Bf_mul (g h : Matrix ι ι F) : Bf (g * h) = Bf g * Bf h := by
  simp [Bf, Matrix.map_mul]

theorem Bf_one : Bf (1 : Matrix ι ι F) = 1 := by
  simp [Bf]

theorem Bf_inv_mul (g : Matrix ι ι F) (hg : g.det ≠ 0) : Bf g⁻¹ * Bf g = 1 := by
  rw [← Bf_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hg), Bf_one]

theorem Bf_mul_inv (g : Matrix ι ι F) (hg : g.det ≠ 0) : Bf g * Bf g⁻¹ = 1 := by
  rw [← Bf_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hg), Bf_one]

end Global

theorem pi_scale : ∀ (F : Type) [Field F] [NumberField F], ∀ [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι], (∀ g : Matrix ι ι F, g.det ≠ 0 → ∀ s : Set (ι → A F), MeasurableSet s → (Measure.pi fun _ : ι => lf) ((fun x => Bf g *ᵥ x) '' s) = ENNReal.ofReal (|((Algebra.norm ℚ g.det : ℚ) : ℝ)|⁻¹) * (Measure.pi fun _ : ι => lf) s) ∧ ∀ (a : (A F)ˣ) (s : Set (ι → A F)), MeasurableSet s → (Measure.pi fun _ : ι => lf) ((fun x => (a : A F) • x) '' s) = lf ((fun x => (a : A F) * x) '' Oh F) ^ Fintype.card ι * (Measure.pi fun _ : ι => lf) s := by
  intro F _ _ _ _ lf hH h1 ι _ _
  obtain ⟨hlc, hsc, ht2, hOc, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  obtain ⟨hF, -, hU⟩ := GlobalTheory.T.adelic_haar_measure_scaling F lf hH h1
  haveI := hlc
  haveI := hsc
  haveI := ht2
  haveI : SigmaFinite lf := inferInstance
  have hmeas : ∀ (g : Matrix ι ι F), g.det ≠ 0 → ∀ s : Set (ι → A F), MeasurableSet s →
      MeasurableSet ((fun x => Bf g *ᵥ x) '' s) := by
    intro g hg s hs
    rw [image_mulVec_eq_preimage _ _ (Bf_mul_inv g hg) (Bf_inv_mul g hg)]
    exact (continuous_mulVec_left _).measurable hs
  refine ⟨?_, ?_⟩
  · intro g hg
    refine diagonal_transvection_induction_of_det_ne_zero
      (fun g => ∀ s : Set (ι → A F), MeasurableSet s →
        (Measure.pi fun _ : ι => lf) ((fun x => Bf g *ᵥ x) '' s) =
          ENNReal.ofReal (|((Algebra.norm ℚ g.det : ℚ) : ℝ)|⁻¹) *
            (Measure.pi fun _ : ι => lf) s) g hg ?_ ?_ ?_
    · intro D hD s hs
      have hD' : ∀ i, D i ≠ 0 := by
        intro i
        rw [det_diagonal] at hD
        exact Finset.prod_ne_zero_iff.1 hD i (Finset.mem_univ i)
      have hfun : (fun x : ι → A F => Bf (diagonal D) *ᵥ x) =
          fun x i => algebraMap F (A F) (D i) * x i := by
        funext x i
        have : Bf (diagonal D) = diagonal (fun i => algebraMap F (A F) (D i)) := by
          ext a b
          by_cases hab : a = b
          · subst hab; simp [Bf]
          · simp [Bf, hab]
        rw [this, mulVec_diagonal]
      rw [hfun, pi_image_mul lf (fun i => algebraMap F (A F) (D i))
        (fun i => algebraMap F (A F) (D i)⁻¹) ?_
        (fun i => Real.toNNReal (|((Algebra.norm ℚ (D i) : ℚ) : ℝ)|⁻¹)) ?_ s hs]
      · congr 1
        rw [det_diagonal, map_prod, Rat.cast_prod, Finset.abs_prod, ← Finset.prod_inv_distrib,
          ENNReal.ofReal_prod_of_nonneg fun i _ => inv_nonneg.2 (abs_nonneg _)]
        rfl
      · intro i
        rw [← map_mul, mul_inv_cancel₀ (hD' i), map_one]
      · intro i t ht
        exact hF (D i) (hD' i) t ht
    · intro t s hs
      have hdet : t.toMatrix.det = 1 := t.det
      have hinv : Bf t.toMatrix * Bf (transvection t.i t.j (-t.c)) = 1 := by
        rw [← Bf_mul, TransvectionStruct.toMatrix, transvection_mul_transvection_same _ _ t.hij]
        simp [Bf_one]
      have hinv' : Bf (transvection t.i t.j (-t.c)) * Bf t.toMatrix = 1 := by
        rw [← Bf_mul, TransvectionStruct.toMatrix, transvection_mul_transvection_same _ _ t.hij]
        simp [Bf_one]
      have hB : Bf (transvection t.i t.j (-t.c)) =
          transvection t.i t.j (algebraMap F (A F) (-t.c)) := by
        simp [Bf, transvection, Matrix.map_add, Matrix.map_one]
      rw [image_mulVec_eq_preimage _ _ hinv hinv', hB,
        (measurePreserving_transvection lf t.i t.j t.hij _).measure_preimage hs.nullMeasurableSet,
        hdet]
      simp
    · intro P Q hP hQ IP IQ s hs
      have himg : (fun x => Bf (P * Q) *ᵥ x) '' s =
          (fun x => Bf P *ᵥ x) '' ((fun x => Bf Q *ᵥ x) '' s) := by
        rw [Set.image_image]
        simp [Bf_mul, Matrix.mulVec_mulVec]
      rw [himg, IP _ (hmeas Q hQ s hs), IQ s hs, ← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 (abs_nonneg _)),
        det_mul, map_mul, Rat.cast_mul, abs_mul, mul_inv]
  · intro a s hs
    have hfin : lf ((fun x => (a : A F) * x) '' Oh F) ≠ ∞ :=
      (hOc.image (continuous_const.mul continuous_id)).measure_lt_top.ne
    have hfun : (fun x : ι → A F => (a : A F) • x) = fun x i => (a : A F) * x i := by
      funext x i
      rfl
    rw [hfun, pi_image_mul lf (fun _ => (a : A F)) (fun _ => ((a⁻¹ : (A F)ˣ) : A F)) (fun _ => by simp)
      (fun _ => (lf ((fun x => (a : A F) * x) '' Oh F)).toNNReal) ?_ s hs]
    · simp [ENNReal.coe_toNNReal hfin]
    · intro _ t ht
      rw [ENNReal.coe_toNNReal hfin]
      exact hU a t ht

end GlobalTheory.CompanionTheory.SW.Core.PiScale
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicLatticeMeasureFormula
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.ThW

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups Kronecker

theorem muF_latN : ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (B : Matrix ι ι F) (N : ℕ), 0 < N → (muF B lf (latN F ι N : Set (ι → A F))).toReal = kap F ^ Fintype.card ι * (Real.sqrt |((Algebra.norm ℚ B.det : ℚ) : ℝ)|)⁻¹ * (((N : ℝ) ^ Module.finrank ℚ F)⁻¹) ^ Fintype.card ι := by
  intro F _ _ _ _ lf hH h1 ι _ _ B N hN
  obtain ⟨hlc, hsc, ht2, -, hopen, -, -, -, -, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  haveI := hlc
  haveI := hsc
  haveI := ht2
  haveI : SigmaFinite lf := inferInstance
  have hscale := (GlobalTheory.T.adelic_haar_measure_scaling F lf hH h1).1
  have hNF : ((N : F)) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hnorm : ((Algebra.norm ℚ (N : F) : ℚ) : ℝ) = (N : ℝ) ^ Module.finrank ℚ F := by
    have : (N : F) = algebraMap ℚ F (N : ℚ) := by simp
    rw [this, Algebra.norm_algebraMap]
    push_cast
    rfl
  set S : Set (A F) := (fun x => algebraMap F (A F) (N : F) * x) '' Oh F with hSdef
  have hlf : lf S = ENNReal.ofReal (((N : ℝ) ^ Module.finrank ℚ F)⁻¹) := by
    rw [hSdef, hscale (N : F) hNF (Oh F) hopen.measurableSet, h1, mul_one, hnorm,
      abs_of_nonneg (by positivity)]
  have hset : (latN F ι N : Set (ι → A F)) = Set.pi Set.univ (fun _ => S) := by
    ext x
    simp only [SetLike.mem_coe, Set.mem_pi, Set.mem_univ, true_imp_iff, hSdef, Set.mem_image,
      map_natCast]
    constructor
    · intro h i
      obtain ⟨y, hy, e⟩ := h i
      exact ⟨y, hy, e.symm⟩
    · intro h i
      obtain ⟨y, hy, e⟩ := h i
      exact ⟨y, hy, e.symm⟩
  have hk : 0 ≤ kap F := inv_nonneg.mpr (Real.sqrt_nonneg _)
  rw [hset, muF, Measure.smul_apply, Measure.pi_pi, smul_eq_mul, Finset.prod_const,
    Finset.card_univ, hlf, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal]
  positivity

end GlobalTheory.CompanionTheory.SW.ThW
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ContDiffOnChartGlobalWhittakerCoefficientStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiffOn_chart_globalWhittakerCoefficient : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (v : HeightOneSpectrum (𝓞 F)), IsCompact (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) ∧ IsOpen (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.LatCpt.latV_compact_open | exact GlobalTheory.CompanionTheory.SW.LatCpt.latV_compact_open | (intros; apply GlobalTheory.CompanionTheory.SW.LatCpt.latV_compact_open <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.DualLatticeMembershipTrace
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.ThW

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups Kronecker

theorem Bf_mulVec_toA {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι F) (y : ι → F) : Bf B *ᵥ toA y = toA (B *ᵥ y) := by
  funext i
  exact (RingHom.map_mulVec (algebraMap F (A F)) B y i).symm

theorem trace_int_of_basis {F : Type} [Field F] [NumberField F]
    (b : Module.Basis (InfinitePlace F) ℤ (𝓞 F)) (N : ℕ) (c : F)
    (h : ∀ v, ∃ m : ℤ, (N : ℚ) * Algebra.trace ℚ F ((b v : F) * c) = m) (r : 𝓞 F) :
    ∃ n : ℤ, Algebra.trace ℚ F ((N : F) * c * (r : F)) = n := by
  choose m hm using h
  have hr : (r : F) = ∑ v, ((b.repr r v : ℤ) : F) * (b v : F) := by
    conv_lhs => rw [← b.sum_repr r]
    simp [map_sum]
  refine ⟨∑ v, b.repr r v * m v, ?_⟩
  rw [hr, Finset.mul_sum, map_sum]
  push_cast
  refine Finset.sum_congr rfl fun v _ => ?_
  have e : (N : F) * c * (((b.repr r v : ℤ) : F) * (b v : F)) =
      (((b.repr r v : ℤ) : ℚ) * (N : ℚ)) • ((b v : F) * c) := by
    rw [Algebra.smul_def]
    simp only [eq_ratCast, Rat.cast_mul, Rat.cast_intCast, Rat.cast_natCast]
    ring
  rw [e, map_smul, smul_eq_mul, mul_assoc, hm v]

theorem toA_mem_perp_latN_iff : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (A F) ℂ), IsStdChar F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (B : Matrix ι ι F) (b : Module.Basis (InfinitePlace F) ℤ (𝓞 F)) (N : ℕ), 0 < N → ∀ y : ι → F, toA y ∈ perp (chiB ψ (Bf B)) (latN F ι N : Set (ι → A F)) ↔ ∀ i v, ∃ m : ℤ, (N : ℚ) * Algebra.trace ℚ F ((b v : F) * (B *ᵥ y) i) = m := by
  intro F _ _ ψ hψ ι _ _ B b N _ y
  obtain ⟨-, hall⟩ := GlobalTheory.T.standard_adelic_character F
  obtain ⟨-, -, hchar⟩ := hall ψ hψ
  have hBy := Bf_mulVec_toA B y
  constructor
  · intro h i v
    have h1 : ∀ x ∈ Oh F, ψ (algebraMap F (A F) ((N : F) * (B *ᵥ y) i) * x) = 1 := by
      intro x hx
      have hmem : (Pi.single i ((N : A F) * x) : ι → A F) ∈ latN F ι N := by
        refine fun j => ?_
        by_cases hj : j = i
        · subst hj
          exact ⟨x, hx, by simp⟩
        · exact ⟨0, oh_zero, by simp [Pi.single_eq_of_ne hj]⟩
      have h2 : ψ ((Pi.single i ((N : A F) * x) : ι → A F) ⬝ᵥ (Bf B *ᵥ toA y)) = 1 := h _ hmem
      rw [hBy, single_dotProduct] at h2
      rw [← h2, map_mul (algebraMap F (A F)), map_natCast (algebraMap F (A F))]
      congr 1
      simp only [toA]
      ring
    obtain ⟨n, hn⟩ := (hchar _).mp h1 (b v)
    refine ⟨n, ?_⟩
    rw [← hn]
    have e : (N : F) * (B *ᵥ y) i * (b v : F) = (N : ℚ) • ((b v : F) * (B *ᵥ y) i) := by
      rw [Algebra.smul_def]
      push_cast
      ring
    rw [e, map_smul, smul_eq_mul]
  · intro h x hx
    have h1 : ∀ i, ∀ x ∈ Oh F, ψ (algebraMap F (A F) ((N : F) * (B *ᵥ y) i) * x) = 1 :=
      fun i => (hchar _).mpr (trace_int_of_basis b N _ (h i))
    show ψ (x ⬝ᵥ (Bf B *ᵥ toA y)) = 1
    rw [hBy, dotProduct]
    have h2 : ∀ s : Finset ι, ψ (∑ i ∈ s, x i * toA (B *ᵥ y) i) = 1 := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert i s hi ih =>
        rw [Finset.sum_insert hi, AddChar.map_add_eq_mul, ih, mul_one]
        obtain ⟨x', hx', e⟩ := hx i
        rw [e, ← h1 i x' hx', map_mul (algebraMap F (A F)), map_natCast (algebraMap F (A F))]
        congr 1
        simp only [toA]
        ring
    exact h2 Finset.univ

end GlobalTheory.CompanionTheory.SW.ThW
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.EulerProductMeasureTransportStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.euler_product_measure_transport : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (I : Measure (Fin n → Fin M → AF F ⊗[F] E)) (minf minf' : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (m m' : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (e : (Fin n → Fin M → AF F ⊗[F] E) → (Fin n → Fin M → AF F ⊗[F] E)) (einf : (Fin n → Fin M → Ainf F ⊗[F] E) → (Fin n → Fin M → Ainf F ⊗[F] E)) (ev : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → (Fin n → Fin M → Fv F v ⊗[F] E)), Measurable e → Measurable einf → (∀ v, Measurable (ev v)) → (∀ X, projInf (e X) = einf (projInf X) ∧ ∀ v, projV v (projFin (e X)) = ev v (projV v (projFin X))) → (∀ᶠ v in Filter.cofinite, ∀ X, ev v X ∈ latV b v ↔ X ∈ latV b v) → ∀ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c → minf.map einf = cinf • minf' → (∀ v, (m v).map (ev v) = c v • m' v) → (∀ v, m' v (latV b v) < ⊤) → IsEulerProd b I 1 minf m → IsEulerProd b (I.map e) 1 minf' m' := by
  first | exact @GlobalTheory.CompanionTheory.SW.EulerMove.euler_move | exact GlobalTheory.CompanionTheory.SW.EulerMove.euler_move | (intros; apply GlobalTheory.CompanionTheory.SW.EulerMove.euler_move <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GlobalProductGramFiberRankOneStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.global_product_gram_fiber_rank_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), (∀ v, IsStdV v (lam v)) → ∀ (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)), (∀ v, IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b (lam v) 1 M) (coordHerm (Fv F v) σ b (lam v) 1) (m v)) → ∀ (lf : Measure (Af F)), lf.IsAddHaarMeasure → lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1 → ∀ a : ℕ, 0 < a → ∀ D : Af F → ℝ, Continuous D → (∀ y, 0 ≤ D y) → (∀ U : Set (Af F), MeasurableSet U → coordW (Af F) b lf 1 M {X | (∀ v, projV v X ∈ {X : (Fin 1 → Fin M → Fv F v ⊗[F] E) | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v}) ∧ algebraMap F (Af F) (1 / 2) * Algebra.trace (Af F) (Af F ⊗[F] E) (gramR (Af F) σ J X 0 0) ∈ U} = ∫⁻ y in U, ENNReal.ofReal (D y) ∂lf) → ∀ β : F, β ≠ 0 → HasProd (fun v => (m v (hermScal (Fv F v) σ (algebraMap F _ β)) {X : (Fin 1 → Fin M → Fv F v ⊗[F] E) | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v}).toReal) (D (algebraMap F (Af F) β)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.EulerDens.hasProd_fibre_mass | exact GlobalTheory.CompanionTheory.SW.EulerDens.hasProd_fibre_mass | (intros; apply GlobalTheory.CompanionTheory.SW.EulerDens.hasProd_fibre_mass <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.NonarchimedeanSelfdualMeasurePiStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonarchimedean_selfdual_measure_pi : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (v : HeightOneSpectrum (𝓞 F)) (k : Measure (Fv F v)), SelfDual k (fun s t => psiV F ψ v (s * t)) → ∀ (ι : Type) [Fintype ι], SelfDual (Measure.pi fun _ : ι => k) (fun x y => psiV F ψ v (x ⬝ᵥ y)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.PiV.selfDual_pi_v | exact GlobalTheory.CompanionTheory.SW.PiV.selfDual_pi_v | (intros; apply GlobalTheory.CompanionTheory.SW.PiV.selfDual_pi_v <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.PureAdelicFunctionMeasurableStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pure_adelic_function_measurable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (S : Finset (HeightOneSpectrum (𝓞 F))) (φinf : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞) (φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℝ≥0∞), Measurable φinf → (∀ v, Measurable (φ v)) → Measurable (pureL b S φinf φ) := by
  first | exact @GlobalTheory.CompanionTheory.SW.PureMeas.measurable_pureL | exact GlobalTheory.CompanionTheory.SW.PureMeas.measurable_pureL | (intros; apply GlobalTheory.CompanionTheory.SW.PureMeas.measurable_pureL <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StandardLocalHaarPropertiesStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_local_haar_properties : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → lam {t | Valued.v t < 1} = (Ideal.absNorm v.asIdeal : ℝ≥0∞)⁻¹ ∧ (∀ π : Fv F v, Valued.v π = WithZero.exp (-1 : ℤ) → lam.map (fun t => π * t) = (Ideal.absNorm v.asIdeal : ℝ≥0∞) • lam) ∧ (∀ u : Fv F v, Valued.v u = 1 → lam.map (fun t => u * t) = lam) ∧ Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) = Ideal.absNorm v.asIdeal := by
  first | exact @GlobalTheory.CompanionTheory.SW.Vol.volumes_in_completion | exact GlobalTheory.CompanionTheory.SW.Vol.volumes_in_completion | (intros; apply GlobalTheory.CompanionTheory.SW.Vol.volumes_in_completion <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaAverageIntegralFormula
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

namespace GlobalTheory.CompanionTheory.SW.Core.ThetaIntegral

theorem thTerm_zero {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ)
    (gf : Matrix ι ι (A F)) (gi : InfinitePlace F → Matrix ι ι ℝ) (φ : (ι → A F) → ℂ)
    (τ : InfinitePlace F → ℂ) : thTerm B ρ P gf gi φ τ 0 = φ 0 := by
  have h1 : (fun j : ι => algebraMap F (A F) ((0 : ι → F) j)) = 0 := by
    funext j; simp
  have h2 : ∀ w, (fun j : ι => ρ w ((0 : ι → F) j)) = 0 := by
    intro w; funext j; simp
  simp only [thTerm, gauss, h1, h2, mulVec_zero]
  simp

theorem main : ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) (gf : Ω → Matrix ι ι (A F)) (gi : Ω → InfinitePlace F → Matrix ι ι ℝ), CountData M B ρ Pr gf gi → ∀ φ τ, SB φ → (∀ w, 0 < (τ w).im) → Integrable (fun ω => theta B ρ P (gf ω) (gi ω) φ τ) Pr ∧ ENNReal.ofReal ‖(∫ ω, theta B ρ P (gf ω) (gi ω) φ τ ∂Pr) - φ 0‖ ≤ ∫⁻ ω, ∑' x : {x : ι → F // x ≠ 0}, ‖thTerm B ρ P (gf ω) (gi ω) φ τ x.1‖ₑ ∂Pr := by
  intro F _ _ _ _ lf _ _ ψ _ ι _ _ M B ρ P hQ Ω _ Pr gf gi hC φ τ hφ hτ
  haveI : IsProbabilityMeasure Pr := hC.1
  have horth : ∀ ω, IsOrth B ρ (gf ω) (gi ω) := hC.2.2.2.1
  haveI : Countable F :=
    Function.Injective.countable (Module.finBasis ℚ F).equivFun.injective
  obtain ⟨w0, -, h0⟩ := Finset.exists_min_image Finset.univ (fun w => (τ w).im) Finset.univ_nonempty
  obtain ⟨w1, -, h1⟩ := Finset.exists_max_image Finset.univ (fun w => (τ w).im) Finset.univ_nonempty
  have ht : 0 < (τ w0).im := hτ w0
  have hs : 0 < (τ w1).im := hτ w1
  obtain ⟨C, hCb⟩ := GlobalTheory.T.weighted_theta_average_le_of_countData F ι M B ρ P hQ Ω Pr gf gi hC φ hφ
    ((τ w0).im / (τ w1).im) (τ w0).im (div_pos ht hs) ht
  obtain ⟨hmeas, hbd⟩ := hCb τ (fun w => h0 w (Finset.mem_univ w)) (by
    intro v w
    have hw : (τ w).im ≤ (τ w1).im := h1 w (Finset.mem_univ w)
    have hv : (τ w0).im ≤ (τ v).im := h0 v (Finset.mem_univ v)
    calc (τ w0).im / (τ w1).im * (τ w).im ≤ (τ w0).im / (τ w1).im * (τ w1).im :=
          mul_le_mul_of_nonneg_left hw (div_pos ht hs).le
      _ = (τ w0).im := div_mul_cancel₀ _ hs.ne'
      _ ≤ (τ v).im := hv)
  have hwt : 0 < wt M τ := Finset.prod_pos fun w _ => pow_pos (Real.sqrt_pos.2 (hτ w)) M
  have hfin : (∫⁻ ω, ∑' x : {x : ι → F // x ≠ 0}, ‖thTerm B ρ P (gf ω) (gi ω) φ τ x.1‖ₑ ∂Pr) ≠ ∞ := by
    intro h
    rw [h, ENNReal.mul_top (by simpa using hwt)] at hbd
    simp at hbd
  have hsum : ∀ ω, Summable (thTerm B ρ P (gf ω) (gi ω) φ τ) := fun ω =>
    ((GlobalTheory.T.theta_series_summable F ι M B ρ P hQ (gf ω) (gi ω) (horth ω) τ hτ).1 φ hφ).of_norm
  have hsub : ∀ ω, Summable fun x : {x : ι → F // x ≠ 0} => thTerm B ρ P (gf ω) (gi ω) φ τ x.1 :=
    fun ω => (hsum ω).subtype _
  set g : Ω → ℂ := fun ω => ∑' x : {x : ι → F // x ≠ 0}, thTerm B ρ P (gf ω) (gi ω) φ τ x.1 with hg
  have hsplit : ∀ ω, theta B ρ P (gf ω) (gi ω) φ τ = φ 0 + g ω := by
    intro ω
    have h := (hsum ω).tsum_subtype_add_tsum_subtype_compl ({0} : Set (ι → F))
    rw [tsum_singleton, thTerm_zero] at h
    exact h.symm
  have hgm : Measurable g :=
    measurable_of_tendsto_metrizable' Filter.atTop
      (f := fun (s : Finset {x : ι → F // x ≠ 0}) ω => ∑ x ∈ s, thTerm B ρ P (gf ω) (gi ω) φ τ x.1)
      (fun s => Finset.measurable_sum _ fun x _ => hmeas x.1)
      (tendsto_pi_nhds.2 fun ω => (hsub ω).hasSum)
  have hgI : ∫⁻ ω, ‖g ω‖ₑ ∂Pr ≤
      ∫⁻ ω, ∑' x : {x : ι → F // x ≠ 0}, ‖thTerm B ρ P (gf ω) (gi ω) φ τ x.1‖ₑ ∂Pr :=
    lintegral_mono fun ω => enorm_tsum_le_tsum_enorm
  have hgint : Integrable g Pr := ⟨hgm.aestronglyMeasurable, lt_of_le_of_lt hgI hfin.lt_top⟩
  have hth : (fun ω => theta B ρ P (gf ω) (gi ω) φ τ) = fun ω => φ 0 + g ω := funext hsplit
  refine ⟨by rw [hth]; exact (integrable_const _).add hgint, ?_⟩
  have hint : (∫ ω, theta B ρ P (gf ω) (gi ω) φ τ ∂Pr) - φ 0 = ∫ ω, g ω ∂Pr := by
    rw [hth, integral_add (integrable_const _) hgint]
    simp
  rw [hint, ofReal_norm_eq_enorm]
  exact (enorm_integral_le_lintegral_enorm g).trans hgI

end GlobalTheory.CompanionTheory.SW.Core.ThetaIntegral
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaIntegralOverCoordinates
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.BB.PullCoord

theorem lintegral_thetaMeas_coord : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (S : Set (Fin M × Fin d → F)) (T : Set (Fin 1 → Fin M → E)), (∀ x, ofF b x ∈ T ↔ x ∈ S) → ∀ Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℝ≥0∞, Measurable Φ → ∫⁻ X, Φ X ∂(thetaMeas σ J μ 𝓕 T) = ∫⁻ ω, ∑' x : S, Φ (actW (AF F) σ J ω⁻¹ (ratTup (AF F) (ofF b x.1))) ∂(prH μ 𝓕) := by
  intro F E _ _ _ _ _ σ hσ M J hJ d b μ 𝓕 hμ h𝓕 S T hST Φ hΦ
  rw [GlobalTheory.T.siegel_mean_value_nonnegative F E σ hσ M J hJ μ 𝓕 hμ h𝓕 1 T Φ hΦ]
  have hb := RatCoord.ofF_bijective (M := M) b
  let e : S ≃ T := Equiv.ofBijective (fun x => ⟨ofF b x.1, (hST x.1).2 x.2⟩) (by
    constructor
    · intro x y hxy
      exact Subtype.ext (hb.1 (congrArg Subtype.val hxy))
    · intro y
      obtain ⟨x, hx⟩ := hb.2 y.1
      exact ⟨⟨x, (hST x).1 (hx ▸ y.2)⟩, Subtype.ext hx⟩)
  have hsum : ∀ h : HA (AF F) σ J,
      ∑' X : T, Φ (actW (AF F) σ J h⁻¹ (ratTup (AF F) (X : Fin 1 → Fin M → E)))
        = ∑' x : S, Φ (actW (AF F) σ J h⁻¹ (ratTup (AF F) (ofF b x.1))) := fun h =>
    (e.tsum_eq (fun X : T =>
      Φ (actW (AF F) σ J h⁻¹ (ratTup (AF F) (X : Fin 1 → Fin M → E))))).symm
  simp only [hsum, prH, lintegral_smul_measure, smul_eq_mul]

end GlobalTheory.CompanionTheory.SW.BB.PullCoord
end

