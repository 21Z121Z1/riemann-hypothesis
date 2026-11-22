import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0017
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0012
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0005
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LatExistsSat
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0006
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0018
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsOrthogonalBasisDotProductApplyEq
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardHermitianMatricesDvdSqStatement
section
open GlobalTheory.GramCount
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_hermitian_matrices_dvd_sq : ∀ {A : Type} [CommRing A] [Finite A] (c : A →+* A), (∀ u, c (c u) = u) → ∀ (ω : A), IsUnit (ω - c ω) → ∀ (p : A), c p = p → ∀ (m : ℕ), Nat.card {H : Matrix (Fin m) (Fin m) A // (∀ a b, c (H b a) = H a b) ∧ ∀ a b, p ∣ H a b} ^ 2 = Nat.card {u : A // p ∣ u} ^ (m * m) := by
  first | exact @GlobalTheory.GramCount.card_hermitian_dvd_sq | exact GlobalTheory.GramCount.card_hermitian_dvd_sq | (intros; apply GlobalTheory.GramCount.card_hermitian_dvd_sq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousAtZeroOfSqueezePowBoundsStatement
section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuousAt_zero_of_squeeze_pow_bounds : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (d : ℕ) (f : V → ℝ≥0∞) (c : ℝ≥0∞), c ≠ ⊤ → (∀ ε : ℝ, 0 < ε → ε < 1 → ∃ η : ℝ, 0 < η ∧ ∀ x : V, ‖x‖ < η → ENNReal.ofReal ((1 + ε)⁻¹ ^ d) * c ≤ f x ∧ f x ≤ ENNReal.ofReal (((1 + ε) / (1 - ε)) ^ d) * c) → f 0 = c ∧ ContinuousAt f 0 := by
  first | exact @GlobalTheory.squeeze_continuousAt_zero | exact GlobalTheory.squeeze_continuousAt_zero | (intros; apply GlobalTheory.squeeze_continuousAt_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CumulantLowerBoundOfBoundedCentred
section
open Matrix Finset Real

namespace GlobalTheory

theorem cumulant_lower_bound_of_bounded_centred :
    ∀ (ι : Type) [Fintype ι] (w y : ι → ℝ) (R : ℝ), 0 < R → (∀ J, 0 ≤ w J) → ∑ J, w J = 1 →
      ∑ J, w J * y J = 0 → (∀ J, w J ≠ 0 → |y J| ≤ R) →
      min 1 (1 / R) * (∑ J, w J * y J ^ 2) / 4 ≤ Real.log (∑ J, w J * Real.exp (y J)) := by
  intro ι _ w y R hR hw hs hm hb
  obtain ⟨hexp, hlog⟩ := GlobalTheory.T.exp_quadratic_lower_and_log_linear_lower'
  set t : ℝ := min 1 (1 / R) with ht
  set V : ℝ := ∑ J, w J * y J ^ 2 with hV
  set S : ℝ := ∑ J, w J * Real.exp (y J) with hS
  have ht0 : 0 < t := lt_min one_pos (by positivity)
  have ht1 : t ≤ 1 := min_le_left _ _
  have htR : t * R ≤ 1 := by
    have : t ≤ 1 / R := min_le_right _ _
    rwa [le_div_iff₀ hR] at this
  have hty : ∀ J, w J ≠ 0 → |t * y J| ≤ 1 := by
    intro J hJ
    rw [abs_mul, abs_of_pos ht0]
    exact (mul_le_mul_of_nonneg_left (hb J hJ) ht0.le).trans htR
  have hV0 : 0 ≤ V := Finset.sum_nonneg fun J _ => mul_nonneg (hw J) (sq_nonneg _)
  have htV : t ^ 2 * V ≤ 1 := by
    rw [hV, Finset.mul_sum, ← hs]
    refine Finset.sum_le_sum fun J _ => ?_
    by_cases hJ : w J = 0
    · simp [hJ]
    · have h1 : (t * y J) ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one _).2 (hty J hJ)
      have := mul_le_mul_of_nonneg_left h1 (hw J)
      nlinarith
  have hlow : 1 + t ^ 2 * V / 3 ≤ ∑ J, w J * Real.exp (t * y J) := by
    have e : 1 + t ^ 2 * V / 3 = ∑ J, w J * (1 + t * y J + (t * y J) ^ 2 / 3) := by
      have e2 : ∀ J, w J * (1 + t * y J + (t * y J) ^ 2 / 3)
          = w J + t * (w J * y J) + t ^ 2 / 3 * (w J * y J ^ 2) := fun J => by ring
      simp only [e2, Finset.sum_add_distrib, ← Finset.mul_sum, hs, hm]
      rw [← hV]; ring
    rw [e]
    refine Finset.sum_le_sum fun J _ => ?_
    by_cases hJ : w J = 0
    · simp [hJ]
    · exact mul_le_mul_of_nonneg_left (hexp _ (hty J hJ)) (hw J)
  have hS1 : 1 ≤ S := by
    have : ∑ J, w J * (y J + 1) = 1 := by
      simp only [mul_add, mul_one, Finset.sum_add_distrib, hs, hm, zero_add]
    rw [← this]
    exact Finset.sum_le_sum fun J _ =>
      mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) (hw J)
  have hS0 : 0 < S := by linarith
  set F : ℝ := Real.log S with hF
  have hEF : Real.exp F = S := Real.exp_log hS0
  have hpt : ∀ J, Real.exp (t * y J)
      ≤ Real.exp (t * F) * (t * (Real.exp (y J) / S) + (1 - t)) := by
    intro J
    have h := convexOn_exp.2 (Set.mem_univ (y J - F)) (Set.mem_univ 0) ht0.le
      (sub_nonneg.2 ht1) (by ring)
    simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one] at h
    rw [Real.exp_sub, hEF] at h
    have e : t * y J = t * F + t * (y J - F) := by ring
    rw [e, Real.exp_add]
    exact mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
  have hup : ∑ J, w J * Real.exp (t * y J) ≤ Real.exp (t * F) := by
    calc ∑ J, w J * Real.exp (t * y J)
        ≤ ∑ J, w J * (Real.exp (t * F) * (t * (Real.exp (y J) / S) + (1 - t))) :=
          Finset.sum_le_sum fun J _ => mul_le_mul_of_nonneg_left (hpt J) (hw J)
      _ = ∑ J, (Real.exp (t * F) * t / S * (w J * Real.exp (y J))
            + Real.exp (t * F) * (1 - t) * w J) :=
          Finset.sum_congr rfl fun J _ => by ring
      _ = Real.exp (t * F) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hs, ← hS]
          field_simp
          ring
  have hu0 : 0 ≤ t ^ 2 * V / 3 := by positivity
  have h1 := hlog (t ^ 2 * V / 3) hu0 (by linarith)
  have h2 : Real.log (1 + t ^ 2 * V / 3) ≤ t * F := by
    rw [Real.log_le_iff_le_exp (by linarith)]
    exact hlow.trans hup
  have h3 : t * (t * V / 4) ≤ t * F := by nlinarith
  exact le_of_mul_le_mul_left h3 ht0

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMassOneCutoffDoubleCosetIntegral
section
open MeasureTheory

namespace GlobalTheory.StabUnfold

open MeasureTheory in
open scoped ENNReal in

theorem _root_.GlobalTheory.StabUnfold.exists_cutoff_doubleCoset : ∀ (G H : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] (μ : Measure G) [μ.IsHaarMeasure] (ν : Measure H) [ν.IsHaarMeasure] [ν.IsMulRightInvariant] (j : H →* G), Topology.IsClosedEmbedding j → ∀ (K : Subgroup G) (K' : Subgroup H) (x : G) (S : Set G), IsOpen (K : Set G) → IsOpen (K' : Set H) → IsCompact (K' : Set H) → (∀ h, h ∈ K' ↔ x⁻¹ * j h * x ∈ K) → (∀ g, g ∈ S ↔ ∃ h, ∃ k ∈ K, g = j h * x * k) → ∃ b : G → ENNReal, Measurable b ∧ (∀ g, ∫⁻ h, b (j h * g) ∂ν = 1) ∧ ∫⁻ g, S.indicator 1 g * b g ∂μ = μ K / ν K' := by
  intro G H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ _ ν _ _ j hj K K' x S hK hK'o hK'c hK'K hS
  obtain ⟨b₀, hb₀m, hb₀⟩ := _root_.GlobalTheory.exists_measurable_lintegral_coset_eq_one G H ν j hj
  have hSeq : S = ⋃ h : H, (fun g => j h * x * g) '' (K : Set G) := by
    ext g
    rw [hS g]
    simp only [Set.mem_iUnion, Set.mem_image, SetLike.mem_coe]
    constructor <;> rintro ⟨h, k, hk, e⟩ <;> exact ⟨h, k, hk, e.symm⟩
  have hSopen : IsOpen S := by
    rw [hSeq]
    exact isOpen_iUnion fun h => isOpenMap_mul_left (j h * x) _ hK
  have hSm : MeasurableSet S := hSopen.measurableSet
  set T : Set G := (fun g => x⁻¹ * g) ⁻¹' (K : Set G) with hT_def
  have hTm : MeasurableSet T := measurable_const_mul x⁻¹ hK.measurableSet
  have hc0 : ν K' ≠ 0 := (hK'o.measure_pos ν ⟨1, K'.one_mem⟩).ne'
  have hcT : ν K' ≠ ∞ := hK'c.measure_lt_top.ne
  have hSinv : ∀ h g, j h * g ∈ S ↔ g ∈ S := by
    intro h g
    rw [hS, hS]
    constructor
    · rintro ⟨h', k, hk, e⟩
      refine ⟨h⁻¹ * h', k, hk, ?_⟩
      have e' : g = (j h)⁻¹ * (j h' * x * k) := by rw [← e]; group
      rw [e', map_mul, map_inv]; group
    · rintro ⟨h', k, hk, e⟩
      exact ⟨h * h', k, hk, by rw [e, map_mul]; group⟩
  have hTS : ∀ g, g ∈ T → g ∈ S := by
    intro g hg
    rw [hS]
    exact ⟨1, x⁻¹ * g, hg, by simp⟩
  have hcoset : ∀ g ∈ S, ∫⁻ h, T.indicator (fun _ => (ν K')⁻¹) (j h * g) ∂ν = 1 := by
    intro g hg
    obtain ⟨h0, k, hk, rfl⟩ := (hS g).1 hg
    have e : ∀ h, T.indicator (fun _ => (ν K')⁻¹) (j h * (j h0 * x * k))
        = (K' : Set H).indicator (fun _ => (ν K')⁻¹) (h * h0) := by
      intro h
      have hiff : j h * (j h0 * x * k) ∈ T ↔ h * h0 ∈ (K' : Set H) := by
        show x⁻¹ * (j h * (j h0 * x * k)) ∈ K ↔ h * h0 ∈ K'
        rw [hK'K, map_mul]
        have e2 : x⁻¹ * (j h * (j h0 * x * k)) = x⁻¹ * (j h * j h0) * x * k := by group
        rw [e2, Subgroup.mul_mem_cancel_right _ hk]
      by_cases hm : h * h0 ∈ (K' : Set H)
      · rw [Set.indicator_of_mem hm, Set.indicator_of_mem (hiff.2 hm)]
      · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem (mt hiff.1 hm)]
    calc ∫⁻ h, T.indicator (fun _ => (ν K')⁻¹) (j h * (j h0 * x * k)) ∂ν
        = ∫⁻ h, (K' : Set H).indicator (fun _ => (ν K')⁻¹) (h * h0) ∂ν := lintegral_congr e
      _ = ∫⁻ h, (K' : Set H).indicator (fun _ => (ν K')⁻¹) h ∂ν :=
          lintegral_mul_right_eq_self (fun h => (K' : Set H).indicator (fun _ => (ν K')⁻¹) h) h0
      _ = 1 := by rw [lintegral_indicator_const hK'o.measurableSet, ENNReal.inv_mul_cancel hc0 hcT]
  have hzero : ∀ g, g ∉ S → ∫⁻ h, T.indicator (fun _ => (ν K')⁻¹) (j h * g) ∂ν = 0 := by
    intro g hg
    have e : ∀ h, T.indicator (fun _ => (ν K')⁻¹) (j h * g) = 0 := fun h =>
      Set.indicator_of_notMem (fun hT => hg ((hSinv h g).1 (hTS _ hT))) _
    simp [e]
  have hjg : ∀ g, Measurable fun h => j h * g := fun g => hj.continuous.measurable.mul_const g
  refine ⟨fun g => T.indicator (fun _ => (ν K')⁻¹) g + Sᶜ.indicator b₀ g,
    (measurable_const.indicator hTm).add (hb₀m.indicator hSm.compl), fun g => ?_, ?_⟩
  · dsimp only
    rw [lintegral_add_left (show Measurable fun h => T.indicator (fun _ => (ν K')⁻¹) (j h * g)
      from (measurable_const.indicator hTm).comp (hjg g))]
    by_cases hg : g ∈ S
    · have e : ∀ h, Sᶜ.indicator b₀ (j h * g) = 0 := fun h =>
        Set.indicator_of_notMem (show j h * g ∉ Sᶜ from fun hc => hc ((hSinv h g).2 hg)) _
      simp only [e, lintegral_zero, add_zero]
      exact hcoset g hg
    · have e : ∀ h, Sᶜ.indicator b₀ (j h * g) = b₀ (j h * g) := fun h =>
        Set.indicator_of_mem (show j h * g ∈ Sᶜ from fun hs => hg ((hSinv h g).1 hs)) _
      rw [hzero g hg, zero_add]
      simp only [e]
      exact hb₀ g
  · have e : ∀ g, S.indicator 1 g * (T.indicator (fun _ => (ν K')⁻¹) g + Sᶜ.indicator b₀ g)
        = T.indicator (fun _ => (ν K')⁻¹) g := by
      intro g
      by_cases hg : g ∈ S
      · simp [hg]
      · have hgT : g ∉ T := fun hT => hg (hTS g hT)
        simp [hg, hgT]
    rw [lintegral_congr e, lintegral_indicator_const hTm, hT_def, measure_preimage_mul,
      ENNReal.div_eq_inv_mul]

end GlobalTheory.StabUnfold
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMemFractionalIdealPrimitiveLocalGeneratorA
section
open NumberField IsDedekindDomain

namespace GlobalTheory
open Formalism.L2.SG.Pf.LatEx

theorem fractionalIdeal_restrictScalars_isLattice_of_tower (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (c : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hc : c ≠ 0) :
    Submodule.IsLattice F ((c : Submodule (𝓞 E) E).restrictScalars (𝓞 F)) := by
  refine ⟨?_, ?_⟩
  · exact (FractionalIdeal.fg_of_isNoetherianRing le_rfl c).restrictScalars
  · obtain ⟨x, hxc, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := (c : Submodule (𝓞 E) E))
      (by rwa [Ne, FractionalIdeal.coeToSubmodule_eq_bot])
    rw [eq_top_iff]
    intro y _
    obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 E)) (y / x)
    dsimp only at hrs
    have hs0 : (s : 𝓞 E) ≠ 0 := nonZeroDivisors.coe_ne_zero s
    have hspan : Ideal.span {(s : 𝓞 E)} ≠ ⊥ := by simpa using hs0
    have hm0 : Ideal.absNorm (Ideal.span {(s : 𝓞 E)}) ≠ 0 := by
      rwa [Ne, Ideal.absNorm_eq_zero_iff]
    obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {(s : 𝓞 E)}))
    set m := Ideal.absNorm (Ideal.span {(s : 𝓞 E)})
    have hmem : (algebraMap (𝓞 E) E (u * r)) * x ∈ c :=
      (c : Submodule (𝓞 E) E).smul_mem (u * r) hxc
    have hyeq : y = ((m : F)⁻¹) • ((algebraMap (𝓞 E) E (u * r)) * x) := by
      have hu' : algebraMap (𝓞 E) E u * algebraMap (𝓞 E) E s = (m : E) := by
        rw [← map_mul, hu, map_natCast]
      have hmE : (m : E) ≠ 0 := Nat.cast_ne_zero.mpr hm0
      rw [Algebra.smul_def, map_inv₀, map_natCast, map_mul]
      have hyx : y = algebraMap (𝓞 E) E r / algebraMap (𝓞 E) E s * x := by
        have hsE : algebraMap (𝓞 E) E s ≠ 0 := by simpa using hs0
        rw [← hrs]; field_simp
      rw [hyx, ← hu']
      have hsE : algebraMap (𝓞 E) E s ≠ 0 := by simpa using hs0
      have huE : algebraMap (𝓞 E) E u ≠ 0 := by
        intro h; rw [h, zero_mul] at hu'; exact hmE hu'.symm
      field_simp
    rw [hyeq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

theorem exists_basis_latSpanV_eq_of_finrank_two (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (hE : Module.finrank F E = 2) (c : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hc : c ≠ 0) :
    ∃ (e : Fin 2 → E) (b : FractionalIdeal (nonZeroDivisors (𝓞 F)) F), LinearIndependent F e ∧ b ≠ 0 ∧
      (c : Submodule (𝓞 E) E).restrictScalars (𝓞 F) =
        latSpanV (Fin.snoc (α := fun _ => FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (fun _ => 1) b) e := by
  have hL := fractionalIdeal_restrictScalars_isLattice_of_tower F E c hc
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hE
  let w := Module.finBasisOfFinrankEq F E hE
  obtain ⟨e, b, he, -, hb, heq⟩ := satBasisV_holds F E _ hL 1 w w.linearIndependent (fun _ => 1)
    (fun _ => one_ne_zero)
  refine ⟨e, b, he, hb, ?_⟩
  rw [← heq, w.span_eq]
  simp

theorem basis_repr_mem_of_mem_latSpanV_two {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (B : Module.Basis (Fin 2) F E) (C : Fin 2 → FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
    {z : E} (hz : z ∈ latSpanV C B) (i : Fin 2) : B.repr z i ∈ C i := by
  induction hz using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, x, hx, rfl⟩ := hy
    rw [map_smul, B.repr_self, Finsupp.smul_apply, Finsupp.single_apply]
    split_ifs with h
    · subst h; simpa using hx
    · rw [smul_zero]; exact (C i : Submodule (𝓞 F) F).zero_mem
  | zero => rw [map_zero, Finsupp.zero_apply]; exact (C i : Submodule (𝓞 F) F).zero_mem
  | add x y _ _ hx hy =>
    rw [map_add, Finsupp.add_apply]; exact (C i : Submodule (𝓞 F) F).add_mem hx hy
  | smul r x _ hx =>
    rw [← algebraMap_smul F r x, map_smul, Finsupp.smul_apply, algebraMap_smul]
    exact (C i : Submodule (𝓞 F) F).smul_mem r hx

theorem algebraMap_ringOfIntegers_tower_mul_eq_smul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (π : 𝓞 F) (z : E) :
    algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) π) * z = (algebraMap (𝓞 F) F π) • z := by
  rw [Algebra.smul_def, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

theorem basis_repr_mem_of_mem_map_mul_two {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (B : Module.Basis (Fin 2) F E) (C : Fin 2 → FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
    (c : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
    (hc : (c : Submodule (𝓞 E) E).restrictScalars (𝓞 F) = latSpanV C B) (p : Ideal (𝓞 F)) {a : E}
    (ha : a ∈ ((Ideal.map (algebraMap (𝓞 F) (𝓞 E)) p : Ideal (𝓞 E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c) (i : Fin 2) :
    B.repr a i ∈ (p : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) * C i := by
  let T : Submodule (𝓞 F) F := (↑((p : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) * C i) : Submodule (𝓞 F) F)
  have hcoord : ∀ z ∈ c, B.repr z i ∈ C i := fun z hz =>
    basis_repr_mem_of_mem_latSpanV_two B C (by rw [← hc]; exact hz) i
  have hgen : ∀ π ∈ p, ∀ z ∈ c,
      B.repr (algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) π) * z) i ∈ T := by
    intro π hπ z hz
    rw [algebraMap_ringOfIntegers_tower_mul_eq_smul, map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _ hπ) (hcoord z hz)
  have hq : ∀ q ∈ Ideal.map (algebraMap (𝓞 F) (𝓞 E)) p, ∀ z ∈ c,
      B.repr (algebraMap (𝓞 E) E q * z) i ∈ T := by
    intro q hq
    induction hq using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨π, hπ, rfl⟩ := hy
      exact hgen π hπ
    | zero => intro z _; simp [T.zero_mem]
    | add x y _ _ hx hy =>
      intro z hz; rw [map_add, add_mul, map_add, Finsupp.add_apply]; exact T.add_mem (hx z hz) (hy z hz)
    | smul r x _ hx =>
      intro z hz
      have e1 : algebraMap (𝓞 E) E (r * x) * z = algebraMap (𝓞 E) E x * (algebraMap (𝓞 E) E r * z) := by
        rw [RingHom.map_mul]; ring
      rw [smul_eq_mul, e1]
      exact hx _ ((c : Submodule (𝓞 E) E).smul_mem r hz)
  refine FractionalIdeal.mul_induction_on (C := fun a => B.repr a i ∈ T) ha ?_ ?_
  · intro u hu z hz
    obtain ⟨q, hq', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hu
    exact hq q hq' z hz
  · intro x y hx hy
    simp only [map_add, Finsupp.add_apply]
    exact T.add_mem hx hy

theorem mem_map_mul_of_basis_repr_mem_two {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (B : Module.Basis (Fin 2) F E) (C : Fin 2 → FractionalIdeal (nonZeroDivisors (𝓞 F)) F)
    (c : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
    (hc : (c : Submodule (𝓞 E) E).restrictScalars (𝓞 F) = latSpanV C B) (p : Ideal (𝓞 F)) {a : E}
    (ha : ∀ i, B.repr a i ∈ (p : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) * C i) :
    a ∈ ((Ideal.map (algebraMap (𝓞 F) (𝓞 E)) p : Ideal (𝓞 E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c := by
  let M : Submodule (𝓞 E) E := (↑(((Ideal.map (algebraMap (𝓞 F) (𝓞 E)) p : Ideal (𝓞 E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c) : Submodule (𝓞 E) E)
  have hterm : ∀ i, B.repr a i • B i ∈ M := by
    intro i
    refine FractionalIdeal.mul_induction_on (C := fun u => u • B i ∈ M) (ha i) ?_ ?_
    · intro u hu x hx
      obtain ⟨π, hπ, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hu
      have hxc : x • B i ∈ c := by
        have : x • B i ∈ latSpanV C B := Submodule.subset_span ⟨i, x, hx, rfl⟩
        rw [← hc] at this; exact this
      show (algebraMap (𝓞 F) F π * x) • B i ∈ M
      rw [mul_smul, ← algebraMap_ringOfIntegers_tower_mul_eq_smul]
      exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _
        (Ideal.mem_map_of_mem _ hπ)) hxc
    · intro x y hx hy
      show (x + y) • B i ∈ M
      rw [add_smul]; exact M.add_mem hx hy
  have hsum := B.sum_repr a
  rw [Fin.sum_univ_two] at hsum
  show a ∈ M
  rw [← hsum]
  exact M.add_mem (hterm 0) (hterm 1)

theorem exists_mem_fractionalIdeal_primitive_local_generator : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Module.finrank F E = 2 → ∀ (c : FractionalIdeal (nonZeroDivisors (𝓞 E)) E), c ≠ 0 → ∀ N : 𝓞 E, N ≠ 0 → ∃ a : E, a ∈ c ∧ (∀ Q : Ideal (𝓞 E), Q.IsMaximal → N ∈ Q → a ∉ (Q : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c) ∧ ∀ p : Ideal (𝓞 F), p.IsMaximal → a ∉ ((Ideal.map (algebraMap (𝓞 F) (𝓞 E)) p : Ideal (𝓞 E)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c := by
  intro F E _ _ _ _ _ hE c hc N hN
  obtain ⟨e, b, he, hb, hce⟩ := exists_basis_latSpanV_eq_of_finrank_two F E hE c hc
  let B : Module.Basis (Fin 2) F E := basisOfLinearIndependentOfCardEqFinrank he (by simp [hE])
  have hBe : ⇑B = e := coe_basisOfLinearIndependentOfCardEqFinrank he _
  let C : Fin 2 → FractionalIdeal (nonZeroDivisors (𝓞 F)) F := Fin.snoc (n := 1) (α := fun _ => FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (fun _ => 1) b
  have hc' : (c : Submodule (𝓞 E) E).restrictScalars (𝓞 F) = latSpanV C B := by rw [hBe]; exact hce
  have hC0 : C 0 = 1 := rfl
  have hC1 : C 1 = b := rfl
  have hspanN : Ideal.span {N} ≠ ⊥ := by simpa using hN
  have hm0 : Ideal.absNorm (Ideal.span {N}) ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
  have hmN : ((Ideal.absNorm (Ideal.span {N}) : ℕ) : 𝓞 E) ∈ Ideal.span {N} := Ideal.absNorm_mem _
  set m := Ideal.absNorm (Ideal.span {N})
  obtain ⟨a₀, ha₀c, ha₀⟩ := GlobalTheory.T.exists_mem_fractionalIdeal_generator_at_primes_over' E c hc (m : 𝓞 E) (Nat.cast_ne_zero.mpr hm0)
  have hco : ∀ i, B.repr a₀ i ∈ C i := fun i =>
    basis_repr_mem_of_mem_latSpanV_two B C (show a₀ ∈ latSpanV C B by rw [← hc']; exact ha₀c) i
  obtain ⟨x₀, hx₀⟩ := (FractionalIdeal.mem_one_iff _).mp (hC0 ▸ hco 0)
  have hy₀ : B.repr a₀ 1 ∈ b := hC1 ▸ hco 1
  have hinj : Function.Injective (algebraMap (𝓞 F) (𝓞 E)) := FaithfulSMul.algebraMap_injective _ _
  have hmono : ∀ (I J : Ideal (𝓞 E)), I ≤ J → (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c ≤
      (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c := by
    intro I J hIJ
    have : (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≤ J := (FractionalIdeal.coeIdeal_le_coeIdeal E).mpr hIJ
    gcongr
  obtain ⟨s, t, ht, hst⟩ := GlobalTheory.exists_unimodular_lift_of_unimodular_mod F b hb (m : 𝓞 F) x₀ (B.repr a₀ 1)
    (Nat.cast_ne_zero.mpr hm0) hy₀ (by
      rintro p hp hnp ⟨hxp, hyp⟩
      have hmem := mem_map_mul_of_basis_repr_mem_two B C c hc' p (a := a₀) (by
        refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
        · rw [← hx₀, hC0, mul_one]; exact FractionalIdeal.mem_coeIdeal_of_mem _ hxp
        · exact hyp)
      obtain ⟨Q, hQ, hQp⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 E) p (by
        rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]; exact bot_le)
      have hle : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) p ≤ Q := Ideal.map_le_iff_le_comap.mpr hQp.ge
      have hmQ : (m : 𝓞 E) ∈ Q := hle (by
        rw [← map_natCast (algebraMap (𝓞 F) (𝓞 E)) m]; exact Ideal.mem_map_of_mem _ hnp)
      exact ha₀ Q hQ hmQ (hmono _ _ hle hmem))
  let w : E := (algebraMap (𝓞 F) F s) • B 0 + t • B 1
  have hw : w ∈ c := by
    have : w ∈ latSpanV C B := Submodule.add_mem _
      (Submodule.subset_span ⟨0, _, (FractionalIdeal.mem_one_iff _).mpr ⟨s, rfl⟩, rfl⟩)
      (Submodule.subset_span ⟨1, t, ht, rfl⟩)
    rw [← hc'] at this; exact this
  have hmw : (m : F) • w = algebraMap (𝓞 E) E (m : 𝓞 E) * w := by
    rw [map_natCast, ← nsmul_eq_mul, Nat.cast_smul_eq_nsmul]
  refine ⟨a₀ + (m : F) • w, ?_, ?_, ?_⟩
  · rw [hmw]; exact (c : Submodule (𝓞 E) E).add_mem ha₀c ((c : Submodule (𝓞 E) E).smul_mem _ hw)
  · intro Q hQ hNQ ha
    have hmQ : (m : 𝓞 E) ∈ Q := (Ideal.span_singleton_le_iff_mem Q).mpr hNQ hmN
    have h2 : (m : F) • w ∈ (Q : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c := by
      rw [hmw]; exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _ hmQ) hw
    refine ha₀ Q hQ hmQ ?_
    have e2 : a₀ = (a₀ + (m : F) • w) - (m : F) • w := by abel
    rw [e2]
    exact Submodule.sub_mem (↑((Q : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c) : Submodule (𝓞 E) E) ha h2
  · intro p hp ha
    have h := basis_repr_mem_of_mem_map_mul_two B C c hc' p ha
    have hr : ∀ i, B.repr (a₀ + (m : F) • w) i = B.repr a₀ i + (m : F) * ((algebraMap (𝓞 F) F s) *
        (Finsupp.single 0 1 : Fin 2 →₀ F) i + t * (Finsupp.single 1 1 : Fin 2 →₀ F) i) := by
      intro i
      simp only [w, map_add, map_smul, B.repr_self, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    refine hst p hp ⟨?_, ?_⟩
    · have h0 := h 0
      rw [hC0, mul_one, hr 0] at h0
      obtain ⟨x', hx'p, hx'⟩ := (FractionalIdeal.mem_coeIdeal _).mp h0
      have : x' = x₀ + (m : 𝓞 F) * s := by
        apply IsFractionRing.injective (𝓞 F) F
        rw [hx', map_add, map_mul, map_natCast, hx₀]
        simp
      exact this ▸ hx'p
    · have h1 := h 1
      rw [hC1, hr 1] at h1
      convert h1 using 1
      simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsPrimitiveAddCharInvolutionInvariantStatement
section
open GlobalTheory.GramCount
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_primitive_addChar_involution_invariant : ∀ {B : Type} [CommRing B] [Fintype B] (c : B →+* B), (∀ u, c (c u) = u) → ∀ (ω : B), IsUnit (ω - c ω) → (∀ t, c t = t → t ≠ 0 → IsUnit t) → ∃ χ : AddChar B ℂ, χ.IsPrimitive ∧ ∀ u, χ (c u) = χ u := by
  first | exact @GlobalTheory.GramCount.exists_isPrimitive_invol_invariant | exact GlobalTheory.GramCount.exists_isPrimitive_invol_invariant | (intros; apply GlobalTheory.GramCount.exists_isPrimitive_invol_invariant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsTupleGramDetNeZero
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.NondegTuple

theorem conj_conj {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2 τ, h.2.2.2 τ, star_star]

theorem exists_tuple_gram_det_ne_zero :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
      (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
      ∀ a : ℕ, a ≤ n → ∃ X0 : Fin a → Fin n → E, (gramE σ J X0).det ≠ 0 ∧
        ∀ i j, σ (gramE σ J X0 j i) = gramE σ J X0 i j := by
  intro F E _ _ _ _ _ σ hσ n J hJ a ha
  have hc : ∀ t, (σ : E →+* E) ((σ : E →+* E) t) = t := conj_conj hσ
  obtain ⟨P, d, -, hd, hfix, hne⟩ := GlobalTheory.HermDiag.exists_congr_diagonal (c := (σ : E →+* E))
    (G := J) two_ne_zero hc (fun i j => hJ.1 j i)
  have hg : gramE σ J (fun i k => σ (P k (Fin.castLE ha i))) =
      Matrix.diagonal fun i => d (Fin.castLE ha i) := by
    ext i j
    have h1 := congrFun (congrFun hd (Fin.castLE ha i)) (Fin.castLE ha j)
    rw [GlobalTheory.HermDiag.transpose_mul_mul_map_apply,
      GlobalTheory.HermDiag.dotProduct_mulVec_comp_eq_sum] at h1
    have h2 : Matrix.diagonal d (Fin.castLE ha i) (Fin.castLE ha j) =
        Matrix.diagonal (fun i => d (Fin.castLE ha i)) i j := by
      simp only [Matrix.diagonal_apply, (Fin.castLE_injective ha).eq_iff]
    rw [← h2, ← h1]
    simp only [gramE, hE, Formalism.UG.hform, RingHom.coe_coe, conj_conj hσ]
  refine ⟨fun i k => σ (P k (Fin.castLE ha i)), ?_, ?_⟩
  · rw [hg, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun i _ => hne hJ.2 _
  · intro i j
    rw [hg]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq]
      exact hfix _
    · rw [Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ (Ne.symm hij), map_zero]

end GlobalTheory.NondegTuple
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFieldOrExistsSwappedIdempotentOfQuadraticEtaleStatement
section
open GlobalTheory.SgAlg Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isField_or_exists_swapped_idempotent_of_quadraticEtale : ∀ {E : Type} [CommRing E] (σ : E →+* E), IsQA σ → IsField E ∨ ∃ e : E, e * e = e ∧ e + σ e = 1 ∧ ∀ x : E, e * x ≠ 0 → ∃ y, e * x * y = e := by
  first | exact @GlobalTheory.SgAlg.isField_or_exists_idempotent_of_isQA | exact GlobalTheory.SgAlg.isField_or_exists_idempotent_of_isQA | (intros; apply GlobalTheory.SgAlg.isField_or_exists_idempotent_of_isQA <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrimitiveTupleOfLinearIndependentFiniteRingStatement
section
open GlobalTheory.GramCount
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPrimitiveTuple_of_linearIndependent_finite_ring : ∀ {B : Type} [CommRing B] [Fintype B] (c : B →+* B), (∀ u, c (c u) = u) → ∀ (χ : AddChar B ℂ), χ.IsPrimitive → ∀ (k n : ℕ) (x : Fin k → Fin n → B), (∀ s : Fin k → B, ∑ a, s a • x a = 0 → s = 0) → Prim c x := by
  first | exact @GlobalTheory.GramCount.prim_of_indep_of_isPrimitive | exact GlobalTheory.GramCount.prim_of_indep_of_isPrimitive | (intros; apply GlobalTheory.GramCount.prim_of_indep_of_isPrimitive <;> assumption)
end

