import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0910
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0901
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth
import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0911
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0904
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0931
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0923
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0924
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0921
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0878
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumWIffGoodFormsOrthSum
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0022
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0070
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0597
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0165
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicGLComplementarySupportsCommuteStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicGL_complementary_supports_commute : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (h t : GA E a), h ∈ GlobalTheory.JSW.supS E a S → GeneralLinearGroup.map (pInf E) t = 1 → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) t = 1) → h * t = t * h := by
  first | exact @GlobalTheory.JSW.MirSemi.supS_mul_comm | exact GlobalTheory.JSW.MirSemi.supS_mul_comm | (intros; apply GlobalTheory.JSW.MirSemi.supS_mul_comm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicLatticeOrderCoprimeIndexStatement
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_lattice_order_coprime_index : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime →
    ∀ y : (Af E)ˣ, (∀ P : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ P.asIdeal → (y : Af E) P = 1) →
    ∃ n : ℕ, n.Coprime l ∧ (∀ x ∈ lattice c y, (n : E) * x ∈ orderC c) ∧ ∀ x ∈ orderC c, (n : E) * x ∈ lattice c y := by
  first | exact @GlobalTheory.CMVal.LatLoc.lattice_near_orderC | exact GlobalTheory.CMVal.LatLoc.lattice_near_orderC | (intros; apply GlobalTheory.CMVal.LatLoc.lattice_near_orderC <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdmissibleConstantsClosedUnderSizeBounds
section
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

namespace GlobalTheory

theorem admissibleConstants_closed_under_sizeBounds : ∀ (𝒞 : FamClass), (∀ {eps : ℝ} (Fm : FamP eps), 𝒞 Fm → TuSize Fm ∧ DGamSize Fm) →
    Closed 𝒞 (fun Fm _ => Formalism.MainNotions.WeightDegreeSizes.FamilySecondComplementInputs Fm) := by
  intro 𝒞 h𝒞
  refine ⟨1 / 100, by norm_num, fun eps he hle => ?_⟩
  have hK : Nonempty TransportedAlt := ⟨by constructor <;> exact 0⟩
  obtain ⟨K⟩ := hK
  refine ⟨K, fun Fm _ hc _ => ?_⟩
  have hlt : eps < 1 / 52 := lt_of_le_of_lt hle (by norm_num)
  exact GlobalTheory.T.admissibleComplementTwo_along_family Fm he hlt (h𝒞 Fm hc).1 (h𝒞 Fm hc).2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanKernelSpanCuspFormRightInvariantOpenStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanKernelSpan_cuspForm_right_invariant_open : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (π : CuspSub E a) (φ : Sm E a), φ ∈ π.V → ∀ F ∈ GlobalTheory.JSW.MirSemi.locSpan S φ.1, ∃ U : Subgroup (GL (Fin a) (Af E)), IsOpen (U : Set (GL (Fin a) (Af E))) ∧ ∀ u ∈ U, ∀ g, F (g * finGL E a u) = F g := by
  first | exact @GlobalTheory.JSW.MirSemi.locSpan_openInv | exact GlobalTheory.JSW.MirSemi.locSpan_openInv | (intros; apply GlobalTheory.JSW.MirSemi.locSpan_openInv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanMatrixSmoothingModerateGrowth
section
open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW.MirCinf

theorem smoothMatInf_keeps_modGrowth : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ)
    (α : (Fin n → Fin n → Cinf E) → ℂ), Continuous α → HasCompactSupport α →
    tsupport α ⊆ {x | IsUnit (Matrix.of x)} → ∀ W : GL (Fin n) (Cinf E) → ℂ, IsModGrowthInf W →
    IsModGrowthInf (smoothMatInf α W) :=
  isModGrowthInf_smoothMatInf

end GlobalTheory.JSW.MirCinf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanRapidKernelOperatorCompRapidFamily
section
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW.MirCinf

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem measurable_htInf_comp {X : Type} [MeasurableSpace X] {γ : X → GL (Fin n) (Cinf E)}
    (hγ : ∀ i j, Measurable fun x => (γ x : Matrix (Fin n) (Fin n) (Cinf E)) i j) :
    Measurable fun x => htInf (γ x) := by
  unfold htInf
  refine Finset.measurable_prod _ fun w _ => ?_
  exact measurable_comp_GL (F := htGL) continuous_htGL fun i j => (measurable_pi_apply w).comp (hγ i j)

theorem isKerOpInf_comp_rapidFamInf : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (Z : Type) [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] (T : (GL (Fin n) (Cinf E) → ℂ) → Z → GL (Fin n) (Cinf E) → ℂ),
    IsKerOpInf T → ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : GL (Fin n) (Cinf E) → X → ℂ)
    (γ : X → GL (Fin n) (Cinf E)) (η : GL (Fin n) (Cinf E) → X → Z →L[ℝ] ℝ), IsRapidFamInf ν k γ η →
    ∀ (S : (GL (Fin n) (Cinf E) → ℂ) → GL (Fin n) (Cinf E) → ℂ) (t : Z → GL (Fin n) (Cinf E)) (χ : Z → ℂ),
    (∀ W, IsModGrowthInf W → IsModGrowthInf (S W)) →
    (∀ W, IsModGrowthInf W → ∀ q z g, χ z * S W (g * t z * q) = ∫ x, k q x * (𝐞 (η q x z) : ℂ) * W (g * γ x) ∂ν) →
    IsKerOpInf (fun W z g => χ z * T (S W) z (g * t z)) := by
  intro E _ _ n Z _ _ _ T hT X _ ν _ k γ η hfam S t χ hS hSk
  obtain ⟨X₀, m₀, ν₀, hν₀, k₀, γ₀, η₀, ⟨hk₀, hγ₀, hη₀, hint₀⟩, hT⟩ := hT
  obtain ⟨hγ, hjoint, hmom⟩ := hfam
  obtain ⟨hkj, hηj⟩ := hjoint X₀ γ₀ hγ₀
  have mη₀ : Measurable η₀ := measurable_dual hη₀
  have mηj : Measurable fun p : X₀ × X => η (γ₀ p.1) p.2 := measurable_dual hηj
  have mht : Measurable fun x => htInf (γ x) := measurable_htInf_comp hγ
  have hrap : IsRapidFInf (ν₀.prod ν) (fun p : X₀ × X => k₀ p.1 * k (γ₀ p.1) p.2) (fun p => γ p.2)
      (fun p => η₀ p.1 + η (γ₀ p.1) p.2) := by
    refine ⟨(hk₀.comp measurable_fst).mul hkj, fun i j => (hγ i j).comp measurable_snd,
      fun z => ((hη₀ z).comp measurable_fst).add (hηj z), fun N => ?_⟩
    obtain ⟨C, M, hCM⟩ := hmom N
    let F : X₀ × X → ℝ := fun p => (‖k₀ p.1‖ * (1 + ‖η₀ p.1‖) ^ N) *
      (‖k (γ₀ p.1) p.2‖ * (htInf (γ p.2) * (1 + ‖η (γ₀ p.1) p.2‖)) ^ N)
    have mF : Measurable F := by
      have a1 : Measurable fun p : X₀ × X => k₀ p.1 := hk₀.comp measurable_fst
      have a2 : Measurable fun p : X₀ × X => η₀ p.1 := mη₀.comp measurable_fst
      have a3 : Measurable fun p : X₀ × X => htInf (γ p.2) := mht.comp measurable_snd
      exact (a1.norm.mul ((measurable_const.add a2.norm).pow_const N)).mul
        (hkj.norm.mul ((a3.mul (measurable_const.add mηj.norm)).pow_const N))
    have F0 : ∀ p, 0 ≤ F p := fun p => by
      have := htInf_pos' (γ p.2)
      positivity
    have hF : Integrable F (ν₀.prod ν) := by
      rw [integrable_prod_iff mF.aestronglyMeasurable]
      refine ⟨Filter.Eventually.of_forall fun x₀ => ((hCM (γ₀ x₀)).1.const_mul (‖k₀ x₀‖ * (1 + ‖η₀ x₀‖) ^ N)), ?_⟩
      refine ((hint₀ (max N M)).const_mul (max C 0)).mono'
        (mF.norm.stronglyMeasurable.integral_prod_right').aestronglyMeasurable
        (Filter.Eventually.of_forall fun x₀ => ?_)
      have e1 : ∫ y, ‖F (x₀, y)‖ ∂ν = (‖k₀ x₀‖ * (1 + ‖η₀ x₀‖) ^ N) *
          ∫ y, ‖k (γ₀ x₀) y‖ * (htInf (γ y) * (1 + ‖η (γ₀ x₀) y‖)) ^ N ∂ν := by
        rw [← integral_const_mul]
        exact integral_congr_ae (Filter.Eventually.of_forall fun y => Real.norm_of_nonneg (F0 _))
      have I0 : 0 ≤ ∫ y, ‖F (x₀, y)‖ ∂ν := integral_nonneg fun _ => norm_nonneg _
      rw [Real.norm_of_nonneg I0, e1]
      have hq := (hCM (γ₀ x₀)).2
      have A0 : 0 ≤ ‖k₀ x₀‖ * (1 + ‖η₀ x₀‖) ^ N := by positivity
      have h1 : 1 ≤ htInf (γ₀ x₀) := le_of_eq_of_le rfl (by
        unfold htInf
        calc (1 : ℝ) = ∏ _w : InfinitePlace E, (1 : ℝ) := by simp
          _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) fun w _ => one_le_htGL _)
      have h2 : (1 : ℝ) ≤ 1 + ‖η₀ x₀‖ := by linarith [norm_nonneg (η₀ x₀)]
      have p1 : (1 + ‖η₀ x₀‖) ^ N ≤ (1 + ‖η₀ x₀‖) ^ max N M := pow_le_pow_right₀ h2 (le_max_left _ _)
      have p2 : htInf (γ₀ x₀) ^ M ≤ htInf (γ₀ x₀) ^ max N M := pow_le_pow_right₀ h1 (le_max_right _ _)
      have hm : C * htInf (γ₀ x₀) ^ M ≤ max C 0 * htInf (γ₀ x₀) ^ max N M :=
        mul_le_mul (le_max_left _ _) p2 (by positivity) (le_max_right _ _)
      calc ‖k₀ x₀‖ * (1 + ‖η₀ x₀‖) ^ N * ∫ y, ‖k (γ₀ x₀) y‖ * (htInf (γ y) * (1 + ‖η (γ₀ x₀) y‖)) ^ N ∂ν
          ≤ ‖k₀ x₀‖ * (1 + ‖η₀ x₀‖) ^ N * (max C 0 * htInf (γ₀ x₀) ^ max N M) :=
            mul_le_mul_of_nonneg_left (hq.trans hm) A0
        _ ≤ ‖k₀ x₀‖ * (1 + ‖η₀ x₀‖) ^ max N M * (max C 0 * htInf (γ₀ x₀) ^ max N M) := by
            gcongr
        _ = max C 0 * (‖k₀ x₀‖ * (htInf (γ₀ x₀) * (1 + ‖η₀ x₀‖)) ^ max N M) := by rw [mul_pow]; ring
    refine hF.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
    · exact (((hk₀.comp measurable_fst).mul hkj).norm.mul (((mht.comp measurable_snd).mul
        (measurable_const.add ((mη₀.comp measurable_fst).add mηj).norm)).pow_const N)).aestronglyMeasurable
    · have hh := htInf_pos' (γ p.2)
      have hb : htInf (γ p.2) * (1 + ‖η₀ p.1 + η (γ₀ p.1) p.2‖) ≤
          (1 + ‖η₀ p.1‖) * (htInf (γ p.2) * (1 + ‖η (γ₀ p.1) p.2‖)) := by
        have := mul_le_mul_of_nonneg_left (show 1 + ‖η₀ p.1 + η (γ₀ p.1) p.2‖ ≤ (1 + ‖η₀ p.1‖) * (1 + ‖η (γ₀ p.1) p.2‖) by
          nlinarith [norm_add_le (η₀ p.1) (η (γ₀ p.1) p.2), norm_nonneg (η₀ p.1), norm_nonneg (η (γ₀ p.1) p.2),
            mul_nonneg (norm_nonneg (η₀ p.1)) (norm_nonneg (η (γ₀ p.1) p.2))]) hh.le
        linarith
      have hp : (htInf (γ p.2) * (1 + ‖η₀ p.1 + η (γ₀ p.1) p.2‖)) ^ N ≤
          (1 + ‖η₀ p.1‖) ^ N * (htInf (γ p.2) * (1 + ‖η (γ₀ p.1) p.2‖)) ^ N :=
        (pow_le_pow_left₀ (by positivity) hb N).trans_eq (mul_pow _ _ _)
      rw [Real.norm_of_nonneg (by positivity), norm_mul]
      calc ‖k₀ p.1‖ * ‖k (γ₀ p.1) p.2‖ * (htInf (γ p.2) * (1 + ‖η₀ p.1 + η (γ₀ p.1) p.2‖)) ^ N
          ≤ ‖k₀ p.1‖ * ‖k (γ₀ p.1) p.2‖ *
              ((1 + ‖η₀ p.1‖) ^ N * (htInf (γ p.2) * (1 + ‖η (γ₀ p.1) p.2‖)) ^ N) :=
            mul_le_mul_of_nonneg_left hp (by positivity)
        _ = F p := by simp only [F]; ring
  refine ⟨X₀ × X, inferInstance, ν₀.prod ν, inferInstance, _, _, _, hrap, ?_⟩
  intro W hW z g
  have hint := hrap.integrable hW z g
  show χ z * T (S W) z (g * t z) = _
  rw [integral_prod _ hint, hT (S W) (hS W hW) z (g * t z), ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x₀ => ?_)
  simp only
  rw [show χ z * (k₀ x₀ * (𝐞 (η₀ x₀ z) : ℂ) * S W (g * t z * γ₀ x₀)) =
      k₀ x₀ * (𝐞 (η₀ x₀ z) : ℂ) * (χ z * S W (g * t z * γ₀ x₀)) by ring, hSk W hW (γ₀ x₀) z g,
    ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [ContinuousLinearMap.add_apply, AddChar.map_add_eq_mul, Circle.coe_mul]
  ring

example : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] (T : (GL (Fin n) (Cinf E) → ℂ) → Z → GL (Fin n) (Cinf E) → ℂ), IsKerOpInf T → ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : GL (Fin n) (Cinf E) → X → ℂ) (γ : X → GL (Fin n) (Cinf E)) (η : GL (Fin n) (Cinf E) → X → Z →L[ℝ] ℝ), IsRapidFamInf ν k γ η → ∀ (S : (GL (Fin n) (Cinf E) → ℂ) → GL (Fin n) (Cinf E) → ℂ) (t : Z → GL (Fin n) (Cinf E)) (χ : Z → ℂ), (∀ W, IsModGrowthInf W → IsModGrowthInf (S W)) → (∀ W, IsModGrowthInf W → ∀ q z g, χ z * S W (g * t z * q) = ∫ x, k q x * (𝐞 (η q x z) : ℂ) * W (g * γ x) ∂ν) → IsKerOpInf (fun W z g => χ z * T (S W) z (g * t z)) := isKerOpInf_comp_rapidFamInf

end GlobalTheory.JSW.MirCinf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSectionMatrixInvertibleLevelReductionStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanSectionMatrix_invertible_level_reduction : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (ρ : Fin n) (j : InfinitePlace E → Fin n), (∀ w, j w ≤ ρ) → (∀ v : Fin n → Cinf E, (∀ w, v (j w) w ≠ 0) → IsUnit (Matrix.of (secMatInf ρ j v)) ∧ toGLInf (Matrix.of (secMatInf ρ j v)) ∈ levSetInf E n (ρ + 1)) ∧ (∀ g ∈ levSetInf E n (ρ + 1), (∀ w, rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E)) (j w) w ≠ 0) → g * (toGLInf (Matrix.of (secMatInf ρ j (rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E))))))⁻¹ ∈ levSetInf E n ρ) ∧ ∃ L : (Fin n → Cinf E) →L[ℝ] (Fin n → Fin n → Cinf E), ∀ v, secMatInf ρ j v = secMatInf ρ j 0 + L v := by
  first | (exact @GlobalTheory.JSW.MirCinf.secMatInf_main) | (exact GlobalTheory.JSW.MirCinf.secMatInf_main) | (intros; apply GlobalTheory.JSW.MirCinf.secMatInf_main  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanTruncatedRowUnipotentInvariantNonzeroStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanTruncatedRow_unipotent_invariant_nonzero : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (ρ : Fin n), ∀ g ∈ levSetInf E n (ρ + 1), (∀ u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin n), rowCutInf ρ ((u * g : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) = rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E))) ∧ ∀ w, ∃ j, j ≤ ρ ∧ rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E)) j w ≠ 0 := by
  first | exact @GlobalTheory.JSW.MirCinf.rowCutInf_unipB_mul_levSetInf | exact GlobalTheory.JSW.MirCinf.rowCutInf_unipB_mul_levSetInf | (intros; apply GlobalTheory.JSW.MirCinf.rowCutInf_unipB_mul_levSetInf; all_goals assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanUnipotentTimesGLrSetClosedSubgroupStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanUnipotentTimesGLrSet_closed_subgroup : ∀ (E : Type) [Field E] [NumberField E] (n r : ℕ), (∀ g ∈ levSetInf E n r, ∀ h ∈ levSetInf E n r, g * h ∈ levSetInf E n r) ∧ (∀ g ∈ levSetInf E n r, g⁻¹ ∈ levSetInf E n r) ∧ (∀ u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin n), u ∈ levSetInf E n r) ∧ IsClosed (levSetInf E n r) := by
  first | exact @GlobalTheory.JSW.MirCinf.levSetInf_closed_subgroup | exact GlobalTheory.JSW.MirCinf.levSetInf_closed_subgroup | (intros; apply GlobalTheory.JSW.MirCinf.levSetInf_closed_subgroup; all_goals assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeDefinite
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep
open scoped TensorProduct

namespace GlobalTheory.SphGal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def BaseChangeDefinite : Prop :=
  ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (M : DSModel V S) (W' W : Submodule ℂ (MMap M)),
    IsInfFam θ → (∀ τ, Formalism.QuantumDeterminants.IsHCParam (M.lam τ)) → V.SigOK → V.IsPosDef → IsCuspQuot θ M W' W → HasBaseChange M W' W

end GlobalTheory.SphGal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFrameIntegralGramMatrix
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameGram

theorem form_mem_span {R : Type} [CommRing R] (S : Subring R) (σ : R →+* R) (hσ : ∀ s ∈ S, σ s ∈ S) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) R) (T : Set (Fin n → R))
    (hT : ∀ x ∈ T, ∀ y ∈ T, ∑ i, ∑ j, σ (x i) * J i j * y j ∈ S) :
    ∀ x ∈ Submodule.span S T, ∀ y ∈ Submodule.span S T, ∑ i, ∑ j, σ (x i) * J i j * y j ∈ S := by
  intro x hx y hy
  induction hx using Submodule.span_induction with
  | mem x hx =>
    induction hy using Submodule.span_induction with
    | mem y hy => exact hT x hx y hy
    | zero => simp
    | add a b _ _ ha hb =>
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      exact S.add_mem ha hb
    | smul c a _ ha =>
      have : ∑ i, ∑ j, σ (x i) * J i j * (c • a) j = (c : R) * ∑ i, ∑ j, σ (x i) * J i j * a j := by
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        show _ * ((c : R) * a j) = _
        ring
      rw [this]; exact S.mul_mem c.2 ha
  | zero => simp
  | add a b _ _ ha hb =>
    simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
    exact S.add_mem ha hb
  | smul c a _ ha =>
    have : ∑ i, ∑ j, σ ((c • a) i) * J i j * y j = σ (c : R) * ∑ i, ∑ j, σ (a i) * J i j * y j := by
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      show σ ((c : R) * a i) * _ * _ = _
      rw [map_mul]; ring
    rw [this]; exact S.mul_mem (hσ _ c.2) ha

theorem exists_unit {R : Type} [CommRing R] (S : Subring R) (σ : R →+* R) (hσ : ∀ s ∈ S, σ s ∈ S) {n m : ℕ}
    (J : Matrix (Fin n) (Fin n) R) (β : GL (Fin n) R) (H : Set (Fin n → R))
    (hβ : ∀ x, x ∈ H ↔ ∀ i, (β⁻¹).1.mulVec x i ∈ S)
    (hH : ∀ x ∈ H, ∀ y ∈ H, ∑ i, ∑ j, σ (x i) * J i j * y j ∈ S)
    (s s' : Fin m → Fin n → R) (hs : ∀ i, s i ∈ H) (hs' : ∀ i, s' i ∈ H)
    (hd : ∀ a j, ∑ i, s i a * ∑ k, σ (s' i k) * J k j = if a = j then 1 else 0) :
    ∃ G : GL (Fin n) S, S.subtype.mapMatrix G.1 = (β.1.map σ)ᵀ * J * β.1 := by
  have hcol : ∀ j, (fun i => β.1 i j) ∈ H := by
    intro j
    rw [hβ]
    intro k
    have : (β⁻¹).1.mulVec (fun i => β.1 i j) k = ((β⁻¹).1 * β.1) k j := rfl
    rw [this, Units.inv_mul, Matrix.one_apply]
    split_ifs
    · exact S.one_mem
    · exact S.zero_mem
  have a1 : ∀ i j, ((β.1.map σ)ᵀ * J * β.1) i j ∈ S := by
    intro i j
    have := hH _ (hcol i) _ (hcol j)
    rw [Finset.sum_comm] at this
    simpa only [Matrix.mul_apply, Finset.sum_mul, Matrix.transpose_apply, Matrix.map_apply] using this
  let P : Matrix (Fin n) (Fin m) R := Matrix.of fun a i => s i a
  let P' : Matrix (Fin n) (Fin m) R := Matrix.of fun a i => s' i a
  have hP : P * ((P'.map σ)ᵀ * J) = 1 := by
    ext a j
    rw [Matrix.one_apply, ← hd]
    rfl
  have a2 : ∀ i j, (((β⁻¹).1 * P) * (((β⁻¹).1 * P').map σ)ᵀ) i j ∈ S := by
    intro i j
    rw [Matrix.mul_apply]
    exact S.sum_mem fun k _ => S.mul_mem ((hβ _).1 (hs k) i) (hσ _ ((hβ _).1 (hs' k) j))
  have hinv : (((β⁻¹).1 * P) * (((β⁻¹).1 * P').map σ)ᵀ) * ((β.1.map σ)ᵀ * J * β.1) = 1 := by
    have e : (((β⁻¹).1 * P').map σ)ᵀ * (β.1.map σ)ᵀ = (P'.map σ)ᵀ := by
      rw [← Matrix.transpose_mul, ← Matrix.map_mul, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    calc _ = (β⁻¹).1 * (P * (((((β⁻¹).1 * P').map σ)ᵀ * (β.1.map σ)ᵀ) * J)) * β.1 := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [e, hP, Matrix.mul_one, Units.inv_mul]
  let M : Matrix (Fin n) (Fin n) S := fun i j => ⟨_, a1 i j⟩
  let M' : Matrix (Fin n) (Fin n) S := fun i j => ⟨_, a2 i j⟩
  have hM : S.subtype.mapMatrix M = (β.1.map σ)ᵀ * J * β.1 := rfl
  have hM' : S.subtype.mapMatrix M' = ((β⁻¹).1 * P) * (((β⁻¹).1 * P').map σ)ᵀ := rfl
  have inj : Function.Injective (S.subtype.mapMatrix (m := Fin n)) := by
    intro A B h
    ext i j
    exact congrFun (congrFun h i) j
  have p2 : M' * M = 1 := inj (by rw [map_mul, map_one, hM, hM', hinv])
  exact ⟨⟨M, M', mul_eq_one_comm.1 p2, p2⟩, hM⟩

theorem exists_unit_adelic {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n m : ℕ}
    (c : E → E) (σ : E ⊗[F] Formalism.L2.Herm.Af F →+* E ⊗[F] Formalism.L2.Herm.Af F)
    (hσ : ∀ s ∈ Formalism.L2.Herm.intAf F E, σ s ∈ Formalism.L2.Herm.intAf F E)
    (hσι : ∀ x, σ (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) x) = Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (c x))
    (J : Matrix (Fin n) (Fin n) E) (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Λ : Submodule (𝓞 E) (Fin n → E))
    (hβ : IsFrame β Λ) (hΛ : ∀ y ∈ Λ, ∀ x ∈ Λ, ∃ b : 𝓞 E, (b : E) = ∑ i, ∑ j, c (x i) * J i j * y j)
    (s s' : Fin m → Fin n → E) (hs : ∀ i, s i ∈ Λ ∧ s' i ∈ Λ)
    (hd : ∀ a j, ∑ i, s i a * ∑ k, c (s' i k) * J k j = if a = j then 1 else 0) :
    ∃ G : GL (Fin n) (Formalism.L2.Herm.intAf F E), (intGL F E n G).val =
      Formalism.UG.cT σ β.1 * J.map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F)) * β.1 := by
  let ι : E →+* E ⊗[F] Formalism.L2.Herm.Af F := Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F)
  replace hσι : ∀ x, σ (ι x) = ι (c x) := hσι
  have hmem : ∀ x ∈ Λ, (fun i => ι (x i)) ∈ Formalism.L2.Herm.hatL (F := F) Λ := fun x hx =>
    Submodule.subset_span ⟨x, hx, rfl⟩
  refine exists_unit (Formalism.L2.Herm.intAf F E) σ hσ (J.map ι) β
    (Formalism.L2.Herm.hatL (F := F) Λ) hβ ?_ (fun i a => ι (s i a)) (fun i a => ι (s' i a))
    (fun i => hmem _ (hs i).1) (fun i => hmem _ (hs i).2) ?_
  · refine form_mem_span _ σ hσ _ _ ?_
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    obtain ⟨b, hb⟩ := hΛ y hy x hx
    have : ∑ i, ∑ j, σ (ι (x i)) * (J.map ι) i j * ι (y j) = ι b := by
      rw [hb]
      simp only [map_sum, RingHom.map_mul, hσι, Matrix.map_apply]
    show ∑ i, ∑ j, σ (ι (x i)) * (J.map ι) i j * ι (y j) ∈ _
    rw [this]
    exact (oToS F E b).2
  · intro a j
    have := congrArg ι (hd a j)
    simp only [map_sum, RingHom.map_mul, ← hσι, apply_ite ι, RingHom.map_one, RingHom.map_zero] at this
    exact this

theorem gram_unimodular : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsBaseFrame V β Λ N → ∃ G : GL (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E), (intGL D.host.F D.host.E V.rank G).val = BadPlacesGoodCoefficients.gramIn V β := by
  intro D V β Λ N hB
  have hsd := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D V β Λ N ⟨1, by rw [pow_one]; exact hB⟩
  obtain ⟨m, s, s', hs, hd⟩ := GlobalTheory.LatVacDual.dualFamily D V Λ hsd
  exact exists_unit_adelic star (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) (fun _ => GlobalTheory.LevSplit.sigR_int)
    (fun _ => rfl) V.gram β Λ hB.1 (fun y hy => (hsd.2 y).1 hy) s s' hs hd

end GlobalTheory.FrameGram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BirigidifiedPullbackMulPairIsoTensorPowSq
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.BirigidPow

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

theorem comp_pow_pt {T T' : Over S} (ρ : T' ⟶ T) (x : T ⟶ A) (n : ℕ) : ρ ≫ x ^ n = (ρ ≫ x) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

def val {P : LB (G2 A).left} (hP : P.IsLB) {T : Over S} (x y : T ⟶ A) : CechPic.Pic T.left :=
  CechPic.pull (lift x y).left (CechPic.cls P hP)

variable {P : LB (G2 A).left} (hP : P.IsLB)

theorem val_one_left (h₁ : ∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) {T : Over S}
    (y : T ⟶ A) : val hP 1 y = 0 := by
  have e : lift (1 : T ⟶ A) y = y ≫ lift (1 : A ⟶ A) (𝟙 A) := by
    rw [comp_lift, MonObj.comp_one, Category.comp_id]
  rw [val, e, Over.comp_left, CechPic.pull_comp, ← CechPic.cls_pull hP _ (pull_isLB hP _),
    (CechPic.cls_eq_zero_iff (pull_isLB hP _)).2 h₁, map_zero]

theorem val_one_right (h₂ : ∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) {T : Over S}
    (x : T ⟶ A) : val hP x 1 = 0 := by
  have e : lift x (1 : T ⟶ A) = x ≫ lift (𝟙 A) (1 : A ⟶ A) := by
    rw [comp_lift, MonObj.comp_one, Category.comp_id]
  rw [val, e, Over.comp_left, CechPic.pull_comp, ← CechPic.cls_pull hP _ (pull_isLB hP _),
    (CechPic.cls_eq_zero_iff (pull_isLB hP _)).2 h₂, map_zero]

theorem add_of_triv {T : Over S} (a b c : T.left ⟶ (G2 A).left)
    (H : ∃ t : (LB.LinComb P (K := Fin 3) ![a, b, c] ![1, -1, -1]).Gen, t.IsGen) :
    CechPic.pull a (CechPic.cls P hP) = CechPic.pull b (CechPic.cls P hP) + CechPic.pull c (CechPic.cls P hP) := by
  have hL := LB.isLB_linComb hP (![a, b, c] : Fin 3 → _) ![1, -1, -1]
  have z := (CechPic.cls_linComb hP _ _ hL).symm.trans ((CechPic.cls_eq_zero_iff hL).2 H)
  rw [Fin.sum_univ_three] at z
  have z' : (1 : ℤ) • CechPic.pull a (CechPic.cls P hP) + (-1 : ℤ) • CechPic.pull b (CechPic.cls P hP) +
      (-1 : ℤ) • CechPic.pull c (CechPic.cls P hP) = 0 := z
  rw [one_zsmul, neg_one_zsmul, neg_one_zsmul] at z'
  rw [← sub_eq_zero, ← z']
  abel

variable (hA : IsAbelianScheme A)
  (hamp : Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left))
  (h₁ : ∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen)
  (h₂ : ∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen)

include hA hamp h₁ h₂

theorem val_mul_left {T : Over S} (x x' y : T ⟶ A) : val hP (x * x') y = val hP x y + val hP x' y :=
  add_of_triv hP _ _ _ (Biadditive.biadditive_of_triv_axes GlobalTheory.laws_without_cohomology.1 S A _ hA
    (pull_isLB hP _) hamp P hP h₁ h₂ T x x' y).1

theorem val_mul_right {T : Over S} (x y y' : T ⟶ A) : val hP x (y * y') = val hP x y + val hP x y' :=
  add_of_triv hP _ _ _ (Biadditive.biadditive_of_triv_axes GlobalTheory.laws_without_cohomology.1 S A _ hA
    (pull_isLB hP _) hamp P hP h₁ h₂ T y y' x).2

theorem val_pow_left {T : Over S} (x y : T ⟶ A) (n : ℕ) : val hP (x ^ n) y = n • val hP x y := by
  induction n with
  | zero => rw [pow_zero, zero_smul]; exact val_one_left hP h₁ y
  | succ n ih => rw [pow_succ, val_mul_left hP hA hamp h₁ h₂, ih, succ_nsmul]

theorem val_pow_right {T : Over S} (x y : T ⟶ A) (n : ℕ) : val hP x (y ^ n) = n • val hP x y := by
  induction n with
  | zero => rw [pow_zero, zero_smul]; exact val_one_right hP h₂ x
  | succ n ih => rw [pow_succ, val_mul_right hP hA hamp h₁ h₂, ih, succ_nsmul]

omit hA hamp h₁ h₂ in
theorem cls_lbPow (m : ℕ) (h : (Hecke.lbPow P m).IsLB) : CechPic.cls _ h = m • CechPic.cls P hP := by
  unfold Hecke.lbPow at h ⊢
  rw [CechPic.cls_linComb hP _ _ h]
  simp [CechPic.pull_id]

include hP in

theorem lineBundleIso_tensorPowSq_pullback_mulPair (n : ℕ) :
    LBIso (Hecke.lbPow P (n ^ 2)) (P.pull (Hecke.sq2 ((𝟙 A) ^ n))) := by
  have hL : (Hecke.lbPow P (n ^ 2)).IsLB := LB.isLB_linComb hP _ _
  refine (CechPic.cls_eq_iff hL (pull_isLB hP _)).1 ?_
  rw [cls_lbPow hP, CechPic.cls_pull hP _ (pull_isLB hP _)]
  change _ = val hP (fst A A ≫ (𝟙 A) ^ n) (snd A A ≫ (𝟙 A) ^ n)
  rw [comp_pow_pt, comp_pow_pt, Category.comp_id, Category.comp_id, val_pow_left hP hA hamp h₁ h₂,
    val_pow_right hP hA hamp h₁ h₂, val, lift_fst_snd, Over.id_left, CechPic.pull_id, smul_smul, sq]

omit hP hA hamp h₁ h₂ in

theorem birigidified_pullback_mulPair_iso_tensorPowSq : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    ∀ P : LB (G2 A).left, P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) →
    (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) →
    ∀ n : ℕ, LBIso (GlobalTheory.UPel.HT.Hecke.lbPow P (n ^ 2)) (P.pull (GlobalTheory.UPel.HT.Hecke.sq2 ((𝟙 A) ^ n))) :=
  fun _ _ _ _ hA _ hP h₁ h₂ hamp n => lineBundleIso_tensorPowSq_pullback_mulPair hP hA hamp h₁ h₂ n

end GlobalTheory.BirigidPow
end
end

