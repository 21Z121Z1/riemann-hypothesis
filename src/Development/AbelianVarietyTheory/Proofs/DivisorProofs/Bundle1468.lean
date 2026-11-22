import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0764
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkGLOneCorner
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1445
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1456
import GroundTheory.GlobalFields.TateThesis.AdelicCharDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1446
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1444
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordHolomorphicAndUniform
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1462
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1455
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1459
import GroundTheory.GlobalFields.Adele.BaseChange
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.BaseChange
import GroundTheory.GlobalFields.IdeleGroups.NormOneCompact
import GroundTheory.GlobalFields.TateThesis.IdeleMeasureNormOne
import CompanionTheory.AutomorphicTheory.UnitriangularMeasure.AdeleCoordinateMeasure.EllipticTorusNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1465
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1448
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermSliceLeviModerateGrowth
section
open NumberField MeasureTheory GlobalTheory.CuspRep

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.LeviGA

namespace GlobalTheory.SliceTwo.Growth

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

omit [IsTotallyComplex E] in

theorem height_inv {a : ℕ} (y : GL (Fin a) (Cinf E)) : height y⁻¹ = height y := by
  unfold height; rw [inv_inv]; ring

omit [IsTotallyComplex E] in

theorem height_mul_right_le {a : ℕ} (c : GL (Fin a) (Cinf E)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y, height (y * c) ≤ B * height y := by
  obtain ⟨B, hB, h⟩ := GlobalTheory.ConstTermGrowth.height_mul_left_le (E := E) (isCompact_singleton (x := c⁻¹))
  refine ⟨B, hB, fun y => ?_⟩
  have := h _ rfl y⁻¹
  rwa [← _root_.mul_inv_rev, height_inv, height_inv] at this

omit [IsTotallyComplex E] in

theorem norm_toL_blkGL_one_le {a r : ℕ} (hr : r ≤ a) (y : GL (Fin (a - r)) (Cinf E)) :
    ‖toL (blkGL hr (1, y)).val‖ ≤ 1 + ‖toL y.val‖ := by
  have h0 : (0 : ℝ) ≤ 1 + ‖toL y.val‖ := by positivity
  refine (pi_norm_le_iff_of_nonneg h0).2 fun i => (pi_norm_le_iff_of_nonneg h0).2 fun j => ?_
  obtain ⟨i, rfl⟩ := (blkEquiv hr).surjective i
  obtain ⟨j, rfl⟩ := (blkEquiv hr).surjective j
  change ‖(blkGL hr (1, y) : Matrix (Fin a) (Fin a) (Cinf E)) (blkEquiv hr i) (blkEquiv hr j)‖ ≤ _
  rw [blkGL_apply]
  rcases i with i | i <;> rcases j with j | j
  · simp only [Matrix.fromBlocks_apply₁₁, Units.val_one]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.one_apply_eq]
      refine ((pi_norm_le_iff_of_nonneg zero_le_one).2 fun w => ?_).trans (by linarith [norm_nonneg (toL y.val)])
      simp
    · rw [Matrix.one_apply_ne hij, norm_zero]; exact h0
  · simp only [Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, norm_zero]; exact h0
  · simp only [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, norm_zero]; exact h0
  · simp only [Matrix.fromBlocks_apply₂₂]
    exact ((norm_le_pi_norm (toL y.val i) j).trans (norm_le_pi_norm (toL y.val) i)).trans
      (by linarith)

omit [IsTotallyComplex E] in

theorem height_blkGL_one_le {a r : ℕ} (hr : r ≤ a) (y : GL (Fin (a - r)) (Cinf E)) :
    height (blkGL hr (1, y)) ≤ 3 * height y := by
  have e : (blkGL hr (1, y))⁻¹ = blkGL hr (1, y⁻¹) := by
    rw [← map_inv, Prod.inv_mk, inv_one]
  have h1 := norm_toL_blkGL_one_le hr y
  have h2 := norm_toL_blkGL_one_le hr y⁻¹
  have n1 := norm_nonneg (toL y.val)
  have n2 := norm_nonneg (toL (y⁻¹).val)
  unfold height
  rw [e]
  linarith

end GlobalTheory.SliceTwo.Growth

open GlobalTheory.SliceTwo.Growth in

theorem GlobalTheory.SliceTwo.Growth.norm_slice_le : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ)
    (hr : r ≤ a) [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)]
    (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure →
    IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 → ∀ φ : Sm E a, IsAutForm φ →
    ∀ (m₁ : GA E r) (t : GL (Fin a) (Af E)) (κ : Kinf E a) (g : GA E (a - r)), ∃ (C : ℝ) (M : ℕ), ∀ y,
      ‖GlobalTheory.SliceTwo.slice E μ 𝓕 hr φ.1 m₁ t κ (g * infGL E (a - r) y)‖ ≤ C * height y ^ M := by
  intro E _ _ _ a r hr _ _ μ 𝓕 hμ hF h1 φ hφ m₁ t κ g
  obtain ⟨C, N, hC⟩ := GlobalTheory.ConstTermGrowth.norm_constTerm_le E a r μ 𝓕 hμ hF h1 φ hφ.left hφ.level hφ.growth
    (blkGL hr (m₁, g) * finGL E a t)
  obtain ⟨B, hB0, hB⟩ := height_mul_right_le (E := E) (Unitary.toUnits κ)
  refine ⟨|C| * (3 * B) ^ N, N, fun y => ?_⟩
  have e : GlobalTheory.SliceTwo.slice E μ 𝓕 hr φ.1 m₁ t κ (g * infGL E (a - r) y) =
      ∫ x in 𝓕, φ.1 (unip x * ((blkGL hr (m₁, g) * finGL E a t) *
        infGL E a (blkGL hr (1, y) * Unitary.toUnits κ))) ∂μ := by
    unfold GlobalTheory.SliceTwo.slice
    congr 1
    funext x
    congr 2
    rw [GlobalTheory.SliceTwo.blkGL_mul_infGL, map_mul]
    simp only [mul_assoc]
    rw [← mul_assoc (infGL E a (blkGL hr (1, y))) (finGL E a t), infGL_comm]
    simp only [mul_assoc]
  rw [e]
  refine (hC _).trans ?_
  have hy := one_le_height y
  have hb := one_le_height (blkGL hr (1, y) * Unitary.toUnits κ)
  have h3 : height (blkGL hr (1, y) * Unitary.toUnits κ) ≤ 3 * B * height y := by
    calc _ ≤ B * height (blkGL hr (1, y)) := hB _
      _ ≤ B * (3 * height y) := mul_le_mul_of_nonneg_left (height_blkGL_one_le hr y) hB0
      _ = 3 * B * height y := by ring
  calc C * height (blkGL hr (1, y) * Unitary.toUnits κ) ^ N
      ≤ |C| * height (blkGL hr (1, y) * Unitary.toUnits κ) ^ N :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg (by linarith) _)
    _ ≤ |C| * (3 * B * height y) ^ N :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) h3 _) (abs_nonneg C)
    _ = |C| * (3 * B) ^ N * height y ^ N := by ring

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousCharacterTrivialOnSmallIdeles
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDenom
open scoped TensorProduct NNReal Matrix

namespace GlobalTheory.PsiTriv

theorem exists_nat_trivial {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) :
    ∃ m : ℕ, 0 < m ∧ ∀ t : AF F, t.1 = 0 → (∀ v, ‖evFin F v t‖ ≤ ‖(m : Fv F v)‖) → ψ t = 1 := by
  classical
  let f : FiniteAdeleRing (𝓞 F) F → AF F := fun y => (0, y)
  have hf : Continuous f := continuous_const.prodMk continuous_id
  have hW : (fun y => ψ (f y)) ⁻¹' {z : ℂ | ‖z - 1‖ < 1 / 2} ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F) := by
    refine ((isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const))
      continuous_const).preimage (hψ.comp hf)).mem_nhds ?_
    show ‖ψ (0 : AF F) - 1‖ < 1 / 2
    rw [AddChar.map_zero_eq_one]; norm_num
  obtain ⟨d, hd0, hd⟩ := GroundTheory.Global.exists_forall_mul_mem_of_mem_nhds hW
  set D : FiniteAdeleRing (𝓞 F) F := algebraMap F _ (algebraMap (𝓞 F) F d) with hD
  have htriv : ∀ y ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F, ψ (f (D * y)) = 1 := by
    intro y hy
    refine GroundTheory.Global.eq_one_of_sq_mem
      (s := {z | ∃ y ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F, ψ (f (D * y)) = z}) ?_ ?_ ⟨y, hy, rfl⟩
    · rintro _ ⟨a, ha, rfl⟩
      refine ⟨a + a, add_mem ha ha, ?_⟩
      rw [sq, ← AddChar.map_add_eq_mul]
      congr 1
      show ((0 : InfiniteAdeleRing F), D * (a + a)) = ((0 : InfiniteAdeleRing F) + 0, D * a + D * a)
      rw [mul_add, add_zero]
    · rintro _ ⟨a, ha, rfl⟩
      exact hd a ha
  have hm0 : Ideal.absNorm (Ideal.span {d}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hd0
  obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {d}))
  refine ⟨Ideal.absNorm (Ideal.span {d}), Nat.pos_of_ne_zero hm0, fun t ht0 ht => ?_⟩
  have hdF : algebraMap (𝓞 F) F d ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hd0
  let y : FiniteAdeleRing (𝓞 F) F := algebraMap F _ (algebraMap (𝓞 F) F d)⁻¹ * t.2
  have hty : t = f (D * y) := by
    refine Prod.ext ht0 ?_
    show t.2 = algebraMap F _ (algebraMap (𝓞 F) F d) * (algebraMap F _ (algebraMap (𝓞 F) F d)⁻¹ * t.2)
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hdF, map_one, one_mul]
  rw [hty]
  refine htriv y fun v => ?_
  have hv : ‖t.2 v‖ ≤ _ := ht v
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, ← Valued.toNormedField.norm_le_one_iff]
  have hy : y v = algebraMap F (Fv F v) (algebraMap (𝓞 F) F d)⁻¹ * t.2 v := rfl
  have hm : ((Ideal.absNorm (Ideal.span {d}) : ℕ) : Fv F v) =
      algebraMap F (Fv F v) (algebraMap (𝓞 F) F e) * algebraMap F (Fv F v) (algebraMap (𝓞 F) F d) := by
    rw [← map_mul, ← map_mul, he, map_natCast, map_natCast]
  have hdv : algebraMap F (Fv F v) (algebraMap (𝓞 F) F d) ≠ 0 := (map_ne_zero _).2 hdF
  have he1 : ‖algebraMap F (Fv F v) (algebraMap (𝓞 F) F e)‖ ≤ 1 := FinitePlace.norm_le_one F v e
  rw [hy, map_inv₀, norm_mul, norm_inv, inv_mul_le_iff₀ (norm_pos_iff.2 hdv)]
  rw [hm, norm_mul] at hv
  nlinarith [norm_nonneg (algebraMap F (Fv F v) (algebraMap (𝓞 F) F d)), norm_nonneg (t.2 v)]

end GlobalTheory.PsiTriv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousCircleIntegralFamily
section
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.CircleCont

theorem continuous_circleIntegral_family : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (H₀ : ℂ → GAd σ J → ℂ) (s₀ : ℂ) (r : ℝ) (V : Set ℂ),
    IsOpen V → 0 < r → Metric.closedBall s₀ r ⊆ V → (∀ s ∈ V, IsSmoothModerate σ J (H₀ s)) →
    (∀ μ, GlobalTheory.EisLine.IsModerateForm σ J μ → DifferentiableOn ℂ (fun s => μ (H₀ s)) V) → ∀ j : ℤ,
    Continuous fun g => circleIntegral (fun z => (z - s₀) ^ j * H₀ z g) s₀ r := by
  intro F E _ _ _ _ _ σ hσ n J hJ H₀ s₀ r V hV hr hsub hH hμ j
  have hsph : Metric.sphere s₀ r ⊆ V := Metric.sphere_subset_closedBall.trans hsub
  obtain ⟨-, N, C, hC⟩ := GlobalTheory.WeakHolFamily.word_holomorphic_and_uniform F E σ n J H₀ V (Metric.sphere s₀ r) hV
    (isCompact_sphere s₀ r) hsph hH hμ [] (by simp)
  have hhol : ∀ g, DifferentiableOn ℂ (fun s => H₀ s g) V := fun g =>
    (hμ _ (GlobalTheory.EisLine.isModerateForm_proj σ J g)).congr fun s _ => rfl
  have hcm : ∀ θ, circleMap s₀ r θ ∈ Metric.sphere s₀ r := fun θ => circleMap_mem_sphere s₀ hr.le θ
  have hht : Continuous fun g : GAd σ J => (height σ J g : ℝ) :=
    NNReal.continuous_coe.comp ((GlobalTheory.Grow.continuous_heightGL F).comp continuous_subtype_val)
  rw [continuous_iff_continuousAt]
  intro g₀
  unfold circleIntegral
  have hne : ∀ θ, circleMap s₀ r θ - s₀ ≠ 0 := fun θ => sub_ne_zero.2 (circleMap_ne_center hr.ne')
  have hn1 : ∀ θ, ‖circleMap s₀ r θ - s₀‖ = r := fun θ => by rw [← dist_eq_norm]; exact hcm θ
  have hev : ∀ᶠ g in 𝓝 g₀, (height σ J g : ℝ) < height σ J g₀ + 1 :=
    hht.continuousAt.eventually (Iio_mem_nhds (lt_add_one _))
  simp_rw [deriv_circleMap]
  refine intervalIntegral.continuousAt_of_dominated_interval
    (bound := fun _ => r * (r ^ j * (|C| * ((height σ J g₀ : ℝ) + 1) ^ N))) ?_ ?_ intervalIntegrable_const ?_
  · refine Eventually.of_forall fun g => Continuous.aestronglyMeasurable ?_
    exact ((continuous_circleMap 0 r).mul continuous_const).smul
      ((((continuous_circleMap s₀ r).sub continuous_const).zpow₀ j (fun θ => Or.inl (hne θ))).mul
        ((hhol g).continuousOn.comp_continuous (continuous_circleMap s₀ r) (fun θ => hsph (hcm θ))))
  · filter_upwards [hev] with g hg
    refine ae_of_all _ fun θ _ => ?_
    rw [← circleMap_sub_center, norm_smul, norm_mul, norm_mul, norm_zpow, hn1, Complex.norm_I, mul_one]
    have h0 : (0 : ℝ) ≤ (height σ J g : ℝ) := NNReal.coe_nonneg _
    have h1 : ‖H₀ (circleMap s₀ r θ) g‖ ≤ |C| * ((height σ J g₀ : ℝ) + 1) ^ N :=
      calc ‖H₀ (circleMap s₀ r θ) g‖ ≤ C * (height σ J g : ℝ) ^ N := hC _ (hcm θ) g
        _ ≤ |C| * (height σ J g : ℝ) ^ N := mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
        _ ≤ |C| * ((height σ J g₀ : ℝ) + 1) ^ N :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 hg.le N) (abs_nonneg C)
    have h2 : (0 : ℝ) < r ^ j := zpow_pos hr j
    gcongr
  · refine ae_of_all _ fun θ _ => ?_
    exact ((continuous_const.mul (hH _ (hsph (hcm θ))).cont).const_smul (circleMap 0 r θ * Complex.I)).continuousAt
end GlobalTheory.CircleCont
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLogHomIsMultipleOfLogAbs
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThKCtFin

open scoped GroundTheory.Global.AdeleBaseChange NumberField.AdeleRing

noncomputable section

namespace GlobalTheory.IdeleLogHom

open GroundTheory.Global GroundTheory.Global.AdeleBaseChange

section Transfer

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def toE : (AE F E)ˣ →* IdeleGroup E :=
  Units.map (adeleTensorAlgEquivLeft F E : AE F E →ₐ[AF F] AdeleRing (𝓞 E) E).toMonoidHom

def ofE : IdeleGroup E →* (AE F E)ˣ :=
  Units.map ((adeleTensorAlgEquivLeft F E).symm : AdeleRing (𝓞 E) E →ₐ[AF F] AE F E).toMonoidHom

theorem ofE_toE (x : (AE F E)ˣ) : ofE F E (toE F E x) = x := by
  ext
  simp [ofE, toE]

theorem continuous_ofE : Continuous (ofE F E) := by
  have : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  have := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  have := IsModuleTopology.toContinuousSMul (AF F) (AE F E)
  have : IsModuleTopology (AF F) (AdeleRing (𝓞 E) E) := isModuleTopology_adeleRing
  exact Continuous.units_map _
    (IsModuleTopology.continuous_of_linearMap (adeleTensorAlgEquivLeft F E).symm.toLinearMap)

theorem toE_inclR (γ : Eˣ) :
    toE F E (Units.map (inclR (F := F) (AF F)).toMonoidHom γ) = IdeleGroup.diagonal E γ := by
  ext
  simp [toE, inclR, adeleTensorAlgEquivLeft_tmul, IdeleGroup.coe_diagonal]

theorem absE_eq_ideleModule (x : (AE F E)ˣ) :
    (absE F E x : ℝ) = (IdeleGroup.ideleModule E (toE F E x) : ℝ) := by
  rw [← GroundTheory.Automorphic.EllipticTorus.ideleModule_ideleNorm (K := F), ← GlobalTheory.ModuAdele.modu_norm_eq_absE]
  have h2 : ∀ u : (AF F)ˣ, (((adeleClass F).modu u : ℝ≥0) : ℝ) = (IdeleGroup.ideleModule F u : ℝ) := fun u => by
    change (distribHaarChar (AdeleRing (𝓞 F) F) u : ℝ) = _
    exact GlobalTheory.ModuAdele.distribHaarChar_adeleRing F u
  have h3 : Units.map (Algebra.norm (AF F) : AE F E →* AF F) x = ideleNorm F E (toE F E x) := by
    ext
    simp [toE, ideleNorm, Algebra.norm_eq_of_algEquiv]
  rw [h2, h3]

end Transfer

section OnE

variable {E : Type} [Field E] [NumberField E]

theorem map_pow_eq (ψ : IdeleGroup E → ℂ) (hadd : ∀ s t, ψ (s * t) = ψ s + ψ t) (y : IdeleGroup E) (n : ℕ) :
    ψ (y ^ n) = n * ψ y := by
  induction n with
  | zero =>
    have h := hadd 1 1
    rw [mul_one] at h
    simpa using h
  | succ n ih => rw [pow_succ, hadd, ih]; push_cast; ring

theorem eq_zero_of_mem_normOne (ψ : IdeleGroup E → ℂ) (hψ : Continuous ψ) (hadd : ∀ s t, ψ (s * t) = ψ s + ψ t)
    (hE : ∀ γ : Eˣ, ψ (IdeleGroup.diagonal E γ) = 0) {y : IdeleGroup E} (hy : y ∈ IdeleGroup.normOneSubgroup E) :
    ψ y = 0 := by
  obtain ⟨D, hD, -, hxD⟩ := IdeleGroup.exists_isCompact_normOneSubgroup E
  obtain ⟨M, hM⟩ := (hD.image hψ).isBounded.exists_norm_le
  have hb : ∀ z ∈ IdeleGroup.normOneSubgroup E, ‖ψ z‖ ≤ M := fun z hz => by
    obtain ⟨k, hk⟩ := hxD z hz
    have := hM _ ⟨_, hk, rfl⟩
    rwa [hadd, hE, zero_add] at this
  by_contra hne
  have hpos : 0 < ‖ψ y‖ := norm_pos_iff.2 hne
  obtain ⟨n, hn⟩ := exists_nat_gt (M / ‖ψ y‖)
  have h1 := hb _ (pow_mem hy n)
  rw [map_pow_eq ψ hadd, norm_mul, Complex.norm_natCast] at h1
  rw [div_lt_iff₀ hpos] at hn
  linarith

theorem exists_log_of_ideleGroup (ψ : IdeleGroup E → ℂ) (hψ : Continuous ψ) (hadd : ∀ s t, ψ (s * t) = ψ s + ψ t)
    (hE : ∀ γ : Eˣ, ψ (IdeleGroup.diagonal E γ) = 0) :
    ∃ A : ℂ, ∀ y, ψ y = A * (Real.log (IdeleGroup.ideleModule E y : ℝ) : ℂ) := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  let s := moduleSection w
  have h1 : ψ 1 = 0 := by
    have h := hadd 1 1
    rw [mul_one] at h
    linear_combination -h
  let e : ℝ → {r : ℝ // 0 < r} := fun u => ⟨Real.exp u, Real.exp_pos u⟩
  let fA : ℝ →+ ℂ :=
    { toFun := fun u => ψ (s (e u))
      map_zero' := by
        have : e 0 = 1 := Subtype.ext Real.exp_zero
        simp only [this, map_one, h1]
      map_add' := fun u v => by
        have : e (u + v) = e u * e v := Subtype.ext (Real.exp_add u v)
        simp only [this, map_mul, hadd] }
  have hfc : Continuous fA :=
    hψ.comp ((continuous_moduleSection w).comp (Real.continuous_exp.subtype_mk _))
  let L := fA.toRealLinearMap hfc
  have hL : ∀ u : ℝ, fA u = u * fA 1 := fun u => by
    have h := L.map_smul u 1
    simp only [smul_eq_mul, mul_one, Complex.real_smul, L, AddMonoidHom.coe_toRealLinearMap] at h
    exact h
  refine ⟨fA 1, fun y => ?_⟩
  set r := IdeleGroup.ideleModule E y with hr
  have hsplit : y = (y * (s r)⁻¹) * s r := by group
  have hr' : e (Real.log r) = r := Subtype.ext (Real.exp_log r.2)
  have hz : ψ (y * (s r)⁻¹) = 0 :=
    eq_zero_of_mem_normOne ψ hψ hadd hE (by exact mul_inv_moduleSection_mem w y)
  have hs : ψ (s r) = fA (Real.log r) := by
    show ψ (s r) = ψ (s (e (Real.log r)))
    rw [hr']
  rw [hsplit, hadd, hz, zero_add, hs, hL, mul_comm]

end OnE

theorem exists_eq_mul_log_absE : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (φ : (AE F E)ˣ → ℂ), Continuous φ → (∀ s t, φ (s * t) = φ s + φ t) →
    (∀ γ : Eˣ, φ (Units.map (inclR (F := F) (AF F)).toMonoidHom γ) = 0) →
    ∃ A : ℂ, ∀ t, φ t = A * ((Real.log (absE F E t : ℝ) : ℝ) : ℂ) := by
  intro F E _ _ _ _ _ φ hφ hadd hE
  have hdiag : ∀ γ : Eˣ, ofE F E (IdeleGroup.diagonal E γ) = Units.map (inclR (F := F) (AF F)).toMonoidHom γ :=
    fun γ => by rw [← toE_inclR F E, ofE_toE]
  obtain ⟨A, hA⟩ := exists_log_of_ideleGroup (fun y => φ (ofE F E y)) (hφ.comp (continuous_ofE F E))
    (fun s t => by simp only [map_mul, hadd]) (fun γ => by simp only [hdiag, hE])
  refine ⟨A, fun t => ?_⟩
  have h := hA (toE F E t)
  rw [ofE_toE] at h
  rw [h, absE_eq_ideleModule F E]

end GlobalTheory.IdeleLogHom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousMixedSymm
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
open GlobalTheory.ArchDecay

noncomputable section

namespace GlobalTheory.ArchDecay

variable (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]

theorem continuous_mixedSymm : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
  refine continuous_pi fun v => ?_
  rcases v.isReal_or_isComplex with hv | hv
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_fst).congr fun y =>
      (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_snd).congr fun y =>
      (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm

theorem continuous_mixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  change Continuous fun x : InfiniteAdeleRing F =>
    ((fun (v : {w : InfinitePlace F // w.IsReal}) => InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
     (fun (v : {w : InfinitePlace F // w.IsComplex}) => InfinitePlace.Completion.extensionEmbedding v.1 (x v)))
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)

theorem continuous_infAd : Continuous (infAd F) :=
  (continuous_mixedSymm F).prodMk continuous_const

theorem continuous_evI_arch : Continuous (evI F) := (continuous_mixed F).comp continuous_fst

@[simp] theorem evI_infAd (a : mixedEmbedding.mixedSpace F) : evI F (infAd F a) = a := by
  simp [evI, infAd]

theorem infAd_add (a b : mixedEmbedding.mixedSpace F) : infAd F (a + b) = infAd F a + infAd F b := by
  unfold infAd; rw [map_add, map_add]; rfl

theorem infAd_zero : infAd F 0 = 0 := by unfold infAd; rw [map_zero, map_zero]; rfl

theorem evI_add' (a b : AF F) : evI F (a + b) = evI F a + evI F b := by
  exact map_add ((InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp
    (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))) a b

theorem evI_zero' : evI F 0 = 0 := by
  exact map_zero ((InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp
    (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)))

abbrev dimA : ℕ := Module.finrank ℝ (κ → mixedEmbedding.mixedSpace F)

def ubasis : Module.Basis (Fin (dimA F κ)) ℝ (κ → mixedEmbedding.mixedSpace F) :=
  (Module.finBasis ℝ _).unitsSMul fun j =>
    Units.mk0 ‖Module.finBasis ℝ (κ → mixedEmbedding.mixedSpace F) j‖⁻¹
      (inv_ne_zero (norm_ne_zero_iff.2 ((Module.finBasis ℝ _).ne_zero j)))

theorem norm_ubasis (j : Fin (dimA F κ)) : ‖ubasis F κ j‖ = 1 := by
  have h := norm_ne_zero_iff.2 ((Module.finBasis ℝ (κ → mixedEmbedding.mixedSpace F)).ne_zero j)
  simp [ubasis, Module.Basis.unitsSMul_apply, norm_smul, h]

def archIn : (Fin (dimA F κ) → ℝ) →+ (κ → AF F) where
  toFun t := fun i => infAd F ((ubasis F κ).equivFun.symm t i)
  map_zero' := by funext i; rw [map_zero]; exact infAd_zero F
  map_add' s t := by funext i; rw [map_add]; exact infAd_add F _ _

def archOut : (κ → AF F) →+ (Fin (dimA F κ) → ℝ) where
  toFun x := (ubasis F κ).equivFun (arch F x)
  map_zero' := by
    have : arch F (0 : κ → AF F) = 0 := by funext i; exact evI_zero' F
    rw [this, map_zero]
  map_add' x y := by
    have : arch F (x + y) = arch F x + arch F y := by funext i; exact evI_add' F _ _
    rw [this, map_add]

theorem archIn_apply (t : Fin (dimA F κ) → ℝ) (i : κ) :
    archIn F κ t i = infAd F ((ubasis F κ).equivFun.symm t i) := rfl

theorem archOut_apply (x : κ → AF F) : archOut F κ x = (ubasis F κ).equivFun (arch F x) := rfl

@[simp] theorem archOut_archIn (t : Fin (dimA F κ) → ℝ) : archOut F κ (archIn F κ t) = t := by
  have : arch F (archIn F κ t) = (ubasis F κ).equivFun.symm t := by funext i; simp [arch, archIn_apply]
  rw [archOut_apply, this, LinearEquiv.apply_symm_apply]

theorem continuous_archIn : Continuous (archIn F κ) := by
  refine continuous_pi fun i => ?_
  show Continuous fun t => infAd F ((ubasis F κ).equivFun.symm t i)
  exact (continuous_infAd F).comp ((continuous_apply i).comp
    (LinearMap.continuous_of_finiteDimensional (ubasis F κ).equivFun.symm.toLinearMap))

theorem continuous_archOut : Continuous (archOut F κ) := by
  show Continuous fun x => (ubasis F κ).equivFun (arch F x)
  exact (LinearMap.continuous_of_finiteDimensional (ubasis F κ).equivFun.toLinearMap).comp
    (continuous_pi fun i => (continuous_evI_arch F).comp (continuous_apply i))

def perSet (m : ℕ) : Set (κ → AF F) :=
  {z | ∀ i, ∃ a : AF F, evI F a = 0 ∧ (∀ v, evFin F v a ∈ v.adicCompletionIntegers F) ∧ z i = (m : AF F) * a}

theorem per_iff (m : ℕ) (f : (κ → AF F) → ℂ) : Per F m f ↔ ∀ x, ∀ z ∈ perSet F κ m, f (x + z) = f x :=
  ⟨fun h x z hz => h x z hz, fun h x z hz => h x z hz⟩

def slab (m : ℕ) : Set (κ → AF F) := {w | w - archIn F κ (archOut F κ w) ∈ perSet F κ m}

def cube (N : ℕ) : Set (Fin N → ℝ) := Set.univ.pi fun _ => Set.Icc (0 : ℝ) 1

end GlobalTheory.ArchDecay
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactConeDiagonalConjUpperTriangularStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compact_coneDiagonal_conj_upperTriangular : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ω : Set (GL (Fin a) (Cinf E))), IsCompact ω → (∀ b ∈ ω, b.val.BlockTriangular id) → ∀ t : ℝ, 0 < t → ∃ Ω : Set (GL (Fin a) (Cinf E)), IsCompact Ω ∧ ∀ (r : Fin a → ℝ) (d : GL (Fin a) (Cinf E)), (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) → ∀ b ∈ ω, d⁻¹ * b * d ∈ Ω := by
  first | exact @GlobalTheory.upperCone_conj_compact | exact GlobalTheory.upperCone_conj_compact | (intros; apply GlobalTheory.upperCone_conj_compact <;> assumption)
end

