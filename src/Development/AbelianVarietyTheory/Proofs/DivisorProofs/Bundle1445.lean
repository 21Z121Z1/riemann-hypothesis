import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0764
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0189
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1438
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1424
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSplitFinMulSplitInf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1425
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.Bundle0025
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1407

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermModerateGrowth
section
noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.AutGrowth

namespace GlobalTheory.ConstTermGrowth

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem continuous_pInf_alt : Continuous (pInf E) :=
  continuous_pi fun w =>
    ((InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)).comp continuous_fst

theorem continuous_mapInf : Continuous (Matrix.GeneralLinearGroup.map (n := Fin a) (pInf E)) :=
  Continuous.units_map _ (continuous_id.matrix_map continuous_pInf_alt)

theorem continuous_mapFin : Continuous (Matrix.GeneralLinearGroup.map (n := Fin a) (pFin E)) :=
  Continuous.units_map _ (continuous_id.matrix_map (continuous_snd : Continuous (pFin E)))

omit [IsTotallyComplex E] in

theorem height_mul_left_le {Ω : Set (GL (Fin a) (Cinf E))} (hΩ : IsCompact Ω) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ c ∈ Ω, ∀ y : GL (Fin a) (Cinf E), height (c * y) ≤ B * height y := by
  have c1 : Continuous fun u : GL (Fin a) (Cinf E) => toL u.val :=
    (Units.continuous_val : Continuous fun u : GL (Fin a) (Cinf E) => u.val)
  have c2 : Continuous fun u : GL (Fin a) (Cinf E) => toL (u⁻¹).val :=
    (Units.continuous_coe_inv : Continuous fun u : GL (Fin a) (Cinf E) => (u⁻¹).val)
  obtain ⟨M1, h1⟩ := hΩ.exists_bound_of_continuousOn c1.continuousOn
  obtain ⟨M2, h2⟩ := hΩ.exists_bound_of_continuousOn c2.continuousOn
  have M0 : (0 : ℝ) ≤ max 0 (max M1 M2) := le_max_left _ _
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  refine ⟨1 + a * max 0 (max M1 M2), by positivity, fun c hc y => ?_⟩
  have m1 : ‖toL c.val‖ ≤ max 0 (max M1 M2) := (h1 c hc).trans ((le_max_left _ _).trans (le_max_right _ _))
  have m2 : ‖toL (c⁻¹).val‖ ≤ max 0 (max M1 M2) := (h2 c hc).trans ((le_max_right _ _).trans (le_max_right _ _))
  have e2 : ((c * y)⁻¹ : GL (Fin a) (Cinf E)).val = (y⁻¹).val * (c⁻¹).val := by
    rw [_root_.mul_inv_rev]; rfl
  have p1 := norm_toL_mul_le c.val y.val
  have p2 := norm_toL_mul_le (y⁻¹).val (c⁻¹).val
  have n1 := norm_nonneg (toL y.val)
  have n2 := norm_nonneg (toL (y⁻¹).val)
  have q1 : (a : ℝ) * (‖toL c.val‖ * ‖toL y.val‖) ≤ a * max 0 (max M1 M2) * ‖toL y.val‖ := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right m1 n1) ha
  have q2 : (a : ℝ) * (‖toL (y⁻¹).val‖ * ‖toL (c⁻¹).val‖) ≤ a * max 0 (max M1 M2) * ‖toL (y⁻¹).val‖ := by
    calc (a : ℝ) * (‖toL (y⁻¹).val‖ * ‖toL (c⁻¹).val‖) ≤ a * (‖toL (y⁻¹).val‖ * max 0 (max M1 M2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left m2 n2) ha
      _ = _ := by ring
  have aM : (0 : ℝ) ≤ a * max 0 (max M1 M2) := by positivity
  unfold height
  rw [show toL (c * y).val = toL (c.val * y.val) from rfl, e2]
  nlinarith

theorem uniform_growth (φ : Sm E a) (hopen : IsOpen {k | finRep E a k φ = φ})
    (hgr : ∀ g, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖φ.1 (g * infGL E a y)‖ ≤ C * height y ^ N)
    {Ω : Set (GA E a)} (hΩ : IsCompact Ω) :
    ∃ (C : ℝ) (N : ℕ), ∀ h ∈ Ω, ∀ y, ‖φ.1 (h * infGL E a y)‖ ≤ C * height y ^ N := by
  have hS : ∀ s : GL (Fin a) (Af E), finRep E a s φ = φ → ∀ x, φ.1 (x * finGL E a s) = φ.1 x := fun s hs x => by
    have := congrFun (congrArg Subtype.val hs) x
    exact this
  have hU : ∀ t : GL (Fin a) (Af E), IsOpen ((fun k => t⁻¹ * k) ⁻¹' {k | finRep E a k φ = φ}) := fun t =>
    hopen.preimage (continuous_const.mul continuous_id)
  have hKf : IsCompact (Matrix.GeneralLinearGroup.map (n := Fin a) (pFin E) '' Ω) := hΩ.image continuous_mapFin
  obtain ⟨T, hT⟩ := hKf.elim_finite_subcover (fun t => (fun k => t⁻¹ * k) ⁻¹' {k | finRep E a k φ = φ}) hU
    (fun k _ => Set.mem_iUnion.2 ⟨k, by
      change finRep E a (k⁻¹ * k) φ = φ
      rw [inv_mul_cancel, map_one]; rfl⟩)
  choose C N hCN using hgr
  obtain ⟨B, hB0, hB⟩ := height_mul_left_le (hΩ.image (continuous_mapInf (E := E) (a := a)))
  refine ⟨∑ t ∈ T, |C (finGL E a t)| * B ^ N (finGL E a t), ∑ t ∈ T, N (finGL E a t), fun h hh y => ?_⟩
  obtain ⟨t, htT, hkt⟩ := Set.mem_iUnion₂.1 (hT ⟨h, hh, rfl⟩)
  have e : h * infGL E a y = finGL E a t * infGL E a (Matrix.GeneralLinearGroup.map (pInf E) h * y) *
      finGL E a (t⁻¹ * Matrix.GeneralLinearGroup.map (pFin E) h) := by
    apply ga_ext
    · simp only [map_mul, pInf_infGL, pInf_finGL, one_mul, mul_one]
    · simp only [map_mul, pFin_infGL, pFin_finGL, one_mul, mul_one, mul_inv_cancel_left]
  rw [e, hS _ hkt]
  have hcy := hB _ ⟨h, hh, rfl⟩ y
  have h0 := one_le_height (Matrix.GeneralLinearGroup.map (pInf E) h * y)
  have hy := one_le_height y
  calc ‖φ.1 (finGL E a t * infGL E a (Matrix.GeneralLinearGroup.map (pInf E) h * y))‖
      ≤ C (finGL E a t) * height (Matrix.GeneralLinearGroup.map (pInf E) h * y) ^ N (finGL E a t) := hCN _ _
    _ ≤ |C (finGL E a t)| * (B * height y) ^ N (finGL E a t) :=
        mul_le_mul (le_abs_self _) (pow_le_pow_left₀ (by linarith) hcy _) (pow_nonneg (by linarith) _) (abs_nonneg _)
    _ = |C (finGL E a t)| * B ^ N (finGL E a t) * height y ^ N (finGL E a t) := by ring
    _ ≤ |C (finGL E a t)| * B ^ N (finGL E a t) * height y ^ (∑ t ∈ T, N (finGL E a t)) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hy
          (Finset.single_le_sum (f := fun t => N (finGL E a t)) (fun _ _ => Nat.zero_le _) htT))
          (mul_nonneg (abs_nonneg _) (pow_nonneg hB0 _))
    _ ≤ (∑ t ∈ T, |C (finGL E a t)| * B ^ N (finGL E a t)) * height y ^ (∑ t ∈ T, N (finGL E a t)) :=
        mul_le_mul_of_nonneg_right (Finset.single_le_sum (f := fun t => |C (finGL E a t)| * B ^ N (finGL E a t))
          (fun _ _ => mul_nonneg (abs_nonneg _) (pow_nonneg hB0 _)) htT) (pow_nonneg (by linarith) _)

theorem norm_constTerm_le : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ)
    [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E))
    (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 →
    ∀ φ : Sm E a, (∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g) → IsOpen {k | finRep E a k φ = φ} →
    (∀ g, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖φ.1 (g * infGL E a y)‖ ≤ C * height y ^ N) →
    ∀ g, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖∫ x in 𝓕, φ.1 (unip x * (g * infGL E a y)) ∂μ‖ ≤ C * height y ^ N := by
  intro E _ _ _ a r _ _ μ 𝓕 _ _ h1 φ hleft hopen hgr g
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.ConstNotCusp.exists_compact_ratN E a r
  have hc : Continuous fun x : BlockIx a r → Ad E => unip x * g :=
    GlobalTheory.CuspRep.CuspidalL2GL.continuous_unip.mul continuous_const
  obtain ⟨C, N, hC⟩ := uniform_growth φ hopen hgr (hK.image hc)
  refine ⟨C, N, fun y => ?_⟩
  have hb : ∀ x : BlockIx a r → Ad E, ‖φ.1 (unip x * (g * infGL E a y))‖ ≤ C * height y ^ N := by
    intro x
    obtain ⟨γ, ⟨z, rfl⟩, hγ⟩ := hcov x
    have hu : unip ((AddMonoidHom.compLeft (algebraMap E (Ad E)).toAddMonoidHom (BlockIx a r)) z) =
        ratGL E a (unip z) := unip_algebraMap z
    have e : φ.1 (unip (AddMonoidHom.compLeft (algebraMap E (Ad E)).toAddMonoidHom (BlockIx a r) z + x) * g *
        infGL E a y) = φ.1 (unip x * (g * infGL E a y)) := by
      rw [unip_add, hu]
      simp only [mul_assoc]
      exact hleft _ _
    rw [← e]
    exact hC _ ⟨_, hγ, rfl⟩ y
  have hfin : μ 𝓕 < ⊤ := by rw [h1]; exact ENNReal.one_lt_top
  calc _ ≤ C * height y ^ N * (μ 𝓕).toReal := norm_setIntegral_le_of_norm_le_const hfin (fun x _ => hb x)
    _ = C * height y ^ N := by rw [h1]; simp

end GlobalTheory.ConstTermGrowth

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermUnipotentIntegral
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.UnipCT
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem topFacts (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    IsTopologicalGroup (UA σ J) ∧ LocallyCompactSpace (UA σ J) ∧ SecondCountableTopology (UA σ J) ∧ T2Space (UA σ J) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : LocallyCompactSpace (AE F E) := e.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E) := e.secondCountableTopology
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (AE F E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → AE F E))
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (AE F E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : LocallyCompactSpace (GL (Fin n) (AE F E)) :=
    Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (AE F E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → AE F E))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (AE F E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology (GL (Fin n) (AE F E)) :=
    Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : T2Space (GL (Fin n) (AE F E)) := Units.isEmbedding_embedProduct.t2Space
  have hcA : Continuous (cA (F := F) σ) := by
    exact IsModuleTopology.continuous_of_linearMap (cA (F := F) σ).toLinearMap
  have hc : IsClosed (UG (cA σ) (incM F J) : Set (GL (Fin n) (AE F E))) := by
    have hv : Continuous fun g : GL (Fin n) (AE F E) => (g : Matrix (Fin n) (Fin n) (AE F E)) :=
      Units.continuous_val
    exact isClosed_eq (((hv.matrix_transpose.matrix_mul continuous_const).matrix_mul
      (hv.matrix_map hcA))) continuous_const
  exact ⟨inferInstance, hc.isClosedEmbedding_subtypeVal.locallyCompactSpace,
    hc.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology, inferInstance⟩

theorem setIntegral_fd_eq {N : Type} [Group N] [TopologicalSpace N] [IsTopologicalGroup N] [LocallyCompactSpace N]
    [SecondCountableTopology N] [T2Space N] [MeasurableSpace N] [BorelSpace N] (Γ : Subgroup N) [Countable Γ]
    (g : N → ℂ) (hg : ∀ γ ∈ Γ, ∀ x, g (γ * x) = g x)
    (μ μ₀ : Measure N) [μ.IsHaarMeasure] [μ₀.IsHaarMeasure] (𝓕 𝓕₀ : Set N)
    (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (h𝓕₀ : IsFundamentalDomain Γ 𝓕₀ μ₀) (h1 : μ 𝓕 = 1) (h₀ : μ₀ 𝓕₀ = 1) :
    ∫ x in 𝓕, g x ∂μ = ∫ x in 𝓕₀, g x ∂μ₀ := by
  letI : MeasurableSpace Γ := ⊤
  haveI : MeasurableSMul Γ N :=
    { measurable_const_smul := fun γ => measurable_const_mul (γ : N)
      measurable_smul_const := fun _ => measurable_from_top }
  have hs := Measure.isMulLeftInvariant_eq_smul μ μ₀
  have hc : Measure.haarScalarFactor μ μ₀ ≠ 0 := (Measure.haarScalarFactor_pos_of_isHaarMeasure μ μ₀).ne'
  have h𝓕' : IsFundamentalDomain Γ 𝓕 μ₀ := by
    refine h𝓕.mono ?_
    rw [hs]; exact Measure.absolutelyContinuous_smul (by exact_mod_cast hc)
  have hm : μ₀ 𝓕 = 1 := (h𝓕'.measure_eq h𝓕₀).trans h₀
  have hc1 : Measure.haarScalarFactor μ μ₀ = 1 := by
    have h2 := h1; rw [hs, Measure.smul_apply, hm] at h2
    simpa using h2
  have hμ : μ = μ₀ := by rw [hs, hc1, one_smul]
  subst hμ
  exact h𝓕'.setIntegral_eq h𝓕₀ (fun γ x => hg γ γ.2 x)

theorem mat_mul' {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g h : UA σ J) : mat (g * h) = mat g * mat h := rfl

theorem mat_inv_mul' {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) : mat g⁻¹ * mat g = 1 := by
  show (g.1⁻¹ * g.1 : GL (Fin n) (AE F E)).1 = 1
  simp

theorem isClosed_line {d : ℕ} (x : Fin d → E) :
    IsClosed (Set.range fun a : AE F E => a • incV F x) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  by_cases hx : x = 0
  · subst hx
    have h0 : incV F (0 : Fin d → E) = 0 := by ext i; simp [incV]
    have : (Set.range fun a : AE F E => a • incV F (0 : Fin d → E)) = {0} := by
      ext v; simp [h0, eq_comm]
    rw [this]; exact isClosed_singleton
  · obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
    set c : AE F E := inclR (F := F) (AF F) (x i)⁻¹
    have hxc : inclR (F := F) (AF F) (x i) * c = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hi, map_one]
    have : (Set.range fun a : AE F E => a • incV F x) = {v | v = (v i * c) • incV F x} := by
      ext v
      simp only [Set.mem_range, Set.mem_setOf_eq]
      constructor
      · rintro ⟨a, rfl⟩
        congr 1
        simp only [Pi.smul_apply, smul_eq_mul, incV]
        rw [mul_assoc, hxc, mul_one]
      · intro h; exact ⟨_, h.symm⟩
    rw [this]
    exact isClosed_eq continuous_id (((continuous_apply i).mul continuous_const).smul continuous_const)

variable (σ) in

def unipSet {d d₁ : ℕ} (W : Spc F E d) (H' : Plane E d d₁) : Subgroup (UA σ W.J) where
  carrier := {u | mat u *ᵥ incV F H'.x = incV F H'.x ∧
    ∀ z, ∃ a : AE F E, mat u *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z + a • incV F H'.x}
  one_mem' := by
    refine ⟨by simp [mat], fun z => ⟨0, by simp [mat]⟩⟩
  mul_mem' := by
    rintro u v ⟨hu1, hu2⟩ ⟨hv1, hv2⟩
    refine ⟨by rw [mat_mul', ← Matrix.mulVec_mulVec, hv1, hu1], fun z => ?_⟩
    obtain ⟨a, ha⟩ := hu2 z
    obtain ⟨b, hb⟩ := hv2 z
    refine ⟨a + b, ?_⟩
    rw [mat_mul', ← Matrix.mulVec_mulVec, hb, Matrix.mulVec_add, Matrix.mulVec_smul, hu1, ha, add_smul, add_assoc]
  inv_mem' := by
    rintro u ⟨hu1, hu2⟩
    have h1 : mat u⁻¹ *ᵥ incV F H'.x = incV F H'.x := by
      conv_lhs => rw [← hu1]
      rw [Matrix.mulVec_mulVec, mat_inv_mul', Matrix.one_mulVec]
    refine ⟨h1, fun z => ?_⟩
    obtain ⟨a, ha⟩ := hu2 z
    refine ⟨-a, ?_⟩
    have h2 : mat u⁻¹ *ᵥ (mat u *ᵥ (incM F H'.ι *ᵥ z)) = incM F H'.ι *ᵥ z := by
      rw [Matrix.mulVec_mulVec, mat_inv_mul', Matrix.one_mulVec]
    rw [ha, Matrix.mulVec_add, Matrix.mulVec_smul, h1] at h2
    rw [neg_smul, ← sub_eq_add_neg, eq_sub_iff_add_eq]; exact h2

theorem unip_eq {d d₁ : ℕ} (σ : E →ₐ[F] E) (W : Spc F E d) (H' : Plane E d d₁) : unip σ W H' = unipSet σ W H' :=
  le_antisymm ((Subgroup.closure_le _).2 fun _ h => h) fun _ h => Subgroup.subset_closure h

theorem isClosed_unip {d d₁ : ℕ} (σ : E →ₐ[F] E) (W : Spc F E d) (H' : Plane E d d₁) :
    IsClosed ((unip σ W H' : Subgroup (UA σ W.J)) : Set (UA σ W.J)) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  have hm : Continuous fun g : UA σ W.J => mat g := Units.continuous_val.comp continuous_subtype_val
  rw [unip_eq]
  have hS : ((unipSet σ W H' : Subgroup (UA σ W.J)) : Set (UA σ W.J)) = {u | mat u *ᵥ incV F H'.x = incV F H'.x} ∩
      ⋂ z, {u : UA σ W.J | ∃ a : AE F E, mat u *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z + a • incV F H'.x} := by
    ext u; simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]; rfl
  rw [hS]
  refine (isClosed_eq (hm.matrix_mulVec continuous_const) continuous_const).inter (isClosed_iInter fun z => ?_)
  have : {u : UA σ W.J | ∃ a : AE F E, mat u *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z + a • incV F H'.x} =
      (fun u : UA σ W.J => mat u *ᵥ (incM F H'.ι *ᵥ z) - incM F H'.ι *ᵥ z) ⁻¹' Set.range fun a : AE F E => a • incV F H'.x := by
    ext u; simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_range]
    exact exists_congr fun a => by rw [eq_sub_iff_add_eq', eq_comm]
  rw [this]
  exact (isClosed_line H'.x).preimage ((hm.matrix_mulVec continuous_const).sub continuous_const)

theorem countable_ratU {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Countable (ratU σ J) := by
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin n) (Fin n) E) := inferInstanceAs (Countable (Fin n → Fin n → E))
  haveI : Countable (GL (Fin n) E) :=
    Function.Injective.countable (f := fun g : GL (Fin n) E => (g.1, g.inv)) fun g h hgh => Units.ext (congrArg Prod.fst hgh)
  have hr : Set.Countable (((Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F))).range :
      Subgroup (GL (Fin n) (AE F E))) : Set (GL (Fin n) (AE F E))) := by
    rw [MonoidHom.coe_range]; exact Set.countable_range _
  haveI := hr.to_subtype
  exact Function.Injective.countable (f := fun g : ratU σ J => (⟨g.1.1, g.2⟩ : (Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F))).range))
    fun g h hgh => by
      apply Subtype.ext; apply Subtype.ext
      simpa using congrArg Subtype.val hgh

theorem isCT_of_fundamentalDomain : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ → ∀ f : UA σ G.W.J → ℂ, (∀ γ ∈ ratU σ G.W.J, ∀ h, f (γ * h) = f h) → ∀ (μ₀ : Measure (unip σ G.W H')) (𝓕₀ : Set (unip σ G.W H')), μ₀.IsHaarMeasure → IsFundamentalDomain ((ratU σ G.W.J).subgroupOf (unip σ G.W H')) 𝓕₀ μ₀ → μ₀ 𝓕₀ = 1 → IsCT H' f (fun h => ∫ u in 𝓕₀, f (u.1 * h) ∂μ₀) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' _ d₁ W₁ H' i₀ i₁ _ f hf μ₀ 𝓕₀ hμ₀ h𝓕₀ h₀ μ 𝓕 hμ h𝓕 h1 h
  obtain ⟨i1, i2, i3, i4⟩ := topFacts (F := F) σ G.W.J
  haveI : BorelSpace (UA σ G.W.J) := ⟨rfl⟩
  haveI : LocallyCompactSpace (unip σ G.W H') := (isClosed_unip σ G.W H').isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI := countable_ratU (σ := σ) G.W.J
  haveI : Countable ((ratU σ G.W.J).subgroupOf (unip σ G.W H')) :=
    Function.Injective.countable (f := fun g : (ratU σ G.W.J).subgroupOf (unip σ G.W H') => (⟨g.1.1, g.2⟩ : ratU σ G.W.J))
      fun g h hgh => by
        apply Subtype.ext; apply Subtype.ext
        simpa using congrArg Subtype.val hgh
  refine (setIntegral_fd_eq ((ratU σ G.W.J).subgroupOf (unip σ G.W H')) (fun u => f (u.1 * h)) ?_ μ μ₀ 𝓕 𝓕₀ h𝓕 h𝓕₀ h1 h₀).symm
  intro γ hγ x
  show f ((γ.1 * x.1) * h) = f (x.1 * h)
  rw [mul_assoc]; exact hf _ (Subgroup.mem_subgroupOf.1 hγ) _
end GlobalTheory.UnipCT

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalMultiplicityCarriersStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_multiplicity_carriers : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → GoodStable A3.A.X → GlobalTheory.CuspMult.CuspDecomp D → GlobalTheory.CuspMult.MultEq R.toRealDat → (∀ c, R.EEc c ≠ ⊥ → ∃ p, R.Carries p c) → ∀ i, (⨆ p, R.Wp3 i p) = LinearMap.range (eH R.toRealDat i) := by
  first | exact @GlobalTheory.SpanW.iSup_wp3_eq_range_eH | exact GlobalTheory.SpanW.iSup_wp3_eq_range_eH | (intros; apply GlobalTheory.SpanW.iSup_wp3_eq_range_eH <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DHRealAdSmul
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix

noncomputable section

namespace GlobalTheory.ThetaDecay

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def dH (ψ : AddChar (AF F) ℂ) (w : (κ → AF F) × (κ → AF F)) (Φ : (κ → AF F) → ℂ) : (κ → AF F) → ℂ :=
  fun x => deriv (fun t : ℝ => schr ψ (realAd F t • w) Φ x) 0

def wordH (ψ : AddChar (AF F) ℂ) (l : List ((κ → AF F) × (κ → AF F))) (Φ : (κ → AF F) → ℂ) : (κ → AF F) → ℂ :=
  l.foldr (dH ψ) Φ

def IsArch (w : (κ → AF F) × (κ → AF F)) : Prop :=
  ∀ i, At (evI F) (w.1 i) ∧ At (evI F) (w.2 i)

open scoped Classical in

def IsArchUnit (w : (κ → AF F) × (κ → AF F)) : Prop :=
  IsArch w ∧ ∀ i, ‖evI F (w.1 i)‖ ≤ 1 ∧ ‖evI F (w.2 i)‖ ≤ 1

@[simp] theorem wordH_nil (ψ : AddChar (AF F) ℂ) (Φ : (κ → AF F) → ℂ) : wordH ψ [] Φ = Φ := rfl

theorem wordH_cons (ψ : AddChar (AF F) ℂ) (w : (κ → AF F) × (κ → AF F)) (l : List ((κ → AF F) × (κ → AF F)))
    (Φ : (κ → AF F) → ℂ) : wordH ψ (w :: l) Φ = dH ψ w (wordH ψ l Φ) := rfl

theorem dH_smul (ψ : AddChar (AF F) ℂ) (w : (κ → AF F) × (κ → AF F)) (a : ℂ) (Φ : (κ → AF F) → ℂ) :
    dH ψ w (a • Φ) = a • dH ψ w Φ := by
  funext x
  simp only [dH, schr, Pi.smul_apply, smul_eq_mul]
  have : (fun t : ℝ => ψ (x ⬝ᵥ (realAd F t • w).2 + ⅟(2 : AF F) * ((realAd F t • w).1 ⬝ᵥ (realAd F t • w).2)) *
      (a * Φ (x + (realAd F t • w).1))) = fun t => a * (ψ (x ⬝ᵥ (realAd F t • w).2 +
      ⅟(2 : AF F) * ((realAd F t • w).1 ⬝ᵥ (realAd F t • w).2)) * Φ (x + (realAd F t • w).1)) := by
    funext t; ring
  rw [this, deriv_const_mul_field']

theorem realAd_mul (a b : ℝ) : realAd F a * realAd F b = realAd F (a * b) := by
  unfold realAd
  simp only [LinearMap.inl_apply, map_mul]
  refine Prod.ext ?_ ?_
  · show _ * _ = _
    rw [← map_mul]
  · exact mul_zero _

theorem dH_realAd_smul (ψ : AddChar (AF F) ℂ) (c : ℝ) (w : (κ → AF F) × (κ → AF F)) (Φ : (κ → AF F) → ℂ) :
    dH ψ (realAd F c • w) Φ = (c : ℂ) • dH ψ w Φ := by
  funext x
  simp only [dH, Pi.smul_apply, smul_eq_mul]
  have e : (fun t : ℝ => schr ψ (realAd F t • realAd F c • w) Φ x) =
      fun t => (fun s : ℝ => schr ψ (realAd F s • w) Φ x) (c * t) := by
    funext t; rw [smul_smul, realAd_mul, mul_comm t c]
  rw [e]
  have h := deriv_comp_mul_left (f := fun s : ℝ => schr ψ (realAd F s • w) Φ x) (c := c) (x := 0)
  rw [mul_zero, Complex.real_smul] at h
  exact h

theorem isArch_smul {w : (κ → AF F) × (κ → AF F)} (hw : IsArch w) (a : AF F) : IsArch (a • w) := by
  intro i
  refine ⟨fun u hu => ?_, fun u hu => ?_⟩
  · show u * (a * w.1 i) = 0
    rw [mul_left_comm]
    have := (hw i).1 u hu
    simp only [smul_eq_mul] at this
    rw [this, mul_zero]
  · show u * (a * w.2 i) = 0
    rw [mul_left_comm]
    have := (hw i).2 u hu
    simp only [smul_eq_mul] at this
    rw [this, mul_zero]

end GlobalTheory.ThetaDecay

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteUnitaryRationalPointSplitFiniteInfiniteStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct Topology
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteUnitaryRationalPoint_split_finite_infinite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), ∀ γ ∈ ratU E n, ∃ γ₀ : UE E n, splitFin E n γ = finPt γ₀ ∧ ∀ v : InfinitePlace E, cEmb v.embedding γ = GeneralLinearGroup.map v.embedding γ₀.1 := by
  first | exact @GlobalTheory.BCT.RatSplit.ratU_split | exact GlobalTheory.BCT.RatSplit.ratU_split | (intros; apply GlobalTheory.BCT.RatSplit.ratU_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivContinuousCharacterRealUnitaryOneParameterStatement
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deriv_continuous_character_real_unitary_one_parameter : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (β : Type) [Fintype β]
    [DecidableEq β] (R S : InfinitePlace F → ℕ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (J : Matrix β β (AE F E)) (b : ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ), IsCMExt F E σ → (∀ w, IsFrame (b • J.map (piInf (τ w))) (C w)) →
    ∀ ν : UG (cA σ) J → ℂ,
      (∀ g h : UG (cA σ) J, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) → At (evI F) ((h.1 : Matrix β β (AE F E)) - 1) →
        ν (g * h) = ν g * ν h) →
      ContinuousOn ν {g : UG (cA σ) J | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)} →
      (∀ g : UG (cA σ) J, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) → ν g ≠ 0) →
      ∃ k : InfinitePlace F → ℂ, ∀ γ ∈ RLines σ J, ∀ Y, IsGenD τ C γ Y →
        HasDerivAt (fun t : ℝ => ν (γ (Multiplicative.ofAdd t))) (∑ w, k w * (Y w).trace) 0 := by
  first | exact @GlobalTheory.HoweD.deriv_charD | exact GlobalTheory.HoweD.deriv_charD | (intros; apply GlobalTheory.HoweD.deriv_charD <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetColumnsNeZeroOfPointValuesIndependentStatement
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_columns_ne_zero_of_pointValues_independent : ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A] (S : Sys F A), S.Hyp → ∀ (E A' : Type) [Field E] [Algebra F E] [AddCommGroup A'] [Module E A'] (s : Fin S.D → Fin S.N → E) (δ : ℕ) (Φ : S.Flat E A' s δ) (d : ℕ) (b : Module.Basis (Fin d) F (S.V S.T)) (c : Fin d → A →ₗ[F] F), S.IsCo b c → ∀ (col : Fin d → S.Col) (u : Fin (S.D + 1) × Fin S.N → E), LinearIndependent E (fun k => word Φ.mul (fun q j => u ((col k).β q, j)) (Φ.ι (col k).x)) → S.det c col ≠ 0 := by
  first | exact @GlobalTheory.HSShort.DetNe.det_ne_zero_of_indep | exact GlobalTheory.HSShort.DetNe.det_ne_zero_of_indep | (intros; apply GlobalTheory.HSShort.DetNe.det_ne_zero_of_indep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNeZeroOfHasSig
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.SigDet

theorem det_ne_zero_of_hasSig : ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) (r s : ℕ), HasSig M r s → M.det ≠ 0 := by
  intro n M r s h
  obtain ⟨hn, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hn)
  set B : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm with hB
  have key : Bᵀ * M * B.map star = (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).submatrix e.symm e.symm := by
    rw [← hA]
    have t1 : Bᵀ = Aᵀ.submatrix e.symm id := rfl
    have t2 : B.map star = (A.map star).submatrix id e.symm := rfl
    rw [t1, t2, Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id]
    rfl
  have hd := congrArg Matrix.det key
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_mul, Matrix.det_mul] at hd
  intro h0
  rw [h0] at hd
  rw [Matrix.det_neg] at hd
  simp at hd
  exact pow_ne_zero s (neg_ne_zero.mpr one_ne_zero) hd.symm

end GlobalTheory.SigDet
end

