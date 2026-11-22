import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1947
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1950
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1481
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1444
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlanePairRestrictionFirst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1639
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1951
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0072
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0022
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundCmFrameNonvanishingStatement
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1790
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1802
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1732
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1876
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1714
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1916
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1936
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFinitePureTensors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1796
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1952
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1956
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1050

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKOOfIsGLO
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes ValuativeRel
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.StdPairCone
open GlobalTheory.Doubling (absE)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable local instance measFvZetaA {F : Type} [Field F] [NumberField F] (v : Pl F) : MeasurableSpace (Fv F v) := borel _

local instance borelFvZetaA {F : Type} [Field F] [NumberField F] (v : Pl F) : BorelSpace (Fv F v) := ⟨rfl⟩

open GlobalTheory.SplitFlip GlobalTheory.SplitWeil

noncomputable section

namespace GlobalTheory.StdPairZeta
open GlobalTheory.OneSquareZeta

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem blk₁_mul {m a a' : ℕ} (M : Matrix (Fin m) (Fin a) k) (X : Matrix (Fin a) (Fin (a + a')) k) :
    blk₁ (M * X) = M * blk₁ X := by
  ext i j; simp [blk₁, Matrix.mul_apply]

theorem blk₂_mul {m a a' : ℕ} (M : Matrix (Fin m) (Fin a) k) (X : Matrix (Fin a) (Fin (a + a')) k) :
    blk₂ (M * X) = M * blk₂ X := by
  ext i j; simp [blk₂, Matrix.mul_apply]

theorem val_gdet {a : ℕ} (g : GL (Fin a) k) : ((gdet g : kˣ) : k) = g.val.det := by
  first | rfl | exact Matrix.GeneralLinearGroup.val_det_apply g

theorem isGLO_of_mem_KO {a : ℕ} {g : GL (Fin a) k} (hg : g ∈ KO k (Fin a)) : g.val.det ≠ 0 ∧ IsGLO g.val := by
  have hv : valuation k g.val.det = 1 := by rw [← val_gdet]; exact GlobalTheory.SplitFlip.valuation_gdet_of_mem_KO hg
  exact ⟨fun h => by simp [h] at hv, ((GlobalTheory.SplitFlip.mem_KO_iff g).1 hg).1, hv⟩

theorem mem_KO_of_isGLO {a : ℕ} (g : GL (Fin a) k) (h : IsGLO g.val) : g ∈ KO k (Fin a) := by
  obtain ⟨hM, hd⟩ := h
  let A : Matrix (Fin a) (Fin a) 𝒪[k] := fun i j => ⟨g.val i j, hM i j⟩
  have e : (algebraMap 𝒪[k] k).mapMatrix A = g.val := rfl
  have hu : IsUnit A.det := by
    refine (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.2 ?_
    rw [RingHom.map_det, e, hd]
  obtain ⟨u, hu'⟩ := (Matrix.isUnit_iff_isUnit_det A).2 hu
  refine ⟨u, Units.ext ?_⟩
  change (algebraMap 𝒪[k] k).mapMatrix u.val = g.val
  rw [hu', e]

theorem mul_mem_cball {n m p : ℕ} {s : kˣ} {M : Matrix (Fin n) (Fin m) k} {Y : Matrix (Fin m) (Fin p) k}
    (hM : ∀ i j, M i j ∈ 𝒪[k]) (hY : ∀ i j, Y i j ∈ GlobalTheory.SplitWeil.cball s) :
    ∀ i j, (M * Y) i j ∈ GlobalTheory.SplitWeil.cball s := by
  intro i j
  simp only [GlobalTheory.SplitWeil.cball, Set.mem_setOf_eq, Matrix.mul_apply] at hY ⊢
  refine Valuation.map_sum_le _ fun l _ => ?_
  rw [map_mul]
  exact (mul_le_mul' ((Valuation.mem_integer_iff _ _).1 (hM i l)) (hY l j)).trans_eq (one_mul _)

variable [MeasurableSpace k] [BorelSpace k]

theorem bigF_stdA_zero (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c a a' : ℕ) (X : Matrix (Fin a) (Fin (a + a')) k)
    (hX : (blk₁ X).det = 0) : bigF (haarVol (KO k (Fin a))) ϖ ν (stdA ν ϖ c a a') X = 0 := by
  have h0 : ∀ g : Matrix (Fin a) (Fin a) k, stdA ν ϖ c a a' (g * X) = 0 := by
    intro g
    unfold stdA
    rw [dif_neg]
    rintro ⟨h, -⟩
    exact h (by rw [blk₁_mul, Matrix.det_mul, hX, mul_zero])
  simp [bigF, shellSum, shell, h0]

theorem bigF_stdA_eq (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c a a' : ℕ) (hϖ : IsUnif ϖ) (X : Matrix (Fin a) (Fin (a + a')) k)
    (g₁ : GL (Fin a) k) (hg₁ : g₁.val = blk₁ X) :
    bigF (haarVol (KO k (Fin a))) ϖ ν (stdA ν ϖ c a a') X =
      (((ν (gdet g₁))⁻¹ : ℂˣ) : ℂ) * apow (gdet g₁) (-((Fintype.card (Fin (a + a')) : ℂ) / 2)) *
        Set.indicator {M : Matrix (Fin a) (Fin a') k | ∀ i j, M i j ∈ cball (ϖ ^ c)} 1 ((g₁⁻¹).val * blk₂ X) := by
  set N : ℂ := (Fintype.card (Fin (a + a')) : ℂ) / 2 with hN
  set Y := (g₁⁻¹).val * blk₂ X with hY
  set C : ℂ := (((ν (gdet g₁))⁻¹ : ℂˣ) : ℂ) * apow (gdet g₁) (-N) *
      Set.indicator {M : Matrix (Fin a) (Fin a') k | ∀ i j, M i j ∈ cball (ϖ ^ c)} 1 Y with hC
  set S : Set (GL (Fin a) k) := (fun g => g * g₁) ⁻¹' (KO k (Fin a) : Set (GL (Fin a) k)) with hSdef
  have hSm : @MeasurableSet (GL (Fin a) k) Units.instMeasurableSpace S := by
    letI : MeasurableSpace (GL (Fin a) k) := Units.instMeasurableSpace
    haveI : BorelSpace (GL (Fin a) k) := borel_GL
    exact (isOpen_KO.preimage (continuous_mul_right _)).measurableSet
  have hS1 : (haarVol (KO k (Fin a))).real S = 1 := by
    simp [hSdef, Measure.real, measure_preimage_mul_right, haarVol_self isOpen_KO le_rfl]
  have hint : ∀ g : GL (Fin a) k, stdA ν ϖ c a a' (g.val * X) * (ν (gdet g) : ℂ) * apow (gdet g) N =
      S.indicator (fun _ => C) g := by
    intro g
    have h1 : blk₁ (g.val * X) = (g * g₁).val := by rw [blk₁_mul, Units.val_mul, hg₁]
    have h2 : blk₂ (g.val * X) = (g * g₁).val * Y := by
      rw [blk₂_mul, hY, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel_right]
    by_cases hg : g ∈ S
    · rw [Set.indicator_of_mem hg]
      have hκ : g * g₁ ∈ KO k (Fin a) := hg
      obtain ⟨hdet, hglo⟩ := isGLO_of_mem_KO hκ
      have hv : valuation k ((gdet (g * g₁) : kˣ) : k) = 1 := GlobalTheory.SplitFlip.valuation_gdet_of_mem_KO hκ
      have hinv : (g * g₁)⁻¹ ∈ KO k (Fin a) := inv_mem hκ
      have hYiff : (∀ i j, ((g * g₁).val * Y) i j ∈ cball (ϖ ^ c)) ↔ ∀ i j, Y i j ∈ cball (ϖ ^ c) := by
        constructor
        · intro h
          have e : Y = ((g * g₁)⁻¹).val * ((g * g₁).val * Y) := by
            rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
          rw [e]; exact mul_mem_cball ((GlobalTheory.SplitFlip.mem_KO_iff _).1 hinv).1 h
        · exact mul_mem_cball ((GlobalTheory.SplitFlip.mem_KO_iff _).1 hκ).1
      have hap : apow (gdet g) N = apow (gdet g₁) (-N) := by
        have : gdet g = gdet (g * g₁) * (gdet g₁)⁻¹ := by rw [gdet_mul]; group
        rw [this, apow_mul, apow_of_valuation_eq_one hv, one_mul, apow_inv]
      unfold stdA
      by_cases hc : ∀ i j, Y i j ∈ cball (ϖ ^ c)
      · have hcond : (blk₁ (g.val * X)).det ≠ 0 ∧ IsGLO (blk₁ (g.val * X)) ∧
            ∀ i j, blk₂ (g.val * X) i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c) := by
          rw [h1, h2]; exact ⟨hdet, hglo, hYiff.2 hc⟩
        have hmk : Units.mk0 _ hcond.1 = gdet g * gdet g₁ := by
          rw [← gdet_mul]; exact Units.ext (by rw [Units.val_mk0, val_gdet, h1])
        rw [dif_pos hcond, hC, Set.indicator_of_mem (show Y ∈ {M : Matrix (Fin a) (Fin a') k |
          ∀ i j, M i j ∈ cball (ϖ ^ c)} from hc), Pi.one_apply, mul_one, hmk, hap, map_mul, mul_inv]
        simp only [Units.val_mul, Units.val_inv_eq_inv_val]
        have h3 := (ν (gdet g)).ne_zero
        linear_combination ((ν (gdet g₁) : ℂ))⁻¹ * apow (gdet g₁) (-N) * inv_mul_cancel₀ h3
      · have hneg : ¬ ((blk₁ (g.val * X)).det ≠ 0 ∧ IsGLO (blk₁ (g.val * X)) ∧
            ∀ i j, blk₂ (g.val * X) i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c)) := by
          rintro ⟨-, -, h⟩
          rw [h2] at h
          exact hc (hYiff.1 h)
        rw [dif_neg hneg, hC, Set.indicator_of_notMem (show Y ∉ {M : Matrix (Fin a) (Fin a') k |
          ∀ i j, M i j ∈ cball (ϖ ^ c)} from hc)]
        simp
    · rw [Set.indicator_of_notMem hg]
      have hneg : ¬ ((blk₁ (g.val * X)).det ≠ 0 ∧ IsGLO (blk₁ (g.val * X)) ∧
          ∀ i j, blk₂ (g.val * X) i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c)) := by
        rintro ⟨-, hglo, -⟩
        rw [h1] at hglo
        exact hg (mem_KO_of_isGLO _ hglo)
      unfold stdA
      rw [dif_neg hneg, zero_mul, zero_mul]
  have hshell : ∀ m : {m : Fin a → ℤ // Antitone m}, shell (haarVol (KO k (Fin a))) ϖ ν N
      (fun M => stdA ν ϖ c a a' (M * X)) m.1 = (haarVol (KO k (Fin a))).real (shellSet ϖ m.1 ∩ S) • C := by
    intro m
    rw [shell]
    simp_rw [hint]
    have e1 := setIntegral_indicator (μ := haarVol (KO k (Fin a))) (s := shellSet ϖ m.1)
      (f := fun _ => C) hSm
    rw [e1, setIntegral_const]
  obtain ⟨⟨m₀, hm₀⟩, hmem, huniq⟩ := exists_unique_shell hϖ g₁⁻¹
  have hsub : S ⊆ shellSet ϖ m₀ := by
    intro g hg
    obtain ⟨x, hx, y, hy, e⟩ := mem_shellSet.1 hmem
    refine mem_shellSet.2 ⟨g * g₁ * x, mul_mem hg hx, y, hy, ?_⟩
    calc g = g * g₁ * g₁⁻¹ := by group
      _ = _ := by rw [e]; simp only [mul_assoc]; try rfl
  rw [bigF, shellSum, finsum_eq_single _ ⟨m₀, hm₀⟩]
  · rw [hshell, Set.inter_eq_right.2 hsub, hS1, one_smul]
  · intro m hm
    rw [hshell]
    have : shellSet ϖ m.1 ∩ S = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun g ⟨hg1, hg2⟩ => hm (huniq m ?_)
      obtain ⟨x, hx, y, hy, e⟩ := mem_shellSet.1 hg1
      refine mem_shellSet.2 ⟨(g * g₁)⁻¹ * x, mul_mem (inv_mem hg2) hx, y, hy, ?_⟩
      calc g₁⁻¹ = (g * g₁)⁻¹ * g := by group
        _ = _ := by rw [e]; simp only [mul_assoc]; try rfl
    simp [this]

end GlobalTheory.StdPairZeta

open GlobalTheory.StdPairZeta in

theorem GlobalTheory.StdPairZeta.bigF_stdA : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c a a' : ℕ), IsUnif ϖ →
    (∀ X : Matrix (Fin a) (Fin (a + a')) k, (blk₁ X).det = 0 →
      bigF (haarVol (KO k (Fin a))) ϖ ν (stdA ν ϖ c a a') X = 0) ∧
    ∀ (X : Matrix (Fin a) (Fin (a + a')) k) (g₁ : GL (Fin a) k), g₁.val = blk₁ X →
      bigF (haarVol (KO k (Fin a))) ϖ ν (stdA ν ϖ c a a') X =
        (((ν (gdet g₁))⁻¹ : ℂˣ) : ℂ) * apow (gdet g₁) (-((Fintype.card (Fin (a + a')) : ℂ) / 2)) *
          Set.indicator {M : Matrix (Fin a) (Fin a') k | ∀ i j, M i j ∈ cball (ϖ ^ c)} 1 ((g₁⁻¹).val * blk₂ X) := by
  intro k _ _ _ _ _ _ ν ϖ c a a' hϖ
  exact ⟨fun X hX => bigF_stdA_zero ν ϖ c a a' X hX, fun X g₁ hg₁ => bigF_stdA_eq ν ϖ c a a' hϖ X g₁ hg₁⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairLinearBarVectorStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_linear_bar_vector : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ (c : Fin n → AE F E)
    (ι : ((Fin n × Fin d → Fv F B.v₁) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F B.v₁) → ℂ)),
    M.IsLinBar B.ψ B.τ₁ 1 1 ι → ∀ w : Fin d → Fv F B.v₁, ∃ z : Fin d → AE F E, At (evFin F B.v₁) z ∧
      (∀ l, piW (B.τ₁.comp σ) (z l) = 0) ∧
      ∀ φ ∈ SB (Fin n × Fin d → Fv F B.v₁), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F B.v₁),
        Acts (evFin F B.v₁) (M.co.rho B.ψ (Matrix.vecMulVec c z)) φ φ₁ →
        ∀ Y : Matrix (Fin n) (Fin d) (Fv F B.v₁),
          ι φ₁ Y = psiLoc B.ψ B.v₁ (∑ k, ∑ l, Y k l * piW B.τ₁ (c k) * w l) * ι φ Y := by
  first | exact @GlobalTheory.HeisMultLin.heis_mult_lin | exact GlobalTheory.HeisMultLin.heis_mult_lin | (intros; apply GlobalTheory.HeisMultLin.heis_mult_lin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialFourierPreservesSchwartzL2
section
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval

noncomputable section

namespace GlobalTheory.DblEval

theorem lintegral_partL_eq : ∀ {F : Type} [Field F] [NumberField F] {κ κ' : Type} [Fintype κ] [Fintype κ']
    (T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)),
    (∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ C : ℝ≥0∞, ∀ φ ∈ schA F κ, ∫⁻ x, ‖T φ x‖ₑ ^ 2 ∂μ = C * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) →
    (∀ Φ ∈ schA F (κ ⊕ κ'), partL T Φ ∈ schA F (κ ⊕ κ')) →
    ∀ μ : @Measure (κ ⊕ κ' → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ C : ℝ≥0∞, ∀ Φ ∈ schA F (κ ⊕ κ'), ∫⁻ x, ‖partL T Φ x‖ₑ ^ 2 ∂μ = C * ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ := by
  intro F _ _ κ κ' _ _ T hT hmem μ hμ
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  letI mX : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  letI mY : MeasurableSpace (κ' → AF F) := borel _
  haveI : BorelSpace (κ' → AF F) := ⟨rfl⟩
  letI mZ : MeasurableSpace (κ ⊕ κ' → AF F) := borel _
  haveI : BorelSpace (κ ⊕ κ' → AF F) := ⟨rfl⟩
  let μ₁ : Measure (κ → AF F) := Measure.addHaar
  let μ₂ : Measure (κ' → AF F) := Measure.addHaar
  obtain ⟨C₁, hC₁⟩ := hT μ₁ inferInstance
  refine ⟨C₁, fun Φ hΦ => ?_⟩
  let e : (κ ⊕ κ' → AF F) ≃ₜ (κ → AF F) × (κ' → AF F) := Homeomorph.sumArrowHomeomorphProdArrow
  let eA : ((κ → AF F) × (κ' → AF F)) ≃ₜ+ (κ ⊕ κ' → AF F) :=
    { e.symm with map_add' := fun a b => by funext i; cases i <;> rfl }
  let ν : Measure (κ ⊕ κ' → AF F) := (μ₁.prod μ₂).map eA
  haveI : ν.IsAddHaarMeasure := eA.isAddHaarMeasure_map _
  obtain ⟨c, hμν⟩ : ∃ c : ℝ≥0, μ = c • ν := ⟨_, Measure.isAddLeftInvariant_eq_smul μ ν⟩
  have key : ∀ f : (κ ⊕ κ' → AF F) → ℝ≥0∞, Measurable f →
      ∫⁻ z, f z ∂μ = c * ∫⁻ y, ∫⁻ x, f (Sum.elim x y) ∂μ₁ ∂μ₂ := by
    intro f hf
    have hmeas : Measurable (⇑eA) := eA.continuous.measurable
    rw [hμν, lintegral_smul_measure]
    simp only [ν]
    rw [lintegral_map hf hmeas, lintegral_prod_symm (fun p => f (eA p)) (hf.comp hmeas).aemeasurable]
    rfl
  have hc1 := GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F (hmem Φ hΦ)
  have hc2 := GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F hΦ
  rw [key _ (hc1.measurable.enorm.pow_const 2), key _ (hc2.measurable.enorm.pow_const 2)]
  have inner : ∀ y, ∫⁻ x, ‖partL T Φ (Sum.elim x y)‖ₑ ^ 2 ∂μ₁ = C₁ * ∫⁻ x, ‖Φ (Sum.elim x y)‖ₑ ^ 2 ∂μ₁ :=
    fun y => hC₁ _ (sliceL_mem hΦ y)
  have hm : Measurable fun y => ∫⁻ x, ‖Φ (Sum.elim x y)‖ₑ ^ 2 ∂μ₁ :=
    Measurable.lintegral_prod_left' (f := fun p : (κ → AF F) × (κ' → AF F) => ‖Φ (eA p)‖ₑ ^ 2)
      ((hc2.comp eA.continuous).measurable.enorm.pow_const 2)
  simp_rw [inner]
  rw [lintegral_const_mul _ hm]
  ring

end GlobalTheory.DblEval

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalCongruenceConjMemArithmeticGroupStatement
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal
open IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalCongruence_conj_mem_arithmeticGroup : ∀ (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (Comp : Type) (X : Comp → Data D.host.E V.rank)
    (dict : GA D V → Σ k, Frame (X k).Ψ V.rank) (Kf : Subgroup (GA D V))
    (th : ∀ c, (X c).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : ℕ) (x0 : ∀ c, Frame (X c).Ψ V.rank),
    IsLevelK V M Kf → (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) → DictIsUnif V dict Kf th rfl →
    (∀ c, x0 c ∈ (X c).dom) →
    (∀ g, ∀ h ∈ GinfC V, ∃ γ' ∈ (X (dict g).1).Γ,
      dict (g * h) = ⟨(dict g).1, lact γ' (rmul (dict g).2 (archMat V th rfl x0 h (dict g).1))⟩) →
    (∀ c, (X c).Gm = -(V.gram)ᵀ) →
    ∀ (k : Comp) (g : GA D V), dict g = ⟨k, x0 k⟩ →
    ∀ Λk : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E),
      (Λk : Set (Fin V.rank → D.host.E)) = GlobalTheory.AdLat.latOf (maximalRealSubfield D.host.E) (finHom V g).1
        (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) →
      (GlobalTheory.AdLat.hat (maximalRealSubfield D.host.E) (Λk : Set (Fin V.rank → D.host.E)) :
                   Set (Fin V.rank → GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E)) =
        ((finHom V g).1 : Matrix (Fin V.rank) (Fin V.rank) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E)).mulVec ''
          (GlobalTheory.AdLat.hat (maximalRealSubfield D.host.E) (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E))) →
    ∀ γ' : GL (Fin V.rank) D.host.E,
      (IsUStab (-(V.gram)ᵀ) Λk γ' ∧ ∀ x ∈ Λk, ∃ y ∈ Λk, (γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E).mulVec x - x = M • y) →
      ∃ γ ∈ (X k).Γ, ∀ (τ : D.host.E →+* ℂ) (hτ : τ ∈ (X k).Ψ),
        archM V (th k ⟨τ, hτ⟩) g * (γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map τ =
          (γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map τ * archM V (th k ⟨τ, hτ⟩) g := by
  first | exact @GlobalTheory.RepConv.conj_mem_of_cong | exact GlobalTheory.RepConv.conj_mem_of_cong | (intros; apply GlobalTheory.RepConv.conj_mem_of_cong <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelLiftModuliLawsOfCoreStatement
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalLevelLiftModuliLaws_of_core : ∀ (D : D7) (T : CoreJ D) (j : ℕ), LawsJ T → InR D j → Laws D j (T.Q.Xo j) T.Q.c (T.U j) (coreDict T.toCore j) ∧ ∀ (G : WTZ D.host.E) (σ : T.Q.c.F →+* ℂ) (f : cuspW (T.Q.Xo j) T.Q.c (T.U j) G), normW (T.U j) (xiR D) (fun _ => D.sp.W j) (coreDict T.toCore j) G σ f = normW (T.U j) (xiR D) (T.V j) (T.dict j) G σ f := by
  first | exact @GlobalTheory.LevGeo.laws_of_coreJ | exact GlobalTheory.LevGeo.laws_of_coreJ | (intros; apply GlobalTheory.LevGeo.laws_of_coreJ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalFixatorOfColumnsIsSemidirectLatticeStatement
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalFixatorOfColumns_isSemidirectLattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∃ (ν : Measure (unipRad σ J C)) (π : Measure (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J))) (DN : Set (unipRad σ J C)) (DM : Set (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J))), SemiLat (unipRad σ J C) (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J)) (ratPts σ J ⊓ fixG σ J C) ν π DN DM := by
  first | exact @GlobalTheory.SphEis.semiLat_fixG | exact GlobalTheory.SphEis.semiLat_fixG | (intros; apply GlobalTheory.SphEis.semiLat_fixG <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSquaringPathsRigidOfTorusExtension
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef.TorExt

theorem algebraMap_comp_C (Ω : Type) [Field Ω] :
    (algebraMap (RatFunc Ω) (LaurentSeries Ω)).comp RatFunc.C =
      (algebraMap (PowerSeries Ω) (LaurentSeries Ω)).comp PowerSeries.C := by
  refine RingHom.ext fun c => ?_
  simp only [RingHom.comp_apply]
  rw [← RatFunc.algebraMap_C]
  have := RatFunc.coe_coe (Polynomial.C c)
  simp only [Polynomial.coe_C] at this
  exact this.symm

theorem unitSec_comp {S : Scheme.{0}} {G H : Over S} [GrpObj G] [GrpObj H] (f : G ⟶ H) [IsMonHom f] :
    unitSec G ≫ f.left = unitSec H := by
  rw [unitSec, unitSec, sec, sec, ← Over.comp_left, IsMonHom.one_hom]

theorem isLocalHom_field {K L : Type} [Field K] [Field L] (φ : K →+* L) : IsLocalHom φ :=
  ⟨fun x hx => by
    by_cases h : x = 0
    · subst h; simp at hx
    · exact IsUnit.mk0 x h⟩

theorem exists_lift {Ω : Type} [Field Ω] {G : Over (Sp Ω)} [GrpObj G] (E : TorusExtension G) {Z : Scheme.{0}}
    (z : Z ⟶ Sp Ω) (f : Z ⟶ G.left) (hf : f ≫ G.hom = z) (hq : letI := E.grpB; f ≫ E.q.left = z ≫ unitSec E.B) :
    letI := E.addCommGroup
    ∃ g : Z ⟶ (splitTorus (Sp Ω) E.X).left, g ≫ E.i.left = f ∧ g ≫ (splitTorus (Sp Ω) E.X).hom = z := by
  letI := E.addCommGroup
  letI := E.grpB
  let f' : Over.mk z ⟶ G := Over.homMk f hf
  have h : f' ≫ E.q = toUnit _ ≫ η := by
    ext
    simp [f', hq, unitSec, sec]
  refine ⟨(E.isKernel.lift f' (toUnit _) h).left, ?_, ?_⟩
  · rw [← Over.comp_left, E.isKernel.lift_fst]
    rfl
  · exact Over.w (E.isKernel.lift f' (toUnit _) h)

theorem mono_i {Ω : Type} [Field Ω] {G : Over (Sp Ω)} [GrpObj G] (E : TorusExtension G) :
    letI := E.addCommGroup
    Mono E.i.left := by
  letI := E.addCommGroup
  letI := E.grpB
  have : Mono E.i := ⟨fun a b hab => E.isKernel.hom_ext hab (toUnit_unique _ _)⟩
  exact Over.mono_left_of_mono _

end GlobalTheory.Nef.TorExt

namespace GlobalTheory.Nef

open TorExt in

theorem ratRigid_of_torusExtension : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (G : Over (Sp Ω)) [GrpObj G],
    Nonempty (TorusExtension G) → RatRigid G (𝟙 (Sp Ω)) := by
  intro Ω _ _ G _ ⟨E⟩ ξ hξ ⟨β, hβ⟩
  letI := E.addCommGroup
  letI := E.grpB
  haveI := E.q_hom
  haveI := E.i_hom
  haveI : IsProper E.B.hom := E.isAbelian.proper
  haveI := mono_i E
  haveI := isLocalHom_field (algebraMap (RatFunc Ω) (LaurentSeries Ω))
  obtain ⟨-, bc2⟩ := GlobalTheory.T.formalSquaringPaths_baseChange_and_hom
  obtain ⟨epi1, -⟩ := GlobalTheory.T.spec_injectiveRingMap_cancellation
  set T := splitTorus (Sp Ω) E.X
  set a := algebraMap (RatFunc Ω) (LaurentSeries Ω)
  set ι₀ := algebraMap (PowerSeries Ω) (LaurentSeries Ω)
  have ha : Function.Injective a := a.injective
  have hC : spMap a ≫ spMap RatFunc.C = spMap ι₀ ≫ spMap (PowerSeries.C (R := Ω)) := by
    rw [← Geo.Tor.spMap_comp, ← Geo.Tor.spMap_comp, algebraMap_comp_C]
  have hq : ξ ≫ E.q.left = spMap (PowerSeries.C (R := Ω)) ≫ unitSec E.B := by
    have := GlobalTheory.T.rationalSquaringPathsRigid_of_proper_charZero Ω E.B inferInstance (ξ ≫ E.q.left) ((bc2 _ G E.B E.q Ω 2 (𝟙 _) ξ).1 hξ)
      ⟨β ≫ E.q.left, by rw [← Category.assoc, hβ, Category.assoc]⟩
    rw [this, triv, Category.id_comp]
  have hbase : ξ ≫ G.hom = spMap (PowerSeries.C (R := Ω)) := by
    rw [hξ.base, Category.comp_id]
  obtain ⟨ζ, hζ, hζT⟩ := exists_lift E _ ξ hbase hq
  have hβG : β ≫ G.hom = spMap (RatFunc.C (K := Ω)) :=
    epi1 _ _ a ha _ _ _ (by rw [reassoc_of% hβ, hbase, hC])
  have hβq : β ≫ E.q.left = spMap (RatFunc.C (K := Ω)) ≫ unitSec E.B :=
    epi1 _ _ a ha _ _ _ (by rw [reassoc_of% hβ, hq, reassoc_of% hC])
  obtain ⟨βT, hβT, -⟩ := exists_lift E _ β hβG hβq
  have hTunit : unitSec T ≫ E.i.left = unitSec G := unitSec_comp E.i
  have hpath : IsPath T 2 (𝟙 _) ζ := by
    refine ⟨by rw [hζT, Category.comp_id], ?_, ?_⟩
    · rw [← cancel_mono E.i.left, Category.assoc, hζ, hξ.zero, Category.assoc, hTunit]
    · rw [← cancel_mono E.i.left, Category.assoc, hζ, hξ.scale, Category.assoc,
        (bc2 _ T G E.i Ω 2 (𝟙 _) ζ).2.2, reassoc_of% hζ]
  have hrat : IsRatPath ζ :=
    ⟨βT, by rw [← cancel_mono E.i.left, Category.assoc, hβT, hβ, Category.assoc, hζ]⟩
  have h := GlobalTheory.T.splitTorus_rationalSquaringPathsRigid_charZero Ω E.X ζ hpath hrat
  rw [← hζ, h, (bc2 _ T G E.i Ω 2 (𝟙 _) ζ).2.1]

end GlobalTheory.Nef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedTensorLocalOperatorsStatement
section
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restricted_tensor_local_operators : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (e : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (ei : SInf F κ →L[ℂ] SInf F κ)
    (ev : ∀ v : Pl F, ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ → Fv F v) → ℂ),
    (∀ v, ∀ φ ∈ SB (κ → Fv F v), ev v φ ∈ SB (κ → Fv F v)) →
    (∀ᶠ v in cofinite, ev v (stdInd F κ v) = stdInd F κ v) →
    (∀ (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ), (∀ v, φ v ∈ SB (κ → Fv F v)) →
      (∀ᶠ v in cofinite, φ v = stdInd F κ v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    Set.InjOn e (schA F κ : Set ((κ → AF F) → ℂ)) →
    ∀ v, ∀ ψ ∈ SB (κ → Fv F v), ev v ψ = 0 → ψ = 0 := by
  first | exact @GlobalTheory.EvKer.ker_trivial | exact GlobalTheory.EvKer.ker_trivial | (intros; apply GlobalTheory.EvKer.ker_trivial <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartz
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny

namespace GlobalTheory.WeylFour.SchrKeep

theorem schr_mem_schA : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    (w : (κ → AF F) × (κ → AF F)), ∀ Φ ∈ schA F κ, schr ψ w Φ ∈ schA F κ := by
  intro F _ _ ψ hψ κ _ w Φ hΦ
  exact GlobalTheory.ConeMeasV.schr_mem_schA hψ w hΦ

end GlobalTheory.WeylFour.SchrKeep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylElementRealisedByFourierTransformsStatement
section
open scoped TensorProduct NNReal ENNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.TowU

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weylElement_realised_by_fourierTransforms : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ] [DecidableEq κ], ∃ (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (S' : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)), IsOp2 ψ (GlobalTheory.AdelicSvN.act (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (κ ⊕ κ) (κ ⊕ κ) F)) S S' := by
  first | exact @GlobalTheory.TowU.realised_weyl2 | exact GlobalTheory.TowU.realised_weyl2 | (intros; apply GlobalTheory.TowU.realised_weyl2 <;> assumption)
end

