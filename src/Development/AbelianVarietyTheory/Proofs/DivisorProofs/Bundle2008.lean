import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1999
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1919
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1960
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1969
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1696
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1740
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1809
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1876
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1764
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1759
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0097
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1912
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1953
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1718
import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1983
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1997
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1991

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactOpenSeparating
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct Topology

namespace GlobalTheory.FinSepChar

variable {F : Type} [Field F] [NumberField F]

theorem pairA_zero_zero : pairA F 0 (0 : Af F) = 0 := Prod.ext rfl rfl

theorem pairA_zero_neg (b : Af F) : pairA F 0 (-b) = -pairA F 0 b :=
  Prod.ext (neg_zero (G := Ainf F)).symm rfl

theorem algebraMap_mul_inv {a : F} (ha : a ≠ 0) :
    algebraMap F (FiniteAdeleRing (𝓞 F) F) a * algebraMap F (FiniteAdeleRing (𝓞 F) F) a⁻¹ = 1 := by
  rw [← map_mul, mul_inv_cancel₀ ha, map_one]

def ann (ψ : AddChar (AF F) ℂ) (κ : Type) [Fintype κ] (L : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F)) :
    AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F) where
  carrier := {x | ∀ y ∈ L, ψ (pairA F 0 (x ⬝ᵥ y)) = 1}
  zero_mem' := fun y _ => by
    show ψ (pairA F 0 (0 ⬝ᵥ y)) = 1
    rw [zero_dotProduct, pairA_zero_zero, AddChar.map_zero_eq_one]
  add_mem' := fun {a b} ha hb y hy => by
    show ψ (pairA F 0 ((a + b) ⬝ᵥ y)) = 1
    rw [add_dotProduct, GlobalTheory.AnnCompactStd.pairA_zero_add, AddChar.map_add_eq_mul, ha y hy, hb y hy, mul_one]
  neg_mem' := fun {a} ha y hy => by
    show ψ (pairA F 0 ((-a) ⬝ᵥ y)) = 1
    rw [neg_dotProduct, pairA_zero_neg, AddChar.map_neg_eq_inv, ha y hy, inv_one]

theorem mem_ann {ψ : AddChar (AF F) ℂ} {κ : Type} [Fintype κ] {L : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F)}
    {x : κ → FiniteAdeleRing (𝓞 F) F} : x ∈ ann ψ κ L ↔ ∀ y ∈ L, ψ (pairA F 0 (x ⬝ᵥ y)) = 1 := Iff.rfl

def scaledInt (κ : Type) (a : FiniteAdeleRing (𝓞 F) F) : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F) where
  carrier := {y | ∀ i, a * y i ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F}
  zero_mem' := fun i => by
    show a * 0 ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F
    rw [mul_zero]; exact Subring.zero_mem _
  add_mem' := fun {u v} hu hv i => by
    show a * (u i + v i) ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F
    rw [mul_add]; exact Subring.add_mem _ (hu i) (hv i)
  neg_mem' := fun {u} hu i => by
    show a * (-u i) ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F
    rw [mul_neg]; exact Subring.neg_mem _ (hu i)

theorem isOpen_scaledInt (κ : Type) [Fintype κ] (a : FiniteAdeleRing (𝓞 F) F) :
    IsOpen (scaledInt κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)) := by
  have h : (scaledInt κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)) =
      ⋂ i, (fun y : κ → FiniteAdeleRing (𝓞 F) F => a * y i) ⁻¹'
        (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F)) := by
    ext y; simp only [Set.mem_iInter, Set.mem_preimage]; exact Iff.rfl
  rw [h]
  exact isOpen_iInter_of_finite fun i =>
    GroundTheory.Global.isOpen_integralFiniteAdeles.preimage (continuous_const.mul (continuous_apply i))

end GlobalTheory.FinSepChar

namespace GlobalTheory.FinSepChar

variable {F : Type} [Field F] [NumberField F]

theorem exists_compact_open_separating {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (κ : Type) [Fintype κ]
    {N : Set (κ → Af F)} (hN : N ∈ 𝓝 (0 : κ → Af F)) : ∃ U : AddSubgroup (κ → Af F),
      IsOpen (U : Set (κ → Af F)) ∧ IsCompact (U : Set (κ → Af F)) ∧ (U : Set (κ → Af F)) ⊆ N ∧
      ∀ x₀ ∉ U, ∃ y : κ → Af F, (∀ u ∈ U, ψ (pairA F 0 (u ⬝ᵥ y)) = 1) ∧ ψ (pairA F 0 (x₀ ⬝ᵥ y)) ≠ 1 := by
  classical
  rw [nhds_pi, Filter.mem_pi] at hN
  obtain ⟨I, -, t, ht, hsub⟩ := hN
  have hW : (⋂ i, t i) ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F) := Filter.iInter_mem.mpr ht
  obtain ⟨d, hd0, hd⟩ := GroundTheory.Global.exists_forall_mul_mem_of_mem_nhds hW
  obtain ⟨c, hc0, hc⟩ := GlobalTheory.AnnCompactStd.exists_mul_mem_of_forall hψ
  obtain ⟨e, he0, he⟩ := GlobalTheory.AnnCompactStd.exists_psi_fin_trivial hψ
  have hinj : ∀ a : 𝓞 F, a ≠ 0 → algebraMap (𝓞 F) F a ≠ 0 := fun a ha =>
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr ha
  set cc := algebraMap (𝓞 F) F c with hcc
  set dd := algebraMap (𝓞 F) F d with hdd
  set ee := algebraMap (𝓞 F) F e with hee
  have hC := algebraMap_mul_inv (F := F) (hinj c hc0)
  have hD := algebraMap_mul_inv (F := F) (hinj d hd0)
  have hE := algebraMap_mul_inv (F := F) (hinj e he0)
  set ι := algebraMap F (FiniteAdeleRing (𝓞 F) F) with hι
  set O := GroundTheory.Global.integralFiniteAdeles (𝓞 F) F with hO

  set L := scaledInt (F := F) κ (ι cc * ι dd) with hL
  have hLo : IsOpen (L : Set (κ → FiniteAdeleRing (𝓞 F) F)) := isOpen_scaledInt κ _
  refine ⟨ann ψ κ L, ?_, ?_, ?_, ?_⟩
  ·
    set δ := ι ee⁻¹ * (ι cc⁻¹ * ι dd⁻¹) with hδ
    have hVo : IsOpen (scaledInt (F := F) κ δ : Set (κ → FiniteAdeleRing (𝓞 F) F)) := isOpen_scaledInt κ _
    have hVU : (scaledInt (F := F) κ δ : Set (κ → FiniteAdeleRing (𝓞 F) F)) ⊆ ann ψ κ L := by
      intro x hx y hy
      have hsum : x ⬝ᵥ y = ι ee * ∑ i, (δ * x i) * ((ι cc * ι dd) * y i) := by
        rw [dotProduct, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hδ]
        linear_combination (-(x i * y i * (ι cc * ι dd) * (ι cc⁻¹ * ι dd⁻¹))) * hE
          + (-(x i * y i * ι dd * ι dd⁻¹)) * hC + (-(x i * y i)) * hD
      rw [hsum]
      exact he _ (Subring.sum_mem _ fun i _ => Subring.mul_mem _ (hx i) (hy i))
    exact AddSubgroup.isOpen_of_mem_nhds _
      (Filter.mem_of_superset (hVo.mem_nhds (scaledInt (F := F) κ δ).zero_mem) hVU)
  · exact GlobalTheory.AnnCompactStd.isCompact_annihilator F ψ hψ κ L hLo
  · intro x hx
    apply hsub
    intro i _
    have hz : ∀ s ∈ O, ψ (pairA F 0 ((ι cc⁻¹ * ι dd⁻¹ * x i) * s)) = 1 := by
      intro s hs
      have hy : (Pi.single i (ι cc⁻¹ * ι dd⁻¹ * s) : κ → FiniteAdeleRing (𝓞 F) F) ∈ L := by
        intro k
        by_cases hk : k = i
        · subst hk
          rw [Pi.single_eq_same]
          have : ι cc * ι dd * (ι cc⁻¹ * ι dd⁻¹ * s) = s := by
            linear_combination (ι dd * ι dd⁻¹ * s) * hC + s * hD
          rw [this]; exact hs
        · rw [Pi.single_eq_of_ne hk, mul_zero]; exact Subring.zero_mem _
      have h1 := hx _ hy
      rw [dotProduct_single] at h1
      rw [show ι cc⁻¹ * ι dd⁻¹ * x i * s = x i * (ι cc⁻¹ * ι dd⁻¹ * s) by ring]
      exact h1
    have h2 := hc _ hz
    have h3 := hd _ h2
    have h4 : ι dd * (ι cc * (ι cc⁻¹ * ι dd⁻¹ * x i)) = x i := by
      linear_combination (ι dd * ι dd⁻¹ * x i) * hC + x i * hD
    rw [h4] at h3
    exact Set.mem_iInter.mp h3 i
  · intro x₀ hx₀
    rw [mem_ann] at hx₀
    push_neg at hx₀
    obtain ⟨y, hy, hne⟩ := hx₀
    exact ⟨y, fun u hu => hu y hy, hne⟩

end GlobalTheory.FinSepChar

theorem GlobalTheory.FinSepChar.finite_chars_separate : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ (κ : Type) [Fintype κ], ∀ N ∈ nhds (0 : κ → Af F), ∃ U : AddSubgroup (κ → Af F),
      IsOpen (U : Set (κ → Af F)) ∧ IsCompact (U : Set (κ → Af F)) ∧ (U : Set (κ → Af F)) ⊆ N ∧
      ∀ x₀ ∉ U, ∃ y : κ → Af F, (∀ u ∈ U, ψ (pairA F 0 (u ⬝ᵥ y)) = 1) ∧ ψ (pairA F 0 (x₀ ⬝ᵥ y)) ≠ 1 :=
  fun _ _ _ _ hψ κ _ _ hN => GlobalTheory.FinSepChar.exists_compact_open_separating hψ κ hN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDepthSplitThetaBigEqSmallBlockTranslate
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
open GlobalTheory.PureMatch GlobalTheory.SquareFlipReach ValuativeRel

namespace GlobalTheory.PureMatch

theorem smallP_smul_measure_mul {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] {A A' C : Type} [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C]
    (μ : Measure (GL A' k)) (c : NNReal) (z : ℂ) (σ : A ⊕ A' ≃ C) (ν α : kˣ →* ℂˣ) (Ψ : Matrix A' C k → ℂ)
    (h : GL C k) : smallP (c • μ) σ ν α (fun Y => z * Ψ Y) h = (c : ℂ) * z * smallP μ σ ν α Ψ h := by
  simp only [smallP, smallF, mul_assoc, integral_const_mul, integral_smul_nnreal_measure, NNReal.smul_def,
    Complex.real_smul]
  ring

theorem bigZetaIntegral_const_mul {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] {a : ℕ} {A' C : Type} [Fintype C] [DecidableEq C]
    (μ : @Measure (GL (Fin a) k) Units.instMeasurableSpace) (ϖ : kˣ) (σ : Fin a ⊕ A' ≃ C) (ν β : kˣ →* ℂˣ) (z : ℂ)
    (Φ : Matrix (Fin a) C k → ℂ) (h : GL C k) :
    bigP μ ϖ σ ν β (fun Z => z * Φ Z) h = z * bigP μ ϖ σ ν β Φ h := by
  simp only [bigZetaIntegral_eq, bigF, shellSum_smul]
  ring

theorem exists_depth_bigP_eq_smallP : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (a : ℕ) (A' C : Type) [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C] (μ₀ : Measure (GL A' k)) [μ₀.IsHaarMeasure]
    (σ : Fin a ⊕ A' ≃ C) (ν β : kˣ →* ℂˣ) (ϖ : kˣ) (P : Finset C) (g₀ : GL (Fin a) k) (c₀ : GL C k) (Ψ : Matrix A' C k → ℂ),
    Ψ ∈ GlobalTheory.WeilM.SB (Matrix A' C k) → IsUnif ϖ → ∃ m : ℕ, ∀ n, 2 * m ≤ n →
      ∀ (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (σ' : Fin a ⊕ A' ≃ C) (r : ℂ), r ≠ 0 → ∃ Ξ : Matrix A' C k → ℂ,
        HasDepth ϖ n (blockLat ϖ n P) Ξ ∧
        bigP (haarVol (KO k (Fin a))) ϖ σ ν β (fun Z => r * phiA μ σ' ν ϖ n (blockLat ϖ n P) Ξ
          (g₀.val * Z * (c₀ * diagGL (fun col => if col ∈ P then ϖ ^ m else (ϖ ^ m)⁻¹)).val)) = smallP μ₀ σ ν (ν * β) Ψ := by
  intro k _ _ _ _ _ _ a A' C _ _ _ _ μ₀ _ σ ν β ϖ P g₀ c₀ Ψ hΨ hϖ
  have hΨ' : (fun Y : Matrix A' C k => Ψ (Y * c₀.valᵀ)) ∈ GlobalTheory.WeilM.SB (Matrix A' C k) := by
    have := comp_mul_mem_SB (1 : GL A' k) (invT c₀)⁻¹ hΨ
    simp only [invT_inv_val, Units.val_one, Matrix.one_mul] at this
    exact this
  obtain ⟨m, hm⟩ := GlobalTheory.T.schwartzBruhat_blockScaled_hasLatticeDepth k A' C ϖ P _ hΨ' hϖ
  refine ⟨m, fun n hn μ _ σ' r hr => ?_⟩
  obtain ⟨u, hu, hphi⟩ := GlobalTheory.T.exists_ne_zero_primitiveFrameDatum_renumber k (Fin a) A' C μ σ σ' ν
  obtain ⟨c, hc0, hc⟩ : ∃ c : NNReal, c ≠ 0 ∧ μ = c • μ₀ :=
    ⟨Measure.haarScalarFactor μ μ₀, (Measure.haarScalarFactor_pos_of_isHaarMeasure μ μ₀).ne',
      Measure.isMulLeftInvariant_eq_smul μ μ₀⟩
  set N : GL C k := c₀ * diagGL (fun col => if col ∈ P then ϖ ^ m else (ϖ ^ m)⁻¹) with hN
  set κ : ℂ := (ν (gdet g₀) : ℂ) * apow (gdet g₀) ((Fintype.card C : ℂ) / 2) * (ν (gdet N) : ℂ) *
    apow (gdet N) ((Fintype.card C : ℂ) / 2) with hκ
  have hκ0 : κ ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (Units.ne_zero _) (apow_ne_zero _ _)) (Units.ne_zero _)) (apow_ne_zero _ _)
  have hc0' : ((c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc0
  have hNT : ∀ Y : Matrix A' C k, Y * N.valᵀ =
      Y * diagonal (fun col => if col ∈ P then ((ϖ ^ m : kˣ) : k) else (((ϖ ^ m)⁻¹ : kˣ) : k)) * c₀.valᵀ := by
    intro Y
    rw [hN, Units.val_mul, transpose_mul, diagGL_val, diagonal_transpose, Matrix.mul_assoc]
    congr 3
    funext col
    split_ifs <;> rfl
  refine ⟨fun Y => (κ / (r * u * c)) * Ψ (Y * N.valᵀ), ?_, ?_⟩
  · have h1 := (depthSpace A' ϖ n (blockLat ϖ n P)).smul_mem (κ / (r * u * c)) (hm n hn)
    simp only [hNT]
    exact h1
  · funext h
    have h2 := GlobalTheory.T.zetaIntegral_twoSidedMovedDatum_eq_smallZeta k a A' C μ σ ν β ϖ n (blockUnits ϖ n P)
      (fun Y => (κ / (r * u * c)) * Ψ (Y * N.valᵀ)) g₀ N h hϖ
    have h3 : ∀ Y : Matrix A' C k, Y * (invT N).val * N.valᵀ = Y := fun Y => by
      rw [Matrix.mul_assoc, ← invT_inv_val, Units.mul_inv, Matrix.mul_one]
    simp only [h3] at h2
    have h4 := smallP_smul_measure_mul μ₀ c (κ / (r * u * c)) σ ν (ν * β) Ψ h
    rw [← hc, ← h2, ← hκ] at h4
    simp only [hphi, ← mul_assoc]
    rw [bigZetaIntegral_const_mul]
    apply mul_left_cancel₀ hκ0
    rw [mul_left_comm]
    refine (congrArg (fun x => r * u * x) h4).trans ?_
    field_simp

end GlobalTheory.PureMatch
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearFunctionalGoodPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.LinWAt

theorem nonempty_emb_of_splitsFully {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (hv : SplitsFully E v) :
    Nonempty (E →ₐ[F] Fv F v) := by
  set q : Ideal ℤ := v.asIdeal.under ℤ with hq
  obtain ⟨g, hg⟩ := (Submodule.IsPrincipal.principal q)
  have hqs : q = Ideal.span {((g.natAbs : ℕ) : ℤ)} := by
    rw [hg]; exact Eq.symm (Int.span_natAbs g)
  have hqne : q ≠ ⊥ := by
    intro h0
    apply v.ne_bot
    exact Ideal.eq_bot_of_comap_eq_bot h0
  have hg0 : g ≠ 0 := by rintro rfl; apply hqne; rw [hg]; simp
  have hp : (g.natAbs).Prime := by
    have hI : (Ideal.span {((g.natAbs : ℕ) : ℤ)}).IsPrime := hqs ▸ (Ideal.IsPrime.under ℤ v.asIdeal)
    have hne : ((g.natAbs : ℕ) : ℤ) ≠ 0 := by simpa using hg0
    exact Nat.prime_iff_prime_int.2 ((Ideal.span_singleton_prime hne).1 hI)
  have hmem : ((g.natAbs : ℕ) : 𝓞 F) ∈ v.asIdeal := by
    have : ((g.natAbs : ℕ) : ℤ) ∈ q := by rw [hqs]; exact Ideal.subset_span rfl
    rw [hq, Ideal.under_def, Ideal.mem_comap] at this
    simpa using this
  have h : (Ideal.primesOver (Ideal.span {((g.natAbs : ℕ) : ℤ)}) (𝓞 E)).ncard = Module.finrank ℚ E := by
    rw [← hqs]; exact hv
  rw [GlobalTheory.AdelicU.nonempty_split_iff hcm]
  exact GlobalTheory.GoodPlace.ncard_primesOver_eq_two hcm.2.2.1 hp h v hmem

end GlobalTheory.LinWAt

namespace GlobalTheory.LinWAt

theorem locCo_form {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (AF F) W]
    {B : W → W → AF F} {κ : Type} [Fintype κ] (co : Darboux B κ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (x u : W) :
    (GlobalTheory.LatVac.locCo co v x).1 ⬝ᵥ (GlobalTheory.LatVac.locCo co v u).2 -
      (GlobalTheory.LatVac.locCo co v u).1 ⬝ᵥ (GlobalTheory.LatVac.locCo co v x).2 = evFin F v (B x u) := by
  rw [co.form]
  simp [GlobalTheory.LatVac.locCo, dotProduct, map_sum, map_mul, map_sub]

theorem locCo_surj {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (AF F) W]
    {B : W → W → AF F} {κ : Type} [Fintype κ] (co : Darboux B κ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)
    (w : (κ → Fv F v) × (κ → Fv F v)) : ∃ u : W, At (evFin F v) u ∧ GlobalTheory.LatVac.locCo co v u = w := by
  refine ⟨co.e.symm (fun k => GlobalTheory.LatVac.liftV v (w.1 k), fun k => GlobalTheory.LatVac.liftV v (w.2 k)), ?_, ?_⟩
  · intro a ha
    rw [← LinearEquiv.map_smul, ← co.e.symm.map_zero]
    congr 1
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
    · exact GlobalTheory.LatVac.at_liftV v _ a ha
    · exact GlobalTheory.LatVac.at_liftV v _ a ha
  · refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;>
      simp [GlobalTheory.LatVac.locCo, GlobalTheory.LatVac.evFin_liftV]

theorem at_symp {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {n d : ℕ} (JA : Matrix (Fin n) (Fin n) (AE F E)) (JB : Matrix (Fin d) (Fin d) (AE F E)) {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F}
    (x u : Matrix (Fin n) (Fin d) (AE F E)) (hx : At (evFin F v) x) :
    At (evFin F v) (symp (R := AF F) (cA σ) (-1) JA JB x u) := by
  intro a ha
  have h := GlobalTheory.LatVac.symp_smul_smul σ JA JB (-1) a 1 x u
  rw [hx a ha, one_smul, mul_one, GlobalTheory.VacIndic.symp_zero_left] at h
  rw [smul_eq_mul]
  exact h.symm

theorem co_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} (t : E →ₐ[F] Fv F v) (u : Matrix (Fin n) (Fin d) (AE F E)) :
    ((1 : GL (Fin n) (Fv F v))⁻¹).1 * u.map (piW t) * ((1 : GL (Fin d) (Fv F v))⁻¹).1ᵀ = u.map (piW t) := by
  simp

theorem exists_isLinW : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v →
    ∃ (t : E →ₐ[F] Fv F v) (ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ)), G.M.IsLinW B.ψ t 1 1 ι := by
  intro _ F E _ _ _ _ _ σ B a a' G X om om' hTr v hv
  obtain ⟨t⟩ := nonempty_emb_of_splitsFully hTr.base.cm v hv.2
  obtain ⟨uT, uM, hT, hM, hspan, hsymp⟩ := (GlobalTheory.T.local_unipotent_embeddings_exist) F E σ B a a' G X om om' hTr v t
  have hψc : Continuous (GlobalTheory.LatVac.psiAt B.ψ v) := GlobalTheory.VacAny.continuous_psiV hTr.base.std.1 v
  have hunr : PsiUnr B.ψ v := GlobalTheory.StdCharUnrF.psiUnr_of_not_le F B.ψ hTr.base.std v
    (GlobalTheory.SplitFullyUnr.not_le_differentIdeal v hv.2)
  have hunr' : ∀ x : Fv F v, (∀ y ∈ 𝒪[Fv F v], GlobalTheory.LatVac.psiAt B.ψ v (x * y) = 1) ↔
      x ∈ 𝒪[Fv F v] := by
    intro x
    simp only [GlobalTheory.FinPl.SplitPoint.mem_integer_iff]
    exact hunr x
  have hcoT : ∀ Y, coW G t (uT Y) = 0 := fun Y => coW_eq_zero G t _ (hT Y).2.1
  haveI : CharZero (Fv F v) := charZero_of_injective_algebraMap (algebraMap F _).injective
  obtain ⟨ι, hbij, htr, hmu⟩ := GlobalTheory.T.stoneVonNeumann_schwartzBruhat_transverseLagrangians (GlobalTheory.LatVac.psiAt B.ψ v) hψc hunr'
    ((GlobalTheory.LatVac.locCo G.M.co v).comp uT) ((GlobalTheory.LatVac.locCo G.M.co v).comp uM)
    (fun Y Y' => by
      simp only [AddMonoidHom.comp_apply]
      rw [locCo_form, hsymp _ _ (hT Y).1 (hT Y').1, hcoT, hcoT]
      simp)
    (fun z z' => by
      simp only [AddMonoidHom.comp_apply]
      rw [locCo_form, hsymp _ _ (hM z).1 (hM z').1, (hM z).2.1, (hM z').2.1]
      simp)
    (fun Y z => by
      simp only [AddMonoidHom.comp_apply]
      rw [locCo_form, hsymp _ _ (hT Y).1 (hM z).1, (hT Y).2.2, (hM z).2.2, hcoT, (hM z).2.1]
      simp)
    (fun w => by
      obtain ⟨u, hu, rfl⟩ := locCo_surj G.M.co v w
      obtain ⟨Y, z, rfl⟩ := hspan u hu
      exact ⟨Y, z, by simp only [AddMonoidHom.comp_apply, map_add]⟩)
  have hφ₁ : ∀ (u : Matrix (Fin a) (Fin (a + a')) (AE F E)), At (evFin F v) u →
      ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ₁, Acts (evFin F v) (G.M.co.rho B.ψ u) φ φ₁ →
        φ₁ = GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v u) φ :=
    fun u hu φ hφ φ₁ hact => GlobalTheory.TensUniq.eq_of_tens_eq v φ φ₁ _ hφ fun r hr =>
      (hact r hr).symm.trans (GlobalTheory.VacBridge.rho_acts_locCo G.M.co B.ψ v u hu φ r hr)
  refine ⟨t, ι, hbij, ?_, ?_⟩
  · intro u hu hu0 φ hφ φ₁ _ hact Y
    have e1 := hφ₁ u hu φ hφ φ₁ hact
    obtain ⟨Y₀, z, rfl⟩ := hspan u hu
    have hz : z = 0 := by
      have h := hu0
      rw [Matrix.map_add _ (map_add _), (hT Y₀).2.1, zero_add] at h
      rw [← (hM z).2.2]
      exact coW_eq_zero G t _ h
    subst hz
    rw [map_zero, add_zero] at e1 ⊢
    rw [co_one, (hT Y₀).2.2, e1]
    exact congrFun (htr Y₀ φ hφ) Y
  · intro u hu hu1 φ hφ φ₁ _ hact x hx hx0
    have e1 := hφ₁ u hu φ hφ φ₁ hact
    obtain ⟨Y₀, z, rfl⟩ := hspan u hu
    have hY : Y₀ = 0 := by
      have h := hu1
      rw [Matrix.map_add _ (map_add _), (hM z).2.1, add_zero] at h
      rw [← (hT Y₀).2.2]
      exact h
    subst hY
    rw [map_zero, zero_add] at e1 ⊢
    rw [co_one, e1, GlobalTheory.VacIndic.psi_of_at B.ψ (at_symp _ _ _ x (uM z) hx), hsymp x (uM z) hx (hM z).1,
      coW_eq_zero G t x hx0, (hM z).2.1, (hM z).2.2]
    have h2 := congrFun (hmu z φ hφ) (x.map (piW t))
    simp only [AddMonoidHom.comp_apply] at h2
    rw [h2, ← GlobalTheory.LatVac.psiAt_apply]
    congr 2
    simp

end GlobalTheory.LinWAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNhdsTransportedActionFiniteOpenSubgroups
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

namespace GlobalTheory.WeilTransNbhdD

theorem exists_nhds_finite_preimage_D : ∀ (D : D7) (a b : ℕ) (JA : Matrix (Fin a) (Fin a) D.host.E) (JB : Matrix (Fin b) (Fin b) D.host.E)
    (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (κ : Type) [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ)
    (L₁ L₂ : AddSubgroup (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)),
    IsOpen (L₁ : Set (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)) →
    IsOpen (L₂ : Set (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)) →
    ∀ p0 : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB),
    ∃ N ∈ nhds p0, ∃ L₁' L₂' : AddSubgroup (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F),
      IsOpen (L₁' : Set (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ∧
      IsCompact (L₁' : Set (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ∧
      IsOpen (L₂' : Set (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ∧
      ∀ p ∈ N, ∀ x ∈ L₁', ∀ y ∈ L₂', ∃ x' ∈ L₁, ∃ y' ∈ L₂,
        co.e (GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) p
          (co.e.symm (GlobalTheory.WeilCont.adeleJoin D.host.F 0 x', GlobalTheory.WeilCont.adeleJoin D.host.F 0 y'))) =
          (GlobalTheory.WeilCont.adeleJoin D.host.F 0 x, GlobalTheory.WeilCont.adeleJoin D.host.F 0 y) := by
  intro D a b JA JB ξ κ _ co L₁ L₂ hL₁ hL₂ p0
  exact GlobalTheory.WeilTransNbhd.exists_nhds_finite_preimage D.host.F D.host.E D.sp.cm.sig a b JA JB ξ κ co L₁ L₂ hL₁ hL₂ p0

end GlobalTheory.WeilTransNbhdD
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNhdsTransportedActionFinitePointPreimageStatement
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nhds_transportedAction_finitePoint_preimage : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (a b : ℕ) (JA : Matrix (Fin a) (Fin a) E) (JB : Matrix (Fin b) (Fin b) E) (ξ : AF F ⊗[F] E) (κ : Type) [Fintype κ]
    (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ) (L₁ L₂ : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F)),
    IsOpen (L₁ : Set (κ → FiniteAdeleRing (𝓞 F) F)) → IsOpen (L₂ : Set (κ → FiniteAdeleRing (𝓞 F) F)) →
    ∀ p0 : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB),
    ∃ N ∈ nhds p0, ∃ L₁' L₂' : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F),
      IsOpen (L₁' : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧ IsCompact (L₁' : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧
      IsOpen (L₂' : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧
      ∀ p ∈ N, ∀ x ∈ L₁', ∀ y ∈ L₂', ∃ x' ∈ L₁, ∃ y' ∈ L₂,
        co.e (actAB (cA σ) p (co.e.symm (GlobalTheory.WeilCont.adeleJoin F 0 x', GlobalTheory.WeilCont.adeleJoin F 0 y'))) =
          (GlobalTheory.WeilCont.adeleJoin F 0 x, GlobalTheory.WeilCont.adeleJoin F 0 y) := by
  first | exact @GlobalTheory.WeilTransNbhd.exists_nhds_finite_preimage | exact GlobalTheory.WeilTransNbhd.exists_nhds_finite_preimage | (intros; apply GlobalTheory.WeilTransNbhd.exists_nhds_finite_preimage <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenSubgroupsSchroedingerFixContinuousCharStatement
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_openSubgroups_schroedinger_fix_continuousChar : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), Continuous ψ →
    ∀ (κ : Type) [Fintype κ], ∀ Φ ∈ schA F κ,
      ∃ L₁ L₂ : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F),
        IsOpen (L₁ : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧ IsOpen (L₂ : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧
        ∀ x ∈ L₁, ∀ y ∈ L₂, schr ψ (GlobalTheory.WeilCont.adeleJoin F 0 x, GlobalTheory.WeilCont.adeleJoin F 0 y) Φ = Φ := by
  first | exact @GlobalTheory.SchrFixFin.exists_fix | exact GlobalTheory.SchrFixFin.exists_fix | (intros; apply GlobalTheory.SchrFixFin.exists_fix <;> assumption)
end

