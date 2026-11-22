import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0229
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlanePairRestrictionFirst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1466
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1467
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1978
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1887
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1919
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousComplEquivSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1967
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1974
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1977
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1981
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1727
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1975
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1914
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1803
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1780
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1444

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLinEqOfEqOn
section
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval GlobalTheory.WeilTr

noncomputable section

namespace GlobalTheory.DblTr

section Blocks

variable {A : Type} {κ κ₁ κ' κ₁' : Type}

def partLe (U : ((κ → A) → ℂ) ≃ₗ[ℂ] ((κ₁ → A) → ℂ)) : ((κ ⊕ κ' → A) → ℂ) ≃ₗ[ℂ] ((κ₁ ⊕ κ' → A) → ℂ) :=
  { partLₗ U.toLinearMap with
    invFun := partL U.symm
    left_inv := fun Φ => by
      show partL U.symm (partL U Φ) = Φ
      rw [partL_partL]
      simp only [LinearEquiv.symm_apply_apply]
      exact partL_id Φ
    right_inv := fun Φ => by
      show partL U (partL U.symm Φ) = Φ
      rw [partL_partL]
      simp only [LinearEquiv.apply_symm_apply]
      exact partL_id Φ }

def partRe (U : ((κ' → A) → ℂ) ≃ₗ[ℂ] ((κ₁' → A) → ℂ)) : ((κ ⊕ κ' → A) → ℂ) ≃ₗ[ℂ] ((κ ⊕ κ₁' → A) → ℂ) :=
  { partRₗ U.toLinearMap with
    invFun := partR U.symm
    left_inv := fun Φ => by
      show partR U.symm (partR U Φ) = Φ
      rw [partR_partR]
      simp only [LinearEquiv.symm_apply_apply]
      exact partR_id Φ
    right_inv := fun Φ => by
      show partR U (partR U.symm Φ) = Φ
      rw [partR_partR]
      simp only [LinearEquiv.apply_symm_apply]
      exact partR_id Φ }

end Blocks

def conjE {X Y : Type} (U : (X → ℂ) ≃ₗ[ℂ] (Y → ℂ)) : (X → ℂ) ≃ₗ[ℂ] (Y → ℂ) :=
  { conjLin U.toLinearMap with
    invFun := conjLin U.symm.toLinearMap
    left_inv := fun φ => by
      funext x
      simp [conjLin_apply]
    right_inv := fun φ => by
      funext x
      simp [conjLin_apply] }

theorem conjE_apply {X Y : Type} (U : (X → ℂ) ≃ₗ[ℂ] (Y → ℂ)) (φ : X → ℂ) : conjE U φ = conjLin U.toLinearMap φ := rfl

end GlobalTheory.DblTr

namespace GlobalTheory.DblTr

section Gen

variable {F : Type} [Field F] [NumberField F]

theorem partL_eq_of_eqOn {κ κ₁ κ' : Type} [Fintype κ] [Fintype κ'] {T e : ((κ → AF F) → ℂ) → (κ₁ → AF F) → ℂ}
    (h : ∀ Φ ∈ schA F κ, T Φ = e Φ) {Φ : (κ ⊕ κ' → AF F) → ℂ} (hΦ : Φ ∈ schA F (κ ⊕ κ')) :
    partL T Φ = partL e Φ :=
  partL_congr fun b => h _ (sliceL_mem hΦ b)

theorem partR_eq_of_eqOn {κ κ' κ₁' : Type} [Fintype κ] [Fintype κ'] {T e : ((κ' → AF F) → ℂ) → (κ₁' → AF F) → ℂ}
    (h : ∀ Φ ∈ schA F κ', T Φ = e Φ) {Φ : (κ ⊕ κ' → AF F) → ℂ} (hΦ : Φ ∈ schA F (κ ⊕ κ')) :
    partR T Φ = partR e Φ :=
  partR_congr fun a => h _ (sliceR_mem hΦ a)

theorem conjLin_eq_of_eqOn {κ κ₁ : Type} [Fintype κ] {T e : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ₁ → AF F) → ℂ}
    (h : ∀ Φ ∈ schA F κ, T Φ = e Φ) : ∀ Φ ∈ schA F κ, conjLin T Φ = conjLin e Φ := fun Φ hΦ => by
  funext y
  rw [conjLin_apply, conjLin_apply, h _ (GlobalTheory.ConjSch.conj_mem_schA Φ hΦ)]

theorem adm_congr {κ : Type} [Fintype κ] {l l' : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ} (h : ∀ Φ ∈ schA F κ, l Φ = l' Φ)
    (hl : l' ∈ (adeleClass F).adm κ) : l ∈ (adeleClass F).adm κ := by
  intro g hg
  obtain ⟨T, hT⟩ := hl g hg
  exact ⟨T, fun f => by rw [h _ (Submodule.subset_span ⟨f, g, hg, rfl⟩), hT]⟩

theorem dbl_eq {κ : Type} [Fintype κ] (U : ((κ → AF F) → ℂ) ≃ₗ[ℂ] ((κ → AF F) → ℂ))
    (u : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (hu : IsLocOp u) (hUu : ∀ Φ ∈ schA F κ, U Φ = u Φ)
    {Φ : (κ ⊕ κ → AF F) → ℂ} (hΦ : Φ ∈ schA F (κ ⊕ κ)) :
    partR (conjLin U.toLinearMap) (partL U Φ) = partR (conjLin u) (partL u Φ) ∧
      partR (conjLin u) (partL u Φ) ∈ schA F (κ ⊕ κ) := by
  have h1 : partL U Φ = partL u Φ := partL_eq_of_eqOn hUu hΦ
  have h2 : partL u Φ ∈ schA F (κ ⊕ κ) := partL_mem u hu Φ hΦ
  refine ⟨?_, partR_mem (conjLin u) (GlobalTheory.DblEval.ConjLoc.isLocOp_conjLin u hu) _ h2⟩
  rw [h1]
  exact partR_eq_of_eqOn (conjLin_eq_of_eqOn (T := U.toLinearMap) hUu) h2

theorem dbl_eq' {κ : Type} [Fintype κ] (U : ((κ → AF F) → ℂ) ≃ₗ[ℂ] ((κ → AF F) → ℂ))
    (u : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (hu : IsLocOp u) (hUu : ∀ Φ ∈ schA F κ, U Φ = u Φ)
    {Φ : (κ ⊕ κ → AF F) → ℂ} (hΦ : Φ ∈ schA F (κ ⊕ κ)) :
    partL U (partR (conjLin U.toLinearMap) Φ) = partL u (partR (conjLin u) Φ) ∧
      partL u (partR (conjLin u) Φ) ∈ schA F (κ ⊕ κ) := by
  have h1 : partR (conjLin U.toLinearMap) Φ = partR (conjLin u) Φ :=
    partR_eq_of_eqOn (conjLin_eq_of_eqOn (T := U.toLinearMap) hUu) hΦ
  have h2 : partR (conjLin u) Φ ∈ schA F (κ ⊕ κ) :=
    partR_mem (conjLin u) (GlobalTheory.DblEval.ConjLoc.isLocOp_conjLin u hu) Φ hΦ
  refine ⟨?_, partL_mem u hu _ h2⟩
  rw [h1]
  exact partL_eq_of_eqOn hUu h2

end Gen

end GlobalTheory.DblTr

namespace GlobalTheory.DblTr

section Main

variable {F : Type} [Field F] [NumberField F]

theorem hasDbl_of_loc {E' : Type} [CommRing E'] [Algebra (AF F) E'] (c : E' →ₐ[AF F] E') {α β : Type} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (ξ : E') (JA : Matrix α α E') (JB : Matrix β β E') {κ : Type}
    [Fintype κ] (ψ : AddChar (AF F) ℂ) (hψ : ∀ t, ‖ψ t‖ = 1) (d d₁ : Darboux (symp c ξ JA JB) κ)
    (T : ((κ → AF F) → ℂ) ≃ₗ[ℂ] ((κ → AF F) → ℂ)) (e e' : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ))
    (hL : IsLocOp e) (hL' : IsLocOp e') (hTe : ∀ Φ ∈ schA F κ, T Φ = e Φ)
    (hTe' : ∀ Φ ∈ schA F κ, T.symm Φ = e' Φ) (hmem : ∀ Φ, Φ ∈ schA F κ ↔ T Φ ∈ schA F κ)
    (Heisenberg₂ : ∀ w, ∀ Φ ∈ schA F κ, T (d.rho ψ w Φ) = d₁.rho ψ w (T Φ))
    (hunit : ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ C : ℝ≥0∞, ∀ Φ ∈ schA F κ, ∫⁻ x, ‖T Φ x‖ₑ ^ 2 ∂μ = C * ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ) :
    HasDbl c (adeleClass F) ψ ξ JA JB d d₁ T := by
  intro dd hdd
  have hconj : ∀ Φ ∈ schA F κ, (fun x => starRingEnd ℂ (Φ x)) ∈ schA F κ := fun Φ hΦ =>
    GlobalTheory.ConjSch.conj_mem_schA Φ hΦ

  have hSmem : ∀ φ, φ ∈ schA F κ ↔ conjE T φ ∈ schA F κ := fun φ => by
    constructor
    · intro hφ
      have := hconj _ ((hmem _).1 (hconj φ hφ))
      exact this
    · intro hφ
      have h1 : (fun x => starRingEnd ℂ (conjE T φ x)) = T (fun x => starRingEnd ℂ (φ x)) := by
        funext x; simp [conjE_apply, conjLin_apply]
      have h2 := hconj _ hφ
      rw [h1, ← hmem] at h2
      have h3 := hconj _ h2
      simpa using h3

  have hLmem : ∀ Φ ∈ schA F (κ ⊕ κ), partL T Φ ∈ schA F (κ ⊕ κ) := fun Φ hΦ => by
    rw [partL_eq_of_eqOn hTe hΦ]; exact partL_mem e hL Φ hΦ
  have hRmem : ∀ Φ ∈ schA F (κ ⊕ κ), partR (conjE T) Φ ∈ schA F (κ ⊕ κ) := fun Φ hΦ => by
    have h := partR_eq_of_eqOn (κ := κ) (conjLin_eq_of_eqOn (T := T.toLinearMap) hTe) hΦ
    rw [show partR (conjE T) Φ = partR (conjLin T.toLinearMap) Φ from rfl, h]
    exact partR_mem (conjLin e) (GlobalTheory.DblEval.ConjLoc.isLocOp_conjLin e hL) Φ hΦ

  have heis₂ : ∀ w, ∀ φ ∈ schA F κ, conjE T (d.rho ψ⁻¹ w φ) = d₁.rho ψ⁻¹ w (conjE T φ) := fun w φ hφ => by
    funext y
    rw [conjE_apply, conjLin_apply]
    have h1 : (fun x => starRingEnd ℂ (d.rho ψ⁻¹ w φ x)) = d.rho ψ w (fun x => starRingEnd ℂ (φ x)) :=
      funext fun x => conj_schr_inv ψ hψ _ _ _
    rw [LinearEquiv.coe_coe, h1, Heisenberg₂ w _ (hconj φ hφ)]
    exact conj_schr ψ hψ _ _ _

  have hunitS : ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ C : ℝ≥0∞, ∀ Φ ∈ schA F κ, ∫⁻ x, ‖conjE T Φ x‖ₑ ^ 2 ∂μ = C * ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ := fun μ hμ => by
    obtain ⟨C, hC⟩ := hunit μ hμ
    refine ⟨C, fun Φ hΦ => ?_⟩
    have h1 := hC _ (hconj Φ hΦ)
    have hce : ∀ z : ℂ, ‖starRingEnd ℂ z‖ₑ = ‖z‖ₑ := fun z => by
      rw [enorm_eq_nnnorm, enorm_eq_nnnorm]
      congr 1
      ext
      simp
    simp only [conjE_apply, conjLin_apply, LinearEquiv.coe_coe, hce] at h1 ⊢
    exact h1
  set Td : ((κ ⊕ κ → AF F) → ℂ) ≃ₗ[ℂ] ((κ ⊕ κ → AF F) → ℂ) := (partLe (κ' := κ) T).trans (partRe (κ := κ) (conjE T))
    with hTd
  have hTd_apply : ∀ Φ, Td Φ = partR (conjE T) (partL T Φ) := fun Φ => rfl
  have hTd_symm : ∀ Φ, Td.symm Φ = partL T.symm (partR (conjE T).symm Φ) := fun Φ => rfl
  have hTeq : ∀ Φ ∈ schA F (κ ⊕ κ), Td Φ = partR (conjLin e) (partL e Φ) ∧ partR (conjLin e) (partL e Φ) ∈ schA F (κ ⊕ κ) :=
    fun Φ hΦ => dbl_eq T e hL hTe hΦ
  have hTeq' : ∀ Φ ∈ schA F (κ ⊕ κ), Td.symm Φ = partL e' (partR (conjLin e') Φ) ∧
      partL e' (partR (conjLin e') Φ) ∈ schA F (κ ⊕ κ) :=
    fun Φ hΦ => dbl_eq' T.symm e' hL' hTe' hΦ
  refine ⟨GlobalTheory.DblSchr.dblD c d₁, Td, conjE T, GlobalTheory.DblSchr.isDblCoord_dblD c d₁, ⟨fun Φ => ?_, fun w Φ hΦ => ?_,
    fun l => ?_, fun μ hμ => ?_⟩, hSmem, fun φ₁ _ φ₂ _ => ?_⟩
  · constructor
    · intro hΦ
      rw [(hTeq Φ hΦ).1]; exact (hTeq Φ hΦ).2
    · intro hΦ
      have := (hTeq' _ hΦ)
      rw [LinearEquiv.symm_apply_apply] at this
      rw [this.1]; exact this.2
  · rw [← Matrix.fromCols_toCols w, rho_dbl c ξ JA JB d dd hdd, rho_dbl c ξ JA JB d₁ _ (GlobalTheory.DblSchr.isDblCoord_dblD c d₁),
      hTd_apply, hTd_apply]
    have hc1 : ∀ Ψ : (κ ⊕ κ → AF F) → ℂ, partL T (partR (d.rho ψ⁻¹ w.toCols₂) Ψ) =
        partR (d.rho ψ⁻¹ w.toCols₂) (partL T Ψ) := fun Ψ => partL_partR_rho T.toLinearMap d ψ⁻¹ _ Ψ
    have hc2 : ∀ Ψ : (κ ⊕ κ → AF F) → ℂ, partR (conjE T) (partL (d₁.rho ψ w.toCols₁) Ψ) =
        partL (d₁.rho ψ w.toCols₁) (partR (conjE T) Ψ) := fun Ψ => partR_partL_rho (conjE T).toLinearMap d₁ ψ _ Ψ
    rw [partL_intertwine T (d.rho ψ w.toCols₁) (d₁.rho ψ w.toCols₁) T _ (fun φ hφ => Heisenberg₂ _ φ hφ)
        (fun b => by rw [sliceL_partR_rho]; exact Submodule.smul_mem _ _ (sliceL_mem hΦ _)),
      hc1, hc2,
      partR_intertwine (conjE T) (d.rho ψ⁻¹ w.toCols₂) (d₁.rho ψ⁻¹ w.toCols₂) (conjE T) _ (fun φ hφ => heis₂ _ φ hφ)
        (fun a => sliceR_mem (hLmem Φ hΦ) a)]
  · constructor
    · intro hl
      refine adm_congr (l' := (l ∘ₗ partRₗ (conjLin e)) ∘ₗ partLₗ e) (fun Φ hΦ => ?_)
        (partL_adm e hL _ (partR_adm (conjLin e) (GlobalTheory.DblEval.ConjLoc.isLocOp_conjLin e hL) l hl))
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, partLₗ_apply, partRₗ_apply]
      rw [(hTeq Φ hΦ).1]
    · intro hl
      refine adm_congr (l' := ((l ∘ₗ Td.toLinearMap) ∘ₗ partLₗ e') ∘ₗ partRₗ (conjLin e')) (fun Φ hΦ => ?_)
        (partR_adm (conjLin e') (GlobalTheory.DblEval.ConjLoc.isLocOp_conjLin e' hL') _ (partL_adm e' hL' _ hl))
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, partLₗ_apply, partRₗ_apply]
      rw [← (hTeq' Φ hΦ).1, LinearEquiv.apply_symm_apply]
  · obtain ⟨C₁, hC₁⟩ := GlobalTheory.T.partial_fourier_preserves_schwartz_L2 T.toLinearMap hunit hLmem μ hμ
    obtain ⟨C₂, hC₂⟩ := GlobalTheory.T.partial_right_preserves_l2_norm (κ := κ) (conjE T).toLinearMap hunitS hRmem μ hμ
    refine ⟨C₂ * C₁, fun φ hφ => ?_⟩
    rw [hTd_apply]
    have h2 := hC₂ _ (hLmem φ hφ)
    have h1 := hC₁ φ hφ
    simp only [LinearEquiv.coe_coe] at h1 h2
    rw [h2, h1, mul_assoc]
  · funext y
    rw [hTd_apply]
    simp only [partR, partL, boxFun, Sum.elim_comp_inl, Sum.elim_comp_inr]
    have h1 : (fun x => T (fun x' => φ₁ x' * φ₂ x) (y ∘ Sum.inl)) = T φ₁ (y ∘ Sum.inl) • φ₂ := funext fun x => by
      rw [show (fun x' => φ₁ x' * φ₂ x) = φ₂ x • φ₁ from funext fun x' => by simp [mul_comm], map_smul]
      simp [mul_comm]
    rw [h1, map_smul]
    rfl

end Main

end GlobalTheory.DblTr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DatumPhiASplitPlaceTransportEq
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

noncomputable section

namespace GlobalTheory.PureMatch.Transport
open GlobalTheory.FlipMatch GlobalTheory.FlipMatch.FieldTransport
open scoped Pointwise

section General
variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {j : k ≃+* k'}
  {A A' D A₂ A₂' D₂ : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
  [Fintype A₂] [DecidableEq A₂] [Fintype A₂'] [DecidableEq A₂'] [Fintype D₂] [DecidableEq D₂]

theorem corr_smul_of (hj : IsLocIso j) (cD : D₂ ≃ D) {Λ : Submodule 𝒪[k] (D → k)} {Λ₂ : Submodule 𝒪[k'] (D₂ → k')}
    (h : LatCorr j cD Λ Λ₂) (c : kˣ) (c₂ : k'ˣ) (hc : valuation k' (j c) = valuation k' (c₂ : k')) :
    LatCorr j cD (c • Λ) (c₂ • Λ₂) := latCorr_smul hj cD h c c₂ hc

theorem corr_dual_of (hj : IsLocIso j) (cD : D₂ ≃ D) {Λ : Submodule 𝒪[k] (D → k)} {Λ₂ : Submodule 𝒪[k'] (D₂ → k')}
    (h : LatCorr j cD Λ Λ₂) : LatCorr j cD (dualLat Λ) (dualLat Λ₂) := GlobalTheory.T.dualLattice_correspondingLattices hj cD h

theorem primFrame_corr (hj : IsLocIso j) (rA : A₂ ≃ A) (cD : D₂ ≃ D) {Λ : Submodule 𝒪[k] (D → k)}
    {Λ₂ : Submodule 𝒪[k'] (D₂ → k')} (h : LatCorr j cD Λ Λ₂) (Z : Matrix A D k) :
    IsPrimFrame Λ₂ (trM j rA cD Z) ↔ IsPrimFrame Λ Z := GlobalTheory.T.isPrimitiveFrame_matrixTransport_iff hj rA cD h Z

theorem corr_blockLat_of (hj : IsLocIso j) (cD : D₂ ≃ D) {ϖ : kˣ} {ϖ₂ : k'ˣ} (hϖ : IsUnif ϖ) (hϖ₂ : IsUnif ϖ₂)
    (e : ℕ) (P : Finset D) (P₂ : Finset D₂) (hP : ∀ c, c ∈ P₂ ↔ cD c ∈ P) :
    LatCorr j cD (blockLat ϖ e P) (blockLat ϖ₂ e P₂) := GlobalTheory.T.correspondingLattices_blockLattice hj cD hϖ hϖ₂ e P P₂ hP

variable [MeasurableSpace k] [BorelSpace k] [MeasurableSpace k'] [BorelSpace k']

theorem fFun_corr (hj : IsLocIso j) (rA : A₂ ≃ A) (rA' : A₂' ≃ A') (cD : D₂ ≃ D)
    (μ₂ : MeasureTheory.Measure (GL A₂' k')) [μ₂.IsHaarMeasure] (σ₂ : A₂ ⊕ A₂' ≃ D₂) (σ : A ⊕ A' ≃ D)
    (hσ : ∀ s, cD (σ₂ s) = σ (Sum.map rA rA' s)) (ν₂ : k'ˣ →* ℂˣ) (ν : kˣ →* ℂˣ)
    (hν : ∀ x, ν x = ν₂ (Units.map (j : k →* k') x)) (Ψ : Matrix A₂' D₂ k' → ℂ) (Z : Matrix A D k) :
    fFun μ₂ σ₂ ν₂ Ψ (trM j rA cD Z) = fFun (pullMeas hj rA' μ₂) σ ν (fun Y => Ψ (trM j rA' cD Y)) Z :=
  GlobalTheory.T.zetaFunction_transport_localFieldIso hj rA rA' cD μ₂ σ₂ σ hσ ν₂ ν hν Ψ Z

end General
end GlobalTheory.PureMatch.Transport

namespace GlobalTheory.PureMatch.Transport
open GlobalTheory.FlipMatch GlobalTheory.FlipMatch.FieldTransport
open scoped Pointwise

section General
variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {j : k ≃+* k'}
  {A A' D A₂ A₂' D₂ : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
  [Fintype A₂] [DecidableEq A₂] [Fintype A₂'] [DecidableEq A₂'] [Fintype D₂] [DecidableEq D₂]

theorem latCorr_latA (hj : IsLocIso j) (cD : D₂ ≃ D) {Λ : Submodule 𝒪[k] (D → k)} {Λ₂ : Submodule 𝒪[k'] (D₂ → k')}
    (h : LatCorr j cD Λ Λ₂) {ϖ : kˣ} {ϖ₂ : k'ˣ} (hϖ : IsUnif ϖ) (hϖ₂ : IsUnif ϖ₂) (e : ℕ) :
    LatCorr j cD (latA ϖ e Λ) (latA ϖ₂ e Λ₂) := by
  refine corr_smul_of hj cD (corr_dual_of hj cD h) _ _ ?_
  have h1 : valuation k' (j ϖ) = valuation k' (ϖ₂ : k') := (isUnif_map hj hϖ).trans hϖ₂.symm
  simp only [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_inv₀, map_pow, h1]

theorem trM_mem_matLat (rA : A₂ ≃ A) (cD : D₂ ≃ D) {Λ : Submodule 𝒪[k] (D → k)} {Λ₂ : Submodule 𝒪[k'] (D₂ → k')}
    (h : LatCorr j cD Λ Λ₂) (Z : Matrix A D k) : trM j rA cD Z ∈ matLat A₂ Λ₂ ↔ Z ∈ matLat A Λ := by
  rw [mem_matLat, mem_matLat]
  refine ⟨fun H a => ?_, fun H r => (h (Z.row (rA r))).2 (H _)⟩
  obtain ⟨r, rfl⟩ := rA.surjective a
  exact (h (Z.row (rA r))).1 (H r)

theorem hasDepth_trM (hj : IsLocIso j) (rA : A₂ ≃ A) (cD : D₂ ≃ D) {Λ : Submodule 𝒪[k] (D → k)}
    {Λ₂ : Submodule 𝒪[k'] (D₂ → k')} (h : LatCorr j cD Λ Λ₂) {ϖ : kˣ} {ϖ₂ : k'ˣ} (hϖ : IsUnif ϖ)
    (hϖ₂ : IsUnif ϖ₂) (e : ℕ) (Ξ : Matrix A D k → ℂ) (hΞ : HasDepth ϖ e Λ Ξ) :
    HasDepth ϖ₂ e Λ₂ (fun Y => Ξ (trM j.symm rA.symm cD.symm Y)) := by
  have h1 : valuation k' (j ϖ) = valuation k' (ϖ₂ : k') := (isUnif_map hj hϖ).trans hϖ₂.symm
  have hs : LatCorr j cD (ϖ ^ e • Λ) (ϖ₂ ^ e • Λ₂) := corr_smul_of hj cD h _ _ (by
    simp only [Units.val_pow_eq_pow_val, map_pow]; rw [h1])
  refine ⟨fun Y hY => hΞ.1 _ fun hZ => hY ?_, fun Y W hW => ?_⟩
  · rw [← trM_trM_symm j rA cD Y]; exact (trM_mem_matLat rA cD h _).2 hZ
  · have hW' : trM j.symm rA.symm cD.symm W ∈ matLat A (ϖ ^ e • Λ) := by
      rw [← trM_mem_matLat rA cD hs, trM_trM_symm]; exact hW
    show Ξ (trM j.symm rA.symm cD.symm (Y + W)) = Ξ (trM j.symm rA.symm cD.symm Y)
    rw [show trM j.symm rA.symm cD.symm (Y + W) = trM j.symm rA.symm cD.symm Y + trM j.symm rA.symm cD.symm W by
      ext r c; simp]
    exact hΞ.2 _ _ hW'

variable [MeasurableSpace k] [BorelSpace k] [MeasurableSpace k'] [BorelSpace k']

theorem phiA_trM (hj : IsLocIso j) (rA : A₂ ≃ A) (rA' : A₂' ≃ A') (cD : D₂ ≃ D)
    (μ₂ : MeasureTheory.Measure (GL A₂' k')) [μ₂.IsHaarMeasure] (σ₂ : A₂ ⊕ A₂' ≃ D₂) (σ : A ⊕ A' ≃ D)
    (hσ : ∀ s, cD (σ₂ s) = σ (Sum.map rA rA' s)) (ν₂ : k'ˣ →* ℂˣ) (ν : kˣ →* ℂˣ)
    (hν : ∀ x, ν x = ν₂ (Units.map (j : k →* k') x)) {ϖ : kˣ} {ϖ₂ : k'ˣ} (hϖ : IsUnif ϖ) (hϖ₂ : IsUnif ϖ₂) (e : ℕ)
    {Λ : Submodule 𝒪[k] (D → k)} {Λ₂ : Submodule 𝒪[k'] (D₂ → k')} (h : LatCorr j cD Λ Λ₂)
    (Ψ : Matrix A₂' D₂ k' → ℂ) (Z : Matrix A D k) :
    phiA μ₂ σ₂ ν₂ ϖ₂ e Λ₂ Ψ (trM j rA cD Z) =
      phiA (pullMeas hj rA' μ₂) σ ν ϖ e Λ (fun Y => Ψ (trM j rA' cD Y)) Z := by
  classical
  unfold phiA
  rw [primFrame_corr hj rA cD (latCorr_latA hj cD h hϖ hϖ₂ e), fFun_corr hj rA rA' cD μ₂ σ₂ σ hσ ν₂ ν hν]

end General
end GlobalTheory.PureMatch.Transport

namespace GlobalTheory.PureMatch
open GlobalTheory.PureMatch.Transport GlobalTheory.FlipMatch

theorem mem_one_block_iff {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (t : T)
    (w : Pl D.host.E) {i j : Fin D.R.m} (e : Num G i j) (c : (locGrid G t w).Cols i j) :
    c ∈ Assignment.one.block _ _ ↔ GlobalTheory.SquareFlipReach.colE t w e c ∈ blockV e := by
  rcases c with c | c
  · simp [Assignment.block, blockV, GlobalTheory.SquareFlipReach.colE]
  · simp [Assignment.block, blockV, GlobalTheory.SquareFlipReach.colE]

theorem phiA_transport_split_place : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m) (e : Num G i j) (w : Pl D.host.E) (hw : w ∈ locPl G t) (v : Pl D.host.F) (hv : w.under (𝓞 D.host.F) = v)
    (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v), splitPrime τ = w → ∀ n : ℕ,
    ∃ (μ : @Measure (GL (Fin (spW₁ G i j).rank) (Fv D.host.F v)) Units.instMeasurableSpace)
      (_ : @Measure.IsHaarMeasure _ _ _ Units.instMeasurableSpace μ)
      (σ' : Fin (spW G i j).rank ⊕ Fin (spW₁ G i j).rank ≃ Fin ((spW G i j).rank + (spW₁ G i j).rank)),
      (∀ (Ψ : Matrix (Fin ((locGrid G t w).rank ((i : ℕ), (j : ℕ)))) ((locGrid G t w).Cols i j) (Kw w) → ℂ) Z,
        phiA (haarVol ((givenLevel G t w ((i : ℕ), (j : ℕ))).map invT)) (stdSplit ((locGrid G t w).rank_square i j))
          ((locGrid G t w).nu i j) (unifAt w) n (blockLat (unifAt w) n (Assignment.one.block _ _)) Ψ (trA t hv e Z) =
        phiA μ σ' (((locGrid G t w).nu i j).comp (Units.map (GlobalTheory.LFun.complMap hv).toMonoidHom)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) n
          (blockLat (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) n (blockV e)) (fun Y => Ψ (trB t hv e Y)) Z) ∧
      ∀ Ξ, HasDepth (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) n (blockLat (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) n (blockV e)) Ξ →
        ∃ Ξ', HasDepth (unifAt w) n (blockLat (unifAt w) n (Assignment.one.block _ _)) Ξ' ∧ ∀ Y, Ξ' (trB t hv e Y) = Ξ Y := by
  intro D T L sc G μ₀ hL t i j e w hw v hv τ hτ n
  subst hτ
  have hjj := isLocIso_complEquiv τ hv
  have hO := GivenAdm.givenLevel_open (G := G) hL hw ((i : ℕ), (j : ℕ))
  have hO' := isOpen_map_invT hO.1 hO.2
  haveI := isHaarMeasure_haarVol hO'.1 hO'.2
  have hϖv : IsUnif (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) := (GlobalTheory.SplitFlip.exists_isUnif (k := Fv D.host.F v)).choose_spec
  have hc := corr_blockLat_of hjj (GlobalTheory.SquareFlipReach.colE t (splitPrime τ) e) hϖv (isUnif_unifAt _) n (blockV e)
      (Assignment.one.block _ _) (mem_one_block_iff t _ e)
  refine ⟨pullMeas hjj (rowB t (splitPrime τ) i j)
      (haarVol ((givenLevel G t (splitPrime τ) ((i : ℕ), (j : ℕ))).map invT)), inferInstance,
    (Equiv.sumCongr (GlobalTheory.SquareFlipReach.rowE t (splitPrime τ) i j).symm (rowB t (splitPrime τ) i j).symm).trans
      ((stdSplit ((locGrid G t (splitPrime τ)).rank_square i j)).trans (GlobalTheory.SquareFlipReach.colE t (splitPrime τ) e)),
    fun Ψ Z => ?_, fun Ξ hΞ => ?_⟩
  · exact phiA_trM hjj (GlobalTheory.SquareFlipReach.rowE t (splitPrime τ) i j) (rowB t (splitPrime τ) i j)
      (GlobalTheory.SquareFlipReach.colE t (splitPrime τ) e) _ _ _ (fun s => by simp) _ _ (fun x => rfl) hϖv
      (isUnif_unifAt _) n hc Ψ Z
  · exact ⟨_, hasDepth_trM hjj (rowB t (splitPrime τ) i j) (GlobalTheory.SquareFlipReach.colE t (splitPrime τ) e) hc hϖv
      (isUnif_unifAt _) n Ξ hΞ, fun Y => by
        show Ξ (trM _ _ _ (trM (GlobalTheory.LFun.SplitTie.complEquiv τ hv) (rowB t (splitPrime τ) i j)
          (GlobalTheory.SquareFlipReach.colE t (splitPrime τ) e) Y)) = Ξ Y
        rw [trM_symm_trM]⟩

end GlobalTheory.PureMatch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDefiniteBottomTripleTransferredFrames
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotFrames

theorem frames_transfer : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (S : GridChoice W Set.univ),
    IsStdChar D W.ψ (-1) → ∀ μ₀ : T, L.Is μ₀ → NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
    (X Y : Tri T A A' WW), IsBottomTri W i j X → IsBottomTri W i j Y →
    ∃ Y₁ : Tri T A A' WW, IsBottomTri W i j Y₁ ∧ Y₁.rA = X.rA ∧ Y₁.rA' = X.rA' ∧ Y₁.rW = X.rW ∧
      ∀ c : T → ℂ, Y.IsConst W.ψ W.θ c → ∃ u : T → D.what₂.LLˣ, Y₁.IsConst W.ψ W.θ fun t => D.what₂.embLL (u t) * c t := by
  intro D T L sc G W S _ μ₀ hL hN i j A A' WW X Y hX hY
  choose g g' h x x' y hE using fun t => GlobalTheory.T.exists_supported_unitaries_moving_bottomTriples W i j A A' WW X Y hX hY t
  have hC := fun t => GlobalTheory.T.definite_bottom_triple_basis_change_factor_mem_field W S μ₀ hL hN i j A A' WW Y hY t (g t) (g' t) (h t) (x t) (x' t) (y t)
    (hE t).1.1 (hE t).1.2.1 (hE t).1.2.2 (hE t).2.1.1 (hE t).2.1.2.1 (hE t).2.1.2.2 (hE t).2.2.1.1 (hE t).2.2.1.2.1
    (hE t).2.2.1.2.2
  choose z hz using hC
  have κne : ∀ t, ((splitFacO (GlobalTheory.BotFrames.botBeta G i j) (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.botAlpha L i j t)
      (x t) (y t) : Circle) : ℂ) ≠ 0 := fun t => Circle.coe_ne_zero _
  have κne' : ∀ t, ((splitFacO (GlobalTheory.BotFrames.botAlpha L i j t) (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j)
      (x' t) (y t) : Circle) : ℂ) ≠ 0 := fun t => Circle.coe_ne_zero _
  have sA := GlobalTheory.BotFrames.isStd_s_eq hX.std hY.std
  have sA' := GlobalTheory.BotFrames.isStd_s_eq hX.std' hY.std'
  have sW := GlobalTheory.BotFrames.isStd_s_eq hX.stdW hY.stdW
  have lA := GlobalTheory.BotFrames.isStd_lat_eq hX.std hY.std
  have lA' := GlobalTheory.BotFrames.isStd_lat_eq hX.std' hY.std'
  have lW := GlobalTheory.BotFrames.isStd_lat_eq hX.stdW hY.stdW
  refine ⟨GlobalTheory.BotFrames.reRig Y X.rA X.rA' X.rW
    (fun t => ((splitFacO (GlobalTheory.BotFrames.botBeta G i j) (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.botAlpha L i j t)
      (x t) (y t) : Circle) : ℂ) • Y.ω t ((g t)⁻¹, (h t)⁻¹) (Y.f t))
    (fun t => ((splitFacO (GlobalTheory.BotFrames.botAlpha L i j t) (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j)
      (x' t) (y t) : Circle) : ℂ) • Y.ω' t ((g' t)⁻¹, (h t)⁻¹) (Y.f' t)),
    ⟨hY.rank, hY.rank', hX.std, hX.std', hX.stdW, ?_⟩, rfl, rfl, rfl, fun c hc => ?_⟩
  · have hi := hY.is
    refine ⟨hi.rank, hX.is.rigA, hX.is.rigA', hX.is.rigW, hi.weil, hi.weil', ?_, ?_, hi.idem, hi.expo,
      fun t => GlobalTheory.T.standardPairFirstMember_movedDatum_splittingScale W i j A A' WW X Y hX hY t (g t) (h t) (x t) (y t) (hE t).1.1 (hE t).1.2.1 (hE t).1.2.2 (hE t).2.2.1.1
        (hE t).2.2.1.2.1 (hE t).2.2.1.2.2 (hE t).2.2.2.1,
      fun t => GlobalTheory.T.standard_pair_second_eq_moved_bottom_datum W i j A A' WW X Y hX hY t (g' t) (h t) (x' t) (y t) (hE t).2.1.1 (hE t).2.1.2.1 (hE t).2.1.2.2
        (hE t).2.2.1.1 (hE t).2.2.1.2.1 (hE t).2.2.1.2.2 (hE t).2.2.2.2, hi.meas, hi.meas'⟩
    · show IsVacO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.Λ X.rW.Λ Y.vac
      rw [sA, sW, lA, lW]
      exact hi.isVac
    · show IsVacO W.ψ W.θ A' WW X.rA'.s X.rW.s X.rA'.Λ X.rW.Λ Y.vac'
      rw [sA', sW, lA', lW]
      exact hi.isVac'
  · refine ⟨fun t => (z t)⁻¹, ?_⟩
    have hD := GlobalTheory.T.definiteBottomTriple_weilMove_rightTranslate W i j A A' WW X Y hX hY g g' h _ _ κne κne' (fun t => ⟨(hE t).1.1, (hE t).1.2.1⟩)
      (fun t => ⟨(hE t).2.1.1, (hE t).2.1.2.1⟩) (fun t => ⟨(hE t).2.2.1.1, (hE t).2.2.1.2.1⟩) c hc
    convert hD using 2 with t
    rw [map_units_inv, hz t, inv_div]

end GlobalTheory.BotFrames

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieScalarStatement
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieScalar_of_prints_derEx_vacLine : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.VacLine → GlobalTheory.RealLift.LieScalar := by
  first | exact @GlobalTheory.LieScal.lieScalar | exact GlobalTheory.LieScal.lieScalar | (intros; apply GlobalTheory.LieScal.lieScalar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOperatorInverseLocalStatement
section
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_operator_inverse_local : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (e : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)), IsLocOp e →
    Set.BijOn e (schA F κ : Set ((κ → AF F) → ℂ)) (schA F κ : Set ((κ → AF F) → ℂ)) →
    ∃ e' : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ), IsLocOp e' ∧ ∀ Φ ∈ schA F κ, e' (e Φ) = Φ := by
  first | exact @GlobalTheory.LocOpInv.isLocOp_inv | exact GlobalTheory.LocOpInv.isLocOp_inv | (intros; apply GlobalTheory.LocOpInv.isLocOp_inv <;> assumption)
end

