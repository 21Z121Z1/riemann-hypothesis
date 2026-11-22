import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLiftModelsOn
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0026
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0283
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import ReciprocityTheory.DualLattices.Bundle0018
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0030
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0078
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0278
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0259
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowsPrescribedUnitaryFormsStandIns
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameForm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSStageUnconditional

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHilbertChainOfLevelOverTops
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.ChainHilb

section Gen

variable {N : Type} [AddCommGroup N] [Module ℂ N] {C : Submodule ℂ N} {ip : N → N → ℂ}

theorem hp_add_right (h : PeterssonHilbertSpace.IsHermPos C ip) (x y y' : C) : ip x ((y : N) + y') = ip x y + ip x y' := by
  rw [← Submodule.coe_add, ← h.herm (y + y') x, Submodule.coe_add, h.add y y' x, map_add, h.herm y x, h.herm y' x]

theorem hp_smul_right (h : PeterssonHilbertSpace.IsHermPos C ip) (s : ℂ) (x y : C) : ip x (s • (y : N)) = s * ip x y := by
  rw [← Submodule.coe_smul, ← h.herm (s • y) x, Submodule.coe_smul, h.smul s y x, map_mul, h.herm y x,
    Complex.conj_conj]

theorem hp_restrict (h : PeterssonHilbertSpace.IsHermPos C ip) {C' : Submodule ℂ N} (hle : C' ≤ C) : PeterssonHilbertSpace.IsHermPos C' ip := by
  haveI := h.fd
  refine ⟨Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle), ?_, ?_, ?_, ?_⟩
  · intro x x' y; exact h.add ⟨x, hle x.2⟩ ⟨x', hle x'.2⟩ ⟨y, hle y.2⟩
  · intro s x y; exact h.smul s ⟨x, hle x.2⟩ ⟨y, hle y.2⟩
  · intro x y; exact h.herm ⟨x, hle x.2⟩ ⟨y, hle y.2⟩
  · intro x hx
    refine h.pos ⟨x, hle x.2⟩ ?_
    intro h0; apply hx; ext; simpa using congrArg Subtype.val h0

theorem hp_model (h : PeterssonHilbertSpace.IsHermPos C ip) : ∃ H : Hs, ∃ j : H.T →ₗ[ℂ] N,
    Function.Injective j ∧ LinearMap.range j = C ∧ ∀ x x', ⟪x, x'⟫_ℂ = ip (j x) (j x') := by
  have h1 : ∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C, ∀ c : ℂ, ip x (y + c • z) = ip x y + c * ip x z ∧ ip y x = star (ip x y) := by
    intro x hx y hy z hz c
    refine ⟨?_, ?_⟩
    · have e1 := hp_add_right h ⟨x, hx⟩ ⟨y, hy⟩ ⟨c • z, C.smul_mem c hz⟩
      have e2 := hp_smul_right h c ⟨x, hx⟩ ⟨z, hz⟩
      exact e1.trans (congrArg (fun t => ip x y + t) e2)
    · exact (h.herm ⟨x, hx⟩ ⟨y, hy⟩).symm
  have h2 : ∀ x ∈ C, x ≠ 0 → 0 < (ip x x).re := fun x hx hne =>
    h.pos ⟨x, hx⟩ (fun h0 => hne (by simpa using congrArg Subtype.val h0))
  obtain ⟨M, hM⟩ := GlobalTheory.HilbertModel.exists_hmod N C ip h.fd h1 h2
  exact ⟨⟨M.H⟩, M.e, hM.1, hM.2.1, hM.2.2⟩

theorem hp_riesz {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (h : PeterssonHilbertSpace.IsHermPos C ip) (j : H →ₗ[ℂ] N) (hj : ∀ x, j x ∈ C) :
    ∃ r : C →ₗ[ℂ] H, ∀ x (w : C), ⟪x, r w⟫_ℂ = ip (j x) w := by
  have key : ∀ w : C, ∃ y : H, ∀ x, ⟪x, y⟫_ℂ = ip (j x) w := by
    intro w
    let φ : H →ₗ[ℂ] ℂ :=
      { toFun := fun x => ip w (j x)
        map_add' := fun a b => by
          have := hp_add_right h w ⟨j a, hj a⟩ ⟨j b, hj b⟩
          simpa [map_add] using this
        map_smul' := fun s a => by
          have := hp_smul_right h s w ⟨j a, hj a⟩
          simpa [map_smul] using this }
    refine ⟨(InnerProductSpace.toDual ℂ H).symm (LinearMap.toContinuousLinearMap φ), fun x => ?_⟩
    rw [← inner_conj_symm, InnerProductSpace.toDual_symm_apply]
    exact h.herm w ⟨j x, hj x⟩
  choose y hy using key
  refine ⟨⟨⟨y, fun a b => ext_inner_left ℂ fun x => ?_⟩, fun s a => ext_inner_left ℂ fun x => ?_⟩, fun x w => hy w x⟩
  · rw [inner_add_right, hy, hy, hy, Submodule.coe_add]
    exact hp_add_right h ⟨j x, hj x⟩ a b
  · rw [RingHom.id_apply, inner_smul_right, hy, hy, Submodule.coe_smul]
    exact hp_smul_right h s ⟨j x, hj x⟩ a

end Gen

def heqv {A B : Hs} (h : A = B) : A.T ≃ₗᵢ[ℂ] B.T := by
  subst h; exact LinearIsometryEquiv.refl ℂ A.T

theorem heqv_heq {A B E : Hs} (e1 : A = E) (e2 : B = E) (v' : A.T) (v : B.T) (h : HEq v' v) :
    heqv e1 v' = heqv e2 v := by
  subst e1; subst e2; cases h; rfl

theorem heqv_self {A : Hs} (h : A = A) (x : A.T) : heqv h x = x := rfl

def chSel (m : ℕ) (A B : Hs) (L : ℕ → Hs) (j : ℕ) : Hs := if j = 0 then A else if j = m then B else L j

theorem chSel_zero {m : ℕ} {A B : Hs} {L : ℕ → Hs} : chSel m A B L 0 = A := if_pos rfl

theorem chSel_top {m : ℕ} {A B : Hs} {L : ℕ → Hs} (hm : m ≠ 0) : chSel m A B L m = B := by
  rw [chSel, if_neg hm, if_pos rfl]

theorem chSel_mid {m j : ℕ} {A B : Hs} {L : ℕ → Hs} (h1 : j ≠ 0) (h2 : j ≠ m) : chSel m A B L j = L j := by
  rw [chSel, if_neg h1, if_neg h2]

end GlobalTheory.ChainHilb

namespace GlobalTheory.ChainHilb

theorem exists_chainHilb : ∀ (D : D7) (C : ChainReal D) (b : Bool) (U : D.what₂.Tup → Prop) (Top : D.what₂.Tup → Hs) (jX : ∀ μ, (Top μ).T →ₗ[ℂ] C.AmbX), 2 ≤ D.R.m → PeterssonHilbertSpace.IsHermPos (C.EEc b) (C.ipE b) → (∀ μ, C.EEc b ≤ C.CC b μ 0 ∧ C.CCXP b μ ≤ C.CCX b μ ∧ PeterssonHilbertSpace.IsHermPos (C.CCX b μ) (C.ipXP b μ) ∧ ∀ j, j ≤ D.R.m - 1 → C.CCP b μ j ≤ C.CC b μ j ∧ PeterssonHilbertSpace.IsHermPos (C.CC b μ j) (C.ipP b μ j)) → (∀ μ, PeterssonHilbertSpace.IsHermPos (C.CC b μ 0) (C.ipE b)) → (∀ μ, U μ → Function.Injective (jX μ) ∧ LinearMap.range (jX μ) = C.CCXP b μ ∧ ∀ x x', ⟪x, x'⟫_ℂ = C.ipXP b μ (jX μ x) (jX μ x')) → ∃ (EE : Hs) (Mult : D.what₂.Tup → ℕ → Hs) (multZero : ∀ μ, (Mult μ 0).T ≃ₗᵢ[ℂ] EE.T) (multTop : ∀ μ, (Mult μ D.R.m).T ≃ₗᵢ[ℂ] (Top μ).T) (io : ∀ μ j, (Mult μ (j + 1)).T →ₗ[ℂ] (Mult μ j).T) (jE : EE.T →ₗ[ℂ] C.Amb 0) (jM : ∀ μ j, (Mult μ j).T →ₗ[ℂ] C.Amb j), Function.Injective jE ∧ LinearMap.range jE = C.EEc b ∧ (∀ x x', ⟪x, x'⟫_ℂ = C.ipE b (jE x) (jE x')) ∧ (∀ μ, U μ → ∀ j, 1 ≤ j → j ≤ D.R.m - 1 → Function.Injective (jM μ j) ∧ LinearMap.range (jM μ j) = C.CCP b μ j ∧ ∀ x x', ⟪x, x'⟫_ℂ = C.ipP b μ j (jM μ j x) (jM μ j x')) ∧ (∀ μ, U μ → ∀ x (v : (Mult μ 1).T) (h : jM μ 1 v ∈ C.CC b μ 1), ⟪x, multZero μ (io μ 0 v)⟫_ℂ = C.ipE b (jE x) (C.ioC b μ 0 ⟨jM μ 1 v, h⟩ : C.Amb 0)) ∧ (∀ μ, U μ → ∀ j, 1 ≤ j → j + 1 ≤ D.R.m - 1 → ∀ x (v : (Mult μ (j + 1)).T) (h : jM μ (j + 1) v ∈ C.CC b μ (j + 1)), ⟪x, io μ j v⟫_ℂ = C.ipP b μ j (jM μ j x) (C.ioC b μ j ⟨jM μ (j + 1) v, h⟩ : C.Amb j)) ∧ (∀ μ, U μ → ∀ x (v : (Mult μ D.R.m).T) (v' : (Mult μ (D.R.m - 1 + 1)).T), HEq v' v → ∀ h : jX μ (multTop μ v) ∈ C.CCX b μ, ⟪x, io μ (D.R.m - 1) v'⟫_ℂ = C.ipP b μ (D.R.m - 1) (jM μ (D.R.m - 1) x) (C.ioX b μ ⟨jX μ (multTop μ v), h⟩ : C.Amb (D.R.m - 1))) ∧ (∀ μ, ¬ U μ → ∀ j, io μ j = 0) := by
  classical
  intro D C b U Top jX hm hE hle hE0 hX
  obtain ⟨EE, jE, hEi, hEr, hEip⟩ := hp_model hE
  have jE_mem : ∀ μ x, jE x ∈ C.CC b μ 0 := fun μ x =>
    (hle μ).1 (by rw [← hEr]; exact LinearMap.mem_range_self jE x)
  have hLo : ∀ (μ : D.what₂.Tup) (j : ℕ), ∃ H : Hs, ∃ jj : H.T →ₗ[ℂ] C.Amb j, j ≤ D.R.m - 1 →
      Function.Injective jj ∧ LinearMap.range jj = C.CCP b μ j ∧
        ∀ x x', ⟪x, x'⟫_ℂ = C.ipP b μ j (jj x) (jj x') := by
    intro μ j
    by_cases hj : j ≤ D.R.m - 1
    · obtain ⟨h1, h2⟩ := (hle μ).2.2.2 j hj
      obtain ⟨H, jj, a1, a2, a3⟩ := hp_model (hp_restrict h2 h1)
      exact ⟨H, jj, fun _ => ⟨a1, a2, a3⟩⟩
    · exact ⟨EE, 0, fun h => absurd h hj⟩
  choose Lo jL hL using hLo
  let Mult : D.what₂.Tup → ℕ → Hs := fun μ => chSel D.R.m EE (Top μ) (Lo μ)
  let jM : ∀ μ j, (Mult μ j).T →ₗ[ℂ] C.Amb j := fun μ j =>
    if h : 1 ≤ j ∧ j ≤ D.R.m - 1 then
      (jL μ j).comp (heqv (chSel_mid (m := D.R.m) (A := EE) (B := Top μ) (L := Lo μ)
        (by have := h.1; omega) (by have := h.2; omega))).toLinearEquiv.toLinearMap
    else 0
  have jM_mem : ∀ μ j x, jM μ j x ∈ C.CC b μ j := by
    intro μ j x
    dsimp only [jM]
    split_ifs with h
    · rw [LinearMap.comp_apply]
      refine ((hle μ).2.2.2 j h.2).1 ?_
      rw [← (hL μ j h.2).2.1]
      exact LinearMap.mem_range_self _ _
    · rw [LinearMap.zero_apply]; exact zero_mem _
  have hr0 : ∀ μ, ∃ r : C.CC b μ 0 →ₗ[ℂ] EE.T, ∀ x (w : C.CC b μ 0), ⟪x, r w⟫_ℂ = C.ipE b (jE x) w :=
    fun μ => hp_riesz (hE0 μ) jE (jE_mem μ)
  choose r0 hr0 using hr0
  have hR : ∀ μ j, ∃ r : C.CC b μ j →ₗ[ℂ] (Mult μ j).T, j ≤ D.R.m - 1 →
      ∀ x (w : C.CC b μ j), ⟪x, r w⟫_ℂ = C.ipP b μ j (jM μ j x) w := by
    intro μ j
    by_cases hj : j ≤ D.R.m - 1
    · obtain ⟨r, hr⟩ := hp_riesz ((hle μ).2.2.2 j hj).2 (jM μ j) (jM_mem μ j)
      exact ⟨r, fun _ => hr⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose R hR using hR
  have memX : ∀ μ, U μ → ∀ y, jX μ y ∈ C.CCX b μ := fun μ hU y =>
    (hle μ).2.1 (by rw [← (hX μ hU).2.1]; exact LinearMap.mem_range_self (jX μ) y)
  let io : ∀ μ j, (Mult μ (j + 1)).T →ₗ[ℂ] (Mult μ j).T := fun μ j =>
    if hU : U μ then
      if h0 : j = 0 then
        (heqv (show Mult μ j = EE by rw [h0]; exact chSel_zero)).symm.toLinearEquiv.toLinearMap ∘ₗ r0 μ ∘ₗ
          C.ioC b μ 0 ∘ₗ (jM μ 1 ∘ₗ (heqv (show Mult μ (j + 1) = Mult μ 1 by rw [h0])).toLinearEquiv.toLinearMap).codRestrict
            (C.CC b μ 1) (fun y => jM_mem μ 1 _)
      else if hT : j + 1 = D.R.m then
        (heqv (show Mult μ (D.R.m - 1) = Mult μ j by rw [show D.R.m - 1 = j by omega])).toLinearEquiv.toLinearMap ∘ₗ
          R μ (D.R.m - 1) ∘ₗ C.ioX b μ ∘ₗ
          (jX μ ∘ₗ (heqv (show Mult μ (j + 1) = Top μ by rw [hT]; exact chSel_top (by omega))).toLinearEquiv.toLinearMap).codRestrict
            (C.CCX b μ) (fun y => memX μ hU _)
      else
        R μ j ∘ₗ C.ioC b μ j ∘ₗ (jM μ (j + 1)).codRestrict (C.CC b μ (j + 1)) (jM_mem μ (j + 1))
    else 0
  refine ⟨EE, Mult, fun μ => heqv (chSel_zero (m := D.R.m) (A := EE) (B := Top μ) (L := Lo μ)),
    fun μ => heqv (chSel_top (m := D.R.m) (A := EE) (B := Top μ) (L := Lo μ) (by omega)), io, jE, jM,
    hEi, hEr, hEip, ?_, ?_, ?_, ?_, ?_⟩
  · intro μ _ j h1 h2
    have hh : 1 ≤ j ∧ j ≤ D.R.m - 1 := ⟨h1, h2⟩
    obtain ⟨hi, hr, hip⟩ := hL μ j h2
    dsimp only [jM]
    rw [dif_pos hh]
    refine ⟨?_, ?_, ?_⟩
    · rw [LinearMap.coe_comp]; exact hi.comp (LinearEquiv.injective _)
    · rw [LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _), hr]
    · intro x x'
      rw [LinearMap.comp_apply, LinearMap.comp_apply, ← hip]
      exact (LinearIsometryEquiv.inner_map_map _ x x').symm
  · intro μ hU x v h
    dsimp only [io]
    rw [dif_pos hU, dif_pos rfl]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
      LinearIsometryEquiv.apply_symm_apply]
    exact hr0 μ x _
  · intro μ hU j h1 h2 x v h
    dsimp only [io]
    rw [dif_pos hU, dif_neg (by omega), dif_neg (by omega)]
    rw [LinearMap.comp_apply, hR μ j (by omega)]
    rfl
  · intro μ hU x v v' hv h
    dsimp only [io]
    rw [dif_pos hU, dif_neg (by omega), dif_pos (by omega)]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv]
    rw [heqv_self, hR μ _ le_rfl]
    refine congrArg (fun y => C.ipP b μ (D.R.m - 1) (jM μ (D.R.m - 1) x)
      ((C.ioX b μ y : C.CC b μ (D.R.m - 1)) : C.Amb (D.R.m - 1))) (Subtype.ext ?_)
    exact congrArg (jX μ) (heqv_heq _ _ v' v hv)
  · intro μ hU j
    dsimp only [io]
    rw [dif_neg hU]

end GlobalTheory.ChainHilb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalEmbeddingOverPlace
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocEmbExist

variable {E : Type} [Field E] [NumberField E]

theorem isIntegral_or_isIntegral_inv (w : HeightOneSpectrum (𝓞 E)) (x : GlobalTheory.LocDict.Kbar w) :
    IsIntegral (w.adicCompletionIntegers E) x ∨ IsIntegral (w.adicCompletionIntegers E) x⁻¹ := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact Or.inl isIntegral_zero
  let K := w.adicCompletion E
  let L : IntermediateField K (GlobalTheory.LocDict.Kbar w) := IntermediateField.adjoin K {x}
  have : FiniteDimensional K L :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  let y : L := ⟨x, IntermediateField.mem_adjoin_simple_self K x⟩
  have hy0 : y ≠ 0 := fun h => hx (congrArg Subtype.val h)
  let f : L →ₐ[w.adicCompletionIntegers E] GlobalTheory.LocDict.Kbar w := L.val.restrictScalars _
  have hf : Function.Injective f := L.val.injective
  have key : ∀ z : L, IsIntegral (w.adicCompletionIntegers E) (z : GlobalTheory.LocDict.Kbar w) ↔
      Valued.v (Algebra.norm K z) ≤ 1 := fun z => by
    rw [← GlobalTheory.CNorm.isIntegral_iff_valued_norm_le_one E w L z]
    exact isIntegral_algHom_iff f hf
  have hyx : ((y⁻¹ : L) : GlobalTheory.LocDict.Kbar w) = x⁻¹ := by simp [y]
  have hmul : Valued.v (Algebra.norm K y) * Valued.v (Algebra.norm K y⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ hy0, map_one, map_one]
  rcases le_total (Valued.v (Algebra.norm K y)) 1 with h | h
  · exact Or.inl ((key y).2 h)
  · right
    rw [← hyx]
    refine (key _).2 ?_
    calc Valued.v (Algebra.norm K y⁻¹) = 1 * Valued.v (Algebra.norm K y⁻¹) := (one_mul _).symm
      _ ≤ Valued.v (Algebra.norm K y) * Valued.v (Algebra.norm K y⁻¹) := mul_le_mul' h le_rfl
      _ = 1 := hmul

def intValRing (w : HeightOneSpectrum (𝓞 E)) : ValuationSubring (GlobalTheory.LocDict.Kbar w) where
  toSubring := (integralClosure (w.adicCompletionIntegers E) (GlobalTheory.LocDict.Kbar w)).toSubring
  mem_or_inv_mem' x := isIntegral_or_isIntegral_inv w x

theorem mem_intValRing {w : HeightOneSpectrum (𝓞 E)} (x : GlobalTheory.LocDict.Kbar w) :
    x ∈ intValRing w ↔ IsIntegral (w.adicCompletionIntegers E) x := Iff.rfl

theorem isIntegral_algebraMap_iff (w : HeightOneSpectrum (𝓞 E)) (e : E) :
    IsIntegral (w.adicCompletionIntegers E) (algebraMap E (GlobalTheory.LocDict.Kbar w) e) ↔
      w.valuation E e ≤ 1 := by
  let K := w.adicCompletion E
  have h1 : algebraMap E (GlobalTheory.LocDict.Kbar w) e = algebraMap K (GlobalTheory.LocDict.Kbar w) (algebraMap E K e) :=
    IsScalarTower.algebraMap_apply E K _ e
  let f : K →ₐ[w.adicCompletionIntegers E] GlobalTheory.LocDict.Kbar w :=
    (IsScalarTower.toAlgHom K K (GlobalTheory.LocDict.Kbar w)).restrictScalars _
  rw [h1, show algebraMap K (GlobalTheory.LocDict.Kbar w) (algebraMap E K e) = f (algebraMap E K e) from rfl,
    isIntegral_algHom_iff f f.toRingHom.injective, IsIntegrallyClosed.isIntegral_iff (K := K)]
  have hv : Valued.v (algebraMap E K e) = w.valuation E e :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w e
  constructor
  · rintro ⟨y, hy⟩
    have h := y.2
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h
    change Valued.v (y : K) ≤ 1 at h
    rw [show (y : K) = algebraMap E K e from hy, hv] at h
    exact h
  · intro h
    refine ⟨⟨algebraMap E K e, ?_⟩, rfl⟩
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hv]
    exact h

theorem valuation_lt_one_iff_of_mem_iff {Ω : Type} [Field Ω] [Algebra E Ω] (B : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (hB : ∀ e : E, algebraMap E Ω e ∈ B ↔ w.valuation E e ≤ 1) (e : E) :
    B.valuation (algebraMap E Ω e) < 1 ↔ w.valuation E e < 1 := by
  rcases eq_or_ne e 0 with rfl | he
  · simp
  have ha : algebraMap E Ω e ≠ 0 := (map_ne_zero _).2 he
  have h1 : B.valuation (algebraMap E Ω e) < 1 ↔ ¬ B.valuation (algebraMap E Ω e⁻¹) ≤ 1 := by
    rw [map_inv₀, map_inv₀, inv_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 ha)), not_le]
  have h2 : w.valuation E e < 1 ↔ ¬ w.valuation E e⁻¹ ≤ 1 := by
    rw [map_inv₀, inv_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 he)), not_le]
  rw [h1, h2, ValuationSubring.valuation_le_one_iff, hB]

end GlobalTheory.LocEmbExist

namespace GlobalTheory.LocDict

theorem exists_isLocEmb : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w), ∃ ι : Ω →ₐ[E] Kbar w, IsLocEmb A w ι := by
  intro E Ω _ _ _ _ _ A w h
  have : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  let ι₀ : Ω →ₐ[E] Kbar w := IsAlgClosed.lift
  let A₀ : ValuationSubring Ω := (GlobalTheory.LocEmbExist.intValRing w).comap ι₀.toRingHom
  have hA₀ : ∀ z, z ∈ A₀ ↔ IsIntegral (w.adicCompletionIntegers E) (ι₀ z) := fun _ => Iff.rfl
  have hE : ∀ e : E, algebraMap E Ω e ∈ A₀ ↔ w.valuation E e ≤ 1 := fun e => by
    rw [hA₀, ι₀.commutes]
    exact GlobalTheory.LocEmbExist.isIntegral_algebraMap_iff w e
  have hP : IsPlaceOver A₀ w := fun x => by
    rw [GlobalTheory.LocEmbExist.valuation_lt_one_iff_of_mem_iff A₀ w hE]
    exact w.valuation_lt_one_iff_mem (K := E) x
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver hP h
  refine ⟨ι₀.comp (σ.symm : Ω →ₐ[E] Ω), fun z => ?_⟩
  rw [← hσ, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, hA₀]
  rfl

end GlobalTheory.LocDict
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalHoweContractionCompactUnitary
section
open Formalism.MainNotions.S Matrix GlobalTheory.CompactHowe
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompactHowe.Contraction

open MvPolynomial ReciprocityTheory.PGsh

theorem mem_iff {k : ℕ} (g : Matrix (Fin k) (Fin k) ℂ) : g ∈ UJset (allPos k) ↔ gᴴ * g = 1 := by
  have h : Formalism.REAL.Jm (allPos k) = 1 := by simp [Formalism.REAL.Jm, allPos]
  show gᴴ * Formalism.REAL.Jm (allPos k) * g = Formalism.REAL.Jm (allPos k) ↔ _
  rw [h, Matrix.mul_one]

theorem map_star_map_star {k : ℕ} (g : Matrix (Fin k) (Fin k) ℂ) : (g.map star).map star = g := by
  ext i j; simp

theorem map_star_mem {k : ℕ} {g : Matrix (Fin k) (Fin k) ℂ} (hg : g ∈ UJset (allPos k)) :
    g.map star ∈ UJset (allPos k) := by
  rw [mem_iff] at hg ⊢
  ext i j
  have := congrArg star (congrFun (congrFun hg i) j)
  simp only [Matrix.mul_apply, star_sum, star_mul', Matrix.conjTranspose_apply, Matrix.map_apply] at this ⊢
  rw [this]
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem inv_transpose {k : ℕ} {g : Matrix (Fin k) (Fin k) ℂ} (hg : g ∈ UJset (allPos k)) :
    (g⁻¹)ᵀ = g.map star := by
  rw [Matrix.inv_eq_left_inv ((mem_iff g).1 hg)]
  ext i j; simp

theorem det_map_star {k : ℕ} (g : Matrix (Fin k) (Fin k) ℂ) : (g.map star).det = star g.det := by
  rw [← Matrix.det_conjTranspose, ← Matrix.det_transpose]
  rfl

theorem star_det {k : ℕ} {g : Matrix (Fin k) (Fin k) ℂ} (hg : g ∈ UJset (allPos k)) :
    star g.det = g.det⁻¹ := by
  have := congrArg Matrix.det ((mem_iff g).1 hg)
  rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at this
  exact eq_inv_of_mul_eq_one_left this

theorem conjTranspose_mem {k : ℕ} {g : Matrix (Fin k) (Fin k) ℂ} (hg : g ∈ UJset (allPos k)) :
    gᴴ ∈ UJset (allPos k) := by
  rw [mem_iff] at hg ⊢
  rw [Matrix.conjTranspose_conjTranspose]
  exact mul_eq_one_comm.1 hg

variable {N n : ℕ}

theorem fischer_swap (P Q : MvPolynomial (Fin N × Fin n) ℂ) :
    fischer (rename Prod.swap P) (rename Prod.swap Q) = fischer P Q := by
  classical
  have hinj : Function.Injective (Prod.swap : Fin N × Fin n → Fin n × Fin N) := Prod.swap_injective
  rw [fischer_eq_sum _ _ _ subset_rfl, fischer_eq_sum P Q _ subset_rfl,
    support_rename_of_injective hinj, Finset.sum_image
      (fun a _ b _ h => Finsupp.mapDomain_injective hinj h)]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [coeff_rename_mapDomain _ hinj, coeff_rename_mapDomain _ hinj]
  congr 1
  unfold fw
  rw [Finsupp.prod_mapDomain_index_inj hinj]

theorem subst2_row (h : Matrix (Fin N) (Fin N) ℂ) (P : MvPolynomial (Fin N × Fin n) ℂ) :
    subst2 h 1 P = rowSubst h P := by
  have key : subst2 h (1 : Matrix (Fin n) (Fin n) ℂ) = rowSubst h := by
    refine algHom_ext fun p => ?_
    rw [subst2_X, rowSubst_X]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_eq_single p.2]
    · simp
    · intro l _ hl; simp [Matrix.one_apply_ne hl]
    · simp
  rw [key]

theorem subst2_col (g : Matrix (Fin n) (Fin n) ℂ) (P : MvPolynomial (Fin N × Fin n) ℂ) :
    rename Prod.swap (subst2 1 g P) = rowSubst g (rename Prod.swap P) := by
  have key : (rename Prod.swap).comp (subst2 (1 : Matrix (Fin N) (Fin N) ℂ) g) =
      (rowSubst g).comp (rename Prod.swap) := by
    refine algHom_ext fun p => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, rename_X, subst2_X, rowSubst_X,
      Finset.sum_eq_single p.1]
    · simp
    · intro l _ hl; simp [Matrix.one_apply_ne hl]
    · simp
  exact congrArg (fun f => f P) key

theorem fischer_subst2 (h : Matrix (Fin N) (Fin N) ℂ) (g : Matrix (Fin n) (Fin n) ℂ)
    (P Q : MvPolynomial (Fin N × Fin n) ℂ) :
    fischer (subst2 h g P) Q = fischer P (subst2 hᴴ gᴴ Q) := by
  have h1 : subst2 h g P = subst2 h 1 (subst2 1 g P) := by rw [subst2_mul]; simp
  have h2 : subst2 hᴴ gᴴ Q = subst2 1 gᴴ (subst2 hᴴ 1 Q) := by rw [subst2_mul]; simp
  rw [h1, h2, subst2_row, fischer_rowSubst, ← subst2_row, ← fischer_swap, subst2_col,
    fischer_rowSubst, ← subst2_col, fischer_swap]

theorem fischer_subst2_unitary {h : Matrix (Fin N) (Fin N) ℂ} {g : Matrix (Fin n) (Fin n) ℂ}
    (hh : h ∈ UJset (allPos N)) (hg : g ∈ UJset (allPos n)) (P Q : MvPolynomial (Fin N × Fin n) ℂ) :
    fischer (subst2 h g P) (subst2 h g Q) = fischer P Q := by
  rw [fischer_subst2, subst2_mul, (mem_iff h).1 hh, (mem_iff g).1 hg, subst2_one]

theorem exists_contraction {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] {H' E : Type} [AddCommGroup H'] [Module ℂ H'] [AddCommGroup E] [Module ℂ E]
    (J : H' →ₛₗ[starRingEnd ℂ] E) (Ψ : E →ₗ[ℂ] H →ₗ[ℂ] MvPolynomial (Fin N × Fin n) ℂ) :
    ∃ I : MvPolynomial (Fin N × Fin n) ℂ →ₗ[ℂ] H' →ₗ[ℂ] H,
      ∀ P v u, inner ℂ u (I P v) = fischer P (Ψ (J v) u) := by
  let b := stdOrthonormalBasis ℂ H
  refine ⟨LinearMap.mk₂ ℂ (fun P v => ∑ i, fischer P (Ψ (J v) (b i)) • b i) ?_ ?_ ?_ ?_, ?_⟩
  · intro P P' v
    simp only [fischer_add_left, add_smul, Finset.sum_add_distrib]
  · intro c P v
    simp only [fischer_smul_left, Finset.smul_sum, smul_smul]
  · intro P v v'
    simp only [map_add, LinearMap.add_apply, fischer_add_right, add_smul, Finset.sum_add_distrib]
  · intro c P v
    simp only [LinearMap.map_smulₛₗ, map_smul, LinearMap.smul_apply, fischer_smul_right, Finset.smul_sum,
      smul_smul, Complex.conj_conj, RingHom.id_apply]
  · intro P v u
    conv_rhs => rw [← b.sum_repr' u]
    simp only [LinearMap.mk₂_apply, inner_sum, inner_smul_right, map_sum, map_smul, fischer_sum_right,
      fischer_smul_right, inner_conj_symm]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _

end GlobalTheory.CompactHowe.Contraction

namespace GlobalTheory.CompactHowe

open Contraction ReciprocityTheory.PGsh

theorem exists_local_contraction : ∀ (N n : ℕ) (hn : n ≤ N) (ν : Fin N → ℕ) (x₁ x₃ : ℤ) (Λ : Fin n → ℝ) (Λ' : Fin N → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [FiniteDimensional ℂ H'] (σ' : Matrix (Fin N) (Fin N) ℂ → (H' →L[ℂ] H')), Antitone ν → (∀ b : Fin N, n ≤ (b : ℕ) → ν b = 0) → (∀ a, Λ a = (x₃ : ℝ) - ν (Fin.castLE hn (Fin.rev a))) → (∀ b, Λ' b = -(x₁ : ℝ) - ν (Fin.rev b)) → IsURepOn (UJset (allPos n)) σ → IsKTypeOf (allPos n) σ Λ ⊤ → IsURepOn (UJset (allPos N)) σ' → IsKTypeOf (allPos N) σ' Λ' ⊤ → ∃ I : MvPolynomial (Fin N × Fin n) ℂ →ₗ[ℂ] H' →ₗ[ℂ] H, I ≠ 0 ∧ ∀ h ∈ UJset (allPos N), ∀ g ∈ UJset (allPos n), ∀ P v, I ((h.det ^ x₁ * g.det ^ x₃) • subst2 h (g⁻¹)ᵀ P) (σ' h v) = σ g (I P v) := by
  intro N n hn ν x₁ x₃ Λ Λ' H _ _ _ σ H' _ _ _ σ' hν hν0 hΛ hΛ' hσ hK hσ' hK'
  obtain ⟨hτ, hτK⟩ := GlobalTheory.T.detTwistedConjugate_isKTypeOf_reversed n Λ x₃ H σ hσ hK
  obtain ⟨hτ', hτK'⟩ := GlobalTheory.T.detTwistedConjugate_isKTypeOf_reversed N Λ' (-x₁) H' σ' hσ' hK'
  have e1 : (fun a => ((x₃ : ℤ) : ℝ) - Λ (Fin.rev a)) = fun a => (ν (Fin.castLE hn a) : ℝ) := by
    funext a; rw [hΛ, Fin.rev_rev]; ring
  have e2 : (fun b => ((-x₁ : ℤ) : ℝ) - Λ' (Fin.rev b)) = fun b => (ν b : ℝ) := by
    funext b; rw [hΛ', Fin.rev_rev]; push_cast; ring
  rw [e1] at hτK
  rw [e2] at hτK'
  obtain ⟨E, i1, i2, i3, π, J, hJ, hπ, hπK, hπJ⟩ := GlobalTheory.T.exists_conjugate_unitaryKType_sameWeight N _ H' _ hτ' hτK'
  obtain ⟨Ψ, hΨ0, hΨ⟩ := GlobalTheory.T.exists_tensor_types_intertwiner_matrix_polynomials N n hn ν H _ E π hν hν0 hτ hτK hπ hπK
  obtain ⟨I, hI⟩ := exists_contraction J Ψ
  refine ⟨I, fun h0 => hΨ0 ?_, fun h hh g hg P v => ?_⟩
  · ext1 w
    ext1 u
    obtain ⟨v, rfl⟩ := hJ.2 w
    by_contra hne
    apply fischer_self_ne_zero _ hne
    rw [← hI, h0]
    simp
  · refine ext_inner_left ℂ fun w => ?_
    obtain ⟨u, rfl⟩ : ∃ u, σ g u = w := by
      refine ⟨σ gᴴ w, ?_⟩
      have := hσ.1.2 g hg _ (conjTranspose_mem hg)
      rw [mul_eq_one_comm.1 ((mem_iff g).1 hg), hσ.1.1] at this
      simpa using (congrArg (fun f => f w) this).symm
    have hiso : inner ℂ (σ g u) (σ g (I P v)) = inner ℂ u (I P v) :=
      (LinearIsometry.mk (σ g : H →ₗ[ℂ] H) (hσ.2.1 g hg)).inner_map_map u (I P v)
    rw [hiso, hI, hI, inv_transpose hg, fischer_smul_left,
      ← fischer_subst2_unitary hh (map_star_mem hg) P, ← hΨ h hh _ (map_star_mem hg), hπJ]
    simp only [map_star_map_star, det_map_star, ContinuousLinearMap.smul_apply, LinearMap.map_smulₛₗ,
      map_smul, LinearMap.smul_apply, fischer_smul_right, RingHom.id_apply, Complex.conj_conj,
      map_zpow₀, starRingEnd_apply, star_star]
    rw [star_det hh, _root_.inv_zpow', neg_neg]
    ring

end GlobalTheory.CompactHowe

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPointCarriesFrameFlagsOwnFrameStatement
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pointCarriesFrameFlags_own_frame : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y : Var F) (Eb : Fr (ratOf X) m 0) (S : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Reps Eb S φ f → ∀ (K : Type) [Field K] (w : Sp K ⟶ Y.X), ∃ A ∈ Eb.S ((w ≫ f) (IsLocalRing.closedPoint K)), ∃ h : Mat m K, Par 0 ⊤ h ∧ Bears S φ A h w := by
  first | exact @GlobalTheory.FlagBundle.bears_self | exact GlobalTheory.FlagBundle.bears_self | (intros; apply GlobalTheory.FlagBundle.bears_self <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowsPrescribedUnitaryFormsStandInsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df
attribute [local instance] GlobalTheory.Mem.Col2.starE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rows_prescribedUnitaryForms_standIns : ∀ (B : Base) (C : Cols B) (n : C.Tup → ℕ) (e0 : ∀ u, (C.mem u).P.Mt ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (n C.mu0))) (eT : ∀ u a, (C.PTw u a).Mt ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (n a))) (L : ∀ a, Rows.OLat B.O (B.embLL.comp B.OtoLL) (EuclideanSpace ℂ (Fin (n a)))) (mt : B.places.Pl → C.Tup), (∀ w, mt (B.places.conj w) = mt w) → SpectralModel.ColsPos C → ∃ (W : RowsRest B C) (g : ∀ a, EuclideanSpace ℂ (Fin (n a)) ≃ₗᵢ[ℂ] W.Amb a), StandIn W ∧ (∀ w, W.muAt w = C.mu0) ∧ (∀ w, W.muTw w = mt w) ∧ (∀ u F, W.eMt0 u F = g C.mu0 (e0 u F)) ∧ (∀ u a F, W.eMtTw u a F = g a (eT u a F)) ∧ (∀ a y, g a y ∈ (W.Mtilde a).carrier ↔ y ∈ (L a).carrier) ∧ (∀ a y, g a y ∈ (W.Mtilde a).gen ↔ y ∈ (L a).gen) ∧ (∀ a, W.eOp a = LinearMap.id) ∧ ∀ u a, W.ze u a = 1 := by
  first | exact @GlobalTheory.Mem.DfGen.exists_rowsRest_std | exact GlobalTheory.Mem.DfGen.exists_rowsRest_std | (intros; apply GlobalTheory.Mem.DfGen.exists_rowsRest_std <;> assumption)
end

