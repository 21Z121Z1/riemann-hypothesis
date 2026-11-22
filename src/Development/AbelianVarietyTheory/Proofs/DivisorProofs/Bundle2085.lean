import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0018
import Development.AbelianVarietyTheory.Definitions.UpperBounds.FreeBallIffOfDimXEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorsEqAtRealPlacesSameExponents
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1765
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1777
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1815
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1983
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2067
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2014

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelCuspFormsDirectSumComponents
section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShareOn.Decomp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {U C : Type} [Group U] [MulAction U C]
  [DecidableEq C]

def onComp (M : TwoLevels E r U C) (c : C) : Submodule ℂ (C → M.dom → ℂ) where
  carrier := {v | ∀ c', c' ≠ c → v c' = 0}
  add_mem' := by
    intro a b ha hb c' hc
    simp [ha c' hc, hb c' hc]
  zero_mem' := by
    intro c' _
    rfl
  smul_mem' := by
    intro t a ha c' hc
    simp [ha c' hc]

def cut (M : TwoLevels E r U C) (c : C) : (C → M.dom → ℂ) →ₗ[ℂ] (C → M.dom → ℂ) where
  toFun v := fun c' => if c' = c then v c' else 0
  map_add' := by
    intro a b
    funext c' x
    by_cases h : c' = c <;> simp [h]
  map_smul' := by
    intro t a
    funext c' x
    by_cases h : c' = c <;> simp [h]

theorem cut_apply (M : TwoLevels E r U C) (c : C) (v : C → M.dom → ℂ) (c' : C) :
    cut M c v c' = if c' = c then v c' else 0 := rfl

theorem cutF_mem_SS (M : TwoLevels E r U C) (la : Wt M.Ψ r) (c : C) {F : C → Frame M.Ψ r → ℂ}
    (hF : F ∈ M.SS la) : (fun c' => if c' = c then F c' else 0) ∈ M.SS la := by
  intro c'
  by_cases h : c' = c
  · simpa [h] using hF c'
  · simp only [h, if_false]
    exact ⟨BoundedSectionAlgebra.bdd_zero _ _, fun ξ _ x _ => BoundedSectionAlgebra.fj_zero _ _ ξ x 0⟩

theorem cut_mem_cusp (M : TwoLevels E r U C) (la : Wt M.Ψ r) (c : C) {v : C → M.dom → ℂ}
    (hv : v ∈ M.cusp la) : cut M c v ∈ M.cusp la := by
  have : (M.cusp la).map (cut M c) ≤ M.cusp la := by
    unfold TwoLevels.cusp
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨F, hF, rfl⟩, rfl⟩
    refine Submodule.subset_span ⟨_, cutF_mem_SS M la c hF, ?_⟩
    funext c' x
    simp [TwoLevels.res, cut_apply]
    split_ifs <;> rfl
  exact this ⟨v, hv, rfl⟩

theorem mem_span_of_onComp (M : TwoLevels E r U C) (la : Wt M.Ψ r) (c : C) {v : C → M.dom → ℂ}
    (hv : v ∈ M.cusp la) (hc : v ∈ onComp M c) :
    v ∈ Submodule.span ℂ (M.res '' {F | F ∈ M.SS la ∧ ∀ c', c' ≠ c → F c' = 0}) := by
  have hcut : cut M c v = v := by
    funext c' x
    by_cases h : c' = c
    · simp [cut_apply, h]
    · simp [cut_apply, h, hc c' h]
  rw [← hcut]
  have : (M.cusp la).map (cut M c) ≤
      Submodule.span ℂ (M.res '' {F | F ∈ M.SS la ∧ ∀ c', c' ≠ c → F c' = 0}) := by
    unfold TwoLevels.cusp
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨F, hF, rfl⟩, rfl⟩
    refine Submodule.subset_span ⟨_, ⟨cutF_mem_SS M la c hF, fun c' hc' => by simp [hc']⟩, ?_⟩
    funext c' x
    simp [TwoLevels.res, cut_apply]
    split_ifs <;> rfl
  exact this ⟨v, hv, rfl⟩

end GlobalTheory.ShareOn.Decomp

end

namespace GlobalTheory.ShareOn.Decomp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {U C : Type} [Group U] [MulAction U C]
  [DecidableEq C]

theorem pullRep_onComp (M : TwoLevels E r U C) (la : Wt M.Ψ r) (ρ : Representation ℂ U (M.cusp la))
    (hρ : IsPullRep M la ρ) (g : U) (c : C) (w : M.cusp la) (hw : (w : C → M.dom → ℂ) ∈ onComp M c) :
    ((ρ g⁻¹ w : M.cusp la) : C → M.dom → ℂ) ∈ onComp M (g⁻¹ • c) := by
  obtain ⟨a, ha⟩ := hρ
  obtain ⟨w, hwc⟩ := w
  have hs := mem_span_of_onComp M la c hwc hw
  clear hw
  revert hwc
  suffices H : ∀ h' : w ∈ M.cusp la, ((ρ g⁻¹ ⟨w, h'⟩ : M.cusp la) : C → M.dom → ℂ) ∈ onComp M (g⁻¹ • c) from fun h' => H h'
  induction hs using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨F, ⟨hF, hFc⟩, rfl⟩ := hy
    intro h' c' hc'
    funext x
    have hgc : g • c' ≠ c := fun h => hc' (eq_inv_smul_iff.2 h)
    have := ha g F hF c' x
    rw [this]
    simp [TwoLevels.pull, hFc _ hgc]
  | zero =>
    intro h'
    have : (⟨0, h'⟩ : M.cusp la) = 0 := rfl
    rw [this, map_zero]
    exact (onComp M (g⁻¹ • c)).zero_mem
  | add x y hx hy ihx ihy =>
    intro h'
    have hx' : x ∈ M.cusp la := (Submodule.span_le.2 (by
      rintro _ ⟨F, ⟨hF, -⟩, rfl⟩; exact Submodule.subset_span ⟨F, hF, rfl⟩)) hx
    have hy' : y ∈ M.cusp la := (Submodule.span_le.2 (by
      rintro _ ⟨F, ⟨hF, -⟩, rfl⟩; exact Submodule.subset_span ⟨F, hF, rfl⟩)) hy
    have : (⟨x + y, h'⟩ : M.cusp la) = ⟨x, hx'⟩ + ⟨y, hy'⟩ := rfl
    rw [this, map_add, Submodule.coe_add]
    exact (onComp M (g⁻¹ • c)).add_mem (ihx hx') (ihy hy')
  | smul t x hx ihx =>
    intro h'
    have hx' : x ∈ M.cusp la := (Submodule.span_le.2 (by
      rintro _ ⟨F, ⟨hF, -⟩, rfl⟩; exact Submodule.subset_span ⟨F, hF, rfl⟩)) hx
    have : (⟨t • x, h'⟩ : M.cusp la) = t • ⟨x, hx'⟩ := rfl
    rw [this, map_smul, Submodule.coe_smul]
    exact (onComp M (g⁻¹ • c)).smul_mem t (ihx hx')

end GlobalTheory.ShareOn.Decomp

open GlobalTheory.ShareOn.Decomp in

theorem GlobalTheory.ShareOn.cusp_decomp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [Finite C]
    [DecidableEq C] [MulAction U C] (M : TwoLevels E r U C) (ka : Wt M.Ψ r) (ρ : Representation ℂ U (M.cusp ka)),
    IsPullRep M ka ρ → ∃ A : C → Submodule ℂ (M.cusp ka), DirectSum.IsInternal A ∧
      ∀ (h : U) (c : C), ∀ v ∈ A c, ρ h v ∈ A (h • c) := by
  intro E _ _ _ r U C _ _ _ _ M ka ρ hρ
  have : Fintype C := Fintype.ofFinite C
  refine ⟨fun c => (onComp M c).comap (M.cusp ka).subtype, ?_, ?_⟩
  · apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    · rw [iSupIndep_def]
      intro i
      rw [Submodule.disjoint_def]
      intro x hx hx2
      have hle : (⨆ j, ⨆ (_ : j ≠ i), (onComp M j).comap (M.cusp ka).subtype) ≤
          LinearMap.ker ((LinearMap.proj i : (C → M.dom → ℂ) →ₗ[ℂ] (M.dom → ℂ)) ∘ₗ (M.cusp ka).subtype) := by
        refine iSup₂_le fun j hj => ?_
        intro y hy
        simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj,
          Function.eval, Submodule.coe_subtype]
        exact hy i (Ne.symm hj)
      have h0 := hle hx2
      simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj,
          Function.eval, Submodule.coe_subtype] at h0
      apply Subtype.ext
      funext c'
      by_cases h : c' = i
      · subst h; simpa using h0
      · simpa using hx c' h
    · rw [eq_top_iff]
      rintro ⟨v, hv⟩ -
      have hsum : (⟨v, hv⟩ : M.cusp ka) = ∑ c, ⟨GlobalTheory.ShareOn.Decomp.cut M c v, cut_mem_cusp M ka c hv⟩ := by
        apply Subtype.ext
        rw [Submodule.coe_sum]
        funext c' x
        simp only [Finset.sum_apply, GlobalTheory.ShareOn.Decomp.cut_apply]
        have hh : ∀ c, (if c' = c then v c' else 0) x = if c' = c then v c' x else 0 := fun c => by
          split_ifs <;> rfl
        simp only [hh]
        rw [Finset.sum_ite_eq]
        simp
      rw [hsum]
      refine Submodule.sum_mem_iSup fun c => ?_
      intro c' hc'
      simp [GlobalTheory.ShareOn.Decomp.cut_apply, hc']
  · intro h c v hv
    have := pullRep_onComp M ka ρ hρ h⁻¹ c v hv
    simp only [inv_inv] at this
    exact this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryMatrixMajorantOperatorNormLeDefinite
section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

namespace GlobalTheory.DefiniteOpNorm

theorem span_colP {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (hp : X.p0 = r) (x : Frame X.Ψ r) (τ : X.Ψ) (A : Matrix (Fin r) (Fin r) ℂ)
    (hA : (A * mat x τ).det ≠ 0) (w : Fin r → ℂ) :
    ∃ K : Fin X.p0 → ℂ, w = ∑ a, K a • Matrix.mulVec A (X.colP x τ a) := by
  classical
  set M := A * mat x τ with hM
  set c := M⁻¹.mulVec w with hc
  have hw : w = M.mulVec c := by
    rw [hc, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hA), Matrix.one_mulVec]
  refine ⟨fun a => c (Fin.castLE X.p0_le a), ?_⟩
  have hsum : ∀ f : Fin r → Fin r → ℂ,
      ∑ a : Fin X.p0, f (Fin.castLE X.p0_le a) = ∑ j : Fin r, f j := by
    intro f
    exact Fintype.sum_equiv (finCongr hp) _ _ (fun a => by congr 1)
  show w = ∑ a : Fin X.p0, (fun j => c j • A.mulVec (ReciprocityTheory.ChartRestriction.G.FD.col (mat x τ) j)) (Fin.castLE X.p0_le a)
  rw [hsum (fun j => c j • A.mulVec (ReciprocityTheory.ChartRestriction.G.FD.col (mat x τ) j))]
  conv_lhs => rw [hw]
  funext k
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, ReciprocityTheory.ChartRestriction.G.FD.col, hM, Matrix.mulVec, dotProduct,
    Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem opNormLe_definite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r),
    (X.p0 = 0 ∨ X.p0 = r) → ∀ x ∈ X.dom, ∀ β : GL (Fin r) E,
    (∀ v w, herm X.Gm (Matrix.mulVec (β : Matrix (Fin r) (Fin r) E) v)
      (Matrix.mulVec (β : Matrix (Fin r) (Fin r) E) w) = herm X.Gm v w) →
    ∀ τ : X.Ψ, GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.OpNormLe X x τ (β : Matrix (Fin r) (Fin r) E)
      (Real.exp (1 / (3 * (r : ℝ)))) := by
  intro E _ _ _ r X hp x hx β hβ τ u
  set g : Matrix (Fin r) (Fin r) ℂ := (β : Matrix (Fin r) (Fin r) E).map τ.1 with hg
  set g' : Matrix (Fin r) (Fin r) ℂ := ((β⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 with hg'
  have hgg : g * g' = 1 := by
    rw [hg, hg', ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    exact Matrix.map_one τ.1 τ.1.map_zero τ.1.map_one
  have hg'g : g' * g = 1 := by
    rw [hg, hg', ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    exact Matrix.map_one τ.1 τ.1.map_zero τ.1.map_one
  have hdetg : g.det ≠ 0 := by
    intro h
    have := congrArg Matrix.det hgg
    rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have hdetx : (mat x τ).det ≠ 0 := (hx τ).1
  have hiso : ∀ u v, hermC τ.1 X.Gm (Matrix.mulVec g u) (Matrix.mulVec g v) = hermC τ.1 X.Gm u v :=
    GlobalTheory.MajInv.hermC_stab X hβ τ.1
  have H1 : ∀ c, ∃ K : Fin X.p0 → ℂ, Matrix.mulVec g (X.colP x τ c) = ∑ a, K a • X.colP x τ a := by
    intro c
    rcases hp with hp | hp
    · exact absurd c.isLt (by omega)
    · obtain ⟨K, hK⟩ := span_colP X hp x τ 1 (by rw [Matrix.one_mul]; exact hdetx)
        (Matrix.mulVec g (X.colP x τ c))
      exact ⟨K, by simpa only [Matrix.one_mulVec] using hK⟩
  have H2 : ∀ a, ∃ L : Fin X.p0 → ℂ, X.colP x τ a = ∑ c, L c • Matrix.mulVec g (X.colP x τ c) := by
    intro a
    rcases hp with hp | hp
    · exact absurd a.isLt (by omega)
    · exact span_colP X hp x τ g (by rw [Matrix.det_mul]; exact mul_ne_zero hdetg hdetx) _
  have key : X.maj x τ (Matrix.mulVec g u) = X.maj x τ u := by
    have h := ReciprocityTheory.ChartRestriction.G.FD.MajorantConjugateTransfer.maj_transfer X hx hx τ g g'
      (fun w => by rw [Matrix.mulVec_mulVec, hgg, Matrix.one_mulVec]) hiso H1 H2 (Matrix.mulVec g u)
    rwa [Matrix.mulVec_mulVec, hg'g, Matrix.one_mulVec] at h
  rw [key]
  have h0 := ReciprocityTheory.ChartRestriction.G.FD.MajorantConjugateTransfer.maj_nonneg X hx τ u
  have h1 : (1 : ℝ) ≤ Real.exp (1 / (3 * (r : ℝ))) ^ 2 :=
    one_le_pow₀ (Real.one_le_exp (by positivity))
  nlinarith

end GlobalTheory.DefiniteOpNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UpperLevelIsUnitaryStabiliserBothLattices
section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

namespace GlobalTheory.UpperStab

theorem upper_isUStab (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C]
    (M : TwoLevels E r U C) (c : C) :
    ∀ β ∈ M.upper c, IsUStab (M.comp c).Gm (M.comp c).L' β ∧ IsUStab (M.comp c).Gm (M.comp c).Λ β := by
  rintro β ⟨u, hu, γ, hγ, rfl⟩
  have hs := (M.comp c).Γ_stab γ hγ
  have hh : ∀ x y, herm (M.comp c).Gm (Matrix.mulVec ((γ * M.tr u c : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) x)
      (Matrix.mulVec ((γ * M.tr u c : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) y) = herm (M.comp c).Gm x y := by
    intro x y
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hs.1, M.comp_Gm c, M.tr_herm]
  refine ⟨⟨hh, fun v => ?_⟩, ⟨hh, fun v => ?_⟩⟩
  · have h1 := M.tr_L' u c v
    rw [hu] at h1
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, h1]
    exact M.Γ_L' c γ hγ _
  · have h1 := M.tr_Λ u c v
    rw [hu] at h1
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, h1]
    exact hs.2 _

end GlobalTheory.UpperStab
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorsEqAtRealPlacesSameExponentsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilOperators_eq_at_realPlaces_same_exponents : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xa Xb : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) oa oa' ob ob',
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B Γ Xa oa oa' → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B Γ Xb ob ob' →
    (∀ g h, g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ Γ.V (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) → h ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ Γ.W (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) →
      ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')), oa (g, h) Φ = ob (g, h) Φ) ∧
    (∀ g h, g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ Γ.V' (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) → h ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ Γ.W (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) →
      ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a' × Fin (a + a')), oa' (g, h) Φ = ob' (g, h) Φ) := by
  first | exact @GlobalTheory.ArchWeil.weil_eq_at_real_places | exact GlobalTheory.ArchWeil.weil_eq_at_real_places | (intros; apply GlobalTheory.ArchWeil.weil_eq_at_real_places <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilTransportArchimedeanSliceSobolevBounds
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

open MeasureTheory

namespace GlobalTheory.WeilL2Words

section Core

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem schA_decomp {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ GlobalTheory.WeilM.schA F κ) :
    ∃ (n : ℕ) (f : Fin n → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : Fin n → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ),
      (∀ i, g i ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) ∧ Φ = ∑ i, GlobalTheory.WeilM.pureA F (f i) (g i) := by
  rw [GlobalTheory.WeilM.schA, Submodule.mem_span_set'] at hΦ
  obtain ⟨n, c, s, rfl⟩ := hΦ
  choose f g hg hfg using fun i => (s i).2
  refine ⟨n, fun i => c i • f i, g, hg, Finset.sum_congr rfl fun i _ => ?_⟩
  rw [hfg i]
  ext a
  simp [GlobalTheory.WeilM.pureA, mul_assoc]

theorem list_sum_ne_top {l : List ENNReal} (h : ∀ a ∈ l, a ≠ ⊤) : l.sum ≠ ⊤ := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.sum_cons]
    exact ENNReal.add_ne_top.2 ⟨h a (by simp), ih fun b hb => h b (by simp [hb])⟩

variable [Invertible (2 : AdeleRing (𝓞 F) F)] {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ}

theorem dS_mem (hψ : IsStdInf F ψ) (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ}
    (hΦ : Φ ∈ GlobalTheory.WeilM.schA F κ) : dS F ψ h Φ ∈ GlobalTheory.WeilM.schA F κ := by
  obtain ⟨n, f, g, hg, rfl⟩ := schA_decomp hΦ
  obtain ⟨f', hf'⟩ := GlobalTheory.T.archDerivative_keeps_sums_fixed_finite_parts F κ ψ hψ n g f h
  rw [hf']
  exact Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨f' i, g i, hg i, rfl⟩

theorem word_mem (hψ : IsStdInf F ψ) : ∀ (w : List ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))) {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ},
    Φ ∈ GlobalTheory.WeilM.schA F κ → word F ψ w Φ ∈ GlobalTheory.WeilM.schA F κ
  | [], _, hΦ => hΦ
  | h :: w, _, hΦ => by
    rw [word_cons]
    exact dS_mem hψ h (word_mem hψ w hΦ)

theorem word_sum (hψ : IsStdInf F ψ) {m : ℕ} (g : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    ∀ (w : List ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))) (f : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ), ∃ f' : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      word F ψ w (∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) = ∑ i, GlobalTheory.WeilM.pureA F (f' i) (g i)
  | [], f => ⟨f, rfl⟩
  | h :: w, f => by
    obtain ⟨f1, e1⟩ := word_sum hψ g w f
    obtain ⟨f2, e2⟩ := GlobalTheory.T.archDerivative_keeps_sums_fixed_finite_parts F κ ψ hψ m g f1 h
    exact ⟨f2, by rw [word_cons, e1, e2]⟩

theorem word_law (hψ : IsStdInf F ψ) {G : Type} [Group G] (om : G →* Module.End ℂ ((κ → AdeleRing (𝓞 F) F) → ℂ))
    (pres : ∀ p, ∀ φ ∈ GlobalTheory.WeilM.schA F κ, om p φ ∈ GlobalTheory.WeilM.schA F κ)
    (M : G → ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) →ₗ[ℝ] ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)))
    (himpl : ∀ p h, ∀ φ ∈ GlobalTheory.WeilM.schA F κ,
      om p (GlobalTheory.WeilM.schr ψ (archPair F (M p h)) φ) = GlobalTheory.WeilM.schr ψ (archPair F h) (om p φ))
    (μ : @Measure (κ → FiniteAdeleRing (𝓞 F) F) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ)
    (hiso : ∀ p, ∀ φ ∈ GlobalTheory.WeilM.schA F κ, l2A F μ (om p φ) = l2A F μ φ) (p : G) :
    ∀ (w : List ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))) {φ : (κ → AdeleRing (𝓞 F) F) → ℂ}, φ ∈ GlobalTheory.WeilM.schA F κ →
      word F ψ w (om p φ) = om p (word F ψ (w.map (M p)) φ)
  | [], _, _ => rfl
  | h :: w, φ, hφ => by
    rw [List.map_cons, word_cons, word_cons, word_law hψ om pres M himpl μ hμ hiso p w hφ]
    exact GlobalTheory.T.weilRep_derivative_law_of_L2Isometric F κ ψ hψ om pres M himpl μ hμ hiso p h _ (word_mem hψ _ hφ)

theorem slice_l2_of (hψ : IsStdInf F ψ) {G : Type} [Group G] [TopologicalSpace G]
    (om : G →* Module.End ℂ ((κ → AdeleRing (𝓞 F) F) → ℂ))
    (pres : ∀ p, ∀ φ ∈ GlobalTheory.WeilM.schA F κ, om p φ ∈ GlobalTheory.WeilM.schA F κ)
    (M : G → ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) →ₗ[ℝ] ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)))
    (himpl : ∀ p h, ∀ φ ∈ GlobalTheory.WeilM.schA F κ,
      om p (GlobalTheory.WeilM.schr ψ (archPair F (M p h)) φ) = GlobalTheory.WeilM.schr ψ (archPair F h) (om p φ))
    (hM : ∀ h, Continuous fun p => M p h)
    (μ : @Measure (κ → FiniteAdeleRing (𝓞 F) F) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ)
    (hiso : ∀ p, ∀ φ ∈ GlobalTheory.WeilM.schA F κ, l2A F μ (om p φ) = l2A F μ φ)
    {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ GlobalTheory.WeilM.schA F κ) (p0 : G)
    (hfin : ∃ N ∈ nhds p0, ∃ (m : ℕ) (g : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (yy : Fin m → (κ → FiniteAdeleRing (𝓞 F) F)),
      (∀ i, g i ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) ∧ (∀ i j, g i (yy j) = if i = j then 1 else 0) ∧
      ∀ p ∈ N, ∃ f : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, om p Φ = ∑ i, GlobalTheory.WeilM.pureA F (f i) (g i))
    (y : (κ → FiniteAdeleRing (𝓞 F) F)) (i j : ℕ) :
    ∃ B : ℝ, ∀ᶠ p in nhds p0,
      ∫ x, (‖x‖ ^ i * ‖iteratedFDeriv ℝ j (fun x => om p Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x‖) ^ 2 ≤ B := by
  obtain ⟨L, C, hL⟩ := GlobalTheory.T.adelic_schwartz_l2_word_bound_exists F κ ψ hψ i j
  obtain ⟨N, hN, m, g, yy, hg, hdual, hf⟩ := hfin
  obtain ⟨CG, hCG, hG⟩ := GlobalTheory.T.finite_adelic_dual_basis_integral F κ m g yy hg hdual μ hμ y
  set R : ℝ := ∑ h ∈ L.flatten.toFinset, (‖M p0 h‖ + 1) with hR
  have hev : ∀ᶠ p in nhds p0, ∀ h ∈ L.flatten.toFinset, ‖M p h‖ ≤ R := by
    refine (Filter.eventually_all_finset _).2 fun h hh => ?_
    have hc : ContinuousAt (fun p => ‖M p h‖) p0 := ((hM h).norm).continuousAt
    filter_upwards [hc.eventually_lt continuousAt_const (lt_add_one ‖M p0 h‖)] with p hp
    exact hp.le.trans (Finset.single_le_sum (f := fun h => ‖M p0 h‖ + 1) (fun _ _ => by positivity) hh)
  have hB : ∀ w ∈ L, ∃ B : ENNReal, B ≠ ⊤ ∧ ∀ ws : List ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)), ws.length = w.length →
      (∀ h ∈ ws, ‖h‖ ≤ R) → l2A F μ (word F ψ ws Φ) ≤ B :=
    fun w _ => GlobalTheory.T.exists_finite_l2A_bound_words F κ ψ hψ Φ hΦ μ hμ w.length R
  choose! B hBtop hBle using hB
  have htop : ENNReal.ofReal C * (L.map fun w => CG * B w).sum ≠ ⊤ := by
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (list_sum_ne_top fun a ha => ?_)
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 ha
    exact ENNReal.mul_ne_top hCG (hBtop w hw)
  refine ⟨(ENNReal.ofReal C * (L.map fun w => CG * B w).sum).toReal, ?_⟩
  filter_upwards [hev, hN] with p hp hpN
  have key := hL (om p Φ) (pres p Φ hΦ) y
  have hsum : (L.map fun w => ∫⁻ x, ‖word F ψ w (om p Φ) (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2).sum ≤
      (L.map fun w => CG * B w).sum := by
    refine List.sum_le_sum fun w hw => ?_
    obtain ⟨f, hfp⟩ := hf p hpN
    obtain ⟨f', hf'⟩ := word_sum hψ g w f
    have e1 : word F ψ w (om p Φ) = ∑ i, GlobalTheory.WeilM.pureA F (f' i) (g i) := by rw [hfp, hf']
    calc ∫⁻ x, ‖word F ψ w (om p Φ) (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2
        ≤ CG * l2A F μ (word F ψ w (om p Φ)) := by rw [e1]; exact hG f'
      _ = CG * l2A F μ (word F ψ (w.map (M p)) Φ) := by
          rw [word_law hψ om pres M himpl μ hμ hiso p w hΦ, hiso p _ (word_mem hψ _ hΦ)]
      _ ≤ CG * B w := by
          gcongr
          refine hBle w hw _ (List.length_map _) fun h hh => ?_
          obtain ⟨h0, h0m, rfl⟩ := List.mem_map.1 hh
          exact hp h0 (List.mem_toFinset.2 (List.mem_flatten.2 ⟨w, hw, h0m⟩))
  exact (ENNReal.ofReal_le_iff_le_toReal htop).1 (key.trans (by gcongr))

end Core

end GlobalTheory.WeilL2Words

theorem GlobalTheory.WeilL2Words.weilTransport_archimedeanSlice_sobolev_bounds_alt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
 ∀ om : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →* Module.End ℂ ((κ → AF D.host.F) → ℂ),
                       GlobalTheory.WeilSchrodinger.IsTransport ψ co ω om →
  ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ (y : κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F) p0 (i j : ℕ), ∃ B : ℝ,
      ∀ᶠ p in nhds p0, ∫ x, (‖x‖ ^ i * ‖iteratedFDeriv ℝ j (fun x => om p Φ (GlobalTheory.WeilCont.adeleJoin D.host.F x y)) x‖) ^ 2 ≤ B := by
  intro D ψ hψ S T χS χT hS hT hrS hrT JA JB ξ hA hJB κ _ co hco ω hω om hom Φ hΦ y p0 i j
  have hI := GlobalTheory.T.transportedWeil_preserves_schwartz_heisenberg_equivariant D ψ hψ S T χS χT hS hT hrS hrT JA JB ξ hA hJB κ co hco ω hω om hom
  obtain ⟨M, himpl, hM⟩ := GlobalTheory.T.transported_archHeisenbergDirections_continuous D ψ _ _ JA JB ξ κ co om hI.2
  obtain ⟨μ, hμ, hiso⟩ := GlobalTheory.T.l2A_transport_gram_transpose D ψ hψ S T χS χT hS hT hrS hrT JA JB ξ hA hJB κ co hco ω hω om hom
  exact GlobalTheory.WeilL2Words.slice_l2_of (GlobalTheory.T.isStandardArchimedeanAddChar_of_standardChar D ψ hψ) om hI.1 M himpl hM μ hμ hiso hΦ p0
    (GlobalTheory.T.exists_local_finiteDim_finiteParts_weilOperators D ψ hψ S T χS χT hS hT hrS hrT JA JB ξ hA hJB κ co hco ω hω om hom Φ hΦ p0) y i j
end
end

