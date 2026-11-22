import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IntegralApproximation
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DataCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0020
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowFrameCoherence.Bundle0001
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.NormAdditiveCharacterTypePrimeEqOne
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.HermitianCombinationZ

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.AlpBoundHolds
section
namespace Formalism.L2.SG.IntegralApproximation

theorem AlpBound_holds (D : Formalism.BasicNotions.D7) : Formalism.L2.SG.DataCut.AlpBound D := alpBoundU D

end Formalism.L2.SG.IntegralApproximation
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CardCells
section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.CountAb

variable {G 𝒳 : Type} [Group G] [MulAction G 𝒳]
variable (W : 𝒳) (S N' K : Subgroup G) (π : G →* G) (g : G)

def cellEquiv (hD : Data W S N' K π) :
    Quotient (Setoid.ker (Formalism.L2.SG.Pf.ProdEP2Core.dcMap (Ak S K) (πk W S N' K π hD) (Hk W K g))) ≃
      Quotient (cellRel W N' K g) := by
  refine Equiv.ofBijective (Quotient.lift (fun k => (⟦toCell W S N' K π g hD k⟧ : Quotient (cellRel W N' K g)))
    (fun k₁ k₂ h => ?_)) ⟨?_, ?_⟩
  · apply Quotient.sound
    exact (cellRel_iff W S N' K π g hD k₁ k₂).2
      ((Formalism.L2.SG.Pf.ProdEP2Core.dcMap_eq_iff (Ak S K) (πk W S N' K π hD) (Hk W K g) k₁ k₂).1 h)
  · intro x y hxy
    induction x using Quotient.inductionOn with
    | h k₁ =>
      induction y using Quotient.inductionOn with
      | h k₂ =>
        apply Quotient.sound
        have h2 := Quotient.exact hxy
        exact (Formalism.L2.SG.Pf.ProdEP2Core.dcMap_eq_iff (Ak S K) (πk W S N' K π hD) (Hk W K g) k₁ k₂).2
          ((cellRel_iff W S N' K π g hD k₁ k₂).1 h2)
  · intro y
    induction y using Quotient.inductionOn with
    | h c =>
      obtain ⟨k, rfl⟩ := toCell_surj W S N' K π g hD c
      exact ⟨⟦k⟧, rfl⟩

theorem card_cells (hD : Data W S N' K π) :
    Nat.card (Quotient (cellRel W N' K g)) = ((Hk W K g).map (πk W S N' K π hD)).index := by
  rw [← Nat.card_congr (cellEquiv W S N' K π g hD)]
  exact Formalism.L2.SG.Pf.ProdEP2Core.card_dc (Ak S K) (πk W S N' K π hD) (Hk W K g) (πk_id W S N' K π hD)

end Formalism.L2.SG.Pf.CountAb
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ClassFrameCut
section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.RowForm

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets
  Formalism.L2.SG.MassDataConc Formalism.L2.SG.MassDataForm MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (Y : Formalism.L2.SG.Full.Full X)
  (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
  (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (sd C Th : ℝ)
  (vR : Term D u u' (X.Fu u) (Y.what₂ u) → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' (X.Fu u) (Y.what₂ u))
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
  (κ : Term D u u' (X.Fu u) (Y.what₂ u) → ℕ)

def chiOO (s : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) : X.Vpi u' →L[ℂ] X.Vpi u :=
  Formalism.L2.SG.TermOp.chiN X (Formalism.L2.SG.TermOp.kOf X u u' ((Y.cs u).h ((Y.cs u).base s.lam) : X.B.I.Gf)
            ((Y.cs u').h ((Y.cs u').base s.lam') : X.B.I.Gf) s.pt) • Formalism.L2.SG.TermOp.OOt s

def OOnu (s : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) : X.Vpi u' →L[ℂ] X.Vpi u :=
  haveI := FiniteDimensional.complete ℂ (X.Vpi u)
  Formalism.L2.SG.TermOp.OO (νq s.pt.1) Set.univ (X.Wu u) (X.Wu u') s.pt.1

def frameVal (A : X.Vpi u ≃ₗᵢ[ℂ] X.Vpi u) (B : X.Vpi u' ≃ₗᵢ[ℂ] X.Vpi u')
    (s : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) : X.Vpi u' →L[ℂ] X.Vpi u :=
  Formalism.L2.SG.PairVal.cTerm vR s.toTerm •
    ((A : X.Vpi u →L[ℂ] X.Vpi u).comp
      ((Formalism.L2.SG.RealObj.unscaledOperatorAtPointRepresentative X u u' 1 i0 i0' νq (Formalism.L2.SG.PairVal.ptOf s.toTerm)).comp (B.symm : X.Vpi u' →L[ℂ] X.Vpi u')))

def FormAllVolC : Prop :=
  ∀ (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ) (s : LiftT X Y u u' κ R ρ), s.1.relevant →
    Formalism.L2.SG.TermOp.OOt s.1 = ((vR s.1.toTerm : ℝ) : ℂ) • OOnu X Y u u' νq s.1

def NormalFormC : Prop :=
  ∀ (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ) (s : LiftT X Y u u' κ R ρ), s.1.relevant →
    ∃ (A : X.Vpi u ≃ₗᵢ[ℂ] X.Vpi u) (B : X.Vpi u' ≃ₗᵢ[ℂ] X.Vpi u'),
      chiOO X Y u u' s.1 = frameVal X Y u u' vR i0 i0' νq A B s.1

def CommonFrameC : Prop :=
  ∀ (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ),
    ∃ (U : X.Vpi u ≃ₗᵢ[ℂ] X.Vpi u) (U' : X.Vpi u' ≃ₗᵢ[ℂ] X.Vpi u') (ζ : ℂ), ‖ζ‖ = 1 ∧
      ∀ (s : LiftT X Y u u' κ R ρ) (A : X.Vpi u ≃ₗᵢ[ℂ] X.Vpi u) (B : X.Vpi u' ≃ₗᵢ[ℂ] X.Vpi u'),
        chiOO X Y u u' s.1 = frameVal X Y u u' vR i0 i0' νq A B s.1 →
          frameVal X Y u u' vR i0 i0' νq A B s.1 = ζ • frameVal X Y u u' vR i0 i0' νq U U' s.1

def LemmaVLiftC : Prop :=
  ∀ (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ) (s : LiftT X Y u u' κ R ρ), ¬ s.1.relevant →
    Formalism.L2.SG.TermOp.OOt s.1 = 0

def AtPtRelevantC : Prop :=
  ∀ (t : Term D u u' (X.Fu u) (Y.what₂ u)) (w : Point D.host.E (D.R.rS + 1)), t.atPt w → t.relevant

theorem cTerm_irrel (hAt : AtPtRelevantC X Y u u') (t : Term D u u' (X.Fu u) (Y.what₂ u)) (ht : ¬ t.relevant) :
    Formalism.L2.SG.PairVal.cTerm vR t = 0 := by
  unfold Formalism.L2.SG.PairVal.cTerm
  rw [dif_neg]
  rintro ⟨w, hw⟩
  exact ht (hAt t w hw)

end Formalism.L2.SG.Pf.RowForm

namespace Formalism.L2.SG.Pf

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.Pf.RowForm
  MeasureTheory

theorem classFrameOO_of {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
    (vR : Term D u u' (X.Fu u) (Y.what₂ u) → ℝ)
    (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (κ : Term D u u' (X.Fu u) (Y.what₂ u) → ℕ)
    (hB : NormalFormC X Y u u' vR i0 i0' νq κ)
    (hC : CommonFrameC X Y u u' vR i0 i0' νq κ) (hV : LemmaVLiftC X Y u u' κ) (hAt : AtPtRelevantC X Y u u') :
    ClassFrameOO X Y u u' vR i0 i0' νq κ := by
  intro R ρ
  obtain ⟨U, U', ζ, hζ, hU⟩ := hC R ρ
  refine ⟨U, U', ζ, hζ, fun s => ?_⟩
  by_cases hs : s.1.relevant
  · obtain ⟨A, B, hAB⟩ := hB R ρ s hs
    have h1 := hAB.trans (hU s A B hAB)
    unfold chiOO frameVal at h1
    rw [h1, smul_smul]
  · rw [hV R ρ s hs, smul_zero, cTerm_irrel X Y u u' vR hAt _ hs, mul_zero, zero_smul]

end Formalism.L2.SG.Pf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ClmEqZeroOfSpan
section
noncomputable section

open scoped InnerProductSpace
open Matrix Formalism.MainNotions.S

namespace PI.SchurPlaces

section Tens

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, NormedAddCommGroup (V i)]
  [∀ i, InnerProductSpace ℂ (V i)] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]

theorem eq_of_inner_span (tens : (∀ i, V i) → W) (hspan : Submodule.span ℂ (Set.range tens) = ⊤) {a b : W}
    (h : ∀ z, ⟪tens z, a⟫_ℂ = ⟪tens z, b⟫_ℂ) : a = b := by
  have h2 : ∀ w ∈ Submodule.span ℂ (Set.range tens), ⟪w, a - b⟫_ℂ = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, rfl⟩ := hx
      rw [inner_sub_right, h z, sub_self]
    | zero => exact inner_zero_left _
    | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
    | smul c x _ hx => rw [inner_smul_left, hx, mul_zero]
  have h3 := h2 (a - b) (by rw [hspan]; exact Submodule.mem_top)
  exact sub_eq_zero.1 (inner_self_eq_zero.1 h3)

theorem prod_upd_left (y z : ∀ i, V i) (i₀ : ι) (b : V i₀) :
    ∏ i, ⟪Function.update y i₀ b i, z i⟫_ℂ = ⟪b, z i₀⟫_ℂ * ∏ i ∈ Finset.univ.erase i₀, ⟪y i, z i⟫_ℂ := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀)]
  congr 1
  · simp
  · apply Finset.prod_congr rfl
    intro i hi
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

theorem prod_upd_right (y z : ∀ i, V i) (i₀ : ι) (c : V i₀) :
    ∏ i, ⟪y i, Function.update z i₀ c i⟫_ℂ = ⟪y i₀, c⟫_ℂ * ∏ i ∈ Finset.univ.erase i₀, ⟪y i, z i⟫_ℂ := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀)]
  congr 1
  · simp
  · apply Finset.prod_congr rfl
    intro i hi
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

variable (tens : (∀ i, V i) → W) (hin : ∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ i, ⟪x i, y i⟫_ℂ)
  (hspan : Submodule.span ℂ (Set.range tens) = ⊤)

include hin hspan in
theorem tens_upd_add (x : ∀ i, V i) (i₀ : ι) (p q : V i₀) :
    tens (Function.update x i₀ (p + q)) = tens (Function.update x i₀ p) + tens (Function.update x i₀ q) := by
  refine eq_of_inner_span tens hspan fun z => ?_
  rw [inner_add_right, hin, hin, hin, prod_upd_right, prod_upd_right, prod_upd_right, inner_add_right, add_mul]

include hin hspan in
theorem tens_upd_smul (x : ∀ i, V i) (i₀ : ι) (c : ℂ) (p : V i₀) :
    tens (Function.update x i₀ (c • p)) = c • tens (Function.update x i₀ p) := by
  refine eq_of_inner_span tens hspan fun z => ?_
  rw [inner_smul_right, hin, hin, prod_upd_right, prod_upd_right, inner_smul_right, mul_assoc]

def insertLocal (x : ∀ i, V i) (i₀ : ι) : V i₀ →ₗ[ℂ] W where
  toFun p := tens (Function.update x i₀ p)
  map_add' p q := tens_upd_add tens hin hspan x i₀ p q
  map_smul' c p := tens_upd_smul tens hin hspan x i₀ c p

end Tens

theorem clm_eq_zero_of_span {W W' : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [NormedAddCommGroup W']
    [InnerProductSpace ℂ W'] {S : Set W'} (hS : Submodule.span ℂ S = ⊤) (P : W' →L[ℂ] W) (h : ∀ w ∈ S, P w = 0) :
    P = 0 := by
  ext w
  have h1 : (P : W' →ₗ[ℂ] W) = ((0 : W' →L[ℂ] W) : W' →ₗ[ℂ] W) :=
    LinearMap.ext_on hS (fun v hv => by simp [h v hv])
  exact LinearMap.congr_fun h1 w

theorem jm_allPos' (k : ℕ) : Formalism.REAL.Jm (allPos k) = 1 := by
  unfold Formalism.REAL.Jm allPos
  simp

theorem memU_iff {k : ℕ} (g : Matrix (Fin k) (Fin k) ℂ) : g ∈ UJset (allPos k) ↔ gᴴ * g = 1 := by
  simp only [UJset, Set.mem_setOf_eq, Formalism.REAL.inUJ, jm_allPos', Matrix.mul_one]

theorem memU_mul {k : ℕ} {a b : Matrix (Fin k) (Fin k) ℂ} (ha : a ∈ UJset (allPos k)) (hb : b ∈ UJset (allPos k)) :
    a * b ∈ UJset (allPos k) := by
  rw [memU_iff] at *
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc aᴴ, ha, Matrix.one_mul, hb]

theorem memU_star {k : ℕ} {a : Matrix (Fin k) (Fin k) ℂ} (ha : a ∈ UJset (allPos k)) : aᴴ ∈ UJset (allPos k) := by
  rw [memU_iff] at *
  rw [Matrix.conjTranspose_conjTranspose]
  exact mul_eq_one_comm.1 ha

theorem memU_rinv {k : ℕ} {a : Matrix (Fin k) (Fin k) ℂ} (ha : a ∈ UJset (allPos k)) : a * aᴴ = 1 :=
  mul_eq_one_comm.1 ((memU_iff a).1 ha)

theorem memU_one (k : ℕ) : (1 : Matrix (Fin k) (Fin k) ℂ) ∈ UJset (allPos k) := by
  rw [memU_iff]; simp

private theorem inner_apply_eq_inner_conjTranspose_apply_of_isHCTypeU {k : ℕ} {u : Fin k → ℝ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin k) (Fin k) ℂ → H →L[ℂ] H} (hσ : IsHCTypeU k u σ) {h : Matrix (Fin k) (Fin k) ℂ}
    (hh : h ∈ UJset (allPos k)) (v w : H) : ⟪v, σ h w⟫_ℂ = ⟪σ hᴴ v, w⟫_ℂ := by
  obtain ⟨_, _, ⟨⟨h1, hmul⟩, hnorm, _⟩, _⟩ := hσ
  have hs : hᴴ ∈ UJset (allPos k) := memU_star hh
  have e : hᴴ * h = 1 := (memU_iff h).mp hh
  have hinv : σ hᴴ (σ h w) = w := by
    rw [← ContinuousLinearMap.comp_apply, ← hmul _ hs _ hh, e, h1, ContinuousLinearMap.one_apply]
  let L : H →ₗᵢ[ℂ] H := ⟨(σ hᴴ : H →ₗ[ℂ] H), fun x => hnorm _ hs x⟩
  have key := L.inner_map_map v (σ h w)
  change ⟪σ hᴴ v, σ hᴴ (σ h w)⟫_ℂ = _ at key
  rw [hinv] at key
  exact key.symm

private theorem inner_tens_apply_eq_inner_update_adjoint {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, NormedAddCommGroup (V i)]
    [∀ i, InnerProductSpace ℂ (V i)] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (tens : (∀ i, V i) → W) (hin : ∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ i, ⟪x i, y i⟫_ℂ)
    (hspan : Submodule.span ℂ (Set.range tens) = ⊤) (i₀ : ι) (f g : V i₀ →L[ℂ] V i₀)
    (hfg : ∀ a b, ⟪a, f b⟫_ℂ = ⟪g a, b⟫_ℂ) (T : W →L[ℂ] W)
    (hT : ∀ z, T (tens z) = tens (Function.update z i₀ (f (z i₀)))) (y : ∀ i, V i) (w : W) :
    ⟪tens y, T w⟫_ℂ = ⟪tens (Function.update y i₀ (g (y i₀))), w⟫_ℂ := by
  have hw : w ∈ Submodule.span ℂ (Set.range tens) := by rw [hspan]; trivial
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨z, rfl⟩ := hx
    rw [hT, hin, hin, prod_upd_right, prod_upd_left, hfg]
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, inner_add_right, inner_add_right, ha, hb]
  | smul c a _ ha => rw [map_smul, inner_smul_right, inner_smul_right, ha]

theorem schurCoreA_of (h7 : Formalism.MainNotions.NonGenericAndKTwoTheorems.adm7) : SchurCoreA := by
  classical
  unfold SchurCoreA
  intro k ι _ V V' _ _ _ _ _ _ W W' _ _ _ _ _ _ tens tens' hin hspan hin' hspan' π π' lam lam' hπ hπ' i₀ hne C hC P hP
  have hπ1 : ∀ i, π i 1 = 1 := fun i => by
    obtain ⟨_, _, ⟨⟨h1, _⟩, _⟩, _⟩ := hπ i
    exact h1
  have hπ'1 : ∀ i, π' i 1 = 1 := fun i => by
    obtain ⟨_, _, ⟨⟨h1, _⟩, _⟩, _⟩ := hπ' i
    exact h1
  have hπ'mul : ∀ a ∈ UJset (allPos k), ∀ b ∈ UJset (allPos k), π' i₀ (a * b) = π' i₀ a ∘L π' i₀ b := by
    obtain ⟨_, _, ⟨⟨_, hm⟩, _⟩, _⟩ := hπ' i₀
    exact hm
  have key : ∀ h ∈ UJset (allPos k), ∀ (y : ∀ i, V i) (y' : ∀ i, V' i),
      ⟪tens y, P (tens' (Function.update y' i₀ (π' i₀ (C i₀ * h * (C i₀)ᴴ) (y' i₀))))⟫_ℂ =
        ⟪tens (Function.update y i₀ (π i₀ hᴴ (y i₀))), P (tens' y')⟫_ℂ := by
    intro h hh y y'
    have hM : ∀ i, Function.update (fun _ => (1 : Matrix (Fin k) (Fin k) ℂ)) i₀ h i ∈ UJset (allPos k) := by
      intro i
      by_cases hi : i = i₀
      · subst hi
        simpa using hh
      · rw [Function.update_of_ne hi]
        exact memU_one k
    obtain ⟨A, B, hA, hB, hAB⟩ := hP _ hM
    have hA' : ∀ z, A (tens z) = tens (Function.update z i₀ (π i₀ h (z i₀))) := by
      intro z
      rw [hA]
      congr 1
      funext i
      by_cases hi : i = i₀
      · subst hi
        simp
      · simp [Function.update_of_ne hi, hπ1]
    have hB' : ∀ z, B (tens' z) = tens' (Function.update z i₀ (π' i₀ (C i₀ * h * (C i₀)ᴴ) (z i₀))) := by
      intro z
      rw [hB]
      congr 1
      funext i
      by_cases hi : i = i₀
      · subst hi
        simp
      · simp [Function.update_of_ne hi, memU_rinv (hC i), hπ'1]
    rw [← hB', ← ContinuousLinearMap.comp_apply P B, ← hAB, ContinuousLinearMap.comp_apply]
    exact inner_tens_apply_eq_inner_update_adjoint tens hin hspan i₀ (π i₀ h) (π i₀ hᴴ) (fun a b => inner_apply_eq_inner_conjTranspose_apply_of_isHCTypeU (hπ i₀) hh a b) A hA' y _
  have main : ∀ (x : ∀ i, V i) (x' : ∀ i, V' i), ⟪tens x, P (tens' x')⟫_ℂ = 0 := by
    intro x x'
    obtain ⟨Q, hQ⟩ : ∃ Q : V' i₀ →L[ℂ] V i₀, ∀ p q,
        ⟪p, Q q⟫_ℂ = ⟪tens (Function.update x i₀ p), P (tens' (Function.update x' i₀ q))⟫_ℂ := by
      let S : V i₀ →L[ℂ] W := LinearMap.toContinuousLinearMap (insertLocal tens hin hspan x i₀)
      let S' : V' i₀ →L[ℂ] W' := LinearMap.toContinuousLinearMap (insertLocal tens' hin' hspan' x' i₀)
      refine ⟨ContinuousLinearMap.adjoint S ∘L P ∘L S', fun p q => ?_⟩
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
      rfl
    have hint : ∀ h ∈ UJset (allPos k), Q ∘L π' i₀ (C i₀ * h * (C i₀)ᴴ) = π i₀ h ∘L Q := by
      intro h hh
      ext q
      apply ext_inner_left ℂ
      intro p
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hQ, inner_apply_eq_inner_conjTranspose_apply_of_isHCTypeU (hπ i₀) hh, hQ]
      have e := key h hh (Function.update x i₀ p) (Function.update x' i₀ q)
      simp only [Function.update_idem, Function.update_self] at e
      exact e
    have hc := hC i₀
    have hR : ∀ h ∈ UJset (allPos k), (Q ∘L π' i₀ (C i₀)) ∘L π' i₀ h = π i₀ h ∘L (Q ∘L π' i₀ (C i₀)) := by
      intro h hh
      have hch : C i₀ * h ∈ UJset (allPos k) := memU_mul hc hh
      have hchc : C i₀ * h * (C i₀)ᴴ ∈ UJset (allPos k) := memU_mul hch (memU_star hc)
      have e : C i₀ * h = C i₀ * h * (C i₀)ᴴ * C i₀ := by
        rw [Matrix.mul_assoc (C i₀ * h), (memU_iff _).mp hc, Matrix.mul_one]
      rw [ContinuousLinearMap.comp_assoc, ← hπ'mul _ hc _ hh, e, hπ'mul _ hchc _ hc,
        ← ContinuousLinearMap.comp_assoc Q, hint h hh, ContinuousLinearMap.comp_assoc (π i₀ h)]
    have hR0 : Q ∘L π' i₀ (C i₀) = 0 :=
      h7 k (lam i₀) (lam' i₀) (V i₀) (V' i₀) (π i₀) (π' i₀) (hπ i₀) (hπ' i₀) hne _ hR
    have hQ0 : Q = 0 := by
      have e1 : π' i₀ (C i₀) ∘L π' i₀ (C i₀)ᴴ = 1 := by
        rw [← hπ'mul _ hc _ (memU_star hc), memU_rinv hc, hπ'1]
      calc Q = Q ∘L (π' i₀ (C i₀) ∘L π' i₀ (C i₀)ᴴ) := by
            rw [e1]
            ext
            simp
        _ = (Q ∘L π' i₀ (C i₀)) ∘L π' i₀ (C i₀)ᴴ := (ContinuousLinearMap.comp_assoc _ _ _).symm
        _ = 0 := by rw [hR0, ContinuousLinearMap.zero_comp]
    have e2 := hQ (x i₀) (x' i₀)
    rw [Function.update_eq_self, Function.update_eq_self, hQ0] at e2
    simpa using e2.symm
  apply clm_eq_zero_of_span hspan' P
  rintro w ⟨x', rfl⟩
  exact eq_of_inner_span (a := P (tens' x')) (b := 0) tens hspan (fun x => by rw [main x x', inner_zero_right])

end PI.SchurPlaces
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LeviTens
section
noncomputable section

open scoped Classical InnerProductSpace
open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full

namespace PI.SchurPlaces

open Formalism.L2.SG.KappaOffDiagonal PI.SchurPlaces.LeviLA

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem frameAt (X : HidaSetting D) (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) :
    Frame (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (fun a => rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR u))
      (X.wfr u v) where
  ee a b := by
    simp only [HidaSetting.eR]; rw [Formalism.L2.SG.PoincareInHH.Cut.hJ_crd, X.ee, map_zero]
  ef a b := by
    simp only [HidaSetting.eR, HidaSetting.fR]; rw [Formalism.L2.SG.PoincareInHH.Cut.hJ_crd, X.ef]; split_ifs <;> simp
  ff a b := by
    simp only [HidaSetting.fR]; rw [Formalism.L2.SG.PoincareInHH.Cut.hJ_crd, X.ff, map_zero]
  ez a := by
    simp only [HidaSetting.eR, HidaSetting.zR]; rw [Formalism.L2.SG.PoincareInHH.Cut.hJ_crd, (X.zu_orth u a).1, map_zero]
  fz a := by
    simp only [HidaSetting.fR, HidaSetting.zR]; rw [Formalism.L2.SG.PoincareInHH.Cut.hJ_crd, (X.zu_orth u a).2, map_zero]
  ew a b := ((X.wfr_perp u v b).1 a).1
  fw a b := ((X.wfr_perp u v b).1 a).2
  zw b := (X.wfr_perp u v b).2
  ww := X.wfr_on u v
  zz := by
    simp only [HidaSetting.zR]
    rw [Formalism.L2.SG.PoincareInHH.Cut.hJ_crd, X.zu_norm, map_neg, map_natCast]
    exact neg_ne_zero.2 (Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero)
  card := by
    have h1 := X.n_eq; have h2 := D.R.r_eq; have h3 := D.R.rS_two; omega

theorem wfrSpan : WfrSpan := by
  intro D X u v y hef hz
  exact perp_efz (frameAt X u v) y hef hz

theorem leviTens : LeviTens := by
  intro D X u h hh x
  have hS : ∀ v, InS (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) (uMat (h v)) := hh
  choose V hVu hVe hVf hVz hVw hVN using fun v =>
    levi_place (frameAt X u v) ((h v : Formalism.REAL.UJ (X.B.I.ε v)) : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ)
      (h v).2 (hS v)
  let s0 : X.B.I.Ginf := fun v => ⟨V v, hVu v⟩
  have hs0 : ∀ v, uMat (s0 v) = (V v : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) := fun v => rfl
  have hn : ∀ v, uMat ((s0⁻¹ * h) v) =
      (((V v)⁻¹ : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) *
        uMat (h v) := fun v => rfl
  have hs0S : s0 ∈ X.SinfU u := by
    intro v
    refine ⟨fun a => ?_, ?_⟩
    · rw [hs0, sub_mulVec, one_mulVec, hVe v a, sub_self]; exact zero_mem _
    · rw [hs0, sub_mulVec, one_mulVec, hVz v, sub_self]; exact zero_mem _
  have hnN : s0⁻¹ * h ∈ X.NinfU u := fun v => by rw [show uMat ((s0⁻¹ * h) v) = _ from hn v]; exact hVN v
  have hnS : s0⁻¹ * h ∈ X.SinfU u := fun v => (hnN v).1
  have hsplit : h = s0 * (s0⁻¹ * h) := by rw [mul_inv_cancel_left]
  have hpi : X.piU u h = X.piU u s0 := by
    rw [hsplit, (X.piU_rep u).2.1 s0 hs0S _ hnS, (X.piU_rep u).2.2.2.1 _ hnN, mul_one]
  have hs0H : s0 ∈ Hset X.B.I (Set.range (fun a => crdOf X.B.I X.ιE X.bas (X.eX a)) ∪
      Set.range (fun a => crdOf X.B.I X.ιE X.bas (X.fY a)) ∪ {crdOf X.B.I X.ιE X.bas (X.zu u)}) := by
    intro v p hp
    rw [hs0]
    rcases hp with (⟨a, rfl⟩ | ⟨a, rfl⟩) | hp
    · exact hVe v a
    · exact hVf v a
    · rw [Set.mem_singleton_iff] at hp; subst hp; exact hVz v
  have hmat : ∀ v, matW X.B.I (X.wfr u v) v s0 = matW X.B.I (X.wfr u v) v h := fun v => by
    ext a b; exact hVw v a b
  rw [hpi, X.tensU_equiv u s0 hs0H x]
  simp only [hmat]

end PI.SchurPlaces
end
end

