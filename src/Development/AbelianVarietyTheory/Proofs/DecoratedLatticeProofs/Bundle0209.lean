import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0389
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0042
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0074
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0291
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceCharacterConductorIntegers
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0034
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0190
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0174

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemBlockUpperTriangularTwoIffLowerLeftZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.ParabIndex

theorem card_GL_real (κ : Type) [Field κ] [Finite κ] (m : ℕ) :
    (Nat.card (GL (Fin m) κ) : ℝ)
      = (Nat.card κ : ℝ) ^ (m * m) * ∏ i ∈ Finset.Ioc 0 m, (1 - ((Nat.card κ : ℝ) ^ i)⁻¹) := by
  letI := Fintype.ofFinite κ
  rw [GlobalTheory.Mem.card_GL_eq_pow_mul_qE κ m, Nat.card_eq_fintype_card, Formalism.MainNotions.ZetaProductPairs.qE]
  congr 1
  have h : Finset.Icc 1 m = Finset.Ioc 0 m := by
    ext i; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [h]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [_root_.zpow_neg, zpow_natCast]

variable {κ : Type} [Field κ]

theorem val_mk' {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι κ) (h : IsUnit A.det) :
    ((Matrix.GeneralLinearGroup.mk'' A h : GL ι κ) : Matrix ι ι κ) = A := rfl

def toSum {r s : ℕ} (g : GL (Fin (r + s)) κ) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) κ :=
  Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm (g : Matrix (Fin (r + s)) (Fin (r + s)) κ)

theorem isUnit_det_toSum {r s : ℕ} (g : GL (Fin (r + s)) κ) : IsUnit (toSum g).det := by
  rw [toSum, Matrix.det_reindex_self]
  exact (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit

theorem mem_blockUpperTriangularTwo_iff_lowerLeft_zero {r s : ℕ} (g : GL (Fin (r + s)) κ) :
    g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) ↔ (toSum g).toBlocks₂₁ = 0 := by
  rw [Formalism.L2.DIV.mem_blockTri]
  constructor
  · intro h
    ext i j
    simp only [toSum, Matrix.toBlocks₂₁, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
      Matrix.of_apply, Matrix.zero_apply]
    apply h
    simp [Formalism.L2.DIV.blk2]
  · intro h i j hij
    obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective j
    rcases x with x | x <;> rcases y with y | y
    · simp [Formalism.L2.DIV.blk2] at hij
    · simp [Formalism.L2.DIV.blk2] at hij
    · have := congrFun (congrFun h x) y
      simpa [toSum, Matrix.toBlocks₂₁] using this
    · simp [Formalism.L2.DIV.blk2] at hij

theorem toSum_eq_fromBlocks {r s : ℕ} {g : GL (Fin (r + s)) κ} (hg : g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r)) :
    toSum g = Matrix.fromBlocks (toSum g).toBlocks₁₁ (toSum g).toBlocks₁₂ 0 (toSum g).toBlocks₂₂ := by
  rw [← (mem_blockUpperTriangularTwo_iff_lowerLeft_zero g).1 hg]; exact (Matrix.fromBlocks_toBlocks _).symm

theorem isUnit_blocks {r s : ℕ} {g : GL (Fin (r + s)) κ} (hg : g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r)) :
    IsUnit ((toSum g).toBlocks₁₁.det * (toSum g).toBlocks₂₂.det) := by
  rw [← Matrix.det_fromBlocks_zero₂₁ _ (toSum g).toBlocks₁₂, ← toSum_eq_fromBlocks hg]
  exact isUnit_det_toSum g

theorem isUnit_det_fromBlocks {r s : ℕ} (A : GL (Fin r) κ) (D : GL (Fin s) κ) (B : Matrix (Fin r) (Fin s) κ) :
    IsUnit (Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (A : Matrix (Fin r) (Fin r) κ) B 0 (D : Matrix (Fin s) (Fin s) κ))).det := by
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]
  exact ((Matrix.isUnit_iff_isUnit_det _).1 A.isUnit).mul ((Matrix.isUnit_iff_isUnit_det _).1 D.isUnit)

noncomputable def blockTriangularEquiv (r s : ℕ) :
    Formalism.L2.DIV.blockTri (κ := κ) (Formalism.L2.DIV.blk2 (n := r + s) r) ≃
      GL (Fin r) κ × GL (Fin s) κ × Matrix (Fin r) (Fin s) κ where
  toFun g :=
    (Matrix.GeneralLinearGroup.mk'' _ (isUnit_of_mul_isUnit_left (isUnit_blocks g.2)),
     Matrix.GeneralLinearGroup.mk'' _ (isUnit_of_mul_isUnit_right (isUnit_blocks g.2)),
     (toSum g.1).toBlocks₁₂)
  invFun x := ⟨Matrix.GeneralLinearGroup.mk'' _ (isUnit_det_fromBlocks x.1 x.2.1 x.2.2), by
    rw [mem_blockUpperTriangularTwo_iff_lowerLeft_zero]
    ext i j
    simp [toSum, Matrix.toBlocks₂₁, val_mk']⟩
  left_inv g := by
    apply Subtype.ext
    apply Units.ext
    show Matrix.reindex finSumFinEquiv finSumFinEquiv _ = _
    have h := toSum_eq_fromBlocks g.2
    change Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (toSum g.1).toBlocks₁₁ (toSum g.1).toBlocks₁₂ 0 (toSum g.1).toBlocks₂₂) = _
    rw [← h, toSum]
    simp
  right_inv x := by
    rcases x with ⟨A, D, B⟩
    refine Prod.ext (Units.ext ?_) (Prod.ext (Units.ext ?_) ?_)
    · show (toSum _).toBlocks₁₁ = _
      ext i j; simp [toSum, Matrix.toBlocks₁₁, val_mk']
    · show (toSum _).toBlocks₂₂ = _
      ext i j; simp [toSum, Matrix.toBlocks₂₂, val_mk']
    · show (toSum _).toBlocks₁₂ = _
      ext i j; simp [toSum, Matrix.toBlocks₁₂, val_mk']

theorem natCard_blockUpperTriangularTwo_finiteField (κ : Type) [Field κ] [Finite κ] (r s : ℕ) :
    Nat.card (Formalism.L2.DIV.blockTri (κ := κ) (Formalism.L2.DIV.blk2 (n := r + s) r)) =
      Nat.card (GL (Fin r) κ) * Nat.card (GL (Fin s) κ) * Nat.card κ ^ (r * s) := by
  rw [Nat.card_congr (blockTriangularEquiv r s), Nat.card_prod, Nat.card_prod, mul_assoc]
  congr 2
  show Nat.card (Fin r → Fin s → κ) = _
  rw [Nat.card_fun, Nat.card_fun, Nat.card_fin, Nat.card_fin, ← pow_mul, mul_comm]

end GlobalTheory.ParabIndex

namespace GlobalTheory.ParabIndex

theorem index_maxParabolic_GL_finiteField : ∀ (κ : Type) [Field κ] [Finite κ] (n r s : ℕ), n = r + s → (((Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) : Subgroup (GL (Fin n) κ)).index : ℕ) : ℝ) = (Nat.card κ : ℝ) ^ (r * s) * (∏ i ∈ Finset.Ioc 0 n, (1 - ((Nat.card κ : ℝ) ^ i)⁻¹)) / ((∏ i ∈ Finset.Ioc 0 r, (1 - ((Nat.card κ : ℝ) ^ i)⁻¹)) * ∏ i ∈ Finset.Ioc 0 s, (1 - ((Nat.card κ : ℝ) ^ i)⁻¹)) := by
  intro κ _ _ n r s hn
  subst hn
  have hmul := (Formalism.L2.DIV.blockTri (κ := κ) (Formalism.L2.DIV.blk2 (n := r + s) r)).card_mul_index
  rw [natCard_blockUpperTriangularTwo_finiteField] at hmul
  have hR : (((Formalism.L2.DIV.blockTri (κ := κ) (Formalism.L2.DIV.blk2 (n := r + s) r)).index : ℕ) : ℝ) *
      ((Nat.card (GL (Fin r) κ) : ℝ) * (Nat.card (GL (Fin s) κ) : ℝ) * (Nat.card κ : ℝ) ^ (r * s))
      = (Nat.card (GL (Fin (r + s)) κ) : ℝ) := by
    rw [mul_comm]; exact_mod_cast hmul
  have hGr : (Nat.card (GL (Fin r) κ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hGs : (Nat.card (GL (Fin s) κ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  rw [card_GL_real] at hGr hGs
  rw [card_GL_real, card_GL_real, card_GL_real] at hR
  have hq : (Nat.card κ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hPr := right_ne_zero_of_mul hGr
  have hPs := right_ne_zero_of_mul hGs
  rw [eq_div_iff (mul_ne_zero hPr hPs)]
  have key : (r + s) * (r + s) = r * r + s * s + r * s + r * s := by ring
  rw [key, pow_add, pow_add, pow_add] at hR
  have hX : (Nat.card κ : ℝ) ^ (r * r) * (Nat.card κ : ℝ) ^ (s * s) * (Nat.card κ : ℝ) ^ (r * s) ≠ 0 := by
    have := pow_ne_zero (r * r) hq; have := pow_ne_zero (s * s) hq; have := pow_ne_zero (r * s) hq
    positivity
  apply mul_right_cancel₀ hX
  linear_combination hR

end GlobalTheory.ParabIndex
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSchwartzAOfIsSchwartzBruhat
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SchwartzBruhatTensor

variable {D : D7}

theorem exists_finSection (D : D7) :
    ∃ s : (Af D.host.F ⊗[D.host.F] D.host.E) →+ AE D, Continuous s ∧ (∀ a, finPart D (s a) = a) ∧
      ∀ a, infPart D (s a) = 0 := by
  obtain ⟨e, he, -, hec⟩ : ∃ e : AE D ≃+* (Ainf D.host.F ⊗[D.host.F] D.host.E) × (Af D.host.F ⊗[D.host.F] D.host.E),
      (∀ z, (e z).1 = infPart D z ∧ (e z).2 = finPart D z) ∧ Continuous e ∧ Continuous e.symm :=
    GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  refine ⟨e.symm.toAddEquiv.toAddMonoidHom.comp (AddMonoidHom.inr _ _), hec.comp (continuous_const.prodMk continuous_id),
    fun a => ?_, fun a => ?_⟩
  · have := (he (e.symm (0, a))).2
    rw [RingEquiv.apply_symm_apply] at this
    exact this.symm
  · have := (he (e.symm (0, a))).1
    rw [RingEquiv.apply_symm_apply] at this
    exact this.symm

theorem isOpen_intAE (D : D7) : IsOpen (intAE D : Set (Af D.host.F ⊗[D.host.F] D.host.E)) := by
  have := GlobalTheory.IdeleParts.isOpen_nsmul_adelicCompletion_integers D.host.F D.host.E 1 one_pos
  rw [← GlobalTheory.IdeleParts.integralFiniteAdeles_eq_adelicCompletion_integers] at this
  have hs : (intAE D : Set (Af D.host.F ⊗[D.host.F] D.host.E)) = {z | ∃ y ∈ intAE D, z = 1 • y} := by
    ext z
    constructor
    · intro h
      exact ⟨z, h, (one_nsmul z).symm⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  rw [hs]
  exact this

theorem isCompact_intAE (D : D7) : IsCompact (intAE D : Set (Af D.host.F ⊗[D.host.F] D.host.E)) := by
  haveI : IsModuleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (Af D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (Af D.host.F) _
  obtain ⟨C, hC, hCd⟩ := GlobalTheory.SmoothForms.Cover.exists_compact_denom D 1 one_pos
  exact hC.of_isClosed_subset (AddSubgroup.isClosed_of_isOpen _ (isOpen_intAE D)) fun y hy => hCd y (by simpa using hy)

end GlobalTheory.SchwartzBruhatTensor

namespace GlobalTheory.SchwartzBruhatTensor

variable {D : D7}

def chartM (σ : (D.what₂.Tau → ℂ) →+ AE D) (m n : ℕ) : (D.what₂.Tau → Fin m → Fin n → ℂ) →+ Mx D m n where
  toFun c := Matrix.of fun i j => σ fun τ => c τ i j
  map_zero' := by
    funext i j
    show σ (fun τ => (0 : D.what₂.Tau → Fin m → Fin n → ℂ) τ i j) = 0
    exact σ.map_zero
  map_add' c c' := by
    funext i j
    show σ (fun τ => (c + c') τ i j) = σ (fun τ => c τ i j) + σ (fun τ => c' τ i j)
    exact σ.map_add _ _

theorem continuous_chartM {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : Continuous σ) (m n : ℕ) :
    Continuous (chartM σ m n) :=
  continuous_pi fun i => continuous_pi fun j => hσ.comp (continuous_pi fun τ =>
    (continuous_apply j).comp ((continuous_apply i).comp (continuous_apply τ)))

theorem compAt_chartM {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ) {m n : ℕ}
    (c : D.what₂.Tau → Fin m → Fin n → ℂ) (τ : D.what₂.Tau) (i : Fin m) (j : Fin n) :
    compAt θ τ (chartM σ m n c) i j = c τ i j :=
  hσ.comp (fun τ => c τ i j) τ

theorem finPart_chartM {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ) {m n : ℕ}
    (c : D.what₂.Tau → Fin m → Fin n → ℂ) : (chartM σ m n c).map (finPart D) = 0 := by
  funext i j
  exact hσ.fin _

theorem decomp {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ)
    {s : (Af D.host.F ⊗[D.host.F] D.host.E) →+ AE D} (hsf : ∀ a, finPart D (s a) = a) (hsi : ∀ a, infPart D (s a) = 0)
    {m n : ℕ} (y : Mx D m n) :
    y = s.mapMatrix (y.map (finPart D)) + chartM σ m n (fun τ i j => compAt θ τ y i j) := by
  funext i j
  refine sub_eq_zero.1 (hσ.ext _ ?_ fun τ => ?_)
  · show finPart D (y i j - (s (finPart D (y i j)) + σ fun τ => compAt θ τ y i j)) = 0
    rw [RingHom.map_sub, RingHom.map_add, hsf, hσ.fin, add_zero, sub_self]
  · show θ τ (infPart D (y i j - (s (finPart D (y i j)) + σ fun τ => compAt θ τ y i j))) = 0
    rw [RingHom.map_sub, RingHom.map_add, RingHom.map_sub, RingHom.map_add, hsi, hσ.comp, RingHom.map_zero, zero_add]
    exact sub_self _

end GlobalTheory.SchwartzBruhatTensor

namespace GlobalTheory.SchwartzBruhatTensor

variable {D : D7}

open Classical in

theorem coset_mem_SB {m n : ℕ} (W : AddSubgroup (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E)))
    (hWo : IsOpen (W : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))))
    (hWc : IsCompact (W : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))))
    (q : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) ⧸ W) :
    (fun a : Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E =>
      if (QuotientAddGroup.mk (show Matrix (Fin m) (Fin n) _ from a) : _ ⧸ W) = q then (1 : ℂ) else 0) ∈
      GlobalTheory.WeilM.SB (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) := by
  haveI : IsModuleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (Af D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (Af D.host.F) _
  have hmk : IsLocallyConstant
      (fun a : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) => (a : _ ⧸ W)) := by
    refine (IsLocallyConstant.iff_exists_open _).2 fun x => ⟨{b | -b + x ∈ W},
      hWo.preimage (continuous_neg.add continuous_const), by simp, fun b hb => QuotientAddGroup.eq.2 hb⟩
  refine ⟨hmk.comp fun q' => if q' = q then (1 : ℂ) else 0, ?_⟩
  have hcl : IsClosed (W : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) :=
    AddSubgroup.isClosed_of_isOpen _ hWo
  let K : Set (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) :=
    (fun b : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) => q.out + b) '' (W : Set _)
  have hKc : IsCompact K := hWc.image (continuous_const.add continuous_id)
  have hKcl : IsClosed K := (Homeomorph.addLeft q.out).isClosedMap _ hcl
  refine HasCompactSupport.intro' hKc hKcl fun x hx => ?_
  show (if (QuotientAddGroup.mk (show Matrix (Fin m) (Fin n) _ from x) : _ ⧸ W) = q then (1 : ℂ) else 0) = 0
  rw [if_neg]
  intro hq
  apply hx
  have h1 : (QuotientAddGroup.mk q.out : _ ⧸ W) = QuotientAddGroup.mk (show Matrix (Fin m) (Fin n) _ from x) := by
    rw [hq, QuotientAddGroup.out_eq']
  exact ⟨-q.out + (show Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) from x), QuotientAddGroup.eq.1 h1,
    add_neg_cancel_left _ _⟩

end GlobalTheory.SchwartzBruhatTensor

namespace GlobalTheory.SchwartzBruhatTensor

open Classical in

theorem mem_schwartzA_of_isSchwartzBruhat : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n : ℕ) (φ : Mx D m n → ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ → φ ∈ GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA θ m n := by
  intro D θ hθ m n φ hφ
  haveI : IsModuleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (Af D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (Af D.host.F) _
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨s, hsc, hsf, hsi⟩ := exists_finSection D
  obtain ⟨U, hUo, hU⟩ := hφ.level
  obtain ⟨K, hK, hKs⟩ := hφ.supp
  let S : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) →+ Mx D m n := s.mapMatrix
  have hSc : Continuous S := continuous_id.matrix_map hsc
  have hSi : ∀ a, (S a).map (infPart D) = 0 := fun a => by
    funext i j
    exact hsi (a i j)
  let W : AddSubgroup (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E)) :=
    { carrier := {a | S a ∈ U ∧ ∀ i j, a i j ∈ intAE D}
      add_mem' := fun {a b} ha hb => ⟨by rw [S.map_add]; exact U.add_mem ha.1 hb.1,
        fun i j => (intAE D).add_mem (ha.2 i j) (hb.2 i j)⟩
      zero_mem' := ⟨by rw [S.map_zero]; exact U.zero_mem, fun _ _ => (intAE D).zero_mem⟩
      neg_mem' := fun {a} ha => ⟨by rw [S.map_neg]; exact U.neg_mem ha.1, fun i j => (intAE D).neg_mem (ha.2 i j)⟩ }
  have hWe : (W : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) =
      S ⁻¹' U ∩ ⋂ i, ⋂ j, (fun a : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) => a i j) ⁻¹'
        (intAE D : Set (Af D.host.F ⊗[D.host.F] D.host.E)) := by
    ext a
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_iInter, SetLike.mem_coe]
    rfl
  have hWo : IsOpen (W : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) := by
    rw [hWe]
    exact (hUo.preimage hSc).inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (isOpen_intAE D).preimage ((continuous_apply j).comp (continuous_apply i)))
  have hcl : IsClosed (W : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) :=
    AddSubgroup.isClosed_of_isOpen _ hWo
  have hbig : IsCompact {a : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) | ∀ i j, a i j ∈ intAE D} :=
    isCompact_pi_infinite fun _ => isCompact_pi_infinite fun _ => isCompact_intAE D
  have hWc : IsCompact (W : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) :=
    hbig.of_isClosed_subset hcl fun a ha => ha.2
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun a : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) => {b | -a + b ∈ W})
    (fun a => hWo.preimage (continuous_const.add continuous_id))
    (fun b _ => Set.mem_iUnion.2 ⟨b, show -b + b ∈ W by rw [neg_add_cancel]; exact W.zero_mem⟩)
  let T : Finset (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) ⧸ W) := t.image QuotientAddGroup.mk
  let k := Module.finrank ℝ (D.what₂.Tau → Fin m → Fin n → ℂ)
  let eZ : (D.what₂.Tau → Fin m → Fin n → ℂ) ≃L[ℝ] (Fin k → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℝ).symm
  let L : (Fin k → ℝ) →+ Mx D m n := (chartM σ m n).comp eZ.symm.toLinearEquiv.toAddEquiv.toAddMonoidHom
  have hL : GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsRealParam L :=
    ⟨(continuous_chartM hσ.cont m n).comp eZ.symm.continuous, fun t => finPart_chartM hσ _⟩
  have hLi : Function.Injective L := by
    intro t t' h
    apply eZ.symm.injective
    funext τ i j
    have e := congrArg (fun y => compAt θ τ y i j) h
    simp only [L, AddMonoidHom.coe_comp, Function.comp_apply] at e
    rw [compAt_chartM hσ, compAt_chartM hσ] at e
    exact e
  choose g hg using fun q : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) ⧸ W =>
    hφ.schwartz k L hL hLi (S q.out)
  let f : (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) ⧸ W) →
      SchwartzMap (D.what₂.Tau → Fin m → Fin n → ℂ) ℂ :=
    fun q => SchwartzMap.compCLMOfContinuousLinearEquiv ℂ eZ (g q)
  have hf : ∀ q c, f q c = φ (S q.out + chartM σ m n c) := fun q c => by
    show g q (eZ c) = _
    rw [hg q (eZ c)]
    congr 2
    show chartM σ m n (eZ.symm (eZ c)) = _
    rw [ContinuousLinearEquiv.symm_apply_apply]
  let gf : (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) ⧸ W) →
      (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ := fun q a =>
    if (QuotientAddGroup.mk (show Matrix (Fin m) (Fin n) _ from a) : _ ⧸ W) = q then (1 : ℂ) else 0
  have key : φ = ∑ q ∈ T, fun x : Mx D m n =>
      f q (fun τ i j => compAt θ τ x i j) * gf q (fun i j => finPart D (x i j)) := by
    funext y
    rw [Finset.sum_apply]
    let a : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) := fun i j => finPart D (y i j)
    let c : D.what₂.Tau → Fin m → Fin n → ℂ := fun τ i j => compAt θ τ y i j
    have hdec : y = S a + chartM σ m n c := decomp hσ hsf hsi y
    show φ y = ∑ q ∈ T, f q c * (if (QuotientAddGroup.mk a : _ ⧸ W) = q then (1 : ℂ) else 0)
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    split_ifs with hT
    · rw [hf]
      have hmem : -(QuotientAddGroup.mk a : _ ⧸ W).out + a ∈ W := QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' _)
      have e := hU (S (-(QuotientAddGroup.mk a : _ ⧸ W).out + a)) hmem.1 (hSi _)
        (S (QuotientAddGroup.mk a : _ ⧸ W).out + chartM σ m n c)
      rw [← e]
      conv_lhs => rw [hdec]
      congr 1
      rw [S.map_add, S.map_neg]
      abel
    · by_contra hne
      obtain ⟨b, hb, hab⟩ := Set.mem_iUnion₂.1 (ht (hKs y hne))
      have hba : (QuotientAddGroup.mk b : _ ⧸ W) = QuotientAddGroup.mk a := QuotientAddGroup.eq.2 hab
      exact hT (Finset.mem_image.2 ⟨b, hb, hba⟩)
  rw [key]
  exact Submodule.sum_mem _ fun q _ => Submodule.subset_span ⟨f q, gf q, coset_mem_SB W hWo hWc q, rfl⟩

end GlobalTheory.SchwartzBruhatTensor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NatCastNotMemUnderSq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open NumberField IsDedekindDomain Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.SplitDegOneChar

theorem absNorm_under {E F : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [Algebra (𝓞 F) (𝓞 E)] [Algebra.IsIntegral (𝓞 F) (𝓞 E)]
    (PP : HeightOneSpectrum (𝓞 E)) (p : ℕ) (hp : p.Prime) (hPP : Ideal.absNorm PP.asIdeal = p) :
    Ideal.absNorm (PP.under (𝓞 F)).asIdeal = p := by
  set v := PP.under (𝓞 F) with hvdef
  have hle : v.asIdeal ≤ PP.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) := le_rfl
  haveI := v.isMaximal
  haveI := PP.isMaximal
  letI := Ideal.Quotient.field v.asIdeal
  letI : Algebra (𝓞 F ⧸ v.asIdeal) (𝓞 E ⧸ PP.asIdeal) := Ideal.Quotient.algebraQuotientOfLEComap hle
  have hE : Nat.card (𝓞 E ⧸ PP.asIdeal) = p := by rw [← hPP, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 E ⧸ PP.asIdeal) := Nat.finite_of_card_ne_zero (by rw [hE]; exact hp.ne_zero)
  haveI : Module.Finite (𝓞 F ⧸ v.asIdeal) (𝓞 E ⧸ PP.asIdeal) := Module.Finite.of_finite
  have h := Module.natCard_eq_pow_finrank (K := 𝓞 F ⧸ v.asIdeal) (V := 𝓞 E ⧸ PP.asIdeal)
  rw [hE] at h
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact ((hp.pow_eq_iff).1 h.symm).1

theorem natCast_not_mem_under_sq {E F : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra (𝓞 F) (𝓞 E)] [Algebra.IsIntegral (𝓞 F) (𝓞 E)]
    (PP : HeightOneSpectrum (𝓞 E)) (p : ℕ) (hsq : (p : 𝓞 E) ∉ PP.asIdeal ^ 2) :
    (p : 𝓞 F) ∉ (PP.under (𝓞 F)).asIdeal ^ 2 := by
  intro h
  apply hsq
  have h1 := Ideal.mem_map_of_mem (algebraMap (𝓞 F) (𝓞 E)) h
  rw [Ideal.map_pow, map_natCast] at h1
  exact Ideal.pow_right_mono (Ideal.map_comap_le) 2 h1

end GlobalTheory.SplitDegOneChar

namespace GlobalTheory.SplitDegOneChar

theorem psiE_sec_pr_eq_exp : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E) (p : ℕ), p.Prime → Ideal.absNorm PP.asIdeal = p → ((p : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal ^ 2 → q.v = PP.under (𝓞 D.host.F) → (∀ x, (ofSplit q).pr x ∈ 𝒪[k] ↔ Formalism.L2.Col.IntAt PP x) → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (x : D.host.E) (b : ℤ), Formalism.L2.Col.IntAt PP (x - (b : D.host.E) / (p : D.host.E)) → psiE ψ (q.sec ((ofSplit q).pr x)) = Complex.exp (2 * Real.pi * Complex.I * b / (p : ℂ)) := by
  intro D k _ _ _ _ q PP p hp hPP hsq hv hint ψ hψ x b hx
  have hpr : ∀ y : D.host.E, (ofSplit q).pr y = q.pr (incA D y) := fun _ => rfl
  set c : D.host.F := (b : D.host.F) / (p : D.host.F) with hcdef
  have hc : algebraMap D.host.F D.host.E c = (b : D.host.E) / (p : D.host.E) := by
    rw [hcdef, map_div₀, map_intCast, map_natCast]
  have hxs : x = (x - (b : D.host.E) / (p : D.host.E)) + algebraMap D.host.F D.host.E c := by
    rw [hc]; ring
  have hadd : ∀ u w : AE D, psiE ψ (u + w) = psiE ψ u * psiE ψ w := by
    intro u w; simp only [GlobalTheory.MixPer.psiE, map_add, AddChar.map_add_eq_mul]
  rw [hxs, hpr, map_add, map_add, map_add, hadd]

  have hy : q.pr (incA D (x - (b : D.host.E) / (p : D.host.E))) ∈ 𝒪[k] := by
    rw [← hpr]; exact (hint _).2 hx
  have h1 : psiE ψ (q.sec (q.pr (incA D (x - (b : D.host.E) / (p : D.host.E))))) = 1 := by
    rw [GlobalTheory.MixPer.psiE, GlobalTheory.SplitCharCond.trace_sec q, GlobalTheory.SplitCharCond.snd_trace,
      GlobalTheory.SplitCharCond.char_int hψ (GlobalTheory.SplitCharCond.trace_int ((q.int_iff _).1 hy))]
  rw [h1, one_mul]

  obtain ⟨ε, hε, he⟩ := q.above
  have htr : Algebra.trace (AF D.host.F) (AE D) q.e = ε := by
    refine Algebra.TensorProduct.includeLeft_injective (S := AF D.host.F) (algebraMap D.host.F D.host.E).injective ?_
    change algebraMap (AF D.host.F) (AE D) _ = algebraMap (AF D.host.F) (AE D) _
    rw [GlobalTheory.FockCompare.SymplVal.trace_AE, he]
  have hinc : incA D (algebraMap D.host.F D.host.E c) =
      algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) c) := GlobalTheory.SplitCharCond.one_tmul_eq c
  rw [q.sec_pr, hinc, mul_comm, ← Algebra.smul_def, GlobalTheory.MixPer.psiE, map_smul, smul_eq_mul, htr, mul_comm]
  have hnorm : Ideal.absNorm q.v.asIdeal = p := by rw [hv]; exact absNorm_under PP p hp hPP
  have hsqv : (p : 𝓞 D.host.F) ∉ q.v.asIdeal ^ 2 := by rw [hv]; exact natCast_not_mem_under_sq PP p hsq
  have key := GlobalTheory.StdCharDegOne.stdChar_placeIdem_div D ψ hψ p hp q.v hnorm hsqv ε hε (b : 𝓞 D.host.F) b
    (by rw [sub_self]; exact zero_mem _)
  rw [← key, hcdef]
  push_cast
  rfl

end GlobalTheory.SplitDegOneChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalIsometryNormalisesIsotropicUnipotentRadiStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.Dich
open Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_isometry_normalises_isotropic_unipotent_radical : ∀ (D : D7) (V : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E), ∀ δ ∈ GQ V, ∀ δ₀ : Matrix (Fin V.rank) (Fin V.rank) D.host.E, (matHom V δ).1 = δ₀.map (incA D) → ∀ G : Matrix (Fin r) (Fin r) D.host.E, IsUnit G → δ₀ * C = C * G → ∀ n ∈ NI V C, δ * n * δ⁻¹ ∈ NI V C := by
  first | exact @GlobalTheory.FrameNorm.norm | exact GlobalTheory.FrameNorm.norm | (intros; apply GlobalTheory.FrameNorm.norm <;> assumption)
end

