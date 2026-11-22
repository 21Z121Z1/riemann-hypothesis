import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.Bundle0001
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.MirabolicInduction.LinearIndependentRealOfInt
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Objects

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PReducedBasisBound
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open Module Submodule Matrix GroundTheory.Heights₂.Theta.FunctionalEquationAlt.ShortGen

noncomputable section

theorem ReducedBasisBound.short_basis {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] (m : ℕ) : ∀ lam : ℝ, 0 < lam → ∀ C : ℝ, ∃ R : ℝ,
    ∀ b : Fin m → W, LinearIndependent ℝ b → Sep (span ℤ (Set.range b)) lam →
      (gram ℝ b).det ≤ C → ∃ b' : Fin m → W, span ℤ (Set.range b') = span ℤ (Set.range b) ∧
        ∀ i, ‖b' i‖ ≤ R := by
  induction m with
  | zero => exact fun _ _ _ => ⟨0, fun b _ _ _ => ⟨b, rfl, fun i => i.elim0⟩⟩
  | succ m ih =>
    intro lam hlam C
    obtain ⟨g, hg, hgb⟩ := (bounds (W := W) m).1 (lam / 2) (half_pos hlam)
    obtain ⟨R', hR'⟩ := ih (lam / 2) (half_pos hlam) (C / lam ^ 2)
    refine ⟨|R'| + Real.sqrt (C / g), fun b hb hsep hC => ?_⟩
    obtain ⟨v, c, hvL, hv, hlv, hmin, hc, hmemc, hsepc, hdet⟩ := decompose b hb hlam hsep
    have hgc := hgb c hc hsepc
    have hv2 : ‖v‖ ^ 2 ≤ C / g := by
      rw [le_div_iff₀ hg]
      nlinarith [mul_le_mul_of_nonneg_left hgc (sq_nonneg ‖v‖)]
    have hvR : ‖v‖ ≤ Real.sqrt (C / g) := (le_abs_self _).trans (Real.abs_le_sqrt hv2)
    have hcC : (gram ℝ c).det ≤ C / lam ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      have h2 : lam ^ 2 ≤ ‖v‖ ^ 2 := pow_le_pow_left₀ hlam.le hlv 2
      nlinarith [hg.le.trans hgc]
    obtain ⟨c', hc'span, hc'R⟩ := hR' c hc hsepc hcC
    set L := span ℤ (Set.range b) with hL
    have hlift : ∀ i, ∃ y ∈ L, proj v y = c' i ∧ ‖y‖ ≤ ‖c' i‖ + ‖v‖ / 2 := by
      intro i
      have hci : c' i ∈ span ℤ (Set.range c) := hc'span ▸ subset_span ⟨i, rfl⟩
      obtain ⟨x, hx, hxe⟩ := (hmemc _).1 hci
      obtain ⟨y, hyL, hy, hyn⟩ := exists_lift hvL hv hx
      exact ⟨y, hyL, hy.trans hxe, hxe ▸ hyn⟩
    choose y hyL hy hyn using hlift
    refine ⟨Fin.cons v y, le_antisymm ?_ ?_, fun i => ?_⟩
    · rw [span_le]
      rintro _ ⟨i, rfl⟩
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hvL
      · simpa using hyL j
    · intro x hx
      obtain ⟨k, hk⟩ := (mem_span_range_iff_exists_fun ℤ).1
        (hc'span ▸ (hmemc (proj v x)).2 ⟨x, hx, rfl⟩)
      have hzL : ∑ j, k j • y j ∈ L := L.sum_mem fun j _ => L.smul_mem _ (hyL j)
      have h0 : proj v (x - ∑ j, k j • y j) = 0 := by
        rw [map_sub, map_sum, ← hk, sub_eq_zero]
        simp [map_zsmul, hy]
      obtain ⟨n, hn⟩ := mem_zsmul_of_proj_eq_zero hvL hv hmin (L.sub_mem hx hzL) h0
      have hxe : x = n • v + ∑ j, k j • y j := by rw [← hn]; abel
      rw [hxe]
      refine add_mem (smul_mem _ _ (subset_span ⟨0, by simp⟩))
        (sum_mem fun j _ => smul_mem _ _ (subset_span ⟨j.succ, by simp⟩))
    · have hs := Real.sqrt_nonneg (C / g)
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Fin.cons_zero]
        linarith [abs_nonneg R']
      · simp only [Fin.cons_succ]
        linarith [hyn j, hc'R j, le_abs_self R']

theorem ReducedBasisBound.proof : ReducedBasisBound.Statement := by
  intro d t c ht
  obtain ⟨R, hR⟩ := ReducedBasisBound.short_basis (W := EuclideanSpace ℝ (Fin d)) d t ht (c ^ 2)
  refine ⟨R, fun L _ _ hmin hcov => ?_⟩
  have hrk : finrank ℤ L = d := by rw [ZLattice.rank ℝ L, finrank_euclideanSpace_fin]
  let e : Basis (Fin d) ℤ L := Module.finBasisOfFinrankEq ℤ L hrk
  have hspan : span ℤ (Set.range fun i => (e i : EuclideanSpace ℝ (Fin d))) = L := by
    rw [show (Set.range fun i => (e i : EuclideanSpace ℝ (Fin d))) = L.subtype '' Set.range e by
      rw [← Set.range_comp]; rfl, ← Submodule.map_span, e.span_eq, Submodule.map_top,
      Submodule.range_subtype]
  have hli : LinearIndependent ℝ fun i => (e i : EuclideanSpace ℝ (Fin d)) := by
    have h := (e.ofZLatticeBasis ℝ L).linearIndependent
    rwa [show ⇑(e.ofZLatticeBasis ℝ L) = fun i => (e i : EuclideanSpace ℝ (Fin d)) from
      funext fun i => e.ofZLatticeBasis_apply ℝ L i] at h
  have hdet : (gram ℝ fun i => (e i : EuclideanSpace ℝ (Fin d))).det ≤ c ^ 2 := by
    have h1 := GroundTheory.Heights₂.Heights.covolume_eq_sqrt_det_gram L e
    rcases le_or_gt 0 (gram ℝ fun i => (e i : EuclideanSpace ℝ (Fin d))).det with h | h
    · rw [← Real.sq_sqrt h, ← h1]
      exact pow_le_pow_left₀ (ZLattice.covolume_pos L).le hcov 2
    · nlinarith [sq_nonneg c]
  have hsep : Sep (span ℤ (Set.range fun i => (e i : EuclideanSpace ℝ (Fin d)))) t := by
    rw [hspan]; exact hmin
  obtain ⟨b', hb'span, hb'R⟩ := hR _ hli hsep hdet
  rw [hspan] at hb'span
  have htop : ⊤ ≤ span ℝ (Set.range b') := by
    rw [← IsZLattice.span_top (K := ℝ) (L := L), ← hb'span, Submodule.span_span_of_tower]
  have hliR : LinearIndependent ℝ b' :=
    linearIndependent_of_top_le_span_of_card_eq_finrank htop (by simp)
  refine ⟨(Basis.span (hliR.restrict_scalars' ℤ)).map (LinearEquiv.ofEq _ _ hb'span), fun i => ?_⟩
  simpa using hb'R i

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.ReindexBasis
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FiniteCovolume.Reindex

open NumberField GroundTheory.Automorphic Module Matrix Topology
open scoped ComplexOrder

noncomputable section

set_option linter.unusedSectionVars false

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def reGL (e : ι ≃ κ) : GL ι ℂ →* GL κ ℂ :=
  Units.map (Matrix.reindexRingEquiv ℂ e).toMonoidHom

theorem coe_reGL (e : ι ≃ κ) (g : GL ι ℂ) :
    ((reGL e g : GL κ ℂ) : Matrix κ κ ℂ) = reindex e e (g : Matrix ι ι ℂ) := rfl

theorem reGL_symm_reGL (e : ι ≃ κ) (g : GL ι ℂ) : reGL e.symm (reGL e g) = g := by
  ext i j
  simp [coe_reGL, Matrix.reindex_apply]

theorem reGL_reGL_symm (e : ι ≃ κ) (g : GL κ ℂ) : reGL e (reGL e.symm g) = g := by
  ext i j
  simp [coe_reGL, Matrix.reindex_apply]

theorem continuous_reGL (e : ι ≃ κ) : Continuous (reGL e) :=
  Units.continuous_map (continuous_id.matrix_reindex e e)

theorem reGL_mem_unitary (e : ι ≃ κ) (s : ℂ →+* ℂ) (H : Matrix ι ι ℂ) (g : GL ι ℂ) :
    reGL e g ∈ unitaryGroupMatrix s (reindex e e H) ↔ g ∈ unitaryGroupMatrix s H := by
  rw [mem_unitaryGroupMatrix, mem_unitaryGroupMatrix, coe_reGL]
  have : ((reindex e e (g : Matrix ι ι ℂ)).map s)ᵀ * reindex e e H * reindex e e (g : Matrix ι ι ℂ) =
      reindex e e (((g : Matrix ι ι ℂ).map s)ᵀ * H * (g : Matrix ι ι ℂ)) := by
    simp only [Matrix.reindex_apply]
    rw [← Matrix.submatrix_map, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_mul_equiv]
  rw [this, (reindex e e).injective.eq_iff]

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

theorem gramAt_reindex (h : HermitianForm F E W) (v : Basis ι E W) (e : ι ≃ κ)
    (w : InfinitePlace E) : gramAt h (v.reindex e) w = reindex e e (gramAt h v w) := by
  ext i j
  simp [gramAt, Automorphic.gram_apply, Basis.reindex_apply, Matrix.reindex_apply]

theorem vecAt_reindex (v : Basis ι E W) (e : ι ≃ κ) (x : W) :
    vecAt (v.reindex e) x = fun w => vecAt v x w ∘ e.symm := by
  funext w i
  simp [vecAt]

variable [NumberField E]

def archReindex (h : HermitianForm F E W) (v : Basis ι E W) (e : ι ≃ κ) :
    archUnitary h v →* archUnitary h (v.reindex e) where
  toFun g := ⟨fun w => reGL e ((g : InfinitePlace E → GL ι ℂ) w), (Subgroup.mem_pi _).2 fun w _ => by
    rw [gramAt_reindex, reGL_mem_unitary]
    exact (Subgroup.mem_pi _).1 g.2 w trivial⟩
  map_one' := by
    ext w : 2
    simp
  map_mul' a b := by
    ext w : 2
    simp

def archReindexBack (h : HermitianForm F E W) (v : Basis ι E W) (e : ι ≃ κ) :
    archUnitary h (v.reindex e) →* archUnitary h v where
  toFun g := ⟨fun w => reGL e.symm ((g : InfinitePlace E → GL κ ℂ) w),
    (Subgroup.mem_pi _).2 fun w _ => by
      rw [← reGL_mem_unitary e, reGL_reGL_symm, ← gramAt_reindex]
      exact (Subgroup.mem_pi _).1 g.2 w trivial⟩
  map_one' := by
    ext w : 2
    simp
  map_mul' a b := by
    ext w : 2
    simp

theorem archReindexBack_archReindex (h : HermitianForm F E W) (v : Basis ι E W) (e : ι ≃ κ)
    (g : archUnitary h v) : archReindexBack h v e (archReindex h v e g) = g := by
  apply Subtype.ext
  funext w
  exact reGL_symm_reGL e _

theorem continuous_archReindexBack (h : HermitianForm F E W) (v : Basis ι E W) (e : ι ≃ κ) :
    Continuous (archReindexBack h v e) :=
  Continuous.subtype_mk (continuous_pi fun w =>
    (continuous_reGL e.symm).comp ((continuous_apply w).comp continuous_subtype_val)) _

theorem invApply_reindex {h : HermitianForm F E W} {v : Basis ι E W} (e : ι ≃ κ)
    (g : archUnitary h v) (y : InfinitePlace E → ι → ℂ) :
    invApply (archReindex h v e g) (fun w => y w ∘ e.symm) = fun w => invApply g y w ∘ e.symm := by
  funext w
  rw [invApply, invApply, ← map_inv]
  change (reindex e e _) *ᵥ (y w ∘ e.symm) = _
  rw [Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv, Function.comp_assoc, Equiv.symm_symm,
    Equiv.symm_comp_self, Function.comp_id]

def majReindex {h : HermitianForm F E W} {v : Basis ι E W} (e : ι ≃ κ) (M : Majorant h v) :
    Majorant h (v.reindex e) where
  P w := Matrix.reindex e e (M.P w)
  posDef w := by
    rw [Matrix.reindex_apply]
    exact (M.posDef w).submatrix e.symm.injective
  siegel w := by
    rw [gramAt_reindex, Matrix.inv_reindex]
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
    rw [M.siegel w]

theorem len_majReindex {h : HermitianForm F E W} {v : Basis ι E W} (e : ι ≃ κ)
    (M : Majorant h v) (y : InfinitePlace E → ι → ℂ) :
    (majReindex e M).len (fun w => y w ∘ e.symm) = M.len y := by
  unfold Majorant.len
  congr 1
  refine Finset.sum_congr rfl fun w _ => ?_
  congr 1
  change star (y w ∘ e.symm) ⬝ᵥ (Matrix.reindex e e (M.P w) *ᵥ (y w ∘ e.symm)) =
    star (y w) ⬝ᵥ (M.P w *ᵥ y w)
  rw [Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv, Function.comp_assoc, Equiv.symm_symm,
    Equiv.symm_comp_self, Function.comp_id]
  simp only [dotProduct, Function.comp_apply, Pi.star_apply]
  exact Equiv.sum_comp e.symm (fun i => star (y w i) * (M.P w *ᵥ y w) i)

theorem len_invApply_reindex {h : HermitianForm F E W} {v : Basis ι E W} (e : ι ≃ κ)
    (M : Majorant h v) (g : archUnitary h v) (x : W) :
    (majReindex e M).len (invApply (archReindex h v e g) (vecAt (v.reindex e) x)) =
      M.len (invApply g (vecAt v x)) := by
  rw [vecAt_reindex, invApply_reindex, len_majReindex]

variable [NumberField F] [IsTotallyReal F] [IsTotallyComplex E]

theorem archReindex_archEmbed (h : HermitianForm F E W) (v : Basis ι E W) (e : ι ≃ κ)
    (γ : h.unitaryGroup) : archReindex h v e (archEmbed h v γ) = archEmbed h (v.reindex e) γ := by
  apply Subtype.ext
  funext w
  ext i j
  change reindex e e ((Matrix.GeneralLinearGroup.map w.embedding
      (unitaryGroupEquivMatrix h v γ : GL ι E) : GL ι ℂ) : Matrix ι ι ℂ) i j =
    ((Matrix.GeneralLinearGroup.map w.embedding
      (unitaryGroupEquivMatrix h (v.reindex e) γ : GL κ E) : GL κ ℂ) : Matrix κ κ ℂ) i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.GeneralLinearGroup.map_apply]
  congr 1
  rw [unitaryGroupEquivMatrix_apply, unitaryGroupEquivMatrix_apply, LinearMap.toMatrix_apply,
    LinearMap.toMatrix_apply, Basis.reindex_apply, Basis.repr_reindex_apply]

end

end GroundTheory.Heights₂.Heights.FiniteCovolume.Reindex
end

