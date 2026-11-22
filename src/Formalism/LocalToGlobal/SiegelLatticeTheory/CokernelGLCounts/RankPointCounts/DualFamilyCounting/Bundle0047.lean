import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0045
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0046
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0032
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.OneMemZpowZero
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.HTAaLbMem
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibAlg
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0043
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.GenusMassPosOfMassLowerBound
import Formalism.HermitianLattices.HermitianLatticesProofs.Bundle0001
import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeGluingRadicals

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GlueExistsHolds
section
namespace Formalism.L2.SG.Pf.Cnt

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem glueExists_holds : GlueExists :=
  glueExists_of_last last_unit_holds

end Formalism.L2.SG.Pf.Cnt
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GluingMassHolds
section
namespace Formalism.L2.SG.Pf.Cnt

theorem gluing_mass_holds : GlueMass :=
  glueMass_of' jordan_splitting_exists jordan_invariants_holds alpha_discriminant_holds local_gluing_holds gluing_product_holds

end Formalism.L2.SG.Pf.Cnt
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.IsoGenLeft
section
noncomputable section

open NumberField Formalism.BasicNotions Matrix
open scoped BigOperators

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf.Ex

open Formalism.L2.SG.HidaSetting Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX.NOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (xs : Fin D.R.rS → (VS D).V)
  (M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E)

theorem h_e_nLw (hxs : ∀ b, InW X (xs b)) {w : (VS D).V} (hw : InW X w) (c : Fin D.R.rS) :
    (VS D).hT (X.eX c) (nL X X0 xs M w) = 0 := by
  rw [nL_w X X0 xs M hw, map_add, h_sum_right]
  simp [(hw c).1, X.ee]

theorem h_f_nLw (hxs : ∀ b, InW X (xs b)) {w : (VS D).V} (hw : InW X w) (c : Fin D.R.rS) :
    (VS D).hT (X.fY c) (nL X X0 xs M w) = (VS D).hT (xs c) w := by
  rw [nL_w X X0 xs M hw, map_add, h_sum_right]
  simp [(hw c).2, h_fe, Finset.sum_ite_eq]

theorem h_xs_nLw (hxs : ∀ b, InW X (xs b)) {w : (VS D).V} (hw : InW X w) (c : Fin D.R.rS) :
    (VS D).hT (xs c) (nL X X0 xs M w) = (VS D).hT (xs c) w := by
  rw [nL_w X X0 xs M hw, map_add, h_sum_right]
  simp [(inW_left X (hxs c) _).1]

theorem g_ew (hxs : ∀ b, InW X (xs b)) {w : (VS D).V} (hw : InW X w) (a : Fin D.R.rS) :
    (VS D).hT (nE X X0 a) (nL X X0 xs M w) = (VS D).hT (X.eX a) w := by
  rw [h_nE_left, (hw a).1]
  simp [h_e_nLw X X0 xs M hxs hw]

theorem g_fw (hxs : ∀ b, InW X (xs b)) {w : (VS D).V} (hw : InW X w) (a : Fin D.R.rS) :
    (VS D).hT (nF X X0 xs M a) (nL X X0 xs M w) = (VS D).hT (X.fY a) w := by
  rw [h_nF_left, (hw a).2]
  simp [h_e_nLw X X0 xs M hxs hw, h_f_nLw X X0 xs M hxs hw, h_xs_nLw X X0 xs M hxs hw]

theorem g_ww (hxs : ∀ b, InW X (xs b)) {w w' : (VS D).V} (hw : InW X w) (hw' : InW X w') :
    (VS D).hT (nL X X0 xs M w) (nL X X0 xs M w') = (VS D).hT w w' := by
  rw [nL_w X X0 xs M hw, nL_w X X0 xs M hw', LinearMap.map_add₂, map_add, map_add, h_sum_left, h_sum_left,
    h_sum_right]
  simp [h_sum_right, (hw' _).1, (inW_left X hw _).1, X.ee]

theorem iso_gen_left (hinv : X0⁻¹ * X0 = 1) (hxs : ∀ b, InW X (xs b)) (hM : M + Mᴴ = -Gp D X0 xs)
    (g : (VS D).V) (hg : ∀ c, (VS D).hT (nL X X0 xs M g) (nL X X0 xs M (X.eX c)) = (VS D).hT g (X.eX c) ∧
      (VS D).hT (nL X X0 xs M g) (nL X X0 xs M (X.fY c)) = (VS D).hT g (X.fY c))
    (hgw : ∀ w, InW X w → (VS D).hT (nL X X0 xs M g) (nL X X0 xs M w) = (VS D).hT g w) (y : (VS D).V) :
    (VS D).hT (nL X X0 xs M g) (nL X X0 xs M y) = (VS D).hT g y := by
  conv_lhs => rw [decomp X y]
  conv_rhs => rw [decomp X y]
  simp only [map_add, map_sum, map_smul, smul_eq_mul]
  rw [hgw _ (inW_pW X y)]
  simp only [(hg _).1, (hg _).2]

end Formalism.L2.SG.Pf.NcReal.JX.NOf.Ex
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.MapInv
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

section Inv

variable (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (hup : ∀ b a : Fin D.R.rS, a < b → X0 b a = 0)
  (hd : ∀ a, X0 a a = 1)

include hup hd

theorem det_one : X0.det = 1 := by
  rw [Matrix.det_of_upperTriangular (fun i j hij => hup i j hij)]
  simp [hd]

theorem inv_mul : X0⁻¹ * X0 = 1 := Matrix.nonsing_inv_mul _ (by rw [det_one X0 hup hd]; exact isUnit_one)

theorem mul_inv : X0 * X0⁻¹ = 1 := Matrix.mul_nonsing_inv _ (by rw [det_one X0 hup hd]; exact isUnit_one)

theorem inv_up : ∀ b a : Fin D.R.rS, a < b → X0⁻¹ b a = 0 := by
  have hU : IsUnit X0.det := by rw [det_one X0 hup hd]; exact isUnit_one
  have hbt : X0.BlockTriangular id := fun i j hij => hup i j hij
  haveI : Invertible X0 := Matrix.invertibleOfIsUnitDet X0 hU
  exact fun b a h => Matrix.blockTriangular_inv_of_blockTriangular hbt h

theorem inv_diag : ∀ a, X0⁻¹ a a = 1 := by
  intro a
  have h := congrFun (congrFun (mul_inv X0 hup hd) a) a
  rw [Matrix.mul_apply, Matrix.one_apply_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ a), hd, one_mul] at h
  have hz : ∑ e ∈ Finset.univ.erase a, X0 a e * X0⁻¹ e a = 0 := by
    refine Finset.sum_eq_zero fun e he => ?_
    rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase he) with h1 | h1
    · rw [hup a e h1, zero_mul]
    · rw [inv_up X0 hup hd e a h1, mul_zero]
  rw [hz, add_zero] at h
  exact h

theorem map_inv' {K : Type*} [Field K] (f : D.host.E →+* K) : (X0.map f)⁻¹ = X0⁻¹.map f := by
  refine Matrix.inv_eq_left_inv ?_
  rw [← Matrix.map_mul, inv_mul X0 hup hd, Matrix.map_one _ f.map_zero f.map_one]

end Inv

theorem gram_mem (xs : Fin D.R.rS → (VS D).V) (hxs : ∀ b, xs b ∈ aaLb X b) (b c : Fin D.R.rS) :
    Gq D xs b c ∈ aaD D b * aaD D c := by
  show (VS D).hT (xs b) (xs c) ∈ aaD D b * aaD D c
  suffices H : ∀ y ∈ Submodule.span (𝓞 D.host.E) {y | ∃ d ∈ (aaD D c : Set D.host.E), ∃ l ∈ X.Lb, y = d • l},
      (VS D).hT (xs b) y ∈ aaD D b * aaD D c from H _ (hxs c)
  intro y hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨d, hdm, l, hl, rfl⟩ := hz
    rw [map_smul, smul_eq_mul, mul_comm d]
    exact FractionalIdeal.mul_mem_mul (LatA.hT_aaLb_mem X (hxs b) hl) hdm
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul o x _ hx =>
    rw [← algebraMap_smul D.host.E o x, map_smul, smul_eq_mul]
    exact LatA.fi_smul_mem hx o

end Formalism.L2.SG.Pf.NcReal.JX.NOf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibLatB
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace LatB

open Alg LatA

variable {D : D7} {X : HidaSetting D} {u : D.what₂.Word} {n : (VS D).V ≃ₗ[D.host.E] (VS D).V}

theorem inW_add {v w : (VS D).V} (hv : InW X v) (hw : InW X w) : InW X (v + w) := fun c =>
  ⟨by rw [map_add, (hv c).1, (hw c).1, add_zero], by rw [map_add, (hv c).2, (hw c).2, add_zero]⟩

theorem inW_sum (s : Finset (Fin D.R.rS)) (c : Fin D.R.rS → D.host.E) (v : Fin D.R.rS → (VS D).V)
    (hv : ∀ d, InW X (v d)) : InW X (∑ d ∈ s, c d • v d) := fun e =>
  ⟨by rw [hT_sumR]; exact Finset.sum_eq_zero fun d _ => by rw [(hv d e).1, mul_zero],
   by rw [hT_sumR]; exact Finset.sum_eq_zero fun d _ => by rw [(hv d e).2, mul_zero]⟩

theorem pW_nf (hn : NFl X u n) (a : Fin D.R.rS) :
    pW X (n (X.fY a)) = -∑ d, Bq (X := X) n d a • xq X n d := by
  set v := pW X (n (X.fY a)) + ∑ d, Bq (X := X) n d a • xq X n d with hv
  have hvW : InW X v := inW_add (pW_inW X _) (inW_sum _ _ _ fun d => xq_inW (X := X) d)
  have horth : ∀ w, InW X w → (VS D).hT v w = 0 := by
    intro w hw
    rw [hv, map_add, LinearMap.add_apply, hT_sumL, omega_rel hn a hw]
    simp only [neg_add_cancel]
  have hall : ∀ y, (VS D).hT v y = 0 := by
    intro y
    rw [decomp X y, map_add, map_add, hT_sumR, hT_sumR, horth _ (pW_inW X y)]
    have h1 : ∀ c, (VS D).hT v (X.eX c) = 0 := fun c => by rw [hsw, (hvW c).1, star_zero]
    have h2 : ∀ c, (VS D).hT v (X.fY c) = 0 := fun c => by rw [hsw, (hvW c).2, star_zero]
    simp only [h1, h2, mul_zero, Finset.sum_const_zero, add_zero]
  have hv0 : v = 0 := (VS D).nondeg.1 v hall
  exact eq_neg_of_add_eq_zero_left hv0

theorem pW_nw (hn : NFl X u n) {w : (VS D).V} (hw : InW X w) : pW X (n w) = w := by
  conv_lhs => rw [nw hn hw]
  rw [pW_add, pW_sum_e, add_zero, pW_of_inW X hw]

theorem pW_sum (s : Finset (Fin D.R.rS)) (c : Fin D.R.rS → D.host.E) (v : Fin D.R.rS → (VS D).V) :
    pW X (∑ d ∈ s, c d • v d) = ∑ d ∈ s, c d • pW X (v d) := by
  induction s using Finset.induction_on with
  | empty => simp [pW]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, pW_add, pW_smul, ih]

theorem inv_up (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (hup : ∀ b a, a < b → X0 b a = 0)
    (hd : ∀ a, X0 a a = 1) : (∀ b a, a < b → X0⁻¹ b a = 0) ∧ ∀ a, X0⁻¹ a a = 1 := by
  have hdet : X0.det = 1 := by
    rw [Matrix.det_of_upperTriangular (fun i j hij => hup i j hij)]
    simp [hd]
  have hU : IsUnit X0.det := by rw [hdet]; exact isUnit_one
  have hXY : X0 * X0⁻¹ = 1 := Matrix.mul_nonsing_inv _ hU
  have hYup : ∀ b a, a < b → X0⁻¹ b a = 0 := by
    have hbt : X0.BlockTriangular id := fun i j hij => hup i j hij
    haveI : Invertible X0 := Matrix.invertibleOfIsUnitDet X0 hU
    exact fun b a h => Matrix.blockTriangular_inv_of_blockTriangular hbt h
  refine ⟨hYup, fun a => ?_⟩
  have h := congrFun (congrFun hXY a) a
  rw [Matrix.mul_apply, Matrix.one_apply_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ a), hd, one_mul] at h
  have hz : ∑ e ∈ Finset.univ.erase a, X0 a e * X0⁻¹ e a = 0 := by
    refine Finset.sum_eq_zero fun e he => ?_
    rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase he) with h1 | h1
    · rw [hup a e h1, zero_mul]
    · rw [hYup e a h1, mul_zero]
  rw [hz, add_zero] at h
  exact h

end LatB

open LatB LatA Alg in

theorem dictLatB_holds : DictLatB := by
  intro D X u n hn hLQ
  obtain ⟨hXs, hxs, hMs⟩ := hLQ
  have hup : ∀ b a, a < b → Xq X n b a = 0 := fun b a h => Xq_lower hn h
  have hd : ∀ a, Xq X n a a = 1 := Xq_diag hn
  have hXs' : ∀ b a, b < a → Xq X n b a ∈ aaD D b * (aaD D a)⁻¹ := hXs
  have hMs' : ∀ b a, Mq X n b a ∈ aaD D b * aaD D a := hMs
  have hXinv := shape_inv (Xq X n) hup hd hXs'
  obtain ⟨hYup, hYd⟩ := inv_up (Xq X n) hup hd
  have hdet : IsUnit (Xq X n).det := by rw [Xq_det hn]; exact isUnit_one
  have hAeq : Xq X n * Mq X n = Aq X n := by
    unfold Mq; rw [Matrix.mul_nonsing_inv_cancel_left _ _ hdet]
  have hA : ∀ b a, Aq X n b a ∈ aaD D b * aaD D a := by
    rw [← hAeq]; exact shape_mul (Xq X n) (Mq X n) hup hd hXs' hMs'
  have hBeq : Bq (X := X) n = ((Xq X n)⁻¹)ᴴ := by
    have h := XB hn
    rw [Matrix.conjTranspose_nonsing_inv]
    exact (Matrix.inv_eq_right_inv h).symm
  have hB : ∀ d a, Bq (X := X) n d a ∈ (aaD D d)⁻¹ * aaD D a := by
    intro d a
    rw [hBeq, Matrix.conjTranspose_apply]
    rcases lt_trichotomy a d with h | h | h
    · rw [mul_comm]; exact SS_mul (SS_aaD a) (SS_inv (SS_aaD d)) _ (hXinv a d h)
    · subst h; rw [hYd, star_one, mul_comm]; exact one_mem_aa a
    · rw [hYup a d h, star_zero]; exact Submodule.zero_mem _

  have hsub : ∀ x ∈ (VS D).L0, n x ∈ (VS D).L0 := by
    intro x hx
    obtain ⟨hf, he, hw⟩ := (mem_hermitianStandardLattice_iff_pairing_integral X x).1 hx
    have hwW : InW X (pW X x) := pW_inW X x
    have hnx : n x = ∑ c, (VS D).hT (X.fY c) x • n (X.eX c) + ∑ c, (VS D).hT (X.eX c) x • n (X.fY c) +
        n (pW X x) := by
      conv_lhs => rw [decomp X x]
      simp only [map_add, map_sum, map_smul]
    rw [mem_hermitianStandardLattice_iff_pairing_integral X]
    refine ⟨fun b => ?_, fun b => ?_, ?_⟩
    · rw [hnx, map_add, map_add, hT_sumR, hT_sumR, row hn b hwW]
      refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.sum_mem _ fun c _ => ?_)
        (Submodule.sum_mem _ fun c _ => ?_)) (hT_aaLb_mem X (hxs b) hw)
      · show (VS D).hT (X.fY c) x * Xq X n b c ∈ aaD D b
        rcases lt_trichotomy c b with h | h | h
        · rw [hup b c h, mul_zero]; exact Submodule.zero_mem _
        · subst h; rw [hd, mul_one]; exact hf c
        · have e : aaD D c * (aaD D b * (aaD D c)⁻¹) = aaD D b := by
            rw [mul_comm, mul_assoc, inv_mul_cancel₀ (aa_ne c), mul_one]
          rw [← e]; exact FractionalIdeal.mul_mem_mul (hf c) (hXs' b c h)
      · show (VS D).hT (X.eX c) x * Aq X n b c ∈ aaD D b
        have e : (aaD D c)⁻¹ * (aaD D b * aaD D c) = aaD D b := by
          rw [mul_comm, mul_assoc, mul_inv_cancel₀ (aa_ne c), mul_one]
        rw [← e]; exact FractionalIdeal.mul_mem_mul (he c) (hA b c)
    · rw [hnx, map_add, map_add, hT_sumR, hT_sumR]
      have h1 : ∀ c, (VS D).hT (X.eX b) (n (X.eX c)) = 0 := fun c => by
        rw [Xq_expand hn c, hT_sumR]; simp only [X.ee, mul_zero, Finset.sum_const_zero]
      have h2 : (VS D).hT (X.eX b) (n (pW X x)) = 0 := by
        rw [nw hn hwW, map_add, hT_sumR, (hwW b).1, zero_add]
        simp only [X.ee, mul_zero, Finset.sum_const_zero]
      simp only [h1, h2, mul_zero, Finset.sum_const_zero, zero_add, add_zero]
      refine Submodule.sum_mem _ fun c _ => ?_
      show (VS D).hT (X.eX c) x * Bq (X := X) n b c ∈ (aaD D b)⁻¹
      have e : (aaD D c)⁻¹ * ((aaD D b)⁻¹ * aaD D c) = (aaD D b)⁻¹ := by
        rw [mul_comm, mul_assoc, mul_inv_cancel₀ (aa_ne c), mul_one]
      rw [← e]; exact FractionalIdeal.mul_mem_mul (he c) (hB b c)
    · rw [hnx, pW_add, pW_add, pW_sum, pW_sum, pW_nw hn hwW]
      have h1 : ∀ c, pW X (n (X.eX c)) = 0 := fun c => by rw [Xq_expand hn c, pW_sum_e]
      simp only [h1, smul_zero, Finset.sum_const_zero, zero_add, pW_nf hn]
      refine Submodule.add_mem _ (Submodule.sum_mem _ fun c _ => ?_) hw
      rw [smul_neg, Finset.smul_sum]
      refine Submodule.neg_mem _ (Submodule.sum_mem _ fun d _ => ?_)
      rw [smul_smul]
      refine smul_aaLb X ?_ (hxs d)
      have e : (aaD D c)⁻¹ * ((aaD D d)⁻¹ * aaD D c) = (aaD D d)⁻¹ := by
        rw [mul_comm, mul_assoc, mul_inv_cancel₀ (aa_ne c), mul_one]
      rw [← e]; exact FractionalIdeal.mul_mem_mul (he c) (hB d c)

  have hle : Formalism.HermitianLatticesTheory.gmap n (VS D).L0 ≤ (VS D).L0 := by
    intro y hy
    rw [Formalism.HermitianLatticesTheory.isomAct_mem_gmap] at hy
    have := hsub _ hy
    rwa [LinearEquiv.apply_symm_apply] at this
  have hU0 : Formalism.HermitianLatticesTheory.dual (VS D).hT (VS D).L0 = (VS D).L0 := (VS D).baseLattice_isUnimodular
  have hUg : Formalism.HermitianLatticesTheory.dual (VS D).hT (Formalism.HermitianLatticesTheory.gmap n (VS D).L0) = Formalism.HermitianLatticesTheory.gmap n (VS D).L0 := by
    rw [Formalism.MainNotions.BridgeLemma₂.c3sub_dual_gmap _ n hn.1, hU0]
  refine le_antisymm hle ?_
  intro x hx
  rw [← hUg, Formalism.HermitianLatticesTheory.isomAct_mem_dual]
  rw [← hU0, Formalism.HermitianLatticesTheory.isomAct_mem_dual] at hx
  exact fun y hy => hx y (hle hy)

end Formalism.L2.SG.Pf.NcReal.JX.NOf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.RowRankHolds
section
noncomputable section

open NumberField Formalism.BasicNotions Module
open scoped BigOperators

namespace Formalism.L2.SG.Pf.NcReal.JX.CovB.CovolumeSpans

open Formalism.L2.SG.HidaSetting Formalism.MainNotions.S

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D)

theorem rowRank_holds : RowRank := by
  intro D X b
  set S := Submodule.span D.host.E (aaLbS X b : Set (VS D).V) with hSdef
  have hSfin : finrank D.host.E S = D.R.k + 1 := by
    rw [hSdef, span_aaLbS, finrank_span_Lb]
  have hSle : ∀ x ∈ aaLbS X b, x ∈ S := fun x hx => Submodule.subset_span hx
  let B : Basis (Fin (D.R.k + 1)) D.host.E S := Module.finBasisOfFinrankEq D.host.E S hSfin
  let eS : S ≃ₗ[D.host.E] (Fin (D.R.k + 1) → D.host.E) := B.equivFun
  let Φ : (Fin (D.R.k + 1) → D.host.E) →ₗ[𝓞 D.host.E] (VS D).V :=
    (S.subtype.comp eS.symm.toLinearMap).restrictScalars (𝓞 D.host.E)
  have hΦ : ∀ y, Φ y = ((eS.symm y : S) : (VS D).V) := fun y => rfl
  have hΦinj : Function.Injective Φ := by
    intro y y' h
    rw [hΦ, hΦ] at h
    exact eS.symm.injective (Subtype.ext h)
  let A : Submodule (𝓞 D.host.E) (Fin (D.R.k + 1) → D.host.E) := (aaLbS X b).comap Φ
  have hmemA : ∀ y, y ∈ A ↔ Φ y ∈ aaLbS X b := fun y => Iff.rfl

  have hmap : A.map Φ = aaLbS X b := by
    refine le_antisymm (Submodule.map_comap_le _ _) fun x hx => ?_
    refine ⟨eS ⟨x, hSle x hx⟩, ?_, ?_⟩
    · show Φ (eS ⟨x, hSle x hx⟩) ∈ aaLbS X b
      rw [hΦ, LinearEquiv.symm_apply_apply]
      exact hx
    · show Φ (eS ⟨x, hSle x hx⟩) = x
      rw [hΦ, LinearEquiv.symm_apply_apply]
  have hAfg : A.FG := Submodule.fg_of_fg_map_injective Φ hΦinj (by rw [hmap]; exact fg_aaLbS X b)

  have hAspan : Submodule.span D.host.E (A : Set (Fin (D.R.k + 1) → D.host.E)) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have key : ∀ (v : (VS D).V) (hv : v ∈ S), eS ⟨v, hv⟩ ∈ Submodule.span D.host.E (A : Set _) := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem x hx =>
        refine Submodule.subset_span ?_
        show Φ (eS ⟨x, _⟩) ∈ aaLbS X b
        rw [hΦ, LinearEquiv.symm_apply_apply]
        exact hx
      | zero =>
        have : eS ⟨0, S.zero_mem⟩ = 0 := by
          rw [show (⟨0, S.zero_mem⟩ : S) = 0 from rfl, map_zero]
        rw [this]
        exact Submodule.zero_mem _
      | add x y hx hy ihx ihy =>
        have : eS ⟨x + y, S.add_mem hx hy⟩ = eS ⟨x, hx⟩ + eS ⟨y, hy⟩ := by
          rw [← map_add]; rfl
        rw [this]
        exact Submodule.add_mem _ ihx ihy
      | smul c x hx ihx =>
        have : eS ⟨c • x, S.smul_mem c hx⟩ = c • eS ⟨x, hx⟩ := by
          rw [← map_smul]; rfl
        rw [this]
        exact Submodule.smul_mem _ c ihx
    have := key _ (eS.symm y).2
    rwa [Subtype.coe_eta, LinearEquiv.apply_symm_apply] at this

  let Az : Submodule ℤ (Fin (D.R.k + 1) → D.host.E) := A.restrictScalars ℤ
  have h1 : Module.Finite (𝓞 D.host.E) A := Module.Finite.iff_fg.2 hAfg
  have h2 : Module.Finite ℤ A := Module.Finite.trans (𝓞 D.host.E) _
  have h3 : Module.Finite ℤ Az :=
    Module.Finite.equiv ((Submodule.restrictScalarsEquiv ℤ (𝓞 D.host.E) _ A).restrictScalars ℤ).symm
  have hlat : Submodule.IsLattice ℚ Az := by
    refine ⟨Module.Finite.iff_fg.1 h3, ?_⟩
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ Submodule.span D.host.E (A : Set (Fin (D.R.k + 1) → D.host.E)) := by rw [hAspan]; trivial
    obtain ⟨n, hn, hnx⟩ := Formalism.MainNotions.LatticeGluingRadicals.j_exists_nat_smul_mem A hx
    have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
    have : x = (n : ℚ)⁻¹ • (n • x) := by
      rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ hn', one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hnx)
  have hr : finrank ℤ Az = finrank ℚ (Fin (D.R.k + 1) → D.host.E) :=
    Module.finrank_eq_of_rank_eq
      ((Submodule.IsLattice.rank' ℚ Az).trans (Module.finrank_eq_rank ℚ (Fin (D.R.k + 1) → D.host.E)).symm)
  let bZ : Basis (Fin (finrank ℚ (Fin (D.R.k + 1) → D.host.E))) ℤ Az := Module.finBasisOfFinrankEq ℤ Az hr
  have hdim : finrank ℚ (Fin (D.R.k + 1) → D.host.E) = finrank ℚ D.host.E * (D.R.k + 1) := by
    rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_comm]

  let eqv : Az ≃ₗ[ℤ] ((aaLbS X b).restrictScalars ℤ) :=
    { toFun := fun y => ⟨Φ (y : Fin (D.R.k + 1) → D.host.E), (hmemA _).1 y.2⟩
      invFun := fun x => ⟨eS ⟨x, hSle x x.2⟩, by
        show Φ (eS ⟨x, hSle x x.2⟩) ∈ aaLbS X b
        rw [hΦ, LinearEquiv.symm_apply_apply]
        exact x.2⟩
      map_add' := fun y y' => Subtype.ext (map_add Φ (y : Fin (D.R.k + 1) → D.host.E) y')
      map_smul' := fun c y => Subtype.ext (by
        show Φ (c • (y : Fin (D.R.k + 1) → D.host.E)) = c • Φ (y : Fin (D.R.k + 1) → D.host.E)
        exact map_zsmul Φ c _)
      left_inv := fun y => Subtype.ext (by
        show eS ⟨Φ (y : Fin (D.R.k + 1) → D.host.E), _⟩ = (y : Fin (D.R.k + 1) → D.host.E)
        have : (⟨Φ (y : Fin (D.R.k + 1) → D.host.E), hSle _ ((hmemA _).1 y.2)⟩ : S) = eS.symm y := Subtype.ext (hΦ _)
        rw [this, LinearEquiv.apply_symm_apply])
      right_inv := fun x => Subtype.ext (by
        show Φ (eS ⟨x, _⟩) = (x : (VS D).V)
        rw [hΦ, LinearEquiv.symm_apply_apply]) }
  exact ⟨(bZ.map eqv).reindex (finCongr hdim)⟩

end Formalism.L2.SG.Pf.NcReal.JX.CovB.CovolumeSpans
end
end

