import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.UnipotentMatrixMapSecondComponent
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0061
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.FullExistsTiedHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0042
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0420
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0081
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0027
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0009
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0071
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0082
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0042

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CondXG
section
noncomputable section

open Matrix

namespace Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  (M : Formalism.MainNotions.S.Loc.Model F E) (g : Formalism.MainNotions.S.Loc.SplitG M.L) {r : ℕ}

theorem q_ne (g : Formalism.MainNotions.S.Loc.SplitG M.L) : ((g.q : F)) ≠ 0 := by
  exact fun h => g.q_irr.ne_zero (Subtype.ext h)

theorem zzrel_G (hs : M.split = some g) {X X' L P : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    (hL : ∀ i, L i (Fin.last r) = if i = Fin.last r then 1 else 0)
    (hP : ∀ j, P (Fin.last r) j = if j = Fin.last r then 1 else 0) (T T' : F)
    (h : Formalism.MainNotions.S.Loc.HermSp.ZZplusOf M X' T T' = L * Formalism.MainNotions.S.Loc.HermSp.ZZplusOf M X T T' * P) :
    X'.map (π1 M g) = L.map (π1 M g) * X.map (π1 M g) * P.map (π1 M g) ∧
    (X'.map (π2 M g))ᵀ = L.map (π2 M g) * (X.map (π2 M g))ᵀ * P.map (π2 M g) := by
  classical
  have hq : (g.q : F) ≠ 0 := q_ne M g
  have hπ1 : ∀ x : E, π1 M g x = (g.e x).1 := fun x => rfl
  have hπ2 : ∀ x : E, π2 M g x = (g.e x).2 := fun x => rfl
  have hZ : ∀ (Y : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (a b : Fin (r + 1)),
      Formalism.MainNotions.S.Loc.HermSp.ZZplusOf M Y T T' a b =
        g.e.symm ((g.e (Y a b)).1 / (g.q : F), -((g.e (Y b a)).2 / (g.q : F))) -
        (if a = Fin.last r ∧ b = Fin.last r then g.e.symm (-T / (g.q : F), T' / (g.q : F)) else 0) := by
    intro Y a b
    simp only [Formalism.MainNotions.S.Loc.HermSp.ZZplusOf, hs, Matrix.of_apply]
  let Ec : Matrix (Fin (r + 1)) (Fin (r + 1)) F :=
    Matrix.of fun a b => if a = Fin.last r ∧ b = Fin.last r then 1 else 0
  have hZ1 : ∀ Y : Matrix (Fin (r + 1)) (Fin (r + 1)) E, (Formalism.MainNotions.S.Loc.HermSp.ZZplusOf M Y T T').map (π1 M g) =
      (g.q : F)⁻¹ • Y.map (π1 M g) + (T / (g.q : F)) • Ec := by
    intro Y
    ext a b
    by_cases hab : a = Fin.last r ∧ b = Fin.last r
    · simp only [Matrix.map_apply, hZ, hπ1, map_sub, Prod.fst_sub, AlgEquiv.apply_symm_apply, if_pos hab,
        Matrix.add_apply, Matrix.smul_apply, Ec, Matrix.of_apply, smul_eq_mul, mul_one]
      ring
    · simp only [Matrix.map_apply, hZ, hπ1, map_sub, Prod.fst_sub, AlgEquiv.apply_symm_apply, if_neg hab,
        map_zero, Prod.fst_zero, sub_zero, Matrix.add_apply, Matrix.smul_apply, Ec, Matrix.of_apply, smul_eq_mul,
        mul_zero, add_zero]
      ring
  have hZ2 : ∀ Y : Matrix (Fin (r + 1)) (Fin (r + 1)) E, (Formalism.MainNotions.S.Loc.HermSp.ZZplusOf M Y T T').map (π2 M g) =
      -((g.q : F)⁻¹ • (Y.map (π2 M g))ᵀ) - (T' / (g.q : F)) • Ec := by
    intro Y
    ext a b
    by_cases hab : a = Fin.last r ∧ b = Fin.last r
    · simp only [Matrix.map_apply, hZ, hπ2, map_sub, Prod.snd_sub, AlgEquiv.apply_symm_apply, if_pos hab,
        Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.transpose_apply, Ec, Matrix.of_apply,
        smul_eq_mul, mul_one]
      ring
    · simp only [Matrix.map_apply, hZ, hπ2, map_sub, Prod.snd_sub, AlgEquiv.apply_symm_apply, if_neg hab,
        map_zero, Prod.snd_zero, sub_zero, Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply,
        Matrix.transpose_apply, Ec, Matrix.of_apply, smul_eq_mul, mul_zero]
      ring
  have hE : ∀ φ : E →+* F, L.map φ * Ec * P.map φ = Ec := by
    intro φ
    ext i j
    simp only [Matrix.mul_apply, Matrix.map_apply, Ec, Matrix.of_apply]
    rw [Finset.sum_eq_single (Fin.last r)]
    · rw [Finset.sum_eq_single (Fin.last r)]
      · simp only [and_self, if_true, mul_one, hL, hP]
        split_ifs <;> simp_all
      · intro k _ hk
        simp [hk]
      · simp
    · intro l _ hl
      simp [hl]
    · simp
  have hinv : (g.q : F)⁻¹ ≠ 0 := inv_ne_zero hq
  constructor
  · have hmap := congrArg (fun Z => Matrix.map Z (π1 M g)) h
    simp only [Matrix.map_mul] at hmap
    rw [hZ1, hZ1] at hmap
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, hE] at hmap
    exact smul_right_injective _ hinv (add_right_cancel hmap)
  · have hmap := congrArg (fun Z => Matrix.map Z (π2 M g)) h
    simp only [Matrix.map_mul] at hmap
    rw [hZ2, hZ2] at hmap
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul,
      hE] at hmap
    exact smul_right_injective _ hinv (neg_inj.1 (sub_left_inj.1 hmap))

theorem condX_G (hs : M.split = some g) {X X' L P : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    (hL : ∀ i, L i (Fin.last r) = if i = Fin.last r then 1 else 0)
    (hP : ∀ j, P (Fin.last r) j = if j = Fin.last r then 1 else 0) (T T' : F)
    (h : Formalism.MainNotions.S.Loc.HermSp.ZZplusOf M X' T T' = L * Formalism.MainNotions.S.Loc.HermSp.ZZplusOf M X T T' * P) :
    cjT (M.L.cj : E →+* E) (mmG M g L P) * X * uuG M g L P = X' := by
  obtain ⟨h1, h2⟩ := zzrel_G M g hs hL hP T T' h
  have hπ1 : ∀ x : E, π1 M g x = (g.e x).1 := fun x => rfl
  have hπ2 : ∀ x : E, π2 M g x = (g.e x).2 := fun x => rfl
  have hcj : ∀ x : E, g.e ((M.L.cj : E →+* E) x) = (g.e x).swap := fun x => g.e_cj x
  ext i j
  apply g.e.injective
  refine Prod.ext ?_ ?_
  · have h1' := congrArg (fun A => A i j) h1
    simp only [Matrix.map_apply, Matrix.mul_apply, hπ1, Finset.sum_mul] at h1'
    simp only [cjT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, Prod.fst_sum,
      Prod.fst_mul, hcj, Prod.fst_swap, mmG, uuG, Matrix.of_apply, AlgEquiv.apply_symm_apply, Finset.sum_mul]
    rw [h1']
  · have h2' := congrArg (fun A => A j i) h2
    simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.transpose_apply, hπ2, Finset.sum_mul] at h2'
    simp only [cjT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, Prod.snd_sum,
      Prod.snd_mul, hcj, Prod.snd_swap, mmG, uuG, Matrix.of_apply, AlgEquiv.apply_symm_apply, Finset.sum_mul]
    rw [h2', Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring

theorem condM_G {L P : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    (hL : ∀ i, L i (Fin.last r) = if i = Fin.last r then 1 else 0)
    (hP : ∀ j, P (Fin.last r) j = if j = Fin.last r then 1 else 0) (c : E) :
    cjT (M.L.cj : E →+* E) (mmG M g L P) * cornerM c * mmG M g L P = cornerM c := by
  have hm : ∀ i, mmG M g L P (Fin.last r) i = if i = Fin.last r then 1 else 0 := by
    intro i
    simp only [mmG, Matrix.of_apply, hP, hL]
    split_ifs <;> simp
  ext i j
  simp only [cjT, cornerM, Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply, Matrix.map_apply]
  rw [Finset.sum_eq_single (Fin.last r)]
  · rw [Finset.sum_eq_single (Fin.last r)]
    · simp only [and_self, if_true, hm]
      split_ifs <;> simp_all
    · intro k _ hk
      simp [hk]
    · simp
  · intro l _ hl
    simp [hl]
  · simp

theorem condU_G {L P : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    (hL : ∀ i, L i (Fin.last r) = if i = Fin.last r then 1 else 0)
    (hP : ∀ j, P (Fin.last r) j = if j = Fin.last r then 1 else 0) (c : E) :
    cjT (M.L.cj : E →+* E) (uuG M g L P) * cornerM c * uuG M g L P = cornerM c := by
  have hm : ∀ i, uuG M g L P (Fin.last r) i = if i = Fin.last r then 1 else 0 := by
    intro i
    simp only [uuG, Matrix.of_apply, hP, hL]
    split_ifs <;> simp
  ext i j
  simp only [cjT, cornerM, Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply, Matrix.map_apply]
  rw [Finset.sum_eq_single (Fin.last r)]
  · rw [Finset.sum_eq_single (Fin.last r)]
    · simp only [and_self, if_true, hm]
      split_ifs <;> simp_all
    · intro k _ hk
      simp [hk]
    · simp
  · intro l _ hl
    simp [hl]
  · simp

end Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DiagCLC
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc

namespace Formalism.L2.SG.RowsConc

theorem normExpSatTied_holds : NormExpSatTied := by
  intro D X Y u u' hT
  have hF := Formalism.L2.SG.Closed.FundExistsC_holds D X Y u u'
  have hO : ∀ w, Formalism.L2.SG.WuDecay.FoldOK X w Y.hK :=
    fun w => Formalism.L2.SG.Closed.FoldOKC_outright D X Y w hT.1 hT.2.2.2.2.1
  have hI := Formalism.L2.SG.Closed.OOIntAllC_outright D X Y u u' (hO u) (hO u') hF
  have hAbs := absConvTied_of_full Formalism.L2.SG.Closed.FoldOKC_outright Formalism.L2.SG.Closed.FundExistsC_holds
    Formalism.L2.SG.Closed.OOIntAllC_outright Formalism.L2.SG.Closed.AbsConvC_outright D X Y u u' hT
  exact Formalism.L2.SG.NormCut.normExpSatC'_of_PD (fun D => Formalism.L2.SG.Pf.positive_definite_isomorphism D) D X Y u u' hI
    (Formalism.L2.SG.Closed.AmpWellDefC_holds D X Y u u' hI) (Formalism.L2.SG.Closed.OOFundIndepC_holds D X Y u u' hF hI) hAbs

theorem idOneC_holds : IdOneC :=
  idOneC_of_full Formalism.L2.SG.Closed.FoldOKC_outright Formalism.L2.SG.Closed.FundExistsC_holds
    Formalism.L2.SG.Closed.OOIntAllC_outright Formalism.L2.SG.Closed.IdCellDiagC_holds

theorem diagonal_contribution_of_equal_words (hNG : RowNGC) (hM : RowMainEqC) : DiagCL := by
  exact diagCL_of_rows Formalism.FourierDecayAlt.P.pair_bound_abstract Formalism.FourierDecayAlt.P.price_of_index
    Formalism.FourierDecayAlt.P.equal_index Formalism.FourierDecayAlt.P.pair_split_alt Formalism.FourierDecayAlt.P.subfamilyAlt
    Formalism.L2.SG.Closed.TermsGGBound_holds normExpSatTied_holds
    (fun D X Y u u' _ => Formalism.L2.SG.Pf.SatGram.corankPos_tO (X := X) (Y := Y) u u') idOneC_holds hNG hM
    Formalism.L2.SG.Pf.diagNumC_holds

end Formalism.L2.SG.RowsConc
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IsUpUniMul
section
noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolGrp

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ZsVolCut Matrix
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Uni

variable {R : Type*} [CommRing R] {n : ℕ}

theorem isLoUni_mul {l l' : Matrix (Fin n) (Fin n) R} (h : IsLoUni l) (h' : IsLoUni l') : IsLoUni (l * l') := by
  intro a b
  refine ⟨fun hab => ?_, fun hab => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rcases lt_or_ge a c with hc | hc
    · rw [(h a c).1 hc, zero_mul]
    · rw [(h' c b).1 (lt_of_le_of_lt hc hab), mul_zero]
  · subst hab
    rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [(h a a).2 rfl, (h' a a).2 rfl, mul_one]
    · intro c _ hc
      rcases lt_or_gt_of_ne hc with hc' | hc'
      · rw [(h' c a).1 hc', mul_zero]
      · rw [(h a c).1 hc', zero_mul]
    · simp

theorem isUpUni_mul {l l' : Matrix (Fin n) (Fin n) R} (h : IsUpUni l) (h' : IsUpUni l') : IsUpUni (l * l') := by
  first | exact GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul .. | (apply GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul <;> assumption) | (intros; apply GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul <;> assumption) | (apply @GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul <;> assumption) | (intros; apply @GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul <;> assumption) | (apply @GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul <;> first | assumption | infer_instance) | exact @GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul R ‹_› n l l' h h' | exact @GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul R ‹_› n l l' h | exact @GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul R ‹_› n l l' | exact @GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul R ‹_› n l | exact @GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul R ‹_› n | exact @GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul R ‹_› | exact @GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul R

theorem isLoUni_one : IsLoUni (1 : Matrix (Fin n) (Fin n) R) := fun a b =>
  ⟨fun h => Matrix.one_apply_ne h.ne, fun h => by subst h; exact Matrix.one_apply_eq a⟩

theorem isUpUni_one : IsUpUni (1 : Matrix (Fin n) (Fin n) R) := fun a b =>
  ⟨fun h => Matrix.one_apply_ne h.ne', fun h => by subst h; exact Matrix.one_apply_eq a⟩

theorem isLoUni_inv {l : Matrix (Fin n) (Fin n) R} (h : IsLoUni l) : IsLoUni l⁻¹ ∧ l⁻¹ * l = 1 ∧ l * l⁻¹ = 1 := by
  have hd : l.det = 1 := det_lo (fun a => (h a a).2 rfl) (fun a b hab => (h a b).1 hab)
  have hu : IsUnit l.det := by rw [hd]; exact isUnit_one
  have hli : l⁻¹ * l = 1 := Matrix.nonsing_inv_mul l hu
  have hil : l * l⁻¹ = 1 := Matrix.mul_nonsing_inv l hu
  have := Matrix.invertibleOfIsUnitDet l hu
  have hb : l⁻¹.BlockTriangular OrderDual.toDual :=
    Matrix.blockTriangular_inv_of_blockTriangular (fun i j hij => (h i j).1 hij)
  refine ⟨fun a b => ⟨fun hab => hb hab, fun hab => ?_⟩, hli, hil⟩
  subst hab
  have e := congrFun (congrFun hil a) a
  rw [Matrix.mul_apply, Finset.sum_eq_single a, (h a a).2 rfl, one_mul] at e
  · simpa using e
  · intro c _ hc
    rcases lt_or_gt_of_ne hc with hc' | hc'
    · rw [hb hc', mul_zero]
    · rw [(h a c).1 hc', zero_mul]
  · simp

theorem isUpUni_inv {l : Matrix (Fin n) (Fin n) R} (h : IsUpUni l) : IsUpUni l⁻¹ ∧ l⁻¹ * l = 1 ∧ l * l⁻¹ = 1 := by
  have hd : l.det = 1 := det_up (fun a => (h a a).2 rfl) (fun a b hab => (h a b).1 hab)
  have hu : IsUnit l.det := by rw [hd]; exact isUnit_one
  have hli : l⁻¹ * l = 1 := Matrix.nonsing_inv_mul l hu
  have hil : l * l⁻¹ = 1 := Matrix.mul_nonsing_inv l hu
  have := Matrix.invertibleOfIsUnitDet l hu
  have hb : l⁻¹.BlockTriangular id :=
    Matrix.blockTriangular_inv_of_blockTriangular (fun i j hij => (h i j).1 hij)
  refine ⟨fun a b => ⟨fun hab => hb hab, fun hab => ?_⟩, hli, hil⟩
  subst hab
  have e := congrFun (congrFun hil a) a
  rw [Matrix.mul_apply, Finset.sum_eq_single a, (h a a).2 rfl, one_mul] at e
  · simpa using e
  · intro c _ hc
    rcases lt_or_gt_of_ne hc with hc' | hc'
    · rw [(h a c).1 hc', zero_mul]
    · rw [hb hc', mul_zero]
  · simp

end Uni

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)

def stZ (Z L : Formalism.L2.SG.PairVal.MatR D) (hL : IsUnit L.det) : Subgroup (Formalism.L2.SG.PairVal.GLR D) where
  carrier := stZSet M δ u u' Z L
  one_mem' := by
    refine ⟨1, ?_, isLoUni_one, 1, isUpUni_one, by simp, fun p => ⟨1, 1, intLow_one _, intUp_one _, fun Z' => ?_⟩⟩
    · simp [Matrix.nonsing_inv_mul L hL]
    · simp [zhatOM_zhatOM]
  mul_mem' := by
    rintro x y ⟨x', hx, hxl, bx, hbx, hxZ, hxp⟩ ⟨y', hy, hyl, by', hby, hyZ, hyp⟩
    refine ⟨x' * y', ?_, ?_, by' * bx, isUpUni_mul hby hbx, ?_, fun p => ?_⟩
    · rw [Units.val_mul, hx, hy, Units.val_mul]
      calc L⁻¹ * (x' : Formalism.L2.SG.PairVal.MatR D) * L * (L⁻¹ * (y' : Formalism.L2.SG.PairVal.MatR D) * L) =
          L⁻¹ * (x' : Formalism.L2.SG.PairVal.MatR D) * (L * L⁻¹) * (y' : Formalism.L2.SG.PairVal.MatR D) * L := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [Matrix.mul_nonsing_inv L hL, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    · rw [Units.val_mul]
      exact isLoUni_mul hxl hyl
    · rw [Units.val_mul]
      calc (x' : Formalism.L2.SG.PairVal.MatR D) * (y' : Formalism.L2.SG.PairVal.MatR D) * ZhatOM Z * (by' * bx) =
          (x' : Formalism.L2.SG.PairVal.MatR D) * ((y' : Formalism.L2.SG.PairVal.MatR D) * ZhatOM Z * by') * bx := by
            simp only [Matrix.mul_assoc]
        _ = ZhatOM Z := by rw [hyZ, hxZ]
    · obtain ⟨l1, ρ1, hl1, hρ1, h1⟩ := hxp p
      obtain ⟨l2, ρ2, hl2, hρ2, h2⟩ := hyp p
      refine ⟨l1 * l2, ρ2 * ρ1, intLow_mul _ hl1 hl2, intUp_mul _ hρ2 hρ1, fun Z' => ?_⟩
      have e : ((x' * y' : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) * ZhatOM Z' * (by' * bx) =
          (x' : Formalism.L2.SG.PairVal.MatR D) *
            ZhatOM (ZhatOM ((y' : Formalism.L2.SG.PairVal.MatR D) * ZhatOM Z' * by')) * bx := by
        rw [zhatOM_zhatOM, Units.val_mul]
        simp only [Matrix.mul_assoc]
      rw [e, h1, h2]
      simp only [Matrix.mul_assoc]
  inv_mem' := by
    rintro x ⟨x', hx, hxl, bx, hbx, hxZ, hxp⟩
    obtain ⟨hxi, hxi1, hxi2⟩ := isLoUni_inv hxl
    obtain ⟨hbi, hbi1, hbi2⟩ := isUpUni_inv hbx
    have hZ : ((x'⁻¹ : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) * ZhatOM Z * bx⁻¹ = ZhatOM Z := by
      rw [Matrix.coe_units_inv]
      calc (x' : Formalism.L2.SG.PairVal.MatR D)⁻¹ * ZhatOM Z * bx⁻¹ =
          (x' : Formalism.L2.SG.PairVal.MatR D)⁻¹ * ((x' : Formalism.L2.SG.PairVal.MatR D) * ZhatOM Z * bx) * bx⁻¹ := by rw [hxZ]
        _ = ZhatOM Z := by
          simp only [← Matrix.mul_assoc]
          rw [hxi1, Matrix.one_mul, Matrix.mul_assoc, hbi2, Matrix.mul_one]
    refine ⟨x'⁻¹, ?_, by rw [Matrix.coe_units_inv]; exact hxi, bx⁻¹, hbi, hZ, fun p => ?_⟩
    · rw [Matrix.coe_units_inv, Matrix.coe_units_inv, hx]
      have hLi := Matrix.nonsing_inv_mul L hL
      have hiL := Matrix.mul_nonsing_inv L hL
      refine Matrix.inv_eq_left_inv ?_
      calc L⁻¹ * (x' : Formalism.L2.SG.PairVal.MatR D)⁻¹ * L * (L⁻¹ * (x' : Formalism.L2.SG.PairVal.MatR D) * L) =
          L⁻¹ * ((x' : Formalism.L2.SG.PairVal.MatR D)⁻¹ * (L * L⁻¹) * (x' : Formalism.L2.SG.PairVal.MatR D)) * L := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hiL, Matrix.mul_one, hxi1, Matrix.mul_one, hLi]
    · obtain ⟨l, ρ, hl, hρ, h⟩ := hxp p
      obtain ⟨hli, hli1, hli2⟩ := intLow_inv _ hl
      obtain ⟨hρi, hρi1, hρi2⟩ := intUp_inv _ hρ
      refine ⟨l⁻¹, ρ⁻¹, hli, hρi, fun Z' => ?_⟩
      have h2 := h (ZhatOM (((x'⁻¹ : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) * ZhatOM Z' * bx⁻¹))
      have e : (x' : Formalism.L2.SG.PairVal.MatR D) *
          ZhatOM (ZhatOM (((x'⁻¹ : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) * ZhatOM Z' * bx⁻¹)) * bx =
          ZhatOM Z' := by
        rw [zhatOM_zhatOM, Matrix.coe_units_inv]
        simp only [← Matrix.mul_assoc]
        rw [hxi2, Matrix.one_mul, Matrix.mul_assoc, hbi1, Matrix.mul_one]
      rw [e, zhatOM_zhatOM] at h2
      rw [h2]
      simp only [← Matrix.mul_assoc]
      rw [hli1, Matrix.one_mul]
      simp only [Matrix.mul_assoc, hρi2, Matrix.mul_one]

theorem mem_CZ (Z L : Formalism.L2.SG.PairVal.MatR D) (hL : IsUnit L.det) (a : Formalism.L2.SG.PairVal.GLR D) :
    a ∈ CZ M δ u u' Z L ↔ a ∈ stZSet M δ u u' Z L := by
  have e : CZ M δ u u' Z L = stZ M δ u u' Z L hL := by
    unfold CZ
    exact Subgroup.closure_eq (stZ M δ u u' Z L hL)
  rw [e]
  rfl

end Formalism.L2.SG.Pf.ZsVolGrp

end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IsotropicSpanOrthogonalAnisotropicVector
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.SpanOmPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

theorem hsw' (x y : (VS D).V) : (VS D).hT y x = star ((VS D).hT x y) := ((VS D).herm.eq x y).symm

theorem fvec_cs {T : D.host.E} (F : FlagG (VS D) D.R.rS T) (i : Fin D.R.rS) : F.fvec i.castSucc = F.e i := by
  simp [FlagG.fvec]

theorem fvec_last {T : D.host.E} (F : FlagG (VS D) D.R.rS T) : F.fvec (Fin.last D.R.rS) = F.z := by
  simp [FlagG.fvec]

theorem hff {T : D.host.E} (F : FlagG (VS D) D.R.rS T) (a b : Fin (D.R.rS + 1)) :
    (VS D).hT (F.fvec a) (F.fvec b) = if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then -T else 0 := by
  induction a using Fin.lastCases with
  | last =>
    induction b using Fin.lastCases with
    | last => rw [fvec_last, F.z_norm, if_pos ⟨rfl, rfl⟩]
    | cast j =>
      rw [fvec_last, fvec_cs, if_neg (fun h => Fin.castSucc_ne_last j h.2), hsw', F.z_orth, star_zero]
  | cast i =>
    rw [if_neg (fun h => Fin.castSucc_ne_last i h.1)]
    induction b using Fin.lastCases with
    | last => rw [fvec_cs, fvec_last, F.z_orth]
    | cast j => rw [fvec_cs, fvec_cs, F.e_iso]

theorem iso_X {T : D.host.E} (F : FlagG (VS D) D.R.rS T) {x y : (VS D).V} (hx : x ∈ F.X) (hy : y ∈ F.X) :
    (VS D).hT x y = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hx
  obtain ⟨d, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hy
  simp [map_sum, LinearMap.sum_apply, F.e_iso]

theorem isotropicSpan_orthogonal_anisotropicVector {T : D.host.E} (F : FlagG (VS D) D.R.rS T) {x : (VS D).V} (hx : x ∈ F.X) :
    (VS D).hT x F.z = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hx
  simp [map_sum, LinearMap.sum_apply, F.z_orth]

theorem z_orth_X {T : D.host.E} (F : FlagG (VS D) D.R.rS T) {x : (VS D).V} (hx : x ∈ F.X) :
    (VS D).hT F.z x = 0 := by
  rw [hsw', isotropicSpan_orthogonal_anisotropicVector F hx, star_zero]

theorem Xplus_eq {T : D.host.E} (F : FlagG (VS D) D.R.rS T) :
    F.Xplus = Submodule.span D.host.E (Set.range F.fvec) := by
  apply le_antisymm
  · apply sup_le
    · rw [FlagG.X, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨i.castSucc, fvec_cs F i⟩
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact Submodule.subset_span ⟨Fin.last _, fvec_last F⟩
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    induction a using Fin.lastCases with
    | last => rw [fvec_last]; exact Submodule.mem_sup_right (Submodule.subset_span rfl)
    | cast i => rw [fvec_cs]; exact Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.SpanOmPf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MemDdSPow
section
noncomputable section

open scoped Classical Matrix
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc

namespace Formalism.L2.SG.Pf.FibD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

theorem mem_ddS_pow (t : 𝓞 D.host.F) (ht : t ∈ differentIdeal ℤ (𝓞 D.host.F)) (k : ℕ) :
    (((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t) ^ k : 𝓞 D.host.E) : D.host.E) ∈ ddS D ^ k := by
  have h1 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t ∈
      Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F)) :=
    Ideal.mem_map_of_mem _ ht
  have h2 : ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t : 𝓞 D.host.E) : D.host.E) ∈ ddS D :=
    FractionalIdeal.mem_coeIdeal_of_mem _ h1
  have h3 := Submodule.pow_mem_pow (ddS D : Submodule (𝓞 D.host.E) D.host.E) h2 k
  rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_pow]
  push_cast
  exact h3

theorem dict_holds (Zd : LocDat D) : Formalism.L2.SG.Pf.TupGlob.Dict Zd := by
  intro A B hA hB hloc
  have hAu : IsLoUni A := fun i j => ⟨hA.2 i j, fun h => h ▸ hA.1 i⟩
  have hBu : IsUpUni B := Formalism.L2.SG.Pf.TupGlob.isUpUni_of hB
  have hsh : ∀ p, Formalism.L2.SG.Pf.StabIntSh.LocEntryShape D p A B := fun p =>
    (Formalism.L2.SG.Pf.StabIntSh.loc_iff Formalism.L2.SG.Pf.StabIntSh.locShapeL Formalism.L2.SG.Pf.StabIntSh.locShapeG (p := p)
      Zd.agree hAu hBu).1
      ⟨by rw [lOf_eq]; exact (hloc p).1, by rw [ρOf_eq]; exact Formalism.L2.SG.Pf.FibQ.sgn_conj_intUp Zd p (hloc p).2⟩
  have hES := (Formalism.L2.SG.Pf.StabIntSh.glob_iff Formalism.L2.SG.Pf.StabIntSh.locGlob Formalism.L2.SG.Pf.StabIntSh.shapeNZ A B).1 hsh
  refine ⟨fun c b hcb x hx => ?_, fun c b hcb x hx => ?_, fun P hP c b => ?_⟩
  · rw [Matrix.conjTranspose_apply, PI.UnitaryGroupMassFormula.CntFormula.star_eq_conjF]
    exact mem_aaF hcb hx (ddPow_conj Zd (by have := b.isLt; omega) (hES b c hcb).1)
  · rw [sg_entry]
    exact mem_aaF hcb hx (hES b c hcb).2.1
  · rcases lt_trichotomy c b with h | h | h
    · have hq := (hES b c h).2.2
      unfold Formalism.L2.SG.Pf.StabIntSh.qdPow Formalism.L2.SG.Pf.StabIntSh.qq at hq
      rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.mem_singleton_mul] at hq
      obtain ⟨z, hz, hzy⟩ := hq
      obtain ⟨t, ht, htP⟩ := diff_avoid P hP
      have hk : b.val - c.val ≤ D.R.rS := by have := b.isLt; omega
      have hz' := ddPow_conj Zd hk hz
      have hprod := FractionalIdeal.mul_mem_mul (mem_ddS_pow t ht (b.val - c.val)) hz'
      unfold Formalism.L2.SG.Pf.StabIntSh.ddPow at hprod
      rw [← zpow_natCast, ← zpow_add₀ (PI.NRCW.ddS_ne_zero D), add_neg_cancel, zpow_zero] at hprod
      obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 hprod
      refine ⟨(algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t) ^ (b.val - c.val), fun hs => htP (P.isPrime.mem_of_pow_mem _ hs),
        o, ?_⟩
      rw [Matrix.conjTranspose_apply, PI.UnitaryGroupMassFormula.CntFormula.star_eq_conjF, sg_entry]
      have e1 : D.conjF (A b c) - Formalism.L2.SG.Pf.StabIntSh.bt D B c b =
          D.conjF (algebraMap (𝓞 D.host.E) D.host.E ((gS D : ℕ) : 𝓞 D.host.E) * z) := by
        have := congrArg D.conjF hzy
        simpa only [map_sub, Formalism.L2.SG.Pf.LocalDenominators.conjF_invol] using this
      rw [e1, map_mul, map_natCast, map_natCast, mul_left_comm, ← ho]
    · subst h
      refine ⟨1, fun h1 => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1), 0, ?_⟩
      rw [Matrix.conjTranspose_apply, sg_entry]
      simp [Formalism.L2.SG.Pf.StabIntSh.bt, hA.1 c, hB.1 c, ← pow_add, ← two_mul, pow_mul]
    · refine ⟨1, fun h1 => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1), 0, ?_⟩
      rw [Matrix.conjTranspose_apply, sg_entry]
      simp [Formalism.L2.SG.Pf.StabIntSh.bt, hA.2 b c h, hB.2 b c h]

end Formalism.L2.SG.Pf.FibD
end
end

