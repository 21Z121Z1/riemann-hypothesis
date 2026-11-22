import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1965
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2138
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedLagrangianOppositeLagrangianChart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0407
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2078
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2148
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1825
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1765
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0950
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1777
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1453
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0201
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0331
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CentralInvolutionRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1816
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1894
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1873
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniqueUpToTargetGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2116

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStandingTripleThetaFirst
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

namespace GlobalTheory.TopFlip.ChartB

theorem reindex_blocks {K C : Type} [Field K] {n p q d : ℕ} (e : Fin p ⊕ Fin q ≃ Fin d) (ρ : Fin p ⊕ Fin q ≃ C)
    (x : Matrix (Fin n) (Fin n) K) (Z : Matrix (Fin n) (Fin d) K) (P R : Matrix (Fin p) (Fin p) K)
    (Q S : Matrix (Fin q) (Fin q) K) (r : Fin n) (c : C) :
    (x * (Z.submatrix id (e.symm.trans finSumFinEquiv).symm * GlobalTheory.Doubling.blkMat finSumFinEquiv P Q) *
      GlobalTheory.Doubling.blkMat finSumFinEquiv R (-S)) r ((finSumFinEquiv.symm.trans ρ).symm c) =
    (x * Z * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e (P * R) (-(Q * S))) r ((e.symm.trans ρ).symm c) := by
  have h : Z.submatrix id (e.symm.trans finSumFinEquiv).symm * GlobalTheory.Doubling.blkMat finSumFinEquiv P Q *
      GlobalTheory.Doubling.blkMat finSumFinEquiv R (-S) =
      (Z * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e (P * R) (-(Q * S))).submatrix id (e.symm.trans finSumFinEquiv).symm := by
    have h1 : GlobalTheory.Doubling.blkMat finSumFinEquiv P Q * GlobalTheory.Doubling.blkMat finSumFinEquiv R (-S) =
        (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e (P * R) (-(Q * S))).submatrix (e.symm.trans finSumFinEquiv).symm
          (e.symm.trans finSumFinEquiv).symm := by
      unfold GlobalTheory.Doubling.blkMat GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk
      rw [submatrix_mul_equiv, fromBlocks_multiply]
      ext a b
      simp
    rw [Matrix.mul_assoc, h1, submatrix_mul_equiv]
  rw [Matrix.mul_assoc, h, Matrix.mul_assoc]
  simp [Matrix.mul_apply]

variable {D : D7}

theorem adj_coord (S X : HSp D) (y : Matrix (Fin S.rank) (Fin X.rank) (AE D)) :
    (S.gram⁻¹).map (incA D) * ((HMul.hMul yᵀ (incM S.gram) : Matrix (Fin X.rank) (Fin S.rank) (AE D)).map (cA D))ᵀ =
      y.map (cA D) := by
  have e0 : ((incM S.gram).map (cA D))ᵀ = S.gram.map (incA D) := by
    ext a b
    exact congrArg (incA D) (show star (S.gram b a) = S.gram a b from S.herm.eq (S.frame b) (S.frame a))
  rw [Matrix.map_mul, Matrix.transpose_mul, e0, ← Matrix.mul_assoc, GlobalTheory.RouteCoords.inv_mul_gram, Matrix.one_mul]
  rfl

theorem linB_ptB {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} (B : Frames G) (t : T)
    {i j : Fin D.R.m} (e : Num G i j) (w : Pl D.host.E)
    (u : Matrix (Fin (spW₁ G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)) :
    linB B t i j w (ptB e u) =
      reindex (finCongr (rankW₁ G t i j w)) (colsEq t e w) (((loc w (B.β i j))⁻¹).val *
        u.map (fun a => cpt w (toEAf D (cA D a))) *
        GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e ((spV G i j).gram.map (algebraMap D.host.E (Kw w)) * (loc w (B.β i (j + 1))).val)
          (-((spV₁ G i j).gram.map (algebraMap D.host.E (Kw w)) * (loc w (B.β (i + 1) j)).val))) := by
  have h1 := adj_coord (spW₁ G i j) (spX G i j) (u.submatrix id (e.symm.trans finSumFinEquiv).symm)
  have h2 : (((spX G i j).gram.map (incA D)).map (toEAf D)).map (cpt w) = GlobalTheory.Doubling.blkMat finSumFinEquiv
      ((spV G i j).gram.map (algebraMap D.host.E (Kw w))) ((spV₁ G i j).gram.map (algebraMap D.host.E (Kw w))) := by
    rw [GlobalTheory.Doubling.gram_hsum]
    refine Matrix.ext fun a b => ?_
    refine (GlobalTheory.FunObj.Good.cpt_incA w _).trans ?_
    obtain ⟨a | a, rfl⟩ := finSumFinEquiv.surjective a <;> obtain ⟨b | b, rfl⟩ := finSumFinEquiv.surjective b <;>
      simp [GlobalTheory.Doubling.blkMat, -finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right]
  have h3 : (frX B i j).val.map (cpt w) = GlobalTheory.Doubling.blkMat finSumFinEquiv (loc w (B.β i (j + 1))).val
      (-(loc w (B.β (i + 1) j)).val) := by
    refine Matrix.ext fun a b => ?_
    change cpt w (GlobalTheory.Doubling.blkMat finSumFinEquiv (B.β i (j + 1)).val (-(B.β (i + 1) j).val) a b) = _
    obtain ⟨a | a, rfl⟩ := finSumFinEquiv.surjective a <;> obtain ⟨b | b, rfl⟩ := finSumFinEquiv.surjective b <;>
      simp [GlobalTheory.Doubling.blkMat, -finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right]
  have h4 : (frMapAdj (spW₁ G i j) (spX G i j) (B.β i j) (frX B i j) (ptB e u)).map (cpt w) =
      ((loc w (B.β i j))⁻¹).val * ((u.map (fun a => cpt w (toEAf D (cA D a)))).submatrix id
        (e.symm.trans finSumFinEquiv).symm * GlobalTheory.Doubling.blkMat finSumFinEquiv
      ((spV G i j).gram.map (algebraMap D.host.E (Kw w))) ((spV₁ G i j).gram.map (algebraMap D.host.E (Kw w)))) *
      GlobalTheory.Doubling.blkMat finSumFinEquiv (loc w (B.β i (j + 1))).val (-(loc w (B.β (i + 1) j)).val) := by
    rw [← h2, ← h3]
    unfold frMapAdj
    erw [h1]
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul]
    rfl
  refine Matrix.ext fun r c => ?_
  unfold linB
  rw [h4]
  exact reindex_blocks e _ _ _ _ _ _ _ _ c

open GlobalTheory.FlipMatch.ChartOpp hiding isHalf_of_mulG in

theorem exists_mixChart_linB : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (B : Frames G) (t : T) (i j : Fin D.R.m) (M : Vol G), SquareStanding G t →
    ∀ (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : Chars D.host.F D.host.E)
      (om : Rep D.sp.cm.sig Γ.V Γ.W) (om' : Rep D.sp.cm.sig Γ.V' Γ.W), IsTripleOf W M t i j e Bs Γ X →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' → IsDoublyCompatible t i j e Bs Γ X →
    ∀ (v : Bs.P) (w : Pl D.host.E), splitPrime (Bs.τ v) = w → ∀ jj : Fv D.host.F v ≃+* Kw w, IsPlaceIso (Bs.τ v) w jj → IsLocIso jj →
    ∀ cc : GL (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (Kw w), (Γ.W.bas v).val.map jj * cc.val = basCols B e w →
    ∃ g : GL (Fin (spW₁ G i j).rank) (Kw w),
      IsMixChart v.1 (mixHalfS e (atPl w 1)) (mixHalfS e (cA D (atPl w 1))) (mixCoS B t e w)
        (fun u => chart jj (finCongr (rankW₁ G t i j w)) (colsEq t e w) g cc
          (coY D.sp.cm.sig Γ.V' Γ.W (Bs.τ v) (Γ.V'.bas v) (Γ.W.bas v) u))
        (fun u => (xiAt w)⁻¹ • chart jj (finCongr (rankW₁ G t i j w)) (colsEq t e w) (invT g) (invT cc)
          (coX (Bs.τ v) (Γ.V'.bas v) (Γ.W.bas v) u))
        (Assignment.one.block _ _) ∧
      ∀ u, chart jj (finCongr (rankW₁ G t i j w)) (colsEq t e w) g cc
          (coY D.sp.cm.sig Γ.V' Γ.W (Bs.τ v) (Γ.V'.bas v) (Γ.W.bas v) u) = linB B t i j w (ptB e u) := by
  intro D T L sc G μ₀ _ W B t i j M _ e Bs Γ X _ _ h _ _ v w hw jj hjj _ cc hcc
  classical

  have hε : atPl w 1 = GlobalTheory.EmbChart.idem (Bs.τ v) :=
    (GlobalTheory.IdemAtPl.eq_atPl_of_isIdemAt (hw ▸ GlobalTheory.EmbChart.isIdemAt_idem (Bs.τ v))).symm
  have hsum : GlobalTheory.EmbChart.idem (Bs.τ v) + cA D (GlobalTheory.EmbChart.idem (Bs.τ v)) =
      algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v.1 1) := by
    rw [GlobalTheory.EmbChart.cA_idem, GlobalTheory.EmbChart.idem, ← LinearMap.map_add, add_sub_cancel]; rfl
  have hii := GlobalTheory.SrcHalfOne.idem_mul_self (Bs.τ v)
  have hic : GlobalTheory.EmbChart.idem (Bs.τ v) * cA D (GlobalTheory.EmbChart.idem (Bs.τ v)) = 0 :=
    (GlobalTheory.EmbChart.isSplitIdem_idem (Bs.τ v)).2.1
  have hcc' : cA D (GlobalTheory.EmbChart.idem (Bs.τ v)) * cA D (GlobalTheory.EmbChart.idem (Bs.τ v)) =
      cA D (GlobalTheory.EmbChart.idem (Bs.τ v)) := by rw [← map_mul, hii]
  have hb₁ : GlobalTheory.EmbChart.idem (Bs.τ v) * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v.1 1) =
      GlobalTheory.EmbChart.idem (Bs.τ v) := by rw [← hsum, mul_add, hii, hic, add_zero]
  have hb₂ : cA D (GlobalTheory.EmbChart.idem (Bs.τ v)) * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v.1 1) =
      cA D (GlobalTheory.EmbChart.idem (Bs.τ v)) := by
    rw [← hsum, mul_add, mul_comm (cA D _) (GlobalTheory.EmbChart.idem _), hic, zero_add, hcc']
  rw [hε]

  have hzero : cpt w (toEAf D (cA D (GlobalTheory.EmbChart.idem (Bs.τ v)))) = 0 := by
    rw [← hjj]
    exact (congrArg jj (GlobalTheory.SrcHalfOne.piW_cA_idem (Bs.τ v))).trans (map_zero jj)
  have hE : ∀ x : D.host.E, jj (Bs.τ v x) = algebraMap D.host.E (Kw w) x := fun x => by
    rw [← GlobalTheory.FunObj.Good.cpt_incA w x, ← hjj]
    exact congrArg jj (GlobalTheory.LocFrame.piW_incA (Bs.τ v) x).symm
  have hcA : ∀ a, jj (piW ((Bs.τ v).comp D.sp.cm.sig) a) = cpt w (toEAf D (cA D a)) := fun a => by
    rw [← hjj]
    exact congrArg jj (GlobalTheory.SrcHalfOne.piW_cA (Bs.τ v) a).symm

  obtain ⟨κ, hκ⟩ : ∃ κ : D.host.E →+* Kw w, κ = algebraMap D.host.E (Kw w) := ⟨_, rfl⟩
  obtain ⟨Bp, hBp⟩ : ∃ Bp : GL (Fin (spW₁ G i j).rank) (Kw w),
    Bp = Matrix.GeneralLinearGroup.map (jj : Fv D.host.F v.1 →+* Kw w) (Γ.V'.bas v) := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : GL (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (Kw w),
    C = Matrix.GeneralLinearGroup.map (jj : Fv D.host.F v.1 →+* Kw w) (Γ.W.bas v) := ⟨_, rfl⟩
  have hG₁ : ((spW₁ G i j).gram.map κ).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero κ).2 (GlobalTheory.RouteCoords.gram_det_ne _)
  have hξ : xiAt w ≠ 0 := (map_ne_zero _).2 GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero
  have hCc : C.val * cc.val = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e (loc w (B.β i (j + 1))).val (-(loc w (B.β (i + 1) j)).val) := by
    rw [hC]; exact hcc
  obtain ⟨g, hg⟩ := chart_algebra e Bp C cc _ hG₁ (loc w (B.β i j)) (loc w (B.β i (j + 1))) (loc w (B.β (i + 1) j))
    ((spV G i j).gram.map κ) ((spV₁ G i j).gram.map κ) (xiAt w) hξ hCc
  refine ⟨g, ?_⟩

  have hκm : ∀ {a b : Type} (Z : Matrix a b D.host.E), (Z.map (Bs.τ v)).map jj = Z.map κ := fun Z =>
    Matrix.ext fun _ _ => by rw [hκ]; exact hE _
  have hX : ∀ u, (coX (Bs.τ v) (Γ.V'.bas v) (Γ.W.bas v) u).map jj =
      (Bp⁻¹).val * u.map (fun a => cpt w (toEAf D a)) * ((C⁻¹).val)ᵀ := fun u => by
    unfold coX
    rw [map_mul_equiv, map_mul_equiv, Matrix.transpose_map, Matrix.map_map]
    have : u.map (⇑jj ∘ ⇑(piW (Bs.τ v))) = u.map (fun a => cpt w (toEAf D a)) := Matrix.ext fun _ _ => hjj _
    rw [this, hBp, hC]
    rfl
  have hJ1 : (Γ.V'.J.map (Bs.τ v)).map jj = -((spW₁ G i j).gram.map κ) := by
    rw [hκm, h.JW₁]
    ext a b
    simp
  have hJ2 : ((Γ.W.J.map (Bs.τ v))ᵀ).map jj = xiAt w • GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e ((spV G i j).gram.map κ) ((spV₁ G i j).gram.map κ) := by
    rw [Matrix.transpose_map, hκm, h.JWW, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram]
    ext a b
    simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk,
      Matrix.reindex_apply, Matrix.submatrix_apply]
    rcases e.symm a with a | a <;> rcases e.symm b with b | b <;> simp [xiAt, hκ]
  have hY : ∀ u, (coY D.sp.cm.sig Γ.V' Γ.W (Bs.τ v) (Γ.V'.bas v) (Γ.W.bas v) u).map jj =
      -(Bp.valᵀ * (-((spW₁ G i j).gram.map κ)) * u.map (fun a => cpt w (toEAf D (cA D a))) *
        (xiAt w • GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e ((spV G i j).gram.map κ) ((spV₁ G i j).gram.map κ)) * C.val) := fun u => by
    unfold coY
    rw [Matrix.map_neg _ (map_neg jj), map_mul_equiv, map_mul_equiv, map_mul_equiv, map_mul_equiv, hJ1, hJ2,
      Matrix.map_map]
    have : u.map (⇑jj ∘ ⇑(piW ((Bs.τ v).comp D.sp.cm.sig))) = u.map (fun a => cpt w (toEAf D (cA D a))) :=
      Matrix.ext fun _ _ => hcA _
    rw [this, Matrix.transpose_map, hBp, hC]
    rfl

  have htr : ∀ u, chart jj (finCongr (rankW₁ G t i j w)) (colsEq t e w) g cc
      (coY D.sp.cm.sig Γ.V' Γ.W (Bs.τ v) (Γ.V'.bas v) (Γ.W.bas v) u) =
      reindex (finCongr (rankW₁ G t i j w)) (colsEq t e w) (((loc w (B.β i j))⁻¹).val *
        u.map (fun a => cpt w (toEAf D (cA D a))) *
        GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e ((spV G i j).gram.map κ * (loc w (B.β i (j + 1))).val)
          (-((spV₁ G i j).gram.map κ * (loc w (B.β (i + 1) j)).val))) := fun u => by
    unfold chart
    rw [hY, (hg 0 _).1]
  have hmu : ∀ u, (xiAt w)⁻¹ • chart jj (finCongr (rankW₁ G t i j w)) (colsEq t e w) (invT g) (invT cc)
      (coX (Bs.τ v) (Γ.V'.bas v) (Γ.W.bas v) u) =
      reindex (finCongr (rankW₁ G t i j w)) (colsEq t e w) ((loc w (B.β i j)).valᵀ * ((spW₁ G i j).gram.map κ)ᵀ *
        u.map (fun a => cpt w (toEAf D a)) *
        GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e (((loc w (B.β i (j + 1)))⁻¹).val)ᵀ (-(((loc w (B.β (i + 1) j))⁻¹).val)ᵀ)) := fun u => by
    unfold chart
    rw [hX, ← (hg (u.map fun a => cpt w (toEAf D a)) 0).2]
    rfl
  have hinc : ∀ x : D.host.E, cpt w (toEAf D (inclR (AF D.host.F) x)) = κ x := fun x => by
    rw [hκ]; exact GlobalTheory.FunObj.Good.cpt_incA w x
  have hPl : ∀ k, colsEq t e w (e (.inl k)) ∈ Assignment.one.block _ _ := fun k => by
    rw [colsEq_inl]; exact Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩
  have hPr : ∀ k, colsEq t e w (e (.inr k)) ∉ Assignment.one.block _ _ := fun k hk => by
    rw [colsEq_inr] at hk; exact Bool.false_ne_true (Finset.mem_filter.1 hk).2

  have z₁ : ∀ z : AE D, GlobalTheory.EmbChart.idem (Bs.τ v) * z = z → cpt w (toEAf D (cA D z)) = 0 := fun z hz => by
    rw [← hz, RingHom.map_mul, RingHom.map_mul, RingHom.map_mul, hzero, zero_mul]
  have z₂ : ∀ z : AE D, cA D (GlobalTheory.EmbChart.idem (Bs.τ v)) * z = z → cpt w (toEAf D z) = 0 := fun z hz => by
    rw [← hz, RingHom.map_mul, RingHom.map_mul, hzero, zero_mul]
  have hat : ∀ (u : Matrix (Fin (spW₁ G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)) (b b' : AE D),
      b * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v.1 1) = b →
      b' * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v.1 1) = b' →
      IsHalf b (u.submatrix id fun k => e (.inl k)) → IsHalf b' (u.submatrix id fun k => e (.inr k)) →
      At (evFin D.host.F v.1) u := fun u b b' hb hb' h1 h2 c hc => by
    have k1 := GlobalTheory.BigDat.smul_eq_zero_of_isHalf v.1 hb h1 c hc
    have k2 := GlobalTheory.BigDat.smul_eq_zero_of_isHalf v.1 hb' h2 c hc
    refine Matrix.ext fun a s => ?_
    obtain ⟨z, rfl⟩ := e.surjective s
    rcases z with k | k
    · exact congrFun₂ k1 a k
    · exact congrFun₂ k2 a k
  refine ⟨?_, fun u => by rw [htr, linB_ptB, hκ]⟩
  unfold IsMixChart
  simp only [htr, hmu]
  refine ⟨fun u hu => ?_, fun u hu => ?_⟩
  · have h1 : IsHalf (GlobalTheory.EmbChart.idem (Bs.τ v)) (u.submatrix id fun k => e (.inl k)) := fun a c =>
      GlobalTheory.FlipMatch.ChartOpp.isHalf_of_mulG _ hu.1 c a
    have h2 := isHalf_cA_of_adjV₁ e hu.2
    have hZ : ((u.map fun a => cpt w (toEAf D (cA D a))).submatrix id fun k => e (.inl k)) = 0 :=
      Matrix.ext fun a k => z₁ _ (h1 a k)
    have hU : ((u.map fun a => cpt w (toEAf D a)).submatrix id fun k => e (.inr k)) = 0 :=
      Matrix.ext fun a k => z₂ _ (h2 a k)
    exact ⟨hat u _ _ hb₁ hb₂ h1 h2, zero_inl e _ _ _ hPr _ _ _ _ hZ, zero_inr e _ _ _ hPl _ _ _ _ hU,
      eq_add_of_blocks e _ _ _ _ _ _ _ _ _ _ _ hZ hU (mixCoS_inl t e w B κ hinc u) (mixCoS_inr t e w B κ hinc u)⟩
  · have h1 : IsHalf (cA D (GlobalTheory.EmbChart.idem (Bs.τ v))) (u.submatrix id fun k => e (.inl k)) := fun a c =>
      GlobalTheory.FlipMatch.ChartOpp.isHalf_of_mulG _ hu.1 c a
    have h2 := isHalf_cA_of_adjV₁ e hu.2
    rw [Formalism.L2.Theta.cA_cA] at h2
    have hZ : ((u.map fun a => cpt w (toEAf D (cA D a))).submatrix id fun k => e (.inr k)) = 0 :=
      Matrix.ext fun a k => z₁ _ (h2 a k)
    have hU : ((u.map fun a => cpt w (toEAf D a)).submatrix id fun k => e (.inl k)) = 0 :=
      Matrix.ext fun a k => z₂ _ (h1 a k)
    exact ⟨hat u _ _ hb₂ hb₁ h1 h2, zero_inr e _ _ _ hPl _ _ _ _ hZ, zero_inl e _ _ _ hPr _ _ _ _ hU⟩

end GlobalTheory.TopFlip.ChartB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSeesawTripleMovedToSelfDualIsValid
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
open GlobalTheory.BotMove
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.Grid Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Mult MeasureTheory

noncomputable section

namespace GlobalTheory.BotMove

theorem rig_move {D : D7} {V : HSp D} (rr : Rig V) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (g : GA D V)
    (hr : rr.Is) (hΛ : IsSelfDualC V Λ) (hm : GlobalTheory.FinPl.Moves V g rr.Λ Λ (fun _ => True)) :
    Rig.Is (⟨Λ, Lev.finE V g * rr.β, rr.s, rr.B⟩ : Rig V) :=
  ⟨hΛ, GlobalTheory.Core.Mi.FrameMove.isFrame_of_moves D V g rr.Λ Λ rr.β hm hr.2.1, hr.2.2⟩

theorem moveTri_is : ∀ {D : D7} {T : Type} {A A' WW : HSp D} (Y : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (α β : T → ((AE D)ˣ →* Circle)) (νH : T → HChar D.host.E) (S : T → Finset (Formalism.L2.DIV.Pl D.host.E)),
    Y.Is ψ θ α β νH S →
    ∀ (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (ΛA' : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E))
      (ΛW : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)),
    IsSelfDualC A ΛA → IsSelfDualC A' ΛA' → IsSelfDualC WW ΛW →
    ∀ g ∈ GfC A, ∀ g' ∈ GfC A', ∀ h ∈ GfC WW,
    GlobalTheory.FinPl.Moves A g Y.rA.Λ ΛA (fun _ => True) → GlobalTheory.FinPl.Moves A' g' Y.rA'.Λ ΛA' (fun _ => True) →
    GlobalTheory.FinPl.Moves WW h Y.rW.Λ ΛW (fun _ => True) →
    ∀ (t₀ : T) (r r' : T → ℂ), (∀ t, r t ≠ 0 ∧ r' t ≠ 0) →
    (∀ t, Y.ω t (g, h) Y.vac = r t • Y.ω t₀ (g, h) Y.vac) → (∀ t, Y.ω' t (g', h) Y.vac' = r' t • Y.ω' t₀ (g', h) Y.vac') →
    (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').Is ψ θ α β νH S := by
  intro D T A A' WW Y ψ θ α β νH S hY ΛA ΛA' ΛW hA hA' hW g hg g' hg' h hh mA mA' mW t₀ r r' hr hv hv'
  exact ⟨hY.rank, rig_move _ _ _ hY.rigA hA mA, rig_move _ _ _ hY.rigA' hA' mA', rig_move _ _ _ hY.rigW hW mW, hY.weil,
    hY.weil', GlobalTheory.T.movedVacuum_negHom_eq_vacuum_movedLattices Y ψ θ α β νH S hY ΛA ΛA' ΛW hA hA' hW g hg g' hg' h hh mA mA' mW t₀ r r' hr hv hv', GlobalTheory.T.movedVacuum_hom_eq_vacuum_movedLattices Y ψ θ α β νH S hY ΛA ΛA' ΛW hA hA' hW g hg g' hg' h hh mA mA' mW t₀ r r' hr hv hv', hY.idem, hY.expo, GlobalTheory.T.movedFiniteDatum_negHom_eq_standardPair_first Y ψ θ α β νH S hY ΛA ΛA' ΛW hA hA' hW g hg g' hg' h hh mA mA' mW t₀ r r' hr hv hv',
    GlobalTheory.T.translated_finite_datum_eq_standardPairSecondMember Y ψ θ α β νH S hY ΛA ΛA' ΛW hA hA' hW g hg g' hg' h hh mA mA' mW t₀ r r' hr hv hv', GlobalTheory.T.haar_fundamentalDomain_rightTranslate_unitary _ _ g hY.meas.1 hY.meas.2, GlobalTheory.T.haar_fundamentalDomain_rightTranslate_unitary _ _ g' hY.meas'.1 hY.meas'.2⟩

end GlobalTheory.BotMove

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaStepFactorRatioUnitGaussSumQuotient
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

namespace GlobalTheory.SqStepArith

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Chars Base stepFac chrW eps idealVal)

theorem stepFac_ratio_core {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) {μ₀ : T} (hL : Lc.Is μ₀)
    (W : G.Weil) (S : GridChoice W Set.univ) (hN : NumbersIn D.what₂.embLL S μ₀) (i j : Fin D.R.m) (t : T)
    (Bs : Base D.host.F D.host.E) (e₁ e₂ s : ℤˣ) (𝔟 𝔠 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) (z : ℤ)
    (hB : GlobalTheory.SqStep.BaseFits G W i j t Bs) (h0 : stepFac Bs (GlobalTheory.SqStep.chs G i j t) e₁ e₂ s 𝔟 𝔠 z ≠ 0) :
    GlobalTheory.Square.StepRatio D.what₂.embLL (Qn G t) G.pl.S0 (condExp G.pl) (fun v => Ideal.absNorm v.asIdeal)
      (stepFac Bs (GlobalTheory.SqStep.chs G i j μ₀) e₁ e₂ s 𝔟 𝔠 z) (stepFac Bs (GlobalTheory.SqStep.chs G i j t) e₁ e₂ s 𝔟 𝔠 z) := by
  classical
  have hQn : 0 < Qn G t := Finset.prod_pos fun w _ => Nat.pos_of_ne_zero fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  obtain ⟨hc1, -, hcmul, hcinv, -⟩ := GlobalTheory.Square.isAwayUnit_closure D.what₂.LL (Qn G t) hQn
  have hone : GlobalTheory.Square.IsAwayUnit (Qn G t) (1 : D.what₂.LL) := GlobalTheory.Square.IsAwayUnit.one _
  have hzpow : ∀ (x : D.what₂.LL) (n : ℕ), 0 < n → x ^ n = 1 → ∀ e : ℤ, GlobalTheory.Square.IsAwayUnit (Qn G t) (x ^ e) := by
    intro x n hn hx e
    refine hc1 _ n hn ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]
  have hprod : ∀ (s : Finset Bs.P) (f : Bs.P → D.what₂.LL), (∀ v ∈ s, GlobalTheory.Square.IsAwayUnit (Qn G t) (f v)) →
      GlobalTheory.Square.IsAwayUnit (Qn G t) (∏ v ∈ s, f v) := by
    intro s f hf
    induction s using Finset.induction_on with
    | empty => simpa using hone
    | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact hcmul _ _ (hf a (Finset.mem_insert_self _ _)) (ih fun v hv => hf v (Finset.mem_insert_of_mem hv))
  set σ := D.what₂.embLL with hσ
  set X₀ := GlobalTheory.SqStep.chs G i j μ₀ with hX₀
  set X := GlobalTheory.SqStep.chs G i j t with hX
  set Sz := G.pl.S0 with hS0
  set f : Chars D.host.F D.host.E → Bs.P → ℂ := fun Y v =>
    (chrW Y.ν (Bs.τ v) (Units.map (Int.castRingHom _).toMonoidHom s) : ℂ) * eps Bs.ψ (chrW Y.ν (Bs.τ v)) z with hf
  have hS0T : Sz ⊆ X.T := Finset.subset_union_left
  have hT0 : X₀.T = Sz := GlobalTheory.SqStepArith.chs_T_base G hL i j
  have hst : ∀ Y : Chars D.host.F D.host.E, stepFac Bs Y e₁ e₂ s 𝔟 𝔠 z =
      ((idealVal Y.ν 𝔟 : ℂ)) ^ (e₁ : ℤ) * ((idealVal Y.ν 𝔠 : ℂ)) ^ (e₂ : ℤ) *
        ∏ v ∈ Finset.univ.filter (fun v : Bs.P => v.1 ∈ Y.T), f Y v := by
    intro Y
    simp only [stepFac, Units.val_mul, Units.val_zpow_eq_zpow_val, hf]

  have hsplit : ∏ v ∈ Finset.univ.filter (fun v : Bs.P => v.1 ∈ X.T), f X v =
      (∏ v ∈ Finset.univ.filter (fun v : Bs.P => v.1 ∈ Sz), f X v) *
        ∏ v ∈ Finset.univ.filter (fun v : Bs.P => v.1 ∈ X.T ∧ v.1 ∉ Sz), f X v := by
    rw [← Finset.prod_filter_mul_prod_filter_not (Finset.univ.filter (fun v : Bs.P => v.1 ∈ X.T)) (fun v : Bs.P => v.1 ∈ Sz),
      Finset.filter_filter, Finset.filter_filter]
    congr 2
    · ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => h.2, fun h => ⟨hS0T h, h⟩⟩
  have hne : ∀ v : Bs.P, v.1 ∈ Sz → f X v ≠ 0 := by
    intro v hv
    rw [hst, hsplit] at h0
    have h1 := left_ne_zero_of_mul (right_ne_zero_of_mul h0)
    exact (Finset.prod_ne_zero_iff.1 h1) v (by simpa using hv)
  have hS := fun (v : Bs.P) (hv : v.1 ∈ Sz) => GlobalTheory.T.base_place_character_factor G hL W S hN i j t Bs hB v hv s z (hne v hv)
  choose bS gS gS' hbS hgS hgS' heS using hS
  have hneT : ∀ v : Bs.P, v.1 ∈ X.T → v.1 ∉ Sz → f X v ≠ 0 := by
    intro v hv hv'
    rw [hst, hsplit] at h0
    have h1 := right_ne_zero_of_mul (right_ne_zero_of_mul h0)
    exact (Finset.prod_ne_zero_iff.1 h1) v (by simpa using And.intro hv hv')
  have hTw := fun (v : Bs.P) (hv : v.1 ∈ X.T) (hv' : v.1 ∉ Sz) => GlobalTheory.T.twistPlace_stepFactor_inverse_awayUnit G hL W S hN i j t Bs hB v hv hv' s z (hneT v hv hv')
  choose bT hbT heT using hTw
  obtain ⟨b1, ⟨n1, hn1, hb1⟩, e1⟩ := GlobalTheory.T.squareStepChar_idealValue_eq_base_mul_rootOfUnity G hL W S hN i j t 𝔟
  obtain ⟨b2, ⟨n2, hn2, hb2⟩, e2⟩ := GlobalTheory.T.squareStepChar_idealValue_eq_base_mul_rootOfUnity G hL W S hN i j t 𝔠
  let bS₁ : Bs.P → D.what₂.LL := fun v => if h : v.1 ∈ Sz then bS v h else 1
  let bT₁ : Bs.P → D.what₂.LL := fun v => if h : v.1 ∈ X.T ∧ v.1 ∉ Sz then bT v h.1 h.2 else 1
  let g : HeightOneSpectrum (𝓞 D.host.F) → 𝓞 D.what₂.LL := fun v => if h : v ∈ Bs.P ∧ v ∈ Sz then gS ⟨v, h.1⟩ h.2 else 1
  let g' : HeightOneSpectrum (𝓞 D.host.F) → 𝓞 D.what₂.LL := fun v => if h : v ∈ Bs.P ∧ v ∈ Sz then gS' ⟨v, h.1⟩ h.2 else 1
  have hSP : ∀ v ∈ Sz, v ∈ Bs.P := fun v hv => hB.2.1 (hS0T hv)

  have hmap : ∀ F' : HeightOneSpectrum (𝓞 D.host.F) → D.what₂.LL,
      ∏ v ∈ Finset.univ.filter (fun v : Bs.P => v.1 ∈ Sz), F' v.1 = ∏ v ∈ Sz, F' v := by
    intro F'
    rw [show (∏ v ∈ Finset.univ.filter (fun v : Bs.P => v.1 ∈ Sz), F' v.1) =
        ∏ v ∈ (Finset.univ.filter (fun v : Bs.P => v.1 ∈ Sz)).map (Function.Embedding.subtype _), F' v from
      (Finset.prod_map (Finset.univ.filter (fun v : Bs.P => v.1 ∈ Sz)) (Function.Embedding.subtype _) F').symm]
    congr 1
    ext v
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Function.Embedding.coe_subtype]
    exact ⟨fun ⟨w, hw, e⟩ => e ▸ hw, fun hv => ⟨⟨v, hSP v hv⟩, hv, rfl⟩⟩
  refine ⟨b1 ^ (e₁ : ℤ) * b2 ^ (e₂ : ℤ) * (∏ v ∈ Finset.univ.filter (fun v : Bs.P => v.1 ∈ Sz), bS₁ v) *
    (∏ v ∈ Finset.univ.filter (fun v : Bs.P => v.1 ∈ X.T ∧ v.1 ∉ Sz), bT₁ v), g, g', ?_, ?_, ?_⟩
  · refine hcmul _ _ (hcmul _ _ (hcmul _ _ (hzpow b1 n1 hn1 hb1 _) (hzpow b2 n2 hn2 hb2 _)) ?_) ?_
    · refine hprod _ _ fun v hv => ?_
      have hv' : v.1 ∈ Sz := by simpa using hv
      simp only [bS₁, dif_pos hv']
      exact hbS v hv'
    · refine hprod _ _ fun v hv => ?_
      have hv' : v.1 ∈ X.T ∧ v.1 ∉ Sz := by simpa using hv
      simp only [bT₁, dif_pos hv']
      exact hbT v hv'.1 hv'.2
  · intro v hv
    have h : v ∈ Bs.P ∧ v ∈ Sz := ⟨hSP v hv, hv⟩
    simp only [g, g', dif_pos h]
    exact ⟨hgS _ h.2, hgS' _ h.2⟩
  · have hA : ∀ v ∈ Finset.univ.filter (fun v : Bs.P => v.1 ∈ Sz),
        f X₀ v = σ (bS₁ v * ((g v.1 : D.what₂.LL) / (g' v.1 : D.what₂.LL))) * f X v := by
      intro v hv
      have hv' : v.1 ∈ Sz := by simpa using hv
      have h2 : v.1 ∈ Bs.P ∧ v.1 ∈ Sz := ⟨v.2, hv'⟩
      simp only [bS₁, g, g', dif_pos hv', dif_pos h2]
      exact heS v hv'
    have hTw : (∏ v ∈ Finset.univ.filter (fun v : Bs.P => v.1 ∈ X.T ∧ v.1 ∉ Sz), f X v) *
        σ (∏ v ∈ Finset.univ.filter (fun v : Bs.P => v.1 ∈ X.T ∧ v.1 ∉ Sz), bT₁ v) = 1 := by
      rw [map_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun v hv => ?_
      have hv' : v.1 ∈ X.T ∧ v.1 ∉ Sz := by simpa using hv
      simp only [bT₁, dif_pos hv']
      rw [mul_comm]
      exact heT v hv'.1 hv'.2
    rw [hst X₀, hst X, hsplit, hT0, Finset.prod_congr rfl hA, Finset.prod_mul_distrib, ← map_prod,
      Finset.prod_mul_distrib, hmap (fun v => (g v : D.what₂.LL) / (g' v : D.what₂.LL)), e1, e2, mul_zpow, mul_zpow]
    simp only [map_mul, map_zpow₀]
    linear_combination (-((σ b1) ^ (e₁ : ℤ) * (σ b2) ^ (e₂ : ℤ) *
      σ (∏ v ∈ Finset.univ.filter (fun v : Bs.P => v.1 ∈ Sz), bS₁ v) *
      σ (∏ v ∈ Sz, (g v : D.what₂.LL) / (g' v : D.what₂.LL)) * ((idealVal X.ν 𝔟 : ℂ)) ^ (e₁ : ℤ) *
      ((idealVal X.ν 𝔠 : ℂ)) ^ (e₂ : ℤ) * ∏ v ∈ Finset.univ.filter (fun v : Bs.P => v.1 ∈ Sz), f X v)) * hTw

end GlobalTheory.SqStepArith

namespace GlobalTheory.SqStepArith

theorem stepFac_ratio : GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (t : T) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (e₁ e₂ s : ℤˣ)
      (𝔟 𝔠 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) (z : ℤ), GlobalTheory.SqStep.BaseFits G W i j t Bs →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j t) e₁ e₂ s 𝔟 𝔠 z ≠ 0 →
      GlobalTheory.Square.StepRatio D.what₂.embLL (Qn G t) G.pl.S0 (condExp G.pl) (fun v => Ideal.absNorm v.asIdeal)
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j μ₀) e₁ e₂ s 𝔟 𝔠 z) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j t) e₁ e₂ s 𝔟 𝔠 z) := by
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ hL G => ?_⟩⟩
  intro W S _ hN i j t Bs e₁ e₂ s 𝔟 𝔠 z hB h0
  exact stepFac_ratio_core G hL W S hN i j t Bs e₁ e₂ s 𝔟 𝔠 z hB h0

end GlobalTheory.SqStepArith
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedLiftInvariantExtensionLocalisationStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_lift_invariantExtension_localisation : ∀ (A B A₂ : Type) [CommRing A] [IsLocalRing A] [CommRing B] [Algebra A B] [CommRing A₂] [IsLocalRing A₂] (G : Type) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B] [Algebra.IsInvariant A B G] (f : B →+* A₂), IsLocalHom (f.comp (algebraMap A B)) → (∀ y : A₂, ∃ b s : B, IsUnit (f s) ∧ y * f s = f b) → (∀ b : B, f b = 0 → ∃ s : B, IsUnit (f s) ∧ s * b = 0) → ∀ (V' : Type) [CommRing V'] [IsLocalRing V'] (e₁ : A →+* V') (β : B →+* V'), IsLocalHom e₁ → β.comp (algebraMap A B) = e₁ → ∃ ev₂ : A₂ →+* V', IsLocalHom ev₂ ∧ ev₂.comp (f.comp (algebraMap A B)) = e₁ := by
  first | exact @GlobalTheory.twisted_lift_to_localisation | exact GlobalTheory.twisted_lift_to_localisation | (intros; apply GlobalTheory.twisted_lift_to_localisation <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedSplittingCharacterUnitOffPlacesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open Formalism.IndefR.Fin Formalism.IndefR.Fin.LevelGroupLemmas
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_splitting_character_unit_off_places : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m), VStd D i → ∀ (ξ : Formalism.L2.Host.HChar D.host.E) (χ : (AE D)ˣ →* Circle) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ω : WeilRep D i) (φ : WO (Vc D i) (Wc D i) → ℂ), KerDat R i ξ χ ξR Q ω φ → (∃ t, Q ⊆ R.Q t) → ∀ N : ℕ, N ≠ 0 → (∀ PP ∈ Q, (N : 𝓞 D.host.E) ∈ PP.asIdeal) → ∀ eQ : AE D, IsIdemSum eQ Q → ∀ ϖ : 𝓞 D.host.E, (ϖ : D.host.E) ≠ 0 → (∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) → ∀ z : GA D (Vc D i), mt (Vc D i) z = Matrix.diagonal (fun _ => eQ * incA D ((ϖ : D.host.E)⁻¹) + cA D eQ * cA D (incA D (ϖ : D.host.E)) + (1 - eQ - cA D eQ)) → ∀ x : (AE D)ˣ, IsDetAt (cA D eQ) (Vc D i) z x → UnitOff N ((((Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 x : Circle) : ℂ))⁻¹ := by
  first | exact @GlobalTheory.DilChi.chi_unitOff | exact GlobalTheory.DilChi.chi_unitOff | (intros; apply GlobalTheory.DilChi.chi_unitOff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniqueUpToTargetGroupStatement
section
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unique_up_to_target_group : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (ψ : ∀ k : (uAt r v i).Comp, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] latQ p r i v k) (γ : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l) (k k₁ k₂ : (uAt r v i).Comp) (a₁ a₂ : GL (Fin D.R.r) D.host.E), IsTransp p r i v ψ γ k k₁ a₁ → IsTransp p r i v ψ γ k k₂ a₂ → k₁ = k₂ ∧ a₁ * a₂⁻¹ ∈ ((uAt r v i).X k₁).Γ := by
  first | exact @GlobalTheory.ShareOn.IsTransp.uniq | exact GlobalTheory.ShareOn.IsTransp.uniq | (intros; apply GlobalTheory.ShareOn.IsTransp.uniq <;> assumption)
end

