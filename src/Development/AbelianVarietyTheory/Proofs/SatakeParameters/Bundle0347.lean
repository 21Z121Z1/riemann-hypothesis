import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0275
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IntegralGLSuccEmbeddingMemParahoricTimesPrincipa
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0344
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0343
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0346
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0345
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivFrameBTheta
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0031
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0027
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0019
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0006
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0239
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0342
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0144
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0007
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.AdmissibleEntriesOfKernelLaw
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanRangeEmb4EqTop
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FrecAt
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.MovDXiAtRecStep
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0002
import Formalism.LocalToGlobal.GlobalTheory.BaseLatticeSelfDual
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepComb

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompanionLatticeEqPointLatticeOverCompanion
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LatCoCompan

open Formalism.L2.GlobalTheoryTheory.Comp in

theorem latCo_eq_latAd_compan : ∀ (D : D7) (i : ℕ) (hi : i ≤ D.R.m) (co : GL (Fin (D.R.N i)) D.host.E), cT (sigD D : D.host.E →+* D.host.E) co.1 * co.1 = gramN D i hi → ∀ (a : 𝓞 D.host.E) (x : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (Lb : Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)), Module.Finite (𝓞 D.host.E) Lb → Submodule.span D.host.E (Lb : Set (Fin (D.R.N i) → D.host.E)) = ⊤ → latCo D.sp (gramN D i hi) co a x.1 Lb = latAd (ratA D.host.F co * x.1) (compan (sp := D.sp) (gramN D i hi) a Lb) ∧ Module.Finite (𝓞 D.host.E) (compan (sp := D.sp) (gramN D i hi) a Lb) ∧ Submodule.span D.host.E ((compan (sp := D.sp) (gramN D i hi) a Lb : Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)) : Set (Fin (D.R.N i) → D.host.E)) = ⊤ := by
  intro D i hi co hco a x Lb hfin hspan
  have horth : IsOrthCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) (toLE co) := by
    intro u v
    have h := hform_mulVec_rect (D.sp.cm.sig : D.host.E →+* D.host.E) (1 : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E)
      (co.1 : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E) u v
    rw [Matrix.mul_one] at h
    have hc : cT (D.sp.cm.sig : D.host.E →+* D.host.E) co.1 * co.1 = (gramN D i hi) := hco
    rw [hc] at h
    have e1 : hform (D.sp.cm.sig : D.host.E →+* D.host.E) 1 (co.1 *ᵥ u) (co.1 *ᵥ v) =
        ∑ b, (D.sp.cm.sig : D.host.E →+* D.host.E) ((co.1 *ᵥ u) b) * (co.1 *ᵥ v) b := by
      simp only [hform, Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
        Finset.mem_univ, if_true]
    rw [e1] at h
    exact h
  have hJ : ∀ M : Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E), IsLat M → IsLat (dl D.sp.cm.sig (gramN D i hi) M) :=
    fun M hM => GlobalTheory.OrthDual.isLat_dl D.sp.cm.sig (gramN D i hi) (toLE co) horth M hM
  have hLb : IsLat Lb := ⟨hfin, hspan⟩
  have hx : x.1 ∈ UPts D.sp.cm.sig (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := x.2
  have hC : IsLat (compan (sp := D.sp) (gramN D i hi) a Lb) := by
    by_cases ha : a = 0
    · subst ha; rw [GlobalTheory.SDCompan.compan_zero]; exact hLb
    · rw [GlobalTheory.SDCompan.compan_eq]; exact isLat_sup hLb (isLat_smul (hJ _ hLb) ha)
  refine ⟨?_, hC.1, hC.2⟩
  have hG : compan (sp := D.sp) (gramN D i hi) a (latAd x.1 Lb) = latAd x.1 (compan (sp := D.sp) (gramN D i hi) a Lb) := by
    by_cases ha : a = 0
    · subst ha; rw [GlobalTheory.SDCompan.compan_zero, GlobalTheory.SDCompan.compan_zero]
    · rw [GlobalTheory.SDCompan.compan_eq, GlobalTheory.SDCompan.compan_eq, GlobalTheory.SDCompan.latAd_eq, GlobalTheory.SDCompan.latAd_eq]
      exact (glob_companion D.sp.cm.sig (gramN D i hi) hJ hLb ha x.1 hx).symm
  unfold latCo
  rw [hG, latAd_rat]

end GlobalTheory.LatCoCompan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ComplexBlockActionInvReadAsSubstitution
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.TwV.DelA.ActInv

theorem det_inv_gl {n : ℕ} {F : Type} [Field F] (A : GL (Fin n) F) :
    ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = (A : Matrix (Fin n) (Fin n) F).det⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf) {Tau : Type} [Fintype Tau] {n : ℕ}

theorem det_placeBlockMatrix_unit_twist (h : P.m + 1 = n) (pos : (Σ v : Fin P.nV, Fin (P.n' v)) ≃ Tau) (g : Tau → GL (Fin n) ℂ)
    (v : Fin P.nV) (s : Fin (P.n' v)) :
    ((hAt P h pos (fun _ => 1) g v s : GL (Fin (P.m + 1)) ℂ) : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ).det =
      if Even s.val then (g (pos ⟨v, s⟩) : Matrix (Fin n) (Fin n) ℂ).det
      else (g (pos ⟨v, s⟩) : Matrix (Fin n) (Fin n) ℂ).det⁻¹ := by
  unfold hAt
  by_cases hs : Even s.val
  · simp only [hs, if_true, one_mul, inv_one, mul_one]
    show (reM P h (g (pos ⟨v, s⟩) : Matrix (Fin n) (Fin n) ℂ)).det = _
    unfold reM
    rw [Matrix.det_submatrix_equiv_self]
  · simp only [hs, if_false, one_mul, inv_one, mul_one]
    show (Matrix.transpose (((reG P h (g (pos ⟨v, s⟩)))⁻¹ : GL (Fin (P.m + 1)) ℂ) : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ)).det = _
    rw [Matrix.det_transpose, det_inv_gl]
    show (reM P h (g (pos ⟨v, s⟩) : Matrix (Fin n) (Fin n) ℂ)).det⁻¹ = _
    unfold reM
    rw [Matrix.det_submatrix_equiv_self]

theorem inv_placeBlockMatrix_unit_twist (h : P.m + 1 = n) (pos : (Σ v : Fin P.nV, Fin (P.n' v)) ≃ Tau) (g : Tau → GL (Fin n) ℂ)
    (v : Fin P.nV) (s : Fin (P.n' v)) :
    (((hAt P h pos (fun _ => 1) g v s)⁻¹ : GL (Fin (P.m + 1)) ℂ) : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ) =
      if Even s.val then reM P h (((g (pos ⟨v, s⟩))⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)
      else Matrix.transpose (reM P h (g (pos ⟨v, s⟩) : Matrix (Fin n) (Fin n) ℂ)) := by
  unfold hAt
  by_cases hs : Even s.val
  · simp only [hs, if_true, one_mul, inv_one, mul_one]
    rw [← map_inv]
    rfl
  · simp only [hs, if_false, one_mul, inv_one, mul_one]
    rfl

end GlobalTheory.TwV.DelA.ActInv

open GlobalTheory.TwV.DelA.ActInv in

theorem GlobalTheory.TwV.DelA.actC_inv_read : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra (Formalism.MainNotions.FormalGroupSystem.K0 p) Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v), PosTie X D pos Kc ι ρ → ∀ (fd : FData X D) (j : ℕ) (hN : RankTie X D j) (La' : X.Lt (j + 1)) (M : GL (Fin (D.R.N (j + 1))) D.host.E), StdU D M → FrIs fd ρ (j + 1) La' (rkT X D hN) M → ∀ R : XR (X.Pj (j + 1)) ℂ, MvPolynomial.map ι (actC X D pos (j + 1) (rkT X D hN) M⁻¹ R) = ι (∏ τ, embT D τ (M : Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) D.host.E).det ^ (if IsOddPos (pos.symm τ).2 then cT1 X D pos j τ - wT X D pos j τ else -wT X D pos j τ)) • GlobalTheory.FrameB.tau0 X Kc j (GlobalTheory.FrameB.mk Kc fd j La') (MvPolynomial.map ι R) := by
  intro p _ X D pos Kc _ _ _ ι ρ hT fd j hN La' M hU hF R
  have hblk := GlobalTheory.TwV.DelA.blkC_atR_read X D pos Kc ι ρ hT M hU
  have hcoe : ∀ {k : ℕ} {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (g : GL (Fin k) A),
      ((Matrix.GeneralLinearGroup.map f g : GL (Fin k) B) : Matrix (Fin k) (Fin k) B) = (g : Matrix (Fin k) (Fin k) A).map f :=
    fun _ _ => rfl
  have hdm : ∀ {k : ℕ} {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (g : Matrix (Fin k) (Fin k) A),
      (g.map f).det = f g.det := fun f g => (RingHom.map_det f g).symm
  have hev : ∀ (v : X.Pl) (s : Fin (X.G.P.n' v)), Even s.val ↔ ¬ IsOddPos s := by
    intro v s; unfold IsOddPos; rw [Nat.even_iff]; omega
  have hsc : (∏ v, ∏ s, ((Matrix.GeneralLinearGroup.map ι (hAt (X.Pj (j + 1)) (rkT X D hN) (posJ X D pos (j + 1)) (fun _ => 1) (atR D M⁻¹) v s) : GL (Fin ((X.Pj (j + 1)).m + 1)) Kc) : Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj (j + 1)).m + 1)) Kc).det ^ (-eAt (X.Pj (j + 1)) v s)) =
      ι (∏ τ, embT D τ (M : Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) D.host.E).det ^ (if IsOddPos (pos.symm τ).2 then cT1 X D pos j τ - wT X D pos j τ else -wT X D pos j τ)) := by
    rw [map_prod, ← Equiv.prod_comp pos, Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun v _ => Finset.prod_congr rfl fun s _ => ?_
    have he : eAt (X.Pj (j + 1)) v s = eT X D pos (j + 1) (pos ⟨v, s⟩) := by
      show _ = eAt (X.Pj (j + 1)) ((pos.symm (pos ⟨v, s⟩)).1) ((pos.symm (pos ⟨v, s⟩)).2)
      rw [Equiv.symm_apply_apply]
    rw [he, (eT_last_pair X D pos j _).2, Equiv.symm_apply_apply, hcoe, hdm, det_placeBlockMatrix_unit_twist]
    rw [show posJ X D pos (j + 1) = pos from rfl]
    simp only [atR]
    rw [hcoe, hdm, det_inv_gl, map_inv₀]
    split_ifs with h1 h2 h3
    · exact absurd h2 ((hev v s).1 h1)
    · rw [map_inv₀, map_zpow₀, inv_zpow', neg_neg]
      rfl
    · rw [inv_inv, map_zpow₀, neg_sub]
      rfl
    · exact absurd ((hev v s).2 h3) h1
  have hent : ∀ (v : Fin (X.Pj (j + 1)).nV) (s : Fin ((X.Pj (j + 1)).n' v)) (a b : Fin ((X.Pj (j + 1)).m + 1)),
      ((((Matrix.GeneralLinearGroup.map ι (hAt (X.Pj (j + 1)) (rkT X D hN) (posJ X D pos (j + 1)) (fun _ => 1) (atR D M⁻¹) v s) : GL (Fin ((X.Pj (j + 1)).m + 1)) Kc))⁻¹ : GL (Fin ((X.Pj (j + 1)).m + 1)) Kc) : Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj (j + 1)).m + 1)) Kc) a b =
      GlobalTheory.FrameB.mk Kc fd j La' v s (Fin.cast (rankJ X (j + 1)) a) (Fin.cast (rankJ X (j + 1)) b) := by
    intro v s a b
    rw [← map_inv, hcoe, Matrix.map_apply, inv_placeBlockMatrix_unit_twist]
    have hb := congrFun (congrFun (hblk v s).1 (finCongr (rkT X D hN) a)) (finCongr (rkT X D hN) b)
    have hinv : (atR D M (pos ⟨v, s⟩))⁻¹ = atR D M⁻¹ (pos ⟨v, s⟩) := by simp [atR, map_inv]
    unfold GlobalTheory.FrameB.mk mAt
    rw [Matrix.submatrix_apply, Matrix.map_apply, hF v, Matrix.submatrix_apply]
    rw [show posJ X D pos (j + 1) = pos from rfl]
    split_ifs at hb with h2 <;> split_ifs with h1
    · exact absurd h2 ((hev v s).1 h1)
    · simp only [Matrix.map_apply, Matrix.transpose_apply] at hb
      rw [hinv] at hb
      exact hb
    · simp only [Matrix.map_apply] at hb
      have e : ((atR D M⁻¹ (pos ⟨v, s⟩))⁻¹ : GL (Fin (D.R.N (j + 1))) ℂ) = atR D M (pos ⟨v, s⟩) := by rw [← hinv, inv_inv]
      refine Eq.trans ?_ hb
      exact congrArg ι (congrArg (fun g : GL (Fin (D.R.N (j + 1))) ℂ => (g : Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ) (finCongr (rkT X D hN) a) (finCongr (rkT X D hN) b)) e)
    · exact absurd ((hev v s).2 h2) h1
  have hsub : (substR (X.Pj (j + 1)) Kc fun v s => (((Matrix.GeneralLinearGroup.map ι (hAt (X.Pj (j + 1)) (rkT X D hN) (posJ X D pos (j + 1)) (fun _ => 1) (atR D M⁻¹) v s) : GL (Fin ((X.Pj (j + 1)).m + 1)) Kc))⁻¹ : GL (Fin ((X.Pj (j + 1)).m + 1)) Kc)) = GlobalTheory.FrameB.tau0 X Kc j (GlobalTheory.FrameB.mk Kc fd j La') := by
    apply MvPolynomial.algHom_ext
    rintro ⟨v, s, a, t⟩
    simp only [substR, GlobalTheory.FrameB.tau0, MvPolynomial.aeval_X, GlobalTheory.FrameB.frF]
    refine Fintype.sum_equiv (finCongr (rankJ X (j + 1))) _ _ fun b => ?_
    rw [hent v s a b]
    congr 2
  unfold actC
  rw [map_natActR]
  unfold natActR
  rw [LinearMap.smul_apply, AlgHom.toLinearMap_apply]
  rw [hsc, hsub]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConstructionAtBundlePointsOfTrueColumns
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

namespace GlobalTheory.AtG

theorem row_aAtG_of_rowPin : ∀ {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd),
    (∀ K X f T c, Q K X f T c →
      (positionOf (HasPartAnd fun _ _ _ _ w Z => ∀ a, GlobalTheory.AtG.RowPin w.I w.ok w.l Z a)) K X f T c) →
    AllBundlePointProperties.ArithmeticConditionAtBundlePoints Q Lk :=
  GlobalTheory.T.atGRows_bundlePoints_of_jetSplitAmbient GlobalTheory.T.jetTableBound_splitPrime

end GlobalTheory.AtG
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EvalBasisCoordsAgainstBlockActionStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evalBasisCoords_against_blockAction : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (i : ℕ) {n : ℕ} (h : (X.Pj i).m + 1 = n) (Gr : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (B M : GL (Fin n) D.host.E) (V : XR (X.Pj i) ℂ) (z : Frames Gr) (f : Fr1 D n), (∀ τ, f.1 τ = (atR D (M * B⁻¹) τ : Matrix (Fin n) (Fin n) ℂ) * z.1 τ) → evC (X.Pj i) h (posJ X D pos i) Gr (crdB (embT D) B) V z = ev1 X D pos i h (actC X D pos i h M V) f ∧ actC X D pos i h M (actC X D pos i h M⁻¹ V) = V := by
  first | exact @GlobalTheory.TwV.DelA.evC_crdB_actC | exact GlobalTheory.TwV.DelA.evC_crdB_actC | (intros; apply GlobalTheory.TwV.DelA.evC_crdB_actC <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EvalModelPolynomialOnStdFramesInjectiveStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evalModelPolynomialOnStdFrames_injective : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (i : ℕ) {n : ℕ} (h : (X.Pj i).m + 1 = n) (R : XR (X.Pj i) ℂ), (∀ f : Fr1 D n, ev1 X D pos i h R f = 0) → R = 0 := by
  first | exact @GlobalTheory.TwV.DelA.eq_zero_of_ev1_eq_zero_on_frames | exact GlobalTheory.TwV.DelA.eq_zero_of_ev1_eq_zero_on_frames | (intros; apply GlobalTheory.TwV.DelA.eq_zero_of_ev1_eq_zero_on_frames <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EvalStdFramesEqDetPowerMulBlockValueStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evalStdFrames_eq_detPower_mul_blockValue : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (i : ℕ) {n : ℕ} (h : (X.Pj i).m + 1 = n) (R : XR (X.Pj i) ℂ) (f : Fr1 D n), ev1 X D pos i h R f = (∏ τ, (zT X D pos f.1 τ).det ^ eT X D pos i τ) * valZ X D pos i h R f.1 := by
  first | exact @GlobalTheory.TwV.DelA.ev1_eq_prod_det_pow_mul_valZ | exact GlobalTheory.TwV.DelA.ev1_eq_prod_det_pow_mul_valZ | (intros; apply GlobalTheory.TwV.DelA.ev1_eq_prod_det_pow_mul_valZ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCEmbCLam
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

set_option maxHeartbeats 2000000 in

theorem exists_cEmbC_lam : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∃ (E : CEmbC (sysS H X std).G) (lam : TaylorLogMetric.Qbar →+* ℂ_[D.what₂.places.resChar w]), ∀ (z : D.what₂.LL) (hz : D.what₂.embLL z ∈ algebraicClosure ℚ ℂ), E.iK (ex.cmp.embW u w hg z) = lam ⟨D.what₂.embLL z, hz⟩ := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J
  have hV : 0 < (sysS H X std).G.P.nV := (Gl.vOf u w hg 0).pos
  obtain ⟨E⟩ := GlobalTheory.TwU.nonempty_cEmbC _ (sysS H X std).G hV
  obtain ⟨lam, hlam⟩ := GlobalTheory.padic_emb_extends_algebraicClosure (D.what₂.places.resChar w) D.what₂.LL D.what₂.embLL
    (E.iK.comp (ex.cmp.embW u w hg))
  exact ⟨E, lam, fun z hz => hlam z hz⟩

end GlobalTheory.TwV
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFinsetRepsOfCls
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.TwV.exists_finset_reps_of_cls {T Γ C : Type} [Finite C] (P : T → Prop) (sm : Γ → T → T) (cls : T → C)
    (h : ∀ L L', P L → P L' → cls L = cls L' → ∃ γ, L' = sm γ L) :
    ∃ R : Finset T, (∀ L ∈ R, P L) ∧ ∀ L, P L → ∃ L₀ ∈ R, ∃ γ : Γ, L = sm γ L₀ := by
  classical
  let S : Set C := {x | ∃ L, P L ∧ cls L = x}
  have hS : ∀ x : S, ∃ L, P L ∧ cls L = x.1 := fun x => x.2
  choose f hf using hS
  haveI : Fintype S := Fintype.ofFinite S
  refine ⟨Finset.univ.image f, ?_, ?_⟩
  · intro L hL
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hL
    exact (hf x).1
  · intro L hL
    let x : S := ⟨cls L, L, hL, rfl⟩
    exact ⟨f x, Finset.mem_image_of_mem f (Finset.mem_univ x), h (f x) L (hf x).1 hL (hf x).2⟩

set_option maxHeartbeats 2000000 in

theorem GlobalTheory.TwV.finClasses_sysS : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ j c, ((sysS H X std).Lv.lev j c).FinClasses := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J j c
  change (Lv.lev j c).FinClasses
  by_cases hj : j ≤ D.R.m
  · exact GlobalTheory.TwV.exists_finset_reps_of_cls (C := (D.chTw u μ).cls j) _ (Lv.lev j c).smul ((labAt X H).cls j c)
      (fun L L' hL hL' e => (((labAt X H).cls_iff j hj c c L L' hL hL').1 e).2)
  · exact (J.empty j (by omega)).elim c
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinStabSite
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

set_option maxHeartbeats 2000000 in

theorem finStab_site : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), FinStab (sysS H X std).Lv := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J
  show FinStab Lv
  intro j c La hLa
  by_cases hj : j ≤ D.R.m
  · exact Nat.finite_of_card_ne_zero ((labAt X H).stab_dvd j hj c La hLa).1.ne'
  · exact (J.empty j (by omega)).elim c

end GlobalTheory.TwV
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertThetaAdmissibilityOfComplexMultiplication
section
namespace GlobalTheory.TwV.Lt

theorem inert_theta_admissibility_of_complex_multiplication : Formalism.L2.Th1.CM.CM2 → GlobalTheory.TwV.Lt.AdmAtEnt2 := fun h => by
  haveI : Fact Formalism.L2.Th1.CM.CM2 := ⟨h⟩
  exact Formalism.L2.KerInert.AdmLoc2.admissible_entries_small_chain

end GlobalTheory.TwV.Lt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSDLatLatKOfStdL
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.KerSelfDual

theorem isSDLat_latK_of_stdL : ∀ {D : D7} {i : ℕ} {hi : i ≤ D.R.m} {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} (lev : StepLevel D.host.F D.host.E (sigD D) (gramN D i hi) T D.R.f bad) (co : GL (Fin (D.R.N i)) D.host.E) (a : 𝓞 D.host.E), cT (sigD D : D.host.E →+* D.host.E) co.1 * co.1 = gramN D i hi → latCo D.sp (gramN D i hi) co a 1 lev.Lb = StandardLatticesGL3.stdL D (D.R.N i) → ∀ x : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F), IsSDLat D.host.E (D.R.N i) (latK D.sp (gramN D i hi) a x.1 lev.Lb) := by
  intro D i hi T bad lev co a hco hstd x
  have hc : IsOrthCo ((sigD D : D.host.E →ₐ[D.host.F] D.host.E) : D.host.E →+* D.host.E) (gramN D i hi) (toLE co) :=
    GlobalTheory.TwV.isOrthCo_toLE_of_cT_mul_self _ _ co hco
  have hc' : ∃ c, IsOrthCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) c := ⟨toLE co, hc⟩
  have hJ := GlobalTheory.isLat_dl_of_isOrthCo D.sp (gramN D i hi) hc'
  have hLb : Formalism.L2.GlobalTheoryTheory.Comp.IsLat lev.Lb := ⟨lev.Lb_fin, lev.Lb_span⟩
  have h1 : Formalism.L2.PairingIndexBounds.F.latAd (1 : GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) lev.Lb = lev.Lb := by
    rw [GlobalTheory.SDCompan.latAd_eq]
    exact Formalism.L2.GlobalTheoryTheory.Comp.glob_one hLb
  have hm : mvL co (compan (sp := D.sp) (gramN D i hi) a lev.Lb) = StandardLatticesGL3.stdL D (D.R.N i) := by
    rw [← hstd, latCo, h1]
  have hsd := GlobalTheory.FourthRootStd.stdL_isSD D (D.R.N i)
  rw [← hm] at hsd
  obtain ⟨hM, hdl⟩ := GlobalTheory.OrthSelfDual.isLat_and_dl_eq_of_isSDLat_mvL D.sp (gramN D i hi) co _ hc hsd
  exact GlobalTheory.SDCompan.isSDLat_latK D.sp (gramN D i hi) hJ hc' x.1 x.2 lev.Lb a hLb hM hdl

end GlobalTheory.KerSelfDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KerThEntireAlgCoef
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open Formalism.L2.KerInert.RepComb Formalism.L2.Th1.H

namespace GlobalTheory

theorem kerTh_entire_algCoef : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → TaylorLogMetric.IsChi D χ → ∀ {a b : ℕ} (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ) (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ) (S : Finset ℕ), TaylorLogMetric.admitted D a b N N' → SNum S cl → (∀ x, IntOff S (Ξ x)) → Differentiable ℂ (kerTh B χ SS cl N N' Ξ) ∧ TaylorLogMetric.CoefIn D (kerTh B χ SS cl N N' Ξ) TaylorLogMetric.Qbar := by
  intro D cc δ B χ hcc hδ hχ a b SS cl N N' Ξ S hA hS hΞ
  have hL := lattice_integral_of_facts D.host.E D.what₂.Tau a b (fun τ => TaylorLogMetric.embT D τ) δ D.host.d
    (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹ (Formalism.L2.PairingIndexBounds.F.aaOf D cc) N N' (laFacts_of_adm B hcc hδ hA)
  have hLFG := period_lattice_finitely_generated D.host.E D.what₂.Tau a b (fun τ => TaylorLogMetric.embT D τ) δ (Formalism.L2.PairingIndexBounds.F.aaOf D cc) N N' hA.2.2.2.1
    hA.2.2.1.2.1 (aaOf_fg cc)
  obtain ⟨hi1, hi2, hi3⟩ := finite_index_of_fg D.host.E D.what₂.Tau a b (fun τ => TaylorLogMetric.embT D τ) δ (Formalism.L2.PairingIndexBounds.F.aaOf D cc) SS N N'
    cl hS.1 hLFG
  obtain ⟨n, r, t, hr, ht, hΘ⟩ := theta_coset_kernel D.host.E D.what₂.Tau a b (fun τ => TaylorLogMetric.embT D τ) δ D.host.d
    (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹ (Formalism.L2.PairingIndexBounds.F.aaOf D cc) SS N N' cl S Ξ (B.eNat χ a b N N') hL hi1 hi2 hi3 hS hΞ
  have hfun : kerTh B χ SS cl N N' Ξ =
      fun z => ∑ k, r k * TaylorLogMetric.U D B.tor (t k) (B.eNat χ a b N N') z := by
    funext z
    simp only [Formalism.L2.KerInert.RepComb.U_eq_opU]
    exact congrFun hΘ z
  rw [hfun]
  refine entire_algCoef_comb D r _ (fun k => (hr k).1) fun k => ?_
  obtain ⟨m, hm, hmt⟩ := ht k
  exact TwV.translate_entire_algebraic D cc δ B χ hcc hδ hχ a b N N' hA (t k) ⟨m, hm.1, lambda_in_lattice_pair cc δ N N' hmt⟩

end GlobalTheory
end
end

