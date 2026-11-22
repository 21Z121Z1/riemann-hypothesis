import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0133
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0151
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0145
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0162
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0150
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0943
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0346

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaFunctionDoublingSeesawOfStandardChar
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (resL resR)

noncomputable section

namespace GlobalTheory.Core.Rk.DeltaTheta

variable {D : D7}

def fstH (A B : HSp D) : WO (dblSp A) B →+ WO A B where
  toFun := resL A B
  map_zero' := rfl
  map_add' _ _ := rfl

def sndH (A B : HSp D) : WO (dblSp A) B →+ WO A B where
  toFun x := -resR A B x
  map_zero' := neg_zero
  map_add' x y := neg_add (resR A B x) (resR A B y)

theorem continuous_fstH (A B : HSp D) : Continuous (fstH A B) :=
  continuous_matrix fun i _ => continuous_id.matrix_elem i _

theorem continuous_sndH (A B : HSp D) : Continuous (sndH A B) := by
  obtain ⟨i1, -⟩ := GlobalTheory.MixModel.lattice_Mx D B.rank A.rank
  have h : Continuous (resR A B) := continuous_matrix fun i _ => continuous_id.matrix_elem i _
  exact h.neg

theorem map_fstH {R : Type} [CommRing R] (φ : AE D →+* R) (A B : HSp D) {u : WO (dblSp A) B} (h : u.map φ = 0) :
    (fstH A B u).map φ = 0 :=
  Matrix.ext fun i j => congrFun (congrFun h i) (finSumFinEquiv (Sum.inl j))

theorem map_sndH {R : Type} [CommRing R] (φ : AE D →+* R) (A B : HSp D) {u : WO (dblSp A) B} (h : u.map φ = 0) :
    (sndH A B u).map φ = 0 :=
  Matrix.ext fun i j => by
    have e : φ (u i (finSumFinEquiv (Sum.inr j))) = 0 := congrFun (congrFun h i) (finSumFinEquiv (Sum.inr j))
    change φ (-(u i (finSumFinEquiv (Sum.inr j)))) = 0
    rw [map_neg, e, neg_zero]

theorem hO_dbl (A B : HSp D) (x y : WO (dblSp A) B) :
    hO (dblSp A) B x y = hO A B (fstH A B x) (fstH A B y) - hO A B (sndH A B x) (sndH A B y) := by
  have hi : (dblSp A).gram⁻¹ = blkMat finSumFinEquiv A.gram⁻¹ (-A.gram⁻¹) := Matrix.inv_eq_left_inv (by
    rw [gram_hdbl, dblGram, blkMat_mul, neg_mul_neg, Matrix.nonsing_inv_mul _ (GlobalTheory.MixModel.gram_isUnit_det A), blkMat_one])
  simp only [hO, hi, ← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, fstH, sndH, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    resR, Matrix.of_apply,
    blkMat, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.neg_apply, map_zero,
    map_neg, zero_mul, Finset.sum_const_zero, add_zero, zero_add, neg_mul, mul_neg, neg_neg,
    Finset.sum_neg_distrib, sub_eq_add_neg]
  rfl

theorem symplOH_dbl (A B : HSp D) (x y : WO (dblSp A) B) :
    symplOH (dblSp A) B x y =
      symplOH A B (fstH A B x) (fstH A B y) - symplOH A B (sndH A B x) (sndH A B y) := by
  simp only [GlobalTheory.MixModel.symplOH_eq, hO_dbl, map_sub]

theorem conj_char {G : Type} [AddCommGroup G] (ψ : AddChar G ℂ) (h : ∀ x, ‖ψ x‖ = 1) (x : G) :
    conj (ψ x) = ψ (-x) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (h x)]

theorem isThetaFunO_delta {ψ : AddChar (AF D.host.F) ℂ} (hn : ∀ x, ‖ψ x‖ = 1) {A B : HSp D} {f₁ f₂ : WO A B → ℂ}
    (h₁ : IsThetaFunO ψ A B f₁) (h₂ : IsThetaFunO ψ A B f₂) : IsThetaFunO ψ (dblSp A) B (delta A B f₁ f₂) := by
  have hd : delta A B f₁ f₂ = fun w => f₁ (fstH A B w) * conj (f₂ (sndH A B w)) := rfl
  rw [hd]
  refine ⟨fun γ w => ?_, ?_, ?_, fun k L hL h0 w => ?_⟩
  · have e₁ : fstH A B (ratW B (dblSp A) γ) =
        ratW B A (Matrix.of fun i j => γ i (finSumFinEquiv (Sum.inl j))) := rfl
    have e₂ : sndH A B (ratW B (dblSp A) γ) =
        ratW B A (Matrix.of fun i j => -γ i (finSumFinEquiv (Sum.inr j))) :=
      Matrix.ext fun i j => (map_neg (incA D) _).symm
    rw [map_add, map_add, symplOH_dbl, e₁, e₂, h₁.quasi, h₂.quasi, map_mul, conj_char ψ hn, neg_neg, neg_sub,
      sub_eq_add_neg, AddChar.map_add_eq_mul]
    ring
  · obtain ⟨U₁, hU₁, k₁⟩ := h₁.level
    obtain ⟨U₂, hU₂, k₂⟩ := h₂.level
    refine ⟨U₁.comap (fstH A B) ⊓ U₂.comap (sndH A B),
      (hU₁.preimage (continuous_fstH A B)).inter (hU₂.preimage (continuous_sndH A B)), fun u hu h0 => ?_⟩
    funext w
    have e₁ := congrFun (k₁ _ hu.1 (map_fstH _ _ _ h0)) (fstH A B w)
    have e₂ := congrFun (k₂ _ hu.2 (map_sndH _ _ _ h0)) (sndH A B w)
    simp only [heisO] at e₁ e₂ ⊢
    rw [← e₁, ← e₂, symplOH_dbl, sub_eq_add_neg, AddChar.map_add_eq_mul, map_add, map_add, map_mul, conj_char ψ hn]
    ring
  · exact (h₁.cont.comp (continuous_fstH A B)).mul
      (Complex.continuous_conj.comp (h₂.cont.comp (continuous_sndH A B)))
  · simp only [map_add]
    exact (h₁.smooth k ((fstH A B).comp L) ((continuous_fstH A B).comp hL) (fun t => map_fstH _ _ _ (h0 t)) _).mul
      (Complex.conjCLE.contDiff.comp (h₂.smooth k ((sndH A B).comp L) ((continuous_sndH A B).comp hL)
        (fun t => map_sndH _ _ _ (h0 t)) _))

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D), IsStdChar D ψ (-1) → ∀ f₁ f₂, IsThetaFunO ψ A B f₁ → IsThetaFunO ψ A B f₂ → IsThetaFunO ψ (dblSp A) B (delta A B f₁ f₂) :=
  fun _ _ _ _ hψ _ _ h₁ h₂ => isThetaFunO_delta hψ.1.2.1 h₁ h₂

end GlobalTheory.Core.Rk.DeltaTheta

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlacesDatumInvLeftMulTargetLevel
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.LevelMove

section Mat

variable {κ : Type} [CommRing κ] {a b r t j : ℕ}

def IsTopB (r t : ℕ) (y : Matrix (Fin b) (Fin a) κ) (g : GL (Fin a) κ) : Prop :=
  LowZero a y ∧ g.val = topL a y ∧ g ∈ blockTri (blkOf r t)

theorem IsTopB.move (hab : a ≤ b) (ea : a = r + j * t) (eb : b = r + (j + 1) * t)
    {y : Matrix (Fin b) (Fin a) κ} {g : GL (Fin a) κ} {H : GL (Fin b) κ} (h : IsTopB r t y g)
    (hT : H ∈ blockTri (blkOf r t)) :
    IsTopB r t ((H⁻¹).val * y) ((upperLeftBlock hab H)⁻¹ * g) := by
  obtain ⟨h1, h2, h3⟩ := h
  have t2 := GlobalTheory.StepLaw.TypeDatum.mem_twoBlockTriangular_of_blockTriangular ea eb hT
  have tm := GlobalTheory.StepLaw.TypeDatum.top_mem hab t2 hT
  have hinv : upperLeftBlock hab H⁻¹ = (upperLeftBlock hab H)⁻¹ := extendOne_inv _ t2
  have e1 := GlobalTheory.StepLaw.TypeDatum.topL_mul hab (Subgroup.inv_mem _ t2) h1 1
  have e2 := GlobalTheory.StepLaw.TypeDatum.lowZero_mul (Subgroup.inv_mem _ t2) h1 1
  rw [Matrix.mul_one] at e1 e2
  rw [Matrix.mul_one] at e1
  refine ⟨e2, ?_, Subgroup.mul_mem _ (Subgroup.inv_mem _ tm) h3⟩
  rw [e1, hinv, ← h2, Units.val_mul]

theorem restrictBlock_inv_mul_block_triangular_move (hab : a ≤ b) (ha : r ≤ a) (hb : r ≤ b) (ea : a = r + j * t) (eb : b = r + (j + 1) * t)
    {g : GL (Fin a) κ} {H : GL (Fin b) κ} (hg : g ∈ blockTri (blkOf r t)) (hT : H ∈ blockTri (blkOf r t)) :
    upperLeftBlock ha ((upperLeftBlock hab H)⁻¹ * g) = (upperLeftBlock hb H)⁻¹ * upperLeftBlock ha g := by
  have t2 := GlobalTheory.StepLaw.TypeDatum.mem_twoBlockTriangular_of_blockTriangular ea eb hT
  have tm := GlobalTheory.StepLaw.TypeDatum.top_mem hab t2 hT
  have le := blockTri_blkOf_le (κ := κ) (n := a) r t
  have m2 : upperLeftBlock ha ((upperLeftBlock hab H)⁻¹ * g) = upperLeftBlock ha (upperLeftBlock hab H)⁻¹ * upperLeftBlock ha g :=
    extendMatrixByIdentityAlongIndices_mul _ (le (Subgroup.inv_mem _ tm)) (le hg)
  have m3 : upperLeftBlock ha (upperLeftBlock hab H)⁻¹ = (upperLeftBlock ha (upperLeftBlock hab H))⁻¹ := extendOne_inv _ (le tm)
  rw [m2, m3, GlobalTheory.StepLaw.TypeDatum.restrictTopBlock_restrictTopBlock hab ha hb t2 hT]

theorem char_move (hab : a ≤ b) (ea : a = r + j * t) (eb : b = r + (j + 1) * t) {A : Type} [CommGroup A]
    (χ : ℕ → κˣ →* A) {g : GL (Fin a) κ} {H : GL (Fin b) κ} (hg : g ∈ blockTri (blkOf r t))
    (hT : H ∈ blockTri (blkOf r t)) :
    (∏ c ∈ Finset.range j, χ (c + 1) (dBlk (blkOf r t) (c + 1) ((upperLeftBlock hab H)⁻¹ * g))) *
        (χ (j + 1) (Matrix.GeneralLinearGroup.det ((upperLeftBlock hab H)⁻¹ * g)))⁻¹ =
      (∏ c ∈ Finset.range (j + 1), χ (c + 1) (dBlk (blkOf r t) (c + 1) H))⁻¹ *
        χ (j + 1) (Matrix.GeneralLinearGroup.det H) *
        ((∏ c ∈ Finset.range j, χ (c + 1) (dBlk (blkOf r t) (c + 1) g)) *
          (χ (j + 1) (Matrix.GeneralLinearGroup.det g))⁻¹) := by
  have h := GlobalTheory.StepLaw.TypeDatum.char_law hab ea eb χ hg (Subgroup.one_mem _) hT
  have d1 : ∀ c, dBlk (blkOf r t) c (1 : GL (Fin a) κ) = 1 := fun c => blockDiagonalExtendByOnePrimeField_one _ _
  simp only [mul_one, d1, map_one, Finset.prod_const_one, one_mul] at h
  rw [inv_mul_eq_iff_eq_mul] at h
  rw [h]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end Mat

section Dat

variable {D : D7} {a b r t k : ℕ} (ha : r ≤ a) (Pg : Finset (Pl D.host.E)) (P : LevelP Pg r ℂ)
  (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ χj : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
  (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP))

theorem omegaG_of_top (g : ∀ PP : ↥Pg, GL (Fin a) (kP PP.1)) (hg : ∀ PP : ↥Pg, IsTopB r t (y PP.1) (g PP))
    (hm : (fun PP : ↥Pg => upperLeftBlock ha (g PP)) ∈ P.H) :
    omegaG (Lev.datY a r t k ha Pg ∅ P χ ξ Lev.Frm.B) χj y =
      ((P.chi ⟨_, hm⟩ * ∏ PP : ↥Pg, ((∏ c ∈ Finset.range k, χ (c + 1) PP.1 (dBlk (blkOf r t) (c + 1) (g PP))) *
        (χj PP.1 (Matrix.GeneralLinearGroup.det (g PP)))⁻¹) : ℂˣ) : ℂ) := by
  unfold omegaG
  split_ifs with h
  · have e : h.2.choose = g := funext fun PP =>
      Units.ext ((h.2.choose_spec.1 PP).trans (hg PP).2.1.symm)
    have e2 : (Lev.datY a r t k ha Pg ∅ P χ ξ Lev.Frm.B).P.chi
        ⟨fun PP => upperLeftBlock (Lev.datY a r t k ha Pg ∅ P χ ξ Lev.Frm.B).hr (h.2.choose PP), h.2.choose_spec.2.2⟩ =
        P.chi ⟨_, hm⟩ := by
      show P.chi _ = P.chi _
      congr 1
      exact Subtype.ext (funext fun PP => congrArg (fun x => upperLeftBlock ha x) (congrFun e PP))
    rw [e2]
    simp only [e, Finset.prod_mul_distrib, Units.val_mul, Units.coe_prod, Units.val_inv_eq_inv_val, mul_assoc]
    rfl
  · exfalso
    exact h ⟨fun PP hP => (hg ⟨PP, hP⟩).1, g, fun PP => (hg PP).2.1, fun PP => (hg PP).2.2, hm⟩

theorem omegaG_of_notTop (hg : ¬ ∃ g : ∀ PP : ↥Pg, GL (Fin a) (kP PP.1), (∀ PP : ↥Pg, IsTopB r t (y PP.1) (g PP)) ∧
      (fun PP : ↥Pg => upperLeftBlock ha (g PP)) ∈ P.H) :
    omegaG (Lev.datY a r t k ha Pg ∅ P χ ξ Lev.Frm.B) χj y = 0 := by
  unfold omegaG
  split_ifs with h
  · exfalso
    obtain ⟨h1, g, g1, g2, g3⟩ := h
    exact hg ⟨g, fun PP => ⟨h1 PP.1 PP.2, g1 PP, g2 PP⟩, g3⟩
  · rfl

end Dat

end GlobalTheory.ChainOnto.LevelMove

namespace GlobalTheory.ChainOnto

open LevelMove

theorem omegaG_levelP_move : ∀ (D : D7) (a b r t k : ℕ) (ha : r ≤ a) (hb : r ≤ b), a = r + k * t → b = r + (k + 1) * t → ∀ (Pg : Finset (Pl D.host.E)) (P : LevelP Pg r ℂ) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (H : ∀ PP : Pl D.host.E, GL (Fin b) (kP PP)), (∀ PP ∈ Pg, H PP ∈ blockTri (blkOf r t)) → ∀ hP : (fun PP : ↥Pg => upperLeftBlock hb (H PP.1)) ∈ P.H, ∀ y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP), omegaG (Lev.datY a r t k ha Pg ∅ P χ ξ Lev.Frm.B) (χ (k + 1)) (fun PP => ((H PP)⁻¹).val * y PP) = (((P.chi ⟨_, hP⟩ * ∏ PP ∈ Pg, ∏ i ∈ Finset.range (k + 1), χ (i + 1) PP (dBlk (blkOf r t) (i + 1) (H PP)))⁻¹ * ∏ PP ∈ Pg, χ (k + 1) PP (Matrix.GeneralLinearGroup.det (H PP)) : ℂˣ) : ℂ) * omegaG (Lev.datY a r t k ha Pg ∅ P χ ξ Lev.Frm.B) (χ (k + 1)) y := by
  intro D a b r t k ha hb ea eb Pg P χ ξ H hH hP y
  have hab : a ≤ b := by rw [ea, eb, add_mul]; omega
  by_cases h : ∃ g : ∀ PP : ↥Pg, GL (Fin a) (kP PP.1), (∀ PP : ↥Pg, IsTopB r t (y PP.1) (g PP)) ∧
      (fun PP : ↥Pg => upperLeftBlock ha (g PP)) ∈ P.H
  · obtain ⟨g, hg, hm⟩ := h
    have hg' : ∀ PP : ↥Pg, IsTopB r t (((H PP.1)⁻¹).val * y PP.1) ((upperLeftBlock hab (H PP.1))⁻¹ * g PP) :=
      fun PP => (hg PP).move hab ea eb (hH _ PP.2)
    have hr : (fun PP : ↥Pg => upperLeftBlock ha ((upperLeftBlock hab (H PP.1))⁻¹ * g PP)) =
        (fun PP : ↥Pg => upperLeftBlock hb (H PP.1))⁻¹ * (fun PP : ↥Pg => upperLeftBlock ha (g PP)) :=
      funext fun PP => restrictBlock_inv_mul_block_triangular_move hab ha hb ea eb (hg PP).2.2 (hH _ PP.2)
    have hm' : (fun PP : ↥Pg => upperLeftBlock ha ((upperLeftBlock hab (H PP.1))⁻¹ * g PP)) ∈ P.H := by
      rw [hr]; exact P.H.mul_mem (P.H.inv_mem hP) hm
    have hc : P.chi ⟨_, hm'⟩ = (P.chi ⟨_, hP⟩)⁻¹ * P.chi ⟨_, hm⟩ := by
      rw [← map_inv, ← map_mul]; congr 1; exact Subtype.ext hr
    have hx : ∀ PP : ↥Pg, (∏ c ∈ Finset.range k, χ (c + 1) PP.1 (dBlk (blkOf r t) (c + 1) ((upperLeftBlock hab (H PP.1))⁻¹ * g PP))) *
        (χ (k + 1) PP.1 (Matrix.GeneralLinearGroup.det ((upperLeftBlock hab (H PP.1))⁻¹ * g PP)))⁻¹ =
        (∏ c ∈ Finset.range (k + 1), χ (c + 1) PP.1 (dBlk (blkOf r t) (c + 1) (H PP.1)))⁻¹ *
          χ (k + 1) PP.1 (Matrix.GeneralLinearGroup.det (H PP.1)) *
          ((∏ c ∈ Finset.range k, χ (c + 1) PP.1 (dBlk (blkOf r t) (c + 1) (g PP))) *
            (χ (k + 1) PP.1 (Matrix.GeneralLinearGroup.det (g PP)))⁻¹) :=
      fun PP => char_move hab ea eb (fun c => χ c PP.1) (hg PP).2.2 (hH _ PP.2)
    rw [omegaG_of_top ha Pg P χ ξ _ (fun PP => ((H PP)⁻¹).val * y PP) _ hg' hm', omegaG_of_top ha Pg P χ ξ _ y g hg hm,
      hc, ← Units.val_mul]
    congr 1
    rw [Finset.prod_congr rfl fun PP _ => hx PP, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_inv_distrib,
      ← Finset.prod_coe_sort Pg (fun PP => χ (k + 1) PP (Matrix.GeneralLinearGroup.det (H PP))),
      ← Finset.prod_coe_sort Pg (fun PP => ∏ i ∈ Finset.range (k + 1), χ (i + 1) PP (dBlk (blkOf r t) (i + 1) (H PP)))]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · have h' : ¬ ∃ g : ∀ PP : ↥Pg, GL (Fin a) (kP PP.1),
        (∀ PP : ↥Pg, IsTopB r t ((fun PP => ((H PP)⁻¹).val * y PP) PP.1) (g PP)) ∧ (fun PP : ↥Pg => upperLeftBlock ha (g PP)) ∈ P.H := by
      rintro ⟨g, hg, hm⟩
      refine h ⟨fun PP => (upperLeftBlock hab (H PP.1)⁻¹)⁻¹ * g PP, fun PP => ?_, ?_⟩
      · have e : y PP.1 = ((H PP.1)⁻¹⁻¹).val * (((H PP.1)⁻¹).val * y PP.1) := by
          rw [← Matrix.mul_assoc, ← Units.val_mul, inv_inv, mul_inv_cancel, Units.val_one, Matrix.one_mul]
        rw [e]
        exact (hg PP).move hab ea eb (Subgroup.inv_mem _ (hH _ PP.2))
      · have hr : (fun PP : ↥Pg => upperLeftBlock ha ((upperLeftBlock hab (H PP.1)⁻¹)⁻¹ * g PP)) =
            (fun PP : ↥Pg => upperLeftBlock hb (H PP.1)⁻¹)⁻¹ * (fun PP : ↥Pg => upperLeftBlock ha (g PP)) :=
          funext fun PP => restrictBlock_inv_mul_block_triangular_move hab ha hb ea eb (hg PP).2.2 (Subgroup.inv_mem _ (hH _ PP.2))
        have i2 : (fun PP : ↥Pg => upperLeftBlock hb (H PP.1)⁻¹) = (fun PP : ↥Pg => upperLeftBlock hb (H PP.1))⁻¹ :=
          funext fun PP => extendOne_inv _ (blockTri_blkOf_le r t (hH _ PP.2))
        rw [hr, i2, inv_inv]
        exact P.H.mul_mem hP hm
    rw [omegaG_of_notTop ha Pg P χ ξ _ y h, omegaG_of_notTop ha Pg P χ ξ _ _ h', mul_zero]

end GlobalTheory.ChainOnto

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlacesDatumMulRightSourceLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto.RightMove

variable {D : D7}

theorem topL_mul {κ : Type} [CommRing κ] {a b : ℕ} (y : Matrix (Fin b) (Fin a) κ) (γ : Matrix (Fin a) (Fin a) κ) :
    topL a (y * γ) = topL a y * γ := by
  ext i j
  by_cases hi : i.val < b
  · simp [topL, Matrix.mul_apply, hi]
  · simp [topL, Matrix.mul_apply, hi]

theorem lowZero_mul {κ : Type} [CommRing κ] {a b : ℕ} {y : Matrix (Fin b) (Fin a) κ} (hy : LowZero a y)
    (γ : Matrix (Fin a) (Fin a) κ) : LowZero a (y * γ) := by
  intro i j hi _
  rw [Matrix.mul_apply]
  exact Finset.sum_eq_zero fun l _ => by rw [hy i l hi l.2, zero_mul]

abbrev Cond {a b : ℕ} (L : LevDat D.host.E ℂ a) (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) : Prop :=
  (∀ PP ∈ L.Pg, LowZero a (y PP)) ∧ ∃ g : ∀ PP : ↥L.Pg, GL (Fin a) (kP PP.1),
    (∀ PP : ↥L.Pg, ((g PP : GL (Fin a) _) : Matrix (Fin a) (Fin a) _) = topL a (y PP.1)) ∧
    (∀ PP : ↥L.Pg, g PP ∈ blockTri (blkOf L.r L.t)) ∧ (fun PP => upperLeftBlock L.hr (g PP)) ∈ L.P.H

theorem cond_mul {a b : ℕ} (L : LevDat D.host.E ℂ a) (γ : ∀ PP : Pl D.host.E, GL (Fin a) (kP PP))
    (hγ : ∀ PP ∈ L.Pg, γ PP ∈ blockTri (blkOf L.r L.t)) (hP : (fun PP : ↥L.Pg => upperLeftBlock L.hr (γ PP.1)) ∈ L.P.H)
    (y z : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) (hz : ∀ PP, z PP = y PP * (γ PP).val)
    (h : Cond L y) : Cond L z := by
  obtain ⟨h1, g, h2, h3, h4⟩ := h
  refine ⟨fun PP hP' => (hz PP).symm ▸ lowZero_mul (h1 PP hP') _, fun PP => g PP * γ PP.1, fun PP => ?_,
    fun PP => mul_mem (h3 PP) (hγ PP.1 PP.2), ?_⟩
  · rw [Units.val_mul, h2, hz, topL_mul]
  · have e : (fun PP : ↥L.Pg => upperLeftBlock L.hr (g PP * γ PP.1)) =
        (fun PP => upperLeftBlock L.hr (g PP)) * (fun PP : ↥L.Pg => upperLeftBlock L.hr (γ PP.1)) := by
      funext PP
      exact extendMatrixByIdentityAlongIndices_mul _ (blockTri_blkOf_le _ _ (h3 PP)) (blockTri_blkOf_le _ _ (hγ PP.1 PP.2))
    rw [e]
    exact mul_mem h4 hP

theorem omegaG_mul_right : ∀ (D : D7) (a b : ℕ) (L : LevDat D.host.E ℂ a) (χ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (G : ∀ PP : Pl D.host.E, GL (Fin a) (kP PP)), (∀ PP ∈ L.Pg, G PP ∈ blockTri (blkOf L.r L.t)) → ∀ hP : (fun PP : ↥L.Pg => upperLeftBlock L.hr (G PP.1)) ∈ L.P.H, ∀ y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP), omegaG L χ (fun PP => y PP * (G PP).val) = ((L.P.chi ⟨_, hP⟩ * (∏ PP ∈ L.Pg, ∏ i ∈ Finset.range L.s, L.cg (i + 1) PP (dBlk (blkOf L.r L.t) (i + 1) (G PP))) * ∏ PP ∈ L.Pg, (χ PP (Matrix.GeneralLinearGroup.det (G PP)))⁻¹ : ℂˣ) : ℂ) * omegaG L χ y := by
  intro D a b L χ G hG hP y
  have hGi : ∀ PP ∈ L.Pg, (G PP)⁻¹ ∈ blockTri (blkOf L.r L.t) := fun PP h => inv_mem (hG PP h)
  have hPi : (fun PP : ↥L.Pg => upperLeftBlock L.hr (G PP.1)⁻¹) ∈ L.P.H := by
    have e : (fun PP : ↥L.Pg => upperLeftBlock L.hr (G PP.1)⁻¹) = (fun PP : ↥L.Pg => upperLeftBlock L.hr (G PP.1))⁻¹ := by
      funext PP
      exact extendOne_inv _ (blockTri_blkOf_le _ _ (hG PP.1 PP.2))
    rw [e]
    exact inv_mem hP
  unfold omegaG
  by_cases hy : Cond L y
  · have hy' : Cond L (fun PP => y PP * (G PP).val) := cond_mul L G hG hP y _ (fun _ => rfl) hy
    rw [dif_pos hy', dif_pos hy]
    have key : ∀ PP : ↥L.Pg, hy'.2.choose PP = hy.2.choose PP * G PP.1 := fun PP => Units.ext (by
      rw [Units.val_mul, hy'.2.choose_spec.1 PP, hy.2.choose_spec.1 PP, topL_mul])
    have hc : (⟨fun PP => upperLeftBlock L.hr (hy'.2.choose PP), hy'.2.choose_spec.2.2⟩ : L.P.H) =
        ⟨fun PP => upperLeftBlock L.hr (hy.2.choose PP), hy.2.choose_spec.2.2⟩ * ⟨_, hP⟩ :=
      Subtype.ext (funext fun PP => by
        show upperLeftBlock L.hr (hy'.2.choose PP) = upperLeftBlock L.hr (hy.2.choose PP) * upperLeftBlock L.hr (G PP.1)
        rw [key]
        exact extendMatrixByIdentityAlongIndices_mul _ (blockTri_blkOf_le _ _ (hy.2.choose_spec.2.1 PP)) (blockTri_blkOf_le _ _ (hG PP.1 PP.2)))
    have hd : ∀ PP : ↥L.Pg, ∀ c : ℕ, dBlk (blkOf L.r L.t) c (hy'.2.choose PP) =
        dBlk (blkOf L.r L.t) c (hy.2.choose PP) * dBlk (blkOf L.r L.t) c (G PP.1) := fun PP c => by
      rw [key]; exact diag_block_det_mul (hy.2.choose_spec.2.1 PP) (hG PP.1 PP.2)
    rw [hc, map_mul]
    simp only [hd]
    simp only [key, map_mul, Units.val_mul, mul_inv, Finset.prod_mul_distrib, Units.val_inv_eq_inv_val, Units.coe_prod]
    rw [← Finset.prod_coe_sort L.Pg (fun PP => ((χ PP (Matrix.GeneralLinearGroup.det (G PP)) : ℂˣ) : ℂ)⁻¹),
      ← Finset.prod_coe_sort L.Pg (fun PP => ∏ i ∈ Finset.range L.s, ((L.cg (i + 1) PP (dBlk (blkOf L.r L.t) (i + 1) (G PP)) : ℂˣ) : ℂ))]
    ring
  · have hy' : ¬ Cond L (fun PP => y PP * (G PP).val) := fun h => hy (cond_mul L (fun PP => (G PP)⁻¹) hGi hPi _ y
      (fun PP => by rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]) h)
    rw [dif_neg hy', dif_neg hy, mul_zero]

end GlobalTheory.ChainOnto.RightMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

open GlobalTheory.MixModel Matrix

noncomputable section

namespace GlobalTheory.Core.Rk.SWLaw

variable {D : D7}

abbrev zeroSp (D : D7) : HSp D := Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral 0

def stackRows {a k : ℕ} (X Y : Matrix (Fin a) (Fin k) D.host.E) : Matrix (Fin (a + a)) (Fin k) D.host.E :=
  (Matrix.fromRows X Y).submatrix finSumFinEquiv.symm id

theorem stackRows_gram (A : HSp D) {k l : ℕ} (X Y : Matrix (Fin A.rank) (Fin k) D.host.E)
    (P Q : Matrix (Fin A.rank) (Fin l) D.host.E) :
    (stackRows X Y)ᴴ * (dblSp A).gram * stackRows P Q = Xᴴ * A.gram * P - Yᴴ * A.gram * Q := by
  rw [GlobalTheory.Doubling.gram_hdbl, GlobalTheory.Doubling.dblGram, GlobalTheory.Doubling.blkMat, stackRows, stackRows,
    conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv, submatrix_id_id,
    conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromBlocks, fromCols_mul_fromRows]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_neg, Matrix.neg_mul, sub_eq_add_neg]

def dblDec (A : HSp D) : HypDec (dblSp A) (zeroSp D) A.rank where
  e := stackRows A.gram⁻¹ A.gram⁻¹
  e' := stackRows ((2 : D.host.E)⁻¹ • 1) (-((2 : D.host.E)⁻¹ • 1))
  i₀ := 0
  ee := by rw [stackRows_gram, sub_self]
  e'e' := by
    rw [stackRows_gram, conjTranspose_neg, Matrix.neg_mul, Matrix.neg_mul, Matrix.mul_neg, neg_neg, sub_self]
  e'e := by
    have hG : IsUnit A.gram.det := (gram_det_ne A).isUnit
    rw [stackRows_gram, conjTranspose_neg, Matrix.neg_mul, Matrix.neg_mul, sub_neg_eq_add, Matrix.mul_assoc,
      mul_nonsing_inv _ hG, Matrix.mul_one, conjTranspose_smul, conjTranspose_one, ← add_smul, star_inv₀, star_ofNat]
    rw [show ((2 : D.host.E)⁻¹ + 2⁻¹) = 1 by rw [← two_mul, mul_inv_cancel₀ two_ne_zero], one_smul]
  iso := Matrix.ext fun i _ => Fin.elim0 i
  i₀e := by rw [conjTranspose_zero, Matrix.zero_mul, Matrix.zero_mul]
  i₀e' := by rw [conjTranspose_zero, Matrix.zero_mul, Matrix.zero_mul]
  rank_add := by show 0 + 2 * A.rank = A.rank + A.rank; omega

theorem dblDec_qY (A : HSp D) :
    (dblDec A).qY = (Matrix.fromCols (1 : Matrix (Fin A.rank) (Fin A.rank) D.host.E) (-1)).submatrix id
      finSumFinEquiv.symm := by
  have hG : IsUnit A.gram.det := (gram_det_ne A).isUnit
  rw [HypDec.qY]
  show (stackRows A.gram⁻¹ A.gram⁻¹)ᴴ * (dblSp A).gram = _
  rw [GlobalTheory.Doubling.gram_hdbl, GlobalTheory.Doubling.dblGram, GlobalTheory.Doubling.blkMat, stackRows, conjTranspose_submatrix,
    submatrix_mul_equiv, conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromBlocks,
    conjTranspose_nonsing_inv, gram_conjTranspose, nonsing_inv_mul _ hG]
  simp only [Matrix.mul_zero, add_zero, zero_add, Matrix.mul_neg, nonsing_inv_mul _ hG]

theorem extY_dblDec (A B : HSp D) (w : Mx D B.rank A.rank) : (dblDec A).extY B w = GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.lagr A B w := by
  rw [HypDec.extY_apply, HypDec.pY, dblDec_qY]
  ext i j
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective j
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.lagr, rat, Matrix.mul_apply, Matrix.of_apply, Matrix.map_apply, Matrix.submatrix_apply,
    id, Equiv.symm_apply_apply]
  rcases s with k | k
  · simp [Matrix.one_apply]
  · simp [Matrix.one_apply]

theorem mixS_dblDec_zero (A B : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (ν : Measure (WO A B)) (𝓕 : Set (WO A B))
    (f : WO (dblSp A) B → ℂ) (w₀ : WO (zeroSp D) B) :
    (dblDec A).mixS B ψ ν 𝓕 f 0 w₀ = GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.evZero A B ν 𝓕 f := by
  have hw : w₀ = 0 := Matrix.ext fun _ j => Fin.elim0 j
  subst hw
  have hz : ∀ y : WO (dblSp A) B, symplOH (dblSp A) B y 0 = 0 := fun y => by
    have h := GlobalTheory.OrientedHeis.symplOH_add_right (S := dblSp A) (T := B) y 0 0
    rw [add_zero] at h
    exact left_eq_add.1 h
  unfold HypDec.mixS GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.evZero
  congr 1
  funext a
  rw [HypDec.integrandS_eq, map_zero, map_zero, hz, AddChar.map_zero_eq_one, one_mul, add_zero, add_zero,
    extY_dblDec]

end GlobalTheory.Core.Rk.SWLaw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinatesOfThetaFunctionAreThetaFunctions
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.MixValues

theorem mixS_theta (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S S₀ T : HSp D) (ρ : ℕ)
    (d : HypDec S S₀ ρ) (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ))
    (hμ : IsCovolOne (ratMx D T.rank ρ) μ 𝓕) (f : WO S T → ℂ) (hf : IsThetaFunO ψ S T f) (x : Mx D T.rank ρ) :
    IsThetaFunO ψ S₀ T (d.mixS T ψ μ 𝓕 f x) := by
  rcases Nat.eq_zero_or_pos ρ with rfl | hρ
  · rw [(GlobalTheory.T.wittDecomposition_mixedCoords_rank_zero D ψ).1 S S₀ T d μ 𝓕 hμ f x]
    exact ((GlobalTheory.T.weil_datum_transport_source_rational_isometry D ψ S S₀ T d hψ).2.2.1 f).2 hf
  · obtain ⟨hiso, hrat, -, -, -, hres, -⟩ := GlobalTheory.T.wittSourceMixedCoord_heisenbergRestriction D ψ S S₀ T ρ d
    rw [hres]
    have hμ' : IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D T.rank ρ) μ 𝓕 := by rw [hrat]; exact hμ
    have hg := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1 (d.extX T x) f hf
    exact ((GlobalTheory.TowerRestrict.res_theta D S S₀ T ρ d.e d.i₀ (hiso hρ) ψ hψ μ 𝓕 hμ').1 _ hg).2.1

end GlobalTheory.MixValues

theorem GlobalTheory.MixValues.mixed_values : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.MixedValues D := by
  intro D ψ hψ
  refine ⟨fun S S₀ T ρ d μ 𝓕 hμ f hf x => GlobalTheory.MixValues.mixS_theta D ψ hψ S S₀ T ρ d μ 𝓕 hμ f hf x, ?_⟩
  intro S T T₀ ρ d μ 𝓕 hμ f hf y
  obtain ⟨μ', 𝓕', hμ', -, -, -, hsw⟩ := GlobalTheory.T.wittMixedCoords_conj_hermitianAdjoint D ψ hψ S T T₀ ρ d μ 𝓕 hμ
  have hcd := GlobalTheory.T.hermitianAdjoint_symplectic_action_theta_heisenberg D ψ hψ
  have h1 : IsThetaFunO ψ T S (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger T S) f) := ((hcd S T).2.2.1 f).2 hf
  have h2 := GlobalTheory.MixValues.mixS_theta D ψ hψ T T₀ S ρ d μ' 𝓕' hμ' _ h1 (incA D D.host.xi0⁻¹ • y)
  rw [hsw] at h2
  exact ((hcd S T₀).2.2.1 _).1 h2
end

