import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsGLSubmatrix
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0200
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0201
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0129
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0125
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0032
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0208
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsBiThetaIffJoin
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.SeeSaw GlobalTheory.ChiGrid GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BiTransfer

variable {D : D7}

def sumDec (A B : HSp D) : OrthDec (GlobalTheory.Doubling.hsum A B) A B where
  iA := (fromRows (1 : Matrix (Fin A.rank) (Fin A.rank) D.host.E) (0 : Matrix (Fin B.rank) (Fin A.rank) D.host.E)).submatrix
    finSumFinEquiv.symm id
  iB := (fromRows (0 : Matrix (Fin A.rank) (Fin B.rank) D.host.E) (1 : Matrix (Fin B.rank) (Fin B.rank) D.host.E)).submatrix
    finSumFinEquiv.symm id
  isoA := by
    rw [GlobalTheory.Doubling.gram_hsum, conjTranspose_submatrix]
    unfold GlobalTheory.Doubling.blkMat
    simp [submatrix_mul_equiv, conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromBlocks, fromCols_mul_fromRows]
  isoB := by
    rw [GlobalTheory.Doubling.gram_hsum, conjTranspose_submatrix]
    unfold GlobalTheory.Doubling.blkMat
    simp [submatrix_mul_equiv, conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromBlocks, fromCols_mul_fromRows]
  orth := by
    rw [GlobalTheory.Doubling.gram_hsum, conjTranspose_submatrix]
    unfold GlobalTheory.Doubling.blkMat
    simp [submatrix_mul_equiv, conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromBlocks, fromCols_mul_fromRows]
  rank_add := rfl

theorem finPart_conj (z : AE D) : finPart D (cA D z) = sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig (finPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem infPart_conj (z : AE D) : infPart D (cA D z) = sigR (Ainf D.host.F) D.sp.cm.sig (infPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem fin_dagger (S T : HSp D) {x : WO S T} (hx : x.map (finPart D) = 0) : (dagger S T x).map (finPart D) = 0 := by
  refine map_mul_eq_zero_right _ _ (map_mul_eq_zero_left _ ?_ _)
  funext i j
  have := congrFun (congrFun hx j) i
  change finPart D (x j i) = 0 at this
  change finPart D (cA D (x j i)) = 0
  rw [finPart_conj, this, map_zero]

theorem inf_dagger (S T : HSp D) {x : WO S T} (hx : x.map (infPart D) = 0) : (dagger S T x).map (infPart D) = 0 := by
  refine map_mul_eq_zero_right _ _ (map_mul_eq_zero_left _ ?_ _)
  funext i j
  have := congrFun (congrFun hx j) i
  change infPart D (x j i) = 0 at this
  change infPart D (cA D (x j i)) = 0
  rw [infPart_conj, this, map_zero]

def daggerHom (S T : HSp D) : WO S T →+ WO T S where
  toFun := dagger S T
  map_zero' := by simp [dagger]
  map_add' x y := by simp only [dagger, adj_add, Matrix.add_mul, Matrix.mul_add]

theorem dagger_add (S T : HSp D) (x y : WO S T) : dagger S T (x + y) = dagger S T x + dagger S T y :=
  (daggerHom S T).map_add x y

theorem dagger_zero (S T : HSp D) : dagger S T 0 = 0 := (daggerHom S T).map_zero

theorem continuous_dagger (S T : HSp D) : Continuous (dagger S T) :=
  continuous_const.matrix_mul (continuous_adj.matrix_mul continuous_const)

theorem dagger_rat (S T : HSp D) (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    dagger S T (rat γ) = rat (S.gram⁻¹ * (γᴴ * T.gram)) := by
  rw [rat_mul, rat_mul]; rfl

theorem giA_negSp (S : HSp D) : giA (negSp S) = -giA S := by
  have : (negSp S).gram⁻¹ = -S.gram⁻¹ := by
    refine Matrix.inv_eq_right_inv ?_
    rw [negSp_gram, Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_nonsing_inv _ (gram_isUnit_det S)]
  rw [giA, this, rat_neg]; rfl

theorem symplOH_dagger (S T : HSp D) (x y : WO T S) :
    symplOH S T (dagger T S x) (dagger T S y) = symplOH (negSp T) S x y := by
  have h1 : hO S T (dagger T S x) (dagger T S y) = hO T S y x := by
    simp only [hO_eq_trace, dagger, adj_mul, adj_adj, adj_gA, adj_giA, Matrix.mul_assoc, giA_gA_cancel, gA_giA_cancel]
    rw [trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have h2 : hO (negSp T) S x y = -hO T S x y := by
    rw [hO_eq_trace, hO_eq_trace, giA_negSp, Matrix.neg_mul, trace_neg]
  rw [symplOH_eq, h1, ← symplOH_eq, symplOH_skew, symplOH_eq, symplOH_eq, h2, map_neg]

variable {W A A' : HSp D} (d : OrthDec W A (negSp A')) (S : HSp D)

def fstH : WO W S →+ WO A S := (AddMonoidHom.fst _ _).comp (d.resS S).toAddMonoidHom

def sndH : WO W S →+ WO S A' := (daggerHom A' S).comp ((AddMonoidHom.snd _ _).comp (d.resS S).toAddMonoidHom)

def inlH : WO A S →+ WO W S := (d.resS S).symm.toAddMonoidHom.comp (AddMonoidHom.inl _ _)

def inrH : WO S A' →+ WO W S :=
  (d.resS S).symm.toAddMonoidHom.comp ((AddMonoidHom.inr _ _).comp (daggerHom S A'))

theorem fstH_apply (x : WO W S) : fstH d S x = (d.resS S x).1 := rfl
theorem sndH_apply (x : WO W S) : sndH d S x = dagger A' S (d.resS S x).2 := rfl
theorem inlH_apply (u : WO A S) : inlH d S u = (d.resS S).symm (u, 0) := rfl
theorem inrH_apply (v : WO S A') : inrH d S v = (d.resS S).symm (0, dagger S A' v) := rfl

theorem fst_inl (u : WO A S) : fstH d S (inlH d S u) = u := by
  rw [fstH_apply, inlH_apply, AddEquiv.apply_symm_apply]
theorem fst_inr (v : WO S A') : fstH d S (inrH d S v) = 0 := by
  rw [fstH_apply, inrH_apply, AddEquiv.apply_symm_apply]
theorem snd_inl (u : WO A S) : sndH d S (inlH d S u) = 0 := by
  rw [sndH_apply, inlH_apply, AddEquiv.apply_symm_apply]; exact dagger_zero A' S
theorem snd_inr (v : WO S A') : sndH d S (inrH d S v) = v := by
  rw [sndH_apply, inrH_apply, AddEquiv.apply_symm_apply]; exact dagger_dagger S A' v

theorem continuous_fstH : Continuous (fstH d S) := continuous_fst.comp (d.continuous_resS S)
theorem continuous_sndH : Continuous (sndH d S) :=
  (continuous_dagger A' S).comp (continuous_snd.comp (d.continuous_resS S))
theorem continuous_inlH : Continuous (inlH d S) :=
  (d.continuous_resS_symm S).comp (continuous_id.prodMk continuous_const)
theorem continuous_inrH : Continuous (inrH d S) :=
  (d.continuous_resS_symm S).comp (continuous_const.prodMk (continuous_dagger S A'))

theorem symplOH_split (x y : WO W S) :
    symplOH W S x y = symplOH A S (fstH d S x) (fstH d S y) + symplOH S A' (sndH d S x) (sndH d S y) := by
  rw [d.symplOH_resS, sndH_apply, sndH_apply, symplOH_dagger]; rfl

theorem map_resS_symm {B : Type} [CommRing B] (φ : AE D →+* B) {u : WO A S} {v : WO (negSp A') S}
    (hu : u.map φ = 0) (hv : v.map φ = 0) : ((d.resS S).symm (u, v)).map φ = 0 := by
  rw [d.resS_symm_apply, Matrix.map_add _ (map_add φ), map_mul_eq_zero_left φ hu, map_mul_eq_zero_left φ hv, add_zero]

theorem map_inlH {B : Type} [CommRing B] (φ : AE D →+* B) {u : WO A S} (hu : u.map φ = 0) : (inlH d S u).map φ = 0 :=
  map_resS_symm d S φ hu (Matrix.map_zero _ φ.map_zero)

theorem fin_inrH {v : WO S A'} (hv : v.map (finPart D) = 0) : (inrH d S v).map (finPart D) = 0 :=
  map_resS_symm d S _ (Matrix.map_zero _ (finPart D).map_zero) (fin_dagger S A' hv)

theorem inf_inrH {v : WO S A'} (hv : v.map (infPart D) = 0) : (inrH d S v).map (infPart D) = 0 :=
  map_resS_symm d S _ (Matrix.map_zero _ (infPart D).map_zero) (inf_dagger S A' hv)

def join (C : WO A S → WO S A' → ℂ) : WO W S → ℂ := fun x => C (d.resS S x).1 (dagger A' S (d.resS S x).2)

theorem join_apply (C : WO A S → WO S A' → ℂ) (x : WO W S) : join d S C x = C (fstH d S x) (sndH d S x) := rfl

theorem join_symm (C : WO A S → WO S A' → ℂ) (u : WO A S) (y : WO (negSp A') S) :
    join d S C ((d.resS S).symm (u, y)) = C u (dagger A' S y) := by
  rw [join, AddEquiv.apply_symm_apply]

theorem join_inl_inr (C : WO A S → WO S A' → ℂ) (u : WO A S) (v : WO S A') :
    join d S C (inlH d S u + inrH d S v) = C u v := by
  rw [join_apply, map_add, map_add, fst_inl, fst_inr, snd_inl, snd_inr, add_zero, zero_add]

variable {S} {ψ : AddChar (AF D.host.F) ℂ} {C : WO A S → WO S A' → ℂ}

theorem isThetaFunO_join (h : IsBiTheta ψ A S A' C) : IsThetaFunO ψ W S (join d S C) where
  quasi γ w := by
    have e₁ : fstH d S (ratW S W γ) = ratW S A (γ * d.iA) := (rat_mul γ d.iA).symm
    have e₂ : sndH d S (ratW S W γ) = ratW A' S (A'.gram⁻¹ * ((γ * d.iB)ᴴ * S.gram)) := by
      rw [ratW_eq A' S, ← dagger_rat A' S, rat_mul]; rfl
    rw [join_apply, join_apply, map_add, map_add, symplOH_split d, e₁, e₂, h.quasiL, h.quasiR, neg_add,
      AddChar.map_add_eq_mul, mul_assoc]
  level := by
    obtain ⟨U₁, hU₁, k₁⟩ := h.levL
    obtain ⟨U₂, hU₂, k₂⟩ := h.levR
    refine ⟨U₁.comap (fstH d S) ⊓ U₂.comap (sndH d S),
      (hU₁.preimage (continuous_fstH d S)).inter (hU₂.preimage (continuous_sndH d S)), fun u hu h0 => ?_⟩
    funext w
    have e₁ := congrFun (k₁ _ hu.1 (map_mul_eq_zero_left _ h0 _) (sndH d S w + sndH d S u)) (fstH d S w)
    have e₂ := congrFun (k₂ _ hu.2 (inf_dagger A' S (map_mul_eq_zero_left _ h0 _)) (fstH d S w)) (sndH d S w)
    simp only [heisO] at e₁ e₂ ⊢
    rw [join_apply, join_apply, ← e₂, ← e₁, symplOH_split d, AddChar.map_add_eq_mul, map_add, map_add]
    ring
  cont := h.cont.comp ((continuous_fstH d S).prodMk (continuous_sndH d S))
  smooth k L hL h0 w := by
    simp only [join_apply, map_add]
    exact h.smooth k ((fstH d S).comp L) ((sndH d S).comp L) ((continuous_fstH d S).comp hL)
      ((continuous_sndH d S).comp hL) (fun t => map_mul_eq_zero_left _ (h0 t) _)
      (fun t => fin_dagger A' S (map_mul_eq_zero_left _ (h0 t) _)) _ _

theorem cont_of_join (h : IsThetaFunO ψ W S (join d S C)) : Continuous fun p : WO A S × WO S A' => C p.1 p.2 := by
    have := h.cont.comp (((continuous_inlH d S).comp continuous_fst).add ((continuous_inrH d S).comp continuous_snd))
    exact this.congr fun p => join_inl_inr d S C p.1 p.2

theorem smooth_of_join (h : IsThetaFunO ψ W S (join d S C)) : IsBiSmooth C := fun n L L' hL hL' h0 h0' u v => by
    have := h.smooth n ((inlH d S).comp L + (inrH d S).comp L')
      (((continuous_inlH d S).comp hL).add ((continuous_inrH d S).comp hL')) (fun t => by
        change (inlH d S (L t) + inrH d S (L' t)).map _ = 0
        rw [Matrix.map_add _ (finPart D).map_add, map_inlH d S _ (h0 t), fin_inrH d S (h0' t), add_zero])
      (inlH d S u + inrH d S v)
    convert this using 2 with t
    rw [← join_inl_inr d S C, (inlH d S).map_add, (inrH d S).map_add, add_add_add_comm]; rfl

theorem quasiL_of_join (h : IsThetaFunO ψ W S (join d S C)) (γ) (u : WO A S) (v : WO S A') :
    C (ratW S A γ + u) v = ψ (-(symplOH A S (ratW S A γ) u)) * C u v := by
    have e : inlH d S (ratW S A γ) = ratW S W (γ * d.qA) := by
      rw [inlH_apply, d.resS_symm_apply, Matrix.zero_mul, add_zero, ratW_eq S W, rat_mul]; rfl
    have := h.quasi (γ * d.qA) (inlH d S u + inrH d S v)
    rw [← e, ← add_assoc, ← (inlH d S).map_add, join_inl_inr, join_inl_inr, symplOH_split d, (fstH d S).map_add, fst_inl, fst_inl, fst_inr,
      snd_inl, symplOH_zero_left, add_zero, add_zero] at this
    exact this

theorem quasiR_of_join (h : IsThetaFunO ψ W S (join d S C)) (γ) (u : WO A S) (v : WO S A') :
    C u (ratW A' S γ + v) = ψ (-(symplOH S A' (ratW A' S γ) v)) * C u v := by
    have e : inrH d S (ratW A' S γ) = ratW S W (S.gram⁻¹ * (γᴴ * A'.gram) * d.qB) := by
      rw [inrH_apply, d.resS_symm_apply, Matrix.zero_mul, zero_add, ratW_eq S W, rat_mul, ← dagger_rat S A']; rfl
    have := h.quasi (S.gram⁻¹ * (γᴴ * A'.gram) * d.qB) (inlH d S u + inrH d S v)
    rw [← e, add_left_comm, ← (inrH d S).map_add, join_inl_inr, join_inl_inr, symplOH_split d, (sndH d S).map_add, fst_inr, snd_inr,
      snd_inl, snd_inr, symplOH_zero_left, zero_add, zero_add] at this
    exact this

theorem levL_of_join (h : IsThetaFunO ψ W S (join d S C)) : ∃ U : AddSubgroup (WO A S), IsOpen (U : Set (WO A S)) ∧
    ∀ a ∈ U, a.map (infPart D) = 0 → ∀ v, heisO ψ A S a (fun u => C u v) = fun u => C u v := by
    obtain ⟨U, hU, k⟩ := h.level
    refine ⟨U.comap (inlH d S), hU.preimage (continuous_inlH d S), fun a ha h0 v => funext fun u => ?_⟩
    have := congrFun (k _ ha (map_inlH d S _ h0)) (inlH d S u + inrH d S v)
    simp only [heisO] at this ⊢
    rw [add_right_comm, ← (inlH d S).map_add, join_inl_inr, join_inl_inr, symplOH_split d, (fstH d S).map_add, fst_inl, fst_inl, fst_inr,
      snd_inl d S a, symplOH_zero_right, add_zero, add_zero] at this
    exact this

theorem levR_of_join (h : IsThetaFunO ψ W S (join d S C)) : ∃ U : AddSubgroup (WO S A'), IsOpen (U : Set (WO S A')) ∧
    ∀ a ∈ U, a.map (infPart D) = 0 → ∀ u, heisO ψ S A' a (C u) = C u := by
    obtain ⟨U, hU, k⟩ := h.level
    refine ⟨U.comap (inrH d S), hU.preimage (continuous_inrH d S), fun a ha h0 u => funext fun v => ?_⟩
    have := congrFun (k _ ha (inf_inrH d S h0))
      (inlH d S u + inrH d S v)
    simp only [heisO] at this ⊢
    rw [add_assoc, ← (inrH d S).map_add, join_inl_inr, join_inl_inr, symplOH_split d, (sndH d S).map_add, fst_inr d S a, snd_inl,
      snd_inr, snd_inr, symplOH_zero_right, zero_add, zero_add] at this
    exact this

theorem isBiTheta_of_join (h : IsThetaFunO ψ W S (join d S C)) : IsBiTheta ψ A S A' C :=
  ⟨cont_of_join d h, smooth_of_join d h, quasiL_of_join d h, quasiR_of_join d h, levL_of_join d h, levR_of_join d h⟩

theorem isBiTheta_iff_join : IsBiTheta ψ A S A' C ↔ IsThetaFunO ψ W S (join d S C) :=
  ⟨isThetaFunO_join d, isBiTheta_of_join d⟩

end GlobalTheory.BiTransfer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPolynomialFockThetaVectorOrthogonalBoxProduct
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
open GlobalTheory.Core.Rk.SumBox
open GlobalTheory.OrientedHeis GlobalTheory.Core.Rk.FockBox

noncomputable section

namespace GlobalTheory.Core.Rk.FockBoxT

theorem killed_of_leibniz₂ {P₁ P₂ Q U₁ U₂ V : Type} [Zero U₁] [Zero U₂] [AddCommGroup V] (a₁ : P₁ → U₁ → U₁)
    (a₂ : P₂ → U₂ → U₂) (b : Q → V → V) (T₁ : U₁ → Prop) (T₂ : U₂ → Prop)
    (TV : V → Prop) (δ : U₁ → U₂ → V) (c₁ : Q → P₁) (c₂ : Q → P₂) (ha₁ : ∀ p f, T₁ f → T₁ (a₁ p f))
    (ha₂ : ∀ p f, T₂ f → T₂ (a₂ p f)) (hb : ∀ q f, TV f → TV (b q f))
    (hadd : ∀ q f g, TV f → TV g → b q (f + g) = b q f + b q g) (hb0 : ∀ q, b q 0 = 0)
    (hδ : ∀ f g, T₁ f → T₂ g → TV (δ f g)) (h1 : ∀ g, δ 0 g = 0) (h2 : ∀ f, δ f 0 = 0)
    (hL : ∀ q f g, T₁ f → T₂ g → b q (δ f g) = δ (a₁ (c₁ q) f) g + δ f (a₂ (c₂ q) g)) (N : ℕ) :
    ∀ (N₁ N₂ : ℕ) (f : U₁) (g : U₂), N₁ + N₂ ≤ N → T₁ f → T₂ g →
      (∀ l : List P₁, l.length = N₁ → l.foldr a₁ f = 0) → (∀ l : List P₂, l.length = N₂ → l.foldr a₂ g = 0) →
      ∀ l : List Q, l.length = N → l.foldr b (δ f g) = 0 := by
  have w0 : ∀ l : List Q, l.foldr b 0 = 0 := fun l => by
    induction l with
    | nil => rfl
    | cons q l ih => rw [List.foldr_cons, ih, hb0]
  have wT : ∀ (l : List Q) f, TV f → TV (l.foldr b f) := fun l f hf => by
    induction l with
    | nil => exact hf
    | cons q l ih => exact hb _ _ ih
  have wadd : ∀ (l : List Q) f g, TV f → TV g → l.foldr b (f + g) = l.foldr b f + l.foldr b g := fun l f g hf hg => by
    induction l with
    | nil => rfl
    | cons q l ih => rw [List.foldr_cons, ih, hadd _ _ _ (wT l f hf) (wT l g hg)]; rfl
  have step : ∀ {P U : Type} [Zero U] (a : P → U → U) (M : ℕ) (f : U) (p : P),
      (∀ l : List P, l.length = M + 1 → l.foldr a f = 0) →
      ∀ l : List P, l.length = M → l.foldr a (a p f) = 0 := fun a M f p h l hl => by
    have := h (l ++ [p]) (by simp [hl])
    rwa [List.foldr_append] at this
  induction N with
  | zero =>
    intro N₁ N₂ f g hN _ _ k₁ _ l _
    have : f = 0 := k₁ [] (by simp; omega)
    rw [this, h1, w0]
  | succ N ih =>
    intro N₁ N₂ f g hN hf hg k₁ k₂ l hl
    rcases N₁ with _ | M₁
    · have : f = 0 := k₁ [] rfl
      rw [this, h1, w0]
    rcases N₂ with _ | M₂
    · have : g = 0 := k₂ [] rfl
      rw [this, h2, w0]
    obtain rfl | ⟨l', q, rfl⟩ := l.eq_nil_or_concat'
    · simp at hl
    have hl' : l'.length = N := by simpa using hl
    rw [List.foldr_append, List.foldr_cons, List.foldr_nil, hL q f g hf hg,
      wadd _ _ _ (hδ _ _ (ha₁ _ _ hf) hg) (hδ _ _ hf (ha₂ _ _ hg)),
      ih M₁ (M₂ + 1) _ _ (by omega) (ha₁ _ _ hf) hg (step _ _ _ _ k₁) k₂ l' hl',
      ih (M₁ + 1) M₂ _ _ (by omega) hf (ha₂ _ _ hg) k₁ (step _ _ _ _ k₂) l' hl', add_zero]

variable {D : D7} {θ : InfFam D} {ψ : AddChar (AF D.host.F) ℂ}

theorem lineAt_mul_left (hθ : IsInfFam θ) {k m n : ℕ} (p : Mx D k m) (τ : D.what₂.Tau)
    (z : Matrix (Fin m) (Fin n) ℂ) (t : ℝ) :
    lineAt θ τ (Formalism.IndefR.Datum.compAt θ τ p * z) t = (HMul.hMul p (lineAt θ τ z t) : Mx D k n) := by
  have hL := isLineAt_lineAt hθ τ z
  let L : ℝ →+ Mx D k n :=
    { toFun := fun t => HMul.hMul p (lineAt θ τ z t)
      map_zero' := by rw [AddMonoidHom.map_zero, Matrix.mul_zero]
      map_add' := fun s t => by rw [AddMonoidHom.map_add, Matrix.mul_add] }
  have hL' : IsLineAt θ τ (Formalism.IndefR.Datum.compAt θ τ p * z) L := by
    refine ⟨continuous_const.matrix_mul hL.1, fun t => ?_, fun t τ' => ?_⟩
    · show (HMul.hMul p (lineAt θ τ z t) : Mx D k n).map (finPart D) = 0
      rw [Matrix.map_mul, hL.2.1, Matrix.mul_zero]
    · show Formalism.IndefR.Datum.compAt θ τ' (HMul.hMul p (lineAt θ τ z t) : Mx D k n) = _
      rw [GlobalTheory.OrientedHeis.compAt_mul, hL.2.2]
      split_ifs with e
      · rw [e, Matrix.mul_smul]
      · rw [Matrix.mul_zero]
  rw [GlobalTheory.RealLineAt.lineAt_unique D θ hθ _ _ τ _ _ _ (isLineAt_lineAt hθ τ _) hL']
  rfl

variable {A B W H : HSp D} (o : OrthDec B W H)

theorem compAt_pA (hθ : IsInfFam θ) (τ : D.what₂.Tau) :
    Formalism.IndefR.Datum.compAt θ τ o.pA = o.qA.map (tauE D τ) := by
  ext i j
  exact GlobalTheory.FockCompare.comp_incA hθ τ _

theorem compAt_pB (hθ : IsInfFam θ) (τ : D.what₂.Tau) :
    Formalism.IndefR.Datum.compAt θ τ o.pB = o.qB.map (tauE D τ) := by
  ext i j
  exact GlobalTheory.FockCompare.comp_incA hθ τ _

theorem dRho_boxT (hθ : IsInfFam θ) (hψ : IsStdChar D ψ (-1)) (τ : D.what₂.Tau)
    (z : Matrix (Fin B.rank) (Fin A.rank) ℂ) {f : WO A W → ℂ} {g : WO A H → ℂ} (hf : IsThetaFunO ψ A W f)
    (hg : IsThetaFunO ψ A H g) :
    Formalism.IndefR.Datum.dRho (heisO ψ A B) θ τ z (o.boxT A f g) =
      o.boxT A (Formalism.IndefR.Datum.dRho (heisO ψ A W) θ τ (o.qA.map (tauE D τ) * z) f) g +
        o.boxT A f (Formalism.IndefR.Datum.dRho (heisO ψ A H) θ τ (o.qB.map (tauE D τ) * z) g) := by
  funext x
  have d := (hasDerivAt_dRho hθ hψ τ (o.qA.map (tauE D τ) * z) hf (o.resT A x).1).mul
    (hasDerivAt_dRho hθ hψ τ (o.qB.map (tauE D τ) * z) hg (o.resT A x).2)
  simp only [map_zero, heisO_zero] at d
  refine Eq.trans ?_ d.deriv
  unfold Formalism.IndefR.Datum.dRho
  congr 1
  funext t
  rw [o.heisO_boxT, Pi.mul_apply, ← compAt_pA o hθ, ← compAt_pB o hθ, lineAt_mul_left hθ, lineAt_mul_left hθ]
  rfl

theorem qA_sumMat (sW : RealMat W) (sH : RealMat H) (τ : D.what₂.Tau) :
    o.qA.map (tauE D τ) * sumMat o sW sH τ = sW τ * o.qA.map (tauE D τ) := by
  simp only [sumMat_apply, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.map_mul, o.qA_iA, o.qA_iB,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_zero _ (map_zero _), Matrix.one_mul, Matrix.zero_mul, add_zero]

theorem qB_sumMat (sW : RealMat W) (sH : RealMat H) (τ : D.what₂.Tau) :
    o.qB.map (tauE D τ) * sumMat o sW sH τ = sH τ * o.qB.map (tauE D τ) := by
  simp only [sumMat_apply, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.map_mul, o.qB_iA, o.qB_iB,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_zero _ (map_zero _), Matrix.one_mul, Matrix.zero_mul, zero_add]

theorem mul_cplxO {k m n : ℕ} {q : Matrix (Fin k) (Fin m) ℂ} {s : Matrix (Fin m) (Fin m) ℂ}
    {s' : Matrix (Fin k) (Fin k) ℂ} (h : q * s = s' * q) (r : Matrix (Fin n) (Fin n) ℂ) (z : Matrix (Fin m) (Fin n) ℂ) :
    q * cplxO r s z = cplxO r s' (q * z) := by
  unfold cplxO
  rw [Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h, Matrix.mul_assoc s']

theorem annih_boxT (hθ : IsInfFam θ) (hψ : IsStdChar D ψ (-1)) (τ : D.what₂.Tau)
    (s : Matrix (Fin A.rank) (Fin A.rank) ℂ) (sW : RealMat W) (sH : RealMat H)
    (z : Matrix (Fin B.rank) (Fin A.rank) ℂ) {f : WO A W → ℂ} {g : WO A H → ℂ} (hf : IsThetaFunO ψ A W f)
    (hg : IsThetaFunO ψ A H g) :
    annih (heisO ψ A B) θ τ (cplxO s (sumMat o sW sH τ)) z (o.boxT A f g) =
      o.boxT A (annih (heisO ψ A W) θ τ (cplxO s (sW τ)) (o.qA.map (tauE D τ) * z) f) g +
        o.boxT A f (annih (heisO ψ A H) θ τ (cplxO s (sH τ)) (o.qB.map (tauE D τ) * z) g) := by
  unfold annih
  rw [dRho_boxT o hθ hψ τ _ hf hg, dRho_boxT o hθ hψ τ _ hf hg, mul_cplxO (qA_sumMat o sW sH τ),
    mul_cplxO (qB_sumMat o sW sH τ)]
  funext x
  simp only [OrthDec.boxT, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem isFockVec_boxT : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B W H : HSp D) (o : OrthDec B W H) (sA : RealMat A) (sW : RealMat W) (sH : RealMat H), IsStdChar D ψ (-1) → IsInfFam θ → ∀ Φ Φ', IsFockVec ψ θ A W sA sW Φ → IsFockVec ψ θ A H sA sH Φ' → IsFockVec ψ θ A B sA (sumMat o sW sH) (o.boxT A Φ Φ') := by
  intro D ψ θ A B W H o sA sW sH hψ hθ Φ₁ Φ₂ ⟨t₁, N₁, k₁⟩ ⟨t₂, N₂, k₂⟩
  have hT : ∀ (S : HSp D) τ J z f, IsThetaFunO ψ A S f → IsThetaFunO ψ A S (annih (heisO ψ A S) θ τ J z f) :=
    fun S τ J z f hf => theta_add (theta_dRho hθ hψ τ z hf) (theta_smul _ (theta_dRho hθ hψ τ _ hf))
  refine ⟨o.isThetaFunO_boxT t₁ t₂, N₁ + N₂, ?_⟩
  refine killed_of_leibniz₂ (P₁ := D.what₂.Tau × Matrix (Fin W.rank) (Fin A.rank) ℂ)
    (P₂ := D.what₂.Tau × Matrix (Fin H.rank) (Fin A.rank) ℂ)
    (Q := D.what₂.Tau × Matrix (Fin B.rank) (Fin A.rank) ℂ)
    (fun p f => annih (heisO ψ A W) θ p.1 (cplxO (sA p.1) (sW p.1)) p.2 f)
    (fun p f => annih (heisO ψ A H) θ p.1 (cplxO (sA p.1) (sH p.1)) p.2 f)
    (fun p f => annih (heisO ψ A B) θ p.1 (cplxO (sA p.1) (sumMat o sW sH p.1)) p.2 f)
    (IsThetaFunO ψ A W) (IsThetaFunO ψ A H) (IsThetaFunO ψ A B) (o.boxT A)
    (fun q => (q.1, o.qA.map (tauE D q.1) * q.2)) (fun q => (q.1, o.qB.map (tauE D q.1) * q.2))
    (fun p f hf => hT W _ _ _ f hf) (fun p f hf => hT H _ _ _ f hf) (fun p f hf => hT B _ _ _ f hf)
    (fun q f g hf hg => ?_) (fun q => ?_)
    (fun f g hf hg => o.isThetaFunO_boxT hf hg) (fun g => ?_) (fun f => ?_)
    (fun q f g hf hg => annih_boxT o hθ hψ q.1 (sA q.1) sW sH q.2 hf hg)
    _ N₁ N₂ Φ₁ Φ₂ le_rfl t₁ t₂ k₁ k₂
  · simp only [annih]
    rw [GlobalTheory.Core.Rk.FockBox.dRho_add hθ hψ _ _ hf hg, GlobalTheory.Core.Rk.FockBox.dRho_add hθ hψ _ _ hf hg, smul_add]
    abel
  · funext x
    simp [annih, Formalism.IndefR.Datum.dRho, heisO]
  · funext x
    simp [OrthDec.boxT]
  · funext x
    simp [OrthDec.boxT]

end GlobalTheory.Core.Rk.FockBoxT

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaFunctionCompSkewAdjointSimilitude
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KappaTheta

theorem isThetaFunO_comp_kappa : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (L S L'' : HSp D) (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E), τᴴ * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram → ∀ f, IsThetaFunO ψ L S f → IsThetaFunO ψ S L'' (fun w => f (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L''.rank) * w))) := by
  intro D ψ L S L'' τ hτ f hf
  have hτ' : τᴴ * (L.gram * τ) = (((-1 : ℤ) : D.host.E) * (D.host.xi0 * star D.host.xi0)) • L''.gram := by
    rw [hτ]; congr 1; push_cast; ring
  set κ : WO S L'' → WO L S := fun w => GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L''.rank) * w) with hκdef
  obtain ⟨hadd, hcont, hrat, -, hsym, hparts⟩ :=
    GlobalTheory.LinkKappa.kappa_props D L L'' S τ (-1) hτ' κ (fun _ => rfl)
  have hH : ∀ w w', symplOH L S (κ w) (κ w') = symplOH S L'' w w' := fun w w' => by
    unfold symplOH
    rw [hsym]
    push_cast
    ring
  let A : WO S L'' →+ WO L S := AddMonoidHom.mk' κ hadd
  refine ⟨fun γ w => ?_, ?_, hf.cont.comp hcont, fun k M h1 h2 w => ?_⟩
  · obtain ⟨γ', hγ'⟩ := hrat (ratW L'' S γ) ⟨γ, rfl⟩
    show f (κ (ratW L'' S γ + w)) = ψ (-(symplOH S L'' (ratW L'' S γ) w)) * f (κ w)
    have e : κ (ratW L'' S γ) = ratW S L γ' := hγ'.symm
    rw [hadd, ← hH, e, hf.quasi]
  · obtain ⟨U, hU, h⟩ := hf.level
    refine ⟨U.comap A, hU.preimage hcont, fun u hu h0 => ?_⟩
    funext w
    have e := congrFun (h _ hu ((hparts u).1 h0)) (κ w)
    unfold heisO at e ⊢
    show ψ (symplOH S L'' w u) * f (κ (w + u)) = f (κ w)
    rw [← e, ← hH, hadd]
    rfl
  · have h3 : ∀ t, (A (M t)).map (finPart D) = 0 := fun t => (hparts (M t)).2 (h2 t)
    have := hf.smooth k (A.comp M) (hcont.comp h1) h3 (κ w)
    have heq : (fun t => f (κ (w + M t))) = fun t => f (κ w + A (M t)) :=
      funext fun t => congrArg f (hadd w (M t))
    exact (congrArg (ContDiff ℝ _) heq).mpr this

end GlobalTheory.KappaTheta

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LinearIndependentOfIsParamFunVStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearIndependent_of_ne_zero_of_isParamFunV_of_separated : ∀ (D : D7) (V : HSp D) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (ι : Type) (f : ι → (GA D V → ℂ)) (B : ι → GlobalTheory.LFun.Fam D.host.E), (∀ i, f i ≠ 0) → (∀ i, GlobalTheory.LFun.IsParamFunV V Sb (f i) (B i)) → (∀ i i', i ≠ i' → ∃ w ∉ GlobalTheory.LFun.above D.host.E (Sb : Set (HeightOneSpectrum (𝓞 D.host.F))), B i w ≠ B i' w) → LinearIndependent ℂ f := by
  first | exact @GlobalTheory.ChainOnto.linearIndependent_of_isParamFunV | exact GlobalTheory.ChainOnto.linearIndependent_of_isParamFunV | (intros; apply GlobalTheory.ChainOnto.linearIndependent_of_isParamFunV <;> assumption)
end

