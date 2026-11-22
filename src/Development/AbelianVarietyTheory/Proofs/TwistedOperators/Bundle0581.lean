import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0526
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0751
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0032
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0561
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0484
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0567
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAllTiedNotStable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0007
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0091
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0020
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0556
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0535
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0247

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairVecSumEqOfProdEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.TopZeroInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.TopZeroInv

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

variable (W) in

def thetaSub (p : Pair T) : Submodule ℂ (WO (G.pS p) (G.pT p) → ℂ) where
  carrier := {f | IsThetaFunO W.ψ _ _ f}
  add_mem' := GlobalTheory.OrientedHeis.theta_add
  zero_mem' := GlobalTheory.OrientedHeis.theta_zero
  smul_mem' c _ hf := GlobalTheory.OrientedHeis.theta_smul c hf

theorem colV_congr (S : GridChoice W U) {t : T} {fs fs' : Vecs G t} (h : ∀ j, fs (.inl j) = fs' (.inl j))
    (x : ∀ j, FinPt G (.top j)) : colV S fs x = colV S fs' x := by
  have e : (fun j => if h : j < D.R.m then kkVec S (.top t j) (fs (.inl ⟨j, h⟩)) (x j) (x (j + 1)) else 0) =
      (fun j => if h : j < D.R.m then kkVec S (.top t j) (fs' (.inl ⟨j, h⟩)) (x j) (x (j + 1)) else 0) := by
    funext j; split_ifs with hj
    · rw [h]
    · rfl
  simp only [colV, e]

theorem rowV_congr (S : GridChoice W U) {t : T} {fs fs' : Vecs G t} (h : ∀ i, fs (.inr i) = fs' (.inr i))
    (y : ∀ i, FinPt G (.grid i D.R.m)) : rowV S fs y = rowV S fs' y := by
  have e : (fun i => if h : i < D.R.m then kkVec S (.chi i D.R.m) (fs (.inr ⟨i, h⟩)) (y i) (y (i + 1)) else 0) =
      (fun i => if h : i < D.R.m then kkVec S (.chi i D.R.m) (fs' (.inr ⟨i, h⟩)) (y i) (y (i + 1)) else 0) := by
    funext i; split_ifs with hi
    · rw [h]
    · rfl
  simp only [rowV, e]

theorem colK_update (S : GridChoice W U) {t : T} (fs : Vecs G t) (x : ∀ j, FinPt G (.top j)) (j₀ : Fin D.R.m)
    (F : WO (G.pS (arrP t (.inl j₀ : Arr D))) (G.pT (arrP t (.inl j₀ : Arr D))) → ℂ) :
    (fun j => if h : j < D.R.m then kkVec S (.top t j) (Function.update fs (.inl j₀) F (.inl ⟨j, h⟩)) (x j) (x (j + 1))
      else 0) =
    Function.update (fun j => if h : j < D.R.m then kkVec S (.top t j) (fs (.inl ⟨j, h⟩)) (x j) (x (j + 1)) else 0) j₀.1
      (kkVec S (.top t j₀.1) F (x j₀.1) (x (j₀.1 + 1))) := by
  funext j
  by_cases hj : j = j₀.1
  · subst hj
    rw [Function.update_self, dif_pos j₀.2]
    show kkVec S (.top t j₀.1) (Function.update fs (.inl j₀) F (.inl j₀)) _ _ = _
    rw [Function.update_self]
  · rw [Function.update_of_ne hj]
    split_ifs with h
    · rw [Function.update_of_ne]
      intro e; exact hj (congrArg Fin.val (Sum.inl_injective e))
    · rfl

end GlobalTheory.TopZeroInv

namespace GlobalTheory.TopZeroInv

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem rowK_update (S : GridChoice W U) {t : T} (fs : Vecs G t) (y : ∀ i, FinPt G (.grid i D.R.m)) (i₀ : Fin D.R.m)
    (F : WO (G.pS (arrP t (.inr i₀ : Arr D))) (G.pT (arrP t (.inr i₀ : Arr D))) → ℂ) :
    (fun i => if h : i < D.R.m then kkVec S (.chi i D.R.m) (Function.update fs (.inr i₀) F (.inr ⟨i, h⟩)) (y i) (y (i + 1))
      else 0) =
    Function.update (fun i => if h : i < D.R.m then kkVec S (.chi i D.R.m) (fs (.inr ⟨i, h⟩)) (y i) (y (i + 1)) else 0) i₀.1
      (kkVec S (.chi i₀.1 D.R.m) F (y i₀.1) (y (i₀.1 + 1))) := by
  funext i
  by_cases hi : i = i₀.1
  · subst hi
    rw [Function.update_self, dif_pos i₀.2]
    show kkVec S (.chi i₀.1 D.R.m) (Function.update fs (.inr i₀) F (.inr i₀)) _ _ = _
    rw [Function.update_self]
  · rw [Function.update_of_ne hi]
    split_ifs with h
    · rw [Function.update_of_ne]
      intro e; exact hi (congrArg Fin.val (Sum.inr_injective e))
    · rfl

theorem colV_update_add (S : GridChoice W U) {t : T} (fs : Vecs G t) (x : ∀ j, FinPt G (.top j)) (j₀ : Fin D.R.m)
    {F F' : WO (G.pS (arrP t (.inl j₀ : Arr D))) (G.pT (arrP t (.inl j₀ : Arr D))) → ℂ}
    (hF : IsThetaFunO W.ψ _ _ F) (hF' : IsThetaFunO W.ψ _ _ F') :
    colV S (Function.update fs (.inl j₀) (F + F')) x =
      colV S (Function.update fs (.inl j₀) F) x + colV S (Function.update fs (.inl j₀) F') x := by
  have h : kkVec S (.top t j₀.1) (F + F') (x j₀.1) (x (j₀.1 + 1)) =
      kkVec S (.top t j₀.1) F (x j₀.1) (x (j₀.1 + 1)) + kkVec S (.top t j₀.1) F' (x j₀.1) (x (j₀.1 + 1)) :=
    GlobalTheory.T.normalizedKernelOfVector_add S (.top t j₀.1) hF hF' _ _
  rw [colV, colV, colV, colK_update, colK_update, colK_update, h, GlobalTheory.T.linearMapChainComposite_update_add _ _ _ _ _ j₀.2, LinearMap.add_comp]

theorem colV_update_smul (S : GridChoice W U) {t : T} (fs : Vecs G t) (x : ∀ j, FinPt G (.top j)) (j₀ : Fin D.R.m) (c : ℂ)
    (F : WO (G.pS (arrP t (.inl j₀ : Arr D))) (G.pT (arrP t (.inl j₀ : Arr D))) → ℂ) :
    colV S (Function.update fs (.inl j₀) (c • F)) x = c • colV S (Function.update fs (.inl j₀) F) x := by
  have h : kkVec S (.top t j₀.1) (c • F) (x j₀.1) (x (j₀.1 + 1)) = c • kkVec S (.top t j₀.1) F (x j₀.1) (x (j₀.1 + 1)) :=
    GlobalTheory.T.normalizedKernelOfVector_smul S (.top t j₀.1) c F _ _
  rw [colV, colV, colK_update, colK_update, h, GlobalTheory.T.linearMapChainComposite_update_smul _ _ _ _ _ j₀.2, LinearMap.smul_comp]

theorem rowV_update_add (S : GridChoice W U) {t : T} (fs : Vecs G t) (y : ∀ i, FinPt G (.grid i D.R.m)) (i₀ : Fin D.R.m)
    {F F' : WO (G.pS (arrP t (.inr i₀ : Arr D))) (G.pT (arrP t (.inr i₀ : Arr D))) → ℂ}
    (hF : IsThetaFunO W.ψ _ _ F) (hF' : IsThetaFunO W.ψ _ _ F') :
    rowV S (Function.update fs (.inr i₀) (F + F')) y =
      rowV S (Function.update fs (.inr i₀) F) y + rowV S (Function.update fs (.inr i₀) F') y := by
  have h : kkVec S (.chi i₀.1 D.R.m) (F + F') (y i₀.1) (y (i₀.1 + 1)) =
      kkVec S (.chi i₀.1 D.R.m) F (y i₀.1) (y (i₀.1 + 1)) + kkVec S (.chi i₀.1 D.R.m) F' (y i₀.1) (y (i₀.1 + 1)) :=
    GlobalTheory.T.normalizedKernelOfVector_add S (.chi i₀.1 D.R.m) hF hF' _ _
  rw [rowV, rowV, rowV, rowK_update, rowK_update, rowK_update, h, GlobalTheory.T.linearMapChainComposite_update_add _ _ _ _ _ i₀.2, LinearMap.add_comp]

theorem rowV_update_smul (S : GridChoice W U) {t : T} (fs : Vecs G t) (y : ∀ i, FinPt G (.grid i D.R.m)) (i₀ : Fin D.R.m)
    (c : ℂ) (F : WO (G.pS (arrP t (.inr i₀ : Arr D))) (G.pT (arrP t (.inr i₀ : Arr D))) → ℂ) :
    rowV S (Function.update fs (.inr i₀) (c • F)) y = c • rowV S (Function.update fs (.inr i₀) F) y := by
  have h : kkVec S (.chi i₀.1 D.R.m) (c • F) (y i₀.1) (y (i₀.1 + 1)) = c • kkVec S (.chi i₀.1 D.R.m) F (y i₀.1) (y (i₀.1 + 1)) :=
    GlobalTheory.T.normalizedKernelOfVector_smul S (.chi i₀.1 D.R.m) c F _ _
  rw [rowV, rowV, rowK_update, rowK_update, h, GlobalTheory.T.linearMapChainComposite_update_smul _ _ _ _ _ i₀.2, LinearMap.smul_comp]

end GlobalTheory.TopZeroInv

namespace GlobalTheory.TopZeroInv

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem coe_update {t : T} (m : ∀ l : Arr D, thetaSub W (arrP t l)) (i : Arr D) (z : thetaSub W (arrP t i)) :
    (fun l => ((Function.update m i z l : thetaSub W (arrP t l)) : WO (G.pS (arrP t l)) (G.pT (arrP t l)) → ℂ)) =
      Function.update (fun l => (m l : WO (G.pS (arrP t l)) (G.pT (arrP t l)) → ℂ)) i (z : _ → ℂ) :=
  funext fun l => Function.apply_update (fun l (q : thetaSub W (arrP t l)) => (q : WO (G.pS (arrP t l)) (G.pT (arrP t l)) → ℂ)) m i z l

theorem pairVec_apply (S : GridChoice W U) {t : T} (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (fs : Vecs G t)
    (v : VV ℂ (wt G (.top 0))) (w : VV ℂ (listedWt G (.grid 0 D.R.m))) :
    pairVec S x y fs v w =
      brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m)) (colV S fs x v) (rowV S fs y w) := rfl

def pairML (S : GridChoice W U) {t : T} (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m))
    (v : VV ℂ (wt G (.top 0))) (w : VV ℂ (listedWt G (.grid 0 D.R.m))) :
    MultilinearMap ℂ (fun l : Arr D => thetaSub W (arrP t l)) ℂ where
  toFun fs := pairVec S (t := t) x y (fun l => ((fs l : thetaSub W (arrP t l)) : WO (G.pS (arrP t l)) (G.pT (arrP t l)) → ℂ)) v w
  map_update_add' := by
    intro inst m i a b
    obtain rfl : inst = (by clear inst; infer_instance : DecidableEq (Arr D)) := Subsingleton.elim _ _
    simp only [coe_update, Submodule.coe_add]
    rcases i with j₀ | i₀
    · have hr : ∀ F, rowV S (Function.update (fun l => (m l : WO (G.pS (arrP t l)) (G.pT (arrP t l)) → ℂ)) (.inl j₀) F) y =
          rowV S (fun l => (m l : WO (G.pS (arrP t l)) (G.pT (arrP t l)) → ℂ)) y := fun F =>
        rowV_congr S (fun i => Function.update_of_ne (Sum.inr_ne_inl) _ _) y
      rw [pairVec_apply, pairVec_apply, pairVec_apply, hr, hr, hr, colV_update_add S _ x j₀ a.2 b.2, LinearMap.add_apply]
      exact LinearMap.map_add₂ _ _ _ _
    · have hc : ∀ F, colV S (Function.update (fun l => (m l : WO (G.pS (arrP t l)) (G.pT (arrP t l)) → ℂ)) (.inr i₀) F) x =
          colV S (fun l => (m l : WO (G.pS (arrP t l)) (G.pT (arrP t l)) → ℂ)) x := fun F =>
        colV_congr S (fun j => Function.update_of_ne (Sum.inl_ne_inr) _ _) x
      rw [pairVec_apply, pairVec_apply, pairVec_apply, hc, hc, hc, rowV_update_add S _ y i₀ a.2 b.2, LinearMap.add_apply]
      exact map_add _ _ _
  map_update_smul' := by
    intro inst m i c a
    obtain rfl : inst = (by clear inst; infer_instance : DecidableEq (Arr D)) := Subsingleton.elim _ _
    simp only [coe_update, Submodule.coe_smul]
    rcases i with j₀ | i₀
    · have hr : ∀ F, rowV S (Function.update (fun l => (m l : WO (G.pS (arrP t l)) (G.pT (arrP t l)) → ℂ)) (.inl j₀) F) y =
          rowV S (fun l => (m l : WO (G.pS (arrP t l)) (G.pT (arrP t l)) → ℂ)) y := fun F =>
        rowV_congr S (fun i => Function.update_of_ne (Sum.inr_ne_inl) _ _) y
      rw [pairVec_apply, pairVec_apply, hr, hr, colV_update_smul S _ x j₀, LinearMap.smul_apply]
      exact LinearMap.map_smul₂ _ _ _ _
    · have hc : ∀ F, colV S (Function.update (fun l => (m l : WO (G.pS (arrP t l)) (G.pT (arrP t l)) → ℂ)) (.inr i₀) F) x =
          colV S (fun l => (m l : WO (G.pS (arrP t l)) (G.pT (arrP t l)) → ℂ)) x := fun F =>
        colV_congr S (fun j => Function.update_of_ne (Sum.inl_ne_inr) _ _) x
      rw [pairVec_apply, pairVec_apply, hc, hc, rowV_update_smul S _ y i₀, LinearMap.smul_apply]
      exact map_smul _ _ _

end GlobalTheory.TopZeroInv

namespace GlobalTheory.TopZeroInv

theorem pairVec_sum_eq_of_prod_eq : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {t : T} {κ : Type} (a : κ →₀ ℂ) (f g : κ → Vecs G t)
    (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (v : VV ℂ (wt G (.top 0)))
    (w : VV ℂ (listedWt G (.grid 0 D.R.m))),
    (∀ c ∈ a.support, ∀ l, IsThetaFunO W.ψ _ _ (f c l)) → (∀ c ∈ a.support, ∀ l, IsThetaFunO W.ψ _ _ (g c l)) →
    (∀ z : ∀ l : Arr D, WO (G.pS (arrP t l)) (G.pT (arrP t l)),
      (a.sum fun c b => b * ∏ l, f c l (z l)) = a.sum fun c b => b * ∏ l, g c l (z l)) →
    (a.sum fun c b => b * pairVec S x y (f c) v w) = a.sum fun c b => b * pairVec S x y (g c) v w := by
  intro D T L sc G W U S t κ a f g x y v w hf hg hprod
  classical
  let f' : κ → ∀ l : Arr D, thetaSub W (arrP t l) := fun c l => if h : c ∈ a.support then ⟨f c l, hf c h l⟩ else 0
  let g' : κ → ∀ l : Arr D, thetaSub W (arrP t l) := fun c l => if h : c ∈ a.support then ⟨g c l, hg c h l⟩ else 0
  have ef : ∀ c ∈ a.support, ∀ l, ((f' c l : thetaSub W (arrP t l)) : WO (G.pS (arrP t l)) (G.pT (arrP t l)) → ℂ) = f c l :=
    fun c h l => by simp only [f', dif_pos h]
  have eg : ∀ c ∈ a.support, ∀ l, ((g' c l : thetaSub W (arrP t l)) : WO (G.pS (arrP t l)) (G.pT (arrP t l)) → ℂ) = g c l :=
    fun c h l => by simp only [g', dif_pos h]
  have key := GlobalTheory.T.multilinearMap_sum_eq_of_sum_prod_eval_eq (fun l : Arr D => thetaSub W (arrP t l)) (pairML S x y v w) a f' g' (fun z => by
    have := hprod z
    unfold Finsupp.sum at this ⊢
    refine (Finset.sum_congr rfl fun c h => ?_).trans (this.trans (Finset.sum_congr rfl fun c h => ?_))
    · simp only [ef c h]
    · simp only [eg c h])
  unfold Finsupp.sum at key ⊢
  refine (Finset.sum_congr rfl fun c h => ?_).trans (key.trans (Finset.sum_congr rfl fun c h => ?_))
  · change _ = _ * pairVec S (t := t) x y (fun l => ((f' c l : thetaSub W (arrP t l)) : WO (G.pS (arrP t l)) (G.pT (arrP t l)) → ℂ)) v w
    rw [funext (ef c h)]
  · change _ * pairVec S (t := t) x y (fun l => ((g' c l : thetaSub W (arrP t l)) : WO (G.pS (arrP t l)) (G.pT (arrP t l)) → ℂ)) v w = _
    rw [funext (eg c h)]

end GlobalTheory.TopZeroInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairwiseFlatMapBand
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries

namespace GlobalTheory.RowReal

theorem block_bounds {x y : ℚ} {n : ℕ} (h : y ∈ GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block x n) :
    x - ((n : ℚ) - 1) / 2 ≤ y ∧ y ≤ x + ((n : ℚ) - 1) / 2 := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 h
  have hi' : (i : ℚ) + 1 ≤ n := by exact_mod_cast (List.mem_range.1 hi)
  have h0 : (0 : ℚ) ≤ i := by positivity
  constructor <;> linarith

theorem block_pairwise (x : ℚ) (n : ℕ) : (GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block x n).Pairwise (· > ·) := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block
  rw [List.pairwise_map]
  refine List.pairwise_lt_range.imp fun {i j} h => ?_
  have : (i : ℚ) < j := by exact_mod_cast h
  show _ < _
  linarith

theorem pairwise_flatMap_band {n : ℕ} (f : Fin n → List ℚ) (lo hi : Fin n → ℚ)
    (hp : ∀ i, (f i).Pairwise (· > ·)) (hb : ∀ i, ∀ x ∈ f i, lo i ≤ x ∧ x ≤ hi i)
    (hs : ∀ i j : Fin n, i < j → hi j < lo i) : ((List.finRange n).flatMap f).Pairwise (· > ·) := by
  rw [List.pairwise_flatMap]
  refine ⟨fun i _ => hp i, (List.pairwise_lt_finRange n).imp fun {i j} hij x hx y hy => ?_⟩
  linarith [(hb i x hx).1, (hb j y hy).2, hs i j hij]

theorem rowEntries_good (D : D7) (C : ℝ) (τ : D.what₂.Tau) : (rowEntries D C τ).Good := by
  set G := num D C τ with hG
  set P := rowEntries D C τ with hPdef
  have hGm : G.m = D.R.m := rfl
  have hGk : G.k = D.R.k := rfl
  have hGs : G.s = sLen D := rfl
  have hGt : G.t = D.R.t := rfl
  have hGg : G.ga = gap D C := rfl
  have hSm : (rowSizes D).m = D.R.m := rfl
  have hSk : (rowSizes D).k = D.R.k := rfl
  have hSs : (rowSizes D).s = sLen D := rfl
  have hSt : (rowSizes D).t = D.R.t := rfl
  have hPa : ∀ l, P.a l = G.a l := fun _ => rfl
  have hPc : ∀ i, P.c i = G.cen (i + 1) := fun _ => rfl
  have hPv : ∀ i, P.v i = G.v (i + 2) := fun _ => rfl
  have hPu : ∀ i, P.u i = G.vHalf (i + 2) := fun _ => rfl
  have hPb : ∀ j, P.b j = G.b (j + 1) := fun _ => rfl
  have hPe : ∀ j, P.e j = G.e (j + 1) := fun _ => rfl
  have hm2 := D.R.two_le_m
  have hk3 := D.R.m_add_three_le_k
  have hgap : sLen D + 2 < gap D C := by have := (isLeast_gap D C).1.2.1; omega
  have hgQ : (sLen D : ℚ) + 2 < G.ga := by rw [hGg]; exact_mod_cast hgap
  have ht1 : (1 : ℚ) ≤ D.R.t := by exact_mod_cast D.R.t_odd.pos
  have hle : ∀ {i j : ℕ}, i ≤ j → G.a j ≤ G.a i := fun h => by
    rcases h.eq_or_lt with rfl | h
    · exact le_rfl
    · linarith [a_add_le (G := G) h]
  have hcen : ∀ i : ℕ, 1 ≤ i → i ≤ D.R.m → |(G.cen i : ℚ) - (G.a i + G.ga / 2)| ≤ 1 := fun i h1 h2 => by
    rw [← G.mid_eq h1]; exact num_nearMid D C τ i (Finset.mem_Icc.2 ⟨h1, h2⟩)
  have hC : ∀ i : ℕ, 1 ≤ i → i ≤ D.R.m → ∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block (G.cen i : ℚ) (sLen D),
      G.a i + G.ga / 2 - ((sLen D : ℚ) + 1) / 2 ≤ x ∧ x ≤ G.a i + G.ga / 2 + ((sLen D : ℚ) + 1) / 2 := by
    intro i h1 h2 x hx
    have e1 := block_bounds hx
    have e2 := abs_le.1 (hcen i h1 h2)
    constructor <;> linarith [e1.1, e1.2, e2.1, e2.2]
  have hspec := GlobalTheory.SignedHC.GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D C) (cen D C τ)
  have hbe : ∀ j (h : j < D.R.m), ((D.R.t : ℚ) + 3) / 2 ≤ G.e (j + 1) - G.b (j + 1) := fun j h => by
    have := (D.hc τ).gap_be ⟨j, h⟩
    rw [hspec.2.1 ⟨j, h⟩, hspec.2.2 ⟨j, h⟩] at this
    exact this
  have heb : ∀ j (h : j + 1 < D.R.m), ((D.R.t : ℚ) + 3) / 2 ≤ G.b (j + 2) - G.e (j + 1) := fun j h => by
    have := (D.hc τ).gap_eb ⟨j, by omega⟩ h
    rw [hspec.2.1 ⟨j + 1, h⟩, hspec.2.2 ⟨j, by omega⟩] at this
    exact this
  have hvle : ∀ i j, 2 ≤ i → i ≤ j → j ≤ D.R.k → G.v j ≤ G.v i := fun i j h1 h2 h3 => by
    rcases h2.eq_or_lt with rfl | h
    · exact le_rfl
    · exact (G.v_anti i j h1 h h3).le
  have hble : ∀ i j, 1 ≤ i → i ≤ j → j ≤ D.R.m → G.b i ≤ G.b j := fun i j h1 h2 h3 => by
    rcases h2.eq_or_lt with rfl | h
    · exact le_rfl
    · exact (G.b_mono i j h1 h h3).le
  have hvk : (-(G.b 1 : ℚ)) < G.v D.R.k - 1 / 2 := by
    have h1 := (D.hc τ).v_gt_u ⟨D.R.k - 2, by omega⟩
    have h2 := (D.hc τ).u_last_gt (by omega) (by omega)
    have h3 : -(D.hc τ).b ⟨0, by omega⟩ < (D.hc τ).v ⟨D.R.k - 2, by omega⟩ := by
      refine h2.trans (lt_of_eq_of_lt ?_ h1)
      congr 1
      ext
      simp only
      omega
    rw [hspec.2.1 ⟨0, by omega⟩, hspec.1 ⟨D.R.k - 2, by omega⟩] at h3
    have h4 : -(G.b 1) < G.v D.R.k := by
      rw [show D.R.k - 2 + 2 = D.R.k by omega] at h3
      exact_mod_cast h3
    have h5 : ((-(G.b 1) + 1 : ℤ) : ℚ) ≤ G.v D.R.k := by exact_mod_cast h4
    push_cast at h5
    linarith
  refine ⟨fun l => ⟨G.v 2 + ((G.m : ℤ) + 1 - ((l : ℕ) : ℤ)) * G.ga, ?_⟩, fun i => ⟨G.v (i + 2) - 1, ?_⟩, ?_⟩
  · rw [hPa]; unfold GlobalTheory.SignedHC.GridData.a; push_cast; ring
  · rw [hPu]; unfold GlobalTheory.SignedHC.GridData.vHalf; push_cast; ring

  have bX : ∀ (i : Fin (rowSizes D).m), ∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block (P.c i) (rowSizes D).s ++ [P.a i.succ],
      G.a (i + 1) ≤ x ∧ x ≤ G.a (i + 1) + G.ga / 2 + ((sLen D : ℚ) + 1) / 2 := by
    intro i x hx
    have hi := i.2
    rw [List.mem_append, List.mem_singleton, hPc, hPa, hSs, Fin.val_succ] at hx
    rcases hx with hx | rfl
    · have := hC (i + 1) (by omega) (by omega) x hx
      constructor <;> linarith [this.1, this.2]
    · constructor
      · exact le_rfl
      · have : (0 : ℚ) ≤ G.ga := by positivity
        linarith
  have pX : (P.a 0 :: (List.finRange (rowSizes D).m).flatMap fun i =>
      GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block (P.c i) (rowSizes D).s ++ [P.a i.succ]).Pairwise (· > ·) := by
    rw [List.pairwise_cons]
    constructor
    · intro x hx
      obtain ⟨i, -, hx⟩ := List.mem_flatMap.1 hx
      have h1 := (bX i x hx).2
      have h2 := a_add_le (G := G) (show 0 < (i : ℕ) + 1 by omega)
      rw [hPa]
      show x < G.a 0
      linarith
    · refine pairwise_flatMap_band _ (fun i => G.a (i + 1)) (fun i => G.a (i + 1) + G.ga / 2 + ((sLen D : ℚ) + 1) / 2)
        (fun i => ?_) bX (fun i j hij => ?_)
      · rw [List.pairwise_append]
        refine ⟨block_pairwise _ _, List.pairwise_singleton _ _, fun x hx y hy => ?_⟩
        rw [List.mem_singleton] at hy
        subst hy
        rw [hPc, hSs] at hx
        have := hC (i + 1) (by omega) (by omega) x hx
        rw [hPa, Fin.val_succ]
        show _ < _
        linarith [this.1]
      · have h := a_add_le (G := G) (show (i : ℕ) + 1 < j + 1 by have : (i : ℕ) < j := hij; omega)
        show _ < _
        linarith
  have tX : ∀ x ∈ (P.a 0 :: (List.finRange (rowSizes D).m).flatMap fun i =>
      GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block (P.c i) (rowSizes D).s ++ [P.a i.succ]), G.a G.m ≤ x := by
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · rw [hPa]; exact hle (by simp)
    · obtain ⟨i, -, hx⟩ := List.mem_flatMap.1 hx
      have := i.2
      exact (hle (show (i : ℕ) + 1 ≤ G.m by rw [hGm]; omega)).trans (bX i x hx).1

  have bY : ∀ (i : Fin ((rowSizes D).k - 1)), ∀ y ∈ [(P.v i : ℚ), P.u i],
      (G.v (i + 2) : ℚ) - 1 / 2 ≤ y ∧ y ≤ G.v (i + 2) := by
    intro i y hy
    rw [hPv, hPu] at hy
    unfold GlobalTheory.SignedHC.GridData.vHalf at hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl <;> constructor <;> linarith
  have pY : ((List.finRange ((rowSizes D).k - 1)).flatMap fun i => [(P.v i : ℚ), P.u i]).Pairwise (· > ·) := by
    refine pairwise_flatMap_band _ (fun i => (G.v (i + 2) : ℚ) - 1 / 2) (fun i => (G.v (i + 2) : ℚ)) (fun i => ?_) bY
      (fun i j hij => ?_)
    · refine List.Pairwise.cons (fun y hy => ?_) (List.pairwise_singleton _ _)
      rw [List.mem_singleton] at hy
      subst hy
      rw [hPv, hPu]
      unfold GlobalTheory.SignedHC.GridData.vHalf
      show _ < _
      linarith
    · have hj : (j : ℕ) < D.R.k - 1 := j.2
      have hij' : (i : ℕ) < j := hij
      have h := G.v_anti (i + 2) (j + 2) (by omega) (by omega) (by rw [hGk]; omega)
      have h' : ((G.v (j + 2) + 1 : ℤ) : ℚ) ≤ G.v (i + 2) := by exact_mod_cast h
      push_cast at h'
      show _ < _
      linarith
  have tY : ∀ y ∈ ((List.finRange ((rowSizes D).k - 1)).flatMap fun i => [(P.v i : ℚ), P.u i]),
      (G.v D.R.k : ℚ) - 1 / 2 ≤ y ∧ y ≤ G.v 2 := by
    intro y hy
    obtain ⟨i, -, hy⟩ := List.mem_flatMap.1 hy
    have hi : (i : ℕ) < D.R.k - 1 := i.2
    have h1 : ((G.v D.R.k : ℤ) : ℚ) ≤ G.v (i + 2) := by exact_mod_cast hvle (i + 2) D.R.k (by omega) (by omega) le_rfl
    have h2 : ((G.v (i + 2) : ℤ) : ℚ) ≤ G.v 2 := by exact_mod_cast hvle 2 (i + 2) le_rfl (by omega) (by omega)
    have := bY i y hy
    constructor <;> linarith [this.1, this.2]

  have bZ : ∀ (j : Fin (rowSizes D).m), ∀ z ∈ ((-P.b j : ℚ) :: GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block (-P.e j) (rowSizes D).t),
      -(G.e (j + 1) : ℚ) - ((D.R.t : ℚ) - 1) / 2 ≤ z ∧ z ≤ -(G.b (j + 1) : ℚ) := by
    intro j z hz
    have hj : (j : ℕ) < D.R.m := j.2
    have h1 := hbe j hj
    rw [List.mem_cons, hPb, hPe, hSt] at hz
    rcases hz with rfl | hz
    · constructor <;> linarith
    · have := block_bounds hz
      constructor <;> linarith [this.1, this.2]
  have pZ : ((List.finRange (rowSizes D).m).flatMap fun j =>
      (-P.b j : ℚ) :: GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block (-P.e j) (rowSizes D).t).Pairwise (· > ·) := by
    refine pairwise_flatMap_band _ (fun j => -(G.e (j + 1) : ℚ) - ((D.R.t : ℚ) - 1) / 2) (fun j => -(G.b (j + 1) : ℚ))
      (fun j => ?_) bZ (fun i j hij => ?_)
    · have hj : (j : ℕ) < D.R.m := j.2
      have h1 := hbe j hj
      rw [List.pairwise_cons]
      refine ⟨fun z hz => ?_, block_pairwise _ _⟩
      rw [hPb, hPe, hSt] at *
      have := block_bounds hz
      show _ < _
      linarith [this.2]
    · have hj : (j : ℕ) < D.R.m := j.2
      have hij' : (i : ℕ) < j := hij
      have h1 := heb i (by omega)
      have h2 : ((G.b (i + 2) : ℤ) : ℚ) ≤ G.b (j + 1) := by exact_mod_cast hble (i + 2) (j + 1) (by omega) (by omega) (by omega)
      show _ < _
      linarith
  have tZ : ∀ z ∈ ((List.finRange (rowSizes D).m).flatMap fun j =>
      (-P.b j : ℚ) :: GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block (-P.e j) (rowSizes D).t), z ≤ -(G.b 1 : ℚ) := by
    intro z hz
    obtain ⟨j, -, hz⟩ := List.mem_flatMap.1 hz
    have hj : (j : ℕ) < D.R.m := j.2
    have h1 : ((G.b 1 : ℤ) : ℚ) ≤ G.b (j + 1) := by exact_mod_cast hble 1 (j + 1) le_rfl (by omega) (by omega)
    linarith [(bZ j z hz).2]

  have hv2 : (G.v 2 : ℚ) < G.a G.m := by
    rw [G.a_m]
    have : (0 : ℚ) ≤ G.ga := by positivity
    linarith
  show (Entries.orderList P).Pairwise (· > ·)
  rw [Entries.orderList, List.pairwise_append, List.pairwise_append]
  refine ⟨⟨pX, pY, fun x hx y hy => ?_⟩, pZ, fun x hx z hz => ?_⟩
  · have h1 := tX x hx
    have h2 := (tY y hy).2
    show _ < _
    linarith
  · have h3 := tZ z hz
    show _ < _
    rcases List.mem_append.1 hx with hx | hx
    · have h1 := tX x hx
      have h2 := tY _ (List.mem_flatMap.2 ⟨⟨0, by rw [hSk]; omega⟩, List.mem_finRange _, List.mem_cons_self⟩)
      linarith [h2.1, h2.2]
    · have h1 := (tY x hx).1
      linarith

end GlobalTheory.RowReal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlacesDistinctTranslationsDerivativesCommute
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

namespace GlobalTheory.PlaceComm

theorem place_comm : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D),
    IsInfFam (D := D) θ → ∀ τ τ' : D.what₂.Tau, τ ≠ τ' →
    (∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ'), ∀ f : GA D V → ℂ,
      rTr V (atTau θ V τ g) (rTr V (atTau θ V τ' h) f) = rTr V (atTau θ V τ' h) (rTr V (atTau θ V τ g) f)) ∧
    (∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ X ∈ lieAt V τ', ∀ f : GA D V → ℂ,
      Rder θ V τ' X (rTr V (atTau θ V τ g) f) = rTr V (atTau θ V τ g) (Rder θ V τ' X f)) ∧
    (∀ X ∈ lieAt V τ, ∀ Y ∈ lieAt V τ', ∀ f : GA D V → ℂ, IsAutFunSm θ V f →
      Rder θ V τ X (Rder θ V τ' Y f) = Rder θ V τ' Y (Rder θ V τ X f)) := by
  intro D θ V hθ τ τ' hne
  refine ⟨fun g hg h hh f => ?_, fun g hg X hX f => ?_, fun X hX Y hY f hf => ?_⟩
  · funext x
    simp only [rTr]
    rw [mul_assoc, mul_assoc, GlobalTheory.AvgOtherPlace.atTau_comm hθ (Ne.symm hne) hg hh]
  · rw [GlobalTheory.Mem.RealTranslate.Rder_rTr hθ (GlobalTheory.Mem.RealTranslate.isRealPt_atTau hθ τ hg) hX,
      GlobalTheory.AvgOtherPlace.adAt_atTau_of_ne hθ (Ne.symm hne) hg]
  · exact GlobalTheory.DerBracket.Rder_comm hθ hf.smooth hne hX hY

end GlobalTheory.PlaceComm

end
end

