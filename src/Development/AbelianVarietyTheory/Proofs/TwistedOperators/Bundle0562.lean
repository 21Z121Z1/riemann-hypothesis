import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0512
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0527
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0543
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0544
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0475
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0517
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealVectorsAllPlacesOfLocalData
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0287

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairFnUpdateLinear
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.RowVertexInv

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem kkV_add (S : GridChoice W U) (p : Pair T) {f f' : WO (G.pS p) (G.pT p) → ℂ}
    (hf : IsThetaFunO W.ψ _ _ f) (hf' : IsThetaFunO W.ψ _ _ f') (a : FinPt G p.small) (b : FinPt G p.big) :
    kkV S p (f + f') a b = kkV S p f a b + kkV S p f' a b :=
  GlobalTheory.TopZeroInv.kkVec_add S p hf hf' a b

theorem kkV_smul (S : GridChoice W U) (p : Pair T) (c : ℂ) (f : WO (G.pS p) (G.pT p) → ℂ)
    (a : FinPt G p.small) (b : FinPt G p.big) :
    kkV S p (c • f) a b = c • kkV S p f a b :=
  GlobalTheory.TopZeroInv.kkVec_smul S p c f a b

theorem colV_congr (S : GridChoice W U) {t : T} {v v' : ∀ a, FactorFn G t a} (h : ∀ j, v (.inl j) = v' (.inl j))
    (x : ∀ j, FinPt G (.top j)) : colV S v x = colV S v' x := by
  have e : (fun j => if h : j < D.R.m then kkV S (.top t j) (v (.inl ⟨j, h⟩)) (x j) (x (j + 1)) else 0) =
      (fun j => if h : j < D.R.m then kkV S (.top t j) (v' (.inl ⟨j, h⟩)) (x j) (x (j + 1)) else 0) := by
    funext j; split_ifs with hj
    · rw [h]
    · rfl
  simp only [colV, e]

theorem rowV_congr (S : GridChoice W U) {t : T} {v v' : ∀ a, FactorFn G t a} (h : ∀ i, v (.inr i) = v' (.inr i))
    (y : ∀ i, FinPt G (.grid i D.R.m)) : rowV S v y = rowV S v' y := by
  have e : (fun i => if h : i < D.R.m then kkV S (.chi i D.R.m) (v (.inr ⟨i, h⟩)) (y i) (y (i + 1)) else 0) =
      (fun i => if h : i < D.R.m then kkV S (.chi i D.R.m) (v' (.inr ⟨i, h⟩)) (y i) (y (i + 1)) else 0) := by
    funext i; split_ifs with hi
    · rw [h]
    · rfl
  simp only [rowV, e]

theorem colK_update (S : GridChoice W U) {t : T} (v : ∀ a, FactorFn G t a) (x : ∀ j, FinPt G (.top j)) (j₀ : Fin D.R.m)
    (F : FactorFn G t (.inl j₀)) :
    (fun j => if h : j < D.R.m then kkV S (.top t j) (Function.update v (.inl j₀) F (.inl ⟨j, h⟩)) (x j) (x (j + 1))
      else 0) =
    Function.update (fun j => if h : j < D.R.m then kkV S (.top t j) (v (.inl ⟨j, h⟩)) (x j) (x (j + 1)) else 0) j₀.1
      (kkV S (.top t j₀.1) F (x j₀.1) (x (j₀.1 + 1))) := by
  funext j
  by_cases hj : j = j₀.1
  · subst hj
    rw [Function.update_self, dif_pos j₀.2]
    show kkV S (.top t j₀.1) (Function.update v (.inl j₀) F (.inl j₀)) _ _ = _
    rw [Function.update_self]
  · rw [Function.update_of_ne hj]
    split_ifs with h
    · rw [Function.update_of_ne]
      intro e; exact hj (congrArg Fin.val (Sum.inl_injective e))
    · rfl

theorem rowK_update (S : GridChoice W U) {t : T} (v : ∀ a, FactorFn G t a) (y : ∀ i, FinPt G (.grid i D.R.m)) (i₀ : Fin D.R.m)
    (F : FactorFn G t (.inr i₀)) :
    (fun i => if h : i < D.R.m then kkV S (.chi i D.R.m) (Function.update v (.inr i₀) F (.inr ⟨i, h⟩)) (y i) (y (i + 1))
      else 0) =
    Function.update (fun i => if h : i < D.R.m then kkV S (.chi i D.R.m) (v (.inr ⟨i, h⟩)) (y i) (y (i + 1)) else 0) i₀.1
      (kkV S (.chi i₀.1 D.R.m) F (y i₀.1) (y (i₀.1 + 1))) := by
  funext i
  by_cases hi : i = i₀.1
  · subst hi
    rw [Function.update_self, dif_pos i₀.2]
    show kkV S (.chi i₀.1 D.R.m) (Function.update v (.inr i₀) F (.inr i₀)) _ _ = _
    rw [Function.update_self]
  · rw [Function.update_of_ne hi]
    split_ifs with h
    · rw [Function.update_of_ne]
      intro e; exact hi (congrArg Fin.val (Sum.inr_injective e))
    · rfl

theorem pairFn_apply (S : GridChoice W U) {t : T} (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m))
    (v : ∀ a, FactorFn G t a) (p : VV ℂ (wt G (.top 0))) (q : VV ℂ (listedWt G (.grid 0 D.R.m))) :
    pairFn S x y v p q =
      brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m)) (colV S v x p) (rowV S v y q) := rfl

theorem pairFn_update_linear : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (v : ∀ a, FactorFn G t a), (∀ a, v a ∈ thetaSub W.ψ (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a))) → ∀ (a : Fin D.R.m ⊕ Fin D.R.m) (f g : FactorFn G t a), f ∈ thetaSub W.ψ (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a)) → g ∈ thetaSub W.ψ (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a)) → pairFn S x y (Function.update v a (f + g)) = pairFn S x y (Function.update v a f) + pairFn S x y (Function.update v a g) ∧ ∀ c : ℂ, pairFn S x y (Function.update v a (c • f)) = c • pairFn S x y (Function.update v a f) := by
  intro D T L sc G W U S t x y v _ a f g hf hg
  rcases a with j₀ | i₀
  · have hr : ∀ F, rowV S (Function.update v (.inl j₀) F) y = rowV S v y := fun F =>
      rowV_congr S (fun i => Function.update_of_ne Sum.inr_ne_inl _ _) y
    have hadd : colV S (Function.update v (.inl j₀) (f + g)) x =
        colV S (Function.update v (.inl j₀) f) x + colV S (Function.update v (.inl j₀) g) x := by
      have h : kkV S (.top t j₀.1) (f + g) (x j₀.1) (x (j₀.1 + 1)) =
          kkV S (.top t j₀.1) f (x j₀.1) (x (j₀.1 + 1)) + kkV S (.top t j₀.1) g (x j₀.1) (x (j₀.1 + 1)) :=
        kkV_add S (.top t j₀.1) hf hg _ _
      rw [colV, colV, colV, colK_update, colK_update, colK_update, h,
        GlobalTheory.chainTo_update_add _ _ _ _ _ j₀.2, LinearMap.add_comp]
    have hsmul : ∀ c : ℂ, colV S (Function.update v (.inl j₀) (c • f)) x = c • colV S (Function.update v (.inl j₀) f) x := by
      intro c
      have h : kkV S (.top t j₀.1) (c • f) (x j₀.1) (x (j₀.1 + 1)) = c • kkV S (.top t j₀.1) f (x j₀.1) (x (j₀.1 + 1)) :=
        kkV_smul S (.top t j₀.1) c f _ _
      rw [colV, colV, colK_update, colK_update, h, GlobalTheory.ChainSmul.chainTo_update_smul _ _ _ _ _ j₀.2,
        LinearMap.smul_comp]
    refine ⟨?_, fun c => ?_⟩
    · ext p q
      rw [LinearMap.add_apply, LinearMap.add_apply, pairFn_apply, pairFn_apply, pairFn_apply, hr, hr, hr, hadd,
        LinearMap.add_apply]
      exact LinearMap.map_add₂ _ _ _ _
    · ext p q
      rw [LinearMap.smul_apply, LinearMap.smul_apply, pairFn_apply, pairFn_apply, hr, hr, hsmul, LinearMap.smul_apply]
      exact LinearMap.map_smul₂ _ _ _ _
  · have hc : ∀ F, colV S (Function.update v (.inr i₀) F) x = colV S v x := fun F =>
      colV_congr S (fun j => Function.update_of_ne Sum.inl_ne_inr _ _) x
    have hadd : rowV S (Function.update v (.inr i₀) (f + g)) y =
        rowV S (Function.update v (.inr i₀) f) y + rowV S (Function.update v (.inr i₀) g) y := by
      have h : kkV S (.chi i₀.1 D.R.m) (f + g) (y i₀.1) (y (i₀.1 + 1)) =
          kkV S (.chi i₀.1 D.R.m) f (y i₀.1) (y (i₀.1 + 1)) + kkV S (.chi i₀.1 D.R.m) g (y i₀.1) (y (i₀.1 + 1)) :=
        kkV_add S (.chi i₀.1 D.R.m) hf hg _ _
      rw [rowV, rowV, rowV, rowK_update, rowK_update, rowK_update, h,
        GlobalTheory.chainTo_update_add _ _ _ _ _ i₀.2, LinearMap.add_comp]
    have hsmul : ∀ c : ℂ, rowV S (Function.update v (.inr i₀) (c • f)) y = c • rowV S (Function.update v (.inr i₀) f) y := by
      intro c
      have h : kkV S (.chi i₀.1 D.R.m) (c • f) (y i₀.1) (y (i₀.1 + 1)) = c • kkV S (.chi i₀.1 D.R.m) f (y i₀.1) (y (i₀.1 + 1)) :=
        kkV_smul S (.chi i₀.1 D.R.m) c f _ _
      rw [rowV, rowV, rowK_update, rowK_update, h, GlobalTheory.ChainSmul.chainTo_update_smul _ _ _ _ _ i₀.2,
        LinearMap.smul_comp]
    refine ⟨?_, fun c => ?_⟩
    · ext p q
      rw [LinearMap.add_apply, LinearMap.add_apply, pairFn_apply, pairFn_apply, pairFn_apply, hc, hc, hc, hadd,
        LinearMap.add_apply]
      exact map_add _ _ _
    · ext p q
      rw [LinearMap.smul_apply, LinearMap.smul_apply, pairFn_apply, pairFn_apply, hc, hc, hsmul, LinearMap.smul_apply]
      exact map_smul _ _ _

end GlobalTheory.RowVertexInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairVEqOfProdFunEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ExpansionInvariance

theorem chainTo_congr_lt {V : ℕ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)]
    {k k' : ∀ j, V j →ₗ[ℂ] V (j + 1)} : ∀ n, (∀ j, j < n → k j = k' j) → chainTo k n = chainTo k' n
  | 0, _ => rfl
  | n + 1, h => by
    show k n ∘ₗ chainTo k n = k' n ∘ₗ chainTo k' n
    rw [h n n.lt_succ_self, chainTo_congr_lt n fun j hj => h j (by omega)]

theorem chainTo_add_at {V : ℕ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)]
    {k₁ k₂ k₃ : ∀ j, V j →ₗ[ℂ] V (j + 1)} (j₀ : ℕ) (h₂ : ∀ j, j ≠ j₀ → k₂ j = k₁ j) (h₃ : ∀ j, j ≠ j₀ → k₃ j = k₁ j)
    (h : k₁ j₀ = k₂ j₀ + k₃ j₀) : ∀ n, j₀ < n → chainTo k₁ n = chainTo k₂ n + chainTo k₃ n
  | 0, hn => absurd hn (Nat.not_lt_zero _)
  | n + 1, hn => by
    show k₁ n ∘ₗ chainTo k₁ n = k₂ n ∘ₗ chainTo k₂ n + k₃ n ∘ₗ chainTo k₃ n
    rcases Nat.lt_succ_iff_lt_or_eq.mp hn with h' | h'
    · rw [chainTo_add_at j₀ h₂ h₃ h n h', h₂ n (by omega), h₃ n (by omega), LinearMap.comp_add]
    · subst h'
      rw [chainTo_congr_lt (k := k₂) (k' := k₁) j₀ (fun j hj => h₂ j (by omega)),
        chainTo_congr_lt (k := k₃) (k' := k₁) j₀ (fun j hj => h₃ j (by omega)), h, LinearMap.add_comp]

theorem chainTo_smul_at {V : ℕ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)]
    {k₁ k₂ : ∀ j, V j →ₗ[ℂ] V (j + 1)} (j₀ : ℕ) (a : ℂ) (h₂ : ∀ j, j ≠ j₀ → k₂ j = k₁ j)
    (h : k₁ j₀ = a • k₂ j₀) : ∀ n, j₀ < n → chainTo k₁ n = a • chainTo k₂ n
  | 0, hn => absurd hn (Nat.not_lt_zero _)
  | n + 1, hn => by
    show k₁ n ∘ₗ chainTo k₁ n = a • (k₂ n ∘ₗ chainTo k₂ n)
    rcases Nat.lt_succ_iff_lt_or_eq.mp hn with h' | h'
    · rw [chainTo_smul_at j₀ a h₂ h n h', h₂ n (by omega), LinearMap.comp_smul]
    · subst h'
      rw [chainTo_congr_lt (k := k₂) (k' := k₁) j₀ (fun j hj => h₂ j (by omega)), h, LinearMap.smul_comp]

theorem jetOp_mul_tab {K : Type} [Field K] {ι : Type} [Fintype ι] {a b : ℕ} (lam : ι → DomWeight a)
    (lam' : ι → DomWeight b) (c : K) (J : (Formalism.L2.Ker.DVar ι a b →₀ ℕ) → K) (n : ι → ℕ) :
    Formalism.L2.Ker.jetOp lam lam' (fun k => c * J k) n = c • Formalism.L2.Ker.jetOp lam lam' J n := by
  have e : Formalism.L2.Ker.jetLin (fun k => c * J k) = c • Formalism.L2.Ker.jetLin J := by
    refine (MvPolynomial.basisMonomials ((ι × Fin b × Fin b) ⊕ Formalism.L2.Ker.DVar ι a b) K).ext fun m => ?_
    simp only [Formalism.L2.Ker.jetLin, LinearMap.smul_apply, Module.Basis.constr_basis, MvPolynomial.smul_monomial,
      smul_eq_mul]
  ext1 P
  simp only [Formalism.L2.Ker.jetOp, Formalism.L2.Ker.jetMap, e, LinearMap.comp_apply, LinearMap.smul_apply, map_smul]

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem kkVec_smul (S : GridChoice W U) (p : Pair T) (a : ℂ) (f : WO (G.pS p) (G.pT p) → ℂ) (x : FinPt G p.small)
    (y : FinPt G p.big) : GlobalTheory.TopZeroInv.kkVec S p (a • f) x y = a • GlobalTheory.TopZeroInv.kkVec S p f x y := by
  have hJ : ∀ x' y', jetTab W S.N.frC p (a • f) x' y' = fun k => a * jetTab W S.N.frC p f x' y' k := by
    intro x' y'
    funext k
    simp only [jetTab, kerFin, fockIn, GlobalTheory.FiniteFock.pureTensorO_smul, GridData.Weil.ker, thetaKO, map_smul,
      Pi.smul_apply, smul_eq_mul]
  unfold GlobalTheory.TopZeroInv.kkVec fockComp
  rw [hJ, jetOp_mul_tab, smul_comm]

def colML (S : GridChoice W U) (t : T) (x : ∀ j, FinPt G (.top j)) :
    MultilinearMap ℂ (fun j : Fin D.R.m => ↥(GlobalTheory.RowVertexInv.thetaSub W.ψ (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T))))
      (VV ℂ (wt G (.top 0)) →ₗ[ℂ] VV ℂ (wt G (.top D.R.m))) where
  toFun cc := colMapV S t (fun j => (cc j : WO _ _ → ℂ)) x
  map_update_add' := by
    intro _ cc j₀ a b
    unfold colMapV
    rw [← LinearMap.add_comp]
    congr 1
    refine chainTo_add_at j₀.1 ?_ ?_ ?_ D.R.m j₀.2
    · intro j hj
      dsimp only
      split_ifs with h
      · have hne : (⟨j, h⟩ : Fin D.R.m) ≠ j₀ := fun e => hj (congrArg Fin.val e)
        simp only [Function.update_of_ne hne]
      · rfl
    · intro j hj
      dsimp only
      split_ifs with h
      · have hne : (⟨j, h⟩ : Fin D.R.m) ≠ j₀ := fun e => hj (congrArg Fin.val e)
        simp only [Function.update_of_ne hne]
      · rfl
    · simp only [dif_pos j₀.2, Fin.eta, Function.update_self, Submodule.coe_add]
      exact GlobalTheory.TopZeroInv.kkVec_add S _ a.2 b.2 _ _
  map_update_smul' := by
    intro _ cc j₀ c a
    unfold colMapV
    rw [← LinearMap.smul_comp]
    congr 1
    refine chainTo_smul_at j₀.1 c ?_ ?_ D.R.m j₀.2
    · intro j hj
      dsimp only
      split_ifs with h
      · have hne : (⟨j, h⟩ : Fin D.R.m) ≠ j₀ := fun e => hj (congrArg Fin.val e)
        simp only [Function.update_of_ne hne]
      · rfl
    · simp only [dif_pos j₀.2, Fin.eta, Function.update_self, Submodule.coe_smul]
      exact kkVec_smul S _ c _ _ _

def rowML (S : GridChoice W U) (t : T) (y : ∀ i, FinPt G (.grid i D.R.m)) :
    MultilinearMap ℂ (fun i : Fin D.R.m => ↥(GlobalTheory.RowVertexInv.thetaSub W.ψ (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))))
      (VV ℂ (listedWt G (.grid 0 D.R.m)) →ₗ[ℂ] VV ℂ (wt G (.grid D.R.m D.R.m))) where
  toFun rr := rowMapV S (fun i => (rr i : WO _ _ → ℂ)) y
  map_update_add' := by
    intro _ rr i₀ a b
    unfold rowMapV
    rw [← LinearMap.add_comp]
    congr 1
    refine chainTo_add_at i₀.1 ?_ ?_ ?_ D.R.m i₀.2
    · intro i hi
      dsimp only
      split_ifs with h
      · have hne : (⟨i, h⟩ : Fin D.R.m) ≠ i₀ := fun e => hi (congrArg Fin.val e)
        simp only [Function.update_of_ne hne]
      · rfl
    · intro i hi
      dsimp only
      split_ifs with h
      · have hne : (⟨i, h⟩ : Fin D.R.m) ≠ i₀ := fun e => hi (congrArg Fin.val e)
        simp only [Function.update_of_ne hne]
      · rfl
    · simp only [dif_pos i₀.2, Fin.eta, Function.update_self, Submodule.coe_add]
      exact GlobalTheory.TopZeroInv.kkVec_add S _ a.2 b.2 _ _
  map_update_smul' := by
    intro _ rr i₀ c a
    unfold rowMapV
    rw [← LinearMap.smul_comp]
    congr 1
    refine chainTo_smul_at i₀.1 c ?_ ?_ D.R.m i₀.2
    · intro i hi
      dsimp only
      split_ifs with h
      · have hne : (⟨i, h⟩ : Fin D.R.m) ≠ i₀ := fun e => hi (congrArg Fin.val e)
        simp only [Function.update_of_ne hne]
      · rfl
    · simp only [dif_pos i₀.2, Fin.eta, Function.update_self, Submodule.coe_smul]
      exact kkVec_smul S _ c _ _ _

def pairRowL (S : GridChoice W U) (t : T) (y : ∀ i, FinPt G (.grid i D.R.m)) (u : VV ℂ (wt G (.top 0)))
    (v : VV ℂ (listedWt G (.grid 0 D.R.m))) :
    (VV ℂ (wt G (.top 0)) →ₗ[ℂ] VV ℂ (wt G (.top D.R.m))) →ₗ[ℂ]
      MultilinearMap ℂ (fun i : Fin D.R.m => ↥(GlobalTheory.RowVertexInv.thetaSub W.ψ (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)))) ℂ where
  toFun A := ((brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m)) (A u)).comp
    (LinearMap.applyₗ v)).compMultilinearMap (rowML S t y)
  map_add' A B := by
    ext rr
    simp only [LinearMap.add_apply, map_add, LinearMap.add_comp, MultilinearMap.add_apply]
    rfl
  map_smul' c A := by
    ext rr
    simp only [LinearMap.smul_apply, map_smul, LinearMap.smul_comp, MultilinearMap.smul_apply, RingHom.id_apply]
    rfl

def pairML (S : GridChoice W U) (t : T) (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m))
    (u : VV ℂ (wt G (.top 0))) (v : VV ℂ (listedWt G (.grid 0 D.R.m))) :
    MultilinearMap ℂ (fun j : Fin D.R.m => ↥(GlobalTheory.RowVertexInv.thetaSub W.ψ (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T))))
      (MultilinearMap ℂ (fun i : Fin D.R.m => ↥(GlobalTheory.RowVertexInv.thetaSub W.ψ (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)))) ℂ) :=
  (pairRowL S t y u v).compMultilinearMap (colML S t x)

theorem pairML_apply (S : GridChoice W U) (t : T) (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m))
    (u : VV ℂ (wt G (.top 0))) (v : VV ℂ (listedWt G (.grid 0 D.R.m))) (cc rr) :
    pairML S t x y u v cc rr = (brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m))).compl₁₂
      (colMapV S t (fun j => (cc j : WO _ _ → ℂ)) x) (rowMapV S (fun i => (rr i : WO _ _ → ℂ)) y) u v := rfl

theorem pairV_eq_of_prodFun_eq : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) (t : T)
    {δ : Type} (τ : δ →₀ ℂ) (c c' : δ → ∀ j : Fin D.R.m, WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) → ℂ)
    (r r' : δ → ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ),
    (∀ d ∈ τ.support, ∀ j : Fin D.R.m, IsThetaFunO W.ψ (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) (c d j) ∧
      IsThetaFunO W.ψ (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) (c' d j)) →
    (∀ d ∈ τ.support, ∀ i : Fin D.R.m, IsThetaFunO W.ψ (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) (r d i) ∧
      IsThetaFunO W.ψ (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) (r' d i)) →
    (∀ (w : ∀ j : Fin D.R.m, WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)))
      (z : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))),
      (τ.sum fun d a => a * (∏ j, c d j (w j)) * ∏ i, r d i (z i)) = τ.sum fun d a => a * (∏ j, c' d j (w j)) * ∏ i, r' d i (z i)) →
    ∀ x y, pairV S t τ c r x y = pairV S t τ c' r' x y := by
  intro D T L sc G W U S t δ τ c c' r r' hc hr hprod x y
  classical
  refine LinearMap.ext fun u => LinearMap.ext fun v => ?_
  let f : δ → ∀ j : Fin D.R.m, ↥(GlobalTheory.RowVertexInv.thetaSub W.ψ (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T))) :=
    fun d j => if h : d ∈ τ.support then ⟨c d j, (hc d h j).1⟩ else 0
  let f' : δ → ∀ j : Fin D.R.m, ↥(GlobalTheory.RowVertexInv.thetaSub W.ψ (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T))) :=
    fun d j => if h : d ∈ τ.support then ⟨c' d j, (hc d h j).2⟩ else 0
  let g : δ → ∀ i : Fin D.R.m, ↥(GlobalTheory.RowVertexInv.thetaSub W.ψ (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))) :=
    fun d i => if h : d ∈ τ.support then ⟨r d i, (hr d h i).1⟩ else 0
  let g' : δ → ∀ i : Fin D.R.m, ↥(GlobalTheory.RowVertexInv.thetaSub W.ψ (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))) :=
    fun d i => if h : d ∈ τ.support then ⟨r' d i, (hr d h i).2⟩ else 0
  have ef : ∀ d ∈ τ.support, (fun j => (f d j : WO _ _ → ℂ)) = c d := fun d hd => funext fun j => by simp only [f, dif_pos hd]
  have ef' : ∀ d ∈ τ.support, (fun j => (f' d j : WO _ _ → ℂ)) = c' d := fun d hd => funext fun j => by simp only [f', dif_pos hd]
  have eg : ∀ d ∈ τ.support, (fun i => (g d i : WO _ _ → ℂ)) = r d := fun d hd => funext fun i => by simp only [g, dif_pos hd]
  have eg' : ∀ d ∈ τ.support, (fun i => (g' d i : WO _ _ → ℂ)) = r' d := fun d hd => funext fun i => by simp only [g', dif_pos hd]
  have key := GlobalTheory.funProd_multilinear_sum_eq (pairML S t x y u v) τ f f' g g' (fun w z => by
    rw [Finsupp.sum, Finsupp.sum]
    have h1 := hprod w z
    rw [Finsupp.sum, Finsupp.sum] at h1
    refine (Finset.sum_congr rfl fun d hd => ?_).trans (h1.trans (Finset.sum_congr rfl fun d hd => ?_))
    · rw [← ef d hd, ← eg d hd]
    · rw [← ef' d hd, ← eg' d hd])
  have hL : ∀ (cc : δ → ∀ j : Fin D.R.m, WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) → ℂ)
      (rr : δ → ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ)
      (F : δ → ∀ j : Fin D.R.m, ↥(GlobalTheory.RowVertexInv.thetaSub W.ψ (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T))))
      (H : δ → ∀ i : Fin D.R.m, ↥(GlobalTheory.RowVertexInv.thetaSub W.ψ (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)))),
      (∀ d ∈ τ.support, (fun j => (F d j : WO _ _ → ℂ)) = cc d) → (∀ d ∈ τ.support, (fun i => (H d i : WO _ _ → ℂ)) = rr d) →
      pairV S t τ cc rr x y u v = τ.sum fun d a => a * pairML S t x y u v (F d) (H d) := by
    intro cc rr F H hF hH
    unfold pairV
    rw [Finsupp.sum, Finsupp.sum, LinearMap.sum_apply, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, pairML_apply, hF d hd, hH d hd]
  rw [hL c r f g ef eg, hL c' r' f' g' ef' eg']
  exact key

end GlobalTheory.ExpansionInvariance

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PartialColumnFourierMemSchwartzBruhat
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.ColFourier
open scoped Topology

noncomputable section
namespace GlobalTheory.ColFourier

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {A C : Type} [Fintype A] [DecidableEq C]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype A] in

theorem setCols_eq_add_offBlock (P : Finset C) (Y Y' : Matrix A C k) (T : Matrix A P k) :
    setCols P Y' T = setCols P Y T + setCols P (Y' - Y) 0 := by
  ext i j; by_cases h : j ∈ P <;> simp [setCols, h]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype A] in

theorem setCols_of_add (P : Finset C) (Y : Matrix A C k) (x t : (Σ _ : A, P) → k) :
    setCols P Y (Matrix.of fun i j => (x + t) ⟨i, j⟩) =
      setCols P Y (Matrix.of fun i j => x ⟨i, j⟩) + setCols P 0 (Matrix.of fun i j => t ⟨i, j⟩) := by
  ext i j; by_cases h : j ∈ P <;> simp [setCols, h]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [Fintype A] in
theorem continuous_setCols_left (P : Finset C) (T : Matrix A P k) :
    Continuous fun Y : Matrix A C k => setCols P Y T := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  by_cases h : j ∈ P
  · simp only [setCols, of_apply, dif_pos h]; exact continuous_const
  · simp only [setCols, of_apply, dif_neg h]
    exact continuous_id.matrix_elem i j

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [Fintype A] in
theorem continuous_setCols_pair (P : Finset C) :
    Continuous fun q : Matrix A C k × ((Σ _ : A, P) → k) =>
      setCols P q.1 (Matrix.of fun i j => q.2 ⟨i, j⟩) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  by_cases h : j ∈ P
  · simp only [setCols, of_apply, dif_pos h]
    exact (continuous_apply (⟨i, ⟨j, h⟩⟩ : (Σ _ : A, P))).comp continuous_snd
  · simp only [setCols, of_apply, dif_neg h]
    exact continuous_fst.matrix_elem i j

omit [DecidableEq C] in
theorem continuous_pairCols_pair (P : Finset C) :
    Continuous fun q : Matrix A C k × Matrix A P k => pairCols P q.1 q.2 := by
  unfold pairCols
  refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
  exact (continuous_snd.matrix_elem i j).mul (continuous_fst.matrix_elem i (j : C))

end GlobalTheory.ColFourier

theorem GlobalTheory.ColFourier.fourierInt_mem_SB : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (A C : Type) [Fintype A] [DecidableEq A] [DecidableEq C] (ψ : AddChar k Circle) (m : Measure k), HasConductor ψ 1 → IsUnitVol m → ∀ (P : Finset C), ∀ Ξ ∈ SB (Matrix A C k), fourierInt ψ m P Ξ ∈ SB (Matrix A C k) := by
  intro k _ _ _ _ _ _ A C _ _ _ ψ m hψ hm P Ξ hΞ
  haveI := secondCountable k
  haveI := t2Space k
  haveI := hm.1
  have hinv := GlobalTheory.LocFlat.PartialFourier.eventually_add_invariant hΞ
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).mpr fun Y => ?_, ?_⟩
  · have hK : IsCompact (restrictCols P '' tsupport Ξ) := hΞ.2.image (continuous_restrictCols P)
    have h1 : ∀ᶠ Y' in 𝓝 Y, ∀ X, Ξ (X + setCols P (Y' - Y) 0) = Ξ X := by
      have hc : Continuous (fun Y' : Matrix A C k => setCols P (Y' - Y) 0) :=
        (continuous_setCols_left P 0).comp (continuous_id.sub continuous_const)
      have h0 : setCols P (Y - Y) (0 : Matrix A P k) = 0 := by
        ext i j; by_cases h : j ∈ P <;> simp [setCols, h]
      have ht : Filter.Tendsto (fun Y' : Matrix A C k => setCols P (Y' - Y) 0) (𝓝 Y) (𝓝 0) := by
        convert hc.tendsto Y using 2
        exact h0.symm
      exact ht.eventually hinv
    have h2 : ∀ᶠ Y' in 𝓝 Y, ∀ T ∈ restrictCols P '' tsupport Ξ,
        ψ (pairCols P Y' T) = ψ (pairCols P Y T) := by
      refine hK.eventually_forall_of_forall_eventually fun T _ => ?_
      have h3 : IsLocallyConstant fun q : Matrix A C k × Matrix A P k =>
          (ψ (pairCols P q.1 q.2), ψ (pairCols P Y q.2)) :=
        (hψ.isLocallyConstant.comp_continuous (continuous_pairCols_pair P)).prodMk
          (hψ.isLocallyConstant.comp_continuous
            ((continuous_pairCols_pair P).comp (continuous_const.prodMk continuous_snd)))
      filter_upwards [h3.eventually_eq (Y, T)] with q hq
      simp only [Prod.mk.injEq] at hq
      rw [hq.1, hq.2]
    filter_upwards [h1, h2] with Y' hY1 hY2
    unfold fourierInt
    congr 1
    funext T
    rw [setCols_eq_add_offBlock P Y Y' T, hY1]
    by_cases hT : setCols P Y T ∈ tsupport Ξ
    · rw [hY2 T ⟨_, hT, restrictCols_setCols P Y T⟩]
    · simp [image_eq_zero_of_notMem_tsupport hT]
  · have hc : Continuous fun t : (Σ _ : A, P) → k =>
        setCols P (0 : Matrix A C k) (Matrix.of fun i j => t ⟨i, j⟩) :=
      (continuous_setCols_pair P).comp (continuous_const.prodMk continuous_id)
    have h0 : setCols P (0 : Matrix A C k) (Matrix.of fun i j => (0 : (Σ _ : A, P) → k) ⟨i, j⟩) = 0 := by
      ext i j; by_cases h : j ∈ P <;> simp [setCols, h]
    have hU : {Z : Matrix A C k | ∀ X, Ξ (X + Z) = Ξ X} ∈
        𝓝 (setCols P (0 : Matrix A C k) (Matrix.of fun i j => (0 : (Σ _ : A, P) → k) ⟨i, j⟩)) := by
      rw [h0]; exact hinv
    obtain ⟨s, hs⟩ := FourierPi.exists_box_subset (hc.continuousAt.preimage_mem_nhds hU)
    refine HasCompactSupport.intro ((hΞ.2.prod (FourierPi.isCompact_box (1 * s⁻¹))).image
      (continuous_setCols_pair P)) fun Y hY => ?_
    rw [fourierInt_eq_pi]
    by_cases hy : (fun p : (Σ _ : A, P) => Y p.1 p.2) ∈ FourierPi.box (Σ _ : A, P) (1 * s⁻¹)
    · refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun x => ?_)
      have hback : setCols P (setCols P Y (Matrix.of fun i j => x ⟨i, j⟩))
          (Matrix.of fun i j => (fun p : (Σ _ : A, P) => Y p.1 p.2) ⟨i, j⟩) = Y := by
        ext i j; by_cases h : j ∈ P <;> simp [setCols, h]
      have hX : setCols P Y (Matrix.of fun i j => x ⟨i, j⟩) ∉ tsupport Ξ := fun hX =>
        hY ⟨(_, fun p => Y p.1 p.2), ⟨hX, hy⟩, hback⟩
      simp [image_eq_zero_of_notMem_tsupport hX]
    · refine FourierPi.fourier_eq_zero_pi (Measure.pi fun _ : (Σ _ : A, P) => m) hψ (s := s)
        (f := fun x => Ξ (setCols P Y (Matrix.of fun i j => x ⟨i, j⟩))) (fun t ht x => ?_) hy
      show Ξ (setCols P Y (Matrix.of fun i j => (x + t) ⟨i, j⟩)) = Ξ (setCols P Y (Matrix.of fun i j => x ⟨i, j⟩))
      rw [setCols_of_add]
      exact hs ht _
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealVectorsAllPlacesOfLocalDataStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realVectors_allPlaces_of_localData : ∀ {D : D7} (θ : InfFam D), IsInfFam θ → ∀ {Y V : HSp D} (d : HermitianOrthogonalExtensionData Y V 1 1) {S S' : D.what₂.Tau → SPar}
  (M₀ : DSModel Y S') (M : DSModel V S) (q : ℝ) (εA : D.what₂.Tau → Fin Y.rank → Bool)
  (A : D.what₂.Tau → Matrix (Fin Y.rank) (Fin Y.rank) ℂ) (εB : D.what₂.Tau → Fin V.rank → Bool)
  (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (v₀ : ∀ τ, M.H τ) (g₀ : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
  (w : ∀ τ, M₀.H τ) (c : D.what₂.Tau → ℂ),
  (∀ τ, GlobalTheory.PackLoc.LocOK θ d M₀ M τ q (εA τ) (A τ) (εB τ) (B τ) (v₀ τ) (g₀ τ) (w τ) (c τ)) →
    ∃ p : Pack M₀ M, p.Is θ d (Fintype.card D.what₂.Tau * q) := by
  first | exact @GlobalTheory.PackGlob.pack_of_loc | exact GlobalTheory.PackGlob.pack_of_loc | (intros; apply GlobalTheory.PackGlob.pack_of_loc <;> assumption)
end

