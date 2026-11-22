import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0512
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0527
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0542
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0181
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0569
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0710
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0759
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0276
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0478
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0395
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0428
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0391
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PsiEOffS0ColumnPair

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumProdExpansionFunctionsRowVertexInvariant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.RowVertexInv
open GlobalTheory.SplitFlip

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

abbrev movPt (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m))
    (z : ∀ a, WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a))) :
    ∀ a, WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a)) :=
  Function.update (Function.update z (.inr ⟨j, by omega⟩)
    (actO _ _ (G.toPair (.chi j D.R.m) 1 (moved S j k))⁻¹.1 (G.toPair (.chi j D.R.m) 1 (moved S j k))⁻¹.2
      (z (.inr ⟨j, by omega⟩)) : WO (G.pS (.chi j D.R.m : Pair T)) (G.pT (.chi j D.R.m : Pair T))))
    (.inr ⟨j + 1, hj⟩) (actO _ _ (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1)⁻¹.1
      (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1)⁻¹.2 (z (.inr ⟨j + 1, hj⟩)) :
      WO (G.pS (.chi (j + 1) D.R.m : Pair T)) (G.pT (.chi (j + 1) D.R.m : Pair T)))

theorem movPt_two (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m))
    (z : ∀ a, WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a))) :
    movPt S j hj k z (.inr ⟨j + 1, hj⟩) = actO _ _ (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1)⁻¹.1
      (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1)⁻¹.2 (z (.inr ⟨j + 1, hj⟩)) :=
  Function.update_self _ _ _

theorem movPt_one (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m))
    (z : ∀ a, WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a))) :
    movPt S j hj k z (.inr ⟨j, by omega⟩) = actO _ _ (G.toPair (.chi j D.R.m) 1 (moved S j k))⁻¹.1
      (G.toPair (.chi j D.R.m) 1 (moved S j k))⁻¹.2 (z (.inr ⟨j, by omega⟩)) :=
  (Function.update_of_ne (by simp) _ _).trans (Function.update_self _ _ _)

theorem movPt_other (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m))
    (z : ∀ a, WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a))) (a : Fin D.R.m ⊕ Fin D.R.m)
    (h1 : a ≠ .inr ⟨j, by omega⟩) (h2 : a ≠ .inr ⟨j + 1, hj⟩) : movPt S j hj k z a = z a :=
  (Function.update_of_ne h2 _ _).trans (Function.update_of_ne h1 _ _)

theorem movFn_two (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m))
    (v : ∀ a, FactorFn G t a) (x : WO (G.pS (.chi (j + 1) D.R.m : Pair T)) (G.pT (.chi (j + 1) D.R.m : Pair T))) :
    movFn S j hj k v (.inr ⟨j + 1, hj⟩) x = v (.inr ⟨j + 1, hj⟩) (actO _ _ (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1)⁻¹.1
      (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1)⁻¹.2 x) := by
  unfold movFn; rw [Function.update_self]

theorem movFn_one (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m))
    (v : ∀ a, FactorFn G t a) (x : WO (G.pS (.chi j D.R.m : Pair T)) (G.pT (.chi j D.R.m : Pair T))) :
    movFn S j hj k v (.inr ⟨j, by omega⟩) x = v (.inr ⟨j, by omega⟩) (actO _ _ (G.toPair (.chi j D.R.m) 1 (moved S j k))⁻¹.1
      (G.toPair (.chi j D.R.m) 1 (moved S j k))⁻¹.2 x) := by
  unfold movFn; rw [Function.update_of_ne (by simp), Function.update_self]

theorem movFn_other (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m))
    (v : ∀ a, FactorFn G t a) (a : Fin D.R.m ⊕ Fin D.R.m)
    (h1 : a ≠ .inr ⟨j, by omega⟩) (h2 : a ≠ .inr ⟨j + 1, hj⟩) : movFn S j hj k v a = v a := by
  unfold movFn; rw [Function.update_of_ne h2, Function.update_of_ne h1]

theorem scale_movFn_apply (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m))
    (c₁ c₂ : ℂ) (v : ∀ a, FactorFn G t a) (z : ∀ a, WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a)))
    (a : Fin D.R.m ⊕ Fin D.R.m) :
    (scaleAt j hj c₁ c₂ a • movFn S j hj k v a) (z a) =
      ((Pi.mulSingle (.inr ⟨j, by omega⟩ : Fin D.R.m ⊕ Fin D.R.m) c₁ : Fin D.R.m ⊕ Fin D.R.m → ℂ) a *
        (Pi.mulSingle (.inr ⟨j + 1, hj⟩ : Fin D.R.m ⊕ Fin D.R.m) c₂ : Fin D.R.m ⊕ Fin D.R.m → ℂ) a) *
        v a (movPt S j hj k z a) := by
  have hne : (.inr ⟨j, by omega⟩ : Fin D.R.m ⊕ Fin D.R.m) ≠ .inr ⟨j + 1, hj⟩ := by simp
  by_cases h2' : a = .inr ⟨j + 1, hj⟩
  · subst h2'
    have e1 : movFn S j hj k v (.inr ⟨j + 1, hj⟩) (z (.inr ⟨j + 1, hj⟩)) =
        v (.inr ⟨j + 1, hj⟩) (movPt S j hj k z (.inr ⟨j + 1, hj⟩)) :=
      (movFn_two S j hj k v (z (.inr ⟨j + 1, hj⟩))).trans (congrArg (v _) (movPt_two S j hj k z).symm)
    rw [Pi.smul_apply, smul_eq_mul, e1]
    simp [scaleAt, Pi.mulSingle_apply, hne.symm]
  · by_cases h1' : a = .inr ⟨j, by omega⟩
    · subst h1'
      have e1 : movFn S j hj k v (.inr ⟨j, by omega⟩) (z (.inr ⟨j, by omega⟩)) =
          v (.inr ⟨j, by omega⟩) (movPt S j hj k z (.inr ⟨j, by omega⟩)) :=
        (movFn_one S j hj k v (z (.inr ⟨j, by omega⟩))).trans (congrArg (v _) (movPt_one S j hj k z).symm)
      rw [Pi.smul_apply, smul_eq_mul, e1]
      simp [scaleAt, Pi.mulSingle_apply, hne, Function.update_of_ne hne]
    · rw [Pi.smul_apply, smul_eq_mul, movFn_other S j hj k v a h1' h2', movPt_other S j hj k z a h1' h2']
      simp [scaleAt, Pi.mulSingle_apply, h1', h2', Function.update_of_ne h1', Function.update_of_ne h2']

end GlobalTheory.RowVertexInv

namespace GlobalTheory.RowVertexInv
open GlobalTheory.SplitFlip

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem prod_scale_movFn (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m))
    (c₁ c₂ : ℂ) (v : ∀ a, FactorFn G t a) (z : ∀ a, WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a))) :
    ∏ a, (scaleAt j hj c₁ c₂ a • movFn S j hj k v a) (z a) = c₁ * c₂ * ∏ a, v a (movPt S j hj k z a) := by
  rw [Finset.prod_congr rfl fun a _ => scale_movFn_apply S j hj k c₁ c₂ v z a, Finset.prod_mul_distrib,
    Finset.prod_mul_distrib, Fintype.prod_pi_mulSingle', Fintype.prod_pi_mulSingle']

theorem isHalf_movPt (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m))
    (z : ∀ a, WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a))) (e : AE D) (a : Fin D.R.m ⊕ Fin D.R.m) :
    IsHalf e (movPt S j hj k z a) ↔ IsHalf e (z a) := by
  by_cases h2' : a = .inr ⟨j + 1, hj⟩
  · subst h2'
    rw [movPt_two]
    exact GlobalTheory.SchrMove.isHalf_actO_iff _ _ _
  · by_cases h1' : a = .inr ⟨j, by omega⟩
    · subst h1'
      rw [movPt_one]
      exact GlobalTheory.SchrMove.isHalf_actO_iff _ _ _
    · rw [movPt_other S j hj k z a h1' h2']

theorem sum_fn_eq_zero {t : T} (τ : PureDat G t →₀ ℂ) (e : AE D)
    (hsupp : ∀ d ∈ τ.support, (∀ j, (d.1 j).P = locPl G t ∧ (d.1 j).e = e ∧ (d.1 j).z = 1) ∧
      ∀ i, (d.2 i).P = locPl G t ∧ (d.2 i).e = e ∧ (d.2 i).z = 1)
    (z : ∀ a, WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a))) (a : Fin D.R.m ⊕ Fin D.R.m)
    (ha : ¬ IsHalf e (z a)) : (τ.sum fun d c => c * ∏ a, fnOf d a (z a)) = 0 := by
  unfold Finsupp.sum
  refine Finset.sum_eq_zero fun d hd => ?_
  beta_reduce
  rw [Finset.prod_eq_zero (Finset.mem_univ a), mul_zero]
  rcases a with j | i
  · by_contra hne
    have h := (d.1 j).sb.1 _ hne
    rw [((hsupp d hd).1 j).2.1] at h
    exact ha h
  · by_contra hne
    have h := (d.2 i).sb.1 _ hne
    rw [((hsupp d hd).2 i).2.1] at h
    exact ha h

theorem sum_fn_of_half (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} (τ : PureDat G t →₀ ℂ) (e : AE D)
    (hexp : ∀ (x : ∀ j : Fin D.R.m, WO (G.V (.top j)) (G.V (.top (j + 1))))
      (y : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))), (∀ j, IsHalf e (x j)) →
      (∀ i, IsHalf e (y i)) → (τ.sum fun d c => c * (∏ j, (d.1 j).fn (x j)) * ∏ i, (d.2 i).fn (y i)) =
        ∏ w, (S.term t Φ β w).datum (S.colAt t w x) (S.rowAt t w y))
    (z : ∀ a, WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a))) (h : ∀ a, IsHalf e (z a)) :
    (τ.sum fun d c => c * ∏ a, fnOf d a (z a)) =
      ∏ w, (S.term t Φ β w).datum (S.colAt t w fun j => z (.inl j)) (S.rowAt t w fun i => z (.inr i)) := by
  rw [← hexp (fun j => z (.inl j)) (fun i => z (.inr i)) (fun j => h _) (fun i => h _)]
  refine Finsupp.sum_congr fun d _ => ?_
  rw [Fintype.prod_sum_type, mul_assoc]
  rfl

end GlobalTheory.RowVertexInv

namespace GlobalTheory.RowVertexInv
open GlobalTheory.SplitFlip

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem inl_movPt (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m))
    (z : ∀ a, WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a))) :
    (fun i => movPt S j hj k z (.inl i)) = fun i => z (.inl i) :=
  funext fun i => movPt_other S j hj k z _ (by simp) (by simp)

theorem inr_movPt (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m))
    (z : ∀ a, WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a))) :
    (fun i => movPt S j hj k z (.inr i)) = Function.update (Function.update (fun i => z (.inr i)) ⟨j, by omega⟩
        (actO _ _ (G.toPair (.chi j D.R.m) 1 (moved S j k))⁻¹.1 (G.toPair (.chi j D.R.m) 1 (moved S j k))⁻¹.2
          (z (.inr ⟨j, by omega⟩)) : WO (G.pS (.chi j D.R.m : Pair T)) (G.pT (.chi j D.R.m : Pair T))))
      ⟨j + 1, hj⟩ (actO _ _ (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1)⁻¹.1
          (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1)⁻¹.2 (z (.inr ⟨j + 1, hj⟩)) :
          WO (G.pS (.chi (j + 1) D.R.m : Pair T)) (G.pT (.chi (j + 1) D.R.m : Pair T))) := by
  funext i
  let B : Fin D.R.m → Type := fun i => WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))
  have hne : (⟨j, by omega⟩ : Fin D.R.m) ≠ ⟨j + 1, hj⟩ := by simp
  by_cases h2' : i = ⟨j + 1, hj⟩
  · subst h2'
    exact (movPt_two S j hj k z).trans (Function.update_self (β := B) (⟨j + 1, hj⟩ : Fin D.R.m) _ _).symm
  · by_cases h1' : i = ⟨j, by omega⟩
    · subst h1'
      exact (movPt_one S j hj k z).trans ((Function.update_of_ne (β := B) hne _ _).trans (Function.update_self (β := B) _ _ _)).symm
    · refine (movPt_other S j hj k z _ (fun h => h1' (Sum.inr_injective h)) (fun h => h2' (Sum.inr_injective h))).trans ?_
      symm
      refine (Function.update_of_ne (β := B) (a := i) h2' _ _).trans ?_
      exact Function.update_of_ne (β := B) (a := i) h1' _ _

theorem local_prod (S : GridChoice W U) {t : T} {Φ : G.Datum} (β : CosFam G t) {μ₀ : T} (hμ : L.Is μ₀)
    (hq : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q))
    (hc : ∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) (hU : t ∈ U) (j : ℕ) (hj : j + 1 < D.R.m)
    (k : FinPt G (.grid (j + 1) D.R.m)) (hk : finG (G.V (.grid (j + 1) D.R.m)) k ∈ S.levRow t (j + 1) hj.le) (c₁ c₂ : ℂ)
    (h1 : W.om (.chi j D.R.m) (G.toPair (.chi j D.R.m) 1 (moved S j k)) (S.Z.vac (.chi j D.R.m)) = c₁ • S.Z.vac (.chi j D.R.m))
    (h2 : W.om (.chi (j + 1) D.R.m) (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1) (S.Z.vac (.chi (j + 1) D.R.m)) =
      c₂ • S.Z.vac (.chi (j + 1) D.R.m))
    (x : ∀ j : Fin D.R.m, WO (G.V (.top j)) (G.V (.top (j + 1))))
    (y : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))) :
    c₁ * c₂ * ∏ w, (S.term t Φ β w).datum (S.colAt t w x) (S.rowAt t w (Function.update (Function.update y ⟨j, by omega⟩
        (actO _ _ (G.toPair (.chi j D.R.m) 1 (moved S j k))⁻¹.1 (G.toPair (.chi j D.R.m) 1 (moved S j k))⁻¹.2
          (y ⟨j, by omega⟩) : WO (G.pS (.chi j D.R.m : Pair T)) (G.pT (.chi j D.R.m : Pair T))))
      ⟨j + 1, hj⟩ (actO _ _ (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1)⁻¹.1
          (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1)⁻¹.2 (y ⟨j + 1, hj⟩) :
          WO (G.pS (.chi (j + 1) D.R.m : Pair T)) (G.pT (.chi (j + 1) D.R.m : Pair T))))) =
      ∏ w, (S.term t Φ β w).datum (S.colAt t w x) (S.rowAt t w y) := by
  have hκ : ∀ w : locPl G t, inBasis (rank_vertex G t w.1 (X := (j + 1, D.R.m)) ⟨hj.le, le_rfl⟩) (S.B.β (j + 1) D.R.m) w.1
      (finG (G.V (.grid (j + 1) D.R.m)) k) ∈ givenLevel G t w.1 (j + 1, D.R.m) := fun w =>
    Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hk).1 w
  rw [GlobalTheory.T.vacuum_scalars_eq_product_edge_factors_row S hμ hU j hj k hk c₁ c₂ h1 h2, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [GlobalTheory.RowMoveAt.rowAt_move S hU j hj k w.1 w.2 y]
  exact GlobalTheory.T.termDatum_rowMove_level_edgeFactors S β hμ hq hc hU w j hj _ (hκ w) _ _

end GlobalTheory.RowVertexInv

namespace GlobalTheory.RowVertexInv

theorem sum_prod_scale_movFn_eq : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T},
    L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → t ∈ U → β ∈ S.supp t Φ → S.IsExpansion t Φ β τ → (∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) → ∀ (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m)), finG (G.V (.grid (j + 1) D.R.m)) k ∈ S.levRow t (j + 1) hj.le → ∀ c₁ c₂ : ℂ, W.om (.chi j D.R.m) (G.toPair (.chi j D.R.m) 1 (moved S j k)) (S.Z.vac (.chi j D.R.m)) = c₁ • S.Z.vac (.chi j D.R.m) → W.om (.chi (j + 1) D.R.m) (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1) (S.Z.vac (.chi (j + 1) D.R.m)) = c₂ • S.Z.vac (.chi (j + 1) D.R.m) → ∀ z : ∀ a, WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a)), (τ.sum fun d c => c * ∏ a, (scaleAt j hj c₁ c₂ a • movFn S j hj k (fnOf d) a) (z a)) = τ.sum fun d c => c * ∏ a, fnOf d a (z a) := by
  intro D T L sc G W U S t Φ β τ μ₀ hμ hq hc hU hβ hE hv j hj k hk c₁ c₂ h1 h2 z
  obtain ⟨e, -, hsupp, hexp⟩ := hE
  have hL : (τ.sum fun d c => c * ∏ a, (scaleAt j hj c₁ c₂ a • movFn S j hj k (fnOf d) a) (z a)) =
      c₁ * c₂ * τ.sum fun d c => c * ∏ a, fnOf d a (movPt S j hj k z a) := by
    rw [Finsupp.mul_sum]
    refine Finsupp.sum_congr fun d _ => ?_
    rw [prod_scale_movFn]
    ring
  rw [hL]
  by_cases hall : ∀ a, IsHalf e (z a)
  · rw [sum_fn_of_half S τ e hexp z hall,
      sum_fn_of_half S τ e hexp _ fun a => (isHalf_movPt S j hj k z e a).2 (hall a), inl_movPt, inr_movPt]
    exact local_prod S β hμ hq hc hU j hj k hk c₁ c₂ h1 h2 (fun i => z (.inl i)) (fun i => z (.inr i))
  · push_neg at hall
    obtain ⟨a, ha⟩ := hall
    rw [sum_fn_eq_zero τ e hsupp z a ha,
      sum_fn_eq_zero τ e hsupp _ a (fun h => ha ((isHalf_movPt S j hj k z e a).1 h)), mul_zero]

end GlobalTheory.RowVertexInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGridPairingBoundMemCompletionOfMapBound
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.CharXFB

noncomputable section
namespace GlobalTheory.CharXFB.PairAt

variable {D : D7}
open GlobalTheory.SeeSaw (idV FI conjFI)

theorem conjFI_modul {T : Type} {L : LevCh D T} (P : GlobalTheory.ChiGrid.Places L) (sc : Consts) :
    conjFI D ((P.modul sc : Ideal (𝓞 D.host.E)) : FI D) = ((P.modulBar sc : Ideal (𝓞 D.host.E)) : FI D) := by
  have h := congrArg (conjFI D) (GlobalTheory.CharXFB.OffPl.conjFI_modulBar P sc)
  rw [GlobalTheory.CharXFB.OffPl.conjFI_conjFI] at h
  exact h.symm

private theorem mul_mem_idAt' {D : D7} {v : GlobalTheory.FinPl.Pl D} {a : AE D} (b : AE D) (ha : a ∈ idAt D (· = v)) :
    a * b ∈ idAt D (· = v) := by
  rw [GlobalTheory.FinPlLoc.mem_idAt_iff] at ha ⊢
  rw [← mul_assoc, ha]

theorem pair_mem_idV_of_maps {S T : HSp D} {ΛS : Lat S} {ΛT : Lat T} (sdT : IsSelfDualC T ΛT) {u : WO S T}
    {v : GlobalTheory.FinPl.Pl D} {yS : Fin S.rank → AE D} {yT : Fin T.rank → AE D} {𝔟S 𝔟T 𝔐 : FI D} (h𝔟S : 𝔟S ≠ 0)
    (h𝔟T : 𝔟T ≠ 0) (h𝔐 : 𝔐 ≠ 0)
    (hu : ∀ y ∈ latV S ΛS (· = v), ∀ s ∈ idV 𝔐 v, s • (u *ᵥ y) ∈ latV T ΛT (· = v))
    (hyS : ∀ t ∈ idV 𝔟S v, t • yS ∈ latV S ΛS (· = v)) (hyT : ∀ r ∈ idV 𝔟T v, r • yT ∈ latV T ΛT (· = v)) :
    GlobalTheory.FinPlLoc.idem D (· = v) * hA T yT (u *ᵥ yS) ∈
      idV (1 * 𝔟T⁻¹ * (conjFI D 𝔐)⁻¹ * (conjFI D 𝔟S)⁻¹) v := by
  have hx : GlobalTheory.FinPlLoc.idem D (· = v) * hA T yT (u *ᵥ yS) ∈ idAt D (· = v) :=
    mul_mem_idAt' _ (GlobalTheory.FinPlLoc.idem_mem_idAt _)
  have cS : conjFI D 𝔟S ≠ 0 := fun h => h𝔟S ((conjFI D).injective (by rw [h, map_zero]))
  have cM : conjFI D 𝔐 ≠ 0 := fun h => h𝔐 ((conjFI D).injective (by rw [h, map_zero]))
  have n1 : (1 : FI D) * 𝔟T⁻¹ ≠ 0 := mul_ne_zero one_ne_zero (inv_ne_zero h𝔟T)
  have n2 : (1 : FI D) * 𝔟T⁻¹ * (conjFI D 𝔐)⁻¹ ≠ 0 := mul_ne_zero n1 (inv_ne_zero cM)
  refine (GlobalTheory.IdealQuot.mul_subset_iff D v (conjFI D 𝔟S) _ cS n2 _ hx).1 ?_
  intro t ht
  refine (GlobalTheory.IdealQuot.mul_subset_iff D v (conjFI D 𝔐) _ cM n1 _ (mul_mem_idAt' t hx)).1 ?_
  intro m hm
  refine (GlobalTheory.IdealQuot.mul_subset_iff D v 𝔟T 1 h𝔟T one_ne_zero _
    (mul_mem_idAt' m (mul_mem_idAt' t hx))).1 ?_
  intro r hr
  rw [GlobalTheory.SeeSaw.idV_one_eq_intAt]
  have ht' : cA D t ∈ idV 𝔟S v := by
    have h := GlobalTheory.SeeSaw.cA_mem_idV ht
    rwa [GlobalTheory.CharXFB.OffPl.conjFI_conjFI] at h
  have hm' : cA D m ∈ idV 𝔐 v := by
    have h := GlobalTheory.SeeSaw.cA_mem_idV hm
    rwa [GlobalTheory.CharXFB.OffPl.conjFI_conjFI] at h
  have hz := GlobalTheory.CharXFB.OffPl.hA_mem_intAt sdT (hyT r hr) (hu _ (hyS _ ht') _ hm')
  have hprod := GlobalTheory.IdealQuot.intAt_mul (GlobalTheory.FinPlLoc.idem_mem_intAt (D := D) (· = v)) hz
  have e : GlobalTheory.FinPlLoc.idem D (· = v) * hA T (r • yT) (cA D m • (u *ᵥ (cA D t • yS))) =
      GlobalTheory.FinPlLoc.idem D (· = v) * hA T yT (u *ᵥ yS) * t * m * r := by
    rw [GlobalTheory.CharXFB.OffPl.hA_smul_left, GlobalTheory.CharXFB.OffPl.hA_smul_right, Matrix.mulVec_smul,
      GlobalTheory.CharXFB.OffPl.hA_smul_right, GlobalTheory.SeeSaw.cA_cA, GlobalTheory.SeeSaw.cA_cA]
    ring
  rw [← e]
  exact hprod

private theorem stairId_ne_zero_twisted_operators {D : D7} {A B : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} (hA : A ≠ 0) (hB : B ≠ 0)
    (c : ℕ) (p : Fin c) : GlobalTheory.ChiGrid.stairId A B c p ≠ 0 := by
  rw [GlobalTheory.ChiGrid.stairId]
  exact mul_ne_zero (pow_ne_zero _ hA) (inv_ne_zero (pow_ne_zero _ hB))

theorem pair_mem_AA_AAbar : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (σ : ℕ) (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m) (u : WO (G.V (.grid (2 * σ + 2 + 1) 0)) (G.V (.grid (2 * σ + 2) 0))) (v : GlobalTheory.FinPl.Pl D), (∀ y ∈ latV (G.V (.grid (2 * σ + 2 + 1) 0)) (G.Λ (.grid (2 * σ + 2 + 1) 0)) (· = v), ∀ s ∈ GlobalTheory.SeeSaw.idV (D.host.AA⁻¹ * ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹) v, s • (u *ᵥ y) ∈ latV (G.V (.grid (2 * σ + 2) 0)) (G.Λ (.grid (2 * σ + 2) 0)) (· = v)) → ∀ p : Fin (σ + 1), GlobalTheory.FinPlLoc.idem D (· = v) * hA _ (ratV fun k => (G.colDec (2 * σ + 2) (by omega) h').a k (Fin.castLE (by omega) p)) (u *ᵥ ratV fun k => (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a k (Fin.castLE (by omega) p : Fin (2 * (σ + 1) + 1 - 1)).rev) ∈ GlobalTheory.SeeSaw.idV (D.host.AA * D.host.AAbar) v := by
  intro D T L sc G σ h h' u v hu p
  have hAA : (D.host.AA : GlobalTheory.SeeSaw.FI D) ≠ 0 := by
    first
      | exact (GlobalTheory.SeeSaw.ChainIdeals.host_ne_zero D).2.1
      | exact Formalism.IndefR.Fin.PDA.AA_ne_zero (D := D)
      | exact GlobalTheory.IndefiniteRowSideFullHecke.TwistCoverDesign.AA_ne_zero D
      | exact GlobalTheory.SeeSaw.LatAt.AA_ne_zero (D := D)
  have hAbar : (D.host.AAbar : GlobalTheory.SeeSaw.FI D) ≠ 0 := fun e =>
    hAA ((conjFI D).injective (by rw [GlobalTheory.SeeSaw.conjFI_AA, e, map_zero]))
  have hm : ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr (G.pl.modul_ne_bot sc)
  have hmB : ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D) ≠ 0 := fun e =>
    hm ((conjFI D).injective (by rw [conjFI_modul G.pl sc, e, map_zero]))
  have hstA : G.pl.stA sc ≠ 0 := by
    rw [GlobalTheory.ChiGrid.Places.stA]
    exact mul_ne_zero hAA (inv_ne_zero hmB)
  have hstAbar : G.pl.stAbar sc ≠ 0 := by
    rw [GlobalTheory.ChiGrid.Places.stAbar]
    exact mul_ne_zero hAbar (inv_ne_zero hm)
  have sdT : IsSelfDualC (G.V (.grid (2 * σ + 2) 0)) (G.Λ (.grid (2 * σ + 2) 0)) :=
    (G.sp.V_is (2 * σ + 2) 0 (by omega) h' (Nat.zero_le _)).sd
  have hyT : ∀ r ∈ GlobalTheory.SeeSaw.idV (GlobalTheory.ChiGrid.stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * σ + 2 - 1)
      (Fin.castLE (by omega) p)) v,
      r • ratV (fun k => (G.colDec (2 * σ + 2) (by omega) h').a k (Fin.castLE (by omega) p)) ∈
        latV (G.V (.grid (2 * σ + 2) 0)) (G.Λ (.grid (2 * σ + 2) 0)) (· = v) := by
    intro r hr
    have hl := GlobalTheory.CharXFB.OffPl.scaled_auxiliary_vector_mem_lattice_completion (G.colDec (2 * σ + 2) (by omega) h') (G.sp.P (2 * σ + 2)).lat _ _ v hr
    rw [show G.Λ (.grid (2 * σ + 2) 0) = _ from G.sp.colLat (2 * σ + 2) (by omega) h']
    exact hl
  have hyS : ∀ t ∈ GlobalTheory.SeeSaw.idV (GlobalTheory.ChiGrid.stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * (σ + 1) + 1 - 1)
      (Fin.castLE (by omega) p : Fin (2 * (σ + 1) + 1 - 1)).rev) v,
      t • ratV (fun k => (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a k
        (Fin.castLE (by omega) p : Fin (2 * (σ + 1) + 1 - 1)).rev) ∈
        latV (G.V (.grid (2 * σ + 2 + 1) 0)) (G.Λ (.grid (2 * σ + 2 + 1) 0)) (· = v) := by
    intro t ht
    have hl := GlobalTheory.CharXFB.OffPl.scaled_auxiliary_vector_mem_lattice_completion (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega))
      (G.sp.P (2 * (σ + 1) + 1)).lat _ _ v ht
    rw [show G.Λ (.grid (2 * σ + 2 + 1) 0) = _ from G.sp.colLat (2 * (σ + 1) + 1) (by omega) (by omega)]
    exact hl
  have key := pair_mem_idV_of_maps (ΛS := G.Λ (.grid (2 * σ + 2 + 1) 0)) sdT (u := u) (v := v)
    (stairId_ne_zero_twisted_operators hstA hstAbar _ _) (stairId_ne_zero_twisted_operators hstA hstAbar _ _)
    (mul_ne_zero (inv_ne_zero hAA) (inv_ne_zero hm)) hu hyS hyT
  have hcM : conjFI D (D.host.AA⁻¹ * ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹) =
      D.host.AAbar⁻¹ * ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹ := by
    rw [map_mul, map_inv₀, map_inv₀, GlobalTheory.SeeSaw.conjFI_AA, conjFI_modul]
  have hst := GlobalTheory.CharXFB.OffPl.stair_prod hstA hstAbar (GlobalTheory.CharXFB.OffPl.conjFI_stA G.pl sc)
    (GlobalTheory.CharXFB.OffPl.conjFI_stAbar G.pl sc) σ p (by omega) (by omega)
  have hid : ∀ X Y : GlobalTheory.SeeSaw.FI D, 1 * X⁻¹ * (D.host.AAbar⁻¹)⁻¹ * Y⁻¹ = D.host.AAbar * G.pl.stA sc →
      1 * X⁻¹ * (D.host.AAbar⁻¹ * ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹)⁻¹ * Y⁻¹ =
        D.host.AA * D.host.AAbar := by
    intro X Y hXY
    rw [mul_inv, inv_inv (((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D))]
    calc 1 * X⁻¹ * ((D.host.AAbar⁻¹)⁻¹ * ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)) * Y⁻¹
        = (1 * X⁻¹ * (D.host.AAbar⁻¹)⁻¹ * Y⁻¹) * ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D) := by
          ring
      _ = D.host.AAbar * (D.host.AA * ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹) *
          ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D) := by
          rw [hXY, GlobalTheory.ChiGrid.Places.stA]
      _ = D.host.AA * D.host.AAbar * (((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹ *
          ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)) := by ring
      _ = D.host.AA * D.host.AAbar := by rw [inv_mul_cancel₀ hmB, mul_one]
  rw [hcM] at key
  rw [← hid _ _ hst]
  exact key

end GlobalTheory.CharXFB.PairAt
end
end

