import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0512
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0563
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0743
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0775
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0131
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0496
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0776
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0533
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0777
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0257
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0078
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1163
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstColumnVectorSumFormula
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FirstRowDatum

private theorem prod_apply_update_eq_mul_prod_erase {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type}
    (F : ∀ i, X i → ℂ) (x : ∀ i, X i) (j : ι) (y : X j) :
    ∏ i, F i (Function.update x j y i) = F j y * ∏ i ∈ Finset.univ.erase j, F i (x i) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
  simp only [Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

private theorem sum_prod_ite_map_eq_zero_of_sum_prod_eq_zero {ι κ : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type}
    (Tm : ∀ i, (X i → ℂ) →ₗ[ℂ] (X i → ℂ)) (S : Finset κ) (c : κ → ℂ) (Φ : κ → ∀ i, X i → ℂ)
    (h : ∀ x : ∀ i, X i, ∑ d ∈ S, c d * ∏ i, Φ d i (x i) = 0) (s : Finset ι) :
    ∀ x : ∀ i, X i, ∑ d ∈ S, c d * ∏ i, (if i ∈ s then Tm i (Φ d i) else Φ d i) (x i) = 0 := by
  induction s using Finset.induction_on with
  | empty => simpa using h
  | insert j s hj ih =>
    intro x

    have hg : (∑ d ∈ S, (c d * ∏ i ∈ Finset.univ.erase j,
        (if i ∈ s then Tm i (Φ d i) else Φ d i) (x i)) • Φ d j) = 0 := by
      funext y
      rw [Finset.sum_apply, Pi.zero_apply, ← ih (Function.update x j y)]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [prod_apply_update_eq_mul_prod_erase (fun i => if i ∈ s then Tm i (Φ d i) else Φ d i) x j y]
      simp only [Pi.smul_apply, smul_eq_mul, if_neg hj]
      ring

    have hT := congrArg (fun g => Tm j g (x j)) hg
    simp only [map_sum, map_smul, map_zero, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hT
    rw [← hT]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
    have h2 : ∏ i ∈ Finset.univ.erase j, (if i ∈ insert j s then Tm i (Φ d i) else Φ d i) (x i) =
        ∏ i ∈ Finset.univ.erase j, (if i ∈ s then Tm i (Φ d i) else Φ d i) (x i) := by
      refine Finset.prod_congr rfl fun i hi => ?_
      have hij : i ≠ j := Finset.ne_of_mem_erase hi
      simp only [Finset.mem_insert, hij, false_or]
    rw [h2, if_pos (Finset.mem_insert_self j s)]
    ring

theorem sum_prod_map_eq_zero {ι κ : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type}
    (Tm : ∀ i, (X i → ℂ) →ₗ[ℂ] (X i → ℂ)) (S : Finset κ) (c : κ → ℂ) (Φ : κ → ∀ i, X i → ℂ)
    (h : ∀ x : ∀ i, X i, ∑ d ∈ S, c d * ∏ i, Φ d i (x i) = 0) (x : ∀ i, X i) :
    ∑ d ∈ S, c d * ∏ i, Tm i (Φ d i) (x i) = 0 := by
  have := sum_prod_ite_map_eq_zero_of_sum_prod_eq_zero Tm S c Φ h Finset.univ x
  simpa using this

theorem sum_prod_map_eq_zero₂ {κ : Type} {m : ℕ} {X Y : Fin m → Type} (TX : ∀ j, (X j → ℂ) →ₗ[ℂ] (X j → ℂ))
    (TY : ∀ i, (Y i → ℂ) →ₗ[ℂ] (Y i → ℂ)) (S : Finset κ) (c : κ → ℂ) (Φ : κ → ∀ j, X j → ℂ) (Ψ : κ → ∀ i, Y i → ℂ)
    (h : ∀ (x : ∀ j, X j) (y : ∀ i, Y i), ∑ d ∈ S, c d * (∏ j, Φ d j (x j)) * ∏ i, Ψ d i (y i) = 0)
    (x : ∀ j, X j) (y : ∀ i, Y i) :
    ∑ d ∈ S, c d * (∏ j, TX j (Φ d j) (x j)) * ∏ i, TY i (Ψ d i) (y i) = 0 := by

  have hx : ∀ (y : ∀ i, Y i) (x : ∀ j, X j),
      ∑ d ∈ S, (c d * ∏ i, Ψ d i (y i)) * ∏ j, TX j (Φ d j) (x j) = 0 := by
    intro y
    refine sum_prod_map_eq_zero TX S (fun d => c d * ∏ i, Ψ d i (y i)) Φ (fun x => ?_)
    rw [← h x y]
    refine Finset.sum_congr rfl fun d _ => ?_
    ring

  have hy := sum_prod_map_eq_zero TY S (fun d => c d * ∏ j, TX j (Φ d j) (x j)) Ψ (fun y' => by
    rw [← hx y' x]
    exact Finset.sum_congr rfl fun d _ => by ring) y
  rw [← hy]

private theorem mul_sum_prod_map_eq_of_sum_prod_eq {κ : Type} {m : ℕ} {X Y : Fin m → Type} (TX : ∀ j, (X j → ℂ) →ₗ[ℂ] (X j → ℂ))
    (TY : ∀ i, (Y i → ℂ) →ₗ[ℂ] (Y i → ℂ)) (S : Finset κ) (c : κ → ℂ) (u : ℂ) (Φ : κ → ∀ j, X j → ℂ)
    (Ψ Ψ' : κ → ∀ i, Y i → ℂ)
    (h : ∀ (x : ∀ j, X j) (y : ∀ i, Y i), u * ∑ d ∈ S, c d * (∏ j, Φ d j (x j)) * ∏ i, Ψ d i (y i) =
      ∑ d ∈ S, c d * (∏ j, Φ d j (x j)) * ∏ i, Ψ' d i (y i))
    (x : ∀ j, X j) (y : ∀ i, Y i) :
    u * ∑ d ∈ S, c d * (∏ j, TX j (Φ d j) (x j)) * ∏ i, TY i (Ψ d i) (y i) =
      ∑ d ∈ S, c d * (∏ j, TX j (Φ d j) (x j)) * ∏ i, TY i (Ψ' d i) (y i) := by

  have key := sum_prod_map_eq_zero₂ TX TY (S.disjSum S) (Sum.elim (fun d => u * c d) fun d => -c d)
    (Sum.elim Φ Φ) (Sum.elim Ψ Ψ') (fun x' y' => by
      rw [Finset.sum_disjSum]
      simp only [Sum.elim_inl, Sum.elim_inr]
      have e1 : ∑ d ∈ S, u * c d * (∏ j, Φ d j (x' j)) * ∏ i, Ψ d i (y' i) =
          u * ∑ d ∈ S, c d * (∏ j, Φ d j (x' j)) * ∏ i, Ψ d i (y' i) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun d _ => by ring
      have e2 : ∑ d ∈ S, -c d * (∏ j, Φ d j (x' j)) * ∏ i, Ψ' d i (y' i) =
          -∑ d ∈ S, c d * (∏ j, Φ d j (x' j)) * ∏ i, Ψ' d i (y' i) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun d _ => by ring
      rw [e1, e2, h x' y', add_neg_cancel]) x y
  rw [Finset.sum_disjSum] at key
  simp only [Sum.elim_inl, Sum.elim_inr] at key
  have e1 : ∑ d ∈ S, u * c d * (∏ j, TX j (Φ d j) (x j)) * ∏ i, TY i (Ψ d i) (y i) =
      u * ∑ d ∈ S, c d * (∏ j, TX j (Φ d j) (x j)) * ∏ i, TY i (Ψ d i) (y i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun d _ => by ring
  have e2 : ∑ d ∈ S, -c d * (∏ j, TX j (Φ d j) (x j)) * ∏ i, TY i (Ψ' d i) (y i) =
      -∑ d ∈ S, c d * (∏ j, TX j (Φ d j) (x j)) * ∏ i, TY i (Ψ' d i) (y i) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun d _ => by ring
  rw [e1, e2, add_neg_eq_zero] at key
  exact key

private theorem apply_update_eq_update_apply {ι : Type} [DecidableEq ι] {X : ι → Type} (Tm : ∀ i, (X i → ℂ) →ₗ[ℂ] (X i → ℂ))
    (F : ∀ i, X i → ℂ) (i₀ : ι) (g : X i₀ → ℂ) (i : ι) :
    Tm i (Function.update F i₀ g i) = Function.update (fun i => Tm i (F i)) i₀ (Tm i₀ g) i := by
  by_cases h : i = i₀
  · subst h
    simp only [Function.update_self]
  · simp only [Function.update_of_ne h]

set_option maxHeartbeats 2000000 in
private theorem vec_law_lemma_5 {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {μ₀ : T} (hL : L.Is μ₀) {t : T} (ht : t ∈ U) {Φ : G.Datum} {β : CosFam G t}
    {τ : PureDat G t →₀ ℂ} (hτ : S.IsExpansion t Φ β τ)
    (hv : ∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i))
    (k : FinPt G (.grid 0 D.R.m)) (hk : finG (G.V (.grid 0 D.R.m)) k ∈ S.levRow t 0 (Nat.zero_le _)) (s : ℂ)
    (hlaw : ∀ c : ℂ, W.om (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)
        (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1)
        (S.Z.vac (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) = c • S.Z.vac (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) →
      ∀ (xs : ∀ j : Fin D.R.m, WO (G.pS (.top t j)) (G.pT (.top t j)))
        (ys : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))),
        s * c * (τ.sum fun d a' => a' * (∏ j, (d.1 j).fn (xs j)) *
          ∏ i, Function.update (fun i => (d.2 i).fn) (GlobalTheory.FirstRowVertex.firstIx D)
            (fun y => (d.2 (GlobalTheory.FirstRowVertex.firstIx D)).fn (actO (G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).1⁻¹ (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).2⁻¹ y)) i (ys i)) =
        τ.sum fun d a' => a' * (∏ j, (d.1 j).fn (xs j)) * ∏ i, (d.2 i).fn (ys i))
    (xs : ∀ j : Fin D.R.m, WO (G.pS (.top t j)) (G.pT (.top t j)))
    (ys : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))) :
    s * (τ.sum fun d c => c * (∏ j, S.Z.vec (d.1 j) (xs j)) *
      ∏ i, Function.update (fun i => S.Z.vec (d.2 i)) (GlobalTheory.FirstRowVertex.firstIx D)
        (GlobalTheory.FirstRowVertex.rowShift0 S k (S.Z.vec (d.2 (GlobalTheory.FirstRowVertex.firstIx D)))) i (ys i)) =
      τ.sum fun d c => c * (∏ j, S.Z.vec (d.1 j) (xs j)) * ∏ i, S.Z.vec (d.2 i) (ys i) := by
  obtain ⟨e, he, hsup, -⟩ := id hτ
  obtain ⟨c, hc, hmod⟩ := GlobalTheory.FirstRowShift.rowShift0_model S hL ht he k hk
  rcases τ.support.eq_empty_or_nonempty with hne | ⟨d₀, hd₀⟩
  · simp only [Finsupp.sum, hne, Finset.sum_empty, mul_zero]

  have hTXe : ∀ j : Fin D.R.m, ∃ Tm : (WO (G.pS (.top t j)) (G.pT (.top t j)) → ℂ) →ₗ[ℂ] (WO (G.pS (.top t j)) (G.pT (.top t j)) → ℂ),
      IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e (GlobalTheory.LastVertexMove.stdLat S (.top t j)) 1 (S.Z.vac (.top t j)) Tm := by
    intro j
    obtain ⟨f, ⟨Tm, hTm⟩, -⟩ := (hv d₀ hd₀).1 j
    rw [((hsup d₀ hd₀).1 j).2.1] at hTm
    exact ⟨Tm, hTm⟩
  have hTYe : ∀ i : Fin D.R.m, ∃ Tm : (WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ) →ₗ[ℂ]
      (WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ),
      IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e (GlobalTheory.LastVertexMove.stdLat S (.chi i D.R.m)) 1 (S.Z.vac (.chi i D.R.m)) Tm := by
    intro i
    obtain ⟨f, ⟨Tm, hTm⟩, -⟩ := (hv d₀ hd₀).2 i
    rw [((hsup d₀ hd₀).2 i).2.1] at hTm
    exact ⟨Tm, hTm⟩
  choose TX hTX using hTXe
  choose TY hTY using hTYe

  have hvx : ∀ d ∈ τ.support, ∀ j, S.Z.vec (d.1 j) = TX j (d.1 j).fn := fun d hd j =>
    GlobalTheory.LastVertexTensor.vec_eq_model S (d.1 j) ((hv d hd).1 j) ((hsup d hd).1 j).2.2 (TX j)
      (by rw [((hsup d hd).1 j).2.1]; exact hTX j)
  have hvy : ∀ d ∈ τ.support, ∀ i, S.Z.vec (d.2 i) = TY i (d.2 i).fn := fun d hd i =>
    GlobalTheory.LastVertexTensor.vec_eq_model S (d.2 i) ((hv d hd).2 i) ((hsup d hd).2 i).2.2 (TY i)
      (by rw [((hsup d hd).2 i).2.1]; exact hTY i)

  have key := mul_sum_prod_map_eq_of_sum_prod_eq TX TY τ.support (fun d => τ d) (s * c) (fun d j => (d.1 j).fn)
    (fun d => Function.update (fun i => (d.2 i).fn) (GlobalTheory.FirstRowVertex.firstIx D)
      (fun y => (d.2 (GlobalTheory.FirstRowVertex.firstIx D)).fn (actO (G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).1⁻¹ (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).2⁻¹ y)))
    (fun d i => (d.2 i).fn) (fun x y => hlaw c hc x y) xs ys

  have hL' : ∀ d ∈ τ.support, τ d * (∏ j, S.Z.vec (d.1 j) (xs j)) *
      ∏ i, Function.update (fun i => S.Z.vec (d.2 i)) (GlobalTheory.FirstRowVertex.firstIx D)
        (GlobalTheory.FirstRowVertex.rowShift0 S k (S.Z.vec (d.2 (GlobalTheory.FirstRowVertex.firstIx D)))) i (ys i) =
      c * (τ d * (∏ j, TX j (d.1 j).fn (xs j)) * ∏ i, TY i (Function.update (fun i => (d.2 i).fn) (GlobalTheory.FirstRowVertex.firstIx D)
      (fun y => (d.2 (GlobalTheory.FirstRowVertex.firstIx D)).fn (actO (G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).1⁻¹ (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).2⁻¹ y)) i) (ys i)) := by
    intro d hd
    have hsb : IsSBHalf e (latO (G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T))
        (G.latS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) : Set _) (G.latT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) : Set _) fun _ => True)
        (d.2 (GlobalTheory.FirstRowVertex.firstIx D)).fn := by
      have h0 := (d.2 (GlobalTheory.FirstRowVertex.firstIx D)).sb
      rw [((hsup d hd).2 (GlobalTheory.FirstRowVertex.firstIx D)).2.1] at h0
      exact h0
    rw [hvy d hd (GlobalTheory.FirstRowVertex.firstIx D), hmod (TY _) (hTY _) _ hsb]
    simp only [hvx d hd, hvy d hd]
    rw [GlobalTheory.FirstRowVertex.prod_update_smul]
    simp only [apply_update_eq_update_apply]
    ring
  have hR' : ∀ d ∈ τ.support, τ d * (∏ j, S.Z.vec (d.1 j) (xs j)) * ∏ i, S.Z.vec (d.2 i) (ys i) =
      τ d * (∏ j, TX j (d.1 j).fn (xs j)) * ∏ i, TY i (d.2 i).fn (ys i) := by
    intro d hd
    simp only [hvx d hd, hvy d hd]
  unfold Finsupp.sum
  rw [Finset.sum_congr rfl hL', Finset.sum_congr rfl hR', ← Finset.mul_sum, ← mul_assoc]
  exact key

theorem main_law : GlobalTheory.FunPr.Hypotheses₂ → SumOKK → Big fun {D} {_Γ} _ _ {_Pl0} {T} {_A} {_Ks} _ _ _ {R} ch =>
    ∀ (t : T) a, ∀ β ∈ ch.S.supp t (ch.Phi a), ∀ τ, ch.S.IsExpansion t (ch.Phi a) β τ →
    ∀ (k : FinPt ch.G (.grid 0 D.R.m)), finG (ch.G.V (.grid 0 D.R.m)) k ∈ ch.S.levRow t 0 (Nat.zero_le _) →
    ∀ (hk : toXf k ∈ (levEnv D.sp.X' R.βX (R.datXt t)).J)
      (xs : ∀ j : Fin D.R.m, WO (ch.G.pS (.top t j)) (ch.G.pT (.top t j)))
      (ys : ∀ i : Fin D.R.m, WO (ch.G.pS (.chi i D.R.m : Pair T)) (ch.G.pT (.chi i D.R.m : Pair T))),
      (((levEnv D.sp.X' R.βX (R.datXt t)).χ ⟨toXf k, hk⟩ : ℂˣ) : ℂ) *
        (τ.sum fun d c => c * (∏ j, ch.S.Z.vec (d.1 j) (xs j)) *
          ∏ i, Function.update (fun i => ch.S.Z.vec (d.2 i)) (GlobalTheory.FirstRowVertex.firstIx D)
            (GlobalTheory.FirstRowVertex.rowShift0 ch.S.toGridChoice k (ch.S.Z.vec (d.2 (GlobalTheory.FirstRowVertex.firstIx D)))) i (ys i)) =
      τ.sum fun d c => c * (∏ j, ch.S.Z.vec (d.1 j) (xs j)) * ∏ i, ch.S.Z.vec (d.2 i) (ys i) := by
  intro hP hS
  obtain ⟨CF0, hB⟩ := GlobalTheory.T.first_row_vertex_weil_value hP hS
  obtain ⟨CF1, hO⟩ := hS
  refine ⟨max CF0 CF1, fun ε CF hCF => ?_⟩
  obtain ⟨x₀, hx⟩ := hB ε CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨x₁, hx1⟩ := hO ε CF (le_trans (le_max_right _ _) hCF)
  refine ⟨max x₀ x₁, ?_⟩
  intro D large₂ hε hxs Γ _ _ Pl0 T A Ks _ _ _ R F hSet ch hch hsc
  have H := hx D large₂ hε (le_trans (le_max_left _ _) hxs) Γ Pl0 T A Ks R F hSet ch hch hsc
  have HO := hx1 D large₂ hε (le_trans (le_max_right _ _) hxs) Γ Pl0 T A Ks R F hSet ch hch hsc
  intro t a β hβ τ hτ k hk hkχ xs ys
  exact vec_law_lemma_5 ch.S.toGridChoice hSet.core.lev (Set.mem_univ t) hτ ((HO t a).vec β τ hτ) k hk _
    (fun c hc => H t a β hβ τ hτ k hk hkχ c hc) xs ys

end GlobalTheory.FirstRowDatum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeThetaLevelThird
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section

namespace GlobalTheory.XArrowCusp

theorem lift_isCuspFun : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i < D.R.m → j ≤ D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.V (i + 1) j).V) (G.V i j).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.X i j).ω h g Φ * φ g) (G.meas t i j).fd (G.meas t i j).ν) → IsCuspFun (G.V (i + 1) j).V (fun h => ∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g Φ * φ g ∂(G.meas t i j).ν) := by
  intro hLC hP D hS G₀ _ _ Pl0 T A Ks _ _ _ R G hRB hG t i j hi hj Φ hΦ φ hφ hint
  refine GlobalTheory.CuspLocApprox.isCuspFun_of_locApprox fun C hC ε hε => ?_
  obtain ⟨n, f, p, F, v, hf, hF, happ⟩ :=
    GlobalTheory.T.negative_theta_level_sixth hLC hP D hS G₀ Pl0 T A Ks R G hRB hG t i j hi hj Φ hΦ φ hφ hint C hC ε hε
  have hX := (hLC D hS G₀ Pl0 T A Ks R G hRB hG).X t i j hi hj
  choose F' hF' hE using fun l => hX (f l) (hf l) (F l) (hF l)
  refine ⟨n, fun l => F' l ((G.X i j).It (p l) (v l)), fun l => ?_, fun x hx => ?_⟩
  · obtain ⟨h1, h2⟩ := GlobalTheory.LowVanishObj.multT_apply_cusp R.θ _ _ _ (F' l) (hF' l) ((G.X i j).It (p l) (v l))
    exact ⟨h1.toIsAutFun.cont, h1.toIsAutFun.left, h2⟩
  · have e : ∑ l, ∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω x g
          (GlobalTheory.Grid.fock R.ψ R.θ true (G.V (i + 1) j) (G.V i j) (f l) (p l)) * F l (v l) g ∂(G.meas t i j).ν =
        ∑ l, F' l ((G.X i j).It (p l) (v l)) x :=
      Finset.sum_congr rfl fun l _ => (hE l (p l) (v l) x).2
    rw [← e]
    exact happ x hx

end GlobalTheory.XArrowCusp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodAlgebraicFixedDegreeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_algebraic_fixed_degree : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∀ dg : D.what₂.Tau →₀ ℕ, ∃ Ω : ℂ, Ω ≠ 0 ∧ ∀ u : WO (GlobalTheory.Grid.neg A) WW, u.map (infPart D) = 0 →
      ∀ k : FVar D WW.rank A.rank →₀ ℕ, Finsupp.mapDomain Prod.fst k = dg →
        IsAlgebraic ℚ (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B
          (heisO W.ψ (GlobalTheory.Grid.neg A) WW u X.vac) (MvPolynomial.monomial k 1) 0 / Ω) := by
  first | exact @GlobalTheory.BotTransJet.jets_div_period_isAlgebraic | exact GlobalTheory.BotTransJet.jets_div_period_isAlgebraic | (intros; apply GlobalTheory.BotTransJet.jets_div_period_isAlgebraic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalMapColumnsMemLatGIffMovedFinitePart
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Datum ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Geo.Tor
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.ColSplit

open GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues GlobalTheory.AdLat
open scoped TensorProduct

variable {D : D7}

theorem finite_part_apply (V W : HSp D) (Y : Matrix (Fin W.rank) (Fin V.rank) D.host.E) (i : Fin W.rank) (j : Fin V.rank) :
    (ratW W V Y - realPt V W Y : WO V W) i j = (pairA D.host.F 0 1) ⊗ₜ[D.host.F] Y i j := by
  change (1 : AF D.host.F) ⊗ₜ[D.host.F] Y i j - (pairA D.host.F 1 0) ⊗ₜ[D.host.F] Y i j = _
  rw [← TensorProduct.sub_tmul]
  congr 1
  exact Prod.ext (sub_self (1 : Ainf D.host.F)) (sub_zero (1 : Af D.host.F))

def rk (V W : HSp D) (s : Fin V.rank → D.host.E) : (Fin W.rank → D.host.E) →+ WO V W where
  toFun c := Matrix.of fun i j => (pairA D.host.F 0 1) ⊗ₜ[D.host.F] (c i * ∑ k, star (s k) * V.gram k j)
  map_zero' := by ext i j; simp
  map_add' y z := by
    ext i j
    simp only [Matrix.of_apply, Matrix.add_apply, Pi.add_apply, add_mul, TensorProduct.tmul_add]

theorem rk_mem (V W : HSp D) (LV : Set (Fin V.rank → D.host.E)) (L : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E))
    (s : Fin V.rank → D.host.E) (hs : s ∈ LV) (c : Fin W.rank → D.host.E)
    (hc : c ∈ Submodule.span (𝓞 D.host.E) {w | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ v ∈ L, w = a • v}) :
    rk V W s c ∈ latO V W LV (L : Set (Fin W.rank → D.host.E)) fun _ => True := by
  have hc' := (GlobalTheory.OneMapRef.FactsLat.isAA_span L c).1 hc
  clear hc
  induction hc' using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, t, ht, rfl⟩ := hx
    exact AddSubgroup.subset_closure ⟨1, fun _ => one_mem _, fun _ h => absurd trivial h, a, ha, s, hs, t, ht, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | neg y _ hy => rw [map_neg]; exact neg_mem hy

def colF (V W : HSp D) (s : Fin V.rank → D.host.E) : WO V W →+ (Fin W.rank → RA D.host.F D.host.E) where
  toFun u := fun m => ∑ n, finPart D (u m n) * ((1 : Af D.host.F) ⊗ₜ[D.host.F] s n)
  map_zero' := by ext m; simp
  map_add' y z := by
    ext m
    simp only [Matrix.add_apply, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem colF_pure (V W : HSp D) (s : Fin V.rank → D.host.E) (α : Af D.host.F)
    (X : Matrix (Fin W.rank) (Fin V.rank) D.host.E) :
    colF V W s (Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] X i j) =
      fun m => α ⊗ₜ[D.host.F] ∑ n, X m n * s n := by
  funext m
  change ∑ n, (α ⊗ₜ[D.host.F] X m n) * ((1 : Af D.host.F) ⊗ₜ[D.host.F] s n) = _
  simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, TensorProduct.tmul_sum]

theorem colF_mem (V W : HSp D) (L : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E))
    (s : Fin V.rank → D.host.E) (hs : s ∈ GlobalTheory.Member.latC V) (u : WO V W)
    (hu : u ∈ latO V W (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) (L : Set (Fin W.rank → D.host.E)) fun _ => True) :
    colF V W s u ∈ hat D.host.F ((Submodule.span (𝓞 D.host.E)
      {w | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ v ∈ L, w = a • v} : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) :
        Set (Fin W.rank → D.host.E)) := by
  induction hu using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨α, hα, -, a, ha, s', hs', t, ht, rfl⟩ := hx
    rw [colF_pure V W s α fun i j => a * t i * ∑ k, star (s' k) * V.gram k j]
    obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1
      (((GlobalTheory.Member.latHat_eq_hat_and_gram D V).2.2.2.2.2.2.2.2.2.2 s).2 hs s' hs')
    refine AddSubgroup.subset_closure ⟨α, hα, a • (r • t), Submodule.subset_span ⟨a, ha, _, L.smul_mem r ht, rfl⟩, ?_⟩
    funext m
    congr 1
    change _ = a * (algebraMap (𝓞 D.host.E) D.host.E r * t m)
    rw [hr]
    simp only [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun k _ => ?_
    change _ = a * (s n * V.gram k n * star (s' k) * t m)
    ring
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | neg y _ hy => rw [map_neg]; exact neg_mem hy

theorem complete (V : HSp D) (b : Matrix (Fin V.rank) (Fin V.rank) D.host.E) (hb : IsONLatBasis V b) (n j : Fin V.rank) :
    ∑ a, b n a * ∑ k, star (b k a) * V.gram k j = if n = j then 1 else 0 := by
  have h1 : (Matrix.of fun a j => ∑ k, star (b k a) * V.gram k j) * b = 1 := by
    ext a a'
    rw [Matrix.one_apply, ← hb.1 a a', Matrix.mul_apply, Finset.sum_comm]
    simp only [Matrix.of_apply, Finset.sum_mul]
  have h3 : b * (Matrix.of fun a j => ∑ k, star (b k a) * V.gram k j) = 1 := mul_eq_one_comm.1 h1
  have h2 := congrFun (congrFun h3 n) j
  rw [Matrix.one_apply, Matrix.mul_apply] at h2
  exact h2

theorem cols_iff_moved (V W : HSp D) (b : Matrix (Fin V.rank) (Fin V.rank) D.host.E) (hb : IsONLatBasis V b) (y : GA D W)
    (Y : Matrix (Fin W.rank) (Fin V.rank) D.host.E) :
    (∀ a, (fun m => ∑ n, Y m n * b n a) ∈ latG W y) ↔
      (ratW W V Y - realPt V W Y : WO V W) ∈ latO V W (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E))
        (Bridge.hLat W (FWT.fin W y) : Set (Fin W.rank → D.host.E)) fun _ => True := by
  have hbm : ∀ a, (fun i => b i a) ∈ GlobalTheory.Member.latC V := fun a => by
    rw [← SetLike.mem_coe, GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq, hb.2]
    exact Submodule.subset_span ⟨a, rfl⟩
  constructor
  · intro h
    have e : (ratW W V Y - realPt V W Y : WO V W) = ∑ a, rk V W (fun i => b i a) fun m => ∑ n, Y m n * b n a := by
      ext i j
      rw [finite_part_apply, Matrix.sum_apply]
      change _ = ∑ a, (pairA D.host.F 0 1) ⊗ₜ[D.host.F] ((∑ n, Y i n * b n a) * ∑ k, star (b k a) * V.gram k j)
      rw [← TensorProduct.tmul_sum]
      congr 1
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      simp only [mul_assoc, ← Finset.mul_sum, complete V b hb, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
    rw [e]
    refine sum_mem fun a _ => rk_mem V W _ _ _ (hbm a) _ ?_
    rw [← GlobalTheory.MovedLat.latG_eq]
    exact h a
  · intro h a
    have h1 := colF_mem V W _ _ (hbm a) _ h
    rw [← GlobalTheory.MovedLat.latG_eq] at h1
    have e : (ratW W V Y - realPt V W Y : WO V W) =
        Matrix.of fun i j => (pairA D.host.F 0 1) ⊗ₜ[D.host.F] Y i j := by
      ext i j; exact finite_part_apply V W Y i j
    rw [e, colF_pure] at h1
    obtain ⟨f1, f2, -⟩ := GlobalTheory.Member.latG_lattice_and_completion D W y
    exact ((hat_rational_points_and_approx D.host.F D.host.E W.rank _ f1 f2).1 _).1 h1

theorem moved_iff (V W : HSp D) (y : GA D W) (u : WO V W) :
    u ∈ (latO V W (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E))
        (Bridge.hLat W (FWT.fin W y) : Set (Fin W.rank → D.host.E)) fun _ => True) ↔
      actO V W 1 y⁻¹ u ∈ latO V W (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E))
        (GlobalTheory.Member.latC W : Set (Fin W.rank → D.host.E)) fun _ => True := by
  have h1 : ∀ z ∈ hat D.host.F (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)),
      Matrix.mulVec (finHom V 1).1 z ∈ hat D.host.F (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) := by
    intro z hz
    rw [map_one, Units.val_one, Matrix.one_mulVec]
    exact hz
  constructor
  · exact GlobalTheory.MovedLat.actO_mem V W 1 y⁻¹ _ _ _ _ h1 (GlobalTheory.MovedLat.bwd W y) u
  · intro h
    have h2 := GlobalTheory.MovedLat.actO_mem V W 1 y _ _ _ _ h1 (GlobalTheory.MovedLat.fwd W y) _ h
    have h3 := GlobalTheory.AdelicLatMove.actO_actO_inv V W 1 y u
    rw [inv_one] at h3
    rwa [h3] at h2

theorem cols_mem_iff : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks),
    R.toLevCh.Is A.μ0 → ∀ (i : Fin D.R.m) (b : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) D.host.E),
    GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsONLatBasis (Vc D i) b → ∀ (y : GA D (Wc D i)) (Yr : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E),
      (∀ a, (fun m => ∑ n, Yr m n * b n a) ∈ latG (Wc D i) y) ↔
        actO (Vc D i) (Wc D i) 1 y⁻¹ (ratW (Wc D i) (Vc D i) Yr - GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) Yr) ∈
          latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hR i b hb y Yr
  have hV := (GlobalTheory.OneMapRef.FactsLat.selfDual_frame_level_one_lattice_eq_standard (hR.βV i)).trans (GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq _).symm
  have hW := (GlobalTheory.OneMapRef.FactsLat.selfDual_frame_level_one_lattice_eq_standard (hR.βW i)).trans (GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq _).symm
  rw [cols_iff_moved _ _ b hb, moved_iff, ← hV, ← hW]

end GlobalTheory.ColSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedPlacesSphericalStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_places_spherical : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' →
    ∃ S₀ : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F), ∀ v, v ∉ S₀ → ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v,
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om' (1, k)) (G.M'.vac v) (G.M'.vac v) := by
  first | exact @GlobalTheory.SphOffFinite.vac_fixed_off_finite | exact GlobalTheory.SphOffFinite.vac_fixed_off_finite | (intros; apply GlobalTheory.SphOffFinite.vac_fixed_off_finite <;> assumption)
end

