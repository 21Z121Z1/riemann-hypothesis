import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0546
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0564
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1155
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0101
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0114
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0407
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0132
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1729
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0155
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1699
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0636
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0479
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0117
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0125
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0150
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0118
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0708
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0301
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianSkewModelGood
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0174
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjUInvMemGfC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0706
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0353
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2011
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0709
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsVEqOne
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0505
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0711
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalLocalUniqueness
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0710
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1163

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GivenLevelInner
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.LastVertexInv GlobalTheory.LastVertexMove
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.LastRowLat

open GlobalTheory.FinPl (Moves Lat)
open Matrix

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

variable (G) in

theorem givenLevel_inner (t : T) (w : Pl D.host.E) : ∀ X : ℕ × ℕ, 1 ≤ X.1 → 1 ≤ X.2 →
    givenLevel G t w X = GlobalTheory.SplitWeil.KO (Kw w) _
  | (_ + 1, _ + 1), _, _ => rfl
  | (0, _), h, _ => absurd h (by omega)
  | (_ + 1, 0), _, h => absurd h (by omega)

theorem inBasis_KO {n n' : ℕ} (h : n' = n) (β x : GL (Fin n) (Lev.EAf D)) (w : Pl D.host.E)
    (K : Subgroup (GL (Fin n') (Kw w))) (hK : K = GlobalTheory.SplitWeil.KO (Kw w) (Fin n')) (hx : inBasis h β w x ∈ K) :
    inBasis rfl β w x ∈ GlobalTheory.SplitWeil.KO (Kw w) (Fin n) := by
  subst h; subst hK; exact hx

theorem isFrame_grid (S : GridChoice W U) : ∀ {i : ℕ}, 1 ≤ i → i ≤ D.R.m → IsFrame (S.B.β i D.R.m) (G.Λ (.grid i D.R.m))
  | 0, h, _ => absurd h (by omega)
  | i + 1, _, hi => S.B.isFrame (i + 1) D.R.m (by omega) hi le_rfl

theorem isSelfDual_grid : ∀ {i : ℕ}, 1 ≤ i → i ≤ D.R.m → IsSelfDualC (G.V (.grid i D.R.m)) (G.Λ (.grid i D.R.m))
  | 0, h, _ => absurd h (by omega)
  | i + 1, _, hi => (G.sp.V_is (i + 1) D.R.m (by omega) hi le_rfl).sd

theorem levRow_mem_St (S : GridChoice W U) (t : T) (k : FinPt G (.grid D.R.m D.R.m))
    (hk : finG (G.V (.grid D.R.m D.R.m)) k ∈ S.levRow t D.R.m le_rfl) :
    finG (G.V (.grid D.R.m D.R.m)) k ∈ St (S.B.β D.R.m D.R.m) := by
  have hm : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
  have hfr := isFrame_grid S hm le_rfl
  have hsd := isSelfDual_grid (G := G) hm le_rfl
  have hU : finG (G.V (.grid D.R.m D.R.m)) k ∈ UA D.sp.cm (G.V (.grid D.R.m D.R.m)).gram := GlobalTheory.LevSplit.finE_mem_UA _ _
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hk
  have hP : ∀ w0 ∈ locPl G t, inBasis rfl (S.B.β D.R.m D.R.m) w0 (finG (G.V (.grid D.R.m D.R.m)) k) ∈ GlobalTheory.SplitWeil.KO (Kw w0) _ := fun w0 hw0 =>
    inBasis_KO _ _ _ _ _ (givenLevel_inner G t w0 (D.R.m, D.R.m) hm hm) (Subgroup.mem_iInf.1 h1 ⟨w0, hw0⟩)
  refine GlobalTheory.Adopt.mem_latticeStabilizer_of_local_integral_inBasis _ _ fun w => ?_
  by_cases hw : ∃ w0 ∈ locPl G t, w.under (𝓞 D.host.F) = w0.under (𝓞 D.host.F)
  · obtain ⟨w0, hw0, e⟩ := hw
    rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq e with rfl | rfl
    · exact hP w hw0
    · exact GlobalTheory.T.unitaryInBasis_integral_at_conjugatePlace _ _ _ hfr (GlobalTheory.AdIsom.dualL_eq hsd) _ hU w0 (hP w0 hw0)
  · push_neg at hw
    exact Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h2 w) hw

theorem hat_stab_of_St {n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (β M : GL (Fin n) (Lev.EAf D))
    (hβ : IsFrame β Λ) (hM : M ∈ St β) (z : Fin n → Lev.EAf D) :
    z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ ↔ M.val *ᵥ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
  refine ⟨GlobalTheory.LatStab.mulVec_mem_of_mem_St Λ β M hβ hM z, fun h => ?_⟩
  have e : (M⁻¹).val *ᵥ (M.val *ᵥ z) = z := by rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  rw [← e]
  exact GlobalTheory.LatStab.mulVec_mem_of_mem_St Λ β M⁻¹ hβ (inv_mem hM) _ h

theorem hat_stab_conj (V : HSp D) (u k : GA D V) (Λ M : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hu : ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) M ↔ (Lev.finE V u).val *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ)
    (hk : ∀ z, z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ ↔ (Lev.finE V k).val *ᵥ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ)
    (v : Fin V.rank → Lev.EAf D) :
    v ∈ Formalism.L2.Herm.hatL (F := D.host.F) M ↔
      (Lev.finE V (u⁻¹ * k * u)).val *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) M := by
  have e : (Lev.finE V u).val *ᵥ ((Lev.finE V (u⁻¹ * k * u)).val *ᵥ v) =
      (Lev.finE V k).val *ᵥ ((Lev.finE V u).val *ᵥ v) := by
    rw [map_mul, map_mul, map_inv, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul]
    congr 2
    group
  refine (hu v).trans ((hk _).trans ?_)
  rw [← e]
  exact (hu _).symm

theorem moves_of_hat (V : HSp D) (g : GA D V) (Λ : Lat V)
    (h : ∀ z, z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ ↔ (Lev.finE V g).val *ᵥ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) :
    Moves V g Λ Λ (fun _ => True) := by
  intro y hy
  have hy' : ∀ i, (Formalism.L2.Theta.mt V g *ᵥ y) i ∈ GlobalTheory.FinPl.idAt D (fun _ => True) :=
    GlobalTheory.Core.Mi.FrameMove.mulVec_mem_ideal _ hy
  constructor
  · intro h1
    refine GlobalTheory.HatLatV.mem_latV_of_hatL D V Λ _ _ hy' ?_
    rw [GlobalTheory.Core.Mi.FrameMove.finE_mulVec_hat]
    exact (h _).1 (GlobalTheory.LatVHat.latV_mem_hatL D V Λ _ y h1)
  · intro h1
    refine GlobalTheory.HatLatV.mem_latV_of_hatL D V Λ _ _ hy ?_
    have h2 := GlobalTheory.LatVHat.latV_mem_hatL D V Λ _ _ h1
    rw [GlobalTheory.Core.Mi.FrameMove.finE_mulVec_hat] at h2
    exact (h _).2 h2

theorem moves_neg (V : HSp D) (g : GA D V) (Λ : Lat V) {P : GlobalTheory.FinPl.Pl D → Prop} (h : Moves V g Λ Λ P) :
    Moves (negSp V) (negGA V g) Λ Λ P := h

theorem moves_cast (S : GridChoice W U) : ∀ (i : ℕ) (e : D.R.m = i) (g : FinPt G (.grid D.R.m D.R.m)),
    Moves (G.V (.grid D.R.m D.R.m)) g.1 (colLat (S.N.fr (.grid D.R.m D.R.m))) (colLat (S.N.fr (.grid D.R.m D.R.m)))
      (fun _ => True) →
    Moves (G.V (.grid i D.R.m)) (e ▸ g : FinPt G (.grid i D.R.m)).1 (colLat (S.N.fr (.grid i D.R.m)))
      (colLat (S.N.fr (.grid i D.R.m))) (fun _ => True) := by
  rintro i rfl g h
  exact h

end GlobalTheory.LastRowLat

namespace GlobalTheory.LastRowLat

open GlobalTheory.FinPl (Moves Lat)
open Matrix

theorem rowPt_mem_stdLat : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T}, t ∈ U → ∀ k : FinPt G (.grid D.R.m D.R.m),
    finG (G.V (.grid D.R.m D.R.m)) k ∈ S.levRow t D.R.m le_rfl →
    ∀ x : WO (G.pS (.chi (lastIx D) D.R.m : Pair T)) (G.pT (.chi (lastIx D) D.R.m : Pair T)),
    actO _ _ (rowPt S k).1⁻¹ (rowPt S k).2⁻¹ x ∈ stdLat S (.chi (lastIx D) D.R.m) ↔ x ∈ stdLat S (.chi (lastIx D) D.R.m) := by
  intro D T L sc G W U S t _ k hk x
  have hm : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
  have hX : DefNode D.R.m (.grid D.R.m D.R.m) := ⟨le_rfl, rfl⟩
  have hk' := hat_stab_of_St _ _ _ (isFrame_grid S hm le_rfl) (levRow_mem_St S t k hk)
  have hg := hat_stab_conj (G.V (.grid D.R.m D.R.m)) (S.N.u (.grid D.R.m D.R.m)).1 k.1 _ _
    (S.N.u_lat _ hX) hk'
  have mv : Moves (G.V (.grid D.R.m D.R.m)) ((S.N.u (.grid D.R.m D.R.m))⁻¹ * k * S.N.u (.grid D.R.m D.R.m)).1
      (colLat (S.N.fr (.grid D.R.m D.R.m))) (colLat (S.N.fr (.grid D.R.m D.R.m))) (fun _ => True) :=
    moves_of_hat _ _ _ hg
  have mv2 := moves_cast S _ (lastIx_succ D) _ mv
  have mvS : Moves (G.pS (.chi (lastIx D) D.R.m : Pair T)) (rowPt S k).1⁻¹ (S.N.latS (.chi (lastIx D) D.R.m))
      (S.N.latS (.chi (lastIx D) D.R.m)) (fun _ => True) :=
    GlobalTheory.VacMove.moves_inv (moves_neg _ _ _ mv2)
  have mvT : Moves (G.pT (.chi (lastIx D) D.R.m : Pair T)) (rowPt S k).2⁻¹ (S.N.latT (.chi (lastIx D) D.R.m))
      (S.N.latT (.chi (lastIx D) D.R.m)) (fun _ => True) := by
    have e2 : (rowPt S k).2 = 1 := rfl
    rw [e2, inv_one]
    intro y _
    rw [GlobalTheory.VacMove.mt_one₀, Matrix.one_mulVec]
  have hl := (lastIx D).2
  have sdS : IsSelfDualC (G.pS (.chi (lastIx D) D.R.m : Pair T)) (S.N.latS (.chi (lastIx D) D.R.m)) :=
    isSelfDualC_neg (OrthoFrame.isSelfDualC_colLat_of_orthonormal _ _ (S.N.fr_on _ ⟨by omega, rfl⟩))
  have sdT : IsSelfDualC (G.pT (.chi (lastIx D) D.R.m : Pair T)) (S.N.latT (.chi (lastIx D) D.R.m)) :=
    OrthoFrame.isSelfDualC_colLat_of_orthonormal _ _ (S.N.fr_on _ ⟨by omega, rfl⟩)
  exact (GlobalTheory.VacMove.mem_latO_iff_actO sdS sdS sdT sdT mvS mvT x).symm

end GlobalTheory.LastRowLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodPlaceOneCosetOfBesselLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.OneCosetGood

variable {D : D7}

theorem ell_mul {ρ : ℕ} (u : GL (Fin ρ) (AE D)) (hu : u ∈ UX D ρ) (j : Fin ρ) :
    ∑ l, ell D ρ l * u.1 l j = ell D ρ j := by
  have hu' := mem_UX.1 hu
  have hρ : 0 < ρ := Fin.pos j
  set m : Fin ρ := ⟨ρ - 1, by omega⟩ with hmdef
  have hm : m.1 + 1 = ρ := by rw [hmdef]; simp only; omega
  have hne : ∀ b : Fin ρ, b ≠ m → ¬ (b.1 + 1 = ρ) := fun b hb h => hb (Fin.ext (by rw [hmdef]; simp only; omega))
  rw [Finset.sum_eq_single m]
  · rw [show ell D ρ m = 1 from if_pos hm, one_mul]
    by_cases hj : j = m
    · rw [hj, (hu' m m).2, show ell D ρ m = 1 from if_pos hm]
    · have hlt : j < m := by
        rw [Fin.lt_iff_val_lt_val]
        have h1 := j.2
        have h2 : j.1 ≠ m.1 := fun h => hj (Fin.ext h)
        rw [hmdef] at h2 ⊢
        simp only at h2 ⊢
        omega
      rw [(hu' m j).1 hlt, show ell D ρ j = 0 from if_neg (hne j hj)]
  · intro b _ hb
    rw [show ell D ρ b = 0 from if_neg (hne b hb), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem yZero_mul {V₀ : HSp D} {ρ : ℕ} (z : Fin V₀.rank → D.host.E) (u : GL (Fin ρ) (AE D)) (hu : u ∈ UX D ρ) :
    yZero V₀ ρ z ⬝ u.1 = yZero V₀ ρ z := by
  ext k j
  simp only [yZero, zEll, Matrix.neg_mul, Matrix.neg_apply, Matrix.mul_apply, vecMulVec_apply, neg_mul,
    Finset.sum_neg_distrib, neg_inj]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, ell_mul u hu j]

set_option maxHeartbeats 1000000 in

theorem cond_red : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V₀ W W₀ : HSp D) (ρ : ℕ) (dW : HypDec W W₀ ρ) (p : Pieces V₀ W W₀ ρ ρ) (z : Fin V₀.rank → D.host.E) (P : GlobalTheory.FinPl.Pl D → Prop) (r g : GA D W), r ∈ Rgrp W (xZero dW) → Cond dW p (xZero dW) (yZero V₀ ρ z) ψ P (r * g) → Cond dW p (xZero dW) (yZero V₀ ρ z) ψ P g := by
  intro D ψ V₀ W W₀ ρ dW p z P r g hr H
  have hr' : r⁻¹ ∈ Rgrp W (xZero dW) := inv_mem hr
  obtain ⟨u, hu, hru⟩ := hr
  obtain ⟨u', hu', hru'⟩ := hr'
  have hinv : mt W (r * g)⁻¹ = mt W g⁻¹ ⬝ mt W r⁻¹ := by rw [_root_.mul_inv_rev, mt_mul]
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨w, a, ha, hw⟩ := H.pt
    refine ⟨⟨u' * w.1, mul_mem hu' w.2⟩, a, ha, ?_⟩
    have e : mt W (r * g)⁻¹ ⬝ (xZero dW ⬝ w.1.1) = mt W g⁻¹ ⬝ (xZero dW ⬝ (u' * w.1).1) := by
      rw [hinv, Matrix.mul_assoc, ← Matrix.mul_assoc (mt W r⁻¹), hru', Units.val_mul, Matrix.mul_assoc]
    rw [← e]; exact hw
  · intro N hN hup hmem
    have hU := mem_UX.1 (inv_mem hu')
    have h1 : MxAt P ((u'⁻¹).1 ⬝ N) := fun i j => by
      simp only [Matrix.mul_apply]
      exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (hN k j)
    have h2 : ∀ i j, j ≤ i → ((u'⁻¹).1 ⬝ N) i j = 0 := by
      intro i j hij
      simp only [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hk : k < i
      · rw [(hU i k).1 hk, zero_mul]
      · rw [hup k j (le_trans hij (not_lt.1 hk)), mul_zero]
    have h3 : mt W (r * g)⁻¹ ⬝ (xZero dW ⬝ ((u'⁻¹).1 ⬝ N)) = mt W g⁻¹ ⬝ (xZero dW ⬝ N) := by
      rw [hinv, Matrix.mul_assoc, ← Matrix.mul_assoc (mt W r⁻¹), hru']
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (u'.1) ((u'⁻¹).1) N, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
    have h4 : upSum ((u'⁻¹).1 ⬝ N) = upSum N := by
      unfold upSum
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      split_ifs with hj
      · simp only [Matrix.mul_apply]
        rw [Finset.sum_eq_single i]
        · rw [(hU i i).2, one_mul]
        · intro k _ hk
          rcases lt_or_gt_of_ne hk with hk | hk
          · rw [(hU i k).1 hk, zero_mul]
          · rw [hup k j (by rw [Fin.le_iff_val_le_val]; have := Fin.lt_iff_val_lt_val.1 hk; omega), mul_zero]
        · intro h; exact absurd (Finset.mem_univ _) h
      · rfl
    rw [← h4]
    exact H.shift _ h1 h2 (h3 ▸ hmem)
  · intro ξ hξ ξ' hP he
    have e : mt W (r * g) ⬝ dW.incX V₀ ξ = dW.incX V₀ (u.1 ⬝ ξ') := by
      rw [mt_mul, Matrix.mul_assoc, he, HypDec.incX_apply, HypDec.incX_apply, ← Matrix.mul_assoc,
        show mt W r ⬝ dW.jX = dW.jX ⬝ u.1 from hru, Matrix.mul_assoc]
    rw [← H.iso ξ hξ (u.1 ⬝ ξ') hP e]
    congr 1
    rw [GlobalTheory.OrientedHeis.symplO_skew (dW.incX V₀ ξ') (dW.incAdj V₀ _),
      GlobalTheory.OrientedHeis.symplO_skew (dW.incX V₀ (u.1 ⬝ ξ')) (dW.incAdj V₀ _), HypDec.symplO_incX_incAdj,
      HypDec.symplO_incX_incAdj, ← Matrix.mul_assoc, yZero_mul z u hu]

end GlobalTheory.OneCosetGood

namespace GlobalTheory.OneCosetGood

open GlobalTheory.FinPl (Lat idAt intAt grpAt InK)

set_option maxHeartbeats 1000000 in

theorem oneCoset_good : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ ρ) (p : Pieces V₀ W W₀ ρ ρ) (z : Fin V₀.rank → D.host.E) (LV : Lat V) (LV₀ : Lat V₀) (LW : Lat W) (LW₀ : Lat W₀) (v : GlobalTheory.FinPl.Pl D), GoodAt dV dW (xZero dW) ψ LV LV₀ LW LW₀ v → StdAt dV dW p LV LW v → (0 < ρ → ∀ a ∈ idAt D (· = v), dW.incAdj V₀ (a • yZero V₀ ρ z) ∈ latO V₀ W (LV₀ : Set _) (LW : Set _) (· = v) ↔ a ∈ intAt D (· = v)) → ∀ h ∈ grpAt W (· = v), (∀ κ, GlobalTheory.FinPl.InK W LW (· = v) κ → Cond dW p (xZero dW) (yZero V₀ ρ z) ψ (· = v) (h * κ)) → CosetAt W (Rgrp W (xZero dW)) LW v h := by
  intro D ψ hψ V V₀ W W₀ ρ dV dW p z LV LV₀ LW LW₀ v hG hS hlast h hh hC
  obtain ⟨n, hnN, hnG, t, ht, htG, γ, hγ, κ, hκ, rfl⟩ :=
    GlobalTheory.IwaPlace.iwasawa_at_place D W W₀ ρ dW LW LW₀ v (GlobalTheory.FinPl.TamePlaces.tame D v) hG.sdW hG.sdW₀ hG.monoW h hh
  have hR : Rgrp W (xZero dW) = jacGrp dW := (GlobalTheory.Unf.base_point D W W₀ ρ dW).2.2.2.1
  have hr : n * dW.emb0 γ ∈ Rgrp W (xZero dW) := by
    rw [hR]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hnN) (Subgroup.mem_sup_right ⟨γ, rfl⟩)
  have heq : n * dW.levi t * dW.emb0 γ * κ * κ⁻¹ = n * dW.emb0 γ * dW.levi t := by
    rw [mul_inv_cancel_right, mul_assoc n, ← dW.wittHyperbolic_anisotropic_commute_levi, mul_assoc]
  have hc := cond_red D ψ V₀ W W₀ ρ dW p z (· = v) _ _ hr (heq ▸ hC κ⁻¹ (inK_inv hκ))
  have hinv := GlobalTheory.T.goodPlace_pointCondition_torus_inverseDiag_integral D ψ hψ V V₀ W W₀ ρ dV dW p LV LV₀ LW LW₀ v hG hS t ht htG hc.pt
  have hint : ∀ i : Fin ρ, t.1 i i - 1 ∈ intAt D (· = v) := by
    intro i
    by_cases hi : i.1 + 1 < ρ
    · exact GlobalTheory.T.goodPlace_shiftCondition_torus_diag_integral D ψ hψ V V₀ W W₀ ρ dV dW p LV LV₀ LW LW₀ v hG hS t ht htG hc.shift i ⟨i.1 + 1, hi⟩ rfl
    · exact GlobalTheory.T.isotropic_condition_last_torus_diagonal_integral D ψ hψ V V₀ W W₀ ρ dV dW p z LV LV₀ LW LW₀ v hG hS hlast t ht htG hc.iso i (by omega)
  have hK := GlobalTheory.FinPl.LeviUnitK.inK_levi D W W₀ ρ dW LW LW₀ v hG.sdW hG.monoW t ht htG (fun i => ⟨hint i, hinv i⟩)
  refine ⟨n * dW.emb0 γ, hr, ?_, dW.levi t * κ, inK_mul hK hκ, ?_⟩
  · exact Subgroup.mul_mem _ hnG (GlobalTheory.OneCosetEmb.wittCoreEmbedding_mem_unitaryAdelicSupportedSubgroup D W W₀ ρ dW (· = v) γ hγ)
  · rw [mul_assoc n (dW.levi t), ← dW.wittHyperbolic_anisotropic_commute_levi γ t]
    simp only [mul_assoc]

end GlobalTheory.OneCosetGood

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianSkewModelGoodStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_skew_model_good : GlobalTheory.FunPr.Hypotheses₂ → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) {n d : ℕ} {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d}
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) {r s r' s' : ℕ},
    B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ → M.IsWeil B.ψ χX χW om →
    ∀ {Pi : Type} [AddCommGroup Pi] [Module ℂ Pi] (Q : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] Pi) (N : Submodule ℂ Pi),
    (∀ (w : InfinitePlace F) (Z : Matrix (Fin d) (Fin d) ℂ) (γ : Multiplicative ℝ →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J),
      γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ W →
      (∀ t : ℝ, (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (γ (Multiplicative.ofAdd t))).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (B.emb w)) =
        NormedSpace.exp (t • Z)) →
      (∀ (t : ℝ) (w' : InfinitePlace F), w' ≠ w →
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (γ (Multiplicative.ofAdd t))).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (B.emb w')) = 1) →
      ∀ (m : ℕ) (f f₁ : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))
        (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin d → Fv F v) → ℂ),
      (∀ i, (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ ∀ᶠ v in Filter.cofinite, φ i v = M.vac v) →
      (∀ i, f i ∈ M.Pol B.ψ B.emb ∧ f₁ i ∈ M.Pol B.ψ B.emb) →
      (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) (f i) (f₁ i)) →
      Q (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)) ∈ N → Q (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f₁ i) (φ i)) ∈ N) →
    ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ W B.emb, ∀ Ψ ∈ GlobalTheory.SquareAgree.algD M B.ψ B.emb,
      om (1, k) Ψ ∈ GlobalTheory.SquareAgree.algD M B.ψ B.emb ∧ (Q Ψ ∈ N → Q (om (1, k) Ψ) ∈ N) := by
  first | exact @GlobalTheory.KStableSums.kStable_sums | exact GlobalTheory.KStableSums.kStable_sums | (intros; apply GlobalTheory.KStableSums.kStable_sums <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeVacuumCombinationLocalModelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeVacuumCombination_localModel : Big fun ch => LatP ch → CombP ch := by
  first | exact @GlobalTheory.FlatPlace.eventually_combination_of_lattice | exact GlobalTheory.FlatPlace.eventually_combination_of_lattice | (intros; apply GlobalTheory.FlatPlace.eventually_combination_of_lattice <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinearIndependenceFromLifts
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

noncomputable section

namespace GlobalTheory.RowEx

theorem linB (hP : GlobalTheory.FunPr.Hypotheses₂) (hL : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal) : LinB := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hsc hch a u => ?_⟩⟩
  obtain ⟨h1, h2⟩ := GlobalTheory.T.theta_convergence_base_choice hP hL large₂ hS ch hch CF hsc a u
  exact ⟨h1, GlobalTheory.T.besselPeriodCorank_converges_column ch.W ch.M hch.vol ch.ξ _ (col_mem ch a) _ h2⟩

end GlobalTheory.RowEx

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalWeilLinearModelMeasure
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LatVac
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.MixedForm

theorem char_eq_local_any : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (ι : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a) (Fin (a + a')) (Fv F v) → ℂ)), G.M.IsLinW B.ψ t 1 1 ι → ∀ ν₀ : (Fv F v)ˣ →* ℂˣ, (∀ g ∈ UAt σ G.V (evFin F v), ∃ g' : GL (Fin a) (Fv F v), (mat g).map (piW t) = g'.1 ∧
      ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (g, 1)) φ φ₁ → ι φ₁ = GlobalTheory.SplitFlip.omA ν₀ 1 g' 1 (ι φ)) →
    ∃ t' : E →ₐ[F] Fv F v, ν₀ = chrW X.ν t' ∨ ν₀ = (chrW X.ν t')⁻¹ := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT v t ι hι ν₀ hν
  have h := hT.base.cm
  have hJ : IsUnit (G.V.J.map t).det := by
    obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
    have h0 := GlobalTheory.LeviAtPlace.det_ne_zero_of_sig (hT.geo.hV.sig (InfinitePlace.mk φ))
    have h1 : G.V.J.det ≠ 0 := fun e => h0 (by
      rw [show G.V.J.map _ = RingHom.mapMatrix _ G.V.J from rfl, ← RingHom.map_det, e, map_zero])
    rw [show G.V.J.map t = (t : E →+* Fv F v).mapMatrix G.V.J from rfl, ← RingHom.map_det]
    exact isUnit_iff_ne_zero.2 ((map_ne_zero _).2 h1)
  haveI : Nonempty (Fin a) := ⟨⟨0, lt_of_le_of_lt (Nat.zero_le _) hT.geo.lt⟩⟩
  obtain ⟨φ, hφ, hφ0⟩ : ∃ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ι φ 0 ≠ 0 := by
    obtain ⟨Λ, -, f, hf, hne⟩ := GlobalTheory.T.exists_translation_invariant_functional F v a (a + a')
    obtain ⟨Y₀, hY⟩ : ∃ Y₀, f Y₀ ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hne (by rw [show f = 0 from funext hc, map_zero])
    have hf' : (fun Y => f (Y + Y₀)) ∈ SB (Matrix (Fin a) (Fin (a + a')) (Fv F v)) :=
      ⟨hf.1.comp_continuous (continuous_add_const Y₀), hf.2.comp_homeomorph (Homeomorph.addRight Y₀)⟩
    obtain ⟨φ, hφ, e⟩ := hι.bij.surjOn hf'
    exact ⟨φ, hφ, by rw [e]; simpa using hY⟩
  refine ⟨t.comp σ, Or.inr (MonoidHom.ext fun x => ?_)⟩
  obtain ⟨g', rfl⟩ := Matrix.GeneralLinearGroup.det_surjective (n := Fin a) x
  set g := GlobalTheory.LeviAtPlace.leviHom h t G.V.J hJ hT.geo.hV.herm g' with hgdef
  have hg : g ∈ UAt σ G.V (evFin F v) := GlobalTheory.LeviAtPlace.lift_sub_one_at v _
  have g1 : (mat g).map (piW t) = g'.1 := by
    rw [hgdef, GlobalTheory.LeviAtPlace.leviHom_map_piW, GlobalTheory.LeviAtPlace.locMat, GlobalTheory.LeviAtPlace.pairMat_fst]
  have g2 : (((Matrix.GeneralLinearGroup.det g')⁻¹ : (Fv F v)ˣ) : Fv F v) = ((mat g).map (piW (t.comp σ))).det := by
    rw [hgdef, GlobalTheory.LeviAtPlace.leviHom_map_piW, GlobalTheory.LeviAtPlace.locMat, GlobalTheory.LeviAtPlace.pairMat_snd,
      GlobalTheory.LeviAtPlace.conjComp, Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul,
      Matrix.nonsing_inv_mul _ hJ, Matrix.det_one, one_mul, Matrix.det_transpose, ← map_inv]
    rfl
  obtain ⟨g'', e, hact⟩ := hν g hg
  obtain rfl : g' = g'' := Units.ext (g1.symm.trans e)
  obtain ⟨φ₁, ⟨hφ₁, hA⟩, -⟩ := (GlobalTheory.T.theta_action_exists hP F E σ B _ _ _ _ G.M _ _ om _ _ _ _
    (GlobalTheory.ThK.Check.isPair_of_isTriple hT).1 v).1 g hg 1 (fun u _ => by
      rw [show mat (1 : UA σ G.W.J) = 1 from rfl, sub_self, smul_zero]) φ hφ
  have k1 := lin_zero h G.M B.ψ hT.base.std _ _ om hT.weil t ι hι g hg _ g2 φ φ₁ hφ hA
  rw [hact φ hφ φ₁ hφ₁ hA, chrW_div, map_inv, inv_inv] at k1
  have k2 : ((GlobalTheory.SplitWeil.nabs (Fv F v) (Matrix.GeneralLinearGroup.det g')⁻¹ ^ (((a + a' : ℕ) : ℝ) / 2) : ℝ) : ℂ) =
      GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g') (-(Fintype.card (Fin (a + a')) : ℂ) / 2) := by
    rw [neg_div, ← GlobalTheory.SplitFlip.apow_inv, GlobalTheory.SplitFlip.apow,
      Complex.ofReal_cpow (show 0 ≤ GlobalTheory.SplitWeil.nabs _ _ from NNReal.coe_nonneg _), Fintype.card_fin]
    push_cast
    rfl
  rw [k2] at k1
  simp only [GlobalTheory.SplitFlip.omA, map_one, GlobalTheory.SplitFlip.apow_one, MonoidHom.one_apply, Units.val_one, mul_one,
    Matrix.mul_zero, Matrix.zero_mul] at k1
  have k3 := mul_right_cancel₀ (GlobalTheory.SplitFlip.apow_ne_zero _ _) (mul_right_cancel₀ hφ0 k1)
  rw [MonoidHom.inv_apply, ← inv_eq_iff_eq_inv]
  exact Units.ext k3

end GlobalTheory.MixedForm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsLocalIdentityStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matched_maps_local_identity : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf →
    ∀ (T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F), v ∈ T →
    ∀ h ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ G.W (GlobalTheory.AdelicU.evFin F v), ∀ Φ Φ',
    GlobalTheory.ThK.PolynomialMatching.PolMatchOn B G X R Rf T Φ Φ' → GlobalTheory.ThK.PolynomialMatching.PolMatchOn B G X R Rf T (om (1, h) Φ) (om' (1, h) Φ') := by
  first | exact @GlobalTheory.ThK.PolMatchStep.polMatchOn_step | exact GlobalTheory.ThK.PolMatchStep.polMatchOn_step | (intros; apply GlobalTheory.ThK.PolMatchStep.polMatchOn_step <;> assumption)
end

