import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsVEqOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatTensorPureTensorEqProdContr
import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0674
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0037
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0677
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0428
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0390
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0407
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0106
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0575
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMatrixOfIsLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AuxiliaryVectorDecompositionEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0102
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0670
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAllTiedPerTied
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0500
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0511
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0671
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0296

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatTensorPureTensorEqProdLocalFactors
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

namespace GlobalTheory.FlatPlace

open GlobalTheory.SplitFlip (Grid Edge)

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]

theorem flCol_datC_congr (ψ : AddChar k Circle) (ν : Measure k) {a b N N' : ℕ} (Φ : Matrix (Fin N) (Fin N') k → ℂ)
    {c₁ c₂ p₁ p₂ : ℕ} (hc : c₁ = c₂) (hp : p₁ = p₂) (h₁ : a + c₁ = N') (h₁' : b + (c₁ + 1) = N) (h₂ : a + c₂ = N')
    (h₂' : b + (c₂ + 1) = N) :
    GlobalTheory.LocFlat.flCol ψ ν p₁ (datC h₁ h₁' Φ) = GlobalTheory.LocFlat.flCol ψ ν p₂ (datC h₂ h₂' Φ) := by
  subst hc hp; rfl

theorem flRow_datC_congr (ψ : AddChar k Circle) (ν : Measure k) {a b N N' : ℕ} (Φ : Matrix (Fin N) (Fin N') k → ℂ)
    {c₁ c₂ p₁ p₂ : ℕ} (hc : c₁ = c₂) (hp : p₁ = p₂) (h₁ : a + c₁ = N') (h₁' : b + (c₁ + 1) = N) (h₂ : a + c₂ = N')
    (h₂' : b + (c₂ + 1) = N) :
    GlobalTheory.LocFlat.flRow ψ ν p₁ (datC h₁ h₁' Φ) = GlobalTheory.LocFlat.flRow ψ ν p₂ (datC h₂ h₂' Φ) := by
  subst hc hp; rfl

theorem stepDatum_eq_datC (G : Grid k) (hs : 1 ≤ G.s) (φ : ∀ b : Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ)
    (j : Fin (G.m - 1)) :
    stepDatum hs φ j = datC (c := G.m - 2 - j) (c' := G.m - 2 - j + 1)
      (by have := topRank_add hs (j + 1); have := j.2; show _ = G.rank (G.m, j + 1); omega)
      (by have := topRank_add hs j; have := j.2; show _ = G.rank (G.m, j); omega) (φ (.theta G.m j)) := rfl

theorem theta_sub_congr (G : Grid k) (φ : ∀ b : Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ) (x : ColArgs G)
    {i i' : ℕ} (h : i = i') (p₁ : G.rank (G.m, i + 1) ≤ topRank G (i + 1)) (p₂ : G.rank (G.m, i) = topRank G i)
    (p₃ : G.rank (G.m, i' + 1) ≤ topRank G (i' + 1)) (p₄ : G.rank (G.m, i') = topRank G i') :
    φ (.theta G.m i) ((x i).submatrix (Fin.castLE p₁) (Fin.cast p₂))ᵀ =
      φ (.theta G.m i') ((x i').submatrix (Fin.castLE p₃) (Fin.cast p₄))ᵀ := by
  subst h; rfl

theorem prod_fin_even (n : ℕ) (g : ℕ → ℂ) :
    (∏ j ∈ Finset.range (2 * n), if Even j then g j else 1) = ∏ i ∈ Finset.range n, g (2 * i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.prod_range_succ, Finset.prod_range_succ, ih,
      Finset.prod_range_succ, if_pos (even_two_mul n), if_neg (by rw [Nat.not_even_iff_odd]; exact odd_two_mul_add_one n), mul_one]

theorem locA_last (G : Grid k) (hs : 1 ≤ G.s) (ψ : AddChar k Circle) (ν : Measure k)
    (φ : ∀ b : Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ) (x : ColArgs G) (j : ℕ) (hj : j + 2 = G.m) :
    locA G hs ψ ν φ j (x j, x (j + 1)) =
      φ (.theta G.m (G.m - 1)) (lastMap hs (by omega) x)ᵀ * GlobalTheory.StepData.hat ψ ν (-1) (fun u =>
        GlobalTheory.LocFlat.flCol ψ ν 1 (stepDatum hs φ ⟨G.m - 2, by omega⟩) (fromCols (x (G.m - 2)) (Matrix.of fun r _ => u r)))
        (x (G.m - 2 + 1) (topLast G (G.m - 2 + 1 + 1))) := by
  obtain rfl : j = G.m - 2 := by omega
  rw [locA, dif_pos (by omega), stepDatum_eq_datC]
  refine congrArg₂ (· * ·) ?_ ?_
  · exact theta_sub_congr G φ x (by omega) _ _ _ _
  · congr 1
    funext u
    exact congrFun (flCol_datC_congr ψ ν _ (by simp) rfl _ _ _ _) _

theorem locA_double (G : Grid k) (hs : 1 ≤ G.s) (ψ : AddChar k Circle) (ν : Measure k)
    (φ : ∀ b : Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ) (hm : Even G.m) (j : ℕ) (he : Even j)
    (hj : j < G.m - 2) (q) :
    locA G hs ψ ν φ j q =
      GlobalTheory.LocFlat.contr ψ ν (GlobalTheory.LocFlat.flCol ψ ν ((G.m - 2 - j) / 2 + 1) (stepDatum hs φ ⟨j, by omega⟩))
        (GlobalTheory.LocFlat.flRow ψ ν ((G.m - 2 - (j + 1)) / 2 + 1) (stepDatum hs φ ⟨j + 1, by omega⟩)) q := by
  obtain ⟨a, ha⟩ := he
  obtain ⟨b, hb⟩ := hm
  rw [locA, dif_neg (by omega), dif_pos (by omega), stepDatum_eq_datC, stepDatum_eq_datC]
  exact congrArg₂ (fun A B => GlobalTheory.LocFlat.contr ψ ν A B q)
    (flCol_datC_congr ψ ν _ (by simp only; omega) (by omega) _ _ _ _)
    (flRow_datC_congr ψ ν _ (by simp only; omega) (by omega) _ _ _ _)

end

theorem flatTensor_pureTensor_eq_prod_locA : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (G : GlobalTheory.SplitFlip.Grid k) (hs : 1 ≤ G.s), 2 ≤ G.m → Even G.m → ∀ (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (φ : ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ), (∀ j < G.m - 1, φ (.theta G.m j) ∈ SB _) → ∀ (x : ColArgs G) (y : RowArgs G), flatTensor hs ψ ν (G.lines₂ (GlobalTheory.SplitFlip.oppositePath G.m) φ) x y = (∏ i ∈ Finset.range G.m, φ (.ex i G.m) (y i)ᵀ) * ∏ n ∈ Finset.range (G.m / 2), locA G hs ψ ν φ (2 * n) (x (2 * n), x (2 * n + 1)) := by
  intro k _ _ _ _ _ _ G hs hm hme ψ ν hψ hψ1 hν φ hφ x y
  rw [GlobalTheory.FunObj.flatTensor_pureTensor_eq_prod_contr k G hs hm hme ψ ν hψ hψ1 hν φ hφ x y, mul_assoc]
  congr 1
  obtain ⟨n, hn⟩ : ∃ n, G.m = 2 * n + 2 := by obtain ⟨b, hb⟩ := hme; exact ⟨b - 1, by omega⟩
  have hr : G.m / 2 = n + 1 := by omega
  rw [hr, Finset.prod_range_succ, mul_comm, locA_last G hs ψ ν φ x (2 * n) (by omega)]
  congr 1
  have h2 : G.m - 2 = 2 * n := by omega
  rw [← prod_fin_even n (fun j => locA G hs ψ ν φ j (x j, x (j + 1)))]
  rw [← Fin.prod_univ_eq_prod_range (fun j => if Even j then locA G hs ψ ν φ j (x j, x (j + 1)) else 1) (2 * n)]
  rw [← h2]
  refine Finset.prod_congr rfl fun j _ => if_ctx_congr Iff.rfl (fun hj => ?_) fun _ => rfl
  exact (locA_double G hs ψ ν φ ⟨n + 1, by omega⟩ j hj j.2 _).symm

end GlobalTheory.FlatPlace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatTensorRowFactorLargeDepth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LocAsm
open GlobalTheory.SplitFlip

section General
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem moved_pureTensor_eq_mul (G : Grid k) (keep : Bool) (g : G.VertexGroup)
    (hg : ∀ i < G.m, g (i, G.m) = 1 ∧ g (i + 1, G.m) = 1)
    (φ : ∀ b : Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ) (z : G.Args) :
    moved G keep g (G.lines₂ (oppositePath G.m) φ) z =
      moved G keep g (G.lines₂ (oppositePath G.m) (exOne φ)) z *
        ∏ i ∈ Finset.range G.m, φ (.ex i G.m) (z (.ex i G.m)) := by
  have h1 : ((List.range G.m).map fun i => φ (.ex i G.m) (G.moveArgs .one g z (.ex i G.m))) =
      (List.range G.m).map fun i => φ (.ex i G.m) (z (.ex i G.m)) := by
    refine List.map_congr_left fun i hi => ?_
    obtain ⟨ha, hb⟩ := hg i (List.mem_range.1 hi)
    simp only [Grid.moveArgs, Edge.src, Edge.tgt, ha, hb, map_one, inv_one, Units.val_one, Matrix.one_mul,
      Matrix.mul_one]
  have h2 : ((List.range G.m).map fun i => exOne φ (.ex i G.m) (G.moveArgs .one g z (.ex i G.m))).prod = 1 := by
    simp
  simp only [moved, Grid.pathAct, Grid.lines₂, oppositePath, List.map_append, List.prod_append, List.map_map,
    Function.comp_def]
  rw [h1, h2]
  show _ = _ * ((List.range G.m).map fun i => φ (.ex i G.m) (z (.ex i G.m))).prod
  simp only [exOne_theta, List.map_reverse]
  ring

theorem moved_exOne_fill (G : Grid k) (hs : 1 ≤ G.s) (keep : Bool) (g : G.VertexGroup) (γ : List Edge)
    (φ : ∀ b : Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ) (x : ColArgs G) (y y' : RowArgs G)
    (e : Vars G) :
    moved G keep g (G.lines₂ γ (exOne φ)) (fill hs x y e) =
      moved G keep g (G.lines₂ γ (exOne φ)) (fill hs x y' e) := by
  simp only [moved, Grid.pathAct, Grid.lines₂]
  congr 3
  refine List.map_congr_left fun b _ => ?_
  cases b <;> rfl

variable [MeasurableSpace k] [BorelSpace k]

theorem flatTensor_moved_pureTensor (G : Grid k) (hs : 1 ≤ G.s) (ψ : AddChar k Circle) (ν : Measure k) (keep : Bool)
    (g : G.VertexGroup) (hg : ∀ i < G.m, g (i, G.m) = 1 ∧ g (i + 1, G.m) = 1)
    (φ : ∀ b : Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ) (x : ColArgs G) (y : RowArgs G) :
    flatTensor hs ψ ν (moved G keep g (G.lines₂ (oppositePath G.m) φ)) x y =
      flatTensor hs ψ ν (moved G keep g (G.lines₂ (oppositePath G.m) (exOne φ))) x 0 *
        ∏ i ∈ Finset.range G.m, φ (.ex i G.m) (y i)ᵀ := by
  unfold flatTensor flatIntegrand
  rw [← integral_mul_const]
  congr 1
  funext e
  rw [moved_pureTensor_eq_mul G keep g hg φ, moved_exOne_fill G hs keep g _ φ x y 0 e]
  simp only [fill_ex]
  ring

end General

theorem Reps.elt_row {k : Type} [Field k] {G : Grid k} {hs : 1 ≤ G.s} {J : G.Level} (ρ : Reps hs J)
    (β : Cosets hs J) : ∀ i < G.m, ρ.elt β (i, G.m) = 1 ∧ ρ.elt β (i + 1, G.m) = 1 := by
  intro i hi
  refine ⟨dif_neg (by simp only; omega), ?_⟩
  by_cases h : i + 1 = G.m
  · have key : ∀ j (hj : j = i + 1), ρ.elt β (G.m, j) = 1 := by
      intro j hj
      subst hj
      rw [Reps.elt, onColumn_apply]
      exact dif_neg (by omega)
    rw [h]
    exact key G.m h.symm
  · exact dif_neg (by simp only; omega)

theorem flatTensor_rowFactor : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (β : CosFam ch.G t) (w : locPl ch.G t) (φ : ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w.1).rank b.tgt)) (Fin ((locGrid ch.G t w.1).rank b.src)) (Kw w.1) → ℂ), (∀ b ∈ GlobalTheory.SplitFlip.oppositePath D.R.m, GlobalTheory.SplitFlip.IsNatDatum (unifAt w.1) (depthAt ch.G w.1) (φ b)) → ∀ (u : ∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1)))) (y : ∀ i : Fin D.R.m, WO (ch.G.pS (.chi i D.R.m : Pair T)) (ch.G.pT (.chi i D.R.m : Pair T))), flatTensor one_le_sLen (psiAt ch.W w.1) (unitVol w.1) (moved (locGrid ch.G t w.1) (keepAt ch.G w.1) ((repsAt ch.G t w.1).elt (β w)) ((locGrid ch.G t w.1).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) φ)) (ch.S.colAt t w.1 u) (ch.S.rowAt t w.1 y) = flatTensor one_le_sLen (psiAt ch.W w.1) (unitVol w.1) (moved (locGrid ch.G t w.1) (keepAt ch.G w.1) ((repsAt ch.G t w.1).elt (β w)) ((locGrid ch.G t w.1).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) (GlobalTheory.LocAsm.exOne φ))) (ch.S.colAt t w.1 u) 0 * ∏ i : Fin D.R.m, φ (.ex i D.R.m) (ch.S.B.coord t w.1 (X := (i, D.R.m)) (Y := (i + 1, D.R.m)) ⟨i.2.le, le_rfl⟩ ⟨i.2, le_rfl⟩ ((y i).map fun a => cpt w.1 (toEAf D a))) := by
  refine ⟨0, fun _ _ _ => ⟨0, ?_⟩⟩
  intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F _ ch _ _ t β w φ _ u y
  refine (flatTensor_moved_pureTensor (locGrid ch.G t w.1) one_le_sLen _ _ _ _ (Reps.elt_row _ _) φ _ _).trans ?_
  congr 1
  rw [Finset.prod_range]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [GridChoice.rowAt]
  rw [dif_pos (show (i : ℕ) < D.R.m from i.2)]
  rfl

end GlobalTheory.LocAsm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridBasePointCarriesLatticeToMovedLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open scoped nonZeroDivisors

namespace GlobalTheory.BaseMoveAt

theorem val_of_reGL_eq_inv_diagGL {k : Type} [Field k] {a b : ℕ} (h : a = b) (Y : GL (Fin a) k) (c : Fin b → kˣ)
    (hY : GlobalTheory.StepData.reGL (finCongr h) Y = (GlobalTheory.SplitFlip.diagGL c)⁻¹) :
    (Y : Matrix (Fin a) (Fin a) k) = diagonal fun i => (((c (Fin.cast h i))⁻¹ : kˣ) : k) := by
  subst h
  have e : GlobalTheory.StepData.reGL (finCongr (rfl : a = a)) Y = Y := by
    ext i j
    simp [GlobalTheory.StepData.reGL]
  rw [e] at hY
  rw [hY]
  rfl

theorem submatrix_mulVec_comp {k : Type} [CommRing k] {m n ι : Type} [Fintype n] [Fintype ι] (M : Matrix m n k) (F : ι ≃ n)
    (y : n → k) : (M.submatrix id F) *ᵥ (fun i => y (F i)) = M *ᵥ y := by
  funext i
  simp only [mulVec, dotProduct, submatrix_apply, id]
  exact Fintype.sum_equiv F _ _ fun _ => rfl

end GlobalTheory.BaseMoveAt

namespace GlobalTheory.BaseMoveAt

set_option maxHeartbeats 1000000 in

theorem lat_moves_at_place : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → ∀ (G : GridData L sc) (W : G.Weil) (U : Set T) (S : GridChoice W U) (t : T), t ∈ U → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → ∀ b : Pts G, IsBase t S.B b → ∀ w ∈ locPl G t, ∀ p : GlobalTheory.FinPl.SplitPt D (Kw w), Formalism.L2.NTheta.IsIdemAt p.e w → (∀ a : AE D, p.pr a = cpt w (Lev.swapAE D (finPart D a))) → ∀ x : Fin (G.V (.grid D.R.m 0)).rank → Kw w, ((fun i => p.sec (x i)) ∈ GlobalTheory.FinPl.latV _ (G.Λ (.grid D.R.m 0)) (· = p.v) ↔ (fun i => p.sec (((Formalism.L2.Theta.mt _ (b 0)).map p.pr *ᵥ x) i)) ∈ GlobalTheory.FinPl.latV _ (GlobalTheory.RowShape.rowN G 0) (· = p.v)) := by
  intro D T L sc μ₀ hL hde G W U S t ht hc b hb w hw p hpw hpr x
  have h0 : 0 < D.R.m := by have := D.R.two_le_m; omega
  have hpr' : ∀ a : D.host.E, p.pr (incA D a) = algebraMap D.host.E (Kw w) a := fun a =>
    (hpr _).trans (GlobalTheory.FunObj.Good.cpt_incA w a)
  have hN : (Formalism.L2.Theta.mt _ (b 0)).map p.pr =
      ((GlobalTheory.StdFrames.loc w (Lev.finE (G.V (.grid D.R.m 0)) (b 0)) : GL _ (Kw w)) : Matrix _ _ (Kw w)) := by
    ext i j
    rw [Matrix.map_apply, hpr]
    rfl
  obtain ⟨e, -, -, hloc⟩ := hb.1
  have hl := hloc ⟨w, hw⟩
  simp only [GlobalTheory.FunObj.inBasis, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.conj_inv_apply] at hl
  have hY := val_of_reGL_eq_inv_diagGL _ _ _ hl
  simp only [Fin.coe_cast, topRank_eq G t w (Nat.zero_le _), map_mul, map_inv] at hY
  have hrow := S.row t ht w hw 0 h0
  unfold GlobalTheory.FunObj.IsSumFrame at hrow
  simp only [if_true] at hrow
  have hΛ : G.Λ (.grid D.R.m 0) = (G.rowDec 0 h0).lat (G.Λ (.top 0)) (stairId (G.pl.stA sc) (G.pl.stAbar sc) (D.R.m - 1 - 0)) :=
    G.sp.colLat D.R.m h0 le_rfl
  have hR : GlobalTheory.RowShape.rowN G 0 = (G.rowDec 0 h0).lat (G.Λ (.top 0)) (GlobalTheory.RowShape.rowId D 0) := by
    simp [GlobalTheory.RowShape.rowN, h0]

  obtain ⟨δ, hδ⟩ : ∃ δ : Fin (G.V (.grid D.R.m 0)).rank → Kw w, δ = fun i =>
      ((((unifAt w) ^ (cosExp G w * (i.1 + 1 - (G.V (.top 0)).rank)))⁻¹ : (Kw w)ˣ) : Kw w) := ⟨_, rfl⟩
  have hcomm : ((GlobalTheory.StdFrames.loc w (Lev.finE (G.V (.grid D.R.m 0)) (b 0)) : GL _ (Kw w)) : Matrix _ _ (Kw w)) *
      ((GlobalTheory.StdFrames.loc w (S.B.β D.R.m 0) : GL _ (Kw w)) : Matrix _ _ (Kw w)) =
      ((GlobalTheory.StdFrames.loc w (S.B.β D.R.m 0) : GL _ (Kw w)) : Matrix _ _ (Kw w)) * diagonal δ := by
    rw [hδ, ← hY, ← Units.val_mul, ← Units.val_mul]
    congr 1
    group

  obtain ⟨s, hs⟩ : ∃ s : Fin (D.R.m - 1 - 0) → Kw w, s = fun r =>
      frameSign (Kw w) (D.R.m - 1 - 0) r * ((unifAt w : Kw w) ^ (cosExp G w * (r.1 + 1))) := ⟨_, rfl⟩
  obtain ⟨M', hM'⟩ : ∃ M' : Matrix (Fin (G.V (.grid D.R.m 0)).rank) (Fin (G.V (.top 0)).rank ⊕ Fin (D.R.m - 1 - 0)) (Kw w),
      M' = (fromCols (frameMat (G.V (.grid D.R.m 0)) (G.V (.top 0)) (G.rowDec 0 h0).ι) (G.rowDec 0 h0).a).map
        (fun a => p.pr (incA D a)) := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : Matrix (Fin (G.V (.top 0)).rank ⊕ Fin (D.R.m - 1 - 0)) (Fin (G.V (.top 0)).rank ⊕ Fin (D.R.m - 1 - 0)) (Kw w),
      Q = fromBlocks ((GlobalTheory.StdFrames.loc w (S.βp 0) : GL _ (Kw w)) : Matrix _ _ (Kw w)) 0 0 (diagonal s) := ⟨_, rfl⟩
  have hLb : ((GlobalTheory.StdFrames.loc w (S.B.β D.R.m 0) : GL _ (Kw w)) : Matrix _ _ (Kw w)).submatrix id
      (GlobalTheory.FunObj.frame (G.rowDec 0 h0).rank) = M' * Q := by
    have hM'' : M' = fromCols ((frameMat (G.V (.grid D.R.m 0)) (G.V (.top 0)) (G.rowDec 0 h0).ι).map
        (algebraMap D.host.E (Kw w))) ((G.rowDec 0 h0).a.map (algebraMap D.host.E (Kw w))) := by
      rw [hM']
      ext i j
      rcases j with j | j <;> simp [hpr']
    rw [hrow, hM'', hQ, fromCols_mul_fromBlocks, hs]
    simp only [Matrix.mul_zero, add_zero, zero_add]

  have hδl : ∀ i, δ (GlobalTheory.FunObj.frame (G.rowDec 0 h0).rank (Sum.inl i)) = 1 := by
    intro i
    have hi : i.1 + 1 - (G.V (.top 0)).rank = 0 := by have := i.2; omega
    simp [hδ, GlobalTheory.FunObj.frame, hi]
  have hδr : ∀ r, δ (GlobalTheory.FunObj.frame (G.rowDec 0 h0).rank (Sum.inr r)) =
      ((unifAt w : Kw w) ^ (cosExp G w * (r.1 + 1)))⁻¹ := by
    intro r
    have hi : (G.V (.top 0)).rank + r.1 + 1 - (G.V (.top 0)).rank = r.1 + 1 := by omega
    simp [hδ, GlobalTheory.FunObj.frame, hi]
  have hQc : Q * diagonal (fun s => δ (GlobalTheory.FunObj.frame (G.rowDec 0 h0).rank s)) =
      diagonal (fun s => δ (GlobalTheory.FunObj.frame (G.rowDec 0 h0).rank s)) * Q := by
    ext i j
    rw [mul_diagonal, diagonal_mul, hQ]
    rcases i with i | i <;> rcases j with j | j
    · simp [hδl]
    · simp
    · simp
    · by_cases h : i = j
      · subst h; exact mul_comm _ _
      · simp [diagonal_apply, h]
  obtain ⟨z, hx, hNx⟩ : ∃ z, M' *ᵥ z = x ∧
      ((GlobalTheory.StdFrames.loc w (Lev.finE (G.V (.grid D.R.m 0)) (b 0)) : GL _ (Kw w)) : Matrix _ _ (Kw w)) *ᵥ x =
        M' *ᵥ (diagonal (fun s => δ (GlobalTheory.FunObj.frame (G.rowDec 0 h0).rank s)) *ᵥ z) := by
    obtain ⟨y, hy⟩ : ∃ y : Fin (G.V (.grid D.R.m 0)).rank → Kw w, y = (((GlobalTheory.StdFrames.loc w (S.B.β D.R.m 0))⁻¹ : GL _ (Kw w)) : Matrix _ _ (Kw w)) *ᵥ x := ⟨_, rfl⟩
    have hxy : ((GlobalTheory.StdFrames.loc w (S.B.β D.R.m 0) : GL _ (Kw w)) : Matrix _ _ (Kw w)) *ᵥ y = x := by
      rw [hy, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
    refine ⟨Q *ᵥ fun i => y (GlobalTheory.FunObj.frame (G.rowDec 0 h0).rank i), ?_, ?_⟩
    · rw [mulVec_mulVec, ← hLb, submatrix_mulVec_comp, hxy]
    · rw [← hxy, mulVec_mulVec, hcomm, ← mulVec_mulVec, ← submatrix_mulVec_comp _ (GlobalTheory.FunObj.frame (G.rowDec 0 h0).rank), hLb]
      have hv : (fun i => (diagonal δ *ᵥ y) (GlobalTheory.FunObj.frame (G.rowDec 0 h0).rank i)) =
          diagonal (fun s => δ (GlobalTheory.FunObj.frame (G.rowDec 0 h0).rank s)) *ᵥ fun i => y (GlobalTheory.FunObj.frame (G.rowDec 0 h0).rank i) := by
        funext i
        simp [mulVec_diagonal]
      rw [hv]
      simp only [mulVec_mulVec]
      rw [Matrix.mul_assoc, hQc]

  have h1 := (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).1
  have h2 := (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).2 T L G.pl sc
  have h3 := GlobalTheory.FunObj.ne_zero_of_conj h2.1 h2.2
  have h1' := GlobalTheory.FunObj.ne_zero_of_conj h1.1 h1.2
  have hA := GlobalTheory.FunObj.count_AA_AAbar w (GlobalTheory.FunObj.Good.badInt_notMem hL hde hc hw)
  have hmo : ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact G.pl.modul_ne_bot sc
  have hmb : ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
    intro h
    have h4 := h2.1
    rw [GlobalTheory.ChiGrid.Places.stA, h, _root_.inv_zero, mul_zero] at h4
    exact h4 rfl
  have hI1 : ∀ r, stairId (G.pl.stA sc) (G.pl.stAbar sc) (D.R.m - 1 - 0) r ≠ 0 := fun r =>
    mul_ne_zero (pow_ne_zero _ h2.1) (inv_ne_zero (pow_ne_zero _ h3))
  have hn1 : ∀ r : Fin (D.R.m - 1 - 0), FractionalIdeal.count D.host.E w
      (stairId (G.pl.stA sc) (G.pl.stAbar sc) (D.R.m - 1 - 0) r) = ((cosExp G w * (r.1 + 1) : ℕ) : ℤ) := by
    intro r
    rw [GlobalTheory.FunObj.count_stairId h2.1 h3, GlobalTheory.ChiGrid.Places.stA, GlobalTheory.ChiGrid.Places.stAbar,
      FractionalIdeal.count_mul _ _ h1.1 (inv_ne_zero hmb), FractionalIdeal.count_mul _ _ h1' (inv_ne_zero hmo),
      FractionalIdeal.count_inv, FractionalIdeal.count_inv, GlobalTheory.FunObj.count_modulBar G hw, GlobalTheory.FunObj.count_modul, hA.1, hA.2]
    push_cast
    ring
  have hrId : ∀ r, GlobalTheory.RowShape.rowId D 0 r = stairId D.host.AA D.host.AAbar (D.R.m - 1 - 0) r := by
    intro r
    simp [GlobalTheory.RowShape.rowId, GlobalTheory.RowShape.tiltSc]
  have hI2 : ∀ r, GlobalTheory.RowShape.rowId D 0 r ≠ 0 := fun r => by
    rw [hrId]
    exact mul_ne_zero (pow_ne_zero _ h1.1) (inv_ne_zero (pow_ne_zero _ h1'))
  have hn2 : ∀ r, FractionalIdeal.count D.host.E w (GlobalTheory.RowShape.rowId D 0 r) = ((0 : ℕ) : ℤ) := by
    intro r
    rw [hrId, GlobalTheory.FunObj.count_stairId h1.1 h1', hA.1, hA.2]
    simp
  have hϖ := GlobalTheory.SplitFlip.IsUnif.irreducible (isUnif_unifAt w)
  rw [hN, hNx]
  subst hx
  subst hM'
  rw [hΛ, hR, GlobalTheory.LatticeMembershipValuation.sec_mem_lat_iff p (G.rowDec 0 h0) (neg_ne_zero.2 one_ne_zero),
    GlobalTheory.LatticeMembershipValuation.sec_mem_lat_iff p (G.rowDec 0 h0) (neg_ne_zero.2 one_ne_zero)]
  simp only [mulVec_diagonal, hδl, one_mul, hδr]
  refine and_congr Iff.rfl (forall_congr' fun r => ?_)
  rw [GlobalTheory.LatticeMembershipValuation.sec_mem_idV_iff p hpw hϖ (hI1 r) (hn1 r), GlobalTheory.LatticeMembershipValuation.sec_mem_idV_iff p hpw hϖ (hI2 r) (hn2 r)]
  have hq : ((unifAt w : Kw w) ^ (cosExp G w * (r.1 + 1))) ≠ 0 := pow_ne_zero _ (Units.ne_zero _)
  constructor
  · rintro ⟨o, ho⟩
    refine ⟨o, ?_⟩
    rw [ho, pow_zero, one_mul, ← mul_assoc]
    exact (inv_mul_cancel₀ hq).symm ▸ (one_mul _)
  · rintro ⟨o, ho⟩
    refine ⟨o, ?_⟩
    rw [pow_zero, one_mul] at ho
    rw [← ho, ← mul_assoc]
    exact ((mul_inv_cancel₀ hq).symm ▸ (one_mul _)).symm

end GlobalTheory.BaseMoveAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridBasePointTrivialOffTensorPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RowVal

theorem placeIdem_eq_under_of_idemAt {D : D7} {P : HeightOneSpectrum (𝓞 D.host.E)} {e : Formalism.L2.Theta.AE D}
    (h : Formalism.L2.NTheta.IsIdemAt e P) {v' : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v' ε)
    (hs : e + cA D e = algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) ε) : v' = P.under (𝓞 D.host.F) := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨h1, h2, -⟩ := h.1
  have hm : e * (e + cA D e) = e := by rw [mul_add, h1, h2, add_zero]
  by_contra hne
  have h0 := (GlobalTheory.IdemSupport.place_comp hΦ hε).2.2 P (fun e => hne e.symm)
  have h3 := GlobalTheory.IdemSupport.ev_mul (Φ := Φ) e (e + cA D e) P
  rw [hm, hs, h0, mul_zero, (GlobalTheory.IdemSupport.delta_of_isIdemAt hΦ h).2.1] at h3
  exact one_ne_zero h3

theorem base_mt_mulVec_off : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (B : Frames G) (b : Pts G), IsBase t B b → ∀ v : GlobalTheory.FinPl.Pl D, (∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ≠ v) → ∀ y : Fin (G.V (.grid D.R.m 0)).rank → AE D, (∀ i, y i ∈ idAt D (· = v)) → Formalism.L2.Theta.mt _ (b 0) *ᵥ y = y := by
  intro D T L sc G t B b hb v hv y hy
  obtain ⟨e, ⟨⟨es, hes, rfl⟩, -⟩, hsupp, -⟩ := hb.1
  have hkill : ∀ PP ∈ locPl G t, ∀ a ∈ idAt D (· = v), (es PP + cA D (es PP)) * a = 0 := by
    intro PP hPP a ha
    obtain ⟨-, -, v', ε, hε, hs⟩ := (hes PP hPP).1
    have hv' : v' = PP.under (𝓞 D.host.F) := placeIdem_eq_under_of_idemAt (hes PP hPP) hε hs
    rw [hs]
    apply (GlobalTheory.FinPl.placeIdem_acts D v' ε hε).2
    rw [GlobalTheory.FinPl.mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere] at ha ⊢
    refine ⟨ha.1, fun w hw => ha.2 w ?_⟩
    intro h
    apply hw
    intro hwv'
    exact hv PP hPP (hv'.symm.trans (hwv'.symm.trans h))
  have hz : ∀ i, ((Formalism.L2.Theta.mt _ (b 0) - 1) *ᵥ y) i ∈ idAt D (· = v) := fun i => by
    simp only [Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hy j)
  have hE : ∀ i, ((Formalism.L2.Theta.mt _ (b 0) - 1) *ᵥ y) i =
      ((∑ PP ∈ locPl G t, es PP) + cA D (∑ PP ∈ locPl G t, es PP)) * ((Formalism.L2.Theta.mt _ (b 0) - 1) *ᵥ y) i := by
    intro i
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_assoc, hsupp i j]
  have h0 : (Formalism.L2.Theta.mt _ (b 0) - 1) *ᵥ y = 0 := by
    funext i
    rw [hE i, map_sum, ← Finset.sum_add_distrib, Finset.sum_mul]
    exact Finset.sum_eq_zero fun PP hPP => hkill PP hPP _ (hz i)
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h0
  exact h0

end GlobalTheory.RowVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridMatchingOfBaseChoiceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.grid_matching_of_base_choice : GlobalTheory.FunPr.Hypotheses₂ → ∀ {D : D7} (large₂ : SizeData₂ D)
    {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A},
    HidaSetting large₂ R F → ∀ (ch : Choice R), ch.IsBase → ∀ (CF : ℝ), ch.AtScale CF large₂.sc.b →
    ∃ G' : GlobalTheory.Grid.GridPre R, G'.Is ∧ GlobalTheory.RowLift.RowMatchS ch G' := by
  first | exact @GlobalTheory.RowLift.exists_rowMatchS | exact GlobalTheory.RowLift.exists_rowMatchS | (intros; apply GlobalTheory.RowLift.exists_rowMatchS <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLocalLatticeMatricesInvStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasLocalLatticeMatrices_inv : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (t : T) (B : Frames G) {j : ℕ}
    (hj : j ≤ D.R.m) (x : GA D (G.V (.grid D.R.m j)))
    (g : ∀ w : locPl G t, GL (Fin ((locGrid G t w.1).rank (D.R.m, j))) (Kw w.1)), HasLoc t B hj x g → HasLoc t B hj x⁻¹ (fun w => (g w)⁻¹) := by
  first | exact @GlobalTheory.RowVal.hasLoc_inv | exact GlobalTheory.RowVal.hasLoc_inv | (intros; apply GlobalTheory.RowVal.hasLoc_inv <;> assumption)
end
end

