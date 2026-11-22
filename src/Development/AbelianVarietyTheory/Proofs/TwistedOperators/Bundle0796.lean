import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0792
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0735
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0696
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0674
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefinitePeriodDependsOnProductFunction
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0117
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0122
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0790
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0770
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0346
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0753
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0788
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0779
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0776
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0758
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0647
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0757
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0740
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0296
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0769
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0723
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0668
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0518
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0290
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0303

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodReductionToFockVectorsLargeDepth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockRed

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem opPow_smul {ι X : Type} (A : ι → (X → ℂ) → X → ℂ) (hA : ∀ i (c : ℂ) g, A i (c • g) = c • A i g)
    (k : ι →₀ ℕ) (c : ℂ) (f : X → ℂ) : opPow A k (c • f) = c • opPow A k f := by
  unfold opPow
  induction (Finsupp.toMultiset k).toList with
  | nil => rfl
  | cons i l ih => simp only [List.foldr_cons, ih, hA]

theorem pureTensorL_smul {ι X : Type} (A : ι → (X → ℂ) → X → ℂ) (hA : ∀ i (c : ℂ) g, A i (c • g) = c • A i g)
    (c : ℂ) (f : X → ℂ) : pureTensorL A (c • f) = c • pureTensorL A f := by
  refine (MvPolynomial.basisMonomials ι ℂ).ext fun k => ?_
  simp only [pureTensorL, Module.Basis.constr_basis, LinearMap.smul_apply, opPow_smul A hA]

theorem dRho_smul {m n : ℕ} (hs : Mx D m n → (Mx D m n → ℂ) → Mx D m n → ℂ)
    (hhs : ∀ w (c : ℂ) g, hs w (c • g) = c • hs w g) (θ : InfFam D) (τ : D.what₂.Tau) (z : Matrix (Fin m) (Fin n) ℂ)
    (c : ℂ) (g : Mx D m n → ℂ) : Datum.dRho hs θ τ z (c • g) = c • Datum.dRho hs θ τ z g := by
  funext x
  simp only [Datum.dRho, hhs, Pi.smul_apply, smul_eq_mul]
  exact deriv_const_mul_field c

theorem aPlusAll_smul {m n : ℕ} (hs : Mx D m n → (Mx D m n → ℂ) → Mx D m n → ℂ)
    (hhs : ∀ w (c : ℂ) g, hs w (c • g) = c • hs w g) (θ : InfFam D) J B B' (k : FVar D m n) (c : ℂ) (g : Mx D m n → ℂ) :
    aPlusAll hs θ J B B' k (c • g) = c • aPlusAll hs θ J B B' k g := by
  simp only [aPlusAll, aPlus, crea, dRho_smul hs hhs, smul_comm _ c, smul_sub]

theorem fock_smul (W : G.Weil) (p : Pair T) (c : ℂ) (f : WO (G.pS p) (G.pT p) → ℂ) (Q : PolF D (G.pT p).rank (G.pS p).rank) :
    W.fock p (c • f) Q = c • W.fock p f Q := by
  have hh : ∀ w (c : ℂ) g, heisO W.ψ (G.pS p) (G.pT p) w (c • g) = c • heisO W.ψ (G.pS p) (G.pT p) w g := by
    intro w c g; funext x; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring
  simp only [GridData.Weil.fock, pureTensorO]
  rw [pureTensorL_smul _ (fun i c g => aPlusAll_smul _ hh _ _ _ _ i c g)]
  rfl

end GlobalTheory.FockRed

namespace GlobalTheory.FockRed

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem liftA_smul_left (W : G.Weil) (M : Vol G) (a : Arrow T) (f : Sch G a) (c : ℂ) (F : Fn G a.src) :
    liftA W M a f (c • F) = c • liftA W M a f F := by
  funext g
  simp only [liftA, Formalism.IndefR.Lift.liftInt, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext h; ring

theorem liftA_smul_right (W : G.Weil) (M : Vol G) (a : Arrow T) (ha : ∀ i, a ≠ .coreUp i) (c : ℂ) (f : Sch G a)
    (F : Fn G a.src) : liftA W M a (c • f) F = c • liftA W M a f F := by
  funext g
  simp only [liftA, Formalism.IndefR.Lift.liftInt, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext h
  cases a with
  | coreUp i => exact absurd rfl (ha i)
  | _ => simp only [GridData.Weil.kerA, GridData.Weil.ker, thetaKO, map_smul, LinearMap.smul_apply, Module.End.smul_def, Pi.smul_apply, smul_eq_mul]; ring

theorem pathLift_column_smul_univ (W : G.Weil) (M : Vol G) (t : T) : ∀ (n : ℕ) (s : Fin n → ℂ) (g : ∀ j : Fin n, Sch G (.col t j))
    (φ : Fn G (.top 0)), liftP W M (colPath t n) (colFam t n fun j => s j • g j) φ =
      (∏ j, s j) • liftP W M (colPath t n) (colFam t n g) φ
  | 0, s, g, φ => by simp [colPath, liftP]
  | n + 1, s, g, φ => by
    show liftA W M (.col t n) (s (Fin.last n) • g (Fin.last n))
        (liftP W M (colPath t n) (colFam t n fun j => s j.castSucc • g j.castSucc) φ) =
      (∏ j, s j) • liftA W M (.col t n) (g (Fin.last n)) (liftP W M (colPath t n) (colFam t n fun j => g j.castSucc) φ)
    rw [pathLift_column_smul_univ W M t n (fun j => s j.castSucc) (fun j => g j.castSucc) φ, liftA_smul_left,
      liftA_smul_right W M _ (fun i h => by cases h), Fin.prod_univ_castSucc, smul_smul, mul_comm]

theorem pathLift_row_smul_univ (W : G.Weil) (M : Vol G) (m : ℕ) : ∀ (n : ℕ) (s : Fin n → ℂ) (g : ∀ i : Fin n, Sch G (.right i m))
    (F : Fn G (.grid 0 m)), liftP W M (rowPath T m n) (rowFam m n fun i => s i • g i) F =
      (∏ i, s i) • liftP W M (rowPath T m n) (rowFam m n g) F
  | 0, s, g, F => by simp [rowPath, liftP]
  | n + 1, s, g, F => by
    show liftA W M (.right n m) (s (Fin.last n) • g (Fin.last n))
        (liftP W M (rowPath T m n) (rowFam m n fun i => s i.castSucc • g i.castSucc) F) =
      (∏ i, s i) • liftA W M (.right n m) (g (Fin.last n)) (liftP W M (rowPath T m n) (rowFam m n fun i => g i.castSucc) F)
    rw [pathLift_row_smul_univ W M m n (fun i => s i.castSucc) (fun i => g i.castSucc) F, liftA_smul_left,
      liftA_smul_right W M _ (fun i h => by cases h), Fin.prod_univ_castSucc, smul_smul, mul_comm]

end GlobalTheory.FockRed

namespace GlobalTheory.FockRed

theorem defPer_of_smul {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) (t : T) (M : Vol G) (Q : PolCol G) (P : PolRow G) (d : PureDat G t) (φ : Fn G (.top 0))
    (F : Fn G (.grid 0 D.R.m)) (s s' : Fin D.R.m → ℂ) (g : ∀ j : Fin D.R.m, WO (G.V (.top j)) (G.V (.top (j + 1))) → ℂ)
    (f : SchRow G) (h1 : ∀ j : Fin D.R.m, movedVec t S (d.1 j) = s j • g j) (h2 : ∀ i : Fin D.R.m, movedVec t S (d.2 i) = s' i • f i) :
    defPer t S M (Q, P) d φ F = ((∏ j, s j) * ∏ i, s' i) * ∫ h in M.fd (.grid D.R.m D.R.m),
      liftP W M (colPath t D.R.m) (colFam t D.R.m fun j => W.fock (.top t j) (g j) (Q j)) φ (stabilizerEmbedding G.sp.topDec h) *
        liftP W M (rowPath T D.R.m D.R.m) (rowFam D.R.m D.R.m fun i => W.fock (.chi i D.R.m) (f i) (P i)) F h
        ∂M.ν (.grid D.R.m D.R.m) := by
  have e1 : (fun j : Fin D.R.m => (W.fock (.top t j) (movedVec t S (d.1 j)) (Q j) : Sch G (.col t j))) =
      fun j : Fin D.R.m => s j • (W.fock (.top t j) (g j) (Q j) : Sch G (.col t j)) := funext fun j => by
    rw [h1 j]; exact fock_smul W (.top t j) _ _ _
  have e2 : (fun i : Fin D.R.m => (W.fock (.chi i D.R.m) (movedVec t S (d.2 i)) (P i) : Sch G (.right i D.R.m))) =
      fun i : Fin D.R.m => s' i • (W.fock (.chi i D.R.m) (f i) (P i) : Sch G (.right i D.R.m)) := funext fun i => by
    rw [h2 i]; exact fock_smul W (.chi i D.R.m) _ _ _
  have e3 := (congrArg (fun x => liftP W M (colPath t D.R.m) (colFam t D.R.m x) φ) e1).trans
    (pathLift_column_smul_univ W M t D.R.m s (fun j => W.fock (.top t j) (g j) (Q j)) φ)
  have e4 := (congrArg (fun x => liftP W M (rowPath T D.R.m D.R.m) (rowFam D.R.m D.R.m x) F) e2).trans
    (pathLift_row_smul_univ W M D.R.m D.R.m s' (fun i => W.fock (.chi i D.R.m) (f i) (P i)) F)
  unfold defPer
  rw [← integral_const_mul]
  congr 1
  funext h
  have e5 := congrFun e3 (stabilizerEmbedding G.sp.topDec h)
  have e6 := congrFun e4 h
  simp only [Pi.smul_apply, smul_eq_mul] at e5 e6
  refine (congrArg₂ (· * ·) e5 e6).trans ?_
  ring

section
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

set_option maxHeartbeats 1600000 in

theorem fockAt_of_steps (ch : Choice R) (hB : BasicAt ch) (hMv : MovedAt ch) (hCF : ColFock ch)
    (hL : ∀ (t : T) (M : Vol ch.G), IsHaarDef M → ∀ (f : SchRow ch.G), (∀ i, IsThetaFunO ch.W.ψ _ _ (f i)) →
      ∀ (P : PolRow ch.G) (y : (R.HX t).H), GlobalTheory.Unf.IsContAut _ (liftP ch.W M (rowPath T D.R.m D.R.m)
        (rowFam D.R.m D.R.m fun i => ch.W.fock (.chi i D.R.m) (f i) (P i)) (formTop ch t y))) : FockAt ch := by
  classical
  obtain ⟨_, _, _, _, _, hBgood', _⟩ := hB
  obtain ⟨v, hv, κ, κ', z, hz, hmv⟩ := hMv
  refine ⟨fun t => ∏ j : Fin D.R.m, z t j, fun t => Subgroup.prod_mem _ fun j _ => hz t j, ?_⟩
  intro C hC P
  obtain ⟨σc, hσc⟩ := hCF v hv C hC
  obtain ⟨K, hK⟩ : ∃ K : ℂ, K = (∏ j : Fin D.R.m, ((κ j : ℂˣ) : ℂ))⁻¹ * (∏ i : Fin D.R.m, ((κ' i : ℂˣ) : ℂ))⁻¹ := ⟨_, rfl⟩
  refine ⟨K • σc.mapDomain (fun Q => (Q, P)), ?_⟩
  intro t a β M hM hS τ c hτ hc y
  obtain ⟨Z, hZ⟩ : ∃ Z : ℂ, Z = ∏ j : Fin D.R.m, ((z t j : ℂˣ) : ℂ) := ⟨_, rfl⟩
  have hone : Z⁻¹ * K * ((∏ j : Fin D.R.m, ((κ j * z t j : ℂˣ) : ℂ)) * ∏ i : Fin D.R.m, ((κ' i : ℂˣ) : ℂ)) = 1 := by
    have n1 : (∏ j : Fin D.R.m, ((κ j : ℂˣ) : ℂ)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => (κ j).ne_zero
    have n2 : (∏ j : Fin D.R.m, ((κ' j : ℂˣ) : ℂ)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => (κ' j).ne_zero
    have n3 : (∏ j : Fin D.R.m, ((z t j : ℂˣ) : ℂ)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => (z t j).ne_zero
    simp only [Units.val_mul, Finset.prod_mul_distrib]
    rw [hK, hZ]
    field_simp
  have key : ∀ d ∈ τ.support, per ch.W M t (combC ch.W (c d) C) (combR ch.rm (c d)) P (colFn ch a) (formTop ch t y) =
      σc.sum fun Q x => x * (Z⁻¹ * K * defPer t ch.S.toGridChoice M (Q, P) d (colFn ch a) (formTop ch t y)) := by
    intro d hd
    obtain ⟨h1, h2⟩ := hmv t a β τ c hS hτ hc d hd
    have hfin : ∀ j, j < D.R.m → IsFinComb ((c d).1 j) := fun j hj => ((hc d hd).1 ⟨j, hj⟩).1
    have hth := (hBgood' C hC (c d) hfin).2
    refine (hσc t M hM a (c d) hfin _ (hL t M hM (combR ch.rm (c d)) hth P y)).trans ?_
    refine Finset.sum_congr rfl fun Q _ => ?_
    dsimp only
    rw [defPer_of_smul ch.S.toGridChoice t M Q P d (colFn ch a) (formTop ch t y) (fun j => ((κ j * z t j : ℂˣ) : ℂ))
      (fun i => ((κ' i : ℂˣ) : ℂ)) (fun j => comb ch.W.ψ _ _ ((c d).1 j) (v j)) (combR ch.rm (c d)) h1 h2,
      ← mul_assoc (Z⁻¹ * K), hone, one_mul]
  rw [defTot_smul, Units.coe_prod, ← hZ]
  unfold defTot
  rw [Finsupp.sum_mapDomain_index_inj (fun Q Q' h => (Prod.ext_iff.1 h).1), Finsupp.sum_comm]
  simp only [Finsupp.sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [key d hd, Finsupp.sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun Q _ => ?_
  ring

end

theorem fockAt_big : Big fun ch => FockAt ch := by
  obtain ⟨a0, ha⟩ := Big.and (Big.and GlobalTheory.T.lastRow_unfolding_basicHypotheses GlobalTheory.T.movedVectorsAreCombinationsOfVacua_of_large_depth) GlobalTheory.T.columnRealDatum_fockCombination_largeDepth
  refine ⟨a0, fun ε CF hC => ?_⟩
  obtain ⟨x, hx⟩ := ha ε CF hC
  refine ⟨x, fun D large₂ he hxx Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch hsc => ?_⟩
  obtain ⟨⟨hB, hMv⟩, hCF⟩ := hx D large₂ he hxx Γ Pl0 T A Ks R F s ch hch hsc
  refine fockAt_of_steps ch hB hMv hCF fun t M hM f hf P y => ?_
  have hN : ∀ X, DefNode D.R.m X → X ≠ .top D.R.m → GlobalTheory.RowTens.Nice M X := fun X hX hX' => by
    refine ⟨?_, hM X hX hX'⟩
    rcases X with ⟨i, j⟩ | i | j
    all_goals first
      | exact hX.elim
      | exact GlobalTheory.DefConv.posDef_of_node ch.G s.core.lev hX rfl
      | (obtain ⟨h1, rfl⟩ := hX
         exact GlobalTheory.DefConv.posDef_of_node ch.G s.core.lev ⟨h1, le_rfl⟩ (by simp [Node.neg]))
  have := GlobalTheory.RowTens.row_invCont ch.W hN (hB.2.1 t y) D.R.m le_rfl _
    fun k : Fin D.R.m => GlobalTheory.RowTens.fock_theta ch.W _ (hf k) (P k)
  exact ⟨this.2, this.1⟩

end GlobalTheory.FockRed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StandardAuxiliaryFramesGoodRowGrids
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.Unf.FB (selFirst lastE mul_mul_mul_of_gram)

namespace GlobalTheory.AscFin.GoodStd

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem xLast_rat {V V₀ A L : HSp D} {σ : ℕ} (d : HypDec V V₀ σ) (o : OrthDec V₀ A L) (ζ : Fin L.rank → D.host.E)
    (hζ : IsLineVec L ζ) : ∃ x₀ : Matrix (Fin V.rank) (Fin (σ + 1)) D.host.E,
      LinearIndependent D.host.E x₀.transpose ∧ xLast d (vecB o ζ) = rat x₀ := by
  set x₀ : Matrix (Fin V.rank) (Fin (σ + 1)) D.host.E := d.e * selFirst D σ + d.i₀ * vecMulVec (vecB o ζ) (lastE D σ) with hx₀
  have hne : ∀ x : Fin σ, (Fin.last σ = x.castSucc) ↔ False := fun x => iff_false_intro (Fin.castSucc_lt_last x).ne'
  have hrat : xLast d (vecB o ζ) = rat x₀ := by
    funext k j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [hx₀, xLast, rat, selFirst, lastE, Matrix.mul_apply, vecMulVec, HypDec.j0, mulVec, dotProduct, ratV, vecB, hne]
    · simp [hx₀, xLast, rat, selFirst, lastE, Matrix.mul_apply, vecMulVec, HypDec.jX, mulVec, dotProduct, ratV, vecB]
  have hgram : x₀ᴴ * V.gram * x₀ = (vecMulVec ζ (lastE D σ))ᴴ * L.gram * vecMulVec ζ (lastE D σ) := by
    have hXX := mul_mul_mul_of_gram (n := Fin (σ + 1)) d.ee
    have h0X := mul_mul_mul_of_gram (n := Fin (σ + 1)) d.i₀e
    have hX0 : d.eᴴ * V.gram * d.i₀ = 0 := by
      have := congrArg conjTranspose d.i₀e
      rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, gram_conjTranspose, conjTranspose_zero,
        ← Matrix.mul_assoc] at this
    have hX0' := mul_mul_mul_of_gram (n := Fin (σ + 1)) hX0
    have h00 := mul_mul_mul_of_gram (n := Fin (σ + 1)) d.iso
    have hBB := mul_mul_mul_of_gram (n := Fin (σ + 1)) o.isoB
    have hz : vecMulVec (vecB o ζ) (lastE D σ) = o.iB * vecMulVec ζ (lastE D σ) := by
      rw [vecB, mul_vecMulVec]
    rw [hx₀, hz]
    simp only [conjTranspose_add, conjTranspose_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, hXX, h0X, hX0',
      h00, hBB, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
  refine ⟨x₀, ?_, hrat⟩
  refine Fintype.linearIndependent_iff.2 ?_
  intro g hg
  have hv : x₀ *ᵥ g = 0 := by
    funext k
    have := congrFun hg k
    simpa [Finset.sum_apply, mulVec, dotProduct, mul_comm] using this
  have h0 : d.e'ᴴ * V.gram * d.i₀ = 0 := by
    have := congrArg conjTranspose d.i₀e'
    rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, gram_conjTranspose, conjTranspose_zero,
      ← Matrix.mul_assoc] at this
  have hq : (d.e'ᴴ * V.gram) * x₀ = selFirst D σ := by
    rw [hx₀, Matrix.mul_add, ← Matrix.mul_assoc, d.e'e, Matrix.one_mul, ← Matrix.mul_assoc, h0, Matrix.zero_mul, add_zero]
  have h1 : selFirst D σ *ᵥ g = 0 := by rw [← hq, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  have h2 : ((vecMulVec ζ (lastE D σ))ᴴ * L.gram * vecMulVec ζ (lastE D σ)) *ᵥ g = 0 := by
    rw [← hgram, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  intro i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · have h3 := congrFun h2 (Fin.last σ)
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, vecMulVec_mulVec, conjTranspose_vecMulVec, vecMulVec_mulVec] at h3
    simp [lastE, mulVec_smul] at h3
    rcases h3 with h3 | h3
    · exact h3
    · exact absurd h3 hζ.2
  · have := congrFun h1 i
    simpa [selFirst, mulVec, dotProduct] using this

theorem loc_cls {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (s : Step ψ V V₀ W W₀ ρ σ)
    (x : Mx D W.rank ρ) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (hx : x = rat x₀) (y : Mx D V₀.rank σ)
    (p : Pieces V₀ W W₀ ρ σ) (Γ : AddSubgroup (WO V W)) (K : Subgroup (GA D W)) (hψ : IsStdChar D ψ (-1))
    (hli : LinearIndependent D.host.E x₀.transpose) (hp : p.Is dV dW x ψ) (hs : Splits dV dW p x y ψ Γ)
    (hfin : K ≤ GfC W) (hcpt : IsCompact (K : Set (GA D W)))
    (hopn : IsOpen ((K.subgroupOf (GfC W) : Subgroup (GfC W)) : Set (GfC W)))
    (hfix : ∀ f, VacG ψ V W Γ f → ∀ k ∈ K, s.om (1, k) f = f)
    (hsupp : ∀ h, Cond dW p x y ψ (fun _ => True) h → (∀ κ ∈ K, Cond dW p x y ψ (fun _ => True) (h * κ)) →
      ∃ r ∈ Rgrp W x, ∃ a ∈ GinfC W, ∃ k ∈ K, h = r * a * k) :
    Loc dV dW s x y (cls dV dW p x y ψ) p.Γ₀ K ∧ ∀ Φ ∈ cls dV dW p x y ψ, VacG ψ V W Γ Φ := by
  subst hx
  have hvac : ∀ Φ ∈ cls dV dW p (rat x₀) y ψ, VacG ψ V W Γ Φ := fun Φ hΦ =>
    GlobalTheory.T.doubleMixedModelSupportedClass_subset_splitLatticeVacua D ψ hψ V V₀ W W₀ ρ σ dV dW p (rat x₀) y Γ hp hs Φ hΦ
  have hst := fun Φ hΦ => GlobalTheory.T.doubleMixedModelClass_stable_flat_vacua D ψ V V₀ W W₀ ρ σ dV dW s x₀ y hli p hp Φ hΦ
  refine ⟨⟨fun Φ hΦ => hΦ.1, fun Φ hΦ => (hst Φ hΦ).1, fun Φ hΦ => (hst Φ hΦ).2.1, fun Φ hΦ => (hst Φ hΦ).2.2, hfin,
    hcpt, hopn, fun Φ hΦ k hk => hfix Φ (hvac Φ hΦ) k hk, ?_, GlobalTheory.T.exists_unfolding_flatMap_ne_zero_fullRank D ψ hψ V V₀ W W₀ ρ σ dV dW s x₀ y hli p hp⟩, hvac⟩
  intro Φ hΦ h hne
  refine hsupp h (GlobalTheory.T.unfoldingConditions_of_flatMap_weilAction_ne_zero D ψ V V₀ W W₀ ρ σ dV dW s x₀ y hli p hp Φ hΦ h hne) fun κ hκ =>
    GlobalTheory.T.unfoldingConditions_of_flatMap_weilAction_ne_zero D ψ V V₀ W W₀ ρ σ dV dW s x₀ y hli p hp Φ hΦ (h * κ) ?_
  have e : s.om (1, h * κ) Φ = s.om (1, h) Φ := by
    have : ((1 : GA D V), h * κ) = (1, h) * (1, κ) := by simp
    rw [this, map_mul, Module.End.mul_apply, hfix Φ (hvac Φ hΦ) κ hκ]
  rwa [e]

end GlobalTheory.AscFin.GoodStd

namespace GlobalTheory.AscFin.GoodStd

theorem std_good : GlobalTheory.SepRows.DepFixed → All fun {_} _ _ _ {G} W _ =>
    ∀ (v : CoreVol G) (F : GlobalTheory.Asc.Frames G), Std F → F.Good v W (lineLat F) := by
  intro hDF D hQ T L μ0 hL sc G W M hM v F hF
  have hψ : IsStdChar D W.ψ (-1) := W.ψ_std
  have cj := GlobalTheory.T.weil_datum_conjugation_dictionary_row_grid hDF D hQ T L μ0 hL sc G W M hM
  have gl := GlobalTheory.T.depthCongruenceSubgroup_compactOpen_places_to_adeles D hQ T L μ0 hL sc G W M hM
  have kv := GlobalTheory.T.latticeStabilizerAtPlace_mem_depthCongruence_gridNode D hQ T L μ0 hL sc G W M hM
  have lt := GlobalTheory.T.last_seesaw_lattices_nonzero_line_vacua D hQ T L μ0 hL sc G W M hM F hF
  refine ⟨?_, ?_, lt.1, fun h => lt.2 v h⟩
  · intro ρ h s hs
    obtain ⟨hbase, -, hx, -⟩ := GlobalTheory.Unf.base_point D _ _ ρ (F.dJ ρ h)
    obtain ⟨hpIs, hspl⟩ := GlobalTheory.T.besselToFourierJacobi_mixedPieces_admissible D hQ T L μ0 hL sc G W M hM F hF ρ h
    have gd := GlobalTheory.T.goodPosition_and_incAdj_mem_latO_iff_mem_intAt D hQ T L μ0 hL sc G W M hM F hF ρ h
    have g0 := gl (2 * ρ + 1) (by omega)
    have hsupp : ∀ g, Cond (F.dJ ρ h) (pcBF W F ρ h) (xZero (F.dJ ρ h)) (yBF F ρ h) W.ψ (fun _ => True) g →
        (∀ κ ∈ lev G (.grid (2 * ρ + 1) 0),
          Cond (F.dJ ρ h) (pcBF W F ρ h) (xZero (F.dJ ρ h)) (yBF F ρ h) W.ψ (fun _ => True) (g * κ)) →
        ∃ r ∈ Rgrp _ (xZero (F.dJ ρ h)), ∃ a ∈ GinfC _, ∃ k ∈ lev G (.grid (2 * ρ + 1) 0), g = r * a * k := by
      intro g hc hcK
      refine g0.2 (Rgrp _ (xZero (F.dJ ρ h))) g ?_ ?_
      · intro w hw h₁ hh₁ h₂ hh₂ e
        obtain ⟨g1, g2, g3⟩ := gd w hw
        refine GlobalTheory.T.goodPlace_oneCoset_of_besselLevel D W.ψ hψ _ _ _ _ ρ (F.dB ρ h) (F.dJ ρ h) (pcBF W F ρ h) (vecB (F.oB ρ h) (F.ζ (ρ + 1)))
          _ _ _ _ w g1 g2 g3 h₁ hh₁ ?_
        intro κ hκ
        have hκl : κ ∈ lev G (.grid (2 * ρ + 1) 0) := kv (2 * ρ + 1) (by omega) w hw κ hκ
        have hcomm : κ * h₂ = h₂ * κ := ((GlobalTheory.FinPl.localComponents D (· = w)).2 _).2.1 κ hκ.1 h₂ hh₂
        have e' : g * κ = (h₁ * κ) * h₂ := by rw [e, mul_assoc, ← hcomm, mul_assoc]
        have hc' := hcK κ hκl
        rw [e'] at hc'
        exact GlobalTheory.T.flatMapNonvanishingCondition_localise D W.ψ hψ _ _ _ _ ρ ρ (F.dB ρ h) (F.dJ ρ h) (pcBF W F ρ h) _ _ (· = w) (h₁ * κ) h₂
          (mul_mem hh₁ hκ.1) hh₂ hc'
      · intro h₁ hh₁ h₂ hh₂ e
        exact GlobalTheory.T.besselLevel_oneCoset_at_exceptionalPlaces D hQ T L μ0 hL sc G W M hM F hF ρ h h₁ hh₁
          (GlobalTheory.T.flatMapNonvanishingCondition_localise D W.ψ hψ _ _ _ _ ρ ρ (F.dB ρ h) (F.dJ ρ h) (pcBF W F ρ h) _ _ (fun v => v ∈ G.pl.S0) h₁ h₂ hh₁ hh₂
            (e ▸ hc))
    obtain ⟨hloc, hvac⟩ := loc_cls (F.dB ρ h) (F.dJ ρ h) s (xZero (F.dJ ρ h)) (F.dJ ρ h).e hx (yBF F ρ h) (pcBF W F ρ h)
      (latRow G (2 * ρ + 1)) (lev G (.grid (2 * ρ + 1) 0)) hψ hbase.1 hpIs hspl g0.1.1 g0.1.2.1 g0.1.2.2
      (fun f hf k hk => by rw [hs]; exact (cj (2 * ρ + 1) (by omega)).2.2.2.2.2.2 f hf k hk) hsupp
    exact ⟨_, _, hloc, hvac, GlobalTheory.T.boxDepthData_mul_lineVacua_besselLevel D hQ T L μ0 hL sc G W M hM F hF ρ h⟩
  · intro σ h h' s hs
    obtain ⟨x₀, hli, hx⟩ := xLast_rat (F.dB σ h') (F.oB σ h') (F.ζ (σ + 1)) (F.line (σ + 1))
    obtain ⟨hpIs, hspl⟩ := GlobalTheory.T.fourierJacobi_step_pieces_admissible_splits D hQ T L μ0 hL sc G W M hM F hF σ h h'
    have gd := GlobalTheory.T.standard_frames_successive_levels D hQ T L μ0 hL sc G W M hM F hF σ h h'
    have lat := (GlobalTheory.T.grid_lattices_compact_selfDual_splitting D hQ T L μ0 hL sc G W M hM F hF).2.1 σ h'
    have g0 := gl (2 * σ + 2) (by omega)
    have hsupp : ∀ g, Cond (F.dB σ h') (pcFB W F σ h h') (xFB F σ h') 0 W.ψ (fun _ => True) g →
        (∀ κ ∈ lev G (.grid (2 * σ + 2) 0), Cond (F.dB σ h') (pcFB W F σ h h') (xFB F σ h') 0 W.ψ (fun _ => True) (g * κ)) →
        ∃ r ∈ Rgrp _ (xFB F σ h'), ∃ a ∈ GinfC _, ∃ k ∈ lev G (.grid (2 * σ + 2) 0), g = r * a * k := by
      intro g hc _
      refine g0.2 (Rgrp _ (xFB F σ h')) g ?_ ?_
      · intro w hw h₁ hh₁ h₂ hh₂ e
        obtain ⟨g1, g2⟩ := gd w hw
        exact GlobalTheory.T.fourierJacobiLevel_oneCoset_at_goodPlace D W.ψ hψ _ _ _ _ _ _ σ (F.dJ (σ + 1) h) (F.dB σ h') (F.oB σ h') (F.ζ (σ + 1)) (F.line (σ + 1))
          (pcFB W F σ h h') _ _ _ _ (G.Λ (.core (2 * σ + 2))) _ w g1 g2 (G.sp.P_is (2 * σ + 2) (by omega)).sd lat.2.2.1
          (lat.2.2.2 w) h₁ hh₁
          (GlobalTheory.T.flatMapNonvanishingCondition_localise D W.ψ hψ _ _ _ _ (σ + 1) σ (F.dJ (σ + 1) h) (F.dB σ h') (pcFB W F σ h h') _ _ (· = w) h₁ h₂ hh₁ hh₂
            (e ▸ hc))
      · intro h₁ hh₁ h₂ hh₂ e
        exact GlobalTheory.T.one_coset_decomposition_statement D hQ T L μ0 hL sc G W M hM F hF σ h h' h₁ hh₁
          (GlobalTheory.T.flatMapNonvanishingCondition_localise D W.ψ hψ _ _ _ _ (σ + 1) σ (F.dJ (σ + 1) h) (F.dB σ h') (pcFB W F σ h h') _ _ (fun v => v ∈ G.pl.S0)
            h₁ h₂ hh₁ hh₂ (e ▸ hc))
    obtain ⟨hloc, hvac⟩ := loc_cls (F.dJ (σ + 1) h) (F.dB σ h') s (xFB F σ h') x₀ hx 0 (pcFB W F σ h h')
      (latRow G (2 * σ + 2)) (lev G (.grid (2 * σ + 2) 0)) hψ hli hpIs hspl g0.1.1 g0.1.2.1 g0.1.2.2
      (fun f hf k hk => by rw [hs]; exact (cj (2 * σ + 2) (by omega)).2.2.2.2.2.2 f hf k hk) hsupp
    exact ⟨_, _, hloc, hvac, GlobalTheory.T.fourierJacobi_depthDatum_mul_lineVacuum_isVacuum D hQ T L μ0 hL sc G W M hM F hF σ h h'⟩

end GlobalTheory.AscFin.GoodStd
end
end

