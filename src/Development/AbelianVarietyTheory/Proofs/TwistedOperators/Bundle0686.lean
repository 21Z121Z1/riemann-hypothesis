import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0677
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0910
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0931
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0926
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0541
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0644
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0428
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0388
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsVEqOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0508
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0390
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0650
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LatNotSelfDual
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0163
import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastRowRealIteratedIntegralEqConstMulFinite

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualGridRowMovedLatticeLargeDepth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped nonZeroDivisors

namespace GlobalTheory.RowShape

variable {D : D7}

theorem mem_spanSingleton_mul_iff {s x : D.host.E} (hs : s ≠ 0) (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :
    x ∈ FractionalIdeal.spanSingleton _ s * I ↔ x * s⁻¹ ∈ I := by
  rw [FractionalIdeal.mem_singleton_mul]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rwa [mul_comm, ← mul_assoc, inv_mul_cancel₀ hs, one_mul]
  · intro h
    exact ⟨x * s⁻¹, h, by rw [mul_comm, mul_assoc, inv_mul_cancel₀ hs, mul_one]⟩

theorem tiltSc_ne_zero (j : ℕ) (p : Fin (D.R.m - 1 - j)) : tiltSc D j p ≠ 0 := by
  unfold tiltSc
  split_ifs
  · exact inv_ne_zero (pow_ne_zero _ cmHost_imaginaryGenerator_ne_zero)
  · exact star_ne_zero.2 (pow_ne_zero _ cmHost_imaginaryGenerator_ne_zero)
  · exact one_ne_zero

theorem tiltSc_mul_star_rev (j : ℕ) (p : Fin (D.R.m - 1 - j)) : tiltSc D j p * star (tiltSc D j p.rev) = 1 := by
  have hx : D.host.xi0 ≠ 0 := cmHost_imaginaryGenerator_ne_zero
  obtain ⟨a, ha⟩ := D.R.m_even
  have hp := p.2
  unfold tiltSc
  by_cases hj : Odd j
  · obtain ⟨b, hb⟩ := hj
    have hj' : Odd j := ⟨b, hb⟩
    rw [if_pos hj', if_pos hj', Fin.val_rev]
    by_cases h1 : 2 * p.1 < D.R.m - 1 - j
    · rw [if_pos h1, if_neg (by omega)]
      have e : D.R.m - 1 - j - 1 - (D.R.m - 1 - j - (p.1 + 1)) = p.1 := by omega
      rw [e, star_star, inv_mul_cancel₀ (pow_ne_zero _ hx)]
    · rw [if_neg h1, if_pos (by omega)]
      have e : D.R.m - 1 - j - (p.1 + 1) = D.R.m - 1 - j - 1 - p.1 := by omega
      rw [e, star_inv₀, mul_inv_cancel₀ (star_ne_zero.2 (pow_ne_zero _ hx))]
  · rw [if_neg hj, if_neg hj, star_one, one_mul]

theorem rowId_ne_zero_and_dual (j : ℕ) (p : Fin (D.R.m - 1 - j)) :
    rowId D j p ≠ 0 ∧ ∀ x, x ∈ rowId D j p.rev ↔ star x ∈ (rowId D j p)⁻¹ := by
  obtain ⟨hA, hconj⟩ := (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).1
  obtain ⟨h0, hd⟩ := GlobalTheory.ChiGrid.stairId_ne_zero_and_mem_rev_iff D _ _ hA hconj (D.R.m - 1 - j) p
  have hs := tiltSc_ne_zero (D := D) j p
  have hs' := tiltSc_ne_zero (D := D) j p.rev
  refine ⟨mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.2 hs) h0, fun x => ?_⟩
  unfold rowId
  rw [mul_inv, FractionalIdeal.spanSingleton_inv, mem_spanSingleton_mul_iff hs', mem_spanSingleton_mul_iff (inv_ne_zero hs),
    inv_inv, hd, star_mul', star_inv₀]
  have e : (star (tiltSc D j p.rev))⁻¹ = tiltSc D j p := by
    exact inv_eq_of_mul_eq_one_left (tiltSc_mul_star_rev j p)
  rw [e]

variable {T : Type} {L : LevCh D T} {sc : Consts}

theorem isSelfDualC_rowN (G : GridData L sc) (j : ℕ) (hj : j ≤ D.R.m) : IsSelfDualC _ (rowN G j) := by
  unfold rowN
  split_ifs with h
  · refine GlobalTheory.ChiGrid.SumDual.isSelfDualC_lat D _ _ _ _ (G.rowDec j h) _ _ (Or.inr rfl)
      (G.isV (X := .top j) hj (fun _ h' => by cases h')).sd (fun p => (rowId_ne_zero_and_dual j p).1)
      (fun p x => (rowId_ne_zero_and_dual j p).2 x)
  · exact (G.isV (X := .grid D.R.m j) ⟨le_rfl, hj⟩ (fun _ h' => by
      have := D.R.two_le_m
      injection h' with h1; omega)).sd

end GlobalTheory.RowShape

theorem GlobalTheory.RowShape.big_isSelfDualC_rowN :
    Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ j, j ≤ D.R.m → IsSelfDualC _ (GlobalTheory.RowShape.rowN ch.G j) :=
  ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ j hj => GlobalTheory.RowShape.isSelfDualC_rowN ch.G j hj⟩⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiFlagCharPrimitiveMovedLatticeLargeDepth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped nonZeroDivisors

namespace GlobalTheory.RowShape

namespace PrimJac

theorem rowJac_line {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (n : ℕ) (hn : n < D.R.m) (σ : ℕ)
    (h : D.R.m - 1 - n = 2 * σ) (v : Pl D) (p : Fin σ) (a : AE D) :
    colMul (rowJac G n hn σ h).jX p a ∈ latV _ (rowN G n) (· = v) ↔
      a ∈ idV (rowId D n (Fin.castLE (by omega) p)) v := by
  have e1 : colMul (rowJac G n hn σ h).jX p a =
      fun k => a * incA D (1 * (G.rowDec n hn).a k (Fin.castLE (by omega) p)) := by
    funext k
    simp [colMul, HypDec.jX, rat, Matrix.map_apply, rowJac, jacDec, HermitianOrthogonalExtensionData.iso]
  have e2 : rowN G n = (G.rowDec n hn).lat (G.Λ (.top n)) (rowId D n) := by
    unfold rowN; rw [dif_pos hn]
  rw [e1, e2, GlobalTheory.StairLine.line_mem_iff _ _ _ _ (by simp only [Fin.coe_castLE]; omega) one_ne_zero v a, inv_one,
    FractionalIdeal.spanSingleton_one, one_mul]

theorem stairId_ne_zero (D : D7) (c : ℕ) (p : Fin c) : stairId D.host.AA D.host.AAbar c p ≠ 0 := by
  unfold stairId
  exact mul_ne_zero (pow_ne_zero _ (GlobalTheory.CuspCharLattice.host_AA_ne_zero _))
    (inv_ne_zero (pow_ne_zero _ (GlobalTheory.Member.LatSelfDual.AAbar_ne_zero D)))

theorem tiltSc_first {D : D7} {n : ℕ} (hodd : Odd n) (p : Fin (D.R.m - 1 - n)) (hp : 2 * p.1 < D.R.m - 1 - n) :
    tiltSc D n p = (D.host.xi0 ^ p.1)⁻¹ := by
  unfold tiltSc; rw [if_pos hodd, if_pos hp]

theorem rowId_ratio {D : D7} {n : ℕ} (hodd : Odd n) (p q : Fin (D.R.m - 1 - n)) (hpq : q.1 = p.1 + 1)
    (hq : 2 * q.1 < D.R.m - 1 - n) : rowId D n p * (rowId D n q)⁻¹ = dI D := by
  have hx : D.host.xi0 ≠ 0 := cmHost_imaginaryGenerator_ne_zero
  unfold rowId
  rw [tiltSc_first hodd p (by omega), tiltSc_first hodd q hq,
    stairId_succ (GlobalTheory.Member.LatSelfDual.AAbar_ne_zero D) p q hpq]
  have hS := stairId_ne_zero D (D.R.m - 1 - n) q
  revert hS
  generalize stairId D.host.AA D.host.AAbar (D.R.m - 1 - n) q = S
  intro hS
  rw [mul_inv, FractionalIdeal.spanSingleton_inv, inv_inv]
  unfold dI
  calc _ = FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (D.host.xi0 ^ p.1)⁻¹ *
        FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (D.host.xi0 ^ q.1) * D.host.AA * D.host.AAbar * (S * S⁻¹) := by ring
    _ = _ := by
      rw [mul_inv_cancel₀ hS, mul_one, FractionalIdeal.spanSingleton_mul_spanSingleton, hpq, pow_succ,
        ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hx), one_mul]

end PrimJac

open PrimJac

theorem primAt_rowJac {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (ψ : AddChar (AF D.host.F) ℂ)
    (hψ : IsStdChar D ψ (-1)) (n : ℕ) (hn : n < D.R.m) (σ : ℕ) (h : D.R.m - 1 - n = 2 * σ) (v : Pl D) :
    PrimAt ψ (rowJac G n hn σ h) (rowN G n) v := by
  have hodd : Odd n := by
    obtain ⟨k, hk⟩ := D.R.m_even
    exact ⟨k - σ - 1, by omega⟩
  intro i j hij s hs
  have key : (∀ a : AE D, colMul (rowJac G n hn σ h).jX j a ∈ latV _ (rowN G n) (· = v) →
      colMul (rowJac G n hn σ h).jX i (s * a) ∈ latV _ (rowN G n) (· = v)) ↔
      ∀ a ∈ idV (rowId D n (Fin.castLE (by omega) j)) v, s * a ∈ idV (rowId D n (Fin.castLE (by omega) i)) v :=
    ⟨fun H a ha => (rowJac_line G n hn σ h v i _).1 (H a ((rowJac_line G n hn σ h v j a).2 ha)),
      fun H a hc => (rowJac_line G n hn σ h v i _).2 (H a ((rowJac_line G n hn σ h v j a).1 hc))⟩
  have hne : ∀ p : Fin (D.R.m - 1 - n), rowId D n p ≠ 0 := fun p => mul_ne_zero
    (by
      rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]
      unfold tiltSc
      split_ifs <;> simp [cmHost_imaginaryGenerator_ne_zero])
    (stairId_ne_zero D _ p)
  rw [key, GlobalTheory.IdealQuot.mul_subset_iff D v _ _ (hne _) (hne _) s hs,
    rowId_ratio hodd _ _ (by simp only [Fin.coe_castLE]; exact hij) (by simp only [Fin.coe_castLE]; have := j.2; omega)]
  exact DiffDual.idV_dI_iff D ψ hψ v s hs

theorem big_primAt_rowJac : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ n (hn : n < D.R.m) σ
    (h : D.R.m - 1 - n = 2 * σ) v, GlobalTheory.FinPl.PrimAt ch.W.ψ (rowJac ch.G n hn σ h) (GlobalTheory.RowShape.rowN ch.G n) v :=
  ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ n hn σ h v =>
    primAt_rowJac ch.G ch.W.ψ ch.W.ψ_std n hn σ h v⟩⟩

end GlobalTheory.RowShape
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiFrameOfGridLatticeLargeDepth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

namespace GlobalTheory.FlatPlace

namespace NormalJac

theorem jacobiDualColumn_scalar_identity {K : Type} [Field K] (X : K) (hX : X ≠ 0) (i k : ℕ) :
    (X ^ (i + 1 + k))⁻¹ * (-((-X) ^ (i + 1 + k) * X ^ (i + 1 + k)) / X) * (-1 / X) ^ k = (-X) ^ i := by
  have h1 : ((-1 : K) ^ k) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  rw [neg_pow X, neg_pow X, div_pow]
  field_simp
  linear_combination (X * X ^ i * X ^ k * (-1) ^ i) * h1

theorem mul_col_eq {ι' ι κ μ K : Type} [Fintype ι] [Field K] (P : Matrix ι' ι K) (Y : Matrix ι κ K) (Z : Matrix ι μ K)
    (c : κ) (c' : μ) (h : ∀ l, Y l c = Z l c') (r : ι') : (P * Y) r c = (P * Z) r c' := by
  simp only [mul_apply, h]

theorem hz_besAt {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {t : T} {M : Vol G} (hM : M.Is t)
    (j σ : ℕ) (hj : j + 2 * σ + 2 = D.R.m) (vN : GlobalTheory.Unf.VolN (besDecAt G j σ hj)) {k : Type} [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) :
    p.hz (besAt G hM j σ hj vN) = -((-p.xi) ^ σ * p.xi ^ σ) := by
  simp only [Place.hz, besAt, dotProduct, mulVec]
  show p.pr (∑ i : Fin 1, star (fun _ : Fin 1 => D.host.xi0 ^ σ) i * ∑ i_1 : Fin 1, (GlobalTheory.SeeSaw.Model.nLine D).gram i i_1 * D.host.xi0 ^ σ) = _
  simp only [Fin.sum_univ_one, nLine_gram, Pi.star_apply, star_pow, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, Place.xi, Place.pr, map_mul, map_neg, map_pow, map_one]
  ring

theorem pr_mul' {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)
    (x y : D.host.E) : p.pr (x * y) = p.pr x * p.pr y := map_mul (p.π.comp (incA D)) x y

theorem place_proj_neg_xi_pow {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) (n : ℕ) : p.pr ((-D.host.xi0) ^ n) = (-p.xi) ^ n :=
  (map_pow (p.π.comp (incA D)) _ n).trans (congrArg (· ^ n) (map_neg (p.π.comp (incA D)) _))

theorem neg_mul_neg_one_eq_of_eq {K : Type} [Field K] (y a S : K) (h : S = a) : -(y * a) * -1 = S * y := by rw [h]; ring

end NormalJac

open NormalJac in
set_option maxHeartbeats 1600000 in

theorem big_jacP : Big fun ch => JacP ch := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ hε hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch hsc => ?_⟩⟩
  clear hε hx hsc hch s
  intro t w hw p hp M hM j σ hj vN a ha c hc
  have h1 := ch.S.row t trivial w hw (j + 1) (by omega)
  have hm : (locGrid ch.G t w).m = D.R.m := rfl
  obtain rfl : c = 2 * σ := by
    have h2 := topRank_add (G := locGrid ch.G t w) one_le_sLen (j + 1)
    rw [hm] at h2; omega
  have hpr : ∀ x, p.pr x = algebraMap D.host.E (Kw w) x := fun x =>
    (hp.2.1 _).trans (Comparison₂.cpt_tmul w x)
  have hxi : p.xi ≠ 0 := by
    rw [Place.xi, hpr]; exact (map_ne_zero _).2 (GlobalTheory.Unf.Inhab.cmHost_imaginaryGenerator_ne_zero D)
  have hE : (epsV ch.G t w (D.R.m, j + 1)).val =
      diagonal fun q => if topRank (locGrid ch.G t w) (j + 1) + σ ≤ q.val then -1 else 1 := by
    by_cases hσ : σ = 0
    · subst hσ
      rw [epsV_eq_one _ _ (by omega), Units.val_one]
      ext q q'
      rw [Matrix.one_apply, diagonal_apply, if_neg (show ¬ (topRank (locGrid ch.G t w) (j + 1) + 0 ≤ q.val) by have := q.2; omega)]
    · have hodd : Odd (j + 1) := by
        obtain ⟨b, hb⟩ := D.R.m_even
        exact ⟨j / 2, by omega⟩
      rw [epsV_apply, if_pos (mem_idx.2 ⟨by omega, by omega⟩), sgnAt, GlobalTheory.SplitFlip.diagGL_val]
      congr 1
      funext q
      have e : (D.R.m - 1 - (j + 1)) / 2 = σ := by omega
      simp only [e, hodd, true_and]
      split_ifs <;> simp
  have h₁ : j + 1 < D.R.m := by omega
  have h₂ : D.R.m - 1 - (j + 1) = 2 * σ := by omega
  obtain ⟨T0, T1, T2⟩ : (mt _ a).map p.π * (rowJac ch.G (j + 1) h₁ σ h₂).i₀.map p.pr = (rowJac ch.G (j + 1) h₁ σ h₂).i₀.map p.pr ∧
      (mt _ a).map p.π * (rowJac ch.G (j + 1) h₁ σ h₂).e.map p.pr =
        ((rowJac ch.G (j + 1) h₁ σ h₂).e * diagonal fun a : Fin σ => (D.host.xi0 ^ a.1)⁻¹).map p.pr ∧
      (mt _ a).map p.π * (rowJac ch.G (j + 1) h₁ σ h₂).e'.map p.pr =
        ((rowJac ch.G (j + 1) h₁ σ h₂).e' * diagonal fun a : Fin σ => star (D.host.xi0 ^ a.1)).map p.pr := by
    rcases ha with ⟨rfl, rfl⟩ | ⟨δ, hδ, hδa⟩
    · refine ⟨?_, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
      rw [show mt (ch.G.V (Node.grid D.R.m (j + 1))) 1 = 1 by simp [Formalism.L2.Theta.mt], Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
    · obtain ⟨e0, e1, e2⟩ := hδ.2.2 σ h₁ h₂
      have key : ∀ {n : ℕ} (X Y : Matrix (Fin (ch.G.V (Node.grid D.R.m (j + 1))).rank) (Fin n) D.host.E),
          HMul.hMul (mt _ δ) (X.map (incA D)) = Y.map (incA D) → (mt _ a).map p.π * X.map p.pr = Y.map p.pr := by
        intro n X Y h
        have := congrArg (fun Z => Z.map p.π) h
        simp only [Matrix.map_mul, Matrix.map_map] at this
        rw [hδa]
        exact this
      exact ⟨key _ _ e0, key _ _ e1, key _ _ e2⟩
  have hfl : ∀ {a c b : ℕ} (h : a + c = b) (x : Fin a), ((frame h (Sum.inl x)) : ℕ) = x := by intros; simp [frame]
  have hfr : ∀ {a c b : ℕ} (h : a + c = b) (q : Fin c), ((frame h (Sum.inr q)) : ℕ) = a + q := by intros; simp [frame]
  clear ha
  have T0' : ∀ {n : Type} [Fintype n] (Z : Matrix (Fin (ch.G.V (Node.top (j + 1))).rank) n (Kw w)), (mt _ a).map p.π * ((rowJac ch.G (j + 1) h₁ σ h₂).i₀.map p.pr * Z) =
      (rowJac ch.G (j + 1) h₁ σ h₂).i₀.map p.pr * Z := by
    intro n _ Z; rw [← Matrix.mul_assoc, T0]
  dsimp only [Place.IsJacFrame, jacAt]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro r x
    simp only [mvFr, frRow, frOf, frTop, submatrix_apply, id, hE, mul_diagonal]
    rw [if_neg (by rw [hfl]; omega), mul_one]
    refine (mul_col_eq _ _ ((rowJac ch.G (j + 1) h₁ σ h₂).i₀.map p.pr *
      (loc w (ch.S.βp (j + 1))).val.submatrix id (Fin.cast (topRank_eq ch.G t w h₁.le))) _ x (fun l => ?_) r).trans
      (congrFun (congrFun (T0' _) r) x)
    have e1 := congrFun (congrFun h1 l) (Sum.inl (Fin.cast (topRank_eq ch.G t w h₁.le) x))
    simp only [submatrix_apply, id, fromCols_apply_inl, mul_apply, Matrix.map_apply] at e1
    simp only [submatrix_apply, id, mul_apply, Matrix.map_apply, hpr]
    refine (congrArg _ (Fin.ext ?_)).trans e1
    simp [frame]
  · intro i jj hij r
    simp only [mvFr, frRow, frOf, submatrix_apply, id, hE, mul_diagonal]
    rw [if_neg (by rw [hfr]; omega), mul_one]
    refine (mul_col_eq _ _ ((rowJac ch.G (j + 1) h₁ σ h₂).e.map p.pr) _ i (fun l => ?_) r).trans ?_
    rotate_left
    · rw [T1]
      have hinv : ∀ x : D.host.E, p.π (incA D x⁻¹) = (p.π (incA D x))⁻¹ := fun x => map_inv₀ (p.π.comp (incA D)) x
      simp only [Matrix.map_apply, mul_diagonal, Place.pr, Place.xi, map_mul, hinv, map_pow]
      have hx : p.π (incA D D.host.xi0) ≠ 0 := hxi
      have e : p.π (incA D D.host.xi0) ^ σ = p.π (incA D D.host.xi0) ^ (σ - i.val) * p.π (incA D D.host.xi0) ^ i.val := by
        rw [← pow_add]; congr 1; omega
      rw [e]
      field_simp
    · have e1 := congrFun (congrFun h1 l) (Sum.inr (Fin.cast h₂.symm jj))
      simp only [submatrix_apply, id, fromCols_apply_inr, mul_diagonal, Matrix.map_apply] at e1
      rw [if_neg (Nat.succ_ne_zero j), pow_zero, mul_one, frameSign, if_neg (by simp only [Fin.val_cast]; omega), mul_one] at e1
      simp only [submatrix_apply, id, Matrix.map_apply, hpr]
      refine (congrArg _ (Fin.ext ?_)).trans (e1.trans ?_)
      · simp [frame, topRank_eq ch.G t w h₁.le]
      · have he : (rowJac ch.G (j + 1) h₁ σ h₂).e l i = (ch.G.rowDec (j + 1) h₁).a l (Fin.castLE (by omega) i) := rfl
        rw [he]
        exact congrArg _ (congrArg _ (Fin.ext (by simp; omega)))
  · intro i jj hij r
    simp only [mvFr, frRow, frOf, submatrix_apply, id, hE, mul_diagonal]
    rw [if_pos (by rw [hfr]; omega)]
    refine (congrArg (· * (-1)) (mul_col_eq _ _ (-((rowJac ch.G (j + 1) h₁ σ h₂).e'.map p.pr)) _ i (fun l => ?_) r)).trans ?_
    rotate_left
    · rw [Matrix.mul_neg, Matrix.neg_apply, T2, hz_besAt]
      simp only [Matrix.neg_apply, Matrix.map_apply, mul_diagonal, pr_mul', star_pow, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, place_proj_neg_xi_pow]
      have key := jacobiDualColumn_scalar_identity p.xi hxi i (σ - 1 - i)
      rw [show (i : ℕ) + 1 + (σ - 1 - i) = σ by omega] at key
      exact neg_mul_neg_one_eq_of_eq _ _ _ key
    · have e1 := congrFun (congrFun h1 l) (Sum.inr (Fin.cast h₂.symm jj))
      simp only [submatrix_apply, id, fromCols_apply_inr, mul_diagonal, Matrix.map_apply] at e1
      rw [if_neg (Nat.succ_ne_zero j), pow_zero, mul_one, frameSign, if_pos (by simp only [Fin.val_cast]; omega), mul_neg_one] at e1
      simp only [submatrix_apply, id, Matrix.neg_apply, Matrix.map_apply, hpr]
      refine (congrArg _ (Fin.ext ?_)).trans (e1.trans ?_)
      · simp [frame, topRank_eq ch.G t w h₁.le]
      · simp only [rowJac, jacDec, submatrix_apply, id]
        exact congrArg _ (congrArg _ (congrArg _ (Fin.ext (by simp; omega))))

end GlobalTheory.FlatPlace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiToBesselCarriesFlagLinesRowPeriodSucc
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowShape.ColsJB

variable {D : D7} {A B : HSp D} {c : ℕ}

theorem coreMat_iB' {σ : ℕ} (d : HermitianOrthogonalExtensionData A B c (-1)) (h : c = 2 * σ + 1) :
    coreMat d h * (GlobalTheory.OrthSumExists.orthDecHsum D A (GlobalTheory.SeeSaw.Model.nLine D)).iB = midCol d h := by
  refine (Matrix.submatrix_mul_equiv _ _ _ _ _).trans ?_
  show Matrix.fromCols (frameMat B A d.ι) (midCol d h) *
      Matrix.fromRows (0 : Matrix (Fin A.rank) (Fin 1) D.host.E) (1 : Matrix (Fin 1) (Fin 1) D.host.E) = _
  rw [Matrix.fromCols_mul_fromRows, Matrix.mul_one, Matrix.mul_zero, zero_add]

theorem coreMat_vecB {σ : ℕ} (d : HermitianOrthogonalExtensionData A B c (-1)) (h : c = 2 * σ + 1) (x : D.host.E) :
    coreMat d h *ᵥ vecB (GlobalTheory.OrthSumExists.orthDecHsum D A (GlobalTheory.SeeSaw.Model.nLine D)) (fun _ => x) =
      fun k => x * d.a k ⟨σ, by omega⟩ := by
  show coreMat d h *ᵥ (_ *ᵥ _) = _
  rw [Matrix.mulVec_mulVec, coreMat_iB']
  funext k
  show ∑ j : Fin 1, midCol d h k j * x = _
  simp [midCol, mul_comm]

end GlobalTheory.RowShape.ColsJB

theorem GlobalTheory.RowShape.cols_jacBes_rowN : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ i σ (hi : i + 2 * (σ + 1) + 1 = D.R.m) v, GlobalTheory.FinPl.ColsAt (rowJac ch.G i (by omega) (σ + 1) (by omega))
    (xLast (besDecAt ch.G (i + 1) σ (by omega)) (vecB (GlobalTheory.OrthSumExists.orthDecHsum D (ch.G.V (.top (i + 1))) (GlobalTheory.SeeSaw.Model.nLine D)) fun _ => D.host.xi0 ^ σ))
    (GlobalTheory.RowShape.rowN ch.G i) (GlobalTheory.RowShape.rowN ch.G (i + 1)) v := by
  refine ⟨0, fun _ _ _ => ⟨0, fun D _ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F _ ch _ _ => ?_⟩⟩
  intro i σ hi v a s hs
  have hodd : Odd i := by
    obtain ⟨k, hk⟩ := D.R.m_even
    exact ⟨k - σ - 2, by omega⟩
  unfold GlobalTheory.RowShape.rowN
  rw [dif_pos (by omega), dif_pos (by omega)]
  have hrat : ∀ {m n : ℕ} (N : Matrix (Fin m) (Fin n) D.host.E) (z : Fin n → D.host.E),
      GlobalTheory.MixModel.rat N *ᵥ ratV z = ratV (N *ᵥ z) := by
    intro m n N z
    funext k
    simp [GlobalTheory.MixModel.rat, ratV, Matrix.mulVec, dotProduct, map_sum, map_mul]
  have hL : colMul (rowJac ch.G i (by omega) (σ + 1) (by omega)).jX a s =
      fun k => s * incA D ((ch.G.rowDec i (by omega)).a k ⟨a.1, by omega⟩) := by
    funext k
    rfl
  have hR : colMul (xLast (besDecAt ch.G (i + 1) σ (by omega))
      (vecB (GlobalTheory.OrthSumExists.orthDecHsum D (ch.G.V (.top (i + 1))) (GlobalTheory.SeeSaw.Model.nLine D)) fun _ => D.host.xi0 ^ σ)) a s =
      fun k => (s * incA D (D.host.xi0 ^ a.1)) * incA D ((ch.G.rowDec (i + 1) (by omega)).a k ⟨a.1, by omega⟩) := by
    funext k
    induction a using Fin.lastCases with
    | last =>
      have e1 := GlobalTheory.RowShape.ColsJB.coreMat_vecB (ch.G.rowDec (i + 1) (by omega)) (σ := σ) (by omega) (D.host.xi0 ^ σ)
      simp only [colMul, xLast, Matrix.of_apply, Fin.snoc_last, HypDec.j0, hrat, Fin.val_last]
      show s * ratV ((coreMat (ch.G.rowDec (i + 1) (by omega)) (σ := σ) (by omega)) *ᵥ _) k = _
      rw [e1]
      simp only [ratV, map_mul]
      ring
    | cast b =>
      simp only [colMul, xLast, Matrix.of_apply, Fin.snoc_castSucc, HypDec.jX, GlobalTheory.MixModel.rat, Matrix.map_apply]
      show s * incA D ((Matrix.submatrix (ch.G.rowDec (i + 1) (by omega)).a id (Fin.castLE (by omega)) *
        diagonal (lam (D := D) σ) : Matrix (Fin _) (Fin σ) D.host.E) k b) = _
      rw [Matrix.mul_diagonal, map_mul]
      simp only [lam, Matrix.submatrix_apply, id, Fin.coe_castSucc]
      rw [mul_comm (incA D _) (incA D _), ← mul_assoc]
      rfl
  rw [hL, hR, (GlobalTheory.AscFin.UnitaryEmbeddingLine.embedding_line_mem_lattice_iff _ (neg_ne_zero.2 one_ne_zero) _ _ _ v s).1,
    (GlobalTheory.AscFin.UnitaryEmbeddingLine.embedding_line_mem_lattice_iff _ (neg_ne_zero.2 one_ne_zero) _ _ _ v _).2]
  have hx : D.host.xi0 ^ a.1 ≠ 0 := pow_ne_zero _ (GlobalTheory.Unf.Inhab.cmHost_imaginaryGenerator_ne_zero D)
  have h1 : GlobalTheory.RowShape.rowId D i ⟨a.1, by omega⟩ = FractionalIdeal.spanSingleton _ ((D.host.xi0 ^ a.1)⁻¹) *
      stairId D.host.AA D.host.AAbar (D.R.m - 1 - i) ⟨a.1, by omega⟩ := by
    unfold GlobalTheory.RowShape.rowId GlobalTheory.RowShape.tiltSc
    rw [if_pos hodd, if_pos (by simp only; omega)]
  have h2 : D.host.AA * GlobalTheory.RowShape.rowId D (i + 1) ⟨a.1, by omega⟩ =
      stairId D.host.AA D.host.AAbar (D.R.m - 1 - i) ⟨a.1, by omega⟩ := by
    unfold GlobalTheory.RowShape.rowId GlobalTheory.RowShape.tiltSc
    rw [if_neg (by rw [Nat.not_odd_iff_even]; exact hodd.add_one), FractionalIdeal.spanSingleton_one, one_mul]
    unfold stairId
    rw [show D.R.m - 1 - i - a.1 = (D.R.m - 1 - (i + 1) - a.1) + 1 by omega, pow_succ]
    ring
  rw [h1, h2, idV_spanSingleton_mul_iff D v _ _ (inv_ne_zero hx) s, inv_inv, mul_comm, and_iff_left hs]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastRowCharsUnramifiedOffTensorPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LastRowUnram

theorem chars_unram : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ (t : T) (v : GlobalTheory.FinPl.Pl D), (∀ w ∈ locPl ch.G t, w.under (𝓞 D.host.F) ≠ v) → ∀ i, i < D.R.m →
    GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (ch.G.chrS (.mu t D.R.m i)) v ∧ GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (ch.G.chrT (.mu t D.R.m i)) v := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch _ _ => ?_⟩⟩
  intro t v hv i hi
  classical
  have hL : R.toLevCh.Is A.μ0 := hS.core.lev
  have hS0 := GlobalTheory.RowVacScalar.notMem_S0_of_no_place_above ch.G t hv
  have hQ : ∀ PP ∈ R.toLevCh.Q t, PP ∈ locPl ch.G t := fun PP h => by
    unfold locPl
    exact Finset.mem_union_right _ h
  have hmu : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (R.toLevCh.mu t (i + 1)) v := by
    refine GlobalTheory.SeeSaw.LevelTest.charUnramAt_of fun w hw => ?_
    show GlobalTheory.LFun.UnrAt (R.toLevCh.mu0 (i + 1) * R.toLevCh.xi t) w
    refine GlobalTheory.LFun.UnrAt.mul ?_ ?_
    · refine (GlobalTheory.LFun.unrAt_iff_of_chrEq (hL.mu0 ⟨i, hi⟩) w).2 ((R.toLevCh.C.isMu0 ⟨i, hi⟩).unr w fun k hk => ?_)
      refine hS0 (ch.G.pl.mem_S0_of_sum_eq.2 (Or.inr ((GlobalTheory.ChiGrid.S1_mem_OmF D).2 ?_)))
      have : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (w.under (𝓞 D.host.F)).asIdeal := by
        show algebraMap _ (𝓞 D.host.E) _ ∈ w.asIdeal
        rw [map_natCast]; exact hk
      rw [hw] at this
      fin_cases k
      · exact Or.inl this
      · exact Or.inr (Or.inl this)
    · refine (GlobalTheory.LFun.unrAt_iff_of_chrEq (hL.xi t) w).2 ?_
      by_contra hu
      rcases (hL.Q_ram t w).1 hu with h | ⟨P', hP', hc⟩
      · exact hv w (hQ w h) hw
      · exact hv P' (hQ P' hP') ((GlobalTheory.LevelPlaces.under_eq_of_isConjPl hc).trans hw)
  have key := GlobalTheory.RowVacScalar.attChr_charUnramAt hmu (GlobalTheory.RowVacScalar.eta_charUnramAt hL v)
  exact ⟨key _, key _⟩

end GlobalTheory.LastRowUnram
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastRowRealIteratedIntegralEqConstMulFiniteStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastRow_real_iterated_integral_eq_const_mul_finite : CellVan → Big fun ch => GrpAt ch → IterAt ch → LinAt ch → InvAt ch → (∃ s, SuppOn ch s ∧ RepAt ch s ∧ ValAt ch s) → RealLine ch → (∀ t a, ch.S.SumOK t (ch.Phi a)) → UnfoldAt ch := by
  first | exact @GlobalTheory.RowRealInt.unfold_of_steps | exact GlobalTheory.RowRealInt.unfold_of_steps | (intros; apply GlobalTheory.RowRealInt.unfold_of_steps <;> assumption)
end

