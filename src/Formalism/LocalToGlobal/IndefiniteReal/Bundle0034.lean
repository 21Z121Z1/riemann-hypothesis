import Formalism.LocalToGlobal.IndefiniteReal.Bundle0033
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0020
import Formalism.LocalRingCardinality.Bundle0005
import Formalism.SharpRestriction.Divisibility.FunctionModelRallisFromInputs
import Mathlib
import Formalism.SharpRestriction.AdmissibleParameterJoins.SfromGLw
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ZuckermanTensor.DiscreteSeriesHolds
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.HarishChandraMultiplicityBound
import Formalism.LocalToGlobal.IndefiniteReal.SchurOrthogonality
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.WeylBridge

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.DiscreteSeriesParameterPos
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult Matrix

namespace Formalism.IndefR.DiscreteSeriesPlaces

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem lamAt_of_b {R : Ranks} (hc : HCParam R) (c : ℕ) (h1 : R.k - 1 ≤ c) (h2 : c - (R.k - 1) < R.m) :
    lamAt hc c = -hc.b ⟨c - (R.k - 1), h2⟩ := by
  unfold lamAt
  rw [dif_neg (by omega), dif_pos h2]

theorem lamAt_anti {R : Ranks} (hc : HCParam R) {d c : ℕ} (hdc : d ≤ c) (hc' : c < R.r) :
    lamAt hc c ≤ lamAt hc d := by
  have := lamAt_add_add_le hc (c - d) d (by omega)
  rw [show d + (c - d) = c by omega] at this
  have h0 : (0 : ℚ) ≤ ((c - d : ℕ) : ℚ) := by positivity
  linarith

theorem gap_minus {R : Ranks} (hc : HCParam R) (h : ℝ)
    (hb : ∀ (j j' : ℕ) (hj : j < R.m) (hj' : j' < R.m), j' = j + 1 → h ≤ ((hc.b ⟨j', hj'⟩ - hc.b ⟨j, hj⟩ : ℚ) : ℝ))
    (c d : ℕ) (hcr : c < R.r) (hdr : d < R.r) (hcs : sgA R c = false) (hdc : d ≠ c) :
    h ≤ |((lamAt hc d : ℚ) : ℝ) - ((lamAt hc c : ℚ) : ℝ)| := by
  have hrr : R.r = R.k + R.m - 1 := rfl
  have hk := R.m_add_three_le_k
  unfold sgA at hcs
  simp only [decide_eq_false_iff_not, not_or, not_lt, Nat.not_even_iff_odd] at hcs
  obtain ⟨hc1, ⟨i, hi⟩⟩ := hcs
  have hcm : c - (R.k - 1) < R.m := by omega
  have hlc := lamAt_of_b hc c hc1 hcm
  rcases Nat.lt_or_gt_of_ne hdc with hlt | hgt
  · have hm1 : c - 1 - (R.k - 1) < R.m := by omega
    have hl1 := lamAt_of_b hc (c - 1) (by omega) hm1
    have hmono := lamAt_anti hc (show d ≤ c - 1 by omega) (by omega)
    have hg := hb (c - 1 - (R.k - 1)) (c - (R.k - 1)) hm1 hcm (by omega)
    have hmono' : ((lamAt hc (c - 1) : ℚ) : ℝ) ≤ ((lamAt hc d : ℚ) : ℝ) := by exact_mod_cast hmono
    rw [hl1] at hmono'
    rw [hlc]
    push_cast at hg hmono' ⊢
    exact le_trans (by linarith) (le_abs_self _)
  · have hm1 : c + 1 - (R.k - 1) < R.m := by omega
    have hl1 := lamAt_of_b hc (c + 1) (by omega) hm1
    have hmono := lamAt_anti hc (show c + 1 ≤ d by omega) hdr
    have hg := hb (c - (R.k - 1)) (c + 1 - (R.k - 1)) hcm hm1 (by omega)
    have hmono' : ((lamAt hc d : ℚ) : ℝ) ≤ ((lamAt hc (c + 1) : ℚ) : ℝ) := by exact_mod_cast hmono
    rw [hl1] at hmono'
    rw [hlc]
    push_cast at hg hmono' ⊢
    exact le_trans (by linarith) (neg_le_abs _)

theorem isEnum_dual {n : ℕ} {S : SPar} {lam : Fin n → ℝ} {ε : Fin n → Bool} (h : IsEnum S lam ε) :
    IsEnum (dualPar S) (fun a => -lam (Fin.rev a)) (fun a => ε (Fin.rev a)) := by
  obtain ⟨hanti, Q, hQ, rfl⟩ := h
  refine ⟨fun a b hab => neg_lt_neg (hanti (Fin.rev_lt_rev.mpr hab)), fun a => -Q (Fin.rev a),
    fun a => by simp [hQ], ?_⟩
  unfold dualPar
  rw [Finset.image_image]
  ext ⟨x, s⟩
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply, Prod.mk.injEq]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨Fin.rev a, by simpa using ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨_, ha⟩

theorem exists_enumB (D : D7) (h : ℝ) (hN : D.NodeGap h) (τ : D.what₂.Tau) (n : ℕ) (hn : n = D.R.r) :
    ∃ (lam : Fin n → ℝ) (ε : Fin n → Bool), IsEnum (parB (tparRec D) 0 τ) lam ε ∧ Formalism.QuantumDeterminants.IsHCParam lam ∧
      Formalism.QuantumDeterminants.GapAtLeast ε lam h ∧ (Finset.univ.filter fun a => ε a = true).card = D.R.sigY0.1 ∧
      (Finset.univ.filter fun a => ε a = false).card = D.R.sigY0.2 := by
  subst hn
  have hb : ∀ (j j' : ℕ) (hj : j < D.R.m) (hj' : j' < D.R.m), j' = j + 1 →
      h ≤ (((D.hc τ).b ⟨j', hj'⟩ - (D.hc τ).b ⟨j, hj⟩ : ℚ) : ℝ) := by
    intro j j' hj hj' e
    subst e
    have := hN D.u₀ τ j hj'
    rwa [D.hcW_base] at this
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  obtain ⟨c, hc⟩ := D.R.m_even
  have hcnt : (Finset.univ.filter fun a : Fin D.R.r => sgA D.R (Fin.rev a) = true).card =
      (Finset.univ.filter fun a : Fin D.R.r => sgA D.R a = true).card :=
    Finset.card_equiv Fin.revPerm (by intro i; simp)
  have hA : (Finset.univ.filter fun a : Fin D.R.r => sgA D.R (Fin.rev a) = true).card = D.R.k - 1 + D.R.m / 2 :=
    hcnt.trans (card_sgA D.R)
  refine ⟨fun a => -((lamAt (D.hc τ) (Fin.rev a) : ℚ) : ℝ), fun a => sgA D.R (Fin.rev a), ?_, ?_, ?_, ?_, ?_⟩
  · show IsEnum (dualPar (parA (tparHC D _ _) 0 τ)) _ _
    rw [parA_eq]
    exact isEnum_dual (lam := fun a => ((lamAt (D.hc τ) a : ℚ) : ℝ))
      ⟨fun _ _ h => by dsimp only; exact_mod_cast lamAt_strictAnti _ h, fun a => lamAt (D.hc τ) a,
        fun _ => rfl, rfl⟩
  · refine ⟨fun a b hab => neg_lt_neg ?_, fun a => ?_⟩
    · exact_mod_cast lamAt_strictAnti (D.hc τ) (Fin.rev_lt_rev.mpr hab)
    · obtain ⟨z, hz⟩ := lamAt_half (D.hc τ) (Fin.rev a)
      refine ⟨-z - ((D.R.r : ℤ) - 1), ?_⟩
      push_cast
      linarith
  · intro a b hab
    dsimp only at hab ⊢
    have hne : (Fin.rev a : ℕ) ≠ (Fin.rev b : ℕ) := by
      intro e
      apply hab
      rw [Fin.ext e]
    have e1 : -((lamAt (D.hc τ) (Fin.rev a) : ℚ) : ℝ) - -((lamAt (D.hc τ) (Fin.rev b) : ℚ) : ℝ) =
        ((lamAt (D.hc τ) (Fin.rev b) : ℚ) : ℝ) - ((lamAt (D.hc τ) (Fin.rev a) : ℚ) : ℝ) := by ring
    rw [e1]
    cases ha : sgA D.R (Fin.rev a)
    · exact gap_minus (D.hc τ) h hb _ _ (Fin.rev a).2 (Fin.rev b).2 ha (Ne.symm hne)
    · have hbf : sgA D.R (Fin.rev b) = false := by
        rw [ha] at hab
        cases hh : sgA D.R (Fin.rev b)
        · rfl
        · exact absurd hh.symm hab
      rw [abs_sub_comm]
      exact gap_minus (D.hc τ) h hb _ _ (Fin.rev b).2 (Fin.rev a).2 hbf hne
  · rw [hA]; simp only [Ranks.sigY0, Ranks.rS]; omega
  · rw [card_false_eq, hA]; simp only [Ranks.sigY0, Ranks.rS, Ranks.r]; omega

theorem big_rec (D : D7) (n : ℕ) (hn : n = D.R.r) (ε : Fin n → Bool) :
    max (2 * (n : ℝ)) (8 * (n : ℝ) * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ)) <
      4 * (D.R.N D.R.m : ℝ) ^ 3 + 2 * D.R.t + 6 := by
  have hk := D.R.m_add_three_le_k
  have hq : ReciprocityTheory.ChartRestriction.DS.S7.q0 ε ≤ n := by
    unfold ReciprocityTheory.ChartRestriction.DS.S7.q0 ReciprocityTheory.ChartRestriction.DS.pOf
    refine le_trans (min_le_left _ _) ?_
    refine le_trans (Finset.card_filter_le _ _) ?_
    simp
  have hnN : n ≤ D.R.N D.R.m := by
    subst hn
    unfold Ranks.r Ranks.N
    have : D.R.m ≤ D.R.m * (D.R.t + 1) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have h2N : 2 ≤ D.R.N D.R.m := by unfold Ranks.N; omega
  have hqR : (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ) ≤ n := by exact_mod_cast hq
  have hnR : (n : ℝ) ≤ D.R.N D.R.m := by exact_mod_cast hnN
  have h2R : (2 : ℝ) ≤ D.R.N D.R.m := by exact_mod_cast h2N
  have ht : (0 : ℝ) ≤ D.R.t := by positivity
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hq0 : (0 : ℝ) ≤ (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ) := by positivity
  set x : ℝ := (D.R.N D.R.m : ℝ)
  have hx2 : 8 * x ^ 2 ≤ 4 * x ^ 3 := by nlinarith
  have hsq : 8 * (n : ℝ) * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ) ≤ 8 * x ^ 2 := by
    have : (n : ℝ) * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ) ≤ x * x := mul_le_mul hnR (hqR.trans hnR) hq0 (by linarith)
    nlinarith
  refine max_lt ?_ ?_
  · nlinarith
  · linarith

section Rec

variable (D : D7) (τ : D.what₂.Tau)

end Rec

section Rec2

variable (D : D7) (τ : D.what₂.Tau)

end Rec2

theorem isHCParam_dual {n : ℕ} {lam : Fin n → ℝ} (h : Formalism.QuantumDeterminants.IsHCParam lam) :
    Formalism.QuantumDeterminants.IsHCParam (fun a => -lam (Fin.rev a)) := by
  obtain ⟨hanti, hint⟩ := h
  refine ⟨fun a b hab => neg_lt_neg (hanti (Fin.rev_lt_rev.mpr hab)), fun a => ?_⟩
  obtain ⟨z, hz⟩ := hint (Fin.rev a)
  refine ⟨-z - ((n : ℤ) - 1), ?_⟩
  push_cast
  linarith

theorem gap_dual {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {h : ℝ} (hg : Formalism.QuantumDeterminants.GapAtLeast ε lam h) :
    Formalism.QuantumDeterminants.GapAtLeast (fun a => ε (Fin.rev a)) (fun a => -lam (Fin.rev a)) h := by
  intro a b hab
  have := hg (Fin.rev a) (Fin.rev b) hab
  rw [show -lam (Fin.rev a) - -lam (Fin.rev b) = -(lam (Fin.rev a) - lam (Fin.rev b)) by ring, abs_neg]
  exact this

end Formalism.IndefR.DiscreteSeriesPlaces

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.ModelConjugation
section
noncomputable section

open Matrix
open scoped InnerProductSpace ComplexConjugate

namespace Formalism.IndefR.ModelConjugation

open PI.ZuckTensorWork

variable {n : ℕ}

def toCj (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] : H ≃ₗᵢ⋆[ℂ] Cj H where
  toFun := Cj.mk
  invFun := Cj.un
  map_add' _ _ := rfl
  map_smul' c x := Cj.mk_smul c x
  left_inv _ := rfl
  right_inv _ := rfl
  norm_map' _ := rfl

theorem conjDS_unique (ε : Fin n → Bool) (lam : Fin n → ℝ) (hlam : Formalism.QuantumDeterminants.IsHCParam lam) (h : ℝ)
    (hgap : Formalism.QuantumDeterminants.GapAtLeast ε lam h) (hbig : 2 * (n : ℝ) < h)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (hσ : Formalism.MainNotions.S.IsDS ε lam σ)
    (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
    (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')) (hσ' : Formalism.MainNotions.S.IsDS (revE ε) (revP lam) σ') :
    ∃ U : H ≃ₗᵢ⋆[ℂ] H', ∀ m ∈ Formalism.MainNotions.S.UJset ε, ∀ x, U (σ m x) = σ' (revM m) (U x) := by
  have hC : Formalism.MainNotions.S.IsDS (revE ε) (revP lam) (sigC σ) := discrete_series_holds n ε H σ lam hσ
  have hlam' : Formalism.QuantumDeterminants.IsHCParam (revP lam) := harish_chandra_holds n lam hlam
  have hgap' : Formalism.QuantumDeterminants.GapAtLeast (revE ε) (revP lam) h := spectral_gap_holds n ε lam h hgap
  obtain ⟨-, -, -, -, hU⟩ := ReciprocityTheory.ChartRestriction.DS.G2.discrete_series_props_large_gap n (revE ε) (revP lam) hlam' h hgap' hbig
    (Cj H) (sigC σ) hC
  obtain ⟨U', hU'⟩ := hU H' σ' hσ'
  refine ⟨(toCj H).trans U', fun m hm x => ?_⟩
  have hm' : revM m ∈ Formalism.MainNotions.S.UJset (revE ε) := revM_mem_UJset' hm
  have e1 : Cj.mk (σ m x) = sigC σ (revM m) (Cj.mk x) := by
    show Cj.mk (σ m x) = cjOp (σ (revM (revM m))) (Cj.mk x)
    rw [revM_revM]
    rfl
  show U' (Cj.mk (σ m x)) = σ' (revM m) (U' (Cj.mk x))
  rw [e1, hU' _ hm']

def Rm (n : ℕ) : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => if j = Fin.rev i then 1 else 0

theorem revM_eq_Rm (m : Matrix (Fin n) (Fin n) ℂ) : revM m = Rm n * m * Rm n := by
  ext i j
  simp only [revM, Rm, Matrix.submatrix_apply, Matrix.mul_apply, Matrix.of_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (Fin.rev j)]
  · simp
  · intro b _ hb
    rw [if_neg]
    intro h
    exact hb (by rw [h, Fin.rev_rev])
  · simp

theorem Rm_mul_self : Rm n * Rm n = 1 := by
  have h := revM_eq_Rm (1 : Matrix (Fin n) (Fin n) ℂ)
  rw [revM_one, Matrix.mul_one] at h
  exact h.symm

theorem Rm_conjTranspose : (Rm n)ᴴ = Rm n := by
  ext i j
  simp only [Rm, conjTranspose_apply, Matrix.of_apply]
  by_cases h : i = Fin.rev j
  · rw [if_pos h, if_pos (by rw [h, Fin.rev_rev]), star_one]
  · rw [if_neg h, if_neg (fun h' => h (by rw [h', Fin.rev_rev])), star_zero]

theorem lowKSub_kStable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin n → Bool) (lam : Fin n → ℝ)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) :
    Formalism.MainNotions.S.IsKStableOn ε σ (Formalism.MainNotions.S.lowKSub ε lam σ) := by
  intro g hg x hx
  have hle : Formalism.MainNotions.S.lowKSub ε lam σ ≤ (Formalism.MainNotions.S.lowKSub ε lam σ).comap (σ g : H →ₗ[ℂ] H) := by
    apply sSup_le
    intro S hS y hy
    exact le_sSup hS (hS.2.1 g hg y hy)
  exact hle hx

theorem conjDS_frame {N : ℕ} (hN : N = n) (εX : Fin n → Bool) (lamX : Fin n → ℝ) (hlam : Formalism.QuantumDeterminants.IsHCParam lamX)
    (h : ℝ) (hgap : Formalism.QuantumDeterminants.GapAtLeast εX lamX h) (hbig : 2 * (n : ℝ) < h)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (hσ : Formalism.MainNotions.S.IsDS εX lamX σ)
    (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
    (σ' : Matrix (Fin N) (Fin N) ℂ → (H' →L[ℂ] H')) (εM : Fin N → Bool) (lamM : Fin N → ℝ)
    (hσ' : Formalism.MainNotions.S.IsDS εM lamM σ')
    (hε : ∀ a, εM a = εX (Fin.rev (finCongr hN a))) (hl : ∀ a, lamM a = -lamX (Fin.rev (finCongr hN a)))
    (A : Matrix (Fin N) (Fin n) ℂ) (A' : Matrix (Fin n) (Fin N) ℂ) (h1 : A * A' = 1) (h2 : A' * A = 1)
    (hJ : Aᴴ * PI.UpqRep.Jm εM * A = PI.UpqRep.Jm εX) :
    ∃ U : H ≃ₗᵢ⋆[ℂ] H', (∀ m ∈ Formalism.MainNotions.S.UJset εX, ∀ x, U (σ m x) = σ' (A * m * A') (U x)) ∧
      ∃ k ∈ Formalism.MainNotions.S.UJset εM, ∃ W : Submodule ℂ H', FiniteDimensional ℂ W ∧ Formalism.MainNotions.S.IsKStableOn εM σ' W ∧
        ∀ w ∈ Formalism.MainNotions.S.lowKSub εX lamX σ, ∃ w' ∈ W, U w = σ' k w' := by
  subst hN
  have eε : εM = revE εX := funext fun a => by rw [hε a]; rfl
  have el : lamM = revP lamX := funext fun a => by rw [hl a]; rfl
  subst eε el
  obtain ⟨U0, hU0⟩ := conjDS_unique εX lamX hlam h hgap hbig H σ hσ H' σ' hσ'

  set k : Matrix (Fin N) (Fin N) ℂ := A * Rm N with hk
  set k' : Matrix (Fin N) (Fin N) ℂ := Rm N * A' with hk'
  have hkk' : k * k' = 1 := by
    rw [hk, hk', Matrix.mul_assoc, ← Matrix.mul_assoc (Rm N), Rm_mul_self, Matrix.one_mul, h1]
  have hk'k : k' * k = 1 := by
    rw [hk, hk', Matrix.mul_assoc, ← Matrix.mul_assoc A', h2, Matrix.one_mul, Rm_mul_self]
  have hkU : k ∈ Formalism.MainNotions.S.UJset (revE εX) := by
    show kᴴ * PI.UpqRep.Jm (revE εX) * k = PI.UpqRep.Jm (revE εX)
    rw [hk, conjTranspose_mul, Rm_conjTranspose]
    calc Rm N * Aᴴ * PI.UpqRep.Jm (revE εX) * (A * Rm N) = Rm N * (Aᴴ * PI.UpqRep.Jm (revE εX) * A) * Rm N := by
          simp only [Matrix.mul_assoc]
      _ = PI.UpqRep.Jm (revE εX) := by rw [hJ, ← revM_eq_Rm, revM_Jm]
  have ujMul : ∀ a b : Matrix (Fin N) (Fin N) ℂ, a ∈ Formalism.MainNotions.S.UJset (revE εX) → b ∈ Formalism.MainNotions.S.UJset (revE εX) →
      a * b ∈ Formalism.MainNotions.S.UJset (revE εX) := by
    intro a b ha hb
    have ha' : aᴴ * PI.UpqRep.Jm (revE εX) * a = PI.UpqRep.Jm (revE εX) := ha
    have hb' : bᴴ * PI.UpqRep.Jm (revE εX) * b = PI.UpqRep.Jm (revE εX) := hb
    show (a * b)ᴴ * PI.UpqRep.Jm (revE εX) * (a * b) = PI.UpqRep.Jm (revE εX)
    calc (a * b)ᴴ * PI.UpqRep.Jm (revE εX) * (a * b) = bᴴ * (aᴴ * PI.UpqRep.Jm (revE εX) * a) * b := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = PI.UpqRep.Jm (revE εX) := by rw [ha', hb']
  have hk'U : k' ∈ Formalism.MainNotions.S.UJset (revE εX) := by
    have hk0 : kᴴ * PI.UpqRep.Jm (revE εX) * k = PI.UpqRep.Jm (revE εX) := hkU
    show k'ᴴ * PI.UpqRep.Jm (revE εX) * k' = PI.UpqRep.Jm (revE εX)
    calc k'ᴴ * PI.UpqRep.Jm (revE εX) * k' = k'ᴴ * (kᴴ * PI.UpqRep.Jm (revE εX) * k) * k' := by rw [hk0]
      _ = (k * k')ᴴ * PI.UpqRep.Jm (revE εX) * (k * k') := by simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = PI.UpqRep.Jm (revE εX) := by rw [hkk', conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have hrep := hσ'.2.2.1
  have hmul : ∀ a b, a ∈ Formalism.MainNotions.S.UJset (revE εX) → b ∈ Formalism.MainNotions.S.UJset (revE εX) → ∀ y,
      σ' (a * b) y = σ' a (σ' b y) := by
    intro a b ha hb y
    rw [hrep.1.2 a ha b hb]
    rfl
  have hone : ∀ y, σ' 1 y = y := by intro y; rw [hrep.1.1]; rfl

  let Lk : H' →ₗᵢ[ℂ] H' := ⟨(σ' k : H' →ₗ[ℂ] H'), hrep.2.1 k hkU⟩
  have hLk : Function.Surjective Lk := fun y => ⟨σ' k' y, by
    show σ' k (σ' k' y) = y
    rw [← hmul k k' hkU hk'U, hkk', hone]⟩
  refine ⟨U0.trans (LinearIsometryEquiv.ofSurjective Lk hLk), ?_, ?_⟩
  · intro m hm x
    have hmr : revM m ∈ Formalism.MainNotions.S.UJset (revE εX) := revM_mem_UJset' hm
    have hAm : A * m * A' = k * revM m * k' := by
      rw [revM_eq_Rm, hk, hk']
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (Rm N) (Rm N), Rm_mul_self, Matrix.one_mul, ← Matrix.mul_assoc (Rm N) (Rm N),
        Rm_mul_self, Matrix.one_mul]
    show σ' k (U0 (σ m x)) = σ' (A * m * A') (σ' k (U0 x))
    rw [hU0 m hm x, hAm, ← hmul _ _ (ujMul _ _ (ujMul _ _ hkU hmr) hk'U) hkU, Matrix.mul_assoc (k * revM m),
      hk'k, Matrix.mul_one, hmul _ _ hkU hmr]
  · refine ⟨k, hkU, (Formalism.MainNotions.S.lowKSub εX lamX σ).map (U0 : H →ₛₗ[starRingEnd ℂ] H'), ?_, ?_, ?_⟩
    · have hfin := (ReciprocityTheory.ChartRestriction.DS.G2.discrete_series_props_large_gap _ εX lamX hlam h hgap hbig H σ hσ).2.2.1
        (Formalism.QuantumDeterminants.lowK εX lamX)
      have hfg : (Formalism.MainNotions.S.lowKSub εX lamX σ).FG := (Submodule.fg_iff_finiteDimensional _).2 hfin
      exact (Submodule.fg_iff_finiteDimensional _).1 (hfg.map _)
    · rintro g hg _ ⟨x, hx, rfl⟩
      have hm : revM g ∈ Formalism.REAL.Kset εX := revM_mem_Kset hg
      have hmU : revM g ∈ Formalism.MainNotions.S.UJset εX := ReciprocityTheory.ChartRestriction.DS.HW.hw_kset_subset εX hm
      refine ⟨σ (revM g) x, lowKSub_kStable εX lamX σ (revM g) hm x hx, ?_⟩
      show U0 (σ (revM g) x) = σ' g (U0 x)
      rw [hU0 _ hmU x, revM_revM]
    · intro w hw
      exact ⟨U0 w, Submodule.mem_map_of_mem hw, rfl⟩

section Rec

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

def ModelConjAt (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (M : Formalism.IndefR.Mult.DSModel V S) (v : NumberField.InfinitePlace X.B.I.F)
    (τ : D.what₂.Tau) (A : Matrix (Fin V.rank) (Fin X.B.I.n) ℂ) (A' : Matrix (Fin X.B.I.n) (Fin V.rank) ℂ) : Prop :=
  ∃ U : X.B.H v ≃ₗᵢ⋆[ℂ] M.H τ,
    (∀ m ∈ Formalism.MainNotions.S.UJset (X.B.I.ε v), ∀ x, U (X.B.σ v m x) = M.σ τ (A * m * A') (U x)) ∧
    U (X.B.w v) ∈ M.sm τ ∧ ‖U (X.B.w v)‖ = 1

theorem modelConjAt_of (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (M : Formalism.IndefR.Mult.DSModel V S)
    (v : NumberField.InfinitePlace X.B.I.F) (τ : D.what₂.Tau) (hN : V.rank = X.B.I.n)
    (hlamX : Formalism.QuantumDeterminants.IsHCParam (X.B.lam v)) (hX : ℝ) (hgapX : Formalism.QuantumDeterminants.GapAtLeast (X.B.I.ε v) (X.B.lam v) hX)
    (hbigX : 2 * (X.B.I.n : ℝ) < hX)
    (hlamM : Formalism.QuantumDeterminants.IsHCParam (M.lam τ)) (hM : ℝ) (hgapM : Formalism.QuantumDeterminants.GapAtLeast (M.ε τ) (M.lam τ) hM)
    (hbigM : 2 * (V.rank : ℝ) < hM)
    (hε : ∀ a, M.ε τ a = X.B.I.ε v (Fin.rev (finCongr hN a)))
    (hl : ∀ a, M.lam τ a = -X.B.lam v (Fin.rev (finCongr hN a)))
    (A : Matrix (Fin V.rank) (Fin X.B.I.n) ℂ) (A' : Matrix (Fin X.B.I.n) (Fin V.rank) ℂ) (h1 : A * A' = 1)
    (h2 : A' * A = 1) (hJ : Aᴴ * PI.UpqRep.Jm (M.ε τ) * A = PI.UpqRep.Jm (X.B.I.ε v)) :
    ModelConjAt X M v τ A A' := by
  have hdsM := M.ds τ
  haveI : CompleteSpace (M.H τ) := hdsM.1
  obtain ⟨U, hU, k, hk, W, hWf, hWK, hlow⟩ := conjDS_frame hN (X.B.I.ε v) (X.B.lam v) hlamX hX hgapX hbigX
    (X.B.H v) (X.B.σ v) (X.ds v) (M.H τ) (M.σ τ) (M.ε τ) (M.lam τ) hdsM hε hl A A' h1 h2 hJ
  obtain ⟨w', hw', hUw⟩ := hlow (X.B.w v) (X.low v).2
  refine ⟨U, hU, ?_, by rw [LinearIsometryEquiv.norm_map]; exact (X.low v).1⟩

  have hsm := (ReciprocityTheory.ChartRestriction.DS.G2.discrete_series_props_large_gap V.rank (M.ε τ) (M.lam τ) hlamM hM hgapM hbigM (M.H τ) (M.σ τ)
    hdsM).2.2.2.1 W hWf hWK w' hw'
  have hw'sm : w' ∈ M.sm τ := Submodule.subset_span
    (Formalism.IndefR.PeterssonHilbertSpace.sm_transfer (M.ε τ) (M.σ τ) (M.fr τ) _ (M.fr_unit τ) (M.fr_gram τ) (lieAt V τ)
      (fun X hX => hX) w' (Formalism.IndefR.LowestKTypeSmoothness.smoothOnH_of_isSmoothVecU (M.ε τ) (M.σ τ) w' hsm))

  have hfr : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have hk' : kᴴ * Formalism.REAL.Jm (M.ε τ) * k = Formalism.REAL.Jm (M.ε τ) := hk
  have hkdet : IsUnit k.det := by
    have hJd : (Formalism.REAL.Jm (M.ε τ)).det ≠ 0 := by
      have := congrArg Matrix.det (Formalism.REAL.Jm_mul_self (M.ε τ))
      intro h0; rw [det_mul, h0, mul_zero, det_one] at this; exact zero_ne_one this
    have := congrArg Matrix.det hk'
    rw [det_mul, det_mul] at this
    refine isUnit_iff_ne_zero.2 fun h0 => hJd ?_
    rw [h0, mul_zero] at this
    exact this.symm
  set g0 : Matrix (Fin V.rank) (Fin V.rank) ℂ := (M.fr τ)⁻¹ * k * M.fr τ with hg0
  have hg0u : IsUnit g0 := by
    rw [Matrix.isUnit_iff_isUnit_det, hg0, det_mul, det_mul]
    exact ((isUnit_nonsing_inv_det _ hfr).mul hkdet).mul hfr
  have hg0mem : g0 ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
    show g0ᴴ * gramAt D V τ * g0 = gramAt D V τ
    rw [← M.fr_gram τ, hg0]
    have hfrh : IsUnit (M.fr τ)ᴴ.det := by rw [det_conjTranspose]; exact hfr.star
    calc ((M.fr τ)⁻¹ * k * M.fr τ)ᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * ((M.fr τ)⁻¹ * k * M.fr τ)
        = (M.fr τ)ᴴ * kᴴ * (((M.fr τ)ᴴ)⁻¹ * (M.fr τ)ᴴ) * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) * k *
            M.fr τ := by
          rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_nonsing_inv]; simp only [Matrix.mul_assoc]
      _ = (M.fr τ)ᴴ * (kᴴ * Formalism.REAL.Jm (M.ε τ) * k) * M.fr τ := by
          rw [Matrix.nonsing_inv_mul _ hfrh, Matrix.mul_nonsing_inv _ hfr]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = _ := by rw [hk']
  let g : Formalism.IndefR.SchurOrthogonalityAlt.Gt V τ := ⟨hg0u.unit, hg0mem⟩
  have hrep : M.rep τ (Formalism.IndefR.SchurOrthogonalityAlt.gm g) = M.σ τ k := by
    show M.σ τ (M.fr τ * g0 * (M.fr τ)⁻¹) = M.σ τ k
    congr 1
    rw [hg0]
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv _ hfr, Matrix.mul_one, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hfr, Matrix.one_mul]
  rw [hUw, ← hrep]
  exact Formalism.IndefR.SchurOrthogonalityAlt.sm_stable M τ g hw'sm

end Rec

end Formalism.IndefR.ModelConjugation
end
end

