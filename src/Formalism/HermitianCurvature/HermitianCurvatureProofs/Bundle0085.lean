import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0079
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0045
import Formalism.HermitianCurvature.HermitianCurvatureProofs.QxChain
import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LUFactorOrbitBounds

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftOfLocal
section
open Finset NumberField
open scoped ComplexConjugate ComplexOrder

namespace Formalism.FourierDecayAlt.P.PBA

open Formalism.FourierDecayAlt

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

def lpt (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (s : ℕ) (t : E) (h : TB.Pt E) : C.LPt :=
  C.loc (S.σ v) h ++ [(s, S.σ v t)]

theorem re_real_sum {W : Type} (c : ℝ) (Ws : Finset W) (p : W → ℝ) (N : W → ℂ) :
    ((c : ℂ) * ∑ w ∈ Ws, (p w : ℂ) * N w).re = c * ∑ w ∈ Ws, p w * (N w).re := by
  rw [Complex.re_ofReal_mul, Complex.re_sum]
  simp only [Complex.re_ofReal_mul]

theorem liftOfLoc_statement : KB.LiftOfLoc := by
  intro E _ _ _ Wp Wq _ _ _ _ S Λ hpos _ _ hloc
  intro ε hε i s hs hsi hir w _ hcnt
  have hcnt' : w.1.cnt + C.Kst ≤ S.Ntop := hcnt
  have hlen : ∀ v, (w.1 v).length + C.Kst ≤ S.Ntop := fun v => by
    have := len_le_cnt S w.1 v; omega
  have hb1 : 1 ≤ i - s + 1 := by omega
  have hbs : i - s + 1 + s ≤ S.G.r + 1 := by omega
  have hlev : i - s + 1 + s - 1 = i := by omega
  have hi : i ≤ S.G.r + 1 := by omega
  have hwn : w.1.cnt ≤ w.1.cnt + C.Kst := by omega
  have hL := fun v => hloc v (i - s + 1) s hb1 hs hbs (w.1 v) ⟨w, rfl⟩ (hlen v)
  simp only [hlev] at hL
  choose Up θp Um θm hPp hPm hblk using hL
  have hUp : ∀ v, ∀ a ∈ Up v, D.AdmAt S v a ∧ a.length ≤ w.1.cnt + C.Kst := fun v a ha =>
    ⟨((hPp v).2 a ha).1, ((hPp v).2 a ha).2.trans (by have := len_le_cnt S w.1 v; omega)⟩
  have hUm : ∀ v, ∀ a ∈ Um v, D.AdmAt S v a ∧ a.length ≤ w.1.cnt + C.Kst := fun v a ha =>
    ⟨((hPm v).2 a ha).1, ((hPm v).2 a ha).2.trans (by have := len_le_cnt S w.1 v; omega)⟩
  have hprobP := fun A : Finset (Fin S.f) =>
    pθ_prob (A := A) (θ := θp) (fun v _ => (hPp v).1) (fun v _ => hUp v) hwn hcnt'
  have hprobM := fun A : Finset (Fin S.f) =>
    pθ_prob (A := A) (θ := θm) (fun v _ => (hPm v).1) (fun v _ => hUm v) hwn hcnt'
  refine ⟨fun A x => pθ S A w θp x.1 * pθ S A w θm x.2, fun A => pair_prob (hprobP A) (hprobM A), ?_⟩
  intro Y T κ hY hκ t ht t' ht' ht0 ht0' _ A
  have hσ : ∀ v, S.σ v t ≠ 0 := fun v => (map_ne_zero _).2 ht0
  have hσ' : ∀ v, S.σ v t' ≠ 0 := fun v => (map_ne_zero _).2 ht0'
  have hsz : ∀ v, ∀ p ∈ Y.image (C.loc (S.σ v)), D.ptSize p = i - s + 1 - 1 := by
    intro v p hp
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 hp
    rw [ptSize_loc, hY h hh]; omega
  have hU : ∀ v, ∃ u : ℂ, ‖u‖ = 1 ∧ (v ∈ A → KB.BlockPSD Y Y
      (fun h h' => ((Λ (i - s + 1) s v ^ C.Kst : ℝ) : ℂ) *
        KB.mix S v ε i (Up v) (θp v) (lpt S v s t h) (lpt S v s t h'))
      (fun h h' => u * ((S.σ v t)⁻¹ - (S.σ v t')⁻¹) ^ C.Kst *
        KB.gN S v ε i (w.1 v) (lpt S v s t h) (lpt S v s t' h'))
      (fun h h' => ((Λ (i - s + 1) s v ^ C.Kst : ℝ) : ℂ) *
        KB.mix S v ε i (Um v) (θm v) (lpt S v s t' h) (lpt S v s t' h'))) := by
    intro v
    by_cases hv : v ∈ A
    · obtain ⟨u, hu, hB⟩ := hblk v ε hε (S.σ v t) (S.σ v t') (Y.image (C.loc (S.σ v))) (hσ v) (hσ' v) (hsz v)
      exact ⟨u, hu, fun _ => blockPSD_comp _ _ _ _ hB Y (C.loc (S.σ v))
        (fun x hx => Finset.mem_image_of_mem _ hx)⟩
    · exact ⟨1, by simp, fun h => absurd h hv⟩
  choose u hu1 hu2 using hU
  have hprod := blockPSD_prod (Y₁ := Y) (Y₂ := Y) univ
    (fun v h h' => (if v ∈ A then ((Λ (i - s + 1) s v ^ C.Kst : ℝ) : ℂ) else 1) *
      (if v ∈ A then KB.mix S v ε i (Up v) (θp v) (lpt S v s t h) (lpt S v s t h')
        else KB.gN S v ε i (w.1 v) (lpt S v s t h) (lpt S v s t h')))
    (fun v h h' => (if v ∈ A then u v * ((S.σ v t)⁻¹ - (S.σ v t')⁻¹) ^ C.Kst else 1) *
      KB.gN S v ε i (w.1 v) (lpt S v s t h) (lpt S v s t' h'))
    (fun v h h' => (if v ∈ A then ((Λ (i - s + 1) s v ^ C.Kst : ℝ) : ℂ) else 1) *
      (if v ∈ A then KB.mix S v ε i (Um v) (θm v) (lpt S v s t' h) (lpt S v s t' h')
        else KB.gN S v ε i (w.1 v) (lpt S v s t' h) (lpt S v s t' h')))
    (by
      intro v _
      by_cases hv : v ∈ A
      · simp only [if_pos hv]; exact hu2 v hv
      · simp only [if_neg hv, one_mul]
        exact blockPSD_pull (Y.image (lpt S v s t) ∪ Y.image (lpt S v s t')) (KB.gN S v ε i (w.1 v))
          (gN_psd S hpos v hε hi w _) Y (lpt S v s t) (lpt S v s t')
          (fun h hh => Finset.mem_union_left _ (Finset.mem_image_of_mem _ hh))
          (fun h hh => Finset.mem_union_right _ (Finset.mem_image_of_mem _ hh)))
  have hmem : ∀ τ ∈ T, ∀ h ∈ Y, TB.join h s τ ∈ TB.pts Y s T := by
    classical
    intro τ hτ h hh
    unfold TB.pts
    exact Finset.mem_image.2 ⟨(h, τ), Finset.mem_product.2 ⟨hh, hτ⟩, rfl⟩
  have hκb : KB.BlockPSD Y Y (TB.blk κ s t t) (TB.blk κ s t t') (TB.blk κ s t' t') :=
    blockPSD_pull (TB.pts Y s T) κ hκ Y (fun h => TB.join h s t) (fun h => TB.join h s t')
      (hmem t ht) (hmem t' ht')
  have hmain := block_cross_le (blockPSD_mul hκb hprod)

  have eL : (∑ h ∈ Y, ∑ h' ∈ Y, TB.blk κ s t t' h h' * ∏ v, (if v ∈ A then u v * ((S.σ v t)⁻¹ - (S.σ v t')⁻¹) ^ C.Kst else 1) *
      KB.gN S v ε i (w.1 v) (lpt S v s t h) (lpt S v s t' h')) =
      (∏ v ∈ A, u v * ((S.σ v t)⁻¹ - (S.σ v t')⁻¹) ^ C.Kst) * S.base.Nst ε i s w Y (TB.blk κ s t t') t t' := by
    rw [Nst_eq S hi, Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun h' _ => ?_
    rw [Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.univ_inter]
    simp only [lpt]; ring

  have eD : ∀ (τ : E) (Uq : Fin S.f → Finset (List C.Letter)) (θq : Fin S.f → List C.Letter → ℝ),
      (∀ v, TB.IsProb (Uq v) (θq v)) → (∀ v, ∀ a ∈ Uq v, D.AdmAt S v a ∧ a.length ≤ w.1.cnt + C.Kst) →
      (∑ h ∈ Y, ∑ h' ∈ Y, TB.blk κ s τ τ h h' * ∏ v,
        (if v ∈ A then ((Λ (i - s + 1) s v ^ C.Kst : ℝ) : ℂ) else 1) *
        (if v ∈ A then KB.mix S v ε i (Uq v) (θq v) (lpt S v s τ h) (lpt S v s τ h')
          else KB.gN S v ε i (w.1 v) (lpt S v s τ h) (lpt S v s τ h'))) =
      ((∏ v ∈ A, Λ (i - s + 1) s v ^ C.Kst : ℝ) : ℂ) *
        ∑ w' ∈ S.base.Wb (w.1.cnt + C.Kst), (pθ S A w θq w' : ℂ) * S.base.Nst ε i s w' Y (TB.blk κ s τ τ) τ τ := by
    intro τ Uq θq hP hUq
    have hx : ∀ h h', (∏ v, (if v ∈ A then ((Λ (i - s + 1) s v ^ C.Kst : ℝ) : ℂ) else 1) *
        (if v ∈ A then KB.mix S v ε i (Uq v) (θq v) (lpt S v s τ h) (lpt S v s τ h')
          else KB.gN S v ε i (w.1 v) (lpt S v s τ h) (lpt S v s τ h'))) =
        ((∏ v ∈ A, Λ (i - s + 1) s v ^ C.Kst : ℝ) : ℂ) * ∑ w' ∈ S.base.Wb (w.1.cnt + C.Kst),
          (pθ S A w θq w' : ℂ) * ∏ v, KB.gN S v ε i (w'.1 v) (lpt S v s τ h) (lpt S v s τ h') := by
      intro h h'
      have he := expand (A := A) (w := w) (θ := θq) (U := Uq) (fun v _ => hP v) (fun v _ => hUq v) hwn hcnt'
        (fun v a => KB.gN S v ε i a (lpt S v s τ h) (lpt S v s τ h'))
      rw [he, Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.univ_inter, Complex.ofReal_prod]
      rfl
    simp only [hx]
    rw [mix_sum]
    congr 1
    refine Finset.sum_congr rfl fun w' _ => ?_
    rw [Nst_eq S hi]; rfl
  have hK : S.base.K = C.Kst := rfl
  have hcw : S.base.cnt w = w.1.cnt := rfl
  rw [eL, eD t Up θp (fun v => (hPp v).1) hUp, eD t' Um θm (fun v => (hPm v).1) hUm, re_real_sum, re_real_sum]
    at hmain
  have hsp := sum_pair (S.base.Wb (w.1.cnt + C.Kst)) (S.base.Wb (w.1.cnt + C.Kst)) (pθ S A w θp) (pθ S A w θm)
    (fun w' => (S.base.Nst ε i s w' Y (TB.blk κ s t t) t t).re)
    (fun w' => (S.base.Nst ε i s w' Y (TB.blk κ s t' t') t' t').re) (hprobM A).2.2 (hprobP A).2.2
  rw [hK, hcw, hsp]
  calc (∏ v ∈ A, S.base.av v (t⁻¹ - t'⁻¹) ^ C.Kst) * ‖S.base.Nst ε i s w Y (TB.blk κ s t t') t t'‖ =
      ‖(∏ v ∈ A, u v * ((S.σ v t)⁻¹ - (S.σ v t')⁻¹) ^ C.Kst) * S.base.Nst ε i s w Y (TB.blk κ s t t') t t'‖ := by
        rw [norm_mul, norm_prod]
        congr 1
        refine Finset.prod_congr rfl fun v _ => ?_
        rw [norm_mul, hu1, one_mul, norm_pow, av_eq, map_sub, map_inv₀, map_inv₀]
    _ ≤ _ := hmain
    _ = _ := by ring

end

end Formalism.FourierDecayAlt.P.PBA
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.NormEntryBounds
section
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P

open C2x2 C2x5 HermitianXiVector UnipotentSums EntryMinorBounds

namespace NormEntryBounds

variable {k r : ℕ}

lemma gN_le (g : B.Mat k r) (E : ℝ) (hE : 0 ≤ E) (h : ∀ i j, ‖g i j‖ ≤ E) :
    B.gN g ≤ ((2 * r + k + 1 : ℕ) : ℝ) * E := by
  unfold B.gN
  rw [show ((2 * r + k + 1 : ℕ) : ℝ) * E = Real.sqrt ((((2 * r + k + 1 : ℕ) : ℝ) * E) ^ 2) by
    rw [Real.sqrt_sq (by positivity)]]
  apply Real.sqrt_le_sqrt
  have hs : ∀ i j, Complex.normSq (g i j) ≤ E ^ 2 := by
    intro i j; rw [Complex.normSq_eq_norm_sq]; exact pow_le_pow_left₀ (norm_nonneg _) (h i j) 2
  calc ∑ i, ∑ j, Complex.normSq (g i j) ≤ ∑ _i : Fin (2 * r + k + 1), ∑ _j : Fin (2 * r + k + 1), E ^ 2 :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hs i j))
    _ = (((2 * r + k + 1 : ℕ) : ℝ) * E) ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

lemma Hpk_mulVec_le (y : Fin (2 * r + k + 1) → ℂ) (X : ℝ) (hy : ∀ p, ‖y p‖ ≤ X) (j : Fin (2 * r + k + 1)) :
    ‖(Hpk k r *ᵥ y) j‖ ≤ X := by
  rw [gn_Hpk_mulVec]
  split_ifs
  · exact hy _
  · rw [norm_neg]; exact hy _
  · exact hy _

lemma mul_entry_le (A M : B.Mat k r) (a b : ℝ) (ha : ∀ i j, ‖A i j‖ ≤ a) (hb : ∀ i j, ‖M i j‖ ≤ b)
    (hb0 : 0 ≤ b) (i j : Fin (2 * r + k + 1)) :
    ‖(A * M) i j‖ ≤ ((2 * r + k + 1 : ℕ) : ℝ) * (a * b) := by
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans ?_
  have ht : ∀ p, ‖A i p * M p j‖ ≤ a * b := by
    intro p
    rw [norm_mul]
    exact mul_le_mul (ha i p) (hb p j) (norm_nonneg _) (le_trans (norm_nonneg _) (ha i p))
  calc ∑ p, ‖A i p * M p j‖ ≤ ∑ _p : Fin (2 * r + k + 1), a * b := Finset.sum_le_sum (fun p _ => ht p)
    _ = ((2 * r + k + 1 : ℕ) : ℝ) * (a * b) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end NormEntryBounds

open NormEntryBounds

theorem tau_norm_bound : C2.TauBound := by
  intro k r z hz
  have hn0 : (0 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by positivity
  obtain ⟨Zm, hZm⟩ : ∃ Zm : ℝ, Zm = ∑ p, ‖z p‖ := ⟨_, rfl⟩
  have hZm0 : 0 ≤ Zm := by rw [hZm]; exact Finset.sum_nonneg (fun p _ => norm_nonneg _)
  have hzp : ∀ p, ‖z p‖ ≤ Zm := fun p => by
    rw [hZm]; exact Finset.single_le_sum (fun q _ => norm_nonneg (z q)) (Finset.mem_univ p)
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = (1 : ℂ) / ((Tz k r z : ℝ) : ℂ) := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 1 + ‖c‖ * (2 * Zm + 1) := ⟨_, rfl⟩
  have hA1 : 1 ≤ A := by rw [hA]; nlinarith [norm_nonneg c]
  obtain ⟨Cm, hCm⟩ : ∃ Cm : ℝ, Cm = (Nat.factorial r : ℝ) := ⟨_, rfl⟩
  have hCm1 : 1 ≤ Cm := by rw [hCm]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero r)
  refine ⟨((2 * r + k + 1 : ℕ) : ℝ) * (((2 * r + k + 1 : ℕ) : ℝ) * (A * Cm)), fun v hv => ?_⟩
  obtain ⟨X, hX⟩ : ∃ X, X = C2.mx v := ⟨_, rfl⟩
  rw [← hX]
  have hX0 : 0 ≤ X := by rw [hX]; exact norm_nonneg _
  have hvX : ∀ a b, ‖v a b‖ ≤ X := fun a b => by rw [hX]; exact entry_le_mx v a b
  have h1X : 1 ≤ 1 + X := by linarith
  obtain ⟨ξ, hξ⟩ : ∃ ξ : Fin r → ℂ, ξ = fun a => v a.castSucc (Fin.last r) := ⟨_, rfl⟩
  obtain ⟨vX, hvXe⟩ : ∃ vX : Matrix (Fin r) (Fin r) ℂ, vX = v.submatrix Fin.castSucc Fin.castSucc := ⟨_, rfl⟩
  have hvXU : vX ∈ C2.UTset r := by
    rw [hvXe]; exact ⟨fun i j h => hv.1 _ _ (Fin.castSucc_lt_castSucc_iff.mpr h), fun i => hv.2 _⟩
  have hτ : C2.tauM k r z v = C2.nEich k r z ξ * C2.mX k r vX := by rw [hξ, hvXe]; rfl
  have hxi : ∀ p, ‖C2.xiV k r ξ p‖ ≤ X := by
    intro p; simp only [C2.xiV]; split_ifs
    · rw [hξ]; exact hvX _ _
    · rw [norm_zero]; exact hX0

  have hnE : ∀ i j, ‖C2.nEich k r z ξ i j‖ ≤ A * (1 + X) ^ 2 := by
    intro i j
    simp only [C2.nEich, Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply, vecMulVec_apply,
      Pi.star_apply, smul_eq_mul, ← hc]
    have h1 : ‖(1 : B.Mat k r) i j‖ ≤ 1 := by rw [Matrix.one_apply]; split_ifs <;> simp
    have hHz := Hpk_mulVec_le z Zm hzp j
    have hHx := Hpk_mulVec_le (C2.xiV k r ξ) X hxi j
    have hsum : ‖-(C2.xiV k r ξ i * star ((Hpk k r *ᵥ z) j)) + z i * star ((Hpk k r *ᵥ C2.xiV k r ξ) j) +
        1 / 2 * (C2.xiV k r ξ i * star ((Hpk k r *ᵥ C2.xiV k r ξ) j))‖ ≤ (2 * Zm + 1) * (1 + X) ^ 2 := by
      refine (norm_add_le _ _).trans ?_
      refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
      simp only [norm_neg, norm_mul, norm_star]
      have e1 : ‖C2.xiV k r ξ i‖ * ‖(Hpk k r *ᵥ z) j‖ ≤ X * Zm := mul_le_mul (hxi i) hHz (norm_nonneg _) hX0
      have e2 : ‖z i‖ * ‖(Hpk k r *ᵥ C2.xiV k r ξ) j‖ ≤ Zm * X := mul_le_mul (hzp i) hHx (norm_nonneg _) hZm0
      have e3 : ‖(1 / 2 : ℂ)‖ * (‖C2.xiV k r ξ i‖ * ‖(Hpk k r *ᵥ C2.xiV k r ξ) j‖) ≤ 1 * (X * X) := by
        apply mul_le_mul (by norm_num) (mul_le_mul (hxi i) hHx (norm_nonneg _) hX0) (by positivity) (by norm_num)
      nlinarith
    calc _ ≤ ‖(1 : B.Mat k r) i j‖ + ‖c‖ * ‖-(C2.xiV k r ξ i * star ((Hpk k r *ᵥ z) j)) +
            z i * star ((Hpk k r *ᵥ C2.xiV k r ξ) j) +
            1 / 2 * (C2.xiV k r ξ i * star ((Hpk k r *ᵥ C2.xiV k r ξ) j))‖ := by
          refine (norm_add_le _ _).trans (le_of_eq ?_); rw [norm_mul]
      _ ≤ 1 + ‖c‖ * ((2 * Zm + 1) * (1 + X) ^ 2) := add_le_add h1 (mul_le_mul_of_nonneg_left hsum (norm_nonneg _))
      _ ≤ A * (1 + X) ^ 2 := by
          rw [hA]; nlinarith [norm_nonneg c, pow_le_pow_left₀ (by linarith : (0:ℝ) ≤ 1) h1X 2, sq_nonneg (1 + X)]

  have hvXb : ∀ a b, ‖vX a b‖ ≤ 1 + X := fun a b => by rw [hvXe]; simp only [Matrix.submatrix_apply]; linarith [hvX (Fin.castSucc a) (Fin.castSucc b)]
  have hmE : ∀ i j, ‖C2.mX k r vX i j‖ ≤ Cm * (1 + X) ^ r := by
    have hpow1 : 1 ≤ (1 + X) ^ r := one_le_pow₀ h1X
    intro i j
    simp only [C2.mX]
    split_ifs with h1 h2 h3 h4 h5
    · calc ‖vX _ _‖ ≤ 1 + X := hvXb _ _
        _ ≤ (1 + X) ^ r := by
            calc 1 + X = (1 + X) ^ 1 := (pow_one _).symm
              _ ≤ (1 + X) ^ r := pow_le_pow_right₀ h1X (by omega)
        _ ≤ Cm * (1 + X) ^ r := le_mul_of_one_le_left (by positivity) hCm1
    · rw [norm_zero]; positivity
    · have hdet : vXᴴ.det = 1 := by rw [Matrix.det_conjTranspose, ut_det hvXU, star_one]
      refine (inv_entry_le vXᴴ hdet (1 + X) h1X
        (fun a b => by rw [Matrix.conjTranspose_apply, norm_star]; exact hvXb _ _) _ _).trans ?_
      rw [← hCm]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1X (Nat.sub_le r 1)) (by positivity)
    · rw [norm_zero]; positivity
    · rw [norm_one]; nlinarith
    · rw [norm_zero]; positivity
  have hτE : ∀ i j, ‖C2.tauM k r z v i j‖ ≤ ((2 * r + k + 1 : ℕ) : ℝ) * (A * Cm) * (1 + X) ^ (2 * r + 2) := by
    intro i j
    rw [hτ]
    refine (mul_entry_le _ _ _ _ hnE hmE (by positivity) i j).trans ?_
    have key : ((2 * r + k + 1 : ℕ) : ℝ) * (A * (1 + X) ^ 2 * (Cm * (1 + X) ^ r)) =
        ((2 * r + k + 1 : ℕ) : ℝ) * (A * Cm) * (1 + X) ^ (r + 2) := by ring
    rw [key]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1X (by omega)) (by positivity)
  have hgN : B.gN (C2.tauM k r z v) ≤ ((2 * r + k + 1 : ℕ) : ℝ) * (((2 * r + k + 1 : ℕ) : ℝ) * (A * Cm)) *
      (1 + X) ^ (2 * r + 2) := by
    refine (gN_le _ _ (by positivity) hτE).trans (le_of_eq ?_)
    ring
  have hτG : C2.tauM k r z v ∈ B.GV k r := ((c2_tau_mem k r z hz v hv).1).1
  refine ⟨hgN, ?_⟩
  rw [(norm_of_inverse k r _ hτG).1]
  exact hgN

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ResGDifferentiableAt
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

namespace Formalism.FourierDecayAlt.P.CutMP.TemperedBoundGL3

noncomputable section

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem sf_resG {D : Set (Mx k r)} {F : Mx k r → E} (hF : SmoothLev k r 0 D F) (i : Fin (r + 1)) :
    SmoothFam k r i (Formalism.FourierDecayAlt.P.Qx6.UU (Formalism.FourierDecayAlt.P.Qx6.Dcell D i)) (resG k r i F) := by
  induction i using Fin.induction with
  | zero =>
    have e : resG k r 0 F = fun _ => F := by
      funext c g
      exact Formalism.FourierDecayAlt.P.Qx6.resG_zero F c g
    rw [e, Formalism.FourierDecayAlt.P.Qx6.Dcell_zero]
    exact Formalism.FourierDecayAlt.P.Qx6.sf_const_fam hF
  | succ l ih =>
    rw [Formalism.FourierDecayAlt.P.Qx6.resG_succ, Formalism.FourierDecayAlt.P.Qx6.Dcell_succ]
    exact Formalism.FourierDecayAlt.P.Qx6.sf_Res Formalism.FourierDecayAlt.P.weyl_level_element_properties l ih

end

end Formalism.FourierDecayAlt.P.CutMP.TemperedBoundGL3
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SigmaContOn
section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace Formalism.FourierDecayAlt.P.S3dx4

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

def triv {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) : B.RealPlaceData k r ℂ ℂ where
  z := D.z
  z' := D.z'
  π := fun _ => 1
  π' := fun _ => 1
  μG := D.μG
  μW := D.μW
  μN := D.μN
  μW' := D.μW'
  μsec := D.μsec
  χ := D.χ
  k_pos := D.k_pos
  z_mem := D.z_mem
  z'_mem := D.z'_mem
  T_pos := D.T_pos
  T'_pos := D.T'_pos
  π_rep := ⟨rfl, fun _ _ _ _ => by ext; simp⟩
  π'_rep := ⟨rfl, fun _ _ _ _ => by ext; simp⟩
  π_unitary := fun _ _ v => by simp
  π'_unitary := fun _ _ v => by simp
  π_cont := continuousOn_const
  π'_cont := continuousOn_const
  haarG := D.haarG
  haarW := D.haarW
  haarN := D.haarN
  haarW' := D.haarW'
  sec := D.sec
  χ_smooth := D.χ_smooth
  χ_supp := D.χ_supp
  χ_int := D.χ_int

theorem hpk_eq (k r : ℕ) : PI.UpqRep.Hpk k r = Formalism.QuantumDeterminants.Hpk k r := rfl

theorem uh_eq (k r : ℕ) : PI.UpqRep.UH (PI.UpqRep.Hpk k r) = Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := rfl

theorem sigma_contOn {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Mx k r → (H →L[ℂ] H)}
    (hσ : PI.UpqRep.IsDSHpk k r ε lam σ) (v : H) :
    ContinuousOn (fun g => σ g v) (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) := by
  obtain ⟨P, ⟨⟨hPu, hPJ⟩, hPunit⟩, hDS⟩ := hσ
  have hc := hDS.2.2.1.2.2 v
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hPu
  have hmaps : Set.MapsTo (fun g : Mx k r => P * g * P⁻¹) (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
      (PI.UpqRep.UJset ε) := by
    intro g hg
    show (P * g * P⁻¹)ᴴ * PI.UpqRep.Jm ε * (P * g * P⁻¹) = PI.UpqRep.Jm ε
    have hg' : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
    have hJ : (P⁻¹)ᴴ * Formalism.QuantumDeterminants.Hpk k r * P⁻¹ = PI.UpqRep.Jm ε := by
      rw [← hpk_eq, ← hPJ]
      have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hdet
      have h2 : (P⁻¹)ᴴ * Pᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
      calc (P⁻¹)ᴴ * (Pᴴ * PI.UpqRep.Jm ε * P) * P⁻¹
          = ((P⁻¹)ᴴ * Pᴴ) * PI.UpqRep.Jm ε * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
        _ = PI.UpqRep.Jm ε := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
    have hPP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
    have hPPh : Pᴴ * (P⁻¹)ᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hPP, Matrix.conjTranspose_one]
    calc (P * g * P⁻¹)ᴴ * PI.UpqRep.Jm ε * (P * g * P⁻¹)
        = (P⁻¹)ᴴ * gᴴ * Pᴴ * ((P⁻¹)ᴴ * Formalism.QuantumDeterminants.Hpk k r * P⁻¹) * (P * g * P⁻¹) := by
          rw [hJ]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (P⁻¹)ᴴ * (gᴴ * Formalism.QuantumDeterminants.Hpk k r * g) * P⁻¹ := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc Pᴴ (P⁻¹)ᴴ, hPPh, Matrix.one_mul]
          rw [← Matrix.mul_assoc P⁻¹ P, hPP, Matrix.one_mul]
      _ = PI.UpqRep.Jm ε := by rw [hg', hJ]
  have hcont : Continuous (fun g : Mx k r => P * g * P⁻¹) := by fun_prop
  have := hc.comp hcont.continuousOn hmaps
  refine this.congr ?_
  intro g _
  show σ g v = σ (P⁻¹ * (P * g * P⁻¹) * P) v
  congr 2
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul P hdet, Matrix.one_mul,
    Matrix.mul_assoc, Matrix.nonsing_inv_mul P hdet, Matrix.mul_one]

end Formalism.FourierDecayAlt.P.S3dx4
end
end

