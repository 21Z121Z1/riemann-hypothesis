import Formalism.GaussJetBounds.Bundle0001
import Formalism.GaussJetBounds.Bundle0006
import Formalism.GaussJetBounds.ThmAGauss
import Formalism.GaussJetBounds.GaussJetProofs.OneGauss
import Formalism.GaussJetBounds.StatementV
import Formalism.GaussJetBounds.GaussJetProofs.Bundle0004

-- bundled from Formalism.GaussJetBounds.GaussJetProofs.OrbMul
section
noncomputable section
open scoped BigOperators

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

namespace OrbMul

section Pair

variable {K : Type} [Field K] {σ ι : Type}

lemma jetPairPoly_eq_sum (P : MvPolynomial ι (MvPolynomial σ K)) (Th : MvPowerSeries ι K)
    (S : Finset (ι →₀ ℕ)) (hS : P.support ⊆ S) :
    jetPairPoly P Th = ∑ κ ∈ S, MvPolynomial.coeff κ P *
      MvPolynomial.C (((mfact κ : ℕ) : K) * MvPowerSeries.coeff κ Th) := by
  unfold jetPairPoly
  refine Finset.sum_subset hS fun κ _ hκ => ?_
  rw [MvPolynomial.notMem_support_iff.mp hκ, zero_mul]

lemma jetPairPoly_add_left (P Q : MvPolynomial ι (MvPolynomial σ K)) (Th : MvPowerSeries ι K) :
    jetPairPoly (P + Q) Th = jetPairPoly P Th + jetPairPoly Q Th := by
  classical
  rw [jetPairPoly_eq_sum (P + Q) Th (P.support ∪ Q.support) MvPolynomial.support_add,
    jetPairPoly_eq_sum P Th (P.support ∪ Q.support) Finset.subset_union_left,
    jetPairPoly_eq_sum Q Th (P.support ∪ Q.support) Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun κ _ => ?_
  rw [MvPolynomial.coeff_add, add_mul]

lemma jetPairPoly_monomial (κ : ι →₀ ℕ) (c : MvPolynomial σ K) (Th : MvPowerSeries ι K) :
    jetPairPoly (MvPolynomial.monomial κ c) Th =
      c * MvPolynomial.C (((mfact κ : ℕ) : K) * MvPowerSeries.coeff κ Th) := by
  classical
  rw [jetPairPoly_eq_sum _ Th {κ} MvPolynomial.support_monomial_subset, Finset.sum_singleton,
    MvPolynomial.coeff_monomial, if_pos rfl]

end Pair

section Exps

variable {ι₁ ι₂ : Type}

def jn (a : ι₁ →₀ ℕ) (b : ι₂ →₀ ℕ) : ι₁ ⊕ ι₂ →₀ ℕ :=
  a.mapDomain Sum.inl + b.mapDomain Sum.inr

end Exps

section Along

variable {K : Type} [Field K] {ι₁ ι₂ σ₁ σ₂ : Type} [Finite ι₁] [Finite ι₂]

end Along

section Trunc

variable {K : Type} [Field K] {σ ι : Type} [Finite ι]

end Trunc

section Norm

variable {K : Type} [NormedField K] [IsUltrametricDist K] {σ₁ σ₂ : Type}

lemma norm_coeff_rename_le {σ τ : Type} (e : σ → τ) (he : Function.Injective e)
    (A : MvPolynomial σ K) {B : ℝ} (hA : ∀ n, ‖MvPolynomial.coeff n A‖ ≤ B) (n : τ →₀ ℕ) :
    ‖MvPolynomial.coeff n (MvPolynomial.rename e A)‖ ≤ B := by
  by_cases hn : ∃ u : σ →₀ ℕ, u.mapDomain e = n
  · obtain ⟨u, rfl⟩ := hn
    rw [MvPolynomial.coeff_rename_mapDomain e he]
    exact hA u
  · rw [MvPolynomial.coeff_rename_eq_zero e A n fun u hu => absurd ⟨u, hu⟩ hn, norm_zero]
    exact le_trans (norm_nonneg _) (hA 0)

end Norm

end OrbMul

namespace OrbMul

lemma linSub_idM {K : Type} [Field K] {d N0 N1 : ℕ} [NeZero d] (x : ZV d N0 N1) :
    linSub (idM : ZV d N0 N1 → ZV d N0 N1 → K) x = MvPowerSeries.X x := by
  classical
  unfold linSub idM
  simp

lemma thetaZ_eq {K : Type} [NormedField K] [CharZero K] {d N0 N1 : ℕ} [NeZero d]
    (g : ZV d N0 N1 → MvPowerSeries (ZV d N0 N1) K) (U : MvPowerSeries (ZV d N0 N1) K) (ε : K)
    (be : MvPowerSeries (ZMod d) K) :
    thetaZ g U ε be = MvPowerSeries.subst g U *
      mvExp (ε • bSum (idM : ZV d N0 N1 → ZV d N0 N1 → K) be) := by
  unfold thetaZ
  rw [show (linSub (idM : ZV d N0 N1 → ZV d N0 N1 → K) : ZV d N0 N1 → MvPowerSeries (ZV d N0 N1) K) =
      MvPowerSeries.X from funext linSub_idM, MvPowerSeries.subst_self]
  rfl

end OrbMul

end Formalism.DworkPowerSeriesWeights
end
end

-- bundled from Formalism.GaussJetBounds.GaussJetProofs.TheoremAMatrixEntries
section
noncomputable section
open scoped BigOperators

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

lemma norm_l_pos (l : ℕ) [hl : Fact l.Prime] : 0 < ‖(l : ℂ_[l])‖ :=
  norm_pos_iff.2 (Nat.cast_ne_zero.2 hl.out.ne_zero)

lemma norm_l_lt_one (l : ℕ) [hl : Fact l.Prime] : ‖(l : ℂ_[l])‖ < 1 := by
  have h : ‖(((l : ℚ_[l]) : ℚ_[l]) : ℂ_[l])‖ = ‖(l : ℚ_[l])‖ := PadicComplex.norm_extends' l _
  have h2 : (((l : ℚ_[l]) : ℚ_[l]) : ℂ_[l]) = (l : ℂ_[l]) := by
    simp
  rw [h2] at h
  rw [h]
  exact Padic.norm_p_lt_one

lemma exists_norm_eq_rpow_rat (l : ℕ) [hl : Fact l.Prime] (q : ℚ) :
    ∃ c : ℂ_[l], ‖c‖ = ‖(l : ℂ_[l])‖ ^ (q : ℝ) := by
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq ((l : ℂ_[l]) ^ q.num) q.pos
  refine ⟨c, ?_⟩
  have hπ := norm_l_pos l
  have h1 : ‖c‖ ^ q.den = ‖(l : ℂ_[l])‖ ^ q.num := by
    rw [← norm_pow, hc, norm_zpow]
  have hden : (q.den : ℝ) ≠ 0 := Nat.cast_ne_zero.2 q.den_nz
  have h2 : (‖(l : ℂ_[l])‖ ^ (q : ℝ)) ^ q.den = ‖(l : ℂ_[l])‖ ^ q.num := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hπ.le, ← Real.rpow_intCast]
    congr 1
    have : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := by
      exact_mod_cast (Rat.num_div_den q).symm
    rw [this]
    field_simp
  exact (pow_left_inj₀ (norm_nonneg c) (Real.rpow_nonneg hπ.le _) q.den_nz).1 (h1.trans h2.symm)

lemma le_rpow_of_forall_norm (l : ℕ) [hl : Fact l.Prime] (b x : ℝ) (hx : 0 ≤ x)
    (h : ∀ c : ℂ_[l], ‖(l : ℂ_[l])‖ ^ b ≤ ‖c‖ → x ≤ ‖c‖) : x ≤ ‖(l : ℂ_[l])‖ ^ b := by
  have hπ := norm_l_pos l
  have hπ1 := norm_l_lt_one l
  rcases hx.eq_or_lt with h0 | h0
  · rw [← h0]; exact Real.rpow_nonneg hπ.le _
  by_contra hlt
  rw [not_le] at hlt
  set t : ℝ := Real.logb ‖(l : ℂ_[l])‖ x with ht
  have hxt : ‖(l : ℂ_[l])‖ ^ t = x := Real.rpow_logb hπ hπ1.ne h0
  rw [← hxt] at hlt
  have htb : t < b := (Real.rpow_lt_rpow_left_iff_of_base_lt_one hπ hπ1).1 hlt
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn htb
  obtain ⟨c, hc⟩ := exists_norm_eq_rpow_rat l q
  have h1 : x ≤ ‖c‖ := h c (by
    rw [hc]; exact Real.rpow_le_rpow_of_exponent_ge hπ hπ1.le hq2.le)
  rw [hc, ← hxt] at h1
  exact absurd h1 (not_le.2 ((Real.rpow_lt_rpow_left_iff_of_base_lt_one hπ hπ1).2 hq1))

theorem thmAEntry_of (hW : ThmAWeyl) : ThmAEntry := by
  intro l _ d N0 N1 _ hl hd hev K0 hK0 ζ hζ be hbe g hg0 hg U hU ε hε TT colN p hp hp1 I nu1 nu2 size
    hnu1 hnu2 hsize a ha hsa hN0 hsat δ hδ
  refine le_rpow_of_forall_norm l _ _ (norm_nonneg _) fun c hc => ?_
  have hmem := hW l d N0 N1 hl hd hev K0 hK0 ζ hζ be hbe g hg0 hg U hU ε hε TT colN p hp hp1 I nu1 nu2
    size hnu1 hnu2 hsize a ha hsa hN0 hsat c hc
  have hcpos : 0 < ‖c‖ := lt_of_lt_of_le (Real.rpow_pos_of_pos (norm_l_pos l) _) hc
  have h1 := hδ _ hmem
  rw [map_smul, norm_smul, norm_inv] at h1
  rwa [inv_mul_le_iff₀ hcpos, mul_one] at h1

theorem theorem_A_matrix_entries : ThmAEntry := thmAEntry_of (thmAWeyl_of thmAGauss)

end Formalism.DworkPowerSeriesWeights
end
end

