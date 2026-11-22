import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle0009
import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.SelfDualLatticesOneOrbit
import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.LatticeCountingFormula
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle0001

-- bundled from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.CoarseMultAt
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory MvPolynomial

theorem val_digit {D : Formalism.BasicNotions.D7} (h52 : Formalism.MainNotions.CovariantDegrees.FactorialUnitDecomposition D) {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (σ : Type)
    [Fintype σ] [DecidableEq σ] (odd : σ → Prop) [DecidablePred odd] (t ρ L : σ → ℕ)
    (hodd : ∀ v, odd v → L v = p ^ (t v + 1) ∧ ρ v < L v) (hend : ∀ v, ¬ odd v → L v = 1 ∧ ρ v = 0) (μ : σ → ℕ) :
    (∏ v, (ρ v + L v * μ v).factorial).factorization p =
      (∏ v, (ρ v).factorial * (μ v).factorial * (L v).factorial ^ (μ v)).factorization p := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨h1, h2⟩ := h52 p hp h5
  set t' : σ → ℕ := fun v => if odd v then t v else 0 with ht'
  set ρ' : σ → ℕ := fun v => if odd v then ρ v else 0 with hρ'
  have hlt : ∀ k, ρ' k < p ^ (t' k + 1) := by
    intro k
    by_cases hk : odd k
    · simp only [hρ', ht', if_pos hk]
      rw [← (hodd k hk).1]; exact (hodd k hk).2
    · simp only [hρ', ht', if_neg hk]
      exact pow_pos hp.pos _
  obtain ⟨hunit, -, -⟩ := h2 σ t' ρ' hlt
  set e' : σ → ℕ := fun v => if odd v then μ v else 0 with he'
  set U : ℚ := ∏ k, cUnit (p ^ (t' k + 1)) (e' k) * dUnit (p ^ (t' k + 1)) (e' k) (ρ' k) with hU
  have hU0 : U ≠ 0 := (hunit e').1
  have hUv : padicValRat p U = 0 := (hunit e').2
  have key : ((∏ v, (ρ v + L v * μ v).factorial : ℕ) : ℚ) =
      ((∏ v, (ρ v).factorial * (μ v).factorial * (L v).factorial ^ (μ v) : ℕ) : ℚ) * U := by
    push_cast
    rw [hU, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    by_cases hv : odd v
    · have := h1 (t' v) (ρ' v) (e' v) (hlt v)
      simp only [hρ', ht', he', if_pos hv] at this ⊢
      rw [(hodd v hv).1, this]
      ring
    · have := h1 (t' v) (ρ' v) (e' v) (hlt v)
      simp only [hρ', ht', he', if_neg hv] at this ⊢
      rw [(hend v hv).1, (hend v hv).2]
      simp only [zero_add, mul_zero, Nat.factorial_zero, Nat.cast_one, pow_zero, one_mul, mul_one, zero_add] at this ⊢
      rw [← this]
      simp
  have hQ0 : ((∏ v, (ρ v).factorial * (μ v).factorial * (L v).factorial ^ (μ v) : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast Finset.prod_ne_zero_iff.2 fun v _ =>
      mul_ne_zero (mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)) (pow_ne_zero _ (Nat.factorial_ne_zero _))
  have hv := congrArg (padicValRat p) key
  rw [padicValRat.mul hQ0 hU0, hUv, add_zero, padicValRat.of_nat, padicValRat.of_nat] at hv
  rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp]
  exact_mod_cast hv

def tdeg (C0 CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m)
    (x : X.TT × Bool) : ℕ :=
  multideg (ioExp C0 CE1 CE2 X j b (mu0 C0 CE1 CE2 X j b)) x

def TrueDegAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m], D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m),
      Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b →
      ∏ x : X.TT × Bool, (tdeg C0 CE1 CE2 X j b x).factorial = facSeg X j ∧
      ∑ x : X.TT × Bool, Nat.log X.p (tdeg C0 CE1 CE2 X j b x) = lgSeg X j

def CoarseMultAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m], D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m),
      Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b →
      (∏ x : X.TT × Bool, (cdeg C0 CE1 CE2 X j b x).factorial).factorization X.p ≤
        (expFact (mu0 C0 CE1 CE2 X j b)).factorization X.p + lgSeg X j

theorem kapNumAt_of {D : Formalism.BasicNotions.D7} (h52 : Formalism.MainNotions.CovariantDegrees.FactorialUnitDecomposition D) {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ}
    (hT : TrueDegAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) (hM : CoarseMultAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) :
    KapNumAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  classical
  intro X _ hD1 hH hc j b hb
  have hp : X.p.Prime := hD1.1
  obtain ⟨hT1, hT2⟩ := hT X hD1 hH hc j b hb
  have hM1 := hM X hD1 hH hc j b hb
  set μ0 := mu0 C0 CE1 CE2 X j b

  obtain ⟨M, hM0, hEM, hMv⟩ := expFact_mul X.p (tdeg C0 CE1 CE2 X j b) (ioExp C0 CE1 CE2 X j b μ0) (fun x => rfl)
  rw [hT1] at hEM
  have hMv' : M.factorization X.p ≤ X.m * lgSeg X j := by
    rw [← hT2, Finset.mul_sum]
    refine hMv.trans (le_of_eq (Finset.sum_congr rfl fun x _ => ?_))
    simp

  have ht : ∀ v : BV C0 CE1 CE2 X j, ∃ t, IsOddVar C0 CE1 CE2 X j v → symLev X.p C0 CE1 CE2 X j v = X.p ^ (t + 1) := by
    intro v
    by_cases hv : IsOddVar C0 CE1 CE2 X j v
    · obtain ⟨t, ht⟩ := (oddVar_data C0 CE1 CE2 X j b hb v hv).1
      exact ⟨t, fun _ => ht⟩
    · exact ⟨0, fun h => absurd h hv⟩
  choose t ht using ht
  have hvd := val_digit h52 hp hD1.2.1 (BV C0 CE1 CE2 X j) (IsOddVar C0 CE1 CE2 X j) t
    (fun v => baseExp C0 CE1 CE2 X j b (symVar C0 CE1 CE2 X j v)) (fun v => symLev X.p C0 CE1 CE2 X j v)
    (fun v hv => ⟨ht v hv, (oddVar_data C0 CE1 CE2 X j b hb v hv).2⟩)
    (fun v hv => endVar_data C0 CE1 CE2 X j b v hv) μ0
  have hE0 : expFact (ioExp C0 CE1 CE2 X j b μ0) ≠ 0 := by
    unfold expFact; exact Finsupp.prod_ne_zero_iff.2 fun _ _ => Nat.factorial_ne_zero _
  have hmu0 : expFact μ0 = ∏ v : BV C0 CE1 CE2 X j, (μ0 v).factorial := by
    unfold expFact
    rw [Finsupp.prod_fintype _ _ (fun _ => rfl)]
  have hR0 : Rblk C0 CE1 CE2 X j b ≠ 0 := Finset.prod_ne_zero_iff.2 fun _ _ => Nat.factorial_ne_zero _
  have hP1 : (∏ v : BV C0 CE1 CE2 X j, (baseExp C0 CE1 CE2 X j b (symVar C0 CE1 CE2 X j v) +
      symLev X.p C0 CE1 CE2 X j v * μ0 v).factorial) ≠ 0 := Finset.prod_ne_zero_iff.2 fun _ _ => Nat.factorial_ne_zero _
  have hP2 : (∏ v : BV C0 CE1 CE2 X j, (baseExp C0 CE1 CE2 X j b (symVar C0 CE1 CE2 X j v)).factorial *
      (symLev X.p C0 CE1 CE2 X j v).factorial ^ (μ0 v)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun _ _ => mul_ne_zero (Nat.factorial_ne_zero _) (pow_ne_zero _ (Nat.factorial_ne_zero _))
  have hP3 : (∏ v : BV C0 CE1 CE2 X j, (μ0 v).factorial) ≠ 0 := Finset.prod_ne_zero_iff.2 fun _ _ => Nat.factorial_ne_zero _
  have hsplit : (∏ v : BV C0 CE1 CE2 X j, (baseExp C0 CE1 CE2 X j b (symVar C0 CE1 CE2 X j v)).factorial *
      (μ0 v).factorial * (symLev X.p C0 CE1 CE2 X j v).factorial ^ (μ0 v)) =
      (∏ v : BV C0 CE1 CE2 X j, (baseExp C0 CE1 CE2 X j b (symVar C0 CE1 CE2 X j v)).factorial *
        (symLev X.p C0 CE1 CE2 X j v).factorial ^ (μ0 v)) * ∏ v : BV C0 CE1 CE2 X j, (μ0 v).factorial := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun v _ => by ring
  have hvE : (expFact (ioExp C0 CE1 CE2 X j b μ0)).factorization X.p =
      (PhiB C0 CE1 CE2 X j b).factorization X.p + (expFact μ0).factorization X.p := by
    rw [expFact_ioExp, Nat.factorization_mul hR0 hP1, Finsupp.add_apply, hvd, hsplit, Nat.factorization_mul hP2 hP3,
      Finsupp.add_apply, hmu0]
    unfold PhiB
    rw [Nat.factorization_mul hR0 hP2, Finsupp.add_apply]
    ring
  have hvF : (facSeg X j).factorization X.p = (expFact (ioExp C0 CE1 CE2 X j b μ0)).factorization X.p +
      M.factorization X.p := by
    rw [← hEM, Nat.factorization_mul hE0 hM0, Finsupp.add_apply]

  have hdv : expFact μ0 ∣ ∏ x : X.TT × Bool, (cdeg C0 CE1 CE2 X j b x).factorial := by
    have h := dvdAt C0 CE1 CE2 X j b hb μ0 (leading_exponent_homogeneous C0 CE1 CE2 X j b)
    unfold Nblk at h
    exact Nat.dvd_of_mul_dvd_mul_right (Nat.pos_of_ne_zero (specConst_ne _ _ _)) h
  have hc0 : (∏ x : X.TT × Bool, (cdeg C0 CE1 CE2 X j b x).factorial) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun x _ => Nat.factorial_ne_zero _
  have hle : (expFact μ0).factorization X.p ≤ (∏ x : X.TT × Bool, (cdeg C0 CE1 CE2 X j b x).factorial).factorization X.p :=
    (Nat.factorization_le_iff_dvd (by rw [hmu0]; exact hP3) hc0).2 hdv X.p
  constructor
  · rw [hvF, hvE]
    have : X.m * lgSeg X j ≤ (X.m + 1) * lgSeg X j := Nat.mul_le_mul_right _ (Nat.le_succ _)
    omega
  · rw [hvF, hvE]
    omega

end Formalism.MainNotions.ColumnSystems.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.KeyMinorDvd
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.LemmaBAlt

theorem key_pow_dvd {A : Type} [CommRing A] (p : ℕ) (hp : p.Prime) (w : A) (hw : w ^ 2 = (p : A)) (k e : ℕ)
    (u v : Fin (k + 1) → A) (M N' N : Fin (k + 1) → Fin (k + 1) → A)
    (hMN : ∀ b a, ∃ T, M b a ^ (p ^ e) = N' b a + p * T)
    (hinv : ∀ b b', ∑ a, N' b a * N a b' = if b = b' then 1 else 0)
    (hu : ∀ b, b ≠ 0 → w ∣ u b) (hv0 : w ∣ v 0) :
    w ∣ ∑ a, (∑ b, u b * M b a) ^ (p ^ e) * (∑ b', v b' * N a b') := by

  apply (Ideal.Quotient.eq_zero_iff_dvd w _).mp
  set φ := Ideal.Quotient.mk (Ideal.span {w}) with hφ
  have hw0 : φ w = 0 := (Ideal.Quotient.eq_zero_iff_dvd w w).mpr dvd_rfl
  have hp0 : φ (p : A) = 0 := by rw [← hw, map_pow, hw0, zero_pow two_ne_zero]
  have hu0 : ∀ b, b ≠ 0 → φ (u b) = 0 := fun b hb => (Ideal.Quotient.eq_zero_iff_dvd w _).mpr (hu b hb)
  have hv0' : φ (v 0) = 0 := (Ideal.Quotient.eq_zero_iff_dvd w _).mpr hv0
  have hrow : ∀ a, φ (∑ b, u b * M b a) = φ (u 0) * φ (M 0 a) := by
    intro a
    have hz : ∀ i : Fin k, φ (u i.succ) = 0 := fun i => hu0 _ (Fin.succ_ne_zero _)
    rw [map_sum, Fin.sum_univ_succ, map_mul]
    simp [hz]
  have hpow : ∀ a, φ (M 0 a) ^ (p ^ e) = φ (N' 0 a) := by
    intro a
    obtain ⟨T, hT⟩ := hMN 0 a
    rw [← map_pow, hT, map_add, map_mul, hp0, zero_mul, add_zero]
  have hδ : ∀ b', ∑ a, φ (N' 0 a) * φ (N a b') = if (0 : Fin (k + 1)) = b' then 1 else 0 := by
    intro b'
    have h := congrArg φ (hinv 0 b')
    rw [map_sum] at h
    simp_rw [map_mul] at h
    rw [h]
    split_ifs <;> simp
  rw [map_sum]
  simp_rw [map_mul, map_pow, hrow, mul_pow, hpow, map_sum, map_mul]
  have e : ∑ a, φ (u 0) ^ (p ^ e) * φ (N' 0 a) * ∑ b', φ (v b') * φ (N a b') =
      φ (u 0) ^ (p ^ e) * ∑ b', φ (v b') * ∑ a, φ (N' 0 a) * φ (N a b') := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b' _ => Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [e]
  simp_rw [hδ]
  simp [hv0']

theorem sigPow_mod' (p f : ℕ) [Fact p.Prime] (s : ℤ) : sigPow p f s = sigPow p f (s % (f : ℤ)) := by
  unfold sigPow
  rw [Int.emod_emod]

theorem segPos_val (X : Loc) (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) :
    (((segPos X.TT j i).val : ℕ) : ℤ) = (((segStart X.TT j).val : ℤ) + ((segDists X.TT j).get i : ℤ)) % (X.n' : ℤ) := by
  simp only [segPos, posAdd]
  push_cast
  rfl

theorem kS_ord (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O) (hsq : S.SqP) (hD : D1num X)
    (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j))
    (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) (hg : IsGLW g) :
    InWjRg X.p X.n' O S.w 1 (hhLetters X.TT) g (kSkey O X j i) 1 := by
  classical
  have hp : X.p.Prime := hD.1
  have hf : 1 ≤ X.n' := by have := hD.2.2.1; omega
  set d := (segDists X.TT j).get i with hd
  set s0 : ℤ := ((topStart X j : X.TT).val.val : ℤ) with hs0
  set s1 : ℤ := ((topOdd X j i : X.TT).val.val : ℤ) with hs1
  let xs : X.TT × Bool := (topStart X j, true)
  let y : X.TT × Bool := (topOdd X j i, false)
  let A := MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) O
  let u : Fin (X.m + 1) → A := fun b => C (dW O S.w (hhLetters X.TT) 1 xs b) * MvPolynomial.X (xs, b)
  let v : Fin (X.m + 1) → A := fun b => C (dW O S.w (hhLetters X.TT) 1 y b) * MvPolynomial.X (y, b)
  let M : Fin (X.m + 1) → Fin (X.m + 1) → A := fun b a => C (psiO X.p X.n' O s0 (g⁻¹ b a))
  let N' : Fin (X.m + 1) → Fin (X.m + 1) → A := fun b a => C (psiO X.p X.n' O s1 (g⁻¹ b a))
  let N : Fin (X.m + 1) → Fin (X.m + 1) → A := fun a b => C (psiO X.p X.n' O s1 (g a b))

  have hlift : liftSubst X.p X.n' O S.w 1 (hhLetters X.TT) g (kSkey O X j i) =
      MvPolynomial.map (algebraMap O (KK O)) (∑ a, (∑ b, u b * M b a) ^ (X.p ^ d) * (∑ b', v b' * N a b')) := by
    unfold kSkey
    simp only [map_sum, map_mul, map_pow]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [liftSubst_X_vec X.p X.n' O S.w (hhLetters X.TT) 1 g hg xs a rfl,
      liftSubst_X_cov X.p X.n' O S.w (hhLetters X.TT) 1 g y a rfl]
    simp only [u, v, M, N, map_sum, map_mul, map_C, map_X, sigMat_apply]
    rfl

  have hMN : ∀ b a, ∃ T, M b a ^ (X.p ^ d) = N' b a + X.p * T := by
    intro b a
    obtain ⟨τ, hτ⟩ := frobCong X.p X.n' hf s0 (s0 + d) (by omega) (g⁻¹ b a)
    have e1 : (s0 + d - s0).toNat = d := by omega
    rw [e1] at hτ
    have e2 : sigPow X.p X.n' (s0 + d) = sigPow X.p X.n' s1 := by
      rw [sigPow_mod' X.p X.n' (s0 + d), sigPow_mod' X.p X.n' s1]
      congr 1
      simp only [hs0, hs1, topStart, topOdd]
      rw [segPos_val, Int.emod_emod_of_dvd _ (dvd_refl _)]
    rw [e2] at hτ
    refine ⟨C (algebraMap (WF X.p X.n') O τ), ?_⟩
    have := congrArg (fun z => (C (algebraMap (WF X.p X.n') O z) : A)) hτ
    simp only [map_sub, map_pow, map_mul, map_natCast] at this
    simp only [M, N', psiO, RingHom.comp_apply]
    linear_combination this

  have hinv : ∀ b b', ∑ a, N' b a * N a b' = if b = b' then 1 else 0 := by
    intro b b'
    have h1 : ∑ a, N' b a * N a b' = C (psiO X.p X.n' O s1 ((g⁻¹ * g) b b')) := by
      simp only [N', N, ← map_mul, ← map_sum, Matrix.mul_apply]
    rw [h1, Matrix.nonsing_inv_mul g hg, Matrix.one_apply]
    split_ifs <;> simp
  have hw : (C S.w : A) ^ 2 = (X.p : A) := by rw [← map_pow, hsq, map_natCast]
  have hu : ∀ b, b ≠ 0 → (C S.w : A) ∣ u b := by
    intro b hb
    have : dW O S.w (hhLetters X.TT) 1 xs b = S.w := by
      have : 1 ≤ (b : ℕ) := Nat.one_le_iff_ne_zero.2 (fun h => hb (Fin.ext h))
      simp [dW, hhLetters, xs, this]
    exact ⟨MvPolynomial.X (xs, b), by simp only [u, this]⟩
  have hv0 : (C S.w : A) ∣ v 0 := by
    have : dW O S.w (hhLetters X.TT) 1 y (0 : Fin (X.m + 1)) = S.w := by simp [dW, hhLetters, y]
    exact ⟨MvPolynomial.X (y, 0), by simp only [v, this]⟩
  obtain ⟨Q, hQ⟩ := key_pow_dvd X.p hp (C S.w : A) hw X.m d u v M N' N hMN hinv hu hv0
  unfold InWjRg
  rw [hlift, hQ]
  intro m
  refine ⟨Q.coeff m, ?_⟩
  rw [coeff_map, coeff_C_mul, pow_one, map_mul]

theorem key_minor_dvd {A : Type} [CommRing A] (p : ℕ) (hp : p.Prime) (w : A) (hw : w ^ 2 = (p : A)) (k e : ℕ)
    (u u' : Fin (k + 1) → A) (M N' : Fin (k + 1) → Fin (k + 1) → A)
    (hMN : ∀ b a, ∃ T, M b a ^ (p ^ e) = N' b a + p * T)
    (hu : ∀ b, b ≠ 0 → w ∣ u b) (hu' : ∀ b, b ≠ 0 → w ∣ u' b) (c : Fin (k + 1)) :
    w ∣ (∑ b, u' b * N' b c) * (∑ b, u b * M b 0) ^ (p ^ e) - (∑ b, u' b * N' b 0) * (∑ b, u b * M b c) ^ (p ^ e) := by

  apply (Ideal.Quotient.eq_zero_iff_dvd w _).mp
  set φ := Ideal.Quotient.mk (Ideal.span {w}) with hφ
  have hw0 : φ w = 0 := (Ideal.Quotient.eq_zero_iff_dvd w w).mpr dvd_rfl
  have hp0 : φ (p : A) = 0 := by rw [← hw, map_pow, hw0, zero_pow two_ne_zero]
  have hrow : ∀ (x : Fin (k + 1) → A) (Q : Fin (k + 1) → Fin (k + 1) → A), (∀ b, b ≠ 0 → w ∣ x b) →
      ∀ a, φ (∑ b, x b * Q b a) = φ (x 0) * φ (Q 0 a) := by
    intro x Q hx a
    have hz : ∀ i : Fin k, φ (x i.succ) = 0 := fun i =>
      (Ideal.Quotient.eq_zero_iff_dvd w _).mpr (hx _ (Fin.succ_ne_zero _))
    rw [map_sum, Fin.sum_univ_succ, map_mul]
    simp [hz]
  have hpow : ∀ a, φ (M 0 a) ^ (p ^ e) = φ (N' 0 a) := by
    intro a
    obtain ⟨T, hT⟩ := hMN 0 a
    rw [← map_pow, hT, map_add, map_mul, hp0, zero_mul, add_zero]
  rw [map_sub, map_mul, map_mul, map_pow, map_pow, hrow u' N' hu' c, hrow u M hu 0, hrow u' N' hu' 0,
    hrow u M hu c, mul_pow, mul_pow, hpow 0, hpow c]
  ring

theorem kW_ord (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O) (hsq : S.SqP) (hD : D1num X)
    (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j))
    (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) (hg : IsGLW g) (c : Fin (X.m + 1)) :
    InWjRg X.p X.n' O S.w 1 (hhLetters X.TT) g (kWkey O X j i c) 1 := by
  classical
  have hp : X.p.Prime := hD.1
  have hf : 1 ≤ X.n' := by have := hD.2.2.1; omega
  set d := (segDists X.TT j).get i with hd
  set s0 : ℤ := ((topStart X j : X.TT).val.val : ℤ) with hs0
  set s1 : ℤ := ((topOdd X j i : X.TT).val.val : ℤ) with hs1
  let xs : X.TT × Bool := (topStart X j, true)
  let z : X.TT × Bool := (topOdd X j i, true)
  let A := MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) O
  let u : Fin (X.m + 1) → A := fun b => C (dW O S.w (hhLetters X.TT) 1 xs b) * MvPolynomial.X (xs, b)
  let u' : Fin (X.m + 1) → A := fun b => C (dW O S.w (hhLetters X.TT) 1 z b) * MvPolynomial.X (z, b)
  let M : Fin (X.m + 1) → Fin (X.m + 1) → A := fun b a => C (psiO X.p X.n' O s0 (g⁻¹ b a))
  let N' : Fin (X.m + 1) → Fin (X.m + 1) → A := fun b a => C (psiO X.p X.n' O s1 (g⁻¹ b a))
  have hlift : liftSubst X.p X.n' O S.w 1 (hhLetters X.TT) g (kWkey O X j i c) =
      MvPolynomial.map (algebraMap O (KK O)) ((∑ b, u' b * N' b c) * (∑ b, u b * M b 0) ^ (X.p ^ d) -
        (∑ b, u' b * N' b 0) * (∑ b, u b * M b c) ^ (X.p ^ d)) := by
    unfold kWkey
    simp only [map_sub, map_mul, map_pow]
    rw [liftSubst_X_vec X.p X.n' O S.w (hhLetters X.TT) 1 g hg z c rfl,
      liftSubst_X_vec X.p X.n' O S.w (hhLetters X.TT) 1 g hg xs 0 rfl,
      liftSubst_X_vec X.p X.n' O S.w (hhLetters X.TT) 1 g hg z 0 rfl,
      liftSubst_X_vec X.p X.n' O S.w (hhLetters X.TT) 1 g hg xs c rfl]
    simp only [u, u', M, N', map_sum, map_mul, map_C, map_X, sigMat_apply]
    rfl
  have hMN : ∀ b a, ∃ T, M b a ^ (X.p ^ d) = N' b a + X.p * T := by
    intro b a
    obtain ⟨τ, hτ⟩ := frobCong X.p X.n' hf s0 (s0 + d) (by omega) (g⁻¹ b a)
    have e1 : (s0 + d - s0).toNat = d := by omega
    rw [e1] at hτ
    have e2 : sigPow X.p X.n' (s0 + d) = sigPow X.p X.n' s1 := by
      rw [sigPow_mod' X.p X.n' (s0 + d), sigPow_mod' X.p X.n' s1]
      congr 1
      simp only [hs0, hs1, topStart, topOdd]
      rw [segPos_val, Int.emod_emod_of_dvd _ (dvd_refl _)]
    rw [e2] at hτ
    refine ⟨C (algebraMap (WF X.p X.n') O τ), ?_⟩
    have := congrArg (fun z => (C (algebraMap (WF X.p X.n') O z) : A)) hτ
    simp only [map_sub, map_pow, map_mul, map_natCast] at this
    simp only [M, N', psiO, RingHom.comp_apply]
    linear_combination this
  have hw : (C S.w : A) ^ 2 = (X.p : A) := by rw [← map_pow, hsq, map_natCast]
  have hu : ∀ b, b ≠ 0 → (C S.w : A) ∣ u b := by
    intro b hb
    have : dW O S.w (hhLetters X.TT) 1 xs b = S.w := by
      have : 1 ≤ (b : ℕ) := Nat.one_le_iff_ne_zero.2 (fun h => hb (Fin.ext h))
      simp [dW, hhLetters, xs, this]
    exact ⟨MvPolynomial.X (xs, b), by simp only [u, this]⟩
  have hu' : ∀ b, b ≠ 0 → (C S.w : A) ∣ u' b := by
    intro b hb
    have : dW O S.w (hhLetters X.TT) 1 z b = S.w := by
      have : 1 ≤ (b : ℕ) := Nat.one_le_iff_ne_zero.2 (fun h => hb (Fin.ext h))
      simp [dW, hhLetters, z, this]
    exact ⟨MvPolynomial.X (z, b), by simp only [u', this]⟩
  obtain ⟨Q, hQ⟩ := key_minor_dvd X.p hp (C S.w : A) hw X.m d u u' M N' hMN hu hu' c
  unfold InWjRg
  rw [hlift, hQ]
  intro m
  refine ⟨Q.coeff m, ?_⟩
  rw [coeff_map, coeff_C_mul, pow_one, map_mul]

theorem key3Ord : CoarseMultiplicityOrderBound := by
  intro X _ O _ _ _ _ S hsq hD j i g hg
  exact ⟨kS_ord X O S hsq hD j i g hg, fun c => kW_ord X O S hsq hD j i g hg c.succ⟩

theorem key3At : CoarseMultiplicityBoundAtIdentity := third_key_of_order key3Ord

end Formalism.MainNotions.ColumnSystems.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.LevOfSymVar
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

section

variable (C0 CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] (j : Fin (numSeg X.TT))

theorem lev_of_symVar (v : BV C0 CE1 CE2 X j) (i : Fin (segS X.TT j)) (h : (symVar C0 CE1 CE2 X j v).1.1 = topOdd X j i) :
    symLev X.p C0 CE1 CE2 X j v = (X.seg C0 CE1 CE2 j).P X.p i := by
  rcases v with ⟨a, c⟩ | ⟨l, bo⟩
  · by_cases ha : (a : ℕ) < 2 * segS X.TT j
    · simp only [symVar, symLev, dif_pos ha] at h ⊢
      rw [topOdd_inj X j h]
    · simp only [symVar, dif_neg ha] at h
      exact absurd h.symm (topOdd_ne_end X j i)
  · by_cases hl : (l : ℕ) < (X.seg C0 CE1 CE2 j).t
    · simp only [symVar, symLev, dif_pos hl] at h ⊢
      rw [topOdd_inj X j h]
    · simp only [symVar, dif_neg hl] at h
      exact absurd h.symm (topOdd_ne_end X j i)

theorem coarse_dvd (μ : BV C0 CE1 CE2 X j →₀ ℕ) (i : Fin (segS X.TT j)) (β : Bool) (c : Fin (X.m + 1)) :
    (X.seg C0 CE1 CE2 j).P X.p i ∣
      (μ.sum fun v n => Finsupp.single (symVar C0 CE1 CE2 X j v) (symLev X.p C0 CE1 CE2 X j v * n)) ((topOdd X j i, β), c) := by
  classical
  rw [Finsupp.sum_apply]
  refine Finset.dvd_sum fun v _ => ?_
  show _ ∣ (Finsupp.single (symVar C0 CE1 CE2 X j v) (symLev X.p C0 CE1 CE2 X j v * μ v)) ((topOdd X j i, β), c)
  rw [Finsupp.single_apply]
  split_ifs with h
  · rw [lev_of_symVar C0 CE1 CE2 X j v i (by rw [h])]
    exact dvd_mul_right _ _
  · exact dvd_zero _

theorem coarse_spec (μ : BV C0 CE1 CE2 X j →₀ ℕ) (i : Fin (segS X.TT j)) (β : Bool)
    (hi : (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma) :
    (μ.sum fun v n => Finsupp.single (symVar C0 CE1 CE2 X j v) (symLev X.p C0 CE1 CE2 X j v * n))
      ((topOdd X j i, β), 0) = 0 := by
  classical
  rw [Finsupp.sum_apply]
  refine Finset.sum_eq_zero fun v _ => ?_
  show (Finsupp.single (symVar C0 CE1 CE2 X j v) (symLev X.p C0 CE1 CE2 X j v * μ v)) ((topOdd X j i, β), 0) = 0
  rw [Finsupp.single_apply, if_neg]
  intro h
  rcases v with ⟨a, c⟩ | ⟨l, bo⟩
  · simp only [symVar] at h
    split_ifs at h <;> exact Fin.succ_ne_zero _ (congrArg Prod.snd h)
  · simp only [symVar] at h
    split_ifs at h with hl
    · have e := topOdd_inj X j (congrArg (fun z => z.1.1) h)
      have : (X.seg C0 CE1 CE2 j).sigma + (l : ℕ) = (i : ℕ) := congrArg Fin.val e
      omega
    · exact topOdd_ne_end X j i (congrArg (fun z => z.1.1) h).symm

theorem ioExp_mod (b : SegBlock (segS X.TT j) X.m)
    (hb : Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b) (μ : BV C0 CE1 CE2 X j →₀ ℕ)
    (i : Fin (segS X.TT j)) (β : Bool) (c : Fin (X.m + 1)) :
    ioExp C0 CE1 CE2 X j b μ ((topOdd X j i, β), c) % (X.seg C0 CE1 CE2 j).P X.p i =
      if β then b.rz i c else b.ry i c := by
  unfold ioExp
  rw [Finsupp.add_apply, baseExp_odd]
  obtain ⟨k, hk⟩ := coarse_dvd C0 CE1 CE2 X j μ i β c
  rw [hk]
  have hlt : (if β then b.rz i c else b.ry i c) < (X.seg C0 CE1 CE2 j).P X.p i := by
    split_ifs
    · exact (hb.1.1 i c).1
    · exact (hb.1.1 i c).2
  set P := (X.seg C0 CE1 CE2 j).P X.p i
  have e1 : ∀ (cond : Prop) [Decidable cond] (T : ℕ), (if cond then P * T else 0) = P * (if cond then T else 0) := by
    intro cond _ T
    split_ifs <;> simp
  rw [e1, add_assoc, ← mul_add, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

end

end Formalism.MainNotions.ColumnSystems.Pf
end
end

