import Mathlib
import Formalism.GL3MeanSquares.InvariantSeriesBidegreeOneOne
import Formalism.GL3MeanSquares.LegendreCoefficient
import Formalism.FormalGroupWitt.FormalGroupWittProofs.Bundle0002
import Formalism.FormalGroupWitt.FormalGroupWittProofs.SolveV
import Formalism.FormalGroupWitt.FormalGroupWittProofs.InvIntV

-- bundled from Formalism.GL3MeanSquares.HookFormulaTorsion.ArithmeticFrobeniusAction
section
namespace Formalism.HermitianLattices.IntegralLatticeDensity

open Finset

private theorem frob_teich (p : ℕ) [Fact p.Prime] (k : Type) [CommRing k] [CharP k p] (x : k) :
    WittVector.frobenius (WittVector.teichmuller p x) = (WittVector.teichmuller p x) ^ p := by
  rw [← map_pow]
  ext n
  rw [WittVector.coeff_frobenius_charP]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [WittVector.teichmuller_coeff_zero, WittVector.teichmuller_coeff_zero]
  · rw [WittVector.teichmuller_coeff_pos p _ n hn, WittVector.teichmuller_coeff_pos p _ n hn,
      zero_pow (Fact.out : p.Prime).ne_zero]

end Formalism.HermitianLattices.IntegralLatticeDensity
end

-- bundled from Formalism.GL3MeanSquares.HookFormulaTorsion.FourFoldOrthogonalSum
section
namespace Formalism.HermitianLattices.IntegralLatticeDensity

open Finset

theorem integer_mean_log_bound : IntegerMeanLog := by
  intro K _ _ x hx
  have hx' : (x : K) ≠ 0 := by exact_mod_cast hx
  have hne : ∀ φ : K →+* ℂ, ‖φ (x : K)‖ ≠ 0 := fun φ => by
    rw [norm_ne_zero_iff]
    exact (map_ne_zero φ).mpr hx'
  rw [← Real.log_prod (fun φ _ => hne φ)]
  apply Real.log_nonneg
  rw [← norm_prod]
  have key : (∏ φ : K →+* ℂ, φ (x : K)) = algebraMap ℚ ℂ (Algebra.norm ℚ (x : K)) := by
    rw [Algebra.norm_eq_prod_embeddings ℚ ℂ]
    exact Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) _ _ (fun φ => rfl)
  rw [key, ← Algebra.coe_norm_int x]
  have hN0 : Algebra.norm ℤ x ≠ 0 := by
    intro h0
    have h5 : Algebra.norm ℚ (x : K) ≠ 0 := Algebra.norm_ne_zero_iff.mpr hx'
    apply h5
    rw [← Algebra.coe_norm_int x, h0, Int.cast_zero]
  rw [eq_ratCast, Rat.cast_intCast, Complex.norm_intCast]
  exact_mod_cast Int.one_le_abs hN0

theorem weber_function_root : WeberRoot := by
  intro x j s hs hj hx
  have hs0 : (s : ℂ) ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
  refine ⟨?_, ?_⟩
  · let R := integralClosure ℤ ℂ
    let jR : R := ⟨j, hj⟩
    let q : Polynomial R := (Polynomial.X - Polynomial.C (s : R)) ^ 3 - Polynomial.C jR * Polynomial.X
    have hq : q.Monic := by
      apply Polynomial.Monic.sub_of_left ((Polynomial.monic_X_sub_C _).pow 3)
      rw [Polynomial.degree_pow, Polynomial.degree_X_sub_C]
      refine lt_of_le_of_lt (Polynomial.degree_C_mul_X_le _) ?_
      norm_num
    have hxR : IsIntegral R x := by
      refine ⟨q, hq, ?_⟩
      simp only [q, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_C, Polynomial.eval₂_mul]
      simp only [map_intCast]
      have hjR : algebraMap R ℂ jR = j := rfl
      rw [hjR]
      linear_combination hx
    exact isIntegral_trans x hxR
  · intro h
    rw [h] at hx
    apply hs0
    have h3 : (s : ℂ) ^ 3 = 0 := by linear_combination -hx
    exact (pow_eq_zero_iff (by norm_num)).mp h3

end Formalism.HermitianLattices.IntegralLatticeDensity
end

-- bundled from Formalism.GL3MeanSquares.HookFormulaTorsion.HyperbolicPlaneSplit
section
namespace Formalism.HermitianLattices.IntegralLatticeDensity.PD

open Finset Formalism.HermitianLattices.IntegralLatticeDensity

section calculus

variable {M Q : Type} [AddCommGroup M] [AddCommGroup Q] {φ : M → Q}

theorem cob_symm' (a b : M) : cob φ a b = cob φ b a := by
  simp only [cob]
  rw [add_comm a b]
  abel

theorem phi_add' (a b : M) : φ (a + b) = φ a + φ b + cob φ a b := by
  simp only [cob]
  abel

theorem cob_add_right' (h1 : ∀ a a' b, cob φ (a + a') b = cob φ a b + cob φ a' b) (a b b' : M) :
    cob φ a (b + b') = cob φ a b + cob φ a b' := by
  rw [cob_symm', h1, cob_symm' b, cob_symm' b']

theorem cob_zero_left' (h1 : ∀ a a' b, cob φ (a + a') b = cob φ a b + cob φ a' b) (b : M) :
    cob φ 0 b = 0 := by
  have h := h1 0 0 b
  rw [add_zero] at h
  calc cob φ 0 b = (cob φ 0 b + cob φ 0 b) - cob φ 0 b := by abel
    _ = cob φ 0 b - cob φ 0 b := by rw [← h]
    _ = 0 := sub_self _

theorem cob_zero_right' (h1 : ∀ a a' b, cob φ (a + a') b = cob φ a b + cob φ a' b) (a : M) :
    cob φ a 0 = 0 := by
  rw [cob_symm', cob_zero_left' h1]

theorem phi_zero' (h1 : ∀ a a' b, cob φ (a + a') b = cob φ a b + cob φ a' b) : φ 0 = 0 := by
  have h := cob_zero_left' h1 (0 : M)
  simp only [cob, add_zero, sub_self, zero_sub, neg_eq_zero] at h
  exact h

theorem cob_sum_right' (h1 : ∀ a a' b, cob φ (a + a') b = cob φ a b + cob φ a' b)
    {J : Type} (a : M) (s : Finset J) (x : J → M) :
    cob φ a (∑ j ∈ s, x j) = ∑ j ∈ s, cob φ a (x j) := by
  induction s using Finset.cons_induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, cob_zero_right' h1]
  | cons j s hj ih => rw [Finset.sum_cons, Finset.sum_cons, cob_add_right' h1, ih]

theorem cob_sum_left' (h1 : ∀ a a' b, cob φ (a + a') b = cob φ a b + cob φ a' b)
    {J : Type} (b : M) (s : Finset J) (x : J → M) :
    cob φ (∑ j ∈ s, x j) b = ∑ j ∈ s, cob φ (x j) b := by
  induction s using Finset.cons_induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, cob_zero_left' h1]
  | cons j s hj ih => rw [Finset.sum_cons, Finset.sum_cons, h1, ih]

variable {O : Type} [CommRing O] [StarRing O] [Module O M]

theorem cross' (h1 : ∀ a a' b, cob φ (a + a') b = cob φ a b + cob φ a' b)
    (h2 : ∀ (α : O) a b, cob φ (α • a) b = cob φ a (star α • b))
    {n J : Type} [Fintype n] (c : n → O) (d : n → J → O) (a : M) (s : Finset J) (x : J → M) :
    ∑ i, cob φ (c i • a) (∑ j ∈ s, d i j • x j) =
      ∑ j ∈ s, cob φ a ((∑ i, star (c i) * d i j) • x j) := by
  simp_rw [h2, Finset.smul_sum, smul_smul, cob_sum_right' h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_smul, cob_sum_right' h1]

variable {Z : Type} [CommRing Z] [Module Z Q] {nm : O → Z}

theorem diag' (h1 : ∀ a a' b, cob φ (a + a') b = cob φ a b + cob φ a' b)
    (h2 : ∀ (α : O) a b, cob φ (α • a) b = cob φ a (star α • b))
    (h3 : ∀ (α : O) u, φ (α • u) = nm α • φ u)
    {n J : Type} [Fintype n] (c : n → J → O)
    (hG : ∀ a j, a ≠ j → ∑ i, star (c i a) * c i j = 0) (u : J → M) (s : Finset J) :
    ∑ i, φ (∑ j ∈ s, c i j • u j) = ∑ j ∈ s, (∑ i, nm (c i j)) • φ (u j) := by
  induction s using Finset.cons_induction with
  | empty => simp [phi_zero' h1]
  | cons k s hk ih =>
    have hcross : ∑ i, cob φ (c i k • u k) (∑ j ∈ s, c i j • u j) = 0 := by
      rw [cross' h1 h2 (fun i => c i k) c (u k) s u]
      refine Finset.sum_eq_zero fun j hj => ?_
      have hne : k ≠ j := by
        rintro rfl
        exact hk hj
      rw [hG k j hne, zero_smul, cob_zero_right' h1]
    simp only [Finset.sum_cons]
    simp only [phi_add', Finset.sum_add_distrib, h3]
    rw [hcross, ih, ← Finset.sum_smul, add_zero]

end calculus

end Formalism.HermitianLattices.IntegralLatticeDensity.PD

namespace Formalism.HermitianLattices.IntegralLatticeDensity

open Finset PD

theorem unitary_invariance : UnitaryInvariance := by
  intro Z O M Q _ _ _ _ _ _ _ _ φ nm hinj hnm h1 h2 h3 n _ _ δ hδ u
  have hG : ∀ a j, a ≠ j → ∑ i, star (δ i a) * δ i j = 0 := by
    intro a j hne
    have := congrFun (congrFun hδ a) j
    simpa [Matrix.mul_apply, Matrix.one_apply_ne hne] using this
  have hN : ∀ j, ∑ i, nm (δ i j) = 1 := by
    intro j
    apply hinj
    have := congrFun (congrFun hδ j) j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at this
    rw [map_sum, map_one]
    simpa [hnm] using this
  rw [diag' h1 h2 h3 δ hG u Finset.univ]
  simp [hN]

theorem hyperbolic_plane_split : HyperbolicSplit := by
  intro Z O M Q _ _ _ _ _ _ _ _ φ nm hinj hnm h1 h2 h3 n ι _ _ _ f f' hff hf'f' hff' t t'

  have hiso : ∀ (g : ι → n → O) (w : ι → M), (∀ e e', ∑ i, star (g e i) * g e' i = 0) →
      ∑ i, φ (∑ e, g e i • w e) = 0 := by
    intro g w hg
    have hz : ∀ e, ∑ i, nm (g e i) = 0 := by
      intro e
      apply hinj
      rw [map_sum, map_zero]
      simpa [hnm] using hg e e
    rw [diag' h1 h2 h3 (fun i e => g e i) (fun a j _ => hg a j) w Finset.univ]
    simp [hz]

  have hcross : ∑ i, cob φ (∑ e, f e i • t e) (∑ e, f' e i • t' e) = ∑ e, cob φ (t e) (t' e) := by
    simp_rw [cob_sum_left' h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [cross' h1 h2 (fun i => f e i) (fun i e' => f' e' i) (t e) Finset.univ t',
      Finset.sum_eq_single e]
    · rw [hff' e e, if_pos rfl, one_smul]
    · intro e' _ hne
      rw [hff' e e', if_neg (fun h => hne h.symm), zero_smul, cob_zero_right' h1]
    · intro h
      exact absurd (Finset.mem_univ e) h
  calc ∑ i, φ (∑ e, (f e i • t e + f' e i • t' e))
      = ∑ i, (φ (∑ e, f e i • t e) + φ (∑ e, f' e i • t' e) +
          cob φ (∑ e, f e i • t e) (∑ e, f' e i • t' e)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_add_distrib, phi_add' (φ := φ)]
    _ = ∑ e, cob φ (t e) (t' e) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hiso f t hff, hiso f' t' hf'f', hcross,
          zero_add, zero_add]

end Formalism.HermitianLattices.IntegralLatticeDensity
end

-- bundled from Formalism.GL3MeanSquares.HookFormulaTorsion.IntegralInverse
section
noncomputable section

namespace Formalism.HermitianLattices.ExpSeriesBivariate

open Finset

private theorem g3cw2_lin_integral {K : Type} [NormedField K] [IsUltrametricDist K] {σ τ : Type}
    [Fintype σ] (a : σ → K) (ha : ∀ k, ‖a k‖ ≤ 1) (g : σ → MvPowerSeries τ K)
    (hg : ∀ k, Formalism.G.IntegralMv (g k)) :
    Formalism.G.IntegralMv (∑ k, MvPowerSeries.C (a k) * g k) := by
  intro d
  rw [map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
  rw [MvPowerSeries.coeff_C_mul, norm_mul]
  exact mul_le_one₀ (ha k) (norm_nonneg _) (hg k d)

private theorem g3cw2_subst_lin {K : Type} [Field K] {σ ρ τ : Type} [Fintype σ]
    (a : σ → K) (g : σ → MvPowerSeries ρ K) (h : ρ → MvPowerSeries τ K)
    (hh : MvPowerSeries.HasSubst h) :
    MvPowerSeries.subst h (∑ k, MvPowerSeries.C (a k) * g k) =
      ∑ k, MvPowerSeries.C (a k) * MvPowerSeries.subst h (g k) := by
  rw [← MvPowerSeries.coe_substAlgHom (R := K) hh, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_C]

private theorem g3cw2_inv_lin {K : Type} [Field K] {σ τ : Type} [Fintype σ] [DecidableEq σ]
    (J J' : Matrix σ σ K) (hJ : J * J' = 1) (a : σ → MvPowerSeries τ K) (i : σ) :
    ∑ j, MvPowerSeries.C (J i j) * ∑ k, MvPowerSeries.C (J' j k) * a k = a i := by
  calc ∑ j, MvPowerSeries.C (J i j) * ∑ k, MvPowerSeries.C (J' j k) * a k
      = ∑ j, ∑ k, MvPowerSeries.C (J i j * J' j k) * a k := by
        simp_rw [Finset.mul_sum, ← mul_assoc, ← map_mul]
    _ = ∑ k, ∑ j, MvPowerSeries.C (J i j * J' j k) * a k := Finset.sum_comm
    _ = ∑ k, MvPowerSeries.C ((J * J') i k) * a k := by
        simp_rw [← Finset.sum_mul, ← map_sum, Matrix.mul_apply]
    _ = a i := by
        rw [hJ]
        simp [Matrix.one_apply]

theorem integralInverse_statement : IntegralInverse := by
  intro K _ _ σ _ _ T J' hT0 hTI hJ'I hLJ
  set L : Matrix σ σ K := Matrix.of fun i j => MvPowerSeries.coeff (Finsupp.single j 1) (T i) with hL
  have hJL : J' * L = 1 := (Matrix.mul_eq_one_comm_of_card_eq σ σ K rfl).mp hLJ
  have hTs : MvPowerSeries.HasSubst T := MvPowerSeries.hasSubst_of_constantCoeff_zero hT0

  let f : σ → MvPowerSeries σ K := fun j => ∑ i, MvPowerSeries.C (J' j i) * T i
  have hf0 : ∀ j, MvPowerSeries.constantCoeff (f j) = 0 := by
    intro j
    simp [f, map_sum, hT0]
  have hfI : ∀ j, Formalism.G.IntegralMv (f j) := fun j => g3cw2_lin_integral _ (fun i => hJ'I j i) _ hTI
  have hfId : Formalism.FG.IsIdMod2 f := by
    refine ⟨hf0, fun j m => ?_⟩
    have h1 : MvPowerSeries.coeff (Finsupp.single m 1) (f j) = (J' * L) j m := by
      simp only [f, map_sum, MvPowerSeries.coeff_C_mul, Matrix.mul_apply, hL, Matrix.of_apply]
    rw [h1, hJL, Matrix.one_apply]
    simp [eq_comm]
  have hTf : ∀ i, T i = ∑ j, MvPowerSeries.C (L i j) * f j := fun i => (g3cw2_inv_lin L J' hLJ T i).symm
  have hXI : ∀ k : σ, Formalism.G.IntegralMv (MvPowerSeries.X k : MvPowerSeries σ K) := by
    intro k d
    rw [MvPowerSeries.coeff_X]
    split_ifs <;> simp
  let G : σ → MvPowerSeries σ K := fun j => ∑ k, MvPowerSeries.C (J' j k) * MvPowerSeries.X k
  have hG0 : ∀ j, MvPowerSeries.constantCoeff (G j) = 0 := by
    intro j
    simp [G, map_sum]
  obtain ⟨X', hX'0, hX'⟩ := Formalism.FG.solve_exists_vector K σ σ f G hfId hG0
  have hX's : MvPowerSeries.HasSubst X' := MvPowerSeries.hasSubst_of_constantCoeff_zero hX'0
  have hX'I : ∀ i, Formalism.G.IntegralMv (X' i) := by
    refine Formalism.FG.inverse_integral_vector K σ σ (fun D => ∀ j, Formalism.G.IntegralMv (D j)) f hfId ?_ ?_ ?_ X' hX'0 ?_
    · intro a b ha hb j d
      rw [Pi.sub_apply, map_sub]
      rw [sub_eq_add_neg]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans
        (max_le (ha j d) (by rw [norm_neg]; exact hb j d))
    · intro P hP0 hPI j
      exact Formalism.FG.IntegralSubstitution.integralSubstV (f j) P (hfI j) hP0 hPI
    · intro D hD N _ _ j d _
      exact hD j d
    · intro j
      show Formalism.G.IntegralMv (MvPowerSeries.subst X' (f j))
      rw [hX' j]
      exact g3cw2_lin_integral _ (fun k => hJ'I j k) _ hXI
  refine ⟨X', hX'0, hX'I, fun i => ?_, fun i => ?_⟩
  · rw [hTf i, g3cw2_subst_lin _ f X' hX's]
    simp_rw [hX']
    exact g3cw2_inv_lin L J' hLJ (fun k => MvPowerSeries.X k) i
  ·
    have key := Formalism.FG.subst_injective_vector K σ σ f (fun i => MvPowerSeries.subst T (X' i))
      (fun i => MvPowerSeries.X i) hfId
      (fun i => MvPowerSeries.constantCoeff_subst_eq_zero hTs hT0 (hX'0 i))
      (fun i => MvPowerSeries.constantCoeff_X i) (fun j => ?_)
    · exact congrFun key i
    · rw [← MvPowerSeries.subst_comp_subst_apply hX's hTs, hX' j]
      show MvPowerSeries.subst T (G j) = MvPowerSeries.subst MvPowerSeries.X (f j)
      rw [MvPowerSeries.subst_self, g3cw2_subst_lin _ _ T hTs]
      simp_rw [MvPowerSeries.subst_X hTs]
      rfl

end Formalism.HermitianLattices.ExpSeriesBivariate
end
end

