import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0002
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0020
import Formalism.LocalToGlobal.CharacterGerms.BiadditiveInSingleVariables
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuation
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0009
import Formalism.DropLevelBounds.Statement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.DmonOfMulCongrOfCongr
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory

theorem dmonOf_mul_congr_of_congr :
  (∀ (R : Type) [CommRing R] (d : ℕ) (F : Fin d → PS R 2 d) (I : Ideal R) (ι : Type) [Fintype ι] (u : ι → Fin d → R) (f f' g : PS R 1 d),
    (∀ mo : ι →₀ ℕ, constantCoeff (DmonOf F u mo f) - constantCoeff (DmonOf F u mo f') ∈ I) →
    ∀ mo : ι →₀ ℕ, constantCoeff (DmonOf F u mo (f * g)) - constantCoeff (DmonOf F u mo (f' * g)) ∈ I) := by
  intro R _ d F I ι _ u f f' g h mo
  have hsub : ∀ (m : ι →₀ ℕ) (a b : PS R 1 d),
      DmonOf F u m (a - b) = DmonOf F u m a - DmonOf F u m b := fun m a b => by
    have e := ExpCong.along_add (fun l => Dof F (u l)) (fun l => GE.dof_add F (u l))
      (ExpCong.grouped (Finset.univ : Finset ι).toList m).reverse (a - b) b
    rw [sub_add_cancel, ← ExpCong.dmonOf_eq_along, ← ExpCong.dmonOf_eq_along,
      ← ExpCong.dmonOf_eq_along] at e
    rw [e, add_sub_cancel_right]
  have key := ExpCong.along_mul_mem (fun l => Dof F (u l)) (constantCoeff : PS R 1 d →+* R)
    (fun a => GE.dof_add F (u a)) (fun a => GE.dof_mul F (u a)) Set.univ I.toAddSubgroup
    (fun s _ j hj => I.mul_mem_left s hj)
    (ExpCong.grouped (Finset.univ : Finset ι).toList mo).reverse g (f - f')
    (fun _ _ => Set.mem_univ _)
    (fun v hv => by
      obtain ⟨m', hm'⟩ := ExpCong.exists_along_eq_dmonOf F u mo v hv
      rw [hm', hsub, map_sub]
      exact h m')
  rw [← ExpCong.dmonOf_eq_along, show g * (f - f') = f * g - f' * g by ring, hsub, map_sub] at key
  exact key

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LegendreAndCapelli
section
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds

namespace GlobalTheory.LegendreFacts

open GlobalTheory.LegendreBounds

theorem mfact_eq_prod {σ : Type} [Fintype σ] (A : σ →₀ ℕ) :
    mfact A = ∏ j, (A j).factorial := by
  unfold mfact
  exact Finsupp.prod_fintype A _ (fun _ => Nat.factorial_zero)

theorem degree_eq_sum' {σ : Type} [Fintype σ] (A : σ →₀ ℕ) : A.degree = ∑ j, A j := by
  rw [Finsupp.degree_apply]
  refine Finset.sum_subset (Finset.subset_univ _) ?_
  intro j _ hj
  simpa using hj

theorem capNat_mul (n0 x : ℕ) :
    capNat n0 x * ∏ c ∈ Finset.range n0, c.factorial
      = ∏ c ∈ Finset.range n0, (x + c).factorial := by
  unfold capNat
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl ?_
  intro c _
  exact Nat.div_mul_cancel (Nat.factorial_dvd_factorial (Nat.le_add_left c x))

private lemma padicValNat_factorial_eq_div_of_lt_sq (l : ℕ) (hl : l.Prime) (N : ℕ) (hN : N < l ^ 2) :
    padicValNat l N.factorial = N / l := by
  have : Fact l.Prime := ⟨hl⟩
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · subst h0
    simp
  · rw [padicValNat_factorial (b := 2) (Nat.log_lt_of_lt_pow hpos.ne' hN)]
    simp

theorem legendre_facts : F2 := by
  intro l hl
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  have hden : (0 : ℝ) < (l : ℝ) - 1 := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro N
    have h := legendre_real l hl N
    simpa using h
  · intro N _
    have h := digitSum_le l N hl.one_lt
    rw [Real.natFloor_logb_natCast]
    have hc : (((Nat.digits l N).sum : ℕ) : ℝ) ≤ (((Nat.log l N + 1) * (l - 1) : ℕ) : ℝ) := by
      exact_mod_cast h
    rw [Nat.cast_mul, Nat.cast_sub hl.one_lt.le, Nat.cast_add, Nat.cast_one] at hc
    rw [mul_comm]
    exact hc
  · intro σ _ A hA
    rw [mfact_eq_prod, degree_eq_sum']
    rw [degree_eq_sum'] at hA
    constructor
    · have h := ((legendre_bounds l hl).2.1) σ (fun j => A j) hA
      simpa using h
    · rw [padicValNat_prod_factorial l hl Finset.univ (fun j => A j)]
      have hterm : ∀ j ∈ (Finset.univ : Finset σ),
          (padicValNat l (A j).factorial : ℝ) ≤ (A j : ℝ) / ((l : ℝ) - 1) :=
        fun j _ => upper l hl (A j)
      calc ∑ j, (padicValNat l (A j).factorial : ℝ)
          ≤ ∑ j, (A j : ℝ) / ((l : ℝ) - 1) := Finset.sum_le_sum hterm
        _ = ((∑ j, A j : ℕ) : ℝ) / ((l : ℝ) - 1) := by
          rw [← Finset.sum_div]
          push_cast
          rfl
  · intro N hN
    exact padicValNat_factorial_eq_div_of_lt_sq l hl N hN

theorem capelli_bound : F3 := by
  intro l hl n0 n x hn hn0
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  have : Fact l.Prime := ⟨hl⟩
  constructor
  · have hP : (∏ c ∈ Finset.range n0, c.factorial) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun c _ => Nat.factorial_ne_zero c)
    have hC : capNat n0 x ≠ 0 := by
      intro h0
      have h := capNat_mul n0 x
      rw [h0, zero_mul] at h
      exact (Finset.prod_ne_zero_iff.mpr (fun c _ => Nat.factorial_ne_zero (x + c))) h.symm
    have hv : padicValNat l (capNat n0 x) + padicValNat l (∏ c ∈ Finset.range n0, c.factorial)
        = padicValNat l (∏ c ∈ Finset.range n0, (x + c).factorial) := by
      rw [← padicValNat.mul hC hP, capNat_mul]
    have hvR : (padicValNat l (capNat n0 x) : ℝ)
        = (padicValNat l (∏ c ∈ Finset.range n0, (x + c).factorial) : ℝ)
          - (padicValNat l (∏ c ∈ Finset.range n0, c.factorial) : ℝ) := by
      rw [← hv]
      push_cast
      ring
    have h := ((legendre_bounds l hl).2.2) n0 x
    rw [hvR]
    exact h
  · have hlogn : 0 ≤ Real.logb l n := Real.logb_nonneg hl1 (by exact_mod_cast hn)
    have hnn : (n0 : ℝ) ≤ n := by exact_mod_cast hn0
    rcases Nat.eq_zero_or_pos n0 with h0 | hpos
    · subst h0
      have : (0 : ℝ) ≤ (n : ℝ) * (Real.logb l n + 1) := by positivity
      simpa using this
    · have hpos' : (0 : ℝ) < n0 := by exact_mod_cast hpos
      have hlog0 : 0 ≤ Real.logb l n0 := Real.logb_nonneg hl1 (by exact_mod_cast hpos)
      have hle : Real.logb l n0 ≤ Real.logb l n := Real.logb_le_logb_of_le hl1 hpos' hnn
      have : (n0 : ℝ) * (Real.logb l n0 + 1) ≤ n * (Real.logb l n + 1) :=
        mul_le_mul hnn (by linarith) (by linarith) (by positivity)
      linarith

end GlobalTheory.LegendreFacts
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NewtonBoundPosAndNewtonStep
section
open Formalism.L2.FormalSeriesBounds

namespace GlobalTheory

private lemma sum_range_succ_choose_mul_eq_add_shift {C : Type} [Field C] (f : ℕ → C) (y : ℕ) :
    ∑ s ∈ Finset.range (y + 1 + 1), ((y + 1).choose s : C) * f s =
      ∑ s ∈ Finset.range (y + 1), (y.choose s : C) * f s +
        ∑ s ∈ Finset.range (y + 1), (y.choose s : C) * f (s + 1) := by
  rw [Finset.sum_range_succ' (fun s => ((y + 1).choose s : C) * f s)]
  simp_rw [Nat.choose_succ_succ', Nat.cast_add, add_mul, Finset.sum_add_distrib]
  rw [Finset.sum_range_succ' (fun s => (y.choose s : C) * f s),
    Finset.sum_range_succ (fun s => (y.choose (s + 1) : C) * f (s + 1)), Nat.choose_succ_self]
  simp
  ring

theorem _root_.GlobalTheory.newtonBound_pos_and_newtonStep : _root_.Formalism.L2.FormalSeriesBounds.NewtonBoundPositive ∧ _root_.Formalism.L2.FormalSeriesBounds.P7 := by
  refine ⟨?_, ?_⟩
  · unfold _root_.Formalism.L2.FormalSeriesBounds.NewtonBoundPositive
    intro l hl i n0 s hi hn hs
    unfold _root_.Formalism.L2.FormalSeriesBounds.S0 at hs
    have hl' : (5:ℝ) ≤ l := by exact_mod_cast hl
    have hN : (1:ℝ) ≤ n0 := by exact_mod_cast hn
    have hi' : (1:ℝ) ≤ i := by exact_mod_cast hi
    have hlogl : 1 ≤ Real.log l := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      have := Real.exp_one_lt_d9
      linarith
    have hlbN1 : 0 ≤ Real.logb l ((n0:ℝ) + 1) := Real.logb_nonneg (by linarith) (by linarith)
    have hsK : 64 * (n0:ℝ) ^ 2 * ((i:ℝ) + 3 + 3 * Real.logb l ((n0:ℝ) + 1)) ≤ (s:ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hs)
    have hN2 : 0 < 64 * (n0:ℝ) ^ 2 := by positivity
    set t : ℝ := (s:ℝ) / (64 * (n0:ℝ) ^ 2) with ht
    have hst : (s:ℝ) = t * 64 * (n0:ℝ) ^ 2 := by rw [ht]; field_simp
    have htK : (i:ℝ) + 3 + 3 * Real.logb l ((n0:ℝ) + 1) ≤ t := by
      rw [ht, le_div_iff₀ hN2]; linarith
    have ht0 : 0 < t := by linarith
    have hlogs : Real.logb l s = Real.logb l t + Real.logb l 64 + 2 * Real.logb l n0 := by
      rw [hst, Real.logb_mul (by positivity) (by positivity), Real.logb_mul (by positivity) (by norm_num),
        Real.logb_pow]
      push_cast
      ring
    have hlbt : Real.logb l t ≤ t - 1 := by
      have h1 := Real.log_le_sub_one_of_pos ht0
      have h2 : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
      rw [Real.logb, div_le_iff₀ (by linarith)]
      nlinarith
    have hlb64 : Real.logb l 64 ≤ 3 := by
      have h3 : Real.logb l ((l:ℝ) ^ 3) = 3 := by
        rw [Real.logb_pow, Real.logb_self_eq_one (by linarith)]
        norm_num
      rw [← h3]
      apply Real.logb_le_logb_of_le (by linarith) (by norm_num)
      have hcube : (5:ℝ) ^ 3 ≤ (l:ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) hl' 3
      linarith
    have hlbN : Real.logb l n0 ≤ Real.logb l ((n0:ℝ) + 1) :=
      Real.logb_le_logb_of_le (by linarith) (by linarith) (by linarith)
    have key : 3 * Real.logb l n0 + 2 * Real.logb l s + i + 3 < 8 * t := by
      rw [hlogs]
      nlinarith
    have hs8 : (s:ℝ) / 8 = 8 * t * (n0:ℝ) ^ 2 := by rw [hst]; ring
    rw [hs8]
    have hpos : 0 < (n0:ℝ) ^ 2 := by positivity
    nlinarith [mul_lt_mul_of_pos_left key hpos]
  · unfold _root_.Formalism.L2.FormalSeriesBounds.P7
    intro C _ v S a hS ha0 hpos Y0
    by_contra hcon
    push_neg at hcon
    have hadd : ∀ x y : C, 0 < v x → 0 < v y → 0 < v (x + y) := fun x y hx hy =>
      lt_of_lt_of_le (lt_min hx hy) (v.map_add x y)
    have hsub : ∀ x y : C, 0 < v x → 0 < v y → 0 < v (x - y) := fun x y hx hy => by
      rw [sub_eq_add_neg]
      exact hadd _ _ hx (by rwa [v.map_neg])
    have hnat : ∀ (c : ℕ) (x : C), 0 < v x → 0 < v ((c : C) * x) := fun c x hx => by
      rw [v.map_mul]
      have h := _root_.ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.intCast_nonneg v (c : ℤ)
      rw [Int.cast_natCast] at h
      exact lt_of_lt_of_le hx (le_add_of_nonneg_left h)
    have hsum : ∀ (s : Finset ℕ) (f : ℕ → C), (∀ j ∈ s, 0 < v (f j)) → 0 < v (∑ j ∈ s, f j) := by
      intro s f hf
      induction s using Finset.induction_on with
      | empty => simp
      | insert j s hj ih =>
        rw [Finset.sum_insert hj]
        exact hadd _ _ (hf j (Finset.mem_insert_self _ _))
          (ih fun x hx => hf x (Finset.mem_insert_of_mem hx))
    set B : ℕ → ℕ → C := fun k y => ∑ s ∈ Finset.range (y + 1), (y.choose s : C) * a (s + k) with hB
    have hpascal : ∀ k y, B (k + 1) y = B k (y + 1) - B k y := by
      intro k y
      simp only [hB]
      rw [sum_range_succ_choose_mul_eq_add_shift (fun s => a (s + k)) y]
      have : ∀ s, a (s + 1 + k) = a (s + (k + 1)) := fun s => by rw [add_assoc, add_comm 1 k]
      simp only [this]
      ring
    have hup : ∀ k, k < S → ∀ y, Y0 ≤ y → y + k < Y0 + S → 0 < v (B k y) := by
      intro k
      induction k with
      | zero =>
        intro _ y h1 h2
        simpa [hB] using hcon y h1 (by omega)
      | succ k ih =>
        intro hk y h1 h2
        rw [hpascal]
        exact hsub _ _ (ih (by omega) (y + 1) (by omega) (by omega)) (ih (by omega) y h1 (by omega))
    have hbig : ∀ k, S ≤ k → ∀ y, 0 < v (B k y) := fun k hk y =>
      hsum _ _ fun s _ => hnat _ _ (hpos _ (by omega))
    have hdown : ∀ d, d ≤ Y0 → ∀ k, 0 < v (B k (Y0 - d)) := by
      intro d
      induction d with
      | zero =>
        intro _ k
        by_cases hk : k < S
        · exact hup k hk Y0 le_rfl (by simpa using hk)
        · exact hbig k (by omega) _
      | succ d ih =>
        intro hd
        have hy : Y0 - d = Y0 - (d + 1) + 1 := by omega
        have main : ∀ m k, S ≤ k + m → 0 < v (B k (Y0 - (d + 1))) := by
          intro m
          induction m with
          | zero => intro k hk; exact hbig k (by omega) _
          | succ m ihm =>
            intro k hk
            have e := hpascal k (Y0 - (d + 1))
            have : B k (Y0 - (d + 1)) = B k (Y0 - (d + 1) + 1) - B (k + 1) (Y0 - (d + 1)) := by
              rw [e]; ring
            rw [this, ← hy]
            exact hsub _ _ (ih (by omega) k) (ihm (k + 1) (by omega))
        exact fun k => main S k (by omega)
    have h0 := hdown Y0 le_rfl 0
    simp [hB, ha0] at h0

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ParametersSmallBoundStatement
section
open Formalism.UnitaryBoundIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sizeData_small_bound : ParametersSmall := by
  first | exact @GlobalTheory.FlowParameters.sizeDataSmall | exact GlobalTheory.FlowParameters.sizeDataSmall | (intros; apply GlobalTheory.FlowParameters.sizeDataSmall <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ProdIccMulFactorial
section
open Formalism.L2.FormalSeriesBounds

noncomputable section

namespace GlobalTheory.CayleyCapelli

open MvPolynomial Formalism.IncomingBounds ReciprocityTheory.PGsh GlobalTheory.DetPowPairing

variable {σ : Type} {C : Type} [Field C]

theorem wt_eq (A : σ →₀ ℕ) : wt C A = (mfact A : C) := by
  simp [wt, mfact, Finsupp.prod, Nat.cast_prod]

theorem mfact_ne_zero [CharZero C] (A : σ →₀ ℕ) : (mfact A : C) ≠ 0 := by
  rw [Nat.cast_ne_zero, mfact, Finsupp.prod]
  exact Finset.prod_ne_zero_iff.2 fun _ _ => Nat.factorial_ne_zero _

theorem jetAt0_coe (P Q : MvPolynomial σ C) :
    jetAt0 P (Q : MvPowerSeries σ C) = pair P Q := by
  rw [pair_eq, jetAt0]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_coe, wt_eq]

theorem pair_diffOp [CharZero C] (B : σ →₀ ℕ) (P Q : MvPolynomial σ C) :
    pair (monomial B (1 : C)) (diffOp P Q) = pair (monomial B (1 : C) * P) Q := by
  classical
  have hinner : ∀ m : σ →₀ ℕ, coeff B (∑ a ∈ Q.support, if m ≤ a then
      monomial (a - m) (coeff m P * coeff a Q * ((mfact a : C) / (mfact (a - m) : C))) else 0) =
      coeff m P * coeff (B + m) Q * ((mfact (B + m) : C) / (mfact B : C)) := by
    intro m
    rw [coeff_sum, Finset.sum_eq_single (B + m)]
    · rw [if_pos (le_add_self), coeff_monomial, add_tsub_cancel_right, if_pos rfl]
    · intro a _ ha
      split_ifs with hma
      · rw [coeff_monomial, if_neg]
        intro hB
        exact ha (by rw [← hB, tsub_add_cancel_of_le hma])
      · exact coeff_zero B
    · intro hQ
      rw [notMem_support_iff] at hQ
      rw [hQ, if_pos (le_add_self), coeff_monomial, add_tsub_cancel_right, if_pos rfl, mul_zero, zero_mul]
  have hP : monomial B (1 : C) * P = ∑ m ∈ P.support, monomial (B + m) (coeff m P) := by
    conv_lhs => rw [P.as_sum]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [monomial_mul, one_mul]
  rw [pair_monomial, diffOp, coeff_sum, hP, map_sum, LinearMap.sum_apply, wt_eq, one_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [hinner, pair_monomial, wt_eq]
  have := mfact_ne_zero (C := C) B
  field_simp

theorem eq_of_pair [CharZero C] {P Q : MvPolynomial σ C}
    (h : ∀ B : σ →₀ ℕ, pair (monomial B (1 : C)) P = pair (monomial B (1 : C)) Q) : P = Q := by
  ext B
  have hB := h B
  rw [pair_monomial, pair_monomial, one_mul, wt_eq] at hB
  exact mul_left_cancel₀ (mfact_ne_zero B) hB

theorem detL_eq (n : ℕ) : detL C n = rename Sum.inl (cayDet n C) := by
  rw [detL, cayDet, AlgHom.map_det]
  congr 1
  ext b c
  simp [Matrix.mvPolynomialX]

theorem list_rename {ι τ : Type} (g : σ → τ) (hg : Function.Injective g) (f : ι → σ) (l : List ι)
    (Q : MvPolynomial σ C) :
    ((l.map fun j => ((pderiv (g (f j)) : Derivation C _ _) :
        MvPolynomial τ C →ₗ[C] MvPolynomial τ C)).prod : Module.End C (MvPolynomial τ C))
        (rename g Q) =
      rename g (((l.map fun j => ((pderiv (f j) : Derivation C _ _) :
        MvPolynomial σ C →ₗ[C] MvPolynomial σ C)).prod : Module.End C (MvPolynomial σ C)) Q) := by
  induction l with
  | nil => simp
  | cons j l ih =>
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, ih]
    exact pderiv_rename hg _ _

theorem pair_detL (n : ℕ) (P : MvPolynomial (PVar n) C) (Q : MvPolynomial (Fin n × Fin n) C) :
    pair (P * detL C n) (rename Sum.inl Q) = pair P (rename Sum.inl (cayOp n C Q)) := by
  have hσ : ∀ τ : Equiv.Perm (Fin n), pair (P * ∏ i, (X (Sum.inl (τ i, i)) : MvPolynomial (PVar n) C))
      (rename Sum.inl Q) = pair P (rename Sum.inl (cayMono n C τ Q)) := by
    intro τ
    have h1 := pair_list (C := C) (fun j : Fin n => (Sum.inl (τ j, j) : PVar n)) (List.finRange n) P
      (rename Sum.inl Q)
    have h2 := list_rename (C := C) (Sum.inl : Fin n × Fin n → PVar n) Sum.inl_injective
      (fun j : Fin n => (τ j, j)) (List.finRange n) Q
    rw [Fin.prod_univ_def, h1, h2]
    rfl
  rw [detL, Matrix.det_apply', Finset.mul_sum, map_sum, LinearMap.sum_apply, cayOp, LinearMap.sum_apply,
    map_sum, map_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [LinearMap.smul_apply, map_zsmul, map_zsmul, ← hσ τ, mul_left_comm, ← zsmul_eq_mul, map_zsmul,
    LinearMap.smul_apply]
  rfl

theorem pair_detL_pow (n s : ℕ) (P : MvPolynomial (PVar n) C) :
    pair (P * detL C n) (detL C n ^ (s + 1)) =
      ((∏ c ∈ Finset.range n, (s + 1 + c) : ℕ) : C) * pair P (detL C n ^ s) := by
  have e : detL C n ^ (s + 1) = rename Sum.inl (cayDet n C ^ (s + 1)) := by rw [detL_eq, map_pow]
  rw [e, pair_detL, cayley n C (s + 1), Nat.add_sub_cancel, map_nsmul, map_nsmul,
    nsmul_eq_mul, map_pow, ← detL_eq]

theorem cayleyId : CayleyId := by
  intro K _ _ n s
  refine eq_of_pair fun B => ?_
  rw [pair_diffOp, pair_detL_pow, map_smul, smul_eq_mul]
  push_cast
  rfl

theorem pair_pow_self (n x : ℕ) :
    pair (detL C n ^ x) (detL C n ^ x) =
      ((∏ t ∈ Finset.Icc 1 x, ∏ c ∈ Finset.range n, (t + c) : ℕ) : C) := by
  induction x with
  | zero =>
    rw [pow_zero, ← MvPolynomial.C_1, MvPolynomial.C_apply, pair_monomial, wt_eq]
    simp [mfact]
  | succ x ih =>
    have h := pair_detL_pow n x (detL C n ^ x)
    rw [← pow_succ] at h
    rw [h, ih, Finset.prod_Icc_succ_top (by omega), Nat.cast_mul, mul_comm]

theorem prod_Icc_mul_factorial (x c : ℕ) :
    (∏ t ∈ Finset.Icc 1 x, (t + c)) * c.factorial = (x + c).factorial := by
  induction x with
  | zero => simp
  | succ x ih =>
    rw [Finset.prod_Icc_succ_top (by omega), mul_right_comm, ih, show x + 1 + c = (x + c) + 1 by omega,
      Nat.factorial_succ, mul_comm]

theorem prod_eq_capNat (n x : ℕ) :
    (∏ t ∈ Finset.Icc 1 x, ∏ c ∈ Finset.range n, (t + c)) = capNat n x := by
  rw [capNat, Finset.prod_comm]
  refine Finset.prod_congr rfl fun a _ => ?_
  exact (Nat.div_eq_of_eq_mul_left (Nat.factorial_pos a) (prod_Icc_mul_factorial x a).symm).symm

theorem main : F1 ∧ CapacityFactorialProduct := by
  refine ⟨cayleyId, ?_⟩
  intro K _ _ n x
  refine ⟨by rw [jetAt0_coe, pair_pow_self], prod_eq_capNat n x,
    fun c => Nat.factorial_dvd_factorial (by omega), ?_⟩
  rw [← prod_eq_capNat]
  refine Finset.prod_ne_zero_iff.2 fun t ht => Finset.prod_ne_zero_iff.2 fun c _ => ?_
  rw [Finset.mem_Icc] at ht
  omega

end GlobalTheory.CayleyCapelli
end
end

