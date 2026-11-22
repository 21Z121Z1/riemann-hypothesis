import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0075
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0128
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0166
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0168
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0059
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0169
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0085
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0005
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0143
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0156
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0139
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0081
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyMeasAndReps
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TendstoBadWindowDivRho
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

namespace GlobalTheory.UnitLemma.Desc

open Classical in

noncomputable def badWinBox {ι : Type} (S I : Finset ι) (L k : ℕ) (i₀ i : ι) : Finset ℤ :=
  if i ∈ S then (if i ∈ I then Finset.Icc (2 * (k : ℤ) - L) (2 * k + L) else Finset.Icc (-(L : ℤ)) L)
  else if i = i₀ then Finset.Ico (-(L : ℤ)) L ∪ Finset.Ioc (2 * (k : ℤ) - L) (2 * k + L)
  else Finset.Icc (-(L : ℤ)) (2 * k + L)

open Classical in
theorem card_badWinBox_le {ι : Type} (S I : Finset ι) (L k : ℕ) (i₀ i : ι) :
    (badWinBox S I L k i₀ i).card ≤
      2 * (2 * L + 1) * (if i ∈ insert i₀ S then 1 else k + 1) := by
  unfold badWinBox
  by_cases hS : i ∈ S
  · have : i ∈ insert i₀ S := Finset.mem_insert_of_mem hS
    rw [if_pos hS, if_pos this]
    split_ifs <;> simp [Int.card_Icc] <;> omega
  · rw [if_neg hS]
    by_cases h0 : i = i₀
    · subst h0
      rw [if_pos rfl, if_pos (Finset.mem_insert_self _ _)]
      refine (Finset.card_union_le _ _).trans ?_
      simp [Int.card_Ico, Int.card_Ioc]; omega
    · rw [if_neg h0, if_neg (by simp [h0, hS])]
      simp [Int.card_Icc]
      nlinarith

open Classical in
theorem card_piFinset_badWinBox_le {ι : Type} [Fintype ι] (S I : Finset ι) (L k : ℕ) (i₀ : ι) (h₀ : i₀ ∉ S) :
    (Fintype.piFinset (badWinBox S I L k i₀)).card ≤
      (2 * (2 * L + 1)) ^ Fintype.card ι * (k + 1) ^ (Fintype.card ι - S.card - 1) := by
  rw [Fintype.card_piFinset]
  refine (Finset.prod_le_prod (fun _ _ => Nat.zero_le _) fun i _ => card_badWinBox_le S I L k i₀ i).trans ?_
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Finset.prod_ite, Finset.prod_const_one,
    one_mul, Finset.prod_const]
  have : (Finset.univ.filter fun i => i ∉ insert i₀ S).card = Fintype.card ι - S.card - 1 := by
    have h : (Finset.univ.filter fun i => i ∉ insert i₀ S) = (insert i₀ S)ᶜ := by ext; simp
    rw [h, Finset.card_compl, Finset.card_insert_of_notMem h₀]; omega
  rw [this]

end GlobalTheory.UnitLemma.Desc

namespace GlobalTheory.UnitLemma.Desc

theorem tendsto_badWindow_div_rho : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] (e π : ι → B.A) (S : Finset ι) (a : K.O), B.P.Separable → K.Small a → IsFrame B e π S → ∀ (I I' : Finset ι), (∀ i ∈ S, i ∈ I ∨ i ∈ I') → ∀ (N L : ℕ) (D : ℚ) (f : ℕ → Submodule K.O B.A → ℚ), (∀ M ∈ B.Lin, ∃ p, Pos B a e N M p) → (∀ k M, |f k M| ≤ D) → (∀ k, L ≤ k → ∀ M ∈ B.Lin, ∀ p, Pos B a e N M p → f k M ≠ 0 → Win I I' L k p ∧ ¬ Mid S L k p) → Tendsto (fun k : ℕ => ((∑ᶠ M ∈ B.Lin, f k M : ℚ) : ℝ) / (B.rho (algebraMap K.O B.A a ^ k) : ℝ)) atTop (𝓝 0) := by
  intro K B ι _ e π S a hsep ha hfr I I' hI N L D f hpos hD hsupp
  classical
  obtain ⟨C, hC⟩ := GlobalTheory.T.card_lattices_idempotent_position_bounded K B ι e π S a hsep ha hfr N
  have hrho := GlobalTheory.T.rho_pow_lower_bound_swappedPairs K B ι e π S a hsep ha hfr
  have hD0 : 0 ≤ D := le_trans (abs_nonneg _) (hD 0 ⊥)
  set n := Fintype.card ι
  set m := n - S.card
  set A : ℕ := 2 * (2 * L + 1)
  have key : ∀ k, L ≤ k → |∑ᶠ M ∈ B.Lin, f k M| ≤ D * ((m * A ^ n * (k + 1) ^ (m - 1) * C : ℕ) : ℚ) := by
    intro k hk
    let W : Finset (ι → ℤ) :=
      (Finset.univ.filter (· ∉ S)).biUnion fun i₀ => Fintype.piFinset (badWinBox S I L k i₀)
    have hWcard : W.card ≤ m * A ^ n * (k + 1) ^ (m - 1) := by
      refine Finset.card_biUnion_le.trans ?_
      have h1 : ∀ i₀ ∈ Finset.univ.filter (· ∉ S),
          (Fintype.piFinset (badWinBox S I L k i₀)).card ≤ A ^ n * (k + 1) ^ (m - 1) := by
        intro i₀ hi₀
        exact card_piFinset_badWinBox_le S I L k i₀ (Finset.mem_filter.1 hi₀).2
      refine (Finset.sum_le_sum h1).trans ?_
      rw [Finset.sum_const, smul_eq_mul]
      have h2 : (Finset.univ.filter (· ∉ S)).card = m := by
        have h : (Finset.univ.filter (· ∉ S)) = Sᶜ := by ext; simp
        rw [h, Finset.card_compl]
      rw [h2, mul_assoc]
    have hmem : ∀ M ∈ B.Lin, f k M ≠ 0 → ∃ p ∈ W, Pos B a e N M p := by
      intro M hM hf
      obtain ⟨p, hp⟩ := hpos M hM
      obtain ⟨hw, hmid⟩ := hsupp k hk M hM p hp hf
      refine ⟨p, ?_, hp⟩
      simp only [W, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
      unfold Mid at hmid
      push_neg at hmid
      obtain ⟨i₀, hi₀, h₀⟩ := hmid
      refine ⟨i₀, hi₀, fun i => ?_⟩
      obtain ⟨h1, h2, h3, h4⟩ := hw i
      unfold badWinBox
      by_cases hS : i ∈ S
      · rw [if_pos hS]
        by_cases hiI : i ∈ I
        · rw [if_pos hiI]; simp only [Finset.mem_Icc]; exact ⟨h3 hiI, h2⟩
        · rw [if_neg hiI]
          have := (hI i hS).resolve_left hiI
          simp only [Finset.mem_Icc]; exact ⟨h1, h4 this⟩
      · rw [if_neg hS]
        by_cases h0 : i = i₀
        · subst h0
          rw [if_pos rfl]
          simp only [Finset.mem_union, Finset.mem_Ico, Finset.mem_Ioc]
          by_cases hl : (L : ℤ) ≤ p i
          · exact Or.inr ⟨h₀ hl, h2⟩
          · exact Or.inl ⟨h1, lt_of_not_ge hl⟩
        · rw [if_neg h0]; simp only [Finset.mem_Icc]; exact ⟨h1, h2⟩
    let T : Finset (Submodule K.O B.A) := W.biUnion fun p => (hC p).1.toFinset
    have hTcard : T.card ≤ W.card * C := by
      refine Finset.card_biUnion_le.trans ?_
      refine (Finset.sum_le_sum fun p _ => ?_).trans (by rw [Finset.sum_const, smul_eq_mul])
      rw [← Set.ncard_eq_toFinset_card _ (hC p).1]
      exact (hC p).2
    have hfs : ∑ᶠ M ∈ B.Lin, f k M = ∑ M ∈ T.filter (· ∈ B.Lin), f k M := by
      apply finsum_mem_eq_sum_of_inter_support_eq
      ext M
      simp only [Set.mem_inter_iff, Function.mem_support, Finset.coe_filter, Set.mem_setOf_eq]
      constructor
      · rintro ⟨hM, hf⟩
        refine ⟨⟨?_, hM⟩, hf⟩
        obtain ⟨p, hpW, hp⟩ := hmem M hM hf
        simp only [T, Finset.mem_biUnion, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
        exact ⟨p, hpW, hp⟩
      · rintro ⟨⟨_, hM⟩, hf⟩
        exact ⟨hM, hf⟩
    rw [hfs]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun M _ => hD k M).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ hD0
    have : (T.filter (· ∈ B.Lin)).card ≤ m * A ^ n * (k + 1) ^ (m - 1) * C :=
      (Finset.card_filter_le _ _).trans (hTcard.trans (Nat.mul_le_mul_right _ hWcard))
    exact_mod_cast this
  have hm : ∀ k : ℕ, m * (k + 1) ^ (m - 1) * (k + 1) = m * (k + 1) ^ m := by
    intro k
    rcases Nat.eq_zero_or_pos m with h | h
    · simp [h]
    · rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel h]
  set c : ℝ := (D : ℝ) * (A : ℝ) ^ n * (m : ℝ) * (C : ℝ)
  have hlim : Tendsto (fun k : ℕ => c * (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul c
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop L] with k hk
  have hr : ((k + 1 : ℕ) : ℝ) ^ m ≤ (B.rho (algebraMap K.O B.A a ^ k) : ℝ) := by exact_mod_cast hrho k
  have hpos' : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) ^ m := by positivity
  have hk' := key k hk
  have hk'' : |((∑ᶠ M ∈ B.Lin, f k M : ℚ) : ℝ)| ≤ (D : ℝ) * ((m * A ^ n * (k + 1) ^ (m - 1) * C : ℕ) : ℝ) := by
    have := (Rat.cast_le (K := ℝ)).2 hk'
    push_cast at this ⊢
    simpa [Rat.cast_abs] using this
  rw [Real.norm_eq_abs, abs_div, Nat.abs_cast]
  rw [div_le_iff₀ (lt_of_lt_of_le hpos' hr)]
  calc |((∑ᶠ M ∈ B.Lin, f k M : ℚ) : ℝ)|
      ≤ (D : ℝ) * ((m * A ^ n * (k + 1) ^ (m - 1) * C : ℕ) : ℝ) := hk''
    _ = c * (1 / ((k : ℝ) + 1)) * ((k + 1 : ℕ) : ℝ) ^ m := by
        have h := congrArg (fun x : ℕ => (x : ℝ)) (hm k)
        push_cast at h ⊢
        field_simp
        simp only [c]
        linear_combination (D : ℝ) * (A : ℝ) ^ n * (C : ℝ) * h
    _ ≤ c * (1 / ((k : ℝ) + 1)) * (B.rho (algebraMap K.O B.A a ^ k) : ℝ) := by
        refine mul_le_mul_of_nonneg_left hr ?_
        simp only [c]; positivity

end GlobalTheory.UnitLemma.Desc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryActLiftHermitianBlockMemIntegralUnitaryMuStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryAct_liftHermitianBlock_mem_integralUnitary_mul_embedding : ∀ {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] {r : ℕ} (X : Hn r F E) (ν : E) (l : F), ‖ν‖ = 1 → ∀ g : Matrix.unitaryGroup (Fin (r + 1)) E, unitU (r + 1) F E (actU g (GlobalTheory.JR.Step.liftH X ν l)) ≠ 0 → ∃ k ∈ uO (r + 1) E, ∃ s, g = k * GlobalTheory.JR.Step.uEmb r E s := by
  first | exact @GlobalTheory.JR.Step.actU_liftH_mem_uO_mul_uEmb | exact GlobalTheory.JR.Step.actU_liftH_mem_uO_mul_uEmb | (intros; apply GlobalTheory.JR.Step.actU_liftH_mem_uO_mul_uEmb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedQuadraticExistsIntegersUniformiserStatement
section
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedQuadratic_exists_integers_uniformiser : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), IsField A.K → IsField A.L → ∃ (ϖ : A.Kˣ) (O : Subring A.L), IsOpen (O : Set A.L) ∧ IsCompact (O : Set A.L) ∧ (∀ y ∈ O, star y ∈ O) ∧ (¬ ∃ y, A.NL y = (ϖ : A.K)) ∧ algebraMap A.K A.L (ϖ : A.K) ∈ O ∧ (¬ ∃ z ∈ O, algebraMap A.K A.L (ϖ : A.K) * z = 1) ∧ (∀ y ∈ O, (∃ z ∈ O, y = algebraMap A.K A.L (ϖ : A.K) * z) ∨ ∃ z ∈ O, y * z = 1) ∧ (∀ s : A.K, algebraMap A.K A.L s ∈ O → ∃ z ∈ O, Algebra.trace A.K A.L z = s) ∧ (∀ s : A.K, algebraMap A.K A.L s ∈ O → (∃ r ∈ O, algebraMap A.K A.L s * r = 1) → ∃ w ∈ O, A.NL w = s) ∧ (∀ U ∈ 𝓝 (0 : A.L), ∃ n : ℕ, ∀ z ∈ O, algebraMap A.K A.L ((ϖ : A.K) ^ n) * z ∈ U) ∧ ∀ y : A.L, ∃ n : ℕ, algebraMap A.K A.L ((ϖ : A.K) ^ n) * y ∈ O := by
  first | exact @GlobalTheory.JR.UnramInt.main | exact GlobalTheory.JR.UnramInt.main | (intros; apply GlobalTheory.JR.UnramInt.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusLaurentSeriesHasSumBoundFrobenius
section
noncomputable section

open Formalism.Per Filter Topology
open scoped Formalism.Per

namespace GlobalTheory.PSer.Laws

variable {l : ℕ} [Fact l.Prime]

theorem pw_zero (x : Fl l) : pw 0 x = x := by simp [pw]

theorem pw_succ (k : ℤ) (x : Fl l) : pw (k + 1) x = pw k x ^ l := by
  unfold pw
  rw [add_comm, zpow_add, zpow_one]
  rfl

theorem pw_add (a b : ℤ) (x : Fl l) : pw (a + b) x = pw a (pw b x) := by
  unfold pw
  rw [zpow_add]
  rfl

theorem pw_nat (n : ℕ) (x : Fl l) : pw (n : ℤ) x = x ^ l ^ n := by
  induction n with
  | zero => simp [pw_zero]
  | succ n ih => rw [Nat.cast_succ, pw_succ, ih, ← pow_mul, pow_succ]

theorem sh_pow (x : Fl l) (n : ℕ) : sh (x ^ n) = sh x ^ n := by
  unfold sh
  rw [map_pow]; push_cast; rfl

theorem l_pos : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
theorem two_le_l : (2 : ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).two_le

theorem norm_sh_pw (k : ℤ) (x : Fl l) : ‖sh (pw k x)‖ = ‖sh x‖ ^ ((l : ℝ) ^ k) := by
  have hl := l_pos (l := l)
  induction k using Int.induction_on with
  | zero => simp [pw_zero]
  | succ k ih =>
    rw [pw_succ, sh_pow, norm_pow, ih, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _),
      zpow_add_one₀ hl.ne']
  | pred k ih =>
    have h1 : pw (-(k : ℤ)) x = pw (-(k : ℤ) - 1) x ^ l := by
      rw [← pw_succ]; congr 1; ring
    rw [h1, sh_pow, norm_pow] at ih
    have h2 : (‖sh x‖ ^ ((l : ℝ) ^ (-(k : ℤ) - 1))) ^ l = ‖sh x‖ ^ ((l : ℝ) ^ (-(k : ℤ))) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), ← zpow_add_one₀ hl.ne']
      congr 2; ring
    rw [← h2] at ih
    exact (pow_left_inj₀ (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _)
      (Fact.out : l.Prime).ne_zero).1 ih

theorem norm_l : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
  rw [GlobalTheory.RingBasics.norm_eq_val, PadicComplex.valuation_p]; simp

def sz (l : ℕ) [Fact l.Prime] (h j : ℕ) (r : ℝ) (n : ℤ) : ℝ :=
  ‖(l : ℂ_[l])‖ ^ (-n) * r ^ ((l : ℝ) ^ (n * h + j : ℤ))

theorem norm_term (h j : ℕ) (x : Fl l) (n : ℤ) :
    ‖(l : ℂ_[l]) ^ (-n) * sh (pw (n * h + j) x)‖ = sz l h j ‖sh x‖ n := by
  rw [norm_mul, norm_zpow, norm_sh_pw]; rfl

theorem sz_nonneg (h j : ℕ) {r : ℝ} (hr : 0 ≤ r) (n : ℤ) : 0 ≤ sz l h j r n :=
  mul_nonneg (zpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg hr _)

theorem sz_mono (h j : ℕ) {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) (n : ℤ) :
    sz l h j r n ≤ sz l h j s n :=
  mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hr hrs (zpow_nonneg l_pos.le _))
    (zpow_nonneg (norm_nonneg _) _)

theorem tendsto_sz {h : ℕ} (hh : 1 ≤ h) (j : ℕ) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    Tendsto (sz l h j r) cofinite (𝓝 0) := by
  have hl := l_pos (l := l)
  have hl2 := two_le_l (l := l)
  rw [Int.cofinite_eq, tendsto_sup]
  constructor
  · have hb : Tendsto (fun n : ℤ => (l : ℝ) ^ n) atBot (𝓝 0) := by
      have := (tendsto_rpow_atBot_of_base_gt_one (l : ℝ) (by linarith)).comp
        ((tendsto_intCast_atBot_iff (R := ℝ)).2 (tendsto_id (α := ℤ) (x := atBot)))
      refine this.congr fun n => ?_
      simp
    refine squeeze_zero (sz_nonneg h j hr) (fun n => ?_) hb
    unfold sz
    rw [norm_l, inv_zpow', neg_neg]
    exact mul_le_of_le_one_right (zpow_nonneg hl.le _)
      (Real.rpow_le_one hr hr1.le (zpow_nonneg hl.le _))
  · rw [← Nat.map_cast_int_atTop, tendsto_map'_iff]
    have h1 : Tendsto (fun n : ℕ => l ^ n) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (Fact.out : l.Prime).one_lt
    have h2 := (tendsto_self_mul_const_pow_of_lt_one hr hr1).comp h1
    refine squeeze_zero (fun n => sz_nonneg h j hr _) (fun n => ?_) h2
    simp only [Function.comp, sz]
    rw [norm_l, inv_zpow', neg_neg, zpow_natCast, Nat.cast_pow]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hl.le _)
    have : ((n : ℤ) * h + j : ℤ) = ((n * h + j : ℕ) : ℤ) := by push_cast; ring
    rw [this, zpow_natCast, ← Nat.cast_pow, Real.rpow_natCast]
    refine pow_le_pow_of_le_one hr hr1.le (Nat.pow_le_pow_right (Fact.out : l.Prime).pos ?_)
    nlinarith

theorem summable_lam {h : ℕ} (hh : 1 ≤ h) (j : ℕ) {x : Fl l} (hx : ‖sh x‖ < 1) :
    Summable fun n : ℤ => (l : ℂ_[l]) ^ (-n) * sh (pw (n * h + j) x) := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [norm_term]
  exact tendsto_sz hh j (norm_nonneg _) hx

theorem bdd_sz {h : ℕ} (hh : 1 ≤ h) (j : ℕ) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    BddAbove (Set.range (sz l h j r)) :=
  (tendsto_sz hh j hr hr1).bddAbove_range_of_cofinite

theorem gam_nonneg (h j : ℕ) {r : ℝ} (hr : 0 ≤ r) : 0 ≤ gam l h j r :=
  Real.iSup_nonneg (sz_nonneg h j hr)

theorem norm_lam_le {h : ℕ} (hh : 1 ≤ h) (j : ℕ) {x : Fl l} {r : ℝ} (hx : ‖sh x‖ ≤ r) (hr : r < 1) :
    ‖lam h j x‖ ≤ gam l h j r := by
  have h0 : 0 ≤ r := (norm_nonneg _).trans hx
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (gam_nonneg h j h0) fun n => ?_
  rw [norm_term]
  exact (sz_mono h j (norm_nonneg _) hx n).trans (le_ciSup (bdd_sz hh j h0 hr) n)

theorem lam_shift (h j : ℕ) (x : Fl l) : lam h (j + h) x = l * lam h j x := by
  unfold lam
  rw [← tsum_mul_left, ← (Equiv.addRight (1 : ℤ)).tsum_eq
    (fun n : ℤ => (l : ℂ_[l]) * ((l : ℂ_[l]) ^ (-n) * sh (pw (n * h + j) x)))]
  refine tsum_congr fun n => ?_
  have h1 : (n * h + ((j + h : ℕ) : ℤ)) = (n + 1) * h + j := by push_cast; ring
  simp only [Equiv.coe_addRight]
  rw [h1, ← mul_assoc, ← zpow_one_add₀ GlobalTheory.RingBasics.p_ne_zero]
  congr 2; ring

theorem lam_pow (h j k : ℕ) (x : Fl l) : lam h j (x ^ l ^ k) = lam h (j + k) x := by
  unfold lam
  refine tsum_congr fun n => ?_
  rw [← pw_nat, ← pw_add]
  congr 3
  push_cast; ring

end GlobalTheory.PSer.Laws

namespace GlobalTheory.PSer

open Laws

theorem lam_hasSum_norm_le_frob : ∀ (l : ℕ) [Fact l.Prime] (h j : ℕ) (r : ℝ) (x : Fl l), 1 ≤ h → r < 1 →
    ‖sh x‖ ≤ r → HasSum (fun n : ℤ => (l : ℂ_[l]) ^ (-n) * sh (pw (n * h + j) x)) (lam h j x) ∧
      ‖lam h j x‖ ≤ gam l h j r ∧ lam h j (x ^ l ^ h) = (l : ℂ_[l]) * lam h j x ∧
      lam h j (x ^ l) = lam h (j + 1) x := by
  intro l _ h j r x hh hr hx
  refine ⟨(summable_lam hh j (hx.trans_lt hr)).hasSum, norm_lam_le hh j hx hr, ?_, ?_⟩
  · rw [lam_pow, lam_shift]
  · have := lam_pow (l := l) h j 1 x
    rwa [pow_one] at this

end GlobalTheory.PSer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VolumeScaledIntegersMulVolumeDualEqOneStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.volume_scaledIntegers_mul_volume_dual_eq_one : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), SelfDual μK (A.kerK ψ) → ∀ c : F, c ≠ 0 → MeasurableSet {y : A.K | ∀ x : A.K, c • x ∈ A.OK → A.psiK ψ (x * y) = 1} ∧ (((μK {z : A.K | c • z ∈ A.OK}).toReal : ℝ) : ℂ) * (((μK {y : A.K | ∀ x : A.K, c • x ∈ A.OK → A.psiK ψ (x * y) = 1}).toReal : ℝ) : ℂ) = 1 := by
  first | exact @GlobalTheory.LatVol.main | exact GlobalTheory.LatVol.main | (intros; apply GlobalTheory.LatVol.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneInductionPrincipleStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_deligne_induction_principle : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (S : WD h → Prop), (∀ x y, S x → S y → S (x.lpSum y)) → (∀ x y, (∀ σ, x.charPol σ = y.charPol σ) → S x → S y) → (∀ (n : ℕ) (a : WDRep h (Fin n → ℂ)) (μ : Weil h →* ℂˣ) (hμ : IsSmooth μ), (Set.range a.ρ).Finite → S (WD.mk (a.twist μ hμ))) → ∀ x, S x := by
  first | exact @GlobalTheory.WeilDeligne.WD.induction_lpSum_twist_finite | exact GlobalTheory.WeilDeligne.WD.induction_lpSum_twist_finite | (intros; apply GlobalTheory.WeilDeligne.WD.induction_lpSum_twist_finite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneOfFiniteImageStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_deligne_of_finite_image : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (G : Type) [Group G] [Finite G] (π : Weil h →* G), IsOpen {σ : Ine (F := E) A | π (ineIncl h σ) = 1} → ∀ (n : ℕ) (R : Representation ℂ G (Fin n → ℂ)) (μ : Weil h →* ℂˣ), IsSmooth μ → ∃ b : WDRep h (Fin n → ℂ), ∀ σ, b.ρ σ = (μ σ : ℂ) • R (π σ) := by
  first | exact @GlobalTheory.WeilDeligne.exists_wdRep_pull_finite_twist | exact GlobalTheory.WeilDeligne.exists_wdRep_pull_finite_twist | (intros; apply GlobalTheory.WeilDeligne.exists_wdRep_pull_finite_twist <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.XPowSmulMemPrimePowAddFiltrationPhiModule
section
noncomputable section

namespace GlobalTheory.BK

open PowerSeries

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e]

theorem EIn_pow_eq_factorial_mul_Ediv (i : ℕ) :
    EIn l e (S O K e) ^ i = (i.factorial : S O K e) * ⟨Ediv K l e i, Ediv_mem_S l e i⟩ := by
  apply Subtype.ext
  have hf : (i.factorial : K) ≠ 0 := natCast_ne_zero' l i.factorial_ne_zero
  have hc : ((i.factorial : S O K e) : K⟦X⟧) = C (i.factorial : K) := by
    rw [map_natCast]; rfl
  simp only [SubmonoidClass.coe_pow, coe_EIn, Subalgebra.coe_mul, Ediv, hc]
  rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hf, map_one, one_mul]

theorem exists_uIn_pow_eq (j : ℕ) (hj : j ≤ l) : ∃ σ : S O K e, ∃ φ ∈ Fil O K l e j,
    uIn (S O K e) ^ (e * l) = (l : S O K e) ^ (l - j) * σ + φ := by
  have hu : uIn (S O K e) ^ e = EIn l e (S O K e) + -(l : S O K e) := by
    apply Subtype.ext
    simp [E]
  refine ⟨∑ i ∈ Finset.range j, EIn l e (S O K e) ^ i * (-1) ^ (l - i) * (l : S O K e) ^ (j - i) *
      (l.choose i : S O K e),
    ∑ i ∈ Finset.Ico j (l + 1), EIn l e (S O K e) ^ i * (-(l : S O K e)) ^ (l - i) *
      (l.choose i : S O K e), ?_, ?_⟩
  · refine Ideal.sum_mem _ fun i hi => ?_
    have hi' : j ≤ i := (Finset.mem_Ico.1 hi).1
    rw [EIn_pow_eq_factorial_mul_Ediv]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ediv_mem_Fil l e hi')))
  · rw [pow_mul, hu, add_pow, ← Finset.sum_range_add_sum_Ico _ (by omega : j ≤ l + 1),
      Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i < j := Finset.mem_range.1 hi
    have h1 : l - i = (l - j) + (j - i) := by omega
    rw [neg_pow, h1, pow_add, pow_add]
    ring

theorem X_pow_smul_mem_l_pow_MM_add_FilMM (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime]
    [NormedAlgebra ℚ_[l] K] [NeZero e] (P : PhiMod O K l e a ι) (j : ℕ) (hj : j ≤ l)
    (w : Vec K a ι) (hw : w ∈ P.MM) : ∃ s ∈ P.MM, ∃ f ∈ P.FilMM j,
      (X : K⟦X⟧) ^ (e * l) • w = (l : K) ^ (l - j) • s + f := by
  obtain ⟨σ, φ, hφ, h⟩ := exists_uIn_pow_eq (O := O) (K := K) (l := l) (e := e) j hj
  refine ⟨σ • w, P.MM.smul_mem σ hw, φ • w, Submodule.smul_mem_smul hφ hw, ?_⟩
  have h2 : (X : K⟦X⟧) ^ (e * l) • w = (uIn (S O K e) ^ (e * l)) • w := by
    rw [Subalgebra.smul_def]
    simp
  have h3 : ((l : S O K e) ^ (l - j)) • (σ • w) = (l : K) ^ (l - j) • (σ • w) := by
    rw [← Nat.cast_pow, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  rw [h2, h, add_smul, mul_smul, h3]

end GlobalTheory.BK
end
end

