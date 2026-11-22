import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0031
import Formalism.RealPlaceAnalysis.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0001
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0012
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0014
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0011

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliDetMulVectorTypeStatement
section
open Formalism.REAL Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capelliDet_mul_vectorType : ∀ (A : Type) [Ring A] [Algebra ℂ A] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → A) (x : Fin (m + 1) → A), GlRel E → (∀ a b j, E a b * x j = x j * E a b + if b = j then x a else 0) → ∀ (u : ℂ) (j : Fin (m + 1)), qdet E u * x j = x j * qdet E u + ∑ a : Fin (m + 1), ((-1 : ℂ) ^ ((a : ℕ) + (j : ℕ))) • (x a * qminor E (Fin.succAbove a) (Fin.succAbove j) (u - 1)) := by
  first | exact @GlobalTheory.qdet_mul_vector | exact GlobalTheory.qdet_mul_vector | (intros; apply GlobalTheory.qdet_mul_vector <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CompactCasimirBoundElementaryApply
section
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory.CasKAdjoint

def adMat {n : ℕ} (a b : Fin n) : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ := fun i j =>
  (if i.1 = a ∧ j = (b, i.2) then 1 else 0) - (if i.2 = b ∧ j = (i.1, a) then 1 else 0)

end GlobalTheory.CasKAdjoint
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CompactCasimirBoundEmbeddedComponent
section
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

theorem casKLe_io_component : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (N : Fin n → Type) [∀ s, NormedAddCommGroup (N s)] [∀ s, InnerProductSpace ℂ (N s)] (F : ∀ s, Fin n → Fin n → Module.End ℂ (N s)) (io : ∀ s, N s →ₗ[ℂ] (Fin n → M)) (pr : ∀ s, (Fin n → M) →ₗ[ℂ] N s) (c : ℝ) (s : Fin n) (y : N s), IsUnitary ε E → (∀ s, IsUnitary ε (F s)) → AlgTens ε E N F io pr → 0 ≤ c → CasKLe ε (F s) c y → ∀ d, CasKLe ε E (c + Real.sqrt n) (io s y d) := by
  intro M _ _ n ε E N _ _ F io pr c s y hE hF hT hc hy d
  have key := GlobalTheory.T.compactCasimirLe_tensorOperator_raise (N s) n ε (F s) M (Fin n) E
    (fun j => (LinearMap.proj j : (Fin n → M) →ₗ[ℂ] M) ∘ₗ io s)
    (fun a b => Matrix.single a b (1 : ℂ)) c (Real.sqrt n)
    (isUnitary_kUnit ε _ (hF s)) (isUnitary_kUnit ε _ hE) hc (Real.sqrt_nonneg _)
    (by
      intro a b _
      simp [Matrix.conjTranspose_single])
    (by
      intro x
      rw [Real.sq_sqrt (Nat.cast_nonneg n)]
      have h1 : ∀ a b : Fin n,
          ∑ i, ‖∑ j, (Matrix.single a b (1 : ℂ)) i j • x j‖ ^ 2 = ‖x b‖ ^ 2 := by
        intro a b
        rw [Finset.sum_eq_single a]
        · rw [Finset.sum_eq_single b]
          · simp
          · intro j _ hj
            simp [Matrix.single, hj.symm]
          · simp
        · intro i _ hi
          simp [Matrix.single, hi.symm]
        · simp
      calc _ ≤ ∑ _a : Fin n, ∑ b : Fin n, ‖x b‖ ^ 2 := by
            refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
            split_ifs
            · exact (h1 a b).le
            · positivity
        _ = _ := by simp)
    (by
      intro a b _ j w
      have h := congrFun (hT.io_comm s a b w) j
      simp only [dualTens] at h
      simp only [LinearMap.comp_apply, LinearMap.proj_apply]
      rw [h, Finset.sum_eq_single a]
      · by_cases hj : j = b
        · subst hj
          simp
        · simp [hj, Matrix.single, Ne.symm hj]
      · intro i _ hi
        simp [Matrix.single, hi.symm]
      · simp)
    y hy d
  exact key

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CompactCasimirBoundProjectionDualTensor
section
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

theorem kUnit_of_isUnitary_proj {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {n : ℕ} {ε : Fin n → Bool}
    {E : Fin n → Fin n → Module.End ℂ M} (h : IsUnitary ε E) : KUnit ε E := by
  intro a b hab u v
  have := h a b u v
  simpa [Formalism.REAL.sgn, hab] using this

theorem casKLe_proj_single : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (N : Fin n → Type) [∀ s, NormedAddCommGroup (N s)] [∀ s, InnerProductSpace ℂ (N s)] (F : ∀ s, Fin n → Fin n → Module.End ℂ (N s)) (io : ∀ s, N s →ₗ[ℂ] (Fin n → M)) (pr : ∀ s, (Fin n → M) →ₗ[ℂ] N s) (c : ℝ) (w : M), IsUnitary ε E → (∀ s, IsUnitary ε (F s)) → AlgTens ε E N F io pr → 0 ≤ c → CasKLe ε E c w → ∀ s d, CasKLe ε (F s) (c + Real.sqrt n) (pr s (Pi.single d w)) := by
  intro M _ _ n ε E N _ _ F io pr c w hE hF hT hc hw s d
  have key := GlobalTheory.T.compactCasimirLe_tensorOperator_raise M n ε E (N s) (Fin n) (F s)
    (fun j => (pr s) ∘ₗ (LinearMap.single ℂ (fun _ : Fin n => M) j))
    (fun a b => Matrix.of fun i j => if i = b ∧ j = a then (-1 : ℂ) else 0) c (Real.sqrt n)
    (kUnit_of_isUnitary_proj hE) (kUnit_of_isUnitary_proj (hF s)) hc (Real.sqrt_nonneg _) ?_ ?_ ?_ w hw d
  · simpa using key
  · intro a b _
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply]
    by_cases h : i = a ∧ j = b
    · simp [h.1, h.2]
    · have h' : ¬ (j = b ∧ i = a) := fun h2 => h ⟨h2.2, h2.1⟩
      simp [h, h']
  · intro x
    rw [Real.sq_sqrt (Nat.cast_nonneg n), Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    have h1 : ∀ b : Fin n, ∑ i, ‖∑ j, (Matrix.of fun i j => if i = b ∧ j = a then (-1 : ℂ) else 0) i j • x j‖ ^ 2
        = ‖x a‖ ^ 2 := by
      intro b
      rw [Finset.sum_eq_single b]
      · rw [Finset.sum_eq_single a]
        · simp
        · intro j _ hj; simp [hj]
        · simp
      · intro i _ hi; simp [hi]
      · simp
    calc _ ≤ ∑ _b : Fin n, ‖x a‖ ^ 2 := by
          refine Finset.sum_le_sum fun b _ => ?_
          split_ifs
          · exact (h1 b).le
          · positivity
      _ = _ := by simp
  · intro a b _ j v
    simp only [LinearMap.comp_apply, LinearMap.single_apply, Matrix.of_apply]
    rw [← hT.pr_comm]
    simp only [← map_smul, ← map_sum, ← map_add]
    congr 1
    funext i
    rw [Finset.sum_eq_single b]
    · simp only [dualTens, Pi.add_apply, Pi.smul_apply, Pi.single_apply]
      by_cases h1 : i = j <;> by_cases h2 : i = b <;> by_cases h3 : j = a <;>
        simp_all [sub_eq_add_neg, eq_comm]
    · intro k _ hk; simp [hk]
    · simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevSubspaceMono
section
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

theorem lev_subspace_mono :
    ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool)
      (E : Fin n → Fin n → Module.End ℂ M) (μ : Fin n → ℝ), GlRel E → IsUnitary ε E →
      (∀ j, Lev ε E μ j 0) ∧ (∀ j x y, Lev ε E μ j x → Lev ε E μ j y → Lev ε E μ j (x + y)) ∧
      (∀ j (a : ℂ) x, Lev ε E μ j x → Lev ε E μ j (a • x)) ∧
      ∀ j j' x, j ≤ j' → Lev ε E μ j x → Lev ε E μ j' x := by
  intro M _ _ n ε E μ _ hU
  obtain ⟨h0, hadd, hsmul, hmono⟩ := GlobalTheory.T.compactCasimirLe_subspace_monotone M n ε E (isUnitary_kUnit ε E hU)
  refine ⟨fun j => ⟨h0 _, Submodule.zero_mem _⟩,
    fun j x y hx hy => ⟨hadd _ _ _ hx.1 hy.1, Submodule.add_mem _ hx.2 hy.2⟩,
    fun j a x hx => ⟨hsmul _ _ _ hx.1, Submodule.smul_mem _ _ hx.2⟩, ?_⟩
  intro j j' x hj hx
  have hj' : (j : ℝ) ≤ (j' : ℝ) := by exact_mod_cast hj
  refine ⟨hmono _ _ _ (by positivity) ?_ hx.1, ?_⟩
  · gcongr
  · exact wtNear_le_of_add_dist_le M n ε E _ _ _ _ (by simpa using hj') hx.2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowerSeriesEvalTsumUnitDiscPropertiesAlt
section
open GlobalTheory.ConvSer

namespace GlobalTheory.ConvSer

theorem powerSeriesEvalTsum_unitDisc_properties : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (x : K), ‖x‖ < 1 → (∀ f : PowerSeries K, Bdd f → PowerSeriesHasSumAt f x (ev1 f x)) ∧ (∀ f g : PowerSeries K, Bdd f → Bdd g → ev1 (f + g) x = ev1 f x + ev1 g x ∧ ev1 (f - g) x = ev1 f x - ev1 g x ∧ ev1 (f * g) x = ev1 f x * ev1 g x) ∧ (∀ a : K, ev1 (PowerSeries.C a) x = a) ∧ ev1 PowerSeries.X x = x ∧ (∀ P : Polynomial K, Bdd (P : PowerSeries K) ∧ ev1 (P : PowerSeries K) x = P.eval x) ∧ (∀ (ι : Type) (t : Finset ι) (f : ι → PowerSeries K), (∀ i ∈ t, Bdd (f i)) → ev1 (∏ i ∈ t, f i) x = ∏ i ∈ t, ev1 (f i) x) ∧ (∀ f : PowerSeries K, Intg f → ‖ev1 f x‖ ≤ 1 ∧ ‖ev1 f x - PowerSeries.coeff 0 f‖ ≤ ‖x‖ ∧ ‖ev1 f x - PowerSeries.coeff 0 f - PowerSeries.coeff 1 f * x‖ ≤ ‖x‖ ^ 2) ∧ (∀ (f g : PowerSeries K), Intg g → PowerSeries.constantCoeff g = 0 → Bdd f → ev1 (f.subst g) x = ev1 f (ev1 g x)) ∧ (∀ (F : MvPowerSeries (Fin 2) K) (g h : PowerSeries K), Bdd F → Intg g → Intg h → PowerSeries.constantCoeff g = 0 → PowerSeries.constantCoeff h = 0 → ev1 (MvPowerSeries.subst (![g, h] : Fin 2 → MvPowerSeries Unit K) F) x = ev F ![ev1 g x, ev1 h x]) ∧ (∀ (F : MvPowerSeries (Fin 2) K) (y : K), ‖y‖ < 1 → Intg F → Intg (shift1 F y) ∧ ev1 (shift1 F y) x = ev F ![x, y]) ∧ (∀ f : PowerSeries K, ev1 f 0 = PowerSeries.coeff 0 f) := by
  intro K _ _ _ x hx
  have A := GlobalTheory.T.convergentSubst_oneVariable_and_formal_agreement K
  obtain ⟨B1, B2, B3, B4, B5, B6, B7, BetaSesquilinearity, B9, lowerOffDiagonalCoeff⟩ := GlobalTheory.T.mvPowerSeries_integral_bounded_closure K Unit
  obtain ⟨C1, C2, C3, C4, C5, C6, C7, C8⟩ := GlobalTheory.T.mvPowerSeriesEvalTsum_openPolydisc_properties K Unit (fun _ => x) (fun _ => hx)
  have hev : ∀ (f : PowerSeries K) (t : K), ev1 f t = ev f (fun _ : Unit => t) := A.2.1
  have P1 : ∀ f : PowerSeries K, Bdd f → PowerSeriesHasSumAt f x (ev1 f x) := by
    intro f hf
    rw [A.2.2.1, hev]
    exact C1 f hf
  have P2 : ∀ f g : PowerSeries K, Bdd f → Bdd g → ev1 (f + g) x = ev1 f x + ev1 g x ∧
      ev1 (f - g) x = ev1 f x - ev1 g x ∧ ev1 (f * g) x = ev1 f x * ev1 g x := by
    intro f g hf hg
    simp only [hev]
    exact C2 f g hf hg
  have P3 : ∀ a : K, ev1 (PowerSeries.C a) x = a := by
    intro a
    rw [hev]
    exact C3 a
  have P4 : ev1 PowerSeries.X x = x := by
    rw [hev]
    exact C4 ()
  have hBddX : Bdd (PowerSeries.X : PowerSeries K) := (B3 _ 0).2.2 (B5 ()).1
  have hBddP : ∀ P : Polynomial K, Bdd (P : PowerSeries K) := by
    intro P
    rw [(lowerOffDiagonalCoeff _).2]
    refine ⟨∑ i ∈ P.support, ‖P.coeff i‖, fun m => ?_⟩
    rw [Polynomial.coeff_coe]
    by_cases hm : m ∈ P.support
    · exact Finset.single_le_sum (f := fun i => ‖P.coeff i‖) (fun i _ => norm_nonneg _) hm
    · have h0 : P.coeff m = 0 := by simpa using hm
      rw [h0, norm_zero]
      exact Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have P5 : ∀ P : Polynomial K, Bdd (P : PowerSeries K) ∧ ev1 (P : PowerSeries K) x = P.eval x := by
    intro P
    refine ⟨hBddP P, ?_⟩
    refine Polynomial.induction_on P ?_ ?_ ?_
    · intro a
      rw [Polynomial.coe_C, P3, Polynomial.eval_C]
    · intro p q hp hq
      rw [Polynomial.coe_add, (P2 _ _ (hBddP p) (hBddP q)).1, hp, hq, Polynomial.eval_add]
    · intro m a ih
      have e : (Polynomial.C a * Polynomial.X ^ (m + 1) : Polynomial K) =
          (Polynomial.C a * Polynomial.X ^ m) * Polynomial.X := by ring
      rw [e, Polynomial.coe_mul, Polynomial.coe_X, (P2 _ _ (hBddP _) hBddX).2.2, ih, P4]
      simp
  have P6 : ∀ (ι : Type) (t : Finset ι) (f : ι → PowerSeries K), (∀ i ∈ t, Bdd (f i)) →
      ev1 (∏ i ∈ t, f i) x = ∏ i ∈ t, ev1 (f i) x := by
    intro ι t f hf
    classical
    induction t using Finset.induction_on with
    | empty =>
      have h1 : (1 : PowerSeries K) = PowerSeries.C 1 := by simp
      rw [Finset.prod_empty, Finset.prod_empty, h1, P3]
    | @insert j s hj ih =>
      have hs : ∀ i ∈ s, Bdd (f i) := fun i hi => hf i (Finset.mem_insert_of_mem hi)
      rw [Finset.prod_insert hj, Finset.prod_insert hj,
        (P2 _ _ (hf j (Finset.mem_insert_self j s)) ((B6 ι s f).2 hs).1).2.2, ih hs]
  have P7 : ∀ f : PowerSeries K, Intg f → ‖ev1 f x‖ ≤ 1 ∧
      ‖ev1 f x - PowerSeries.coeff 0 f‖ ≤ ‖x‖ ∧
      ‖ev1 f x - PowerSeries.coeff 0 f - PowerSeries.coeff 1 f * x‖ ≤ ‖x‖ ^ 2 := by
    have hI : ∀ f : PowerSeries K, Intg f → ‖ev1 f x‖ ≤ 1 := fun f hf => by
      rw [hev]
      exact (C5 f hf).1
    have hsh : ∀ f : PowerSeries K, Intg f →
        Intg (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) f) ∧
        ev1 f x = PowerSeries.coeff 0 f +
          x * ev1 (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) f) x := by
      intro f hf
      have hg : Intg (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) f) := by
        rw [(lowerOffDiagonalCoeff _).1]
        intro m
        rw [PowerSeries.coeff_mk]
        exact (lowerOffDiagonalCoeff f).1.mp hf (m + 1)
      refine ⟨hg, ?_⟩
      have hgb := (B3 _ 0).2.2 hg
      have e : ev1 f x = ev1 ((PowerSeries.X * PowerSeries.mk fun p => PowerSeries.coeff (p + 1) f) +
          PowerSeries.C (PowerSeries.constantCoeff f)) x :=
        congrArg (fun F => ev1 F x) (PowerSeries.eq_X_mul_shift_add_const f)
      rw [e, (P2 _ _ (B2 _ _ hBddX hgb).2.2
        (show Bdd (PowerSeries.C (PowerSeries.constantCoeff f)) from (B4 _).1)).1, (P2 _ _ hBddX hgb).2.2, P4, P3,
        PowerSeries.coeff_zero_eq_constantCoeff_apply]
      ring
    intro f hf
    obtain ⟨hg, e1⟩ := hsh f hf
    obtain ⟨hh, e2⟩ := hsh _ hg
    rw [PowerSeries.coeff_mk, zero_add] at e2
    refine ⟨hI f hf, ?_, ?_⟩
    · rw [e1, add_sub_cancel_left, norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (hI _ hg)
    · have key : ∀ a b d : K, a + x * (b + x * d) - a - b * x = x ^ 2 * d := by
        intro a b d
        ring
      rw [e1, e2, key, norm_mul, norm_pow]
      exact mul_le_of_le_one_right (by positivity) (hI _ hh)
  have P8 : ∀ (f g : PowerSeries K), Intg g → PowerSeries.constantCoeff g = 0 → Bdd f →
      ev1 (f.subst g) x = ev1 f (ev1 g x) := by
    intro f g hg h0 hf
    rw [hev (f.subst g), hev g]
    exact C8 g f hg h0 hf
  have P9 : ∀ (F : MvPowerSeries (Fin 2) K) (g h : PowerSeries K), Bdd F → Intg g → Intg h →
      PowerSeries.constantCoeff g = 0 → PowerSeries.constantCoeff h = 0 →
      ev1 (MvPowerSeries.subst (![g, h] : Fin 2 → MvPowerSeries Unit K) F) x =
        ev F ![ev1 g x, ev1 h x] := by
    intro F g h hF hg hh hg0 hh0
    rw [hev, C7 (Fin 2) ![g, h] F (fun j => by fin_cases j; exacts [hg, hh])
      (fun j => by fin_cases j; exacts [hg0, hh0]) hF]
    congr 1
    funext j
    fin_cases j <;> simp [hev]
  have product_first_zeroth_parts : ∀ (F : MvPowerSeries (Fin 2) K) (y : K), ‖y‖ < 1 → Intg F →
      Intg (shift1 F y) ∧ ev1 (shift1 F y) x = ev F ![x, y] := by
    intro F y hy hF
    have hs : ∀ i, Small ((![PowerSeries.X, PowerSeries.C y] : Fin 2 → MvPowerSeries Unit K) i) := by
      intro i
      fin_cases i
      · exact B5 ()
      · exact (B4 y).2.2 hy
    have hFb : Bdd F := ((GlobalTheory.T.mvPowerSeries_integral_bounded_closure K (Fin 2)).2.2.1 F 0).2.2 hF
    have D := GlobalTheory.T.mvPowerSeriesConvergentSubst_hasSum_and_bounds K (Fin 2) Unit _ F hs hFb
    rw [A.2.2.2.2.1 F y]
    refine ⟨D.2.2.1 hF, ?_⟩
    rw [hev, C6 (Fin 2) _ F hs hFb]
    congr 1
    funext j
    fin_cases j
    · exact C4 ()
    · exact C3 y
  have product_first_partition : ∀ f : PowerSeries K, ev1 f 0 = PowerSeries.coeff 0 f := by
    intro f
    unfold ev1
    rw [tsum_eq_single 0 (fun n hn => by simp [zero_pow hn])]
    simp
  exact ⟨P1, P2, P3, P4, P5, P6, P7, P8, P9, product_first_zeroth_parts, product_first_partition⟩

end GlobalTheory.ConvSer
end

