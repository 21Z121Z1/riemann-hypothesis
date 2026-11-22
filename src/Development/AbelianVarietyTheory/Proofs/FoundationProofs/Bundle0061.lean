import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0032
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0045
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0056
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0020
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0055
import Formalism.GL3MeanSquares.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0046
import GroundTheory.PAdicHodge.AxLemma

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDerivationExtendPadicLaurentToClosure
section
open GlobalTheory.K5

noncomputable section

namespace GlobalTheory.K5.DerExt

theorem exists_extend_of_formallySmooth {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FormallySmooth R S] [Algebra ℤ R] (D : Derivation ℤ R R) :
    ∃ D' : Derivation ℤ S S, ∀ r, D' (algebraMap R S r) = algebraMap R S (D r) := by
  let g : R →+* TrivSqZeroExt S S :=
    { toFun := fun r ↦ TrivSqZeroExt.inl (algebraMap R S r) + TrivSqZeroExt.inr (algebraMap R S (D r))
      map_one' := by
        ext
        · simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, TrivSqZeroExt.fst_one,
            map_one, add_zero]
        · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.snd_one,
            Derivation.map_one_eq_zero, map_zero, zero_add]
      map_mul' := fun a b ↦ by
        ext
        · simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, TrivSqZeroExt.fst_mul,
            map_mul, add_zero]
        · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.snd_mul,
            TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, Derivation.leibniz,
            smul_eq_mul, map_add, map_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, zero_add, add_zero]
          ring
      map_zero' := by
        ext
        · simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, TrivSqZeroExt.fst_zero,
            map_zero, add_zero]
        · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.snd_zero,
            map_zero, zero_add]
      map_add' := fun a b ↦ by
        ext
        · simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, map_add, add_zero]
        · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, map_add, zero_add] }
  have hg : ∀ r, (g r).fst = algebraMap R S r ∧ (g r).snd = algebraMap R S (D r) := fun r ↦ by
    constructor
    · change (TrivSqZeroExt.inl (algebraMap R S r) + TrivSqZeroExt.inr (algebraMap R S (D r)) :
        TrivSqZeroExt S S).fst = _
      simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]
    · change (TrivSqZeroExt.inl (algebraMap R S r) + TrivSqZeroExt.inr (algebraMap R S (D r)) :
        TrivSqZeroExt S S).snd = _
      simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
  obtain ⟨l, h1, h2⟩ : ∃ l : S →+* TrivSqZeroExt S S, (∀ s, (l s).fst = s) ∧ ∀ r, l (algebraMap R S r) = g r := by
    letI : Algebra R (TrivSqZeroExt S S) := g.toAlgebra
    let π : TrivSqZeroExt S S →ₐ[R] S :=
      { (TrivSqZeroExt.fstHom S S S).toRingHom with commutes' := fun r ↦ (hg r).1 }
    have hs : Function.Surjective π := fun s ↦ ⟨TrivSqZeroExt.inl s, rfl⟩
    have hk : IsNilpotent (RingHom.ker (π : TrivSqZeroExt S S →+* S)) := by
      refine ⟨2, ?_⟩
      rw [pow_two, Submodule.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
      intro x hx y hy
      rw [RingHom.mem_ker] at hx hy
      change x.fst = 0 at hx
      change y.fst = 0 at hy
      rw [Ideal.mem_bot]
      ext
      · simp [hx]
      · simp [TrivSqZeroExt.snd_mul, hx, hy]
    let l := Algebra.FormallySmooth.liftOfSurjective (AlgHom.id R S) π hs hk
    exact ⟨l, fun s ↦ AlgHom.congr_fun (Algebra.FormallySmooth.comp_liftOfSurjective (AlgHom.id R S) π hs hk) s,
      fun r ↦ l.commutes r⟩
  refine ⟨Derivation.mk' (AddMonoidHom.toIntLinearMap
    { toFun := fun s ↦ (l s).snd, map_zero' := by simp, map_add' := fun x y ↦ by rw [map_add]; rfl }) fun a b ↦ ?_,
    fun r ↦ ?_⟩
  · change (l (a * b)).snd = a • (l b).snd + b • (l a).snd
    rw [map_mul, TrivSqZeroExt.snd_mul, h1, h1]
    simp [mul_comm]
  · change (l _).snd = _
    rw [h2, (hg r).2]

theorem derivation_extend : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ D : Derivation ℤ (O0 p) (O0 p),
    ∃ E : Derivation ℤ Ω Ω, ∀ x, E (algebraMap (O0 p) Ω x) = algebraMap (O0 p) Ω (D x) := by
  intro p _ Ω _ _ h D
  haveI : IsDomain (O0 p) := h.inj.isDomain _
  haveI : CharZero Ω := Basic.charZero_of_isClo h
  let K := FractionRing (O0 p)
  letI : Algebra K Ω := (IsFractionRing.lift h.inj).toAlgebra
  haveI : IsScalarTower (O0 p) K Ω := IsScalarTower.of_algebraMap_eq fun x ↦ by
    change _ = IsFractionRing.lift h.inj (algebraMap (O0 p) K x)
    rw [IsFractionRing.lift_algebraMap]
  haveI : Algebra.IsAlgebraic (O0 p) Ω := h.alg
  haveI : Algebra.IsAlgebraic K Ω := Algebra.IsAlgebraic.extendScalars (IsFractionRing.injective (O0 p) K)
  haveI : Algebra.IsSeparable K Ω := Algebra.IsSeparable.of_integral K Ω
  haveI : Algebra.FormallyEtale K Ω := Algebra.FormallyEtale.of_isSeparable K Ω
  haveI : Algebra.FormallySmooth (O0 p) K := Algebra.FormallySmooth.of_isLocalization (nonZeroDivisors (O0 p))
  haveI : Algebra.FormallySmooth (O0 p) Ω := Algebra.FormallySmooth.comp (O0 p) K Ω
  exact exists_extend_of_formallySmooth D

end GlobalTheory.K5.DerExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDerivationModIntegralExtensionPCubeStatement
section
open GlobalTheory.K5 GlobalTheory.KumDlog
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_derivationModIntegral_extension_p_cube : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], ∀ (B C : Subalgebra (O0 p) Ω) (ι : Type) [Fintype ι] (u v : ι → Ω) (tr : Ω → Ω), DualData B C u v tr →
  ∀ d : Ω → Ω, IsDer B d → ∃ D : Ω → Ω, IsDer C D ∧ ∀ b ∈ B, IsInt p (D b - (p : Ω) ^ 3 * d b) := by
  first | exact @GlobalTheory.DerExt.exists_ext | exact GlobalTheory.DerExt.exists_ext | (intros; apply GlobalTheory.DerExt.exists_ext <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDerivationOnExtensionCubeDefectStatement
section
open GlobalTheory.AlmostEt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_derivationOn_extension_cube_defect : ∀ (A S M : Type) [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M] [Module S M] (B C : Subalgebra A S) (tr : S → S) (n : ℕ) (a b : Fin n → S) (e : S), IsTrData B C tr a b e → ∀ D : S → M, IsDerOn B D → ∃ D' : S → M, IsDerOn C D' ∧ ∀ β ∈ B, D' β = (e ^ 3) • D β := by
  first | exact @GlobalTheory.AlmostEt.exists_derOn_ext | exact GlobalTheory.AlmostEt.exists_derOn_ext | (intros; apply GlobalTheory.AlmostEt.exists_derOn_ext <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDerivationOnISupOfCompatibleStatement
section
open GlobalTheory.AlmostEt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_derivationOn_iSup_of_compatible : ∀ (A S M : Type) [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M] [Module S M] (B : ℕ → Subalgebra A S), Monotone B → ∀ D : ℕ → S → M, (∀ m, IsDerOn (B m) (D m)) → (∀ m, ∀ x ∈ B m, D (m + 1) x = D m x) → ∃ D' : S → M, IsDerOn (⨆ m, B m) D' ∧ ∀ m, ∀ x ∈ B m, D' x = D m x := by
  first | exact @GlobalTheory.AlmostEt.isDerOn_iSup_glue | exact GlobalTheory.AlmostEt.isDerOn_iSup_glue | (intros; apply GlobalTheory.AlmostEt.isDerOn_iSup_glue <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDlogDerivationsGluedTowerLevelsStatement
section
open GlobalTheory.K5 GlobalTheory.KumDlog
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dlog_derivations_glued_tower_levels : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (B : Subalgebra (O0 p) Ω), (∀ x ∈ B, ∃ m : ℕ, x ∈ Lev T m) →
  (∀ m : ℕ, 1 ≤ m → ∃ dz dq : Ω → Ω, IsDer (Lev T m) dz ∧ IsDer (Lev T m) dq ∧ Vals T m dz dq) →
  ∃ dz dq : Ω → Ω, IsDer B dz ∧ IsDer B dq ∧ ∀ m : ℕ, 1 ≤ m → Vals T m dz dq := by
  first | exact @GlobalTheory.LevGlue.glue | exact GlobalTheory.LevGlue.glue | (intros; apply GlobalTheory.LevGlue.glue <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEqPrimePowMulNotDvdCompletedLaurent
section
open GlobalTheory.K5

namespace GlobalTheory.K5.Basic

theorem exists_not_prime_pow_dvd_completedLaurent (p : ℕ) [Fact p.Prime] (x : O0 p) (hx : x ≠ 0) :
    ∃ a : ℕ, ¬ (p : O0 p) ^ a ∣ x := by
  obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective (pI p) (Lau p) x
  obtain ⟨a, ha⟩ := exists_not_dvd p s hx
  refine ⟨a, ?_⟩
  rintro ⟨z, hz⟩
  apply ha a le_rfl
  have h1 := congrArg (AdicCompletion.evalₐ (pI p) a) hz
  rw [AdicCompletion.evalₐ_mk, map_mul, map_pow, map_natCast,
    ← map_natCast (Ideal.Quotient.mk (pI p ^ a)), ← map_pow] at h1
  have h2 : Ideal.Quotient.mk (pI p ^ a) ((p : Lau p) ^ a) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem, mem_pI_pow]
  rw [h2, zero_mul, Ideal.Quotient.eq_zero_iff_mem, mem_pI_pow] at h1
  exact h1

theorem exists_eq_prime_pow_mul_not_dvd_completedLaurent : ∀ (p : ℕ) [Fact p.Prime], ∀ x : O0 p, x ≠ 0 →
    ∃ (k : ℕ) (y : O0 p), x = (p : O0 p) ^ k * y ∧ ¬ (p : O0 p) ∣ y := by
  intro p _ x hx
  obtain ⟨a, ha⟩ := exists_not_prime_pow_dvd_completedLaurent p x hx
  have hfin : FiniteMultiplicity (p : O0 p) x :=
    ⟨a, fun h => ha ((pow_dvd_pow _ (Nat.le_succ a)).trans h)⟩
  obtain ⟨y, hy, hnd⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  exact ⟨_, y, hy, hnd⟩

end GlobalTheory.K5.Basic
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsImprovedApproxKummerGenerator
section
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

lemma nnreal_mul_max_le (a b c : ℝ≥0) (hc : c ≤ 1) : c * max a b ≤ max a (c * b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h]; exact le_max_right _ _
  · rw [max_eq_left h]; exact (mul_le_of_le_one_left (by positivity) hc).trans (le_max_left _ _)

theorem exists_approxRoot_step : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime →
    ∀ (F : Subfield L) (θ : ℝ≥0), θ ≤ 1 → v (p : L) ≤ 1 →
    (∀ u ∈ F, ∃ w ∈ F, v (u - w ^ p) ≤ θ * v u) → ∀ α y : L, α ^ p ∈ F → y ∈ F →
    v (α - y) ≤ v α → ∃ y' ∈ F, v (α - y') ^ p ≤
      max (v (p : L) * v (α - y) * v α ^ (p - 1)) (max θ (v (p : L)) * v (α - y) ^ p) := by
  intro L _ v p hp F θ hθ hvp hF α y hα hy hβα
  set β := α - y with hβ
  set A := v (p : L) * v β * v α ^ (p - 1) with hA
  have hyα : v y ≤ v α := by
    have : y = α - β := by rw [hβ]; ring
    rw [this]; exact (Valuation.map_sub v α β).trans (max_le le_rfl hβα)
  have hpp : p - 1 + 1 = p := Nat.sub_add_cancel hp.one_lt.le
  set u := α ^ p - y ^ p with hu
  have huF : u ∈ F := F.sub_mem hα (F.pow_mem hy p)
  have h1 : v (u - β ^ p) ≤ A := by
    have := GlobalTheory.T.valuation_add_pow_sub_pow_sub_pow_le L v p hp y β
    have e : y + β = α := by rw [hβ]; ring
    rw [e] at this
    refine this.trans ?_
    rw [hA]
    gcongr
    exact max_le hyα hβα
  set M := max A (v β ^ p) with hM
  have hvu : v u ≤ M := by
    have : u = (u - β ^ p) + β ^ p := by ring
    rw [this]; refine (Valuation.map_add v _ _).trans ?_
    rw [Valuation.map_pow]; exact max_le_max h1 le_rfl
  obtain ⟨w, hwF, hw⟩ := hF u huF
  have hw' : v (u - w ^ p) ≤ v u := hw.trans (mul_le_of_le_one_left (by positivity) hθ)
  have hwM : v w ^ p ≤ M := by
    have : w ^ p = u - (u - w ^ p) := by ring
    rw [← Valuation.map_pow, this]
    exact ((Valuation.map_sub v _ _).trans (max_le le_rfl hw')).trans hvu
  have h2 : v (β ^ p - w ^ p) ≤ max A (θ * v β ^ p) := by
    have : β ^ p - w ^ p = -(u - β ^ p) + (u - w ^ p) := by ring
    rw [this]; refine (Valuation.map_add v _ _).trans (max_le ?_ ?_)
    · rw [Valuation.map_neg]; exact h1.trans (le_max_left _ _)
    · exact (hw.trans (mul_le_mul_of_nonneg_left hvu (by positivity))).trans (nnreal_mul_max_le _ _ _ hθ)
  refine ⟨y + w, F.add_mem hy hwF, ?_⟩
  set γ := β - w with hγ
  have e2 : α - (y + w) = γ := by rw [hγ, hβ]; ring
  rw [e2]
  set m := max (v w) (v γ) with hm
  have hmβ : m ≤ max (v β) (v w) :=
    max_le (le_max_right _ _) ((Valuation.map_sub v β w))
  have hmM : m ^ p ≤ M := by
    refine (pow_le_pow_left₀ (by positivity) hmβ p).trans ?_
    rcases le_total (v β) (v w) with h | h
    · rw [max_eq_right h]; exact hwM
    · rw [max_eq_left h]; exact le_max_right _ _
  have h3 : v ((w + γ) ^ p - w ^ p - γ ^ p) ≤ max A (v (p : L) * v β ^ p) := by
    refine (GlobalTheory.T.valuation_add_pow_sub_pow_sub_pow_le L v p hp w γ).trans ?_
    have : v (p : L) * v γ * m ^ (p - 1) ≤ v (p : L) * m ^ p := by
      rw [mul_assoc, ← hpp, pow_succ, mul_comm (m ^ (p - 1)) m, hpp]
      gcongr
      exact le_max_right _ _
    refine this.trans ((mul_le_mul_of_nonneg_left hmM (by positivity)).trans (nnreal_mul_max_le _ _ _ hvp))
  have e3 : γ ^ p = (β ^ p - w ^ p) - ((w + γ) ^ p - w ^ p - γ ^ p) := by
    have : w + γ = β := by rw [hγ]; ring
    rw [this]; ring
  rw [← Valuation.map_pow, e3]
  refine (Valuation.map_sub v _ _).trans (max_le (h2.trans ?_) (h3.trans ?_))
  · exact max_le_max le_rfl (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · exact max_le_max le_rfl (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))

end GlobalTheory.AlmostEt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegerCosetRepresentativeTraceEqOfLtOne
section
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem exists_integer_coset_trace_eq (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G]
    [MulSemiringAction G L] (hv : ∀ (g : G) (x : L), v (g • x) = v x) (U : Subgroup G)
    [Fintype (G ⧸ U)] (hU : AlmostSep v U) (e : L) (he : ∀ g : G, g • e = e) (he1 : v e < 1) :
    ∃ y ∈ Fix L U, v y ≤ 1 ∧ cosetTrace U y = e := by
  obtain ⟨n, a, b, c, hs, hc⟩ := hU (v e) he1
  have hid := GlobalTheory.T.sum_mul_cosetRepresentativeTrace_eq L v G U n a b c hs 1 (one_mem _)
  simp only [mul_one] at hid

  obtain ⟨i, hi⟩ : ∃ i, v e < v (cosetTrace U (b i)) := by
    by_contra h
    push_neg at h
    have : v (∑ i, a i * cosetTrace U (b i)) ≤ v e := by
      apply v.map_sum_le
      intro i _
      rw [v.map_mul]
      calc v (a i) * v (cosetTrace U (b i)) ≤ 1 * v (cosetTrace U (b i)) :=
            mul_le_mul_of_nonneg_right (hs.a_le i) zero_le
        _ = v (cosetTrace U (b i)) := one_mul _
        _ ≤ v e := h i
    rw [hid] at this
    exact absurd hc (not_lt.mpr this)
  set t := cosetTrace U (b i) with ht
  have hfix := GlobalTheory.AlmostEt.cosetTrace_fixed_props L v G hv U (b i) (hs.b_mem i)
  have ht0 : t ≠ 0 := by
    intro h0; rw [h0, v.map_zero] at hi; exact absurd hi (not_lt.mpr zero_le)
  have hvt0 : v t ≠ 0 := by rwa [Ne, Valuation.zero_iff]
  have hq : ∀ g : G, g • (e / t) = e / t := by
    intro g
    rw [smul_div₀', he g, hfix.1 g]
  refine ⟨e / t * b i, ?_, ?_, ?_⟩
  · have hb := hs.b_mem i
    intro m
    rw [smul_mul', hb m]
    congr 1
    exact hq (m : G)
  · rw [v.map_mul, map_div₀]
    calc v e / v t * v (b i) ≤ 1 * 1 := by
          apply mul_le_mul' _ (hs.b_le i)
          rw [div_le_one₀ (pos_iff_ne_zero.mpr hvt0)]
          exact hi.le
      _ = 1 := one_mul 1
  · rw [hfix.2.2 (e / t) hq, div_mul_cancel₀ e ht0]

theorem exists_integer_coset_trace_eq' : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G] [MulSemiringAction G L], (∀ (g : G) (x : L), v (g • x) = v x) → ∀ (U : Subgroup G) [Fintype (G ⧸ U)], AlmostSep v U → ∀ e : L, (∀ g : G, g • e = e) → v e < 1 → ∃ y ∈ Fix L U, v y ≤ 1 ∧ cosetTrace U y = e :=
  fun L _ v G _ _ hv U _ hU e he he1 => exists_integer_coset_trace_eq L v G hv U hU e he he1

end GlobalTheory.AlmostEt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsJacobiSymEqNegOne
section
open Finset

namespace GlobalTheory.JacobiClassSum

theorem exists_jacobiSym_eq_neg_one {s : ℕ} (h1 : 1 < s) (hodd : Odd s) (hsq : Squarefree s) :
    ∃ c : ℕ, jacobiSym (c : ℤ) s = -1 := by
  obtain ⟨p, hp, t, rfl⟩ := Nat.exists_prime_and_dvd (ne_of_gt h1)
  have hcop : Nat.Coprime p t := Nat.coprime_of_squarefree_mul hsq
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_odd_iff_even.mpr (even_two_mul t)) hodd
  have ht : t ≠ 0 := by
    rintro rfl
    simp at h1
  haveI : NeZero t := ⟨ht⟩
  obtain ⟨n, hn⟩ := FiniteField.exists_nonsquare (F := ZMod p) (by rwa [ZMod.ringChar_zmod_n])
  obtain ⟨c, hc1, hc2⟩ := Nat.chineseRemainder hcop n.val 1
  refine ⟨c, ?_⟩
  have e1 : jacobiSym (c : ℤ) p = -1 := by
    rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_neg_one_iff]
    have : (((c : ℤ) : ZMod p)) = n := by
      rw [Int.cast_natCast, (ZMod.natCast_eq_natCast_iff _ _ _).mpr hc1, ZMod.natCast_zmod_val]
    rwa [this]
  have e2 : jacobiSym (c : ℤ) t = 1 := by
    rw [jacobiSym.mod_left' (a₂ := 1) (by exact_mod_cast (Int.natCast_modEq_iff.mpr hc2)),
      jacobiSym.one_left]
  rw [jacobiSym.mul_right, e1, e2]
  norm_num

theorem jacobiSym_val_natCast {s : ℕ} [NeZero s] (b : ℕ) :
    jacobiSym (((b : ZMod s).val : ℕ) : ℤ) s = jacobiSym (b : ℤ) s := by
  rw [ZMod.val_natCast, Int.natCast_mod, ← jacobiSym.mod_left]

theorem sum_zmod_eq_zero {s : ℕ} [NeZero s] (h1 : 1 < s) (hodd : Odd s) (hsq : Squarefree s) :
    ∑ x : ZMod s, jacobiSym ((x.val : ℕ) : ℤ) s = 0 := by
  obtain ⟨c, hc⟩ := exists_jacobiSym_eq_neg_one h1 hodd hsq
  have hcop : Nat.Coprime c s := by
    by_contra h
    have : jacobiSym (c : ℤ) s = 0 :=
      jacobiSym.eq_zero_iff_not_coprime.mpr (by simpa [Int.gcd_natCast_natCast] using h)
    rw [this] at hc
    norm_num at hc
  have key : ∀ x : ZMod s, jacobiSym ((((c : ZMod s) * x).val : ℕ) : ℤ) s
      = - jacobiSym ((x.val : ℕ) : ℤ) s := by
    intro x
    have : (c : ZMod s) * x = ((c * x.val : ℕ) : ZMod s) := by
      rw [Nat.cast_mul, ZMod.natCast_zmod_val]
    rw [this, jacobiSym_val_natCast, Nat.cast_mul, jacobiSym.mul_left, hc]
    ring
  have h := Equiv.sum_comp (Units.mulLeft (ZMod.unitOfCoprime c hcop))
    (fun x : ZMod s => jacobiSym ((x.val : ℕ) : ℤ) s)
  simp only [Units.mulLeft_apply, ZMod.coe_unitOfCoprime, key, Finset.sum_neg_distrib] at h
  linarith

theorem lamSumZero : Formalism.HermitianLattices.GL2a2.LamSumZero := by
  intro m₀ s a₀ hm h1 hodd hsq hcop
  haveI : NeZero s := ⟨by omega⟩
  rw [← sum_zmod_eq_zero h1 hodd hsq]
  refine Finset.sum_bij (fun b _ => (b : ZMod s)) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro b hb b' hb' h
    simp only [Finset.mem_filter, Finset.mem_range] at hb hb'
    have h2 : b ≡ b' [MOD s] := (ZMod.natCast_eq_natCast_iff _ _ _).mp h
    have h3 : b ≡ b' [MOD m₀] := hb.2.trans hb'.2.symm
    have h4 : b ≡ b' [MOD m₀ * s] :=
      (Nat.modEq_and_modEq_iff_modEq_mul hcop.symm).mp ⟨h3, h2⟩
    exact Nat.ModEq.eq_of_lt_of_lt h4 hb.1 hb'.1
  · intro x _
    have hlt := Nat.chineseRemainder_lt_mul hcop.symm a₀ x.val hm.ne' (NeZero.ne s)
    have hpr := (Nat.chineseRemainder hcop.symm a₀ x.val).2
    refine ⟨(Nat.chineseRemainder hcop.symm a₀ x.val : ℕ), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨hlt, hpr.1⟩
    · show ((Nat.chineseRemainder hcop.symm a₀ x.val : ℕ) : ZMod s) = x
      rw [(ZMod.natCast_eq_natCast_iff _ _ _).mpr hpr.2, ZMod.natCast_zmod_val]
  · intro b _
    exact (jacobiSym_val_natCast b).symm

end GlobalTheory.JacobiClassSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLagrangeResolventOfPGroupFaithful
section
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem exists_lagrange_resolvent : ∀ (L : Type) [Field L] (p : ℕ), p.Prime → ∀ (G : Type) [Group G]
    [MulSemiringAction G L] [Finite G] [Nontrivial G] [FaithfulSMul G L], IsPGroup p G →
    ∀ ζ : L, IsPrimitiveRoot ζ p → (∀ g : G, g • ζ = ζ) →
    ∃ (σ : G) (α : L), α ≠ 0 ∧ σ • α = ζ * α ∧ ∀ g : G, g • α ^ p = α ^ p := by
  intro L _ p hp G _ _ _ _ _ hG ζ hζ hfix
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (1 < p) := ⟨hp.one_lt⟩
  classical
  letI : Fintype G := Fintype.ofFinite G
  obtain ⟨χ, hχ⟩ := GlobalTheory.T.exists_surjective_hom_zmod_of_isPGroup p G hG
  set ψ : G → L := fun g => ζ ^ (Multiplicative.toAdd (χ g)).val with hψdef
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  have hmod : ∀ n : ℕ, ζ ^ n = ζ ^ (n % p) := fun n => by
    conv_lhs => rw [← Nat.div_add_mod n p, pow_add, pow_mul, hζp, one_pow, one_mul]
  have hψmul : ∀ a b, ψ (a * b) = ψ a * ψ b := by
    intro a b
    simp only [hψdef, map_mul, toAdd_mul, ZMod.val_add, ← pow_add]
    exact (hmod _).symm
  have hψp : ∀ g, ψ g ^ p = 1 := by
    intro g; simp only [hψdef]; rw [← pow_mul, mul_comm, pow_mul, hζp, one_pow]
  have hψne : ∀ g, ψ g ≠ 0 := fun g h => by
    have := hψp g; rw [h, zero_pow hp.ne_zero] at this; exact zero_ne_one this
  have hψfix : ∀ g h : G, g • ψ h = ψ h := fun g h => by simp only [hψdef, smul_pow', hfix]
  let f : G → (L →* L) := fun g => (MulSemiringAction.toRingHom G L g : L →* L)
  have hf : Function.Injective f := by
    intro g h hgh
    apply FaithfulSMul.eq_of_smul_eq_smul (α := L)
    intro x
    exact DFunLike.congr_fun hgh x
  have hli : LinearIndependent L (fun g : G => ((f g : L →* L) : L → L)) :=
    (linearIndependent_monoidHom L L).comp f hf
  have hex : ∃ x : L, ∑ g : G, ψ g⁻¹ * (g • x) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have h0 : ∑ g : G, ψ g⁻¹ • ((f g : L →* L) : L → L) = 0 := by
      funext x
      simpa [f, Finset.sum_apply] using hcon x
    exact hψne _ ((Fintype.linearIndependent_iff.mp hli) (fun g => ψ g⁻¹) h0 1)
  obtain ⟨x, hx⟩ := hex
  set α := ∑ g : G, ψ g⁻¹ * (g • x) with hα
  have hact : ∀ h : G, h • α = ψ h * α := by
    intro h
    rw [hα, Finset.smul_sum, Finset.mul_sum]
    simp only [smul_mul', hψfix, smul_smul]
    refine Fintype.sum_equiv (Equiv.mulLeft h) _ _ (fun g => ?_)
    simp only [Equiv.coe_mulLeft]
    have e : ψ h * ψ h⁻¹ = 1 := by
      rw [← hψmul, mul_inv_cancel]; simp [hψdef]
    rw [mul_inv_rev, hψmul g⁻¹ h⁻¹]
    linear_combination (-(ψ g⁻¹ * ((h * g) • x))) * e
  obtain ⟨σ, hσ⟩ := hχ (Multiplicative.ofAdd 1)
  refine ⟨σ, α, hx, ?_, ?_⟩
  · rw [hact σ]
    congr 1
    simp [hψdef, hσ, ZMod.val_one]
  · intro g
    rw [smul_pow', hact g, mul_pow, hψp, one_mul]

end GlobalTheory.AlmostEt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLinearLimitOfCompatibleFamilyStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linearMap_limit_of_compatible_approximations : ∀ (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module ℤ_[l] M] (B : Submodule ℤ_[l] M) (R : ℕ → M → PadicAlgCl l → Prop) (C : ℝ),
  (∀ n, ∀ b ∈ B, ∃ x, R n b x) →
  (∀ n, ∀ b ∈ B, ∀ x y, R (n + 1) b x → R n b y → ‖x - y‖ ≤ C * ‖((l : ℕ) : PadicAlgCl l) ^ n‖) →
  (∀ n, ∀ b ∈ B, ∀ b' ∈ B, ∀ (a a' : ℤ_[l]) (x x' : PadicAlgCl l), R n b x → R n b' x' →
    R n (a • b + a' • b') (((a.appr n : ℕ) : PadicAlgCl l) * x + ((a'.appr n : ℕ) : PadicAlgCl l) * x')) →
  ∃ L : TensorProduct ℤ_[l] (PadicAlgCl l) M →ₗ[PadicAlgCl l] ℂ_[l], ∀ n, ∀ b ∈ B, ∀ x, R n b x →
    ‖(x : ℂ_[l]) - L (1 ⊗ₜ[ℤ_[l]] b)‖ ≤ C * ‖((l : ℕ) : PadicAlgCl l) ^ n‖ := by
  first | exact @GlobalTheory.exists_linear_limit_of_compatible_family | exact GlobalTheory.exists_linear_limit_of_compatible_family | (intros; apply GlobalTheory.exists_linear_limit_of_compatible_family <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSquarefreePolyDistinctZerosOnCurveStatement
section
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_squarefree_poly_distinct_zeros_on_curve : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CharZero k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra k[X] A] [IsScalarTower k k[X] A] [Module.Finite k[X] A] [Module.Free k[X] A] (g : A) (s : ℕ), g ≠ 0 → ∃ (q : k[X]) (r : ℕ) (Q : Fin r → Ideal A), q.Monic ∧ q.natDegree = s ∧ (∀ i, (Q i).IsMaximal) ∧ Function.Injective Q ∧ (∀ i, g ∉ Q i) ∧ Ideal.span {algebraMap k[X] A q} = ∏ i, Q i := by
  first | exact @GlobalTheory.SquarefreeFibre.main | exact GlobalTheory.SquarefreeFibre.main | (intros; apply GlobalTheory.SquarefreeFibre.main <;> assumption)
end

