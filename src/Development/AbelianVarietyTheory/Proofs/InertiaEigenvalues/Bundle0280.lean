import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0264
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0261
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0059
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0060
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0068
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0078
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0069
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisIncl
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0243
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0129
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0263
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0230
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeOfSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0265

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCyclotomicFrobeniusTwistedValueEq
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

namespace GlobalTheory.ExpImage.Values

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K : FinExt l)

theorem zeta_pow (m i : ℕ) : P.ζQ (m + i) ^ (l ^ i) = P.ζQ m := by
  induction i with
  | zero => simp
  | succ k ih => rw [pow_succ', pow_mul, ← add_assoc, P.ζQ_succ, ih]

theorem cycVal_single {s e j : ℕ} (hj : 1 ≤ j) (hjs : j ≤ s) (μ : ℕ → ℤ) (V : Om l)
    (hμ : ∀ i, 1 ≤ i → i ≤ s →
      ∑ a ∈ primeTo l s, (μ a : Om l) * P.ζQ i ^ a = if i = j then V else 0)
    (x : ↥(K0 K)) :
    cycVal P K s e (fun a => (μ a : ↥(K0 K)) * x) 0 =
      (l : Om l) ^ (e * (s - j)) * (((frK P K ^ (s - j)) x : ↥(K0 K)) : Om l) * V := by
  have key : ∀ i ∈ Finset.range s,
      ∑ a ∈ primeTo l s, (((frK P K ^ i) ((μ a : ↥(K0 K)) * x) : ↥(K0 K)) : Om l) *
        P.ζQ s ^ (a * l ^ i) =
      (((frK P K ^ i) x : ↥(K0 K)) : Om l) * (if s - i = j then V else 0) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [← hμ (s - i) (by omega) (by omega), Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hz : P.ζQ s ^ (l ^ i) = P.ζQ (s - i) := by
      have := zeta_pow P (s - i) i
      rwa [Nat.sub_add_cancel hi'.le] at this
    rw [map_mul, map_intCast, mul_comm a, pow_mul, hz]
    push_cast
    ring
  unfold cycVal
  rw [Finset.sum_congr rfl fun i hi => by rw [key i hi], Finset.sum_eq_single (s - j)]
  · rw [if_pos (by omega)]
    simp [mul_assoc]
  · intro i hi hne
    have hi' := Finset.mem_range.mp hi
    rw [if_neg (by omega)]
    simp
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

theorem cycVal_add (s e : ℕ) (f g : ℕ → ↥(K0 K)) (d : ↥(K0 K)) :
    cycVal P K s e (fun a => f a + g a) d =
      cycVal P K s e f 0 + cycVal P K s e g 0 + (l : Om l) ^ (s * e) * (d : Om l) := by
  unfold cycVal
  simp only [map_add, IntermediateField.coe_add, add_mul, Finset.sum_add_distrib, mul_add,
    IntermediateField.coe_zero, mul_zero, add_zero]

theorem exists_pre (k : ℕ) (y : ↥(K0 K)) :
    ∃ x : ↥(K0 K), (frK P K ^ k) x = y ∧ ‖(x : Om l)‖ = ‖(y : Om l)‖ := by
  induction k generalizing y with
  | zero => exact ⟨y, rfl, rfl⟩
  | succ k ih =>
    obtain ⟨z, rfl⟩ := (P.PD K).σ_bij.2 y
    obtain ⟨x, hx, hn⟩ := ih z
    refine ⟨x, ?_, ?_⟩
    · rw [pow_succ', AlgHom.mul_apply, hx]
    · rw [hn]
      exact ((GlobalTheory.T.norm_frK_eq_and_exists_sub_pow_smul_frK_eq l P K).1 z).symm

theorem norm_int_mul {z : ℤ} {x : ↥(K0 K)} (hx : ‖(x : Om l)‖ ≤ 1) :
    ‖(((z : ↥(K0 K)) * x : ↥(K0 K)) : Om l)‖ ≤ 1 := by
  push_cast
  rw [norm_mul]
  exact mul_le_one₀ (IsUltrametricDist.norm_intCast_le_one _ z) (norm_nonneg _) hx

theorem norm_pow_mul (k : ℕ) {x : ↥(K0 K)} (hx : ‖(x : Om l)‖ ≤ 1) :
    ‖(((l : ↥(K0 K)) ^ k * x : ↥(K0 K)) : Om l)‖ ≤ 1 := by
  have := norm_int_mul K (z := (l : ℤ) ^ k) hx
  simpa using this

theorem sum_zeta : ∑ r ∈ Finset.Ico 1 l, P.ζQ 1 ^ r = -1 := by
  have h1 : P.ζQ 1 ^ l = 1 := (P.ζQ_succ 0).trans P.ζQ_zero
  have h2 := mul_geom_sum (P.ζQ 1) l
  rw [h1, sub_self, mul_eq_zero] at h2
  have h3 := h2.resolve_left (sub_ne_zero.mpr P.ζQ_one)
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Fact.out : l.Prime).pos] at h3
  simp only [pow_zero, zero_add] at h3
  linear_combination h3

theorem exists_minus_one {s : ℕ} (hs : 1 ≤ s) : ∃ ν : ℕ → ℤ,
    ∑ a ∈ primeTo l s, ν a = ((l : ℤ) - 1) * (l : ℤ) ^ (s - 1) ∧ ∀ i, 1 ≤ i → i ≤ s →
      ∑ a ∈ primeTo l s, (ν a : Om l) * P.ζQ i ^ a =
        if i = 1 then -(l : Om l) ^ (s - 1) else 0 := by
  have h : ∀ r : ℕ, ∃ μ : ℕ → ℤ, r ∈ Finset.Ico 1 l →
      (∑ a ∈ primeTo l s, μ a = (l : ℤ) ^ (s - 1) ∧ ∀ i, 1 ≤ i → i ≤ s →
      ∑ a ∈ primeTo l s, (μ a : Om l) * P.ζQ i ^ a =
        if i = 1 then (l : Om l) ^ (s - 1) * P.ζQ 1 ^ r else 0) := by
    intro r
    by_cases hr : r ∈ Finset.Ico 1 l
    · have hr' := Finset.mem_Ico.mp hr
      obtain ⟨μ, h1, h2⟩ := GlobalTheory.T.exists_int_weights_compatibleRootsOfUnity_levels l P.ζQ P.ζQ_zero P.ζQ_one P.ζQ_succ s 1 r le_rfl hs
        (Nat.not_dvd_of_pos_of_lt hr'.1 hr'.2)
      exact ⟨μ, fun _ => ⟨by simpa using h1, by simpa using h2⟩⟩
    · exact ⟨0, fun h => absurd h hr⟩
  choose μ hμ using h
  refine ⟨fun a => ∑ r ∈ Finset.Ico 1 l, μ r a, ?_, fun i hi his => ?_⟩
  · rw [Finset.sum_comm, Finset.sum_congr rfl fun r hr => (hμ r hr).1, Finset.sum_const,
      Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub (Fact.out : l.Prime).one_lt.le, Nat.cast_one]
  · push_cast
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm, Finset.sum_congr rfl fun r hr => (hμ r hr).2 i hi his]
    split_ifs
    · rw [← Finset.mul_sum, sum_zeta]
      ring
    · simp

theorem exists_cycVal_eq (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s e j n : ℕ)
    (hj : 1 ≤ j) (hjs : j ≤ s) (hn : ¬ l ∣ n) (c : Om l) (hc : c ∈ K0 K) (hc1 : ‖c‖ ≤ 1) :
    ∃ (lam : ℕ → ↥(K0 K)) (d : ↥(K0 K)), (∀ a, ‖(lam a : Om l)‖ ≤ 1) ∧ ‖(d : Om l)‖ ≤ 1 ∧
      d - (l : ↥(K0 K)) ^ e * frK P K d = (frK P K ^ s) (∑ a ∈ primeTo l s, lam a) ∧
      cycVal P K s e lam d = (l : Om l) ^ ((e + 1) * (s - 1)) * (c * P.ζQ j ^ n) := by
  obtain ⟨c, rfl⟩ : ∃ c' : ↥(K0 K), (c' : Om l) = c := ⟨⟨c, hc⟩, rfl⟩
  obtain ⟨μ, h1, h2⟩ := GlobalTheory.T.exists_int_weights_compatibleRootsOfUnity_levels l P.ζQ P.ζQ_zero P.ζQ_one P.ζQ_succ s j n hj hjs hn
  by_cases hj1 : j = 1
  · subst hj1
    simp only [if_true] at h1 h2
    obtain ⟨ν, g1, g2⟩ := exists_minus_one P hjs
    obtain ⟨d, hd, hdc⟩ := (GlobalTheory.T.norm_frK_eq_and_exists_sub_pow_smul_frK_eq l P K).2 (e + 1) (by omega) (frK P K c)
      (by rw [(GlobalTheory.T.norm_frK_eq_and_exists_sub_pow_smul_frK_eq l P K).1]; exact hc1)
    obtain ⟨x, hx, hxn⟩ := exists_pre P K (s - 1) c
    obtain ⟨y, hy, hyn⟩ := exists_pre P K (s - 1) ((l : ↥(K0 K)) ^ e * d)
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at *
    refine ⟨fun a => (μ a : ↥(K0 K)) * x + (ν a : ↥(K0 K)) * y, (l : ↥(K0 K)) ^ t * d,
      fun a => ?_, norm_pow_mul K t hd, ?_, ?_⟩
    · rw [IntermediateField.coe_add]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le
        (norm_int_mul K (hxn ▸ hc1)) (norm_int_mul K (hyn ▸ norm_pow_mul K e hd)))
    · rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, ← Int.cast_sum,
        ← Int.cast_sum, h1, g1, pow_succ' (frK P K), AlgHom.mul_apply, map_add, map_mul, map_mul,
        map_mul, map_intCast, map_intCast, hx, hy]
      simp only [map_add, map_mul, map_pow, map_natCast, map_intCast]
      push_cast
      linear_combination (l : ↥(K0 K)) ^ t * hdc
    · rw [cycVal_add, cycVal_single P K le_rfl hjs μ _ h2, cycVal_single P K le_rfl hjs ν _ g2]
      simp only [Nat.add_sub_cancel]
      rw [hx, hy]
      push_cast
      ring
  · simp only [if_neg hj1] at h1 h2
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
    obtain ⟨t, rfl⟩ : ∃ t, s = k + 2 + t := ⟨s - (k + 2), by omega⟩
    obtain ⟨x, hx, hxn⟩ := exists_pre P K t ((l : ↥(K0 K)) ^ ((e + 1) * k + e) * c)
    refine ⟨fun a => (μ a : ↥(K0 K)) * x, 0,
      fun a => norm_int_mul K (hxn ▸ norm_pow_mul K _ hc1), by simp, ?_, ?_⟩
    · rw [← Finset.sum_mul, ← Int.cast_sum, h1]
      simp
    · rw [cycVal_single P K hj hjs μ _ h2, Nat.add_sub_cancel_left, hx,
        show k + 2 + t - 1 = k + t + 1 by omega]
      push_cast
      ring

end GlobalTheory.ExpImage.Values
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinExt
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.FitsEx

theorem exists_lift {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (i : B →+* C)
    (hi : Function.Injective i) (f : A →+* C) (h : ∀ x, ∃ y, f x = i y) :
    ∃ g : A →+* B, ∀ x, i (g x) = f x := by
  choose g hg using h
  exact ⟨{ toFun := g
           map_one' := hi (by rw [← hg, map_one, map_one])
           map_mul' := fun x y => hi (by rw [map_mul, ← hg, ← hg, ← hg, map_mul])
           map_zero' := hi (by rw [← hg, map_zero, map_zero])
           map_add' := fun x y => hi (by rw [map_add, ← hg, ← hg, ← hg, map_add]) }, fun x => (hg x).symm⟩

variable {l : ℕ} [Fact l.Prime]

theorem eps_root {P : LocPrime l} (AI : LocAinf l P) (m : ℕ) :
    (rootT (l := l) AI.ε m : ℂ_[l]) = algebraMap (Om l) ℂ_[l] (P.ζQ m) := by
  have : rootT (l := l) AI.ε m = AI.ζ m := by
    refine Perfection.teichmuller_spec (I := Ideal.span {(l : Per.OC l)}) fun n => ?_
    refine ⟨AI.ζ (m + n), ?_, by rw [zeta_pow_iter AI.ζ_succ]⟩
    have := zeta_coeff_root_iterate (p := l) (O := Per.OC l) AI.ε m n
    rw [add_comm] at this
    exact (AI.ε_coeff (m + n)).symm.trans this.symm
  rw [this]
  exact AI.ζ_eq m

theorem isLog_unique {e : Per.Fl l} (he : e.untilt = 1) {y y' : Per.BdRp l}
    (h : Per.IsLog l e y) (h' : Per.IsLog l e y') :
    y = y' :=
  GlobalTheory.CrisIncl.log_unique l e he y y' h h'

theorem exists_finExt (x : Om l) : ∃ K : FinExt l, x ∈ K.1 :=
  ⟨⟨IntermediateField.adjoin ℚ_[l] {x},
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)⟩,
    IntermediateField.mem_adjoin_simple_self _ x⟩

theorem iota_alg (P : LocPrime l) (c : ↥(MaximalUnramifiedExtension l)) :
    P.ιB (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c) = algebraMap (Om l) P.R.BdR (c : Om l) := by
  obtain ⟨K, hK⟩ := exists_finExt (c : Om l)
  rw [← P.PD_ι K]
  exact (P.PD K).ι.commutes (⟨c, hK, c.2⟩ : ↥(K0 K))

theorem iota_inj (P : LocPrime l) : Function.Injective P.ιB := by
  obtain ⟨K, -⟩ := exists_finExt (0 : Om l)
  intro a b h
  exact (P.PD K).ι_inj (by rw [P.PD_ι, P.PD_ι, h])

theorem phi_alg {P : LocPrime l} (AI : LocAinf l P) (σ : ↥(MaximalUnramifiedExtension l) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l))
    (hσ : ∀ (c : ↥(MaximalUnramifiedExtension l)) (m : ℕ), 0 < m → ¬ l ∣ m → c ^ m = 1 → σ c = c ^ l) (c : ↥(MaximalUnramifiedExtension l)) :
    P.φB (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c) = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (σ c) := by
  have key : P.φB.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(MaximalUnramifiedExtension l) P.R.B) =
      (IsScalarTower.toAlgHom ℚ_[l] ↥(MaximalUnramifiedExtension l) P.R.B).comp σ := by
    refine IntermediateField.algHom_ext_of_eq_adjoin ℚ_[l] (S := MaximalUnramifiedExtension l) rfl fun x hx => ?_
    obtain ⟨m, hm, hlm, hxm⟩ := id hx
    obtain ⟨xb, hxb⟩ := exists_isTiltOf x m hm hlm hxm
    have hx' : x ∈ MaximalUnramifiedExtension l := IntermediateField.subset_adjoin _ _ hx
    have h1 := AI.ιA_teich ⟨x, hx'⟩ m hm hlm hxm xb hxb
    change P.φB (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B ⟨x, hx'⟩) = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (σ ⟨x, hx'⟩)
    rw [hσ ⟨x, hx'⟩ m hm hlm (Subtype.ext hxm), map_pow, ← h1, ← AI.ιA_φ, ← map_pow,
      WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]
  exact DFunLike.congr_fun key c

theorem sigma_eq {P : LocPrime l} (AI : LocAinf l P) (σ : ↥(MaximalUnramifiedExtension l) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l))
    (hσ : ∀ (c : ↥(MaximalUnramifiedExtension l)) (m : ℕ), 0 < m → ¬ l ∣ m → c ^ m = 1 → σ c = c ^ l)
    (K : FinExt l) (x : ↥(K0 K)) (c : ↥(MaximalUnramifiedExtension l)) (h : (c : Om l) = (x : Om l)) :
    (((P.PD K).σ x : ↥(K0 K)) : Om l) = ((σ c : ↥(MaximalUnramifiedExtension l)) : Om l) := by
  have : Nontrivial P.R.B := by
    refine ⟨⟨1, 0, fun h0 => one_ne_zero (AI.ιA_inj ?_)⟩⟩
    rw [map_one, map_zero, h0]
  have h1 := (P.PD K).φ_K₀ x
  rw [P.PD_φ] at h1
  have hc : c = ⟨x, x.2.2⟩ := Subtype.ext h
  have h2 := phi_alg AI σ hσ c
  rw [hc] at h2 ⊢
  have h3 : algebraMap ↥(MaximalUnramifiedExtension l) P.R.B ⟨((P.PD K).σ x : ↥(K0 K)), ((P.PD K).σ x).2.2⟩ = _ := h1.symm.trans h2
  exact congrArg Subtype.val ((algebraMap ↥(MaximalUnramifiedExtension l) P.R.B).injective h3)

theorem zeta_prim (P : LocPrime l) (m : ℕ) : IsPrimitiveRoot (P.ζQ (m + 1)) (l ^ (m + 1)) := by
  have h0 := zeta_pow_iter P.ζQ_succ 0 (m + 1)
  rw [zero_add, P.ζQ_zero] at h0
  have h1 := zeta_pow_iter P.ζQ_succ 1 m
  rw [add_comm] at h1
  have := orderOf_eq_prime_pow (x := P.ζQ (m + 1)) (p := l) (n := m) (by rw [h1]; exact P.ζQ_one) h0
  rw [← this]
  exact IsPrimitiveRoot.orderOf _

theorem chi_eq (P : LocPrime l) (χ : GQ l →* ℤ_[l]ˣ)
    (hχ : ∀ (g : GQ l) (m : ℕ) (x : Om l), x ^ (l ^ m) = 1 → g x = x ^ (PadicInt.toZModPow m (χ g : ℤ_[l])).val)
    (g : GQ l) : ((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) = (((χ g : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) := by
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have key : ∀ m : ℕ, ‖((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) - (((χ g : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l])‖ ≤
      (l : ℝ) ^ (-((m + 1 : ℕ) : ℤ)) := by
    intro m
    have hp := zeta_prim P m
    obtain ⟨a, ha, hg⟩ := P.χQ_cyc g (m + 1) _ hp.pow_eq_one
    rw [hχ g (m + 1) _ hp.pow_eq_one] at hg
    have hmod : (PadicInt.toZModPow (m + 1) (χ g : ℤ_[l])).val ≡ a [MOD l ^ (m + 1)] := by
      have hfin : IsOfFinOrder (P.ζQ (m + 1)) :=
        isOfFinOrder_iff_pow_eq_one.2 ⟨_, pow_pos (Fact.out : l.Prime).pos _, hp.pow_eq_one⟩
      have := hfin.pow_eq_pow_iff_modEq.1 hg
      rwa [← hp.eq_orderOf] at this
    have hk : ((a : ℤ_[l]) - (χ g : ℤ_[l])) ∈ Ideal.span {(l : ℤ_[l]) ^ (m + 1)} := by
      rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast,
        ← (ZMod.natCast_eq_natCast_iff _ _ _).2 hmod]
      have : NeZero (l ^ (m + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
      rw [ZMod.natCast_zmod_val, sub_self]
    have hn := (PadicInt.norm_le_pow_iff_mem_span_pow _ _).2 hk
    have hn' : ‖(a : ℚ_[l]) - (((χ g : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l])‖ ≤ (l : ℝ) ^ (-((m + 1 : ℕ) : ℤ)) := by
      simpa [PadicInt.norm_def] using hn
    rw [← sub_add_sub_cancel _ (a : ℚ_[l])]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hn')
  by_contra hne
  have hpos := norm_pos_iff.2 (sub_ne_zero.2 hne)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hpos (inv_lt_one_of_one_lt₀ hl)
  have h1 := key n
  rw [zpow_neg, zpow_natCast, ← inv_pow] at h1
  have h2 : (l : ℝ)⁻¹ ^ (n + 1) ≤ (l : ℝ)⁻¹ ^ n :=
    pow_le_pow_of_le_one (by positivity) (inv_lt_one_of_one_lt₀ hl).le (Nat.le_succ n)
  linarith

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem exists_fits : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI),
    ∃ C : Core l, Fits T C := by
  intro l _ P AI T
  have hinj := (BdRField.bdR_isField l).2.1
  obtain ⟨o, ho⟩ := exists_lift _ hinj (T.eD.toRingHom.comp (algebraMap (Om l) P.R.BdR))
    fun x => (T.om x).imp fun _ h => h.1
  have hosec : IsSec o := by
    refine ⟨fun x => ?_, fun z => hinj ?_⟩
    · obtain ⟨y, hy, hy'⟩ := T.om x
      rw [← hy', hinj ((ho x).trans hy)]
    · rw [ho]
      change T.eD (algebraMap (Om l) P.R.BdR _) = _
      rw [← IsScalarTower.algebraMap_apply, T.zD]
      exact GlobalTheory.RingIface.zD_eq_alg l z
  have hincl := T.incl
  set ι := (T.eD.toRingHom.comp (P.ιB : P.R.B →+* P.R.BdR)).comp T.eB.symm.toRingHom with hι
  have hιe : ∀ b : P.R.B, T.eD (P.ιB b) = ι (T.eB b) := fun b => by simp [hι]
  clear_value ι
  obtain ⟨j, hj', hj0, hjb⟩ := GlobalTheory.CrisIncl.exists_restrict l ι hincl
  have hj : ∀ x, algebraMap (Per.BdRp l) (Per.BdR l) (j x) =
      (ι.comp (algebraMap (Per.Acris l) (Per.Bcris l))) x := fun x => (hj' x).symm
  have hjc : IsCrisP j := ⟨hj0, hjb⟩
  have he : PreTilt.untilt (AI.ε : Per.Fl l) = 1 := Subtype.ext (by
    have := eps_root AI 0
    rw [P.ζQ_zero, map_one] at this
    exact this)
  obtain ⟨t, -, ht, -⟩ := exists_isLogA l AI.ε he
  obtain ⟨σ, hσ⟩ := exists_frobenius_Kur l
  obtain ⟨χ, hχ⟩ := exists_cyclotomicChar l
  refine ⟨{ ζ := P.ζQ, ζ_zero := P.ζQ_zero, ζ_succ := P.ζQ_succ, ζ_one := P.ζQ_one
            ε := AI.ε, ε_root := eps_root AI, o := o, o_sec := hosec, j := j, j_cris := hjc
            ι := ι, ι_j := fun x => (hj x).symm
            u := T.eB.toRingHom.comp (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B)
            ι_u := fun c => ?_
            t := t, t_log := ht, σ := σ, σ_root := hσ, χ := χ, χ_cyc := hχ },
    ⟨rfl, rfl, fun x => (ho x).symm, hιe, fun _ => rfl, ?_, chi_eq P χ hχ, sigma_eq AI σ hσ⟩⟩
  · rw [ho]
    exact (hιe _).symm.trans (congrArg T.eD (iota_alg P c))
  · obtain ⟨y, hy, hy'⟩ := T.t
    have h1 := isLog_unique he hy ((LogFun.log_fun l AI.ε t he ht).2.2.2 j hjc)
    have h2 : T.eD (P.ιB P.tB) = T.eD (P.ιB (T.eB.symm (algebraMap (Per.Acris l) (Per.Bcris l) t))) := by
      rw [hy', h1, hj, hιe, RingEquiv.apply_symm_apply]
      rfl
    rw [iota_inj P (T.eD.injective h2), RingEquiv.apply_symm_apply]
    rfl

end GlobalTheory.MemLoc.FitsEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntSubMem
section
open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.SplitFrobDense

theorem exists_conj_ne {R : Ranks} (H : Host R) :
    ∃ x y : 𝓞 H.E, (y : H.E) = H.conj (x : H.E) ∧ y - x ≠ 0 := by
  by_contra hc
  push Not at hc
  have h1 : ∀ x : 𝓞 H.E, H.conj (x : H.E) = x := fun x => by
    have := hc x ⟨H.conj x, (RingOfIntegers.isIntegral_coe x).map (H.conj.toAlgHom.restrictScalars ℤ)⟩ rfl
    exact congrArg (fun z : 𝓞 H.E => (z : H.E)) (sub_eq_zero.1 this)
  have h2 : ∀ z : H.E, H.conj z = z := fun z => by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 H.E) z
    rw [map_div₀]
    exact congrArg₂ (· / ·) (h1 a) (h1 b)
  have := H.isCMField_hostE
  refine IsTotallyComplex.complexEmbedding_not_isReal H.φ₀ (ComplexEmbedding.isReal_iff.2 ?_)
  ext z
  exact (H.conjE_apply H.φ₀ z).symm.trans (congrArg H.φ₀ (h2 z))

theorem exists_int_sub_mem {E : Type} [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E))
    (hv : v.asIdeal.inertiaDeg ℤ = 1) (x : 𝓞 E) : ∃ n : ℤ, x - n ∈ v.asIdeal := by
  have := v.isPrime
  have : NeZero v.asIdeal := ⟨v.ne_bot⟩
  have hp := Nat.absNorm_under_prime v.asIdeal
  have h := Ideal.absNorm_pow_inertiaDeg (v.asIdeal.under ℤ) v.asIdeal
  rw [hv, pow_one] at h
  rw [h] at hp
  have : Fact (Ideal.absNorm v.asIdeal).Prime := ⟨hp⟩
  have hc : Nat.card (𝓞 E ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := rfl
  have : Nontrivial (𝓞 E ⧸ v.asIdeal) := Ideal.Quotient.nontrivial_iff.2 v.isPrime.ne_top
  have hm := mem_zmultiples_of_prime_card hc (g := (1 : 𝓞 E ⧸ v.asIdeal)) (g' := Ideal.Quotient.mk _ x)
    one_ne_zero
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.1 hm
  refine ⟨n, Ideal.Quotient.eq.1 ?_⟩
  rw [← hn]
  simp

theorem frobDense : ∀ D : D7, GlobalTheory.TwSys.Cheb → FrobDense D := by
  classical
  intro D hC T hT
  rw [dense_iff_inter_open]
  rintro V hV ⟨g, hg⟩
  have : IsGalois D.host.E D.nd.Om := {}
  have hn : (fun u : G D.host.E D.nd.Om => u * g) ⁻¹' V ∈ nhds (1 : G D.host.E D.nd.Om) :=
    (hV.preimage (continuous_mul_const g)).mem_nhds (by simpa using hg)
  obtain ⟨L, hfd, hN, hL⟩ := (krullTopology_mem_nhds_one_iff_of_normal D.host.E D.nd.Om _).1 hn
  have hgal : IsGalois D.host.E L := {}
  obtain ⟨x, y, hxy, hne⟩ := exists_conj_ne D.host
  have f1 : {v : PlE D.host | v.asIdeal ∣ Ideal.span {y - x}}.Finite :=
    Ideal.finite_factors (by simpa using hne)
  obtain ⟨v, hv, hf, -, B, hB, -, σ, hσ, hU⟩ := hC D.host.E D.nd.Om L.fixingSubgroup L.fixingSubgroup_isOpen
    ((InfiniteGalois.normal_iff_isGalois L).2 hgal) g (f1.toFinset ∪ hT.toFinset)
  simp only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_span_singleton,
    not_or] at hv
  obtain ⟨h1, h2⟩ := hv
  obtain ⟨n, hx⟩ := exists_int_sub_mem v hf x
  have hsplit : IsSplitPl D.host v := by
    refine ⟨x - n, hx, fun z hz hzv => h1 ?_⟩
    have hz' : z = y - n := by
      apply RingOfIntegers.ext
      rw [hz]
      simp [hxy]
    have := v.asIdeal.sub_mem hzv hx
    rwa [hz', sub_sub_sub_cancel_right] at this
  have := hL hU
  simp only [Set.mem_preimage, inv_mul_cancel_right] at this
  exact ⟨σ, this, v, h2, hsplit, B, hB, hσ⟩

end GlobalTheory.SplitFrobDense
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMutuallyDualStableLattices
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.StableDual

theorem cyc_integral (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL]
    [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL]
    (hO : GoodO (Qp := ℚ_[l]) LL O) (g : ↥(GK K)) :
    ∃ a : O, ((cycLL (P.PD K) LL g : LLˣ) : LL) = algebraMap O LL a := by
  obtain ⟨_, _, hmod, _, hopen⟩ := hO
  have hn : ‖(P.χQ (g : GQ l) : ℚ_[l])‖ ≤ 1 := ((GlobalTheory.Cyc.cyc_basic l P.χQ P.χQ_cyc).1 _).le
  have hmem := GlobalTheory.GoodCoeff.padicInt_mem (algebraMap O LL).range
    (by rw [RingHom.coe_range]; exact hopen) (⟨_, hn⟩ : ℤ_[l])
  obtain ⟨a, ha⟩ := RingHom.mem_range.1 hmem
  refine ⟨a, ?_⟩
  rw [ha]
  simp [cycLL, LocPrime.PD_χ]

theorem stable_dual_lattices : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDual1 (P.PD K) A.ρ A'.ρ m → ∃ (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ), IsDualLat1 (P.PD K) LA LA' m ∧ IsDualLat1 (P.PD K) LA' LA m.flip := by
  intro l _ P K LL _ _ _ O _ _ hO A A' m hm
  haveI : FiniteDimensional ℚ_[l] K.1 := K.2
  haveI : CompactSpace ↥(GK K) :=
    isCompact_iff_compactSpace.1 (IntermediateField.fixingSubgroup_isClosed K.1).isCompact
  obtain ⟨LA⟩ := GlobalTheory.T.exists_stable_lattice_compact_group hO A
  obtain ⟨LA', h⟩ := GlobalTheory.T.dualLattice_stable_twisted_pairing l P K LL O hO A A' m LA hm (cyc_integral l P K LL O hO)
  exact ⟨LA, LA', h⟩

end GlobalTheory.StableDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTraceFormIntegralIffGoodCoeffStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_trace_form_integral_iff_goodCoeff : ∀ (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∃ lam : LL →ₗ[ℚ_[l]] ℚ_[l], ∀ a : LL, (∀ b : O, ∃ u : ℤ_[l], lam (a * algebraMap O LL b) = (u : ℚ_[l])) ↔ ∃ b : O, algebraMap O LL b = a := by
  first | exact @GlobalTheory.GoodCoeff.exists_trace_form_integral_iff | exact GlobalTheory.GoodCoeff.exists_trace_form_integral_iff | (intros; apply GlobalTheory.GoodCoeff.exists_trace_form_integral_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWachModuleGeneratorReductionStatement
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_wachModule_generator_reduction : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n) {k : Type} [Field k] [Algebra O k] (lam : O), Function.Surjective (algebraMap O k) → (∀ x, algebraMap O k x = 0 ↔ lam ∣ x) → ((PD.p : ℕ) : k) = 0 → ∃ p : ZMod n → (W.EE →+* k⸨X⸩), (∀ i (a : LetA O n), p i (algebraMap (LetA O n) W.EE a) = ((PowerSeries.map (algebraMap O k) (a i) : k⟦X⟧) : k⸨X⸩)) ∧ (∀ i, Function.Surjective (p i)) ∧ ∀ i e, p i e = 0 → ∃ e', algebraMap (LetA O n) W.EE (letE i) * e = algebraMap O W.EE lam * e' := by
  first | exact @GlobalTheory.RedFun.exists_letter_reduction | exact GlobalTheory.RedFun.exists_letter_reduction | (intros; apply GlobalTheory.RedFun.exists_letter_reduction <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankAndKernelOfLetterImageTensorStatement
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_and_kernel_of_letter_image_tensor : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n) {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA] [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA} (E : EtTie W RA RW inclR φR gR πA) {k : Type} [Field k] [Algebra O k] {Rk : Type} [CommRing Rk] [Algebra k Rk] [Algebra O Rk] [IsScalarTower O k Rk] (ρ : RW →ₐ[O] Rk) (lam : O) (κ : k⸨X⸩ →+* Rk), IsRed E ρ (k := k) lam κ → ∀ (T : LocLat G Qp LL O) (m : ℕ) (q : ↥T.L.T →ₗ[O] (Fin m → k)), Function.Surjective q → ∀ (T' : LocLat G Qp LL O) (f : LatHom T'.L T.L), (∀ x : ↥T.L.T, q x = 0 ↔ ∃ y ∈ T'.L.T, f.f y = x) → ∀ i, (∃ u : Fin m → W.DD T, ∀ x, ∃ c : Fin m → k⸨X⸩, eps E ρ i • J E ρ T q x = ∑ j, κ (c j) • eps E ρ i • J E ρ T q (u j)) ∧ ∀ h : LatHom T.L T'.L, (∀ x, f.f (h.f x) = algebraMap O LL lam • x) → ∀ x, eps E ρ i • J E ρ T q x = 0 → ∃ y, W.map f y = (letE i : LetA O n) • x := by
  first | exact @GlobalTheory.RedDim.dim_ker | exact GlobalTheory.RedDim.dim_ker | (intros; apply GlobalTheory.RedDim.dim_ker <;> assumption)
end

