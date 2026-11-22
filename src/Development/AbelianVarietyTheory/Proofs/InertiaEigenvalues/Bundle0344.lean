import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0323
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0068
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0203
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0324
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
import Formalism.SharpRestriction.LevelLetterCocycles.SecondComparisonInCoordinates
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0292
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0325
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0197
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0188
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0069
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachInclusionInjectiveSaturatedInter
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerDistinguishedSpanIsPrimeAndNotMem
section
open scoped NNReal

namespace GlobalTheory

theorem wittVector_isUnit_of_isUnit_coeff_zero (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O]
    [CharP O l] [PerfectRing O l] (c : WittVector l O) (hc : IsUnit (c.coeff 0)) : IsUnit c := by
  obtain ⟨u, hu⟩ := hc
  set d := WittVector.teichmuller l (↑u⁻¹ : O) * c with hd
  have h0 : (d - 1).coeff 0 = 0 := by
    have : (d - 1) + 1 = d := sub_add_cancel d 1
    have h2 := congrArg (fun t => t.coeff 0) this
    simp only [WittVector.add_coeff_zero, WittVector.one_coeff_zero, hd,
      WittVector.mul_coeff_zero, WittVector.teichmuller_coeff_zero, ← hu, Units.inv_mul] at h2
    linear_combination h2
  rw [← WittVector.mem_span_p_iff_coeff_zero_eq_zero] at h0
  have hj := IsAdicComplete.le_jacobson_bot (Ideal.span {((l : ℕ) : WittVector l O)}) h0
  have hd1 : IsUnit d := by
    have := (Ideal.mem_jacobson_bot.mp hj) 1
    simpa using this
  exact isUnit_of_mul_isUnit_right hd1

theorem wittVector_natCast_mul_coeff_zero (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O]
    [CharP O l] [PerfectRing O l] (a : WittVector l O) :
    (((l : ℕ) : WittVector l O) * a).coeff 0 = 0 := by
  rw [← WittVector.mem_span_p_iff_coeff_zero_eq_zero]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

theorem wittVector_eq_teichmuller_add (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O]
    [CharP O l] [PerfectRing O l] (a : WittVector l O) :
    ∃ a₁ : WittVector l O, a = WittVector.teichmuller l (a.coeff 0) + ((l : ℕ) : WittVector l O) * a₁ := by
  have h0 : (a - WittVector.teichmuller l (a.coeff 0)).coeff 0 = 0 := by
    have : (a - WittVector.teichmuller l (a.coeff 0)) + WittVector.teichmuller l (a.coeff 0) = a :=
      sub_add_cancel _ _
    have h2 := congrArg (fun t => t.coeff 0) this
    simp only [WittVector.add_coeff_zero, WittVector.teichmuller_coeff_zero] at h2
    linear_combination h2
  rw [← WittVector.mem_span_p_iff_coeff_zero_eq_zero, Ideal.mem_span_singleton] at h0
  obtain ⟨a₁, ha₁⟩ := h0
  exact ⟨a₁, by rw [← ha₁]; ring⟩

section Distinguished

variable (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [CharP O l] [PerfectRing O l]
  (x : O) (e : ℕ) (w E' : WittVector l O)

theorem teichmuller_pow_not_mem_span (hx : x ≠ 0) (hxu : ¬ IsUnit x) (he : 0 < e) (hw : IsUnit w)
    (hE : E' = WittVector.teichmuller l x ^ e + ((l : ℕ) : WittVector l O) * w) (N : ℕ) :
    WittVector.teichmuller l x ^ N ∉ Ideal.span {E'} := by
  intro h
  rw [Ideal.mem_span_singleton] at h
  obtain ⟨c, hc⟩ := h
  have hT : WittVector.teichmuller l x ≠ 0 := by
    intro h0; apply hx; rw [← WittVector.teichmuller_coeff_zero l x, h0]; simp
  obtain ⟨d, rfl⟩ := (GlobalTheory.T.teichmuller_distinguished_regular_sequence l O x e w E' hx he hw hE N c).1 ⟨1, by rw [← hc]; ring⟩
  have h1 : E' * d = 1 := by
    apply mul_left_cancel₀ (pow_ne_zero N hT)
    linear_combination -hc
  have hu : IsUnit E' := IsUnit.of_mul_eq_one d h1
  have hc0 : IsUnit (E'.coeff 0) := by
    have := hu.map (WittVector.constantCoeff (p := l) (R := O))
    simpa [WittVector.constantCoeff] using this
  rw [hE, WittVector.add_coeff_zero, wittVector_natCast_mul_coeff_zero, add_zero, ← map_pow,
    WittVector.teichmuller_coeff_zero] at hc0
  exact hxu ((isUnit_pow_iff he.ne').mp hc0)

end Distinguished

section Distinguished2

variable (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l]
  [PerfectRing O l] (x : O) (e : ℕ) (w E' : WittVector l O)

theorem teichmuller_distinguished_normal_form_step (hw : IsUnit w)
    (hE : E' = WittVector.teichmuller l x ^ e + ((l : ℕ) : WittVector l O) * w) (a : WittVector l O) :
    (∃ a' : WittVector l O, a - WittVector.teichmuller l x ^ e * a' ∈ Ideal.span {E'}) ∨
    ∃ y : O, y ∣ x ^ e ∧ ∃ u : WittVector l O, IsUnit u ∧
      a - WittVector.teichmuller l y * u ∈ Ideal.span {E'} := by
  obtain ⟨v, hv⟩ := hw.exists_right_inv
  obtain ⟨a₁, ha⟩ := wittVector_eq_teichmuller_add l O a
  set a₀ := a.coeff 0
  have hL : ((l : ℕ) : WittVector l O) = E' * v - WittVector.teichmuller l x ^ e * v := by
    rw [hE]; linear_combination (-(((l : ℕ) : WittVector l O))) * hv
  have hmem : E' * (v * a₁) ∈ Ideal.span {E'} :=
    Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  obtain ⟨c, hc | hc⟩ := ValuationRing.cond a₀ (x ^ e)
  ·
    by_cases hcu : IsUnit c
    · left
      obtain ⟨c', hc'⟩ := hcu.exists_right_inv
      have ha₀ : a₀ = x ^ e * c' := by rw [← hc, mul_assoc, hc', mul_one]
      refine ⟨WittVector.teichmuller l c' - v * a₁, ?_⟩
      convert hmem using 1
      rw [ha, ha₀, map_mul, map_pow, hL]; ring
    · right
      refine ⟨a₀, ⟨c, hc.symm⟩, 1 - WittVector.teichmuller l c * (v * a₁), ?_, ?_⟩
      · apply wittVector_isUnit_of_isUnit_coeff_zero
        have h2 : (1 - WittVector.teichmuller l c * (v * a₁)).coeff 0 =
            1 - c * (v * a₁).coeff 0 := by
          have : (1 - WittVector.teichmuller l c * (v * a₁)) +
              WittVector.teichmuller l c * (v * a₁) = 1 := sub_add_cancel _ _
          have h3 := congrArg (fun t => t.coeff 0) this
          simp only [WittVector.add_coeff_zero, WittVector.one_coeff_zero, WittVector.mul_coeff_zero,
            WittVector.teichmuller_coeff_zero] at h3
          rw [WittVector.mul_coeff_zero]
          linear_combination h3
        rw [h2]
        rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (c * (v * a₁).coeff 0) with h | h
        · exact absurd (isUnit_of_mul_isUnit_left h) hcu
        · exact h
      · convert hmem using 1
        rw [ha, hL, ← map_pow, ← hc, map_mul]; ring
  ·
    left
    refine ⟨WittVector.teichmuller l c - v * a₁, ?_⟩
    convert hmem using 1
    rw [ha, ← hc, map_mul, map_pow, hL]; ring

theorem teichmuller_distinguished_normal_form_iter (hw : IsUnit w)
    (hE : E' = WittVector.teichmuller l x ^ e + ((l : ℕ) : WittVector l O) * w) (n : ℕ) :
    ∀ a : WittVector l O,
    (∃ a' : WittVector l O, a - WittVector.teichmuller l x ^ (e * n) * a' ∈ Ideal.span {E'}) ∨
    ∃ y : O, y ∣ x ^ (e * n) ∧ ∃ u : WittVector l O, IsUnit u ∧
      a - WittVector.teichmuller l y * u ∈ Ideal.span {E'} := by
  induction n with
  | zero => intro a; left; exact ⟨a, by simp⟩
  | succ n ih =>
    intro a
    rcases ih a with ⟨a', ha'⟩ | ⟨y, hy, u, hu, hya⟩
    · rcases teichmuller_distinguished_normal_form_step l O x e w E' hw hE a' with ⟨a'', ha''⟩ | ⟨y, hy, u, hu, hya⟩
      · left
        refine ⟨a'', ?_⟩
        have := Ideal.add_mem _ ha' (Ideal.mul_mem_left _ (WittVector.teichmuller l x ^ (e * n)) ha'')
        convert this using 1
        rw [Nat.mul_succ, pow_add]; ring
      · right
        refine ⟨x ^ (e * n) * y, ?_, u, hu, ?_⟩
        · rw [Nat.mul_succ, pow_add]; exact mul_dvd_mul_left _ hy
        · have := Ideal.add_mem _ ha' (Ideal.mul_mem_left _ (WittVector.teichmuller l x ^ (e * n)) hya)
          convert this using 1
          rw [map_mul, map_pow]; ring
    · right
      exact ⟨y, hy.trans (pow_dvd_pow _ (Nat.mul_le_mul_left e n.le_succ)), u, hu, hya⟩

end Distinguished2

section Distinguished3

variable (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [CharP O l]
  [PerfectRing O l] (x : O) (e : ℕ) (w E' : WittVector l O)

theorem mem_span_singleton_pow_smul_top_iff_dvd {R : Type} [CommRing R] (t a : R) (m : ℕ) :
    a ∈ (Ideal.span {t} ^ m • ⊤ : Submodule R R) ↔ t ^ m ∣ a := by
  rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

theorem teichmuller_distinguished_span_closed (hx : x ≠ 0) (he : 0 < e) (hw : IsUnit w)
    (hE : E' = WittVector.teichmuller l x ^ e + ((l : ℕ) : WittVector l O) * w)
    (hc : IsAdicComplete (Ideal.span {x}) O) (a : WittVector l O)
    (h : ∀ k : ℕ, ∃ c : WittVector l O, a - WittVector.teichmuller l x ^ k * c ∈ Ideal.span {E'}) :
    a ∈ Ideal.span {E'} := by
  set T := WittVector.teichmuller l x with hTdef
  have hcT := (GlobalTheory.T.wittVector_teichmuller_isAdicComplete_of_perfect l O x hx hc).1
  have hreg := GlobalTheory.T.teichmuller_distinguished_regular_sequence l O x e w E' hx he hw hE
  choose c hc' using h
  have hb : ∀ k, ∃ b : WittVector l O, a = E' * b + T ^ k * c k := by
    intro k
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp (hc' k)
    exact ⟨b, by rw [← hb]; ring⟩
  choose b hb using hb
  have hcauchy : ∀ {m n : ℕ}, m ≤ n → b m ≡ b n [SMOD (Ideal.span {T} ^ m • ⊤ : Submodule (WittVector l O) (WittVector l O))] := by
    intro m n hmn
    rw [SModEq.sub_mem, mem_span_singleton_pow_smul_top_iff_dvd]
    apply (hreg m _).1
    refine ⟨c n * T ^ (n - m) - c m, ?_⟩
    have h1 := (hb m).symm.trans (hb n)
    have h2 : T ^ n = T ^ m * T ^ (n - m) := by rw [← pow_add, Nat.add_sub_cancel' hmn]
    rw [h2] at h1
    linear_combination h1
  obtain ⟨L, hL⟩ := hcT.toIsPrecomplete.prec hcauchy
  have hzero : a - E' * L = 0 := by
    apply hcT.toIsHausdorff.haus
    intro n
    rw [SModEq.sub_mem, sub_zero, mem_span_singleton_pow_smul_top_iff_dvd]
    have hn := hL n
    rw [SModEq.sub_mem, mem_span_singleton_pow_smul_top_iff_dvd] at hn
    obtain ⟨d, hd⟩ := hn
    refine ⟨E' * d + c n, ?_⟩
    rw [hb n]
    linear_combination E' * hd
  rw [Ideal.mem_span_singleton]
  exact ⟨L, by linear_combination hzero⟩

end Distinguished3

theorem teichmuller_distinguished_span_isPrime : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l] (x : O), x ≠ 0 → ¬ IsUnit x → IsAdicComplete (Ideal.span {x}) O → ∀ (e : ℕ) (w E' : WittVector l O), 0 < e → IsUnit w → E' = WittVector.teichmuller l x ^ e + ((l : ℕ) : WittVector l O) * w → (Ideal.span {E'}).IsPrime ∧ ((l : ℕ) : WittVector l O) ∉ Ideal.span {E'} := by
  intro l _ O _ _ _ _ _ x hx hxu hc e w E' he hw hE
  have hnot := teichmuller_pow_not_mem_span l O x e w E' hx hxu he hw hE

  have hform : ∀ a : WittVector l O, a ∉ Ideal.span {E'} → ∃ (y : O) (N : ℕ), y ∣ x ^ N ∧
      ∃ u : WittVector l O, IsUnit u ∧ a - WittVector.teichmuller l y * u ∈ Ideal.span {E'} := by
    intro a ha
    have : ¬ ∀ k : ℕ, ∃ c : WittVector l O,
        a - WittVector.teichmuller l x ^ k * c ∈ Ideal.span {E'} :=
      fun h => ha (teichmuller_distinguished_span_closed l O x e w E' hx he hw hE hc a h)
    push_neg at this
    obtain ⟨k, hk⟩ := this
    rcases teichmuller_distinguished_normal_form_iter l O x e w E' hw hE k a with ⟨a', ha'⟩ | ⟨y, hy, u, hu, hya⟩
    · exfalso
      apply hk (WittVector.teichmuller l x ^ (e * k - k) * a')
      convert ha' using 2
      rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' (Nat.le_mul_of_pos_left k he)]
    · exact ⟨y, e * k, hy, u, hu, hya⟩
  have hI : Ideal.span {E'} ≠ ⊤ := by
    intro h
    exact hnot 0 (by rw [h]; exact Submodule.mem_top)
  refine ⟨(Ideal.isPrime_iff).mpr ⟨hI, ?_⟩, ?_⟩
  · intro a b hab
    by_contra hne
    push_neg at hne
    obtain ⟨y, N, hy, u, hu, hya⟩ := hform a hne.1
    obtain ⟨y', N', hy', u', hu', hyb⟩ := hform b hne.2
    obtain ⟨s, hs⟩ := mul_dvd_mul hy hy'
    have h1 : WittVector.teichmuller l (y * y') * (u * u') ∈ Ideal.span {E'} := by
      have := Ideal.sub_mem _ hab (Ideal.add_mem _ (Ideal.mul_mem_right b _ hya)
        (Ideal.mul_mem_left _ (WittVector.teichmuller l y * u) hyb))
      convert this using 1
      rw [map_mul]; ring
    obtain ⟨v, hv⟩ := (hu.mul hu').exists_right_inv
    have h2 : WittVector.teichmuller l (y * y') ∈ Ideal.span {E'} := by
      have := Ideal.mul_mem_right v _ h1
      rwa [mul_assoc, hv, mul_one] at this
    apply hnot (N + N')
    have := Ideal.mul_mem_right (WittVector.teichmuller l s) _ h2
    rw [← map_mul, ← hs, map_mul, map_pow, map_pow, ← pow_add] at this
    exact this
  · intro hl
    apply hnot e
    have : E' - ((l : ℕ) : WittVector l O) * w ∈ Ideal.span {E'} :=
      Ideal.sub_mem _ (Ideal.mem_span_singleton_self _) (Ideal.mul_mem_right _ _ hl)
    convert this using 1
    rw [hE]; ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltUntiltAddEstimateLe
section
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer

theorem tiltUntilt_add_estimate_of_norm_le (l : ℕ) [Fact l.Prime] (x y : Fl l) (hxy : ‖sh x‖ ≤ ‖sh y‖) :
    ‖sh (x + y) - sh x - sh y‖ ≤ ‖(l : ℂ_[l])‖ * ‖sh y‖ ∧ ‖sh (x + y)‖ ≤ ‖sh y‖ := by
  obtain ⟨h1, -, hmul, -, hle1, -, hadd, -⟩ := GlobalTheory.T.tiltUntiltToComplexPAdic_basic_laws l
  obtain ⟨u, rfl⟩ := (GlobalTheory.T.tilt_untilt_injective_and_dvd_of_norm_le l).2 x y hxy
  have hsum : y * u + y = y * (u + 1) := by ring
  rw [hsum, hmul, hmul]
  constructor
  · have key : sh y * sh (u + 1) - sh y * sh u - sh y
        = sh y * (sh (u + 1) - sh u - sh (1 : Fl l)) := by rw [h1]; ring
    rw [key, norm_mul, mul_comm ‖(l : ℂ_[l])‖]
    exact mul_le_mul_of_nonneg_left (hadd u 1) (norm_nonneg _)
  · rw [norm_mul]
    calc ‖sh y‖ * ‖sh (u + 1)‖ ≤ ‖sh y‖ * 1 :=
          mul_le_mul_of_nonneg_left (hle1 _) (norm_nonneg _)
      _ = ‖sh y‖ := mul_one _

theorem sh_add_le : ∀ (l : ℕ) [Fact l.Prime] (r : ℝ) (x y : Fl l), ‖sh x‖ ≤ r → ‖sh y‖ ≤ r →
    ‖sh (x + y) - sh x - sh y‖ ≤ ‖(l : ℂ_[l])‖ * r ∧ ‖sh (x + y)‖ ≤ r := by
  intro l _ r x y hx hy
  have hl : 0 ≤ ‖(l : ℂ_[l])‖ := norm_nonneg _
  rcases le_total ‖sh x‖ ‖sh y‖ with h | h
  · obtain ⟨h1, h2⟩ := tiltUntilt_add_estimate_of_norm_le l x y h
    exact ⟨h1.trans (mul_le_mul_of_nonneg_left hy hl), h2.trans hy⟩
  · obtain ⟨h1, h2⟩ := tiltUntilt_add_estimate_of_norm_le l y x h
    rw [add_comm x y]
    refine ⟨?_, h2.trans hx⟩
    have e : sh (y + x) - sh x - sh y = sh (y + x) - sh y - sh x := by ring
    rw [e]
    exact h1.trans (mul_le_mul_of_nonneg_left hx hl)

end GlobalTheory.PSer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToricLam0HasInfinityTypeConjRatio
section
noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie.InfType

theorem inf_eq_one {L : Type} [Field L] [NumberField L] [IsTotallyComplex L] {χ : Formalism.L2.Host.HChar L} {n : ℕ} (hn : 0 < n)
    (h : χ.OrderDvd n) (k : Lˣ) : χ.inf k = 1 := by
  have hx : ∀ x, (χ.1 x) ^ n = 1 := fun x => congrArg (fun ξ : Formalism.L2.Host.HChar L => ξ.1 x) h
  have hw : ∀ (w : InfinitePlace L) (y : (w.Completion)ˣ), χ.locInf w y = 1 := by
    intro w y
    let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (e (y : w.Completion)) hn
    have hz' : (e.symm z) ^ n = y := by rw [← map_pow, hz]; simp
    have hz0 : e.symm z ≠ 0 := by
      intro h0; rw [h0, zero_pow hn.ne'] at hz'; exact y.ne_zero hz'.symm
    have : y = (Units.mk0 _ hz0) ^ n := Units.ext (by simp [hz'])
    rw [this, map_pow]
    exact hx _
  show χ.1 (Formalism.L2.Host.infDiag k) = 1
  unfold Formalism.L2.Host.infDiag
  rw [MonoidHom.finset_prod_apply, map_prod]
  exact Finset.prod_eq_one fun w _ => hw w _

theorem conj_div_norm {z : ℂ} (hz : z ≠ 0) :
    starRingEnd ℂ z / ((‖starRingEnd ℂ z‖ : ℝ) : ℂ) = (z / ((‖z‖ : ℝ) : ℂ))⁻¹ := by
  have h1 : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hz
  rw [Complex.norm_conj, inv_div, div_eq_div_iff h1 hz, ← sq, ← Complex.mul_conj', mul_comm]

theorem delAt_inf {D : D7} (C : CharFrame D) (l : ℕ) (k : D.host.Eˣ) : (C.delAt l).inf k = 1 := by
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  unfold CharFrame.delAt
  split_ifs
  · obtain ⟨n, hn, h⟩ := C.isDel'.fin
    exact inf_eq_one hn h k
  · obtain ⟨n, hn, h⟩ := C.isDel.fin
    exact inf_eq_one hn h k

theorem toricLam0_hasInfinityType_conjRatio (D : D7) (Z : LamDat D) (hZ : Z.Ok) (l : ℕ) (j a : Fin D.R.m) (s : ℕ)
    (hs : (s : ℤ) ≤ (BlochKatoReduction.Gen.NFun D.R : ℤ) + 1) :
    (∀ g, 1 ≤ Z.kap j a s g) ∧
      GlobalTheory.CMVal.HasInf (Z.lam0 l j a) (phi D.host) (fun g => (Z.kap j a s g : ℤ) + s) := by
  have he : ∀ g, ∃ z : ℤ, eExp D j g = z := fun g => (D.hc _).e_int j
  choose e he using he
  have hpos : ∀ g, 1 ≤ e g + Z.c a g - s := fun g => by
    have h := hZ.big j a g
    rw [he] at h
    have h' : (BlochKatoReduction.Gen.NFun D.R : ℤ) + 1 < e g + Z.c a g := by exact_mod_cast h
    omega
  have hk : ∀ g, (Z.kap j a s g : ℤ) = e g + Z.c a g - s := fun g => by
    unfold LamDat.kap
    rw [he, Int.floor_intCast]
    exact Int.toNat_of_nonneg (by have := hpos g; omega)
  refine ⟨fun g => by have := hk g; have := hpos g; omega, fun k => ?_⟩
  obtain ⟨n, hn, h1⟩ := (Z.C.isMu0 j).inf
  obtain ⟨n', hn', h2⟩ := (hZ.aux a).inf
  unfold LamDat.lam0
  rw [HChar.inf_mul, HChar.inf_mul, HChar.inf_inv, delAt_inf, mul_one, Units.val_mul, Units.val_inv_eq_inv_val, h1 k, h2 k,
    ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun g _ => ?_
  have hz : embPsi D.host g (k : D.host.E) ≠ 0 := by simp
  have hu : embPsi D.host g (k : D.host.E) / ((‖embPsi D.host g (k : D.host.E)‖ : ℝ) : ℂ) ≠ 0 :=
    div_ne_zero hz (by exact_mod_cast norm_ne_zero_iff.2 hz)
  have e1 : n g = 2 * -(e g) := by
    have := hn g
    simp only [he] at this
    exact_mod_cast this
  have e2 : n' g = 2 * Z.c a g := by
    have := hn' g
    beta_reduce at this
    exact_mod_cast this
  have e3 : phi D.host g (k : D.host.E) = starRingEnd ℂ (embPsi D.host g (k : D.host.E)) := rfl
  rw [e3, conj_div_norm hz, inv_zpow', ← zpow_neg, ← zpow_add₀ hu, e1, e2]
  congr 1
  beta_reduce
  rw [hk]
  ring

end GlobalTheory.LamTie.InfType
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToricLam0UnitaryTrivOnMaxRealSubfield
section
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie

theorem delAt_unitary_triv {D : D7} (C : CharFrame D) (l : ℕ) : (C.delAt l).IsUnitary ∧ (C.delAt l).TrivOn D.host.F := by
  unfold CharFrame.delAt
  split_ifs
  · exact ⟨C.isDel'.unitary, C.isDel'.triv⟩
  · exact ⟨C.isDel.unitary, C.isDel.triv⟩

theorem toricLam0_unitary_trivOnMaxRealSubfield : ∀ (D : D7) (Z : LamDat D), Z.Ok → ∀ (l : ℕ) (j a : Fin D.R.m),
    (Z.lam0 l j a).IsUnitary ∧ TrivOnF (Z.lam0 l j a) := by
  intro D Z h l j a
  have hd := delAt_unitary_triv Z.C l
  exact ⟨((Z.C.isMu0 j).unitary.mul hd.1).mul (h.aux a).unitary.inv,
    ((Z.C.isMu0 j).triv.mul hd.2).mul (h.aux a).triv.inv⟩

end GlobalTheory.LamTie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitGenExists
section
noncomputable section

namespace GlobalTheory.WachUnit

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

theorem unitGen_exists : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), ∃ e, Formalism.MainNotions.WachCoordinates.Br.UnitGen ((HW l).W K s LL h) e := by
  intro D HW F l _ K s LL h
  obtain ⟨e, -, -, -, -, hN, -, hφ, hγ, hfree⟩ := GlobalTheory.WachUnit.unitVector D HW F l K s LL h
  exact ⟨e, hN, hφ, hγ, hfree⟩

end GlobalTheory.WachUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedOverFinExtOfFiniteInertiaImageStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_over_finExt_of_finite_inertia_image : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)), IsRat r ρ → (ρ '' (IK K : Set ↥(GK K))).Finite → ∃ (K' : FinExt l) (hK : K.1 ≤ K'.1), (∀ g ∈ IK K', ρ ⟨g, GK_le hK g.2⟩ = 1) ∧ ∀ (g : ↥(GK K')) i j, ‖(((ρ ⟨g, GK_le hK g.2⟩ : Matrix n n ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l) - (1 : Matrix n n (Om l)) i j‖ < 1 := by
  first | exact @GlobalTheory.PMon.unr_of_finite_inertia | exact GlobalTheory.PMon.unr_of_finite_inertia | (intros; apply GlobalTheory.PMon.unr_of_finite_inertia <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusDoubleSeriesHasSumAndNormBounds
section
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer

theorem Lam_main : ∀ (l : ℕ) [Fact l.Prime] (h j : ℕ) (r : ℝ) (y : ℕ → Fl l), 1 ≤ h → r < 1 → (∀ k, ‖sh (y k)‖ ≤ r) → HasSum (fun k : ℕ => (l : ℂ_[l]) ^ k * lam h j (y k)) (abelian₂ h j y) ∧ ‖abelian₂ h j y - lam h j (y 0)‖ ≤ ‖(l : ℂ_[l])‖ * gam l h j r ∧ ‖abelian₂ h j y‖ ≤ gam l h j r ∧ ∀ N : ℕ, abelian₂ h j (fun k => y k ^ l ^ (h * N)) = (l : ℂ_[l]) ^ N * abelian₂ h j y := by
  intro l _ h j r y hh hr hy
  have hl : ‖(l : ℂ_[l])‖ < 1 := GlobalTheory.RingBasics.norm_p_lt
  have hl0 : 0 ≤ ‖(l : ℂ_[l])‖ := norm_nonneg _
  have hlam : ∀ k, ‖lam h j (y k)‖ ≤ gam l h j r := fun k =>
    (GlobalTheory.T.untiltFrobeniusLaurentSeries_hasSum_bound_frobenius l h j r (y k) hh hr (hy k)).2.1
  have hterm : ∀ k : ℕ, ‖(l : ℂ_[l]) ^ k * lam h j (y k)‖ ≤ ‖(l : ℂ_[l])‖ ^ k * gam l h j r := by
    intro k
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left (hlam k) (pow_nonneg hl0 k)
  have hsum : Summable (fun k : ℕ => (l : ℂ_[l]) ^ k * lam h j (y k)) :=
    Summable.of_norm_bounded ((summable_geometric_of_lt_one hl0 hl).mul_right _) hterm
  have hHas : HasSum (fun k : ℕ => (l : ℂ_[l]) ^ k * lam h j (y k)) (abelian₂ h j y) := hsum.hasSum
  have hg0 : 0 ≤ gam l h j r := le_trans (norm_nonneg _) (hlam 0)
  refine ⟨hHas, ?_, ?_, ?_⟩
  · have := GlobalTheory.T.ultrametric_norm_hasSum_sub_finset_sum_le ℂ_[l] ℕ (fun k : ℕ => (l : ℂ_[l]) ^ k * lam h j (y k)) (abelian₂ h j y) {0}
      (‖(l : ℂ_[l])‖ * gam l h j r) (mul_nonneg hl0 hg0) hHas (by
        intro k hk
        have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (by simpa using hk)
        refine le_trans (hterm k) (mul_le_mul_of_nonneg_right ?_ hg0)
        simpa using pow_le_pow_of_le_one hl0 hl.le hk1)
    simpa using this
  · have := GlobalTheory.T.ultrametric_norm_hasSum_sub_finset_sum_le ℂ_[l] ℕ (fun k : ℕ => (l : ℂ_[l]) ^ k * lam h j (y k)) (abelian₂ h j y) ∅
      (gam l h j r) hg0 hHas (by
        intro k _
        refine le_trans (hterm k) ?_
        calc ‖(l : ℂ_[l])‖ ^ k * gam l h j r ≤ 1 * gam l h j r :=
              mul_le_mul_of_nonneg_right (pow_le_one₀ hl0 hl.le) hg0
          _ = gam l h j r := one_mul _)
    simpa using this
  · have hsh := GlobalTheory.T.tiltUntiltToComplexPAdic_basic_laws l

    have key : ∀ (N : ℕ) (x : Fl l), ‖sh x‖ ≤ r → lam h j (x ^ l ^ (h * N)) = (l : ℂ_[l]) ^ N * lam h j x := by
      intro N
      induction N with
      | zero => intro x _; simp
      | succ N ih =>
        intro x hx
        have hx' : ‖sh (x ^ l ^ (h * N))‖ ≤ r := by
          rw [hsh.2.2.2.1, norm_pow]
          have h1 : ‖sh x‖ ≤ 1 := hsh.2.2.2.2.1 x
          have hpos : 1 ≤ l ^ (h * N) := Nat.one_le_pow _ _ (Fact.out : l.Prime).pos
          exact le_trans (pow_le_of_le_one (norm_nonneg _) h1 (by omega)) hx
        have e : x ^ l ^ (h * (N + 1)) = (x ^ l ^ (h * N)) ^ l ^ h := by
          rw [← pow_mul, ← pow_add, Nat.mul_succ]
        rw [e, (GlobalTheory.T.untiltFrobeniusLaurentSeries_hasSum_bound_frobenius l h j r _ hh hr hx').2.2.1, ih x hx, pow_succ]
        ring
    intro N
    unfold abelian₂
    rw [← tsum_mul_left]
    congr 1
    funext k
    rw [key N (y k) (hy k)]
    ring

end GlobalTheory.PSer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachInclusionInjectiveSaturatedInterStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachInclusion_injective_saturated_inter : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I → Function.Injective I.ioE ∧ (∀ x : R.EE, IsUnit (I.ioE x) → IsUnit x) ∧ (∀ (x : R.EE) (y : RW LL), I.ioE x = ((l : ℕ) : RW LL) * y → ∃ x', x = ((l : ℕ) : R.EE) * x') ∧ ∀ x : R.EE, (∃ y, inclR LL y = I.ioE x) → ∃ a : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K)), algebraMap _ R.EE a = x := by
  first | exact @GlobalTheory.IoInj.ioE_injective_saturated_inter | exact GlobalTheory.IoInj.ioE_injective_saturated_inter | (intros; apply GlobalTheory.IoInj.ioE_injective_saturated_inter <;> assumption)
end

