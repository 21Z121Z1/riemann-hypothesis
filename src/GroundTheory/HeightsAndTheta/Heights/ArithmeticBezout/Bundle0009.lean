import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0002

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PQuasiFiniteSheets
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

namespace QuasiFiniteSheets

variable {n d : ℕ}

def HasSheetsOff (S : Set (Fin n → ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) (c : MvPolynomial (Fin d) ℂ) : Prop :=
  ∀ y : Fin d → ℂ, eval y c ≠ 0 →
    ∃ (U : Set (Fin d → ℂ)) (N : ℕ) (s : Fin N → (Fin d → ℂ) → Fin n → ℂ),
      IsOpen U ∧ y ∈ U ∧ (∀ j, DifferentiableOn ℂ (s j) U) ∧
      ∀ y' ∈ U, (∀ j, s j y' ∈ {x | x ∈ S ∧ A.mulVec x = y'}) ∧
        Function.Injective (fun j => s j y') ∧
        {x | x ∈ S ∧ A.mulVec x = y'} ⊆ Set.range (fun j => s j y')

theorem hasSheetsOff_empty (A : Matrix (Fin d) (Fin n) ℂ) : HasSheetsOff ∅ A 1 := by
  intro y _
  refine ⟨Set.univ, 0, Fin.elim0, isOpen_univ, Set.mem_univ _, fun j => j.elim0, fun y' _ => ?_⟩
  refine ⟨fun j => j.elim0, fun i => i.elim0, ?_⟩
  rintro x ⟨hx, -⟩
  exact hx.elim

theorem hasSheetsOff_union {S T : Set (Fin n → ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {c c' e : MvPolynomial (Fin d) ℂ} (h₁ : HasSheetsOff S A c) (h₂ : HasSheetsOff T A c')
    (he : ∀ x ∈ S ∩ T, eval (A.mulVec x) e = 0) : HasSheetsOff (S ∪ T) A (c * c' * e) := by
  intro y hy
  simp only [map_mul, ne_eq, mul_eq_zero, not_or] at hy
  obtain ⟨⟨hc, hc'⟩, hey⟩ := hy
  obtain ⟨U₁, N₁, s₁, hU₁, hyU₁, hd₁, hs₁⟩ := h₁ y hc
  obtain ⟨U₂, N₂, s₂, hU₂, hyU₂, hd₂, hs₂⟩ := h₂ y hc'
  refine ⟨U₁ ∩ U₂ ∩ {w | eval w e ≠ 0}, N₁ + N₂, Fin.append s₁ s₂,
    (hU₁.inter hU₂).inter (isOpen_ne_fun (MvPolynomial.continuous_eval e) continuous_const),
    ⟨⟨hyU₁, hyU₂⟩, hey⟩, fun j => ?_, ?_⟩
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · rw [Fin.append_left]; exact (hd₁ j).mono fun w hw => hw.1.1
    · rw [Fin.append_right]; exact (hd₂ j).mono fun w hw => hw.1.2
  rintro w ⟨⟨hw₁, hw₂⟩, hwe⟩
  obtain ⟨hm₁, hi₁, hr₁⟩ := hs₁ w hw₁
  obtain ⟨hm₂, hi₂, hr₂⟩ := hs₂ w hw₂
  have hcross : ∀ i j, s₁ i w ≠ s₂ j w := by
    intro i j hij
    apply hwe
    rw [← (hm₁ i).2]
    exact he _ ⟨(hm₁ i).1, hij ▸ (hm₂ j).1⟩
  refine ⟨fun j => ?_, fun i j hij => ?_, ?_⟩
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · rw [Fin.append_left]; exact ⟨Or.inl (hm₁ j).1, (hm₁ j).2⟩
    · rw [Fin.append_right]; exact ⟨Or.inr (hm₂ j).1, (hm₂ j).2⟩
  · induction i using Fin.addCases with
    | left i =>
      induction j using Fin.addCases with
      | left j => simp only [Fin.append_left] at hij; rw [hi₁ hij]
      | right j => simp only [Fin.append_left, Fin.append_right] at hij; exact (hcross i j hij).elim
    | right i =>
      induction j using Fin.addCases with
      | left j => simp only [Fin.append_left, Fin.append_right] at hij; exact (hcross j i hij.symm).elim
      | right j => simp only [Fin.append_right] at hij; rw [hi₂ hij]
  · rintro x ⟨hx | hx, hAx⟩
    · obtain ⟨j, rfl⟩ := hr₁ ⟨hx, hAx⟩
      exact ⟨Fin.castAdd N₂ j, by simp only [Fin.append_left]⟩
    · obtain ⟨j, rfl⟩ := hr₂ ⟨hx, hAx⟩
      exact ⟨Fin.natAdd N₁ j, by simp only [Fin.append_right]⟩

theorem hasSheetsOff_biUnion (F : Finset (Ideal (MvPolynomial (Fin n) ℂ))) (A : Matrix (Fin d) (Fin n) ℂ)
    (hsh : ∀ Q ∈ F, ∃ c : MvPolynomial (Fin d) ℂ, c ≠ 0 ∧ HasSheetsOff (ComplexSets.zeroSet Q) A c)
    (hpair : ∀ Q ∈ F, ∀ Q' ∈ F, Q ≠ Q' → ∃ e : MvPolynomial (Fin d) ℂ, e ≠ 0 ∧
      ∀ x ∈ ComplexSets.zeroSet Q ∩ ComplexSets.zeroSet Q', eval (A.mulVec x) e = 0) :
    ∃ c : MvPolynomial (Fin d) ℂ, c ≠ 0 ∧ HasSheetsOff (⋃ Q ∈ F, ComplexSets.zeroSet Q) A c := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by simpa using hasSheetsOff_empty A⟩
  | insert Q F hQ ih =>
    obtain ⟨c₀, hc₀, h₀⟩ := ih (fun Q' h => hsh Q' (Finset.mem_insert_of_mem h))
      (fun Q' h Q'' h' hne => hpair Q' (Finset.mem_insert_of_mem h) Q'' (Finset.mem_insert_of_mem h') hne)
    obtain ⟨c, hc, h⟩ := hsh Q (Finset.mem_insert_self _ _)
    have hp : ∀ Q' ∈ F, ∃ e : MvPolynomial (Fin d) ℂ, e ≠ 0 ∧
        ∀ x ∈ ComplexSets.zeroSet Q ∩ ComplexSets.zeroSet Q', eval (A.mulVec x) e = 0 :=
      fun Q' hQ' => hpair Q (Finset.mem_insert_self _ _) Q' (Finset.mem_insert_of_mem hQ')
        (by rintro rfl; exact hQ hQ')
    choose! e he0 he using hp
    refine ⟨c * c₀ * ∏ Q' ∈ F, e Q', mul_ne_zero (mul_ne_zero hc hc₀) (Finset.prod_ne_zero_iff.mpr he0), ?_⟩
    rw [Finset.set_biUnion_insert]
    refine hasSheetsOff_union h h₀ ?_
    rintro x ⟨hxQ, hxF⟩
    obtain ⟨Q', hQ', hx'⟩ := Set.mem_iUnion₂.mp hxF
    rw [map_prod]
    exact Finset.prod_eq_zero hQ' (he Q' hQ' x ⟨hxQ, hx'⟩)

end QuasiFiniteSheets

open QuasiFiniteSheets in

theorem QuasiFiniteSheets.proof (h₁ : PrimeQuasiFiniteSheets.Statement)
    (h₂ : PrimePairMeetImage.Statement) : QuasiFiniteSheets.Statement := by
  intro n d I A hfin
  classical
  have hmin := I.finite_minimalPrimes_of_isNoetherianRing
  have hfinQ : ∀ Q ∈ I.minimalPrimes, ∀ y, (ComplexSets.fibre Q A y).Finite := fun Q hQ y =>
    (hfin y).subset fun x hx => ⟨fun q hq => hx.1 q (hQ.1.2 hq), hx.2⟩
  have hZ : ComplexSets.zeroSet I = ⋃ Q ∈ hmin.toFinset, ComplexSets.zeroSet Q := by
    ext x
    constructor
    · intro hx
      have hker : I ≤ RingHom.ker (eval x) := fun q hq => hx q hq
      have : (RingHom.ker (eval x : MvPolynomial (Fin n) ℂ →+* ℂ)).IsPrime := RingHom.ker_isPrime _
      obtain ⟨Q, hQ, hQle⟩ := Ideal.exists_minimalPrimes_le hker
      exact Set.mem_iUnion₂.mpr ⟨Q, hmin.mem_toFinset.mpr hQ, fun q hq => hQle hq⟩
    · intro hx
      obtain ⟨Q, hQ, hxQ⟩ := Set.mem_iUnion₂.mp hx
      exact fun q hq => hxQ q ((hmin.mem_toFinset.mp hQ).1.2 hq)
  obtain ⟨c, hc, hsh⟩ := hasSheetsOff_biUnion hmin.toFinset A
    (fun Q hQ => h₁ n d Q A (hmin.mem_toFinset.mp hQ).1.1 (hfinQ Q (hmin.mem_toFinset.mp hQ)))
    (fun Q hQ Q' hQ' hne => h₂ n d Q Q' A (hmin.mem_toFinset.mp hQ).1.1 (hmin.mem_toFinset.mp hQ').1.1 hne
      (hfinQ Q (hmin.mem_toFinset.mp hQ)) (hfinQ Q' (hmin.mem_toFinset.mp hQ')))
  rw [← hZ] at hsh
  exact ⟨c, hc, hsh⟩

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PSectionLengthSum
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace SectionLengthSum

theorem prime_between {A : Type*} [CommRing A] [IsNoetherianRing A] {J W Q : Ideal A} {f : A}
    (hWP : ∀ P ∈ J.minimalPrimes, P ≤ W → W ∈ (P ⊔ Ideal.span {f}).minimalPrimes)
    [hQ : Q.IsPrime] (hJQ : J ≤ Q) (hQW : Q ≤ W) : Q ∈ J.minimalPrimes ∨ Q = W := by
  obtain ⟨P, hP, hPQ⟩ := Ideal.exists_minimalPrimes_le hJQ
  have hPp : P.IsPrime := hP.1.1
  rcases eq_or_lt_of_le hPQ with h | hlt
  · exact Or.inl (h ▸ hP)
  rcases eq_or_lt_of_le hQW with h | hlt2
  · exact Or.inr h
  exfalso
  have hW := hWP P hP (hPQ.trans hQW)
  have hWp : W.IsPrime := hW.1.1
  have h1 := Ideal.map_height_le_one_of_mem_minimalPrimes hW
  set g := Ideal.Quotient.mk P
  have hsurj : Function.Surjective g := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker g = P := Ideal.mk_ker
  have hcm : ∀ I : Ideal A, P ≤ I → (I.map g).comap g = I := fun I hI => by
    rw [Ideal.comap_map_of_surjective g hsurj, ← RingHom.ker_eq_comap_bot, hker, sup_eq_left.mpr hI]
  have : (Q.map g).IsPrime :=
    Ideal.map_isPrime_of_surjective hsurj (by rw [hker]; exact hPQ)
  have : (W.map g).IsPrime :=
    Ideal.map_isPrime_of_surjective hsurj (by rw [hker]; exact hPQ.trans hQW)
  have : (W.map g).FiniteHeight := ⟨Or.inr (h1.trans_lt (WithTop.coe_lt_top 1)).ne⟩
  have : (Q.map g).FiniteHeight :=
    ⟨Or.inr ((Ideal.height_mono (Ideal.map_mono hQW)).trans_lt (h1.trans_lt (WithTop.coe_lt_top 1))).ne⟩
  have hbot : (⊥ : Ideal (A ⧸ P)) < Q.map g := by
    refine lt_of_le_of_ne bot_le fun h => hlt.ne ?_
    rw [← hcm Q hPQ, ← h, ← RingHom.ker_eq_comap_bot, hker]
  have hQW' : Q.map g < W.map g := by
    refine lt_of_le_of_ne (Ideal.map_mono hQW) fun h => hlt2.ne ?_
    rw [← hcm Q hPQ, h, hcm W (hPQ.trans hQW)]
  have h2 := Ideal.height_strict_mono_of_isPrime_of_isPrime hQW'
  have h3 := Ideal.height_strict_mono_of_isPrime_of_isPrime (I := ⊥) hbot
  have h4 : (Q.map g).height < 1 := h2.trans_le h1
  rw [Order.lt_one_iff] at h4
  rw [h4] at h3
  exact absurd h3 (not_lt_of_ge bot_le)

theorem length_ne_top_of_mem_minimalPrimes {B : Type*} [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
    (I : Ideal B) (hI : IsLocalRing.maximalIdeal B ∈ I.minimalPrimes) : Module.length B (B ⧸ I) ≠ ⊤ := by
  have : IsArtinianRing (B ⧸ I) := IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing _ hI
  have : IsArtinian B (B ⧸ I) := isArtinian_of_surjective_algebraMap (Ideal.Quotient.mk_surjective (I := I))
  exact Module.length_ne_top

theorem proof (hLoc : LocalSectionLengthSum.Statement) : SectionLengthSum.Statement := by
  intro A _ _ J W f hJ hf hW hWP
  classical
  have hWp : W.IsPrime := hW.1.1
  let B := Localization.AtPrime W
  let φ := algebraMap A B
  have : IsNoetherianRing B := IsLocalization.isNoetherianRing W.primeCompl B inferInstance
  have hmin : ∀ Q : Ideal B, Q ∈ (J.map φ).minimalPrimes ↔ Q.comap φ ∈ J.minimalPrimes := fun Q => by
    rw [IsLocalization.minimalPrimes_map W.primeCompl B J]
    rfl
  have hcomapW : ∀ Q : Ideal B, Q.IsPrime → Q.comap φ ≤ W := fun Q hQ x hx => by
    by_contra hxW
    exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ hx (IsLocalization.map_units B (⟨x, hxW⟩ : W.primeCompl)))
  have hmapcomap : ∀ Q : Ideal B, (Q.comap φ).map φ = Q := fun Q =>
    IsLocalization.map_under W.primeCompl B Q
  have hcomapmap : ∀ P : Ideal A, P.IsPrime → P ≤ W → (P.map φ).comap φ = P := fun P hP hPW =>
    IsLocalization.under_map_of_isPrime_disjoint W.primeCompl B hP
      (Set.disjoint_left.mpr fun x hx hxP => hx (hPW hxP))
  have hJ' : (J.map φ).IsRadical := by
    show (J.map φ).radical ≤ J.map φ
    rw [← IsLocalization.map_radical W.primeCompl B J, hJ.radical]
  have hf' : ∀ Q ∈ (J.map φ).minimalPrimes, φ f ∉ Q := fun Q hQ hfQ => hf _ ((hmin Q).1 hQ) hfQ
  have hdim : ∀ Q : Ideal B, Q.IsPrime → J.map φ ≤ Q →
      Q ∈ (J.map φ).minimalPrimes ∨ Q = IsLocalRing.maximalIdeal B := by
    intro Q hQ hJQ
    have : (Q.comap φ).IsPrime := hQ.comap φ
    rcases prime_between hWP (Ideal.map_le_iff_le_comap.mp hJQ) (hcomapW Q hQ) with h | h
    · exact Or.inl ((hmin Q).2 h)
    · right
      rw [← hmapcomap Q, h]
      exact IsLocalization.AtPrime.map_eq_maximalIdeal W B
  have key := hLoc B (J.map φ) (φ f) hJ' hf' hdim
  have hsup : ∀ I : Ideal A, (I ⊔ Ideal.span {f}).map φ = I.map φ ⊔ Ideal.span {φ f} := fun I => by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  have hlm : ∀ I : Ideal A, localMult (I ⊔ Ideal.span {f}) W =
      (Module.length B (B ⧸ (I.map φ ⊔ Ideal.span {φ f}))).toNat := fun I => by
    unfold localMult
    rw [dif_pos hWp, hsup]
  have hfW : φ f ∈ IsLocalRing.maximalIdeal B := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal W B]
    exact Ideal.mem_map_of_mem φ (hW.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f)))
  have hfin : ∀ Q ∈ (J.map φ).minimalPrimes,
      Module.length B (B ⧸ (Q ⊔ Ideal.span {φ f})) ≠ ⊤ := by
    intro Q hQ
    refine length_ne_top_of_mem_minimalPrimes _ ⟨⟨(IsLocalRing.maximalIdeal.isMaximal B).isPrime,
      sup_le (IsLocalRing.le_maximalIdeal hQ.1.1.ne_top) ((Ideal.span_singleton_le_iff_mem _).mpr hfW)⟩,
      fun Q₂ hQ₂ _ => ?_⟩
    rcases hdim Q₂ hQ₂.1 (hQ.1.2.trans (le_sup_left.trans hQ₂.2)) with h | h
    · exact absurd (hQ₂.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))) (hf' Q₂ h)
    · exact h.ge
  rw [hlm J, key, ENat.toNat_sum (fun Q hQ => hfin Q ((Set.Finite.mem_toFinset _).mp hQ))]
  symm
  refine Finset.sum_nbij' (fun P => P.map φ) (fun Q => Q.comap φ) ?_ ?_ ?_ ?_ ?_
  · intro P hP
    rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hP
    rw [Set.Finite.mem_toFinset, hmin, hcomapmap P hP.1.1.1 hP.2]
    exact hP.1
  · intro Q hQ
    rw [Set.Finite.mem_toFinset] at hQ
    rw [Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨(hmin Q).1 hQ, hcomapW Q hQ.1.1⟩
  · intro P hP
    rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hP
    exact hcomapmap P hP.1.1.1 hP.2
  · intro Q _
    exact hmapcomap Q
  · intro P _
    exact hlm P

end SectionLengthSum

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.SphereMeanDisc
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Measure Set Real

noncomputable section

namespace SphereMean

theorem integral_disc_radial (g : ℝ → ℝ) :
    ∫ z : ℂ, (Iio (1 : ℝ)).indicator g ‖z‖ = 2 * π * ∫ y in (0 : ℝ)..1, y * g y := by
  rw [integral_fun_norm_addHaar volume (fun r => (Iio (1 : ℝ)).indicator g r),
    Complex.finrank_real_complex, measureReal_def, Complex.volume_ball]
  have h1 : ∫ y in Ioi (0 : ℝ), y ^ (2 - 1) • (Iio (1 : ℝ)).indicator g y =
      ∫ y in Ioi (0 : ℝ), (Iio (1 : ℝ)).indicator (fun y => y * g y) y := by
    congr 1
    funext y
    by_cases hy : y < 1 <;> simp [indicator, hy]
  rw [h1, setIntegral_indicator measurableSet_Iio, Ioi_inter_Iio,
    intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  simp [nsmul_eq_mul]
  ring

theorem integrable_disc_radial (g : ℝ → ℝ) (hg : ContinuousOn (fun y => y * g y) (Icc 0 1)) :
    Integrable (fun z : ℂ => (Iio (1 : ℝ)).indicator g ‖z‖) := by
  rw [integrable_fun_norm_addHaar volume (f := fun r => (Iio (1 : ℝ)).indicator g r),
    Complex.finrank_real_complex]
  have h1 : (fun y : ℝ => y ^ (2 - 1) • (Iio (1 : ℝ)).indicator g y) =
      (Iio (1 : ℝ)).indicator (fun y => y * g y) := by
    funext y
    by_cases hy : y < 1 <;> simp [indicator, hy]
  rw [h1, IntegrableOn, integrable_indicator_iff measurableSet_Iio, IntegrableOn,
    Measure.restrict_restrict measurableSet_Iio, Iio_inter_Ioi]
  exact (hg.integrableOn_Icc).mono_set Ioo_subset_Icc_self

theorem integral_disc_pow (m : ℕ) :
    ∫ z : ℂ, (Iio (1 : ℝ)).indicator (fun r => (1 - r ^ 2) ^ m) ‖z‖ = π / (m + 1) := by
  rw [integral_disc_radial, integral_disc_weight]
  field_simp

theorem integral_disc_log_pow (m : ℕ) :
    ∫ z : ℂ, (Iio (1 : ℝ)).indicator (fun r => -log r * (1 - r ^ 2) ^ m) ‖z‖ =
      π * harmonic (m + 1) / (2 * (m + 1)) := by
  rw [integral_disc_radial]
  have h : ∫ y in (0 : ℝ)..1, y * (-log y * (1 - y ^ 2) ^ m) =
      -∫ y in (0 : ℝ)..1, y * log y * (1 - y ^ 2) ^ m := by
    rw [← intervalIntegral.integral_neg]
    congr 1
    funext y
    ring
  rw [h, integral_disc_log_weight]
  field_simp
  ring

theorem integrable_disc_pow (m : ℕ) :
    Integrable (fun z : ℂ => (Iio (1 : ℝ)).indicator (fun r => (1 - r ^ 2) ^ m) ‖z‖) :=
  integrable_disc_radial _ (by fun_prop)

theorem integrable_disc_log_pow (m : ℕ) :
    Integrable (fun z : ℂ => (Iio (1 : ℝ)).indicator (fun r => -log r * (1 - r ^ 2) ^ m) ‖z‖) := by
  apply integrable_disc_radial
  have : (fun y : ℝ => y * (-log y * (1 - y ^ 2) ^ m)) =
      fun y => -(y * log y) * (1 - y ^ 2) ^ m := by
    funext y; ring
  rw [this]
  exact (continuous_mul_log.neg.mul (by fun_prop)).continuousOn

end SphereMean

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChowFormSectionPerfect
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial

def ChowFormSectionPerfect.Statement : Prop :=
  ∀ (F : Type) [Field F] [PerfectField F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (u : Fin n → F),
    IsProjPrime I → IsChowForm I (e + 1) f → linForm u ∉ I →
      IsChowFormCycle (divCycle I u) e (specFirst f u)

end ObjectsChow

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsClosedPointChartField
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial

def ClosedPointChartField.Statement : Prop :=
  ∀ (F : Type) [Field F] (n : ℕ) (I : Ideal (MvPolynomial (Fin n) F)) (i : Fin n),
    IsProjPrime I → ringKrullDim (MvPolynomial (Fin n) F ⧸ I) = ((1 : ℕ) : WithBot ℕ∞) → X i ∉ I →
      IsField (MvPolynomial (Fin n) F ⧸ (I ⊔ Ideal.span {X i - 1})) ∧
        Module.Finite F (MvPolynomial (Fin n) F ⧸ (I ⊔ Ideal.span {X i - 1}))

end ObjectsChow

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsClosedPointConeCoord
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial

def ClosedPointConeCoord.Statement : Prop :=
  ∀ (F : Type) [Field F] (n : ℕ) (I : Ideal (MvPolynomial (Fin n) F)) (i : Fin n),
    IsProjPrime I → ringKrullDim (MvPolynomial (Fin n) F ⧸ I) = ((1 : ℕ) : WithBot ℕ∞) → X i ∉ I →
      ∀ (Ω : Type) [Field Ω] [Algebra F Ω] (y : Fin n → Ω), y ≠ 0 → (∀ g ∈ I, aeval y g = 0) → y i ≠ 0

end ObjectsChow

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeMapArea
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

open scoped ENNReal

def ConeMapArea.Statement : Prop :=
  ∀ (n e : ℕ) (ι : Type) [Countable ι] (U D : ι → Set (Fin e → ℂ))
    (v : ι → (Fin e → ℂ) → (Fin n → ℂ)) (F : EuclideanSpace ℂ (Fin n) → ℝ≥0∞),
    (∀ i, IsOpen (U i) ∧ MeasurableSet (D i) ∧ D i ⊆ U i ∧ DifferentiableOn ℂ (v i) (U i)) →
    Set.InjOn (fun q : ι × (Fin e → ℂ) × ℂ => q.2.2 • WithLp.toLp 2 (v q.1 q.2.1))
      {q | q.2.1 ∈ D q.1 ∧ q.2.2 ≠ 0} →
    Measurable F →
      ENNReal.ofReal (Real.pi ^ (e + 1) / ((e + 1).factorial : ℝ)) *
          ∫⁻ y in (fun q : ι × (Fin e → ℂ) × ℂ => q.2.2 • WithLp.toLp 2 (v q.1 q.2.1)) ''
              {q | q.2.1 ∈ D q.1 ∧ q.2.2 ≠ 0}, F y
            ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) =
        Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
            {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ j : Fin n, e + 1 ≤ (j : ℕ) → y j = 0} *
          ∑' i, ∫⁻ x in D i, ∫⁻ t : ℂ, F (t • WithLp.toLp 2 (v i x)) *
            ENNReal.ofReal (‖t‖ ^ (2 * e) * gramVol (v i) x)

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeMapAreaOne
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

open scoped ENNReal

def ConeMapAreaOne.Statement : Prop :=
  ∀ (n e : ℕ) (U D : Set (Fin e → ℂ)) (v : (Fin e → ℂ) → (Fin n → ℂ))
    (F : EuclideanSpace ℂ (Fin n) → ℝ≥0∞),
    IsOpen U → MeasurableSet D → D ⊆ U → DifferentiableOn ℂ v U →
    Set.InjOn (fun q : (Fin e → ℂ) × ℂ => q.2 • WithLp.toLp 2 (v q.1)) {q | q.1 ∈ D ∧ q.2 ≠ 0} →
    Measurable F →
      ENNReal.ofReal (Real.pi ^ (e + 1) / ((e + 1).factorial : ℝ)) *
          ∫⁻ y in (fun q : (Fin e → ℂ) × ℂ => q.2 • WithLp.toLp 2 (v q.1)) ''
              {q | q.1 ∈ D ∧ q.2 ≠ 0}, F y
            ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) =
        Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
            {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ j : Fin n, e + 1 ≤ (j : ℕ) → y j = 0} *
          ∫⁻ x in D, ∫⁻ t : ℂ, F (t • WithLp.toLp 2 (v x)) *
            ENNReal.ofReal (‖t‖ ^ (2 * e) * gramVol v x)

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeMeetNull
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

noncomputable section

def ConeMeetNull.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W W' : Ideal (MvPolynomial (Fin n) ℂ)), W.IsPrime → W'.IsPrime →
    W ≠ W' → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) ≤ ((e + 1 : ℕ) : WithBot ℕ∞) →
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W') ≤ ((e + 1 : ℕ) : WithBot ℕ∞) →
        Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (coneBall h W ∩ coneBall h W') = 0

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeSlab
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

noncomputable section

def ConeSlabBound.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ) (u : Fin n → ℂ),
    IsProjPrime W → IsChowForm W (e + 1) f → linForm u ∉ W →
      ∃ C α : ℝ, 0 < α ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
            (coneBall h W ∩ {y | ‖∑ j, u j * h.pointOf y j‖ ≤ ε * ‖y‖}) ≤
          ENNReal.ofReal (C * ε ^ α)

end

end GroundTheory.Heights₂.Heights
end

