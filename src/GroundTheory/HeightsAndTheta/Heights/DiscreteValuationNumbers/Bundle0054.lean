import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SameGenericSymm
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0044
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0048
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0053
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0001

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsBisFurther
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle)
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IFamily IsFieldIntersection)

def flagFurtherTerm_independent.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) (d N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V]
    (E E' : ChartBundle O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mseg x) N V),
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) d →
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.SameGeneric O x E E' →
    ∀ (φ₁ φ₂ : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagPair O x E E')
      (I : IFamily (IsLocalRing.ResidueField O) ι), IsFieldIntersection I →
    ∀ G : MvPolynomial (Fin N) ℤ, G.IsSymmetric →
    ∀ (r : ℕ) (y y' : Fin r → K → ℤ) (f g : Fin r → MRing ι O),
      (∀ l, IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsVertDiv O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) (y l - y' l)
        (f l) (g l)) →
    ∀ (c : ℕ) (Q : MvPolynomial (Fin r) ℤ), c ≤ d + 1 → G.IsHomogeneous c →
      Q.IsHomogeneous (d + 1 - c) → ∀ l : Fin r,
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O
                                (fun W => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum I W d
                                  (Fin.append (Fin.append φ₁.deg y) (Fin.append φ₁.deg' y'))
                                  (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff (Fin.natAdd N l)
                                    (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q)))
                                (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) (f l) (g l)) =
        IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O
          (fun W => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum I W d
            (Fin.append (Fin.append φ₂.deg y) (Fin.append φ₂.deg' y'))
            (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.divDiff (Fin.natAdd N l)
              (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q)))
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) (f l) (g l))

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpColonFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem pow_add_mul_eq_span_pow_mul {A : Type*} [CommRing A] {I : Ideal A} {k n₀ : ℕ} {y : A}
    (h : I ^ (n₀ + k) = Ideal.span {y} * I ^ n₀) (s : ℕ) :
    I ^ (n₀ + k * s) = Ideal.span {y ^ s} * I ^ n₀ := by
  have hprop : ∀ t, I ^ (n₀ + t + k) = Ideal.span {y} * I ^ (n₀ + t) := by
    intro t
    induction t with
    | zero => simpa using h
    | succ t ih =>
      rw [show n₀ + (t + 1) + k = n₀ + t + k + 1 by omega, pow_succ, ih,
        show n₀ + (t + 1) = n₀ + t + 1 by omega, pow_succ, mul_assoc]
  induction s with
  | zero => simp
  | succ s ih =>
    rw [show n₀ + k * (s + 1) = n₀ + k * s + k by ring, hprop, ih, ← mul_assoc,
      Ideal.span_singleton_mul_span_singleton, ← pow_succ']

theorem mem_div_self_mul_of_mem_div_self {A L : Type*} [CommRing A] [CommRing L] [Algebra A L]
    {P : Submodule A L} (Q : Submodule A L) {f : L} (hf : f ∈ P / P) : f ∈ (P * Q) / (P * Q) := by
  rw [Submodule.mem_div_iff_forall_mul_mem] at hf ⊢
  intro z hz
  refine Submodule.mul_induction_on hz (fun p hp q hq => ?_) (fun a b ha hb => ?_)
  · rw [← mul_assoc]
    exact Submodule.mul_mem_mul (hf p hp) hq
  · rw [mul_add]
    exact add_mem ha hb

theorem BlowUpColonFinite.proof (h₁ : PowSpanFinrankBounded.Statement.{u})
    (h₂ : PrincipalReductionOfBoundedGens.Statement.{u}) : BlowUpColonFinite.Statement.{u} := by
  intro A _ _ _ _ L _ _ hinj _hdim I hI
  obtain ⟨k, hk, y, hy, n₀, hred⟩ := h₂ A I (h₁ A _hdim I)
  have hlin : Algebra.linearMap A L = (Algebra.ofId A L).toLinearMap := LinearMap.ext fun _ => rfl
  have hmap : ∀ (J : Ideal A) (n : ℕ), (Submodule.map (Algebra.linearMap A L) J) ^ n =
      Submodule.map (Algebra.linearMap A L) (J ^ n) := fun J n => by
    rw [hlin]; exact (Submodule.map_pow _ _ n).symm
  set 𝓘 := Submodule.map (Algebra.linearMap A L) I with h𝓘

  have hy0 : y ≠ 0 := by
    rintro rfl
    have : I ^ (n₀ + k) = ⊥ := by
      rw [hred, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.bot_mul]
    exact pow_ne_zero _ hI this
  have hy' : algebraMap A L y ≠ 0 := fun h => hy0 (hinj (by rw [h, map_zero]))

  have hkey : ∀ s, 𝓘 ^ (n₀ + k * s) = Submodule.span A {algebraMap A L y ^ s} * 𝓘 ^ n₀ := by
    intro s
    rw [h𝓘, hmap, hmap, pow_add_mul_eq_span_pow_mul hred s, hlin, Submodule.map_mul,
      ← Ideal.submodule_span_eq, Submodule.map_span, Set.image_singleton,
      AlgHom.toLinearMap_apply, map_pow, Algebra.ofId_apply]

  have hle : ∀ n, 𝓘 ^ n / 𝓘 ^ n ≤ 𝓘 ^ n₀ / 𝓘 ^ n₀ := by
    intro n f hf
    have hn : n ≤ n₀ + k * n := by nlinarith
    have hf' := mem_div_self_mul_of_mem_div_self (𝓘 ^ (n₀ + k * n - n)) hf
    rw [← pow_add, Nat.add_sub_cancel' hn, hkey] at hf'
    rw [Submodule.mem_div_iff_forall_mul_mem] at hf' ⊢
    intro z hz
    obtain ⟨w, hw, hweq⟩ := Submodule.mem_span_singleton_mul.mp
      (hf' _ (Submodule.mem_span_singleton_mul.mpr ⟨z, hz, rfl⟩))
    have : f * z = w := by
      apply mul_left_cancel₀ (pow_ne_zero n hy')
      rw [hweq]; ring
    rw [this]; exact hw

  obtain ⟨a, haI, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  set c := algebraMap A L (a ^ n₀) with hc
  have hc0 : c ≠ 0 := fun h => pow_ne_zero n₀ ha0 (hinj (by rw [← hc, h, map_zero]))
  have hcI : c ∈ 𝓘 ^ n₀ := by
    rw [h𝓘, hmap]; exact Submodule.mem_map_of_mem (Ideal.pow_mem_pow haI n₀)
  have hfg : (𝓘 ^ n₀).FG := by
    rw [h𝓘, hmap]; exact (IsNoetherian.noetherian (I ^ n₀)).map _
  have hcol : (𝓘 ^ n₀ / 𝓘 ^ n₀).FG := by
    refine Submodule.fg_of_fg_map_injective (LinearMap.mulLeft A c)
      (fun x x' h => mul_left_cancel₀ hc0 h) (hfg.of_le ?_)
    rintro _ ⟨f, hf, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_div_iff_forall_mul_mem] at hf
    rw [LinearMap.mulLeft_apply, mul_comm]
    exact hf c hcI
  exact hcol.of_le (iSup_le hle)

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpLocRingInj
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section BlowUpLocRingInj

variable {R : Type*} [CommRing R] {K : Type} [DecidableEq K] {ι : K → Type} {J : Type}

theorem blowUpSubst_eq_C_mul_X_pow (P : Ideal (MRing ι R)) (u : J → MRing ι R) (v : Σ o, extIdx ι J o) :
    blowUpSubst P u v =
      Polynomial.C (blowUpEval P u (X v)) * Polynomial.X ^ (blockWeight (extIdx ι J) v none) := by
  obtain ⟨(_ | k), i⟩ := v
  · simp [blowUpSubst, blowUpEval, blockWeight]
  · simp [blowUpSubst, blowUpEval, blockWeight]

theorem aeval_blowUpSubst_monomial (P : Ideal (MRing ι R)) (u : J → MRing ι R)
    (d : (Σ o, extIdx ι J o) →₀ ℕ) (c : R) :
    aeval (blowUpSubst P u) (monomial d c) =
      Polynomial.C (blowUpEval P u (monomial d c)) *
        Polynomial.X ^ (Finsupp.weight (blockWeight (extIdx ι J)) d none) := by
  have key : ∃ q, aeval (blowUpSubst P u) (monomial d c) =
      Polynomial.C q * Polynomial.X ^ (Finsupp.weight (blockWeight (extIdx ι J)) d none) := by
    refine ⟨algebraMap R _ c * ∏ v ∈ d.support, blowUpEval P u (X v) ^ d v, ?_⟩
    have hp : ∀ (y : MRing ι R ⧸ P) (e k : ℕ),
        (Polynomial.C y * Polynomial.X ^ e) ^ k = Polynomial.C (y ^ k) * Polynomial.X ^ (e * k) := by
      intro y e k
      rw [map_pow, pow_mul]
      ring
    rw [aeval_monomial, Polynomial.algebraMap_apply, Finsupp.prod]
    simp_rw [blowUpSubst_eq_C_mul_X_pow, hp]
    rw [Finset.prod_mul_distrib, ← map_prod, Finset.prod_pow_eq_pow_sum, ← mul_assoc, ← map_mul]
    refine congrArg₂ (· * ·) rfl (congrArg _ ?_)
    rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp [mul_comm]
  obtain ⟨q, hq⟩ := key
  rw [hq]
  congr 2
  change q = Polynomial.eval 1 (aeval (blowUpSubst P u) (monomial d c))
  rw [hq]
  simp

theorem aeval_blowUpSubst_eq_C_blowUpEval_mul_X_pow (P : Ideal (MRing ι R)) (u : J → MRing ι R)
    {G : MRing (extIdx ι J) R} {b : Option K → ℕ} (hG : IsMultiHomog G b) :
    aeval (blowUpSubst P u) G = Polynomial.C (blowUpEval P u G) * Polynomial.X ^ b none := by
  conv_lhs => rw [G.as_sum]
  conv_rhs => rw [G.as_sum]
  rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [aeval_blowUpSubst_monomial, hG (mem_support_iff.mp hd)]

theorem mem_blowUpOf_of_isMultiHomog {P : Ideal (MRing ι R)} {u : J → MRing ι R}
    {G : MRing (extIdx ι J) R} {b : Option K → ℕ} (hG : IsMultiHomog G b) (h : blowUpEval P u G = 0) :
    G ∈ blowUpOf P u := by
  rw [blowUpOf, RingHom.mem_ker, aeval_blowUpSubst_eq_C_blowUpEval_mul_X_pow P u hG, h, map_zero, zero_mul]

theorem algebraMap_blowUpEval_ne_zero {P : Ideal (MRing ι R)} [P.IsPrime] {u : J → MRing ι R}
    {Q : Ideal (MRing (extIdx ι J) R)} (hle : blowUpOf P u ≤ Q) {G : MRing (extIdx ι J) R}
    {b : Option K → ℕ} (hG : IsMultiHomog G b) (hGQ : G ∉ Q) :
    algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (blowUpEval P u G) ≠ 0 := by
  rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective _ _)]
  exact fun h => hGQ (hle (mem_blowUpOf_of_isMultiHomog hG h))

theorem exists_eq_div_of_mem_blowUpLocRing {P : Ideal (MRing ι R)} [P.IsPrime] {u : J → MRing ι R}
    {Q : Ideal (MRing (extIdx ι J) R)} (hQ : Q.IsPrime) (hle : blowUpOf P u ≤ Q)
    {z : FractionRing (MRing ι R ⧸ P)} (hz : z ∈ blowUpLocRing P u Q) :
    ∃ (b : Option K → ℕ) (F G : MRing (extIdx ι J) R), IsMultiHomog F b ∧ IsMultiHomog G b ∧ G ∉ Q ∧
      z = algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (blowUpEval P u F) /
        algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (blowUpEval P u G) := by
  have h1 : (1 : MRing (extIdx ι J) R) ∉ Q := fun h => hQ.ne_top ((Ideal.eq_top_iff_one Q).mpr h)
  induction hz using Subring.closure_induction with
  | mem x hx => exact hx
  | zero =>
    exact ⟨0, 0, 1, isWeightedHomogeneous_zero R _ _, isWeightedHomogeneous_one R _, h1, by simp⟩
  | one =>
    exact ⟨0, 1, 1, isWeightedHomogeneous_one R _, isWeightedHomogeneous_one R _, h1, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨b₁, F₁, G₁, hF₁, hG₁, hG₁Q, rfl⟩ := hx
    obtain ⟨b₂, F₂, G₂, hF₂, hG₂, hG₂Q, rfl⟩ := hy
    refine ⟨b₁ + b₂, F₁ * G₂ + G₁ * F₂, G₁ * G₂,
      IsWeightedHomogeneous.add (IsWeightedHomogeneous.mul hF₁ hG₂) (IsWeightedHomogeneous.mul hG₁ hF₂),
      IsWeightedHomogeneous.mul hG₁ hG₂, fun h => (hQ.mem_or_mem h).elim hG₁Q hG₂Q, ?_⟩
    rw [div_add_div _ _ (algebraMap_blowUpEval_ne_zero hle hG₁ hG₁Q)
      (algebraMap_blowUpEval_ne_zero hle hG₂ hG₂Q)]
    simp only [map_add, map_mul]
  | neg x _ hx =>
    obtain ⟨b, F, G, hF, hG, hGQ, rfl⟩ := hx
    refine ⟨b, -F, G, fun d hd => hF (by rwa [coeff_neg, neg_ne_zero] at hd), hG, hGQ, ?_⟩
    rw [map_neg, map_neg, neg_div]
  | mul x y _ _ hx hy =>
    obtain ⟨b₁, F₁, G₁, hF₁, hG₁, hG₁Q, rfl⟩ := hx
    obtain ⟨b₂, F₂, G₂, hF₂, hG₂, hG₂Q, rfl⟩ := hy
    refine ⟨b₁ + b₂, F₁ * F₂, G₁ * G₂, IsWeightedHomogeneous.mul hF₁ hF₂,
      IsWeightedHomogeneous.mul hG₁ hG₂, fun h => (hQ.mem_or_mem h).elim hG₁Q hG₂Q, ?_⟩
    rw [div_mul_div_comm]
    simp only [map_mul]

theorem exists_monomial_not_mem_of_isMultiHomog {Q : Ideal (MRing (extIdx ι J) R)} (hQ : Q.IsPrime)
    (hrel : IsRelevant Q) {F : MRing (extIdx ι J) R} {b : Option K → ℕ} (hF : IsMultiHomog F b)
    (hF0 : F ≠ 0) : ∃ M : MRing (extIdx ι J) R, IsMultiHomog M b ∧ M ∉ Q := by
  classical
  obtain ⟨d, hd⟩ := exists_coeff_ne_zero hF0
  choose i hi using hrel
  let e := Finsupp.mapDomain (fun v : Σ o, extIdx ι J o => (⟨v.1, i v.1⟩ : Σ o, extIdx ι J o)) d
  refine ⟨monomial e 1, isWeightedHomogeneous_monomial _ _ _ ?_, fun hmem => ?_⟩
  · rw [← hF hd]
    change Finsupp.linearCombination ℕ _ e = Finsupp.linearCombination ℕ _ d
    rw [Finsupp.linearCombination_mapDomain]
    rfl
  · have hmon : (monomial e 1 : MRing (extIdx ι J) R) ∈ Q.primeCompl := by
      rw [monomial_eq, map_one, one_mul, Finsupp.prod]
      refine prod_mem fun v hv => pow_mem ?_ _
      obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hv)
      exact hi w.1
    exact hmon hmem

theorem mem_of_blowUpLocRing_le {P : Ideal (MRing ι R)} [P.IsPrime] {u : J → MRing ι R}
    {Q Q' : Ideal (MRing (extIdx ι J) R)} (hQ : Q.IsPrime) (hrel : IsRelevant Q)
    (hle : blowUpOf P u ≤ Q) (hle' : blowUpOf P u ≤ Q')
    (hsub : blowUpLocRing P u Q' ≤ blowUpLocRing P u Q) {F : MRing (extIdx ι J) R} {b : Option K → ℕ}
    (hF : IsMultiHomog F b) (hFQ : F ∈ Q) : F ∈ Q' := by
  by_contra hFQ'
  have hF0 : F ≠ 0 := fun h => hFQ' (h ▸ Q'.zero_mem)
  obtain ⟨M, hM, hMQ⟩ := exists_monomial_not_mem_of_isMultiHomog hQ hrel hF hF0
  have hz : algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (blowUpEval P u M) /
      algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (blowUpEval P u F) ∈
        blowUpLocRing P u Q :=
    hsub (Subring.subset_closure ⟨b, M, F, hM, hF, hFQ', rfl⟩)
  obtain ⟨b₁, F₁, G₁, hF₁, hG₁, hG₁Q, heq⟩ := exists_eq_div_of_mem_blowUpLocRing hQ hle hz
  rw [div_eq_div_iff (algebraMap_blowUpEval_ne_zero hle' hF hFQ')
    (algebraMap_blowUpEval_ne_zero hle hG₁ hG₁Q)] at heq
  have hinj : blowUpEval P u M * blowUpEval P u G₁ = blowUpEval P u F₁ * blowUpEval P u F :=
    IsFractionRing.injective (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (by
      rw [map_mul, map_mul]
      exact heq)
  have h0 : blowUpEval P u (M * G₁ - F * F₁) = 0 := by
    rw [map_sub, map_mul, map_mul, hinj]
    ring
  have hmem : M * G₁ - F * F₁ ∈ Q :=
    hle (mem_blowUpOf_of_isMultiHomog (IsWeightedHomogeneous.sub
      (IsWeightedHomogeneous.mul hM hG₁) (IsWeightedHomogeneous.mul hF hF₁)) h0)
  rw [Submodule.sub_mem_iff_left _ (Q.mul_mem_right F₁ hFQ)] at hmem
  exact (hQ.mem_or_mem hmem).elim hMQ hG₁Q

theorem le_of_blowUpLocRing_le {P : Ideal (MRing ι R)} [P.IsPrime] {u : J → MRing ι R}
    {Q Q' : Ideal (MRing (extIdx ι J) R)} (hQ : Q.IsPrime) (hQh : IsMultiHomogIdeal Q)
    (hrel : IsRelevant Q) (hle : blowUpOf P u ≤ Q) (hle' : blowUpOf P u ≤ Q')
    (hsub : blowUpLocRing P u Q' ≤ blowUpLocRing P u Q) : Q ≤ Q' := by
  intro f hf
  rw [← sum_weightedHomogeneousComponent (blockWeight (extIdx ι J)) f,
    finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]
  exact Q'.sum_mem fun b _ => mem_of_blowUpLocRing_le hQ hrel hle hle' hsub
    (weightedHomogeneousComponent_isWeightedHomogeneous (n := b) (φ := f)) (hQh f hf b)

theorem BlowUpLocRingInj.proof : BlowUpLocRingInj.Statement.{u} := by
  intro R _ K _ ι J P _ u Q Q' hQ hQh hQr hQle hQ' hQ'h hQ'r hQ'le heq
  exact le_antisymm (le_of_blowUpLocRing_le hQ hQh hQr hQle hQ'le heq.ge)
    (le_of_blowUpLocRing_le hQ' hQ'h hQ'r hQ'le hQle heq.le)

end BlowUpLocRingInj

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpOverLocFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Algebra

variable {L : Type*} [Field L]

theorem exists_mul_mem_of_mem_blowUpColon (A : Subring L) (I : Ideal A) (hI : I ≠ ⊥) {g : L}
    (hg : g ∈ blowUpColon L I) : ∃ d : A, d ≠ 0 ∧ ∃ r : A, algebraMap A L d * g = algebraMap A L r := by
  obtain ⟨y, hyI, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  refine Submodule.iSup_induction _ (motive := fun g => ∃ d : A, d ≠ 0 ∧ ∃ r : A,
    algebraMap A L d * g = algebraMap A L r) hg ?_ ⟨1, one_ne_zero, 0, by simp⟩ ?_
  · intro m g hg
    have hy : algebraMap A L y ^ m ∈ (Submodule.map (Algebra.linearMap A L) I) ^ m :=
      Submodule.pow_mem_pow _ (Submodule.mem_map_of_mem hyI) m
    have hgy := (Submodule.mem_div_iff_forall_mul_mem.mp hg) _ hy
    have h1 : Submodule.map (Algebra.linearMap A L) I ≤ 1 := by
      rw [Submodule.one_eq_range]
      exact LinearMap.map_le_range
    have hone : ∀ k : ℕ, (Submodule.map (Algebra.linearMap A L) I) ^ k ≤ 1 := by
      intro k
      induction k with
      | zero => exact (pow_zero _).le
      | succ k ih =>
        rw [pow_succ]
        exact (mul_le_mul' ih h1).trans (mul_one _).le
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp (hone m hgy)
    refine ⟨y ^ m, pow_ne_zero _ hy0, r, ?_⟩
    rw [map_pow, hr, mul_comm]
  · rintro g₁ g₂ ⟨d₁, hd₁, r₁, h₁⟩ ⟨d₂, hd₂, r₂, h₂⟩
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, d₂ * r₁ + d₁ * r₂, ?_⟩
    simp only [map_mul, map_add, ← h₁, ← h₂]
    ring

theorem finite_finrank_one_of_le_blowUpColon (A B : Subring L) [IsNoetherianRing A] (hAB : A ≤ B)
    (I : Ideal A) (hI : I ≠ ⊥) (hfg : (blowUpColon L I).FG) (hle : ∀ f ∈ B, f ∈ blowUpColon L I) :
    letI := (Subring.inclusion hAB).toAlgebra
    Module.Finite A B ∧ Module.finrank A B = 1 := by
  classical
  let _ := (Subring.inclusion hAB).toAlgebra

  let Bs : Submodule A L :=
    { carrier := B
      add_mem' := fun h₁ h₂ => add_mem h₁ h₂
      zero_mem' := zero_mem _
      smul_mem' := fun r f hf => by
        rw [Algebra.smul_def]
        exact mul_mem (hAB r.2) hf }
  obtain ⟨s, hs⟩ : Bs.FG := hfg.of_le fun f hf => hle f hf

  have hsB : ∀ g ∈ s, ∃ d : A, d ≠ 0 ∧ ∃ r : A, algebraMap A L d * g = algebraMap A L r := fun g hg =>
    exists_mul_mem_of_mem_blowUpColon A I hI (hle g (show g ∈ Bs from hs ▸ Submodule.subset_span hg))
  choose! dg hdg0 rg hrg using hsB
  have hd0 : (∏ g ∈ s, dg g) ≠ 0 := Finset.prod_ne_zero_iff.mpr hdg0
  let T : Submodule A L :=
    { carrier := {g | ∃ r : A, algebraMap A L (∏ g ∈ s, dg g) * g = algebraMap A L r}
      add_mem' := fun ⟨r₁, h₁⟩ ⟨r₂, h₂⟩ => ⟨r₁ + r₂, by rw [map_add, ← h₁, ← h₂, mul_add]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := fun c g ⟨r, hr⟩ => ⟨c * r, by
        rw [Algebra.smul_def, map_mul, ← hr]
        ring⟩ }
  have hBT : Bs ≤ T := by
    rw [← hs, Submodule.span_le]
    intro g hg
    refine ⟨(∏ g' ∈ s.erase g, dg g') * rg g, ?_⟩
    rw [map_mul, ← hrg g hg, ← Finset.prod_erase_mul s dg hg, map_mul]
    ring

  let φ : Bs →ₗ[A] L := (LinearMap.mulLeft A (algebraMap A L (∏ g ∈ s, dg g))).comp Bs.subtype
  have hφ : Function.Injective φ := fun f₁ f₂ h => Subtype.ext
    (mul_left_cancel₀ (fun h0 => hd0 (Subtype.ext h0)) h)
  have hφr : LinearMap.range φ ≤ LinearMap.range (Algebra.linearMap A L) := by
    rintro _ ⟨f, rfl⟩
    obtain ⟨r, hr⟩ := hBT f.2
    exact ⟨r, hr.symm⟩
  have hinj : Function.Injective (Algebra.linearMap A L) := fun _ _ h => Subtype.ext h
  have hle1 : Module.rank A Bs ≤ 1 := by
    rw [← rank_range_of_injective φ hφ, ← Module.rank_self A,
      ← rank_range_of_injective _ hinj]
    exact Submodule.rank_mono hφr
  let ψ : A →ₗ[A] Bs := (Algebra.linearMap A L).codRestrict Bs fun r => hAB r.2
  have hge1 : 1 ≤ Module.rank A Bs := by
    rw [← Module.rank_self A]
    exact LinearMap.rank_le_of_injective ψ fun x y h =>
      hinj (show Algebra.linearMap A L x = Algebra.linearMap A L y from congrArg (fun z : Bs => (z : L)) h)

  let e : Bs ≃ₗ[A] B :=
    { toFun := fun f => ⟨f.1, f.2⟩
      invFun := fun f => ⟨f.1, f.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have : Module.Finite A Bs := Module.Finite.iff_fg.mpr ⟨s, hs⟩
  refine ⟨Module.Finite.equiv e, ?_⟩
  rw [← e.finrank_eq]
  exact Module.finrank_eq_of_rank_eq (le_antisymm hle1 (by exact_mod_cast hge1))

end Algebra

theorem BlowUpOverLocFinite.proof (hloc : HomLocRingLocal.Statement.{u})
    (hchart : BlowUpOverLocInChart.Statement.{u}) (hcolon : ChartsInColon.Statement.{u})
    (hfin : BlowUpColonFinite.Statement.{u}) : BlowUpOverLocFinite.Statement.{u} := by
  intro O _ _ _ K _ _ ι _ J _ P n hP N u hu ⟨j₀, hj₀⟩ c x hx hxP W hW hWrel
  have := hP.multiProj.isPrime
  obtain ⟨hL, hN, hD⟩ := hloc O K ι P hP.multiProj c x hx hxP W hW hWrel
  have hWp : W.IsPrime := hW.1.1
  have hPW : P ≤ W := le_sup_left.trans hW.1.2
  have he : ∀ f, f ∉ P → algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P))
      (Ideal.Quotient.mk P f) ≠ 0 := fun f hf h0 => hf (by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact IsFractionRing.injective _ (FractionRing (MRing ι O ⧸ P)) (h0.trans (map_zero _).symm))
  have he0 : ∀ f, f ∈ P → algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P))
      (Ideal.Quotient.mk P f) = 0 := fun f hf => by
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hf, map_zero]
  obtain ⟨i, hi⟩ := powMonomial_not_mem hWp hWrel N
  have hh0 := he (powMonomial N i) fun hm => hi (hPW hm)
  let a : J → homLocRing P W := fun k =>
    ⟨algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P (u k)) /
      algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P (powMonomial N i)),
      Subring.subset_closure ⟨N, u k, powMonomial N i, hu k, isMultiHomog_powMonomial N i, hi, rfl⟩⟩
  have hI : Ideal.span (Set.range a) ≠ ⊥ := by
    intro hb
    have h1 : a j₀ ∈ Ideal.span (Set.range a) := Ideal.subset_span ⟨j₀, rfl⟩
    rw [hb, Ideal.mem_bot] at h1
    exact div_ne_zero (he _ hj₀) hh0 (congrArg Subtype.val h1)

  have hle : ∀ f ∈ blowUpOverLoc P W u, f ∈ blowUpColon (FractionRing (MRing ι O ⧸ P)) (Ideal.span (Set.range a)) := by
    intro f hf
    refine hcolon (homLocRing P W) _ J a f fun k hk => ?_
    have huk : u k ∉ P := fun hm => hk (by
      show algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P (u k)) / _ = 0
      rw [he0 _ hm, zero_div])
    refine (Subring.closure_le (t := (Algebra.adjoin (homLocRing P W) _).toSubring)).mpr
      (Set.union_subset ?_ ?_) (hchart O K ι J P W hP.multiProj.multiHomog hWp hPW hWrel N u hu k huk hf)
    · intro z hz
      exact Subalgebra.algebraMap_mem _ (⟨z, hz⟩ : homLocRing P W)
    · rintro _ ⟨l, rfl⟩
      refine Algebra.subset_adjoin ⟨l, ?_⟩
      exact div_div_div_cancel_right₀ hh0
        (algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P (u l)))
        (algebraMap (MRing ι O ⧸ P) (FractionRing (MRing ι O ⧸ P)) (Ideal.Quotient.mk P (u k)))
  have := hN
  exact finite_finrank_one_of_le_blowUpColon (homLocRing P W) (blowUpOverLoc P W u)
    (homLocRing_le_blowUpOverLoc P W u) _ hI
    (hfin (homLocRing P W) _ (fun _ _ h => Subtype.ext h) hD _ hI) hle

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

