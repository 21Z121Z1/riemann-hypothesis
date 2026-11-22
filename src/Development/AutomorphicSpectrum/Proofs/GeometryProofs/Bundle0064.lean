import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0016
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0033
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0057
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0059
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0003
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogDenominatorBoundPrimes
section
open GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.ClearConstants

private theorem prod_one_sub_lemma {Ω : Type} [Field Ω] (W : ValuationSubring Ω) (π : Ω)
    (s : Finset Ω) (h : ∀ μ ∈ s, ∃ u ∈ W, 1 - μ = π * u) :
    ∃ w ∈ W, ∏ μ ∈ s, (1 - μ) = w * π ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, W.one_mem, by simp⟩
  | insert a s ha ih =>
    obtain ⟨w, hw, hs⟩ := ih (fun μ hμ => h μ (Finset.mem_insert_of_mem hμ))
    obtain ⟨u, hu, hau⟩ := h a (Finset.mem_insert_self a s)
    refine ⟨u * w, mul_mem hu hw, ?_⟩
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, hs, hau]
    ring

theorem prime_eq_mul_pow {Ω : Type} [Field Ω] (W : ValuationSubring Ω) {p : ℕ} (hp : p.Prime) {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ p) : ∃ w ∈ W, (p : Ω) = w * (ζ - 1) ^ (p - 1) := by
  haveI := Fact.mk hp
  have hpow : ζ ^ p = 1 := hζ.pow_eq_one
  have hζW : ζ ∈ W := by
    rcases W.mem_or_inv_mem ζ with h | h
    · exact h
    · have hne : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
      have h1 : (ζ⁻¹) ^ (p - 1) * ζ⁻¹ = 1 := by
        rw [← pow_succ, Nat.sub_add_cancel hp.one_le, inv_pow, hpow, inv_one]
      have key : (ζ⁻¹) ^ (p - 1) = ζ := by
        calc (ζ⁻¹) ^ (p - 1) = (ζ⁻¹) ^ (p - 1) * ζ⁻¹ * ζ := by
              rw [mul_assoc, inv_mul_cancel₀ hne, mul_one]
          _ = ζ := by rw [h1, one_mul]
      rw [← key]
      exact pow_mem h _
  have hprod : (p : Ω) = ∏ μ ∈ primitiveRoots p Ω, (1 - μ) := by
    have h0 := Polynomial.eval_one_cyclotomic_prime (R := Ω) (p := p)
    rw [Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ, Polynomial.eval_prod] at h0
    simpa using h0.symm
  have hcard : (primitiveRoots p Ω).card = p - 1 := by
    rw [hζ.card_primitiveRoots, Nat.totient_prime hp]
  have hall : ∀ μ ∈ primitiveRoots p Ω, ∃ u ∈ W, 1 - μ = (ζ - 1) * u := by
    intro μ hμ
    have hμp : IsPrimitiveRoot μ p := (mem_primitiveRoots hp.pos).mp hμ
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hμp.pow_eq_one
    refine ⟨-(∑ j ∈ Finset.range i, ζ ^ j), neg_mem (sum_mem fun j _ => pow_mem hζW j), ?_⟩
    rw [← hi]
    linear_combination geom_sum_mul ζ i
  obtain ⟨w, hw, hw'⟩ := prod_one_sub_lemma W (ζ - 1) _ hall
  rw [hcard] at hw'
  exact ⟨w, hw, hprod.trans hw'⟩

def expo (q p : ℕ) : ℕ := if p = 2 then 2 * q else q / (p - 1)

theorem expo_cast {q p : ℕ} (hp : p.Prime) (hd : p - 1 ∣ q) :
    (expo q p : ℝ) = q * (if p = 2 then 2 else 1 / ((p : ℝ) - 1)) := by
  unfold expo
  by_cases h : p = 2
  · subst h
    simp only [if_true]
    push_cast
    ring
  · rw [if_neg h, if_neg h]
    have hne : ((p - 1 : ℕ) : ℝ) ≠ 0 := by
      have h2 : 2 ≤ p := hp.two_le
      have h3 : p - 1 ≠ 0 := by omega
      exact_mod_cast h3
    rw [Nat.cast_div hd hne, Nat.cast_sub hp.one_le]
    push_cast
    ring

theorem pow_expo_eq {Ω : Type} [Field Ω] (W : ValuationSubring Ω) {p q : ℕ} (hp : p.Prime) (hd : p - 1 ∣ q)
    {κ : Ω} (hκ : HT.IsCp p κ) : ∃ w ∈ W, ((p ^ expo q p : ℕ) : Ω) = w * κ ^ q := by
  unfold HT.IsCp at hκ
  by_cases h2 : p = 2
  · subst h2
    rw [if_pos rfl] at hκ
    refine ⟨1, W.one_mem, ?_⟩
    have he : expo q 2 = 2 * q := by simp [expo]
    rw [hκ, one_mul, he, pow_mul]
    norm_num
  · rw [if_neg h2] at hκ
    obtain ⟨ζ, hζ, rfl⟩ := hκ
    obtain ⟨r, rfl⟩ := hd
    obtain ⟨w₀, hw₀, hpw⟩ := prime_eq_mul_pow W hp hζ
    have hpos : 0 < p - 1 := by have := hp.two_le; omega
    refine ⟨w₀ ^ r, pow_mem hw₀ r, ?_⟩
    have he : expo ((p - 1) * r) p = r := by
      simp only [expo, if_neg h2]
      exact Nat.mul_div_cancel_left r hpos
    rw [he, Nat.cast_pow, hpw, mul_pow, ← pow_mul]

theorem clear_constants : ∀ (S : Finset ℕ) (m₀ : ℕ), (∀ p ∈ S, p.Prime) → 0 < m₀ → ∃ q m : ℕ, 0 < q ∧ 0 < m ∧
    Real.log m ≤ q * (Real.log m₀ + ∑ p ∈ S, (if p = 2 then 2 else 1 / ((p : ℝ) - 1)) * Real.log p) ∧
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] (W : ValuationSubring Ω) (κ : Ω), (κ = 1 ∨ ∃ p ∈ S, HT.IsCp p κ) →
      ∀ t : Ω, ((m₀ : Ω) * κ) * t ∈ W → (m : Ω) * t ^ q ∈ W := by
  intro S m₀ hS hm₀
  obtain ⟨q, hq⟩ : ∃ q : ℕ, q = ∏ p ∈ S, (p - 1) := ⟨_, rfl⟩
  have hqpos : 0 < q := by
    rw [hq]
    exact Finset.prod_pos fun p hp => by have := (hS p hp).two_le; omega
  have hdvd : ∀ p ∈ S, p - 1 ∣ q := fun p hp => by
    rw [hq]
    exact Finset.dvd_prod_of_mem (fun p => p - 1) hp
  refine ⟨q, m₀ ^ q * ∏ p ∈ S, p ^ expo q p, hqpos,
    Nat.mul_pos (pow_pos hm₀ q) (Finset.prod_pos fun p hp => pow_pos (hS p hp).pos _), ?_, ?_⟩
  · apply le_of_eq
    push_cast
    have hm0 : ((m₀ : ℝ) ^ q) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hm₀.ne')
    have hprod : (∏ p ∈ S, (p : ℝ) ^ expo q p) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun p hp => pow_ne_zero _ (by exact_mod_cast (hS p hp).ne_zero)
    rw [Real.log_mul hm0 hprod, Real.log_pow,
      Real.log_prod fun p hp => pow_ne_zero _ (by exact_mod_cast (hS p hp).ne_zero),
      mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Real.log_pow, expo_cast (hS p hp) (hdvd p hp)]
    ring
  · intro Ω _ _ W κ hκ t ht
    have hrest : ∀ T : Finset ℕ, (∏ x ∈ T, ((x : Ω) ^ expo q x)) ∈ W :=
      fun T => prod_mem fun x _ => pow_mem (natCast_mem W x) _
    push_cast
    rcases hκ with rfl | ⟨p, hpS, hp⟩
    · rw [mul_one] at ht
      have e : (m₀ : Ω) ^ q * (∏ x ∈ S, (x : Ω) ^ expo q x) * t ^ q
          = ((m₀ : Ω) * t) ^ q * ∏ x ∈ S, (x : Ω) ^ expo q x := by ring
      rw [e]
      exact mul_mem (pow_mem ht q) (hrest S)
    · obtain ⟨w, hw, hpw⟩ := pow_expo_eq W (hS p hpS) (hdvd p hpS) hp
      push_cast at hpw
      have hsplit : ∏ x ∈ S, (x : Ω) ^ expo q x = w * κ ^ q * ∏ x ∈ S.erase p, (x : Ω) ^ expo q x := by
        rw [← Finset.mul_prod_erase S (fun x => (x : Ω) ^ expo q x) hpS, hpw]
      rw [hsplit]
      have e : (m₀ : Ω) ^ q * (w * κ ^ q * ∏ x ∈ S.erase p, (x : Ω) ^ expo q x) * t ^ q
          = w * ((m₀ : Ω) * κ * t) ^ q * ∏ x ∈ S.erase p, (x : Ω) ^ expo q x := by ring
      rw [e]
      exact mul_mem (mul_mem hw (pow_mem ht q)) (hrest _)

end GlobalTheory.CompanionTheory.Ar.ClearConstants
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.MultihomogIdealEquivalence
section
open MvPolynomial

namespace GlobalTheory.CompanionTheory.Ggeo.CompMem

theorem blockWeight_weight_apply {K : Type} [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (m : (Σ k, ι k) →₀ ℕ) (k : K) :
    Finsupp.weight (GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight ι) m k = ∑ i, m ⟨k, i⟩ := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by intro; simp), Finset.sum_apply,
    Fintype.sum_sigma, Finset.sum_eq_single k]
  · simp [GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight]
  · intro b _ hb
    simp [GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight, Pi.single_eq_of_ne hb.symm]
  · simp

theorem comp_mem : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MvPolynomial (Σ k, ι k) ℤ)), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomogIdeal P → GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomogIdeal P := by
  intro K _ _ ι _ P hP f hf b
  obtain ⟨S, hS, rfl⟩ := hP
  classical
  letI := weightedGradedAlgebra ℤ (GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight ι)
  refine weightedHomogeneousComponent_mem_of_mem ℤ _ ?_ hf b
  refine Ideal.homogeneous_span _ S fun g hg => ?_
  obtain ⟨a, ha⟩ := hS g hg
  refine ⟨a, (mem_weightedHomogeneousSubmodule _ _ _ _).2 fun m hm => ?_⟩
  funext k
  rw [blockWeight_weight_apply]
  exact ha m (mem_support_iff.2 hm) k

end GlobalTheory.CompanionTheory.Ggeo.CompMem
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProperPullbackLineBundle
section
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
open Topology

namespace GlobalTheory.CompanionTheory.Ar.Flat.PushLoc

variable {X Y : Scheme.{0}} {Ω : Type} [Field Ω]
  {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξg : Spec (CommRingCat.of Ω) ⟶ Y} {e : Y ⟶ X}

theorem dominates_id (h : ξg ≫ e = ξ) : Dominates ξg ξ e (RingHom.id Ω) := by
  have h0 : Spec.map (CommRingCat.ofHom (RingHom.id Ω)) = 𝟙 _ := by
    rw [show CommRingCat.ofHom (RingHom.id Ω) = 𝟙 (CommRingCat.of Ω) from rfl, Spec.map_id]
  unfold Dominates
  rw [h0, Category.id_comp, h]

def emb (hD : Dominates ξg ξ e (RingHom.id Ω)) (p : Cpt ξg) : Cpt ξ := ⟨e p.1, hD.specializes p⟩

theorem genMap_stalkMap (hD : Dominates ξg ξ e (RingHom.id Ω)) (p : Cpt ξg) (s : X.presheaf.stalk (e p.1)) :
    genMap ξg p ((e.stalkMap p.1).hom s) = genMap ξ (emb hD p) s :=
  PullReg.stalkMap_comp_genMap hD p (hD.specializes p) s

theorem regAt_emb [IsPreimmersion e] (hD : Dominates ξg ξ e (RingHom.id Ω)) (p : Cpt ξg) :
    regAt ξg p = regAt ξ (emb hD p) := by
  ext a
  constructor
  · rintro ⟨s, rfl⟩
    obtain ⟨s', rfl⟩ := Scheme.Hom.stalkMap_surjective e p.1 s
    exact ⟨s', (genMap_stalkMap hD p s').symm⟩
  · rintro ⟨s, rfl⟩
    exact ⟨_, genMap_stalkMap hD p s⟩

theorem isCptGen_of [IsPreimmersion e] (h : ξg ≫ e = ξ) (hg : IsCptGen ξ) : IsCptGen ξg := by
  subst h
  have hD : Dominates ξg (ξg ≫ e) e (RingHom.id Ω) := dominates_id rfl
  refine ⟨?_, fun p => ?_⟩
  · have hb := hg.bij
    rw [Scheme.stalkClosedPointTo_comp] at hb
    have hs := Scheme.Hom.stalkMap_surjective e (ξg (IsLocalRing.closedPoint Ω))
    constructor
    · intro a b hab
      obtain ⟨a', rfl⟩ := hs a
      obtain ⟨b', rfl⟩ := hs b
      have : a' = b' := hb.1 hab
      rw [this]
    · intro c
      obtain ⟨a, rfl⟩ := hb.2 c
      exact ⟨_, rfl⟩
  · intro a b hab
    obtain ⟨a', rfl⟩ := Scheme.Hom.stalkMap_surjective e p.1 a
    obtain ⟨b', rfl⟩ := Scheme.Hom.stalkMap_surjective e p.1 b
    have h1 := genMap_stalkMap hD p a'
    have h2 := genMap_stalkMap hD p b'
    have : a' = b' := hg.inj (emb hD p) (h1.symm.trans (Eq.trans hab h2))
    rw [this]

theorem isIntegral_congr {R S : Subring Ω} (h : R = S) {a : Ω} (ha : IsIntegral R a) : IsIntegral S a := by
  subst h
  exact ha

theorem normalCpt_of [IsPreimmersion e] (hD : Dominates ξg ξ e (RingHom.id Ω)) (hn : NormalCpt ξ) :
    NormalCpt ξg := by
  intro p a ha
  rw [regAt_emb hD p]
  exact hn (emb hD p) a (isIntegral_congr (regAt_emb hD p) ha)

theorem coe_span_eq {R S : Subring Ω} (h : R = S) (M : Submodule S Ω) :
    ((Submodule.span R (M : Set Ω) : Submodule R Ω) : Set Ω) = M := by
  subst h
  rw [Submodule.span_eq]

theorem eq_span_of_coe {R S : Subring Ω} (h : R = S) {N : Submodule R Ω} {M : Submodule S Ω}
    (hNM : (N : Set Ω) = M) {A : Set Ω} (hM : M = Submodule.span S A) : N = Submodule.span R A := by
  subst h
  exact (SetLike.coe_injective hNM).trans hM

theorem coe_pull [IsPreimmersion e] (hD : Dominates ξg ξ e (RingHom.id Ω)) (L : Lat ξ Ω) (p : Cpt ξg) :
    ((L.pull ξg e (AddMonoidHom.id Ω) p : Submodule (regAt ξg p) Ω) : Set Ω) = L (emb hD p) := by
  rw [Lat.pull_apply L hD]
  have h0 : (AddMonoidHom.id Ω) '' (L (emb hD p) : Set Ω) = (L (emb hD p) : Set Ω) := Set.image_id _
  exact (congrArg (fun A : Set Ω => ((Submodule.span (regAt ξg p) A : Submodule _ Ω) : Set Ω)) h0).trans
    (coe_span_eq (regAt_emb hD p) _)

theorem isVBOn_pull [IsPreimmersion e] (hD : Dominates ξg ξ e (RingHom.id Ω)) (L : Lat ξ Ω) {T : Set (Cpt ξ)}
    (hT : ∀ x : Cpt ξ, x ∈ T ↔ x.1 ∈ Set.range e) (h : L.IsVBOn T 1 ⊤) :
    (L.pull ξg e (AddMonoidHom.id Ω)).IsVBOn Set.univ 1 ⊤ := by
  have hmem : ∀ p : Cpt ξg, emb hD p ∈ T := fun p => (hT _).2 ⟨p.1, rfl⟩
  intro p _
  obtain ⟨U, hU, b, hb, hq⟩ := h (emb hD p) (hmem p)
  refine ⟨e ⁻¹ᵁ U, hU, b, hb, fun q _ hqU => ?_⟩
  obtain ⟨h1, h2⟩ := hq (emb hD q) (hmem q) hqU
  exact ⟨h1, eq_span_of_coe (regAt_emb hD q) (coe_pull hD L q) h2⟩

theorem pull_pull_eq [IsPreimmersion e] {X' : Scheme.{0}} {ξ' : Spec (CommRingCat.of Ω) ⟶ X'} {f : X' ⟶ Y}
    (hD : Dominates ξg ξ e (RingHom.id Ω)) (hD' : Dominates ξ' ξg f (RingHom.id Ω))
    (hD'' : Dominates ξ' ξ (f ≫ e) (RingHom.id Ω)) (L : Lat ξ Ω) (p' : Cpt ξ') :
    (L.pull ξg e (AddMonoidHom.id Ω)).pull ξ' f (RingHom.id Ω).toAddMonoidHom p' =
      L.pull ξ' (f ≫ e) (AddMonoidHom.id Ω) p' := by
  rw [Lat.pull_apply _ hD', Lat.pull_apply _ hD'']
  congr 1
  have h1 := coe_pull hD L ⟨f p'.1, hD'.specializes p'⟩
  have h2 : emb hD ⟨f p'.1, hD'.specializes p'⟩ = ⟨(f ≫ e) p'.1, hD''.specializes p'⟩ :=
    Subtype.ext (Scheme.Hom.comp_apply f e p'.1).symm
  rw [h1, h2]
  rfl

theorem gen_descends : ∀ (X₀ Xg X' : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X₀) (ξg : Spec (CommRingCat.of Ω) ⟶ Xg) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (e : Xg ⟶ X₀) (f : X' ⟶ Xg) (L : Lat ξ Ω) (T : Set (Cpt ξ)) (t : Ω), IsPreimmersion e → IsProper f → IsLocallyNoetherian Xg → ξg ≫ e = ξ → ξ' ≫ f = ξg → IsCptGen ξ → NormalCpt ξ → (∀ x : Cpt ξ, x ∈ T ↔ x.1 ∈ Set.range e) → L.IsVBOn T 1 ⊤ → (∀ p' : Cpt ξ', (L.pull ξ' (f ≫ e) (AddMonoidHom.id _)).IsGenAt p' t) → ∀ x ∈ T, L.IsGenAt x t := by
  intro X₀ Xg X' Ω _ ξ ξg ξ' e f L T t hpre hprop hloc h1 h2 hgen hnorm hT hVB hG x hx
  haveI := hpre
  haveI := hprop
  haveI := hloc
  have hD : Dominates ξg ξ e (RingHom.id Ω) := dominates_id h1
  have hD' : Dominates ξ' ξg f (RingHom.id Ω) := dominates_id h2
  have hD'' : Dominates ξ' ξ (f ≫ e) (RingHom.id Ω) := dominates_id (by rw [← Category.assoc, h2, h1])
  obtain ⟨z, hz⟩ := (hT x).1 hx
  have hs : genPt ξg ⤳ z := by
    have h3 : e (genPt ξg) ⤳ e z := by
      rw [hD.map_genPt, hz]
      exact x.2
    exact (e.isEmbedding.isInducing.specializes_iff).1 h3
  have hp : (L.pull ξg e (AddMonoidHom.id Ω)).IsGenAt ⟨z, hs⟩ t :=
    GlobalTheory.T.line_bundle_normal_proper_pullback Xg Ω ξg X' Ω ξ' f (RingHom.id Ω) hD' Function.bijective_id (isCptGen_of h1 hgen)
      (normalCpt_of hD hnorm) (L.pull ξg e (AddMonoidHom.id Ω)) Set.univ ⟨z, hs⟩ t (isVBOn_pull hD L hT hVB)
      (fun _ _ => trivial) (fun p' _ => by
        have h4 := hG p'
        refine ⟨h4.1, ?_⟩
        rw [pull_pull_eq hD hD' hD'' L p']
        exact h4.2)
  have hx' : x = emb hD ⟨z, hs⟩ := Subtype.ext hz.symm
  rw [hx']
  exact ⟨hp.1, eq_span_of_coe (regAt_emb hD _).symm (coe_pull hD L _).symm hp.2⟩

end GlobalTheory.CompanionTheory.Ar.Flat.PushLoc
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PtsIntZero
section
noncomputable section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Topology
open GroundTheory.Heights₂.Heights.HilbertSamuel ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat.LineFlat

def two : ReciprocityTheory.ChartRestriction.G.Geo.HermLine (GlobalTheory (Fin 2)) where
  a := 0
  h _ := 2
  pos _ _ := two_pos
  smul _ _ _ := by simp

def root (r : Unit × Fin 2) : ReciprocityTheory.ChartRestriction.G.Geo.HermLine (GlobalTheory (Fin 2)) :=
  if r.2 = 0 then ProjLine.fsLine1.inv else ProjLine.fsLine1.tensor two

theorem sm1 : IsSmoothHerm ProjLine.fsLine1 := by
  intro z hz
  have hz0 : (WithLp.toLp 2 z : EuclideanSpace ℂ (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Ix (Fin 2))) ≠ 0 := by
    obtain ⟨i, hi⟩ := hz ()
    intro h0
    apply hi
    have h1 := congrArg (fun w : EuclideanSpace ℂ (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Ix (Fin 2)) => w ⟨(), i⟩) h0
    simpa using h1
  have hL := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Ix (Fin 2) => ℂ)).symm.contDiff
    (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
  exact ((contDiffAt_norm ℂ hz0).comp z hL.contDiffAt).contDiffWithinAt

theorem cj1 : IsConjInvariantH ProjLine.fsLine1 := by
  intro z
  show ‖WithLp.toLp 2 (fun p => (starRingEnd ℂ) (z p))‖ = ‖WithLp.toLp 2 z‖
  simp [EuclideanSpace.norm_eq]

theorem sm2 : IsSmoothHerm two := by
  show ContDiffOn ℝ _ (fun _ => (2 : ℝ)) _
  exact contDiffOn_const

def model : RootModel Unit 2 where
  K := Unit
  ι := GlobalTheory (Fin 2)
  Ω := ProjLine.FnField
  y := ProjLine.y
  arith := ProjLine.isArithVar_y'
  birational := ProjLine.birational_y
  xdeg r := (root r).a
  x _ r := root r
  x_deg _ _ := rfl
  x_smooth _ r := by
    unfold root; split_ifs
    · exact isSmoothHerm_inv sm1
    · exact isSmoothHerm_tensor sm1 sm2
  x_conj _ r := by
    unfold root; split_ifs
    · intro z; simp only [HermLine.inv]; rw [cj1 z]
    · intro z; simp only [HermLine.tensor, two]; rw [cj1 z]
  kA := 1
  kA_pos := one_pos
  A := ProjLine.fsLine1
  A_smooth := sm1
  A_conj := cj1
  δ := 1
  δ_pos := one_pos

theorem ptsInt_zero {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ} (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) :
    ReciprocityTheory.ChartRestriction.G.Geo.ptsIntegral P φ (fun _ => 0) = 0 := by
  simp [ReciprocityTheory.ChartRestriction.G.Geo.ptsIntegral, ReciprocityTheory.ChartRestriction.G.Geo.ptsIntegralAt, ReciprocityTheory.ChartRestriction.G.Geo.sheetDensity]

theorem one_not : (1 : ReciprocityTheory.ChartRestriction.G.Geo.MRing (GlobalTheory (Fin 2))) ∉ ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal ProjLine.y := by
  intro h
  rw [ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal, RingHom.mem_ker, map_one] at h
  exact one_ne_zero h

theorem hom1 : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (1 : ReciprocityTheory.ChartRestriction.G.Geo.MRing (GlobalTheory (Fin 2))) 0 := by
  intro m hm k
  rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
  subst hm
  simp

def phi : ℚ →+* ProjLine.FnField := algebraMap ℚ _

def S : FlatHerm ProjLine.y phi two where
  M := 1
  M_pos := one_pos
  f := 1
  g := 1
  df := 0
  dg := 0
  hf := hom1
  hg := hom1
  deg := by intro k; simp [two]
  f_ne := one_not
  g_ne := one_not
  unit := fun W hW _ _ => ⟨1, 1, fun h => hW.ne_top ((Ideal.eq_top_iff_one _).2 h), fun h => hW.ne_top ((Ideal.eq_top_iff_one _).2 h), by simp⟩
  κ _ := 1/2
  κ_pos _ := by norm_num
  κ_conj _ := rfl
  norm σ z _ := by simp [evC, two]

theorem ovi : OverInt ProjLine.y phi := by
  refine ⟨fun k => ⟨(0 : Fin 2), ?_⟩, fun c _ a => ?_⟩
  · simp [ProjLine.y]
  · have ha : IsIntegral ℤ (a : ℚ) := a.2
    obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 ha
    have e : phi (a : ℚ) = algebraMap ℤ ProjLine.FnField n := by
      rw [← hn]
      simp [phi]
    rw [e]
    exact Subalgebra.algebraMap_mem _ n

theorem dg : ∑ i : Fin 2, (root ((), i)).a = two.a := by
  funext k
  simp [root, two, Fin.sum_univ_two, HermLine.inv, HermLine.tensor, ProjLine.fsLine1, HermLine.ofCone]

def R : RootFlat model () where
  F := ℚ
  φ := phi
  overInt := ovi
  A := two
  A_smooth := sm2
  S := S
  deg := dg
  v _ _ := 0
  v_inv _ _ _ _ := rfl
  v_smooth _ := contDiffOn_const
  prod t _ z hz := by
    have := ProjLine.fsLine1.pos z hz.1
    simp only [model, root, two, Fin.prod_univ_two, HermLine.inv, HermLine.tensor]
    simp
    field_simp
  small m _ := by
    simp only [ptsInt_zero]
    exact tendsto_const_nhds

end GlobalTheory.CompanionTheory.Ar.Flat.LineFlat
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianAdicTorsionFourStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiabelian_adic_torsion_four : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (S : Scheme.{0}) [IsLocallyNoetherian S] (G : Over S) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (y : Spec (CommRingCat.of O) ⟶ S) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (X : TorsTower p G y La) (L : Type) [AddCommGroup L] [Module O L] (M : LieModel G y L), (∀ n f g w, X.IsDer M (n + 1) f w → (∀ a : La, g (lev p n a) = f (lev p (n + 1) (p • a))) → X.IsDer M n g w) ∧ ∀ (u : G ⟶ G) [IsMonHom u] (φ : La →+ La) (dφ : L →ₗ[O] L), X.Induces u φ → M.IsDiffOf u dφ → ∀ n (f g : LevGrp La p n → O), (∀ a, g (lev p n a) = f (lev p n (φ a))) → (f ∈ (X.Γ n).btOrder ⊤ → g ∈ (X.Γ n).btOrder ⊤) ∧ ∀ w, X.IsDer M n f w → X.IsDer M n g (w ∘ₗ dφ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.tw_funct | exact GlobalTheory.CompanionTheory.Ar.HT.tw_funct | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.tw_funct <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentVectorSumDualNumberStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_vector_sum_dual_number : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (U : G.left.Opens) (hU : IsAffineOpen U)
  (C : Type) [CommRing C] (y : Sp C ⟶ S) (u : Γ(G.left, U) →+* C),
  (1 : Over.mk y ⟶ G).left = spMap u ≫ hU.fromSpec →
  ∀ (v w : epsAt y ⟶ G), IsTanAt G y v → IsTanAt G y w →
  ∀ φ ψ χ : Γ(G.left, U) →+* DualNumber C, (∀ a, (φ a).fst = u a) → (∀ a, (ψ a).fst = u a) → (∀ a, (χ a).fst = u a) →
    (∀ a, (χ a).snd = (φ a).snd + (ψ a).snd) →
    v.left = spMap φ ≫ hU.fromSpec → w.left = spMap ψ ≫ hU.fromSpec → (v * w).left = spMap χ ≫ hU.fromSpec := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TanMul.mul_left_eq | exact GlobalTheory.CompanionTheory.Ar.TanMul.mul_left_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.TanMul.mul_left_eq <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwistIsoNonemptyStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_iso_nonempty : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : HostAut H), Nonempty (TwIso D g) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.tw_iso_nonempty | exact GlobalTheory.CompanionTheory.Ar.tw_iso_nonempty | (intros; apply GlobalTheory.CompanionTheory.Ar.tw_iso_nonempty <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwistOkAllStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_ok_all : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s) (g : HostAut H) (a : TwIso D g), TwOK o g a := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TwistOk.twOK_obj | exact GlobalTheory.CompanionTheory.Ar.TwistOk.twOK_obj | (intros; apply GlobalTheory.CompanionTheory.Ar.TwistOk.twOK_obj <;> assumption)
end

