import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0014
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Formalism.FrobeniusOrbits.RealSubfieldLeCompositum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0142
import Development.AutomorphicArithmetic.PrimeDiscriminants.CycImage
import Development.AutomorphicArithmetic.CyclotomicBounds.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0011
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0366
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0324
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0356
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0254
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0251
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0102
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0198
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0064
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0367
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0345
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0358

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameFixedLift
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices

namespace GlobalTheory.TameFixedLift

open Pointwise

theorem transfer {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [Algebra ℚ Ω]
    (A : ValuationSubring Ω) (l : ℕ) [Fact l.Prime] (σ : G ℚ Ω) (hσ : σ ∈ Ine (F := ℚ) A)
    (hfix : ∀ x : E, σ (algebraMap E Ω x) = algebraMap E Ω x) :
    ∃ g ∈ Ine (F := E) A, cycZ (F := E) (Ω := Ω) l g = cycZ (F := ℚ) (Ω := Ω) l σ := by
  refine ⟨AlgEquiv.ofRingEquiv (f := (σ : Ω ≃+* Ω)) hfix, ⟨?_, hσ.2⟩, rfl⟩
  have h : σ • A = A := hσ.1
  exact h

theorem root_fix {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (l : ℕ) [Fact l.Prime] (n : ℕ)
    (σ : G ℚ Ω) (u : ℤ_[l])
    (h : ((cycZ (F := ℚ) (Ω := Ω) l σ : ℤ_[l]ˣ) : ℤ_[l]) = 1 + (l : ℤ_[l]) ^ n * u)
    (t : Ω) (ht : t ^ l ^ n = 1) : σ t = t := by
  have : CharZero Ω := algebraRat.charZero Ω
  have : ∀ i : ℕ, NeZero ((l ^ i : ℕ) : Ω) := fun i =>
    ⟨by exact_mod_cast pow_ne_zero i (Fact.out : l.Prime).ne_zero⟩
  have h1 := cyclotomicCharacter.spec l (n := n) (σ : Ω ≃+* Ω) t ht
  have h2 : ((cyclotomicCharacter Ω l (σ : Ω ≃+* Ω) : ℤ_[l]ˣ) : ℤ_[l]) = 1 + (l : ℤ_[l]) ^ n * u := h
  have h3 : PadicInt.toZModPow n ((l : ℤ_[l]) ^ n) = 0 := by
    rw [← RingHom.mem_ker, PadicInt.ker_toZModPow]; exact Ideal.mem_span_singleton_self _
  rw [h2, map_add, map_mul, h3, zero_mul, add_zero, map_one] at h1
  have h4 : t ^ (1 : ZMod (l ^ n)).val = t := by
    rw [ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 ht, pow_one]
  rw [h4] at h1
  exact h1

theorem exists_place (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] :
    ∃ w, w ∈ placesOver E l := by
  have hl : l.Prime := Fact.out
  have hnu : Ideal.span {(l : 𝓞 E)} ≠ ⊤ := by
    intro h
    have h1 := congrArg Ideal.absNorm h
    rw [Ideal.absNorm_span_natCast, Ideal.absNorm_top] at h1
    rcases Nat.pow_eq_one.mp h1 with h2 | h2
    · exact hl.one_lt.ne' h2
    · exact Module.finrank_pos.ne' h2
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hnu
  have hmem : (l : 𝓞 E) ∈ M := hle (Ideal.mem_span_singleton_self _)
  refine ⟨⟨M, hM.isPrime, ?_⟩, hmem⟩
  rintro rfl
  rw [Ideal.mem_bot] at hmem
  exact hl.ne_zero (by exact_mod_cast hmem)

private theorem eq_one_of_cong {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {l m : ℕ}
    (hA : A.valuation (l : Ω) < 1) (hc : Nat.Coprime m l) {z : Ω} (hz : z ^ m = 1)
    (h1 : A.valuation (z - 1) < 1) : z = 1 := by
  by_contra hne
  have hint : ∀ n : ℤ, A.valuation (n : Ω) ≤ 1 := fun n =>
    (A.valuation_le_one_iff _).mpr (intCast_mem A n)
  have hz1 : A.valuation z ≤ 1 := by
    have := Valuation.map_add_le A.valuation h1.le (le_of_eq (map_one A.valuation))
    simpa using this
  have hp : ∀ i : ℕ, A.valuation (z ^ i - 1) < 1 := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [show z ^ (i + 1) - 1 = (z ^ i - 1) * z + (z - 1) by ring]
      refine Valuation.map_add_lt _ ?_ h1
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' hz1) ih
  have hs : ∑ i ∈ Finset.range m, z ^ i = 0 := by
    have := mul_geom_sum z m
    rw [hz, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)
  have hm : A.valuation (m : Ω) < 1 := by
    have h2 : A.valuation (∑ i ∈ Finset.range m, (z ^ i - 1)) < 1 :=
      Valuation.map_sum_lt _ one_ne_zero fun i _ => hp i
    rw [Finset.sum_sub_distrib, hs] at h2
    simpa using h2
  have hb : (1 : Ω) = (m : Ω) * ((Nat.gcdA m l : ℤ) : Ω) + (l : Ω) * ((Nat.gcdB m l : ℤ) : Ω) := by
    have h3 := Nat.gcd_eq_gcd_ab m l
    rw [hc.gcd_eq_one] at h3
    exact_mod_cast congrArg (Int.cast : ℤ → Ω) h3
  have h4 : A.valuation ((m : Ω) * ((Nat.gcdA m l : ℤ) : Ω) + (l : Ω) * ((Nat.gcdB m l : ℤ) : Ω)) < 1 := by
    refine Valuation.map_add_lt _ ?_ ?_ <;> rw [map_mul]
    · exact lt_of_le_of_lt (mul_le_of_le_one_right' (hint _)) hm
    · exact lt_of_le_of_lt (mul_le_of_le_one_right' (hint _)) hA
  rw [← hb, map_one] at h4
  exact lt_irrefl _ h4

private theorem tame_fix {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) {l m : ℕ}
    (hA : A.valuation (l : Ω) < 1) (hm : m ≠ 0) (hc : Nat.Coprime m l) (σ : G ℚ Ω) (hσ : σ ∈ Ine (F := ℚ) A)
    (z : Ω) (hz : z ^ m = 1) : σ z = z := by
  have hv : A.valuation z = 1 := by
    have := congrArg A.valuation hz
    rw [map_pow, map_one] at this
    exact (pow_eq_one_iff_of_nonneg zero_le hm).mp this
  have hz0 : z ≠ 0 := by rintro rfl; simp at hv
  have h3 : A.valuation (σ z - z) < 1 := hσ.2 z hv.le
  have h4 : σ z / z = 1 := eq_one_of_cong A hA hc
    (by rw [div_pow, ← map_pow, hz, map_one, div_one]) (by
      rw [show σ z / z - 1 = (σ z - z) / z by field_simp, map_div₀, hv, div_one]
      exact h3)
  exact (div_eq_one_iff_eq hz0).mp h4

private theorem loc_fix {R : Ranks} (H : Host R) {Ω : Type} [Field Ω] [Algebra H.E Ω] [Algebra ℚ Ω]
    [IsAlgClosed Ω] (A : ValuationSubring Ω) {l : ℕ} (hl : l.Prime) (hA : A.valuation (l : Ω) < 1)
    (σ : G ℚ Ω) (hσ : σ ∈ Ine (F := ℚ) A)
    (hroot : ∀ t : Ω, t ^ l ^ H.condN.factorization l = 1 → σ t = t) (x : H.E) :
    σ (algebraMap H.E Ω x) = algebraMap H.E Ω x := by
  have hN : H.condN ≠ 0 := H.condN_ne_zero
  refine H.image_mem_of_roots (algebraMap H.E Ω) (RingHom.eqLocusField (σ : Ω →+* Ω) (RingHom.id Ω))
    (fun y hy => ?_) x
  show σ y = y
  have hy0 : y ≠ 0 := by rintro rfl; simp [hN] at hy
  have hmul := Nat.ordProj_mul_ordCompl_eq_self H.condN l
  have hco : Nat.Coprime l (ordCompl[l] H.condN) := Nat.coprime_ordCompl hl hN
  have h1 := hroot (y ^ ordCompl[l] H.condN) (by rw [← pow_mul, mul_comm, hmul, hy])
  have h2 := tame_fix A hA (Nat.ordCompl_pos l hN).ne' hco.symm σ hσ (y ^ ordProj[l] H.condN)
    (by rw [← pow_mul, hmul, hy])
  rw [map_pow] at h1 h2
  have h3 : (σ y / y) ^ Nat.gcd (ordProj[l] H.condN) (ordCompl[l] H.condN) = 1 :=
    pow_gcd_eq_one.2 ⟨by rw [div_pow, h2, div_self (pow_ne_zero _ hy0)],
      by rw [div_pow, h1, div_self (pow_ne_zero _ hy0)]⟩
  rw [(Nat.Coprime.pow_left _ hco).gcd_eq_one, pow_one] at h3
  exact (div_eq_one_iff_eq hy0).mp h3

theorem main : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc) , ∃ w ∈ placesOver H.E (N.l i), ∀ u : ℤ_[N.l i], ∃ g ∈ Ine (F := H.E) (N.plOm.1 w), ((cycZ (F := H.E) (Ω := N.Om) (N.l i) g : ℤ_[N.l i]ˣ) : ℤ_[N.l i]) = 1 + (N.l i : ℤ_[N.l i]) ^ N.s0 i * u := by
  intro R H what₂ N i
  obtain ⟨w, hw⟩ := exists_place H.E (N.l i)
  refine ⟨w, hw, fun u => ?_⟩
  have : CharZero N.Om := charZero_of_injective_algebraMap (algebraMap H.E N.Om).injective
  have : IsAlgClosed N.Om := IsAlgClosure.isAlgClosed H.E
  have : IsScalarTower ℚ H.E N.Om := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  have : IsAlgClosure ℚ N.Om := IsAlgClosure.ofAlgebraic ℚ H.E N.Om
  have hA : (N.plOm.1 w).valuation (N.l i : N.Om) < 1 := by
    have := (N.plOm.2 w (N.l i : 𝓞 H.E)).2 hw
    simpa using this
  have hs : 1 ≤ N.s0 i := UpperTheory.KStar.S0.one_le_localLevel N i
  have hunit : IsUnit (1 + (N.l i : ℤ_[N.l i]) ^ N.s0 i * u) := by
    have hm : -((N.l i : ℤ_[N.l i]) ^ N.s0 i * u) ∈ IsLocalRing.maximalIdeal ℤ_[N.l i] := by
      rw [PadicInt.maximalIdeal_eq_span_p, neg_mem_iff, Ideal.mem_span_singleton]
      exact Dvd.dvd.mul_right (dvd_pow_self _ (by omega)) _
    have := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ hm
    simpa using this
  obtain ⟨σ, hσ, hv⟩ := GlobalTheory.T.cyclotomicChar_inertia_surjective N.Om (N.l i) (N.plOm.1 w) hA hunit.unit
  have hv' : ((cycZ (F := ℚ) (Ω := N.Om) (N.l i) σ : ℤ_[N.l i]ˣ) : ℤ_[N.l i]) =
      1 + (N.l i : ℤ_[N.l i]) ^ N.s0 i * u := by rw [hv]; rfl
  obtain ⟨k, hk⟩ := pow_dvd_pow (N.l i) (UpperTheory.KStar.S0.factorization_conductor_le_localLevel N i)
  obtain ⟨g, hg, hc⟩ := transfer (E := H.E) (N.plOm.1 w) (N.l i) σ hσ
    (loc_fix H _ (N.lPrime i).out hA σ hσ fun t ht =>
      root_fix (N.l i) (N.s0 i) σ u hv' t (by rw [hk, pow_mul, ht, one_pow]))
  exact ⟨g, hg, by rw [hc, hv']⟩

end GlobalTheory.TameFixedLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TieConclusion
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
open scoped ENNReal

namespace GlobalTheory.Proof.QuotientLengthInfimum

open GlobalTheory.IndefiniteRowSideFullHecke

theorem length_quot_eq_iInf {O : Type} [CommRing O] [IsPrincipalIdealRing O] (I : Ideal O) :
    Module.length O (O ⧸ I) = ⨅ x ∈ I, Module.length O (O ⧸ Ideal.span {x}) := by
  apply le_antisymm
  · refine le_iInf₂ fun x hx => ?_
    have hle : Ideal.span {x} ≤ I := (Ideal.span_singleton_le_iff_mem _).2 hx
    exact Module.length_le_of_surjective (Submodule.factor hle) (Submodule.factor_surjective hle)
  · have hg : Ideal.span {Submodule.IsPrincipal.generator I} = I :=
      Ideal.span_singleton_generator I
    refine iInf₂_le_of_le (Submodule.IsPrincipal.generator I)
      (Submodule.IsPrincipal.generator_mem I) ?_
    rw [hg]

theorem mem_ccAt {O X : Type} [CommRing O] (T : Subalgebra O (X → O)) (Z : Finset X) (π : X) (y : O) :
    y ∈ ccAt T Z π ↔ ∃ f ∈ ccIdeal T Z, ((f : T) : X → O) π = y := by
  have hs : Function.Surjective ((Pi.evalRingHom (fun _ : X => O) π).comp T.val.toRingHom) :=
    fun a => ⟨algebraMap O T a, by simp⟩
  unfold ccAt
  rw [Ideal.mem_map_iff_of_surjective _ hs]
  rfl

theorem div_le_iff_lengths (e c s h v q : ℕ∞) (he0 : e ≠ 0) (he : e ≠ ⊤) :
    ((c : ℝ≥0∞) / (e : ℝ≥0∞) ≤ (s : ℝ≥0∞) / (e : ℝ≥0∞) + (h : ℝ≥0∞) + (v : ℝ≥0∞) + (q : ℝ≥0∞) / (e : ℝ≥0∞)) ↔
      c ≤ s + e * h + e * v + q := by
  have he0' : (e : ℝ≥0∞) ≠ 0 := by simpa using he0
  have he' : (e : ℝ≥0∞) ≠ ⊤ := by simpa using he
  rw [← ENat.toENNReal_le, ← ENNReal.mul_le_mul_iff_right he0' he']
  simp only [mul_add, ENNReal.mul_div_cancel he0' he', ENat.toENNReal_add, ENat.toENNReal_mul]

theorem toENNReal_sum {ι : Type} (s : Finset ι) (f : ι → ℕ∞) :
    ((∑ a ∈ s, f a : ℕ∞) : ℝ≥0∞) = ∑ a ∈ s, (f a : ℝ≥0∞) :=
  map_sum ENat.toENNRealRingHom f s

section Hyp

end Hyp

section Terms

variable (D : D7) (i : D.nd.Loc)

theorem ramLen_ne : SelmerSumLargePrime.ramLen D i ≠ 0 ∧ SelmerSumLargePrime.ramLen D i ≠ ⊤ := by
  have h := BaseSizes.vO_l D i
  unfold BaseSizes.vO BaseSizes.nlen at h
  change ((SelmerSumLargePrime.ramLen D i : ℕ∞) : ℝ≥0∞) / ((SelmerSumLargePrime.ramLen D i : ℕ∞) : ℝ≥0∞) = 1 at h
  constructor
  · intro h0; rw [h0] at h; simp at h
  · intro h0; rw [h0] at h; simp at h

theorem vCC_eq (π : D.nd.X i) :
    BaseSizes.vCC D i π = (SelmerSumLargePrime.ccLen D i π : ℝ≥0∞) / (SelmerSumLargePrime.ramLen D i : ℝ≥0∞) := by
  unfold BaseSizes.vCC BaseSizes.vO BaseSizes.nlen SelmerSumLargePrime.ccLen
  change ⨅ f ∈ D.nd.cc i, _ / (SelmerSumLargePrime.ramLen D i : ℝ≥0∞) = _
  apply le_antisymm
  · set I := ccAt (D.nd.T i) (D.nd.Z i) π with hI
    have hg : Ideal.span {Submodule.IsPrincipal.generator I} = I := Ideal.span_singleton_generator I
    obtain ⟨f, hf, hfx⟩ := (mem_ccAt _ _ π _).1 (Submodule.IsPrincipal.generator_mem I)
    refine iInf₂_le_of_le f hf ?_
    rw [hfx, hg]
  · refine le_iInf₂ fun f hf => ?_
    refine ENNReal.div_le_div_right ?_ _
    rw [ENat.toENNReal_le, length_quot_eq_iInf]
    exact iInf₂_le _ ((mem_ccAt _ _ π _).2 ⟨f, hf, rfl⟩)

theorem sPi_eq (π : D.nd.X i) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)) :
    BaseSizes.sPi D i π ρ = (SelmerSumLargePrime.selLen D i ρ π : ℝ≥0∞) / (SelmerSumLargePrime.ramLen D i : ℝ≥0∞) := rfl

theorem shaSum_eq : BaseSizes.shaSum D i = (SelmerSumLargePrime.shaSum D i : ℝ≥0∞) := by
  unfold BaseSizes.shaSum SelmerSumLargePrime.shaSum
  rw [toENNReal_sum]

theorem vClass_eq :
    BaseSizes.vClass D i = (((padicValNat (D.nd.l i) (hE D.host) : ℕ) : ℕ∞) : ℝ≥0∞) := by
  unfold BaseSizes.vClass hE
  simp

theorem zetaP_eq (P : HeightOneSpectrum (𝓞 D.host.E)) : BaseSizes.zetaP D i P = SelmerSumLargePrime.zetaP D i P := rfl

theorem epsQ_eq : BaseSizes.epsQ D i = (SelmerSumLargePrime.twistLen D i : ℝ≥0∞) / (SelmerSumLargePrime.ramLen D i : ℝ≥0∞) := by
  unfold BaseSizes.epsQ SelmerSumLargePrime.twistLen BaseSizes.vO BaseSizes.nlen
  rw [ENat.toENNReal_mul, toENNReal_sum, mul_div_assoc, div_eq_mul_inv (∑ _ ∈ _, _), Finset.sum_mul]
  rfl

theorem conclusion_iff (π : D.nd.X i) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)) :
    (BaseSizes.vCC D i π ≤ BaseSizes.sPi D i π ρ + BaseSizes.shaSum D i + BaseSizes.vClass D i + BaseSizes.epsQ D i) ↔
      SelmerSumLargePrime.ccLen D i π ≤ SelmerSumLargePrime.selLen D i ρ π + SelmerSumLargePrime.ramLen D i * SelmerSumLargePrime.shaSum D i +
        SelmerSumLargePrime.ramLen D i * (padicValNat (D.nd.l i) (hE D.host) : ℕ∞) + SelmerSumLargePrime.twistLen D i := by
  rw [vCC_eq, sPi_eq, shaSum_eq, vClass_eq, epsQ_eq]
  exact div_le_iff_lengths _ _ _ _ _ _ (ramLen_ne D i).1 (ramLen_ne D i).2

end Terms

def LengthBoundLoc (D : D7) (L : SizeData₂ D) (i : D.nd.Loc) : Prop :=
  LevelStarExponents.lStar L < (D.nd.l i : ℝ) → D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 →
    D.nd.l i ∉ SelmerSumLargePrime.excPrimes L →
    HG D.nd D.naut i →
    ∀ r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)), GoodR D.nd i r →
    ∀ π ∈ D.nd.Z i, ∀ ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i), SelmerSumLargePrime.IsBlockSplit D i (r π) ρ →
      SelmerSumLargePrime.ccLen D i π ≤ SelmerSumLargePrime.selLen D i ρ π + SelmerSumLargePrime.ramLen D i * SelmerSumLargePrime.shaSum D i +
        SelmerSumLargePrime.ramLen D i * (padicValNat (D.nd.l i) (hE D.host) : ℕ∞) + SelmerSumLargePrime.twistLen D i

def TiedF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (a : Fm.Ix x) (i : (Fm.D x a).nd.Loc), BaseSizes.WeightTie (Fm.D x a) i

end GlobalTheory.Proof.QuotientLengthInfimum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiedTateFilQuot
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.TateFilQuotTied

theorem tied_tate_fil_quot : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P),
    LocTied l P AI → ∀ K : FinExt l, Formalism.MainNotions.LocalSituation.TateFilteredInvariants (P.PD K) := by
  intro l _ P AI TT K LL _ _ _ O _ _ hO A hA a b z hz hg
  haveI := hO.2.1
  exact GlobalTheory.TateFilQuot.tied_invariant_mod l P AI TT K LL A.V A.ρ hA a b z hz hg

end GlobalTheory.TateFilQuotTied
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TrivialLineAdmissibleCocyclesNotIndependent
section
noncomputable section
namespace GlobalTheory.TopSteps.TrivLine
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries

theorem exists_diff_of_sum_eq_zero {k : Type} [Field k] {n : ℕ} [NeZero n] (c : ZMod n → k) (hc : ∑ i, c i = 0) :
    ∃ d : ZMod n → k, ∀ i, c i = d (i - 1) - d i := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  refine ⟨fun i => -∑ j ∈ Finset.range (i.val + 1), c (j : ZMod (n + 1)), fun i => ?_⟩
  have hall : ∑ j ∈ Finset.range (n + 1), c (j : ZMod (n + 1)) = 0 := by
    rw [← hc, Finset.sum_range]
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 1
    exact ZMod.natCast_zmod_val (n := n + 1) x
  by_cases hi : i = 0
  · subst hi
    have h1 : ((0 : ZMod (n + 1)) - 1).val = n := by
      rw [zero_sub]; exact ZMod.val_neg_one n
    simp only [h1, ZMod.val_zero, hall]
    simp
  · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (fun h => hi ((ZMod.val_eq_zero i).1 h))
    have hlt := ZMod.val_lt i
    have hi' : i = ((j + 1 : ℕ) : ZMod (n + 1)) := by
      rw [show j + 1 = i.val from hj.symm, ZMod.natCast_zmod_val]
    have h1 : (i - 1).val = j := by
      have : i - 1 = (j : ZMod (n + 1)) := by rw [hi']; push_cast; ring
      rw [this, ZMod.val_natCast_of_lt (by omega)]
    simp only [h1, hj, Nat.succ_eq_add_one]
    rw [Finset.sum_range_succ _ (j + 1), ← hi']
    ring

variable {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l}

theorem mem_of_inZZ (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (h1 : Dt.T1 l) (h2 : Dt.T2 l)
    (h3 : Dt.T3 l) (b g : ZMod n → Vc k 1) (hZ : InZZ (F.D (chr 1)) Dt (M.Nχ 0) b g) (i : ZMod n) :
    b i ∈ M.Nχ 0 i := by
  have hω : M.ω ^ (-(0 : ℤ)) = 1 := by simp
  have ht : (0 : ℤ) < Dt.t := by exact_mod_cast Dt.one_le_letterBlockLength
  have hlat := M.χ_lat 0 (by norm_num) ht i
  rw [hω] at hlat
  obtain ⟨hL, hC, hP, hS⟩ := hlat
  rw [sh_zero_eq] at hP
  obtain ⟨z0, z1, zG, zB⟩ := hZ i
  have hv := vv_ne_zero k
  have hφ : (F.D (chr 1)).φ i (g (i - 1)) ∈ sh 1 (M.Nχ 0 i) := by
    obtain ⟨y, hy, e⟩ := mem_sh_iff_exists.1 (hZ (i - 1)).2.1
    obtain ⟨u, hu⟩ := R.φ_v
    obtain ⟨l', hl'⟩ := Nat.exists_eq_add_of_le (Fact.out : l.Prime).one_le
    have hy' : (F.D (chr 1)).φ i y ∈ M.Nχ 0 i := by
      rw [← hP]; exact Submodule.subset_span ⟨y, hy, rfl⟩
    refine mem_sh_iff_exists.2 ⟨((u : k⟦X⟧) * PowerSeries.X ^ l') • (F.D (chr 1)).φ i y,
      Submodule.smul_mem _ _ hy', ?_⟩
    rw [← e, (F.D (chr 1)).φ_semi i, zpow_one, hu, ← algebraMap_smul k⸨X⸩ ((u : k⟦X⟧) * PowerSeries.X ^ l'),
      smul_smul]
    congr 1
    change _ * (((u : k⟦X⟧) * PowerSeries.X ^ l' : k⟦X⟧) : k⸨X⸩) = _
    rw [map_mul, map_pow, ← vv_eq_coe_X, hl']
    ring
  have hnab : nab ((F.D (chr 1)).γ i) (b i) ∈ M.Nχ 0 i := by
    have := mem_sh_iff_smul_mem.1 (Submodule.sub_mem _ hφ z1)
    rw [← z0, zpow_neg_one] at this
    exact this
  have key : ∀ J : ℤ, 0 ≤ J → J ≤ Dt.η i → b i ∈ sh (-J) (M.Nχ 0 i) → b i ∈ M.Nχ 0 i := by
    intro J hJ hJ' hb
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hJ
    have hl := h1 i
    have := (GlobalTheory.PhiGam.Window.nab_bijective_window R _ ((F.D (chr 1)).γ_semi i) _ hL hC (-(m : ℤ)) m (by
      intro j hj
      rw [hS, resCount, Multiset.card_eq_zero]
      refine (@Multiset.filter_eq_nil _ _ (_) _).2 ?_
      intro a ha e
      rw [Multiset.mem_singleton] at ha
      subst ha
      have e' : ((m - j : ℕ) : k) = 0 := by
        rw [Nat.cast_sub hj.le]
        push_cast at e
        linear_combination e
      have := Nat.le_of_dvd (by omega) ((CharP.cast_eq_zero_iff k l _).1 e')
      omega)).1 (b i) hb (by rw [neg_add_cancel, sh_zero_eq]; exact hnab)
    rwa [neg_add_cancel, sh_zero_eq] at this
  obtain ⟨-, -, wG, wB⟩ := GlobalTheory.WindowArith.windows (k := k) Dt h1 h2 h3 i
  cases hty : Dt.ty i with
  | G =>
    obtain ⟨-, -, a1, a2⟩ := wG hty
    exact key _ (by omega) (by omega) (zG hty)
  | Bd =>
    obtain ⟨-, -, a1, a2⟩ := wB hty
    have := (zB hty).1
    rw [hP] at this
    exact key _ (by omega) a2 this

theorem exists_const_pair (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (h1 : Dt.T1 l)
    (h2 : Dt.T2 l) (h3 : Dt.T3 l) (z : G → Fin 1 → k) (hz : z ∈ M.twistedModelAdmissibleCocycles (chr 1)) :
    ∃ (b g m : ZMod n → Vc k 1) (c : ZMod n → k), Repr F (chr 1) z b g ∧
      ∀ i, b i = (F.D (chr 1)).φ i (m (i - 1)) - m i + c i • F.unit i ∧ g i = (F.D (chr 1)).γ i (m i) - m i := by
  obtain ⟨N, b, g, hN, hR, hZ⟩ := GlobalTheory.T.exists_phiGammaModel_extension_cocycle_pair F M h1 h2 h3 (chr 1) z hz
  have hω : M.ω ^ (-(0 : ℤ)) = 1 := by simp
  have ht : (0 : ℤ) < Dt.t := by exact_mod_cast Dt.one_le_letterBlockLength
  have hCH := GlobalTheory.T.twistedPhiGammaModel_character_eq_standard F M h1 h2 h3 0 le_rfl ht N
  rw [hω] at hCH
  obtain rfl := hCH hN
  have hb : ∀ i, ∃ β : k⟦X⟧, b i = (β : k⸨X⸩) • F.unit i := fun i => by
    have := mem_of_inZZ F M h1 h2 h3 b g hZ i
    rw [M.χ_zero, Submodule.mem_span_singleton] at this
    obtain ⟨β, e⟩ := this
    exact ⟨β, by rw [← e, ← algebraMap_smul k⸨X⸩ β]; rfl⟩
  have hg : ∀ i, ∃ β : k⟦X⟧, PowerSeries.constantCoeff β = 0 ∧ g i = (β : k⸨X⸩) • F.unit i := fun i => by
    obtain ⟨y, hy, e⟩ := mem_sh_iff_exists.1 (hZ i).2.1
    rw [M.χ_zero, Submodule.mem_span_singleton] at hy
    obtain ⟨β, rfl⟩ := hy
    refine ⟨PowerSeries.X * β, by simp, ?_⟩
    rw [← e, ← algebraMap_smul k⸨X⸩ β, zpow_one, smul_smul, map_mul, ← vv_eq_coe_X]; rfl
  choose β hβ using hb
  choose δ hδ0 hδ using hg
  have eφ : ∀ i (a : k⸨X⸩), (F.D (chr 1)).φ i (a • F.unit (i - 1)) = R.φ a • F.unit i := fun i a => by
    rw [(F.D (chr 1)).φ_semi i, F.unit_φ]
  have eγ : ∀ i (a : k⸨X⸩), (F.D (chr 1)).γ i (a • F.unit i) = R.γ a • F.unit i := fun i a => by
    rw [(F.D (chr 1)).γ_semi i, F.unit_γ]
  obtain ⟨m, c, hm⟩ := GlobalTheory.PhiGam.TrivCocycle.main R β δ hδ0 (fun i => by
    have e := (hZ i).1
    rw [hβ i, hδ i, hδ (i - 1), eφ, eγ, ← sub_smul, ← sub_smul] at e
    exact smul_left_injective _ (F.unit_ne i) e)
  refine ⟨b, g, fun i => (m i : k⸨X⸩) • F.unit i, c, hR, fun i => ⟨?_, ?_⟩⟩
  · rw [hβ, (hm i).1, eφ, add_smul, sub_smul]
    congr 1
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, const_smul_eq]
  · rw [hδ, (hm i).2, eγ, sub_smul]

theorem main : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt), Dt.T1 l → Dt.T2 l → Dt.T3 l → ∀ z : Fin 2 → G → Fin 1 → k, (∀ a, z a ∈ M.twistedModelAdmissibleCocycles (chr 1)) → ¬ LinearIndependent k (fun a => (cob (chr (1 : G →* kˣ))).mkQ (z a)) := by
  intro k G _ _ l n _ _ _ R F r Dt M h1 h2 h3 z hz hli
  choose b g m c hR hm using fun a => exists_const_pair F M h1 h2 h3 (z a) (hz a)
  have key : ∀ (p q : Fin 2) (x : k), x * ∑ i, c p i + ∑ i, c q i = 0 →
      x • (cob (chr (1 : G →* kˣ))).mkQ (z p) + (cob (chr (1 : G →* kˣ))).mkQ (z q) = 0 := by
    intro p q x hx
    obtain ⟨d, hd⟩ := exists_diff_of_sum_eq_zero (fun i => x * c p i + c q i)
      (by rw [Finset.sum_add_distrib, ← Finset.mul_sum, hx])
    have hr := GlobalTheory.T.repr_smul_add F (chr 1) x (z p) (z q) _ _ _ _ (hR p) (hR q)
    have h0 := GlobalTheory.T.mem_coboundaries_of_herrPair_coboundary F (chr 1) _ _ _ hr (by
      refine ⟨fun i => x • m p i + m q i + d i • F.unit i, Prod.ext (funext fun i => ?_) (funext fun i => ?_)⟩
      · change (F.D (chr 1)).φ i (x • m p (i - 1) + m q (i - 1) + d (i - 1) • F.unit (i - 1)) -
          (x • m p i + m q i + d i • F.unit i) = x • b p i + b q i
        have e : d (i - 1) = x * c p i + c q i + d i := by rw [hd i]; ring
        rw [map_add, map_add, map_smul, map_smul, F.unit_φ, (hm p i).1, (hm q i).1, e]
        module
      · change (F.D (chr 1)).γ i (x • m p i + m q i + d i • F.unit i) -
          (x • m p i + m q i + d i • F.unit i) = x • g p i + g q i
        rw [map_add, map_add, map_smul, map_smul, F.unit_γ, (hm p i).2, (hm q i).2]
        module)
    rw [← map_smul, ← map_add]
    exact (Submodule.Quotient.mk_eq_zero _).2 h0
  rw [Fintype.linearIndependent_iff] at hli
  by_cases hs : ∑ i, c 0 i = 0
  · have := hli ![1, 0] (by
      rw [Fin.sum_univ_two, add_comm]
      have := key 1 0 0 (by rw [hs]; ring)
      simpa using this) 0
    simp at this
  · have := hli ![-(∑ i, c 1 i) / ∑ i, c 0 i, 1] (by
      rw [Fin.sum_univ_two]
      have := key 0 1 (-(∑ i, c 1 i) / ∑ i, c 0 i) (by field_simp; ring)
      simpa using this) 1
    simp at this

end GlobalTheory.TopSteps.TrivLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedRepresentationKillsSmallSubgroupStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_representation_kills_small_subgroup : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) (s : X.Sig i), 0 < nu X i → ∀ (M : ℕ) (L : Subgroup (GE N)) (z : GE N), nu X i + 1 ≤ M → Small2 i s M L z → ∀ (A : Type) [CommRing A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)), Kills i A → IsDual i s ρ → ∀ (Y : Type) [AddCommGroup Y] [Module A Y], ∀ g ∈ L, (∀ m, repOn (Tgl i s) κ Y g m = ((κ g : Aˣ) : A) • m) ∧ (∀ m, repOn ρ κ Y g m = ((κ g : Aˣ) : A) • m) ∧ cycMod D.host.E N.Om (X.l i) (nu X i + 1) g = 1 := by
  first | exact @GlobalTheory.NewPrime.SmallActs.small_acts | exact GlobalTheory.NewPrime.SmallActs.small_acts | (intros; apply GlobalTheory.NewPrime.SmallActs.small_acts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypePrimeCompletionDegreeOneCountProof
section
noncomputable section

namespace GlobalTheory.Pass

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module

theorem stepDeg_main : StepDeg := fun D _ => GlobalTheory.TypeDegOne.degree_one D

end GlobalTheory.Pass
end
end

