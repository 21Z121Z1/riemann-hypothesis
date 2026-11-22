import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0252
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0026
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankWeightComponentEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0155
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1062
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1086
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1084
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1031
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1076
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1090
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionFieldCoordinatesDlog
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.LogDR GlobalTheory.LogPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EtCoordBasis

open KaehlerDifferential

theorem kaehler_map_bijective (p : ℕ) (L : Type) [CommRing L] [Algebra (ZMod p) L] :
    Function.Bijective (KaehlerDifferential.map ℤ (ZMod p) L L) := by
  refine ⟨?_, KaehlerDifferential.map_surjective ℤ (ZMod p) L⟩
  have hsurj : Function.Surjective (algebraMap ℤ (ZMod p)) := by
    intro x
    obtain ⟨m, rfl⟩ := ZMod.intCast_surjective x
    exact ⟨m, by simp⟩
  have hs : Subsingleton Ω[ZMod p⁄ℤ] := KaehlerDifferential.subsingleton_of_surjective ℤ (ZMod p) hsurj
  have hex := KaehlerDifferential.exact_mapBaseChange_map ℤ (ZMod p) L
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := (hex x).1 hx
  clear hx
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [Subsingleton.elim b 0]
  | add y z hy hz => rw [map_add, hy, hz, add_zero]

theorem etale_coords_basis : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [IsDomain A] [Algebra (ZMod p) A] {n : ℕ} (t : Fin n → A), (MvPolynomial.aeval (R := ZMod p) t).toRingHom.Etale → ∀ (L : Type) [Field L] [Algebra A L] [IsFractionRing A L] (ht : ∀ j, algebraMap A L (t j) ≠ 0), IsCoord (fun j => Units.mk0 (algebraMap A L (t j)) (ht j)) ∧ ∀ f : A, ∃ c : Fin n → A, KaehlerDifferential.D ℤ L (algebraMap A L f) = ∑ j, algebraMap A L (c j) • KaehlerDifferential.D ℤ L (algebraMap A L (t j)) := by
  intro p _ A _ _ _ n t het L _ _ _ ht
  classical
  let P := MvPolynomial (Fin n) (ZMod p)
  letI : Algebra P A := (MvPolynomial.aeval t).toRingHom.toAlgebra
  haveI : IsScalarTower (ZMod p) P A :=
    .of_algebraMap_eq fun r => ((MvPolynomial.aeval t).commutes r).symm
  haveI : Algebra.Etale P A := het
  letI : Algebra (ZMod p) L := ((algebraMap A L).comp (algebraMap (ZMod p) A)).toAlgebra
  haveI : IsScalarTower (ZMod p) A L := .of_algebraMap_eq fun _ => rfl
  haveI : Algebra.FormallyEtale A L := .of_isLocalization (nonZeroDivisors A)
  let bA : Module.Basis (Fin n) A Ω[A⁄ZMod p] :=
    ((mvPolynomialBasis (ZMod p) (Fin n)).baseChange A).map
      (tensorKaehlerEquivOfFormallyEtale (ZMod p) P A)
  have hbA : ∀ j, bA j = D (ZMod p) A (t j) := by
    intro j
    simp only [bA, Module.Basis.map_apply, Module.Basis.baseChange_apply,
      tensorKaehlerEquivOfFormallyEtale_apply, mapBaseChange_tmul, one_smul, mvPolynomialBasis_apply, map_D]
    have h : algebraMap P A (MvPolynomial.X j) = t j := by
      change MvPolynomial.aeval t (MvPolynomial.X j) = t j
      exact MvPolynomial.aeval_X t j
    rw [← h, ← map_D (ZMod p) (ZMod p) P A]
    exact (mapBaseChange_tmul (ZMod p) P A 1 _).trans (one_smul _ _)
  let bL : Module.Basis (Fin n) L Ω[L⁄ZMod p] :=
    (bA.baseChange L).map (tensorKaehlerEquivOfFormallyEtale (ZMod p) A L)
  have hbL : ∀ j, bL j = D (ZMod p) L (algebraMap A L (t j)) := by
    intro j
    simp only [bL, Module.Basis.map_apply, Module.Basis.baseChange_apply,
      tensorKaehlerEquivOfFormallyEtale_apply, mapBaseChange_tmul, one_smul, hbA, map_D]
  let e : Ω[L⁄ℤ] ≃ₗ[L] Ω[L⁄ZMod p] :=
    LinearEquiv.ofBijective (KaehlerDifferential.map ℤ (ZMod p) L L) (kaehler_map_bijective p L)
  have he : ∀ x : L, e.symm (D (ZMod p) L x) = D ℤ L x := by
    intro x
    rw [LinearEquiv.symm_apply_eq]
    exact (KaehlerDifferential.map_D ℤ (ZMod p) L L x).symm
  let b : Module.Basis (Fin n) L Ω[L⁄ℤ] := bL.map e.symm
  have hb : ∀ j, b j = D ℤ L (algebraMap A L (t j)) := by
    intro j
    simp only [b, Module.Basis.map_apply, hbL, he]
  have hfun : (fun i => dK ((Units.mk0 (algebraMap A L (t i)) (ht i) : Lˣ) : L)) = ⇑b := by
    funext i
    simp [hb, dK]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [hfun]; exact b.linearIndependent
  · rw [hfun]; exact b.span_eq
  · intro f
    refine ⟨bA.repr (D (ZMod p) A f), ?_⟩
    have h1 := bA.sum_repr (D (ZMod p) A f)
    rw [← he, ← map_D (ZMod p) (ZMod p) A L]
    conv_lhs => rw [← h1]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LinearMap.map_smul, hbA, map_D, ← algebraMap_smul L (bA.repr (D (ZMod p) A f) j), LinearEquiv.map_smul, he]

end GlobalTheory.EtCoordBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusTwistDivisorRecursion
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.LogDR GlobalTheory.LogPair

theorem GlobalTheory.nat_mul_div_bounds_rounded_multiples (p r m : ℕ) (hp : 0 < p) (hr : 0 < r) :
    p * (m / r) ≤ p * m / r ∧ p * m / r + 1 ≤ p * (m / r) + p := by
  have h1 : p * m = p * (m % r) + r * (p * (m / r)) := by
    conv_lhs => rw [← Nat.mod_add_div m r]
    ring
  have h2 : p * m / r = p * (m % r) / r + p * (m / r) := by
    rw [h1, Nat.add_mul_div_left _ _ hr]
  have h4 : p * (m % r) < p * r := Nat.mul_lt_mul_of_pos_left (Nat.mod_lt m hr) hp
  have h3 : p * (m % r) / r < p := (Nat.div_lt_iff_lt_mul hr).2 h4
  rw [h2]
  generalize p * (m % r) / r = q at h3 ⊢
  generalize p * (m / r) = s
  constructor <;> omega

theorem GlobalTheory.rounded_multiples_step : ∀ (X : Scheme.{0}) [IsIntegral X] (p : ℕ) {C : Type} [Fintype C] (E : C → CartierDiv X) (M Kc : CartierDiv X) (r : ℕ) (b : C → ℕ), 0 < p → 0 < r → ∀ e : ℕ, ∃ ρ : C → ℕ, (∀ c, ρ c < p) ∧ (fun e => p ^ e • (M - Kc) - ∑ c, (p ^ e * b c / r) • E c - ∑ c, E c) (e + 1) = p • (fun e => p ^ e • (M - Kc) - ∑ c, (p ^ e * b c / r) • E c - ∑ c, E c) e + ∑ c, ρ c • E c := by
  intro X _ p C _ E M Kc r b hp hr e
  have hm : ∀ c, p ^ (e + 1) * b c = p * (p ^ e * b c) := fun c => by ring
  refine ⟨fun c => p * (p ^ e * b c / r) + p - 1 - p ^ (e + 1) * b c / r, ?_, ?_⟩
  · intro c
    have := GlobalTheory.nat_mul_div_bounds_rounded_multiples p r (p ^ e * b c) hp hr
    show p * (p ^ e * b c / r) + p - 1 - p ^ (e + 1) * b c / r < p
    rw [hm c]
    omega
  · have hc : ∀ c, p • ((p ^ e * b c / r) • E c + E c)
        = (p ^ (e + 1) * b c / r) • E c + E c
          + (p * (p ^ e * b c / r) + p - 1 - p ^ (e + 1) * b c / r) • E c := by
      intro c
      have := GlobalTheory.nat_mul_div_bounds_rounded_multiples p r (p ^ e * b c) hp hr
      have hk : p * (p ^ e * b c / r) + p
          = p ^ (e + 1) * b c / r + 1 + (p * (p ^ e * b c / r) + p - 1 - p ^ (e + 1) * b c / r) := by
        rw [hm c]; omega
      rw [smul_add, ← mul_smul, ← add_smul]
      conv_lhs => rw [hk]
      rw [add_smul, add_smul, one_smul]
    have hs : p • (∑ c, (p ^ e * b c / r) • E c + ∑ c, E c)
        = ∑ c, (p ^ (e + 1) * b c / r) • E c + ∑ c, E c
          + ∑ c, (p * (p ^ e * b c / r) + p - 1 - p ^ (e + 1) * b c / r) • E c := by
      rw [← Finset.sum_add_distrib, Finset.smul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun c _ => hc c)
    have hs' : p • (p ^ e • (M - Kc) - ∑ c, (p ^ e * b c / r) • E c - ∑ c, E c)
        = p ^ (e + 1) • (M - Kc) - p • (∑ c, (p ^ e * b c / r) • E c + ∑ c, E c) := by
      rw [pow_succ', mul_smul, smul_sub, smul_sub, smul_add]; abel
    beta_reduce
    rw [hs', hs]
    abel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullAlgebraPartLeSplitHeckePart
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

namespace GlobalTheory.HeckeSplitPart

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem goodPl (R : RealDat D A Ks) (F : Face D A) (hL : R.toLevCh.Is A.μ0) (hF : R.IsFam)
    {SF : Finset (HeightOneSpectrum (𝓞 D.host.F))} (hSF : IsSF R SF) {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {N : ℕ} (hβ : IsSDFrame V β Λ N)
    (hN : N = 1 ∨ N = D.host.g 0 * D.host.g 1) :
    GlobalTheory.HeckeParts.GoodPl V β R.Pg (A.ok A.μ0) R.pl A.q SF := by
  obtain ⟨hQ, h2, h3, h4⟩ := GlobalTheory.GoodPrimes.good_primes R F hL
  intro P hP
  obtain ⟨hg, hc, hq⟩ := h4 hF _ P hP
  refine ⟨?_, (h3 SF hSF _).2 hg, ?_, fun L hLP hLQ e f hef => ?_⟩
  · rw [hq, Nat.cast_ne_zero]
    exact fun h => (R.pl P).ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  · rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq]
    exact fun h => hc (HeightOneSpectrum.ext h)
  · obtain ⟨c, hcB⟩ := hβ
    refine (GlobalTheory.LevSplit.lev_split V β Λ _ L hcB).2 (R.pl P) e f hef ?_ ?_
    · intro h
      rw [Nat.cast_pow] at h
      have h' := (R.pl P).isPrime.mem_of_pow_mem _ h
      rcases hN with rfl | rfl
      · exact (R.pl P).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using h'))
      · exact (h2 _ _ hg).1 h'
    · rw [hLP, hLQ]
      rintro PP (h | h)
      · exact hg PP (Or.inl h)
      · simp at h

theorem parts_in_hPart : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {s : ℕ}, A.fam.Ok s → Core R F → ∀ SF, IsSF R SF → ∀ (c : Pl D.host.E → List ℤ → ℂ) (Sg : Pl0 → ℂ[X]), ((∀ P ∈ A.ok A.μ0, Sg P = Formalism.L2.Col.heckePolyOf D.R.r (A.q P) fun k => c (R.pl P) (dualLab (splitLab D.R.r k))) → ∀ x ∈ EEc R SF c, R.HE.e x ∈ hPart (R.MY 0) (levG _ (R.βY 0) (R.dat0 R.triv)) (A.ok A.μ0) R.pl A.q Sg) ∧ ∀ i, (∀ P ∈ A.ok A.μ0, Sg P = Formalism.L2.Col.heckePolyOf D.R.r (A.q P) fun k => c (R.pl P) (splitLab D.R.r k)) → ∀ x ∈ Wcc R SF i c, (R.HW i _).e x ∈ hPart (R.MW i (sg0 D A)) (levG _ (R.βW i) (R.datWp i R.triv)) (A.ok A.μ0) R.pl A.q Sg := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F s _ hC SF hSF c Sg
  have hY := goodPl R F hC.lev hC.fam hSF (hC.lev.βY 0 (by have := D.R.two_le_m; omega)) (Or.inr rfl)
  have hW := fun i => goodPl R F hC.lev hC.fam hSF (hC.lev.βW i) (Or.inl rfl)
  refine ⟨fun hSg x hx => ?_, fun i hSg x hx => ?_⟩
  · exact GlobalTheory.HeckeParts.mem_hPart_of_partFull (V := Yc D 0) (β := R.βY 0) (r := D.R.r) (t := D.R.t) (hr := r_le_Y 0)
      (Pg := R.Pg) (χ := R.chi) (ξ := fun _ => 1) (c := fun P d => c P (dualLab d)) hY R.triv hx
      (fun P hP => by rw [hSg P hP, GlobalTheory.HeckeParts.rank_zeroth_component_eq])
  · exact GlobalTheory.HeckeParts.mem_hPart_of_partFull (V := Wc D i) (β := R.βW i) (r := D.R.r) (t := D.R.t) (hr := r_le_rank_Wc i)
      (Pg := R.Pg) (χ := fun _ _ => 1) (ξ := fun _ => 1) (c := c) (hW i) R.triv hx.2
      (fun P hP => by rw [hSg P hP, GlobalTheory.HeckeParts.rank_weight_component_eq])

end GlobalTheory.HeckeSplitPart

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalIdealFrobeniusProduct
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.AfPVecDen

theorem main : ∀ (p : ℕ) [Fact p.Prime] (V : Type) [AddCommGroup V] [Module ℚ V] {ι : Type} [Fintype ι]
    (b : Module.Basis ι ℚ V) (Ω : Set (AfP p ⊗[ℚ] V)),
    @IsCompact _ (moduleTopology (AfP p) (AfP p ⊗[ℚ] V)) Ω →
    ∃ M : ℕ, 0 < M ∧ ∀ c : V, (1 : AfP p) ⊗ₜ[ℚ] c ∈ Ω → ∀ i, ∃ (k : ℤ) (e : ℕ),
      b.repr c i * ((M : ℚ) * (p : ℚ) ^ e) = k := by
  intro p _ V _ _ ι _ b Ω hΩ
  letI : TopologicalSpace (AfP p ⊗[ℚ] V) := moduleTopology (AfP p) (AfP p ⊗[ℚ] V)
  haveI : IsModuleTopology (AfP p) (AfP p ⊗[ℚ] V) := ⟨rfl⟩
  let b' := b.baseChange (AfP p)
  have hcont : ∀ i, Continuous (b'.coord i) := fun i =>
    IsModuleTopology.continuous_of_linearMap (b'.coord i)
  have hcpt : ∀ i, IsCompact ((b'.coord i) '' Ω) := fun i => hΩ.image (hcont i)
  choose m hm0 hm using fun i => GlobalTheory.T.compact_rational_bounded_denominators p _ (hcpt i)
  refine ⟨∏ i, m i, Finset.prod_pos (fun i _ => hm0 i), fun c hc i => ?_⟩
  have hval : b'.coord i ((1 : AfP p) ⊗ₜ[ℚ] c) = algebraMap ℚ (AfP p) (b.repr c i) := by
    simp only [b', Module.Basis.coord_apply, Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]
  obtain ⟨k, e, hk⟩ := hm i (b.repr c i) (hval ▸ ⟨_, hc, rfl⟩)
  obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem m (Finset.mem_univ i)
  refine ⟨k * r, e, ?_⟩
  rw [hr]
  push_cast
  rw [← hk]
  ring

end GlobalTheory.AfPVecDen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratedModuleFiltrationExhaustive
section
noncomputable section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult

namespace GlobalTheory.SteepSpan

variable {R S : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

lemma word_zero (act : Mat R S →ₗ[ℂ] Module.End ℂ V) (g : Fin 0 → NC R S) : word act g = 1 := by
  simp [word]

lemma word_succ (act : Mat R S →ₗ[ℂ] Module.End ℂ V) {k : ℕ} (g : Fin (k + 1) → NC R S) :
    word act g = act (eNC (g 0)) * word act (fun i : Fin k => g i.succ) := by
  simp [word, List.ofFn_succ]

def wordSpan (act : Mat R S →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V) : Submodule ℂ V :=
  Submodule.span ℂ {y | ∃ (k : ℕ) (g : Fin k → NC R S) (n : V), n ∈ N ∧ y = word act g n}

lemma word_mem_wordSpan (act : Mat R S →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V) {k : ℕ} (g : Fin k → NC R S)
    {n : V} (hn : n ∈ N) : word act g n ∈ wordSpan act N :=
  Submodule.subset_span ⟨k, g, n, hn, rfl⟩

lemma le_wordSpan (act : Mat R S →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V) {n : V} (hn : n ∈ N) :
    n ∈ wordSpan act N := by
  simpa [word_zero] using word_mem_wordSpan act N (k := 0) Fin.elim0 hn

lemma nc_mem_wordSpan (act : Mat R S →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V) (x : NC R S) {y : V}
    (hy : y ∈ wordSpan act N) : act (eNC x) y ∈ wordSpan act N := by
  have : wordSpan act N ≤ (wordSpan act N).comap (act (eNC x)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, g, n, hn, rfl⟩
    have h := word_mem_wordSpan act N (k := k + 1) (Fin.cons x g) hn
    rw [word_succ] at h
    simpa using h
  exact this hy

lemma act_base (act : Mat R S →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V) (hN : KStable act N) (Z : Mat R S)
    {n : V} (hn : n ∈ N) : act Z n ∈ wordSpan act N := by
  have hZ : Z = ∑ a, ∑ b, Z a b • Eab a b := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single Z]
    simp [Eab, Matrix.smul_single]
  rw [hZ]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ ?_
  by_cases h : sameBlock a b
  · exact le_wordSpan act N (hN _ (GlobalTheory.TensorHW.isKC_Eab h) _ hn)
  · exact nc_mem_wordSpan act N ⟨(a, b), h⟩ (le_wordSpan act N hn)

lemma act_word (act : Mat R S →ₗ[ℂ] Module.End ℂ V)
    (hL : ∀ Y Z : Mat R S, act (Y * Z - Z * Y) = act Y * act Z - act Z * act Y)
    (N : Submodule ℂ V) (hN : KStable act N) {n : V} (hn : n ∈ N) (k : ℕ) :
    ∀ (g : Fin k → NC R S) (Z : Mat R S), act Z (word act g n) ∈ wordSpan act N := by
  induction k with
  | zero =>
    intro g Z
    rw [word_zero]
    exact act_base act N hN Z hn
  | succ k ih =>
    intro g Z
    rw [word_succ, Module.End.mul_apply]
    have h := ih (fun i => g i.succ) (Z * eNC (g 0) - eNC (g 0) * Z)
    rw [hL, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply] at h
    simpa using add_mem h (nc_mem_wordSpan act N (g 0) (ih (fun i => g i.succ) Z))

lemma filt_mono (act : Mat R S →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V) {k l : ℕ} (h : k ≤ l) :
    filt act N k ≤ filt act N l :=
  iSup_le fun j => le_iSup (fun j : Fin (l + 1) => LinearMap.range (phiN act N j)) ⟨j, by omega⟩

lemma word_mem_filt (act : Mat R S →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V) {k : ℕ} (g : Fin k → NC R S)
    {n : V} (hn : n ∈ N) : word act g n ∈ filt act N k := by
  classical
  refine le_iSup (fun j : Fin (k + 1) => LinearMap.range (phiN act N j)) (Fin.last k) ?_
  refine ⟨(Pi.single g ⟨n, hn⟩ : (Fin k → NC R S) → N), ?_⟩
  change phiN act N k _ = _
  rw [phiN_apply, Finset.sum_eq_single g]
  · simp
  · intro h _ hne
    simp [Pi.single_eq_of_ne hne]
  · simp

theorem filt_exhaustive : ∀ (R S : ℕ) (M : GKMod R S) (Λ : Ix R S → ℚ) (v : M.V), IsHW M.act Λ v →
    genSub M.act {v} = ⊤ → ∀ w, ∃ k, w ∈ filt M.act (GlobalTheory.BlockReps.gen M.act v) k := by
  intro R S M Λ v _ hgen w
  have hle : genSub M.act {v} ≤ wordSpan M.act (GlobalTheory.BlockReps.gen M.act v) := by
    refine sInf_le ⟨Set.singleton_subset_iff.2 (le_wordSpan _ _ (GlobalTheory.BlockReps.mem_gen v)), fun Z => ?_⟩
    have : wordSpan M.act (GlobalTheory.BlockReps.gen M.act v) ≤
        (wordSpan M.act (GlobalTheory.BlockReps.gen M.act v)).comap (M.act Z) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨k, g, n, hn, rfl⟩
      exact act_word M.act M.lie _ (GlobalTheory.BlockReps.stable_gen v) hn k g Z
    exact fun y hy => this hy
  have hw : w ∈ wordSpan M.act (GlobalTheory.BlockReps.gen M.act v) := hle (hgen ▸ Submodule.mem_top)
  induction hw using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨k, g, n, hn, rfl⟩ := hy
    exact ⟨k, word_mem_filt _ _ g hn⟩
  | zero => exact ⟨0, zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨k, hk⟩ := hx
    obtain ⟨l, hl⟩ := hy
    exact ⟨max k l, add_mem (filt_mono _ _ (le_max_left _ _) hk) (filt_mono _ _ (le_max_right _ _) hl)⟩
  | smul c x _ hx =>
    obtain ⟨k, hk⟩ := hx
    exact ⟨k, Submodule.smul_mem _ _ hk⟩

end GlobalTheory.SteepSpan

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratedSubmoduleHighestWeightStructure
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult

namespace GlobalTheory.GenHW

theorem block_span_hw : ∀ (R S : ℕ) (M : GKMod R S) (Λ : Ix R S → ℚ) (v : M.V), IsHW M.act Λ v →
    FiniteDimensional ℂ (GlobalTheory.BlockReps.gen M.act v) ∧
    IsKLieAct (restrAct M.act _ (GlobalTheory.BlockReps.stable_gen (act := M.act) v)) ∧
    (∀ w, w ∈ ⨆ μ : Ix R S → ℚ, wtSub (restrAct M.act _ (GlobalTheory.BlockReps.stable_gen (act := M.act) v)) μ) ∧
    IsHW (restrAct M.act _ (GlobalTheory.BlockReps.stable_gen (act := M.act) v)) Λ ⟨v, GlobalTheory.BlockReps.mem_gen v⟩ ∧
    GlobalTheory.BlockReps.gen (restrAct M.act _ (GlobalTheory.BlockReps.stable_gen (act := M.act) v)) ⟨v, GlobalTheory.BlockReps.mem_gen v⟩ = ⊤ := by
  intro R S M Λ v hv
  have hKS : KStable M.act (GlobalTheory.BlockReps.gen M.act v) := GlobalTheory.BlockReps.stable_gen (act := M.act) v
  set G := GlobalTheory.BlockReps.gen M.act v with hG
  set ρ := restrAct M.act G hKS with hρ
  have hρapp : ∀ Z, IsKC Z → ∀ x : G, ((ρ Z x : G) : M.V) = M.act Z x := by
    intro Z hZ x
    rw [hρ, restrAct_apply, kpart_of_isKC hZ]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨W, hWf, hvW, hWs⟩ := M.kfin v
    exact Submodule.finiteDimensional_of_le (GlobalTheory.BlockReps.gen_le hvW hWs)
  · intro Y Z hY hZ
    ext x
    have hYZ := GlobalTheory.TensorHW.isKC_comm hY hZ
    simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub]
    rw [hρapp _ hYZ, hρapp _ hY, hρapp _ hZ, hρapp _ hZ, hρapp _ hY, M.lie]
    simp
  · intro w
    have h := GlobalTheory.BlockReps.decomp hKS w.2 (M.wts w)
    have hle : (⨆ μ, G ⊓ wtSub M.act μ) ≤ (⨆ μ : Ix R S → ℚ, wtSub ρ μ).map G.subtype := by
      refine iSup_le fun μ x hx => ⟨⟨x, hx.1⟩, Submodule.mem_iSup_of_mem μ ?_, rfl⟩
      rw [GlobalTheory.TensorHW.mem_wt]
      intro a
      apply Subtype.ext
      rw [hρapp _ (GlobalTheory.TensorHW.isKC_Eab (GlobalTheory.TensorHW.same_refl a))]
      exact GlobalTheory.TensorHW.mem_wt.1 hx.2 a
    obtain ⟨y, hy, hyw⟩ := Submodule.mem_map.1 (hle h)
    rwa [Subtype.val_injective hyw] at hy
  · refine ⟨fun h => hv.1 (congrArg Subtype.val h), ?_⟩
    have hv2 := GlobalTheory.TensorHW.mem_hw.1 hv.2
    rw [GlobalTheory.TensorHW.mem_hw]
    refine ⟨fun a => ?_, fun a b hab => ?_⟩
    · apply Subtype.ext
      rw [hρapp _ (GlobalTheory.TensorHW.isKC_Eab (GlobalTheory.TensorHW.same_refl a))]
      exact hv2.1 a
    · apply Subtype.ext
      rw [hρapp _ (GlobalTheory.TensorHW.isKC_Eab (GlobalTheory.TensorHW.same_of_pos hab))]
      exact hv2.2 a b hab
  · set N := GlobalTheory.BlockReps.gen ρ ⟨v, GlobalTheory.BlockReps.mem_gen v⟩ with hN
    have hNs : KStable ρ N := GlobalTheory.BlockReps.stable_gen (act := ρ) _
    have hmap : KStable M.act (N.map G.subtype) := by
      rintro X hX _ ⟨y, hy, rfl⟩
      exact ⟨ρ X y, hNs X hX y hy, hρapp X hX y⟩
    have hle : G ≤ N.map G.subtype :=
      GlobalTheory.BlockReps.gen_le ⟨⟨v, GlobalTheory.BlockReps.mem_gen v⟩, GlobalTheory.BlockReps.mem_gen _, rfl⟩ hmap
    refine eq_top_iff.2 fun w _ => ?_
    obtain ⟨y, hy, hyw⟩ := Submodule.mem_map.1 (hle w.2)
    rwa [Subtype.val_injective hyw] at hy

end GlobalTheory.GenHW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreProjective
section
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj

noncomputable section

namespace GlobalTheory.GenericFibre

open Limits

theorem pullback_isPullback_of_eq {X Y' Z : Scheme.{0}} (a a' : X ⟶ Z) (b b' : Y' ⟶ Z) (ha : a = a') (hb : b = b') :
    IsPullback (pullback.fst a b) (pullback.snd a b) a' b' := by
  subst ha hb; exact IsPullback.of_hasPullback _ _

theorem isProjOver_genericFibre : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] (q : B ⟶ Sp k)
    (p : Y ⟶ Sp k), IsProjOver q → IsProjOver p → ∀ (f : Y ⟶ B), f ≫ q = p → ∀ (G : Scheme.{0}) (j : G ⟶ Y)
    (s : G ⟶ Sp B.functionField), IsPullback j s f (B.fromSpecStalk (genericPoint B)) → IsProjOver s := by
  intro k _ B Y _ q p hq hp f hfq G j s H
  haveI : IsProper q := CommonModel.isProper_of_isProjOver hq
  obtain ⟨φ, hφ⟩ : ∃ φ : k →+* B.functionField, B.fromSpecStalk (genericPoint B) ≫ q = spMap φ :=
    ⟨(Spec.preimage (B.fromSpecStalk (genericPoint B) ≫ q)).hom, by simp [spMap]⟩
  have P : IsPullback (pullback.fst (f ≫ q) (B.fromSpecStalk (genericPoint B) ≫ q))
      (pullback.snd (f ≫ q) (B.fromSpecStalk (genericPoint B) ≫ q)) p (spMap φ) := by
    exact pullback_isPullback_of_eq _ _ _ _ hfq hφ
  have h1 := ProjSpace.isProjOver_of_isPullback_spMap φ P hp
  have h2 := ProjSpace.isProjOver_comp_of_isClosedImmersion
    (H.isoPullback.hom ≫ pullback.mapDesc f (B.fromSpecStalk (genericPoint B)) q) h1
  have e : (H.isoPullback.hom ≫ pullback.mapDesc f (B.fromSpecStalk (genericPoint B)) q) ≫
      pullback.snd (f ≫ q) (B.fromSpecStalk (genericPoint B) ≫ q) = s := by
    simp only [pullback.mapDesc, pullback.map, Category.assoc, pullback.lift_snd, Category.comp_id]
    exact H.isoPullback_hom_snd
  rwa [e] at h2

end GlobalTheory.GenericFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeLocalGaussSumNormSqEqAbsNormPowStatement
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeLocalGaussSum_norm_sq_eq_absNorm_pow : ∀ {E : Type} [Field E] [NumberField E] (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (a : ℕ) (c : Eˣ), a ≠ 0 → ExpAt χ w a → IsUnitary χ → w.valuation E (c : E) = WithZero.exp (-((a + diffExp w : ℕ) : ℤ)) → ‖gaussSumAt χ w a c‖ ^ 2 = (Ideal.absNorm w.asIdeal : ℝ) ^ a := by
  first | exact @GlobalTheory.GaussMod.gaussSumAt_normSq | exact GlobalTheory.GaussMod.gaussSumAt_normSq | (intros; apply GlobalTheory.GaussMod.gaussSumAt_normSq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTripleTrivialOverRealsOfGramCongruentStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianTriple_trivial_over_reals_of_gram_congruent : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ), (∀ v : InfinitePlace G.F, ∃ W : GL (Fin G.n) ℂ, G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C) = (W : Matrix (Fin G.n) (Fin G.n) ℂ)ᴴ * G.gram v * (W : Matrix (Fin G.n) (Fin G.n) ℂ)) → ∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1 := by
  first | (exact @GlobalTheory.LKMid.trivR_of_gram_psi_inv_congr) | (exact GlobalTheory.LKMid.trivR_of_gram_psi_inv_congr) | (intros; apply GlobalTheory.LKMid.trivR_of_gram_psi_inv_congr  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologySubsingletonEtaleOverPolynomiStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistCohomology_subsingleton_etale_over_polynomial_algClosed : ∀ (q : ℕ) [NeZero q] (K E : Type) [Field K] [IsAlgClosed K] [CommRing E] [Algebra (Polynomial K) E] [Algebra.Etale (Polynomial K) E], IsUnit (q : K) → ∀ n i : ℤ, 2 ≤ n → Subsingleton (Ht q (sp E) n i) := by
  first | (exact @GlobalTheory.EtAlgCD.etale_polynomial_cd_le_one) | (exact GlobalTheory.EtAlgCD.etale_polynomial_cd_le_one) | (intros; apply GlobalTheory.EtAlgCD.etale_polynomial_cd_le_one <;> assumption)
end

