import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2107
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1145
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2110
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0505
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2020
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2087
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0083
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0053
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeSubsetAbelianLocusOfGoodReduction
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1761
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1103
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0119
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1051
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2099
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2116
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionPullbackExistsUnique
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0025
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2111
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2086
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1183
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0364
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2112
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylTensorReductionWeightProjector
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.HighWtEmb

namespace GlobalTheory.HighWtEmb

theorem wComp_monomial_eq_ite {σ R M : Type} [CommSemiring R] [AddCommMonoid M] [DecidableEq M] (w : σ → M) (n : M) (d : σ →₀ ℕ) (c : R) :
    weightedHomogeneousComponent w n (monomial d c) = if Finsupp.weight w d = n then monomial d c else 0 := by
  classical
  ext m
  rw [coeff_weightedHomogeneousComponent, coeff_monomial]
  by_cases h : Finsupp.weight w d = n <;> by_cases hd : d = m
  · subst hd; simp [h]
  · simp [h, hd, coeff_monomial]
  · subst hd; simp [h]
  · simp [h, hd]

theorem wComp_mul_of_weight_zero {σ R M : Type} [CommSemiring R] [AddCommMonoid M] (w : σ → M) (n : M) (P Q : MvPolynomial σ R)
    (hQ : IsWeightedHomogeneous w Q 0) :
    weightedHomogeneousComponent w n (P * Q) = weightedHomogeneousComponent w n P * Q := by
  classical
  ext m
  rw [coeff_weightedHomogeneousComponent, coeff_mul, coeff_mul]
  split_ifs with h
  · refine Finset.sum_congr rfl fun x hx => ?_
    rw [coeff_weightedHomogeneousComponent]
    by_cases hq : coeff x.2 Q = 0
    · simp [hq]
    · have h2 := hQ hq
      have hm : x.1 + x.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
      have e : Finsupp.weight w x.1 = n := by rw [← h, ← hm, map_add, h2, add_zero]
      rw [if_pos e]
  · symm
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [coeff_weightedHomogeneousComponent]
    by_cases hq : coeff x.2 Q = 0
    · simp [hq]
    · have h2 := hQ hq
      have hm : x.1 + x.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
      have e : Finsupp.weight w x.1 ≠ n := by rw [← hm, map_add, h2, add_zero] at h; exact h
      rw [if_neg e, zero_mul]

theorem blockRed_eq_rename_map (O : Type) [CommRing O] (N : ℕ) {ι : Type} (ϖ : O) (τ : ι) (f : MvPolynomial (Fin N × Fin N) O) :
    blockRed O N ϖ τ f = rename (fun v => ((τ, v) : BVar N ι)) (map (Ideal.Quotient.mk (Ideal.span {ϖ})) f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [blockRed, MvPolynomial.algebraMap_eq]
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p v hp => rw [map_mul, hp]; simp [blockRed]

theorem weight_blockW_mapDomain_self (N : ℕ) {ι : Type} [DecidableEq ι] (τ : ι) (d : Fin N × Fin N →₀ ℕ) :
    Finsupp.weight (blockW N τ) (Finsupp.mapDomain (fun v => ((τ, v) : BVar N ι)) d) = Finsupp.weight (rowW N N) d := by
  rw [Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum_mapDomain_index (h := fun i c => c • blockW N τ i) (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]
  simp [blockW, rowW]

theorem weight_blockW_mapDomain_of_ne (N : ℕ) {ι : Type} [DecidableEq ι] {τ σ : ι} (h : σ ≠ τ) (d : Fin N × Fin N →₀ ℕ) :
    Finsupp.weight (blockW N τ) (Finsupp.mapDomain (fun v => ((σ, v) : BVar N ι)) d) = 0 := by
  rw [Finsupp.weight_apply, Finsupp.sum_mapDomain_index (h := fun i c => c • blockW N τ i) (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]
  simp [blockW, h]

end GlobalTheory.HighWtEmb

namespace GlobalTheory.HighWtEmb

theorem blockRed_wComp_rowW (O : Type) [CommRing O] (N : ℕ) {ι : Type} [DecidableEq ι] (ϖ : O) (τ : ι) (v : Fin N → ℕ)
    (f : MvPolynomial (Fin N × Fin N) O) :
    blockRed O N ϖ τ (weightedHomogeneousComponent (rowW N N) v f) =
      weightedHomogeneousComponent (blockW N τ) v (blockRed O N ϖ τ f) := by
  classical
  conv_rhs => rw [f.as_sum]
  rw [weightedHomogeneousComponent_apply, map_sum, map_sum, map_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp only [blockRed_eq_rename_map, map_monomial, rename_monomial]
  rw [wComp_monomial_eq_ite, weight_blockW_mapDomain_self]

theorem blockRed_isWeightedHomogeneous_zero (O : Type) [CommRing O] (N : ℕ) {ι : Type} [DecidableEq ι] (ϖ : O) {τ σ : ι} (h : σ ≠ τ)
    (f : MvPolynomial (Fin N × Fin N) O) : IsWeightedHomogeneous (blockW N τ) (blockRed O N ϖ σ f) 0 := by
  rw [blockRed_eq_rename_map, f.as_sum, map_sum, map_sum, ← mem_weightedHomogeneousSubmodule]
  refine Submodule.sum_mem _ fun d _ => ?_
  rw [mem_weightedHomogeneousSubmodule, map_monomial, rename_monomial]
  exact isWeightedHomogeneous_monomial _ _ _ (weight_blockW_mapDomain_of_ne N h d)

theorem redT_tprod_prod_blockRed (O : Type) [CommRing O] (N : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι] (mu : ι → ℕ → ℕ) (ϖ : O)
    (x : ∀ τ, dualWeyl O N N (res N (mu τ))) :
    redT O N mu ϖ (PiTensorProduct.tprod O x) = ∏ σ, blockRed O N ϖ σ (x σ) := by
  simp [redT]

theorem redT_isProj : ∀ (O : Type) [CommRing O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (mu : ι → ℕ → ℕ) (ϖ : O) (τ : ι) (v : Fin N → ℕ) (a : Module.End O (NablaT O N mu)), IsProj O N mu τ v a → ∀ y : NablaT O N mu, redT O N mu ϖ (a y) = weightedHomogeneousComponent (blockW N τ) v (redT O N mu ϖ y) := by
  intro O _ N ι _ _ mu ϖ τ v a ha y
  have key : (redT O N mu ϖ).comp a =
      ((weightedHomogeneousComponent (blockW N τ) v).restrictScalars O).comp (redT O N mu ϖ) := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro x
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearMap.restrictScalars_apply]
    let yy : dualWeyl O N N (res N (mu τ)) := rowProj O N (res N (mu τ)) v (x τ)
    have hQ : IsWeightedHomogeneous (blockW N τ) (∏ σ ∈ ({τ}ᶜ : Finset ι), blockRed O N ϖ σ (x σ)) 0 := by
      have := IsWeightedHomogeneous.prod ({τ}ᶜ : Finset ι) (fun σ => blockRed O N ϖ σ (x σ)) (fun _ => (0 : Fin N → ℕ))
        (fun σ hσ => blockRed_isWeightedHomogeneous_zero O N ϖ (by simpa using hσ) (x σ))
      simpa using this
    rw [ha x yy rfl, redT_tprod_prod_blockRed, redT_tprod_prod_blockRed, Fintype.prod_eq_mul_prod_compl τ, Fintype.prod_eq_mul_prod_compl τ,
      Function.update_self, wComp_mul_of_weight_zero _ _ _ _ hQ]
    congr 1
    · show blockRed O N ϖ τ (weightedHomogeneousComponent (rowW N N) v (x τ : MvPolynomial (Fin N × Fin N) O)) = _
      exact blockRed_wComp_rowW O N ϖ τ v _
    · refine Finset.prod_congr rfl fun σ hσ => ?_
      rw [Function.update_of_ne (by simpa using hσ)]
  exact LinearMap.congr_fun key y

end GlobalTheory.HighWtEmb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoprimeMulInvGenusLatticeScalarIntegralStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coprime_mul_inv_genusLatticeScalar_integral : ∀ (D : D7) (T : Full D), LawsFull T → ∀ (j : ℕ), InR D j → ∀ {n : ℕ} (Λ : GenLat D.host.E n) (σ : T.Q.c.F →+* ℂ) (p : ℕ), p.Prime → Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt p → ∃ m : ℕ, Nat.Coprime m p ∧ IsIntegral ℤ ((m : ℂ) * (σ (betaH (Dw := T.Q.Dw j) T.Q.c Λ))⁻¹) := by
  first | exact @GlobalTheory.BetaInvIntegral.betaH_inv_integral | exact GlobalTheory.BetaInvIntegral.betaH_inv_integral | (intros; apply GlobalTheory.BetaInvIntegral.betaH_inv_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDetIdealCoprimeSplitSupportedPointStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_detIdeal_coprime_splitSupportedPoint : ∀ (D : D7) (V : HSp D), HSpace.gram V = 1 → Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank → ∀ (h : GA D V) (e : AE D) (P : Finset (HeightOneSpectrum (𝓞 D.host.E))) (y : (AE D)ˣ), IsIdemSum e P → SuppAt e V h → IsDetAt e V h y → ∀ (b : ℕ), (∀ Q ∈ P, (b : 𝓞 D.host.E) ∉ Q.asIdeal) → ∀ (c : (AE D)ˣ →* Circle) (ψ : Formalism.L2.Host.HChar D.host.E), ChrEq c ψ → (∀ Q : HeightOneSpectrum (𝓞 D.host.E), (b : 𝓞 D.host.E) ∉ Q.asIdeal → ψ.UnrAt Q) → (∀ Q : HeightOneSpectrum (𝓞 D.host.E), GlobalTheory.IdemSupport.cP Q ≠ Q → ∀ k : D.host.Fˣ, ψ.resFin (Q.under (𝓞 D.host.F)) k = 1) → ∀ (Λ : GenLat D.host.E V.rank), (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat V (fin V h)) → ∀ p : ℕ, p.Prime → Λ.TrivAt p → ∃ cc : Ideal (𝓞 D.host.E), cc ≠ ⊥ ∧ cc ⊔ Ideal.span {(b : 𝓞 D.host.E)} = ⊤ ∧ Nat.Coprime (Ideal.absNorm cc) p ∧ ((c y : Circle) : ℂ) = ((ψ.onId (cc : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.DetIdealPrime.exists_ideal_coprime | exact GlobalTheory.DetIdealPrime.exists_ideal_coprime | (intros; apply GlobalTheory.DetIdealPrime.exists_ideal_coprime <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiscreteValuationCentredCompleteNormal
section
open IsLocalRing GlobalTheory.TorRef

namespace GlobalTheory.DivVal

theorem exists_valuation_centre (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (hV : IsCN V) :
    ∃ ν : Valuation (FractionRing V) (WithZero (Multiplicative ℤ)),
      (∀ v : V, ν (algebraMap V (FractionRing V) v) ≤ 1) ∧
        ∀ v ∈ maximalIdeal V, ν (algebraMap V (FractionRing V) v) < 1 := by
  classical
  haveI : IsNoetherianRing V := hV.1
  by_cases hm : maximalIdeal V = ⊥
  · refine ⟨1, fun v => ?_, fun v hv => ?_⟩
    · by_cases h : algebraMap V (FractionRing V) v = 0
      · simp [h]
      · simp [Valuation.one_apply_of_ne_zero h]
    · rw [hm, Ideal.mem_bot] at hv
      simp [hv]
  · obtain ⟨T, hT, g, hg, hc⟩ := GlobalTheory.GoodVal.exists_dvr_centre (R := V) (K := FractionRing V)
      (L := FractionRing V) (maximalIdeal V) hm
    have hg' : ∀ v : V, algebraMap T (FractionRing V) (g v) = algebraMap V (FractionRing V) v := fun v => by
      simpa using congrArg (fun f => f v) hg
    have hne : maximalIdeal T ≠ ⊥ := IsDiscreteValuationRing.not_a_field T
    let P : IsDedekindDomain.HeightOneSpectrum T := ⟨maximalIdeal T, inferInstance, hne⟩
    refine ⟨P.valuation (FractionRing V), fun v => ?_, fun v hv => ?_⟩
    · rw [← hg']
      exact P.valuation_le_one (g v)
    · rw [← hg']
      refine (P.valuation_lt_one_iff_mem (g v)).2 ?_
      show g v ∈ maximalIdeal T
      rw [← Ideal.mem_comap, hc]
      exact hv

end GlobalTheory.DivVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivariantUnitConstantsGoodEmbedding
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EquivConst

theorem exists_unit_constants {X G H C : Type} [Group G] [Finite G] [Group H] (L : G → H → Prop) (cp : H → X)
    (ρ : G → C → C) (r : C → H → ℂ) (mu : H → ℂ) (s : G → ℂ) (mv : X → G → X) (z : X → G → ℂ)
    (hex : ∀ g, ∃ k, L g k) (hL : ∀ g g' k k', L g k → L g' k' → L (g * g') (k * k'))
    (hρ1 : ∀ f, ρ 1 f = f) (hρ : ∀ g g' f, ρ (g * g') f = ρ g (ρ g' f))
    (hmu : ∀ h k, mu (h * k) = mu h * mu k) (hmu1 : ∀ h, ‖mu h‖ = 1)
    (hs1 : s 1 = 1) (hs : ∀ g g', s (g * g') = s g * s g')
    (hmv1 : ∀ x, mv x 1 = x) (hmv : ∀ x g g', mv x (g * g') = mv (mv x g) g')
    (hcp : ∀ g k, L g k → ∀ h, cp (h * k) = mv (cp h) g)
    (hz1 : ∀ x g, ‖z x g‖ = 1) (hz : ∀ g k, L g k → ∀ f h, r (ρ g f) h = z (cp h) g * r f (h * k))
    (hst : ∀ g k, L g k → ∀ h, cp (h * k) = cp h → ∀ f, mu h * r (ρ g f) h = s g * (mu (h * k) * r f (h * k))) :
    ∃ c : X → ℂ, (∀ x, ‖c x‖ = 1) ∧ ∀ g k, L g k → ∀ f h,
      c (cp h) * mu h * r (ρ g f) h = s g * (c (cp (h * k)) * mu (h * k) * r f (h * k)) := by
  classical
  choose l hl using hex
  have hsn : ∀ g, ‖s g‖ = 1 := by
    intro g
    let S : G →* ℂ := ⟨⟨s, hs1⟩, hs⟩
    have h1 : s g ^ Nat.card G = 1 := by
      show S g ^ Nat.card G = 1
      rw [← map_pow, pow_card_eq_one', map_one]
    have h2 : ‖s g‖ ^ Nat.card G = 1 := by rw [← norm_pow, h1, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) Nat.card_pos.ne').1 h2
  have ne : ∀ {a : ℂ}, ‖a‖ = 1 → a ≠ 0 := fun {a} h h0 => by simp [h0] at h
  let good : X → Prop := fun x => ∃ f h, cp h = x ∧ r f h ≠ 0
  have hinv : ∀ g f, ρ g (ρ g⁻¹ f) = f := fun g f => by rw [← hρ, mul_inv_cancel, hρ1]
  have hgood : ∀ x g, good x → good (mv x g) := by
    rintro _ g ⟨f, h, rfl, hf⟩
    refine ⟨ρ g⁻¹ f, h * l g, hcp g _ (hl g) h, fun h0 => hf ?_⟩
    rw [← hinv g f, hz g _ (hl g), h0, mul_zero]
  have hgood' : ∀ x g, good (mv x g) → good x := fun x g h => by
    have := hgood _ g⁻¹ h
    rwa [← hmv, mul_inv_cancel, hmv1] at this
  have hone : ∀ x, good x → ∀ k, L 1 k → mu k = z x 1 := by
    rintro _ ⟨f, h, rfl, hf⟩ k hk
    have e1 := hz 1 k hk f h
    have e2 := hst 1 k hk h (by rw [hcp 1 k hk, hmv1]) f
    rw [hρ1] at e1 e2
    have h0 : r f (h * k) ≠ 0 := fun h0 => hf (by rw [e1, h0, mul_zero])
    rw [e1, hs1, hmu, one_mul] at e2
    have : mu h * r f (h * k) * mu k = mu h * r f (h * k) * z (cp h) 1 := by linear_combination -e2
    exact mul_left_cancel₀ (mul_ne_zero (ne (hmu1 h)) h0) this
  have hlift : ∀ x, good x → ∀ g k, L g k → mu k = mu (l g) := by
    intro x hx g k hk
    have e1 := hone x hx (k * l g⁻¹) (by simpa using hL _ _ _ _ hk (hl g⁻¹))
    have e2 := hone x hx (l g * l g⁻¹) (by simpa using hL _ _ _ _ (hl g) (hl g⁻¹))
    rw [hmu] at e1 e2
    exact mul_right_cancel₀ (ne (hmu1 _)) (e1.trans e2.symm)
  let w : X → G → ℂ := fun x g => if good x then z x g / (s g * mu (l g)) else 1
  have hw1 : ∀ x g, ‖w x g‖ = 1 := fun x g => by
    simp only [w]
    split_ifs
    · rw [norm_div, norm_mul, hz1, hsn, hmu1]; norm_num
    · exact norm_one
  have key : ∀ g k, L g k → ∀ f h, mu h * r (ρ g f) h = w (cp h) g * s g * (mu (h * k) * r f (h * k)) := by
    intro g k hk f h
    by_cases hg : good (cp h)
    · simp only [w, if_pos hg]
      rw [hz g k hk, hmu, hlift _ hg g k hk]
      have := ne (hsn g)
      have := ne (hmu1 (l g))
      field_simp
    · have h0 : r (ρ g f) h = 0 := by
        by_contra h0
        exact hg ⟨_, h, rfl, h0⟩
      have h1 : r f (h * k) = 0 := by
        have := hz g k hk f h
        rw [h0] at this
        exact (mul_eq_zero.1 this.symm).resolve_left (ne (hz1 _ _))
      rw [h0, h1]; simp
  obtain ⟨c, hc1, hc⟩ := GlobalTheory.unitary_cocycle_coboundary_of_trivial_on_stabilisers mv w hmv1 hmv hw1 (by
    intro x g g'
    by_cases hg : good x
    · obtain ⟨f, h, rfl, hf⟩ := hg
      have e1 := key (g * g') (l g * l g') (hL _ _ _ _ (hl g) (hl g')) (ρ (g * g')⁻¹ f) h
      have e2 := key g (l g) (hl g) (ρ g' (ρ (g * g')⁻¹ f)) h
      have e3 := key g' (l g') (hl g') (ρ (g * g')⁻¹ f) (h * l g)
      rw [← hρ, e3, hcp g _ (hl g), mul_assoc h] at e2
      rw [hinv] at e1 e2
      rw [hs] at e1
      set P := mu (h * (l g * l g')) * r (ρ (g * g')⁻¹ f) (h * (l g * l g')) with hP
      have hP0 : P ≠ 0 := fun h0 => mul_ne_zero (ne (hmu1 h)) hf (by rw [e1, h0, mul_zero])
      have : s g * s g' * P * w (cp h) (g * g') = s g * s g' * P * (w (cp h) g * w (mv (cp h) g) g') := by
        linear_combination e2 - e1
      exact mul_left_cancel₀ (mul_ne_zero (mul_ne_zero (ne (hsn g)) (ne (hsn g'))) hP0) this
    · simp only [w, if_neg hg, if_neg (fun h => hg (hgood' x g h)), mul_one]) (by
    intro x g hx
    by_cases hg : good x
    · obtain ⟨f, h, rfl, hf⟩ := hg
      have e1 := key g (l g) (hl g) (ρ g⁻¹ f) h
      have e2 := hst g (l g) (hl g) h (by rw [hcp g _ (hl g), hx]) (ρ g⁻¹ f)
      rw [hinv] at e1 e2
      set P := mu (h * l g) * r (ρ g⁻¹ f) (h * l g) with hP
      have hP0 : P ≠ 0 := fun h0 => mul_ne_zero (ne (hmu1 h)) hf (by rw [e1, h0, mul_zero])
      have : s g * P * w (cp h) g = s g * P * 1 := by linear_combination e2 - e1
      exact mul_left_cancel₀ (mul_ne_zero (ne (hsn g)) hP0) this
    · simp only [w, if_neg hg])
  refine ⟨c, hc1, fun g k hk f h => ?_⟩
  rw [mul_assoc, key g k hk, hcp g k hk, ← hc]
  ring

end GlobalTheory.EquivConst

namespace GlobalTheory.EquivConst

theorem isLift_mul {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank}
    {g g' : G0 L.Pg L.r} {k k' : GA D V} (hk : Lev.IsLevelLift V β L g k) (hk' : Lev.IsLevelLift V β L g' k') :
    Lev.IsLevelLift V β L (g * g') (k * k') := by
  refine ⟨(GfC V).mul_mem hk.1 hk'.1, ?_, ?_⟩
  · rw [map_mul]; exact Subgroup.mul_mem _ hk.2.1 hk'.2.1
  · rw [map_mul, Formalism.L2.DIV.rTup_mul hk.2.1 hk'.2.1, hk.2.2, hk'.2.2]

theorem muVal_cast {D : D7} {V W : HSp D} (hV : V = W) {χ : (AE D)ˣ →* Circle} {mu : GA D V → ℂ} (h : MuVal V χ mu) :
    (∀ g g', castDict hV mu (g * g') = castDict hV mu g * castDict hV mu g') ∧ ∀ g, ‖castDict hV mu g‖ = 1 := by
  subst hV
  refine ⟨fun g g' => ?_, fun g => h.norm g⟩
  show mu (g * g') = mu g * mu g'
  obtain ⟨x, hx⟩ := h.1 g
  obtain ⟨x', hx'⟩ := h.1 g'
  have hxx : IsDetRoot V (g * g') (x * x') := by
    unfold IsDetRoot at *
    rw [Units.val_mul, (matHom V).map_mul, Units.val_mul, Matrix.det_mul, RingHom.map_mul]
    conv_lhs => rw [hx, hx']
    ring
  rw [h.2 _ _ hxx, h.2 _ _ hx, h.2 _ _ hx', map_mul, Circle.coe_mul]

theorem phiAt_apply {D : D7} (T : CoreJ D) (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ) (hV : T.V ((i : ℕ) + 1) σ = Wc D i)
    (c : (T.U ((i : ℕ) + 1) σ).Comp → ℂ) (f : T.R ((i : ℕ) + 1)) (h : GA D (Wc D i)) :
    phiAt T i σ hV c f h = c (castDict hV (T.dict ((i : ℕ) + 1) σ) h).1 * castDict hV (T.mu ((i : ℕ) + 1) σ) h *
      rdU (T.U ((i : ℕ) + 1) σ) f (castDict hV (T.dict ((i : ℕ) + 1) σ) h).1 (castDict hV (T.dict ((i : ℕ) + 1) σ) h).2 := rfl

set_option maxHeartbeats 1000000 in

theorem exists_equivariant_constants : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), R.toLevCh.Is A.μ0 → TieIn T R κ v₀ → T.pb = R.C.P.pb → (∀ i, OMPins T R κ v₀ O i) → ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i, ∃ c', CUnit c' ∧ EqAt T R κ (O i) σ hV c' := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ O hI hT hpb hO i σ hσ hV
  have hact := (hO i).2.act.1
  have hkeep := fun g => GlobalTheory.T.levelAction_mem_cuspForms_of_action_laws T κ i (O i).lev2 hT.laws hact g (fun _ => rfl)
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.exists_level_action_cusp_form_representation T κ i (O i).lev2 hT.laws hact hkeep
  have hex : ∀ g, ∃ k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k :=
    fun g => ((hO i).2.lift.lev g).imp fun _ h => h.1
  obtain ⟨mv, hmv1, hmv, -, hcp⟩ := GlobalTheory.T.exists_finiteGroup_rightAction_components T R κ v₀ hI hT hpb i σ hσ hV hex
  choose y hy using GlobalTheory.T.residual_character_det_values_mem_coeff_field T R κ v₀ hI hT i
  obtain ⟨z, hz1, hz⟩ := GlobalTheory.T.rightTranslation_lift_eq_levelMove_unit_const T R κ v₀ O hI hT hpb hO i σ hσ hV
  have hst := GlobalTheory.T.levelMove_stabiliser_character_det T R κ v₀ O hI hT hpb hO i σ hσ hV
  have hmu := muVal_cast hV (hT.laws.muVal _ (inR i) σ hσ)
  have hinj : Function.Injective fun a : T.Q.c.F => D.what₂.embLL (algebraMap T.Q.c.F D.what₂.LL a) :=
    D.what₂.embLL.injective.comp (algebraMap T.Q.c.F D.what₂.LL).injective
  have hy1 : y 1 = 1 := hinj (by
    show D.what₂.embLL _ = D.what₂.embLL _
    have : chiC R i 1 = 1 := by
      have := chiC_mul R i 1 1
      rw [mul_one] at this
      exact left_eq_mul.1 this
    rw [hy, this, map_one, map_one, Units.val_one])
  have hym : ∀ g g', y (g * g') = y g * y g' := fun g g' => hinj (by
    show D.what₂.embLL _ = D.what₂.embLL _
    rw [map_mul, map_mul, hy, hy, hy, chiC_mul, Units.val_mul])
  obtain ⟨c, hc1, hc⟩ := exists_unit_constants (C := Cu T κ i)
    (fun g k => Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k)
    (fun h => (castDict hV (T.dict ((i : ℕ) + 1) σ) h).1) (fun g f => ρ g f)
    (fun f h => rdU (T.U ((i : ℕ) + 1) σ) (f : T.R ((i : ℕ) + 1)) (castDict hV (T.dict ((i : ℕ) + 1) σ) h).1
      (castDict hV (T.dict ((i : ℕ) + 1) σ) h).2)
    (castDict hV (T.mu ((i : ℕ) + 1) σ)) (fun g => σ (y g)) mv z hex
    (fun g g' k k' hk hk' => by
      have := isLift_mul hk hk'
      show Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG (g * g')) _
      rw [map_mul]
      exact this)
    (fun f => by rw [map_one]; rfl) (fun g g' f => by rw [map_mul]; rfl) hmu.1 hmu.2
    (by rw [hy1, map_one]) (fun g g' => by rw [hym, map_mul]) hmv1 hmv hcp hz1
    (fun g k hk f h => by
      have := hz g k hk f f.2 h
      rw [← hρ] at this
      exact this)
    (fun g k hk h hh f => by
      have := hst g k hk (y g) (hy g) h hh f f.2
      rw [phiAt_apply, phiAt_apply, ← hρ, one_mul, one_mul] at this
      exact this)
  refine ⟨c, hc1, fun g k hk f hf => ⟨hkeep g f hf, y g, ?_, fun h => ?_⟩⟩
  · rw [hy, chiC, Units.coe_prod]
  · have := hc g k hk ⟨f, hf⟩ h
    rw [hρ] at this
    rw [phiAt_apply, phiAt_apply]
    exact this

end GlobalTheory.EquivConst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdeleEmbeddingExtensionStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteAdeleEmbeddingExtension : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (l : ℕ) [Fact l.Prime]
    (i : E →+* PadicAlgCl l), ∃ ev : FiniteAdeleRing (𝓞 F) F ⊗[F] E →+* PadicAlgCl l, EvOk i ev := by
  first | exact @GlobalTheory.EvExtend.exists_evOk | exact GlobalTheory.EvExtend.exists_evOk | (intros; apply GlobalTheory.EvExtend.exists_evOk <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleGoodCoverLevelMapStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteEtale_goodCover_levelMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (d : DeltaDat Xo c 0), 1 ≤ Dw.p + Dw.q → d.IsLev →
    ∃ (Z : Scheme.{0}) (π : Z ⟶ Xo.XF c) (z₂ : Z ⟶ d.Xo₂.X), IsFinite π ∧ Etale π ∧ Surjective π ∧
      z₂ ≫ d.r = π ≫ pullback.fst _ _ ∧
      z₂ ≫ d.Xo₂.s = π ≫ pullback.snd _ _ ≫
        spMap ((d.eF.symm : d.c₂.F →+* c.F).comp (IntermediateField.inclusion d.c₂.le).toRingHom) := by
  first | exact @GlobalTheory.CoverGood.exists_good_cover | exact GlobalTheory.CoverGood.exists_good_cover | (intros; apply GlobalTheory.CoverGood.exists_good_cover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsJointRowWeightDualWeylModuleStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_jointRowWeight_dualWeylModule : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ) (Gm : Type) [AddCommGroup Gm] [Module (alg O N lam) Gm], Nontrivial Gm → ∃ w : ι → Fin N → ℕ, GlobalTheory.HighWt.JointWt O N lam Gm w := by
  first | exact @GlobalTheory.HighWt.exists_jointWt | exact GlobalTheory.HighWt.exists_jointWt | (intros; apply GlobalTheory.HighWt.exists_jointWt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftFiniteEtaleSurjectionTestRingStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_finiteEtaleSurjection_testRing : ∀ (Y Z : Scheme.{0}) (π : Z ⟶ Y), IsFinite π → Etale π → Surjective π →
    ∀ (K : Type) [Field K] (p : TRing K) (x : Sp p.R ⟶ Y), ∃ (q : TRing K) (ι : p.R →ₐ[K] q.R),
      (letI := ι.toRingHom.toAlgebra; Module.FaithfullyFlat p.R q.R ∧ Algebra.Etale p.R q.R) ∧
      ∃ z : Sp q.R ⟶ Z, z ≫ π = spMap ι.toRingHom ≫ x := by
  first | exact @GlobalTheory.exists_lift_finiteEtale_testRing | exact GlobalTheory.exists_lift_finiteEtale_testRing | (intros; apply GlobalTheory.exists_lift_finiteEtale_testRing <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsParameterRunWithLawsAndPinsAtSpecialPrimeStatement
section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_parameterRun_with_laws_and_pins_at_special_prime : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Csz : ℝ) (p : PtAt ex Csz), Links2 p → CoreTies L ex.errX p.T (R2 p) → ∀ l : ℕ, (l = D.host.pde ∨ l = D.host.pde') → ∃ r : GlobalTheory.RealIndexBound.RunData p.T, LawsFull r.full ∧ (∀ i : Fin D.R.m, GlobalTheory.FormTies.OneCover r.full.toTop ((i : ℕ) + 1)) ∧ (∀ j n : ℕ, InR D j → (r.full.dδ j n).pd = l) ∧ (∀ i : Fin D.R.m, ∀ γ₀ ∈ Formalism.L2.Theta.GQ (r.full.V ((i : ℕ) + 1) r.full.σ₀), r.full.xi (Matrix.GeneralLinearGroup.det (Formalism.L2.Theta.finHom (r.full.V ((i : ℕ) + 1) r.full.σ₀) γ₀)) = 1) ∧ ∀ v ∈ (R2 p).twPl, ownAt D v = l → ∀ i : Fin D.R.m, letI : Algebra r.full.J.Q.c.F D.what₂.LL := p.alg; RunPin (T := r.full) (R2 p) i (p.κ i).n v (ownAt D v) := by
  first | exact @GlobalTheory.RunOnto.exists_run_pins | exact GlobalTheory.RunOnto.exists_run_pins | (intros; apply GlobalTheory.RunOnto.exists_run_pins <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionOfNumericsModelStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.expansion_of_numerics_model : Formalism.CohomologicalDescent.E.ExCut → NumSt → SumExpSt → ModelSt → ExpSt := by
  first | exact @GlobalTheory.ExpTie.Asm.expSt_of | exact GlobalTheory.ExpTie.Asm.expSt_of | (intros; apply GlobalTheory.ExpTie.Asm.expSt_of <;> assumption)
end

