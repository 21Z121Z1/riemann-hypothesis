import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0279
import Formalism.WachLatticeTwists.LatticeDualFibres.FibreDualStable
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorMemCocyclesPowQuot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0280
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0281
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeOfSpan
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0259
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0282
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0053
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfinitelyManyPrimesInRayClass
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0008
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0192
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachDeltaInvariantCoboundaries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0065
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0051
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCocycleCupNotCoboundaryFiniteLevelStatement
section
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cocycle_cup_not_coboundary_finiteLevel : Formalism.GaloisCohomology.LocalTateDualityK → ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [TopologicalSpace (FractionRing O)] [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)] {VT VT' : Type} [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT] [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT'] [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT'] {G : Type} [Group G] [TopologicalSpace G], FiniteDimensional ℚ_[p] K → IsTopologicalRing O → CompactSpace O → T2Space O → IsAdic (IsLocalRing.maximalIdeal O) → (p : O) ∈ IsLocalRing.maximalIdeal O → (p : O) ≠ 0 → Topology.IsOpenEmbedding (algebraMap O (FractionRing O)) → ∀ (i : G ≃ₜ* Formalism.GaloisCohomology.GK p K) (D : LatData O G VT VT'), (∀ (g : G) (n : ℕ) (ζ : PadicAlgCl p), ζ ^ (p ^ n) = 1 → ∃ a : ℕ, (i g) ζ = ζ ^ a ∧ ((D.ε g : Oˣ) : O) - (a : O) ∈ Ideal.span {(p : O) ^ n}) → IsLatticeIn D.T → PerfectRight D.bT → ContAction D.ρT → IsOpen (D.T : Set VT) → T2Space VT → T2Space VT' → ContinuousConstSMul (FractionRing O) VT → ContinuousConstSMul (FractionRing O) VT' → ∀ ϖ : O, Irreducible ϖ → ∀ c ∈ Z1 D.ρA, c ∉ B1 D.ρA → ∀ r : ℕ, (∀ g, ϖ ^ r • c g = 0) → ∀ n : ℕ, r ≤ n → ∃ z ∈ Z1 (quotRep D.ρTl' ϖ n), cupMod D c ϖ n z ∉ B2 (twist D.ε (KO O)) := by
  first | exact @GlobalTheory.LocDualFin.exists_cocycle_cup_not_cob | exact GlobalTheory.LocDualFin.exists_cocycle_cup_not_cob | (intros; apply GlobalTheory.LocDualFin.exists_cocycle_cup_not_cob <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCyclotomicFrobeniusTwistedValueEqStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cyclotomicFrobeniusTwistedValue_eq : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s e j n : ℕ), 1 ≤ j → j ≤ s → ¬ l ∣ n → ∀ c : Om l, c ∈ K0 K → ‖c‖ ≤ 1 → ∃ (lam : ℕ → ↥(K0 K)) (d : ↥(K0 K)), (∀ a, ‖(lam a : Om l)‖ ≤ 1) ∧ ‖(d : Om l)‖ ≤ 1 ∧ d - (l : ↥(K0 K)) ^ e * frK P K d = (frK P K ^ s) (∑ a ∈ primeTo l s, lam a) ∧ cycVal P K s e lam d = (l : Om l) ^ ((e + 1) * (s - 1)) * (c * P.ζQ j ^ n) := by
  first | exact @GlobalTheory.ExpImage.Values.exists_cycVal_eq | exact GlobalTheory.ExpImage.Values.exists_cycVal_eq | (intros; apply GlobalTheory.ExpImage.Values.exists_cycVal_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrameOfTorsionInvariantsStatement
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frame_of_torsion_invariants : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n) {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA] [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA} (E : EtTie W RA RW inclR φR gR πA) {k : Type} [Field k] [Algebra O k] {Rk : Type} [CommRing Rk] [Algebra k Rk] [Algebra O Rk] [IsScalarTower O k Rk] (ρ : RW →ₐ[O] Rk) (lam : O) (κ : k⸨X⸩ →+* Rk) (a : G → (Rk →ₐ[k] Rk)) (ι : k⸨X⸩ →+* k⸨X⸩) (σ : {δ // δ ∈ W.DelF} → (k⸨X⸩ →+* k⸨X⸩)), IsRed E ρ (k := k) lam κ → IsDel E ρ κ a ι σ → ∀ (T : LocLat G Qp LL O) (A : Ob k G) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)), Onto T A q → ∀ i, (∃ u : Fin A.m → W.DD T, ∀ x, ∃ c : Fin A.m → k⸨X⸩, eps E ρ i • J E ρ T q x = ∑ j, κ (c j) • eps E ρ i • J E ρ T q (u j)) → ∃ β : Vc k A.m →+ Rk ⊗[k] (Fin A.m → k), IsFrame (κ.comp ι) (eps E ρ i) β ∧ ∀ y, (∃ x, β x = y) ↔ ∃ x : ↥(DΔ W T), y = eps E ρ i • J E ρ T q x := by
  first | exact @GlobalTheory.RedFun.exists_frame_of_invariants | exact GlobalTheory.RedFun.exists_frame_of_invariants | (intros; apply GlobalTheory.RedFun.exists_frame_of_invariants <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralDualFunctionalStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_dual_functional : ∀ (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL]
    (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O →
    ∃ (lam : LL →ₗ[ℚ_[l]] ℚ_[l]) (n : ℕ) (e f : Fin n → O),
      (∀ z : ℤ_[l], ∃ o : O, algebraMap O LL o = algebraMap ℚ_[l] LL (z : ℚ_[l])) ∧
      (∀ o : O, ∃ z : ℤ_[l], lam (algebraMap O LL o) = (z : ℚ_[l])) ∧
      (∀ x : LL, x = ∑ i, lam (algebraMap O LL (f i) * x) • algebraMap O LL (e i)) := by
  first | exact @GlobalTheory.IntDual.intDual_coef | exact GlobalTheory.IntDual.intDual_coef | (intros; apply GlobalTheory.IntDual.intDual_coef <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLiftsOfNormLeOneStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lifts_of_norm_le_one_alt : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (c : ↥(K0 K)), ‖(c : Om l)‖ ≤ 1 → ∃ w : Ainf l, Lifts AI K w c := by
  first | exact @GlobalTheory.ExpImage.exists_lifts_of_norm_le_one | exact GlobalTheory.ExpImage.exists_lifts_of_norm_le_one | (intros; apply GlobalTheory.ExpImage.exists_lifts_of_norm_le_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLimitCocycleOfCompatibleModPowStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_limit_cocycle_of_compatible_mod_pow : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O), Irreducible ϖ → ∀ (hI : ∀ n : ℕ, StableSub LA (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T)) (w : ℕ → ↥(GK K) → ↥LA.T), (∀ n, (fun g => (Submodule.Quotient.mk (w n g) : ↥LA.T ⧸ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T))) ∈ quotientCocycles LA _ (hI n)) → (∀ n g, w (n + 1) g - w n g ∈ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T)) → ∃ d ∈ latticeCocycles LA, ∀ n g, ∃ t ∈ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T), d g = (w n g : A.V) + (t : A.V) := by
  first | exact @GlobalTheory.LimCocycle.limit_cocycle | exact GlobalTheory.LimCocycle.limit_cocycle | (intros; apply GlobalTheory.LimCocycle.limit_cocycle <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMonodromyEqLeadingCoeffBreuilKisinDescentStatement
section
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_monodromy_eq_leadingCoeff_breuilKisinDescent : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H) (U : Finset ℤ) (N : ℕ), D.jumps ⊆ U → U ⊆ Finset.Icc (-(η : ℤ)) H → U.card ≤ N + 1 → 1 ≤ η → η < H → 14 * H + (N + 2) * η < l → 10 * H + 2 ≤ l → IsAdicComplete (Ideal.span {(l : O)}) D.Y' → IsHausdorff (Ideal.span {(l : O)}) D.Z → ∀ y ∈ D.Y', ∃ y₀ ∈ D.Y', D.Mon y₀ = D.Lc (D.cls y) := by
  first | exact @GlobalTheory.Proof.exists_monodromy_eq_leadingCoeff_breuilKisinDescent.exists_Mon_eq_Lc_cls | exact GlobalTheory.Proof.exists_monodromy_eq_leadingCoeff_breuilKisinDescent.exists_Mon_eq_Lc_cls | (intros; apply GlobalTheory.Proof.exists_monodromy_eq_leadingCoeff_breuilKisinDescent.exists_Mon_eq_Lc_cls <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMutuallyDualStableLatticesStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mutuallyDual_stable_lattices : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDual1 (P.PD K) A.ρ A'.ρ m → ∃ (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ), IsDualLat1 (P.PD K) LA LA' m ∧ IsDualLat1 (P.PD K) LA' LA m.flip := by
  first | exact @GlobalTheory.StableDual.stable_dual_lattices | exact GlobalTheory.StableDual.stable_dual_lattices | (intros; apply GlobalTheory.StableDual.stable_dual_lattices <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimeAbsNormEqOfIrreducibleCyclotomicStatement
section
open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_prime_absNorm_eq_of_irreducible_cyclotomic' : ∀ (K : Type) [Field K] [NumberField K] (m : ℕ), m.Prime → Irreducible (cyclotomic m K) → ∀ (τ : (ZMod m)ˣ) (S : Set (HeightOneSpectrum (𝓞 K))), S.Finite → ∃ P : HeightOneSpectrum (𝓞 K), P ∉ S ∧ (Ideal.absNorm P.asIdeal).Prime ∧ ((Ideal.absNorm P.asIdeal : ℕ) : ZMod m) = (τ : ZMod m) := by
  first | exact @GlobalTheory.CyclotomicPrimes.exists_prime_absNorm_eq_of_irreducible_cyclotomic | exact GlobalTheory.CyclotomicPrimes.exists_prime_absNorm_eq_of_irreducible_cyclotomic | (intros; apply GlobalTheory.CyclotomicPrimes.exists_prime_absNorm_eq_of_irreducible_cyclotomic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsReductionTeichmullerEmbeddingAtLocalisatioStatement
section
open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_reduction_teichmullerEmbedding_at_localisation : ∀ (D : D7) (i : D.nd.Loc) (k : Fin 2), D.nd.l i ≠ D.host.g k → ∃ ι : Fb (D.host.g k) (D.host.g_prime k) →* Formalism.CyclotomicNorms.Fbar (D.nd.l i), InjPrimeTo (D.nd.l i) ι ∧ RedVia D i k ι := by
  first | exact @GlobalTheory.TypeLeaf.exists_redVia | exact GlobalTheory.TypeLeaf.exists_redVia | (intros; apply GlobalTheory.TypeLeaf.exists_redVia <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSubstInvariants
section
open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.SenLines GlobalTheory.IndefiniteRowSideFullHecke.DiagonalQuotientEigen GlobalTheory.CycFr GlobalTheory.WachTie

namespace GlobalTheory.SenLines

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) {l : ℕ}

theorem isUnit_q_of_associated {m : ℕ} (h : Associated W.π₀₁ (X ^ m)) :
    IsUnit (algebraMap (LetA O n) W.EE (W.π₀ + ((PD.p : ℕ) : LetA O n))) := by
  obtain ⟨w, hw⟩ := h.symm
  have e : (W.π₀ : LetA O n) = letπ ^ m * fun _ => (w : O⟦X⟧) := funext fun _ => hw.symm
  have hu : IsUnit (algebraMap (LetA O n) W.EE W.π₀) := by
    rw [e, map_mul, map_pow]
    exact (W.EE_π.pow _).mul (IsUnit.map _ (Pi.isUnit_iff.2 fun _ => w.isUnit))
  haveI := W.EE_complete
  have hJ := IsAdicComplete.le_jacobson_bot (Ideal.span {((PD.p : ℕ) : W.EE)})
    (Ideal.mem_span_singleton_self _)
  obtain ⟨u, hu⟩ := hu
  have h1 := (Ideal.mem_jacobson_bot.1 hJ (↑u⁻¹ : W.EE)).mul u.isUnit
  rw [map_add, map_natCast, ← hu]
  convert h1 using 1
  rw [add_mul, mul_assoc, Units.inv_mul]; ring

variable [Fact l.Prime] [IsDomain O] [CharZero O] [Algebra ℤ_[l] O] (hp : PD.p = l)
  (χ : W.Gam →* ℤ_[l]ˣ) (hχ : ∀ g, algebraMap ℤ_[l] O (χ g : ℤ_[l]) = (W.χΓ g : O))
include hp hχ

theorem exists_subst_invariants (ξ : O⟦X⟧) (hξ : Associated ξ (X ^ W.DelF.card))
    (h0 : constantCoeff ξ = 0) (hinv : ∀ δ ∈ W.DelF, W.γ₀ δ ξ = ξ) :
    ∃ j : O⟦X⟧ →ₐ[O] O⟦X⟧, j X = ξ ∧ Function.Injective j ∧
      ∀ a, (∃ b, j b = a) ↔ ∀ δ ∈ W.DelF, W.γ₀ δ a = a := by
  classical
  have hγ := γ₀_eq W hp χ hχ
  have hχi : Function.Injective χ := fun a b hab =>
    W.χΓ_inj (Units.ext (by rw [← hχ, ← hχ, hab]))
  let Δ : Subgroup ℤ_[l]ˣ := (CommGroup.torsion W.Gam).map χ
  have hΔ : (Δ : Set ℤ_[l]ˣ) = ↑(W.DelF.image χ) := by
    ext x
    simp only [Δ, Subgroup.coe_map, Set.mem_image, SetLike.mem_coe, CommGroup.mem_torsion,
      Finset.coe_image, Finset.mem_coe, mem_DelF_iff]
  have hfa : ∀ p : ℤ_[l]ˣ → Prop, (∀ δ ∈ Δ, p δ) ↔ ∀ δ ∈ W.DelF, p (χ δ) := by
    intro p
    simp only [← SetLike.mem_coe, hΔ, Finset.coe_image, Set.forall_mem_image]
  haveI : Finite Δ := by
    change Finite (Δ : Set ℤ_[l]ˣ)
    rw [hΔ]; infer_instance
  have hcard : Nat.card Δ = W.DelF.card := by
    change Nat.card (Δ : Set ℤ_[l]ˣ) = _
    rw [hΔ, Nat.card_coe_set_eq, Set.ncard_coe_finset, Finset.card_image_of_injective _ hχi]
  have hs : HasSubst ξ := HasSubst.of_constantCoeff_zero' h0
  have hX : (substAlgHom hs : O⟦X⟧ →ₐ[O] O⟦X⟧) X = ξ := by rw [coe_substAlgHom, subst_X hs]
  obtain ⟨h2, h3⟩ := injective_and_range_eq_invariants Δ (substAlgHom hs : O⟦X⟧ →ₐ[O] O⟦X⟧)
    (by rw [hX, hcard]; exact hξ)
    ((hfa _).2 fun δ hδ => by rw [← hγ, hX]; exact hinv δ hδ)
  refine ⟨_, hX, h2, fun a => ?_⟩
  rw [h3, hfa]; simp only [hγ]

theorem exists_qFrame_of_card [IsNoetherianRing O] (hl : l ≠ 2) (hc : W.DelF.card = l - 1)
    (σ : O⟦X⟧ ≃ₐ[O] O⟦X⟧) (hσ : σ X = X + C (l : O)) (g : W.Gam)
    (hg : (l : ℤ_[l]) ∣ (χ g : ℤ_[l]) - 1) : ∃ J, QFrame W g J := by
  have h2l := (Fact.out : l.Prime).two_le
  have hl0 : (l : O) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  obtain ⟨p2, p3, w, hw⟩ := π₀₁_spec W hp χ hχ hl hc
  have hq := (φ₀_eq W hp).2
  have hγ := γ₀_eq W hp χ hχ
  have hX0 : (X : O⟦X⟧) ∣ W.π₀₁ := (dvd_pow_self _ (by omega)).trans p2.symm.dvd
  have h0 := X_dvd_iff.1 hX0
  obtain ⟨j, hj, hji, hjr⟩ := exists_subst_invariants W hp χ hχ _ p2 h0 p3
  let J : O⟦X⟧ →ₐ[O] O⟦X⟧ := j.comp σ
  have hJ : ∀ c, J c = j (σ c) := fun _ => rfl
  have hσ' : σ X = X + (l : O⟦X⟧) := by rw [hσ, map_natCast]
  have hJX : J X = W.π₀₁ + (l : O⟦X⟧) := by rw [hJ, hσ', map_add, hj, map_natCast]
  have hσl : σ (X - (l : O⟦X⟧)) = X := by rw [map_sub, hσ', map_natCast]; ring
  have hr : ∀ a, (∃ b, J b = a) ↔ ∀ δ ∈ W.DelF, W.γ₀ δ a = a := fun a => by
    rw [← hjr]
    exact ⟨fun ⟨b, hb⟩ => ⟨σ b, hb⟩, fun ⟨b, hb⟩ => ⟨σ.symm b, by rw [hJ, σ.apply_symm_apply, hb]⟩⟩
  have hk : ∀ c, constantCoeff (J c) = 0 → X - (l : O⟦X⟧) ∣ c := fun c h => by
    rw [hJ, constantCoeff_algHom j (hj ▸ hX0)] at h
    rw [← map_dvd_iff σ, hσl, X_dvd_iff, h]
  have hc0 : constantCoeff (J X) = (l : O) := by rw [hJX, map_add, h0, map_natCast, zero_add]
  have hwu : IsUnit w := by
    have h1 := congrArg constantCoeff hw
    rw [← hJX, hc0, map_mul, show constantCoeff (lvl l O 0) = (l : O) by simp [lvl]] at h1
    rw [isUnit_iff_constantCoeff, ← mul_left_cancel₀ hl0 ((mul_one _).trans h1)]
    exact isUnit_one
  have hass : Associated (J X) (lvl l O 0) := by
    rw [hJX, hw]; exact associated_mul_unit_left _ _ hwu
  have hne : J X ≠ 0 := fun h => hl0 (by rw [← hc0, h, map_zero])
  obtain ⟨y, hy⟩ : J X * X ∣ W.γ₀ g (J X) - J X := by
    have h1 := dvd_act_sub (O := O) 1 (χ g) 1 (by rwa [pow_one]) (J X)
    have h2 := mul_lvl (l := l) (O := O) 0
    rw [pow_zero, pow_one, add_sub_cancel_left, zero_add] at h2
    rw [act_one, ← hγ, ← h2, mul_comm] at h1
    exact (mul_dvd_mul_right hass.dvd _).trans h1
  have hinv := (hr (J X)).1 ⟨X, rfl⟩
  obtain ⟨y', hy'⟩ := (hr (X * y)).2 fun δ hδ => by
    apply mul_left_cancel₀ hne
    have h1 := congrArg (W.γ₀ δ) hy
    rw [mul_assoc, map_mul, map_sub, hinv δ hδ, hγ δ, hγ g, act_comm, ← hγ δ, hinv δ hδ,
      ← hγ g, hy, mul_assoc] at h1
    exact h1.symm
  obtain ⟨z, hz⟩ := hk y' (by rw [hy']; simp)
  have hs : IsUnit (1 + y') := by
    rw [← MulEquiv.isUnit_map σ, hz, map_add, map_mul, hσl, isUnit_iff_constantCoeff]
    simp
  refine ⟨J, hji.comp σ.injective, hr, by rw [hp, hJX], by rw [hp]; exact hk,
    ⟨hs.unit, ?_, ?_⟩, hq ▸ hass, isUnit_q_of_associated W p2⟩
  · rw [hs.unit_spec, map_add, map_one, hy']
    linear_combination hy
  · rw [hp, hs.unit_spec, add_sub_cancel_left]
    exact ⟨z, hz⟩

end Generic

theorem exists_qFrame : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) {n : ℕ} (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) n) (g : W.Gam), CaseA K LL → ((W.χΓ g : (↥(OL LL))ˣ) : ↥(OL LL)) = 1 + (l : ↥(OL LL)) → IsUnit (W.DelF.card : ↥(OL LL)) ∧ ∃ J, QFrame W g J := by
  intro l _ P K LL n W g ⟨hK, hl, h⟩ hg
  have p1 : Module.finrank ↥(K0 K) ↥K.1 = 1 := by
    rw [Algebra.finrank_eq_one_iff_bijective_algebraMap]
    exact ⟨(algebraMap ↥(K0 K) ↥K.1).injective, fun x => ⟨⟨x.1, x.2, hK x.2⟩, rfl⟩⟩
  have hc := GlobalTheory.TorsionCard.card_torsion_mul_finrank P K LL W hl h.2.2.1
  rw [p1, mul_one] at hc
  obtain ⟨χ, hχ, -⟩ := GlobalTheory.exists_cyclotomicChar_padicInt_units P K LL W
  obtain ⟨_, _, hu⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
  obtain ⟨σ, hσ⟩ := GlobalTheory.NB.LT.exists_algEquiv_X_add_C (IsLocalRing.maximalIdeal ↥(OL LL))
    (l : ↥(OL LL)) hu
  refine ⟨?_, exists_qFrame_of_card W (P.PD_p K) χ hχ hl hc σ hσ g ?_⟩
  · have h1 := IsLocalRing.isUnit_or_isUnit_one_sub_self (l : ↥(OL LL))
    rw [hc, Nat.cast_sub (Fact.out : l.Prime).one_le, Nat.cast_one, ← IsUnit.neg_iff, neg_sub]
    exact h1.resolve_left hu
  · have h1 : (χ g : ℤ_[l]) = 1 + l := GlobalTheory.algebraMap_padicInt_OL_injective LL (by
      rw [hχ, hg, map_add, map_one, map_natCast])
    rw [h1, add_sub_cancel_left]

end GlobalTheory.SenLines
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTorsionModuleExtendingResidueMaps
section
open CategoryTheory GlobalTheory.SelFun

namespace GlobalTheory.SelFun

theorem exists_factor_of_injective {Λ : Type} [CommRing Λ] {X Y J : Type} [AddCommGroup X] [Module Λ X]
    [AddCommGroup Y] [Module Λ Y] [AddCommGroup J] [Module Λ J] (hJ : Module.Injective Λ J)
    (g : X →ₗ[Λ] Y) (ψ : X →ₗ[Λ] J) (h : LinearMap.ker g ≤ LinearMap.ker ψ) :
    ∃ u : Y →ₗ[Λ] J, ∀ x, u (g x) = ψ x := by
  have hi : Function.Injective ((LinearMap.ker g).liftQ g le_rfl) := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ le_rfl
  obtain ⟨u, hu⟩ := hJ.out ((LinearMap.ker g).liftQ g le_rfl) hi ((LinearMap.ker g).liftQ ψ h)
  refine ⟨u, fun x => ?_⟩
  simpa using hu (Submodule.Quotient.mk x)

def powTorsion {Λ : Type} [CommRing Λ] (I : Ideal Λ) (J : Type) [AddCommGroup J] [Module Λ J] : Submodule Λ J where
  carrier := {b | ∃ n : ℕ, ∀ x ∈ I ^ n, x • b = 0}
  zero_mem' := ⟨0, fun x _ => smul_zero x⟩
  add_mem' := by
    rintro a b ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨n + m, fun x hx => ?_⟩
    rw [smul_add, hn x (Ideal.pow_le_pow_right (Nat.le_add_right n m) hx),
      hm x (Ideal.pow_le_pow_right (Nat.le_add_left m n) hx), add_zero]
  smul_mem' := by
    rintro c a ⟨n, hn⟩
    exact ⟨n, fun x hx => by rw [smul_comm, hn x hx, smul_zero]⟩

theorem residue_smul_eq_zero {Λ : Type} [CommRing Λ] [IsLocalRing Λ] (x : Λ) (hx : x ∈ IsLocalRing.maximalIdeal Λ)
    (a : IsLocalRing.ResidueField Λ) : x • a = 0 := by
  rw [Algebra.smul_def, IsLocalRing.ResidueField.algebraMap_eq, (IsLocalRing.residue_eq_zero_iff x).2 hx, zero_mul]

theorem exists_torsion_extension (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] (P : Type) [AddCommGroup P]
    [Module Λ P] [Module.Finite Λ P] (N : Submodule Λ P) :
    ∃ (B : ModuleCat.{0} Λ) (f : IsLocalRing.ResidueField Λ →ₗ[Λ] B), Tors Λ B ∧ Function.Injective f ∧
      ∀ φ : N →ₗ[Λ] IsLocalRing.ResidueField Λ, ∃ u : P →ₗ[Λ] B, u ∘ₗ N.subtype = f ∘ₗ φ := by
  let k := ModuleCat.of Λ (IsLocalRing.ResidueField Λ)
  let J := Injective.under k
  let ι : IsLocalRing.ResidueField Λ →ₗ[Λ] J := (Injective.ι k).hom
  have hι : Function.Injective ι := (ModuleCat.mono_iff_injective (Injective.ι k)).1 inferInstance
  have hJ : Module.Injective Λ J := Module.injective_module_of_injective_object Λ J (inj := Injective.injective_under k)
  let m := IsLocalRing.maximalIdeal Λ
  have hmem : ∀ a, ι a ∈ powTorsion m J := fun a =>
    ⟨1, fun x hx => by rw [← map_smul, residue_smul_eq_zero x (by rwa [pow_one] at hx), map_zero]⟩
  refine ⟨ModuleCat.of Λ (powTorsion m J), ι.codRestrict _ hmem, ?_, ?_, ?_⟩
  · rintro ⟨b, n, hn⟩
    exact ⟨n, fun x hx => Subtype.ext (hn x hx)⟩
  · intro a b hab
    exact hι (congrArg Subtype.val hab)
  · intro φ
    obtain ⟨n, hn⟩ := Ideal.exists_pow_inf_eq_pow_smul m N
    have h1 := hn (n + 1) (Nat.le_succ n)
    rw [Nat.add_sub_cancel_left, pow_one] at h1
    let K : Submodule Λ P := m ^ (n + 1) • ⊤
    have hK : K ⊓ N ≤ m • N := by
      rw [show K ⊓ N = _ from h1]
      exact Submodule.smul_mono le_rfl inf_le_right
    have hker : LinearMap.ker (K.mkQ ∘ₗ N.subtype) ≤ LinearMap.ker (ι ∘ₗ φ) := by
      intro y hy
      have hy1 : (y : P) ∈ K := by simpa using hy
      have hy2 : (y : P) ∈ m • N := hK ⟨hy1, y.2⟩
      have hy3 : y ∈ (m • ⊤ : Submodule Λ N) := by
        rwa [Submodule.mem_smul_top_iff]
      have : φ y = 0 := by
        refine Submodule.smul_induction_on (p := fun y => φ y = 0) hy3 ?_ ?_
        · intro r hr z _
          rw [map_smul, residue_smul_eq_zero r hr]
        · intro a b ha hb
          rw [map_add, ha, hb, add_zero]
      simp [this]
    obtain ⟨u, hu⟩ := exists_factor_of_injective hJ _ _ hker
    have hu2 : ∀ p, (u ∘ₗ K.mkQ) p ∈ powTorsion m J := fun p =>
      ⟨n + 1, fun x hx => by
        rw [← map_smul]
        have : K.mkQ (x • p) = 0 :=
          (Submodule.Quotient.mk_eq_zero K).2 (Submodule.smul_mem_smul hx Submodule.mem_top)
        rw [LinearMap.comp_apply, this, map_zero]⟩
    refine ⟨(u ∘ₗ K.mkQ).codRestrict _ hu2, ?_⟩
    ext y
    exact hu y

end GlobalTheory.SelFun
end

