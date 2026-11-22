import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0683
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0659
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0684
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Definitions.ThetaValues.MemAnalyticAtZeroOfEventuallyDifferentiableAt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothEtaleOfSmoothInChartsStatement
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_and_smoothR_of_contDiffAt_in_charts : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (U : Set Y) (z : Y → V n), Etale A U z → (∀ u : Y → ℂ, (∀ x ∈ U, ∃ i, x ∈ (A.chart i).source ∧ ContDiffAt ℝ ∞ (u ∘ (A.chart i).symm) (A.chart i x)) → Smooth n (fun y : U => z y) (fun y : U => u y)) ∧ (∀ φ : Y → ℝ, (∀ x ∈ U, ∃ i, x ∈ (A.chart i).source ∧ ContDiffAt ℝ ∞ (φ ∘ (A.chart i).symm) (A.chart i x)) → SmoothR n (fun y : U => z y) (fun y : U => φ y)) := by
  first | exact @GlobalTheory.OTY.smooth_etale_of_smooth_in_charts | exact GlobalTheory.OTY.smooth_etale_of_smooth_in_charts | (intros; apply GlobalTheory.OTY.smooth_etale_of_smooth_in_charts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothSectionCutoffMulHolomorphicStatement
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothSection_cutoff_mul_holomorphic : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (la : La) (W : Set Y) (χ : Y → ℝ) (h : ι → Y → ℂ), IsOpen W → A.SmoothFn χ → tsupport χ ⊆ W → A.IsSecOn la W h → A.IsSSec la (fun i y => (χ y : ℂ) * h i y) := by
  first | exact @GlobalTheory.smooth_cutoff_mul_sec | exact GlobalTheory.smooth_cutoff_mul_sec | (intros; apply GlobalTheory.smooth_cutoff_mul_sec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonInvariantDifferentialsOfEtale
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

namespace PDivGroup

theorem subsingleton_omega_of_isEt : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (G : PDivGroup p k), G.IsEt → Subsingleton G.omega ∧ Subsingleton G.dual.dual.omega := by
  intro p _ k _ _ _ G hG
  have hp : (p : k) = 0 := CharP.cast_eq_zero k p
  have h1 : Subsingleton G.omega := by
    refine ⟨fun v w => ?_⟩
    have hz : ∀ u : G.omega, u = 0 := fun u => Subtype.ext (funext fun n => by
      haveI := hG n
      obtain ⟨a, ha⟩ := AugCot.d_surjective _ (u.1 n)
      obtain ⟨b, rfl⟩ := GlobalTheory.T.exists_pow_char_eq_of_isReduced_finite' p k (G.A n) a
      rw [← ha]
      exact dUnit_pow_prime hp b)
    rw [hz v, hz w]
  refine ⟨h1, ?_⟩
  have hinj : Function.Injective (omegaMap G G.dual.dual G.bidual.hom) := by
    refine Function.LeftInverse.injective (g := omegaMap G.dual.dual G G.bidual.inv) fun x => ?_
    rw [← LinearMap.comp_apply, ← omegaMap_comp, Iso.inv_hom_id, omegaMap_id, LinearMap.id_apply]
  exact hinj.subsingleton

end PDivGroup

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstFormalGroupLawNatMultipleEqCoboundarySumStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subst_formalGroupLawNatMultiple_eq_coboundary_sum : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) → ∀ (g : MvPowerSeries (Fin d) R) (n : ℕ), subst (nmul μ n) g = C (constantCoeff g) + (n : R) • g + ∑ k ∈ Finset.range n, at2 (cob1 μ g) (nmul μ k) (fun i => X i) := by
  first | exact @GlobalTheory.QLog.subst_nmul_eq | exact GlobalTheory.QLog.subst_nmul_eq | (intros; apply GlobalTheory.QLog.subst_nmul_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupEqTopOfLeMaximal
section
open NumberField

namespace GlobalTheory.PrimesAboveExistence

theorem sup_eq_top_of_le_maximal {R : Type} [CommRing R] {A B I : Ideal R}
    (h : ∀ M : Ideal R, M.IsMaximal → B ≤ M → A ≤ M) (hA : I ⊔ A = ⊤) : I ⊔ B = ⊤ := by
  by_contra hne

  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  have hAM : A ≤ M := h M hM (le_sup_right.trans hle)
  exact hM.ne_top (top_le_iff.mp (hA ▸ sup_le (le_sup_left.trans hle) hAM))

theorem exists_primes_above {F : Type} [Field F] [NumberField F] (l : ℕ) (hl : Nat.Prime l) :
    ∃ P : Finset (Ideal (𝓞 F)),
      (∀ 𝔭 ∈ P, Ideal.IsMaximal 𝔭 ∧ 𝔭 ≠ ⊥ ∧ l ∣ (Ideal.absNorm : Ideal (𝓞 F) → ℕ) 𝔭) ∧
      ∀ I : Ideal (𝓞 F), Formalism.MainNotions.ShortIntervalPrimes.CoprimeTo F (∏ 𝔭 ∈ P, 𝔭) I ↔
        Formalism.MainNotions.ShortIntervalPrimes.CoprimeTo F (Ideal.span {(l : 𝓞 F)}) I := by
  classical
  set L : Ideal (𝓞 F) := Ideal.span {(l : 𝓞 F)} with hL
  have hL0 : L ≠ ⊥ := by
    rw [hL, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hl.ne_zero

  refine ⟨(UniqueFactorizationMonoid.normalizedFactors L).toFinset, ?_, ?_⟩
  · intro 𝔭 h𝔭
    rw [Multiset.mem_toFinset, Ideal.mem_normalizedFactors_iff hL0] at h𝔭
    obtain ⟨hp, hle⟩ := h𝔭
    have hne : 𝔭 ≠ ⊥ := fun h => hL0 (le_bot_iff.mp (h ▸ hle))
    have hmax : 𝔭.IsMaximal := hp.isMaximal hne
    refine ⟨hmax, hne, ?_⟩

    have hdvd : Ideal.absNorm 𝔭 ∣ l ^ Module.finrank ℤ (𝓞 F) := by
      have h := Ideal.absNorm_dvd_absNorm_of_le hle
      rwa [hL, Ideal.absNorm_span_singleton,
        show (l : 𝓞 F) = algebraMap ℤ (𝓞 F) (l : ℤ) by simp,
        Algebra.norm_algebraMap, Int.natAbs_pow, Int.natAbs_natCast] at h
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hl).mp hdvd
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hmax.ne_top (Ideal.absNorm_eq_one_iff.mp (by simpa using hk))
    change l ∣ Ideal.absNorm 𝔭
    rw [hk]
    exact dvd_pow_self l hk0
  · intro I
    unfold Formalism.MainNotions.ShortIntervalPrimes.CoprimeTo
    refine and_congr_right fun _ =>
      ⟨fun h => sup_eq_top_of_le_maximal ?_ h, fun h => sup_eq_top_of_le_maximal ?_ h⟩
    ·
      intro M hM hLM
      have hmem : M ∈ (UniqueFactorizationMonoid.normalizedFactors L).toFinset := by
        rw [Multiset.mem_toFinset, Ideal.mem_normalizedFactors_iff hL0]
        exact ⟨hM.isPrime, hLM⟩
      exact Ideal.le_of_dvd (Finset.dvd_prod_of_mem (fun 𝔭 => 𝔭) hmem)
    ·
      intro M hM hPM
      obtain ⟨𝔭, h𝔭, hle⟩ := (Ideal.IsPrime.prod_le hM.isPrime).mp hPM
      rw [Multiset.mem_toFinset, Ideal.mem_normalizedFactors_iff hL0] at h𝔭
      have hne : 𝔭 ≠ ⊥ := fun h => hL0 (le_bot_iff.mp (h ▸ h𝔭.2))
      have h𝔭M : 𝔭 = M := (h𝔭.1.isMaximal hne).eq_of_le hM.ne_top hle
      exact h𝔭M ▸ h𝔭.2

end GlobalTheory.PrimesAboveExistence
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectivePullHO2OfPullHO1Statement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.surjective_pullHO2_of_pullHO1 : ∀ (R R' : Type) [CommRing R] [CommRing R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (σ : R →+* R') (φ : X' ⟶ X) (h : φ ≫ s = s' ≫ spMap σ), Function.Surjective (pullHO1 h) → WedgeO (OAff s') → Function.Surjective (pullHO2 h) := by
  first | exact @GlobalTheory.AbCoh.pullHO2_surjective_of_wedge | exact GlobalTheory.AbCoh.pullHO2_surjective_of_wedge | (intros; apply GlobalTheory.AbCoh.pullHO2_surjective_of_wedge <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapVariableGroupsFormalGroupLawCoboundaryOneComStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.swapVariableGroups_formalGroupLawCoboundaryOne_comm : ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), (∀ i, constantCoeff (μ i) = 0) → (∀ i, swap (μ i) = μ i) → ∀ g : MvPowerSeries (Fin d) Q, swap (cob1 (up Q μ) g) = cob1 (up Q μ) g := by
  first | exact @GlobalTheory.CobSwap.swap_cob1_eq_of_swap_eq | exact GlobalTheory.CobSwap.swap_cob1_eq_of_swap_eq | (intros; apply GlobalTheory.CobSwap.swap_cob1_eq_of_swap_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricCocycleAdditiveEqCoboundaryAdd
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.SymCocAdd

variable {R : Type} [CommRing R] {d : ℕ}

theorem subst_zeroPt {σ τ : Type} [Finite σ] (f : MvPowerSeries σ R) :
    subst (fun _ : σ => (0 : MvPowerSeries τ R)) f = C (constantCoeff f) := by
  classical
  have hs : HasSubst (fun _ : σ => (0 : MvPowerSeries τ R)) :=
    hasSubst_of_constantCoeff_zero fun _ => map_zero _
  ext e
  rw [coeff_subst hs, finsum_eq_single _ 0]
  · rw [Finsupp.prod_zero_index, coeff_zero_eq_constantCoeff_apply, coeff_C, coeff_one, smul_eq_mul]
    split_ifs <;> simp
  · intro dd hdd
    obtain ⟨s, hs'⟩ := Finsupp.ne_iff.1 hdd
    have hmem : s ∈ dd.support := Finsupp.mem_support_iff.2 (by simpa using hs')
    rw [Finsupp.prod, Finset.prod_eq_zero hmem (zero_pow (Finsupp.mem_support_iff.1 hmem)), map_zero,
      smul_zero]

theorem hs2 {τ : Type} {u v : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) : HasSubst (Sum.elim u v) :=
  hasSubst_of_constantCoeff_zero fun s => by cases s <;> simp [hu, hv]

theorem subst_powerSeriesEvalTwoGroups {τ τ' : Type} [Finite τ] {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0)
    {a : τ → MvPowerSeries τ' R} (ha : ∀ t, constantCoeff (a t) = 0)
    (c : MvPowerSeries (Fin d ⊕ Fin d) R) :
    subst a (at2 c u v) = at2 c (fun i => subst a (u i)) (fun i => subst a (v i)) := by
  unfold at2
  rw [subst_comp_subst_apply (hs2 hu hv) (hasSubst_of_constantCoeff_zero ha)]
  congr 1
  funext s
  cases s <;> rfl

theorem powerSeriesEvalTwoGroups_X {τ : Type} {u v : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) (s : Fin d ⊕ Fin d) :
    at2 (X s) u v = Sum.elim u v s := by
  unfold at2
  rw [subst_X (hs2 hu hv)]

theorem op_addLaw {τ : Type} {u v : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) : op (addLaw R d) u v = u + v := by
  funext i
  unfold op addLaw at2
  rw [subst_add (hs2 hu hv), subst_X (hs2 hu hv), subst_X (hs2 hu hv)]
  rfl

end GlobalTheory.SymCocAdd

namespace GlobalTheory.SymCocAdd

variable {R : Type} [CommRing R] {d : ℕ}

theorem coc_at {τ : Type} [Finite τ] {c : MvPowerSeries (Fin d ⊕ Fin d) R}
    (hc : cob2 (addLaw R d) c = 0) {u v w : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0)
    (hw : ∀ i, constantCoeff (w i) = 0) :
    at2 c v w - at2 c (u + v) w + at2 c u (v + w) - at2 c u v = 0 := by
  set a : Fin d ⊕ (Fin d ⊕ Fin d) → MvPowerSeries τ R := Sum.elim u (Sum.elim v w) with ha_def
  have ha0 : ∀ t, constantCoeff (a t) = 0 := fun t => by
    rcases t with t | t | t <;> simp [a, hu, hv, hw]
  have ha : HasSubst a := hasSubst_of_constantCoeff_zero ha0
  have h1 : ∀ i, constantCoeff ((x1 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0 :=
    fun i => by simp [x1]
  have h2 : ∀ i, constantCoeff ((x2 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0 :=
    fun i => by simp [x2]
  have h3 : ∀ i, constantCoeff ((x3 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0 :=
    fun i => by simp [x3]
  have e1 : (fun i => subst a ((x1 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i)) = u := by
    funext i; simp only [x1]; rw [subst_X ha]; rfl
  have e2 : (fun i => subst a ((x2 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i)) = v := by
    funext i; simp only [x2]; rw [subst_X ha]; rfl
  have e3 : (fun i => subst a ((x3 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i)) = w := by
    funext i; simp only [x3]; rw [subst_X ha]; rfl
  have hadd : ∀ p q : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R,
      (fun i => subst a ((p + q) i)) = (fun i => subst a (p i)) + (fun i => subst a (q i)) := by
    intro p q; funext i; simp only [Pi.add_apply]; rw [subst_add ha]
  have h12 : ∀ i, constantCoeff ((x1 + x2 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0 :=
    fun i => by simp [h1, h2]
  have h23 : ∀ i, constantCoeff ((x2 + x3 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0 :=
    fun i => by simp [h2, h3]
  have key := congrArg (subst a) hc
  unfold cob2 at key
  rw [op_addLaw h1 h2, op_addLaw h2 h3] at key
  rw [subst_sub ha, subst_add ha, subst_sub ha, subst_powerSeriesEvalTwoGroups h2 h3 ha0, subst_powerSeriesEvalTwoGroups h12 h3 ha0,
    subst_powerSeriesEvalTwoGroups h1 h23 ha0, subst_powerSeriesEvalTwoGroups h1 h2 ha0, hadd, hadd, e1, e2, e3] at key
  rw [key, ← coe_substAlgHom ha, map_zero]

end GlobalTheory.SymCocAdd

namespace GlobalTheory.SymCocAdd

variable {R : Type} [CommRing R] {d : ℕ}

variable (R d) in

def PtGrp (τ : Type) : AddSubgroup (Fin d → MvPowerSeries τ R) where
  carrier := {u | ∀ i, constantCoeff (u i) = 0}
  zero_mem' := fun i => by simp
  add_mem' := fun {u v} hu hv i => by simp [hu i, hv i]
  neg_mem' := fun {u} hu i => by simp [hu i]

theorem sum_single_apply {M : Type} [AddCommMonoid M] (s : Finset (Fin d)) (w : Fin d → M) (i : Fin d) :
    (∑ j ∈ s, Pi.single j (w j) : Fin d → M) i = if i ∈ s then w i else 0 := by
  classical
  rw [Finset.sum_apply]
  simp only [Pi.single_apply]
  rw [Finset.sum_ite_eq]

theorem subst_sum_single {τ : Type} {a : Fin d → MvPowerSeries τ R} (ha : ∀ t, constantCoeff (a t) = 0)
    (s : Finset (Fin d)) :
    (fun i => subst a ((∑ j ∈ s, Pi.single j (X j) : Fin d → MvPowerSeries (Fin d) R) i)) =
      ∑ j ∈ s, Pi.single j (a j) := by
  have hS : HasSubst a := hasSubst_of_constantCoeff_zero ha
  funext i
  rw [sum_single_apply, sum_single_apply]
  split_ifs
  · exact subst_X hS i
  · rw [← coe_substAlgHom hS, map_zero]

theorem cc_sum_single {τ : Type} (s : Finset (Fin d)) (w : Fin d → MvPowerSeries τ R)
    (hw : ∀ j, constantCoeff (w j) = 0) (i : Fin d) :
    constantCoeff ((∑ j ∈ s, Pi.single j (w j) : Fin d → MvPowerSeries τ R) i) = 0 := by
  rw [sum_single_apply]; split_ifs <;> simp [hw]

end GlobalTheory.SymCocAdd

namespace GlobalTheory.SymCocAdd

variable {R : Type} [CommRing R] {d : ℕ}

theorem subst_single {τ : Type} {a : Fin d → MvPowerSeries τ R} (ha : ∀ t, constantCoeff (a t) = 0)
    (m : Fin d) :
    (fun i => subst a ((Pi.single m (X m) : Fin d → MvPowerSeries (Fin d) R) i)) = Pi.single m (a m) := by
  classical
  have hS : HasSubst a := hasSubst_of_constantCoeff_zero ha
  funext i
  rw [Pi.single_apply, Pi.single_apply]
  split_ifs with h
  · subst h; exact subst_X hS i
  · rw [← coe_substAlgHom hS, map_zero]

variable (R) in

def corr (c : MvPowerSeries (Fin d ⊕ Fin d) R) : MvPowerSeries (Fin d) R :=
  ∑ m : Fin d, at2 c (∑ j ∈ Finset.univ.filter (· < m), Pi.single j (X j))
    (Pi.single m (X m) : Fin d → MvPowerSeries (Fin d) R)

theorem subst_corr {τ : Type} {a : Fin d → MvPowerSeries τ R} (ha : ∀ t, constantCoeff (a t) = 0)
    (c : MvPowerSeries (Fin d ⊕ Fin d) R) :
    subst a (corr R c) = ∑ m : Fin d, at2 c (∑ j ∈ Finset.univ.filter (· < m), Pi.single j (a j))
      (Pi.single m (a m)) := by
  classical
  have hS : HasSubst a := hasSubst_of_constantCoeff_zero ha
  unfold corr
  rw [← coe_substAlgHom hS, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coe_substAlgHom hS, subst_powerSeriesEvalTwoGroups (cc_sum_single _ _ (fun j => by simp))
    (fun i => by rw [Pi.single_apply]; split_ifs <;> simp) ha, subst_sum_single ha, subst_single ha]

end GlobalTheory.SymCocAdd

namespace GlobalTheory

open GlobalTheory.SymCocAdd in

theorem symmetricCocycle_additive_eq_coboundary_add_alt (R : Type) [CommRing R] (d : ℕ) (c : MvPowerSeries (Fin d ⊕ Fin d) R)
    (hc : IsCoc (addLaw R d) c) (h0 : constantCoeff c = 0) :
    ∃ b : MvPowerSeries (Fin d) R, c = cob1 (addLaw R d) b +
      ∑ m : Fin d, at2 c (Pi.single m (X (Sum.inl m) : MvPowerSeries (Fin d ⊕ Fin d) R))
        (Pi.single m (X (Sum.inr m))) := by
  classical
  let τ := Fin d ⊕ Fin d
  let A := PtGrp R d τ
  let γ : A → A → MvPowerSeries τ R := fun u v => at2 c u.1 v.1
  have hsymm : ∀ u v, γ u v = γ v u := by
    intro u v
    have hX1 : ∀ i, constantCoeff ((fun i => (X (Sum.inr i) : MvPowerSeries τ R)) i) = 0 :=
      fun i => by simp
    have hX2 : ∀ i, constantCoeff ((fun i => (X (Sum.inl i) : MvPowerSeries τ R)) i) = 0 :=
      fun i => by simp
    have huv : ∀ t, constantCoeff (Sum.elim u.1 v.1 t) = 0 := fun t => by
      cases t with
      | inl t => exact u.2 t
      | inr t => exact v.2 t
    have := subst_powerSeriesEvalTwoGroups hX1 hX2 huv c
    change at2 (swap c) u.1 v.1 = _ at this
    rw [hc.2] at this
    simp only [γ]
    rw [this]
    have hS : HasSubst (Sum.elim u.1 v.1) := hasSubst_of_constantCoeff_zero huv
    congr 1 <;> funext i <;> rw [subst_X hS] <;> rfl
  have hcoc : ∀ x y z : A, γ y z - γ (x + y) z + γ x (y + z) - γ x y = 0 :=
    fun x y z => coc_at hc.1 x.2 y.2 z.2
  have hzero : γ 0 0 = 0 := by
    simp only [γ]
    unfold at2
    have : Sum.elim ((0 : A) : Fin d → MvPowerSeries τ R) ((0 : A) : Fin d → MvPowerSeries τ R) =
        fun _ => 0 := by funext t; cases t <;> rfl
    rw [this, subst_zeroPt, h0, map_zero]
  let x : Fin d → A := fun m => ⟨Pi.single m (X (Sum.inl m)), fun i => by
    rw [Pi.single_apply]; split_ifs <;> simp⟩
  let y : Fin d → A := fun m => ⟨Pi.single m (X (Sum.inr m)), fun i => by
    rw [Pi.single_apply]; split_ifs <;> simp⟩
  have key := GlobalTheory.T.symmCocycle_apply_finset_sum A (MvPowerSeries τ R) γ hsymm hcoc hzero d x y
  have coeA : ∀ (s : Finset (Fin d)) (f : Fin d → A),
      ((∑ j ∈ s, f j : A) : Fin d → MvPowerSeries τ R) = ∑ j ∈ s, (f j : Fin d → MvPowerSeries τ R) :=
    fun s f => map_sum A.subtype f s
  have hL : γ (∑ m, x m) (∑ m, y m) = c := by
    simp only [γ]
    rw [coeA, coeA]
    simp only [x, y]
    rw [Finset.univ_sum_single (fun m => (X (Sum.inl m) : MvPowerSeries τ R)),
      Finset.univ_sum_single (fun m => (X (Sum.inr m) : MvPowerSeries τ R))]
    unfold at2
    have : Sum.elim (fun m => (X (Sum.inl m) : MvPowerSeries τ R)) (fun m => X (Sum.inr m)) = X := by
      funext t; cases t <;> rfl
    rw [this, subst_self]; rfl
  have hT : ((∑ m, γ (∑ j ∈ Finset.univ.filter (· < m), (x j + y j)) (x m + y m)) -
      (∑ m, γ (∑ j ∈ Finset.univ.filter (· < m), x j) (x m)) -
      ∑ m, γ (∑ j ∈ Finset.univ.filter (· < m), y j) (y m)) = cob1 (addLaw R d) (corr R c) := by
    unfold cob1 inL inR
    rw [subst_corr (fun i => by simp [addLaw]), subst_corr (fun i => by simp),
      subst_corr (fun i => by simp)]
    simp only [γ, coeA]
    simp only [x, y, AddSubgroup.coe_add, ← Pi.single_add]
    rfl
  refine ⟨corr R c, ?_⟩
  calc c = γ (∑ m, x m) (∑ m, y m) := hL.symm
    _ = _ := key
    _ = _ := by rw [hT, add_comm]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentEqZeroOfFormalGroupLawCoboundaryOneEqZeroStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_eq_zero_of_formalGroupLawCoboundaryOne_eq_zero : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (f : MvPowerSeries (Fin d) C), constantCoeff f = 0 → cob1 (up C c.μ) f = 0 → c.IsLie f 0 := by
  first | exact @GlobalTheory.QLog.Chart.isLie_zero_of_cob1_eq_zero | exact GlobalTheory.QLog.Chart.isLie_zero_of_cob1_eq_zero | (intros; apply GlobalTheory.QLog.Chart.isLie_zero_of_cob1_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorRemainderIsBigOAndTaylorFlat
section
open Filter Topology

namespace GlobalTheory.PeriodFamily

theorem taylor_eq_partialSum {I : Type} [Fintype I] [DecidableEq I] (N : ℕ) {f : (I → ℂ) → ℂ}
    {p : FormalMultilinearSeries ℂ (I → ℂ) ℂ} (hp : HasFPowerSeriesAt f p 0) (z : I → ℂ) :
    taylor N z f = p.partialSum (N + 1) z := by
  obtain ⟨r, hr⟩ := hp
  unfold taylor FormalMultilinearSeries.partialSum
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have h1 := hr.factorial_smul z k
  have hk : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 k.factorial_ne_zero
  have h2 : (iteratedFDeriv ℂ k f 0 fun _ ↦ z) =
      ∑ s : Fin k → I, (∏ a, z (s a)) • iteratedFDeriv ℂ k f 0 fun a ↦ Pi.single (s a) 1 := by
    have hz : (fun _ : Fin k ↦ z) = fun _ ↦ ∑ i, z i • (Pi.single i (1 : ℂ) : I → ℂ) := by
      funext a j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hz, ContinuousMultilinearMap.map_sum]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [ContinuousMultilinearMap.map_smul_univ]
  rw [h2, nsmul_eq_mul] at h1
  rw [← inv_mul_cancel_left₀ hk (p k fun _ ↦ z), h1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  simp only [smul_eq_mul]
  ring

theorem diag_eq_zero_of_isBigO {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (N : ℕ) {f : E → ℂ}
    {p : FormalMultilinearSeries ℂ E ℂ} (hp : HasFPowerSeriesAt f p 0)
    (hf : f =O[𝓝 0] fun z : E ↦ ‖z‖ ^ (N + 1)) (k : ℕ) : k ≤ N → ∀ y, (p k fun _ ↦ y) = 0 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    have h1 := hp.isBigO_sub_partialSum_pow (k + 1)
    have hs : ∀ y, p.partialSum (k + 1) y = p k fun _ ↦ y := by
      intro y
      rw [FormalMultilinearSeries.partialSum, Finset.sum_range_succ,
        Finset.sum_eq_zero fun j hj ↦ ih j (Finset.mem_range.1 hj)
          (le_trans (Finset.mem_range.1 hj).le hk) y, zero_add]
    have h2 : (fun z : E ↦ ‖z‖ ^ (N + 1)) =O[𝓝 0] fun z : E ↦ ‖z‖ ^ (k + 1) := by
      refine Asymptotics.IsBigO.of_bound 1 ?_
      filter_upwards [Metric.closedBall_mem_nhds (0 : E) one_pos] with z hz
      rw [one_mul, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
      exact pow_le_pow_of_le_one (norm_nonneg _) (by simpa using hz) (by omega)
    have h3 : (fun y : E ↦ p k fun _ ↦ y) =O[𝓝 0] fun z : E ↦ ‖z‖ ^ (k + 1) := by
      refine ((hf.trans h2).sub h1).congr_left fun y ↦ ?_
      simp [hs]
    exact h3.continuousMultilinearMap_apply_eq_zero

theorem iteratedFDeriv_eq_zero_of_isBigO {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (N : ℕ)
    {f : E → ℂ} (ha : AnalyticAt ℂ f 0) (hf : f =O[𝓝 0] fun z : E ↦ ‖z‖ ^ (N + 1)) {k : ℕ} (hk : k ≤ N)
    (v : Fin k → E) : iteratedFDeriv ℂ k f 0 v = 0 := by
  obtain ⟨p, hp⟩ := ha
  have h := diag_eq_zero_of_isBigO N hp hf k hk
  obtain ⟨r, hr⟩ := hp
  rw [hr.iteratedFDeriv_eq_sum_of_completeSpace, ← (p k).iteratedFDeriv_comp_diagonal 0 v]
  simp [h]

theorem taylor_remainder_and_flat : ∀ {I : Type} [Fintype I] [DecidableEq I] (N : ℕ) (f : (I → ℂ) → ℂ), AnalyticAt ℂ f 0 → ((fun z ↦ f z - GlobalTheory.PeriodFamily.taylor N z f) =O[𝓝 0] fun z : I → ℂ ↦ ‖z‖ ^ (N + 1)) ∧ ((f =O[𝓝 0] fun z : I → ℂ ↦ ‖z‖ ^ (N + 1)) → ∀ {D : Type} [CommRing D] [Algebra ℂ D] (t : I → D), GlobalTheory.PeriodFamily.taylor N t f = 0) := by
  intro I _ _ N f ha
  refine ⟨?_, fun hf D _ _ t ↦ ?_⟩
  · obtain ⟨p, hp⟩ := ha
    refine (hp.isBigO_sub_partialSum_pow (N + 1)).congr_left fun z ↦ ?_
    rw [taylor_eq_partialSum N hp, zero_add]
  · unfold taylor
    refine Finset.sum_eq_zero fun k hk ↦ Finset.sum_eq_zero fun s _ ↦ ?_
    rw [iteratedFDeriv_eq_zero_of_isBigO N ha hf (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)), mul_zero,
      zero_smul]

end GlobalTheory.PeriodFamily
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorProjectiveDvdOfCoordDvdStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eq_smul_of_dvd_dualDistrib : ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (N : Type) [AddCommGroup N] [Module O N] [Module.Projective O M] [Module.Projective O N] (a : O) (z : M ⊗[O] N), (∀ (φ : Module.Dual O M) (ψ : Module.Dual O N), a ∣ TensorProduct.dualDistrib O M N (φ ⊗ₜ ψ) z) → ∃ y, z = a • y := by
  first | exact @GlobalTheory.tensor_projective_dvd_of_coord_dvd | exact GlobalTheory.tensor_projective_dvd_of_coord_dvd | (intros; apply GlobalTheory.tensor_projective_dvd_of_coord_dvd <;> assumption)
end

