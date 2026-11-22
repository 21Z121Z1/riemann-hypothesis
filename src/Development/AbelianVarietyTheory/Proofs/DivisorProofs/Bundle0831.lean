import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0812
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeightedNormSquareRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0777
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0813
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0656
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfP
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.VanishAtSStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0026
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0028
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0019
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0814
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0776
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0797
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmPeriodEqTangentHodgeTate
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModFFiniteIdeleUpToExtension
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.UpIdeleMod

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (finiteCompletionMap finiteCompletionMap_coe finiteCompletionMap_mapsTo)

variable {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]

omit [NumberField K] in

theorem valued_algebraMap {R : Type} [CommRing R] [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K]
    (v : HeightOneSpectrum R) (k : K) :
    Valued.v (algebraMap K (v.adicCompletion K) k) = v.valuation K k :=
  HeightOneSpectrum.adicCompletion.valued_coe K v k

theorem valued_finiteCompletionMap (w : HeightOneSpectrum (𝓞 E)) (x : (w.under (𝓞 K)).adicCompletion K) :
    Valued.v (finiteCompletionMap K E w x) =
      Valued.v x ^ ((w.under (𝓞 K)).asIdeal.ramificationIdx' w.asIdeal) := by
  have he : (w.under (𝓞 K)).asIdeal.ramificationIdx' w.asIdeal ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal (w.under (𝓞 K)).ne_bot
  rcases eq_or_ne x 0 with rfl | hx
  · rw [map_zero, map_zero, map_zero, zero_pow he]
  have hx0 : Valued.v x ≠ 0 := by simpa using hx
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer K (w.under (𝓞 K))
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  set m := WithZero.log (Valued.v x)
  set k : K := π ^ (-m)
  have hvk : (w.under (𝓞 K)).valuation K k = Valued.v x := by
    rw [map_zpow₀, hπ, ← WithZero.exp_zsmul]
    simp only [smul_eq_mul, neg_mul_neg, mul_one]
    exact WithZero.exp_log hx0
  set c : (w.under (𝓞 K)).adicCompletion K := algebraMap K _ k
  have hc : Valued.v c = Valued.v x := (valued_algebraMap (w.under (𝓞 K)) k).trans hvk
  have hc0 : c ≠ 0 := fun h => hx0 (by rw [← hc, h, map_zero])
  set u := x * c⁻¹
  have hu0 : u ≠ 0 := mul_ne_zero hx (inv_ne_zero hc0)
  have hu : Valued.v u = 1 := by
    rw [map_mul, map_inv₀, hc, mul_inv_cancel₀ hx0]
  have hu1 : u ∈ (w.under (𝓞 K)).adicCompletionIntegers K := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hu]
  have hu2 : u⁻¹ ∈ (w.under (𝓞 K)).adicCompletionIntegers K := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hu, inv_one]
  have a1 := finiteCompletionMap_mapsTo K E w hu1
  have a2 := finiteCompletionMap_mapsTo K E w hu2
  simp only [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers] at a1 a2
  have hfu : Valued.v (finiteCompletionMap K E w u) = 1 := by
    have hprod : finiteCompletionMap K E w u * finiteCompletionMap K E w u⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hu0, map_one]
    have h3 := congrArg Valued.v hprod
    rw [map_mul, map_one] at h3
    exact eq_one_of_one_le_mul_left a1 a2 h3.ge
  have hxu : x = u * c := by
    simp only [u, mul_assoc, inv_mul_cancel₀ hc0, mul_one]
  conv_lhs => rw [hxu, map_mul, map_mul, hfu, one_mul, finiteCompletionMap_coe, valued_algebraMap,
    ← HeightOneSpectrum.valuation_liesOver E (w.under (𝓞 K)) w k, hvk]

theorem factor_upIdele (t : (Af K)ˣ) (w : HeightOneSpectrum (𝓞 E)) :
    ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ WithZero.log (Valued.v ((upIdele K E t : Af E) w)) =
      (((Ideal.absNorm (w.under (𝓞 K)).asIdeal : ℕ) : ℝ) ^
          WithZero.log (Valued.v ((t : Af K) (w.under (𝓞 K))))) ^
        (w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K)) := by
  haveI := w.isMaximal
  haveI := (w.under (𝓞 K)).isMaximal
  have h1 : ((upIdele K E t : Af E) w) = finiteCompletionMap K E w ((t : Af K) (w.under (𝓞 K))) := rfl
  rw [h1, valued_finiteCompletionMap, WithZero.log_pow,
    Ideal.ramificationIdx'_eq_ramificationIdx _ _ (w.under (𝓞 K)).ne_bot,
    Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver w.asIdeal (w.under (𝓞 K)).asIdeal (w.under (𝓞 K)).isPrime
      (w.under (𝓞 K)).ne_bot,
    Ideal.inertiaDeg'_eq_inertiaDeg]
  push_cast
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul]
  congr 1
  rw [nsmul_eq_mul]
  push_cast
  ring

open Classical in

theorem sum_fiber (v : HeightOneSpectrum (𝓞 K)) (s : Finset (HeightOneSpectrum (𝓞 E)))
    (hs : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 K) = v → w ∈ s) :
    ∑ w ∈ s with w.under (𝓞 K) = v, w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K) =
      Module.finrank K E := by
  rw [IsFractionRing.finrank_eq (𝓞 K) K (𝓞 E) E, ← Ideal.sum_ramification_inertia_eq_finrank v.asIdeal (𝓞 E)]
  refine Finset.sum_bij'
    (fun w hw => (⟨w.asIdeal, w.isPrime, by
      rw [← (Finset.mem_filter.mp hw).2]
      exact GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under K E w⟩ : v.asIdeal.primesOver (𝓞 E)))
    (fun q _ => (⟨q.1, q.2.1, by
      haveI := q.2.2
      exact Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot q.1⟩ : HeightOneSpectrum (𝓞 E)))
    (fun _ _ => Finset.mem_univ _) (fun q _ => ?_) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
  have hq : (⟨q.1, q.2.1, by
      haveI := q.2.2
      exact Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot q.1⟩ : HeightOneSpectrum (𝓞 E)).under (𝓞 K) = v :=
    HeightOneSpectrum.ext q.2.2.over.symm
  exact Finset.mem_filter.mpr ⟨hs _ hq, hq⟩

theorem modF_upIdele (t : (Af K)ˣ) : modF (upIdele K E t) = modF t ^ Module.finrank K E := by
  classical
  set a : HeightOneSpectrum (𝓞 K) → ℝ := fun v =>
    ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ WithZero.log (Valued.v ((t : Af K) v)) with ha
  have hfin : {v : HeightOneSpectrum (𝓞 K) | ¬ Valued.v ((t : Af K) v) = 1}.Finite :=
    Filter.eventually_cofinite.mp (FiniteAdeleRing.isUnit_iff.mp t.isUnit).2
  have hT : ((fun w : HeightOneSpectrum (𝓞 E) => w.under (𝓞 K)) ⁻¹'
      {v : HeightOneSpectrum (𝓞 K) | ¬ Valued.v ((t : Af K) v) = 1}).Finite := by
    have h2 := Filter.mem_cofinite.mp (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under K E hfin.compl_mem_cofinite)
    rwa [Set.preimage_compl, compl_compl] at h2
  set S := hfin.toFinset
  set T := hT.toFinset
  have haS : ∀ v, v ∉ S → a v = 1 := fun v hv => by
    have h3 : Valued.v ((t : Af K) v) = 1 := by
      by_contra h
      exact hv (hfin.mem_toFinset.mpr h)
    simp only [ha, h3, WithZero.log_one, zpow_zero]
  have h1 : modF t = ∏ v ∈ S, a v := by
    refine finprod_eq_prod_of_mulSupport_subset a fun v hv => ?_
    by_contra h
    exact hv (haS v h)
  have h2 : modF (upIdele K E t) = ∏ w ∈ T, a (w.under (𝓞 K)) ^
      (w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K)) := by
    unfold modF
    rw [finprod_congr (factor_upIdele t)]
    refine finprod_eq_prod_of_mulSupport_subset _ fun w hw => ?_
    by_contra h
    apply hw
    have h4 : w.under (𝓞 K) ∉ S := fun h5 => h (hT.mem_toFinset.mpr (hfin.mem_toFinset.mp h5))
    show a (w.under (𝓞 K)) ^ _ = 1
    rw [haS _ h4, one_pow]
  rw [h2, h1, ← Finset.prod_fiberwise_of_maps_to (s := T) (t := S) (g := fun w => w.under (𝓞 K))
    (fun w hw => hfin.mem_toFinset.mpr (hT.mem_toFinset.mp hw)), ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun v hv => ?_
  rw [Finset.prod_congr rfl (g := fun w => a v ^ (w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K)))
      (fun w hw => by rw [(Finset.mem_filter.mp hw).2]),
    Finset.prod_pow_eq_pow_sum, sum_fiber v T fun w hw => hT.mem_toFinset.mpr (by
      show w.under (𝓞 K) ∈ {v : HeightOneSpectrum (𝓞 K) | ¬ Valued.v ((t : Af K) v) = 1}
      rw [hw]; exact hfin.mem_toFinset.mp hv)]

end GlobalTheory.UpIdeleMod
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpNormAtPairingSqLeOfValueBoundStatement
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.opNormAt_pairing_sq_le_of_value_bound : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (c n : ℕ) (X : InfinitePlace K → Matrix (Fin c) (Fin c) ℂ) (X0 : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (g : (Fin c → K) →ₗ[K] Module.Dual K (Fin n → K)) (v : InfinitePlace K) (A : ℝ), IsUnit (X v).det → IsUnit (X0 v).det → (∀ y F, v (g y F) ^ 2 ≤ Real.exp A * Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin c)) X v y ^ 2 * Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) X0 v F ^ 2) → Formalism.HN.opNormAt (Pi.basisFun K (Fin c)) X (Pi.basisFun K (Fin n)).dualBasis (Formalism.HN.dualFrame X0) v g ^ 2 ≤ Real.exp A := by
  first | exact @GlobalTheory.PairingOpNorm.opNormAt_pairing_sq_le | exact GlobalTheory.PairingOpNorm.opNormAt_pairing_sq_le | (intros; apply GlobalTheory.PairingOpNorm.opNormAt_pairing_sq_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicIntegersHenselianFiniteResidueStatement
section
open IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padicIntegers_henselian_finiteResidue : ∀ (v : HeightOneSpectrum ℤ), HenselianLocalRing (v.adicCompletionIntegers ℚ) ∧ Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) := by
  first | (exact @GlobalTheory.IntAdicHensel.henselianLocalRing_and_finite_residueField) | (exact GlobalTheory.IntAdicHensel.henselianLocalRing_and_finite_residueField) | (intros; apply GlobalTheory.IntAdicHensel.henselianLocalRing_and_finite_residueField <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialFreeResolutionsHomotopyEquivalentStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partialFreeResolutions_homotopyEquivalent : ∀ (O : Type) [CommRing O] (N : Type) [AddCommGroup N] [Module O N] (F₀ : Type) [AddCommGroup F₀] [Module O F₀] [Module.Free O F₀] [Module.Finite O F₀] (F₁ : Type) [AddCommGroup F₁] [Module O F₁] [Module.Free O F₁] [Module.Finite O F₁] (F₂ : Type) [AddCommGroup F₂] [Module O F₂] [Module.Free O F₂] [Module.Finite O F₂] (F₃ : Type) [AddCommGroup F₃] [Module O F₃] [Module.Free O F₃] [Module.Finite O F₃] (G₀ : Type) [AddCommGroup G₀] [Module O G₀] [Module.Free O G₀] [Module.Finite O G₀] (G₁ : Type) [AddCommGroup G₁] [Module O G₁] [Module.Free O G₁] [Module.Finite O G₁] (G₂ : Type) [AddCommGroup G₂] [Module O G₂] [Module.Free O G₂] [Module.Finite O G₂] (ε : F₀ →ₗ[O] N) (d₁ : F₁ →ₗ[O] F₀) (d₂ : F₂ →ₗ[O] F₁) (d₃ : F₃ →ₗ[O] F₂) (ν : G₀ →ₗ[O] N) (e₁ : G₁ →ₗ[O] G₀) (e₂ : G₂ →ₗ[O] G₁), Function.Surjective ε → Function.Exact d₁ ε → Function.Exact d₂ d₁ → Function.Exact d₃ d₂ → Function.Surjective ν → Function.Exact e₁ ν → Function.Exact e₂ e₁ → ∃ (a₀ : F₀ →ₗ[O] G₀) (a₁ : F₁ →ₗ[O] G₁) (a₂ : F₂ →ₗ[O] G₂) (b₀ : G₀ →ₗ[O] F₀) (b₁ : G₁ →ₗ[O] F₁) (b₂ : G₂ →ₗ[O] F₂) (h₀ : F₀ →ₗ[O] F₁) (h₁ : F₁ →ₗ[O] F₂) (h₂ : F₂ →ₗ[O] F₃) (k₀ : G₀ →ₗ[O] G₁) (k₁ : G₁ →ₗ[O] G₂), e₁ ∘ₗ a₁ = a₀ ∘ₗ d₁ ∧ e₂ ∘ₗ a₂ = a₁ ∘ₗ d₂ ∧ d₁ ∘ₗ b₁ = b₀ ∘ₗ e₁ ∧ d₂ ∘ₗ b₂ = b₁ ∘ₗ e₂ ∧ LinearMap.id - b₁ ∘ₗ a₁ = d₂ ∘ₗ h₁ + h₀ ∘ₗ d₁ ∧ LinearMap.id - b₂ ∘ₗ a₂ = d₃ ∘ₗ h₂ + h₁ ∘ₗ d₂ ∧ LinearMap.id - a₁ ∘ₗ b₁ = e₂ ∘ₗ k₁ + k₀ ∘ₗ e₁ := by
  first | exact @GlobalTheory.resolutions_homotopy_equivalent | exact GlobalTheory.resolutions_homotopy_equivalent | (intros; apply GlobalTheory.resolutions_homotopy_equivalent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PchernOfStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pChern_neg_one : GlobalTheory.AnPer.PChern (-1) := by
  first | exact @GlobalTheory.AnPer.ChernClause.pchern | exact GlobalTheory.AnPer.ChernClause.pchern | (intros; apply GlobalTheory.AnPer.ChernClause.pchern <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeakExtensionVanishOtherOrbitPoints
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory
  Topology Filter Metric
open scoped ENNReal

noncomputable section

namespace GlobalTheory.PeakOrbit

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem rank_pos (X : Data E r) (hn : 0 < nd X) : 0 < r := by
  obtain ⟨e⟩ : Nonempty (Ent X) := Fintype.card_pos_iff.1 hn
  exact Fin.pos e.2.1.1

theorem isOrth_translate (X : Data E r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {x : Frame X.Ψ r}
    (ho : IsOrth X x) : IsOrth X (lact γ x) := fun τ => by
  rw [OntoS.gram_lact X hγ]; exact ho τ

def testFn (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (Ψ : Frame X.Ψ r → ℝ≥0∞)
    (y : Frame X.Ψ r) : ℝ≥0∞ := by
  classical
  exact ENNReal.ofReal (‖X.dom.piecewise P 0 y‖ ^ 2 * Real.exp (-(X.dom.piecewise (phla X la) 0 y))) * Ψ y

theorem testFn_dom (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (Ψ : Frame X.Ψ r → ℝ≥0∞)
    {y : Frame X.Ψ r} (hy : y ∈ X.dom) :
    testFn X la P Ψ y = ENNReal.ofReal (‖P y‖ ^ 2 * Real.exp (-phla X la y)) * Ψ y := by
  classical
  simp only [testFn, Set.piecewise_eq_of_mem _ _ _ hy]

theorem testFn_meas (X : Data E r) (la : Wt X.Ψ r) {P : Frame X.Ψ r → ℂ} (hP : ContinuousOn P X.dom)
    {Ψ : Frame X.Ψ r → ℝ≥0∞} (hΨ : Measurable Ψ) : Measurable (testFn X la P Ψ) := by
  classical
  have hm := (IW.isOpen_dom X).measurableSet
  have h1 : Measurable (X.dom.piecewise P 0) := hP.measurable_piecewise continuousOn_const hm
  have h2 : Measurable (X.dom.piecewise (phla X la) 0) :=
    (IW.phla_contOn X la).measurable_piecewise continuousOn_const hm
  unfold testFn
  exact ((h1.norm.pow_const 2).mul (h2.neg.exp)).ennreal_ofReal.mul hΨ

theorem testFn_rmul (X : Data E r) {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ} (hP : IsBEq X la P)
    {Ψ : Frame X.Ψ r → ℝ≥0∞} (hΨ : ∀ y ∈ X.dom, ∀ b ∈ Bor X.Ψ r, Ψ (rmul y b) = Ψ y)
    {y : Frame X.Ψ r} (hy : y ∈ X.dom) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) :
    testFn X la P Ψ (rmul y b) = testFn X la P Ψ y := by
  rw [testFn_dom X la P Ψ (OntoS.dom_rmul X hy hb), testFn_dom X la P Ψ hy,
    IW.exp_neg_phla_rmul X GlobalTheory.NormFactor.nfacRmul_holds la hy hb, hP.2 y hy b hb, hΨ y hy b hb]
  congr 2
  have : ‖bchar la b‖ ≠ 0 := norm_ne_zero_iff.2 (IW.bchar_ne_zero X hb la)
  rw [norm_mul]
  field_simp

theorem vanish_translate : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (x : Frame X.Ψ r), IsOrth X x → 0 < nd X →
    ∀ (Ψ : Frame X.Ψ r → ℝ≥0∞), Measurable Ψ → (∀ y ∈ X.dom, ∀ b ∈ Bor X.Ψ r, Ψ (rmul y b) = Ψ y) →
    (∀ γ ∈ X.Γ, ∀ y ∈ X.dom, Ψ (lact γ y) = Ψ y) → ∀ (c ρ' : ℝ), 0 < c → 0 < ρ' →
    (∀ w ∈ Metric.ball (0 : V (nd X)) ρ',
      ENNReal.ofReal (c * ‖w‖ ^ (-(2 * (nd X : ℝ)))) ≤ Ψ (cpt X x w)) →
    (∀ γ ∈ X.Γ, ∀ z z' : V (nd X), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ‖z'‖ ≤ 1 / (100 * (r : ℝ) ^ 2) →
      ∀ b ∈ Bor X.Ψ r, lact γ (cpt X x z) = rmul (cpt X x z') b → γ = 1) →
    ∀ (F0 F : V (nd X) → ℂ), (∀ z, 1 / (100 * (r : ℝ) ^ 2) < ‖z‖ → F0 z = 0) →
    DifferentiableOn ℂ F (OmF X x) →
    ∫⁻ z, ENNReal.ofReal (‖F0 z - F z‖ ^ 2 * Real.exp (-phla X la (cpt X x z))) * Ψ (cpt X x z)
      ∂muF X x < ⊤ →
    ∀ P : Frame X.Ψ r → ℂ, IsBEq X la P → (∀ z ∈ OmF X x, P (cpt X x z) = F z) →
    ∀ γ ∈ X.Γ, γ ≠ 1 → P (lact γ x) = 0 := by
  intro E _ _ _ r X la x ho hn Ψ hΨm hΨB hΨΓ c ρ' hc hρ' hlow hinj F0 F hF0 _ hI P hP hPF γ hγ hγ1
  by_contra hne
  have hr : (0 : ℝ) < r := Nat.cast_pos.2 (rank_pos X hn)
  have hR : (0 : ℝ) < 1 / (100 * (r : ℝ) ^ 2) := by positivity
  set x1 := lact γ x with hx1def
  have ho1 : IsOrth X x1 := isOrth_translate X hγ ho
  have h01 := IW.zero_mem_OmF X x1 ho1
  have hO1 := (ExF.isOpen_OmF X x1).mem_nhds h01
  have hO := (ExF.isOpen_OmF X x).mem_nhds (IW.zero_mem_OmF X x ho)

  set h : V (nd X) → ℝ := fun w => Real.exp (Real.log (densF X x1 w) - phla X la (cpt X x1 w)) *
    ‖P (cpt X x1 w)‖ ^ 2 with hh
  have hcont : ContinuousAt h 0 :=
    (Real.continuous_exp.continuousAt.comp (((IW.logDens_cdAt X x1 h01).sub
      (IW.phla_cpt_cdAt X x1 h01 la)).continuousAt)).mul
      (((IW.comp_cpt_diffOn X hP.1 x1).continuousOn.continuousAt hO1).norm.pow 2)
  have hh0 : 0 < h 0 := by
    simp only [hh, IW.cpt_zero]
    exact mul_pos (Real.exp_pos _) (pow_pos (norm_pos_iff.2 hne) 2)
  have hev : ∀ᶠ w in 𝓝 (0 : V (nd X)), h 0 / 2 < h w :=
    hcont.eventually (lt_mem_nhds (by linarith))
  have hall : ∀ᶠ w in 𝓝 (0 : V (nd X)), h 0 / 2 < h w ∧ w ∈ OmF X x1 ∧ w ∈ OmF X x ∧
      w ∈ ball (0 : V (nd X)) ρ' ∧ w ∈ ball (0 : V (nd X)) (1 / (100 * (r : ℝ) ^ 2)) := by
    filter_upwards [hev, hO1, hO, ball_mem_nhds 0 hρ', ball_mem_nhds 0 hR] with w a b c d e
    exact ⟨a, b, c, d, e⟩
  obtain ⟨ρ, hρ, hsub⟩ := Metric.mem_nhds_iff.1 hall
  obtain ⟨Δ, zOf, bOf, hΔd, -, hzOf, -, hdec, hlast⟩ := lu_holds (E := E) r X x1 ho1
  have hG : IsOpen {y | y ∈ X.dom ∧ Δ y ≠ 0} :=
    hΔd.continuous.continuousOn.isOpen_inter_preimage (IW.isOpen_dom X) isOpen_compl_singleton
  have hNo : IsOpen (IW.Nset X Δ zOf ρ) := hzOf.continuousOn.isOpen_inter_preimage hG isOpen_ball
  have hN1 : ∀ w ∈ ball (0 : V (nd X)) ρ, cpt X x1 w ∈ IW.Nset X Δ zOf ρ := by
    intro w hw
    have hwO := (hsub hw).2.1
    obtain ⟨h1, h2, -⟩ := hlast w hwO (IW.idF X) (IW.idF_mem X)
    rw [IW.rmul_idF] at h1 h2
    exact ⟨⟨hwO, h1⟩, by simp only [Set.mem_preimage]; rw [h2]; exact hw⟩
  have hN2 : ∀ z, cpt X x z ∈ IW.Nset X Δ zOf ρ → z ∈ OmF X x ∧ F0 z = 0 := by
    intro z hzN
    obtain ⟨⟨hzd, hΔz⟩, hzb⟩ := hzN
    refine ⟨hzd, hF0 z (lt_of_not_ge fun hz => hγ1 ?_)⟩
    obtain ⟨-, hbO, hd⟩ := hdec _ hzd hΔz
    have e := IW.rmul_binv X (cpt X x1 (zOf (cpt X x z))) hbO
    rw [← hd, hx1def, IW.cpt_lact] at e
    have hw := (hsub hzb).2.2.2.2
    rw [mem_ball, dist_zero_right] at hw
    exact hinj γ hγ _ z hw.le hz _ (IW.binv_mem X hbO) e.symm
  have hφm : Measurable ((IW.Nset X Δ zOf ρ).indicator (testFn X la P Ψ)) :=
    (testFn_meas X la hP.1.continuousOn hΨm).indicator hNo.measurableSet
  have hφinv : ∀ y ∈ X.dom, ∀ b ∈ Bor X.Ψ r,
      (IW.Nset X Δ zOf ρ).indicator (testFn X la P Ψ) (rmul y b) =
        (IW.Nset X Δ zOf ρ).indicator (testFn X la P Ψ) y := by
    intro y hy b hb
    by_cases hyN : y ∈ IW.Nset X Δ zOf ρ
    · rw [Set.indicator_of_mem hyN,
        Set.indicator_of_mem ((IW.Nset_sat X x1 hdec hlast ρ hy hb).2 hyN),
        testFn_rmul X hP hΨB hy hb]
    · rw [Set.indicator_of_notMem hyN, Set.indicator_of_notMem
        (fun h => hyN ((IW.Nset_sat X x1 hdec hlast ρ hy hb).1 h))]
  have hMI := measInv_holds (E := E) r X x x1 ho ho1 _ hφm hφinv
  have hL : ∫⁻ z, (IW.Nset X Δ zOf ρ).indicator (testFn X la P Ψ) (cpt X x z) ∂muF X x < ⊤ := by
    refine lt_of_le_of_lt (lintegral_mono fun z => ?_) hI
    by_cases hzN : cpt X x z ∈ IW.Nset X Δ zOf ρ
    · obtain ⟨hz, hz0⟩ := hN2 z hzN
      have hzd : cpt X x z ∈ X.dom := hz
      rw [Set.indicator_of_mem hzN, testFn_dom X la P Ψ hzd, hPF z hz, hz0, zero_sub, norm_neg]
    · rw [Set.indicator_of_notMem hzN]; exact zero_le
  have hk : 0 < h 0 / 2 * c := by positivity
  have hpt : ∀ w ∈ ball (0 : V (nd X)) ρ, ENNReal.ofReal (h 0 / 2 * c) *
      ENNReal.ofReal (‖w‖ ^ (-2 * (nd X : ℝ))) ≤
      ENNReal.ofReal (densF X x1 w) * (IW.Nset X Δ zOf ρ).indicator (testFn X la P Ψ) (cpt X x1 w) := by
    intro w hw
    obtain ⟨h1, hw1, hw0, hwρ, -⟩ := hsub hw
    have hd := IW.densF_pos X x1 hw1
    have hwd : cpt X x1 w ∈ X.dom := hw1
    have hΨw : Ψ (cpt X x1 w) = Ψ (cpt X x w) := by
      rw [hx1def, IW.cpt_lact]; exact hΨΓ γ hγ _ hw0
    have hval : h w = densF X x1 w * (‖P (cpt X x1 w)‖ ^ 2 * Real.exp (-phla X la (cpt X x1 w))) := by
      simp only [hh]
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hd]
      ring
    rw [Set.indicator_of_mem (hN1 w hw), testFn_dom X la P Ψ hwd, hΨw, ← mul_assoc,
      ← ENNReal.ofReal_mul hd.le, ← hval, ← ENNReal.ofReal_mul hk.le, mul_assoc,
      ENNReal.ofReal_mul (by positivity), neg_mul]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal h1.le) (hlow w hwρ)
  have hR1 : ENNReal.ofReal (h 0 / 2 * c) *
      ∫⁻ w in ball (0 : V (nd X)) ρ, ENNReal.ofReal (‖w‖ ^ (-2 * (nd X : ℝ))) ≤
      ∫⁻ w, (IW.Nset X Δ zOf ρ).indicator (testFn X la P Ψ) (cpt X x1 w) ∂muF X x1 := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, IW.muF_lintegral]
    exact (setLIntegral_mono' measurableSet_ball hpt).trans
      (lintegral_mono_set fun w hw => (hsub hw).2.1)
  rw [VanishPf.crit_div hn hρ, ENNReal.mul_top (ENNReal.ofReal_pos.2 hk).ne', ← hMI] at hR1
  exact absurd (hR1.trans_lt hL) (lt_irrefl _)

end GlobalTheory.PeakOrbit

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodHomPushEndStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodHom_push_end' : PEnd := by
  first | exact @GlobalTheory.AnPer.periodHom_push_end | exact GlobalTheory.AnPer.periodHom_push_end | (intros; apply GlobalTheory.AnPer.periodHom_push_end <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PieriRecursionUniqueStatement
section
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_pieri_recursion_of_eq_zero : ∀ (n : ℕ) (c : ℕ → ℂ) (V U : (Fin n → ℕ) → ℂ), (∀ l, ¬ Antitone l → V l = 0) → (∀ l, ¬ Antitone l → U l = 0) → (∀ l, Antitone l → ∀ j ≤ n, ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = j), V (l + (fun i => if i ∈ J then 1 else 0)) = c j * V l) → (∀ l, Antitone l → ∀ j ≤ n, ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = j), U (l + (fun i => if i ∈ J then 1 else 0)) = c j * U l) → V 0 = U 0 → V = U := by
  first | exact @GlobalTheory.pieri_recursion_unique | exact GlobalTheory.pieri_recursion_unique | (intros; apply GlobalTheory.pieri_recursion_unique <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PresentationClosedUnderBoundedCombinationStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.presentation_closed_under_bounded_combination : ∀ (D : D7) (T : TaylorLogMetric.Tor D) (a b : ℕ) (L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (F₀ : TaylorLogMetric.VC D a b → ℂ) (α : Type) (R : Finset α) (c : α → ℂ) (F : α → TaylorLogMetric.VC D a b → ℂ) (n β : ℝ), 0 ≤ β → (∀ x ∈ R, Pres D T L L' F₀ (F x) n) → (∀ x ∈ R, c x ∈ TaylorLogMetric.Qbar ∧ ∀ ρ : TaylorLogMetric.Qbar →ₐ[ℚ] ℂ, ‖StandardLatticesGL3.cj TaylorLogMetric.Qbar ρ (c x)‖ ≤ β) → Pres D T L L' F₀ (fun z => ∑ x ∈ R, c x * F x z) (R.card * β * n) := by
  first | exact @GlobalTheory.PresSum.pres_sum | exact GlobalTheory.PresSum.pres_sum | (intros; apply GlobalTheory.PresSum.pres_sum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductDerivWeierstrassPHalfPeriodsDiscriminant
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem prod_derivWeierstrassP_translates_eq_Δ : ∀ (L : PeriodPair) (a b t : ℂ),
    a ∉ L.lattice → b ∉ L.lattice → a + b ∉ L.lattice → 2 * a ∈ L.lattice →
    2 * b ∈ L.lattice → 2 * t ∉ L.lattice →
    L.derivWeierstrassP t * L.derivWeierstrassP (t + a) * L.derivWeierstrassP (t + b) *
      L.derivWeierstrassP (t + (a + b)) = (latticeCurve L).Δ := by
  intro L a b t ha hb hc h2a h2b h2t
  have h2c : 2 * (a + b) ∈ L.lattice := by
    rw [mul_add]; exact L.lattice.add_mem h2a h2b
  have hshift : ∀ u : ℂ, 2 * u ∈ L.lattice → t + u ∉ L.lattice := by
    intro u hu htu
    apply h2t
    have := L.lattice.sub_mem (L.lattice.add_mem htu htu) hu
    convert this using 1; ring
  have ht : t ∉ L.lattice := by simpa using hshift 0 (by simp)
  have hroot : ∀ u : ℂ, u ∉ L.lattice → 2 * u ∈ L.lattice →
      4 * L.weierstrassP u ^ 3 - L.g₂ * L.weierstrassP u - L.g₃ = 0 := by
    intro u hu h2u
    rw [← L.derivWeierstrassP_sq u hu,
      (derivWeierstrassP_eq_zero_iff L hu).2 (by rwa [← two_mul])]
    ring
  have hne : ∀ u v : ℂ, u ∉ L.lattice → v ∉ L.lattice → 2 * v ∈ L.lattice →
      u + v ∉ L.lattice → L.weierstrassP u ≠ L.weierstrassP v := by
    intro u v hu hv h2v huv h
    rcases (weierstrassP_eq_iff L hu hv).1 h with h' | h'
    · apply huv
      have := L.lattice.add_mem h' h2v
      convert this using 1; ring
    · exact huv h'
  have h12 := hne a b ha hb h2b hc
  have h13 := hne a (a + b) ha hc h2c (by
    intro h; apply hb
    have := L.lattice.sub_mem h h2a
    convert this using 1; ring)
  have h23 := hne b (a + b) hb hc h2c (by
    intro h; apply ha
    have := L.lattice.sub_mem h h2b
    convert this using 1; ring)
  obtain ⟨hfac, hdisc⟩ := GlobalTheory.T.cubic_factor_and_discriminant_of_three_distinct_roots L.g₂ L.g₃ _ _ _ (hroot a ha h2a) (hroot b hb h2b)
    (hroot _ hc h2c) h12 h13 h23
  have e1 := GlobalTheory.T.derivWeierstrassP_add_half_period' L a t ha h2a ht (hshift a h2a)
  have e2 := GlobalTheory.T.derivWeierstrassP_add_half_period' L b t hb h2b ht (hshift b h2b)
  have e3 := GlobalTheory.T.derivWeierstrassP_add_half_period' L (a + b) t hc h2c ht (hshift _ h2c)
  have hsq := L.derivWeierstrassP_sq t ht
  rw [hfac] at hsq
  have hd : L.derivWeierstrassP t ≠ 0 := fun h =>
    h2t (by rw [two_mul]; exact (derivWeierstrassP_eq_zero_iff L ht).1 h)
  rw [latticeCurve_Δ]
  generalize L.derivWeierstrassP t = d at *
  generalize L.derivWeierstrassP (t + a) = d₁ at *
  generalize L.derivWeierstrassP (t + b) = d₂ at *
  generalize L.derivWeierstrassP (t + (a + b)) = d₃ at *
  generalize L.weierstrassP t = x at *
  generalize L.weierstrassP a = e₁ at *
  generalize L.weierstrassP b = e₂ at *
  generalize L.weierstrassP (a + b) = e₃ at *
  apply mul_left_cancel₀ (pow_ne_zero 3 hd)
  calc d ^ 3 * (d * d₁ * d₂ * d₃) = (d ^ 2) ^ 2 * (d₁ * d₂ * d₃) := by ring
    _ = 16 * ((d₁ * (x - e₁) ^ 2) * (d₂ * (x - e₂) ^ 2) * (d₃ * (x - e₃) ^ 2)) := by
        rw [hsq]; ring
    _ = -(16 * ((3 * e₁ ^ 2 - L.g₂ / 4) * (3 * e₂ ^ 2 - L.g₂ / 4) *
          (3 * e₃ ^ 2 - L.g₂ / 4))) * d ^ 3 := by
        rw [e1, e2, e3]; ring
    _ = d ^ 3 * (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) := by rw [hdisc]; ring

end GlobalTheory.CMModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmEqPSmulAddIntegralStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiLogarithm_eq_p_smul_add_integral : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (h : IsLaw μ), ∀ f ∈ quasiLog p h, ∀ b, Red p (cob1 (fun i => Katz.lift p (μ i)) f) (cob1 μ b) → RedV p (lin f) (lin b) → ∃ g ∈ quasiLog p h, f - (p : WittVector p k) • g ∈ intBy p k (Fin d) 1 := by
  first | exact @GlobalTheory.Katz.quasiLog_eq_p_smul_add_int | exact GlobalTheory.Katz.quasiLog_eq_p_smul_add_int | (intros; apply GlobalTheory.Katz.quasiLog_eq_p_smul_add_int <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmPeriodEqTangentHodgeTateStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiLogarithm_period_eq_tangent_hodgeTate : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (E : Type) [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (f : MvPowerSeries (Fin d) E) (l : G.dual.Lie), QL c.μ ⊤ f → c.IsLie f l → ∀ t : G.Tate, c.HasPeriod (RingHom.id O) t f (l (hodgeTate G t)) := by
  first | exact @GlobalTheory.QLogPeriod.hasPeriod_hodgeTate | exact GlobalTheory.QLogPeriod.hasPeriod_hodgeTate | (intros; apply GlobalTheory.QLogPeriod.hasPeriod_hodgeTate <;> assumption)
end

