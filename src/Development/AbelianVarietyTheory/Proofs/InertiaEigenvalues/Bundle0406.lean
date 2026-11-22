import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0374
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0375
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0014
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0383
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0376
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AutomorphicArithmetic.CyclotomicBounds.Bundle0002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0386
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0385
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0377

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharactersDetectRestrictNormalInfFiniteLevelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.characters_detect_restrictNormal_inf_finiteLevel : ∀ (l : ℕ) [Fact l.Prime] (L : Type) [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra ℚ_[l] L] [ValuativeExtension ℚ_[l] L] [FiniteDimensional ℚ_[l] L] [IsGalois ℚ_[l] L] [Algebra L (Om l)] [IsScalarTower ℚ_[l] L (Om l)] (r : ℕ) (N N' : Subgroup (GQ l)) (I : Subgroup (L ≃ₐ[ℚ_[l]] L)) (ι : Type) (x : ι → Om l) (a : ι → GQ l → ℤ), (∀ i, x i ∈ Set.range (algebraMap L (Om l))) → (∀ i, ∀ σ ∈ N, ‖σ (x i) - x i - (a i σ : Om l)‖ ≤ ((l : ℝ)⁻¹) ^ r) → (∀ σ ∈ N, (∀ i, (l : ℤ) ^ r ∣ a i σ) → σ ∈ N') → Detects l r (N.map (AlgEquiv.restrictNormalHom L) ⊓ I) (N'.map (AlgEquiv.restrictNormalHom L) ⊓ I) := by
  first | exact @GlobalTheory.PMon.Ram.detects_restrictNormal_inf | exact GlobalTheory.PMon.Ram.detects_restrictNormal_inf | (intros; apply GlobalTheory.PMon.Ram.detects_restrictNormal_inf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyEqOfSemisimplificationStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charpoly_eq_of_semisimplification : ∀ {k Γ : Type} [Field k] [Group Γ] {W : Type} [AddCommGroup W] [Module k W] [FiniteDimensional k W] {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (s : Representation k Γ W) (ρ : Representation k Γ V), GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents.IsSemisimplificationOf s ρ → ∀ g, LinearMap.charpoly (s g) = LinearMap.charpoly (ρ g) := by
  first | exact @GlobalTheory.SemisimplificationCharpoly.charpoly_eq | exact GlobalTheory.SemisimplificationCharpoly.charpoly_eq | (intros; apply GlobalTheory.SemisimplificationCharpoly.charpoly_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassFunctionDegreeEqSumDerivativesStatement
section
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classFunction_degree_eq_sum_derivatives : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (n : ℕ) (χ : Gn g n → ℂ), 0 < n → IsClass χ → χ 1 = ∑ m ∈ Finset.range n, der ψ m χ 1 * ∏ i ∈ Finset.Ico (m + 1) n, ((g : ℂ) ^ i - 1) := by
  first | exact @GlobalTheory.GLq.DegDer.one_eq_sum_der | exact GlobalTheory.GLq.DegDer.one_eq_sum_der | (intros; apply GlobalTheory.GLq.DegDer.one_eq_sum_der <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscCoefficientsTopologicallyFree
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem disc_coefficients : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A) (ι : Type) (TB : TopBasis s bk.J ι) (ρ : ℝ≥0), 0 < ρ → ρ < 1 → ∀ j : bk.DS ρ →+* Disc l (s X) ρ, IsDiscMap s j → ∃ cD : ι → (Disc l (s X) ρ →+ bk.DS ρ), (∀ i a, cD i (toDisc l (s X) ρ a) = toDisc l (X : bk.S) ρ (TB.c i a)) ∧ (∀ i x y, cD i (j x * y) = x * cD i y) ∧ (∀ i y, ‖cD i y‖ ≤ ‖y‖) ∧ (∀ y, Filter.Tendsto (fun i => cD i y) Filter.cofinite (nhds 0)) ∧ (∀ y, HasSum (fun i => j (cD i y) * toDisc l (s X) ρ (TB.b i)) y) ∧ (∀ y (r : ℝ), 0 ≤ r → (∀ i, ‖cD i y‖ ≤ r) → ‖y‖ ≤ r) ∧ (∀ z : ι → bk.DS ρ, Filter.Tendsto z Filter.cofinite (nhds 0) → ∃ y, ∀ i, cD i y = z i) ∧ ∀ x, ‖j x‖ = ‖x‖ := by
  intro l _ K bk A _ s ι TB ρ h0 h1 j hj
  obtain ⟨cD, hc1, hc2, hc3⟩ := GlobalTheory.T.exists_topologicalBasis_coeff_disc_extension l K bk A s ι TB ρ h0 h1 j hj
  have hs := GlobalTheory.T.closedDisc_topologicalBasis_expansion l K bk A s ι TB ρ h0 h1 j hj cD ⟨hc1, hc2, hc3⟩
  haveI : IsUltrametricDist (Disc l (s X) ρ) := (GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l A (s X) ρ).1
  have hb : ∀ (x : bk.DS ρ) (i : ι), ‖j x * toDisc l (s X) ρ (TB.b i)‖ ≤ ‖x‖ := fun x i =>
    (norm_mul_le _ _).trans ((mul_le_mul (hj.norm_le x) (norm_toDisc_le _) (norm_nonneg _)
      (norm_nonneg _)).trans (mul_one _).le)
  have hcont : ∀ i, Continuous (cD i) := fun i =>
    AddMonoidHomClass.continuous_of_bound _ 1 fun y => (hc3 i y).trans (one_mul _).ge
  refine ⟨cD, hc1, hc2, hc3, fun y => (hs y).1, fun y => (hs y).2, ?_, ?_, ?_⟩
  · intro y r hr h
    rw [← (hs y).2.tsum_eq]
    exact IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hr fun i => (hb _ i).trans (h i)
  · intro z hz
    have ht : Filter.Tendsto (fun i => j (z i) * toDisc l (s X) ρ (TB.b i)) Filter.cofinite (nhds 0) :=
      squeeze_zero_norm (fun i => hb (z i) i) (tendsto_zero_iff_norm_tendsto_zero.1 hz)
    have hsum := NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ht
    refine ⟨_, fun i => ((hsum.hasSum.map (cD i) (hcont i)).unique ?_)⟩
    classical
    have e : ((cD i) ∘ fun i => j (z i) * toDisc l (s X) ρ (TB.b i)) = fun i' => if i' = i then z i else 0 := by
      funext i'
      simp only [Function.comp]
      rw [hc2, hc1]
      split_ifs with h
      · subst h
        rw [TB.c_self, map_one, mul_one]
      · rw [TB.c_ne _ _ (Ne.symm h), map_zero, mul_zero]
    rw [e]
    exact hasSum_ite_eq i (z i)
  · intro x
    refine le_antisymm (hj.norm_le x) ?_
    have e : cD TB.i₀ (j x * toDisc l (s X) ρ (TB.b TB.i₀)) = x := by
      rw [hc2, hc1, TB.c_self, map_one, mul_one]
    have h := hc3 TB.i₀ (j x * toDisc l (s X) ρ (TB.b TB.i₀))
    rwa [e, TB.b_i₀, map_one, mul_one] at h

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosingNumericalInequalityTheoremBStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closing_numerical_inequality_theoremB : ∀ (CA C b l S η Rw Tb Vd : ℝ) (f r t m p : ℕ), 13 * max CA 0 ≤ C → 260 * f ^ 2 * t ^ 2 * (r + t) ≤ p → 1 ≤ t → 1 ≤ f → m ≤ r → 3 ≤ l → 0 ≤ S → 0 ≤ η → 0 < b → 1 < Real.log b → Rw ≤ max CA 0 * (3 * (f : ℝ) * r * (4 * b / l + 2 * S + 2 * Real.logb l (2 * b) + 1 + η + t) + 6 * (f : ℝ) * m * (2 * b + 1)) + f → Tb ≤ 240 * (t : ℝ) ^ 2 * (f : ℝ) ^ 2 * ((r : ℝ) + t) * Real.log b → Vd ≤ 4 * ((r : ℝ) + t) * t → Rw + Tb + Vd ≤ C * f * (r * (b / l + S + t + η + Real.log b) + m * b) + (p : ℝ) * Real.log b := by
  first | exact @GlobalTheory.closing_numerical_inequality | exact GlobalTheory.closing_numerical_inequality | (intros; apply GlobalTheory.closing_numerical_inequality <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffDetGenericSumMemHeckeAlgebra
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory.SpanRing

theorem charpoly_coeff_mem_of_charPolyIn {Γ X O : Type} [Group Γ] [CommRing O] {n : ℕ}
    (T : Subalgebra O (X → O)) (rep : X → (Γ →* GL (Fin n) O)) (h : CharPolyIn T rep) (g : Γ) (j : ℕ) :
    (fun x => (mat (rep x) g).charpoly.coeff j) ∈ T := by
  unfold CharPolyIn at h
  rcases subsingleton_or_nontrivial O with hO | hO
  · have hz : (fun x => (mat (rep x) g).charpoly.coeff j) = 0 := Subsingleton.elim _ _
    rw [hz]
    exact T.zero_mem
  · by_cases hj : j ≤ n
    · have e : (fun x => (mat (rep x) g).charpoly.coeff j) =
          fun x => (mat (rep x) g).charpolyRev.coeff (n - j) := by
        funext x
        rw [← Matrix.reverse_charpoly, Polynomial.coeff_reverse, Matrix.charpoly_natDegree_eq_dim,
          Fintype.card_fin, Polynomial.revAt_le (Nat.sub_le n j), Nat.sub_sub_self hj]
      rw [e]
      exact h g (n - j)
    · have hz : (fun x => (mat (rep x) g).charpoly.coeff j) = 0 := by
        funext x
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
        omega
      rw [hz]
      exact T.zero_mem

private theorem coeff_det_generic_sum_eval {X O : Type} [CommRing O] {n m : ℕ}
    (a : Fin m → X → Matrix (Fin n) (Fin n) O) (x : X) (d : Fin m →₀ ℕ) :
    MvPolynomial.coeff d (Matrix.det (∑ k,
      (MvPolynomial.X k : MvPolynomial (Fin m) O) • (a k x).map MvPolynomial.C)) =
    (MvPolynomial.coeff d (Matrix.det (∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) (X → O)) •
      Matrix.of (fun i j => MvPolynomial.C (fun y => a k y i j)))) : X → O) x := by
  set φ : MvPolynomial (Fin m) (X → O) →+* MvPolynomial (Fin m) O :=
    MvPolynomial.map (Pi.evalRingHom (fun _ => O) x) with hφ
  have h1 : φ.mapMatrix (∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) (X → O)) •
      Matrix.of (fun i j => MvPolynomial.C (fun y => a k y i j))) =
      ∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) O) • (a k x).map MvPolynomial.C := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    refine Matrix.ext fun i j => ?_
    simp [hφ]
  rw [← h1, ← RingHom.map_det, hφ, MvPolynomial.coeff_map]
  rfl

theorem coeff_det_generic_sum_mem_of_inRing :
    ∀ {Γ X O : Type} [Group Γ] [CommRing O] {n : ℕ} (T : Subalgebra O (X → O))
      (rep : X → (Γ →* GL (Fin n) O)), CharPolyIn T rep →
      ∀ (m : ℕ) (a : Fin m → X → Matrix (Fin n) (Fin n) O), (∀ k, InRing T rep (a k)) →
      ∀ d : Fin m →₀ ℕ, (fun x => MvPolynomial.coeff d (Matrix.det (∑ k,
        (MvPolynomial.X k : MvPolynomial (Fin m) O) • (a k x).map MvPolynomial.C))) ∈ T := by
  intro Γ X O _ _ n T rep hT m a ha d
  classical

  let T' : Subring (MvPolynomial (Fin m) (X → O)) := (MvPolynomial.map T.val.toRingHom).range
  have hmemT : ∀ p ∈ T', ∀ e, MvPolynomial.coeff e p ∈ T := by
    intro p hp e
    obtain ⟨q, rfl⟩ := RingHom.mem_range.1 hp
    rw [MvPolynomial.coeff_map]
    exact (MvPolynomial.coeff e q).2
  have hC : ∀ f ∈ T, (MvPolynomial.C f : MvPolynomial (Fin m) (X → O)) ∈ T' := fun f hf =>
    RingHom.mem_range.2 ⟨MvPolynomial.C ⟨f, hf⟩, by simp⟩
  have hX : ∀ k, (MvPolynomial.X k : MvPolynomial (Fin m) (X → O)) ∈ T' := fun k =>
    RingHom.mem_range.2 ⟨MvPolynomial.X k, by simp⟩

  let M : Γ → Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) (X → O)) :=
    fun h => Matrix.of fun i j => MvPolynomial.C (fun y => mat (rep y) h i j)
  have hmul : ∀ A ∈ Set.range M, ∀ B ∈ Set.range M, A * B ∈ Set.range M := by
    rintro _ ⟨g, rfl⟩ _ ⟨h, rfl⟩
    refine ⟨g * h, ?_⟩
    refine Matrix.ext fun i j => ?_
    simp only [M, Matrix.mul_apply, Matrix.of_apply, ← map_mul, ← map_sum]
    congr 1
    funext y
    simp [mat, Matrix.mul_apply, Finset.sum_apply]
  have hchar : ∀ A ∈ Set.range M, ∀ j, A.charpoly.coeff j ∈ T' := by
    rintro _ ⟨h, rfl⟩ j
    have hP : M h = (Matrix.of fun i j => fun y => mat (rep y) h i j).map MvPolynomial.C := by
      refine Matrix.ext fun i j => ?_
      rfl
    rw [hP, Matrix.charpoly_map, Polynomial.coeff_map]
    apply hC
    have e : (Matrix.of fun i j => fun y => mat (rep y) h i j).charpoly.coeff j =
        fun y => (mat (rep y) h).charpoly.coeff j := by
      funext y
      have hm : (Matrix.of fun i j => fun y => mat (rep y) h i j).map (Pi.evalRingHom (fun _ => O) y) =
          mat (rep y) h := by
        refine Matrix.ext fun i j => ?_
        rfl
      have e' := congrArg (fun p => Polynomial.coeff p j)
        (Matrix.charpoly_map (Matrix.of fun i j => fun y => mat (rep y) h i j) (Pi.evalRingHom (fun _ => O) y))
      rw [hm] at e'
      simp only [Polynomial.coeff_map] at e'
      exact e'.symm
    rw [e]
    exact charpoly_coeff_mem_of_charPolyIn T rep hT h j

  have hlift : ∀ b : X → Matrix (Fin n) (Fin n) O, b ∈ Submodule.span O (gens T rep) →
      (Matrix.of fun i j => MvPolynomial.C (fun y => b y i j) : Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) (X → O)))
        ∈ Submodule.span T' (Set.range M) := by
    intro b hb
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨f, hf, h, rfl⟩ := hb
      have e : (Matrix.of fun i j => MvPolynomial.C (fun y => (fun x => f x • mat (rep x) h) y i j) :
          Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) (X → O))) =
          (⟨MvPolynomial.C f, hC f hf⟩ : T') • M h := by
        refine Matrix.ext fun i j => ?_
        simp only [Matrix.of_apply, Subring.smul_def, Matrix.smul_apply, smul_eq_mul, M, ← map_mul]
        congr 1
      rw [e]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨h, rfl⟩)
    | zero =>
      have e : (Matrix.of fun i j => MvPolynomial.C (fun y => (0 : X → Matrix (Fin n) (Fin n) O) y i j) :
          Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) (X → O))) = 0 := by
        refine Matrix.ext fun i j => ?_
        simp only [Matrix.of_apply, Pi.zero_apply, Matrix.zero_apply]
        exact map_zero _
      rw [e]
      exact Submodule.zero_mem _
    | add b c _ _ hb hc =>
      have e : (Matrix.of fun i j => MvPolynomial.C (fun y => (b + c) y i j) :
          Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) (X → O))) =
          Matrix.of (fun i j => MvPolynomial.C (fun y => b y i j)) +
            Matrix.of (fun i j => MvPolynomial.C (fun y => c y i j)) := by
        refine Matrix.ext fun i j => ?_
        simp only [Matrix.of_apply, Matrix.add_apply, ← map_add]
        rfl
      rw [e]
      exact Submodule.add_mem _ hb hc
    | smul r b _ hb =>
      have e : (Matrix.of fun i j => MvPolynomial.C (fun y => (r • b) y i j) :
          Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) (X → O))) =
          (⟨MvPolynomial.C (algebraMap O (X → O) r), hC _ (T.algebraMap_mem r)⟩ : T') •
            Matrix.of (fun i j => MvPolynomial.C (fun y => b y i j)) := by
        refine Matrix.ext fun i j => ?_
        simp only [Matrix.of_apply, Subring.smul_def, Matrix.smul_apply, smul_eq_mul, ← map_mul]
        congr 1
      rw [e]
      exact Submodule.smul_mem _ _ hb
  have hB : (∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) (X → O)) •
      Matrix.of (fun i j => MvPolynomial.C (fun y => a k y i j))) ∈ Submodule.span T' (Set.range M) := by
    refine Submodule.sum_mem _ fun k _ => ?_
    have := Submodule.smul_mem (Submodule.span T' (Set.range M)) (⟨MvPolynomial.X k, hX k⟩ : T')
      (hlift (a k) ((inRing_iff_mem_span T rep (a k)).1 (ha k)))
    exact this
  obtain ⟨N, f, g, hfg⟩ := Submodule.mem_span_set'.1 hB
  have hdet := Amitsur.det_sum_smul_mem T' (Set.range M) hmul hchar Finset.univ
    (fun i => (f i : MvPolynomial (Fin m) (X → O))) (fun i => (g i).1)
    (fun i => (f i).2) (fun i => (g i).2)
  have hsum : (∑ i ∈ Finset.univ, (f i : MvPolynomial (Fin m) (X → O)) • (g i).1) =
      ∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) (X → O)) •
        Matrix.of (fun i j => MvPolynomial.C (fun y => a k y i j)) := by
    rw [← hfg]
    rfl
  rw [hsum] at hdet
  have key : (fun x => MvPolynomial.coeff d (Matrix.det (∑ k,
      (MvPolynomial.X k : MvPolynomial (Fin m) O) • (a k x).map MvPolynomial.C))) =
      MvPolynomial.coeff d (Matrix.det (∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) (X → O)) •
        Matrix.of (fun i j => MvPolynomial.C (fun y => a k y i j)))) :=
    funext fun x => coeff_det_generic_sum_eval a x d
  rw [key]
  exact hmemT _ hdet d

end GlobalTheory.SpanRing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComplementOfCharactersUniqueUpToConjStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complement_of_characters_unique_up_to_conj : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc) (r r' : (N.X i → (GE N →* GL (Fin R.nV) (N.O i)))) (ρ ρ' : (N.X i → (GE N →* GL (Fin R.r) (N.O i)))) (π : N.X i), IsSSRep (mapRep (algebraMap (N.O i) (Kf N i)) (r π)) → (∃ Pm : GL (Fin R.nV) (KK N i), ∀ g, (Pm : Matrix (Fin R.nV) (Fin R.nV) (KK N i)) * (rO N i r π g).map (toK N i) = (rO N i r' π g).map (toK N i) * (Pm : Matrix (Fin R.nV) (Fin R.nV) (KK N i))) → (∃ e, IsDecomp (t := R.t) (r π) (ρ π) (N.chi i) e) → (∃ e, IsDecomp (t := R.t) (r' π) (ρ' π) (N.chi i) e) → (∃ Pm : GL (Fin R.r) (KK N i), ∀ g, (Pm : Matrix (Fin R.r) (Fin R.r) (KK N i)) * (rhoO N i ρ π g).map (toK N i) = (rhoO N i ρ' π g).map (toK N i) * (Pm : Matrix (Fin R.r) (Fin R.r) (KK N i))) := by
  first | exact @GlobalTheory.CharCancel.main | exact GlobalTheory.CharCancel.main | (intros; apply GlobalTheory.CharCancel.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompletionOverQOrDEqUnramifiedSupSqrt
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.HubLoc

open Formalism.FrobeniusOrbits

section Gen

variable {l : ℕ} [Fact l.Prime] {R : Ranks} (H : Host R) (J : H.E →+* Om l)

theorem kw_eq_sup_of_gens (Kw : FinExt l) (hE : ∀ x : H.E, J x ∈ Kw.1)
    (hdense : (Kw.1 : Set (Om l)) ⊆ closure (Set.range J)) (g₁ g₂ g₃ : H.E)
    (hgen : ∀ M : IntermediateField ℚ_[l] (Om l), J g₁ ∈ M → J g₂ ∈ M → J g₃ ∈ M → ∀ x : H.E, J x ∈ M) :
    Kw.1 = IntermediateField.adjoin ℚ_[l] ({J g₁, J g₂} : Set (Om l)) ⊔
      IntermediateField.adjoin ℚ_[l] {J g₃} := by
  set M := IntermediateField.adjoin ℚ_[l] ({J g₁, J g₂} : Set (Om l)) with hM
  set N := M ⊔ IntermediateField.adjoin ℚ_[l] {J g₃} with hN
  have hfM : FiniteDimensional ℚ_[l] ↥M :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral (R := ℚ_[l]) x
  have hfy : FiniteDimensional ℚ_[l] ↥(IntermediateField.adjoin ℚ_[l] {J g₃}) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (R := ℚ_[l]) _)
  have hfN : FiniteDimensional ℚ_[l] ↥N := IntermediateField.finiteDimensional_sup _ _
  have hcl : IsClosed ((N : IntermediateField ℚ_[l] (Om l)) : Set (Om l)) :=
    Submodule.closed_of_finiteDimensional N.toSubalgebra.toSubmodule
  have h1 : J g₁ ∈ N := le_sup_left (a := M) (IntermediateField.subset_adjoin _ _ (by simp))
  have h2 : J g₂ ∈ N := le_sup_left (a := M) (IntermediateField.subset_adjoin _ _ (by simp))
  have h3 : J g₃ ∈ N := le_sup_right (a := M) (IntermediateField.mem_adjoin_simple_self _ _)
  apply le_antisymm
  · intro x hx
    refine closure_minimal ?_ hcl (hdense hx)
    rintro _ ⟨z, rfl⟩
    exact hgen N h1 h2 h3 z
  · refine sup_le ?_ ?_
    · rw [hM, IntermediateField.adjoin_le_iff]
      rintro _ (rfl | rfl)
      exacts [hE g₁, hE g₂]
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ rfl
      exact hE g₃

theorem sq_aE_image : (J (H.sqq)) ^ 2 = -(H.q : Om l) := by
  rw [← map_pow, H.sqq_sq]; simp

theorem sq_bE_image : (J (H.sqd)) ^ 2 = -(H.d : Om l) := by
  rw [← map_pow, H.sqd_sq]; simp

theorem kw_eq_sup_sqrt (Kw : FinExt l) (hE : ∀ x : H.E, J x ∈ Kw.1)
    (hdense : (Kw.1 : Set (Om l)) ⊆ closure (Set.range J)) (hl : l = H.q ∨ l = H.d) :
    ∃ M : IntermediateField ℚ_[l] (Om l), M ≤ MaximalUnramifiedExtension l ∧ ∃ y : Om l, y ^ 2 = -(l : Om l) ∧
      Kw.1 = M ⊔ IntermediateField.adjoin ℚ_[l] {y} := by
  have hh := H.hyp
  have hq2 : H.q % 4 = 3 := by have := hh.2.2.1; omega
  have hd2 : H.d % 4 = 3 := by have := hh.2.2.2.1; omega
  have hqd : H.q ≠ H.d := by have := hh.2.2.1; have := hh.2.2.2.1; omega
  have hlS : ¬ l ∣ H.QS := UpperTheory.Small.not_dvd_QS H Fact.out (UpperTheory.Small.not_mem_of_qd H hl)
  have hθ := theta_mem_Kur H J
  rcases hl with rfl | rfl
  · refine ⟨_, ?_, _, sq_aE_image H J, kw_eq_sup_of_gens H J Kw hE hdense (thL H H.q) (H.sqd)
      (H.sqq) fun M m1 m2 m3 x => image_le H J hlS M m1 m3 m2 x⟩
    rw [IntermediateField.adjoin_le_iff]
    rintro _ (rfl | rfl)
    · exact hθ
    · exact sqrtKur_holds _ H.d hh.2.1 hd2 hqd.symm _ (sq_bE_image H J)
  · refine ⟨_, ?_, _, sq_bE_image H J, kw_eq_sup_of_gens H J Kw hE hdense (thL H H.d) (H.sqq)
      (H.sqd) fun M m1 m2 m3 x => image_le H J hlS M m1 m2 m3 x⟩
    rw [IntermediateField.adjoin_le_iff]
    rintro _ (rfl | rfl)
    · exact hθ
    · exact sqrtKur_holds _ H.q hh.1 hq2 hqd _ (sq_aE_image H J)

end Gen

theorem kw_eq_unram_sup_sqrt : ∀ (D : D7) (i : D.nd.Loc), (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) →
    ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
    ∃ M : IntermediateField ℚ_[D.nd.l i] (Om (D.nd.l i)), M ≤ MaximalUnramifiedExtension (D.nd.l i) ∧
      ∃ y : Om (D.nd.l i), y ^ 2 = -(D.nd.l i : Om (D.nd.l i)) ∧
        (D.nbr i w hw).Kw.1 = M ⊔ IntermediateField.adjoin ℚ_[D.nd.l i] {y} := by
  intro D i hl w hw
  exact kw_eq_sup_sqrt D.host ((D.nbr i w hw).j.comp (algebraMap D.host.E D.nd.Om)) (D.nbr i w hw).Kw
    (D.nbr i w hw).j_E (D.nbr i w hw).j_dense hl

end GlobalTheory.HubLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CongrFiltrationDetectingCharactersCoboundary
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon
open scoped Formalism.Per

namespace GlobalTheory

noncomputable def padicClampInt (l : ℕ) [Fact l.Prime] (x : ℚ_[l]) : ℤ_[l] :=
  ⟨if ‖x‖ ≤ 1 then x else 0, by split_ifs with h <;> simp [h]⟩

theorem padicClampInt_coe (l : ℕ) [Fact l.Prime] {x : ℚ_[l]} (h : ‖x‖ ≤ 1) :
    ((padicClampInt l x : ℤ_[l]) : ℚ_[l]) = x := by
  show (if ‖x‖ ≤ 1 then x else 0) = x
  rw [if_pos h]

theorem congrFiltration_detectingCharacters_coboundary : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (ρ : ↥(GK K) →* GL n ℚ_[l]) (M : GL n ℂ_[l]), (∀ g : ↥(GK K), (ρ g : Matrix n n ℚ_[l]).map (algebraMap ℚ_[l] ℂ_[l]) * (M : Matrix n n ℂ_[l]).map (Formalism.Per.σC (g : GQ l)) = M) → ∀ N : ℕ → Subgroup ↥(GK K), (∀ k g, g ∈ N k ↔ ∀ i j, ‖((ρ g : Matrix n n ℚ_[l]) - 1) i j‖ ≤ (l : ℝ) ^ (-((k : ℤ) + 2))) → ∀ r : ℕ, ∃ k₀ : ℕ, ∀ k ≥ k₀, ∃ (ι : Type) (_ : Finite ι) (x : ι → ℂ_[l]) (a : ι → ↥(GK K) → ℤ_[l]), (∀ i, ∀ σ ∈ N k, ‖Formalism.Per.σC (σ : GQ l) (x i) - x i - algebraMap ℚ_[l] ℂ_[l] (a i σ : ℚ_[l])‖ ≤ ((l : ℝ)⁻¹) ^ r) ∧ ∀ σ ∈ N k, (∀ i, (l : ℤ_[l]) ^ r ∣ a i σ) → σ ∈ N (k + r) := by
  intro l _ n _ _ K ρ M hM N hN r
  obtain ⟨b, hb, hcob⟩ := GlobalTheory.T.galoisRep_entries_coboundary_complexPadic l n K ρ M hM
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  obtain ⟨k₀, hk₀⟩ := pow_unbounded_of_one_lt (b * (l : ℝ) ^ r) hl1
  refine ⟨k₀, fun k hk => ?_⟩
  set L : ℝ := (l : ℝ) ^ (k + 2) with hL
  have hLpos : 0 < L := by positivity
  set t : ℝ := (l : ℝ) ^ (-((k : ℤ) + 2)) with htdef
  have ht : t = L⁻¹ := by
    rw [htdef, hL, ← zpow_natCast, ← zpow_neg]; push_cast; rfl
  have htpos : 0 < t := by rw [ht]; positivity
  have hH : ∀ g ∈ N k, ∀ i j, ‖((ρ g : Matrix n n ℚ_[l]) - 1) i j‖ ≤ t := fun g hg => (hN k g).1 hg
  choose y hy using hcob (N k) t htpos hH
  set c : ℚ_[l] := ((l : ℚ_[l]) ^ (k + 2))⁻¹ with hc
  have hcnorm : ‖c‖ = L := by
    rw [hc, norm_inv, norm_pow, Padic.norm_p, inv_pow, inv_inv]
  have hnorm : ∀ g ∈ N k, ∀ i j, ‖c * ((ρ g : Matrix n n ℚ_[l]) - 1) i j‖ ≤ 1 := by
    intro g hg i j
    rw [norm_mul, hcnorm]
    calc L * ‖((ρ g : Matrix n n ℚ_[l]) - 1) i j‖ ≤ L * t :=
          mul_le_mul_of_nonneg_left (hH g hg i j) hLpos.le
      _ = 1 := by rw [ht]; field_simp
  classical
  let a : n × n → ↥(GK K) → ℤ_[l] := fun p g =>
    padicClampInt l (c * ((ρ g : Matrix n n ℚ_[l]) - 1) p.1 p.2)
  have ha : ∀ p, ∀ σ ∈ N k,
      ((a p σ : ℤ_[l]) : ℚ_[l]) = c * ((ρ σ : Matrix n n ℚ_[l]) - 1) p.1 p.2 := by
    intro p σ hσ
    exact padicClampInt_coe l (hnorm σ hσ p.1 p.2)
  let x : n × n → ℂ_[l] := fun p => algebraMap ℚ_[l] ℂ_[l] c * y p.1 p.2
  have hbt : b * t ≤ ((l : ℝ)⁻¹) ^ r := by
    have h1 : (l : ℝ) ^ k₀ ≤ L := pow_le_pow_right₀ hl1.le (by omega)
    have h2 : b * (l : ℝ) ^ r ≤ L := by linarith
    rw [ht, inv_pow, ← div_eq_mul_inv, div_le_iff₀ hLpos, ← div_eq_inv_mul,
      le_div_iff₀ (by positivity)]
    exact h2
  refine ⟨n × n, inferInstance, x, a, ?_, ?_⟩
  · intro p σ hσ
    have hfix : Formalism.Per.σC (σ : GQ l) (algebraMap ℚ_[l] ℂ_[l] c) = algebraMap ℚ_[l] ℂ_[l] c := by
      simp only [hc, map_inv₀, map_pow, map_natCast]
    simp only [x]
    rw [ha p σ hσ, map_mul (Formalism.Per.σC (σ : GQ l)), hfix, map_mul]
    rw [show ∀ u v w : ℂ_[l], u * v - u * w - u * algebraMap ℚ_[l] ℂ_[l] (((ρ σ : Matrix n n ℚ_[l]) - 1) p.1 p.2)
        = u * (v - w - algebraMap ℚ_[l] ℂ_[l] (((ρ σ : Matrix n n ℚ_[l]) - 1) p.1 p.2)) by
          intros; ring]
    rw [norm_mul, norm_algebraMap', hcnorm]
    calc L * ‖_‖ ≤ L * (b * t ^ 2) := mul_le_mul_of_nonneg_left (hy p.1 p.2 σ hσ) hLpos.le
      _ = b * t := by rw [ht]; field_simp
      _ ≤ ((l : ℝ)⁻¹) ^ r := hbt
  · intro σ hσ hdiv
    rw [hN]
    intro i j
    obtain ⟨q, hq⟩ := hdiv (i, j)
    have h1 : ‖((a (i, j) σ : ℤ_[l]) : ℚ_[l])‖ ≤ ((l : ℝ)⁻¹) ^ r := by
      rw [← PadicInt.norm_def, hq, norm_mul, norm_pow, PadicInt.norm_p]
      calc ((l : ℝ)⁻¹) ^ r * ‖q‖ ≤ ((l : ℝ)⁻¹) ^ r * 1 :=
            mul_le_mul_of_nonneg_left (PadicInt.norm_le_one q) (by positivity)
        _ = _ := mul_one _
    rw [ha (i, j) σ hσ, norm_mul, hcnorm] at h1
    have h3 : (l : ℝ) ^ (-(((k + r : ℕ) : ℤ) + 2)) = ((l : ℝ)⁻¹) ^ r * L⁻¹ := by
      rw [hL, ← zpow_natCast, ← zpow_natCast, inv_zpow', ← zpow_neg, ← zpow_add₀ hl0.ne']
      congr 1; push_cast; ring
    rw [h3, le_mul_inv_iff₀ hLpos, mul_comm]
    exact h1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjDualCharpolyOfSplitFrobeniusDenseStatement
section
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjDualCharpoly_of_splitFrobenius_dense : ∀ (D : D7), GlobalTheory.TypeLeaf.FrobDense D → ∀ (i : D.ntw.Tw) (s : D.ntw.Sig i), FrobDual i s → CharDual i s := by
  first | exact @GlobalTheory.CharDualDense.charDual_of_frobDual | exact GlobalTheory.CharDualDense.charDual_of_frobDual | (intros; apply GlobalTheory.CharDualDense.charDual_of_frobDual <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamFilteredComparisonCoordinatesStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRham_filtered_comparison_coordinates : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]), IsDR (P.PD K) (qRep ρ) → ∀ (a : ℤ) (y : Fin d → P.R.BdR), (∀ i, y i ∈ (P.PD K).Fil a) → ∃ (m : ℕ) (k : Fin m → ℤ) (b : Fin m → P.R.BdR) (z : Fin m → Fin d → P.R.BdR), (∀ r, (∀ g : ↥(GK K), (ρ g).val.map (fun z : ℤ_[l] => algebraMap ℚ_[l] P.R.BdR (z : ℚ_[l])) *ᵥ (fun i => P.actQdR (g : GQ l) (z r i)) = z r) ∧ (∀ i, z r i ∈ (P.PD K).Fil (k r)) ∧ b r ∈ (P.PD K).Fil (a - k r)) ∧ y = ∑ r, b r • z r := by
  first | (exact @GlobalTheory.DRFilCoord.filtered_coords) | (exact GlobalTheory.DRFilCoord.filtered_coords) | (intros; apply GlobalTheory.DRFilCoord.filtered_coords  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamFiltrationBoundsInvariantCoordinatesStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRham_filtration_bounds_invariant_coordinates : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (N : ℕ), DdR (P.PD K) (qRep ρ) ≤ FilV (P.PD K) (LL := ℚ_[l]) (V := Fin d → ℚ_[l]) (-(N : ℤ)) → DdR (P.PD K) (qRep ρ) ⊓ FilV (P.PD K) (LL := ℚ_[l]) (V := Fin d → ℚ_[l]) ((N : ℤ) + 1) = ⊥ → ∀ c : Fin d → P.R.BdR, (∀ g : ↥(GK K), (ρ g).val.map (fun z : ℤ_[l] => algebraMap ℚ_[l] P.R.BdR (z : ℚ_[l])) *ᵥ (fun i => P.actQdR (g : GQ l) (c i)) = c) → c ≠ 0 → (∀ i, c i ∈ (P.PD K).Fil (-(N : ℤ))) ∧ ¬ ∀ i, c i ∈ (P.PD K).Fil ((N : ℤ) + 1) := by
  first | exact @GlobalTheory.DRMat.invariant_coord_bounds | exact GlobalTheory.DRMat.invariant_coord_bounds | (intros; apply GlobalTheory.DRMat.invariant_coord_bounds <;> assumption)
end

