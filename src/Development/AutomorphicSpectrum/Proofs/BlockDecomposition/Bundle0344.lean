import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0322
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0324
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.HasFiniteBiproductsModules
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0329
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Bundle0002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0330
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0320

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableNilrad
section
noncomputable section

open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.LocVan

variable {n : ℕ}

theorem locallyCompact_GL (n : ℕ) : LocallyCompactSpace (GL (Fin n) ℂ) := by
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

theorem secondCountable_GL (n : ℕ) : SecondCountableTopology (GL (Fin n) ℂ) := by
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

theorem isClosed_nilrad (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) :
    IsClosed (nilrad W₁ W₂ : Set (Matrix (Fin n) (Fin n) ℂ)) := by
  haveI : FiniteDimensional ℂ (Matrix (Fin n) (Fin n) ℂ) := inferInstance
  letI : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) := Matrix.normedAddCommGroup
  letI : NormedSpace ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.normedSpace
  exact Submodule.closed_of_finiteDimensional (nilrad W₁ W₂)

theorem locallyCompact_nilrad (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) :
    LocallyCompactSpace (nilrad W₁ W₂) := by
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  exact (isClosed_nilrad W₁ W₂).isClosedEmbedding_subtypeVal.locallyCompactSpace

theorem secondCountable_nilrad (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) :
    SecondCountableTopology (nilrad W₁ W₂) := by
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  exact TopologicalSpace.Subtype.secondCountableTopology _

theorem nil_mul_mem {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} (hW : W₁ ≤ W₂)
    {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ nilrad W₁ W₂) (hY : Y ∈ nilrad W₁ W₂) :
    X * Y ∈ nilrad W₁ W₂ := by
  refine ⟨fun y => ?_, fun y hy => ?_, fun y hy => ?_⟩
  · rw [← Matrix.mulVec_mulVec]; exact hW (hX.2.1 _ (hY.1 y))
  · rw [← Matrix.mulVec_mulVec, hX.2.2 _ (hY.2.1 y hy)]; exact W₁.zero_mem
  · rw [← Matrix.mulVec_mulVec, hY.2.2 y hy, Matrix.mulVec_zero]

def nmul {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} (hW : W₁ ≤ W₂) (Y X : nilrad W₁ W₂) : nilrad W₁ W₂ :=
  ⟨Y.1 + X.1 + Y.1 * X.1, (nilrad W₁ W₂).add_mem ((nilrad W₁ W₂).add_mem Y.2 X.2) (nil_mul_mem hW Y.2 X.2)⟩

theorem uOf_nmul {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} (hW : W₁ ≤ W₂) (Y X : nilrad W₁ W₂) :
    uOf (nmul hW Y X) = uOf Y * uOf X := by
  apply Units.ext
  simp only [uOf_val, Units.val_mul, nmul]
  noncomm_ring

def ninv {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} (hW : W₁ ≤ W₂) (X : nilrad W₁ W₂) : nilrad W₁ W₂ :=
  ⟨-X.1 + X.1 * X.1, (nilrad W₁ W₂).add_mem ((nilrad W₁ W₂).neg_mem X.2) (nil_mul_mem hW X.2 X.2)⟩

theorem uOf_ninv {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} (hW : W₁ ≤ W₂) (X : nilrad W₁ W₂) :
    uOf (ninv hW X) = (uOf X)⁻¹ := by
  apply Units.ext
  rw [uOf_val, ninv]
  change _ = 1 - X.1 + X.1 * X.1
  noncomm_ring

def nSet (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) (C : Set (GL (Fin n) ℂ)) : Set (GL (Fin n) ℂ) :=
  {g | ∃ X : nilrad W₁ W₂, ∃ c ∈ C, uOf X * c = g}

theorem exists_open_cover (n : ℕ) : ∃ U : ℕ → Set (GL (Fin n) ℂ),
    (∀ i, IsOpen (U i)) ∧ (∀ i, IsCompact (closure (U i))) ∧ ∀ g, ∃ i, g ∈ U i := by
  haveI := locallyCompact_GL n
  haveI := secondCountable_GL n
  haveI : SigmaCompactSpace (GL (Fin n) ℂ) := inferInstance
  let K := CompactExhaustion.choice (GL (Fin n) ℂ)
  refine ⟨fun i => interior (K i), fun i => isOpen_interior, fun i => ?_, fun g => ?_⟩
  · exact (K.isCompact i).of_isClosed_subset isClosed_closure
      (closure_minimal interior_subset (K.isCompact i).isClosed)
  · obtain ⟨i, hi⟩ := K.exists_mem g
    exact ⟨i + 1, K.subset_interior_succ i hi⟩

theorem isClosed_twCent (d : GL (Fin n) ℂ) :
    IsClosed (twCent (thC n) d : Set (GL (Fin n) ℂ)) := by
  have h : Continuous fun g : GL (Fin n) ℂ => g⁻¹ * d * thC n g :=
    (continuous_inv.mul continuous_const).mul continuous_thC
  exact isClosed_eq h continuous_const

theorem locallyCompact_twCent (d : GL (Fin n) ℂ) : LocallyCompactSpace (twCent (thC n) d) := by
  haveI := locallyCompact_GL n
  exact (isClosed_twCent d).isClosedEmbedding_subtypeVal.locallyCompactSpace

theorem sigmaFinite_twCent [MeasurableSpace (GL (Fin n) ℂ)] [BorelSpace (GL (Fin n) ℂ)]
    (d : GL (Fin n) ℂ) (μd : Measure (twCent (thC n) d)) [μd.IsHaarMeasure] : SigmaFinite μd := by
  haveI := locallyCompact_twCent d
  haveI := secondCountable_GL n
  haveI : SecondCountableTopology (twCent (thC n) d) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  infer_instance

theorem invInvariant_twCent [MeasurableSpace (GL (Fin n) ℂ)] [BorelSpace (GL (Fin n) ℂ)]
    (d : GL (Fin n) ℂ) (μd : Measure (twCent (thC n) d)) [μd.IsHaarMeasure]
    (hc : ∀ a ∈ twCent (thC n) d, ∀ b ∈ twCent (thC n) d, a * b = b * a) : μd.IsInvInvariant := by
  haveI := locallyCompact_twCent d
  haveI := secondCountable_GL n
  letI : CommGroup (twCent (thC n) d) :=
    { (inferInstance : Group (twCent (thC n) d)) with
      mul_comm := fun a b => Subtype.ext (hc a a.2 b b.2) }
  haveI : SecondCountableTopology (twCent (thC n) d) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  exact Measure.IsHaarMeasure.isInvInvariant_of_regular μd

end GlobalTheory.CompanionTheory.LocVan
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SignConeWeightTranslation
section
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.ChainSum

theorem sdot_measurable {m : ℕ} (e : Fin m → SignType) : Measurable (sdot e) := by
  unfold sdot
  exact Finset.measurable_fun_sum _ fun i _ => (measurable_pi_apply i).const_mul _

theorem sdot_add' {m : ℕ} (e : Fin m → SignType) (a b : Fin m → ℝ) :
    sdot e (a + b) = sdot e a + sdot e b := by
  simp [sdot, mul_add, Finset.sum_add_distrib]

theorem chainSum_rest : ∀ m : ℕ, (∀ y : (Fin m → SignType) → ℝ, Measurable (gam y)) ∧
    (∀ (y : (Fin m → SignType) → ℝ) a b, gam (fun e => y e + sdot e b) (a + b) = gam y a) ∧
    ∀ (y y' : (Fin m → SignType) → ℝ) e s t a, (∀ e', SLe e e' ∨ SLe e' e → y e' = y' e') →
      gam (Function.update y e s) a - gam (Function.update y e t) a =
        gam (Function.update y' e s) a - gam (Function.update y' e t) a := by
  intro m
  refine ⟨fun y => ?_, fun y a b => ?_, fun y y' e s t a h => ?_⟩
  · unfold gam gamOn
    refine Finset.measurable_fun_sum _ fun c _ => ?_
    refine Measurable.const_mul (Finset.measurable_fun_prod _ fun e _ => ?_) _
    exact Measurable.ite (measurableSet_lt measurable_const (sdot_measurable e))
      measurable_const measurable_const
  · unfold gam gamOn
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    refine Finset.prod_congr rfl fun e _ => ?_
    have hiff : (y e + sdot e b < sdot e (a + b)) ↔ y e < sdot e a := by
      rw [sdot_add']
      exact add_lt_add_iff_right _
    exact if_congr hiff rfl rfl
  · unfold gam gamOn
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun c hc => ?_
    have hchain : IsChain SLe (↑c : Set (Fin m → SignType)) := by
      simp only [Finset.mem_filter] at hc
      exact hc.2.2.1
    by_cases hec : e ∈ c
    · have key : ∀ u : ℝ, (∏ e' ∈ c, if Function.update y e u e' < sdot e' a then (1 : ℝ) else 0) =
          ∏ e' ∈ c, if Function.update y' e u e' < sdot e' a then (1 : ℝ) else 0 := by
        intro u
        refine Finset.prod_congr rfl fun e' he' => ?_
        by_cases hne : e' = e
        · subst hne
          simp only [Function.update_self]
        · have hcmp : SLe e e' ∨ SLe e' e :=
            hchain (Finset.mem_coe.2 hec) (Finset.mem_coe.2 he') (Ne.symm hne)
          simp only [Function.update_of_ne hne, h e' hcmp]
      rw [key s, key t]
    · have key : ∀ (z : (Fin m → SignType) → ℝ) (u v : ℝ),
          (∏ e' ∈ c, if Function.update z e u e' < sdot e' a then (1 : ℝ) else 0) =
            ∏ e' ∈ c, if Function.update z e v e' < sdot e' a then (1 : ℝ) else 0 := by
        intro z u v
        refine Finset.prod_congr rfl fun e' he' => ?_
        have hne : e' ≠ e := fun hh => hec (hh ▸ he')
        simp only [Function.update_of_ne hne]
      rw [key y s t, key y' s t, sub_self, sub_self]

end GlobalTheory.CompanionTheory.ChainSum
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SizeBasicOfConjPlaces
section
noncomputable section

open NumberField IsDedekindDomain Matrix Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.Size

theorem le_sup {ι : Type} [Finite ι] (f : ι → ℝ) (p : ι) : f p ≤ ⨆ q, f q :=
  le_ciSup (Set.finite_range f).bddAbove p

theorem sz_nonneg {K ι κ : Type} [NormedField K] (g : Matrix ι κ K) : 0 ≤ sz g :=
  Real.iSup_nonneg fun _ => norm_nonneg _

theorem sz_mul_le {K : Type} [NormedField K] [IsUltrametricDist K] {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) K) : sz (A * B) ≤ sz A * sz B := by
  have hA := sz_nonneg A
  have hB := sz_nonneg B
  refine Real.iSup_le (fun p => ?_) (mul_nonneg hA hB)
  rw [Matrix.mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hA hB) fun k _ => ?_
  rw [norm_mul]
  exact mul_le_mul (le_sup (fun q : Fin n × Fin n => ‖A q.1 q.2‖) (p.1, k))
    (le_sup (fun q : Fin n × Fin n => ‖B q.1 q.2‖) (k, p.2)) (norm_nonneg _) hA

def s2 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : ℝ := ⨆ p : Fin n × Fin n, ‖A p.1 p.2‖ ^ 2

theorem max_sq_entry_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ s2 A :=
  Real.iSup_nonneg fun _ => sq_nonneg _

theorem norm_entry_le_sqrt_max_sq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    ‖A i j‖ ≤ √(s2 A) :=
  Real.le_sqrt_of_sq_le (le_sup (fun q : Fin n × Fin n => ‖A q.1 q.2‖ ^ 2) (i, j))

theorem max_sq_entry_mul_le {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    s2 (A * B) ≤ (n : ℝ) ^ 2 * s2 A * s2 B := by
  have hA := max_sq_entry_nonneg A
  have hB := max_sq_entry_nonneg B
  refine Real.iSup_le (fun p => ?_) (mul_nonneg (mul_nonneg (sq_nonneg _) hA) hB)
  have h1 : ‖(A * B) p.1 p.2‖ ≤ n * (√(s2 A) * √(s2 B)) := by
    rw [Matrix.mul_apply]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k, ‖A p.1 k * B k p.2‖ ≤ ∑ _k : Fin n, √(s2 A) * √(s2 B) :=
          Finset.sum_le_sum fun k _ => by
            rw [norm_mul]
            exact mul_le_mul (norm_entry_le_sqrt_max_sq A _ _) (norm_entry_le_sqrt_max_sq B _ _) (norm_nonneg _)
              (Real.sqrt_nonneg _)
      _ = n * (√(s2 A) * √(s2 B)) := by simp
  calc ‖(A * B) p.1 p.2‖ ^ 2 ≤ (n * (√(s2 A) * √(s2 B))) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = (n : ℝ) ^ 2 * s2 A * s2 B := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hB, mul_assoc]

theorem finsum_mono {α : Type} {f g : α → ℝ} (hf : (Function.support f).Finite)
    (hg : (Function.support g).Finite) (h : ∀ a, f a ≤ g a) : ∑ᶠ a, f a ≤ ∑ᶠ a, g a := by
  classical
  rw [finsum_eq_sum_of_support_subset f (s := hf.toFinset ∪ hg.toFinset) (by simp),
    finsum_eq_sum_of_support_subset g (s := hf.toFinset ∪ hg.toFinset) (by simp)]
  exact Finset.sum_le_sum fun a _ => h a

theorem posLog_max_one {x : ℝ} (hx : 0 ≤ x) : Real.posLog (max x 1) = Real.posLog x := by
  rcases le_total x 1 with h | h
  · rw [max_eq_right h, (Real.posLog_eq_zero_iff x).2 (by rwa [abs_of_nonneg hx])]
    simp
  · rw [max_eq_left h]

section Global

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ}

theorem logSizeM_eq (A : Matrix (Fin n) (Fin n) (Ad E)) :
    logSizeM A = ∑ v, Real.posLog (s2 (A.map (cV v))) + ∑ᶠ w, Real.posLog (sz (A.map (cW w))) :=
  rfl

theorem logSizeM_nonneg (A : Matrix (Fin n) (Fin n) (Ad E)) : 0 ≤ logSizeM A :=
  add_nonneg (Finset.sum_nonneg fun _ _ => Real.posLog_nonneg)
    (finsum_nonneg fun _ => Real.posLog_nonneg)

theorem supp_fin (hS : SzFin) (A : Matrix (Fin n) (Fin n) (Ad E)) :
    (Function.support fun w => Real.posLog (sz (A.map (cW w)))).Finite := by
  refine (hS E (Fin n) (Fin n) A).subset fun w hw => ?_
  by_contra h
  exact hw ((Real.posLog_eq_zero_iff _).2 (by rw [abs_of_nonneg (sz_nonneg _)]; exact not_lt.1 h))

theorem logSizeM_mul (hS : SzFin) (A B : Matrix (Fin n) (Fin n) (Ad E)) :
    logSizeM (A * B) ≤ logSizeM A + logSizeM B +
      Fintype.card (InfinitePlace E) * Real.posLog ((n : ℝ) ^ 2) := by
  have hinf : ∑ v, Real.posLog (s2 ((A * B).map (cV v))) ≤
      ∑ v, Real.posLog (s2 (A.map (cV v))) + ∑ v, Real.posLog (s2 (B.map (cV v))) +
        Fintype.card (InfinitePlace E) * Real.posLog ((n : ℝ) ^ 2) := by
    have : ∀ v, Real.posLog (s2 ((A * B).map (cV v))) ≤
        Real.posLog (s2 (A.map (cV v))) + Real.posLog (s2 (B.map (cV v))) +
          Real.posLog ((n : ℝ) ^ 2) := fun v => by
      rw [Matrix.map_mul]
      refine (Real.posLog_le_posLog (max_sq_entry_nonneg _) (max_sq_entry_mul_le _ _)).trans ?_
      refine Real.posLog_mul.trans ?_
      have := Real.posLog_mul (x := (n : ℝ) ^ 2) (y := s2 (A.map (cV v)))
      linarith
    refine (Finset.sum_le_sum fun v _ => this v).trans (le_of_eq ?_)
    simp [Finset.sum_add_distrib]
  have hfin : ∑ᶠ w, Real.posLog (sz ((A * B).map (cW w))) ≤
      ∑ᶠ w, Real.posLog (sz (A.map (cW w))) + ∑ᶠ w, Real.posLog (sz (B.map (cW w))) := by
    rw [← finsum_add_distrib (supp_fin hS A) (supp_fin hS B)]
    refine finsum_mono (supp_fin hS _) (((supp_fin hS A).union (supp_fin hS B)).subset
      (Function.support_add _ _)) fun w => ?_
    rw [Matrix.map_mul]
    exact (Real.posLog_le_posLog (sz_nonneg _) (sz_mul_le _ _)).trans Real.posLog_mul
  rw [logSizeM_eq, logSizeM_eq, logSizeM_eq]
  linarith

theorem continuous_cV (v : InfinitePlace E) : Continuous (cV v : Ad E → ℂ) :=
  (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
    (IsTotallyComplex.isComplex v)).continuous.comp ((continuous_apply v).comp continuous_fst)

theorem eventually_fin (a₀ : Ad E) :
    ∀ᶠ a in 𝓝 a₀, ∀ w, ‖cW w a‖ ≤ max ‖cW w a₀‖ 1 := by
  have hU : IsOpen {f : Af E | ∀ w, f w ∈ (w.adicCompletionIntegers E : Set (w.adicCompletion E))} :=
    RestrictedProduct.isOpen_forall_mem fun w => Valued.isOpen_valuationSubring _
  have hc : Continuous fun a : Ad E => pFin E a - pFin E a₀ :=
    (continuous_snd).sub continuous_const
  have h0 : (fun a : Ad E => pFin E a - pFin E a₀) a₀ ∈
      {f : Af E | ∀ w, f w ∈ (w.adicCompletionIntegers E : Set (w.adicCompletion E))} := by
    intro w
    change (pFin E a₀ - pFin E a₀) w ∈ w.adicCompletionIntegers E
    rw [sub_self]
    exact zero_mem (w.adicCompletionIntegers E)
  filter_upwards [hc.continuousAt.eventually (hU.mem_nhds h0)] with a ha w
  have h1 : ‖cW w a - cW w a₀‖ ≤ 1 := by
    have := ha w
    exact Valued.toNormedField.norm_le_one_iff.2 this
  have h2 : cW w a = (cW w a - cW w a₀) + cW w a₀ := by ring
  rw [h2]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · exact h1.trans (le_max_right _ _)
  · exact le_max_left _ _

theorem logSizeM_locBdd (hS : SzFin) (A₀ : Matrix (Fin n) (Fin n) (Ad E)) :
    ∃ r, ∀ᶠ A in 𝓝 A₀, logSizeM A ≤ r := by
  refine ⟨∑ v, Real.posLog (⨆ p : Fin n × Fin n, (‖cV v (A₀ p.1 p.2)‖ + 1) ^ 2) +
    ∑ᶠ w, Real.posLog (sz (A₀.map (cW w))), ?_⟩
  have hev : ∀ p : Fin n × Fin n, ∀ᶠ A : Matrix (Fin n) (Fin n) (Ad E) in 𝓝 A₀,
      (∀ v, ‖cV v (A p.1 p.2)‖ ≤ ‖cV v (A₀ p.1 p.2)‖ + 1) ∧
        ∀ w, ‖cW w (A p.1 p.2)‖ ≤ max ‖cW w (A₀ p.1 p.2)‖ 1 := fun p => by
    have hc : Continuous fun A : Matrix (Fin n) (Fin n) (Ad E) => A p.1 p.2 :=
      continuous_id.matrix_elem p.1 p.2
    refine Filter.Eventually.and ?_ (hc.continuousAt.eventually (eventually_fin (A₀ p.1 p.2)))
    refine Filter.eventually_all.2 fun v => ?_
    have hc' : Continuous fun A : Matrix (Fin n) (Fin n) (Ad E) => ‖cV v (A p.1 p.2)‖ :=
      ((continuous_cV v).comp hc).norm
    exact (hc'.continuousAt.eventually (gt_mem_nhds (lt_add_one _))).mono fun _ h => h.le
  filter_upwards [Filter.eventually_all.2 hev] with A hA
  rw [logSizeM_eq]
  refine add_le_add (Finset.sum_le_sum fun v _ => ?_) ?_
  · refine Real.posLog_le_posLog (max_sq_entry_nonneg _) (Real.iSup_le (fun p => ?_)
      (Real.iSup_nonneg fun _ => sq_nonneg _))
    exact (pow_le_pow_left₀ (norm_nonneg _) ((hA p).1 v) 2).trans
      (le_sup (fun q : Fin n × Fin n => (‖cV v (A₀ q.1 q.2)‖ + 1) ^ 2) p)
  · refine finsum_mono (supp_fin hS A) (supp_fin hS A₀) fun w => ?_
    rw [← posLog_max_one (sz_nonneg (A₀.map (cW w)))]
    refine Real.posLog_le_posLog (sz_nonneg _) (Real.iSup_le (fun p => ?_) (by positivity))
    exact ((hA p).2 w).trans (max_le_max_right 1
      (le_sup (fun q : Fin n × Fin n => ‖cW w (A₀ q.1 q.2)‖) p))

theorem logSize_compact (hS : SzFin) (C : Set (GA E n)) (hC : IsCompact C) :
    ∃ r, ∀ g ∈ C, logSize g ≤ r := by
  refine hC.induction_on (p := fun S => ∃ r, ∀ g ∈ S, logSize g ≤ r) ⟨0, by simp⟩
    (fun s t hst ⟨r, hr⟩ => ⟨r, fun g hg => hr g (hst hg)⟩)
    (fun s t ⟨r, hr⟩ ⟨r', hr'⟩ => ⟨max r r', fun g hg => hg.elim
      (fun h => (hr g h).trans (le_max_left _ _)) (fun h => (hr' g h).trans (le_max_right _ _))⟩)
    fun x _ => ?_
  obtain ⟨r₁, h₁⟩ := logSizeM_locBdd hS x.val
  obtain ⟨r₂, h₂⟩ := logSizeM_locBdd hS (x⁻¹ : GA E n).val
  have e₁ := (Units.continuous_val (M := Matrix (Fin n) (Fin n) (Ad E))).continuousAt.eventually h₁
  have e₂ := (Units.continuous_coe_inv (M := Matrix (Fin n) (Fin n) (Ad E))).continuousAt.eventually h₂
  refine ⟨{g | logSize g ≤ r₁ + r₂}, mem_nhdsWithin_of_mem_nhds ?_, ⟨r₁ + r₂, fun g hg => hg⟩⟩
  filter_upwards [e₁, e₂] with g a b
  exact add_le_add a b

end Global

section CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem logSizeM_conj (hC : ConjPlaces) (A : Matrix (Fin n) (Fin n) (Ad E)) :
    logSizeM ((A.map (conjAd E))ᵀ) = logSizeM A := by
  obtain ⟨h1, -, π, ψ, hψ, h3⟩ := hC E
  have hinf : ∀ v, (⨆ p : Fin n × Fin n, ‖cV v ((A.map (conjAd E))ᵀ p.1 p.2)‖ ^ 2) =
      ⨆ p : Fin n × Fin n, ‖cV v (A p.1 p.2)‖ ^ 2 := fun v => by
    rw [← (Equiv.prodComm (Fin n) (Fin n)).iSup_comp
      (g := fun p : Fin n × Fin n => ‖cV v (A p.1 p.2)‖ ^ 2)]
    refine iSup_congr fun p => ?_
    simp [h1, Matrix.transpose_apply]
  have hfin : ∀ w, (⨆ p : Fin n × Fin n, ‖cW w ((A.map (conjAd E))ᵀ p.1 p.2)‖) =
      ⨆ p : Fin n × Fin n, ‖cW (π w) (A p.1 p.2)‖ := fun w => by
    rw [← (Equiv.prodComm (Fin n) (Fin n)).iSup_comp
      (g := fun p : Fin n × Fin n => ‖cW (π w) (A p.1 p.2)‖)]
    refine iSup_congr fun p => ?_
    simp [h3, hψ, Matrix.transpose_apply]
  unfold logSizeM
  simp only [hinf, hfin]
  congr 1
  exact finsum_comp_equiv π
    (f := fun w => Real.posLog (⨆ p : Fin n × Fin n, ‖cW w (A p.1 p.2)‖))

theorem inv_thetaR_val {A : Type} [CommRing A] (σ : A →+* A) (g : GL (Fin n) A) :
    ((thetaR σ n g)⁻¹ : GL (Fin n) A).val = (g.val.map σ)ᵀ := rfl

end CM

theorem sizeBasic : SzFin → ConjPlaces → SizeBasic := by
  intro hS hC E _ _ _ n
  refine ⟨logSize_compact hS, fun g => add_nonneg (logSizeM_nonneg _) (logSizeM_nonneg _),
    fun g => ?_, 2 * (Fintype.card (InfinitePlace E) * Real.posLog ((n : ℝ) ^ 2)), fun g h => ?_⟩
  · change logSizeM (thetaR (conjAd E) n g).val + logSizeM ((thetaR (conjAd E) n g)⁻¹ : GA E n).val = _
    rw [inv_thetaR_val, thetaR_val, logSizeM_conj hC, logSizeM_conj hC, logSize, add_comm]
  · have a := logSizeM_mul hS g.val h.val
    have b := logSizeM_mul hS (h⁻¹ : GA E n).val (g⁻¹ : GA E n).val
    simp only [logSize, _root_.mul_inv_rev, Units.val_mul]
    linarith

end GlobalTheory.CompanionTheory.Size

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SpanSectionsAllAffinesOfCover
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GlobalTheory.CompanionTheory.GE.UV

theorem subsingleton_cokernel_desc_of_span {X : Scheme.{0}} {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : ι → X.Modules} {G : X.Modules} [∀ i, (F i).IsQuasicoherent] [G.IsQuasicoherent]
    [(biproduct F).IsQuasicoherent] (φ : ∀ i, F i ⟶ G) {V : X.Opens} (hV : IsAffineOpen V)
    (h : Submodule.span Γ(X, V) (⋃ i, Set.range ((φ i).app V)) = ⊤) :
    Subsingleton Γ(cokernel (biproduct.desc φ), V) := by
  refine subsingleton_of_forall_eq 0 fun s => ?_
  obtain ⟨t, rfl⟩ := GroundTheory.Arith.SchemeCoh.surjective_cokernel_π_app (biproduct.desc φ) hV s
  have hle : Submodule.span Γ(X, V) (⋃ i, Set.range ((φ i).app V)) ≤
      LinearMap.ker (GlobalTheory.QCoh.appLinear (cokernel.π (biproduct.desc φ)) V) := by
    refine Submodule.span_le.2 ?_
    intro y hy
    obtain ⟨i, x, rfl⟩ := Set.mem_iUnion.1 hy
    have hz : φ i ≫ cokernel.π (biproduct.desc φ) = 0 := by
      rw [← biproduct.ι_desc φ i, Category.assoc, cokernel.condition, comp_zero]
    change (cokernel.π (biproduct.desc φ)).app V ((φ i).app V x) = 0
    rw [GlobalTheory.QCoh.app_app, hz]
    rfl
  have ht : t ∈ LinearMap.ker (GlobalTheory.QCoh.appLinear (cokernel.π (biproduct.desc φ)) V) :=
    hle (h ▸ Submodule.mem_top)
  exact ht

theorem span_range_app_eq_top_of_surjective {X : Scheme.{0}} {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : ι → X.Modules} {G : X.Modules} (φ : ∀ i, F i ⟶ G) (U : X.Opens)
    (h : Function.Surjective ((biproduct.desc φ).app U)) :
    Submodule.span Γ(X, U) (⋃ i, Set.range ((φ i).app U)) = ⊤ := by
  refine (Submodule.eq_top_iff').2 fun s => ?_
  obtain ⟨t, rfl⟩ := h s
  rw [GroundTheory.Arith.SchemeCoh.biproduct_app_eq_sum F U t, map_sum]
  refine Submodule.sum_mem _ fun j _ => Submodule.subset_span (Set.mem_iUnion.2 ⟨j, ?_⟩)
  refine ⟨(biproduct.π F j).app U t, ?_⟩
  rw [GlobalTheory.QCoh.app_app (biproduct.ι F j), biproduct.ι_desc]

theorem span_range_app_eq_top_of_local : ∀ {X : AlgebraicGeometry.Scheme.{0}} {ι : Type} [Finite ι]
    {F : ι → X.Modules} {G : X.Modules}, (∀ i, (F i).IsQuasicoherent) → G.IsQuasicoherent →
    ∀ (φ : ∀ i, F i ⟶ G), (∀ x : X, ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
      Submodule.span Γ(X, U) (⋃ i, Set.range ((φ i).app U)) = ⊤) →
    ∀ (U : X.affineOpens), Submodule.span Γ(X, U) (⋃ i, Set.range ((φ i).app U)) = ⊤ := by
  intro X ι _ F G hF hG φ hloc U
  classical
  haveI := Fintype.ofFinite ι
  haveI := hF
  haveI := hG
  haveI : (biproduct F).IsQuasicoherent := GroundTheory.Arith.SchemeCoh.isQuasicoherent_biproduct F
  choose W hxW hW using hloc
  have hcov : TopologicalSpace.IsOpenCover (fun x : X => (W x : X.Opens)) := by
    refine eq_top_iff.2 fun x _ => ?_
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxW x⟩
  have hzero : IsZero (cokernel (biproduct.desc φ)) :=
    (GlobalTheory.QCoh.isZero_iff_affineCover (fun x : X => (W x : X.Opens)) hcov (fun x => (W x).2)).2
      fun x => subsingleton_cokernel_desc_of_span φ (W x).2 (hW x)
  haveI : Epi (biproduct.desc φ) := Preadditive.epi_of_isZero_cokernel _ hzero
  exact span_range_app_eq_top_of_surjective φ U
    (GlobalTheory.QCoh.surjective_app_of_epi (biproduct.desc φ) U.2)

end GlobalTheory.CompanionTheory.GE.UV
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorDirectSumBasisEquivStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_direct_sum_basis_equiv : ∀ {K : Type} [Field K] {J : Type} [DecidableEq J] (V W : J → Type 1) [∀ t, AddCommGroup (V t)] [∀ t, Module K (V t)] [∀ t, AddCommGroup (W t)] [∀ t, Module K (W t)] (B : J → Type 1) [DecidableEq (Σ t, B t)] (b : ∀ t, Module.Basis (B t) K (V t)), ∃ e : (⨁ t, V t ⊗[K] W t) ≃ₗ[K] ⨁ u : (Σ t, B t), W u.1, ∀ (t : J) (β : B t) (x : W t), e (DirectSum.lof K J (fun t => V t ⊗[K] W t) t (b t β ⊗ₜ x)) = DirectSum.lof K (Σ t, B t) (fun u => W u.1) ⟨t, β⟩ x := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.tensBasis | exact GlobalTheory.CompanionTheory.KunGlue.tensBasis | (intros; apply GlobalTheory.CompanionTheory.KunGlue.tensBasis <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedIdealPowerLeSectionsStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_ideal_power_le_sections : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), GlobalTheory.IsAmpleLB H → ∀ {P : X.Modules}, IsCoherent P → ∀ (n : ℤ) (m : ℕ), twPow I H n P m ⊆ twSecs H n (powSub I P m) := by
  first | exact @GlobalTheory.CompanionTheory.GE.twPow_subset_twSecs | exact GlobalTheory.CompanionTheory.GE.twPow_subset_twSecs | (intros; apply GlobalTheory.CompanionTheory.GE.twPow_subset_twSecs <;> assumption)
end

