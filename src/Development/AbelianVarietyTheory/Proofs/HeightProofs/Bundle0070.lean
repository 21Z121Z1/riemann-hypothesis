import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0242
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV
import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0065
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0241
import Development.AbelianVarietyTheory.Proofs.HeightProofs.KProjectionLimitDiscreteSeriesCoeffs
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.NormComparisonConstants
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0004
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeMemAvoidedPrimes
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0061

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSubOrthogonal
section
namespace GlobalTheory.OrthogonalProjectionPoly

open MeasureTheory

theorem exists_sub_orthogonal {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
    [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ] (V : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ V]
    (hV : ∀ q ∈ V, Continuous q) (p : X → ℂ) (hp : Continuous p) :
    ∃ p' ∈ V, ∀ q ∈ V, ∫ x, star (q x) * (p x - p' x) ∂μ = 0 := by
  classical
  let j : V →ₗ[ℂ] C(X, ℂ) :=
    { toFun := fun q => ⟨q, hV q q.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let T : V →ₗ[ℂ] Lp ℂ 2 μ := (ContinuousMap.toLp 2 μ ℂ : C(X, ℂ) →L[ℂ] Lp ℂ 2 μ).toLinearMap ∘ₗ j
  let W : Submodule ℂ (Lp ℂ 2 μ) := LinearMap.range T
  have : FiniteDimensional ℂ W := LinearMap.finiteDimensional_range T
  let P : C(X, ℂ) := ⟨p, hp⟩
  obtain ⟨p', hp'⟩ := LinearMap.mem_range.1 (W.starProjection_apply_mem (ContinuousMap.toLp 2 μ ℂ P))
  refine ⟨p', p'.2, fun q hq => ?_⟩
  have h0 := W.starProjection_inner_eq_zero (ContinuousMap.toLp 2 μ ℂ P) (T ⟨q, hq⟩) ⟨⟨q, hq⟩, rfl⟩
  rw [← hp'] at h0
  have h1 : ContinuousMap.toLp 2 μ ℂ P - T p' = ContinuousMap.toLp 2 μ ℂ (P - j p') := by
    rw [map_sub]
    rfl
  rw [h1] at h0
  have h2 : inner ℂ (ContinuousMap.toLp 2 μ ℂ (P - j p')) (T ⟨q, hq⟩) =
      ∫ x, q x * (starRingEnd ℂ) (p x - (p' : X → ℂ) x) ∂μ :=
    ContinuousMap.inner_toLp μ (P - j p') (j ⟨q, hq⟩)
  rw [h2] at h0
  calc ∫ x, star (q x) * (p x - (p' : X → ℂ) x) ∂μ
      = ∫ x, (starRingEnd ℂ) (q x * (starRingEnd ℂ) (p x - (p' : X → ℂ) x)) ∂μ := by
        congr 1
        funext x
        rw [map_mul, Complex.conj_conj, starRingEnd_apply, _root_.mul_comm]
    _ = (starRingEnd ℂ) (∫ x, q x * (starRingEnd ℂ) (p x - (p' : X → ℂ) x) ∂μ) := integral_conj
    _ = 0 := by rw [h0, map_zero]

theorem exists_proj_polyV : ∀ {n : ℕ} (ε : Fin n → Bool) (d : ℕ) (p : ↥(Formalism.REAL.KG ε) → ℂ), Continuous p →
    ∃ p' ∈ GlobalTheory.KFourier.polyV ε d, ∀ q ∈ GlobalTheory.KFourier.polyV ε d,
      ∫ (k : ↥(Formalism.REAL.KG ε)), Star.star (q k) * (p k - p' k) ∂ Formalism.REAL.muK ε = (0 : ℂ) := by
  intro n ε d p hp
  exact exists_sub_orthogonal (Formalism.REAL.muK ε) (GlobalTheory.KFourier.polyV ε d)
    (fun q hq => GlobalTheory.KFourier.continuous_of_mem hq) p hp

end GlobalTheory.OrthogonalProjectionPoly
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.FinrankCompactUnitaryPolyFunDegLELe
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

namespace GlobalTheory.KFourier

theorem mono_eq_prod_pow {n : ℕ} (ε : Fin n → Bool) (s : List (Fin n × Fin n × Bool)) (k : KG ε) :
    mono ε s k = ∏ c : Fin n × Fin n × Bool, coord ε c k ^ s.count c := by
  classical
  unfold mono
  rw [Finset.prod_list_map_count]
  have h := Finset.prod_subset (M := ℂ) (f := fun c => coord ε c k ^ s.count c) (Finset.subset_univ (s.toFinset))
    (fun c _ hc => by rw [List.count_eq_zero_of_not_mem (by simpa using hc), pow_zero])
  convert h using 4
  all_goals exact lawful_beq_subsingleton _ _

theorem finrank_polyV_le {n : ℕ} (ε : Fin n → Bool) (d : ℕ) :
    Module.finrank ℂ (polyV ε d) ≤ (d + 1) ^ (2 * n ^ 2) := by
  classical
  let b : ((Fin n × Fin n × Bool) → Fin (d + 1)) → (KG ε → ℂ) :=
    fun f k => ∏ c : Fin n × Fin n × Bool, coord ε c k ^ (f c : ℕ)
  have hle : polyV ε d ≤ Submodule.span ℂ (Set.range b) := by
    rw [polyV_eq]
    refine Submodule.span_le.2 ?_
    rintro φ ⟨s, hs, rfl⟩
    refine Submodule.subset_span ⟨fun c => ⟨s.count c, Nat.lt_succ_of_le ((List.count_le_length).trans hs)⟩, ?_⟩
    funext k
    rw [mono_eq_prod_pow]
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range b)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range b)
  calc Module.finrank ℂ (polyV ε d) ≤ Module.finrank ℂ (Submodule.span ℂ (Set.range b)) :=
        Submodule.finrank_mono hle
    _ ≤ Fintype.card ((Fin n × Fin n × Bool) → Fin (d + 1)) := finrank_range_le_card b
    _ = (d + 1) ^ (2 * n ^ 2) := by
        simp [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
        ring

end GlobalTheory.KFourier
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.HasDerivAtMatrixExpEntryReal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KFourier

open MeasureTheory

variable {n : ℕ}

theorem coord_mul_eq_sum (ε : Fin n → Bool) (c : Fin n × Fin n × Bool) (a k : KG ε) :
    coord ε c (a * k) = ∑ l : Fin n, coord ε (c.1, l, c.2.2) a * coord ε (l, c.2.1, c.2.2) k := by
  simp only [coord, toMK_mul, Matrix.mul_apply]
  split_ifs
  · rfl
  · rw [star_sum]; exact Finset.sum_congr rfl fun l _ => by rw [star_mul', mul_comm]

theorem integrable_muK_of_continuous {ε : Fin n → Bool} {F : KG ε → ℂ} (hF : Continuous F) :
    Integrable F (muK ε) :=
  hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace F)

theorem conv_mono_mem (ε : Fin n → Bool) (s : List (Fin n × Fin n × Bool)) :
    ∀ (d : ℕ), s.length ≤ d → ∀ h : KG ε → ℂ, Continuous h →
      (fun k' : KG ε => ∫ k, mono ε s (k'⁻¹ * k) * h k ∂(muK ε)) ∈ polyV ε d := by
  induction s with
  | nil =>
    intro d _ h _
    simpa [mono] using const_mem ε d (∫ k, h k ∂(muK ε))
  | cons c s ih =>
    intro d hd h hh
    have hd' : s.length + 1 ≤ d := by simpa using hd
    have e : (fun k' : KG ε => ∫ k, mono ε (c :: s) (k'⁻¹ * k) * h k ∂(muK ε)) =
        ∑ l : Fin n, (fun k' : KG ε => coord ε (c.1, l, c.2.2) k'⁻¹) *
          (fun k' : KG ε => ∫ k, mono ε s (k'⁻¹ * k) * (coord ε (l, c.2.1, c.2.2) k * h k) ∂(muK ε)) := by
      funext k'
      simp only [Finset.sum_apply, Pi.mul_apply]
      simp only [← integral_const_mul]
      rw [← integral_finset_sum]
      · refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
        have h1 : mono ε (c :: s) (k'⁻¹ * k) = coord ε c (k'⁻¹ * k) * mono ε s (k'⁻¹ * k) := by simp [mono]
        simp only [h1, coord_mul_eq_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun l _ => by ring
      · intro l _
        refine integrable_muK_of_continuous (continuous_const.mul ?_)
        exact ((continuous_mono ε s).comp (continuous_const.mul continuous_id)).mul
          ((continuous_coord ε _).mul hh)
    rw [e]
    refine Submodule.sum_mem _ fun l _ => ?_
    exact polyV_mono ε (show 1 + (d - 1) ≤ d by omega)
      (mul_mem (coord_inv_mem ε _) (ih (d - 1) (by omega) _ ((continuous_coord ε _).mul hh)))

theorem conv_mem {ε : Fin n → Bool} {d : ℕ} {e : KG ε → ℂ} (he : e ∈ polyV ε d) {h : KG ε → ℂ}
    (hh : Continuous h) : (fun k' : KG ε => ∫ k, e (k'⁻¹ * k) * h k ∂(muK ε)) ∈ polyV ε d := by
  induction he using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, hs, rfl⟩ := hx
    exact conv_mono_mem ε s d hs h hh
  | zero =>
    simpa using const_mem ε d 0
  | add x y hx hy ihx ihy =>
    convert add_mem ihx ihy using 1
    funext k'
    simp only [Pi.add_apply, add_mul]
    refine integral_add (integrable_muK_of_continuous ?_) (integrable_muK_of_continuous ?_)
    · exact ((continuous_of_mem (d := d) hx).comp (continuous_const.mul continuous_id)).mul hh
    · exact ((continuous_of_mem (d := d) hy).comp (continuous_const.mul continuous_id)).mul hh
  | smul a x _ ih =>
    convert Submodule.smul_mem _ a ih using 1
    funext k'
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]

theorem avgK_mem : ∀ {n : ℕ} (ε : Fin n → Bool) (i : ℕ) (e : KG ε → ℂ), e ∈ GlobalTheory.KFourier.polyV ε i →
    ∀ f : Mx n → ℂ, ContinuousOn f (UJset ε) → ∀ y ∈ UJset ε,
      GlobalTheory.KFourier.avgK ε e f y ∈ GlobalTheory.KFourier.polyV ε i := by
  intro n ε i e he f hf y hy
  have hh : Continuous fun k : KG ε => f (y * toMK k) :=
    hf.comp_continuous (continuous_const.mul (GlobalTheory.TypeSum.continuous_toMK ε))
      fun k => GlobalTheory.TypeSum.mul_mem_UJ hy (GlobalTheory.TypeSum.K_le_UJ (GlobalTheory.TypeSum.toMK_mem_K k))
  convert conv_mem he hh using 1
  funext k'
  rw [← integral_mul_left_eq_self (μ := muK ε) _ k']
  simp only [avgK, inv_mul_cancel_left, toMK_mul, Matrix.mul_assoc]

end GlobalTheory.KFourier

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.HasFDerivAtDerFamProdExpStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory Filter Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasFDerivAt_derFam_mul_prod_exp_smul_zero : ∀ (n : ℕ) (ε : Fin n → Bool) (N : ℕ) (F : List (GlobalTheory.TypeSum.Mx n) → GlobalTheory.TypeSum.Mx n → ℂ),
    GlobalTheory.TypeSum.IsDerFam ε F → GlobalTheory.TypeSum.FamGrowth ε N F →
    ∀ l : List (GlobalTheory.TypeSum.Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ∀ (d : ℕ) (b : Fin d → GlobalTheory.TypeSum.Mx n), (∀ i, b i ∈ lieSet ε) →
    ∀ g ∈ UJset ε, HasFDerivAt (fun t : Fin d → ℝ => F l (g * (List.ofFn fun i => NormedSpace.exp (t i • b i)).prod))
      (∑ i, (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ).smulRight (F (b i :: l) g)) 0 := by
  first | exact @GlobalTheory.TypeSum.hasFDerivAt_derFam_prodExp | exact GlobalTheory.TypeSum.hasFDerivAt_derFam_prodExp | (intros; apply GlobalTheory.TypeSum.hasFDerivAt_derFam_prodExp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.KProjectionLimitDiscreteSeriesCoeffsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kProjection_limit_discreteSeriesCoeffs : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : GlobalTheory.TypeSum.Mx n → (H →L[ℂ] H)), GlobalTheory.TypeSum.Std ε σ →
    ∀ f : GlobalTheory.TypeSum.Mx n → ℂ, ContinuousOn f (UJset ε) →
    (∀ C : Set (Matrix (Fin n) (Fin n) ℂ), IsCompact C → ∀ δ : ℝ, 0 < δ →
      ∃ (m : ℕ) (ℓ : Fin m → (H →ₗ[ℂ] ℂ)) (v : Fin m → H), (∀ j, Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε) σ (ℓ j)) ∧
        (∀ j, SmoothVec (GlobalTheory.SmoothGlob.lieSet ε) σ (v j)) ∧
        ∀ y ∈ C, y ∈ UJset ε → ‖f y - ∑ j, ℓ j (σ y (v j))‖ < δ) →
    ∀ e : ↥(Formalism.REAL.KG ε) → ℂ, Continuous e → GlobalTheory.TypeSum.KFinFun ε e →
    ∃ (d : ℕ) (w : Fin d → H), (∀ a, IsKFin ε σ (w a)) ∧
      ∀ C : Set (Matrix (Fin n) (Fin n) ℂ), IsCompact C → ∀ δ : ℝ, 0 < δ →
        ∃ L : Fin d → (H →ₗ[ℂ] ℂ), (∀ a, Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε) σ (L a)) ∧
          ∀ y ∈ C, y ∈ UJset ε →
            ‖(∫ k, e k * f (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) - ∑ a, L a (σ y (w a))‖ < δ := by
  first | exact @GlobalTheory.TypeSum.kAvg_approx_coef | exact GlobalTheory.TypeSum.kAvg_approx_coef | (intros; apply GlobalTheory.TypeSum.kAvg_approx_coef <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.MeasurableDerFamCompStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory Filter Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurable_derFam_comp_continuous_of_mem_UJset : ∀ (n : ℕ) (ε : Fin n → Bool) (F : List (GlobalTheory.TypeSum.Mx n) → GlobalTheory.TypeSum.Mx n → ℂ), GlobalTheory.TypeSum.IsDerFam ε F →
    ContinuousOn (F []) (UJset ε) → ∀ l : List (GlobalTheory.TypeSum.Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) →
    ∀ (T : Type) [TopologicalSpace T] [MeasurableSpace T] [OpensMeasurableSpace T] (φ : T → GlobalTheory.TypeSum.Mx n),
      Continuous φ → (∀ t, φ t ∈ UJset ε) → Measurable (fun t => F l (φ t)) := by
  first | exact @GlobalTheory.TypeSum.measurable_derFam_comp | exact GlobalTheory.TypeSum.measurable_derFam_comp | (intros; apply GlobalTheory.TypeSum.measurable_derFam_comp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.PairingConvolutionSwap
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open MeasureTheory GlobalTheory.KFourier

noncomputable section
namespace GlobalTheory.KFourier

theorem pairing_convolution_swap {n : ℕ} (ε : Fin n → Bool) (e q g : KG ε → ℂ)
    (he : Continuous e) (hq : Continuous q) (hg : Continuous g) :
    ∫ k', star (q k') * ∫ k, e k * g (k' * k) ∂(muK ε) ∂(muK ε) =
      ∫ y, g y * ∫ x, e x * star (q (y * x⁻¹)) ∂(muK ε) ∂(muK ε) := by
  haveI : IsProbabilityMeasure (muK ε) := (compact_haar_holds n ε).1
  haveI : (muK ε).IsInvInvariant := ⟨(compact_haar_holds n ε).2.2.2⟩
  haveI : SecondCountableTopology (KG ε) :=
    TopologicalSpace.Subtype.secondCountableTopology (KG ε : Set (UJ ε))

  have h1 : ∀ k' : KG ε, ∫ k, e k * g (k' * k) ∂(muK ε) = ∫ y, e (k'⁻¹ * y) * g y ∂(muK ε) := by
    intro k'
    have := integral_mul_left_eq_self (μ := muK ε) (fun y => e (k'⁻¹ * y) * g y) k'
    rw [← this]; simp [← mul_assoc]

  have h2 : ∀ y : KG ε, ∫ k', star (q k') * e (k'⁻¹ * y) ∂(muK ε) =
      ∫ x, e x * star (q (y * x⁻¹)) ∂(muK ε) := by
    intro y
    have a := integral_inv_eq_self (fun x => star (q (y * x)) * e ((y * x)⁻¹ * y)) (muK ε)
    have b := integral_mul_left_eq_self (μ := muK ε) (fun k' => star (q k') * e (k'⁻¹ * y)) y
    rw [← b, ← a]
    congr 1; funext x
    rw [mul_comm]; congr 2; group
  have hcont : Continuous (fun p : KG ε × KG ε => star (q p.1) * e (p.1⁻¹ * p.2) * g p.2) := by
    fun_prop
  have hint : Integrable (Function.uncurry fun (k' y : KG ε) => star (q k') * e (k'⁻¹ * y) * g y)
      ((muK ε).prod (muK ε)) :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc ∫ k', star (q k') * ∫ k, e k * g (k' * k) ∂(muK ε) ∂(muK ε)
      = ∫ k', ∫ y, star (q k') * e (k'⁻¹ * y) * g y ∂(muK ε) ∂(muK ε) := by
        congr 1; funext k'
        rw [h1, ← integral_const_mul]
        congr 1; funext y; ring
    _ = ∫ y, ∫ k', star (q k') * e (k'⁻¹ * y) * g y ∂(muK ε) ∂(muK ε) :=
        integral_integral_swap hint
    _ = ∫ y, g y * ∫ x, e x * star (q (y * x⁻¹)) ∂(muK ε) ∂(muK ε) := by
        congr 1; funext y
        rw [← h2, ← integral_const_mul]
        congr 1; funext k'; ring

end GlobalTheory.KFourier
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.PeterssonSquareIntegrableDefiniteOfLawsStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.CompRat GlobalTheory.Member
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finVol_and_exists_L2DefiniteCuspForms_of_pkgLaws : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ : c.F →+* ℂ) (V : HSp D) (hr : V.rank = r) ι Kf χ (dict : GA D V → Σ k, Frame ((U σ).X k).Ψ r) mu x₀, V.SigOK → GoodEmb c σ → SupDef Xo c U → PkgLaws V hr ι Kf χ (U σ) dict mu x₀ → FinVol V ∧ (∀ k (τ : D.host.E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = xiR D) ∧ ∃ h : CuspL2 U σ V dict mu, L2DefiniteCuspForms U σ V dict mu h := by
  first | exact @GlobalTheory.FinalJoin2.L2.petersson_squareIntegrable_definite_of_laws | exact GlobalTheory.FinalJoin2.L2.petersson_squareIntegrable_definite_of_laws | (intros; apply GlobalTheory.FinalJoin2.L2.petersson_squareIntegrable_definite_of_laws <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.RowsOfPageFix
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FinalRows

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Pj GlobalTheory.Mem GlobalTheory.EX GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.FieldSize Formalism.MainNotions.WeightAlgebra

theorem rows_of_pageFix : ∀ (eps : ℝ) (Fm : FamP eps), DC.PageFix Fm → 1000 ≤ Fm.CP → ∃ x₁ : ℝ, ∀ x (hx : Fm.x1 < x), x₁ ≤ x → ∀ i : Fm.Ix x, SizesAt (Fm.L x i) ∧ (Fm.params x hx i).CnW = 10 ∧ (∀ k, Real.log ((Fm.D x i).host.g k) ≤ 9 * (Fm.L x i).sc.L + 1) ∧ 1000 ≤ (Fm.parT x hx i).CP ∧ (Fm.parT x hx i).CP ^ 20 ≤ zBase (Fm.L x i) ∧ DV.KapDef (Fm.D x i) ∧ Nonempty (ErrX (Fm.D x i)) ∧ (Fm.L x i).sc.x = x ∧ (JointQ (Fm.D x i) → FieldSmall (Fm.D x i) (Fm.L x i)) := by
  intro eps Fm hP hCP
  refine ⟨max ((10 : ℝ) ^ 60) (Fm.CP ^ 20), ?_⟩
  intro x hx hx₁ i
  have hS : SizesAt (Fm.L x i) := Fm.sizes x hx i
  have hLx : (Fm.L x i).sc.x = x := Fm.L_x x i hx
  have hCnW : (Fm.params x hx i).CnW = 10 := (Fm.fixed.2.2.2.2.2.2.2 x hx i).1

  have hg : ∀ k, Real.log ((Fm.D x i).host.g k) ≤ 9 * (Fm.L x i).sc.L + 1 := by
    intro k
    have hpr := (Fm.D x i).host.g_prime k
    have hpos : (0 : ℝ) < ((Fm.D x i).host.g k : ℝ) := by exact_mod_cast hpr.pos
    have hle := (hP.2.2.2.2.2.2.2.2 x hx i).2.2.1 k
    have := (Real.log_le_iff_le_exp hpos).2 hle
    linarith
  have h60 : (10 : ℝ) ^ 60 ≤ (Fm.L x i).sc.x := by
    rw [hLx]; exact le_trans (le_max_left _ _) hx₁
  obtain ⟨hH, hF⟩ := hostSz_of_sizes (Fm.D x i) (Fm.L x i) (Fm.params x hx i) (Fm.parT x hx i) hS hg h60

  have hCPeq : (Fm.parT x hx i).CP = Fm.CP := by
    unfold FamP.CP
    rw [← Fm.parT_K x hx i]
    rfl
  have hL4 : (4 : ℝ) ≤ (Fm.L x i).sc.L := hH.len

  have hf : (1 : ℝ) ≤ (Fm.D x i).R.f := by
    have hK := hS.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.1
    rcases Nat.eq_zero_or_pos (Fm.D x i).R.f with h0 | hpos
    · exfalso
      rw [h0, Nat.cast_zero, zero_mul] at hK
      have hxpos : 0 < (Fm.L x i).sc.x ^ szTh (Fm.L x i) :=
        Real.rpow_pos_of_pos (by linarith [(Fm.L x i).sc.one_lt_alt]) _
      have := mul_pos hxpos (by linarith : (0 : ℝ) < (Fm.L x i).sc.L)
      linarith
    · exact_mod_cast hpos
  refine ⟨hS, hCnW, hg, ?_, ?_, (Fm.ex x hx i).kap_def, ⟨(Fm.ex x hx i).errX⟩, hLx, ?_⟩
  · rw [hCPeq]; exact hCP
  ·
    unfold zBase
    rw [hCPeq]
    have hr : x ≤ ((Fm.D x i).R.r : ℝ) := by
      have h := scale_le_rank hS
      rw [hLx] at h
      exact h
    have hr0 : (0 : ℝ) ≤ ((Fm.D x i).R.r : ℝ) := Nat.cast_nonneg _
    have h1 : ((Fm.D x i).R.r : ℝ) ≤ (Fm.D x i).R.f * (Fm.D x i).R.r := le_mul_of_one_le_left hr0 hf
    have h2 : ((Fm.D x i).R.f : ℝ) * (Fm.D x i).R.r ≤ (Fm.D x i).R.f * (Fm.D x i).R.r * (Fm.L x i).sc.L :=
      le_mul_of_one_le_right (by positivity) (by linarith)
    linarith [le_trans (le_max_right _ _) hx₁]
  · intro hJ
    exact hF (hJ.2.2.2.2 _ hH)

end GlobalTheory.FinalRows

end
end

