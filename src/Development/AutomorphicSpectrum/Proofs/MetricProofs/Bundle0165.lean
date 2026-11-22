import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0162
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0006
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0147
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0154
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0156
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0009
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0005
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0004
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentRowsDimension
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0035
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionFunctorialHolomorphic
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0163
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0059
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0041
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0023
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ExistsFormOfMemChartRingZ
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEmbeddingWeight
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0072
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0049
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PConstantsDescend
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0050
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0063
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0029
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0123
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0164
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0010
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0007

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.AdaptedFrameBallCoordinateStatement
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_frame_ball_coordinate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F) (R : RiemLat E g Λ) (A A₀ : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ) (τ : Ψ) (W : Matrix (Fin j') (Fin j) ℂ), (∀ u : Matrix (Sg j j') (Sg j j') ℂ, IsSgU u → IsUnit u.toBlocks₁₁.det ∧ IsUnit u.toBlocks₂₂.det ∧ (1 - moebW u 0 * (moebW u 0)ᴴ) * (u.toBlocks₂₂ * u.toBlocks₂₂ᴴ) = 1 ∧ (1 - moebW u 0 * (moebW u 0)ᴴ).PosDef) → (∀ x y : Fin j' → ℂ, R.ip (C.pPart R τ (A τ *ᵥ Sum.elim 0 x)) (C.pPart R τ (A τ *ᵥ Sum.elim 0 y)) = ((2 * C.c : ℝ) : ℂ) * (star x ⬝ᵥ y)) → C.IsAdapted R A → (A₀ τ)ᴴ * C.sgr τ * A₀ τ = sgI j j' → W = moebW (C.cinv (A₀ τ) τ * A τ) 0 → (∀ v : Fin j → ℂ, C.pPart R τ (A₀ τ *ᵥ Sum.elim v (W *ᵥ v)) = 0) ∧ R.gram (fun b : Fin j' => C.pPart R τ (A₀ τ *ᵥ Sum.elim 0 (Pi.single b 1))) * (1 - W * Wᴴ) = ((2 * C.c : ℝ) : ℂ) • (1 : Matrix (Fin j') (Fin j') ℂ) ∧ (1 - W * Wᴴ).PosDef := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.point_graph_gram | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.point_graph_gram | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.point_graph_gram <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.Coefficients
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB.Top

theorem abs_limNum_sub_le {D : ℕ} {σ : Type} {S : AnSys D σ} {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} (Re Re' : Realis S P) (II : IntersectionSystem)
    (w : Fin (D + 1) → σ) (B : ℝ) (ht : 0 < S.t₀)
    (h1 : Tendsto (fun t => Re.num II t w) (𝓝[>] 0) (𝓝 (Re.limNum II w)))
    (h2 : Tendsto (fun t => Re'.num II t w) (𝓝[>] 0) (𝓝 (Re'.limNum II w)))
    (hb : ∀ t, 0 < t → t ≤ S.t₀ → |Re.num II t w - Re'.num II t w| ≤ B) :
    |Re.limNum II w - Re'.limNum II w| ≤ B := by
  refine le_of_tendsto (h1.sub h2).abs ?_
  filter_upwards [Ioc_mem_nhdsGT ht] with t ht'
  exact hb t ht'.1 ht'.2

theorem coefficients : Coefficients := by
  intro hI D N Ψ _ S thH hth
  obtain ⟨C₂', hC⟩ := GlobalTheory.T.realisation_height_independence hI D (Option (Ψ × Fin N)) S thH hth
  obtain ⟨Cst, hW, hWS⟩ := GlobalTheory.T.weighted_polynomial_homogeneous_coeff_bound Ψ N (D + 1)
  have ht : 0 < S.t₀ := (S.reg none).1
  refine ⟨Cst * ((Fintype.card (Option (Ψ × Fin N)) : ℝ) ^ (D + 1)) * C₂',
    fun II hII K _ ι _ P Re => ?_⟩
  obtain ⟨C₃, s₀, -, hag⟩ := GlobalTheory.T.agreement_positive hI D (Option (Ψ × Fin N)) S 0 ht
  have hPB : ∀ R : Realis S P, R.PBs II = toWtS (formPoly (D + 1) (R.limNum II)) := fun R => rfl
  have hPBwt : ∀ R : Realis S P,
      R.PBwt II = toWt (formPoly (D + 1) fun w => R.limNum II (some ∘ w)) := fun R => rfl
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hPB]
    exact (hWS _ 0 (formPoly_isHomogeneous_and_eval _ _ _).1).1
  · rw [hPBwt]
    exact (hW _ 0 (formPoly_isHomogeneous_and_eval _ _ _).1).1
  · rw [hPB, hPBwt]
    exact (poly_s_zero Ψ N (D + 1)).1 _
  · intro Re' T α H hdeg hT hH hpot hvc hnef
    have hb := hC II hII K ι P Re Re' T α H hdeg hT hH hpot hvc hnef
    have hlim : ∀ w, |Re.limNum II w - Re'.limNum II w| ≤ C₂' * ∑ p ∈ T, α p * Real.log p :=
      fun w => abs_limNum_sub_le Re Re' II w _ ht ((hag II hII K ι P Re).1 w)
        ((hag II hII K ι P Re').1 w) fun t h0 h1 => hb t h0 h1 w
    have hB0 : 0 ≤ C₂' * ∑ p ∈ T, α p * Real.log p := (abs_nonneg _).trans (hlim fun _ => none)
    have hcard : ((Fintype.card (Ψ × Fin N) : ℝ)) ^ (D + 1) * (C₂' * ∑ p ∈ T, α p * Real.log p) ≤
        ((Fintype.card (Option (Ψ × Fin N)) : ℝ)) ^ (D + 1) * (C₂' * ∑ p ∈ T, α p * Real.log p) := by
      refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) ?_ _) hB0
      rw [Fintype.card_option]
      push_cast
      linarith
    constructor
    · have hhom := ((formPoly_isHomogeneous_and_eval (Option (Ψ × Fin N)) (D + 1) (Re.limNum II)).1).sub
        ((formPoly_isHomogeneous_and_eval (Option (Ψ × Fin N)) (D + 1) (Re'.limNum II)).1)
      have hco : ∀ m, |coeff m (formPoly (D + 1) (Re.limNum II) - formPoly (D + 1) (Re'.limNum II))| ≤
          ((Fintype.card (Option (Ψ × Fin N)) : ℝ)) ^ (D + 1) * (C₂' * ∑ p ∈ T, α p * Real.log p) :=
        fun m => by
          rw [coeff_sub]
          exact (formPoly_sub_bound _ _ _ _ _ hlim).1 m
      intro m
      rw [hPB, hPB, ← coeff_sub, ← map_sub]
      calc _ ≤ Cst * (((Fintype.card (Option (Ψ × Fin N)) : ℝ)) ^ (D + 1) *
            (C₂' * ∑ p ∈ T, α p * Real.log p)) := (hWS _ _ hhom).2 hco m
        _ = _ := by ring
    · have hhom := ((formPoly_isHomogeneous_and_eval (Ψ × Fin N) (D + 1)
          (fun w => Re.limNum II (some ∘ w))).1).sub
        ((formPoly_isHomogeneous_and_eval (Ψ × Fin N) (D + 1) (fun w => Re'.limNum II (some ∘ w))).1)
      have hco : ∀ m, |coeff m (formPoly (D + 1) (fun w => Re.limNum II (some ∘ w)) -
          formPoly (D + 1) (fun w => Re'.limNum II (some ∘ w)))| ≤
          ((Fintype.card (Option (Ψ × Fin N)) : ℝ)) ^ (D + 1) * (C₂' * ∑ p ∈ T, α p * Real.log p) :=
        fun m => by
          rw [coeff_sub]
          exact ((formPoly_sub_bound _ _ _ _ _ fun w => hlim (some ∘ w)).1 m).trans hcard
      intro m
      rw [hPBwt, hPBwt, ← coeff_sub, ← map_sub]
      calc _ ≤ Cst * (((Fintype.card (Option (Ψ × Fin N)) : ℝ)) ^ (D + 1) *
            (C₂' * ∑ p ∈ T, α p * Real.log p)) := (hW _ _ hhom).2 hco m
        _ = _ := by ring

end GlobalTheory.CompanionTheory.Ar.PB.Top
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsLatticeEmbeddingStatement
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lattice_embedding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (_H : Host E) (F : UnivFam E Ψ j j' n g Λ), Nonempty (LatEmb F) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatEmbEx.exists_latEmb | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatEmbEx.exists_latEmb | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatEmbEx.exists_latEmb <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsRegularizationSettingStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_regularization_setting : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) (M : XModel D) (w : ((Σ k, J k) → ℂ) → ℝ), LogHom D Hd.aMu w → ChartPsh D w → ChartCont D w → ChartBdd D w → ConjOff D w → ∃ S' : BoundedRegularisationSetting M D.Xo Hd.aMu w, S'.IsTied ∧ ConjU S' := by
  first | exact @GlobalTheory.CompanionTheory.Relay.exists_regularization_setting | exact GlobalTheory.CompanionTheory.Relay.exists_regularization_setting | (intros; apply GlobalTheory.CompanionTheory.Relay.exists_regularization_setting <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentRowsDimensionStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_adjacent_rows_dimension : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → d + 1 = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (q : Fin 2 → RW.X → FA.S.X), (∀ i, HoloMap RW.A FA.S.A (q i)) → (∀ x x₀, FA.Re.π x₀ = q 0 x → SameOrbit (FA.Re.R.lift x₀ x₀) (fstPt k₀ (RW.lift x x))) → (∀ x x₀, FA.Re.π x₀ = q 1 x → SameOrbit (FA.Re.R.lift x₀ x₀) (sndPt k₀ (RW.lift x x))) → (Function.Injective fun w => (q 0 w, q 1 w)) → ∃ (U B : ℕ → Set (Fin d → ℂ)) (G : ℕ → (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦY : ℕ → (Fin (d + 1) → ℂ) → FA.S.X) (ΦW : ℕ → (Fin (d + 2) → ℂ) → RW.X), (∀ m, IsOpen (U m)) ∧ (∀ m, MeasurableSet (B m) ∧ B m ⊆ U m) ∧ IsParamCover FA.S.A (fun m => {z | Fin.tail z ∈ U m}) (fun m => {z | Fin.tail z ∈ B m}) ΦY ∧ IsParamCover RW.A (fun m => {z | Fin.tail (Fin.tail z) ∈ U m}) (fun m => {z | Fin.tail (Fin.tail z) ∈ B m}) ΦW ∧ (∀ m (z : Fin (d + 1) → ℂ), Fin.tail z ∈ U m → ΦY m z ∉ bdry FA.S.s) ∧ ∀ m, IsFibreChart FA τ a ca cb q (U m) (G m) (ΦY m) (ΦW m) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.fibre_charts | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.fibre_charts | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.fibre_charts <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticDimensionCount
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq

theorem dim_eq_of_holo_inverse {a b : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : FinHolAtlas a X) (B : FinHolAtlas b Y) (f : X → Y) (g : Y → X)
    (hf : HoloMap A B f) (hg : HoloMap B A g) (hgf : ∀ x, g (f x) = x) (hfg : ∀ y, f (g y) = y) (x : X) :
    a = b := by
  obtain ⟨j, hj⟩ := A.cover x
  obtain ⟨k, hk⟩ := B.cover (f x)
  have hu_t : A.chart j x ∈ (A.chart j).target := (A.chart j).map_source hj
  have hw_t : B.chart k (f x) ∈ (B.chart k).target := (B.chart k).map_source hk
  have hsu : (A.chart j).symm (A.chart j x) = x := (A.chart j).left_inv hj
  have hsw : (B.chart k).symm (B.chart k (f x)) = f x := (B.chart k).left_inv hk
  let F : (Fin a → ℂ) → (Fin b → ℂ) := B.chart k ∘ f ∘ (A.chart j).symm
  let G : (Fin b → ℂ) → (Fin a → ℂ) := A.chart j ∘ g ∘ (B.chart k).symm
  have hFu : F (A.chart j x) = B.chart k (f x) := by
    show B.chart k (f ((A.chart j).symm (A.chart j x))) = _
    rw [hsu]
  have hGw : G (B.chart k (f x)) = A.chart j x := by
    show A.chart j (g ((B.chart k).symm (B.chart k (f x)))) = _
    rw [hsw, hgf]
  have dF : DifferentiableAt ℂ F (A.chart j x) :=
    (hf.2 j k _ ⟨hu_t, by
      show f ((A.chart j).symm (A.chart j x)) ∈ (B.chart k).source
      rw [hsu]; exact hk⟩).differentiableAt
  have dG : DifferentiableAt ℂ G (B.chart k (f x)) :=
    (hg.2 k j _ ⟨hw_t, by
      show g ((B.chart k).symm (B.chart k (f x))) ∈ (A.chart j).source
      rw [hsw, hgf]; exact hj⟩).differentiableAt
  have e1 : G ∘ F =ᶠ[𝓝 (A.chart j x)] id := by
    have c : ContinuousAt (f ∘ (A.chart j).symm) (A.chart j x) :=
      hf.1.continuousAt.comp ((A.chart j).continuousAt_symm hu_t)
    have hs : ∀ᶠ v in 𝓝 (A.chart j x), (f ∘ (A.chart j).symm) v ∈ (B.chart k).source :=
      c.eventually ((B.chart k).open_source.mem_nhds (by
        show f ((A.chart j).symm (A.chart j x)) ∈ (B.chart k).source
        rw [hsu]; exact hk))
    filter_upwards [hs, (A.chart j).open_target.mem_nhds hu_t] with v h1 h2
    have h1' : f ((A.chart j).symm v) ∈ (B.chart k).source := h1
    show A.chart j (g ((B.chart k).symm (B.chart k (f ((A.chart j).symm v))))) = v
    rw [(B.chart k).left_inv h1', hgf, (A.chart j).right_inv h2]
  have e2 : F ∘ G =ᶠ[𝓝 (B.chart k (f x))] id := by
    have c : ContinuousAt (g ∘ (B.chart k).symm) (B.chart k (f x)) :=
      hg.1.continuousAt.comp ((B.chart k).continuousAt_symm hw_t)
    have hs : ∀ᶠ v in 𝓝 (B.chart k (f x)), (g ∘ (B.chart k).symm) v ∈ (A.chart j).source :=
      c.eventually ((A.chart j).open_source.mem_nhds (by
        show g ((B.chart k).symm (B.chart k (f x))) ∈ (A.chart j).source
        rw [hsw, hgf]; exact hj))
    filter_upwards [hs, (B.chart k).open_target.mem_nhds hw_t] with v h1 h2
    have h1' : g ((B.chart k).symm v) ∈ (A.chart j).source := h1
    show B.chart k (f ((A.chart j).symm (A.chart j (g ((B.chart k).symm v))))) = v
    rw [(A.chart j).left_inv h1', hfg, (B.chart k).right_inv h2]
  have d1 : (fderiv ℂ G (B.chart k (f x))).comp (fderiv ℂ F (A.chart j x)) = ContinuousLinearMap.id ℂ _ := by
    have dG' : DifferentiableAt ℂ G (F (A.chart j x)) := by rw [hFu]; exact dG
    have h := fderiv_comp (A.chart j x) dG' dF
    rw [e1.fderiv_eq, fderiv_id, hFu] at h
    exact h.symm
  have d2 : (fderiv ℂ F (A.chart j x)).comp (fderiv ℂ G (B.chart k (f x))) = ContinuousLinearMap.id ℂ _ := by
    have dF' : DifferentiableAt ℂ F (G (B.chart k (f x))) := by rw [hGw]; exact dF
    have h := fderiv_comp (B.chart k (f x)) dF' dG
    rw [e2.fderiv_eq, fderiv_id, hGw] at h
    exact h.symm
  let E : (Fin a → ℂ) ≃ₗ[ℂ] (Fin b → ℂ) := LinearEquiv.ofLinearMap
    (fderiv ℂ F (A.chart j x) : (Fin a → ℂ) →ₗ[ℂ] (Fin b → ℂ))
    (fderiv ℂ G (B.chart k (f x)) : (Fin b → ℂ) →ₗ[ℂ] (Fin a → ℂ))
    (LinearMap.ext fun v => congrArg (fun L : (Fin b → ℂ) →L[ℂ] (Fin b → ℂ) => L v) d2)
    (LinearMap.ext fun v => congrArg (fun L : (Fin a → ℂ) →L[ℂ] (Fin a → ℂ) => L v) d1)
  simpa using E.finrank_eq

theorem dim_eq_of_res {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)} {a b : ℕ}
    (R : AnLogRes P ⊤ a) (hJ : J = ⊤) (R' : AnLogRes P J b) (x : R'.X) : a = b := by
  subst hJ
  have hP : P ≤ imageZ id P := fun f hf => by
    show rename id f ∈ P
    rwa [rename_id_apply]
  obtain ⟨h, hh, ho⟩ := GlobalTheory.CompanionTheory.Ar.PB.Proj.holoMap_of_blockProj K ι K ι id id P P ⊤ a b R R' isBlockMap_id hP
  obtain ⟨g, hg, go⟩ := GlobalTheory.CompanionTheory.Ar.PB.Proj.holoMap_of_blockProj K ι K ι id id P P ⊤ b a R' R isBlockMap_id hP
  have hemp : ∀ z, z ∉ mcPts (⊤ : Ideal (MRing ι)) := fun z hz => by
    have := hz.2 1 trivial
    simp at this
  have hgh : ∀ x, g (h x) = x := fun x => R'.inj _ _ (hemp _) (orbit_trans (go (h x)) (ho x))
  have hhg : ∀ x, h (g x) = x := fun x => R.inj _ _ (hemp _) (orbit_trans (ho (g x)) (go x))
  exact dim_eq_of_holo_inverse R.A R'.A g h hg hh hhg hgh (h x)

theorem flagAn_dim : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d), d + 1 = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA
  have hk : ∀ k, k ∈ Set.range (id : K → K) ↔
      ((∀ p, M.blk p ≠ some k) ∨ ∃ p, (fun _ : Ψ × Fin N => True) p ∧ M.blk p = some k) := fun k =>
    ⟨fun _ => by
      by_cases h : ∀ p, M.blk p ≠ some k
      · exact Or.inl h
      · obtain ⟨p, hp⟩ := not_forall.1 h
        exact Or.inr ⟨p, trivial, not_not.1 hp⟩, fun _ => ⟨k, rfl⟩⟩
  obtain ⟨e, R, he, -⟩ := GlobalTheory.T.flag_bundle_partial_block_map K ι Φ y Ψ N j M n _ BM.Rb rfl (fun _ => True) K ι id id isBlockMap_id hk
  have R2 : AnLogRes (mCoordIdeal y) ⊤ e := R
  obtain ⟨z, hz, hJ⟩ :=
    GroundTheory.Heights₂.Heights.HilbertSamuel.exists_mcPts_not_mem_mcPts FA.Re.arith FA.Re.R.nondeg
  obtain ⟨x, -⟩ := FA.Re.R.surj z hz hJ
  rw [← he fun _ => trivial]
  exact (dim_eq_of_res R2 FA.J_top FA.Re.R x).symm

end GlobalTheory.CompanionTheory.Ar.PB.WSq
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HilbertSamuelG3StarOfStatements
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem hilbert_samuel_G3Star_of_systems :
    ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiHSStatement →
      ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement →
      GroundTheory.Heights₂.Heights.HilbertSamuel.ArithmeticVolumeMultiplicative.Statement := by
  intro hSys hHS hBig hRes
  exact GroundTheory.Heights₂.Heights.HilbertSamuel.ArithmeticVolumeMultiplicative.proof (GlobalTheory.T.hilbert_samuel_G3_of_moriwaki hHS hBig)
    GroundTheory.Heights₂.Heights.HilbertSamuel.EmbeddingWeight.proof
    (GroundTheory.Heights₂.Heights.HilbertSamuel.TwistIntersectionInt.proof (GlobalTheory.T.embedding_pieces_of_intersection_and_resolution hSys hRes)
      (degreeGeneric_of_degree (degree_of_system hSys)))
    GroundTheory.Heights₂.Heights.HilbertSamuel.UnitApprox.proof
    (GroundTheory.Heights₂.Heights.HilbertSamuel.ConstantsRegular.proof
      GroundTheory.Heights₂.Heights.HilbertSamuel.ConstantsDescend.proof
      GroundTheory.Heights₂.Heights.HilbertSamuel.ChartConstantsDetermined.proof)

end GlobalTheory.CompanionTheory.Ar.Giv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LatticeFamilyLocalSectionsStatement
section
open Matrix Metric GroundTheory.Heights₂.Heights.Regular GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_family_local_sections : ∀ (n a g : ℕ) (_h : a ≤ n) (Λ : Type) [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ] (E : LinearMap.BilinForm ℤ Λ) (Γ : (Fin n → ℂ) → AddSubgroup (Fin g → ℂ)) (Hf : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (U : Set (Fin n → ℂ)) (Γ₀ : Submodule ℤ (Fin g → ℂ)) (S : Γ₀ → (Fin n → ℂ) → (Fin g → ℂ)), U = {z | z ∈ ball (0 : Fin n → ℂ) 1 ∧ ∀ i : Fin n, i.val < a → z i ≠ 0} → Module.finrank ℤ Λ = 2 * g → (∀ x, E x x = 0) → Function.Bijective E → (∀ z ∈ U, (Hf z).IsHermitian ∧ ∀ x : Fin g → ℂ, x ≠ 0 → 0 < (x ⬝ᵥ Hf z *ᵥ star x).re) → (∀ z₀ ∈ U, ∃ N : Set (Fin n → ℂ), IsOpen N ∧ z₀ ∈ N ∧ N ⊆ U ∧ ∃ P : (Fin n → ℂ) → (Λ →+ (Fin g → ℂ)), (∀ x, DifferentiableOn ℂ (fun z => P z x) N) ∧ ∀ z ∈ N, Function.Injective (P z) ∧ (P z).range = Γ z ∧ ∀ x y, (P z x ⬝ᵥ Hf z *ᵥ star (P z y)).im = E x y) → (∀ x, DifferentiableOn ℂ (S x) (ball 0 1) ∧ S x 0 = x ∧ ∀ z ∈ U, S x z ∈ Γ z) → (∀ x y z, S (x + y) z = S x z + S y z) → (∀ s : (Fin n → ℂ) → (Fin g → ℂ), ContinuousAt s 0 → (∀ z ∈ U, s z ∈ Γ z) → s 0 ∈ Γ₀) → Submodule.span ℂ (Γ₀ : Set (Fin g → ℂ)) = ⊤ → (∀ N : ℕ, 0 < N → ∃ T : Set (Γ₀ ⧸ LinearMap.range ((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀))), Nat.card (Γ₀ ⧸ LinearMap.range ((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀))) * Nat.card T = N ^ (2 * g) ∧ ∀ x y : Γ₀, Submodule.Quotient.mk x ∈ T → ∀ z ∈ U, ∃ k : ℤ, (S x z ⬝ᵥ Hf z *ᵥ star (S y z)).im = N * k) → ∃ L : LogPeriods n a g Λ, L.H = Hf := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_logPeriods_of_local_markings | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_logPeriods_of_local_markings | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_logPeriods_of_local_markings <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.PshLogGrowthBoundedNearPunctureStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psh_log_growth_bounded_near_puncture : ∀ (n a : ℕ) (ρ C : ℝ) (u : (Fin n → ℂ) → ℝ), 0 < ρ → ρ ≤ 1 → ReciprocityTheory.AnForm.A.IsPsh (Flat.punct n a ρ) u → (∀ t ∈ Flat.punct n a ρ, u t ≤ C * (1 + Real.log (Flat.logSize a t))) → ∃ C' : ℝ, ∀ t ∈ Flat.punct n a (ρ / 2), u t ≤ C' := by
  first | exact @GlobalTheory.CompanionTheory.Relay.psh_log_growth_bounded_near_puncture | exact GlobalTheory.CompanionTheory.Relay.psh_log_growth_bounded_near_puncture | (intros; apply GlobalTheory.CompanionTheory.Relay.psh_log_growth_bounded_near_puncture <;> assumption)
end

