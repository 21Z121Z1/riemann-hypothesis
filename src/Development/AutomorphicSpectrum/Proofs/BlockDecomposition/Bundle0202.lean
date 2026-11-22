import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0469
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0144
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivPullCompIff
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0193
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CechDifferentialPullback.Bridge
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0194
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0007
import Formalism.RealPlaceAnalysis.Bundle0004
import Formalism.PeriodIntegrals.Bundle0022
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0132
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.SymZeroCommFrame

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbelianSchemeBaseChangeExists
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Axis

theorem exists_abelianScheme_baseChange_ringHom :
    ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (A : Over (Sp R)) [GrpObj A] (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∃ (A' : Over (Sp R')) (_ : GrpObj A') (φ : A'.left ⟶ A.left), IsAbelianScheme A' ∧
      SmoothOfRelativeDimension g A'.hom ∧ IsPullback φ A'.hom A.hom (spMap (algebraMap R R')) := by
  intro R R' _ _ _ A _ g hA hg
  exact ⟨(Over.pullback (spMap (algebraMap R R'))).obj A, Functor.grpObjObj,
    Limits.pullback.fst A.hom (spMap (algebraMap R R')),
    GlobalTheory.AbLaw.CubeGen.isAb_baseChange hA _,
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback
      (IsPullback.of_hasPullback _ _) hg,
    IsPullback.of_hasPullback _ _⟩

end GlobalTheory.CompanionTheory.Axis
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageDerivativeL1Bound
section
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace

namespace GlobalTheory.CompanionTheory.WaveK

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def avg {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (h : ℝ → ℝ) (u : ℝ → Mat n → V) : Mat n → V :=
  fun x => ∫ t, (h t : ℂ) • u t x

section Norms

variable [MeasurableSpace (G n)] (μ : Measure (G n)) {V : Type} [NormedAddCommGroup V]

def l1 (f : Mat n → V) : ℝ := ∫ y : G n, ‖f y.val‖ ∂μ

def l2 (f : Mat n → V) : ℝ := Real.sqrt (∫ y : G n, ‖f y.val‖ ^ 2 ∂μ)

def ip [InnerProductSpace ℂ V] (f h : Mat n → V) : ℂ := ∫ y : G n, ⟪f y.val, h y.val⟫_ℂ ∂μ

end Norms

def IsKerC [MeasurableSpace (G n)] (μ : Measure (G n)) (E : KMod n) (g : ℝ → ℝ) (k : Mat n → (E.V →L[ℂ] E.V)) : Prop :=
  ContDiffOn ℝ ∞ k (GLs n) ∧ (∃ R, ∀ y ∈ GLs n, R < lg y → k y = 0) ∧
    (∀ y ∈ GLs n, ∀ k₁ k₂ : Matrix.unitaryGroup (Fin n) ℂ, k (k₁.1 * y * k₂.1) = E.ρ k₁ * k y * E.ρ k₂) ∧
    ∀ u, IsWave E u → Cpt (u 0) → ∀ x ∈ GLs n, act μ E k (u 0) x = avg g u x

def FormSymm : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    (f h : Mat n → E.V), f ∈ CE E → Cpt f → h ∈ CE E → Cpt h → ip μ (Om f) h = ip μ f (Om h)

def FormBound : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n),
    ∃ C : ℝ, ∀ f ∈ CE E, Cpt f → (ip μ (Om f) f).re ≤ C * l2 μ f ^ 2

def WaveUniq : Prop :=
  ∀ (n : ℕ) (E : KMod n) (u v : ℝ → Mat n → E.V), IsWave E u → IsWave E v → (∀ g ∈ GLs n, u 0 g = v 0 g) →
    ∀ t, ∀ x ∈ GLs n, u t x = v t x

def WaveSupp : Prop :=
  ∀ n : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ (E : KMod n) (u : ℝ → Mat n → E.V), IsWave E u → ∀ R : ℝ,
    (∀ y ∈ GLs n, R < lg y → u 0 y = 0) → ∀ t, ∀ y ∈ GLs n, R + c * (1 + |t|) < lg y → u t y = 0

def WaveLeft : Prop :=
  ∀ (n : ℕ) (E : KMod n) (u : ℝ → Mat n → E.V) (a : Mat n), a ∈ GLs n → IsWave E u → IsWave E fun t y => u t (a * y)

def WaveEnergyGrowthBound : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n),
    ∃ c : ℝ, ∀ u : ℝ → Mat n → E.V, IsWave E u → Cpt (u 0) → ∀ t, l2 μ (u t) ≤ Real.exp (c * |t|) * l2 μ (u 0)

def TimeRecip : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    (u v : ℝ → Mat n → E.V), IsWave E u → Cpt (u 0) → IsWave E v → Cpt (v 0) → ∀ t, ip μ (u t) (v 0) = ip μ (u 0) (v t)

def OmAvg : Prop :=
  ∀ (n : ℕ) (E : KMod n) (u : ℝ → Mat n → E.V) (h : ℝ → ℝ) (T : ℝ), IsWave E u → ContDiff ℝ ∞ h →
    (∀ t, T < |t| → h t = 0) → ∀ x ∈ GLs n, Om (avg h u) x = avg (iteratedDeriv 2 h) u x

def AvgSec : Prop :=
  ∀ n : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ (E : KMod n) (u : ℝ → Mat n → E.V) (h : ℝ → ℝ) (T R : ℝ), 0 ≤ T → IsWave E u →
    ContDiff ℝ ∞ h → (∀ t, T < |t| → h t = 0) → (∀ y ∈ GLs n, R < lg y → u 0 y = 0) →
      avg h u ∈ CE E ∧ ∀ y ∈ GLs n, R + c * (1 + T) < lg y → avg h u y = 0

def Recip : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    (u v : ℝ → Mat n → E.V) (h : ℝ → ℝ) (T : ℝ), IsWave E u → Cpt (u 0) → IsWave E v → Cpt (v 0) → ContDiff ℝ ∞ h →
      (∀ t, T < |t| → h t = 0) → ip μ (avg h u) (v 0) = ip μ (u 0) (avg h v)

def WaveAverageL2Bounded : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    (h : ℝ → ℝ) (T : ℝ), ContDiff ℝ ∞ h → (∀ t, T < |t| → h t = 0) →
      ∃ C : ℝ, ∀ u : ℝ → Mat n → E.V, IsWave E u → Cpt (u 0) → l2 μ (avg h u) ≤ C * l2 μ (u 0)

def SobSec : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    (w : List (Bool × Fin n × Fin n)), ∃ (N : ℕ) (C : ℝ), ∀ F ∈ CE E, Cpt F → ∀ x ∈ GLs n,
      ‖Rw w F x‖ ≤ C * ∑ j ∈ range (N + 1), l2 μ (Om^[j] F)

def AverageDerivativeL1Bound : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    (h : ℝ → ℝ) (T : ℝ) (w : List (Bool × Fin n × Fin n)), ContDiff ℝ ∞ h → (∀ t, T < |t| → h t = 0) →
      ∃ C : ℝ, ∀ u : ℝ → Mat n → E.V, IsWave E u → Cpt (u 0) → ∀ x ∈ GLs n, ‖Rw w (avg h u) x‖ ≤ C * l1 μ (u 0)

def ApproxId : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n),
    ∃ ψ : ℕ → E.V →ₗ[ℂ] (Mat n → E.V), (∀ j v, ψ j v ∈ CE E) ∧
      (∃ R, ∀ j v, ∀ y ∈ GLs n, R < lg y → ψ j v y = 0) ∧ (∃ C : ℝ, ∀ j v, l1 μ (ψ j v) ≤ C * ‖v‖) ∧
      (∀ j v, ∀ k : Matrix.unitaryGroup (Fin n) ℂ, ∀ y ∈ GLs n, ψ j v (k.1 * y) = ψ j (E.ρ k⁻¹ v) y) ∧
      ∀ v, ∀ f ∈ CE E, Cpt f → Tendsto (fun j => ip μ (ψ j v) f) atTop (𝓝 ⟪v, f 1⟫_ℂ)

def LimitStep : Prop :=
  ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (F : ℕ → Mat n → V) (R : ℝ),
    (∀ j, ContDiffOn ℝ ∞ (F j) (GLs n)) → (∀ j, ∀ y ∈ GLs n, R < lg y → F j y = 0) →
    (∀ w : List (Bool × Fin n × Fin n), ∃ C : ℝ, ∀ j, ∀ x ∈ GLs n, ‖Rw w (F j) x‖ ≤ C) →
    ∃ (l : Filter ℕ) (L : Mat n → V), l.NeBot ∧ l ≤ atTop ∧ ContDiffOn ℝ ∞ L (GLs n) ∧
      (∀ y ∈ GLs n, R < lg y → L y = 0) ∧ TendstoUniformlyOn F L l (GLs n)

def KerBase : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    (g : ℝ → ℝ) (T : ℝ), IsBump g T → ∃ k, IsKerC μ E g k

def KerExtend : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    (g : ℝ → ℝ) (T : ℝ) (k : Mat n → (E.V →L[ℂ] E.V)), IsBump g T → IsKerC μ E g k → IsKer μ E [] g k

def KerWord : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    (w : List (Bool × ℕ)) (g : ℝ → ℝ) (T : ℝ) (k : Mat n → (E.V →L[ℂ] E.V)), IsBump g T → IsKer μ E [] g k →
      ∃ k', IsKer μ E w g k'

end GlobalTheory.CompanionTheory.WaveK
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageInvarianceStatement
section
open PositivityTheory.RgEis PositivityTheory.RgEis.MG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.average_invariance : AvgMem → AvgInv := by
  first | exact @GlobalTheory.CompanionTheory.RgEisAvg.avgInv_of_avgMem | exact GlobalTheory.CompanionTheory.RgEisAvg.avgInv_of_avgMem | (intros; apply GlobalTheory.CompanionTheory.RgEisAvg.avgInv_of_avgMem <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageMembershipStatement
section
open PositivityTheory.RgEis PositivityTheory.RgEis.MG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.average_membership : AvgMem := by
  first | exact @GlobalTheory.CompanionTheory.EisMirGen.avgMem | exact GlobalTheory.CompanionTheory.EisMirGen.avgMem | (intros; apply GlobalTheory.CompanionTheory.EisMirGen.avgMem <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundaryTermGoodStatement
section
open PositivityTheory.RgEis PositivityTheory.RgEis.MG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundary_term_good : BGood := by
  first | exact @GlobalTheory.CompanionTheory.RgEisLeft.bGood | exact GlobalTheory.CompanionTheory.RgEisLeft.bGood | (intros; apply GlobalTheory.CompanionTheory.RgEisLeft.bGood <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechConnectingPullNaturalStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_connecting_pull_natural : ∀ {X Y : TopCat.{0}} (f : X ⟶ Y) {κ ι : Type} (V : κ → Opens Y) (hV : iSup V = ⊤)
    (U : ι → Opens X) (hU : iSup U = ⊤) (τ : ι → κ) (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i)))
    {S : ShortComplex (AbSheaf Y)} {S' : ShortComplex (AbSheaf X)} (hS : S.ShortExact) [Injective S.X₂]
    (hC : IsCechShortExact V S.f.hom S.g.hom) (hI : CechAcyclic S.X₂.obj V) (hS' : S'.ShortExact) [Injective S'.X₂]
    (hC' : IsCechShortExact U S'.f.hom S'.g.hom) (hI' : CechAcyclic S'.X₂.obj U) (α : S ⟶ S'.map (push f))
    (x : cechH S.X₁.obj V 1),
    (cechHOneEquiv U hU hS' hC' hI' : cechH S'.X₁.obj U 1 ≃+ Sheaf.H.{0} S'.X₁ 1) (cechPullH f α.τ₁.hom V U τ hτ 1 x) =
      hPull f α.τ₁ 1 ((cechHOneEquiv V hV hS hC hI : cechH S.X₁.obj V 1 ≃+ Sheaf.H.{0} S.X₁ 1) x) := by
  first | exact @GlobalTheory.CompanionTheory.CechOne.cechHOneEquiv_pull | exact GlobalTheory.CompanionTheory.CechOne.cechHOneEquiv_pull | (intros; apply GlobalTheory.CompanionTheory.CechOne.cechHOneEquiv_pull <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechSheafCohomologyPullCompatStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_sheaf_cohomology_pull_compat : ∀ {X Y : TopCat.{0}} (f : X ⟶ Y) {κ ι : Type} (V : κ → Opens Y) (U : ι → Opens X) (τ : ι → κ)
    (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i))) {S : ShortComplex (AbSheaf Y)} {S' : ShortComplex (AbSheaf X)}
    (hS : S.ShortExact) [Injective S.X₂] (hC : IsCechShortExact V S.f.hom S.g.hom) (hI : CechAcyclic S.X₂.obj V)
    (hS' : S'.ShortExact) [Injective S'.X₂] (hC' : IsCechShortExact U S'.f.hom S'.g.hom) (hI' : CechAcyclic S'.X₂.obj U)
    (α : S ⟶ S'.map (push f)) (m : ℕ) (e : cechH S.X₃.obj V (m + 1) ≃+ Sheaf.H.{0} S.X₃ (m + 1))
    (e' : cechH S'.X₃.obj U (m + 1) ≃+ Sheaf.H.{0} S'.X₃ (m + 1))
    (he : ∀ y, e' (cechPullH f α.τ₃.hom V U τ hτ (m + 1) y) = hPull f α.τ₃ (m + 1) (e y))
    (x : cechH S.X₁.obj V (m + 2)),
    cechHEquivStep U hS' hC' hI' m e' (cechPullH f α.τ₁.hom V U τ hτ (m + 2) x) =
      hPull f α.τ₁ (m + 2) (cechHEquivStep V hS hC hI m e x) := by
  first | exact @GlobalTheory.CompanionTheory.CechStep.cechHEquivStep_pull | exact GlobalTheory.CompanionTheory.CechStep.cechHEquivStep_pull | (intros; apply GlobalTheory.CompanionTheory.CechStep.cechHEquivStep_pull <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartUnionLeSite
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeSite

theorem wU_le_KS : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (D : E.LineData X) {N m : ℕ}
    (i : X ⟶ PSpace K N) (y : Fin m → MvPolynomial (Fin (N + 1)) K) (s : ℕ), IsTautologicalLineAt D N i → wU q i y s ≤ KS q s (𝒱D D) := by
  intro K _ X q D N m i y s hO T hT
  obtain ⟨k, hQ, V, ⟨j, rfl⟩, hV⟩ := hT
  exact ⟨hQ, wch i j, GlobalTheory.T.chart_open_mem_cover_of_O1 D N i hO j, fun x hx => (hV hx).2⟩

end GlobalTheory.CompanionTheory.ConeSite
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoefSmoothOnG
section
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.CoefSmooth

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem coef_smoothOnG (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (v : GlobalTheory.SmoothVecMod.smoothVec ε σ) (w : H) :
    Formalism.REAL.SmoothOnG ε (fun g => ⟪w, σ g (v : H)⟫_ℂ) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := v.2 g₀ hg₀
  refine ⟨U, fun x => ⟪w, F x⟫_ℂ, hU, hgU, ?_, fun g hg hgJ => ?_⟩
  · exact (((innerSL ℂ w).restrictScalars ℝ).contDiff.comp_contDiffOn hF)
  · exact congrArg (fun z => ⟪w, z⟫_ℂ) (hfF g hg hgJ)

theorem coef_smooth : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (v : GlobalTheory.SmoothVecMod.smoothVec ε σ) (w : H),
    Formalism.REAL.SmoothOnG ε (fun g => ⟪w, σ g (v : H)⟫_ℂ) :=
  fun n ε H _ _ σ v w => coef_smoothOnG n ε H σ v w

end GlobalTheory.CompanionTheory.CoefSmooth
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeMeas
section
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.ConeHaar

open PositivityTheory.RgBcC

def coneW (n : ℕ) (v : Fin n × Fin n → ℝ) : ℝ≥0∞ := ENNReal.ofReal (((hOf v).det.re ^ n)⁻¹)

def coneMeas (n : ℕ) : Measure (Fin n × Fin n → ℝ) :=
  (volume.restrict (cone n)).withDensity (coneW n)

end GlobalTheory.CompanionTheory.ConeHaar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetAddOnesField
section
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.AdjSum

open Matrix Polynomial

theorem det_add_ones_field {K : Type*} [Field K] {n : ℕ} (B : Matrix (Fin n) (Fin n) K)
    (hB : B.det ≠ 0) :
    (B + Matrix.of fun _ _ => (1 : K)).det = B.det + ∑ a, ∑ b, B.adjugate a b := by
  have hJ : (Matrix.of fun _ _ => (1 : K) : Matrix (Fin n) (Fin n) K) =
      replicateCol Unit (fun _ => (1 : K)) * replicateRow Unit (fun _ => (1 : K)) := by
    ext i j
    simp [Matrix.mul_apply]
  rw [hJ, det_add_replicateCol_mul_replicateRow (isUnit_iff_ne_zero.mpr hB)]
  have hinv : B⁻¹ = (B.det)⁻¹ • B.adjugate := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  have h1 : ∀ C : Matrix Unit Unit K, C.det = C () () := fun C => det_unique C
  rw [h1, hinv]
  simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.mul_apply, Matrix.smul_apply,
    replicateRow_apply, replicateCol_apply, one_mul, mul_one, smul_eq_mul, Finset.univ_unique,
    Finset.sum_singleton]
  rw [mul_add, mul_one]
  congr 1
  simp only [← Finset.mul_sum]
  rw [Finset.sum_comm]
  field_simp

theorem det_add_ones {R : Type*} [CommRing R] [IsDomain R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) (hA : A.det ≠ 0) :
    (A + Matrix.of fun _ _ => (1 : R)).det = A.det + ∑ a, ∑ b, A.adjugate a b := by
  let K := FractionRing R
  let f : R →+* K := algebraMap R K
  have hf : Function.Injective f := IsFractionRing.injective R K
  have hdet : ∀ C : Matrix (Fin n) (Fin n) R, f C.det = (C.map f).det := fun C =>
    RingHom.map_det f C
  apply hf
  have h := det_add_ones_field (A.map f) (by
    rw [← hdet]
    exact (map_ne_zero_iff f hf).mpr hA)
  have hadj : (A.map f).adjugate = A.adjugate.map f := by
    have := RingHom.map_adjugate f A
    simpa [RingHom.mapMatrix_apply] using this.symm
  have hsum : (A.map f + Matrix.of fun _ _ => (1 : K)) =
      (A + Matrix.of fun _ _ => (1 : R)).map f := by
    ext i j
    simp
  rw [hsum, ← hdet, ← hdet, hadj] at h
  rw [h, map_add, map_sum]
  simp [map_sum]

theorem entry (n : ℕ) (l : Fin n → ℂ) (a b : Fin n) :
    ((Polynomial.X : Polynomial ℂ) • (1 : Matrix (Fin n) (Fin n) (Polynomial ℂ)) +
        (Formalism.REAL.Amat l).map (fun z : ℂ => Polynomial.C z)) a b =
      if a = b then Polynomial.X + Polynomial.C (l a)
      else if a < b then -1 else 0 := by
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, Formalism.REAL.Amat, Matrix.of_apply,
    Matrix.one_apply, smul_eq_mul]
  split_ifs <;> simp_all

theorem adj_sum : ∀ (n : ℕ) (l : Fin n → ℂ), ∑ a, ∑ b, (Matrix.adjugate ((Polynomial.X : Polynomial ℂ) • (1 : Matrix (Fin n) (Fin n) (Polynomial ℂ)) + (Formalism.REAL.Amat l).map (fun z : ℂ => Polynomial.C z))) a b = ∏ s, (Polynomial.X + Polynomial.C (l s) + 1) - ∏ s, (Polynomial.X + Polynomial.C (l s)) := by
  intro n l
  set M : Matrix (Fin n) (Fin n) (Polynomial ℂ) :=
    (Polynomial.X : Polynomial ℂ) • (1 : Matrix (Fin n) (Fin n) (Polynomial ℂ)) +
      (Formalism.REAL.Amat l).map (fun z : ℂ => Polynomial.C z) with hM
  have he : ∀ a b, M a b = if a = b then Polynomial.X + Polynomial.C (l a)
      else if a < b then -1 else 0 := entry n l
  have hdet : M.det = ∏ s, (Polynomial.X + Polynomial.C (l s)) := by
    rw [Matrix.det_of_upperTriangular]
    · exact Finset.prod_congr rfl fun s _ => by rw [he]; simp
    · intro i j hij
      have hij' : j < i := hij
      rw [he, if_neg (ne_of_gt hij'), if_neg (not_lt_of_gt hij')]
  have hdet1 : (M + Matrix.of fun _ _ => (1 : Polynomial ℂ)).det =
      ∏ s, (Polynomial.X + Polynomial.C (l s) + 1) := by
    rw [Matrix.det_of_lowerTriangular]
    · exact Finset.prod_congr rfl fun s _ => by simp [he]
    · intro i j hij
      have hij' : i < j := hij
      simp [he, ne_of_lt hij', hij']
  have hne : M.det ≠ 0 := by
    rw [hdet, Finset.prod_ne_zero_iff]
    intro s _
    exact (Polynomial.monic_X_add_C (l s)).ne_zero
  have h := det_add_ones M hne
  rw [hdet1, hdet] at h
  rw [h]
  ring

end GlobalTheory.CompanionTheory.AdjSum
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiagonalTermGoodStatement
section
open PositivityTheory.RgEis PositivityTheory.RgEis.MG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonal_term_good : DGood := by
  first | exact @GlobalTheory.CompanionTheory.RgEisDGood.dGood | exact GlobalTheory.CompanionTheory.RgEisDGood.dGood | (intros; apply GlobalTheory.CompanionTheory.RgEisDGood.dGood <;> assumption)
end

