import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0196
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactHaarRightInvariantInst
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0025
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0247
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GrowthSobolevCauchyTendstoSmoothLimit
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0204
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0134
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0330
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0221
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumHeckeEigenvalueGeneratingSeriesGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0182
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1239
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0183
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0155
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0207
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0253
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0237
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0011
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0254
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableMatrixCoeffKAverageRight

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteSupport
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical

namespace GlobalTheory.Chain.IoLift

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def KerLe {A B Z₁ Z₂ : Type} [AddCommMonoid Z₁] [AddCommMonoid Z₂] (q₁ : A → B → Z₁) (q₂ : A → B → Z₂) : Prop :=
  ∀ (n : ℕ) (a : Fin n → A) (b : Fin n → B), ∑ i, q₁ (a i) (b i) = 0 → ∑ i, q₂ (a i) (b i) = 0

def AbsIrr {G K : Type} [AddCommGroup K] [Module ℂ K] (a : G → Module.End ℂ K) : Prop :=
  (∀ N : Submodule ℂ K, (∀ g, ∀ x ∈ N, a g x ∈ N) → N = ⊥ ∨ N = ⊤) ∧
    ∀ T : Module.End ℂ K, (∀ g, T ∘ₗ a g = a g ∘ₗ T) → ∃ c : ℂ, T = c • LinearMap.id

def intersection_update_fsHerm_neg_one {ι : Type} {K : ι → Type} [∀ i, AddCommGroup (K i)] [∀ i, Module ℂ (K i)] (i : ι) (f : Module.End ℂ (K i)) :
    Module.End ℂ (⨂[ℂ] j, K j) :=
  PiTensorProduct.map (Function.update (fun j => (LinearMap.id : K j →ₗ[ℂ] K j)) i f)

theorem position_tprod {ι : Type} {K : ι → Type} [∀ i, AddCommGroup (K i)] [∀ i, Module ℂ (K i)] (i : ι)
    (f : Module.End ℂ (K i)) (v : ∀ j, K j) :
    intersection_update_fsHerm_neg_one i f (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ (Function.update v i (f (v i))) := by
  unfold intersection_update_fsHerm_neg_one
  rw [PiTensorProduct.map_tprod]
  congr 1
  funext j
  rcases eq_or_ne j i with rfl | hji
  · simp
  · simp [hji]

section Cover

variable {p q r s : ℕ}

def AdjRule {Y Z : Type} [AddCommGroup Y] [Module ℂ Y] [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (B : Pol p q r s →ₗ[ℂ] Y →ₛₗ[starRingEnd ℂ] Z) : Prop :=
  ∀ (X : Mat p q) P P' y y', ⟪B (fockAct1 p q r s X P) y, B P' y'⟫_ℂ = ⟪B P y, B (fockAct1 p q r s (adjZ X) P') y'⟫_ℂ

def InvRule (N : GKMod r s) {Z : Type} [AddCommGroup Z] [Module ℂ Z]
    (B : Pol p q r s →ₗ[ℂ] N.V →ₛₗ[starRingEnd ℂ] Z) : Prop :=
  ∀ (Y : Mat r s) P y, B (fockAct2 p q r s Y P) y = B P (N.act (adjZ Y) y)

variable (p q r s) in

def UnitaryImage : Prop :=
  ∀ (Y Z : Type) [AddCommGroup Y] [Module ℂ Y] [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (B : Pol p q r s →ₗ[ℂ] Y →ₛₗ[starRingEnd ℂ] Z), AdjRule B →
    ∃ (A : UGKMod p q) (j : A.M.V →ₗ[ℂ] Z) (B' : Pol p q r s →ₗ[ℂ] Y →ₛₗ[starRingEnd ℂ] A.M.V),
      Function.Injective j ∧ (∀ P y, j (B' P y) = B P y) ∧ Submodule.span ℂ {x | ∃ P y, B' P y = x} = ⊤ ∧
        ∀ X P y, B' (fockAct1 p q r s X P) y = A.M.act X (B' P y)

def contr {A V H : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (ι : V →ₗ[ℂ] H) (y : V) : A ⊗[ℂ] V →ₗ[ℂ] A :=
  (TensorProduct.rid ℂ A).toLinearMap ∘ₗ LinearMap.lTensor A (innerₛₗ ℂ (ι y) ∘ₗ ι)

variable (p q) in

def FiniteSupport {T : GrpData r s} (R : DSRep T) : Prop :=
  ∀ (A : Type) [AddCommGroup A] [Module ℂ A] (B : Pol p q r s →ₗ[ℂ] R.HK.V →ₛₗ[starRingEnd ℂ] A), InvRule R.HK B →
    ∀ P, ∃ E : Submodule ℂ R.HK.V, FiniteDimensional ℂ E ∧ ∀ y, (∀ e ∈ E, ⟪R.ι y, R.ι e⟫_ℂ = 0) → B P y = 0

def TensorForm : Prop :=
  ∀ (U A V H : Type) [AddCommGroup U] [Module ℂ U] [AddCommGroup A] [Module ℂ A] [AddCommGroup V] [Module ℂ V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : V →ₗ[ℂ] H), Function.Injective ι →
    (∀ t : A ⊗[ℂ] V, (∀ y, contr ι y t = 0) → t = 0) ∧
    ∀ B : U →ₗ[ℂ] V →ₛₗ[starRingEnd ℂ] A,
      (∀ P, ∃ E : Submodule ℂ V, FiniteDimensional ℂ E ∧ ∀ y, (∀ e ∈ E, ⟪ι y, ι e⟫_ℂ = 0) → B P y = 0) →
      ∃ f : U →ₗ[ℂ] A ⊗[ℂ] V, ∀ P y, contr ι y (f P) = B P y

structure IsCoverPair (N : GKMod r s) {Z : Type} [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (B : Pol p q r s →ₗ[ℂ] N.V →ₛₗ[starRingEnd ℂ] Z) : Prop where
  skew : ∀ X ∈ upq p q, ∀ P P' y y',
    ⟪B (fockAct1 p q r s X P) y, B P' y'⟫_ℂ + ⟪B P y, B (fockAct1 p q r s X P') y'⟫_ℂ = 0
  inv : ∀ Y ∈ upq r s, ∀ P y, B (fockAct2 p q r s Y P) y + B P (N.act Y y) = 0

variable (p q) in

def CoverKer (N : GKMod r s) : Prop :=
  ∀ (Z₁ Z₂ : Type) [NormedAddCommGroup Z₁] [InnerProductSpace ℂ Z₁] [NormedAddCommGroup Z₂] [InnerProductSpace ℂ Z₂]
    (B₁ : Pol p q r s →ₗ[ℂ] N.V →ₛₗ[starRingEnd ℂ] Z₁) (B₂ : Pol p q r s →ₗ[ℂ] N.V →ₛₗ[starRingEnd ℂ] Z₂),
    IsCoverPair N B₁ → IsCoverPair N B₂ → B₁ ≠ 0 → KerLe (fun P y => B₁ P y) fun P y => B₂ P y

end Cover

variable {D : D7} {V W : HSp D} {S S' : D.what₂.Tau → SPar} (M : DSModel V S) (M' : DSModel W S')

structure IsKAct (τ : D.what₂.Tau) (a : Matrix (Fin V.rank) (Fin V.rank) ℂ → Module.End ℂ (kFin M τ)) : Prop where
  der : ∀ X ∈ lieAt V τ, ∀ v : kFin M τ,
    HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (v : M.H τ)) (a X v : M.H τ) 0
  skew : ∀ X ∈ lieAt V τ, ∀ v w : kFin M τ, ⟪a X v, w⟫_ℂ + ⟪v, a X w⟫_ℂ = 0

def KSm : Prop := ∀ τ, kFin M τ ≤ M.sm τ

abbrev KT : Type := ⨂[ℂ] τ, kFin M τ

variable {M} in

def inclK (h : KSm M) : KT M →ₗ[ℂ] SmT M := PiTensorProduct.map fun τ => Submodule.inclusion (h τ)

def kOp (τ : D.what₂.Tau) {k : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hk : k ∈ maxCpt M τ) : Module.End ℂ (kFin M τ) :=
  (M.rep τ k : M.H τ →ₗ[ℂ] M.H τ).restrict fun _ hv => rep_mem_kFin M τ hk hv

def sOp (τ : D.what₂.Tau) (aT : ℚ) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) : Module.End ℂ (LPol W.rank V.rank) :=
  locS (M.ε τ) (M'.ε τ) ((M.fr τ * X * (M.fr τ)⁻¹).map (starRingEnd ℂ)) + (-((aT : ℂ) * X.trace)) • 1

def tOp (τ : D.what₂.Tau) (aS : ℚ) (Y : Matrix (Fin W.rank) (Fin W.rank) ℂ) : Module.End ℂ (LPol W.rank V.rank) :=
  locT (M.ε τ) (M'.ε τ) (M'.fr τ * Y * (M'.fr τ)⁻¹) + ((aS : ℂ) * Y.trace) • 1

structure IsLocPair (τ : D.what₂.Tau) (aS aT : ℚ) (a' : Matrix (Fin W.rank) (Fin W.rank) ℂ → Module.End ℂ (kFin M' τ))
    {Z : Type} [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] (B : LPol W.rank V.rank →ₗ[ℂ] kFin M' τ →ₗ[ℂ] Z) :
    Prop where
  skew : ∀ X ∈ lieAt V τ, ∀ P P' y y', ⟪B (sOp M M' τ aT X P) y, B P' y'⟫_ℂ + ⟪B P y, B (sOp M M' τ aT X P') y'⟫_ℂ = 0
  inv : ∀ Y ∈ lieAt W τ, ∀ P y, B (tOp M M' τ aS Y P) y + B P (a' Y y) = 0

def LocKer (τ : D.what₂.Tau) (aS aT : ℚ) (a' : Matrix (Fin W.rank) (Fin W.rank) ℂ → Module.End ℂ (kFin M' τ)) : Prop :=
  ∀ (Z₁ Z₂ : Type) [NormedAddCommGroup Z₁] [InnerProductSpace ℂ Z₁] [NormedAddCommGroup Z₂] [InnerProductSpace ℂ Z₂]
    (B₁ : LPol W.rank V.rank →ₗ[ℂ] kFin M' τ →ₗ[ℂ] Z₁) (B₂ : LPol W.rank V.rank →ₗ[ℂ] kFin M' τ →ₗ[ℂ] Z₂),
    IsLocPair M M' τ aS aT a' B₁ → IsLocPair M M' τ aS aT a' B₂ → B₁ ≠ 0 →
      KerLe (fun P y => B₁ P y) fun P y => B₂ P y

def IsCuspGrow (θ : InfFam D) (V : HSp D) (φ : GA D V → ℂ) : Prop :=
  IsAutFun V φ ∧ φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V ∧ IsCuspFun V φ ∧ GlobalTheory.Grow.UnifModGrowth V θ φ

def kMean (τ : D.what₂.Tau) (e : Formalism.REAL.KG (M.ε τ) → ℂ) (w : M.H τ) : M.H τ :=
  ∫ k, e k • M.σ τ (Formalism.REAL.toMK k) w ∂(Formalism.REAL.muK (M.ε τ))

def IsCoefFam {G : Type} [Group G] [TopologicalSpace G] {n : ℕ} (c : Fin n → G → ℂ) : Prop :=
  (∀ i, Continuous (c i)) ∧ ∀ (k₀ : G) (i : Fin n), ∃ d : Fin n → ℂ, ∀ k, c i (k₀ * k) = ∑ j, d j * c j k

end GlobalTheory.Chain.IoLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsOverVacuumIsometryOfSkeletonDatum
section
open Formalism.BasicNotions

namespace GlobalTheory

theorem vacuumFock_all_records : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors.VacuumFock D := GlobalTheory.T.fockVectors_overVacuum_isometry

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridLiftsFixedByCongruenceDepthOfDepthData
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.Asc

theorem partFixed_of_depFixed : DepFixed → DatumDep → PartFixed := by
  intro hD hd D q T L μ0 hL sc G W M hM ρ Φ u i h k hk g
  have hf := hd D q T L μ0 hL sc G W M hM ρ Φ ⟨i, h⟩
  have key := hD D q T L μ0 hL sc G W M hM i h (.chi i 0) (Or.inl rfl) _ hf 1 (one_mem _) k hk
  show liftA W M (.right i 0) (W.datum ρ Φ ⟨i, h⟩) _ (g * k) = liftA W M (.right i 0) (W.datum ρ Φ ⟨i, h⟩) _ g
  rw [liftA_apply, liftA_apply]
  congr 1
  funext x
  congr 1
  show W.om (.chi i 0) (negGA _ (g * k), x) _ 0 = W.om (.chi i 0) (negGA _ g, x) _ 0
  have e : ((negGA _ (g * k), x) : GA D (G.pS (.chi i 0)) × GA D (G.pT (.chi i 0))) =
      (negGA _ g, x) * G.toPair (.chi i 0) 1 k := by
    show _ = (negGA _ g, x) * (negGA _ k, 1)
    rw [map_mul, Prod.mk_mul_mk, mul_one]
  rw [e, map_mul, Module.End.mul_apply, key]

end GlobalTheory.Asc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GrowthSobolevCauchyTendstoSmoothLimitStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.growthSobolev_cauchy_tendsto_smooth_limit : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (N : ℕ) (ψ : ℕ → GA D V → ℂ), (∀ n, Continuous (ψ n) ∧ ψ n ∈ GlobalTheory.Mem.AutSpace.SmFun θ V ∧ ∀ d, GlobalTheory.Size.growthSob θ V d N (ψ n) ≠ ⊤) → (∀ d, Filter.Tendsto (fun p : ℕ × ℕ => GlobalTheory.Size.growthSob θ V d N (ψ p.1 - ψ p.2)) Filter.atTop (nhds 0)) → ∃ f : GA D V → ℂ, Continuous f ∧ f ∈ GlobalTheory.Mem.AutSpace.SmFun θ V ∧ ∀ d, Filter.Tendsto (fun n => GlobalTheory.Size.growthSob θ V d N (ψ n - f)) Filter.atTop (nhds 0) := by
  first | exact @GlobalTheory.GrowthComplete.complete | exact GlobalTheory.GrowthComplete.complete | (intros; apply GlobalTheory.GrowthComplete.complete <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumHeckeEigenvalueGeneratingSeriesGLStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_heckeEigenvalue_generatingSeries_GL : GlobalTheory.Published.UnramifiedDoublingGL → ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin r) (w.adicCompletion E)) V) (x : V) (B : Multiset ℂˣ), IsSatVecGL w ρ x B → ∀ ϖ, IsUnifV E w ϖ → ∀ t : (Fin r → ℤ) → GL (Fin r) (w.adicCompletion E), (∀ d, (t d).1 = Matrix.diagonal fun i => ϖ ^ d i) → ∀ c : (Fin r → ℤ) → ℂ, (∀ d, heckeVec ρ (KGL w r) (dosetInd ℂ (KGL w r) (t d)) x = c d • x) → ∃ δ : ℝ, 0 < δ ∧ ∀ X : ℝ, 0 < X → X < δ → HasSum (fun d : {d : Fin r → ℤ // Antitone d} => c d.1 * (X : ℂ) ^ (∑ i, |d.1 i|).toNat) (eulerFac B ((qV E w : ℂ) ^ (((r : ℂ) - 1) / 2) * X) * eulerFac (B.map (·⁻¹)) ((qV E w : ℂ) ^ (((r : ℂ) - 1) / 2) * X) * ∏ i ∈ Finset.range r, (1 - (qV E w : ℂ) ^ i * (X : ℂ) ^ 2)) := by
  first | exact @GlobalTheory.FinZeta.GLSeries.hasSum_hecke_eigenvalues | exact GlobalTheory.FinZeta.GLSeries.hasSum_hecke_eigenvalues | (intros; apply GlobalTheory.FinZeta.GLSeries.hasSum_hecke_eigenvalues <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeOperatorFaceLevelEqPrincipalLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevOpFace

theorem heckeOp_face_to_principal : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ SF, GlobalTheory.Hk3.IsSF R SF → ∀ (b : Bool) (i : Fin D.R.m) (P : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ) (B : Finset (GA D (Wc D i))), Hecke₂ (Wc D i) (levS _ (R.βW i) (R.datWp i (R.levL F b (sg0 D A)))) (levChi _ (R.βW i) (R.datWp i (R.levL F b (sg0 D A)))) SF P d B → Hecke₂ (Wc D i) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) SF P d B := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC SF hSF b i P d B hB
  have hS : OffS D SF P := by
    obtain ⟨_, _, _, _, hS, -⟩ := hB
    exact hS
  have hG : GlobalTheory.Hk3.Good R A.μ0 P := ((GlobalTheory.GoodPrimes.good_primes R F hC.lev).2.2.1 SF hSF P).1 hS
  obtain ⟨n, hβ⟩ := hC.lev.βW i
  have hN : (((1 ^ n : ℕ) : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    rw [one_pow, Nat.cast_one]
    exact fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have hPP : ∀ L : LevelP R.Pg D.R.r ℂ, ∀ PP, PP ∈ (R.datWp i L).Pg ∨ PP ∈ (R.datWp i L).Q →
      PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P := fun L PP h =>
    hG PP (Or.inl (h.resolve_right (Finset.notMem_empty _)))
  have h1 := ((GlobalTheory.LevOp.level_operators (Wc D i) (R.βW i) (R.ΛW i) (1 ^ n)
    (R.datWp i (R.levL F b (sg0 D A))) hβ P hN (hPP _)).2.1 SF d B).1 hB
  exact ((GlobalTheory.LevOp.level_operators (Wc D i) (R.βW i) (R.ΛW i) (1 ^ n) (R.datWp i R.triv) hβ P hN (hPP _)).2.1 SF d B).2 h1

end GlobalTheory.LevOpFace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergVacuumCommutantPreservesLatticeVacua
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
open GlobalTheory.OrientedHeis GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars

noncomputable section

namespace GlobalTheory.Asc

variable {D : D7}

theorem symplOH_swap {S T : HSp D} (x y : WO S T) : symplOH S T y x = -symplOH S T x y := by
  have h := symplOH_self (S := S) (T := T) (x + y)
  rw [symplOH_add_left, symplOH_add_right, symplOH_add_right, symplOH_self, symplOH_self] at h
  linear_combination h

theorem symplO_swap {S T : HSp D} (x y : WO S T) : symplO S T y x = -symplO S T x y := by
  rw [GlobalTheory.ThetaSquare.symplO_eq, GlobalTheory.ThetaSquare.symplO_eq, symplOH_swap]; ring

theorem psi_symplO_swap (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (x y : WO S T) :
    ψ (symplO S T y x) = 1 ↔ ψ (symplO S T x y) = 1 := by
  rw [symplO_swap, AddChar.map_neg_eq_inv, inv_eq_one]

theorem heisO_comm (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (a b : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T a (heisO ψ S T b f) = ψ (symplO S T a b) • heisO ψ S T b (heisO ψ S T a f) := by
  rw [heisO_heisO, heisO_heisO, smul_smul, add_comm b a, ← AddChar.map_add_eq_mul,
    GlobalTheory.ThetaSquare.symplO_eq, symplOH_swap a b]
  have e : symplOH S T a b + symplOH S T a b + -symplOH S T a b = symplOH S T a b := by ring
  rw [e]

theorem annVac : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (Γ : AddSubgroup (WO S T)),
    (∀ f, VacG ψ S T Γ f → ∀ w ∈ Ann ψ S T Γ, VacG ψ S T Γ (heisO ψ S T w f)) ∧
    (∀ w : WO S T, (∀ u ∈ Γ, u.map (infPart D) = 0) → w.map (finPart D) = 0 → w ∈ Ann ψ S T Γ) ∧
    ∀ (v : VolM D T.rank S.rank) f f₀, VacG ψ S T Γ f → VacG ψ S T Γ f₀ → ∀ w, w ∉ Ann ψ S T Γ →
      thPair v.μ v.𝓕 f (heisO ψ S T w f₀) = 0 := by
  intro D ψ hψ S T Γ
  refine ⟨fun f hf w hw => ?_, fun w hΓ hw => ?_, fun v f f₀ hf hf₀ w hw => ?_⟩
  · refine ⟨GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf.1 w, fun u hu => ?_, fun e he u hu hh => ?_⟩
    · show heisO ψ S T (2 • u) (heisO ψ S T w f) = heisO ψ S T w f
      rw [heisO_comm, hf.2.1 u hu, (psi_symplO_swap ψ _ _).2 (hw.1 u hu), one_smul]
    · show heisO ψ S T u (heisO ψ S T w f) = heisO ψ S T w f
      rw [heisO_comm, hf.2.2 e he u hu hh, (psi_symplO_swap ψ _ _).2 (hw.2 e he u hu hh), one_smul]
  · have key : ∀ u ∈ Γ, symplO S T w u = 0 := fun u hu => by
      rw [GlobalTheory.ThetaSquare.symplO_eq, (symplOH_fin_real (hΓ u hu) hw).2, add_zero]
    refine ⟨fun u hu => ?_, fun e _ u hu _ => by rw [key u hu, AddChar.map_zero_eq_one]⟩
    rw [key _ (Γ.nsmul_mem hu 2), AddChar.map_zero_eq_one]
  · obtain ⟨hμ, h𝓕, -⟩ := v.covol
    have hex : ∃ u, heisO ψ S T u f = f ∧ heisO ψ S T u f₀ = f₀ ∧ ψ (symplO S T w u) ≠ 1 := by
      by_contra hno
      push_neg at hno
      exact hw ⟨fun u hu => hno _ (hf.2.1 u hu) (hf₀.2.1 u hu),
        fun e he u hu hh => hno _ (hf.2.2 e he u hu hh) (hf₀.2.2 e he u hu hh)⟩
    obtain ⟨u, hu, hu₀, hc⟩ := hex
    have hg := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf₀.1 w
    have e1 := GlobalTheory.Size.ipO_heisO hψ hμ h𝓕 hf.1 hg u
    rw [hu, heisO_comm, hu₀] at e1
    have e2 : GlobalTheory.Ker.ipO v.μ v.𝓕 f (ψ (symplO S T u w) • heisO ψ S T w f₀) =
        starRingEnd ℂ (ψ (symplO S T u w)) * GlobalTheory.Ker.ipO v.μ v.𝓕 f (heisO ψ S T w f₀) := by
      unfold GlobalTheory.Ker.ipO
      rw [← integral_const_mul]
      congr 1; funext x; simp only [Pi.smul_apply, smul_eq_mul, map_mul]; ring
    have hc' : starRingEnd ℂ (ψ (symplO S T u w)) ≠ 1 := by
      intro h
      apply hc
      have h2 := congrArg (starRingEnd ℂ) h
      rw [Complex.conj_conj, map_one] at h2
      exact (psi_symplO_swap ψ _ _).1 h2
    rw [e2] at e1
    show GlobalTheory.Ker.ipO v.μ v.𝓕 f (heisO ψ S T w f₀) = 0
    have h3 : (starRingEnd ℂ (ψ (symplO S T u w)) - 1) * GlobalTheory.Ker.ipO v.μ v.𝓕 f (heisO ψ S T w f₀) = 0 := by
      linear_combination e1
    exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hc')

end GlobalTheory.Asc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianPairingSelfDualCompletionIntegralAtPlac
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option synthInstance.maxHeartbeats 160000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.LatPairInt

variable {D : D7}

theorem cA_tmul (p : AF D.host.F) (t : D.host.E) :
    cA D (p ⊗ₜ[D.host.F] t) = p ⊗ₜ[D.host.F] (star t) :=
  rfl

theorem intAt_zero (P : GlobalTheory.FinPl.Pl D → Prop) : (0 : AE D) ∈ intAt D P :=
  ⟨zero_mem _, by rw [map_zero]; exact zero_mem _⟩

theorem intAt_add {P : GlobalTheory.FinPl.Pl D → Prop} {a b : AE D} (ha : a ∈ intAt D P) (hb : b ∈ intAt D P) :
    a + b ∈ intAt D P :=
  ⟨add_mem ha.1 hb.1, by rw [map_add]; exact add_mem ha.2 hb.2⟩

theorem intAt_neg {P : GlobalTheory.FinPl.Pl D → Prop} {a : AE D} (ha : a ∈ intAt D P) : -a ∈ intAt D P :=
  ⟨neg_mem ha.1, by rw [map_neg]; exact neg_mem ha.2⟩

theorem pair_mul (α β : Af D.host.F) :
    pairA D.host.F 0 α * pairA D.host.F 0 β = pairA D.host.F 0 (α * β) :=
  Prod.ext (by show (0 : Ainf D.host.F) * 0 = 0; rw [zero_mul]) rfl

theorem term_eq (p q : AF D.host.F) (a g b : D.host.E) :
    cA D (p ⊗ₜ[D.host.F] a) * incA D g * (q ⊗ₜ[D.host.F] b) = (p * q) ⊗ₜ[D.host.F] (star a * g * b) := by
  rw [cA_tmul]
  change (p ⊗ₜ[D.host.F] star a) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] g) * (q ⊗ₜ[D.host.F] b) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]

theorem pairing_mem (S : HSp D) (L : GlobalTheory.FinPl.Lat S) (hL : IsSelfDualC S L) (P : GlobalTheory.FinPl.Pl D → Prop)
    (z w : Fin S.rank → AE D) (hz : z ∈ latV S L P) (hw : w ∈ latV S L P) :
    (∑ k, ∑ l, cA D (w k) * incA D (S.gram k l) * z l) ∈ intAt D P := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨α, hαi, hα, a, ha, x, hx, rfl⟩ := hz
    induction hw using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨β, hβi, hβ, a', ha', x', hx', rfl⟩ := hw
      rw [Set.mem_singleton_iff] at ha ha'
      subst ha ha'
      obtain ⟨b, hb⟩ := (hL.2 x).1 hx x' hx'
      have e : (∑ k, ∑ l, cA D (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x' k)) * incA D (S.gram k l) *
          (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x l))) =
          pairA D.host.F 0 (β * α) ⊗ₜ[D.host.F] (b : D.host.E) := by
        rw [hb, TensorProduct.tmul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [TensorProduct.tmul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [term_eq, pair_mul, one_mul, one_mul]
      show (∑ k, ∑ l, cA D (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x' k)) * incA D (S.gram k l) *
          (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x l))) ∈ intAt D P
      rw [e]
      refine ⟨GlobalTheory.FinPlLoc.pair_mem_idAt P _ (fun v hv => by rw [map_mul, hα v hv, mul_zero]) _, ?_⟩
      rw [GlobalTheory.FinPlLoc.finPart_pair]
      refine AddSubgroup.subset_closure ⟨β * α, fun v => ?_, b, rfl⟩
      rw [map_mul]; exact mul_mem (hβi v) (hαi v)
    | zero =>
      simp only [Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero]
      exact intAt_zero P
    | add w₁ w₂ _ _ h₁ h₂ =>
      simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
      exact intAt_add h₁ h₂
    | neg w _ h =>
      simp only [Pi.neg_apply, map_neg, neg_mul, Finset.sum_neg_distrib]
      exact intAt_neg h
  | zero =>
    simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero]
    exact intAt_zero P
  | add z₁ z₂ _ _ h₁ h₂ =>
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    exact intAt_add h₁ h₂
  | neg z _ h =>
    simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
    exact intAt_neg h

theorem pairing_mem_at : ∀ (D : D7) (S : HSp D) (L : GlobalTheory.FinPl.Lat S), IsSelfDualC S L → ∀ (v : GlobalTheory.FinPl.Pl D) (z w : Fin S.rank → AE D), z ∈ latV S L (· = v) → w ∈ latV S L (· = v) → (∑ k, ∑ l, cA D (w k) * incA D (S.gram k l) * z l) ∈ intAt D (· = v) :=
  fun _ S L hL v z w hz hw => pairing_mem S L hL (· = v) z w hz hw

end GlobalTheory.LatPairInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InertPlaceHomLatticeComponentsScaledIntegralStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPlace_homLattice_components_scaled_integral : ∀ (D : D7) (S T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) = v → IsInertAt D.host.F D.host.E v w → ∀ a : GL (Fin T.rank) (w.adicCompletion D.host.E), IsFrameAt w (frameLat T) a → ∃ (c₀ : w.adicCompletion D.host.E) (b : GL (Fin S.rank) (w.adicCompletion D.host.E)), c₀ ≠ 0 ∧ ∀ X : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E), X ∈ (GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)).toAddSubgroup.map (GlobalTheory.InertHomIdx.matW S T w) ↔ c₀ • ((a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 * X * b.1) ∈ GlobalTheory.InertHomIdx.intMat (w.adicCompletion D.host.E) T.rank S.rank := by
  first | exact @GlobalTheory.InertHomLattice.mem_map_latF_iff | exact GlobalTheory.InertHomLattice.mem_map_latF_iff | (intros; apply GlobalTheory.InertHomLattice.mem_map_latF_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableMatrixCoeffCyclicSpanStatement
section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_matrixCoeff_cyclic_span : ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (U : Type) [NormedAddCommGroup U] [InnerProductSpace ℂ U] (π : UJ ε →* (U →L[ℂ] U)), IsUnitaryRep π → ∀ (p : ℝ), 1 ≤ p → ∀ v : U, Integrable (fun g => ‖⟪v, π g v⟫_ℂ‖ ^ p) μ → ∀ u ∈ Submodule.span ℂ (Set.range fun g => π g v), ∀ u' ∈ Submodule.span ℂ (Set.range fun g => π g v), Integrable (fun g => ‖⟪u', π g u⟫_ℂ‖ ^ p) μ := by
  first | exact @GlobalTheory.span_orbit_coeff_integrable | exact GlobalTheory.span_orbit_coeff_integrable | (intros; apply GlobalTheory.span_orbit_coeff_integrable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableMatrixCoeffKAverageLeftStatement
section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_matrixCoeff_K_average_left : ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (U : Type) [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U] (π : UJ ε →* (U →L[ℂ] U)), IsUnitaryRep π → ∀ (p : ℝ), 1 ≤ p → ∀ φ : KG ε → ℂ, Continuous φ → ∀ u u' : U, Integrable (fun g => ‖⟪u', π g u⟫_ℂ‖ ^ p) μ → Integrable (fun g => ‖⟪∫ k, φ k • π k u' ∂(muK ε), π g u⟫_ℂ‖ ^ p) μ := by
  first | exact @GlobalTheory.integrable_inner_rpow_avg_left | exact GlobalTheory.integrable_inner_rpow_avg_left | (intros; apply GlobalTheory.integrable_inner_rpow_avg_left <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableMatrixCoeffKAverageRightStatement
section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_matrixCoeff_K_average_right : ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (U : Type) [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U] (π : UJ ε →* (U →L[ℂ] U)), IsUnitaryRep π → ∀ (p : ℝ), 1 ≤ p → ∀ φ : KG ε → ℂ, Continuous φ → ∀ u u' : U, Integrable (fun g => ‖⟪u', π g u⟫_ℂ‖ ^ p) μ → Integrable (fun g => ‖⟪u', π g (∫ k, φ k • π k u ∂(muK ε))⟫_ℂ‖ ^ p) μ := by
  first | exact @GlobalTheory.AvgRightLp.integrable_coeff_avg_right | exact GlobalTheory.AvgRightLp.integrable_coeff_avg_right | (intros; apply GlobalTheory.AvgRightLp.integrable_coeff_avg_right <;> assumption)
end

