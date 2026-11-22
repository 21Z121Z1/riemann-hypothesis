import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AemeasurableCxPosDensity
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.Bundle0001
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.SheetDensityEqSetSheetDensity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0018
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0039
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0049
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0057
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0063
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0018
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0062
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0042
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0044
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsGoodProjFirstCoordinate
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0022
import GroundTheory.HeightsAndTheta.Heights.FactorialBounds.Assembly
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HasSumPolyDerivMulProdAddMatrix
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0018
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsUnitOfLagrangian
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0003
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0043

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.AemeasurableCxPosDensityStatement
section
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.aemeasurable_cxPosDensity : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e : ℕ) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (L : Fin e → HermLine ι) (g : ((Σ k, ι k) → ℂ) → ℝ),
    IsCxVar Q e → IsSetGoodProj (conePts Q) Ψ → (∀ j, IsSmoothHerm (L j)) → Measurable g →
    (∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → g (fun p => c p.1 * z p) = g z) →
    AEMeasurable (cxPosDens (conePts Q) Ψ (pot L) g) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Pub.CxPosMeas.cxPosDens_aemeasurable | exact GlobalTheory.CompanionTheory.Ar.Pub.CxPosMeas.cxPosDens_aemeasurable | (intros; apply GlobalTheory.CompanionTheory.Ar.Pub.CxPosMeas.cxPosDens_aemeasurable <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockMapFrameRestriction
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.PFl.PtsBase

section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}
  {Kk : Type} [Fintype Kk] {ιk : Kk → Type} [∀ k, Fintype (ιk k)]

theorem exists_section (M : FlagModel y Ψ N j) {κ : Kk → K} {v : (Σ k, ιk k) → (Σ k, ι k)} (hb : IsBlockMap κ v)
    (hr : ∀ k : NonPluckerBlocks M.blk, k.1 ∈ Set.range κ) :
    ∃ (κ' : NonPluckerBlocks M.blk → Kk) (v' : (Σ k, baseIdx ι M.blk k) → (Σ k, ιk k)), IsBlockMap κ' v' ∧
      (∀ q, v (v' q) = ⟨q.1.1, q.2⟩) ∧ ∀ z, pBase M v z = z ∘ v' := by
  choose κ' hκ' using hr
  have hex : ∀ q : Σ k, baseIdx ι M.blk k, ∃ q', v q' = ⟨q.1.1, q.2⟩ := fun q =>
    hb.2.2.2 ⟨q.1.1, q.2⟩ ⟨κ' q.1, hκ' q.1⟩
  choose v' hv' using hex
  have hfst : ∀ p, (v' p).1 = κ' p.1 := fun p => hb.1 (by
    rw [← hb.2.2.1, hv', hκ'])
  refine ⟨κ', v', ⟨fun a b e => Subtype.ext (by rw [← hκ' a, ← hκ' b, e]), fun a b e => ?_, hfst, ?_⟩, hv', fun z => ?_⟩
  · have e' := congrArg v e
    rw [hv', hv'] at e'
    exact (GlobalTheory.CompanionTheory.Ar.PB.CPts.blockMap_base M).2.1 e'
  · rintro q ⟨kb, hq⟩
    have h1 : (v q).1 ∈ Set.range (Subtype.val : NonPluckerBlocks M.blk → K) :=
      ⟨kb, by rw [hb.2.2.1, ← hq, hκ']⟩
    obtain ⟨p, hp⟩ := (GlobalTheory.CompanionTheory.Ar.PB.CPts.blockMap_base M).2.2.2 (v q) h1
    exact ⟨p, hb.2.1 ((hv' p).trans hp)⟩
  · funext q
    show upV v z ⟨q.1.1, q.2⟩ = z (v' q)
    rw [← hv', upV_apply hb.2.1]

end

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (keep : Ψ × Fin N → Prop) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)), IsBlockMap κ v → (∀ k, k ∈ Set.range κ ↔ ((∀ p, M.blk p ≠ some k) ∨ ∃ p, keep p ∧ M.blk p = some k)) → (∀ z ∈ mcPts (mCoordIdeal (y ∘ v)), pBase M v z ∈ mcPts (mCoordIdeal M.x)) ∧ ∀ z z' : (Σ k, ιk k) → ℂ, SameOrbit z z' → SameOrbit (pBase M v z) (pBase M v z') := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M keep Kk _ ιk _ κ v hb hk
  obtain ⟨κ', v', hb', hv', hz⟩ := exists_section M hb fun k => (hk k.1).2 (Or.inl k.2)
  refine ⟨fun z hzm => ?_, fun z z' ho => ?_⟩
  · rw [hz]
    refine GlobalTheory.CompanionTheory.Ar.PB.CPts.comp_mem_mcPts hb' (algebraMap M.Ω Φ) (funext fun q => ?_) hzm
    show y (v (v' q)) = algebraMap M.Ω Φ (M.x q)
    rw [hv']
    exact M.y_base q
  · obtain ⟨c, hc, e⟩ := ho
    refine ⟨fun k => c (κ' k), fun k => hc _, ?_⟩
    rw [hz, hz, e]
    funext q
    show c (v' q).1 * z' (v' q) = c (κ' q.1) * z' (v' q)
    rw [hb'.2.2.1]

end GlobalTheory.CompanionTheory.Ar.PB.PFl.PtsBase
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.DomCellLogNormMeasurableInvariantStatement
section
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.domCell_logNorm_measurable_invariant : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (A : HermLine ι) (s : MRingOver ℂ ι) (a : K → ℕ) (i : (k : K) → ι k),
    IsSmoothHerm A → (∀ k, A.a k = a k) → IsMultiHomog s a →
    Measurable ((domCell i).indicator (absLogNorm A s)) ∧
    ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) →
      (domCell i).indicator (absLogNorm A s) (fun p => c p.1 * z p) =
        (domCell i).indicator (absLogNorm A s) z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Pub.CxChart.cutWeight_measurable_invariant | exact GlobalTheory.CompanionTheory.Ar.Pub.CxChart.cutWeight_measurable_invariant | (intros; apply GlobalTheory.CompanionTheory.Ar.Pub.CxChart.cutWeight_measurable_invariant <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsBlkCover
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} {N j : ℕ} {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {Φ' : Type} [Field Φ']
  {y' : (Σ k, ι' k) → Φ'}

def plk (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (b : (Σ k, baseIdx ι M.blk k) → ℂ) (i : Fin N)
    (q : Σ k, ι k) (h : Matrix (Fin N) (Fin N) ℂ) : ℂ :=
  ∑ I, valAt M.x (F.u q I) b * minorIJ h I (stepCols N j i)

def stepCoord {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M)
    (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk) (z : (Σ k, ι' k) → ℂ)
    (p : Ψ × Fin N) (k' : K') (q : Σ k, ι k) : ℂ :=
  ∑ I, valAt M.x (F.u q I) (basePart M'.blk z ∘ Cv.v) *
    ∑ I', if IsStepRows N j p.2 I' then minorIJ (Cv.trans F' F (basePart M'.blk z) p.1) I I' *
      ∑ m' : ι' k', valAt M'.x (F'.u' I' ⟨k', m'⟩) (basePart M'.blk z) * z ⟨k', m'⟩ else 0

def img {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M)
    (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk) (z : (Σ k, ι' k) → ℂ) :
    (Σ k, ι k) → ℂ := fun q =>
  if hk : ∀ p, M.blk p ≠ some q.1 then basePart M'.blk z (Cv.v ⟨⟨q.1, hk⟩, q.2⟩)
  else
    have hp : ∃ p, M.blk p = some q.1 := by simpa using hk
    match M'.blk hp.choose with
    | none => 0
    | some k' => stepCoord Cv F' F z hp.choose k' q

theorem img_base {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M)
    (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk) (z : (Σ k, ι' k) → ℂ) :
    basePart M.blk (img Cv F' F z) = basePart M'.blk z ∘ Cv.v := by
  funext q
  obtain ⟨⟨k, hk⟩, m⟩ := q
  simp only [basePart, img, Function.comp]
  rw [dif_pos hk]

theorem img_step {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M)
    (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk) (z : (Σ k, ι' k) → ℂ)
    {p : Ψ × Fin N} {k : K} {k' : K'} (hp : M.blk p = some k) (hp' : M'.blk p = some k') (m : ι k) :
    img Cv F' F z ⟨k, m⟩ = stepCoord Cv F' F z p k' ⟨k, m⟩ := by
  have hk : ¬ ∀ p', M.blk p' ≠ some k := fun h => h p hp
  have hex : ∃ p', M.blk p' = some k := ⟨p, hp⟩
  have hch : hex.choose = p := M.blk_inj _ _ k hex.choose_spec hp
  simp only [img, dif_neg hk]
  split
  · next h =>
    rw [hch, hp'] at h
    exact absurd h (by simp)
  · next k'' h =>
    rw [hch, hp'] at h
    cases h
    rw [hch]

theorem exists_blk_cover {M : FlagModel y Ψ N j} (M' : FlagModel y' Ψ N j) {p : Ψ × Fin N} {k : K}
    (hp : M.blk p = some k) : ∃ k', M'.blk p = some k' := by
  have h1 : ¬ (M.blk p = none) := by
    rw [hp]
    simp
  rw [M.blk_none] at h1
  have h2 : M'.blk p ≠ none := by
    rw [Ne, M'.blk_none]
    exact h1
  exact Option.ne_none_iff_exists'.mp h2

end GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsGoodProjFirstCoordinateStatement
section
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_goodProj_first_coordinate : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e : ℕ) (i : (k : K) → ι k),
    IsCxVar Q e → (∃ z ∈ conePts Q, segre z i ≠ 0) →
    ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ),
      IsSetGoodProj (conePts Q) Ψ ∧ ∀ w, Ψ w 0 = w i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Pub.CxGoodProj.exists_goodProj_coord | exact GlobalTheory.CompanionTheory.Ar.Pub.CxGoodProj.exists_goodProj_coord | (intros; apply GlobalTheory.CompanionTheory.Ar.Pub.CxGoodProj.exists_goodProj_coord <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsSymplecticBasisPrincipalPolarization
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

namespace GlobalTheory.CompanionTheory.Ar.Sl.SymplecticLattice

open scoped Matrix

noncomputable def imForm {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) :
    LinearMap.BilinForm ℝ (Fin g → ℂ) :=
  LinearMap.mk₂ ℝ (fun y w => (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm y w).im)
    (fun a b w => by simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, add_dotProduct])
    (fun c a w => by
      simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, smul_dotProduct, Complex.smul_im])
    (fun y a b => by
      simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, Matrix.mulVec_add, dotProduct_add])
    (fun c y a => by
      simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul,
        Complex.smul_im])

theorem imForm_apply {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (y w : Fin g → ℂ) :
    imForm Hm y w = (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm y w).im := rfl

theorem imForm_smul_I {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) :
    imForm Hm z (Complex.I • z) = -(ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z z).re := by
  simp [imForm_apply, ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, star_smul, Matrix.mulVec_smul,
    dotProduct_smul, Matrix.mulVec_neg, dotProduct_neg]

theorem imForm_injective {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z z).re) :
    Function.Injective (imForm Hm) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  by_contra h0
  have h1 := imForm_smul_I Hm z
  rw [hz] at h1
  have := hpos z h0
  simp at h1
  linarith

theorem imForm_surjective {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z z).re) :
    Function.Surjective (imForm Hm) :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (Subspace.dual_finrank_eq (K := ℝ) (V := Fin g → ℂ)).symm).1 (imForm_injective Hm hpos)

theorem exists_symplectic_basis : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ),
    DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → Hm.IsHermitian →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) →
    (∀ l l' : Λ, ∃ k : ℤ, (hermForm Hm (l : Fin g → ℂ) (l' : Fin g → ℂ)).im = k) →
    (∀ w : Fin g → ℂ, (∀ l : Λ, ∃ k : ℤ, (hermForm Hm w (l : Fin g → ℂ)).im = k) → w ∈ Λ) →
    ∃ bs : Module.Basis (Fin g ⊕ Fin g) ℤ Λ, ∀ α β,
      (hermForm Hm (bs α : Fin g → ℂ) (bs β : Fin g → ℂ)).im = Matrix.J (Fin g) ℝ α β := by
  intro g Λ Hm hdisc hspan hH hpos hint hdual
  haveI : IsZLattice ℝ Λ := ⟨hspan⟩
  choose k hk using hint
  let Ef : LinearMap.BilinForm ℤ Λ := LinearMap.mk₂ ℤ (fun x y => k x y)
    (fun x x' y => by
      apply Int.cast_injective (α := ℝ); push_cast; simp only [← hk, ← imForm_apply]
      simp)
    (fun c x y => by
      apply Int.cast_injective (α := ℝ); simp only [smul_eq_mul]; push_cast
      simp only [← hk, ← imForm_apply]
      simp [← Int.cast_smul_eq_zsmul ℝ c])
    (fun x y y' => by
      apply Int.cast_injective (α := ℝ); push_cast; simp only [← hk, ← imForm_apply]
      simp)
    (fun c x y => by
      apply Int.cast_injective (α := ℝ); simp only [smul_eq_mul]; push_cast
      simp only [← hk, ← imForm_apply]
      simp [← Int.cast_smul_eq_zsmul ℝ c])
  have hE : ∀ l m : Λ, (Ef l m : ℝ) = imForm Hm (l : Fin g → ℂ) (m : Fin g → ℂ) :=
    fun l m => (hk l m).symm
  have hanti : ∀ l m : Λ, Ef m l = - Ef l m := fun l m => by
    apply Int.cast_injective (α := ℝ)
    have h1 := congrArg Complex.im (GlobalTheory.SiegelNormalForm.form_conj hH (l : Fin g → ℂ) m)
    simp only [Complex.star_def, Complex.conj_im] at h1
    push_cast
    rw [hE, hE, imForm_apply, imForm_apply]
    exact h1.symm
  have halt : Ef.IsAlt := fun l => by
    have := hanti l l
    omega
  have hinj : Function.Injective Ef := by
    rw [injective_iff_map_eq_zero]
    intro l hl
    have hle : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) ≤
        LinearMap.ker (imForm Hm (l : Fin g → ℂ)) := by
      rw [Submodule.span_le]
      intro m hm
      have := hE l ⟨m, hm⟩
      rw [hl] at this
      simpa using this.symm
    rw [hspan] at hle
    have h0 : imForm Hm (l : Fin g → ℂ) = 0 := LinearMap.ext fun y => hle (Submodule.mem_top)
    exact Subtype.ext ((injective_iff_map_eq_zero _).1 (imForm_injective Hm hpos) _ h0)
  have hsurj : Function.Surjective Ef := by
    intro φ
    let b := Module.finBasis ℤ Λ
    let bR := b.ofZLatticeBasis ℝ Λ
    let ψ : (Fin g → ℂ) →ₗ[ℝ] ℝ := bR.constr ℝ fun i => (φ (b i) : ℝ)
    have hψ : ∀ y : Λ, ψ (y : Fin g → ℂ) = (φ y : ℝ) := by
      intro y
      have hb : ∀ i, ψ (b i : Fin g → ℂ) = (φ (b i) : ℝ) := fun i => by
        have h := bR.constr_basis ℝ (fun i => (φ (b i) : ℝ)) i
        rwa [show bR i = (b i : Fin g → ℂ) by simp [bR]] at h
      conv_lhs => rw [← b.sum_repr y]
      conv_rhs => rw [← b.sum_repr y]
      simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul, map_sum, map_zsmul, hb]
      simp
    obtain ⟨w, hw⟩ := imForm_surjective Hm hpos ψ
    have hwy : ∀ y : Λ, imForm Hm w (y : Fin g → ℂ) = (φ y : ℝ) := fun y => by rw [hw, hψ]
    have hwΛ : w ∈ Λ := hdual w fun l => ⟨φ l, hwy l⟩
    refine ⟨⟨w, hwΛ⟩, LinearMap.ext fun y => ?_⟩
    apply Int.cast_injective (α := ℝ)
    rw [hE, hwy]
  have hrank : Module.finrank ℤ Λ = 2 * g := by
    rw [ZLattice.rank ℝ Λ, Module.finrank_pi_fintype]
    simp [mul_comm]
  obtain ⟨bs, hbs⟩ := GlobalTheory.exists_isSymplecticBasis_of_finrank (B := -Ef) halt.neg
    (GlobalTheory.bijective_neg_bilinForm ⟨hinj, hsurj⟩) hrank
  have hval : ∀ α β, (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (bs α : Fin g → ℂ)
      (bs β : Fin g → ℂ)).im = (Ef (bs α) (bs β) : ℝ) := fun α β => (hE _ _).symm
  refine ⟨bs, ?_⟩
  have hee : ∀ i j, Ef (bs (Sum.inl i)) (bs (Sum.inl j)) = 0 := fun i j => by
    have := hbs.left_left i j
    simpa using this
  have hff : ∀ i j, Ef (bs (Sum.inr i)) (bs (Sum.inr j)) = 0 := fun i j => by
    have := hbs.right_right i j
    simpa using this
  have hef : ∀ i j, Ef (bs (Sum.inl i)) (bs (Sum.inr j)) = if i = j then -1 else 0 := fun i j => by
    have := hbs.left_right i j
    simp only [LinearMap.neg_apply, neg_eq_iff_eq_neg] at this
    rw [this]; split_ifs <;> simp
  rintro (i | i) (j | j)
  · rw [hval, hee]; simp [Matrix.J]
  · rw [hval, hef]
    by_cases h : i = j <;> simp [Matrix.J, h, Matrix.one_apply]
  · rw [hval, hanti, hef]
    by_cases h : i = j
    · subst h; simp [Matrix.J]
    · simp [Matrix.J, h, Ne.symm h, Matrix.one_apply]
  · rw [hval, hff]; simp [Matrix.J]

end GlobalTheory.CompanionTheory.Ar.Sl.SymplecticLattice
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartSeventh
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.Orb

section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

theorem blockMap_fst (k₀ : K) : IsBlockMap (ι := ι) (ι' := fun o : Option K => ι (o.getD k₀)) some (v₀ k₀) := by
  refine ⟨Option.some_injective _, ?_, fun _ => rfl, ?_⟩
  · rintro ⟨k, i⟩ ⟨k', i'⟩ h
    simp only [v₀, Sigma.mk.injEq, Option.some.injEq] at h
    obtain ⟨rfl, h⟩ := h
    simp only [Option.getD_some, heq_eq_eq] at h
    subst h
    rfl
  · rintro ⟨o, i⟩ ⟨k, hk⟩
    obtain rfl : o = some k := hk.symm
    exact ⟨⟨k, i⟩, rfl⟩

theorem baseOf_mem (M : FlagModel y Ψ N j) {τ : Ψ} {a : Fin N} {k₀ : K} {ca cb : Fin N}
    {z : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (hz : z ∈ mcPts (wP M τ a k₀ ca cb)) :
    baseOf M k₀ z ∈ mcPts (mCoordIdeal M.x) :=
  CPts.base_mem M (CPts.comp_mem_mcPts (blockMap_fst k₀) (algebraMap Φ (RatFunc Φ)) (funext fun _ => rfl) hz)

theorem twMinor_scale (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) {zb zb' : (Σ k, baseIdx ι M.blk k) → ℂ}
    (hv : ∀ s, valAt M.x s zb' = valAt M.x s zb) (i : Fin N) (k : K) (g : Matrix (Fin N) (Fin N) ℂ)
    {u u' : (Σ k, ι k) → ℂ} {t : ℂ} (hu : ∀ m : ι k, u' ⟨k, m⟩ = t * u ⟨k, m⟩) (J : Finset (Fin N)) :
    twMinor M F zb' i k g u' J = t * twMinor M F zb i k g u J := by
  have hp : ∀ I, pluck M F zb' k u' I = t * pluck M F zb k u I := fun I => by
    unfold pluck
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hv, hu]
    ring
  unfold twMinor
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [hp]
  ring

theorem lr_key (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) {zb zb' : (Σ k, baseIdx ι M.blk k) → ℂ}
    (hv : ∀ s, valAt M.x s zb' = valAt M.x s zb) (g : Matrix (Fin N) (Fin N) ℂ) (i : Fin N) (k : K)
    {u u' : (Σ k, ι k) → ℂ} {t : ℂ} (ht : t ≠ 0) (hu : ∀ m : ι k, u' ⟨k, m⟩ = t * u ⟨k, m⟩) (J J' : Finset (Fin N)) :
    twMinor M F zb' i k g u' J / twMinor M F zb' i k g u' J' = twMinor M F zb i k g u J / twMinor M F zb i k g u J' := by
  rw [twMinor_scale M F hv i k g hu J, twMinor_scale M F hv i k g hu J']
  exact mul_div_mul_left _ _ ht

theorem lowRead_scale (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) {zb zb' : (Σ k, baseIdx ι M.blk k) → ℂ}
    (hv : ∀ s, valAt M.x s zb' = valAt M.x s zb) (h : Ψ → Matrix (Fin N) (Fin N) ℂ)
    {u u' : (Σ k, ι k) → ℂ} {c : K → ℂ} (hc : ∀ k, c k ≠ 0) (hu : ∀ k (m : ι k), u' ⟨k, m⟩ = c k * u ⟨k, m⟩)
    (τ' : Ψ) (a' b' : Fin N) : lowRead M F zb' h u' τ' a' b' = lowRead M F zb h u τ' a' b' := by
  unfold lowRead
  exact congrArg (Option.elim (M.blk (τ', stepOf N j b')) 0) (funext fun k => lr_key M F hv _ _ k (hc k) (hu k) _ _)

end

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin (d + 2)), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h → ∀ z ∈ wO M Rb τ a k₀ ca cb F kb V r h, ∀ z' ∈ mcPts (wP M τ a k₀ ca cb), SameOrbit z' z → z' ∈ wO M Rb τ a k₀ ca cb F kb V r h ∧ wRho M Rb τ k₀ ca cb F kb r h ε z' = wRho M Rb τ k₀ ca cb F kb r h ε z := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε ctx z hz z' hz' ho
  obtain ⟨-, -, -, -, -, -, -, -, hr, -, -⟩ := ctx
  obtain ⟨hzP, hs, hV, hm₁, hm₂⟩ := hz
  obtain ⟨c, hc, rfl⟩ := ho
  set z' : (Σ o : Option K, ι (o.getD k₀)) → ℂ := fun p => c p.1 * z p with hz'def
  have hb := baseOf_mem M hzP
  have hb' := baseOf_mem M hz'
  have eb : baseOf M k₀ z' = fun q => c (some q.1.1) * baseOf M k₀ z q := rfl
  have hob : SameOrbit (baseOf M k₀ z') (baseOf M k₀ z) := ⟨fun k => c (some k.1), fun k => hc _, eb⟩
  have hnot : ∀ x : Rb.X, Rb.lift x x ∉ mcPts (⊤ : Ideal (MRing (baseIdx ι M.blk))) := fun x hx => by
    have := hx.2 1 Submodule.mem_top
    simp at this
  have hrr : r (baseOf M k₀ z') = r (baseOf M k₀ z) :=
    Rb.inj _ _ (hnot _) (orbit_trans (hr _ hb') (orbit_trans hob (orbit_symm (hr _ hb))))
  have hv : ∀ s, valAt M.x s (baseOf M k₀ z') = valAt M.x s (baseOf M k₀ z) := fun s => by
    have := StepW.TorusAct.valAt_torus (x := M.x) (fun k => c (some k.1)) (fun k => hc _) hb (eb ▸ hb') s
    rw [eb]
    exact this
  have h₁ : ∀ k (m : ι k), fstPt k₀ z' ⟨k, m⟩ = c (some k) * fstPt k₀ z ⟨k, m⟩ := fun _ _ => rfl
  let c₂ : K → ℂ := fun k => if k = k₀ then c none else c (some k)
  have hc₂ : ∀ k, c₂ k ≠ 0 := fun k => by
    simp only [c₂]
    split_ifs
    exacts [hc _, hc _]
  have h₂ : ∀ k (m : ι k), sndPt k₀ z' ⟨k, m⟩ = c₂ k * sndPt k₀ z ⟨k, m⟩ := fun k m => by
    by_cases hk : k = k₀
    · subst hk
      simp only [sndPt, Function.comp, v₁_self, c₂, if_true, hz'def]
    · simp only [sndPt, Function.comp, v₁_ne (p := ⟨k, m⟩) hk, c₂, if_neg hk, hz'def]
  refine ⟨?_, ?_⟩
  · show z' ∈ mcPts _ ∧ _
    refine ⟨hz', ?_, ?_, fun p k hp => ?_, ?_⟩
    · rw [hrr]; exact hs
    · rw [hrr]; exact hV
    · rw [twMinor_scale M F hv _ k _ (h₁ k)]
      exact mul_ne_zero (hc _) (hm₁ p k hp)
    · rw [twMinor_scale M F hv _ k₀ _ (h₂ k₀)]
      exact mul_ne_zero (hc₂ _) hm₂
  · funext i
    unfold wRho
    rcases ε.symm i with l | q | u
    · show Rb.A.chart kb (r (baseOf M k₀ z')) l = Rb.A.chart kb (r (baseOf M k₀ z)) l
      rw [hrr]
    · exact lowRead_scale M F hv h (fun k => hc (some k)) h₁ _ _ _
    · show lowRead M F _ h (sndPt k₀ z') τ cb ca - lowRead M F _ h (fstPt k₀ z') τ cb ca = _ - _
      rw [lowRead_scale M F hv h hc₂ h₂, lowRead_scale M F hv h (fun k => hc (some k)) h₁]

end GlobalTheory.CompanionTheory.Ar.PB.WMan.Orb
end
end

