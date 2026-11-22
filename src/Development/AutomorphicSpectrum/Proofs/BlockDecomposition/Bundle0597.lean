import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0572
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0519
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0531
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0567
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0568
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepTwistedBundleExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0523
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0011
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSmoothHermConstLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0569
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0522
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableHermC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0544
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0026
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0058
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1369
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1414
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetGramRatOneNeZero
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLemmas.ToComplBijective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0570
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0543

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FreeCell
section
noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStage

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep

def vH {K : Type} {M : ℕ} (a s : K) (Y : Fin M → K) : Fin (M + 2) → K :=
  Fin.cons a (Fin.cons s Y)

def tailH {K : Type} {M : ℕ} (x : Fin (M + 2) → K) : Fin M → K := fun i => x i.succ.succ

section Chart

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

def halfR : R ⊗[F] E := inclR R (algebraMap F E (1 / 2))

def tHalf (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x : Fin (M + 2) → R ⊗[F] E) : R ⊗[F] E :=
  halfR (F := F) (E := E) R * hR R σ (hypOne J) x x

def cvec (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x v : Fin (M + 2) → R ⊗[F] E) :
    Fin (M + 2) → R ⊗[F] E :=
  vH (x 0 * v 0)
    (v 0 * x 1 + Ring.inverse (sigR R σ (x 0)) *
      (v 1 - tHalf R σ J x * v 0 - hR R σ J (tailH x) (tailH v)))
    (fun i => v 0 * x i.succ.succ + v i.succ.succ)

def chartS (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (x : Fin 1 → Fin (M + 2) → R ⊗[F] E)
    (a s : Fin 1 → Fin n → R ⊗[F] E) (Y : Fin n → Fin M → R ⊗[F] E) : Fin (n + 1) → Fin (M + 2) → R ⊗[F] E :=
  Fin.cons (x 0) fun j => cvec R σ J (x 0) (vH (a 0 j) (s 0 j - tHalf R σ J (x 0) * a 0 j) (Y j))

variable {R} in

def yPart {K : Type} [CommRing K] {M n : ℕ} (X : Fin (n + 1) → Fin (M + 2) → K) : Fin n → Fin M → K :=
  fun j i => X j.succ i.succ.succ - X j.succ 0 * Ring.inverse (X 0 0) * X 0 i.succ.succ

def freeCell (K : Type) [CommRing K] (M n : ℕ) : Set (Fin (n + 1) → Fin (M + 2) → K) :=
  {X | IsUnit (X 0 0) ∧ LinearIndependent K (yPart X)}

theorem sigR_sigR (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) (y : R ⊗[F] E) : sigR R σ (sigR R σ y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [sigR, hσ]
  | add u v hu hv => simp only [map_add, hu, hv]

def qH (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) {n : ℕ} (t : HermR R σ 1) (s a : Fin 1 → Fin n → R ⊗[F] E) :
    HermR R σ n :=
  ⟨Matrix.of fun i j => sigR R σ (a 0 i) * s 0 j + sigR R σ (s 0 i) * a 0 j -
      (t : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0 * (sigR R σ (a 0 i) * a 0 j), by
    intro i j
    have ht : sigR R σ ((t : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0) = (t : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0 :=
      t.2 0 0
    simp only [Matrix.of_apply, map_add, map_sub, map_mul, sigR_sigR R σ hσ, ht]
    ring⟩

end Chart

theorem sig_invol {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (h : IsCMExt F E σ) (e : E) : σ (σ e) = e := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2 τ, h.2.2.2 τ]
  simp

end GlobalTheory.CompanionTheory.WeilSiegel.HypStage
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainSplitCentreProduct
section
open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.CompanionTheory.CuspTransfer

noncomputable section
namespace GlobalTheory.CompanionTheory.CuspTransfer

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

variable (E a) in

abbrev splitFd : Set (GA E a) :=
  (fun p : normOneGL E a × ℝ => splitCentre E a p.2 * (p.1 : GA E a)) ''
    (RightCosetSpace.fundamentalDomain (rationalGLOne E a) ×ˢ Set.Ico (0 : ℝ) 1)

theorem coe_rationalGLOne_mem_latticeGL (δ : rationalGLOne E a) :
    ((δ : normOneGL E a) : GA E a) ∈ latticeGL E a := by
  obtain ⟨γ, hγ⟩ : ((δ : normOneGL E a) : GA E a) ∈ AdelicGLn.rationalGL E a := δ.2
  rw [← hγ]
  exact ratGL_mem_latticeGL γ

theorem splitCentre_mul_mul_swap (s t : ℝ) (d x : GA E a) :
    splitCentre E a s * splitCentre E a t * (d * x) = d * splitCentre E a s * (splitCentre E a t * x) := by
  simp only [mul_assoc]
  rw [← mul_assoc (splitCentre E a t) d x, splitCentre_comm t d, mul_assoc d, ← mul_assoc (splitCentre E a s) d,
    splitCentre_comm s d, mul_assoc]

theorem exists_lattice_smul_mem_splitFd (ha : 0 < a) (g : GA E a) :
    ∃ l : latticeGL E a, l • g ∈ splitFd E a := by
  obtain ⟨e, he⟩ := GlobalTheory.T.adelic_GL_norm_one_split E a ha
  obtain ⟨⟨x, t⟩, rfl⟩ := e.surjective g
  rw [he]
  obtain ⟨δ, hδ, -⟩ := RightCosetSpace.existsUnique_smul_mem_fundamentalDomain (rationalGLOne E a) x
  have hn : splitCentre E a ((-⌊t⌋ : ℤ) : ℝ) ∈ latticeGL E a := by
    rw [splitCentre_intCast]
    exact zpow_mem_latticeGL _
  refine ⟨⟨((δ : normOneGL E a) : GA E a) * splitCentre E a ((-⌊t⌋ : ℤ) : ℝ),
    mul_mem (coe_rationalGLOne_mem_latticeGL δ) hn⟩, ⟨δ • x, Int.fract t⟩,
    ⟨hδ, Int.fract_nonneg t, Int.fract_lt_one t⟩, ?_⟩
  change splitCentre E a (Int.fract t) * (((δ : normOneGL E a) : GA E a) * (x : GA E a)) =
    ((δ : normOneGL E a) : GA E a) * splitCentre E a ((-⌊t⌋ : ℤ) : ℝ) * (splitCentre E a t * (x : GA E a))
  have hf : Int.fract t = ((-⌊t⌋ : ℤ) : ℝ) + t := by
    rw [Int.fract]
    push_cast
    ring
  rw [hf, splitCentre_add, splitCentre_mul_mul_swap]

theorem eq_one_of_mul_mem_splitFd (ha : 0 < a) {l g : GA E a} (hl : l ∈ latticeGL E a) (hg : g ∈ splitFd E a)
    (h : l * g ∈ splitFd E a) : l = 1 := by
  obtain ⟨e, he⟩ := GlobalTheory.T.adelic_GL_norm_one_split E a ha
  obtain ⟨γ, m, rfl⟩ := mem_latticeGL_iff.1 hl
  obtain ⟨⟨x, s⟩, ⟨hx, hs⟩, rfl⟩ := hg
  obtain ⟨⟨y, u⟩, ⟨hy, hu⟩, hyu⟩ := h
  dsimp only at hx hs hy hu hyu
  have hγ : ratGL E a γ ∈ normOneGL E a := rationalGL_le_normOneGL ⟨γ, rfl⟩
  have key : e (y, u) = e (⟨ratGL E a γ, hγ⟩ * x, (m : ℝ) + s) := by
    rw [he, he, hyu, splitCentre_add, ← splitCentre_intCast]
    exact (splitCentre_mul_mul_swap (m : ℝ) s (ratGL E a γ) (x : GA E a)).symm
  obtain ⟨h1, h2⟩ := Prod.mk.inj (e.injective key)
  have hm : m = 0 := by
    have h3 : (m : ℝ) < 1 := by linarith [hs.1, hu.2]
    have h4 : (-1 : ℝ) < m := by linarith [hs.2, hu.1]
    have h5 : m < 1 := by exact_mod_cast h3
    have h6 : -1 < m := by exact_mod_cast h4
    omega
  subst hm
  let δ : rationalGLOne E a := ⟨⟨ratGL E a γ, hγ⟩, ⟨γ, rfl⟩⟩
  have h7 : δ = 1 := (RightCosetSpace.existsUnique_smul_mem_fundamentalDomain (rationalGLOne E a) x).unique
    (show δ • x ∈ _ from by
      change ((⟨ratGL E a γ, hγ⟩ : normOneGL E a) * x) ∈ _
      rw [← h1]
      exact hy) (by simpa using hx)
  have h8 : ratGL E a γ = 1 := congrArg (fun d : rationalGLOne E a => ((d : normOneGL E a) : GA E a)) h7
  rw [h8, zpow_zero, mul_one]

theorem measurableSet_splitFd (ha : 0 < a) : MeasurableSet (splitFd E a) := by
  obtain ⟨e, he⟩ := GlobalTheory.T.adelic_GL_norm_one_split E a ha
  have h : (fun p : normOneGL E a × ℝ => splitCentre E a p.2 * (p.1 : GA E a)) = e :=
    funext fun p => (he p.1 p.2).symm
  rw [splitFd, h]
  exact e.isClosedEmbedding.measurableEmbedding.measurableSet_image.2
    ((RightCosetSpace.measurableSet_fundamentalDomain _).prod measurableSet_Ico)

theorem isFundamentalDomain_splitFd : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 0 < a →
    ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure], IsFundamentalDomain (latticeGL E a)
      ((fun p : normOneGL E a × ℝ => splitCentre E a p.2 * (p.1 : GA E a)) ''
        (RightCosetSpace.fundamentalDomain (rationalGLOne E a) ×ˢ Set.Ico (0 : ℝ) 1)) μ := by
  intro E _ _ _ a ha μ _
  refine IsFundamentalDomain.mk' (measurableSet_splitFd ha).nullMeasurableSet fun g => ?_
  obtain ⟨l, hl⟩ := exists_lattice_smul_mem_splitFd ha g
  refine ⟨l, hl, fun l' hl' => ?_⟩
  have h1 : ((l' : GA E a) * (l : GA E a)⁻¹) * ((l : GA E a) * g) ∈ splitFd E a := by
    have e0 : (l' : GA E a) * (l : GA E a)⁻¹ * ((l : GA E a) * g) = (l' : GA E a) * g := by group
    rw [e0]
    exact hl'
  have h2 := eq_one_of_mul_mem_splitFd ha (mul_mem l'.2 (inv_mem l.2)) hl h1
  exact Subtype.ext (mul_inv_eq_one.1 h2)

end GlobalTheory.CompanionTheory.CuspTransfer
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GoodSetCompactLinearlyIndependent
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WhitFree.AvgInf.Topo

open GlobalTheory.CompanionTheory.WhitFree.AvgInf

variable {K W : Type} [CommRing K] [TopologicalSpace K] [Fintype W]

lemma cont_coord (κ : K ≃+* (W → ℂ)) (hκ : IsHomeomorph κ) {n M : ℕ} (b : Fin n) (i : Fin M) (w : W) :
    Continuous fun X : Fin n → Fin M → K => κ (X b i) w :=
  (continuous_apply w).comp (hκ.continuous.comp ((continuous_apply i).comp (continuous_apply b)))

lemma isOpen_nearK (κ : K ≃+* (W → ℂ)) (hκ : IsHomeomorph κ) {n M : ℕ} (w : W) (s : Fin n → ℂ) (ε : ℝ) :
    IsOpen (nearK (M := M) κ w s ε) := by
  have : nearK (M := M) κ w s ε = ⋂ i, {X | ‖∑ b, s b * κ (X b i) w‖ < ε} := by
    ext X; simp [nearK]
  rw [this]
  refine isOpen_iInter_of_finite fun i => ?_
  refine isOpen_lt ?_ continuous_const
  refine Continuous.norm ?_
  refine continuous_finset_sum _ fun b _ => ?_
  exact continuous_const.mul (cont_coord κ hκ b i w)

lemma isCompact_boxK (κ : K ≃+* (W → ℂ)) (hκ : IsHomeomorph κ) {n M : ℕ} (r : Fin n → W → ℝ) :
    IsCompact (boxK (M := M) κ r) := by
  let e : K ≃ₜ (W → ℂ) := hκ.homeomorph κ
  let Φ : (Fin n → Fin M → K) ≃ₜ (Fin n → Fin M → W → ℂ) :=
    Homeomorph.piCongrRight fun _ => Homeomorph.piCongrRight fun _ => e
  have hB : IsCompact (Set.univ.pi fun a : Fin n => Set.univ.pi fun _ : Fin M =>
      Set.univ.pi fun w : W => Metric.closedBall (0 : ℂ) (r a w)) :=
    isCompact_univ_pi fun a => isCompact_univ_pi fun _ => isCompact_univ_pi fun w =>
      isCompact_closedBall _ _
  have : boxK (M := M) κ r = Φ ⁻¹' (Set.univ.pi fun a : Fin n => Set.univ.pi fun _ : Fin M =>
      Set.univ.pi fun w : W => Metric.closedBall (0 : ℂ) (r a w)) := by
    ext X
    simp [boxK, Φ, e]
  rw [this]
  exact (Homeomorph.isCompact_preimage Φ).2 hB

lemma linIndep_iff (κ : K ≃+* (W → ℂ)) {n M : ℕ} (X : Fin n → Fin M → K) :
    LinearIndependent K X ↔ ∀ w, LinearIndependent ℂ (fun b i => κ (X b i) w) := by
  classical
  constructor
  · intro hX w
    rw [Fintype.linearIndependent_iff] at hX ⊢
    intro t ht b
    have key := hX (fun b => κ.symm (Pi.single w (t b))) (by
      funext i
      apply κ.injective
      funext w'
      have := congrFun ht i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul,
        RingEquiv.apply_symm_apply, Pi.zero_apply, map_zero, Finset.sum_apply, Pi.mul_apply]
      by_cases h : w' = w
      · subst h; simpa using this
      · simp [Pi.single_apply, h])
    have := congrFun (congrArg κ (key b)) w
    simpa using this
  · intro h
    rw [Fintype.linearIndependent_iff]
    intro c hc b
    apply κ.injective
    funext w
    have hw := h w
    rw [Fintype.linearIndependent_iff] at hw
    have := hw (fun b => κ (c b) w) (by
      funext i
      have := congrArg (fun y => κ y w) (congrFun hc i)
      simpa [Finset.sum_apply, map_sum, map_mul] using this) b
    simpa using this

lemma isOpen_linIndep (κ : K ≃+* (W → ℂ)) (hκ : IsHomeomorph κ) (n M : ℕ) :
    IsOpen {X : Fin n → Fin M → K | LinearIndependent K X} := by
  have : {X : Fin n → Fin M → K | LinearIndependent K X} =
      ⋂ w, (fun X : Fin n → Fin M → K => fun b i => κ (X b i) w) ⁻¹'
        {Y : Fin n → Fin M → ℂ | LinearIndependent ℂ Y} := by
    ext X; simp [linIndep_iff κ X]
  rw [this]
  refine isOpen_iInter_of_finite fun w => ?_
  refine isOpen_setOfPred_linearIndependent.preimage ?_
  exact continuous_pi fun b => continuous_pi fun i => cont_coord κ hκ b i w

end GlobalTheory.CompanionTheory.WhitFree.AvgInf.Topo

namespace GlobalTheory.CompanionTheory.WhitFree.AvgInf.Topo

open GlobalTheory.CompanionTheory.WhitFree.AvgInf

variable {K W : Type} [CommRing K] [TopologicalSpace K] [Fintype W]

lemma goodK_subset (κ : K ≃+* (W → ℂ)) {n M : ℕ} (R ε : ℝ) (hε : 0 < ε) :
    goodK (n := n) (M := M) κ R ε ⊆ {X : Fin n → Fin M → K | LinearIndependent K X} := by
  intro X hX
  rcases hX with ⟨-, hX⟩
  show LinearIndependent K X
  rw [Fintype.linearIndependent_iff]
  intro c hc b0
  by_contra h0
  have hk : κ (c b0) ≠ 0 := by
    intro h; exact h0 (κ.injective (by simpa using h))
  obtain ⟨w, hw⟩ := Function.ne_iff.1 hk
  haveI : Nonempty (Fin n) := ⟨b0⟩
  obtain ⟨a, ha⟩ := Finite.exists_max fun b => ‖κ (c b) w‖
  have hca : κ (c a) w ≠ 0 := by
    intro h
    have := ha b0
    rw [h, norm_zero] at this
    exact hw (norm_le_zero_iff.1 this)
  have hsum : ∀ i, ∑ b, κ (c b) w * κ (X b i) w = 0 := by
    intro i
    have := congrArg (fun y => κ y w) (congrFun hc i)
    simpa [Finset.sum_apply, map_sum, map_mul] using this
  apply hX
  simp only [Set.mem_iUnion]
  refine ⟨w, a, fun b => κ (c b) w / κ (c a) w, ⟨div_self hca, fun b => ?_⟩, ?_⟩
  · rw [norm_div]
    exact div_le_one_of_le₀ (ha b) (norm_nonneg _)
  · intro i
    have : ∑ b, κ (c b) w / κ (c a) w * κ (X b i) w = (κ (c a) w)⁻¹ * ∑ b, κ (c b) w * κ (X b i) w := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      ring
    rw [this, hsum i, mul_zero, norm_zero]
    exact hε

theorem boxK_goodK_topology : ∀ (K W : Type) [CommRing K] [TopologicalSpace K] [Fintype W] (κ : K ≃+* (W → ℂ)), IsHomeomorph κ → ∀ n M : ℕ, (∀ r : Fin n → W → ℝ, IsCompact (GlobalTheory.CompanionTheory.WhitFree.AvgInf.boxK (M := M) κ r)) ∧ IsOpen {X : Fin n → Fin M → K | LinearIndependent K X} ∧ ∀ R ε : ℝ, 0 < ε → IsCompact (GlobalTheory.CompanionTheory.WhitFree.AvgInf.goodK (n := n) (M := M) κ R ε) ∧ GlobalTheory.CompanionTheory.WhitFree.AvgInf.goodK (n := n) (M := M) κ R ε ⊆ {X : Fin n → Fin M → K | LinearIndependent K X} := by
  intro K W _ _ _ κ hκ n M
  refine ⟨fun r => isCompact_boxK κ hκ r, isOpen_linIndep κ hκ n M, fun R ε hε => ⟨?_, goodK_subset κ R ε hε⟩⟩
  refine (isCompact_boxK κ hκ _).diff ?_
  exact isOpen_iUnion fun w => isOpen_iUnion fun a => isOpen_iUnion fun s => isOpen_iUnion fun _ =>
    isOpen_nearK κ hκ w s ε

end GlobalTheory.CompanionTheory.WhitFree.AvgInf.Topo
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasSumSquareCoefficientLocalSeriesStatement
section
open Ad3 Ad3.S
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_square_coefficient_local_series : E2a → E2b → ∀ (k N : ℕ) (χ : DirichletCharacter ℂ N) (a : ℕ → ℂ), IsEig k N χ a → 1 ≤ k → ∀ p : ℕ, p.Prime → ∀ α β y s : ℂ, α ≠ 0 → β ≠ 0 → α + β = a p → α * β = χ p * (p : ℂ) ^ (k - 1) → ‖α / β‖ = 1 → ‖y‖ ≤ 1 → 0 < s.re → HasSum (fun j : ℕ => (χ p)⁻¹ ^ j * a (p ^ (2 * j)) * (y * (p : ℂ) ^ (-(s + k - 1))) ^ j) ((1 - (y * (p : ℂ) ^ (-s)) ^ 2) * ((1 - α / β * (y * (p : ℂ) ^ (-s)))⁻¹ * (1 - y * (p : ℂ) ^ (-s))⁻¹ * (1 - (α / β)⁻¹ * (y * (p : ℂ) ^ (-s)))⁻¹)) := by
  first | exact @GlobalTheory.CompanionTheory.LocalSeries.good_prime_local_series | exact GlobalTheory.CompanionTheory.LocalSeries.good_prime_local_series | (intros; apply GlobalTheory.CompanionTheory.LocalSeries.good_prime_local_series <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeCharacterEtaCondition
section
open PositivityTheory.Rg.Rsw

namespace GlobalTheory.CompanionTheory.HeckeEtaExist

theorem heckeEta : HeckeEta :=
  GlobalTheory.RawLift.exists_hecke_resEta

end GlobalTheory.CompanionTheory.HeckeEtaExist
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightEqOfFullIntersectionSystemStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_eq_of_full_intersection_system : GlobalTheory.CompanionTheory.MixZ.PtDict → GlobalTheory.CompanionTheory.MixZ.CodimOne → GlobalTheory.CompanionTheory.MixZ.ExistsRat → GlobalTheory.CompanionTheory.MixZ.CycleOfRat → GlobalTheory.CompanionTheory.MixZ.ArchIntEq → GlobalTheory.CompanionTheory.MixZ.VertEq → GlobalTheory.CompanionTheory.MixZ.PtLen → GlobalTheory.CompanionTheory.MixZ.CurveInt → ReciprocityTheory.ChartRestriction.G.AI.I2.RatRStatement → ∀ II : ReciprocityTheory.ChartRestriction.G.Geo.IntersectionSystem, ReciprocityTheory.ChartRestriction.G.Geo.IsFullIntersectionSystem II → GlobalTheory.CompanionTheory.MixZ.HeightEq II := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.heightEq_holds | exact GlobalTheory.CompanionTheory.MixZ.heightEq_holds | (intros; apply GlobalTheory.CompanionTheory.MixZ.heightEq_holds <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepTwistedBundleExistsStatement
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermRep_twisted_bundle_exists : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (M : HermLB (mpStr ℤ m n)) (c : Fin m) (t : ℤ), Nonempty (LBIso M.B (twB m n c t)) → ∃ A : Geo.HermLine (Bk n), IsHermRep M A ∧ A.a = Pi.single c.succ 1 + t • Pi.single 0 1 := by
  first | exact @GlobalTheory.CompanionTheory.MPDict.TwLine.exists_hermLine_of_twB | exact GlobalTheory.CompanionTheory.MPDict.TwLine.exists_hermLine_of_twB | (intros; apply GlobalTheory.CompanionTheory.MPDict.TwLine.exists_hermLine_of_twB <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianArchimedeanComplexCoordinatesStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch NumberField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_archimedean_complex_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (e : Ainf F ≃+* (InfinitePlace F → ℝ)) (τ : InfinitePlace F → (E →+* ℂ))
  (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)), IsCoord σ e τ Θ →
  ∀ n : ℕ, ∃ Ψ : HermR (Ainf F) σ n ≃+ (InfinitePlace F → hermC n),
    (∀ b w, ((Ψ b w : hermC n) : Matrix (Fin n) (Fin n) ℂ) = matC Θ (b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) w) ∧
    ∀ ν : Measure (HermR (Ainf F) σ n), ν.IsAddHaarMeasure →
      (ν.map Ψ).IsAddHaarMeasure ∧ ∀ G : (InfinitePlace F → hermC n) → ℂ, Integrable G (ν.map Ψ) → Integrable (fun b => G (Ψ b)) ν := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HermCoord.exists_hermEquiv | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HermCoord.exists_hermEquiv | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HermCoord.exists_hermEquiv <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianFiniteAdelesDenseRationalStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_finite_adeles_dense_rational : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (U : AddSubgroup (HermR (Af F) σ n)), IsOpen (U : Set (HermR (Af F) σ n)) →
    ∀ g : HermR (Af F) σ n, ∃ c : hermE σ n, g - hermIn (Af F) σ n c ∈ U := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.hermE_dense_finite | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.hermE_dense_finite | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.hermE_dense_finite <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianFormPolynomialIn
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField PositivityTheory.BCUSide.HermitianLocalForms

namespace GlobalTheory.CompanionTheory.FormRatio

theorem exists_eq_mul_aeval (K : Type) [Field K] (σ : K →+* K) (n : ℕ)
    (A H₀ H : Matrix (Fin n) (Fin n) K) (_hA : IsUnit A.det) (hs : A.charpoly.Separable)
    (hH₀ : H₀.det ≠ 0) (e₀ : cT σ A * H₀ * A = H₀) (e : cT σ A * H * A = H) :
    ∃ m : K[X], H = H₀ * aeval A m := by
  have hH₀' : IsUnit H₀.det := isUnit_iff_ne_zero.mpr hH₀
  have hB : IsUnit (cT σ A).det := by
    refine isUnit_iff_ne_zero.mpr fun h0 => hH₀ ?_
    have h1 := congrArg Matrix.det e₀
    rw [Matrix.det_mul, Matrix.det_mul, h0, zero_mul, zero_mul] at h1
    exact h1.symm
  have k1 : H * A = (cT σ A)⁻¹ * H := by
    calc H * A = ((cT σ A)⁻¹ * cT σ A) * H * A := by
          rw [Matrix.nonsing_inv_mul _ hB, one_mul]
      _ = (cT σ A)⁻¹ * (cT σ A * H * A) := by simp only [mul_assoc]
      _ = (cT σ A)⁻¹ * H := by rw [e]
  have k0 : H₀ * A = (cT σ A)⁻¹ * H₀ := by
    calc H₀ * A = ((cT σ A)⁻¹ * cT σ A) * H₀ * A := by
          rw [Matrix.nonsing_inv_mul _ hB, one_mul]
      _ = (cT σ A)⁻¹ * (cT σ A * H₀ * A) := by simp only [mul_assoc]
      _ = (cT σ A)⁻¹ * H₀ := by rw [e₀]
  have k2 : A * H₀⁻¹ = H₀⁻¹ * (cT σ A)⁻¹ := by
    calc A * H₀⁻¹ = H₀⁻¹ * (H₀ * A) * H₀⁻¹ := by
          rw [← mul_assoc H₀⁻¹ H₀ A, Matrix.nonsing_inv_mul _ hH₀', one_mul]
      _ = H₀⁻¹ * ((cT σ A)⁻¹ * H₀) * H₀⁻¹ := by rw [k0]
      _ = H₀⁻¹ * (cT σ A)⁻¹ * (H₀ * H₀⁻¹) := by simp only [mul_assoc]
      _ = H₀⁻¹ * (cT σ A)⁻¹ := by rw [Matrix.mul_nonsing_inv _ hH₀', mul_one]
  have hc : Commute A (H₀⁻¹ * H) := by
    show A * (H₀⁻¹ * H) = H₀⁻¹ * H * A
    calc A * (H₀⁻¹ * H) = A * H₀⁻¹ * H := (mul_assoc _ _ _).symm
      _ = H₀⁻¹ * (cT σ A)⁻¹ * H := by rw [k2]
      _ = H₀⁻¹ * (H * A) := by rw [k1, mul_assoc]
      _ = H₀⁻¹ * H * A := (mul_assoc _ _ _).symm
  obtain ⟨m, hm⟩ := ClsFin.exists_aeval_of_comm A (H₀⁻¹ * H) hs hc
  refine ⟨m, ?_⟩
  rw [← hm, ← mul_assoc, Matrix.mul_nonsing_inv _ hH₀', one_mul]

end GlobalTheory.CompanionTheory.FormRatio
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HolomorphicLiftGivesHolomorphicSectionStatement
section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_lift_gives_holomorphic_section : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) (i : X ⟶ MP ℤ m n) [IsClosedImmersion i] (D : ℕ)
    (O : Set (Fin D → ℂ)) (γ : (Fin D → ℂ) → (Σ k, Bk n k) → ℂ) (s : (Fin D → ℂ) → GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀),
    IsOpen O → DifferentiableOn ℂ γ O → (∀ v ∈ O, IsUnder (PtsOver.map i rfl _ (s v)) (γ v)) →
    ContinuousOn s O ∧ ∀ (W : X.Opens) (f : Γ(X, W)),
      DifferentiableOn ℂ (ev (i ≫ mpStr ℤ m n) σ₀ W f ∘ s) (O ∩ s ⁻¹' ptsIn (i ≫ mpStr ℤ m n) σ₀ W) := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.Holo.holo | exact GlobalTheory.CompanionTheory.MixZ.Holo.holo | (intros; apply GlobalTheory.CompanionTheory.MixZ.Holo.holo <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InfiniteVectorMeasureIsAddHaarStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows PositivityTheory.AdelicQuotientData GroundTheory.Automorphic.FourierWhittaker GlobalTheory.CompanionTheory.CutOff
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infinite_vector_measure_isAddHaar : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (k : ℕ), (nuInf E k).IsAddHaarMeasure := by
  first | exact @GlobalTheory.CompanionTheory.CutOff.nuInf_isAddHaarMeasure | exact GlobalTheory.CompanionTheory.CutOff.nuInf_isAddHaarMeasure | (intros; apply GlobalTheory.CompanionTheory.CutOff.nuInf_isAddHaarMeasure <;> assumption)
end

