import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0534
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0591
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0604
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0572
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0595
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1369
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1414
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetGramRatOneNeZero
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLemmas.ToComplBijective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0596
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfNonNil
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0597
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinCoefficientBlockUnfolding
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisUnfold

namespace Core

variable {D : D7}

theorem continuous_trA_AE : Continuous (trA (D := D)) := by
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  exact IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF D.host.F) (AE D))

theorem continuous_halfTr_AE : Continuous (halfTr (D := D)) := by
  unfold halfTr
  exact continuous_const.mul continuous_trA_AE

theorem continuous_inner_pair (V : HSp D) {n : ℕ} {X : Type*} [TopologicalSpace X] {u v : X → Mx D V.rank n}
    (hu : Continuous u) (hv : Continuous v) : Continuous fun x => inner V (u x) (v x) := by
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  unfold StdUnn.inner
  exact (continuous_adj.comp hu).matrix_mul (continuous_const.matrix_mul hv)

theorem continuous_colJoin_left {X : Type*} [TopologicalSpace X] {m r s : ℕ} {u : X → Mx D m r} (hu : Continuous u)
    (v : Mx D m s) : Continuous fun x => colJoin (u x) v := by
  refine continuous_matrix fun i k => ?_
  refine Fin.addCases (fun j => ?_) (fun j => ?_) k
  · simp only [colJoin_castAdd]
    exact hu.matrix_elem i j
  · simp only [colJoin_natAdd]
    exact continuous_const

theorem continuous_quad (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (V : HSp D) {r : ℕ}
    (b : Matrix (Fin r) (Fin r) D.host.E) :
    Continuous fun t : Mx D V.rank r =>
      ψ (halfTr (Matrix.trace (HMul.hMul (rat b) (inner V t t) : Mx D r r))) := by
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  exact hψ.1.comp (continuous_halfTr_AE.comp
    (continuous_const.matrix_mul (continuous_inner_pair V continuous_id continuous_id)).matrix_trace)

theorem continuous_lin (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (V : HSp D) {s : ℕ}
    (x : Mx D V.rank s) :
    Continuous fun y : Mx D V.rank s => ψ (trA (Matrix.trace (inner V x y))) := by
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  exact hψ.1.comp (continuous_trA_AE.comp
    (continuous_inner_pair V continuous_const continuous_id).matrix_trace)

theorem enorm_char (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (x : AF D.host.F) : ‖ψ x‖ₑ = 1 := by
  rw [← ofReal_norm_eq_enorm, hψ.2.1, ENNReal.ofReal_one]

theorem join_mul_eq {m r s : ℕ} (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E)
    (p : Matrix (Fin m) (Fin r) D.host.E) (q : Matrix (Fin m) (Fin s) D.host.E) (y : Mx D m r) :
    HMul.hMul (colJoin (rat p - y) (rat q)) (rat a) =
      rat (colJoin p q * a) + -(HMul.hMul (colJoin y (0 : Mx D m s)) (rat a) : Mx D m (r + s)) := by
  have h : colJoin (rat p - y) (rat q) = colJoin (rat p) (rat q) - colJoin y (0 : Mx D m s) := by
    rw [← colJoin_sub, sub_zero]
  rw [h, Matrix.sub_mul, rat_mul, rat_colJoin, sub_eq_add_neg]

theorem join_mul_injective {m r s : ℕ} {a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E} (ha : IsUnit a.det) :
    Function.Injective fun pq : Matrix (Fin m) (Fin r) D.host.E × Matrix (Fin m) (Fin s) D.host.E =>
      colJoin pq.1 pq.2 * a := by
  rintro ⟨p, q⟩ ⟨p', q'⟩ h
  have h' : colJoin p q = colJoin p' q' := by
    have := congrArg (· * a⁻¹) h
    simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv a ha] using this
  obtain ⟨h1, h2⟩ := colJoin_injective h'
  rw [h1, h2]

theorem tsum_join_le {m r s : ℕ} {a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E} (ha : IsUnit a.det)
    {Φ : Mx D m (r + s) → ℂ} {B : ℝ≥0}
    (hB : ∀ w, ∑' ξ : Matrix (Fin m) (Fin (r + s)) D.host.E, ‖Φ (rat ξ + w)‖ₑ ≤ B) (y : Mx D m r) :
    ∑' pq : Matrix (Fin m) (Fin r) D.host.E × Matrix (Fin m) (Fin s) D.host.E,
      ‖Φ (HMul.hMul (colJoin (rat pq.1 - y) (rat pq.2)) (rat a))‖ₑ ≤ B := by
  set w : Mx D m (r + s) := -(HMul.hMul (colJoin y (0 : Mx D m s)) (rat a) : Mx D m (r + s)) with hw
  calc ∑' pq : Matrix (Fin m) (Fin r) D.host.E × Matrix (Fin m) (Fin s) D.host.E,
        ‖Φ (HMul.hMul (colJoin (rat pq.1 - y) (rat pq.2)) (rat a))‖ₑ
      = ∑' pq : Matrix (Fin m) (Fin r) D.host.E × Matrix (Fin m) (Fin s) D.host.E,
          (fun ξ : Matrix (Fin m) (Fin (r + s)) D.host.E => ‖Φ (rat ξ + w)‖ₑ) (colJoin pq.1 pq.2 * a) := by
        refine tsum_congr fun pq => ?_
        simp only [join_mul_eq, hw]
    _ ≤ ∑' ξ : Matrix (Fin m) (Fin (r + s)) D.host.E, ‖Φ (rat ξ + w)‖ₑ :=
        ENNReal.tsum_comp_le_tsum_of_injective (join_mul_injective ha) _
    _ ≤ B := hB w

theorem countable_mat (D : D7) (m n : ℕ) : Countable (Matrix (Fin m) (Fin n) D.host.E) := by
  haveI : Countable D.host.E := (Module.finBasis ℚ D.host.E).equivFun.injective.countable
  exact inferInstanceAs (Countable (Fin m → Fin n → D.host.E))

theorem enorm_cellTerm (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (V : HSp D) {r s : ℕ}
    (b : Matrix (Fin r) (Fin r) D.host.E) (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E)
    (Φ : Mx D V.rank (r + s) → ℂ) (p : Matrix (Fin V.rank) (Fin r) D.host.E)
    (q : Matrix (Fin V.rank) (Fin s) D.host.E) (y₁ : Mx D V.rank r) (y₂ : Mx D V.rank s) :
    ‖cellTerm ψ V b a Φ p q y₁ y₂‖ₑ = ‖Φ (HMul.hMul (colJoin (rat p - y₁) (rat q)) (rat a))‖ₑ := by
  simp only [cellTerm, enorm_mul, enorm_char ψ hψ, one_mul]

def cellRest (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) {r s : ℕ} (b : Matrix (Fin r) (Fin r) D.host.E)
    (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E) (Φ : Mx D V.rank (r + s) → ℂ)
    (p : Matrix (Fin V.rank) (Fin r) D.host.E) (q : Matrix (Fin V.rank) (Fin s) D.host.E)
    (y₁ : Mx D V.rank r) : ℂ :=
  ψ (halfTr (Matrix.trace (HMul.hMul (rat b) (inner V (y₁ - rat p) (y₁ - rat p)) : Mx D r r))) *
    Φ (HMul.hMul (colJoin (rat p - y₁) (rat q)) (rat a))

theorem continuous_cellRest (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (V : HSp D) {r s : ℕ}
    (b : Matrix (Fin r) (Fin r) D.host.E) (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E)
    {Φ : Mx D V.rank (r + s) → ℂ} (hΦ : Continuous Φ) (p : Matrix (Fin V.rank) (Fin r) D.host.E)
    (q : Matrix (Fin V.rank) (Fin s) D.host.E) : Continuous (cellRest ψ V b a Φ p q) := by
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  obtain ⟨i1, -⟩ := lattice_Mx D V.rank r
  haveI : ContinuousSub (Mx D V.rank r) := IsTopologicalAddGroup.to_continuousSub
  have h1 : Continuous fun y₁ : Mx D V.rank r => y₁ - rat p := continuous_id.sub continuous_const
  have h2 : Continuous fun y₁ : Mx D V.rank r => rat p - y₁ :=
    (continuous_const (y := rat p)).sub continuous_id
  exact ((continuous_quad ψ hψ V b).comp h1).mul
    (hΦ.comp ((continuous_colJoin_left h2 _).matrix_mul continuous_const))

def cellZero (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) {r s : ℕ} (b : Matrix (Fin r) (Fin r) D.host.E)
    (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E) (Φ : Mx D V.rank (r + s) → ℂ) (t : Mx D V.rank r) : ℂ :=
  ψ (halfTr (Matrix.trace (HMul.hMul (rat b) (inner V t t) : Mx D r r))) *
    Φ (HMul.hMul (colJoin (-t) (0 : Mx D V.rank s)) (rat a))

theorem cellRest_zero (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) {r s : ℕ} (b : Matrix (Fin r) (Fin r) D.host.E)
    (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E) (Φ : Mx D V.rank (r + s) → ℂ)
    (p : Matrix (Fin V.rank) (Fin r) D.host.E) (y : Mx D V.rank r) :
    cellRest ψ V b a Φ p 0 y = cellZero ψ V b a Φ (y - rat p) := by
  simp only [cellRest, cellZero, rat_zero, neg_sub]

theorem continuous_cellZero (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (V : HSp D) {r s : ℕ}
    (b : Matrix (Fin r) (Fin r) D.host.E) (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E)
    {Φ : Mx D V.rank (r + s) → ℂ} (hΦ : Continuous Φ) : Continuous (cellZero (s := s) ψ V b a Φ) := by
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  obtain ⟨i1, -⟩ := lattice_Mx D V.rank r
  exact (continuous_quad ψ hψ V b).mul
    (hΦ.comp ((continuous_colJoin_left continuous_neg _).matrix_mul continuous_const))

theorem tsum_cellZero_le (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (V : HSp D) {r s : ℕ}
    (b : Matrix (Fin r) (Fin r) D.host.E) {a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E} (ha : IsUnit a.det)
    {Φ : Mx D V.rank (r + s) → ℂ} {B : ℝ≥0}
    (hB : ∀ w, ∑' ξ : Matrix (Fin V.rank) (Fin (r + s)) D.host.E, ‖Φ (rat ξ + w)‖ₑ ≤ B) (y : Mx D V.rank r) :
    ∑' p : Matrix (Fin V.rank) (Fin r) D.host.E, ‖cellZero (s := s) ψ V b a Φ (y - rat p)‖ₑ ≤ B := by
  have hinj : Function.Injective fun p : Matrix (Fin V.rank) (Fin r) D.host.E =>
      ((p, 0) : Matrix (Fin V.rank) (Fin r) D.host.E × Matrix (Fin V.rank) (Fin s) D.host.E) :=
    fun _ _ h => congrArg Prod.fst h
  refine le_trans (le_of_eq (tsum_congr fun p => ?_))
    ((ENNReal.tsum_comp_le_tsum_of_injective hinj _).trans (tsum_join_le (s := s) ha hB y))
  simp only [cellZero, enorm_mul, enorm_char ψ hψ, one_mul, neg_sub, rat_zero]

end Core

theorem integral_cells_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (V : HSp D) (r s : ℕ)
    (μr : Measure (Mx D V.rank r)) (𝓕r : Set (Mx D V.rank r)) (μs : Measure (Mx D V.rank s)) (𝓕s : Set (Mx D V.rank s)),
    IsCovolOne (ratMx D V.rank r) μr 𝓕r → IsCovolOne (ratMx D V.rank s) μs 𝓕s →
    ∀ (b : Matrix (Fin r) (Fin r) D.host.E) (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E), IsUnit a.det →
    ∀ Φ : Mx D V.rank (r + s) → ℂ, Continuous Φ →
    ∀ B : ℝ≥0, (∀ w, ∑' ξ : Matrix (Fin V.rank) (Fin (r + s)) D.host.E, ‖Φ (rat ξ + w)‖ₑ ≤ B) →
      ∫ z in 𝓕r ×ˢ 𝓕s, ∑' pq : Matrix (Fin V.rank) (Fin r) D.host.E × Matrix (Fin V.rank) (Fin s) D.host.E,
          cellTerm ψ V b a Φ pq.1 pq.2 z.1 z.2 ∂(μr.prod μs) =
        ∫ t, ψ (halfTr (Matrix.trace (HMul.hMul (rat b) (inner V t t) : Mx D r r))) *
          Φ (HMul.hMul (colJoin (-t) (0 : Mx D V.rank s)) (rat a)) ∂μr := by
  intro D ψ hψ V r s μr 𝓕r μs 𝓕s hr hs b a ha Φ hΦ B hB
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D V.rank r
  obtain ⟨j1, j2, j3, j4, -, -⟩ := lattice_Mx D V.rank s
  haveI : BorelSpace (Mx D V.rank r) := ⟨rfl⟩
  haveI : BorelSpace (Mx D V.rank s) := ⟨rfl⟩
  haveI := hr.1
  haveI := hs.1
  haveI := Core.countable_mat D V.rank r
  haveI := Core.countable_mat D V.rank s
  haveI : IsFiniteMeasure (μr.restrict 𝓕r) := ⟨by simp [hr.2.2]⟩
  haveI : IsFiniteMeasure (μs.restrict 𝓕s) := ⟨by simp [hs.2.2]⟩
  rw [← Measure.prod_restrict]
  have hνu : ((μr.restrict 𝓕r).prod (μs.restrict 𝓕s)) Set.univ = 1 := by
    rw [← Set.univ_prod_univ, Measure.prod_prod]
    simp [hr.2.2, hs.2.2]
  have hform : ∀ (pq : Matrix (Fin V.rank) (Fin r) D.host.E × Matrix (Fin V.rank) (Fin s) D.host.E)
      (z : Mx D V.rank r × Mx D V.rank s), cellTerm ψ V b a Φ pq.1 pq.2 z.1 z.2 =
        Core.cellRest ψ V b a Φ pq.1 pq.2 z.1 * ψ (trA (Matrix.trace (inner V (rat pq.2) z.2))) :=
    fun pq z => mul_comm _ _
  have hcont : ∀ pq : Matrix (Fin V.rank) (Fin r) D.host.E × Matrix (Fin V.rank) (Fin s) D.host.E,
      Continuous fun z : Mx D V.rank r × Mx D V.rank s => cellTerm ψ V b a Φ pq.1 pq.2 z.1 z.2 := fun pq => by
    simp only [hform]
    exact ((Core.continuous_cellRest ψ hψ V b a hΦ pq.1 pq.2).comp continuous_fst).mul
      ((Core.continuous_lin ψ hψ V (rat pq.2)).comp continuous_snd)
  have hsum : ∑' pq : Matrix (Fin V.rank) (Fin r) D.host.E × Matrix (Fin V.rank) (Fin s) D.host.E,
      ∫⁻ z, ‖cellTerm ψ V b a Φ pq.1 pq.2 z.1 z.2‖ₑ ∂((μr.restrict 𝓕r).prod (μs.restrict 𝓕s)) ≠ ∞ := by
    rw [← lintegral_tsum fun pq => (hcont pq).enorm.measurable.aemeasurable]
    refine ne_top_of_le_ne_top ?_ (lintegral_mono (g := fun _ => (B : ℝ≥0∞)) fun z => ?_)
    · simp [hνu]
    · simp only [Core.enorm_cellTerm ψ hψ]
      exact Core.tsum_join_le ha hB z.1
  rw [integral_tsum (fun pq => (hcont pq).aestronglyMeasurable) hsum]
  have hterm : ∀ pq : Matrix (Fin V.rank) (Fin r) D.host.E × Matrix (Fin V.rank) (Fin s) D.host.E,
      ∫ z, cellTerm ψ V b a Φ pq.1 pq.2 z.1 z.2 ∂((μr.restrict 𝓕r).prod (μs.restrict 𝓕s)) =
        (∫ y in 𝓕r, Core.cellRest ψ V b a Φ pq.1 pq.2 y ∂μr) *
          ∫ y in 𝓕s, ψ (trA (Matrix.trace (inner V (rat pq.2) y))) ∂μs := fun pq => by
    simp only [hform]
    exact integral_prod_mul (Core.cellRest ψ V b a Φ pq.1 pq.2)
      (fun y => ψ (trA (Matrix.trace (inner V (rat pq.2) y))))
  simp only [hterm]
  have hinj : Function.Injective fun p : Matrix (Fin V.rank) (Fin r) D.host.E =>
      ((p, 0) : Matrix (Fin V.rank) (Fin r) D.host.E × Matrix (Fin V.rank) (Fin s) D.host.E) :=
    fun _ _ h => congrArg Prod.fst h
  rw [← hinj.tsum_eq]
  · obtain ⟨-, hu⟩ := GlobalTheory.T.periodization_integral_unfolding D V.rank r μr 𝓕r hr (Core.cellZero (s := s) ψ V b a Φ)
      (Core.continuous_cellZero ψ hψ V b a hΦ) B (Core.tsum_cellZero_le ψ hψ V b ha hB)
    refine Eq.trans (tsum_congr fun p => ?_) hu
    simp only [(GlobalTheory.T.character_integral_orthogonality D ψ hψ V s μs 𝓕s hs 0).1 rfl, mul_one, Core.cellRest_zero]
  · rintro ⟨p, q⟩ hne
    by_cases hq : q = 0
    · exact ⟨p, by rw [hq]⟩
    · exact absurd (by simp only [(GlobalTheory.T.character_integral_orthogonality D ψ hψ V s μs 𝓕s hs q).2 hq, mul_zero]) hne

end GlobalTheory.CompanionTheory.EisUnfold

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EpsteinSeriesAbsoluteConvergence
section
set_option maxSynthPendingDepth 1
set_option synthInstance.maxSize 1000

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GL2Classical (realEmb realPart Gamma0Level archLift)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical nonZeroDivisors

namespace GlobalTheory.CompanionTheory.EpsteinTensorBound

open Ad3.R GroundTheory.Automorphic.Adele2 IdeleGroup

theorem lrow_apply (z : Jd) (κ : G2) (j : Fin 2) :
    lrow z κ j = (z : 𝔸[ℚ]) * (κ : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]) 1 j := by
  simp [lrow, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem abs_realEquiv (x : InfiniteAdeleRing ℚ) :
    |RationalIdeles.realEquiv x| = ‖x default‖ := by
  rw [RationalIdeles.realEquiv_apply, ← Real.norm_eq_abs]
  exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
    (RationalIdeles.isReal_infinitePlace default)).norm_map_of_map_zero (map_zero _) _

theorem exists_half_le_row {κ : G2} (hκ : κ ∈ (maxCompact : Subgroup G2)) :
    ∃ j : Fin 2, 1 / 2 ≤ ‖((κ : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]) 1 j).1 default‖ := by
  have h := (GroundTheory.Automorphic.GL2Classical.realPart_orthogonal hκ).2.1
  have hE : ∀ j : Fin 2, ‖((κ : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]) 1 j).1 default‖ =
      |(realPart κ : Matrix (Fin 2) (Fin 2) ℝ) 1 j| := fun j ↦
    (abs_realEquiv _).symm
  by_contra hc
  push Not at hc
  have h0 := hc 0
  have h1 := hc 1
  rw [hE] at h0 h1
  have a0 := abs_lt.1 h0
  have a1 := abs_lt.1 h1
  nlinarith

theorem norm_le_two_mul_infPart (z : Jd) {κ : G2} (hκ : κ ∈ (maxCompact : Subgroup G2)) :
    ‖((toInfinite ℚ z : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ) default‖ ≤
      2 * ‖Adele2.infPart (lrow z κ)‖ := by
  obtain ⟨j, hj⟩ := exists_half_le_row hκ
  have h1 : ‖(lrow z κ j).1 default‖ ≤ ‖Adele2.infPart (lrow z κ)‖ :=
    (norm_le_norm_homeomorphMixedSpace _ _).trans (norm_le_pi_norm (Adele2.infPart (lrow z κ)) j)
  have h2 : (lrow z κ j).1 default = (z : 𝔸[ℚ]).1 default *
      ((κ : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]) 1 j).1 default := by
    rw [lrow_apply]; rfl
  rw [h2, norm_mul] at h1
  have h3 : ‖(z : 𝔸[ℚ]).1 default‖ * (1 / 2) ≤ ‖(z : 𝔸[ℚ]).1 default‖ *
      ‖((κ : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]) 1 j).1 default‖ :=
    mul_le_mul_of_nonneg_left hj (norm_nonneg _)
  change ‖(z : 𝔸[ℚ]).1 default‖ ≤ _
  linarith

theorem exists_norm_schwartz_lrow_le (φ : 𝓢(Fin 2 → mixedEmbedding.mixedSpace ℚ, ℂ)) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : Jd) (κ : G2), κ ∈ (maxCompact : Subgroup G2) →
      ‖φ (Adele2.infPart (lrow z κ))‖ ≤ C * ∏ w : InfinitePlace ℚ,
        ((1 + ‖((toInfinite ℚ z : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ) w‖) ^ k)⁻¹ := by
  set S := 2 ^ k * ((Finset.Iic (k, 0)).sup fun m ↦ SchwartzMap.seminorm ℝ m.1 m.2) φ with hS
  have hS0 : 0 ≤ S := by positivity
  refine ⟨2 ^ k * S, by positivity, fun z κ hκ ↦ ?_⟩
  set y := Adele2.infPart (lrow z κ)
  set a := ‖((toInfinite ℚ z : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ) default‖ with ha
  have h1 := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0)) le_rfl le_rfl φ y
  rw [norm_iteratedFDeriv_zero] at h1
  have h2 : a ≤ 2 * ‖y‖ := norm_le_two_mul_infPart z hκ
  have ha0 : 0 ≤ a := norm_nonneg _
  have h3 : (1 + a) ^ k ≤ 2 ^ k * (1 + ‖y‖) ^ k := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) k
  rw [Fintype.prod_unique, ← div_eq_mul_inv]
  have hpos : 0 < (1 + a) ^ k := by positivity
  change ‖φ y‖ ≤ 2 ^ k * S / (1 + a) ^ k
  rw [le_div_iff₀ hpos]
  calc ‖φ y‖ * (1 + a) ^ k ≤ ‖φ y‖ * (2 ^ k * (1 + ‖y‖) ^ k) :=
        mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
    _ = 2 ^ k * ((1 + ‖y‖) ^ k * ‖φ y‖) := by ring
    _ ≤ 2 ^ k * S := mul_le_mul_of_nonneg_left h1 (by positivity)

theorem mul_mem_idealFiniteAdeles {L : (FractionalIdeal (𝓞 ℚ)⁰ ℚ)ˣ} {x u : Af}
    (hx : x ∈ idealFiniteAdeles L) (hu : u ∈ integralFiniteAdeles (𝓞 ℚ) ℚ) :
    x * u ∈ idealFiniteAdeles L := by
  rw [mem_idealFiniteAdeles] at hx ⊢
  intro v
  have h1 : Valued.v (u v) ≤ 1 := hu v
  calc Valued.v ((x * u) v) = Valued.v (x v) * Valued.v (u v) := map_mul _ _ _
    _ ≤ _ * 1 := mul_le_mul' (hx v) h1
    _ = _ := mul_one _

theorem mem_ideal_of_row {L : (FractionalIdeal (𝓞 ℚ)⁰ ℚ)ˣ} (z : Jd) {κ : G2}
    (hκ : κ ∈ (maxCompact : Subgroup G2))
    (h : ∀ j, Adele2.finPart (lrow z κ) j ∈ idealFiniteAdeles L) :
    (z : 𝔸[ℚ]).2 ∈ idealFiniteAdeles L := by
  set P := (AdelicGLn.prodEquiv ℚ 2 κ).2 with hP
  obtain ⟨-, hQ⟩ := (AdelicGLn.mem_integralFiniteGL_iff ℚ 2).1
    (GroundTheory.Automorphic.GL2Classical.finitePart_mem_integralFiniteGL hκ)
  have hPQ : (P : Matrix (Fin 2) (Fin 2) Af) * ((P⁻¹ : GL (Fin 2) Af) : Matrix (Fin 2) (Fin 2) Af) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h11 := congrFun (congrFun hPQ 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq] at h11
  have hrow : ∀ j, Adele2.finPart (lrow z κ) j = (z : 𝔸[ℚ]).2 * (P : Matrix (Fin 2) (Fin 2) Af) 1 j := by
    intro j
    change (lrow z κ j).2 = _
    rw [lrow_apply]
    rfl
  have key : (z : 𝔸[ℚ]).2 =
      Adele2.finPart (lrow z κ) 0 * ((P⁻¹ : GL (Fin 2) Af) : Matrix (Fin 2) (Fin 2) Af) 0 1 +
      Adele2.finPart (lrow z κ) 1 * ((P⁻¹ : GL (Fin 2) Af) : Matrix (Fin 2) (Fin 2) Af) 1 1 := by
    rw [hrow, hrow]
    linear_combination (-(z : 𝔸[ℚ]).2) * h11
  rw [key]
  exact add_mem (mul_mem_idealFiniteAdeles (h 0) (hQ 0 1)) (mul_mem_idealFiniteAdeles (h 1) (hQ 1 1))

theorem continuous_tensor (φ : 𝓢(Fin 2 → mixedEmbedding.mixedSpace ℚ, ℂ)) {g : (Fin 2 → Af) → ℂ}
    (hg : g ∈ finiteSchwartzBruhat2 ℚ) : Continuous (schwartzBruhatTensor2 φ g) := by
  have h1 : Continuous (Adele2.infPart (K := ℚ)) :=
    continuous_pi fun i ↦ (homeomorphMixedSpace ℚ).continuous.comp
      (continuous_fst.comp (continuous_apply i))
  have h2 : Continuous (Adele2.finPart (K := ℚ)) :=
    continuous_pi fun i ↦ continuous_snd.comp (continuous_apply i)
  exact (φ.continuous.comp h1).mul (hg.1.continuous.comp h2)

theorem continuous_of_mem {Φ : (Fin 2 → 𝔸[ℚ]) → ℂ} (hΦ : Φ ∈ schwartzBruhat2 ℚ) : Continuous Φ := by
  induction hΦ using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, g, hg, rfl⟩ := hG
    exact continuous_tensor φ hg
  | zero => exact continuous_const
  | add G H _ _ hG hH => exact hG.add hH
  | smul c G _ hG => exact hG.const_smul c

theorem exists_bound_tensor (φ : 𝓢(Fin 2 → mixedEmbedding.mixedSpace ℚ, ℂ)) {g : (Fin 2 → Af) → ℂ}
    (hg : g ∈ finiteSchwartzBruhat2 ℚ) (τ : ℝ) :
    ∃ C : ℝ, ∃ k : ℕ, ∃ L : (FractionalIdeal (𝓞 ℚ)⁰ ℚ)ˣ, 0 ≤ C ∧ 2 * τ + 2 < k ∧
      ∀ (z : Jd) (κ : G2), κ ∈ (maxCompact : Subgroup G2) →
        ‖schwartzBruhatTensor2 φ g (lrow z κ)‖ * md z ^ τ ≤
          C * (infiniteZetaBound τ k (toInfinite ℚ z) * finiteZetaBound L τ (toFinite ℚ z)) := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, 2 * τ + 2 < k := exists_nat_gt _
  obtain ⟨C₁, hC₁, hφ⟩ := exists_norm_schwartz_lrow_le φ k
  obtain ⟨M, hM⟩ := hg.1.continuous.bounded_above_of_compact_support hg.2
  have hcpt : IsCompact (tsupport g) := hg.2
  obtain ⟨L, hL⟩ := exists_subset_idealFiniteAdeles
    ((hcpt.image (continuous_apply (0 : Fin 2))).union (hcpt.image (continuous_apply (1 : Fin 2))))
  refine ⟨C₁ * max M 0, k, L, by positivity, hk, fun z κ hκ ↦ ?_⟩
  set a := toInfinite ℚ z
  set b := toFinite ℚ z
  have hinf : ‖φ (Adele2.infPart (lrow z κ))‖ *
      ∏ w, ‖(a : InfiniteAdeleRing ℚ) w‖ ^ ((w.mult : ℝ) * τ) ≤ C₁ * infiniteZetaBound τ k a := by
    calc ‖φ (Adele2.infPart (lrow z κ))‖ * ∏ w, ‖(a : InfiniteAdeleRing ℚ) w‖ ^ ((w.mult : ℝ) * τ)
        ≤ (C₁ * ∏ w, ((1 + ‖(a : InfiniteAdeleRing ℚ) w‖) ^ k)⁻¹) *
            ∏ w, ‖(a : InfiniteAdeleRing ℚ) w‖ ^ ((w.mult : ℝ) * τ) :=
          mul_le_mul_of_nonneg_right (hφ z κ hκ) (Finset.prod_nonneg fun w _ ↦ by positivity)
      _ = C₁ * infiniteZetaBound τ k a := by
          rw [mul_assoc, ← Finset.prod_mul_distrib, infiniteZetaBound]
          congr 1
          refine Finset.prod_congr rfl fun w _ ↦ ?_
          rw [div_eq_mul_inv, mul_comm]
  have hI := infiniteZetaBound_nonneg τ k a
  unfold schwartzBruhatTensor2
  by_cases hb : (b : Af) ∈ idealFiniteAdeles L
  · have hfz : finiteZetaBound L τ b = finiteModule (ofFinite b) ^ τ := by
      rw [finiteZetaBound, if_pos hb]
    rw [hfz, md, ideleModule_rpow_eq, norm_mul]
    have hgM : ‖g (Adele2.finPart (lrow z κ))‖ ≤ max M 0 := (hM _).trans (le_max_left _ _)
    have hfm : 0 ≤ finiteModule (ofFinite b) ^ τ := by
      have := finiteModule_pos (ofFinite b)
      positivity
    calc ‖φ (Adele2.infPart (lrow z κ))‖ * ‖g (Adele2.finPart (lrow z κ))‖ *
          ((∏ w, ‖(a : InfiniteAdeleRing ℚ) w‖ ^ ((w.mult : ℝ) * τ)) *
            finiteModule (ofFinite b) ^ τ)
        = (‖φ (Adele2.infPart (lrow z κ))‖ *
            ∏ w, ‖(a : InfiniteAdeleRing ℚ) w‖ ^ ((w.mult : ℝ) * τ)) *
              ‖g (Adele2.finPart (lrow z κ))‖ * finiteModule (ofFinite b) ^ τ := by ring
      _ ≤ (C₁ * infiniteZetaBound τ k a) * max M 0 * finiteModule (ofFinite b) ^ τ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul hinf hgM (norm_nonneg _) (mul_nonneg hC₁ hI)) hfm
      _ = C₁ * max M 0 * (infiniteZetaBound τ k a * finiteModule (ofFinite b) ^ τ) := by ring
  · have hg0 : g (Adele2.finPart (lrow z κ)) = 0 := by
      by_contra h
      have hs := subset_tsupport g h
      refine hb (mem_ideal_of_row z hκ fun j ↦ ?_)
      fin_cases j
      · exact hL (Or.inl ⟨_, hs, rfl⟩)
      · exact hL (Or.inr ⟨_, hs, rfl⟩)
    rw [hg0, mul_zero, norm_zero, zero_mul]
    exact mul_nonneg (by positivity) (mul_nonneg hI (finiteZetaBound_nonneg _ _ _))

theorem exists_dominant {Φ : (Fin 2 → 𝔸[ℚ]) → ℂ} (hΦ : Φ ∈ schwartzBruhat2 ℚ) {τ : ℝ} (hτ : 1 < τ) :
    ∃ B : Jd → ℝ, Integrable B (ideleMeasure ℚ) ∧ ∀ (z : Jd) (κ : G2),
      κ ∈ (maxCompact : Subgroup G2) → ‖Φ (lrow z κ)‖ * md z ^ τ ≤ B z := by
  have hpow : ∀ z : Jd, 0 ≤ md z ^ τ := fun z ↦ Real.rpow_nonneg (ideleModule ℚ z).2.le τ
  induction hΦ using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, g, hg, rfl⟩ := hG
    obtain ⟨C, k, L, -, hk, hb⟩ := exists_bound_tensor φ hg τ
    exact ⟨_, (integrable_zetaBound hτ hk L).const_mul C, hb⟩
  | zero =>
    refine ⟨0, integrable_zero _ _ _, fun z κ _ ↦ ?_⟩
    simp
  | add G H _ _ hG hH =>
    obtain ⟨B₁, h₁, b₁⟩ := hG
    obtain ⟨B₂, h₂, b₂⟩ := hH
    refine ⟨B₁ + B₂, h₁.add h₂, fun z κ hκ ↦ ?_⟩
    calc ‖(G + H) (lrow z κ)‖ * md z ^ τ ≤ (‖G (lrow z κ)‖ + ‖H (lrow z κ)‖) * md z ^ τ :=
          mul_le_mul_of_nonneg_right (norm_add_le _ _) (hpow z)
      _ ≤ B₁ z + B₂ z := by
          rw [add_mul]
          exact add_le_add (b₁ z κ hκ) (b₂ z κ hκ)
  | smul c G _ hG =>
    obtain ⟨B, h, b⟩ := hG
    refine ⟨fun z ↦ ‖c‖ * B z, h.const_mul _, fun z κ hκ ↦ ?_⟩
    simp only [Pi.smul_apply, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (b z κ hκ) (norm_nonneg _)

theorem g3a : Ad3.R.G3a := by
  intro Φ hΦ
  refine ⟨continuous_of_mem hΦ, fun τ hτ ↦ ?_⟩
  obtain ⟨B, hB, hle⟩ := exists_dominant hΦ hτ
  refine ⟨∫⁻ z, ENNReal.ofReal (B z) ∂ideleMeasure ℚ, hB.lintegral_lt_top, fun κ ↦
    lintegral_mono fun z ↦ ?_⟩
  rw [← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (hle z κ.1 κ.2)

end GlobalTheory.CompanionTheory.EpsteinTensorBound
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EventuallyMeasurableSetPrimV
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimMeas

theorem eventually_measurableSet_primV : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, MeasurableSet (primV σ J b v) := by
  intro F E _ _ _ _ _ σ hσ M J hJ d b
  exact Filter.Eventually.of_forall fun v => measurableSet_primV F E σ hσ M J hJ d b v

end GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimMeas
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPolynomialChineseRemainderStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField PositivityTheory.BCUSide.HermitianLocalForms
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polynomial_chinese_remainder : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ g : ∀ (r : ℕ) (Q : SelfRecip E r), Fld Q, ∃ m : E[X], ∀ (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly → (AdjoinRoot.mk Q.1 m : Fld Q) = g r Q := by
  first | exact @GlobalTheory.CompanionTheory.EllCRT.main | exact GlobalTheory.CompanionTheory.EllCRT.main | (intros; apply GlobalTheory.CompanionTheory.EllCRT.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLengthOfProductsStatement
section
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_length_of_products : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ι : Type) [Fintype ι] [DecidableEq ι], ProdFinLen F ι := by
  first | exact @GlobalTheory.CompanionTheory.ProdLen.prodFinLen | exact GlobalTheory.CompanionTheory.ProdLen.prodFinLen | (intros; apply GlobalTheory.CompanionTheory.ProdLen.prodFinLen <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeCharacterEtaConditionStatement
section
open PositivityTheory.Rg.Rsw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_character_eta_condition : HeckeEta := by
  first | exact @GlobalTheory.CompanionTheory.HeckeEtaExist.heckeEta | exact GlobalTheory.CompanionTheory.HeckeEtaExist.heckeEta | (intros; apply GlobalTheory.CompanionTheory.HeckeEtaExist.heckeEta <;> assumption)
end

