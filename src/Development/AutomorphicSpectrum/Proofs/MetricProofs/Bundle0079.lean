import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0077
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0042
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0075
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0033
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0071
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Bundle0001
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0032
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0072

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockMinorSumFrameIdentity
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph.FrameExt

section Minors

variable {R : Type} [CommRing R] {S : Type} [CommRing S] {N : ℕ}

theorem minorIJ_map (ρ : R →+* S) (T : Matrix (Fin N) (Fin N) R) (I J : Finset (Fin N)) :
    minorIJ (T.map ρ) I J = ρ (minorIJ T I J) := by
  unfold minorIJ
  split_ifs with e
  · rw [RingHom.map_det]
    rfl
  · simp

theorem detFac_map (ρ : R →+* S) (j : ℕ) (i : Fin N) (T : Matrix (Fin N) (Fin N) R) :
    detFac j i (T.map ρ) = ρ (detFac j i T) := by
  unfold detFac
  simp only [minorIJ_map, map_mul]
  split_ifs <;> simp

def moveMat (R : Type) [CommRing R] (I C : Finset (Fin N)) (e : I.card = C.card) : Matrix (Fin N) (Fin N) R :=
  fun a b => ∑ t : Fin C.card, if a = I.orderEmbOfFin e t ∧ b = C.orderEmbOfFin rfl t then 1 else 0

theorem moveMat_apply (I C : Finset (Fin N)) (e : I.card = C.card) (s t : Fin C.card) :
    moveMat R I C e (I.orderEmbOfFin e s) (C.orderEmbOfFin rfl t) = if s = t then 1 else 0 := by
  unfold moveMat
  rw [Finset.sum_eq_single t]
  · simp
  · intro t' _ h
    rw [if_neg]
    rintro ⟨-, h2⟩
    exact h ((C.orderEmbOfFin rfl).injective h2).symm
  · simp

theorem moveMat_eq_zero (I C : Finset (Fin N)) (e : I.card = C.card) {a b : Fin N}
    (h : ¬ (a ∈ I ∧ b ∈ C)) : moveMat R I C e a b = 0 := by
  unfold moveMat
  refine Finset.sum_eq_zero fun t _ => if_neg ?_
  rintro ⟨rfl, rfl⟩
  exact h ⟨Finset.orderEmbOfFin_mem _ _ _, Finset.orderEmbOfFin_mem _ _ _⟩

theorem moveMat_blockDiag (j : ℕ) (I C : Finset (Fin N)) (e : I.card = C.card)
    (h : ∀ a ∈ I, ∀ b ∈ C, ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)) : IsBlockDiag j (moveMat R I C e) :=
  fun a b hab => moveMat_eq_zero I C e fun hm => hab (h a hm.1 b hm.2)

theorem minorIJ_moveMat (I C I' : Finset (Fin N)) (e : I.card = C.card) :
    minorIJ (moveMat R I C e) I' C = if I' = I then 1 else 0 := by
  by_cases hI : I' = I
  · subst hI
    rw [if_pos rfl]
    unfold minorIJ
    rw [dif_pos e]
    have : (moveMat R I' C e).submatrix (I'.orderEmbOfFin e) (C.orderEmbOfFin rfl) = 1 := by
      ext s t
      rw [Matrix.submatrix_apply, moveMat_apply, Matrix.one_apply]
    rw [this, det_one]
  · rw [if_neg hI]
    unfold minorIJ
    split_ifs with e'
    · have hex : ∃ a ∈ I', a ∉ I := by
        by_contra hc
        push_neg at hc
        exact hI (Finset.eq_of_subset_of_card_le hc (by rw [e, e']))
      obtain ⟨a, ha, haI⟩ := hex
      have hr : a ∈ Set.range (I'.orderEmbOfFin e') := by
        rw [Finset.range_orderEmbOfFin]
        exact ha
      obtain ⟨s, rfl⟩ := hr
      refine det_eq_zero_of_row_eq_zero s fun t => ?_
      rw [Matrix.submatrix_apply]
      exact moveMat_eq_zero I C e fun hm => haI hm.1
    · rfl

theorem stepRows_same (j : ℕ) (hj : j ≤ N) (i : Fin N) {I : Finset (Fin N)} (hI : IsStepRows N j i I) :
    ∀ a ∈ I, ∀ b ∈ stepCols N j i, ((a : ℕ) < N - j ↔ (b : ℕ) < N - j) := by
  intro a ha b hb
  have hi := i.2
  have ha' := hI.2 ha
  simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at hb
  by_cases c : (i : ℕ) + 1 ≤ j
  · rw [if_pos c] at ha' hb
    simp only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and] at ha'
    omega
  · rw [if_neg c] at ha' hb
    simp only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and] at ha'
    omega

theorem stepCols_nonempty (j : ℕ) (hj : j ≤ N) (i : Fin N) (hp : IsProperStep N j i) :
    stepCols N j i ≠ ∅ := by
  have hi := i.2
  obtain ⟨h1, h2⟩ := hp
  by_cases c : (i : ℕ) + 1 ≤ j
  · refine Finset.Nonempty.ne_empty ⟨⟨N - j, by omega⟩, ?_⟩
    simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [if_pos c]
    omega
  · refine Finset.Nonempty.ne_empty ⟨⟨0, by omega⟩, ?_⟩
    simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [if_neg c]
    omega

theorem coeff_eq (j : ℕ) (hj : j ≤ N) (i : Fin N) (T : Matrix (Fin N) (Fin N) R) (c u : Finset (Fin N) → R) (D P : R)
    (H : ∀ h : Matrix (Fin N) (Fin N) R, IsBlockDiag j h →
      D * ∑ I, c I * minorIJ (T * h) I (stepCols N j i) = P * ∑ I, u I * minorIJ h I (stepCols N j i))
    (I₀ : Finset (Fin N)) (hI : IsStepRows N j i I₀) :
    D * ∑ I, c I * minorIJ T I I₀ = P * u I₀ := by
  have h1 := H (moveMat R I₀ (stepCols N j i) hI.1) (moveMat_blockDiag j _ _ _ (stepRows_same j hj i hI))
  have cb := (GlobalTheory.T.block_diagonal_minor_vanishing R N j i hj).1
  simp only [cb, minorIJ_moveMat, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1
  exact h1

theorem map_identity (j : ℕ) (hj : j ≤ N) (i : Fin N) (hC : stepCols N j i ≠ ∅) (T : Matrix (Fin N) (Fin N) R)
    (c u : Finset (Fin N) → R) (D P : R)
    (H : ∀ h : Matrix (Fin N) (Fin N) R, IsBlockDiag j h →
      D * ∑ I, c I * minorIJ (T * h) I (stepCols N j i) = P * ∑ I, u I * minorIJ h I (stepCols N j i))
    (ρ : R →+* S) (h : Matrix (Fin N) (Fin N) S) (hh : IsBlockDiag j h) :
    ρ D * ∑ I, ρ (c I) * minorIJ (T.map ρ * h) I (stepCols N j i) =
      ρ P * ∑ I, ρ (u I) * minorIJ h I (stepCols N j i) := by
  have cb := (GlobalTheory.T.block_diagonal_minor_vanishing S N j i hj).1
  have l : ρ D * ∑ I, ρ (c I) * minorIJ (T.map ρ * h) I (stepCols N j i) =
      ∑ I', ρ (D * ∑ I, c I * minorIJ T I I') * minorIJ h I' (stepCols N j i) := by
    simp only [cb, minorIJ_map, map_mul, map_sum, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have r : ρ P * ∑ I, ρ (u I) * minorIJ h I (stepCols N j i) =
      ∑ I', ρ (P * u I') * minorIJ h I' (stepCols N j i) := by
    simp only [map_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [l, r]
  refine Finset.sum_congr rfl fun I' _ => ?_
  by_cases hI : IsStepRows N j i I'
  · rw [coeff_eq j hj i T c u D P H I' hI]
  · rw [((GlobalTheory.T.block_diagonal_minor_vanishing S N j i hj).2.1 h I' hh hI).resolve_right hC, mul_zero, mul_zero]

end Minors

theorem frame_identity_map : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (S : Type) [CommRing S] (ρ : M.Ω →+* S) (F : FrameData ι Ψ N M.Ω M.blk), M.IsFrame F → ∀ (p : Ψ × Fin N) (k : K), M.blk p = some k → ∀ (m : ι k) (h : Matrix (Fin N) (Fin N) S), IsBlockDiag j h → detFac j p.2 ((F.T p.1).map ρ) * ∑ I, ρ (M.coef ⟨k, m⟩ I) * minorIJ ((F.T p.1).map ρ * h) I (stepCols N j p.2) = ρ (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b p k') * ∑ I, ρ (F.u ⟨k, m⟩ I) * minorIJ h I (stepCols N j p.2) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M S _ ρ F hF p k hp m h hh
  have hprop : IsProperStep N j p.2 := by
    by_contra hc
    rw [(M.blk_none p).2 hc] at hp
    exact absurd hp (by simp)
  rw [detFac_map]
  exact map_identity j M.j_le p.2 (stepCols_nonempty j M.j_le p.2 hprop) (F.T p.1) _ _ _ _
    (fun h' hh' => hF.2.1 p k hp m h' hh') ρ h hh

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph.FrameExt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.CompatibleChartProductProjectionTwisted
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

namespace GlobalTheory.CompanionTheory.Ar.PB.ChartSwap

theorem chart_swap_keep :
    ∀ (e n : ℕ) (X Z : Type) [TopologicalSpace X] [TopologicalSpace Z] (A : FinHolAtlas e X) (Ab : FinHolAtlas n Z) (pr : X → Z) (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (kb : Fin Ab.n) (σ : Fin n ↪ Fin e) (ψb : OpenPartialHomeomorph Z (Fin n → ℂ)), IsCompatChart A ψ → IsCompatChart Ab ψb → (∀ x' ∈ ψ.source, pr x' ∈ (Ab.chart kb).source ∧ ∀ i, Ab.chart kb (pr x') i = ψ x' (σ i)) → ∃ ψ' : OpenPartialHomeomorph X (Fin e → ℂ), IsCompatChart A ψ' ∧ ψ'.source = ψ.source ∩ pr ⁻¹' ψb.source ∧ (∀ y ∈ ψ'.source, ∀ i, ψ' y (σ i) = ψb (pr y) i) ∧ ∀ y ∈ ψ'.source, ∀ i, (∀ l, σ l ≠ i) → ψ' y i = ψ y i := by
  intro e n X Z _ _ A Ab pr ψ kb σ ψb hψ hb hpr
  have h₁ : AnalyticOnNhd ℂ ((Ab.chart kb).symm.trans ψb)
      ((Ab.chart kb).symm.trans ψb).source := by
    intro y hy
    exact (hb kb).1 y hy
  have h₂ : AnalyticOnNhd ℂ ((Ab.chart kb).symm.trans ψb).symm
      ((Ab.chart kb).symm.trans ψb).target := by
    intro y hy
    exact (hb kb).2 y hy
  have hcomp : ∀ y ∈ ψ.source, ψ y ∘ σ = Ab.chart kb (pr y) := fun y hy =>
    funext fun i => ((hpr y hy).2 i).symm
  let T := extendHomeo σ ((Ab.chart kb).symm.trans ψb) h₁ h₂
  have hTan : ∀ w ∈ T.source, AnalyticAt ℂ T w := fun w hw =>
    analyticAt_extend_emb σ (h₁ _ hw)
  have hTsan : ∀ w ∈ T.target, AnalyticAt ℂ T.symm w := fun w hw =>
    analyticAt_extend_emb σ (h₂ _ hw)
  have hsrc : (ψ.trans T).source = ψ.source ∩ pr ⁻¹' ψb.source := by
    ext y
    rw [OpenPartialHomeomorph.trans_source]
    constructor
    · rintro ⟨hy, hy'⟩
      refine ⟨hy, ?_⟩
      have h3 : ψ y ∘ σ ∈ ((Ab.chart kb).symm.trans ψb).source := hy'
      rw [hcomp y hy, OpenPartialHomeomorph.trans_source] at h3
      have h4 := h3.2
      simp only [Set.mem_preimage] at h4
      rwa [(Ab.chart kb).left_inv (hpr y hy).1] at h4
    · rintro ⟨hy, hy'⟩
      refine ⟨hy, ?_⟩
      show ψ y ∘ σ ∈ ((Ab.chart kb).symm.trans ψb).source
      rw [hcomp y hy, OpenPartialHomeomorph.trans_source]
      refine ⟨(Ab.chart kb).map_source (hpr y hy).1, ?_⟩
      simp only [Set.mem_preimage]
      rwa [(Ab.chart kb).left_inv (hpr y hy).1]
  refine ⟨ψ.trans T, ?_, hsrc, ?_, ?_⟩
  · intro j
    refine ⟨?_, ?_⟩
    · rintro y ⟨hy1, hy2⟩
      rw [Set.mem_preimage, OpenPartialHomeomorph.trans_source] at hy2
      have h := (hψ j).1 y ⟨hy1, hy2.1⟩
      exact AnalyticAt.comp (g := T) (f := ψ ∘ (A.chart j).symm) (hTan _ hy2.2) h
    · rintro z ⟨hz1, hz2⟩
      rw [OpenPartialHomeomorph.trans_target] at hz1
      have h := (hψ j).2 (T.symm z) ⟨hz1.2, hz2⟩
      exact AnalyticAt.comp (g := A.chart j ∘ ψ.symm) (f := T.symm) h (hTsan z hz1.1)
  · intro y hy i
    rw [hsrc] at hy
    show Function.extend σ (((Ab.chart kb).symm.trans ψb) (ψ y ∘ σ)) (ψ y) (σ i) = ψb (pr y) i
    rw [σ.injective.extend_apply, hcomp y hy.1]
    show ψb ((Ab.chart kb).symm (Ab.chart kb (pr y))) i = ψb (pr y) i
    rw [(Ab.chart kb).left_inv (hpr y hy.1).1]
  · intro y _ i hi
    show Function.extend σ (((Ab.chart kb).symm.trans ψb) (ψ y ∘ σ)) (ψ y) i = ψ y i
    exact Function.extend_apply' _ _ _ (fun ⟨l, hl⟩ => hi l hl)

end GlobalTheory.CompanionTheory.Ar.PB.ChartSwap
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ConjugationInvariantSingularPotentialStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugation_invariant_singular_potential : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (Θ : LocPot X) (L : LocPot X) (s : X → X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X), IsPotential A L → IsSection A L s → IsSNC A L s m W → (∀ y, logNormSec L s y ≤ 0) → IsPotential A Θ → IsPosPot A Θ → ∀ (c : X → X), Continuous c → (∀ x, c (c x) = x) → (∀ j k, AnalyticOnNhd ℂ (fun z => star (A.chart k (c ((A.chart j).symm z)))) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (c ⁻¹' (A.chart k).source))) → (∀ y, c y ∈ bdry s ↔ y ∈ bdry s) → (∀ y, rW L s (c y) = rW L s y) → ∀ (th : LocPot X) (ph : X → ℝ) (phT : ℝ → X → ℝ) (C t₀ : ℝ), IsPotential A th → (∀ x, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∃ G : X → ℂ, A.HoloOn V G ∧ ∀ y ∈ V, th.φ (c x) (c y) - th.φ x y = (G y).re) → (∀ y ∉ bdry s, ph (c y) = ph y) → IsRegFamily A Θ L s th ph phT C t₀ → IsRegFamilyC2 A s ph phT → ∃ C' t₀' : ℝ, IsRegFamily A Θ L s th ph (fun t y => (phT t y + phT t (c y)) / 2) C' t₀' ∧ IsRegFamilyC2 A s ph fun t y => (phT t y + phT t (c y)) / 2 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.an_conj_symmetrise | exact GlobalTheory.CompanionTheory.Ar.PB.an_conj_symmetrise | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.an_conj_symmetrise <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.CoordinateRatioValueAtPoint
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph

theorem isValueAt_coord_ratio :
    ∀ (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Ω : Type) [Field Ω]
      (y' : (Σ k, ι' k) → Ω) (z : (Σ k, ι' k) → ℂ) (k : K') (c : ι' k),
      z ∈ mcPts (mCoordIdeal y') → z ⟨k, c⟩ ≠ 0 →
        y' ⟨k, c⟩ ≠ 0 ∧ ∀ i : ι' k, IsValueAt y' (y' ⟨k, i⟩ / y' ⟨k, c⟩) z ((z ⟨k, c⟩)⁻¹ * z ⟨k, i⟩) := by
  intro K' _ ι' _ Ω _ y' z k c hz hzc
  have hy : y' ⟨k, c⟩ ≠ 0 := by
    intro h0
    have hm : (X ⟨k, c⟩ : MRing ι') ∈ mCoordIdeal y' := by
      refine RingHom.mem_ker.2 ?_
      simp [mConeMap, h0]
    have h1 := hz.2 _ hm
    simp only [map_X, eval_X] at h1
    exact hzc h1
  refine ⟨hy, fun i => ⟨fun l => if l = k then 1 else 0, X ⟨k, i⟩, X ⟨k, c⟩,
    GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_X_single ⟨k, i⟩,
    GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_X_single ⟨k, c⟩, ?_, ?_, ?_, ?_⟩⟩
  · simpa using hy
  · simp only [aeval_X]
    field_simp
  · simpa using hzc
  · simp only [map_X, eval_X]
    rw [div_eq_inv_mul]

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.DetFacGMatEqOneStatement
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.detFac_gMat_eq_one : ∀ (Ψ : Type) (p q : ℕ) (Ω : Type) [Field Ω] (τ : Ψ) (i : Fin (p + q)), detFac p i (gMat p q Ω τ) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.DetG.detFac_gMat | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.DetG.detFac_gMat | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.DetG.detFac_gMat <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.DetMemSubring
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm

variable {Ψ : Type} {p q : ℕ} {Ω : Type} [Field Ω] {n : Ψ ⊕ Ψ → ℕ}

def tMat (Ts : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (rk Ψ p q s)) Ω) (τ : Ψ) :
    Matrix (Fin (p + q)) (Fin (p + q)) Ω :=
  (Matrix.fromBlocks (Ts (.inr τ)) 0 0 (Ts (.inl τ))).submatrix (blockEquiv p q).symm (blockEquiv p q).symm

def cMin (C : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (t : StepIx Ψ p q)
    (J : Fin ((t.2 : ℕ) + 1) → Fin (n t.1)) (I : Finset (Fin (p + q))) : Ω :=
  if e : I.card = (t.2 : ℕ) + 1 then ((aExt C t.1).submatrix J (I.orderEmbOfFin e)).det else 0

open Classical in

def bExt (B : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (n s)) Ω) (s : Ψ ⊕ Ψ) : Matrix (Fin (p + q)) (Fin (n s)) Ω :=
  fun a j => ∑ l, if posOf p q s l = a then B s l j else 0

def bMin (B : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (n s)) Ω) (t : StepIx Ψ p q)
    (I : Finset (Fin (p + q))) (J : Fin ((t.2 : ℕ) + 1) → Fin (n t.1)) : Ω :=
  if e : I.card = (t.2 : ℕ) + 1 then ((bExt B t.1).submatrix (I.orderEmbOfFin e) J).det else 0

variable (p q) in

def fullT (s : Ψ ⊕ Ψ) (h : 0 < rk Ψ p q s) : StepIx Ψ p q := ⟨s, ⟨rk Ψ p q s - 1, by omega⟩⟩

theorem fullT_base (K₀ : Type) (s : Ψ ⊕ Ψ) (h : 0 < rk Ψ p q s) (r : Ψ × Fin (p + q)) :
    blkF Ψ p q K₀ r ≠ some (.inr (fullT p q s h)) := by
  intro hr
  unfold blkF at hr
  split_ifs at hr with hp
  obtain ⟨h1, h2⟩ := hp
  simp only [Option.some.injEq, Sum.inr.injEq] at hr
  unfold stepOf fullT at hr
  have hv := r.2.isLt
  split_ifs at hr with hlt
  · rw [Sigma.mk.inj_iff] at hr
    obtain ⟨hs, hx⟩ := hr
    subst hs
    have hx' := congrArg Fin.val (eq_of_heq hx)
    simp [rk] at hx' h
    omega
  · rw [Sigma.mk.inj_iff] at hr
    obtain ⟨hs, hx⟩ := hr
    subst hs
    have hx' := congrArg Fin.val (eq_of_heq hx)
    simp [rk] at hx' h
    omega

def baseFull (K₀ : Type) (s : Ψ ⊕ Ψ) (h : 0 < rk Ψ p q s) : NonPluckerBlocks (blkF Ψ p q K₀) :=
  ⟨.inr (fullT p q s h), fullT_base K₀ s h⟩

def baseInl {K₀ : Type} (k : K₀) : NonPluckerBlocks (blkF Ψ p q K₀) :=
  ⟨.inl k, fun r => by
    classical
    unfold blkF
    split_ifs <;> simp⟩

variable {K₀ : Type} {J₀ : K₀ → Type}

def xcOf [Fintype K₀] (x₀ : (Σ k, J₀ k) → Ω)
    (c : ∀ k : NonPluckerBlocks (blkF Ψ p q K₀), baseIdx (idx (p := p) (q := q) J₀ n) (blkF Ψ p q K₀) k) : Ω :=
  ∏ k, x₀ ⟨k, c (baseInl k)⟩

def rowsOf (c : ∀ k : NonPluckerBlocks (blkF Ψ p q K₀), baseIdx (idx (p := p) (q := q) J₀ n) (blkF Ψ p q K₀) k)
    (s : Ψ ⊕ Ψ) : Fin (rk Ψ p q s) → Fin (n s) :=
  fun a => c (baseFull K₀ s (by have := a.2; omega)) (Fin.cast (by have := a.2; show _ = rk Ψ p q s - 1 + 1; omega) a)

def zOf (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω)
    (c : ∀ k : NonPluckerBlocks (blkF Ψ p q K₀), baseIdx (idx (p := p) (q := q) J₀ n) (blkF Ψ p q K₀) k)
    (s : Ψ ⊕ Ψ) : Ω :=
  ((A s).submatrix (rowsOf c s) id).det

theorem xb_full [Fintype Ψ] [Fintype K₀] [∀ k, Fintype (J₀ k)] (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω)
    (x₀ : (Σ k, J₀ k) → Ω) (s : Ψ ⊕ Ψ) (h : 0 < rk Ψ p q s) (J : Fin (rk Ψ p q s) → Fin (n s)) :
    xb A x₀ ⟨baseFull K₀ s h, fun a => J (Fin.cast (by show _ = rk Ψ p q s; have := a.2; show rk Ψ p q s - 1 + 1 = _; omega) a)⟩ =
      ((A s).submatrix J id).det := by
  simp only [xb, baseFull, xv]
  have e : rk Ψ p q s - 1 + 1 = rk Ψ p q s := by omega
  rw [← Matrix.det_submatrix_equiv_self (finCongr e) ((A s).submatrix J id)]
  rfl

theorem xb_rowsOf [Fintype Ψ] [Fintype K₀] [∀ k, Fintype (J₀ k)] (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω)
    (x₀ : (Σ k, J₀ k) → Ω)
    (c : ∀ k : NonPluckerBlocks (blkF Ψ p q K₀), baseIdx (idx (p := p) (q := q) J₀ n) (blkF Ψ p q K₀) k)
    (s : Ψ ⊕ Ψ) (h : 0 < rk Ψ p q s) :
    xb A x₀ ⟨baseFull K₀ s h, c (baseFull K₀ s h)⟩ = zOf A c s :=
  xb_full A x₀ s h (rowsOf c s)

theorem det_mem_subring {ι : Type} [Fintype ι] [DecidableEq ι] (R : Subring Ω) (M : Matrix ι ι Ω)
    (h : ∀ a b, M a b ∈ R) : M.det ∈ R := by
  rw [Matrix.det_apply]
  refine R.sum_mem fun σ _ => ?_
  rw [Units.smul_def]
  exact R.zsmul_mem (R.prod_mem fun i _ => h _ _) _

open Classical in

def sMin (B : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (n s)) Ω) (t : StepIx Ψ p q)
    (I : Finset (Fin (p + q))) (J : Fin ((t.2 : ℕ) + 1) → Fin (n t.1)) : Ω :=
  if StrictMono J then bMin B t I J else 0

private theorem card_filter_fin_Ico (N lo hi : ℕ) (hh : hi ≤ N) :
    (Finset.univ.filter (fun a : Fin N => lo ≤ (a : ℕ) ∧ (a : ℕ) < hi)).card = hi - lo := by
  rw [← Nat.card_Ico lo hi]
  apply Finset.card_bij (fun (a : Fin N) _ => (a : ℕ))
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    simp only [Finset.mem_Ico]
    omega
  · intro a _ b _ hab
    exact Fin.ext hab
  · intro b hb
    simp only [Finset.mem_Ico] at hb
    exact ⟨⟨b, by omega⟩, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega, rfl⟩

theorem card_stepCols (r : Ψ × Fin (p + q)) :
    (stepCols (p + q) p r.2).card = ((stepOf Ψ p q r).2 : ℕ) + 1 := by
  have hv := r.2.isLt
  unfold stepCols
  by_cases hc : (r.2 : ℕ) < p
  · have hs : stepOf Ψ p q r = ⟨Sum.inl r.1, ⟨r.2, by simp [rk]; omega⟩⟩ := by
      unfold stepOf
      rw [dif_pos hc]
    have hc' : (r.2 : ℕ) + 1 ≤ p := hc
    rw [hs]
    simp only [if_pos hc']
    rw [card_filter_fin_Ico _ _ _ (by omega)]
    omega
  · have hs : stepOf Ψ p q r = ⟨Sum.inr r.1, ⟨r.2 - p, by simp [rk]; omega⟩⟩ := by
      unfold stepOf
      rw [dif_neg hc]
    have hc' : ¬ ((r.2 : ℕ) + 1 ≤ p) := by omega
    rw [hs]
    simp only [if_neg hc']
    have := card_filter_fin_Ico (p + q) 0 ((r.2 : ℕ) + 1 - p) (by omega)
    simp only [Nat.zero_le, true_and] at this
    rw [this]
    omega

theorem stepRows_pos (r : Ψ × Fin (p + q)) {I : Finset (Fin (p + q))} (h : IsStepRows (p + q) p r.2 I) :
    ∀ a ∈ I, ∃ l, posOf p q (stepOf Ψ p q r).1 l = a := by
  intro a ha
  obtain ⟨-, hsub⟩ := h
  have hmem := hsub ha
  have hv := a.isLt
  by_cases hc : (r.2 : ℕ) < p
  · have hs : stepOf Ψ p q r = ⟨Sum.inl r.1, ⟨r.2, by simp [rk]; omega⟩⟩ := by
      unfold stepOf
      rw [dif_pos hc]
    have hc' : (r.2 : ℕ) + 1 ≤ p := hc
    rw [if_pos hc'] at hmem
    simp only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    rw [hs]
    refine ⟨⟨a - q, by simp [rk]; omega⟩, ?_⟩
    simp only [posOf, wEmb]
    ext
    simp only
    omega
  · have hs : stepOf Ψ p q r = ⟨Sum.inr r.1, ⟨r.2 - p, by simp [rk]; omega⟩⟩ := by
      unfold stepOf
      rw [dif_neg hc]
    have hc' : ¬ ((r.2 : ℕ) + 1 ≤ p) := by omega
    rw [if_neg hc'] at hmem
    simp only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    rw [hs]
    refine ⟨⟨a, by simp [rk]; omega⟩, ?_⟩
    simp only [posOf, omEmb]

end GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsLocalTwistTrivializationStatement
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_twist_trivialization : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type) (x : κ → Ω) (L : Lat ξ E) (m r n : ℕ) (V : Submodule Ω E) (φ : Fin n → Module.Dual Ω E) (cb : Fin r → E), IsTwistGen ξ x L m φ → L.IsVB r V → LinearIndependent Ω cb → Submodule.span Ω (Set.range cb) = V → ∀ (p : Cpt ξ) (c : κ), InChart ξ x c p → ∃ (T : Matrix (Fin r) (Fin r) Ω) (C : Matrix (Fin r) (Fin n) Ω), IsUnit T.det ∧ L.IsFrameAt (colFrame cb T) p ∧ (∀ a b, ((Matrix.of fun a b => φ a (cb b)) * T) a b / x c ^ m ∈ regAt ξ p) ∧ (∀ a b, C a b ∈ regAt ξ p) ∧ ∀ a b, ∑ k, C a k * (((Matrix.of fun a b => φ a (cb b)) * T) k b / x c ^ m) = if a = b then 1 else 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.RootsBase.frame_values | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.RootsBase.frame_values | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.RootsBase.frame_values <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsNonzeroXbOfLeftInverseStatement
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzero_xb_of_left_inverse : ∀ (Ψ : Type) [Fintype Ψ] (p q : ℕ) (Ω : Type) [Field Ω] (n : Ψ ⊕ Ψ → ℕ) (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω), (∀ k, ∃ i, x₀ ⟨k, i⟩ ≠ 0) → (∀ s, ∃ B : Matrix (Fin (rk Ψ p q s)) (Fin (n s)) Ω, B * A s = 1) → ∀ k, ∃ i, xb A x₀ ⟨k, i⟩ ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.BasePt.xb_block_ne | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.BasePt.xb_block_ne | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.BasePt.xb_block_ne <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsTriangularRegularFrameChangeStatement
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_triangular_regular_frame_change : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (r : ℕ) (w : Fin r → E) (P g : Matrix (Fin r) (Fin r) Ω) (p : Cpt ξ), LinearIndependent Ω w → IsUnit g.det → L.IsFrameAt (colFrame w P) p → L.IsFlagVBOn Set.univ (colFrame w g) → ∃ U Rm Rm' : Matrix (Fin r) (Fin r) Ω, U.BlockTriangular id ∧ (∀ a b, Rm a b ∈ regAt ξ p) ∧ (∀ a b, Rm' a b ∈ regAt ξ p) ∧ Rm * Rm' = 1 ∧ g * U = P * Rm ∧ ∀ l, (L.gr (colFrame w g) l).IsGenAt p (U l l) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FrameTrans.exists_adapted | exact GlobalTheory.CompanionTheory.Ar.PB.FrameTrans.exists_adapted | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FrameTrans.exists_adapted <;> assumption)
end

