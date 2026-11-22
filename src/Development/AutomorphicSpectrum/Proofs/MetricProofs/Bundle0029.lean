import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle0006
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.RiemannLatticeConjugateCusp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0017
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0027
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GenericBlockMatrixIsBlockDiag
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.CauchyBinet
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0003
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalLeviPshRegularization
import ReciprocityTheory.AnalyticForms.LeviForms.RegGlue
import ReciprocityTheory.AnalyticForms.LeviForms.RegChartC
import ReciprocityTheory.AnalyticForms.LeviForms.TailCut
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.Bundle0001
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ArithmeticIntersectionMultilinearPolar
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem combLine_intersection : MetricLocalStatement → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ : Type) [Fintype σ] (P : Ideal (MRing ι)) (n : ℕ) (A : σ → HermLine ι) (c : Fin n → σ → ℤ), IsArithVar P n → (∀ a, IsSmoothHerm (A a)) → (∀ r, IsSmoothHerm (combLine A (c r))) ∧ II K ι P n (fun r => combLine A (c r)) = polar n (fun w => II K ι P n fun r => A (w r)) (fun r a => (c r a : ℝ)) :=
  @PositivityTheory.Xgp.t_re_comb

end GlobalTheory.CompanionTheory.Ar.PB
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ChartLatticeShiftNonzero
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem section_sub_degree : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (α : K → ℤ) (dβ : K → ℕ), (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → (∃ k : ℕ, 1 ≤ k ∧ ∃ e ∈ chartLat y (fun κ => (k : ℤ) * α κ - 1) 1, e ≠ 0) → ∃ k : ℕ, 1 ≤ k ∧ ∃ e ∈ chartLat y (fun κ => (k : ℤ) * α κ - 1 - dβ κ) 1, e ≠ 0 :=
  @PositivityTheory.Xgp.t_pol_sec

end GlobalTheory.CompanionTheory.Ar.PB
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ConjugationInvariantHermitianMetric
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem exists_conjInvariant_line_averaged : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (A : HermLine ι), IsSmoothHerm A → ∃ B : HermLine ι, B.a = A.a ∧ IsSmoothHerm B ∧ IsConjInvariantH B ∧ ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → Real.log (B.h z) = (Real.log (A.h z) + Real.log (A.h fun p => starRingEnd ℂ (z p))) / 2 :=
  @PositivityTheory.Xgp.t_line_conj

end GlobalTheory.CompanionTheory.Ar.PB
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.CuspWeightInvariantUnderConjugation
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.cusp_weight_invariant_under_conjugation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (R : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)), IsCMFam σ → R.cuspW (fun τ => (starRingEnd ℂ).comp (σ τ)) = R.cuspW σ ∧ ∃ R' : RiemLat E g Λ, (∀ v, R'.P v = star (R.P v)) ∧ R'.Hm = R.Hm.map (starRingEnd ℂ) ∧ (∀ a x, R'.B a (star x) = star (R.B a x)) ∧ R'.cuspW (fun τ => (starRingEnd ℂ).comp (σ τ)) = R.cuspW σ := by
  first | exact @LevelTowerAlt.riemann_lattice_conjugate_cusp | exact LevelTowerAlt.riemann_lattice_conjugate_cusp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeOfIsIntersectionSystem
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem degree_of_isIntersectionSystem (II : IntersectionSystem) (hII : IsIntersectionSystem II) :
    ReciprocityTheory.ChartRestriction.G.Geo.DegreeStatement :=
  GroundTheory.Heights₂.Heights.Inter.Conservation.conservation_iff_degree_statement.mp
    (GroundTheory.Heights₂.Heights.Inter.Conservation.conservation_degree_form_of_existence ⟨II, hII⟩
      GroundTheory.Heights₂.Heights.Inter.Conservation.statement_holds)

theorem degree_of_system :
    ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → ReciprocityTheory.ChartRestriction.G.Geo.DegreeStatement :=
  fun ⟨II, hII⟩ => degree_of_isIntersectionSystem II hII.1

end GlobalTheory.CompanionTheory.Ar.Giv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HolomorphicFamilySmoothEntriesStatement
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_family_smooth_entries : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (n : ℕ) (U : Set (Fin n → ℂ)) (R : (Fin n → ℂ) → RiemLat E g Λ), IsOpen U → IsHolFam U R → (∀ i j, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => ((R t).Hm i j).re) U ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => ((R t).Hm i j).im) U) ∧ (∀ a x, DifferentiableOn ℂ (fun t => (R t).B a x) U) ∧ ∀ (m : ℕ) (u : Fin m → (Fin n → ℂ) → Fin g → ℂ), (∀ i, DifferentiableOn ℂ (u i) U) → (∀ t ∈ U, LinearIndependent ℂ fun i => u i t) → ReciprocityTheory.AnForm.A.IsPsh U fun t => Real.log ((R t).gram fun i => u i t).det.re := by
  first | exact @GlobalTheory.CompanionTheory.Relay.holomorphic_family_smooth_entries | exact GlobalTheory.CompanionTheory.Relay.holomorphic_family_smooth_entries | (intros; apply GlobalTheory.CompanionTheory.Relay.holomorphic_family_smooth_entries <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsBlockDiagMapGenBlock
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

section Homog

variable {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isMultiHomog_mul_alt {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) :
    IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m₁, h₁, m₂, h₂, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hm)
  simp [Finset.sum_add_distrib, hf m₁ h₁ k, hg m₂ h₂ k]

theorem isMultiHomog_add_alt {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f + g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
  · exact hf m h k
  · exact hg m h k

theorem isMultiHomog_zero_alt (a : K → ℕ) : IsMultiHomog (0 : MRing ι) a := by
  intro m hm
  simp at hm

theorem isMultiHomog_one_alt : IsMultiHomog (1 : MRing ι) 0 := by
  classical
  intro m hm k
  have : m = 0 := by
    have h := MvPolynomial.support_monomial_subset (s := (0 : (Σ k, ι k) →₀ ℕ)) (a := (1 : ℤ)) hm
    simpa using h
  simp [this]

theorem isMultiHomog_rename_base {σ : Type} (blk : σ → Option K) {d' : NonPluckerBlocks blk → ℕ}
    {g : MRing (baseIdx ι blk)} (hg : IsMultiHomog g d') :
    open Classical in
    IsMultiHomog (rename (fun q : Σ k, baseIdx ι blk k => (⟨q.1.1, q.2⟩ : Σ k, ι k)) g)
      (fun k => if h : ∀ p, blk p ≠ some k then d' ⟨k, h⟩ else 0) := by
  classical
  have hinj : Function.Injective (fun q : Σ k, baseIdx ι blk k => (⟨q.1.1, q.2⟩ : Σ k, ι k)) := by
    rintro ⟨⟨k, hk⟩, a⟩ ⟨⟨k', hk'⟩, b⟩ h
    obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.mp h
    cases h
    rfl
  intro m hm k
  rw [support_rename_of_injective hinj, Finset.mem_image] at hm
  obtain ⟨m', hm', rfl⟩ := hm
  beta_reduce
  by_cases h : ∀ p, blk p ≠ some k
  · rw [dif_pos h, ← hg m' hm' ⟨k, h⟩]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Finsupp.mapDomain_apply hinj m' ⟨⟨k, h⟩, i⟩
  · rw [dif_neg h]
    refine Finset.sum_eq_zero fun i _ => Finsupp.mapDomain_of_notMem_range _ _ ?_
    rintro ⟨⟨⟨k', hk'⟩, b⟩, e⟩
    obtain ⟨rfl, -⟩ := Sigma.mk.inj_iff.mp e
    exact h hk'

def IsFormQuot {Φ : Type} [Field Φ] (y : (Σ k, ι k) → Φ) (s : Φ) : Prop :=
  ∃ (d : K → ℕ) (g h : MRing ι), IsMultiHomog g d ∧ IsMultiHomog h d ∧ aeval y h ≠ 0 ∧ aeval y g = s * aeval y h

variable {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}

theorem IsFormQuot.zero : IsFormQuot y 0 :=
  ⟨0, 0, 1, isMultiHomog_zero_alt _, isMultiHomog_one_alt, by simp, by simp⟩

theorem IsFormQuot.add {s t : Φ} (hs : IsFormQuot y s) (ht : IsFormQuot y t) : IsFormQuot y (s + t) := by
  obtain ⟨d₁, g₁, h₁, hg₁, hh₁, hy₁, e₁⟩ := hs
  obtain ⟨d₂, g₂, h₂, hg₂, hh₂, hy₂, e₂⟩ := ht
  refine ⟨d₁ + d₂, g₁ * h₂ + g₂ * h₁, h₁ * h₂,
    isMultiHomog_add_alt (isMultiHomog_mul_alt hg₁ hh₂) (by rw [add_comm d₁]; exact isMultiHomog_mul_alt hg₂ hh₁),
    isMultiHomog_mul_alt hh₁ hh₂, by rw [map_mul]; exact mul_ne_zero hy₁ hy₂, ?_⟩
  rw [map_add, map_mul, map_mul, map_mul, e₁, e₂]
  ring

theorem IsFormQuot.mul {s t : Φ} (hs : IsFormQuot y s) (ht : IsFormQuot y t) : IsFormQuot y (s * t) := by
  obtain ⟨d₁, g₁, h₁, hg₁, hh₁, hy₁, e₁⟩ := hs
  obtain ⟨d₂, g₂, h₂, hg₂, hh₂, hy₂, e₂⟩ := ht
  refine ⟨d₁ + d₂, g₁ * g₂, h₁ * h₂, isMultiHomog_mul_alt hg₁ hg₂, isMultiHomog_mul_alt hh₁ hh₂,
    by rw [map_mul]; exact mul_ne_zero hy₁ hy₂, ?_⟩
  rw [map_mul, map_mul, e₁, e₂]
  ring

theorem IsFormQuot.inv {s : Φ} (hs : IsFormQuot y s) : IsFormQuot y s⁻¹ := by
  by_cases h0 : s = 0
  · rw [h0, inv_zero]
    exact IsFormQuot.zero
  · obtain ⟨d, g, h, hg, hh, hy, e⟩ := hs
    refine ⟨d, h, g, hh, hg, by rw [e]; exact mul_ne_zero h0 hy, ?_⟩
    rw [e]
    field_simp

theorem IsFormQuot.sum {α : Type} (A : Finset α) {f : α → Φ} (hf : ∀ a ∈ A, IsFormQuot y (f a)) :
    IsFormQuot y (∑ a ∈ A, f a) := by
  classical
  induction A using Finset.induction_on with
  | empty => simpa using IsFormQuot.zero
  | insert a A ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self _ _)).add
      (ih fun b hb => hf b (Finset.mem_insert_of_mem hb))

end Homog

section Minors

variable {N : ℕ}

theorem minorIJ_eq_det_of_card {R : Type} [CommRing R] (h : Matrix (Fin N) (Fin N) R) (I J : Finset (Fin N)) {r : ℕ}
    (hI : I.card = r) (hJ : J.card = r) :
    minorIJ h I J = (h.submatrix (I.orderEmbOfFin hI) (J.orderEmbOfFin hJ)).det := by
  subst hJ
  unfold minorIJ
  rw [dif_pos hI]

theorem minorIJ_mul_sum {R : Type} [CommRing R] (T h : Matrix (Fin N) (Fin N) R) (I J : Finset (Fin N)) :
    minorIJ (T * h) I J = ∑ I', minorIJ T I I' * minorIJ h I' J := by
  classical
  by_cases e : I.card = J.card
  · have hm : (T * h).submatrix (I.orderEmbOfFin e) (J.orderEmbOfFin rfl) =
        T.submatrix (I.orderEmbOfFin e) id * h.submatrix id (J.orderEmbOfFin rfl) := by
      ext a b
      simp [Matrix.mul_apply]
    have hsum : ∑ I', minorIJ T I I' * minorIJ h I' J =
        ∑ S : {S : Finset (Fin N) // S.card = J.card}, minorIJ T I S.1 * minorIJ h S.1 J := by
      rw [← Finset.sum_filter_of_ne (s := Finset.univ) (p := fun S : Finset (Fin N) => S.card = J.card)]
      · exact Finset.sum_subtype _ (by simp) _
      · intro S _ hS
        by_contra hc
        apply hS
        rw [show minorIJ h S J = 0 by unfold minorIJ; rw [dif_neg hc], mul_zero]
    rw [minorIJ_eq_det_of_card _ I J e rfl, hm, ReciprocityTheory.ChartRestriction.DS.cauchyBinet, hsum]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [minorIJ_eq_det_of_card T I S.1 e S.2, minorIJ_eq_det_of_card h S.1 J S.2 rfl]
    rfl
  · have h0 : minorIJ (T * h) I J = 0 := by
      unfold minorIJ
      rw [dif_neg e]
    rw [h0]
    symm
    refine Finset.sum_eq_zero fun I' _ => ?_
    by_cases e' : I.card = I'.card
    · rw [show minorIJ h I' J = 0 by
        unfold minorIJ
        rw [dif_neg fun c => e (e'.trans c)], mul_zero]
    · rw [show minorIJ T I I' = 0 by unfold minorIJ; rw [dif_neg e'], zero_mul]

theorem minorIJ_block_zero {R : Type} [CommRing R] {j : ℕ} {i : Fin N} {h : Matrix (Fin N) (Fin N) R}
    (hh : IsBlockDiag j h) {I : Finset (Fin N)} (hnot : ¬ IsStepRows N j i I) :
    minorIJ h I (stepCols N j i) = 0 := by
  have hiN := i.isLt
  by_cases e : I.card = (stepCols N j i).card
  · have hsub : ¬ I ⊆ if (i : ℕ) + 1 ≤ j then wIdx N j else omIdx N j := fun hs => hnot ⟨e, hs⟩
    obtain ⟨a, haI, haB⟩ := Finset.not_subset.mp hsub
    have hr : a ∈ Set.range (I.orderEmbOfFin e) := by
      rw [Finset.range_orderEmbOfFin]
      exact haI
    obtain ⟨r, rfl⟩ := hr
    unfold minorIJ
    rw [dif_pos e]
    refine Matrix.det_eq_zero_of_row_eq_zero r fun c => ?_
    have hb := Finset.orderEmbOfFin_mem (stepCols N j i) rfl c
    refine hh _ _ ?_
    generalize (stepCols N j i).orderEmbOfFin rfl c = b at hb
    generalize I.orderEmbOfFin e r = a at haB
    by_cases hc : (i : ℕ) + 1 ≤ j
    · simp only [stepCols, wIdx, Finset.mem_filter, Finset.mem_univ, true_and, if_pos hc] at hb haB
      omega
    · simp only [stepCols, omIdx, Finset.mem_filter, Finset.mem_univ, true_and, if_neg hc] at hb haB
      omega
  · unfold minorIJ
    rw [dif_neg e]

def genBlock (Ω : Type) [Field Ω] (N j : ℕ) : Matrix (Fin N) (Fin N) (MvPolynomial (Fin N × Fin N) Ω) :=
  fun a b => if ((a : ℕ) < N - j ↔ (b : ℕ) < N - j) then X (a, b) else 0

theorem isBlockDiag_inv {F : Type} [Field F] {j : ℕ} {T : Matrix (Fin N) (Fin N) F} (hT : IsBlockDiag j T)
    (hd : T.det ≠ 0) : IsBlockDiag j T⁻¹ := by
  classical
  haveI : Invertible T := Matrix.invertibleOfIsUnitDet T (isUnit_iff_ne_zero.mpr hd)
  have h1 : T.BlockTriangular (fun a : Fin N => if (a : ℕ) < N - j then 0 else 1) := by
    intro a b hab
    refine hT a b fun hiff => ?_
    simp only [hiff] at hab
    exact lt_irrefl _ hab
  have h2 : T.BlockTriangular (fun a : Fin N => if (a : ℕ) < N - j then 1 else 0) := by
    intro a b hab
    refine hT a b fun hiff => ?_
    simp only [hiff] at hab
    exact lt_irrefl _ hab
  have i1 := Matrix.blockTriangular_inv_of_blockTriangular h1
  have i2 := Matrix.blockTriangular_inv_of_blockTriangular h2
  intro a b hab
  by_cases ha : (a : ℕ) < N - j
  · have hb : ¬ (b : ℕ) < N - j := fun hb => hab (iff_of_true ha hb)
    refine i2 ?_
    simp [ha, hb]
  · have hb : (b : ℕ) < N - j := by
      by_contra hb
      exact hab (iff_of_false ha hb)
    refine i1 ?_
    simp [ha, hb]

end Minors

section Model

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} {N j : ℕ}

end Model

end GlobalTheory.CompanionTheory.Ar.PB
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsotropicEigencomponentConjugateForm
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.isotropic_eigencomponent_conjugate_form : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (R : RiemLat E g Λ) (I : Submodule (𝓞 E) Λ), IsIsoSub R.form I → ∀ s : 𝓞 E →+* ℂ, (∀ v ∈ I, ∀ w ∈ I, R.ip (eigComp R.B ((starRingEnd ℂ).comp s) (R.P v)) (eigComp R.B ((starRingEnd ℂ).comp s) (R.P w)) = starRingEnd ℂ (R.ip (eigComp R.B s (R.P v)) (eigComp R.B s (R.P w)))) ∧ ∀ (r : ℕ) (v : Fin r → Λ), (∀ a, v a ∈ I) → LinearIndependent (𝓞 E) v → LinearIndependent ℂ fun a => eigComp R.B s (R.P (v a)) := by
  first | exact @LevelTowerAlt.eigen_projection_conjugate_inner | exact LevelTowerAlt.eigen_projection_conjugate_inner
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalLeviPshRegularizationStatement
section
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_levi_psh_regularization : ∀ (D : ℕ) (S : Finset (Fin D)) (m : Fin D → ℕ) (q ph : (Fin D → ℂ) → ℝ) (C₅ K : ℝ), (∀ i ∈ S, 1 ≤ m i) → ContDiffOn ℝ ∞ q (ball (0 : Fin D → ℂ) (2)) → ContDiffOn ℝ ∞ ph (ball (0 : Fin D → ℂ) (2) \ ReciprocityTheory.AnForm.A.coordDiv S) → ReciprocityTheory.AnForm.A.IsLeviPsh (ball (0 : Fin D → ℂ) (2) \ ReciprocityTheory.AnForm.A.coordDiv S) (fun z => q z + ph z) → (∀ z ∈ ball (0 : Fin D → ℂ) (2) \ ReciprocityTheory.AnForm.A.coordDiv S, -C₅ * Real.log (rLoc S m z) ≤ ph z ∧ ph z ≤ C₅) → (∀ z ∈ ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S, ‖fderiv ℝ ph z‖ ≤ C₅ * rLoc S m z ^ C₅ * Real.exp (rLoc S m z / 2)) → ∃ (C t₀ : ℝ) (phT : ℝ → (Fin D → ℂ) → ℝ), 1 ≤ C ∧ 0 < t₀ ∧ t₀ ≤ Real.exp (-Real.exp 1) ∧ (∀ t, 0 < t → t ≤ t₀ → ContDiffOn ℝ ∞ (phT t) (ball (0 : Fin D → ℂ) (5 / 4)) ∧ ReciprocityTheory.AnForm.A.IsLeviPsh (ball (0 : Fin D → ℂ) (5 / 4)) (fun z => q z + phT t z) ∧ (∀ z ∈ ball (0 : Fin D → ℂ) (5 / 4), phT t z ≤ C ∧ -C * Real.log (Real.log (1 / t)) ≤ phT t z) ∧ (∀ z ∈ ball (0 : Fin D → ℂ) (5 / 4) \ ReciprocityTheory.AnForm.A.coordDiv S, ph z ≤ phT t z ∧ (rLoc S m z ≤ Real.log (1 / t) + K → phT t z ≤ ph z + t ^ ((1 : ℝ) / 3))) ∧ (∀ z ∈ ball (0 : Fin D → ℂ) (5 / 4), polyMaxOff S (fun x => q x + ph x) z t - epsT C t ≤ q z + phT t z ∧ q z + phT t z ≤ polyMaxOff S (fun x => q x + ph x) z t) ∧ ∀ t', t ≤ t' → t' ≤ t₀ → ∀ z ∈ ball (0 : Fin D → ℂ) (5 / 4), phT t z ≤ phT t' z + epsT C t') ∧ ∀ K' ⊆ ball (0 : Fin D → ℂ) (5 / 4) \ ReciprocityTheory.AnForm.A.coordDiv S, IsCompact K' → TendstoUniformlyOn (fun t => phT t) (ph) (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ (phT t)) (fderiv ℝ (ph)) (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ (phT t))) (fderiv ℝ (fderiv ℝ (ph))) (𝓝[>] 0) K' ∧ ∃ M : ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ K', ‖fderiv ℝ (phT t) z - fderiv ℝ (ph) z‖ ≤ M * t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.regularise_one_chart | exact GlobalTheory.CompanionTheory.Ar.Giv.regularise_one_chart | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.regularise_one_chart <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MetricLocal
section
namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem metricLocal : ReciprocityTheory.ChartRestriction.G.AI.I2.MetricLocalStatement :=
  GroundTheory.Heights₂.Heights.MetricLocalB.full

end GlobalTheory.CompanionTheory.Ar.Giv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereDifferenceTendstoZeroStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monge_ampere_difference_tendsto_zero : ConvergenceSignedStatement → ∀ (e : ℕ) (σ : Type) (S : AnSys e (σ ⊕ σ)) (d : σ → S.X → ℝ), (∀ a, S.A.Smooth (d a)) → (∀ a, ∀ y ∈ S.open', S.ph (Sum.inl a) y = S.ph (Sum.inr a) y + d a y) → ∀ (a : σ) (w : Fin e → σ ⊕ σ), Tendsto (fun t => mInt S.A (fun i => S.potT (w i) t) (fun x => S.phT (Sum.inl a) t x - S.phT (Sum.inr a) t x - d a x)) (𝓝[>] 0) (𝓝 0) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.an_two_weights_close | exact GlobalTheory.CompanionTheory.Ar.PB.an_two_weights_close | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.an_two_weights_close <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereSingularTotalMassDegree
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem AnSys.eventually_mInt_potT {e : ℕ} {σ : Type} (S : AnSys e σ) (w : Fin e → σ) :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      mInt S.A (fun i => S.potT (w i) t) (fun _ => 1) = S.degNum w := by
  have hsm : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ i, S.A.Smooth (S.phT (w i) t) := by
    refine Filter.eventually_all.2 fun i => ?_
    obtain ⟨h0, -, hreg⟩ := S.reg (w i)
    filter_upwards [Ioc_mem_nhdsGT h0] with t ht
    exact (hreg t ht.1 ht.2).1
  filter_upwards [hsm] with t ht
  exact massIndep S.A (fun i => S.th (w i)) (fun i => S.phT (w i) t)
    (fun i => (S.sing (w i)).1) ht

theorem AnSys.abs_one_le_log_rW {e : ℕ} {σ : Type} (S : AnSys e σ) (y : S.X) :
    |(1 : ℝ)| ≤ 1 * Real.log (rW S.L S.s y) := by
  have h : Real.exp 1 ≤ rW S.L S.s y := by
    have := S.norm_le y
    unfold rW
    linarith
  have h1 : (1 : ℝ) ≤ Real.log (rW S.L S.s y) :=
    (Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos 1) h)).2 h
  simpa using h1

theorem AnSys.mIntegrable_potH_and_mInt_eq_degNum :
    ConvergenceSignedStatement → ∀ (e : ℕ) (σ : Type) (S : AnSys e σ) (w : Fin e → σ),
      MIntegrable S.A (fun i => S.potH (w i)) (fun _ => 1) ∧
        mInt S.A (fun i => S.potH (w i)) (fun _ => 1) = S.degNum w := by
  intro hC e σ S w
  letI : MeasurableSpace S.X := borel S.X
  haveI : BorelSpace S.X := ⟨rfl⟩
  have hlim := hC S.A S.Θ S.L S.s S.m S.W S.potΘ S.posΘ S.potL S.sec S.snc S.norm_le
    (fun i => S.th (w i)) (fun i => S.ph (w i)) (fun i => S.phT (w i)) S.C₅ S.C S.t₀
    (fun i => S.sing (w i)) (fun i => S.reg (w i)) (fun i => S.c2 (w i))
    (fun _ => 1) (fun _ _ => 1) 1 (fun _ => continuousOn_const)
    (fun _ y _ => S.abs_one_le_log_rW y)
    (TendstoUniformlyOn.tendstoLocallyUniformlyOn (by
      refine Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_
      exact Filter.Eventually.of_forall fun _ _ _ => by simpa using hε))
  refine ⟨hlim.1, ?_⟩
  have hT : Tendsto (fun t => mInt S.A (fun i => S.potT (w i) t) (fun _ => 1))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (mInt S.A (fun i => S.potH (w i)) (fun _ => 1))) :=
    hlim.2
  have hc : Tendsto (fun t => mInt S.A (fun i => S.potT (w i) t) (fun _ => 1))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (S.degNum w)) :=
    tendsto_const_nhds.congr' ((S.eventually_mInt_potT w).mono fun _ h => h.symm)
  exact tendsto_nhds_unique hT hc

end GlobalTheory.CompanionTheory.Ar.PB
end

