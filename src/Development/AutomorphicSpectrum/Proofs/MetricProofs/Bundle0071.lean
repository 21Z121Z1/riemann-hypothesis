import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockMapFrameRestrictionRegular
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0057
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0067
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0035
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0043
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0038
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0068
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import Development.WeilBound.CoreStatements.PluriharmonicCharts.XAnConj
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0026
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0042
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticSeventh
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0044

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BasePartYvEqAlgebraMapXb
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.YBase

theorem det_genU (Ω : Type) [Field Ω] {S : Type} (r : S → ℕ) (s : S) : (genU Ω r s).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · refine Finset.prod_eq_one fun i _ => ?_
    simp [genU]
  · intro l k hlk
    have hlk' : l < k := hlk
    have h1 : ¬ k < l := not_lt.2 hlk'.le
    have h2 : l ≠ k := hlk'.ne
    simp [genU, h1, h2]

theorem det_map_mul_submatrix {Ω L : Type} [Field Ω] [Field L] (f : Ω →+* L) {n m r : ℕ} (hm : m = r) (h : m ≤ r)
    (A : Matrix (Fin n) (Fin r) Ω) (U : Matrix (Fin r) (Fin r) L) (hU : U.det = 1) (J : Fin m → Fin n) :
    ((A.map f * U).submatrix J (Fin.castLE h)).det = f ((A.submatrix J (Fin.castLE h)).det) := by
  subst hm
  have hc : (Fin.castLE h : Fin m → Fin m) = id := by
    funext i
    rfl
  rw [hc, RingHom.map_det]
  have : (A.map f * U).submatrix J id = (f.mapMatrix (A.submatrix J id)) * U := by
    ext a b
    simp [Matrix.mul_apply]
  rw [this, Matrix.det_mul, hU, mul_one]

variable {Ψ : Type} {p q : ℕ}

theorem full_of_noBlock (K₀ : Type) (t : StepIx Ψ p q)
    (h : ∀ r, blkF Ψ p q K₀ r ≠ some (.inr t)) : (t.2 : ℕ) + 1 = rk Ψ p q t.1 := by
  obtain ⟨s, i⟩ := t
  rcases s with τ | τ
  · have hi : (i : ℕ) < p := i.2
    by_contra hne
    have hne' : (i : ℕ) + 1 ≠ p := hne
    refine h (τ, ⟨i, by omega⟩) ?_
    have hp : IsProperStep (p + q) p (⟨i, by omega⟩ : Fin (p + q)) := ⟨hne', by
      show (i : ℕ) + 1 ≠ p + q
      omega⟩
    simp only [blkF, if_pos hp, stepOf]
    simp [hi]
    rfl
  · have hi : (i : ℕ) < q := i.2
    by_contra hne
    have hne' : (i : ℕ) + 1 ≠ q := hne
    refine h (τ, ⟨p + i, by omega⟩) ?_
    have hp : IsProperStep (p + q) p (⟨p + i, by omega⟩ : Fin (p + q)) := ⟨by
      show p + (i : ℕ) + 1 ≠ p
      omega, by
      show p + (i : ℕ) + 1 ≠ p + q
      omega⟩
    simp only [blkF, if_pos hp, stepOf]
    simp
    rfl

theorem basePart_yv : ∀ (Ψ : Type) [Fintype Ψ] (p q : ℕ) (Ω : Type) [Field Ω] (n : Ψ ⊕ Ψ → ℕ)
    (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type)
    [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω), ∀ r,
    basePart (blkF Ψ p q K₀) (yv A x₀) r = algebraMap Ω (GenField Ω (rk Ψ p q)) (xb A x₀ r) := by
  intro Ψ _ p q Ω _ n A K₀ _ J₀ _ x₀ r
  obtain ⟨⟨k, hk⟩, i⟩ := r
  rcases k with k | t
  · rfl
  · exact det_map_mul_submatrix (algebraMap Ω (GenField Ω (rk Ψ p q))) (full_of_noBlock K₀ t hk) t.2.2 (A t.1)
      (genU Ω (rk Ψ p q) t.1) (det_genU Ω _ _) i

end GlobalTheory.CompanionTheory.Ar.PB.FMX.YBase
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BlkFProperStepInjectiveBlockDiag
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.Blocks

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

theorem blkF_eq_none_iff (Ψ : Type) (p q : ℕ) (K₀ : Type) (r : Ψ × Fin (p + q)) :
    blkF Ψ p q K₀ r = none ↔ ¬ IsProperStep (p + q) p r.2 := by
  unfold blkF
  split_ifs with h <;> simp [h]

theorem stepOf_injective (Ψ : Type) (p q : ℕ) : Function.Injective (stepOf Ψ p q) := by
  rintro ⟨τ, i⟩ ⟨τ', i'⟩ h
  have hi := i.2
  have hi' := i'.2
  by_cases h₁ : (i : ℕ) < p <;> by_cases h₂ : (i' : ℕ) < p
  · simp only [stepOf, dif_pos h₁, dif_pos h₂] at h
    have e₁ : τ = τ' := Sum.inl.inj (congrArg Sigma.fst h)
    have e₂ := congrArg (fun t : StepIx Ψ p q => (t.2 : ℕ)) h
    exact Prod.ext e₁ (Fin.ext e₂)
  · simp only [stepOf, dif_pos h₁, dif_neg h₂] at h
    exact absurd (congrArg Sigma.fst h) (by simp)
  · simp only [stepOf, dif_neg h₁, dif_pos h₂] at h
    exact absurd (congrArg Sigma.fst h) (by simp)
  · simp only [stepOf, dif_neg h₁, dif_neg h₂] at h
    have e₁ : τ = τ' := Sum.inr.inj (congrArg Sigma.fst h)
    have e₂ : (i : ℕ) - p = (i' : ℕ) - p := congrArg (fun t : StepIx Ψ p q => (t.2 : ℕ)) h
    exact Prod.ext e₁ (Fin.ext (by show (i : ℕ) = (i' : ℕ); omega))

theorem blkF_inj (Ψ : Type) (p q : ℕ) (K₀ : Type) (r r' : Ψ × Fin (p + q)) (k : K₀ ⊕ StepIx Ψ p q)
    (h : blkF Ψ p q K₀ r = some k) (h' : blkF Ψ p q K₀ r' = some k) : r = r' := by
  unfold blkF at h h'
  split_ifs at h h'
  apply stepOf_injective Ψ p q
  have e := (Option.some.inj h).trans (Option.some.inj h').symm
  exact Sum.inr.inj e

theorem fromBlocks_isBlockDiag {R : Type} [CommRing R] (p q : ℕ) (A : Matrix (Fin q) (Fin q) R)
    (B : Matrix (Fin p) (Fin p) R) :
    IsBlockDiag p ((Matrix.fromBlocks A 0 0 B).submatrix (blockEquiv p q).symm (blockEquiv p q).symm) := by
  intro a b hab
  obtain ⟨x, rfl⟩ := (blockEquiv p q).surjective a
  obtain ⟨y, rfl⟩ := (blockEquiv p q).surjective b
  simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases x with x | x <;> rcases y with y | y
  · exfalso
    apply hab
    have hx := x.2
    have hy := y.2
    show ((x : ℕ) < _ ↔ (y : ℕ) < _)
    omega
  · rfl
  · rfl
  · exfalso
    apply hab
    show (q + (x : ℕ) < _ ↔ q + (y : ℕ) < _)
    omega

theorem gMat_isBlockDiag (Ψ : Type) (p q : ℕ) (Ω : Type) [Field Ω] (τ : Ψ) :
    IsBlockDiag p (gMat p q Ω τ) :=
  fromBlocks_isBlockDiag p q (genU Ω (rk Ψ p q) (.inr τ)) (genU Ω (rk Ψ p q) (.inl τ))

theorem blocks_main : ∀ (Ψ : Type) [Fintype Ψ] (p q : ℕ) (Ω : Type) [Field Ω] (K₀ : Type),
    (∀ r, blkF Ψ p q K₀ r = none ↔ ¬ IsProperStep (p + q) p r.2) ∧
    (∀ r r' k, blkF Ψ p q K₀ r = some k → blkF Ψ p q K₀ r' = some k → r = r') ∧
    ∀ τ : Ψ, IsBlockDiag p (gMat p q Ω τ) :=
  fun Ψ _ p q Ω _ K₀ => ⟨blkF_eq_none_iff Ψ p q K₀, blkF_inj Ψ p q K₀, gMat_isBlockDiag Ψ p q Ω⟩

end GlobalTheory.CompanionTheory.Ar.PB.FMX.Blocks
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockMapFrameRestrictionRegularStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockMap_frame_restriction_regular : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (keep : Ψ × Fin N → Prop) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)), IsBlockMap κ v → (∀ k, k ∈ Set.range κ ↔ ((∀ p, M.blk p ≠ some k) ∨ ∃ p, keep p ∧ M.blk p = some k)) → ∀ (F : FrameData ι Ψ N M.Ω M.blk) (z : (Σ k, ιk k) → ℂ), M.IsFrame F → z ∈ mcPts (mCoordIdeal (y ∘ v)) → M.GoodAt F (mCoordIdeal (pBase M v z)) → (∀ k, pBase M v z ⟨k, F.c k⟩ = 1) → ∃ H : Ψ → Matrix (Fin N) (Fin N) ℂ, (∀ τ, IsBlockDiag j (H τ) ∧ (H τ).det ≠ 0) ∧ ∀ p k, keep p → M.blk p = some k → ∃ α : ℂ, α ≠ 0 ∧ ∀ m : ι k, upV v z ⟨k, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) (pBase M v z) * minorIJ (H p.1) I (stepCols N j p.2) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.PFl.Fwd.main | exact GlobalTheory.CompanionTheory.Ar.PB.PFl.Fwd.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.PFl.Fwd.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockMapFrameRestrictionStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockMap_frame_restriction : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (keep : Ψ × Fin N → Prop) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)), IsBlockMap κ v → (∀ k, k ∈ Set.range κ ↔ ((∀ p, M.blk p ≠ some k) ∨ ∃ p, keep p ∧ M.blk p = some k)) → (∀ z ∈ mcPts (mCoordIdeal (y ∘ v)), pBase M v z ∈ mcPts (mCoordIdeal M.x)) ∧ ∀ z z' : (Σ k, ιk k) → ℂ, SameOrbit z z' → SameOrbit (pBase M v z) (pBase M v z') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.PFl.PtsBase.main | exact GlobalTheory.CompanionTheory.Ar.PB.PFl.PtsBase.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.PFl.PtsBase.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockMetricGrassmannChartLocal
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW.FlagPoint

theorem stepCols_ne_empty {N j : ℕ} (hj : j ≤ N) (i : Fin N) : stepCols N j i ≠ ∅ := by
  intro h
  have hi' := i.2
  by_cases hi : (i : ℕ) + 1 ≤ j
  · have hm : (⟨N - j, by omega⟩ : Fin N) ∈ stepCols N j i := by
      simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_pos hi]
      constructor <;> simp
    simp [h] at hm
  · have hm : (⟨0, by omega⟩ : Fin N) ∈ stepCols N j i := by
      simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_neg hi]
      show 0 < (i : ℕ) + 1 - j
      omega
    simp [h] at hm

theorem val_sum {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal x)) {α : Type} (s : Finset α)
    (f : α → Ω) (hf : ∀ a ∈ s, RegAt x (mCoordIdeal z) (f a)) :
    RegAt x (mCoordIdeal z) (∑ a ∈ s, f a) ∧ valAt x (∑ a ∈ s, f a) z = ∑ a ∈ s, valAt x (f a) z := by
  have R := GlobalTheory.CompanionTheory.Ar.PB.ValRing.regAt_valAt_ring K ι Ω x z hz
  induction s using Finset.induction_on with
  | empty => simpa using ⟨R.1, R.2.2.1⟩
  | insert a s ha ih =>
    have ih' := ih fun b hb => hf b (Finset.mem_insert_of_mem hb)
    have h := R.2.2.2.2 (f a) _ (hf a (Finset.mem_insert_self _ _)) ih'.1
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact ⟨h.2.1, h.2.2.2.trans (by rw [ih'.2])⟩

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ]
    (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ)
    (BM : BaseMetric M n) (p : Ψ × Fin N) (k₀ : K) (l : Fin BM.q) (x₀ : BM.Rb.X) (z : (Σ k, ι k) → ℂ),
    M.blk p = some k₀ → x₀ ∈ BM.O l → z ∈ mcPts (mCoordIdeal y) →
    SameOrbit (basePart M.blk z) (BM.Rb.lift x₀ x₀) →
    ∃ (h : Matrix (Fin N) (Fin N) ℂ) (a : ℂ), IsBlockDiag j h ∧ h.det ≠ 0 ∧ a ≠ 0 ∧
      (∀ I, IsStepRows N j p.2 I → plk M (BM.F l) k₀ z I = a * minorIJ h I (stepCols N j p.2)) ∧
      ∀ m : ι k₀, z ⟨k₀, m⟩ =
        a * ∑ I, valAt M.x ((BM.F l).u ⟨k₀, m⟩ I) (basePart M.blk z) * minorIJ h I (stepCols N j p.2) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM p k₀ l x₀ z hblk hx hz horb
  obtain ⟨F, hFe⟩ : ∃ F, F = BM.F l := ⟨_, rfl⟩
  rw [← hFe]
  have hF : M.IsFrame F := hFe ▸ BM.isFrame l
  have hG₀ : M.GoodAt F (mCoordIdeal (BM.Rb.lift x₀ x₀)) := hFe ▸ BM.good l x₀ hx
  obtain ⟨hp1, -, hp3⟩ := GlobalTheory.T.flag_model_base_projection_points K ι Φ y Ψ N j M
  obtain ⟨zb, hzbe⟩ : ∃ zb, zb = basePart M.blk z := ⟨_, rfl⟩
  rw [← hzbe] at horb ⊢
  have hzbm : zb ∈ mcPts (mCoordIdeal M.x) := hzbe ▸ hp1 z hz
  obtain ⟨c₀, hc₀, hc₀e⟩ := horb
  have hG : M.GoodAt F (mCoordIdeal zb) := by
    have e : mCoordIdeal zb = mCoordIdeal (BM.Rb.lift x₀ x₀) := by
      rw [hc₀e]
      exact (GlobalTheory.CompanionTheory.Ar.PB.StepW.TorusAct.main _ _ _ M.x (BM.Rb.lift x₀ x₀) c₀ hc₀).1
    rw [e]
    exact hG₀
  have hne : ∀ k : NonPluckerBlocks M.blk, zb ⟨k, F.c k⟩ ≠ 0 := fun k h0 => hG.1 k (by
    show mConeMap zb (X ⟨k, F.c k⟩) = 0
    rw [mConeMap, aeval_X, h0, map_zero, zero_mul])
  let c : K → ℂ := fun k =>
    if h : ∀ p', M.blk p' ≠ some k then (zb ⟨⟨k, h⟩, F.c ⟨k, h⟩⟩)⁻¹ else 1
  have hck : ∀ k : NonPluckerBlocks M.blk, c k.1 = (zb ⟨k, F.c k⟩)⁻¹ := fun k => dif_pos k.2
  have hc : ∀ k, c k ≠ 0 := fun k => by
    by_cases h : ∀ p', M.blk p' ≠ some k
    · rw [hck ⟨k, h⟩]
      exact inv_ne_zero (hne ⟨k, h⟩)
    · have : c k = 1 := dif_neg h
      rw [this]
      exact one_ne_zero
  have hck₀ : c k₀ = 1 := dif_neg fun h => h p hblk
  let z₁ : (Σ k, ι k) → ℂ := fun q => c q.1 * z q
  have hz₁ : z₁ ∈ mcPts (mCoordIdeal y) := ((GlobalTheory.CompanionTheory.Ar.PB.StepW.TorusAct.main K ι Φ y z c hc).2 hz).1
  let cb : NonPluckerBlocks M.blk → ℂ := fun k => c k.1
  have hb₁ : basePart M.blk z₁ = fun q => cb q.1 * zb q := by
    rw [hzbe]
    rfl
  obtain ⟨hT1, hT2⟩ :=
    GlobalTheory.CompanionTheory.Ar.PB.StepW.TorusAct.main (NonPluckerBlocks M.blk) (baseIdx ι M.blk) M.Ω M.x zb cb fun k => hc k.1
  obtain ⟨-, hval⟩ := hT2 hzbm
  have hG₁ : M.GoodAt F (mCoordIdeal (basePart M.blk z₁)) := by
    rw [hb₁, hT1]
    exact hG
  have hnorm : ∀ k, basePart M.blk z₁ ⟨k, F.c k⟩ = 1 := fun k => by
    rw [hb₁]
    show c k.1 * zb ⟨k, F.c k⟩ = 1
    rw [hck, inv_mul_cancel₀ (hne k)]
  obtain ⟨hh, -, hτ, hstep⟩ := (hp3 F hF z₁ (hp1 z₁ hz₁) hG₁ hnorm).1 hz₁
  obtain ⟨a, ha, hza⟩ := hstep p k₀ hblk
  have hvals : ∀ s, valAt M.x s (basePart M.blk z₁) = valAt M.x s zb := fun s => by
    rw [hb₁]
    exact hval s
  have hzk : ∀ m : ι k₀, z ⟨k₀, m⟩ =
      a * ∑ I, valAt M.x (F.u ⟨k₀, m⟩ I) zb * minorIJ (hh p.1) I (stepCols N j p.2) := fun m => by
    have e : z₁ ⟨k₀, m⟩ = z ⟨k₀, m⟩ := by
      show c k₀ * _ = _
      rw [hck₀, one_mul]
    have := hza m
    rw [e] at this
    simpa only [hvals] using this
  refine ⟨hh p.1, a, (hτ p.1).1, (hτ p.1).2, ha, fun I hI => ?_, hzk⟩
  have R := GlobalTheory.CompanionTheory.Ar.PB.ValRing.regAt_valAt_ring _ _ _ M.x zb hzbm
  have hδ : ∀ I', IsStepRows N j p.2 I' →
      ∑ m : ι k₀, valAt M.x (F.u' I ⟨k₀, m⟩) zb * valAt M.x (F.u ⟨k₀, m⟩ I') zb = if I = I' then 1 else 0 := by
    intro I' hI'
    have h1 := (val_sum hzbm Finset.univ (fun m : ι k₀ => F.u' I ⟨k₀, m⟩ * F.u ⟨k₀, m⟩ I') fun m _ =>
      (R.2.2.2.2 _ _ (hG.2.1 ⟨k₀, m⟩ I).2 (hG.2.1 ⟨k₀, m⟩ I').1).1).2
    rw [hF.2.2.1 p k₀ hblk I I' hI hI'] at h1
    have h2 : ∀ m : ι k₀, valAt M.x (F.u' I ⟨k₀, m⟩ * F.u ⟨k₀, m⟩ I') zb =
        valAt M.x (F.u' I ⟨k₀, m⟩) zb * valAt M.x (F.u ⟨k₀, m⟩ I') zb := fun m =>
      (R.2.2.2.2 _ _ (hG.2.1 ⟨k₀, m⟩ I).2 (hG.2.1 ⟨k₀, m⟩ I').1).2.2.1
    simp only [h2] at h1
    rw [← h1]
    split_ifs
    · exact R.2.2.2.1
    · exact R.2.2.1
  have hmin : ∀ I', ¬ IsStepRows N j p.2 I' → minorIJ (hh p.1) I' (stepCols N j p.2) = 0 := fun I' hI' =>
    ((GlobalTheory.T.block_diagonal_minor_vanishing ℂ N j p.2 M.j_le).2.1 (hh p.1) I' (hτ p.1).1 hI').resolve_right
      (stepCols_ne_empty M.j_le p.2)
  have hsum : ∑ I', (∑ m : ι k₀, valAt M.x (F.u' I ⟨k₀, m⟩) zb * valAt M.x (F.u ⟨k₀, m⟩ I') zb) *
      minorIJ (hh p.1) I' (stepCols N j p.2) = minorIJ (hh p.1) I (stepCols N j p.2) := by
    rw [Finset.sum_eq_single I]
    · rw [hδ I hI, if_pos rfl, one_mul]
    · intro I' _ hne'
      by_cases hs : IsStepRows N j p.2 I'
      · rw [hδ I' hs, if_neg (Ne.symm hne'), zero_mul]
      · rw [hmin I' hs, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ I) h
  have hplk : plk M F k₀ z I = ∑ m : ι k₀, valAt M.x (F.u' I ⟨k₀, m⟩) zb * z ⟨k₀, m⟩ := by
    rw [hzbe]
    rfl
  rw [hplk, ← hsum, Finset.mul_sum]
  simp only [hzk, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun I' _ => Finset.sum_congr rfl fun m _ => ?_
  ring

end GlobalTheory.CompanionTheory.Ar.PB.StepW.FlagPoint
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ConjugationInvariantSingularPotential
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem an_conj_symmetrise : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (Θ : LocPot X) (L : LocPot X) (s : X → X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X), IsPotential A L → IsSection A L s → IsSNC A L s m W → (∀ y, logNormSec L s y ≤ 0) → IsPotential A Θ → IsPosPot A Θ → ∀ (c : X → X), Continuous c → (∀ x, c (c x) = x) → (∀ j k, AnalyticOnNhd ℂ (fun z => star (A.chart k (c ((A.chart j).symm z)))) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (c ⁻¹' (A.chart k).source))) → (∀ y, c y ∈ bdry s ↔ y ∈ bdry s) → (∀ y, rW L s (c y) = rW L s y) → ∀ (th : LocPot X) (ph : X → ℝ) (phT : ℝ → X → ℝ) (C t₀ : ℝ), IsPotential A th → (∀ x, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∃ G : X → ℂ, A.HoloOn V G ∧ ∀ y ∈ V, th.φ (c x) (c y) - th.φ x y = (G y).re) → (∀ y ∉ bdry s, ph (c y) = ph y) → IsRegFamily A Θ L s th ph phT C t₀ → IsRegFamilyC2 A s ph phT → ∃ C' t₀' : ℝ, IsRegFamily A Θ L s th ph (fun t y => (phT t y + phT t (c y)) / 2) C' t₀' ∧ IsRegFamilyC2 A s ph fun t y => (phT t y + phT t (c y)) / 2 :=
  @PositivityTheory.Xgp.t_an_conj

end GlobalTheory.CompanionTheory.Ar.PB
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.DetFacGMatEqOne
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.DetG

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

theorem det_genU (Ω : Type) [Field Ω] {S : Type} (r : S → ℕ) (s : S) : (genU Ω r s).det = 1 := by
  rw [det_of_lowerTriangular (genU Ω r s) fun a b h => ?_]
  · refine Finset.prod_eq_one fun a _ => ?_
    simp [genU]
  · have h' : a < b := h
    simp [genU, not_lt.2 h'.le, h'.ne]

variable (Ψ : Type) (p q : ℕ) (Ω : Type) [Field Ω] (τ : Ψ)

theorem wBlock_gMat : wBlock (gMat p q Ω τ) = genU Ω (rk Ψ p q) (.inl τ) := by
  ext a b
  have ea : (blockEquiv p q).symm (wEmb p q a) = .inr a := by
    rw [← blockEquiv_inr, Equiv.symm_apply_apply]
  have eb : (blockEquiv p q).symm (wEmb p q b) = .inr b := by
    rw [← blockEquiv_inr, Equiv.symm_apply_apply]
  change Matrix.fromBlocks (genU Ω (rk Ψ p q) (.inr τ)) 0 0 (genU Ω (rk Ψ p q) (.inl τ))
    ((blockEquiv p q).symm (wEmb p q a)) ((blockEquiv p q).symm (wEmb p q b)) = _
  rw [ea, eb]
  rfl

theorem omBlock_gMat : omBlock (gMat p q Ω τ) = genU Ω (rk Ψ p q) (.inr τ) := by
  ext a b
  have ea : (blockEquiv p q).symm (omEmb p q a) = .inl a := by
    rw [← blockEquiv_inl, Equiv.symm_apply_apply]
  have eb : (blockEquiv p q).symm (omEmb p q b) = .inl b := by
    rw [← blockEquiv_inl, Equiv.symm_apply_apply]
  change Matrix.fromBlocks (genU Ω (rk Ψ p q) (.inr τ)) 0 0 (genU Ω (rk Ψ p q) (.inl τ))
    ((blockEquiv p q).symm (omEmb p q a)) ((blockEquiv p q).symm (omEmb p q b)) = _
  rw [ea, eb]
  rfl

theorem detFac_gMat (Ψ : Type) (p q : ℕ) (Ω : Type) [Field Ω] (τ : Ψ) (i : Fin (p + q)) :
    detFac p i (gMat p q Ω τ) = 1 := by
  have hw : minorIJ (gMat p q Ω τ) (wIdx (p + q) p) (wIdx (p + q) p) = 1 := by
    rw [minorIJ_wIdx, wBlock_gMat]
    exact det_genU Ω (rk Ψ p q) (.inl τ)
  have ho : minorIJ (gMat p q Ω τ) (omIdx (p + q) p) (omIdx (p + q) p) = 1 := by
    rw [minorIJ_omIdx, omBlock_gMat]
    exact det_genU Ω (rk Ψ p q) (.inr τ)
  simp only [detFac, hw, ho, ite_self, mul_one]

end GlobalTheory.CompanionTheory.Ar.PB.FMX.DetG
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsLocalTwistTrivialization
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.RootsBase

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

theorem frame_values :
    ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type) (x : κ → Ω) (L : Lat ξ E) (m r n : ℕ) (V : Submodule Ω E) (φ : Fin n → Module.Dual Ω E) (cb : Fin r → E), IsTwistGen ξ x L m φ → L.IsVB r V → LinearIndependent Ω cb → Submodule.span Ω (Set.range cb) = V → ∀ (p : Cpt ξ) (c : κ), InChart ξ x c p → ∃ (T : Matrix (Fin r) (Fin r) Ω) (C : Matrix (Fin r) (Fin n) Ω), IsUnit T.det ∧ L.IsFrameAt (colFrame cb T) p ∧ (∀ a b, ((Matrix.of fun a b => φ a (cb b)) * T) a b / x c ^ m ∈ regAt ξ p) ∧ (∀ a b, C a b ∈ regAt ξ p) ∧ ∀ a b, ∑ k, C a k * (((Matrix.of fun a b => φ a (cb b)) * T) k b / x c ^ m) = if a = b then 1 else 0 := by
  intro X Ω _ ξ E _ _ κ x L m r n V φ cb hG hV hli hsp p c hc
  obtain ⟨U, hU, b, hbsp, hb⟩ := hV p (Set.mem_univ p)
  have hf : L.IsFrameAt b p := hb p (Set.mem_univ p) hU
  have h1 : ∀ l, ∃ t : Fin r → Ω, ∑ a, t a • cb a = b l := fun l => by
    have : b l ∈ Submodule.span Ω (Set.range cb) := by
      rw [hsp, ← hbsp]; exact Submodule.subset_span ⟨l, rfl⟩
    exact (Submodule.mem_span_range_iff_exists_fun Ω).1 this
  have h2 : ∀ l, ∃ t : Fin r → Ω, ∑ a, t a • b a = cb l := fun l => by
    have : cb l ∈ Submodule.span Ω (Set.range b) := by
      rw [hbsp, ← hsp]; exact Submodule.subset_span ⟨l, rfl⟩
    exact (Submodule.mem_span_range_iff_exists_fun Ω).1 this
  choose t ht using h1
  choose t' ht' using h2
  let T : Matrix (Fin r) (Fin r) Ω := Matrix.of fun a l => t l a
  let T' : Matrix (Fin r) (Fin r) Ω := Matrix.of fun a l => t' l a
  have hT : colFrame cb T = b := by
    funext l; exact ht l
  have hT' : colFrame b T' = cb := by
    funext l; exact ht' l
  have hmul : T * T' = 1 := by
    have e : colFrame cb (T * T') = colFrame cb (1 : Matrix (Fin r) (Fin r) Ω) := by
      rw [colFrame_mul, hT, hT', colFrame_one]
    ext a l
    have h3 := congrFun e l
    simp only [colFrame] at h3
    have h0 := (Fintype.linearIndependent_iff.1 hli) (fun a => (T * T') a l - (1 : Matrix _ _ Ω) a l)
      (by simp only [sub_smul, Finset.sum_sub_distrib, h3, sub_self]) a
    exact sub_eq_zero.1 h0
  have hdet : IsUnit T.det := Matrix.isUnit_det_of_right_inverse hmul
  have hval : ∀ a l, ((Matrix.of fun a b => φ a (cb b)) * T) a l = φ a (b l) := by
    intro a l
    rw [← hT]
    simp [Matrix.mul_apply, colFrame, mul_comm]
  have hmem : ∀ l, b l ∈ L p := fun l => by
    rw [hf.2]; exact Submodule.subset_span ⟨l, rfl⟩
  have hw : ∀ l, ∃ w : Module.Dual Ω E, ∀ k, w (b k) = if l = k then 1 else 0 := fun l => by
    obtain ⟨w, h1, h0⟩ := GlobalTheory.CompanionTheory.Ar.FlagGrGen.exists_coord hf.1 l
    refine ⟨w, fun k => ?_⟩
    split_ifs with h
    · rw [← h]; exact h1
    · exact h0 k (Ne.symm h)
  choose w hw using hw
  have hwreg : ∀ l, ∀ e ∈ L p, w l e ∈ regAt ξ p := by
    intro l e he
    rw [hf.2] at he
    induction he using Submodule.span_induction with
    | mem e h =>
      obtain ⟨k, rfl⟩ := h
      rw [hw]
      split_ifs
      exacts [one_mem _, zero_mem _]
    | zero => simp [zero_mem]
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a e _ he =>
      have h4 : w l (a • e) = (a : Ω) * w l e := by rw [Subring.smul_def, map_smul, smul_eq_mul]
      rw [h4]; exact mul_mem a.2 he
  choose g hg hg' using fun l => hG.2 p c hc (w l) (hwreg l)
  refine ⟨T, Matrix.of g, hdet, ?_, ?_, ?_, ?_⟩
  · rw [hT]; exact hf
  · intro a l; rw [hval]; exact hG.1 a p c hc _ (hmem l)
  · intro a j; exact hg a j
  · intro a l
    simp only [hval, Matrix.of_apply]
    rw [← hg' a (b l) (hmem l), hw]

end GlobalTheory.CompanionTheory.Ar.PB.FMX.RootsBase
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartSeventhStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_adjacent_chart_seventh : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin (d + 2)), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h → ∀ z ∈ wO M Rb τ a k₀ ca cb F kb V r h, ∀ z' ∈ mcPts (wP M τ a k₀ ca cb), SameOrbit z' z → z' ∈ wO M Rb τ a k₀ ca cb F kb V r h ∧ wRho M Rb τ k₀ ca cb F kb r h ε z' = wRho M Rb τ k₀ ca cb F kb r h ε z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WMan.Orb.main | exact GlobalTheory.CompanionTheory.Ar.PB.WMan.Orb.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WMan.Orb.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticSeventhStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_cover_arithmetic_seventh : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 2) → IsArithVar (mCoordIdeal y') (d + 2) → ∃ (D : MRing (baseIdx ι M.blk)) (a : NonPluckerBlocks M.blk → ℕ), IsMultiHomog D a ∧ D ∉ mCoordIdeal M.x ∧ ∀ b' ∈ mcPts (mCoordIdeal M'.x), ∀ wb, SameOrbit wb (b' ∘ Cv.v) → eval wb (map (Int.castRingHom ℂ) D) ≠ 0 → ∃ (V : Set ((Σ k, baseIdx ι M.blk k) → ℂ)) (V' : Set ((Σ k, baseIdx ι' M'.blk k) → ℂ)) (s : ((Σ k, baseIdx ι M.blk k) → ℂ) → (Σ k, baseIdx ι' M'.blk k) → ℂ), IsOpen V ∧ wb ∈ V ∧ IsOpen V' ∧ b' ∈ V' ∧ AnalyticOnNhd ℂ s V ∧ ∀ b'' ∈ V' ∩ mcPts (mCoordIdeal M'.x), ∀ w' ∈ V, SameOrbit w' (b'' ∘ Cv.v) → SameOrbit (s w') b'' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.BaseEtale.main | exact GlobalTheory.CompanionTheory.Ar.PB.BaseEtale.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.BaseEtale.main <;> assumption)
end

