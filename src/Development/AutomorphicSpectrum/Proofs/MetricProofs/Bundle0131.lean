import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0042
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogPeriodStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0072
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0057
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0071
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0127
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0035
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0128
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0025
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0014
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0004
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0038
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0037
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0014
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDensityNonnegOffNullSet
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0123
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MultihomogeneousLiftToJoin
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridge
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MetricsProjectionFormulaNef
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0023

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartEighth
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan

theorem continuousWithinAt_valAt_of_regAt {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type}
    [Field Ω] {x : (Σ k, ι k) → Ω} {zb : (Σ k, ι k) → ℂ} (hz : zb ∈ mcPts (mCoordIdeal x)) {s : Ω}
    (hs : RegAt x (mCoordIdeal zb) s) : ContinuousWithinAt (valAt x s) (mcPts (mCoordIdeal x)) zb := by
  obtain ⟨d, g, h, hg, hh, hn, heq⟩ := hs
  have hy := GlobalTheory.CompanionTheory.Ar.PB.ValRing.aeval_ne_zero_of_notMem hz hh hn
  have h0 := GlobalTheory.CompanionTheory.Ar.PB.ValRing.eval_ne_zero_of_notMem hh hn
  have cg : Continuous fun w : (Σ k, ι k) → ℂ => eval w (map (Int.castRingHom ℂ) g) :=
    MvPolynomial.continuous_eval _
  have ch : Continuous fun w : (Σ k, ι k) → ℂ => eval w (map (Int.castRingHom ℂ) h) :=
    MvPolynomial.continuous_eval _
  have hnear : valAt x s =ᶠ[𝓝[mcPts (mCoordIdeal x)] zb]
      fun w => eval w (map (Int.castRingHom ℂ) g) / eval w (map (Int.castRingHom ℂ) h) := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (ch.continuousAt.eventually_ne h0)] with w hw hw0
    exact valAt_eq hw ⟨d, g, h, hg, hh, hy, heq, hw0, rfl⟩
  have hat : valAt x s zb = eval zb (map (Int.castRingHom ℂ) g) / eval zb (map (Int.castRingHom ℂ) h) :=
    valAt_eq hz ⟨d, g, h, hg, hh, hy, heq, h0, rfl⟩
  exact (cg.continuousAt.div ch.continuousAt h0).continuousWithinAt.congr_of_eventuallyEq hnear hat

section Flag

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

theorem twMinor_continuousWithinAt (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) {Z : Type}
    [TopologicalSpace Z] {S : Set Z} {z₀ : Z} {β : Z → (Σ k, baseIdx ι M.blk k) → ℂ} {P : Z → (Σ k, ι k) → ℂ}
    (hβ : ContinuousWithinAt β S z₀) (hS : Set.MapsTo β S (mcPts (mCoordIdeal M.x)))
    (hz : β z₀ ∈ mcPts (mCoordIdeal M.x)) (hG : M.GoodAt F (mCoordIdeal (β z₀)))
    (hP : ContinuousWithinAt P S z₀) (i : Fin N) (k : K) (g : Matrix (Fin N) (Fin N) ℂ) (J : Finset (Fin N)) :
    ContinuousWithinAt (fun z => twMinor M F (β z) i k g (P z) J) S z₀ := by
  simp only [twMinor, pluck]
  refine tendsto_finset_sum _ fun I _ => Tendsto.const_mul _ (tendsto_finset_sum _ fun m _ => Tendsto.mul ?_ ?_)
  · exact ContinuousWithinAt.comp (g := valAt M.x (F.u' I ⟨k, m⟩))
      (continuousWithinAt_valAt_of_regAt hz (hG.2.1 _ _).2) hβ hS
  · exact ((continuous_apply (⟨k, m⟩ : Σ k, ι k)).continuousAt.comp_continuousWithinAt hP)

theorem wRho_continuousOn : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin (d + 2)), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h → ContinuousOn (wRho M Rb τ k₀ ca cb F kb r h ε) (wO M Rb τ a k₀ ca cb F kb V r h) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε H
  obtain ⟨hb, hab, hk, hca, hcb, hy, hF, hB, horb, hr, hh⟩ := H
  obtain ⟨hVo, hVt, -, -, hbl⟩ := hB
  have hbase : Set.MapsTo (baseOf M k₀) (wO M Rb τ a k₀ ca cb F kb V r h) (mcPts (mCoordIdeal M.x)) := fun z hz =>
    GlobalTheory.CompanionTheory.Ar.PB.CPts.base_mem M (GlobalTheory.CompanionTheory.Ar.PB.CPts.comp_mem_mcPts (GlobalTheory.CompanionTheory.Ar.PB.WSq.Pts.isBlockMap_v₀ k₀)
      (algebraMap Φ (RatFunc Φ)) (funext fun _ => rfl) hz.1)
  have cB : Continuous (baseOf M k₀) := continuous_pi fun q => continuous_apply _
  have cF : Continuous (fstPt (ι := ι) k₀) := continuous_pi fun q => continuous_apply _
  have cS : Continuous (sndPt (ι := ι) k₀) := continuous_pi fun q => continuous_apply _
  have hgood : ∀ z ∈ wO M Rb τ a k₀ ca cb F kb V r h, M.GoodAt F (mCoordIdeal (baseOf M k₀ z)) := by
    intro z hz
    have h3 := (hbl _ hz.2.2.1).2.2
    rw [(Rb.A.chart kb).left_inv hz.2.1] at h3
    have e := orbit_trans (orbit_symm (horb _ (hbase hz))) h3.2
    rw [GlobalTheory.CompanionTheory.Ar.PB.CovMap.mCoordIdeal_eq_of_sameOrbit e]
    exact h3.1
  have cLow : ∀ (P : ((Σ o : Option K, ι (o.getD k₀)) → ℂ) → (Σ k, ι k) → ℂ), Continuous P → ∀ (τ' : Ψ) (a' b' : Fin N),
      ∀ z ∈ wO M Rb τ a k₀ ca cb F kb V r h, (∀ k, M.blk (τ', stepOf N j b') = some k →
        twMinor M F (baseOf M k₀ z) (stepOf N j b') k (h τ')⁻¹ (P z) (stepCols N j (stepOf N j b')) ≠ 0) →
      ContinuousWithinAt (fun z => lowRead M F (baseOf M k₀ z) h (P z) τ' a' b')
        (wO M Rb τ a k₀ ca cb F kb V r h) z := by
    intro P hP τ' a' b' z hz hne
    have cT := fun (k : K) (J : Finset (Fin N)) => twMinor_continuousWithinAt M F cB.continuousWithinAt hbase (hbase hz)
      (hgood z hz) hP.continuousWithinAt (stepOf N j b') k (h τ')⁻¹ J
    cases e : M.blk (τ', stepOf N j b') with
    | none =>
      simp only [lowRead, e, Option.elim_none]
      exact continuousWithinAt_const
    | some k =>
      simp only [lowRead, e, Option.elim_some]
      exact (cT k _).div (cT k _) (hne k e)
  have hst : stepOf N j ca = a := by
    apply Fin.ext
    have h1 := a.2
    have h2 := ca.2
    have h3 := M.j_le
    simp only [stepOf, lastCol] at hca ⊢
    split_ifs at hca ⊢ <;> omega
  intro z hz
  have hz₄ : ∀ p k, M.blk p = some k →
      twMinor M F (baseOf M k₀ z) p.2 k (h p.1)⁻¹ (fstPt k₀ z) (stepCols N j p.2) ≠ 0 := hz.2.2.2.1
  have hz₅ : twMinor M F (baseOf M k₀ z) a k₀ (h τ)⁻¹ (sndPt k₀ z) (stepCols N j a) ≠ 0 := hz.2.2.2.2
  refine continuousWithinAt_pi.2 fun i => ?_
  rcases e : ε.symm i with l | q | u
  · simp only [wRho, e]
    have c2 : ContinuousWithinAt (r ∘ baseOf M k₀) (wO M Rb τ a k₀ ca cb F kb V r h) z :=
      ContinuousWithinAt.comp (hr _ (hbase hz)) cB.continuousWithinAt hbase
    have c3 : ContinuousAt (fun x => Rb.A.chart kb x l) ((r ∘ baseOf M k₀) z) :=
      (continuous_apply l).continuousAt.comp ((Rb.A.chart kb).continuousAt hz.2.1)
    exact ContinuousAt.comp_continuousWithinAt (g := fun x => Rb.A.chart kb x l) c3 c2
  · simp only [wRho, e]
    exact cLow (fstPt k₀) cF q.1.1 q.1.2.1 q.1.2.2 z hz fun k e' => hz₄ (q.1.1, stepOf N j q.1.2.2) k e'
  · simp only [wRho, e]
    refine (cLow (sndPt k₀) cS τ cb ca z hz fun k e' => ?_).sub (cLow (fstPt k₀) cF τ cb ca z hz fun k e' => ?_)
    · rw [hst] at e' ⊢
      obtain rfl : k₀ = k := Option.some.inj (hk.symm.trans e')
      exact hz₅
    · exact hz₄ (τ, stepOf N j ca) k e'

end Flag

end GlobalTheory.CompanionTheory.Ar.PB.WMan
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameDataLocalDegreeBound
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.PFl.POpn

section Flag

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}
  {Kk : Type} [Fintype Kk] {ιk : Kk → Type} [∀ k, Fintype (ιk k)]

theorem continuous_upV (v : (Σ k, ιk k) → (Σ k, ι k)) : Continuous (upV v) := by
  refine continuous_pi fun q => ?_
  unfold upV
  by_cases h : ∃ q', v q' = q
  · simp only [dif_pos h]
    exact continuous_apply _
  · simp only [dif_neg h]
    exact continuous_const

theorem continuous_pBase (M : FlagModel y Ψ N j) (v : (Σ k, ιk k) → (Σ k, ι k)) : Continuous (pBase M v) := by
  refine continuous_pi fun q => ?_
  exact (continuous_apply (⟨q.1.1, q.2⟩ : Σ k, ι k)).comp (continuous_upV v)

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (keep : Ψ × Fin N → Prop) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ PIdx j keep ≃ Fin e), IsPCtx M Rb keep κ v F kb V bl r h → ∃ O' : Set ((Σ k, ιk k) → ℂ), IsOpen O' ∧ pO M Rb keep v F kb V r h = O' ∩ mcPts (mCoordIdeal (y ∘ v)) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb keep Kk _ ιk _ κ v F kb V bl r h ε hc
  obtain ⟨hBM, hkp, -, hBC, hr, hrc, -⟩ := hc
  have hmaps : Set.MapsTo (pBase M v) (mcPts (mCoordIdeal (y ∘ v))) (mcPts (mCoordIdeal M.x)) :=
    (GlobalTheory.T.blockMap_frame_restriction K ι Φ y Ψ N j M keep Kk ιk κ v hBM hkp).1
  have key : ∀ z₀ ∈ pO M Rb keep v F kb V r h,
      pO M Rb keep v F kb V r h ∈ 𝓝[mcPts (mCoordIdeal (y ∘ v))] z₀ := by
    rintro z₀ ⟨hz₀, hsrc, hV₀, hm⟩
    have hbm := hmaps hz₀
    have hG : M.GoodAt F (mCoordIdeal (pBase M v z₀)) := by
      obtain ⟨-, -, hgood, horb⟩ := hBC.2.2.2.2 _ hV₀
      rw [(Rb.A.chart kb).left_inv hsrc] at horb
      rwa [CovMap.mCoordIdeal_eq_of_sameOrbit (orbit_trans (orbit_symm (hr _ hbm)) horb)]
    have hrb : ContinuousWithinAt (fun z => r (pBase M v z)) (mcPts (mCoordIdeal (y ∘ v))) z₀ :=
      (hrc _ hbm).comp (continuous_pBase M v).continuousWithinAt hmaps
    have e₁ := hrb.tendsto.eventually_mem ((Rb.A.chart kb).open_source.mem_nhds hsrc)
    have e₂ := (((Rb.A.chart kb).continuousAt hsrc).tendsto.comp hrb.tendsto).eventually_mem (hBC.1.mem_nhds hV₀)
    have tw := GlobalTheory.CompanionTheory.Ar.PB.WMan.Opn.continuousWithinAt_twMinor M F (continuous_pBase M v) (continuous_upV v) hmaps hz₀ hG
    have e₃ : ∀ᶠ z in 𝓝[mcPts (mCoordIdeal (y ∘ v))] z₀, ∀ p k, keep p → M.blk p = some k →
        twMinor M F (pBase M v z) p.2 k (h p.1)⁻¹ (upV v z) (stepCols N j p.2) ≠ 0 := by
      refine eventually_all.2 fun p => eventually_all.2 fun k => ?_
      by_cases hp : keep p ∧ M.blk p = some k
      · exact ((tw p.2 k (h p.1)⁻¹ (stepCols N j p.2)).tendsto.eventually_ne
          (hm p k hp.1 hp.2)).mono fun _ hz _ _ => hz
      · exact Eventually.of_forall fun _ h₁ h₂ => absurd ⟨h₁, h₂⟩ hp
    filter_upwards [self_mem_nhdsWithin, e₁, e₂, e₃] with z h₀ h₁ h₂ h₃
    exact ⟨h₀, h₁, h₂, h₃⟩
  choose! U hU hmem hsub using fun z₀ (hz : z₀ ∈ pO M Rb keep v F kb V r h) =>
    mem_nhdsWithin.1 (key z₀ hz)
  refine ⟨⋃ z₀ ∈ pO M Rb keep v F kb V r h, U z₀, isOpen_biUnion hU, Set.Subset.antisymm ?_ ?_⟩
  · intro z hz
    exact ⟨Set.mem_biUnion hz (hmem z hz), hz.1⟩
  · rintro z ⟨hz, hzA⟩
    obtain ⟨z₀, h₀, hz₀⟩ := Set.mem_iUnion₂.1 hz
    exact hsub z₀ h₀ ⟨hz₀, hzA⟩

end Flag

end GlobalTheory.CompanionTheory.Ar.PB.PFl.POpn
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameMinorValueFormula
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.TwRead
open GlobalTheory.CompanionTheory.Ar.PB.CPts GlobalTheory.CompanionTheory.Ar.PB.ValRing

section Read

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ} (M : FlagModel y Ψ N j)

include M in

theorem off_step {p : Ψ × Fin N} {A : Matrix (Fin N) (Fin N) ℂ} (hA : IsBlockDiag j A) (I : Finset (Fin N))
    (hI : ¬ IsStepRows N j p.2 I) : minorIJ A I (stepCols N j p.2) = 0 :=
  ((GlobalTheory.T.block_diagonal_minor_vanishing ℂ N j p.2 M.j_le).2.1 A I hA hI).resolve_right
    (Finset.nonempty_iff_ne_empty.1 (stepCols_nonempty M.j_le p.2))

theorem pluck_eq {F : FrameData ι Ψ N M.Ω M.blk} (hF : M.IsFrame F) {zb : (Σ k, baseIdx ι M.blk k) → ℂ}
    (hzb : zb ∈ mcPts (mCoordIdeal M.x)) (hG : M.GoodAt F (mCoordIdeal zb)) {p : Ψ × Fin N} {k : K}
    (hp : M.blk p = some k) {A : Matrix (Fin N) (Fin N) ℂ} (hA : IsBlockDiag j A) {z : (Σ k, ι k) → ℂ} {α : ℂ}
    (hz : ∀ m : ι k, z ⟨k, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) zb * minorIJ A I (stepCols N j p.2))
    (I₀ : Finset (Fin N)) (hI₀ : IsStepRows N j p.2 I₀) :
    pluck M F zb k z I₀ = α * minorIJ A I₀ (stepCols N j p.2) := by
  let val := regVal hzb
  let uA : (Σ k, ι k) → Finset (Fin N) → regRing M.x zb :=
    fun q I => ⟨F.u q I, exists_isValueAt hzb (hG.2.1 q I).1⟩
  let vA : Finset (Fin N) → (Σ k, ι k) → regRing M.x zb :=
    fun I q => ⟨F.u' I q, exists_isValueAt hzb (hG.2.1 q I).2⟩
  have rel : ∀ I', IsStepRows N j p.2 I' →
      ∑ m : ι k, val (vA I₀ ⟨k, m⟩) * val (uA ⟨k, m⟩ I') = if I₀ = I' then 1 else 0 := fun I' hI' => by
    have e : ∑ m : ι k, vA I₀ ⟨k, m⟩ * uA ⟨k, m⟩ I' = if I₀ = I' then 1 else 0 := by
      apply Subtype.ext
      have := hF.2.2.1 p k hp I₀ I' hI₀ hI'
      split_ifs at this ⊢ <;> simpa [uA, vA] using this
    have e' := congrArg val e
    rw [map_sum] at e'
    simp only [map_mul] at e'
    rw [e']
    split_ifs <;> simp
  have key : ∀ I, (∑ m : ι k, val (vA I₀ ⟨k, m⟩) * val (uA ⟨k, m⟩ I)) * minorIJ A I (stepCols N j p.2) =
      if I = I₀ then minorIJ A I₀ (stepCols N j p.2) else 0 := fun I => by
    by_cases hI : IsStepRows N j p.2 I
    · rw [rel I hI]
      by_cases e : I = I₀
      · subst e; simp
      · simp [e, Ne.symm e]
    · have e : I ≠ I₀ := fun e => hI (e ▸ hI₀)
      rw [off_step M hA I hI, if_neg e, mul_zero]
  have read : ∑ m : ι k, val (vA I₀ ⟨k, m⟩) * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) zb * minorIJ A I (stepCols N j p.2) =
      minorIJ A I₀ (stepCols N j p.2) := by
    calc _ = ∑ I, (∑ m : ι k, val (vA I₀ ⟨k, m⟩) * val (uA ⟨k, m⟩ I)) * minorIJ A I (stepCols N j p.2) := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun m _ => ?_
          rw [mul_assoc]
          rfl
      _ = _ := by simp only [key]; simp
  rw [← read, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [hz m, mul_left_comm]
  rfl

end Read

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (zb : (Σ k, baseIdx ι M.blk k) → ℂ) (p : Ψ × Fin N) (k : K) (A g : Matrix (Fin N) (Fin N) ℂ) (z : (Σ k, ι k) → ℂ) (α : ℂ) (J : Finset (Fin N)), M.IsFrame F → zb ∈ mcPts (mCoordIdeal M.x) → M.GoodAt F (mCoordIdeal zb) → M.blk p = some k → IsBlockDiag j A → (∀ m : ι k, z ⟨k, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) zb * minorIJ A I (stepCols N j p.2)) → twMinor M F zb p.2 k g z J = α * minorIJ (g * A) J (stepCols N j p.2) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M F zb p k A g z α J hF hzb hG hp hA hz
  unfold twMinor
  rw [(GlobalTheory.T.block_diagonal_minor_vanishing ℂ N j p.2 M.j_le).1 g A J (stepCols N j p.2), Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun I _ => ?_
  split_ifs with hI
  · rw [pluck_eq M hF hzb hG hp hA hz I hI]
    ring
  · rw [off_step M hA I hI]
    ring

end GlobalTheory.CompanionTheory.Ar.PB.WMan.TwRead
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LUTwistRefactorization
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.Transv

theorem lastCol_mem {N j : ℕ} {a ca : Fin N} (hj : j ≤ N) (hca : (ca : ℕ) = lastCol N j a) :
    ca ∈ stepCols N j a ∧ ∀ r ∈ stepCols N j a, r ≤ ca := by
  unfold lastCol at hca
  refine ⟨?_, ?_⟩
  · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs at hca ⊢ <;> omega
  · intro r hr
    simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at hr
    rw [Fin.le_iff_val_le_val]
    split_ifs at hca hr <;> omega

theorem transv_mul_transv {N : ℕ} {ca cb : Fin N} (hne : ca ≠ cb) (s : ℂ) :
    (1 + Matrix.single cb ca s) * (1 + Matrix.single cb ca (-s)) = (1 : Matrix (Fin N) (Fin N) ℂ) := by
  rw [add_mul, one_mul, mul_add, mul_one, Matrix.single_mul_single_of_ne s cb ca cb hne (-s), add_zero,
    add_assoc, ← Matrix.single_add, neg_add_cancel, Matrix.single_zero, add_zero]

theorem main : ∀ (N j : ℕ) (a ca cb : Fin N) (L U : Matrix (Fin N) (Fin N) ℂ) (t' : ℂ), j ≤ N → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ((ca : ℕ) < N - j ↔ (cb : ℕ) < N - j) → IsBlockDiag j L → IsLowerUni L → IsBlockDiag j U → U.BlockTriangular id → (∀ c, U c c ≠ 0) → minorIJ (L * U * (1 + Matrix.single cb ca t')) (stepCols N j a) (stepCols N j a) ≠ 0 → ∃ (t : ℂ) (V : Matrix (Fin N) (Fin N) ℂ), IsBlockDiag j V ∧ V.BlockTriangular id ∧ (∀ c ∈ stepCols N j a, V c c ≠ 0) ∧ U * (1 + Matrix.single cb ca t') = (1 + Matrix.single cb ca t) * V := by
  intro N j a ca cb L U t' hj hca hcb hblk hL hLu hU hUt hUd hmin
  have hne : ca ≠ cb := by
    intro h
    have h1 := congrArg Fin.val h
    omega
  obtain ⟨hcaS, hmax⟩ := lastCol_mem hj hca
  have hLM : L * U * (1 + Matrix.single cb ca t') = L * (U * (1 + Matrix.single cb ca t')) :=
    Matrix.mul_assoc _ _ _
  set M := U * (1 + Matrix.single cb ca t') with hMdef
  have hMe : ∀ x y, M x y = U x y + if y = ca then U x cb * t' else 0 := by
    intro x y
    rw [hMdef, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply]
    split_ifs with hy
    · rw [hy, Matrix.mul_single_apply_same]
    · rw [Matrix.mul_single_apply_of_ne t' cb ca x y hy U]
  have hUz : ∀ x y : Fin N, y < x → U x y = 0 := fun x y h => hUt (show id y < id x from h)
  have hMut : ∀ x y : Fin N, y < x → x ≠ cb → M x y = 0 := by
    intro x y hxy hx
    rw [hMe, hUz x y hxy]
    split_ifs with hy
    · rw [hy] at hxy
      have h1 : cb < x := by
        rw [Fin.lt_iff_val_lt_val] at hxy ⊢
        have h2 : (x : ℕ) ≠ cb := fun h => hx (Fin.ext h)
        omega
      rw [hUz x cb h1]
      simp
    · simp
  have hMca : M ca ca ≠ 0 := by
    intro h0
    apply hmin
    rw [hLM]
    unfold minorIJ
    rw [dif_pos rfl]
    set f := (stepCols N j a).orderEmbOfFin (rfl : (stepCols N j a).card = (stepCols N j a).card) with hf
    have hfmem : ∀ r, f r ∈ stepCols N j a := fun r => Finset.orderEmbOfFin_mem _ _ r
    have hSmap : Finset.univ.map f.toEmbedding = stepCols N j a := Finset.map_orderEmbOfFin_univ _ _
    have hrange : Set.range f = ↑(stepCols N j a) := Finset.range_orderEmbOfFin _ _
    have hprod : (L * M).submatrix f f = L.submatrix f f * M.submatrix f f := by
      ext p q
      simp only [Matrix.submatrix_apply, Matrix.mul_apply]
      have hfpS := hfmem p
      have hz : ∀ i ∈ (Finset.univ : Finset (Fin N)), i ∉ stepCols N j a → L (f p) i * M i (f q) = 0 := by
        intro i _ hi
        by_cases hic : (ca : ℕ) < i
        · have hfp := hmax (f p) hfpS
          have hlt : f p < i := by
            rw [Fin.le_iff_val_le_val] at hfp
            rw [Fin.lt_iff_val_lt_val]
            omega
          rw [hLu.2 (f p) i hlt, zero_mul]
        · have hLz : L (f p) i = 0 := by
            apply hL
            intro hiff
            simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at hi hfpS
            unfold lastCol at hca
            split_ifs at hi hfpS hca
            · have h3 := hiff.mpr (by omega)
              omega
            · omega
          rw [hLz, zero_mul]
      have hm := Finset.sum_map Finset.univ f.toEmbedding (fun x => L (f p) x * M x (f q))
      rw [hSmap] at hm
      rw [← Finset.sum_subset (Finset.subset_univ (stepCols N j a)) hz]
      exact hm
    have hUT : (M.submatrix f f).IsUpperTriangular := by
      intro p q hpq
      rw [Matrix.submatrix_apply]
      have hfpcb : f p ≠ cb := by
        intro hfp
        have h4 := hmax (f p) (hfmem p)
        rw [hfp, Fin.le_iff_val_le_val] at h4
        omega
      exact hMut (f p) (f q) (f.strictMono hpq) hfpcb
    have hdetM : (M.submatrix f f).det = 0 := by
      rw [Matrix.det_of_upperTriangular hUT]
      obtain ⟨p0, hp0⟩ : ∃ p0, f p0 = ca := by
        have h1 : ca ∈ Set.range f := by
          rw [hrange]
          exact hcaS
        exact h1
      exact Finset.prod_eq_zero (Finset.mem_univ p0) (by rw [Matrix.submatrix_apply, hp0]; exact h0)
    rw [hprod, Matrix.det_mul, hdetM, mul_zero]
  have hMb : ∀ x y : Fin N, ¬((x : ℕ) < N - j ↔ (y : ℕ) < N - j) → M x y = 0 := by
    intro x y hxy
    rw [hMe, hU x y hxy]
    split_ifs with hy
    · rw [hy] at hxy
      rw [hU x cb (fun h => hxy (h.trans hblk.symm))]
      simp
    · simp
  set t := M cb ca / M ca ca with ht
  have hVe : ∀ x y, ((1 + Matrix.single cb ca (-t)) * M) x y = M x y + if x = cb then -t * M ca y else 0 := by
    intro x y
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.add_apply]
    split_ifs with hx
    · rw [hx, Matrix.single_mul_apply_same]
    · rw [Matrix.single_mul_apply_of_ne (-t) cb ca x y hx M]
  refine ⟨t, (1 + Matrix.single cb ca (-t)) * M, ?_, ?_, ?_, ?_⟩
  · intro x y hxy
    rw [hVe, hMb x y hxy]
    split_ifs with hx
    · rw [hx] at hxy
      rw [hMb ca y (fun h => hxy (hblk.symm.trans h))]
      simp
    · simp
  · intro x y hxy
    change y < x at hxy
    rw [hVe]
    by_cases hx : x = cb
    · rw [if_pos hx, hx]
      rw [hx] at hxy
      by_cases hy : y = ca
      · rw [hy, ht, neg_mul, div_mul_cancel₀ _ hMca, add_neg_cancel]
      · have hylt : y < ca := by
          rw [Fin.lt_iff_val_lt_val] at hxy ⊢
          have h2 : (y : ℕ) ≠ ca := fun h => hy (Fin.ext h)
          omega
        rw [hMe cb y, if_neg hy, hUz cb y hxy, hMe ca y, if_neg hy, hUz ca y hylt]
        simp
    · rw [if_neg hx, add_zero]
      exact hMut x y hxy hx
  · intro c hc
    rw [hVe]
    have hcle := hmax c hc
    have hccb : c ≠ cb := by
      intro h
      rw [h, Fin.le_iff_val_le_val] at hcle
      omega
    rw [if_neg hccb, add_zero]
    by_cases hcc : c = ca
    · rw [hcc]
      exact hMca
    · rw [hMe, if_neg hcc, add_zero]
      exact hUd c
  · rw [← Matrix.mul_assoc, transv_mul_transv hne t, Matrix.one_mul]

end GlobalTheory.CompanionTheory.Ar.PB.WMan.Transv
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogPeriodStatementStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_period_statement : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (d : ℕ) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsArithVar (mCoordIdeal y) (d + 2) → ∀ (F : FrameData ι Ψ N M.Ω M.blk) (z : (Σ o : Option K, ι (o.getD k₀)) → ℂ), M.IsFrame F → basePart M.blk (fstPt k₀ z) ∈ mcPts (mCoordIdeal M.x) → M.GoodAt F (mCoordIdeal (basePart M.blk (fstPt k₀ z))) → (∀ k, basePart M.blk (fstPt k₀ z) ⟨k, F.c k⟩ = 1) → (z ∈ mcPts (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ↔ ∃ (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (t : ℂ), M.IsFlagOf F (fstPt k₀ z) h ∧ M.IsFlagOf F (sndPt k₀ z) (Function.update h τ (h τ * (1 + Matrix.single cb ca t)))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Pts.main | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Pts.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Pts.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MeasurableFibreCountOfLocalDiffeoStatement
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurable_fibre_count_of_local_diffeo : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) (q : X → Fin e → ℂ) (S : Set X) (G : X → ℝ), (∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' S) = 0) → (∀ x ∉ S, ∀ j, x ∈ (A.chart j).source → AnalyticAt ℂ (q ∘ (A.chart j).symm) (A.chart j x) ∧ LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) (A.chart j x) : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0) → (∀ y, (q ⁻¹' {y} \ S).Finite) → (∀ x ∉ S, ∀ i k, x ∈ (A.chart k).source → ContDiffAt ℝ 2 ((Φ i).φ x ∘ (A.chart k).symm) (A.chart k x)) → (∀ j, AEStronglyMeasurable (fun u => G ((A.chart j).symm u) * locDens A Φ j u) (volume.restrict (A.chart j).target)) → AEStronglyMeasurable (fun y => ∑ᶠ x ∈ q ⁻¹' {y} \ S, G x * pushDens A Φ q x) volume := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.Push.aestronglyMeasurable_fibreSum_pushDens | exact GlobalTheory.CompanionTheory.Ar.Giv.Push.aestronglyMeasurable_fibreSum_pushDens | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.Push.aestronglyMeasurable_fibreSum_pushDens <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MultihomogeneousLiftToJoinStatement
section
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multihomogeneous_lift_to_join : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (β : MRing ι) (b : K → ℕ), IsArithVar (mCoordIdeal y) (e + 1) → IsMultiHomog β b → β ∉ mCoordIdeal y → ∃ (β' : MRing ι) (b' : K → ℕ) (M : ℕ) (y' : (Σ _ : Unit, Fin M) → Ω) (J : Ideal (MRing (joinIdx ι fun _ : Unit => Fin M))), IsMultiHomog β' b' ∧ β' ∉ mCoordIdeal y ∧ (∀ z ∈ mcPts (mCoordIdeal y), evC z β = 0 → evC z β' = 0) ∧ (∃ i, y' ⟨(), i⟩ ≠ 0) ∧ blockFnField (joinVec y y') = blockFnField y ∧ IsMultiHomogIdeal J ∧ ¬ J ≤ mCoordIdeal (joinVec y y') ∧ IsSncModel (joinVec y y') e J ∧ (∀ z ∈ mcPts (mCoordIdeal (joinVec y y')), evC z (rename (joinInl ι fun _ : Unit => Fin M) β') = 0 → z ∈ mcPts J) ∧ ∀ z ∈ mcPts (mCoordIdeal y), evC z β' ≠ 0 → ∃ (G : Fin M → MRing ι) (g : K → ℕ), (∀ i, IsMultiHomog (G i) g) ∧ (∀ i j, y' ⟨(), i⟩ * aeval y (G j) = y' ⟨(), j⟩ * aeval y (G i)) ∧ ∃ i, evC z (G i) ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.exists_snc_model_iso | exact GlobalTheory.CompanionTheory.Ar.Giv.exists_snc_model_iso | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.exists_snc_model_iso <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.PushDownOfArithIntersectionSystemStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.push_down_of_arith_intersection_system : ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → GroundTheory.Heights₂.Heights.LowerBoundFree.PushDown.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.pushDown | exact GlobalTheory.CompanionTheory.Ar.Giv.pushDown | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.pushDown <;> assumption)
end

