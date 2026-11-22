import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0042
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0122
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0072
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0114
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0035
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionFunctorialHolomorphic
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0075
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0043
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0118
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartSixth
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.Opn

section Values

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem continuousWithinAt_valAt {x : (Σ k, ι k) → Ω} {b₀ : (Σ k, ι k) → ℂ} (hb : b₀ ∈ mcPts (mCoordIdeal x)) {s : Ω}
    (hs : RegAt x (mCoordIdeal b₀) s) : ContinuousWithinAt (valAt x s) (mcPts (mCoordIdeal x)) b₀ := by
  obtain ⟨d, g, h, hg, hh, hn, heq⟩ := hs
  have hx := ValRing.aeval_ne_zero_of_notMem hb hh hn
  have h0 := ValRing.eval_ne_zero_of_notMem hh hn
  have cg : Continuous fun b : (Σ k, ι k) → ℂ => eval b (map (Int.castRingHom ℂ) g) :=
    MvPolynomial.continuous_eval _
  have ch : Continuous fun b : (Σ k, ι k) → ℂ => eval b (map (Int.castRingHom ℂ) h) :=
    MvPolynomial.continuous_eval _
  have hne : ∀ᶠ b in 𝓝 b₀, eval b (map (Int.castRingHom ℂ) h) ≠ 0 := ch.continuousAt.eventually_ne h0
  have key : valAt x s =ᶠ[𝓝[mcPts (mCoordIdeal x)] b₀]
      fun b => eval b (map (Int.castRingHom ℂ) g) / eval b (map (Int.castRingHom ℂ) h) := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hne] with b hbm hbn
    exact valAt_eq hbm ⟨d, g, h, hg, hh, hx, heq, hbn, rfl⟩
  have hq : ContinuousWithinAt
      (fun b : (Σ k, ι k) → ℂ => eval b (map (Int.castRingHom ℂ) g) / eval b (map (Int.castRingHom ℂ) h))
      (mcPts (mCoordIdeal x)) b₀ := (cg.continuousAt.div ch.continuousAt h0).continuousWithinAt
  exact hq.congr_of_eventuallyEq key (key.self_of_nhdsWithin hb)

end Values

section Flag

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

theorem continuousWithinAt_twMinor (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) {Z : Type}
    [TopologicalSpace Z] {A : Set Z} {z₀ : Z} {bs : Z → (Σ k, baseIdx ι M.blk k) → ℂ} {pt : Z → (Σ k, ι k) → ℂ}
    (hbs : Continuous bs) (hpt : Continuous pt) (hA : Set.MapsTo bs A (mcPts (mCoordIdeal M.x))) (hz₀ : z₀ ∈ A)
    (hG : M.GoodAt F (mCoordIdeal (bs z₀))) (i : Fin N) (k : K) (g : Matrix (Fin N) (Fin N) ℂ)
    (J : Finset (Fin N)) : ContinuousWithinAt (fun z => twMinor M F (bs z) i k g (pt z) J) A z₀ := by
  unfold twMinor pluck
  refine tendsto_finsetSum _ fun I _ => Tendsto.const_mul _ (tendsto_finsetSum _ fun m _ => Tendsto.mul ?_ ?_)
  · exact (continuousWithinAt_valAt (hA hz₀) (hG.2.1 _ _).2).comp hbs.continuousWithinAt hA
  · exact ((continuous_apply _).comp hpt).continuousWithinAt

theorem isBlockMap_v₀ (k₀ : K) : IsBlockMap (some : K → Option K) (v₀ (ι := ι) k₀) := by
  refine ⟨Option.some_injective _, ?_, fun _ => rfl, ?_⟩
  · rintro ⟨k, m⟩ ⟨k', m'⟩ e
    simp only [v₀] at e
    obtain ⟨e1, e2⟩ := Sigma.mk.inj_iff.1 e
    obtain rfl := Option.some_injective _ e1
    rw [eq_of_heq e2]
  · rintro ⟨_, m⟩ ⟨k, rfl⟩
    exact ⟨⟨k, m⟩, rfl⟩

theorem continuous_fstPt (k₀ : K) : Continuous (fstPt (ι := ι) k₀) :=
  continuous_pi fun p => continuous_apply (v₀ k₀ p)

theorem continuous_sndPt (k₀ : K) : Continuous (sndPt (ι := ι) k₀) :=
  continuous_pi fun p => continuous_apply (v₁ k₀ p)

theorem continuous_baseOf (M : FlagModel y Ψ N j) (k₀ : K) : Continuous (baseOf M k₀) :=
  continuous_pi fun q => continuous_apply (v₀ k₀ ⟨q.1.1, q.2⟩)

theorem fstPt_mem (M : FlagModel y Ψ N j) {d : ℕ} {τ : Ψ} {a b : Fin N} {k₀ : K} {ca cb : Fin N}
    (hb : (b : ℕ) = a + 1) (hba : (b : ℕ) < j ∨ j ≤ (a : ℕ)) (hk : M.blk (τ, a) = some k₀)
    (hca : (ca : ℕ) = lastCol N j a) (hcb : (cb : ℕ) = ca + 1) (hV : IsArithVar (mCoordIdeal y) (d + 2))
    {z : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (hz : z ∈ mcPts (wP M τ a k₀ ca cb)) :
    fstPt k₀ z ∈ mcPts (mCoordIdeal y) := by
  have hI := (GlobalTheory.T.flag_adjacent_swap_varieties_arithmetic K ι Φ y Ψ N j M d τ a b k₀ ca cb hb hba hk hca hcb hV).2.2.2.1
  exact GlobalTheory.CompanionTheory.Ar.Chg.mem_mcPts_restr (isBlockMap_v₀ k₀) hI.ge hz

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h → ∃ O' : Set ((Σ o : Option K, ι (o.getD k₀)) → ℂ), IsOpen O' ∧ wO M Rb τ a k₀ ca cb F kb V r h = O' ∩ mcPts (wP M τ a k₀ ca cb) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d Rb τ a b k₀ ca cb F kb V bl r h hc
  obtain ⟨hb, hba, hk₀, hca, hcb, hAV, -, hBC, hr, hrc, -⟩ := hc
  have hmaps : Set.MapsTo (baseOf M k₀) (mcPts (wP M τ a k₀ ca cb)) (mcPts (mCoordIdeal M.x)) := fun z hz =>
    CPts.base_mem M (fstPt_mem M hb hba hk₀ hca hcb hAV hz)
  have key : ∀ z₀ ∈ wO M Rb τ a k₀ ca cb F kb V r h,
      wO M Rb τ a k₀ ca cb F kb V r h ∈ 𝓝[mcPts (wP M τ a k₀ ca cb)] z₀ := by
    rintro z₀ ⟨hz₀, hsrc, hV₀, hm₁, hm₂⟩
    have hbm := hmaps hz₀
    have hG : M.GoodAt F (mCoordIdeal (baseOf M k₀ z₀)) := by
      obtain ⟨-, -, hgood, horb⟩ := hBC.2.2.2.2 _ hV₀
      rw [(Rb.A.chart kb).left_inv hsrc] at horb
      rwa [CovMap.mCoordIdeal_eq_of_sameOrbit (orbit_trans (orbit_symm (hr _ hbm)) horb)]
    have hrb : ContinuousWithinAt (fun z => r (baseOf M k₀ z)) (mcPts (wP M τ a k₀ ca cb)) z₀ :=
      (hrc _ hbm).comp (continuous_baseOf M k₀).continuousWithinAt hmaps
    have e₁ := hrb.tendsto.eventually_mem ((Rb.A.chart kb).open_source.mem_nhds hsrc)
    have e₂ := (((Rb.A.chart kb).continuousAt hsrc).tendsto.comp hrb.tendsto).eventually_mem (hBC.1.mem_nhds hV₀)
    have tw := fun (pt : _ → (Σ k, ι k) → ℂ) (hpt : Continuous pt) =>
      continuousWithinAt_twMinor M F (continuous_baseOf M k₀) hpt hmaps hz₀ hG
    have e₃ : ∀ᶠ z in 𝓝[mcPts (wP M τ a k₀ ca cb)] z₀, ∀ p k, M.blk p = some k →
        twMinor M F (baseOf M k₀ z) p.2 k (h p.1)⁻¹ (fstPt k₀ z) (stepCols N j p.2) ≠ 0 := by
      refine eventually_all.2 fun p => eventually_all.2 fun k => ?_
      by_cases hp : M.blk p = some k
      · exact ((tw _ (continuous_fstPt k₀) p.2 k (h p.1)⁻¹ (stepCols N j p.2)).tendsto.eventually_ne
          (hm₁ p k hp)).mono fun _ hz _ => hz
      · exact Eventually.of_forall fun _ hp' => absurd hp' hp
    have e₄ := (tw _ (continuous_sndPt k₀) a k₀ (h τ)⁻¹ (stepCols N j a)).tendsto.eventually_ne hm₂
    filter_upwards [self_mem_nhdsWithin, e₁, e₂, e₃, e₄] with z h₀ h₁ h₂ h₃ h₄
    exact ⟨h₀, h₁, h₂, h₃, h₄⟩
  choose! U hU hmem hsub using fun z₀ (hz : z₀ ∈ wO M Rb τ a k₀ ca cb F kb V r h) =>
    mem_nhdsWithin.1 (key z₀ hz)
  refine ⟨⋃ z₀ ∈ wO M Rb τ a k₀ ca cb F kb V r h, U z₀, isOpen_biUnion hU, Set.Subset.antisymm ?_ ?_⟩
  · intro z hz
    exact ⟨Set.mem_biUnion hz (hmem z hz), hz.1⟩
  · rintro z ⟨hz, hzA⟩
    obtain ⟨z₀, h₀, hz₀⟩ := Set.mem_iUnion₂.1 hz
    exact hsub z₀ h₀ ⟨hz₀, hzA⟩

end Flag

end GlobalTheory.CompanionTheory.Ar.PB.WMan.Opn
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentRowsAnalytic
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Pr

theorem holoMap_comp' {e₁ e₂ e₃ : ℕ} {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] {C : FinHolAtlas e₁ Z} {B : FinHolAtlas e₂ Y} {A : FinHolAtlas e₃ X}
    {g : Z → Y} {f : Y → X} (hg : HoloMap C B g) (hf : HoloMap B A f) : HoloMap C A (f ∘ g) := by
  refine ⟨hf.1.comp hg.1, fun j k t ht => ?_⟩
  obtain ⟨ht1, ht2⟩ := ht
  obtain ⟨m, hm⟩ := B.cover (g ((C.chart j).symm t))
  have h1 : AnalyticAt ℂ (B.chart m ∘ g ∘ (C.chart j).symm) t := hg.2 j m t ⟨ht1, hm⟩
  have hu : (B.chart m).symm ((B.chart m ∘ g ∘ (C.chart j).symm) t) = g ((C.chart j).symm t) :=
    (B.chart m).left_inv hm
  have h2 : AnalyticAt ℂ (A.chart k ∘ f ∘ (B.chart m).symm)
      ((B.chart m ∘ g ∘ (C.chart j).symm) t) :=
    hf.2 m k _ ⟨(B.chart m).map_source hm, by
      rw [Set.mem_preimage, hu]; exact ht2⟩
  refine (h2.comp h1).congr ?_
  have hc : ContinuousAt (g ∘ (C.chart j).symm) t :=
    hg.1.continuousAt.comp ((C.chart j).continuousAt_symm ht1)
  filter_upwards [hc ((B.chart m).open_source.mem_nhds hm)] with t' ht'
  have ht'' : g ((C.chart j).symm t') ∈ (B.chart m).source := ht'
  simp only [Function.comp]
  rw [(B.chart m).left_inv ht'']

theorem injective_of_degree_one {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {A : FinHolAtlas e X} {B : FinHolAtlas e Y} {π : Y → X} (hd : IsDegreeOff A B π 1 ∅) :
    Function.Injective π := by
  intro u w huw
  obtain ⟨c, hc⟩ := Set.ncard_eq_one.1 (hd.2.2.2.2.1 (π u) (Set.notMem_empty _))
  have hu : u ∈ π ⁻¹' {π u} := rfl
  have hw : w ∈ π ⁻¹' {π u} := huw.symm
  rw [hc] at hu hw
  exact hu.trans hw.symm

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem exists_holo_of_centre {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k, ι' k)) {P : Ideal (MRing ι)} {J : Ideal (MRing ι)}
    {P' J' : Ideal (MRing ι')} {D D' : ℕ} (hJ : J = ⊤) (R : AnLogRes P J D)
    (R' : AnLogRes P' J' D') (hb : IsBlockMap κ v) (hP : P ≤ imageZ v P') :
    ∃ h : R'.X → R.X, HoloMap R'.A R.A h ∧ ∀ x, SameOrbit (R.lift (h x) (h x)) (R'.lift x x ∘ v) := by
  subst hJ
  exact Proj.holoMap_of_blockProj K ι K' ι' κ v P P' J' D D' R R' hb hP

theorem isBlockMap_v₀ (k₀ : K) :
    IsBlockMap (some : K → Option K) (v₀ (ι := ι) k₀) := by
  refine ⟨Option.some_injective _, ?_, fun _ => rfl, ?_⟩
  · rintro ⟨k, m⟩ ⟨k', m'⟩ h
    have h1 : k = k' := Option.some.inj (congrArg Sigma.fst h)
    subst h1
    have h2 : m = m' := eq_of_heq (Sigma.mk.inj h).2
    rw [h2]
  · rintro ⟨o, m⟩ ⟨k, rfl⟩
    exact ⟨⟨k, m⟩, rfl⟩

def κ₁ (k₀ k : K) : Option K := if k = k₀ then none else some k

theorem isBlockMap_v₁ (k₀ : K) : IsBlockMap (κ₁ k₀) (v₁ (ι := ι) k₀) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u w h
    by_cases hu : u = k₀ <;> by_cases hw : w = k₀ <;> simp_all [κ₁]
  · rintro ⟨k, m⟩ ⟨k', m'⟩ h
    by_cases hk : k = k₀
    · subst hk
      by_cases hk' : k' = k
      · subst hk'
        rw [v₁_self, v₁_self] at h
        have h2 : m = m' := eq_of_heq (Sigma.mk.inj h).2
        rw [h2]
      · rw [v₁_self, v₁_ne (p := ⟨k', m'⟩) hk'] at h
        exact absurd (congrArg Sigma.fst h) (by simp)
    · by_cases hk' : k' = k₀
      · subst hk'
        rw [v₁_self, v₁_ne (p := ⟨k, m⟩) hk] at h
        exact absurd (congrArg Sigma.fst h) (by simp)
      · rw [v₁_ne (p := ⟨k, m⟩) hk, v₁_ne (p := ⟨k', m'⟩) hk'] at h
        have h1 : k = k' := Option.some.inj (congrArg Sigma.fst h)
        subst h1
        have h2 : m = m' := eq_of_heq (Sigma.mk.inj h).2
        rw [h2]
  · rintro ⟨k, m⟩
    by_cases hk : k = k₀
    · subst hk
      rw [v₁_self]
      simp [κ₁]
    · rw [v₁_ne (p := ⟨k, m⟩) hk]
      simp [κ₁, hk]
  · rintro ⟨o, m⟩ ⟨k, hk⟩
    by_cases e : k = k₀
    · subst e
      have ho : o = none := by
        have hk' : κ₁ k k = o := hk
        rw [← hk']; simp [κ₁]
      subst ho
      exact ⟨⟨k, m⟩, v₁_self k m⟩
    · have ho : o = some k := by
        have hk' : κ₁ k₀ k = o := hk
        rw [← hk']; simp [κ₁, e]
      subst ho
      exact ⟨⟨k, m⟩, v₁_ne (p := ⟨k, m⟩) e⟩

theorem basePart_orbit {σ : Type} (blk : σ → Option K) {z z' : (Σ k, ι k) → ℂ}
    (h : SameOrbit z z') : SameOrbit (basePart blk z) (basePart blk z') := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => c k.1, fun k => hc _, rfl⟩

theorem basePart_snd {σ : Type} {blk : σ → Option K} {k₀ : K} {s : σ} (hs : blk s = some k₀)
    (z : (Σ o : Option K, ι (o.getD k₀)) → ℂ) :
    basePart blk (sndPt k₀ z) = basePart blk (fstPt k₀ z) := by
  funext ⟨k, m⟩
  have hk : k.1 ≠ k₀ := fun e => k.2 s (by rw [hs, e])
  change z (v₁ k₀ ⟨k.1, m⟩) = z (v₀ k₀ ⟨k.1, m⟩)
  rw [v₁_ne (p := ⟨k.1, m⟩) hk]
  rfl

theorem orbit_of_two {k₀ : K} {z z' : (Σ o : Option K, ι (o.getD k₀)) → ℂ}
    (h₀ : SameOrbit (fstPt k₀ z) (fstPt k₀ z')) (h₁ : SameOrbit (sndPt k₀ z) (sndPt k₀ z')) :
    SameOrbit z z' := by
  obtain ⟨c₀, hc₀, e₀⟩ := h₀
  obtain ⟨c₁, hc₁, e₁⟩ := h₁
  refine ⟨fun o => o.elim (c₁ k₀) c₀, ?_, ?_⟩
  · rintro (_ | k)
    · exact hc₁ k₀
    · exact hc₀ k
  · funext ⟨o, m⟩
    cases o with
    | none =>
      have := congrFun e₁ ⟨k₀, m⟩
      simpa [sndPt, v₁_self] using this
    | some k =>
      have := congrFun e₀ ⟨k, m⟩
      simpa [fstPt, v₀] using this

theorem two_projections : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsArithVar (mCoordIdeal y) (d + 2) → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (pr : RW.X → BM.Rb.X), HoloMap RW.A BM.Rb.A pr → (∀ x, SameOrbit (BM.Rb.lift (pr x) (pr x)) (basePart M.blk (fstPt k₀ (RW.lift x x)))) → ∃ q : Fin 2 → RW.X → FA.S.X, (∀ i, HoloMap RW.A FA.S.A (q i)) ∧ (∀ i, FA.pr ∘ q i = pr) ∧ (∀ x x₀, FA.Re.π x₀ = q 0 x → SameOrbit (FA.Re.R.lift x₀ x₀) (fstPt k₀ (RW.lift x x))) ∧ (∀ x x₀, FA.Re.π x₀ = q 1 x → SameOrbit (FA.Re.R.lift x₀ x₀) (sndPt k₀ (RW.lift x x))) ∧ (Function.Injective fun w => (q 0 w, q 1 w)) ∧ ∀ p, p ≠ (τ, a) → FA.S.ph (some p) ∘ q 0 = FA.S.ph (some p) ∘ q 1 ∧ ∀ t, FA.S.phT (some p) t ∘ q 0 = FA.S.phT (some p) t ∘ q 1 := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA τ a b k₀ ca cb hb hab hk ha hcb hy RW pr hpr hbase
  obtain ⟨-, -, -, hi₀, hi₁⟩ := GlobalTheory.T.flag_adjacent_swap_varieties_arithmetic K ι Φ y Ψ N j M d τ a b k₀ ca cb hb hab hk ha hcb hy
  have hi₁' := hi₁ (v₁ k₀) (fun p hp => v₁_ne hp) (fun m => v₁_self k₀ m)
  obtain ⟨h₀, hh₀, ho₀⟩ := exists_holo_of_centre some (v₀ k₀) FA.J_top FA.Re.R RW
    (isBlockMap_v₀ k₀) hi₀.ge
  obtain ⟨h₁, hh₁, ho₁⟩ := exists_holo_of_centre (κ₁ k₀) (v₁ k₀) FA.J_top FA.Re.R RW
    (isBlockMap_v₁ k₀) hi₁'.ge
  have hdeg := FA.Re.degree
  rw [FA.deg_one, FA.br_empty] at hdeg
  have hπ : Function.Injective FA.Re.π := injective_of_degree_one hdeg
  have hpr' : ∀ (x₁ : FA.Re.R.X) (w : RW.X) (zz : (Σ k, ι k) → ℂ),
      SameOrbit (FA.Re.R.lift x₁ x₁) zz →
      basePart M.blk zz = basePart M.blk (fstPt k₀ (RW.lift w w)) → FA.pr (FA.Re.π x₁) = pr w := by
    intro x₁ w zz h1 h2
    refine BM.Rb.inj _ _ (Proj.not_mem_mcPts_top _) ?_
    have h3 := basePart_orbit M.blk h1
    rw [h2] at h3
    exact orbit_trans (orbit_symm (FA.pr_eq x₁)) (orbit_trans h3 (orbit_symm (hbase w)))
  have hb₀ : ∀ w, FA.pr (FA.Re.π (h₀ w)) = pr w := fun w => hpr' _ w _ (ho₀ w) rfl
  have hb₁ : ∀ w, FA.pr (FA.Re.π (h₁ w)) = pr w := fun w =>
    hpr' _ w _ (ho₁ w) (basePart_snd hk (RW.lift w w))
  refine ⟨![FA.Re.π ∘ h₀, FA.Re.π ∘ h₁], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have c₀ := holoMap_comp' hh₀ FA.Re.holo
    have c₁ := holoMap_comp' hh₁ FA.Re.holo
    exact Fin.forall_fin_two.2 ⟨c₀, c₁⟩
  · exact Fin.forall_fin_two.2 ⟨funext hb₀, funext hb₁⟩
  · intro x x₀ e
    have : x₀ = h₀ x := hπ e
    subst this
    exact ho₀ x
  · intro x x₀ e
    have : x₀ = h₁ x := hπ e
    subst this
    exact ho₁ x
  · intro w w' e
    have e₀ : FA.Re.π (h₀ w) = FA.Re.π (h₀ w') := congrArg Prod.fst e
    have e₁ : FA.Re.π (h₁ w) = FA.Re.π (h₁ w') := congrArg Prod.snd e
    have f₀ := hπ e₀
    have f₁ := hπ e₁
    have g₀ : SameOrbit (fstPt k₀ (RW.lift w w)) (fstPt k₀ (RW.lift w' w')) := by
      have := ho₀ w'
      rw [← f₀] at this
      exact orbit_trans (orbit_symm (ho₀ w)) this
    have g₁ : SameOrbit (sndPt k₀ (RW.lift w w)) (sndPt k₀ (RW.lift w' w')) := by
      have := ho₁ w'
      rw [← f₁] at this
      exact orbit_trans (orbit_symm (ho₁ w)) this
    exact RW.inj w w' (Proj.not_mem_mcPts_top _) (orbit_of_two g₀ g₁)
  · intro p hp
    have key : ∀ w, FA.S.ph (some p) (FA.Re.π (h₀ w)) = FA.S.ph (some p) (FA.Re.π (h₁ w)) ∧
        ∀ t, FA.S.phT (some p) t (FA.Re.π (h₀ w)) = FA.S.phT (some p) t (FA.Re.π (h₁ w)) := by
      intro w
      refine FA.step_ph p (h₀ w) (h₁ w) ((hb₀ w).trans (hb₁ w).symm) ?_
      intro k hkp
      have hne : k ≠ k₀ := fun e => hp (M.blk_inj p (τ, a) k₀ (e ▸ hkp) hk)
      obtain ⟨c₀, -, e₀⟩ := ho₀ w
      obtain ⟨c₁, hc₁, e₁⟩ := ho₁ w
      refine ⟨c₀ k / c₁ k, fun m => ?_⟩
      have a₀ := congrFun e₀ ⟨k, m⟩
      have a₁ := congrFun e₁ ⟨k, m⟩
      simp only [Function.comp] at a₀ a₁
      rw [v₁_ne (p := ⟨k, m⟩) hne] at a₁
      rw [a₀, a₁]
      have := hc₁ k
      simp only [v₀]
      field_simp
    exact ⟨funext fun w => (key w).1, fun t => funext fun w => (key w).2 t⟩

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Pr
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentTwoFramesOrbit
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Indep

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem basePart_orbit {σ : Type} (blk : σ → Option K) {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    SameOrbit (basePart blk z) (basePart blk z') := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => c k.1, fun k => hc k.1, rfl⟩

theorem orbit_ne {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z' z) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    ∀ k, ∃ i, z' ⟨k, i⟩ ≠ 0 := by
  obtain ⟨c, hc, rfl⟩ := h
  intro k
  obtain ⟨i, hi⟩ := hz k
  exact ⟨i, mul_ne_zero (hc k) hi⟩

theorem eq_of_orbit_of_normalised {u v : (Σ k, ι k) → ℂ} (h : SameOrbit u v) (e : ∀ k, ι k)
    (hu : ∀ k, u ⟨k, e k⟩ = 1) (hv : ∀ k, v ⟨k, e k⟩ = 1) : u = v := by
  obtain ⟨c, hc, rfl⟩ := h
  have h1 : ∀ k, c k = 1 := fun k => by
    have h2 : c k * v ⟨k, e k⟩ = 1 := hu k
    rwa [hv k, mul_one] at h2
  funext p
  show c p.1 * v p = v p
  rw [h1 p.1, one_mul]

variable {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

theorem base_of_orbit (M : FlagModel y Ψ N j) {z z' : (Σ k, ι k) → ℂ} (ho : SameOrbit z z')
    (hz : basePart M.blk z ∈ mcPts (mCoordIdeal M.x)) :
    mCoordIdeal (basePart M.blk z') = mCoordIdeal (basePart M.blk z) ∧
      basePart M.blk z' ∈ mcPts (mCoordIdeal M.x) := by
  obtain ⟨c, hc, rfl⟩ := GlobalTheory.CompanionTheory.Ar.PB.WSq.orbit_symm ho
  have h := GlobalTheory.CompanionTheory.Ar.PB.StepW.TorusAct.main (NonPluckerBlocks M.blk) (baseIdx ι M.blk) M.Ω M.x (basePart M.blk z)
    (fun k => c k.1) (fun k => hc k.1)
  exact ⟨h.1, (h.2 hz).1⟩

theorem normRhs_indep : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (F F' : FrameData ι Ψ N M.Ω M.blk) (z₀ z₁ z₀' z₁' : (Σ k, ι k) → ℂ) (h h' : Matrix (Fin N) (Fin N) ℂ) (t t' : ℂ), basePart M.blk z₀ ∈ mcPts (mCoordIdeal M.x) → (∀ k, ∃ i, z₀ ⟨k, i⟩ ≠ 0) → (∀ k, ∃ i, z₁ ⟨k, i⟩ ≠ 0) → basePart M.blk z₁ = basePart M.blk z₀ → M.IsFrame F → M.IsFrame F' → M.GoodAt F (mCoordIdeal (basePart M.blk z₀)) → M.GoodAt F' (mCoordIdeal (basePart M.blk z₀')) → SameOrbit z₀ z₀' → SameOrbit z₁ z₁' → IsBlockDiag j h → h.det ≠ 0 → IsBlockDiag j h' → h'.det ≠ 0 → t ≠ 0 → t' ≠ 0 → (∀ i, M.ExactAt F (τ, i) z₀ h) → (∀ i, M.ExactAt F (τ, i) z₁ (h * (1 + Matrix.single cb ca t))) → (∀ i, M.ExactAt F' (τ, i) z₀' h') → (∀ i, M.ExactAt F' (τ, i) z₁' (h' * (1 + Matrix.single cb ca t'))) → normRhs M τ a F z₀ z₁ h t = normRhs M τ a F' z₀' z₁' h' t' := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M τ a b k₀ ca cb hab hstep hblk hca hcb F F' z₀ z₁ z₀' z₁' h h' t t' hmc hn₀ hn₁ hbase
    hF hF' hG hG' ho₀ ho₁ hh hd hh' hd' ht ht' hE₀ hE₁ hE₀' hE₁'
  obtain ⟨hid, hmc'⟩ := base_of_orbit M ho₀ hmc
  have hn₀' := orbit_ne (GlobalTheory.CompanionTheory.Ar.PB.WSq.orbit_symm ho₀) hn₀
  have hn₁' := orbit_ne (GlobalTheory.CompanionTheory.Ar.PB.WSq.orbit_symm ho₁) hn₁
  have hbase' : basePart M.blk z₁' = basePart M.blk z₀' := by
    have h1 : SameOrbit (basePart M.blk z₁') (basePart M.blk z₁) :=
      basePart_orbit M.blk (GlobalTheory.CompanionTheory.Ar.PB.WSq.orbit_symm ho₁)
    rw [hbase] at h1
    exact eq_of_orbit_of_normalised
      (GlobalTheory.CompanionTheory.Ar.PB.WSq.orbit_trans h1 (basePart_orbit M.blk ho₀)) F'.c (hE₁' a).1 (hE₀' a).1
  obtain ⟨w₀, w₁, S, hw₀, hw₁, hS, hSd, hX₀, hX₁, hnorm⟩ :=
    GlobalTheory.T.flag_adjacent_frame_comparison K ι Φ y Ψ N j M τ a b k₀ ca cb hab hstep hblk hca hcb F F' z₀' z₁' h' t' hmc' hn₀' hn₁' hbase'
      hF hF' (by rw [hid]; exact hG) hG' hh' hd' ht' hE₀' hE₁'
  rw [← hnorm]
  exact GlobalTheory.T.flag_adjacent_orbit_comparison K ι Φ y Ψ N j M τ a b k₀ ca cb hab hstep hblk hca hcb F z₀ z₁ w₀ w₁ h (S * h') t t' hmc hn₀ hn₁
    hbase hF hG (GlobalTheory.CompanionTheory.Ar.PB.WSq.orbit_trans ho₀ (GlobalTheory.CompanionTheory.Ar.PB.WSq.orbit_symm hw₀))
    (GlobalTheory.CompanionTheory.Ar.PB.WSq.orbit_trans ho₁ (GlobalTheory.CompanionTheory.Ar.PB.WSq.orbit_symm hw₁)) hh hd (hS.mul hh')
    (by rw [Matrix.det_mul]; exact mul_ne_zero hSd hd') ht ht' hE₀ hE₁ hX₀ hX₁

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Indep
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IntegralFibreSumChangeOfVariables
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.Giv.Push

theorem integrable_mInt_fibreSum {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) (q : X → Fin e → ℂ) (S : Set X) (G : X → ℝ)
    (hS : ∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' S) = 0)
    (hq : ∀ x ∉ S, ∀ j, x ∈ (A.chart j).source →
      AnalyticAt ℂ (q ∘ (A.chart j).symm) (A.chart j x) ∧
        LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) (A.chart j x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0)
    (hfin : ∀ y, (q ⁻¹' {y} \ S).Finite)
    (hsm : ∀ x ∉ S, ∀ i k, x ∈ (A.chart k).source →
      ContDiffAt ℝ 2 ((Φ i).φ x ∘ (A.chart k).symm) (A.chart k x))
    (hG : MIntegrable A Φ G) :
    Integrable (fun y => ∑ᶠ x ∈ q ⁻¹' {y} \ S, G x * pushDens A Φ q x) ∧
      mInt A Φ G = ∫ y, ∑ᶠ x ∈ q ⁻¹' {y} \ S, G x * pushDens A Φ q x := by
  classical
  have hne : Nonempty (ChartPartition A) := existsPartition A
  have hm : mInt A Φ G = integralWith A hne.some Φ G := by unfold mInt; rw [dif_pos hne]
  set Pt := hne.some with hPt
  set hj : Fin A.n → (Fin e → ℂ) → ℝ := fun j u =>
    Pt.χ j ((A.chart j).symm u) * G ((A.chart j).symm u) * locDens A Φ j u with hhj
  have hN : ∀ j, volume ((q ∘ (A.chart j).symm) '' (goodT A q j ∩ (A.chart j).symm ⁻¹' S)) = 0 := by
    intro j
    refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_ ?_
    · intro u hu
      exact (hu.1.2.1.differentiableAt.restrictScalars ℝ).differentiableWithinAt
    · exact measure_mono_null (Set.inter_subset_inter_left _ fun u (hu : u ∈ goodT A q j) => hu.1)
        (hS j)
  have hfinj : ∀ j, ∀ᵐ y, (goodT A q j ∩ (q ∘ (A.chart j).symm) ⁻¹' {y}).Finite := by
    intro j
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp (hN j)] with y hy
    rw [goodT_fibre_eq A q S hq j hy]
    exact ((hfin y).subset Set.inter_subset_right).image _
  have harea : ∀ j, Integrable (fibSum (goodT A q j) (q ∘ (A.chart j).symm) (hj j)) ∧
      ∫ u in goodT A q j, hj j u = ∫ y, fibSum (goodT A q j) (q ∘ (A.chart j).symm) (hj j) y :=
    fun j => area_open (isOpen_goodT A q j) (fun u hu => hu.2)
      ((integrableOn_chart A Pt Φ G hG j).mono_set fun u hu => hu.1) (hfinj j)
  have hset : ∀ j, ∫ u in (A.chart j).target, hj j u = ∫ u in goodT A q j, hj j u := by
    intro j
    refine setIntegral_congr_set (ae_eq_set.mpr ⟨?_, ?_⟩)
    · exact measure_mono_null (target_diff_goodT_subset A q S hq j) (hS j)
    · rw [Set.sdiff_eq_empty.mpr fun u hu => hu.1]; exact measure_empty
  have hterm : ∀ j x, x ∈ (A.chart j).source → x ∉ S →
      hj j (A.chart j x) / jacN (q ∘ (A.chart j).symm) (A.chart j x) =
        Pt.χ j x * (G x * pushDens A Φ q x) := by
    intro j x hx hxS
    simp only [hhj, (A.chart j).left_inv hx]
    rw [mul_div_assoc, locDens_div_jacN A Φ q S hq hsm j hx hxS, mul_assoc]
  have hae := sum_fibSum_ae A q S hN hq hfin Pt hj (fun x => G x * pushDens A Φ q x) hterm
  refine ⟨(integrable_finsetSum Finset.univ fun j _ => (harea j).1).congr hae, ?_⟩
  rw [hm]
  unfold integralWith
  have hsum : ∑ j, ∫ u in (A.chart j).target, hj j u =
      ∫ y, ∑ j, fibSum (goodT A q j) (q ∘ (A.chart j).symm) (hj j) y := by
    rw [integral_finsetSum _ fun j _ => (harea j).1]
    exact Finset.sum_congr rfl fun j _ => (hset j).trans (harea j).2
  exact hsum.trans (integral_congr_ae hae)

end GlobalTheory.CompanionTheory.Ar.Giv.Push
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ProjectionFormulaOfArithSystemStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projection_formula_of_arith_system : ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → PFStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.ProjF.projFormula | exact GlobalTheory.CompanionTheory.Ar.Giv.ProjF.projFormula | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.ProjF.projFormula <;> assumption)
end

