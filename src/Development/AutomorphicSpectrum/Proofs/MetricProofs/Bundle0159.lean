import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0042
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0122
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0072
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0050
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0059
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0058
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0088
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0061
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0120
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0137
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0142
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0145
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0130
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0071
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0134
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0150
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0057
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0114
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0053
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0143
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0131
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0083
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0136
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0067
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0068
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0139
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ChartImmersion
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0006
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0147
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0154
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0153
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0001

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentRowsResolution
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq
open GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan

theorem sameOrbit_baseOf {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]
    {y : (Σ k, ι k) → Φ} {Ψ : Type} {N j : ℕ} (M : FlagModel y Ψ N j) {k₀ : K}
    {z z' : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (h : SameOrbit z z') :
    SameOrbit (baseOf M k₀ z) (baseOf M k₀ z') := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => c (some k.1), fun k => hc _, rfl⟩

theorem sameOrbit_fstPt {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {k₀ : K}
    {z z' : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (h : SameOrbit z z') :
    SameOrbit (fstPt k₀ z) (fstPt k₀ z') := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => c (some k), fun k => hc _, rfl⟩

theorem sameOrbit_sndPt {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {k₀ : K}
    {z z' : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (h : SameOrbit z z') :
    SameOrbit (sndPt k₀ z) (sndPt k₀ z') := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => if k = k₀ then c none else c (some k), fun k => ?_, ?_⟩
  · dsimp only
    split_ifs
    exacts [hc _, hc _]
  · funext p
    obtain ⟨k, m⟩ := p
    by_cases e : k = k₀
    · subst e
      simp only [sndPt, Function.comp, v₁_self, if_true]
    · simp only [sndPt, Function.comp, v₁_ne (show (⟨k, m⟩ : Σ k, ι k).1 ≠ k₀ from e), if_neg e]

theorem not_mem_mcPts_top {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (z : (Σ k, ι k) → ℂ) :
    z ∉ mcPts (⊤ : Ideal (MRing ι)) := fun h => by
  have := h.2 1 trivial
  simp at this

theorem fibreSquare_atlas : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsArithVar (mCoordIdeal y) (d + 2) → d + 1 = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) → ∃ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (pr : RW.X → Rb.X), IsWAtlas M Rb τ a k₀ ca cb RW pr := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d Rb τ a b k₀ ca cb hb hab hk hca hcb hy hd
  have hA := (GlobalTheory.T.flag_adjacent_swap_varieties_arithmetic K ι Φ y Ψ N j M d τ a b k₀ ca cb hb hab hk hca hcb hy).1
  obtain ⟨ε⟩ := GlobalTheory.T.flag_dimension_index_equiv Ψ N j n d M.j_le hd
  have hcov := GlobalTheory.T.flag_adjacent_arithmetic_height K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb hb hab hk hca hcb hy
  have mk : ∀ (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ))
      (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X)
      (h : Ψ → Matrix (Fin N) (Fin N) ℂ), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h →
      ∃ C : OrbitChart (wP M τ a k₀ ca cb) (d + 2), C.D = wD ε V ∧ C.φ = wPhi M F bl h ε k₀ τ ca cb ∧
        C.O = wO M Rb τ a k₀ ca cb F kb V r h := by
    intro F kb V bl r h hc
    have hV : IsOpen V := hc.2.2.2.2.2.2.2.1.1
    have hh := GlobalTheory.T.flag_adjacent_chart_first K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hc
    have hm := GlobalTheory.T.wPhi_mem_mcPts_wP K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hc
    have hr := GlobalTheory.T.flag_adjacent_chart_fourth K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hc
    have ho := GlobalTheory.T.flag_adjacent_chart_fifth K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hc
    have hO := GlobalTheory.T.flag_adjacent_chart_sixth K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h hc
    have hb' := GlobalTheory.T.flag_adjacent_chart_seventh K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hc
    have ht := GlobalTheory.T.flag_adjacent_chart_eighth K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hc
    have hi := GlobalTheory.T.flag_adjacent_chart_ninth K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hc
    exact ⟨{ D := wD ε V
             isOpen_D := hV.preimage (continuous_pi fun i => continuous_apply _)
             φ := wPhi M F bl h ε k₀ τ ca cb
             holo := hh
             mem := hm
             O := wO M Rb τ a k₀ ca cb F kb V r h
             O_open := hO
             O_orbit := fun z hz z' hz' e => (hb' z hz z' hz' e).1
             ρ := wRho M Rb τ k₀ ca cb F kb r h ε
             ρ_cont := ht
             ρ_orbit := fun z hz z' hz' e => (hb' z hz z' hz'.1 e).2
             φ_mem_O := fun w hw => (hr w hw).1
             ρ_φ := fun w hw => (hr w hw).2
             ρ_mem := fun z hz => (ho z hz).1
             φ_ρ := fun z hz => (ho z hz).2
             immersion := hi }, rfl, rfl, rfl⟩
  obtain ⟨R, hR⟩ := GlobalTheory.T.log_resolution_from_orbit_charts (Option K) (fun o => ι (o.getD k₀)) (wP M τ a k₀ ca cb) (d + 2) hA.1 hA.2.1.2.1
    (fun h => hA.2.1.1.ne_top (top_le_iff.mp h)) (fun z hz => by
      obtain ⟨F, kb, V, bl, r, h, hc, hzO⟩ := hcov z hz
      obtain ⟨C, -, -, hO⟩ := mk F kb V bl r h hc
      exact ⟨C, hO ▸ hzO⟩)

  have key : ∀ x : R.X, ∃ (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ))
      (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X)
      (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ψ : OpenPartialHomeomorph R.X (Fin (d + 2) → ℂ)),
      IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h ∧ IsCompatChart R.A ψ ∧ ψ.target = wD ε V ∧ x ∈ ψ.source ∧
        ∀ x' ∈ ψ.source, SameOrbit (wPhi M F bl h ε k₀ τ ca cb (ψ x')) (R.lift x' x') := by
    intro x
    obtain ⟨F, kb, V, bl, r, h, hc, hzO⟩ := hcov _ (R.mem x x (R.mem_U x))
    obtain ⟨C, hD, hφ, hO⟩ := mk F kb V bl r h hc
    obtain ⟨ψ, h1, h2, h3, h4⟩ := hR C ⟨_, R.mem x x (R.mem_U x)⟩
    exact ⟨F, kb, V, bl, r, h, ψ, hc, h1, h2.trans hD, (h3 x).2 (hO ▸ hzO), fun x' hx' => hφ ▸ h4 x' hx'⟩

  have hbase : ∀ x : R.X, ∃ x' : Rb.X, SameOrbit (Rb.lift x' x') (baseOf M k₀ (R.lift x x)) := by
    intro x
    obtain ⟨F, kb, V, bl, r, h, ψ, hc, -, hT, hx, hs⟩ := key x
    have hB := hc.2.2.2.2.2.2.2.1
    have hw : ψ x ∈ wD ε V := hT ▸ ψ.map_source hx
    have hE := (GlobalTheory.T.flag_adjacent_chart_second K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hc).2 _ hw
    refine ⟨(Rb.A.chart kb).symm (wB ε (ψ x)), orbit_trans (hB.2.2.2.2 _ hw).2.2.2 ?_⟩
    have := sameOrbit_baseOf M (hs x hx)
    rwa [hE.2.1] at this
  choose pr hpr using hbase
  have hcoord : ∀ (x : R.X) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ))
      (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X)
      (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ψ : OpenPartialHomeomorph R.X (Fin (d + 2) → ℂ)),
      IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h → ψ.target = wD ε V → x ∈ ψ.source →
      SameOrbit (wPhi M F bl h ε k₀ τ ca cb (ψ x)) (R.lift x x) →
      pr x ∈ (Rb.A.chart kb).source ∧ ∀ i, Rb.A.chart kb (pr x) i = ψ x (ε (Sum.inl i)) := by
    intro x F kb V bl r h ψ hc hT hx hs
    have hB := hc.2.2.2.2.2.2.2.1
    have hw : ψ x ∈ wD ε V := hT ▸ ψ.map_source hx
    have hE := (GlobalTheory.T.flag_adjacent_chart_second K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hc).2 _ hw
    have h1 : SameOrbit (bl (wB ε (ψ x))) (baseOf M k₀ (R.lift x x)) := by
      have := sameOrbit_baseOf M hs
      rwa [hE.2.1] at this
    have h2 := orbit_trans (hB.2.2.2.2 _ hw).2.2.2 (orbit_trans h1 (orbit_symm (hpr x)))
    have h3 : (Rb.A.chart kb).symm (wB ε (ψ x)) = pr x := Rb.inj _ _ (not_mem_mcPts_top _) h2
    have hwt : wB ε (ψ x) ∈ (Rb.A.chart kb).target := hB.2.1 hw
    rw [← h3]
    exact ⟨(Rb.A.chart kb).map_target hwt, fun i => by
      rw [(Rb.A.chart kb).right_inv hwt]
      rfl⟩
  refine ⟨R, pr, ?_, hpr, fun x => ?_⟩
  · refine GlobalTheory.T.holoMap_of_local_product_charts (d + 2) n R.X Rb.X R.A Rb.A pr fun x => ?_
    obtain ⟨F, kb, V, bl, r, h, ψ, hc, hC, hT, hx, hs⟩ := key x
    exact ⟨ψ, kb, fun i => ε (Sum.inl i), hC, hx, fun x' hx' => hcoord x' F kb V bl r h ψ hc hT hx' (hs x' hx')⟩
  · obtain ⟨F, kb, V, bl, r, h, ψ, hc, hC, hT, hx, hs⟩ := key x
    have hE := GlobalTheory.T.flag_adjacent_chart_second K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hc
    have hB := hc.2.2.2.2.2.2.2.1
    refine ⟨ψ, kb, ⟨fun i => ε (Sum.inl i), fun i i' e => Sum.inl_injective (ε.injective e)⟩, ε (Sum.inr (Sum.inr ())), F,
      fun τ' => wH h ε τ', hx, hC, hc.2.2.2.2.2.2.1, fun i e => Sum.inl_ne_inr (ε.injective e), fun x' hx' =>
        hcoord x' F kb V bl r h ψ hc hT hx' (hs x' hx'), fun τ' r' s' => hT ▸ hE.1 τ' r' s', fun x' hx' => ?_⟩
    have hw : ψ x' ∈ wD ε V := hT ▸ ψ.map_source hx'
    obtain ⟨e1, e2, e3⟩ := hE.2 _ hw
    have h1 := sameOrbit_baseOf M (hs x' hx')
    rw [e2] at h1
    refine ⟨e1, ?_, fstPt k₀ (wPhi M F bl h ε k₀ τ ca cb (ψ x')), sndPt k₀ (wPhi M F bl h ε k₀ τ ca cb (ψ x')),
      sameOrbit_fstPt (hs x' hx'), sameOrbit_sndPt (hs x' hx'), e3⟩
    have h2 : mCoordIdeal (bl (wB ε (ψ x'))) = mCoordIdeal (basePart M.blk (fstPt k₀ (R.lift x' x'))) :=
      GlobalTheory.CompanionTheory.Ar.PB.CovMap.mCoordIdeal_eq_of_sameOrbit h1
    exact h2 ▸ (hB.2.2.2.2 _ hw).2.2.1

end GlobalTheory.CompanionTheory.Ar.PB.WMan
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagBundlePartialBlockMap
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl
open GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.PB.WMan.Gen

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.PFl

theorem exists_res {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {e : ℕ}
    (hP : IsMultiHomogIdeal P) (hnd : ¬ (⊤ : Ideal (MRing ι)) ≤ P)
    (hcov : ∀ z ∈ mcPts P, ∃ C : OrbitChart P e, z ∈ C.O) :
    ∃ R : AnLogRes P ⊤ e, ∀ C : OrbitChart P e, (mcPts P).Nonempty → ∃ ψ : OpenPartialHomeomorph R.X (Fin e → ℂ),
      IsCompatChart R.A ψ ∧ ψ.target = C.D ∧ (∀ x, x ∈ ψ.source ↔ R.lift x x ∈ C.O) ∧
        ∀ x ∈ ψ.source, SameOrbit (C.φ (ψ x)) (R.lift x x) := by
  have h' : ∀ x : PtsOf P, ∃ C : OrbitChart P e, x ∈ srcOf C := fun x => hcov _ (rep_mem_mcPts x)
  choose Cx hCx using h'
  haveI : CompactSpace (PtsOf P) := Top.compactSpace_pts (isMultiHomogIdeal_pC hP)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_nhds_subcover (fun x => srcOf (Cx x))
    (fun x _ => (isOpen_srcOf hP _).mem_nhds (hCx x))
  have hc : ∀ x, ∃ y ∈ t, x ∈ srcOf (Cx y) := fun x => by
    simpa using ht.2 (Set.mem_univ x)
  refine ⟨resOf hP hnd Cx hCx t hc, fun C hne => ?_⟩
  obtain ⟨z, hz⟩ := hne
  have ho : ∀ x : PtsOf P, SameOrbit ((Cx x).φ ((Cx x).ρ (rep x))) (rep x) := fun x => (Cx x).φ_ρ _ (hCx x)
  have hm : ∀ x : PtsOf P, (Cx x).φ ((Cx x).ρ (rep x)) ∈ mcPts P := fun x => (Cx x).mem _ ((Cx x).ρ_mem _ (hCx x))
  refine ⟨orbChart hP C (cls z hz), isCompat_orbChart hP Cx t hc C _, rfl, fun x => ?_, fun x hx => ?_⟩
  · exact ⟨fun h => mem_O_of_orbit C hP h (ho x) (rep_mem_mcPts x),
      fun h => mem_O_of_orbit C hP h (Proj.orbit_symm (ho x)) (hm x)⟩
  · exact Proj.orbit_trans (C.φ_ρ _ hx) (Proj.orbit_symm (ho x))

theorem not_mem_top {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (z : (Σ k, ι k) → ℂ) :
    z ∉ mcPts (⊤ : Ideal (MRing ι)) := fun h => by
  have := h.2 1 trivial
  simp at this

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n), d = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) → ∀ (keep : Ψ × Fin N → Prop) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)), IsBlockMap κ v → (∀ k, k ∈ Set.range κ ↔ ((∀ p, M.blk p ≠ some k) ∨ ∃ p, keep p ∧ M.blk p = some k)) → ∃ (e : ℕ) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e), ((∀ p, keep p) → e = d) ∧ ∃ pr : R.X → Rb.X, HoloMap R.A Rb.A pr ∧ (∀ x, ∃ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift x x ∧ SameOrbit (basePart M.blk z) (Rb.lift (pr x) (pr x))) ∧ ∀ x, ∃ (ψ : OpenPartialHomeomorph R.X (Fin e → ℂ)) (kb : Fin Rb.A.n) (σ : Fin n ↪ Fin e), IsCompatChart R.A ψ ∧ x ∈ ψ.source ∧ (∀ x' ∈ ψ.source, pr x' ∈ (Rb.A.chart kb).source ∧ ∀ i, Rb.A.chart kb (pr x') i = ψ x' (σ i)) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d Rb hd keep Kk _ ιk _ κ v hb hrng
  obtain ⟨e, he, ⟨ε⟩⟩ : ∃ e, e = n + Nat.card (PIdx j keep) ∧ Nonempty (Fin n ⊕ PIdx j keep ≃ Fin e) :=
    ⟨_, rfl, ⟨(Equiv.sumCongr (Equiv.refl _) (Finite.equivFin _)).trans finSumFinEquiv⟩⟩
  have hP : IsMultiHomogIdeal (mCoordIdeal (y ∘ v)) := GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal _
  have hnd : ¬ (⊤ : Ideal (MRing ιk)) ≤ mCoordIdeal (y ∘ v) := fun h =>
    (RingHom.ker_isPrime _ : (mCoordIdeal (y ∘ v)).IsPrime).ne_top (top_le_iff.mp h)
  have hcov := GlobalTheory.CompanionTheory.Ar.PB.PFl.Cover.main K ι Φ y Ψ N j M n Rb keep Kk ιk κ v hb hrng
  have mk : ∀ (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ))
      (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X)
      (h : Ψ → Matrix (Fin N) (Fin N) ℂ), IsPCtx M Rb keep κ v F kb V bl r h →
      ∃ C : OrbitChart (mCoordIdeal (y ∘ v)) e, C.D = pD ε V ∧ C.φ = pPhi M F keep v bl h ε ∧
        C.O = pO M Rb keep v F kb V r h := by
    intro F kb V bl r h hc
    have hV : IsOpen V := hc.2.2.2.1.1
    have hh := GlobalTheory.CompanionTheory.Ar.PB.PFl.Holo.pPhi_holo K ι Φ y Ψ N j M n e Rb keep Kk ιk κ v F kb V bl r h ε hc
    have hr := GlobalTheory.CompanionTheory.Ar.PB.PFl.ChartRead.chart_reads K ι Φ y Ψ N j M n e Rb keep Kk ιk κ v F kb V bl r h ε hc
    have ho := GlobalTheory.CompanionTheory.Ar.PB.PFl.Onto.main K ι Φ y Ψ N j M n e Rb keep Kk ιk κ v F kb V bl r h ε hc
    have hO := GlobalTheory.CompanionTheory.Ar.PB.PFl.POpn.main K ι Φ y Ψ N j M n e Rb keep Kk ιk κ v F kb V bl r h ε hc
    have hb' := GlobalTheory.CompanionTheory.Ar.PB.PFl.Orb.main K ι Φ y Ψ N j M n e Rb keep Kk ιk κ v F kb V bl r h ε hc
    have ht := GlobalTheory.CompanionTheory.Ar.PB.PFl.PCont.main K ι Φ y Ψ N j M n e Rb keep Kk ιk κ v F kb V bl r h ε hc
    have hi := GlobalTheory.CompanionTheory.Ar.PB.PFl.Imm.chart_immersion K ι Φ y Ψ N j M n e Rb keep Kk ιk κ v F kb V bl r h ε hc
    exact ⟨{ D := pD ε V
             isOpen_D := hV.preimage (continuous_pi fun i => continuous_apply _)
             φ := pPhi M F keep v bl h ε
             holo := hh
             mem := fun w hw => (hr w hw).1.1
             O := pO M Rb keep v F kb V r h
             O_open := hO
             O_orbit := fun z hz z' hz' e => (hb' z hz z' hz' e).1
             ρ := pRho M Rb keep v F kb r h ε
             ρ_cont := ht
             ρ_orbit := fun z hz z' hz' e => (hb' z hz z' hz'.1 e).2
             φ_mem_O := fun w hw => (hr w hw).1
             ρ_φ := fun w hw => (hr w hw).2
             ρ_mem := fun z hz => (ho z hz).1
             φ_ρ := fun z hz => (ho z hz).2
             immersion := hi }, rfl, rfl, rfl⟩
  obtain ⟨R, hR⟩ := exists_res (e := e) hP hnd (fun z hz => by
    obtain ⟨F, kb, V, bl, r, h, hc, hzO⟩ := hcov z hz
    obtain ⟨C, -, -, hO⟩ := mk F kb V bl r h hc
    exact ⟨C, hO ▸ hzO⟩)

  have key : ∀ x : R.X, ∃ (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ))
      (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X)
      (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ψ : OpenPartialHomeomorph R.X (Fin e → ℂ)),
      IsPCtx M Rb keep κ v F kb V bl r h ∧ IsCompatChart R.A ψ ∧ ψ.target = pD ε V ∧ x ∈ ψ.source ∧
        ∀ x' ∈ ψ.source, SameOrbit (pPhi M F keep v bl h ε (ψ x')) (R.lift x' x') := by
    intro x
    obtain ⟨F, kb, V, bl, r, h, hc, hzO⟩ := hcov _ (R.mem x x (R.mem_U x))
    obtain ⟨C, hD, hφ, hO⟩ := mk F kb V bl r h hc
    obtain ⟨ψ, h1, h2, h3, h4⟩ := hR C ⟨_, R.mem x x (R.mem_U x)⟩
    exact ⟨F, kb, V, bl, r, h, ψ, hc, h1, h2.trans hD, (h3 x).2 (hO ▸ hzO), fun x' hx' => hφ ▸ h4 x' hx'⟩
  have hob := (GlobalTheory.CompanionTheory.Ar.PB.PFl.PtsBase.main K ι Φ y Ψ N j M keep Kk ιk κ v hb hrng).2

  have hbase : ∀ x : R.X, ∃ x' : Rb.X, SameOrbit (Rb.lift x' x') (pBase M v (R.lift x x)) := by
    intro x
    obtain ⟨F, kb, V, bl, r, h, ψ, hc, -, hT, hx, hs⟩ := key x
    have hB : IsBaseChart M Rb F kb V bl := hc.2.2.2.1
    have hw : ψ x ∈ pD ε V := hT ▸ ψ.map_source hx
    have hE := GlobalTheory.CompanionTheory.Ar.PB.PFl.Exact.chart_points K ι Φ y Ψ N j M n e Rb keep Kk ιk κ v F kb V bl r h ε hc _ hw
    refine ⟨(Rb.A.chart kb).symm (pB ε (ψ x)), orbit_trans (hB.2.2.2.2 _ hw).2.2.2 ?_⟩
    have := hob _ _ (hs x hx)
    rwa [hE.2.1] at this
  choose pr hpr using hbase
  have hcoord : ∀ (x : R.X) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ))
      (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X)
      (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ψ : OpenPartialHomeomorph R.X (Fin e → ℂ)),
      IsPCtx M Rb keep κ v F kb V bl r h → ψ.target = pD ε V → x ∈ ψ.source →
      SameOrbit (pPhi M F keep v bl h ε (ψ x)) (R.lift x x) →
      pr x = (Rb.A.chart kb).symm (pB ε (ψ x)) ∧ pr x ∈ (Rb.A.chart kb).source ∧
        ∀ i, Rb.A.chart kb (pr x) i = ψ x (ε (Sum.inl i)) := by
    intro x F kb V bl r h ψ hc hT hx hs
    have hB : IsBaseChart M Rb F kb V bl := hc.2.2.2.1
    have hw : ψ x ∈ pD ε V := hT ▸ ψ.map_source hx
    have hE := GlobalTheory.CompanionTheory.Ar.PB.PFl.Exact.chart_points K ι Φ y Ψ N j M n e Rb keep Kk ιk κ v F kb V bl r h ε hc _ hw
    have h1 : SameOrbit (bl (pB ε (ψ x))) (pBase M v (R.lift x x)) := by
      have := hob _ _ hs
      rwa [hE.2.1] at this
    have h2 := orbit_trans (hB.2.2.2.2 _ hw).2.2.2 (orbit_trans h1 (orbit_symm (hpr x)))
    have h3 : (Rb.A.chart kb).symm (pB ε (ψ x)) = pr x := Rb.inj _ _ (not_mem_top _) h2
    have hwt : pB ε (ψ x) ∈ (Rb.A.chart kb).target := hB.2.1 hw
    rw [← h3]
    exact ⟨rfl, (Rb.A.chart kb).map_target hwt, fun i => by
      rw [(Rb.A.chart kb).right_inv hwt]
      rfl⟩
  have hlast : ∀ x, ∃ (ψ : OpenPartialHomeomorph R.X (Fin e → ℂ)) (kb : Fin Rb.A.n) (σ : Fin n ↪ Fin e),
      IsCompatChart R.A ψ ∧ x ∈ ψ.source ∧ (∀ x' ∈ ψ.source, pr x' ∈ (Rb.A.chart kb).source ∧
        ∀ i, Rb.A.chart kb (pr x') i = ψ x' (σ i)) := by
    intro x
    obtain ⟨F, kb, V, bl, r, h, ψ, hc, hψ, hT, hx, hs⟩ := key x
    refine ⟨ψ, kb, ⟨fun i => ε (Sum.inl i), fun a b e' => Sum.inl_injective (ε.injective e')⟩, hψ, hx, fun x' hx' => ?_⟩
    obtain ⟨-, h1, h2⟩ := hcoord x' F kb V bl r h ψ hc hT hx' (hs x' hx')
    exact ⟨h1, h2⟩
  refine ⟨e, R, ?_, pr, ?_, ?_, hlast⟩
  · intro hall
    rw [he, GlobalTheory.CompanionTheory.Ar.PB.PFl.AllKept.card_pIdx_of_all Ψ N j keep M.j_le hall, hd]
  · refine GlobalTheory.CompanionTheory.Ar.PB.WMan.Coord.holoMap_of_coord e n R.X Rb.X R.A Rb.A pr fun x => ?_
    obtain ⟨ψ, kb, σ, h1, h2, h3⟩ := hlast x
    exact ⟨ψ, kb, σ, h1, h2, h3⟩
  · intro x
    obtain ⟨F, kb, V, bl, r, h, ψ, hc, -, hT, hx, hs⟩ := key x
    have hB : IsBaseChart M Rb F kb V bl := hc.2.2.2.1
    have hw : ψ x ∈ pD ε V := hT ▸ ψ.map_source hx
    obtain ⟨z₀, hz₀, hzv, hzb⟩ := GlobalTheory.CompanionTheory.Ar.PB.PFl.Ext.main K ι Φ y Ψ N j M n e Rb keep Kk ιk κ v F kb V bl r h ε hc _ hw
    obtain ⟨hpe, -, -⟩ := hcoord x F kb V bl r h ψ hc hT hx (hs x hx)
    obtain ⟨c, hc0, hce⟩ := orbit_symm (hs x hx)
    let c' : K → ℂ := fun k => if hk : ∃ k', κ k' = k then c hk.choose else 1
    have hc'0 : ∀ k, c' k ≠ 0 := fun k => by
      simp only [c']
      split_ifs
      · exact hc0 _
      · exact one_ne_zero
    have hc'κ : ∀ k', c' (κ k') = c k' := fun k' => by
      have hk : ∃ k'', κ k'' = κ k' := ⟨k', rfl⟩
      simp only [c']
      rw [dif_pos hk, hb.1 hk.choose_spec]
    have hyP : IsMultiHomogIdeal (mCoordIdeal y) := GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal _
    refine ⟨fun p => c' p.1 * z₀ p, mcPts_smul hyP c' hc'0 hz₀, ?_, ?_⟩
    · funext q
      have e1 : z₀ (v q) = pPhi M F keep v bl h ε (ψ x) q := congrFun hzv q
      have e2 := congrFun hce q
      show c' (v q).1 * z₀ (v q) = _
      rw [e2, e1, hb.2.2.1 q, hc'κ]
    · have h1 : SameOrbit (fun q => c' q.1.1 * basePart M.blk z₀ q) (bl (pB ε (ψ x))) := by
        rw [hzb]
        exact ⟨fun k => c' k.1, fun k => hc'0 _, rfl⟩
      have h2 : (basePart M.blk fun p => c' p.1 * z₀ p) = fun q => c' q.1.1 * basePart M.blk z₀ q := rfl
      rw [h2, hpe]
      exact orbit_trans h1 (orbit_symm (hB.2.2.2.2 _ hw).2.2.2)

end GlobalTheory.CompanionTheory.Ar.PB.PFl
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HolomorphicCoefficientsInFrame
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart

theorem differentiableOn_coeff_of_linearIndependent (n m g : ℕ) (U : Set (Fin n → ℂ))
    (d : Fin m → (Fin n → ℂ) → Fin g → ℂ) (x : (Fin n → ℂ) → Fin g → ℂ)
    (w : (Fin n → ℂ) → Fin m → ℂ) (hU : IsOpen U)
    (hd : ∀ b, DifferentiableOn ℂ (d b) U) (hx : DifferentiableOn ℂ x U)
    (hli : ∀ t ∈ U, LinearIndependent ℂ (fun b => d b t))
    (hw : ∀ t ∈ U, x t = ∑ b, w t b • d b t) : DifferentiableOn ℂ w U := by
  intro t₀ ht₀
  apply DifferentiableAt.differentiableWithinAt
  have hUn : U ∈ 𝓝 t₀ := hU.mem_nhds ht₀

  let φ : (Fin m → ℂ) →ₗ[ℂ] (Fin g → ℂ) := Fintype.linearCombination ℂ (fun b => d b t₀)
  have hφ : LinearMap.ker φ = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    have h0 := Fintype.linearIndependent_iff.1 (hli t₀ ht₀) v
      (by simpa [φ, Fintype.linearCombination_apply] using hv)
    exact funext h0
  obtain ⟨L0, hL0⟩ := φ.exists_leftInverse_of_injective hφ
  let L : (Fin g → ℂ) →L[ℂ] (Fin m → ℂ) := LinearMap.toContinuousLinearMap L0
  have hLd : ∀ b, L (d b t₀) = Pi.single b 1 := by
    intro b
    have h1 : φ (Pi.single b 1) = d b t₀ := by
      simp [φ, Fintype.linearCombination_apply, Pi.single_apply]
    have h2 := LinearMap.congr_fun hL0 (Pi.single b 1)
    simp only [LinearMap.comp_apply, LinearMap.id_apply, h1] at h2
    exact h2
  let T : (Fin n → ℂ) → ((Fin m → ℂ) →L[ℂ] (Fin m → ℂ)) := fun t =>
    ∑ b, (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin m => ℂ) b).smulRight (L (d b t))
  have hTapply : ∀ t v, T t v = ∑ b, v b • L (d b t) := by
    intro t v
    simp [T, ContinuousLinearMap.sum_apply]
  have hT0 : T t₀ = 1 := by
    apply ContinuousLinearMap.ext
    intro v
    rw [hTapply]
    simp only [hLd]
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  have hTd : DifferentiableAt ℂ T t₀ := by
    have hb : ∀ b ∈ (Finset.univ : Finset (Fin m)), DifferentiableAt ℂ (fun t =>
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin m => ℂ) b).smulRight (L (d b t))) t₀ := by
      intro b _
      exact (ContinuousLinearMap.smulRightL ℂ (Fin m → ℂ) (Fin m → ℂ)
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin m => ℂ) b)).differentiableAt.comp t₀
        (L.differentiableAt.comp t₀ ((hd b).differentiableAt hUn))
    exact DifferentiableAt.fun_sum hb
  have hTu : ∀ᶠ t in 𝓝 t₀, IsUnit (T t) := by
    have hc : ContinuousAt T t₀ := hTd.continuousAt
    have : {u : (Fin m → ℂ) →L[ℂ] (Fin m → ℂ) | IsUnit u} ∈ 𝓝 (T t₀) := by
      rw [hT0]
      exact Units.isOpen.mem_nhds isUnit_one
    exact hc this
  have heq : w =ᶠ[𝓝 t₀] fun t => Ring.inverse (T t) (L (x t)) := by
    filter_upwards [hTu, hUn] with t hu ht
    obtain ⟨u, hu'⟩ := hu
    have h1 : L (x t) = T t (w t) := by
      rw [hw t ht, hTapply, map_sum]
      simp
    rw [h1, ← hu', Ring.inverse_unit, ← ContinuousLinearMap.mul_apply, u.inv_mul]
    rfl
  refine DifferentiableAt.congr_of_eventuallyEq ?_ heq
  have hinv : DifferentiableAt ℂ (fun t => Ring.inverse (T t)) t₀ := by
    have : DifferentiableAt ℂ Ring.inverse (T t₀) := by
      rw [hT0]
      exact differentiableAt_inverse isUnit_one
    exact this.comp t₀ hTd
  have hLx : DifferentiableAt ℂ (fun t => L (x t)) t₀ :=
    L.differentiableAt.comp t₀ (hx.differentiableAt hUn)
  exact hinv.clm_apply hLx

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HolomorphicEigenProjectionOnBall
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart

theorem perExt_differentiableOn {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] {j j' n g : ℕ}
    {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ] {F : UnivFam E Ψ j j' n g Λ} (C : LatEmb F)
    (y : Ψ → Fin (j + j') → ℂ) :
    DifferentiableOn ℂ (fun t => C.perExt (F.R t) y) (ballDom F.q) := by
  have h : (fun t => C.perExt (F.R t) y) =
      fun t => ∑ k, C.bas.equivFun y k • (F.R t).P (C.lam k) := by
    funext t
    exact Module.Basis.constr_apply_fintype ℝ C.bas _ y
  rw [h]
  refine DifferentiableOn.fun_sum fun k _ => ?_
  exact (F.hol.2 (C.lam k)).const_smul (C.bas.equivFun y k)

theorem pPart_differentiableOn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F) (τ : Ψ) (y : Fin (j + j') → ℂ), DifferentiableOn ℂ (fun t => C.pPart (F.R t) τ y) (ballDom F.q) := by
  intro E _ _ _ Ψ _ j j' n g Λ _ _ F C τ y
  classical
  unfold LatEmb.pPart
  exact ((perExt_differentiableOn C _).sub
    ((perExt_differentiableOn C _).const_smul Complex.I)).const_smul (1 / 2 : ℂ)

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LatticeRationalEmbeddingStatement
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_rational_embedding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ], ∃ N : ℕ, Module.finrank ℚ E * N = Module.finrank ℤ Λ ∧ ∃ e : Λ →+ (Fin N → E), Function.Injective e ∧ (∀ (a : 𝓞 E) x, e (a • x) = (a : E) • e x) ∧ ∀ v : Fin N → E, ∃ (k : ℕ) (x : Λ), k ≠ 0 ∧ e x = k • v := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatticeCoordinates.exists_embedding | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatticeCoordinates.exists_embedding | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatticeCoordinates.exists_embedding <;> assumption)
end

