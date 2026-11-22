import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0607
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1437
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1361
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0601
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0563
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0041
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0602
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1369
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1414
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetGramRatOneNeZero
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLemmas.ToComplBijective

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LimitLists
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation

namespace GlobalTheory.CompanionTheory.EGlue

section LimLists

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem limL_allLeaves_strip (P : ∀ M : ℕ, Submodule ℂ (Sm E M) → Prop) :
    ∀ {N : ℕ} (t : Tr E N), t.strip.AllLeaves P ↔ t.AllLeaves P := by
  intro N t
  induction t with
  | leaf V z => exact Iff.rfl
  | node t₁ t₂ i₁ i₂ => exact and_congr i₁ i₂

theorem limL_allLeaves_shift (P : ∀ M : ℕ, Submodule ℂ (Sm E M) → Prop) (z : ℂ) :
    ∀ {N : ℕ} (t : Tr E N), (t.shift z).AllLeaves P ↔ t.AllLeaves P := by
  intro N t
  induction t with
  | leaf V z' => exact Iff.rfl
  | node t₁ t₂ i₁ i₂ => exact and_congr i₁ i₂

theorem limL_allLeaves_mono {P Q : ∀ M : ℕ, Submodule ℂ (Sm E M) → Prop} (h : ∀ M V, P M V → Q M V) :
    ∀ {N : ℕ} {t : Tr E N}, t.AllLeaves P → t.AllLeaves Q := by
  intro N t
  induction t with
  | leaf V z => exact h _ _
  | node t₁ t₂ i₁ i₂ => exact fun a => ⟨i₁ a.1, i₂ a.2⟩

theorem limL_disc_shift (z : ℂ) : ∀ {N : ℕ} {t : Tr E N}, t.AllLeaves (fun M _ => 0 < M) → t.Disc → (t.shift z).Disc := by
  intro N t
  induction t with
  | leaf V z' =>
    intro hp h
    rcases h with h | h
    · exact absurd h.1 (Nat.ne_of_gt (show 0 < _ from hp))
    · exact Or.inr h
  | node t₁ t₂ i₁ i₂ => exact fun hp h => ⟨i₁ hp.1 h.1, i₂ hp.2 h.2⟩

theorem limL_good_shift {z : ℂ} (hz : z.re = 0) :
    ∀ {N : ℕ} {t : Tr E N}, t.AllLeaves (fun M _ => 0 < M) → t.Good → (t.shift z).Good := by
  intro N t
  induction t with
  | leaf V z' =>
    intro hp h
    rcases h with h | h
    · exact absurd h.1 (Nat.ne_of_gt (show 0 < _ from hp))
    · exact Or.inr ⟨h.1, h.2.1, by simp [h.2.2, hz]⟩
  | node t₁ t₂ i₁ i₂ => exact fun hp h => ⟨i₁ hp.1 h.1, i₂ hp.2 h.2⟩

def LimDiscBody (E : Type) [Field E] [NumberField E] [IsCMField E] (M : ℕ) (W : Submodule ℂ (Kinf E M → ℂ))
    (K : Subgroup (GL (Fin M) (Af E))) (Ω : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ)))
    (Θ : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E)))) : Prop :=
  ∀ [MeasurableSpace (GA E M)] [BorelSpace (GA E M)] (μ : Measure (GA E M)) [μ.IsHaarMeasure] (R : ℝ), 0 < M →
  ReproAll E →
  ∀ V : ℕ → Submodule ℂ (Sm E M), (∀ k, IsDiscrete (V k)) → (∀ k, HasType K W (V k)) → (∀ k, InfBdd R (V k)) →
  ∃ (φ : ℕ → ℕ) (t : ℕ → Tr E M) (t₀ : Tr E M), StrictMono φ ∧ t₀.Good ∧ (∀ k, (t k).Disc) ∧
    (∀ k, (t k).strip = t₀.strip) ∧
    t₀.AllLeaves (fun M V => 0 < M ∧ ∃ K' ∈ Θ M, ∃ W' ∈ Ω M, HasType K' W' V) ∧
    (∀ i, Tendsto (fun k => ((t k).twists.getD i 0)) atTop (𝓝 (t₀.twists.getD i 0))) ∧
    ∀ k, Emb (V (φ k)) (· ∈ (t k).space)

theorem limL_exists_haar (M : ℕ) : ∃ (_ : MeasurableSpace (GA E M)) (_ : BorelSpace (GA E M)) (μ : Measure (GA E M)),
    μ.IsHaarMeasure := by
  letI : MeasurableSpace (GA E M) := borel _
  haveI : BorelSpace (GA E M) := ⟨rfl⟩
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.locallyCompactSpace_GA E M
  exact ⟨_, inferInstance, Measure.haar, inferInstance⟩

theorem limL_lim_one (hS : ConvStrip) (hSh : ConvShift) (hC : ConvComp) (hT : TwShift) {M : ℕ} (hM : 0 < M)
    {W : Submodule ℂ (Kinf E M → ℂ)} {K : Subgroup (GL (Fin M) (Af E))}
    {Ω : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ))} {Θ : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E)))}
    (hB : LimDiscBody E M W K Ω Θ) (V : ℕ → Submodule ℂ (Sm E M)) (z : ℕ → ℂ) (R : ℝ) (hR : ReproAll E)
    (hD : ∀ k, IsDiscrete (V k)) (hz : ∀ k, (z k).re = 0) (hTy : ∀ k, HasType K W (V k))
    (hI : ∀ k, InfBdd R (V k)) (hzR : ∀ k, ‖z k‖ ≤ R) :
    ∃ (φ : ℕ → ℕ) (t : ℕ → Tr E M) (s : Tr E M), StrictMono φ ∧ Conv t s ∧ Red s ∧ s.Good ∧
      s.AllLeaves (fun M V => 0 < M ∧ ∃ K' ∈ Θ M, ∃ W' ∈ Ω M, HasType K' W' V) ∧ (∀ k, (t k).Disc) ∧
      ∀ k, Emb (tw (V (φ k)) (z (φ k))) (· ∈ (t k).space) := by
  obtain ⟨_, _, μ, _⟩ := limL_exists_haar (E := E) M
  obtain ⟨φ, tt, t₀, hφ, hG, hDt, hst, hL, htw, hE⟩ := hB μ R hM hR V hD hTy hI
  obtain ⟨z₀, hz₀, ψ, hψ, hlim⟩ := tendsto_subseq_of_bounded (x := fun k => z (φ k))
    (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := R)) (fun k => by simpa using hzR (φ k))
  have hre : z₀.re = 0 := by
    have h1 : Tendsto (fun k => (z (φ (ψ k))).re) atTop (𝓝 z₀.re) :=
      (Complex.continuous_re.tendsto z₀).comp hlim
    simp only [hz, ] at h1
    exact (tendsto_nhds_unique h1 tendsto_const_nhds)
  have hpos : t₀.AllLeaves (fun M _ => 0 < M) := limL_allLeaves_mono (fun _ _ h => h.1) hL
  have hposk : ∀ k, (tt k).AllLeaves (fun M _ => 0 < M) := fun k => by
    rw [← limL_allLeaves_strip, hst k, limL_allLeaves_strip]
    exact hpos
  have hconv : Conv tt t₀ := (hS E M tt t₀).2 ⟨hst, htw⟩
  have hconv' : Conv (fun k => (tt (ψ k)).shift (z (φ (ψ k)))) (t₀.shift z₀) :=
    hSh E M _ t₀ _ z₀ (hC E M tt t₀ ψ hconv hψ) hlim
  have hL' : (t₀.shift z₀).AllLeaves (fun M V => 0 < M ∧ ∃ K' ∈ Θ M, ∃ W' ∈ Ω M, HasType K' W' V) :=
    (limL_allLeaves_shift _ _ _).2 hL
  exact ⟨fun k => φ (ψ k), fun k => (tt (ψ k)).shift (z (φ (ψ k))), t₀.shift z₀, hφ.comp hψ, hconv',
    red_of_leaves hL', limL_good_shift hre hpos hG, hL', fun k => limL_disc_shift _ (hposk _) (hDt _),
    fun k => hT E M _ _ _ (hD _).stable (hE _)⟩

end LimLists

theorem limLists : ConvStrip → ConvShift → ConvComp → LimLists := by
  intro hS hSh hC h5 hT E _ _ _ N Ωs hΩs
  have h1 : ∀ (M : ℕ) (W : Submodule ℂ (Kinf E M → ℂ)),
      ∃ Ω : ∀ M' : ℕ, Set (Submodule ℂ (Kinf E M' → ℂ)), KTypes E Ω ∧
        (FiniteDimensional ℂ W → ∀ K : Subgroup (GL (Fin M) (Af E)), IsOpen (K : Set (GL (Fin M) (Af E))) →
          ∃ Θ : ∀ M' : ℕ, Set (Subgroup (GL (Fin M') (Af E))), Levels E Θ ∧ LimDiscBody E M W K Ω Θ) := by
    intro M W
    by_cases hW : FiniteDimensional ℂ W
    · obtain ⟨Ω, hΩ, h⟩ := h5 E M W hW
      exact ⟨Ω, hΩ, fun _ K hK => h K hK⟩
    · exact ⟨fun _ => ∅, fun _ => ⟨Set.finite_empty, by simp⟩, fun h => absurd h hW⟩
  choose Om hOm hOm' using h1
  refine ⟨fun M' => ⋃ M ∈ Set.Icc 1 N, ⋃ W ∈ Ωs M, Om M W M', ?_, ?_⟩
  · intro M'
    refine ⟨(Set.finite_Icc 1 N).biUnion fun M _ => (hΩs M).1.biUnion fun W _ => (hOm M W M').1, ?_⟩
    intro W' hW'
    simp only [Set.mem_iUnion] at hW'
    obtain ⟨M, _, W, _, h⟩ := hW'
    exact (hOm M W M').2 W' h
  intro Θs hΘs
  have h2 : ∀ (M : ℕ) (W : Submodule ℂ (Kinf E M → ℂ)) (K : Subgroup (GL (Fin M) (Af E))),
      ∃ Θ : ∀ M' : ℕ, Set (Subgroup (GL (Fin M') (Af E))), Levels E Θ ∧
        (FiniteDimensional ℂ W → IsOpen (K : Set (GL (Fin M) (Af E))) → LimDiscBody E M W K (Om M W) Θ) := by
    intro M W K
    by_cases h : FiniteDimensional ℂ W ∧ IsOpen (K : Set (GL (Fin M) (Af E)))
    · obtain ⟨Θ, hΘ, hb⟩ := hOm' M W h.1 K h.2
      exact ⟨Θ, hΘ, fun _ _ => hb⟩
    · exact ⟨fun _ => ∅, fun _ => ⟨Set.finite_empty, by simp⟩, fun a b => absurd ⟨a, b⟩ h⟩
  choose Th hTh hTh' using h2
  refine ⟨fun M' => ⋃ M ∈ Set.Icc 1 N, ⋃ W ∈ Ωs M, ⋃ K ∈ Θs M, Th M W K M', ?_, ?_⟩
  · intro M'
    refine ⟨(Set.finite_Icc 1 N).biUnion fun M _ => (hΩs M).1.biUnion fun W _ =>
      (hΘs M).1.biUnion fun K _ => (hTh M W K M').1, ?_⟩
    intro K' hK'
    simp only [Set.mem_iUnion] at hK'
    obtain ⟨M, _, W, _, K, _, h⟩ := hK'
    exact (hTh M W K M').2 K' h
  intro M hM hMN V z R hR hD hz hTy hI hzR
  choose Kk hKk Wk hWk hty using hTy
  have hfin : (Θs M ×ˢ Ωs M).Finite := (hΘs M).1.prod (hΩs M).1
  haveI := hfin.to_subtype
  obtain ⟨⟨⟨K, W⟩, hKW⟩, hinf⟩ := Finite.exists_infinite_fiber
    (fun k : ℕ => (⟨(Kk k, Wk k), hKk k, hWk k⟩ : ↥(Θs M ×ˢ Ωs M)))
  have hfr : ∃ᶠ k in atTop, Kk k = K ∧ Wk k = W := by
    refine Nat.frequently_atTop_iff_infinite.2 ((Set.infinite_coe_iff.1 hinf).mono ?_)
    intro k hk
    have h := congrArg Subtype.val (Set.mem_singleton_iff.1 (Set.mem_preimage.1 hk))
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  obtain ⟨a, ha, hak⟩ := extraction_of_frequently_atTop hfr
  have hK : K ∈ Θs M := hKW.1
  have hW : W ∈ Ωs M := hKW.2
  have hbody : LimDiscBody E M W K (Om M W) (Th M W K) := hTh' M W K ((hΩs M).2 W hW) ((hΘs M).2 K hK)
  have htyp : ∀ k, HasType K W (V (a k)) := fun k => by
    have h := hty (a k)
    rwa [(hak k).1, (hak k).2] at h
  obtain ⟨φ, t, s, hφ, hc, hr, hg, hl, hd, he⟩ := limL_lim_one hS hSh hC hT hM hbody (fun k => V (a k))
    (fun k => z (a k)) R hR (fun k => hD _) (fun k => hz _) htyp (fun k => hI _) (fun k => hzR _)
  refine ⟨fun k => a (φ k), t, s, ha.comp hφ, hc, hr, hg, limL_allLeaves_mono ?_ hl, hd, he⟩
  rintro M' V' ⟨-, K'', hK'', W'', hW'', h⟩
  refine Or.inr ⟨K'', ?_, W'', ?_, h⟩
  · simp only [Set.mem_iUnion]
    exact ⟨M, ⟨hM, hMN⟩, W, hW, K, hK, hK''⟩
  · simp only [Set.mem_iUnion]
    exact ⟨M, ⟨hM, hMN⟩, W, hW, hW''⟩

end GlobalTheory.CompanionTheory.EGlue

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LimitTrees
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.EGlue

namespace GlobalTheory.CompanionTheory.EGlue.LimT

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def lr : {N : ℕ} → Tr E N → ℕ
  | _, .leaf _ _ => 0
  | _, @Tr.node _ _ _ _ r _ _ _ => r

theorem lr_le {N : ℕ} (u : Tr E N) : lr u ≤ N := by
  cases u with
  | leaf V z => exact Nat.zero_le _
  | node t₁ t₂ => exact Nat.le_add_right _ _

theorem leaf_of {N : ℕ} (u : Tr E N) (h : lr u = 0) (hr : Red u) : ∃ V z, u = .leaf V z := by
  cases u with
  | leaf V z => exact ⟨V, z, rfl⟩
  | node t₁ t₂ => exact absurd (show _ = 0 from h) hr.1.ne'

theorem node_of {n : ℕ} (u : Tr E n) {r s : ℕ} (h : n = r + s) (hl : lr u = r) (hr : 0 < r) (hred : Red u) :
    ∃ (t₁ : Tr E r) (t₂ : Tr E s), h ▸ u = Tr.node t₁ t₂ ∧ Red t₁ ∧ Red t₂ := by
  cases u with
  | leaf V z => exact absurd (show 0 = r from hl) hr.ne
  | @node r' s' t₁ t₂ =>
    have hl' : r' = r := hl
    subst hl'
    have hs : s' = s := by omega
    subst hs
    exact ⟨t₁, t₂, rfl, hred.2.2.1, hred.2.2.2⟩

theorem pigeon {n : ℕ} (c : ℕ → ℕ) (h : ∀ k, c k ≤ n) : ∃ (r : ℕ) (φ : ℕ → ℕ), StrictMono φ ∧ ∀ k, c (φ k) = r := by
  let f : ℕ → Fin (n + 1) := fun k => ⟨c k, Nat.lt_succ_of_le (h k)⟩
  obtain ⟨y, hy⟩ := Finite.exists_infinite_fiber f
  have hinf : (f ⁻¹' {y}).Infinite := Set.infinite_coe_iff.mp hy
  obtain ⟨φ, hφ, h2⟩ := extraction_of_frequently_atTop (P := fun k => f k = y)
    (Nat.frequently_atTop_iff_infinite.mpr hinf)
  exact ⟨y, φ, hφ, fun k => congrArg Fin.val (h2 k)⟩

theorem emb_refl {N : ℕ} (V : Submodule ℂ (Sm E N)) : Emb V (· ∈ V) :=
  ⟨LinearMap.id, fun _ h => h, fun _ _ h => h, fun _ _ _ => rfl⟩

theorem main (hc : ConvComp) (hs : TrStable) (hg : Graft)
    (Θs Θf : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E)))) (Ωs Ωf : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ))) (N : ℕ)
    (hL : LimLeafP N Θs Ωs Θf Ωf) (hR : ReproAll E) (n : ℕ) : n ≤ N → ∀ (t : ℕ → Tr E n) (R : ℝ), (∀ k, Red (t k)) →
    (∀ k, (t k).Good) → (∀ k, (t k).AllLeaves (ListLeaf Θs Ωs)) →
    (∀ k, LeafZ (fun M V z => 0 < M → InfBdd R V ∧ ‖z‖ ≤ R) (t k)) →
    ∃ (φ : ℕ → ℕ) (t' : ℕ → Tr E n) (s : Tr E n), StrictMono φ ∧ Conv t' s ∧ Red s ∧ s.Good ∧
      s.AllLeaves (ListLeaf Θf Ωf) ∧ (∀ k, (t' k).Disc) ∧ ∀ k, Emb (t (φ k)).space (· ∈ (t' k).space) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn t R hred hgood hlist hz
  obtain ⟨r, φ₀, hφ₀, hr⟩ := pigeon (n := n) (fun k => lr (t k)) (fun k => lr_le _)
  by_cases h0 : r = 0
  · subst h0
    choose V z hVz using fun k => leaf_of (t (φ₀ k)) (hr k) (hred _)
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · have hk : ∀ k, t (φ₀ k) = .leaf ⊤ 0 := by
        intro k
        have h := hgood (φ₀ k)
        rw [hVz k] at h
        rcases h with ⟨-, hV, hz'⟩ | ⟨h, -, -⟩
        · rw [hVz k, hV, hz']
        · exact absurd h (lt_irrefl _)
      refine ⟨φ₀, fun _ => .leaf ⊤ 0, .leaf ⊤ 0, hφ₀, Conv.leaf ⊤ (fun _ => 0) 0 tendsto_const_nhds, trivial,
        Or.inl ⟨rfl, rfl, rfl⟩, Or.inl rfl, fun _ => Or.inl ⟨rfl, rfl, rfl⟩, fun k => ?_⟩
      rw [hk k]
      exact emb_refl _
    · have hG : ∀ k, IsDiscrete (V k) ∧ (z k).re = 0 := by
        intro k
        have h := hgood (φ₀ k)
        rw [hVz k] at h
        rcases h with ⟨h, -, -⟩ | ⟨-, h⟩
        · exact absurd h hn0.ne'
        · exact h
      have hT : ∀ k, ∃ K' ∈ Θs n, ∃ W' ∈ Ωs n, HasType K' W' (V k) := by
        intro k
        have h := hlist (φ₀ k)
        rw [hVz k] at h
        rcases h with h | h
        · exact absurd h hn0.ne'
        · exact h
      have hB : ∀ k, InfBdd R (V k) ∧ ‖z k‖ ≤ R := by
        intro k
        have h := hz (φ₀ k)
        rw [hVz k] at h
        exact h hn0
      obtain ⟨φ, t', s, hφ, hc', hrs, hgs, hls, hd, he⟩ := hL n hn0 hn V z R hR (fun k => (hG k).1)
        (fun k => (hG k).2) hT (fun k => (hB k).1) (fun k => (hB k).2)
      refine ⟨φ₀ ∘ φ, t', s, hφ₀.comp hφ, hc', hrs, hgs, hls, hd, fun k => ?_⟩
      have e : t ((φ₀ ∘ φ) k) = .leaf (V (φ k)) (z (φ k)) := hVz _
      rw [e]
      exact he k
  · have hr0 : 0 < r := Nat.pos_of_ne_zero h0
    have hrn : r ≤ n := by
      have := lr_le (t (φ₀ 0))
      rwa [hr 0] at this
    obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hrn
    choose a b hab ha hb using fun k => node_of (t (φ₀ k)) rfl (hr k) hr0 (hred _)
    have hab' : ∀ k, t (φ₀ k) = .node (a k) (b k) := hab
    have hs0 : 0 < s := by
      have h := hred (φ₀ 0)
      rw [hab' 0] at h
      exact h.2.1
    have hG : ∀ k, (a k).Good ∧ (b k).Good := fun k => by
      have h := hgood (φ₀ k)
      rw [hab' k] at h
      exact h
    have hT : ∀ k, (a k).AllLeaves (ListLeaf Θs Ωs) ∧ (b k).AllLeaves (ListLeaf Θs Ωs) := fun k => by
      have h := hlist (φ₀ k)
      rw [hab' k] at h
      exact h
    have hB : ∀ k, LeafZ (fun M V z => 0 < M → InfBdd R V ∧ ‖z‖ ≤ R) (a k) ∧
        LeafZ (fun M V z => 0 < M → InfBdd R V ∧ ‖z‖ ≤ R) (b k) := fun k => by
      have h := hz (φ₀ k)
      rw [hab' k] at h
      exact h
    obtain ⟨φ₁, a', sa, hφ₁, hca, hra, hga, hla, hda, hea⟩ := ih r (by omega) (by omega) a R ha
      (fun k => (hG k).1) (fun k => (hT k).1) (fun k => (hB k).1)
    obtain ⟨φ₂, b', sb, hφ₂, hcb, hrb, hgb, hlb, hdb, heb⟩ := ih s (by omega) (by omega) (fun k => b (φ₁ k)) R
      (fun k => hb _) (fun k => (hG _).2) (fun k => (hT _).2) (fun k => (hB _).2)
    refine ⟨φ₀ ∘ φ₁ ∘ φ₂, fun k => .node (a' (φ₂ k)) (b' k), .node sa sb, hφ₀.comp (hφ₁.comp hφ₂),
      Conv.node (hc E r a' sa φ₂ hca hφ₂) hcb, ⟨hr0, hs0, hra, hrb⟩, ⟨hga, hgb⟩, ⟨hla, hlb⟩,
      fun k => ⟨hda _, hdb k⟩, fun k => ?_⟩
    have e : t ((φ₀ ∘ φ₁ ∘ φ₂) k) = .node (a (φ₁ (φ₂ k))) (b (φ₁ (φ₂ k))) := hab' _
    rw [e]
    exact hg E r s _ _ _ _ (hs E _ _ (disc_stable (good_disc (hG _).1))) (hs E _ _ (disc_stable (hda _)))
      (hs E _ _ (disc_stable (good_disc (hG _).2))) (hs E _ _ (disc_stable (hdb _))) (hea (φ₂ k)) (heb k)

theorem limTrees : ConvComp → LimTrees := by
  intro hc hs hg E _ _ _ Θs Θf Ωs Ωf N hL hR n hn t R h₁ h₂ h₃ h₄
  exact main hc hs hg Θs Θf Ωs Ωf N hL hR n hn t R h₁ h₂ h₃ h₄

end GlobalTheory.CompanionTheory.EGlue.LimT

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalComparisonInert
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.CompanionTheory.LocInert

open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin

def glEquiv {R S : Type} [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S]
    (f : R ≃+* S) (hf : Continuous f) (hf' : Continuous f.symm) (n : ℕ) : GL (Fin n) R ≃ₜ* GL (Fin n) S where
  toFun := GeneralLinearGroup.map f.toRingHom
  invFun := GeneralLinearGroup.map f.symm.toRingHom
  left_inv g := by
    ext i j
    simp
  right_inv g := by
    ext i j
    simp
  map_mul' := map_mul _
  continuous_toFun := Units.continuous_iff.2
    ⟨Units.continuous_val.matrix_map hf, Units.continuous_coe_inv.matrix_map hf⟩
  continuous_invFun := Units.continuous_iff.2
    ⟨Units.continuous_val.matrix_map hf', Units.continuous_coe_inv.matrix_map hf'⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

abbrev aw (w : Pl E) : Above (w.under (𝓞 (maximalRealSubfield E))) := ⟨w, rfl⟩

theorem eq_aw {w : Pl E} (hw : ¬ IsSplitAt w) (u : Above (w.under (𝓞 (maximalRealSubfield E)))) : u = aw w := by
  by_contra h
  exact hw ⟨u.1, fun e => h (Subtype.ext e), u.2⟩

def uniq {w : Pl E} (hw : ¬ IsSplitAt w) : Unique (Above (w.under (𝓞 (maximalRealSubfield E)))) :=
  ⟨⟨aw w⟩, eq_aw hw⟩

def evR {w : Pl E} (hw : ¬ IsSplitAt w) : Av (w.under (𝓞 (maximalRealSubfield E))) ≃+* w.adicCompletion E :=
  letI := uniq hw
  RingEquiv.piUnique fun u : Above (w.under (𝓞 (maximalRealSubfield E))) => u.1.adicCompletion E

theorem evR_apply {w : Pl E} (hw : ¬ IsSplitAt w) (x : Av (w.under (𝓞 (maximalRealSubfield E)))) :
    evR hw x = x (aw w) := rfl

theorem continuous_evR {w : Pl E} (hw : ¬ IsSplitAt w) : Continuous (evR hw) :=
  continuous_apply (aw w)

theorem continuous_evR_symm {w : Pl E} (hw : ¬ IsSplitAt w) : Continuous (evR hw).symm := by
  letI := uniq hw
  exact (Homeomorph.piUnique fun u : Above (w.under (𝓞 (maximalRealSubfield E))) => u.1.adicCompletion E).symm.continuous

def evY {w : Pl E} (hw : ¬ IsSplitAt w) (a b : ℕ) :
    Yv a b (w.under (𝓞 (maximalRealSubfield E))) ≃ₜ* GLw a w × GLw b w where
  toMulEquiv := MulEquiv.prodCongr (glEquiv (evR hw) (continuous_evR hw) (continuous_evR_symm hw) a).toMulEquiv
    (glEquiv (evR hw) (continuous_evR hw) (continuous_evR_symm hw) b).toMulEquiv
  continuous_toFun := (glEquiv (evR hw) (continuous_evR hw) (continuous_evR_symm hw) a).continuous.prodMap
    (glEquiv (evR hw) (continuous_evR hw) (continuous_evR_symm hw) b).continuous
  continuous_invFun := (glEquiv (evR hw) (continuous_evR hw) (continuous_evR_symm hw) a).symm.continuous.prodMap
    (glEquiv (evR hw) (continuous_evR hw) (continuous_evR_symm hw) b).symm.continuous

theorem evY_apply {w : Pl E} (hw : ¬ IsSplitAt w) (a b : ℕ) (y : Yv a b (w.under (𝓞 (maximalRealSubfield E)))) :
    evY hw a b y = evw (aw w) y := rfl

theorem cjv_apply (hC : CjEx) (hU : Unr E) {w : Pl E} (hw : ¬ IsSplitAt w)
    (x : Av (w.under (𝓞 (maximalRealSubfield E)))) : evR hw (cjv _ x) = cj w (evR hw x) := by
  obtain ⟨-, -, -, h4, -⟩ := GlobalTheory.ConjAtPlace.main E hU w
  have hc' := (h4 hw).2.2.1
  have h := hC E (w.under (𝓞 (maximalRealSubfield E)))
  set X : Af E := sLoc E w (evR hw x) with hX
  have hp : pLoc E w X = evR hw x := by
    change (Pi.single w (evR hw x) : ∀ u : Pl E, u.adicCompletion E) w = _
    simp
  have hx : projv _ X = x := by
    funext u
    obtain rfl := eq_aw hw u
    exact hp
  have hs : cjv (w.under (𝓞 (maximalRealSubfield E))) = h.choose := by
    rw [cjv, dif_pos h]
  rw [← hx, hs, ← h.choose_spec.2 X]
  rw [evR_apply, evR_apply]
  exact hc' X

theorem evY_thv (hC : CjEx) (hU : Unr E) {w : Pl E} (hw : ¬ IsSplitAt w) (a b : ℕ)
    (y : Yv a b (w.under (𝓞 (maximalRealSubfield E)))) :
    evY hw a b (thv a b _ y) = ((thL a w).prodMap (thL b w)) (evY hw a b y) := by
  have h : ∀ n (g : GL (Fin n) (Av (w.under (𝓞 (maximalRealSubfield E))))),
      GeneralLinearGroup.map (evR hw).toRingHom (thetaGL n (cjv _) g) =
        thL n w (GeneralLinearGroup.map (evR hw).toRingHom g) := fun n g => by
    rw [thL, if_neg hw]
    exact GlobalTheory.ThetaPull.map_thetaGL _ _ _ (cjv_apply hC hU hw) g
  exact Prod.ext (h a y.1) (h b y.2)

theorem mem_Kv_iff {w : Pl E} (hw : ¬ IsSplitAt w) (a b : ℕ) (y : Yv a b (w.under (𝓞 (maximalRealSubfield E)))) :
    y ∈ Kv a b _ ↔ evY hw a b y ∈ K2 a b w := by
  rw [Kv, Subgroup.mem_iInf]
  constructor
  · intro h
    exact h (aw w)
  · intro h u
    obtain rfl := eq_aw hw u
    exact h

theorem evY_pv {w : Pl E} (hw : ¬ IsSplitAt w) (a b : ℕ) (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E) :
    evY hw a b (pv a b _ (ratF E a δ₁, ratF E b δ₂)) = (locEl a w δ₁, locEl b w δ₂) := by
  have h : ∀ n (δ : GL (Fin n) E), GeneralLinearGroup.map (evR hw).toRingHom
      (GeneralLinearGroup.map (projv (w.under (𝓞 (maximalRealSubfield E)))) (ratF E n δ)) = locEl n w δ := fun n δ => by
    rw [locEl, if_neg hw]
    ext i j
    rfl
  exact Prod.ext (h a δ₁) (h b δ₂)

theorem fv_eq {w : Pl E} (hw : ¬ IsSplitAt w) {a b : ℕ} {S : Set (Pl E)} (hS : w ∈ S)
    (φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ) (y : Yv a b (w.under (𝓞 (maximalRealSubfield E)))) :
    seen φ₁ φ₂ w (evY hw a b y) = fv S φ₁ φ₂ _ y := by
  letI := uniq hw
  rw [fv, finprod_unique]
  change _ = ∏ᶠ (_ : w ∈ S), φ₁ w (evw (aw w) y) * if IsSplitAt w then _ else 1
  rw [finprod_eq_if, if_pos hS, if_neg hw, mul_one, seen, if_neg hw, evY_apply]

theorem locCompareInert : LocCompareInert := by
  intro hC E _ _ _ hU a b S _ φ₁ φ₂ _ _ δ₁ δ₂ _ _ w hS hw
  rw [← evY_pv hw a b δ₁ δ₂]
  exact GlobalTheory.EulerTw.Transport.twOrb_transport _ _ (evY hw a b) _ _ _ _ _ _ _
    (evY_thv hC hU hw a b) (mem_Kv_iff hw a b) (fv_eq hw hS φ₁ φ₂)

end GlobalTheory.CompanionTheory.LocInert
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalComparisonOf
section
namespace GlobalTheory.CompanionTheory.LocCompareHalves

open PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.UnitaryBC GlobalTheory.BCT

theorem locCompareOf : PositivityTheory.Rg.BcB.G8.Fin.LocCompareOf := by
  intro hI hS hC E _ _ _ hU a b S hSec φ₁ φ₂ h₁ h₂ δ₁ δ₂ e₁ e₂ w hw
  by_cases hs : IsSplitAt w
  · exact hS hC E hU a b S hSec φ₁ φ₂ h₁ h₂ δ₁ δ₂ e₁ e₂ w hw hs
  · exact hI hC E hU a b S hSec φ₁ φ₂ h₁ h₂ δ₁ δ₂ e₁ e₂ w hw hs

end GlobalTheory.CompanionTheory.LocCompareHalves
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFibreMeasureUnramifiedFormulaStatement
section
open scoped Matrix NNReal ENNReal TensorProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.AvgFree MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_fibre_measure_unramified_formula : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), HeckeCharacterZeroLocus.SiegelWeilU.IsHermND σ J → ∀ (n : ℕ) (mv : (HermR (Fv F v) σ n) → Measure (Fin n → Fin M → (Fv F v ⊗[F] E))), IsGramFibFree (Fv F v) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) mv → ∀ Tt : Set (Fin n → Fin M → (Fv F v ⊗[F] E)), IsCompact Tt → IsOpen Tt → Tt ⊆ {X : (Fin n → Fin M → (Fv F v ⊗[F] E)) | LinearIndependent (Fv F v ⊗[F] E) X} → (∀ Y : Set (HermR (Fv F v) σ n), MeasurableSet Y → (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) (Tt ∩ gramIn (Fv F v) σ J Y) = ∫⁻ y in Y, mv y Tt ∂(GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n)) ∧ Continuous (fun y => (mv y Tt).toReal) ∧ (∀ y, mv y Tt ≠ ⊤) ∧ ∃ C : ℝ≥0, ∀ y, mv y Tt ≤ C := by
  first | exact @GlobalTheory.CompanionTheory.AvgFree.free_fibre_masses | exact GlobalTheory.CompanionTheory.AvgFree.free_fibre_masses | (intros; apply GlobalTheory.CompanionTheory.AvgFree.free_fibre_masses <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHermitianClassSecondStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField PositivityTheory.BCUSide.HermitianLocalForms
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_hermitian_class_second : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (hv : w.under (𝓞 (maximalRealSubfield E)) = v), ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H₀ : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀ → ∀ m : (w.adicCompletion E)[X], IsHerm (cj w) ((H₀.map (algebraMap E (w.adicCompletion E))) * aeval (γ₀.val.map (algebraMap E (w.adicCompletion E))) m) → ((H₀.map (algebraMap E (w.adicCompletion E))) * aeval (γ₀.val.map (algebraMap E (w.adicCompletion E))) m).det ≠ 0 → ∀ (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly → ∃ x : ((v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] plus Q)ˣ, inclPlus Q (v.adicCompletion (maximalRealSubfield E)) (x : (v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] plus Q) = locPhi hU w hw v hv Q m := by
  first | exact @GlobalTheory.CompanionTheory.LocPhiUnit.locPhi_mem_units_plus | exact GlobalTheory.CompanionTheory.LocPhiUnit.locPhi_mem_units_plus | (intros; apply GlobalTheory.CompanionTheory.LocPhiUnit.locPhi_mem_units_plus <;> assumption)
end

