import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.TreeParts

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PoleReality
section
open Filter Topology Metric
open PositivityTheory.Rg.Rsw

namespace GlobalTheory.CompanionTheory.PoleBound

theorem factor_of_real_bound (s₀ ε : ℝ) (hε : 0 < ε) :
    ∀ (r : ℕ) (u : ℂ → ℂ), ContinuousOn u (closedBall (s₀ : ℂ) ε) →
      DifferentiableOn ℂ u (ball (s₀ : ℂ) ε) →
      (∃ B : ℝ, ∀ᶠ σ : ℝ in 𝓝[>] s₀, ‖u (σ : ℂ) / ((σ : ℂ) - s₀) ^ r‖ ≤ B) →
      ∃ w : ℂ → ℂ, ContinuousOn w (closedBall (s₀ : ℂ) ε) ∧
        DifferentiableOn ℂ w (ball (s₀ : ℂ) ε) ∧
        ∀ z ∈ closedBall (s₀ : ℂ) ε, z ≠ s₀ → u z = (z - s₀) ^ r * w z := by
  intro r
  induction r with
  | zero =>
    intro u hc hd _
    exact ⟨u, hc, hd, fun z _ _ => by simp⟩
  | succ r ih =>
    intro u hc hd hb
    obtain ⟨B, hB⟩ := hb
    have hdiff : DifferentiableAt ℂ u (s₀ : ℂ) := hd.differentiableAt (ball_mem_nhds _ hε)
    have hu0 : u (s₀ : ℂ) = 0 := by
      have hlim₁ : Tendsto (fun σ : ℝ => u (σ : ℂ)) (𝓝[>] s₀) (𝓝 (u (s₀ : ℂ))) :=
        ((hdiff.continuousAt.tendsto).comp (Complex.continuous_ofReal.tendsto s₀)).mono_left
          nhdsWithin_le_nhds
      have hsmall : Tendsto (fun σ : ℝ => B * ‖(σ : ℂ) - s₀‖ ^ (r + 1)) (𝓝[>] s₀) (𝓝 0) := by
        have hcont : Continuous (fun σ : ℝ => B * ‖(σ : ℂ) - s₀‖ ^ (r + 1)) := by fun_prop
        simpa using (hcont.tendsto s₀).mono_left nhdsWithin_le_nhds
      have hlim₂ : Tendsto (fun σ : ℝ => u (σ : ℂ)) (𝓝[>] s₀) (𝓝 0) := by
        refine squeeze_zero_norm' ?_ hsmall
        filter_upwards [hB, self_mem_nhdsWithin] with σ hσB hσ
        have hne : ((σ : ℂ) - s₀) ^ (r + 1) ≠ 0 :=
          pow_ne_zero _ (sub_ne_zero.mpr (Complex.ofReal_injective.ne (show s₀ < σ from hσ).ne'))
        calc ‖u (σ : ℂ)‖ = ‖u (σ : ℂ) / ((σ : ℂ) - s₀) ^ (r + 1)‖ * ‖(σ : ℂ) - s₀‖ ^ (r + 1) := by
              rw [← norm_pow, ← norm_mul, div_mul_cancel₀ _ hne]
          _ ≤ B * ‖(σ : ℂ) - s₀‖ ^ (r + 1) :=
              mul_le_mul_of_nonneg_right hσB (pow_nonneg (norm_nonneg _) _)
      exact tendsto_nhds_unique hlim₁ hlim₂
    have huv : ∀ z, u z = (z - s₀) * dslope u (s₀ : ℂ) z := by
      intro z
      have h := sub_smul_dslope u (s₀ : ℂ) z
      rw [hu0, sub_zero, smul_eq_mul] at h
      exact h.symm
    have hvc : ContinuousOn (dslope u (s₀ : ℂ)) (closedBall (s₀ : ℂ) ε) := by
      intro z hz
      by_cases hzs : z = s₀
      · subst hzs
        exact (continuousAt_dslope_same.mpr hdiff).continuousWithinAt
      · exact (continuousWithinAt_dslope_of_ne hzs).mpr (hc z hz)
    have hvd : DifferentiableOn ℂ (dslope u (s₀ : ℂ)) (ball (s₀ : ℂ) ε) :=
      (Complex.differentiableOn_dslope (ball_mem_nhds _ hε)).mpr hd
    have hvb : ∃ B : ℝ, ∀ᶠ σ : ℝ in 𝓝[>] s₀,
        ‖dslope u (s₀ : ℂ) (σ : ℂ) / ((σ : ℂ) - s₀) ^ r‖ ≤ B := by
      refine ⟨B, ?_⟩
      filter_upwards [hB, self_mem_nhdsWithin] with σ hσB hσ
      have hne : (σ : ℂ) - s₀ ≠ 0 :=
        sub_ne_zero.mpr (Complex.ofReal_injective.ne (show s₀ < σ from hσ).ne')
      rwa [huv (σ : ℂ), pow_succ, mul_comm ((σ : ℂ) - s₀) (dslope u (s₀ : ℂ) (σ : ℂ)),
        mul_div_mul_right _ _ hne] at hσB
    obtain ⟨w, hwc, hwd, hw⟩ := ih (dslope u (s₀ : ℂ)) hvc hvd hvb
    refine ⟨w, hwc, hwd, fun z hz hzs => ?_⟩
    rw [huv z, hw z hz hzs, pow_succ]
    ring

theorem extend_of_real_bound (h : ℂ → ℂ) (d : Polynomial ℂ) (s₀ ε : ℝ) (hε : 0 < ε) (hd0 : d ≠ 0)
    (hh : DifferentiableOn ℂ h (closedBall (s₀ : ℂ) ε))
    (hne : ∀ z ∈ closedBall (s₀ : ℂ) ε, z ≠ s₀ → d.eval z ≠ 0) (n : ℕ)
    (hb : ∃ B : ℝ, ∀ᶠ σ : ℝ in 𝓝[>] s₀,
      ‖((σ : ℂ) - s₀) ^ n * (h (σ : ℂ) / d.eval (σ : ℂ))‖ ≤ B) :
    ∃ w : ℂ → ℂ, ContinuousOn w (closedBall (s₀ : ℂ) ε) ∧
      DifferentiableOn ℂ w (ball (s₀ : ℂ) ε) ∧
      ∀ z ∈ closedBall (s₀ : ℂ) ε, z ≠ s₀ → (z - s₀) ^ n * (h z / d.eval z) = w z := by
  obtain ⟨q, hdq, hndvd⟩ :=
    Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd d hd0 (s₀ : ℂ)
  set m := Polynomial.rootMultiplicity (s₀ : ℂ) d
  have hdeval : ∀ z, d.eval z = (z - s₀) ^ m * q.eval z := by
    intro z
    conv_lhs => rw [hdq]
    simp
  have hq : ∀ z ∈ closedBall (s₀ : ℂ) ε, q.eval z ≠ 0 := by
    intro z hz
    by_cases hzs : z = s₀
    · subst hzs
      intro h0
      exact hndvd (Polynomial.dvd_iff_isRoot.mpr h0)
    · intro h0
      exact hne z hz hzs (by rw [hdeval, h0, mul_zero])
  have hkey : ∀ z, (z - s₀) ^ n * (h z / d.eval z) =
      ((z - s₀) ^ n * h z / q.eval z) / (z - s₀) ^ m := by
    intro z
    rw [hdeval]
    simp only [div_eq_mul_inv, mul_inv]
    ring
  have hud : DifferentiableOn ℂ (fun z => (z - s₀) ^ n * h z / q.eval z)
      (closedBall (s₀ : ℂ) ε) := by
    have hnum : DifferentiableOn ℂ (fun z => (z - s₀) ^ n * h z) (closedBall (s₀ : ℂ) ε) := by
      fun_prop
    exact hnum.div q.differentiable.differentiableOn hq
  obtain ⟨B, hB⟩ := hb
  have hub : ∃ B : ℝ, ∀ᶠ σ : ℝ in 𝓝[>] s₀,
      ‖((σ : ℂ) - s₀) ^ n * h (σ : ℂ) / q.eval (σ : ℂ) / ((σ : ℂ) - s₀) ^ m‖ ≤ B :=
    ⟨B, hB.mono fun σ hσ => by rwa [hkey] at hσ⟩
  obtain ⟨w, hwc, hwd, hw⟩ := GlobalTheory.CompanionTheory.PoleBound.factor_of_real_bound s₀ ε hε m
    (fun z => (z - s₀) ^ n * h z / q.eval z) hud.continuousOn
    (hud.mono ball_subset_closedBall) hub
  refine ⟨w, hwc, hwd, fun z hz hzs => ?_⟩
  rw [hkey z, hw z hz hzs, mul_div_cancel_left₀ _ (pow_ne_zero _ (sub_ne_zero.mpr hzs))]

theorem circle_zero (c : ℂ) (ε : ℝ) (hε : 0 < ε) (g : ℂ → ℂ) (hc : ContinuousOn g (closedBall c ε))
    (hd : DifferentiableOn ℂ g (ball c ε)) : (∮ z in C(c, ε), g z) = 0 :=
  Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hε.le Set.countable_empty hc
    fun _ hz => hd.differentiableAt (isOpen_ball.mem_nhds hz.1)

theorem sphere_facts {c z : ℂ} {ε : ℝ} (hε : 0 < ε) (hz : z ∈ sphere c ε) :
    z ∈ closedBall c ε ∧ z ≠ c := by
  refine ⟨sphere_subset_closedBall hz, ?_⟩
  rintro rfl
  rw [mem_sphere, dist_self] at hz
  exact hε.ne hz

theorem moment_zero (f w : ℂ → ℂ) (s₀ : ℂ) (ε : ℝ) (hε : 0 < ε) (n j : ℕ)
    (hwc : ContinuousOn w (closedBall s₀ ε)) (hwd : DifferentiableOn ℂ w (ball s₀ ε))
    (hw : ∀ z ∈ closedBall s₀ ε, z ≠ s₀ → (z - s₀) ^ n * f z = w z) :
    (∮ z in C(s₀, ε), (z - s₀) ^ (j + n) * f z) = 0 := by
  have hcongr : (∮ z in C(s₀, ε), (z - s₀) ^ (j + n) * f z) =
      ∮ z in C(s₀, ε), (z - s₀) ^ j * w z := by
    refine circleIntegral.integral_congr hε.le fun z hz => ?_
    obtain ⟨hzc, hzs⟩ := GlobalTheory.CompanionTheory.PoleBound.sphere_facts hε hz
    show (z - s₀) ^ (j + n) * f z = (z - s₀) ^ j * w z
    rw [pow_add, mul_assoc, hw z hzc hzs]
  rw [hcongr]
  refine GlobalTheory.CompanionTheory.PoleBound.circle_zero s₀ ε hε _ ?_ ?_
  · fun_prop
  · fun_prop

theorem poleReal : PoleReal := by
  intro h d s₀ ε hε hd0 hh _ hne
  refine ⟨fun hb => ?_, fun hb => ?_⟩
  · have hb' : ∃ B : ℝ, ∀ᶠ σ : ℝ in 𝓝[>] s₀,
        ‖((σ : ℂ) - s₀) ^ 1 * (h (σ : ℂ) / d.eval (σ : ℂ))‖ ≤ B := by
      obtain ⟨B, hB⟩ := hb
      exact ⟨B, hB.mono fun σ hσ => by rwa [pow_one, ← Complex.ofReal_sub]⟩
    obtain ⟨w, hwc, hwd, hw⟩ := GlobalTheory.CompanionTheory.PoleBound.extend_of_real_bound h d s₀ ε hε hd0 hh hne 1 hb'
    refine ⟨fun k hk => ?_, ?_⟩
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
      have hj : j + 2 - 1 = j + 1 := by omega
      rw [hj]
      exact GlobalTheory.CompanionTheory.PoleBound.moment_zero (fun z => h z / d.eval z) w (s₀ : ℂ) ε hε 1 j
        hwc hwd hw
    · have hint : (∮ z in C((s₀ : ℂ), ε), (z - s₀) ^ (1 - 1) * (h z / d.eval z)) =
          ∮ z in C((s₀ : ℂ), ε), (z - s₀)⁻¹ • w z := by
        refine circleIntegral.integral_congr hε.le fun z hz => ?_
        obtain ⟨hzc, hzs⟩ := GlobalTheory.CompanionTheory.PoleBound.sphere_facts hε hz
        show (z - s₀) ^ (1 - 1) * (h z / d.eval z) = (z - s₀)⁻¹ • w z
        rw [← hw z hzc hzs, smul_eq_mul, pow_one, ← mul_assoc,
          inv_mul_cancel₀ (sub_ne_zero.mpr hzs), one_mul, Nat.sub_self, pow_zero, one_mul]
      have hcauchy : (∮ z in C((s₀ : ℂ), ε), (z - s₀)⁻¹ • w z) =
          (2 * Real.pi * Complex.I : ℂ) • w s₀ :=
        Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
          Set.countable_empty (mem_ball_self hε) hwc
          fun x hx => hwd.differentiableAt (isOpen_ball.mem_nhds hx.1)
      have h2pi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 :=
        mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
          Complex.I_ne_zero
      rw [hint, hcauchy, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ h2pi, one_mul]
      have hlim : Tendsto (fun σ : ℝ => w (σ : ℂ)) (𝓝[>] s₀) (𝓝 (w (s₀ : ℂ))) :=
        (((hwc.continuousAt (closedBall_mem_nhds _ hε)).tendsto).comp
          (Complex.continuous_ofReal.tendsto s₀)).mono_left nhdsWithin_le_nhds
      refine Tendsto.congr' ?_ hlim
      have hball : ∀ᶠ σ : ℝ in 𝓝[>] s₀, (σ : ℂ) ∈ closedBall (s₀ : ℂ) ε :=
        nhdsWithin_le_nhds
          ((Complex.continuous_ofReal.tendsto s₀).eventually_mem (closedBall_mem_nhds _ hε))
      filter_upwards [hball, self_mem_nhdsWithin] with σ hσb hσ
      rw [← hw (σ : ℂ) hσb (Complex.ofReal_injective.ne (show s₀ < σ from hσ).ne'), pow_one,
        Complex.ofReal_sub]
  · have hb' : ∃ B : ℝ, ∀ᶠ σ : ℝ in 𝓝[>] s₀,
        ‖((σ : ℂ) - s₀) ^ 0 * (h (σ : ℂ) / d.eval (σ : ℂ))‖ ≤ B := by
      obtain ⟨B, hB⟩ := hb
      exact ⟨B, hB.mono fun σ hσ => by rwa [pow_zero, one_mul]⟩
    obtain ⟨w, hwc, hwd, hw⟩ := GlobalTheory.CompanionTheory.PoleBound.extend_of_real_bound h d s₀ ε hε hd0 hh hne 0 hb'
    intro k _
    exact GlobalTheory.CompanionTheory.PoleBound.moment_zero (fun z => h z / d.eval z) w (s₀ : ℂ) ε hε 0
      (k - 1) hwc hwd hw

end GlobalTheory.CompanionTheory.PoleBound
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation

namespace GlobalTheory.CompanionTheory.EGlue

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

noncomputable def Red : {N : ℕ} → Tr E N → Prop
  | _, .leaf _ _ => True
  | _, @Tr.node _ _ _ _ r s t₁ t₂ => 0 < r ∧ 0 < s ∧ Red t₁ ∧ Red t₂

inductive Conv : {N : ℕ} → (ℕ → Tr E N) → Tr E N → Prop
  | leaf {N : ℕ} (V : Submodule ℂ (Sm E N)) (z : ℕ → ℂ) (z₀ : ℂ) (h : Tendsto z atTop (𝓝 z₀)) :
      Conv (fun k => .leaf V (z k)) (.leaf V z₀)
  | node {r s : ℕ} {t₁ : ℕ → Tr E r} {t₂ : ℕ → Tr E s} {s₁ : Tr E r} {s₂ : Tr E s} (h₁ : Conv t₁ s₁) (h₂ : Conv t₂ s₂) :
      Conv (fun k => .node (t₁ k) (t₂ k)) (.node s₁ s₂)

noncomputable def LeafZ (P : ∀ M : ℕ, Submodule ℂ (Sm E M) → ℂ → Prop) : {N : ℕ} → Tr E N → Prop
  | M, .leaf V z => P M V z
  | _, .node t₁ t₂ => LeafZ P t₁ ∧ LeafZ P t₂

variable {a b : ℕ}

def sl₁ (F : H E a b → ℂ) (m₂ : GA E b) : Sm E a :=
  open Classical in if h : ∃ φ : Sm E a, φ.1 = fun x => F (x, m₂) then h.choose else 0

def sl₂ (F : H E a b → ℂ) (m₁ : GA E a) : Sm E b :=
  open Classical in if h : ∃ φ : Sm E b, φ.1 = fun x => F (m₁, x) then h.choose else 0

def ap₁ (A : Sm E a →ₗ[ℂ] Sm E a) (F : H E a b → ℂ) : H E a b → ℂ := fun x => (A (sl₁ F x.2)).1 x.1

def ap₂ (B : Sm E b →ₗ[ℂ] Sm E b) (F : H E a b → ℂ) : H E a b → ℂ := fun x => (B (sl₂ F x.1)).1 x.2

theorem good_disc : ∀ {N : ℕ} {t : Tr E N}, t.Good → t.Disc := by
  intro N t
  induction t with
  | leaf V z =>
    intro h
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h.1, h.2.1⟩
  | node t₁ t₂ i₁ i₂ => exact fun h => ⟨i₁ h.1, i₂ h.2⟩

theorem disc_stable : ∀ {N : ℕ} {t : Tr E N}, t.Disc → t.AllLeaves fun _ V => IsStable V := by
  intro N t
  induction t with
  | leaf V z =>
    intro h
    rcases h with ⟨-, rfl, -⟩ | h
    · exact fun _ _ _ => trivial
    · exact h.2.stable
  | node t₁ t₂ i₁ i₂ => exact fun h => ⟨i₁ h.1, i₂ h.2⟩

theorem rank_pos_of_leaves {Q : ∀ M : ℕ, Submodule ℂ (Sm E M) → Prop} : ∀ {N : ℕ} {t : Tr E N},
    t.AllLeaves (fun M V => 0 < M ∧ Q M V) → 0 < N := by
  intro N t
  induction t with
  | leaf V z => exact fun h => h.1
  | node t₁ t₂ i₁ i₂ => exact fun h => Nat.add_pos_left (i₁ h.1) _

theorem red_of_leaves {Q : ∀ M : ℕ, Submodule ℂ (Sm E M) → Prop} : ∀ {N : ℕ} {t : Tr E N},
    t.AllLeaves (fun M V => 0 < M ∧ Q M V) → Red t := by
  intro N t
  induction t with
  | leaf V z => exact fun _ => trivial
  | node t₁ t₂ i₁ i₂ => exact fun h => ⟨rank_pos_of_leaves h.1, rank_pos_of_leaves h.2, i₁ h.1, i₂ h.2⟩

section Props

def ListLeaf (Θ : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E)))) (Ω : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ))) :
    ∀ M : ℕ, Submodule ℂ (Sm E M) → Prop :=
  fun M V => M = 0 ∨ ∃ K' ∈ Θ M, ∃ W' ∈ Ω M, HasType K' W' V

def CapEig {N : ℕ} (ψ : Sm E N) (m : (E →+* ℂ) → Multiset ℂ) : Prop :=
  ∀ τ u, cap τ u ψ = ((m τ).map (u + ·)).prod • ψ

def FinGen {N : ℕ} (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ)) (U : Submodule ℂ (Sm E N)) : Prop :=
  ∃ S : Finset (Sm E N), (∀ φ ∈ S, TypeB K W φ) ∧ ↑S ⊆ (U : Set (Sm E N)) ∧
    ∀ U' : Submodule ℂ (Sm E N), IsStable U' → ↑S ⊆ (U' : Set (Sm E N)) → U ≤ U'

def Fac {N : ℕ} (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ))
    (Θ : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E)))) (Ω : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ))) : Prop :=
  ∀ U : Submodule ℂ (Sm E N), IsStable U → (∀ φ ∈ U, IsAutForm φ) → FinGen K W U → NonPos U → CentIm U →
    (∀ τ : E →+* ℂ, ∃ m, HasInfCharGL U τ m ∧ m.Nodup) → U ≠ ⊥ →
    ∃ (t : Tr E N) (T : Sm E N →ₗ[ℂ] Sm E N), Red t ∧ t.Good ∧ t.AllLeaves (ListLeaf Θ Ω) ∧
      (∀ o, ∀ ψ ∈ U, T (act o ψ) = act o (T ψ)) ∧ (∀ ψ ∈ U, T ψ ∈ t.space) ∧ ∃ ψ ∈ U, T ψ ≠ 0

def ReproAll (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)] (ν : Measure (GA E N)) [ν.IsHaarMeasure]
    (K' : Subgroup (GL (Fin N) (Af E))) (W' : Submodule ℂ (Kinf E N → ℂ)) (R' : ℝ),
    IsOpen (K' : Set (GL (Fin N) (Af E))) → FiniteDimensional ℂ W' → Repro ν K' W' R'

def LimLeafP (N : ℕ) (Θs : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E)))) (Ωs : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ)))
    (Θf : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E)))) (Ωf : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ))) : Prop :=
  ∀ M, 0 < M → M ≤ N → ∀ (V : ℕ → Submodule ℂ (Sm E M)) (z : ℕ → ℂ) (R : ℝ), ReproAll E →
    (∀ k, IsDiscrete (V k)) → (∀ k, (z k).re = 0) → (∀ k, ∃ K' ∈ Θs M, ∃ W' ∈ Ωs M, HasType K' W' (V k)) →
    (∀ k, InfBdd R (V k)) → (∀ k, ‖z k‖ ≤ R) →
    ∃ (φ : ℕ → ℕ) (t : ℕ → Tr E M) (s : Tr E M), StrictMono φ ∧ Conv t s ∧ Red s ∧ s.Good ∧
      s.AllLeaves (ListLeaf Θf Ωf) ∧ (∀ k, (t k).Disc) ∧ ∀ k, Emb (tw (V (φ k)) (z (φ k))) (· ∈ (t k).space)

end Props

def PairSlices : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ)
  (U₁ : Submodule ℂ (Sm E a)) (U₂ : Submodule ℂ (Sm E b)) (F : H E a b → ℂ), F ∈ pairSpace U₁ U₂ →
  (∀ m₂, sl₁ F m₂ ∈ U₁ ∧ (sl₁ F m₂).1 = fun x => F (x, m₂)) ∧
  (∀ m₁, sl₂ F m₁ ∈ U₂ ∧ (sl₂ F m₁).1 = fun x => F (m₁, x))

def PairRestrict : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ)
  (U₁ : Submodule ℂ (Sm E a)) (U₂ U₂' : Submodule ℂ (Sm E b)) (F : H E a b → ℂ), F ∈ pairSpace U₁ U₂ →
  (∀ m₁ (φ : Sm E b), (φ.1 = fun x => F (m₁, x)) → φ ∈ U₂') → F ∈ pairSpace U₁ U₂'

def PairFD : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (ι : Type) [Fintype ι]
  (U₁ : Submodule ℂ (Sm E a)) (U₂ : Submodule ℂ (Sm E b)) (f : ι → H E a b → ℂ), (∀ i, f i ∈ pairSpace U₁ U₂) →
  FiniteDimensional ℂ (Submodule.span ℂ (slices₁ f)) ∧ FiniteDimensional ℂ (Submodule.span ℂ (slices₂ f))

def SliceType : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ)
  (K₁ : Subgroup (GL (Fin a) (Af E))) (K₂ : Subgroup (GL (Fin b) (Af E)))
  (W₁ : Submodule ℂ (Kinf E a → ℂ)) (W₂ : Submodule ℂ (Kinf E b → ℂ)) (F : H E a b → ℂ), TypeH K₁ K₂ W₁ W₂ F →
  (∀ (φ : Sm E a) m₂, (φ.1 = fun x => F (x, m₂)) → TypeB K₁ W₁ φ) ∧
  (∀ (φ : Sm E b) m₁, (φ.1 = fun x => F (m₁, x)) → TypeB K₂ W₂ φ)

def PairStep₁ : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (ι : Type) [Fintype ι]
  (K₁ : Subgroup (GL (Fin a) (Af E))) (K₂ : Subgroup (GL (Fin b) (Af E)))
  (W₁ : Submodule ℂ (Kinf E a → ℂ)) (W₂ : Submodule ℂ (Kinf E b → ℂ))
  (U₁ U₁' : Submodule ℂ (Sm E a)) (U₂ : Submodule ℂ (Sm E b)) (T : Sm E a →ₗ[ℂ] Sm E a) (f : ι → H E a b → ℂ),
  FiniteDimensional ℂ W₁ → FiniteDimensional ℂ W₂ → IsStable U₁ → (∀ o, ∀ ψ ∈ U₁, T (act o ψ) = act o (T ψ)) →
  (∀ ψ ∈ U₁, T ψ ∈ U₁') → (∀ i, f i ∈ pairSpace U₁ U₂) → (∀ i, TypeH K₁ K₂ W₁ W₂ (f i)) →
  (∃ i m₂, ∃ φ : Sm E a, (φ.1 = fun x => f i (x, m₂)) ∧ T φ ≠ 0) →
  (fun i => ap₁ T (f i)) ≠ 0 ∧ (∀ i, ap₁ T (f i) ∈ pairSpace U₁' U₂) ∧ (∀ i, TypeH K₁ K₂ W₁ W₂ (ap₁ T (f i))) ∧
    ∀ (h : HeckeM E a b ι) (c : ℂ), heckeAct h f = c • f → heckeAct h (fun i => ap₁ T (f i)) = c • fun i => ap₁ T (f i)

def PairStep₂ : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (ι : Type) [Fintype ι]
  (K₁ : Subgroup (GL (Fin a) (Af E))) (K₂ : Subgroup (GL (Fin b) (Af E)))
  (W₁ : Submodule ℂ (Kinf E a → ℂ)) (W₂ : Submodule ℂ (Kinf E b → ℂ))
  (U₁ : Submodule ℂ (Sm E a)) (U₂ U₂' : Submodule ℂ (Sm E b)) (T : Sm E b →ₗ[ℂ] Sm E b) (f : ι → H E a b → ℂ),
  FiniteDimensional ℂ W₁ → FiniteDimensional ℂ W₂ → IsStable U₂ → (∀ o, ∀ ψ ∈ U₂, T (act o ψ) = act o (T ψ)) →
  (∀ ψ ∈ U₂, T ψ ∈ U₂') → (∀ i, f i ∈ pairSpace U₁ U₂) → (∀ i, TypeH K₁ K₂ W₁ W₂ (f i)) →
  (∃ i m₁, ∃ φ : Sm E b, (φ.1 = fun x => f i (m₁, x)) ∧ T φ ≠ 0) →
  (fun i => ap₂ T (f i)) ≠ 0 ∧ (∀ i, ap₂ T (f i) ∈ pairSpace U₁ U₂') ∧ (∀ i, TypeH K₁ K₂ W₁ W₂ (ap₂ T (f i))) ∧
    ∀ (h : HeckeM E a b ι) (c : ℂ), heckeAct h f = c • f → heckeAct h (fun i => ap₂ T (f i)) = c • fun i => ap₂ T (f i)

def PairEmb : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (ι : Type) [Fintype ι]
  (K₁ : Subgroup (GL (Fin a) (Af E))) (K₂ : Subgroup (GL (Fin b) (Af E)))
  (W₁ : Submodule ℂ (Kinf E a → ℂ)) (W₂ : Submodule ℂ (Kinf E b → ℂ))
  (X₁ Y₁ : Submodule ℂ (Sm E a)) (X₂ Y₂ : Submodule ℂ (Sm E b)) (G : ι → H E a b → ℂ),
  FiniteDimensional ℂ W₁ → FiniteDimensional ℂ W₂ → IsStable X₁ → IsStable X₂ → Emb X₁ (· ∈ Y₁) → Emb X₂ (· ∈ Y₂) →
  G ≠ 0 → (∀ i, G i ∈ pairSpace X₁ X₂) → (∀ i, TypeH K₁ K₂ W₁ W₂ (G i)) →
  ∃ G' : ι → H E a b → ℂ, G' ≠ 0 ∧ (∀ i, G' i ∈ pairSpace Y₁ Y₂) ∧ (∀ i, TypeH K₁ K₂ W₁ W₂ (G' i)) ∧
    ∀ (h : HeckeM E a b ι) (c : ℂ), heckeAct h G = c • G → heckeAct h G' = c • G'

def HullGen : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ)
  (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ)) (S : Set (Sm E N)),
  (∀ φ ∈ S, TypeB K W φ) → FiniteDimensional ℂ (Submodule.span ℂ S) → IsStable (hull S) ∧ FinGen K W (hull S)

def CapEquiv : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (U : Submodule ℂ (Sm E N))
  (T : Sm E N →ₗ[ℂ] Sm E N) (ψ : Sm E N) (m : (E →+* ℂ) → Multiset ℂ), IsStable U →
  (∀ o, ∀ χ ∈ U, T (act o χ) = act o (T χ)) → ψ ∈ U → CapEig ψ m → CapEig (T ψ) m

def DiscInf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (M : ℕ) (V : Submodule ℂ (Sm E M)),
  IsDiscrete V → ∀ τ : E →+* ℂ, ∃ m, HasInfCharGL V τ m

def TopInf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (τ : E →+* ℂ),
  HasInfCharGL (⊤ : Submodule ℂ (Sm E 0)) τ 0

def InfOfEq : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (t : Tr E N) (ψ : Sm E N)
  (m : (E →+* ℂ) → Multiset ℂ) (τ : E →+* ℂ) (m' : Multiset ℂ), InfTree → t.InfOf τ m' → ψ ∈ t.space → ψ ≠ 0 → CapEig ψ m →
  m' = m τ

def LeafBound : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (t : Tr E N) (ψ : Sm E N)
  (m : (E →+* ℂ) → Multiset ℂ) (B : ℝ), InfTree → t.Good → ψ ∈ t.space → ψ ≠ 0 → CapEig ψ m →
  (∀ τ, ∀ x ∈ m τ, ‖x‖ ≤ B) → LeafZ (fun M V z => 0 < M → InfBdd (2 * B) V ∧ ‖z‖ ≤ 2 * B) t

def ConvStrip : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (t : ℕ → Tr E N) (s : Tr E N),
  Conv t s ↔ (∀ k, (t k).strip = s.strip) ∧
    ∀ i, Tendsto (fun k => ((t k).twists.getD i 0)) atTop (𝓝 (s.twists.getD i 0))

def ConvShift : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (t : ℕ → Tr E N) (s : Tr E N)
  (z : ℕ → ℂ) (z₀ : ℂ), Conv t s → Tendsto z atTop (𝓝 z₀) → Conv (fun k => (t k).shift (z k)) (s.shift z₀)

def ConvComp : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (t : ℕ → Tr E N) (s : Tr E N)
  (φ : ℕ → ℕ), Conv t s → StrictMono φ → Conv (fun k => t (φ k)) s

def ConvInf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (t : ℕ → Tr E N) (s : Tr E N)
  (τ : E →+* ℂ), Conv t s → s.Good → ∃ (m₀ : Multiset ℂ) (m : ℕ → Multiset ℂ), s.InfOf τ m₀ ∧ (∀ k, (t k).InfOf τ (m k)) ∧
    ∀ u, Tendsto (fun k => ((m k).map (u + ·)).prod) atTop (𝓝 ((m₀.map (u + ·)).prod))

def FactorStep : Prop := Sep4 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ)
  (W : Submodule ℂ (Kinf E N → ℂ)), FiniteDimensional ℂ W →
  ∃ Ω : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ)), KTypes E Ω ∧
  ∀ K : Subgroup (GL (Fin N) (Af E)), IsOpen (K : Set (GL (Fin N) (Af E))) →
  ∃ Θ : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E))), Levels E Θ ∧ Fac K W Θ Ω

def OneStep : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (ι : Type) [Fintype ι]
  (K₁ : Subgroup (GL (Fin a) (Af E))) (K₂ : Subgroup (GL (Fin b) (Af E)))
  (W₁ : Submodule ℂ (Kinf E a → ℂ)) (W₂ : Submodule ℂ (Kinf E b → ℂ))
  (Θ₁ Θ₂ : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E)))) (Ω₁ Ω₂ : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ)))
  (f : ι → H E a b → ℂ) (m₁ m₂ : (E →+* ℂ) → Multiset ℂ),
  FiniteDimensional ℂ W₁ → FiniteDimensional ℂ W₂ → Fac K₁ W₁ Θ₁ Ω₁ → Fac K₂ W₂ Θ₂ Ω₂ → f ≠ 0 →
  (∀ i, TypeH K₁ K₂ W₁ W₂ (f i)) →
  (∀ i (m₂ : GA E b), ∃ φ : Sm E a, φ.1 = fun x => f i (x, m₂)) →
  (∀ i (m₁ : GA E a), ∃ φ : Sm E b, φ.1 = fun x => f i (m₁, x)) →
  (∀ φ ∈ hull (slices₁ f), IsAutForm φ) → (∀ φ ∈ hull (slices₂ f), IsAutForm φ) →
  NonPos (hull (slices₁ f)) → NonPos (hull (slices₂ f)) → CentIm (hull (slices₁ f)) → CentIm (hull (slices₂ f)) →
  (∀ τ, HasInfCharGL (hull (slices₁ f)) τ (m₁ τ)) → (∀ τ, HasInfCharGL (hull (slices₂ f)) τ (m₂ τ)) →
  (∀ τ, (m₁ τ).Nodup) → (∀ τ, (m₂ τ).Nodup) → (∀ i, f i ∈ pairSpace (hull (slices₁ f)) (hull (slices₂ f))) →
  ∃ (t₁ : Tr E a) (t₂ : Tr E b) (G : ι → H E a b → ℂ) (ψ₁ : Sm E a) (ψ₂ : Sm E b),
    Red t₁ ∧ Red t₂ ∧ t₁.Good ∧ t₂.Good ∧ t₁.AllLeaves (ListLeaf Θ₁ Ω₁) ∧ t₂.AllLeaves (ListLeaf Θ₂ Ω₂) ∧
    G ≠ 0 ∧ (∀ i, G i ∈ pairSpace t₁.space t₂.space) ∧ (∀ i, TypeH K₁ K₂ W₁ W₂ (G i)) ∧
    (∀ (h : HeckeM E a b ι) (c : ℂ), heckeAct h f = c • f → heckeAct h G = c • G) ∧
    ψ₁ ∈ t₁.space ∧ ψ₁ ≠ 0 ∧ CapEig ψ₁ m₁ ∧ ψ₂ ∈ t₂.space ∧ ψ₂ ≠ 0 ∧ CapEig ψ₂ m₂

def LimLists : Prop := Lim5 → TwShift → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ)
  (Ωs : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ))), KTypes E Ωs →
  ∃ Ωf : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ)), KTypes E Ωf ∧
  ∀ Θs : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E))), Levels E Θs →
  ∃ Θf : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E))), Levels E Θf ∧ LimLeafP N Θs Ωs Θf Ωf

def LimTrees : Prop := TrStable → Graft → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
  (Θs Θf : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E)))) (Ωs Ωf : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ))) (N : ℕ),
  LimLeafP N Θs Ωs Θf Ωf → ReproAll E → ∀ (n : ℕ), n ≤ N → ∀ (t : ℕ → Tr E n) (R : ℝ), (∀ k, Red (t k)) → (∀ k, (t k).Good) →
  (∀ k, (t k).AllLeaves (ListLeaf Θs Ωs)) → (∀ k, LeafZ (fun M V z => 0 < M → InfBdd R V ∧ ‖z‖ ≤ R) (t k)) →
  ∃ (φ : ℕ → ℕ) (t' : ℕ → Tr E n) (s : Tr E n), StrictMono φ ∧ Conv t' s ∧ Red s ∧ s.Good ∧
    s.AllLeaves (ListLeaf Θf Ωf) ∧ (∀ k, (t' k).Disc) ∧ ∀ k, Emb (t (φ k)).space (· ∈ (t' k).space)

def MCloseFacts : Prop := (∀ (ε : ℝ) (m n : Multiset ℂ) (B : ℝ), MClose ε m n → (∀ y ∈ n, ‖y‖ ≤ B) → ∀ x ∈ m, ‖x‖ ≤ B + ε) ∧
  (∀ (ε : ℝ) (m n : Multiset ℂ), ε < 1 / 4 → MClose ε m n → GapM n → m.Nodup) ∧
  ∀ (m : ℕ → Multiset ℂ) (n : Multiset ℂ), (∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, MClose ε (m k) n) →
    ∀ u : ℂ, Tendsto (fun k => ((m k).map (u + ·)).prod) atTop (𝓝 ((n.map (u + ·)).prod))

def FactorLim : Prop := TrStable → Graft → InfTree → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
  (Θs Θf : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E)))) (Ωs Ωf : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ))) (N : ℕ)
  (t : ℕ → Tr E N) (ψ : ℕ → Sm E N) (m : ℕ → (E →+* ℂ) → Multiset ℂ) (n : (E →+* ℂ) → Multiset ℂ) (B : ℝ),
  LimLeafP N Θs Ωs Θf Ωf → ReproAll E → (∀ k, Red (t k)) → (∀ k, (t k).Good) →
  (∀ k, (t k).AllLeaves (ListLeaf Θs Ωs)) → (∀ k, ψ k ∈ (t k).space) → (∀ k, ψ k ≠ 0) → (∀ k, CapEig (ψ k) (m k)) →
  (∀ k τ, ∀ x ∈ m k τ, ‖x‖ ≤ B) → (∀ τ (ε : ℝ), 0 < ε → ∀ᶠ k in atTop, MClose ε (m k τ) (n τ)) →
  ∃ (φ : ℕ → ℕ) (t' : ℕ → Tr E N) (s : Tr E N), StrictMono φ ∧ Conv t' s ∧ Red s ∧ s.Good ∧ s.AllLeaves (ListLeaf Θf Ωf) ∧
    (∀ k, (t' k).Disc) ∧ (∀ τ, HasInfCharGL s.space τ (n τ)) ∧ ∀ k, Emb (t (φ k)).space (· ∈ (t' k).space)

end GlobalTheory.CompanionTheory.EGlue

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightIdentityStatement
section
open PositivityTheory.Rg.Rsw GlobalTheory.Cont

namespace GlobalTheory.CompanionTheory.Dblock

theorem rightId : RightId := by
  intro U h g c σ hUo hU hh hg hhg z hzU hzc
  obtain ⟨⟨σ₀, hσ₀⟩, htr⟩ := hU
  set M : ℝ := max (max σ₀ σ) c
  set V : Set ℂ := U ∩ {w : ℂ | c < w.re}
  have hVo : IsOpen V := hUo.inter (isOpen_lt continuous_const Complex.continuous_re)
  have hHV : {w : ℂ | M < w.re} ⊆ V := by
    intro w hw
    have hw' : M < w.re := hw
    refine ⟨hσ₀ ?_, ?_⟩
    · show σ₀ < w.re
      exact lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hw'
    · show c < w.re
      exact lt_of_le_of_lt (le_max_right _ _) hw'
  set x₀ : ℂ := ((M + 1 : ℝ) : ℂ)
  have hx₀ : M < x₀.re := by
    show M < ((M + 1 : ℝ) : ℂ).re
    rw [Complex.ofReal_re]
    linarith
  have hVconn : IsPreconnected V := by
    refine isPreconnected_of_forall x₀ fun y hy => ?_
    have hyc : c < y.re := hy.2
    set T : ℝ := |M - y.re| + 1
    have hT : 0 ≤ T := by positivity
    refine ⟨(fun s : ℝ => y + (s : ℂ)) '' Set.Icc 0 T ∪ {w : ℂ | M < w.re}, ?_, ?_, ?_, ?_⟩
    · rintro w (⟨s, ⟨hs0, _⟩, rfl⟩ | hw)
      · refine ⟨htr y hy.1 s hs0, ?_⟩
        show c < (y + (s : ℂ)).re
        rw [Complex.add_re, Complex.ofReal_re]
        linarith
      · exact hHV hw
    · exact Or.inr hx₀
    · exact Or.inl ⟨0, ⟨le_refl 0, hT⟩, by simp⟩
    · refine IsPreconnected.union (y + (T : ℂ)) ⟨T, ⟨hT, le_refl T⟩, rfl⟩ ?_ ?_ ?_
      · show M < (y + (T : ℂ)).re
        rw [Complex.add_re, Complex.ofReal_re]
        have := le_abs_self (M - y.re)
        linarith
      · exact isPreconnected_Icc.image _
          (continuous_const.add Complex.continuous_ofReal).continuousOn
      · exact (convex_halfSpace_re_gt M).isPreconnected
  have hhA : AnalyticOnNhd ℂ h V := (hh.mono Set.inter_subset_left).analyticOnNhd hVo
  have hgA : AnalyticOnNhd ℂ g V := (hg.mono Set.inter_subset_right).analyticOnNhd hVo
  have hσx : σ < x₀.re := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hx₀
  have hev : h =ᶠ[nhds x₀] g := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hσx] with w hw
    exact hhg w hw
  exact hhA.eqOn_of_preconnected_of_eventuallyEq hgA hVconn (hHV hx₀) hev ⟨hzU, hzc⟩

end GlobalTheory.CompanionTheory.Dblock
end

