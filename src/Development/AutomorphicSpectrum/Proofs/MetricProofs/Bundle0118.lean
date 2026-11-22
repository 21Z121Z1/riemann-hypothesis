import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0005
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0113
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0058
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0041
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0024
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0022
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0115
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Statements.MetricStatements.ExistsFlagModelBaseMetric
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0125
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0108
import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle0019
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ConvergenceStatementHolds
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CorrectedWeightRegularization
import Development.WeilBound.CoreStatements.PluriharmonicCharts.XCBmExistsBounds
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsAnalyticLogResolution
import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle0020
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentFrameComparison
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0042
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0075
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle0018
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0114
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0088
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0095

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.AlgebraicSquareBaseIntersection
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.SqFirst

theorem isSmoothHerm_of_pull {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}
    [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')}
    {A : HermLine ι} {A' : HermLine ι'} (hb : IsBlockMap κ v) (hA : IsSmoothHerm A)
    (hp : IsPullHerm κ v A A') : IsSmoothHerm A' := by
  have hh : A'.h = A.h ∘ (fun (z' : (Σ k', ι' k') → ℂ) (p : Σ k, ι k) => z' (v p)) := funext hp.2
  unfold IsSmoothHerm
  rw [hh]
  refine ContDiffOn.comp hA ?_ ?_
  · exact (contDiff_pi.2 fun p => contDiff_apply ℝ ℂ (v p)).contDiffOn
  · intro z hz k
    obtain ⟨i', hi'⟩ := hz (κ k)
    obtain ⟨⟨k₁, i⟩, hp'⟩ := hb.2.2.2 ⟨κ k, i'⟩ ⟨k, rfl⟩
    have e : κ k₁ = κ k := by
      have := hb.2.2.1 ⟨k₁, i⟩
      rw [hp'] at this
      exact this.symm
    obtain rfl := hb.1 e
    exact ⟨i, by simpa [hp'] using hi'⟩

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem pull_one_of_base {P : Ideal (MRing ι)} {d : ℕ} {k₀ : K} {xi2 : K → ℤ} (Q : AlgSq P d k₀ xi2)
    {A : HermLine ι} {A₀ : HermLine Q.ιW} (hb : FromBase k₀ A) (h : IsPullHerm (Q.κ 0) (Q.v 0) A A₀) :
    IsPullHerm (Q.κ 1) (Q.v 1) A A₀ := by
  have hκ : ∀ k, k ≠ k₀ → Q.κ 0 k = Q.κ 1 k := fun k hk => by
    obtain ⟨i, -⟩ := Q.arithY.2.1.2.2 k
    have := congrArg Sigma.fst (Q.same ⟨k, i⟩ hk)
    rwa [(Q.block 0).2.2.1, (Q.block 1).2.2.1] at this
  refine ⟨?_, fun z' => ?_⟩
  · rw [h.1]
    funext k'
    rcases Q.all k' with ⟨k, rfl⟩ | rfl
    · by_cases hk : k = k₀
      · subst hk
        have hn : ¬ ∃ k', Q.κ 1 k' = Q.κ 0 k := by
          rintro ⟨k', hk'⟩
          by_cases h' : k' = k
          · subst h'
            exact Q.new ⟨k', hk'.symm⟩
          · exact h' ((Q.block 0).1 ((hκ k' h').trans hk'))
        rw [pullDeg, pullDeg, (Q.block 0).1.extend_apply, hb.1, Function.extend_apply' _ _ _ hn]
        rfl
      · rw [pullDeg, pullDeg, (Q.block 0).1.extend_apply, hκ k hk, (Q.block 1).1.extend_apply]
    · have hn : ¬ ∃ k', Q.κ 0 k' = Q.κ 1 k₀ := Q.new
      rw [pullDeg, pullDeg, (Q.block 1).1.extend_apply, hb.1, Function.extend_apply' _ _ _ hn]
      rfl
  · rw [h.2]
    exact hb.2 _ _ fun p hp => by rw [Q.same p hp]

theorem swap_nat {V : Type*} {n : ℕ} (I : (Fin n → V) → ℝ) (S : V → Prop)
    (hI : ∀ L : Fin n → V, (∀ j, S (L j)) → ∀ σ : Equiv.Perm (Fin n), I (L ∘ σ) = I L)
    (f : ℕ → V) (hf : ∀ j, S (f j)) (a b : ℕ) (ha : a < n) (hb : b < n) :
    I (fun j => f j) = I (fun j => f (if (j : ℕ) = a then b else if (j : ℕ) = b then a else j)) := by
  rw [← hI (fun j => f j) (fun j => hf j) (Equiv.swap ⟨a, ha⟩ ⟨b, hb⟩)]
  congr 1
  funext j
  simp only [Function.comp, Equiv.swap_apply_def, Fin.ext_iff]
  split_ifs <;> rfl

theorem interp_mem {V : Type*} {S : V → Prop} {x₁ x₂ a : V} (h₁ : S x₁) (h₂ : S x₂) (h₃ : S a)
    (k i j : ℕ) : S (interp k i x₁ x₂ a j) := by
  unfold interp
  split_ifs <;> assumption

theorem consWord_mem {V : Type*} {S : V → Prop} {x x₁ x₂ a : V} (h₀ : S x) (h₁ : S x₁) (h₂ : S x₂)
    (h₃ : S a) (k i j : ℕ) : S (consWord k i x x₁ x₂ a j) := by
  unfold consWord
  split_ifs <;> assumption

theorem word_mem {V : Type*} {S : V → Prop} {x₁ x₂ a : V} (h₁ : S x₁) (h₂ : S x₂) (h₃ : S a)
    (D k i : ℕ) (j : Fin D) : S (word D k i x₁ x₂ a j) := by
  unfold word
  split_ifs <;> assumption

theorem consWord_left {V : Type*} {D : ℕ} (I : (Fin (D + 2) → V) → ℝ) (S : V → Prop)
    (hI : ∀ L : Fin (D + 2) → V, (∀ j, S (L j)) → ∀ σ : Equiv.Perm (Fin (D + 2)), I (L ∘ σ) = I L)
    (k i : ℕ) (hi : i < k) (hD : 2 * k ≤ D + 1) {x₁ x₂ a : V} (h₁ : S x₁) (h₂ : S x₂) (h₃ : S a) :
    I (fun j => consWord k i x₁ x₁ x₂ a j) = I (fun j => interp k (i + 1) x₁ x₂ a j) := by
  rw [swap_nat I S hI (consWord k i x₁ x₁ x₂ a) (consWord_mem h₁ h₁ h₂ h₃ k i) 0 2 (by omega) (by omega)]
  congr 1
  funext j
  simp only [consWord, interp]
  split_ifs <;> first | rfl | omega | contradiction

theorem consWord_right {V : Type*} {D : ℕ} (I : (Fin (D + 2) → V) → ℝ) (S : V → Prop)
    (hI : ∀ L : Fin (D + 2) → V, (∀ j, S (L j)) → ∀ σ : Equiv.Perm (Fin (D + 2)), I (L ∘ σ) = I L)
    (k i : ℕ) (hi : i < k) (hD : 2 * k ≤ D + 1) {x₁ x₂ a : V} (h₁ : S x₁) (h₂ : S x₂) (h₃ : S a) :
    I (fun j => consWord k i x₂ x₁ x₂ a j) = I (fun j => interp k i x₁ x₂ a j) := by
  rw [swap_nat I S hI (consWord k i x₂ x₁ x₂ a) (consWord_mem h₂ h₁ h₂ h₃ k i) 1 (2 * i + 1)
      (by omega) (by omega),
    swap_nat I S hI (interp k i x₁ x₂ a) (interp_mem h₁ h₂ h₃ k i) 2 (2 * i + 2) (by omega) (by omega)]
  congr 1
  funext j
  simp only [consWord, interp]
  split_ifs <;> first | rfl | omega | contradiction

theorem firstHalf : Inputs → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ) (k₀ : K) (xi2 : K → ℤ) (Q : AlgSq P d k₀ xi2) (Xi : HermLine ι) (X₀ X₁ : HermLine Q.ιW), Xi.a = xi2 → IsSmoothHerm Xi → IsPullHerm (Q.κ 0) (Q.v 0) Xi X₀ → IsPullHerm (Q.κ 1) (Q.v 1) Xi X₁ → ∀ (A : HermLine ι) (A₀ : HermLine Q.ιW), IsSmoothHerm A → FromBase k₀ A → IsPullHerm (Q.κ 0) (Q.v 0) A A₀ → II K ι P (d + 2) (fun _ => A) = 0 ∧ ∀ k : ℕ, 1 ≤ k → 2 * k ≤ d + 2 → II K ι P (d + 2) (mix (2 * k) Xi A) = -∑ i ∈ Finset.range k, (ptsIntegral Q.PW (pot (Fin.cons X₀ (word (d + 1) k i X₀ X₁ A₀) : Fin (d + 2) → HermLine Q.ιW)) (Q.logNormT Xi) - ptsIntegral Q.PW (pot (Fin.cons X₁ (word (d + 1) k i X₀ X₁ A₀) : Fin (d + 2) → HermLine Q.ιW)) (Q.logNormT Xi)) := by
  intro hIn II hII K _ ι _ P d k₀ xi2 Q Xi X₀ X₁ hxi hsm h0 h1 A A₀ hAs hAb hA0
  have hR := GlobalTheory.T.algebraic_square_xi_intersection hIn II hII K ι P d k₀ xi2 Q Xi X₀ X₁ hxi hsm h0 h1
  obtain ⟨hP1, hP0⟩ := GlobalTheory.T.algebraic_square_intersection_pullback hIn II hII K ι P d k₀ xi2 Q
  have hX0 : IsSmoothHerm X₀ := isSmoothHerm_of_pull (Q.block 0) hsm h0
  have hX1 : IsSmoothHerm X₁ := isSmoothHerm_of_pull (Q.block 1) hsm h1
  have hA0s : IsSmoothHerm A₀ := isSmoothHerm_of_pull (Q.block 0) hAs hA0
  have hA1 : IsPullHerm (Q.κ 1) (Q.v 1) A A₀ := pull_one_of_base Q hAb hA0
  have hdeg : ((X₁.a (Q.κ 1 k₀) : ℤ) : ℝ) = -2 := by
    rw [h1.1, pullDeg, (Q.block 1).1.extend_apply, hxi, Q.xi_two_base_eq_neg_two]
    norm_num
  have hsym : ∀ L : Fin (d + 3) → HermLine Q.ιW, (∀ j, IsSmoothHerm (L j)) →
      ∀ σ : Equiv.Perm (Fin (d + 3)), II Q.KW Q.ιW Q.PW (d + 3) (L ∘ σ) = II Q.KW Q.ιW Q.PW (d + 3) L :=
    fun L hL σ => (hII.1 Q.KW Q.ιW).1 Q.PW (d + 3) L σ Q.arithW hL
  have hrot : ∀ (L' : Fin (d + 2) → HermLine Q.ιW) (N : HermLine Q.ιW), (∀ j, IsSmoothHerm (L' j)) →
      IsSmoothHerm N → II Q.KW Q.ιW Q.PW (d + 3) (Fin.snoc L' N) =
        II Q.KW Q.ιW Q.PW (d + 3) (Fin.cons N L') := by
    intro L' N hL' hN
    rw [Fin.snoc_eq_cons_rotate]
    refine hsym (Fin.cons N L') (fun j => ?_) (finRotate _)
    refine Fin.cases ?_ (fun j => ?_) j
    · simpa using hN
    · simpa using hL' j
  refine ⟨?_, ?_⟩
  · have e1 := hP1 (fun _ => A) (fun _ => A₀) X₁ (fun _ => hAs) (fun _ => hA0) hX1
    have e2 := hP0 (Fin.snoc (α := fun _ => HermLine ι) (fun _ => A) Xi)
      (Fin.snoc (α := fun _ => HermLine Q.ιW) (fun _ => A₀) X₁)
      (fun j => by
        refine Fin.lastCases ?_ (fun j => ?_) j
        · simpa using hsm
        · simpa using hAs)
      (fun j => by
        refine Fin.lastCases ?_ (fun j => ?_) j
        · simpa using h1
        · simpa using hA1)
    rw [e2, hdeg] at e1
    linarith
  · intro k hk hkD
    set g : ℕ → ℝ := fun i =>
      II Q.KW Q.ιW Q.PW (d + 3) (fun j : Fin (d + 3) => interp k i X₀ X₁ A₀ j) with hg
    have hstep : ∀ i ∈ Finset.range k,
        2 * (ptsIntegral Q.PW (pot (Fin.cons X₀ (word (d + 1) k i X₀ X₁ A₀) : Fin (d + 2) → HermLine Q.ιW)) (Q.logNormT Xi) - ptsIntegral Q.PW (pot (Fin.cons X₁ (word (d + 1) k i X₀ X₁ A₀) : Fin (d + 2) → HermLine Q.ιW)) (Q.logNormT Xi)) = g (i + 1) - g i := by
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have e0 : (Fin.cons X₀ (Fin.cons X₀ (word (d + 1) k i X₀ X₁ A₀)) : Fin (d + 3) → HermLine Q.ιW) =
          fun j : Fin (d + 3) => consWord k i X₀ X₀ X₁ A₀ j := cons_cons_word (d + 1) k i hk X₀ X₀ X₁ A₀
      have e1 : (Fin.cons X₁ (Fin.cons X₁ (word (d + 1) k i X₀ X₁ A₀)) : Fin (d + 3) → HermLine Q.ιW) =
          fun j : Fin (d + 3) => consWord k i X₁ X₀ X₁ A₀ j := cons_cons_word (d + 1) k i hk X₁ X₀ X₁ A₀
      rw [← hR (word (d + 1) k i X₀ X₁ A₀) (word_mem hX0 hX1 hA0s _ _ _), e0, e1]
      have l := consWord_left (D := d + 1) (II Q.KW Q.ιW Q.PW (d + 3)) IsSmoothHerm hsym k i hi' (by omega) hX0 hX1 hA0s
      have r := consWord_right (D := d + 1) (II Q.KW Q.ιW Q.PW (d + 3)) IsSmoothHerm hsym k i hi' (by omega) hX0 hX1 hA0s
      rw [l, r]
    have h00 : g 0 = 0 := by
      rw [← hP0 (mix (1 + 2 * k) Xi A) (mix (1 + 2 * k) X₁ A₀)
        (fun j => by unfold mix; split_ifs <;> assumption)
        (fun j => by unfold mix; split_ifs <;> assumption)]
      simp only [hg]
      congr 1
      funext j
      simp only [interp, mix]
      split_ifs <;> first | rfl | omega | contradiction
    have hgk : g k = -2 * II K ι P (d + 2) (mix (2 * k) Xi A) := by
      have e := hP1 (mix (2 * k) Xi A) (mix (2 * k) X₀ A₀) X₁
        (fun j => by unfold mix; split_ifs <;> assumption)
        (fun j => by unfold mix; split_ifs <;> assumption) hX1
      rw [hrot _ X₁ (fun j => by unfold mix; split_ifs <;> assumption) hX1, hdeg] at e
      rw [← e]
      simp only [hg]
      congr 1
      funext j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp [interp]
      simp only [Fin.cons_succ, interp, mix, Fin.val_succ]
      split_ifs <;> first | rfl | omega | contradiction
    have hsum := Finset.sum_range_sub g k
    rw [← Finset.sum_congr rfl hstep, ← Finset.mul_sum, h00, hgk] at hsum
    linarith

end GlobalTheory.CompanionTheory.Ar.PB.SqFirst
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.AmpleOnGenericFibreOfSemipositiveStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ample_on_generic_fibre_of_semipositive : PB.Inputs → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MRing J)) (N A : HermLine J) (a' : K → ℤ) (m p : ℕ), IsSemipositiveH P N → IsSmoothHerm A → (∀ k, 0 < a' k) → 1 ≤ m → 1 ≤ p → (m : ℤ) • A.a = N.a + (p : ℤ) • a' → AmpleOnGenericFibre P A := by
  first | exact @GlobalTheory.CompanionTheory.Relay.ample_on_generic_fibre_of_semipositive | exact GlobalTheory.CompanionTheory.Relay.ample_on_generic_fibre_of_semipositive | (intros; apply GlobalTheory.CompanionTheory.Relay.ample_on_generic_fibre_of_semipositive <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BigLineImpliesHeightPositivity
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.Small Filter Topology

namespace GlobalTheory.CompanionTheory.Ar.Small

theorem selfIntersection_le_volNm_of_moriwakiBig : MoriwakiBigStatement → BirationalPullbackPushforwardFormula := by
  intro h K _ ι _ Ω _ y D A P0 II hD hII hV hB hP hS hF hC
  have hN : NefOnGeneric (mCoordIdeal y) A :=
    GroundTheory.Heights₂.Heights.HilbertSamuel.NefOnGenericOfSemipos.proof K ι (mCoordIdeal y) P0 A hP hS
  have hb := h K ι Ω y D A P0 II hII hV hB hP hS hC hF hN
  obtain ⟨hfin, C, hC'⟩ := GlobalTheory.T.packing' K ι Ω y D A (chartLatNm y A.a) hV hB hS.1 (fun _ => le_rfl)
  refine hb.trans ?_
  unfold arVolP
  have h0 : ∀ (La : ℕ → AddSubgroup Ω) (τ : ℕ), 0 ≤ smallSectionCount (IsSmallH (mCoordIdeal y) y A) La τ := by
    intro La τ
    unfold smallSectionCount
    exact Real.log_natCast_nonneg _
  have hden : ∀ k : ℕ, (0 : ℝ) ≤ ((1 * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ) := fun k => by positivity
  refine Filter.limsup_le_limsup ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun k => div_le_div_of_nonneg_right
      (GroundTheory.Heights₂.Heights.HilbertSamuel.smallSectionCount_mono_lattice _ _
        (GroundTheory.Heights₂.Heights.HilbertSamuel.chartLat_le_chartLatNm y A.a _) (hfin _)) (hden k)
  · exact Filter.isCoboundedUnder_le_of_le Filter.atTop (fun k => div_nonneg (h0 _ _) (hden k))
  · refine Filter.isBoundedUnder_of_eventually_le (a := max C 0 * 2 ^ (D + 1) * ((D + 1).factorial : ℝ)) ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with k hk
    have hkpos : (0 : ℝ) < ((1 * k : ℕ) : ℝ) := by
      rw [one_mul]
      exact_mod_cast hk
    have hF : (0 : ℝ) < ((D + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have hpos : (0 : ℝ) < ((1 * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ) := by positivity
    rw [div_le_iff₀ hpos]
    have h1 := hC' (1 * k)
    have h2 : ((1 * k : ℕ) : ℝ) + 1 ≤ 2 * ((1 * k : ℕ) : ℝ) := by
      have : (1 : ℝ) ≤ ((1 * k : ℕ) : ℝ) := by
        rw [one_mul]
        exact_mod_cast hk
      linarith
    have h3 : (((1 * k : ℕ) : ℝ) + 1) ^ (D + 1) ≤ (2 * ((1 * k : ℕ) : ℝ)) ^ (D + 1) :=
      pow_le_pow_left₀ (by positivity) h2 _
    have h4 : C * (((1 * k : ℕ) : ℝ) + 1) ^ (D + 1) ≤ max C 0 * (((1 * k : ℕ) : ℝ) + 1) ^ (D + 1) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    have hF' := hF.ne'
    calc _ ≤ max C 0 * (2 * ((1 * k : ℕ) : ℝ)) ^ (D + 1) :=
          h1.trans (h4.trans (mul_le_mul_of_nonneg_left h3 (le_max_right _ _)))
      _ = max C 0 * 2 ^ (D + 1) * ((D + 1).factorial : ℝ) *
          (((1 * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) := by
        field_simp
        ring

end GlobalTheory.CompanionTheory.Ar.Small
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockGBlockDiagPosDef
section
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PB.BMx

theorem blockG_isBlockDiag_posDef :
    ∀ (p q : ℕ) (Γ : Matrix (Fin (p + q)) (Fin (p + q)) ℂ), Γ.PosDef →
      IsBlockDiag p (blockG Γ) ∧ (blockG Γ).PosDef :=
  PositivityTheory.Xgp.t_c_bm_exists_blockpos

end GlobalTheory.CompanionTheory.Ar.PB.BMx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ConvergenceStatementHoldsStatement
section
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.convergence_statement_holds : ConvergenceStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.convergence_holds | exact GlobalTheory.CompanionTheory.Ar.Giv.convergence_holds | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.convergence_holds <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.CorrectedWeightRegularizationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.corrected_weight_regularization : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) [DecidableEq Ψ] [Nonempty Ψ] (M : XModel D) (U : ((Σ k, J k) → ℂ) → ℝ) (S : LogLogRegularisationSetting M D.Xo (muLine Hd)) (S' : BoundedRegularisationSetting M D.Xo Hd.aMu (corrW Hd U)) (rd Lval Ch Cu : ℝ), S.IsTied → S'.IsTied → (∀ z, 0 ≤ U z) → (∀ z ∈ D.Xo, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → U (torusSmul c z) = U z) → PosU S' → ConjU S' → HtU S' Ch rd Lval → MeanU Hd U Cu rd Lval → ∃ X : ComponentSetting D ℤ (Fin 2 → ℤ), X.H = Hd ∧ (∀ z ∈ D.Xo, X.Cd.cuspWeight z = U z) ∧ X.rd = rd ∧ X.Lval = Lval ∧ CuspBundlePos X ∧ MUConjInvariant X ∧ HtInterior Ch X ∧ HtBoundary Ch X ∧ CuspMean Cu X := by
  first | exact @GlobalTheory.CompanionTheory.Relay.corrected_weight_regularization | exact GlobalTheory.CompanionTheory.Relay.corrected_weight_regularization | (intros; apply GlobalTheory.CompanionTheory.Relay.corrected_weight_regularization <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.CutoffFunctionOnCompatibleAtlas
section
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

theorem GlobalTheory.CompanionTheory.Metric.blockG_bounds_of_local_gram_bounds : ∀ (n p q : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A B : FinHolAtlas n X) (Z Cl U : Set X) (r : X → ℝ) (Γ : X → Matrix (Fin (p + q)) (Fin (p + q)) ℂ), A.Compatible B → (∀ k, Metric.closedBall (0 : Fin n → ℂ) 2 ⊆ (B.chart k).target) → (∀ x, ∃ k, x ∈ (B.chart k).source ∧ B.chart k x ∈ Metric.ball (0 : Fin n → ℂ) 1) → IsClosed Z → IsClosed Cl → IsOpen U → U ⊆ Cl → (∀ x, x ∉ Z → Real.exp 1 ≤ r x) → (∀ (k : Fin B.n) (w₀ : Fin n → ℂ), w₀ ∈ Metric.closedBall (0 : Fin n → ℂ) (3 / 2) → (B.chart k).symm w₀ ∈ Cl → ∃ ε c C : ℝ, 0 < ε ∧ 0 < c ∧ 0 < C ∧ ∀ w : Fin n → ℂ, ‖w - w₀‖ < ε → (B.chart k).symm w ∉ Z → (Γ ((B.chart k).symm w)).PosDef ∧ ((Γ ((B.chart k).symm w))⁻¹ - (c : ℂ) • (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℂ)).PosSemidef ∧ (((C * r ((B.chart k).symm w) : ℝ) : ℂ) • (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) - (Γ ((B.chart k).symm w))⁻¹).PosSemidef ∧ ∀ a b, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w' => Γ ((B.chart k).symm w') a b) w ∧ ‖fderiv ℝ (fun w' => Γ ((B.chart k).symm w') a b) w‖ ≤ C * Real.exp (r ((B.chart k).symm w) / 2)) → (∀ a b, A.SmoothOn (U \ Z) (fun x => (blockG (Γ x) a b).re) ∧ A.SmoothOn (U \ Z) (fun x => (blockG (Γ x) a b).im)) ∧ ∃ C₀ : ℝ, ∀ C : ℝ, C₀ ≤ C → (∀ x ∈ Cl \ Z, (((r x ^ C : ℝ) : ℂ) • (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) - blockG (Γ x)).PosSemidef ∧ (((r x ^ C : ℝ) : ℂ) • blockG (Γ x) - 1).PosSemidef) ∧ ∀ (a b : Fin (p + q)) (k : Fin B.n), ∀ w ∈ Metric.ball (0 : Fin n → ℂ) (3 / 2), (B.chart k).symm w ∈ Cl \ Z → ‖fderiv ℝ (fun w' => blockG (Γ ((B.chart k).symm w')) a b) w‖ ≤ C * r ((B.chart k).symm w) ^ C * Real.exp (r ((B.chart k).symm w) / 2) :=
  @PositivityTheory.Xgp.t_c_bm_exists_bounds
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsAnalyticLogResolutionStatement
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_analytic_log_resolution : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (y : (Σ k, ι k) → Ω) (D : ℕ), IsArithVar (mCoordIdeal y) (D + 1) → SmoothGenericFibreM y → Nonempty (AnLogRes (mCoordIdeal y) ⊤ D) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.nonempty_anLogRes_of_smoothGenericFibre | exact GlobalTheory.CompanionTheory.Ar.PB.nonempty_anLogRes_of_smoothGenericFibre | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.nonempty_anLogRes_of_smoothGenericFibre <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsFiniteFrameCover
section
open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PB.BMx.Frames

theorem exists_finite_good_frames : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j n : ℕ) (M : FlagModel y Ψ N j) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n), ∃ (q : ℕ) (O : Fin q → Set Rb.X) (F : Fin q → FrameData ι Ψ N M.Ω M.blk), (∀ l, IsOpen (O l)) ∧ (∀ x, ∃ l, x ∈ O l) ∧ (∀ l, M.IsFrame (F l)) ∧ ∀ l, ∀ x ∈ closure (O l), M.GoodAt (F l) (mCoordIdeal (Rb.lift x x)) := by
  exact @PositivityTheory.Xgp.t_c_bm_exists_frames

end GlobalTheory.CompanionTheory.Ar.PB.BMx.Frames
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentFrameComparisonStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_adjacent_frame_comparison : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (F₁ F₂ : FrameData ι Ψ N M.Ω M.blk) (z₀ z₁ : (Σ k, ι k) → ℂ) (h : Matrix (Fin N) (Fin N) ℂ) (t : ℂ), basePart M.blk z₀ ∈ mcPts (mCoordIdeal M.x) → (∀ k, ∃ i, z₀ ⟨k, i⟩ ≠ 0) → (∀ k, ∃ i, z₁ ⟨k, i⟩ ≠ 0) → basePart M.blk z₁ = basePart M.blk z₀ → M.IsFrame F₁ → M.IsFrame F₂ → M.GoodAt F₁ (mCoordIdeal (basePart M.blk z₀)) → M.GoodAt F₂ (mCoordIdeal (basePart M.blk z₀)) → IsBlockDiag j h → h.det ≠ 0 → t ≠ 0 → (∀ i, M.ExactAt F₂ (τ, i) z₀ h) → (∀ i, M.ExactAt F₂ (τ, i) z₁ (h * (1 + Matrix.single cb ca t))) → ∃ (z₀' z₁' : (Σ k, ι k) → ℂ) (S : Matrix (Fin N) (Fin N) ℂ), SameOrbit z₀' z₀ ∧ SameOrbit z₁' z₁ ∧ IsBlockDiag j S ∧ S.det ≠ 0 ∧ (∀ i, M.ExactAt F₁ (τ, i) z₀' (S * h)) ∧ (∀ i, M.ExactAt F₁ (τ, i) z₁' (S * h * (1 + Matrix.single cb ca t))) ∧ normRhs M τ a F₁ z₀' z₁' (S * h) t = normRhs M τ a F₂ z₀ z₁ h t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Move.main | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Move.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Move.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentSwapVarietiesArithmetic
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.flag_adjacent_swap_varieties_arithmetic : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (d : ℕ) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsArithVar (mCoordIdeal y) (d + 2) → IsArithVar (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) (d + 3) ∧ IsArithVar (mCoordIdeal (M.wCo (τ, a) k₀ ca cb 0)) (d + 2) ∧ mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X) ≤ mCoordIdeal (M.wCo (τ, a) k₀ ca cb 0) ∧ imageZ (fun p : (Σ k, ι k) => (⟨some p.1, p.2⟩ : Σ o : Option K, ι (o.getD k₀))) (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) = mCoordIdeal y ∧ ∀ v₁ : (Σ k, ι k) → (Σ o : Option K, ι (o.getD k₀)), (∀ p : (Σ k, ι k), p.1 ≠ k₀ → v₁ p = ⟨some p.1, p.2⟩) → (∀ m : ι k₀, v₁ ⟨k₀, m⟩ = ⟨none, m⟩) → imageZ v₁ (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) = mCoordIdeal y := by
  first | exact @PositivityTheory.Xgp.t_c_w_arith | exact PositivityTheory.Xgp.t_c_w_arith
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentTwistedResolution
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec

theorem isBlockDiag_one_add_single {N j : ℕ} {ca cb : Fin N} (hs : (ca : ℕ) < N - j ↔ (cb : ℕ) < N - j) (t : ℂ) :
    IsBlockDiag j (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) := by
  intro r s hrs
  have h1 : (1 : Matrix (Fin N) (Fin N) ℂ) r s = 0 := Matrix.one_apply_ne fun e => hrs (by rw [e])
  have h2 : (Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) r s = 0 := by
    rw [Matrix.single_apply, if_neg]
    rintro ⟨rfl, rfl⟩
    exact hrs hs.symm
  rw [Matrix.add_apply, h1, h2, add_zero]

theorem not_sameOrbit_of_ptData : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X), IsWAtlas M Rb τ a k₀ ca cb RW pr → ∀ (x : RW.X) (z₀ z₁ : (Σ k, ι k) → ℂ) (F : FrameData ι Ψ N M.Ω M.blk) (h : Matrix (Fin N) (Fin N) ℂ) (t : ℂ), IsPtData M τ a k₀ ca cb RW x z₀ z₁ F h t → ¬ SameOrbit (fstPt k₀ (RW.lift x x)) (sndPt k₀ (RW.lift x x)) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb τ a b k₀ ca cb hb hab hk hca hcb RW pr hW x z₀ z₁ F h t hP hOrb
  obtain ⟨hF, hG, h0, h1, hbd, hdet, ht, hE0, hE1⟩ := hP
  obtain ⟨hb0, -, -, -⟩ := GlobalTheory.T.twisted_atlas_compatibility K ι Φ y Ψ N j M n e Rb τ a k₀ ca cb RW pr hk hW x z₀ z₁ h0 h1
  obtain ⟨c, hc, hcz⟩ : SameOrbit z₁ z₀ := orbit_trans (orbit_trans h1 (orbit_symm hOrb)) (orbit_symm h0)
  have hz : ∀ q, z₁ q = c q.1 * z₀ q := fun q => congrFun hcz q

  have hbase : basePart M.blk z₁ = basePart M.blk z₀ := by
    funext q
    have e₀ : z₀ ⟨q.1.1, F.c q.1⟩ = 1 := (hE0 a).1 q.1
    have e₁ : z₁ ⟨q.1.1, F.c q.1⟩ = 1 := (hE1 a).1 q.1
    have hc1 : c q.1.1 = 1 := by
      have := hz ⟨q.1.1, F.c q.1⟩
      rw [e₀, e₁, mul_one] at this
      exact this.symm
    show z₁ ⟨q.1.1, q.2⟩ = z₀ ⟨q.1.1, q.2⟩
    rw [hz, show c (Sigma.fst (⟨q.1.1, q.2⟩ : Σ k, ι k)) = 1 from hc1, one_mul]
  have hs : (ca : ℕ) < N - j ↔ (cb : ℕ) < N - j := by
    have hN := M.j_le
    have ha := a.2
    have hb' := b.2
    unfold lastCol at hca
    split_ifs at hca with hl <;> omega
  have hbd₁ : IsBlockDiag j (h * (1 + Matrix.single cb ca t)) := hbd.mul (isBlockDiag_one_add_single hs t)
  have hplk : ∀ m : ι k₀, plk M F (basePart M.blk z₀) (τ, a).2 ⟨k₀, m⟩ (h * (1 + Matrix.single cb ca t)) =
      c k₀ * plk M F (basePart M.blk z₀) (τ, a).2 ⟨k₀, m⟩ h := fun m => by
    have e₀ := (hE0 a).2 k₀ hk m
    have e₁ := (hE1 a).2 k₀ hk m
    rw [hbase] at e₁
    have e₂ := hz ⟨k₀, m⟩
    rw [e₁, e₀] at e₂
    exact e₂
  have hmin := Ind.minor_eq_of_plk M hb0 hF hG hk hbd₁ hbd hplk
  have hpl := GlobalTheory.T.elementary_twist_minor_scalar N j a b ca cb M.j_le hb hab hca hcb h 1 0 t (c k₀) hdet isBlockDiag_one
    Matrix.blockTriangular_one (fun I => by
      have e : (1 + Matrix.single cb ca (0 : ℂ) : Matrix (Fin N) (Fin N) ℂ) = 1 := by simp
      rw [e, Matrix.mul_one]
      exact hmin I)
  have h2 := hpl.2
  simp only [mul_zero, Matrix.one_apply_eq, mul_one, Finset.prod_const_one, one_mul] at h2
  exact ht h2.symm

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec
end
end

