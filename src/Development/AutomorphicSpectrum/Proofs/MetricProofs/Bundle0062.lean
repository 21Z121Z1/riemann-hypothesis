import Mathlib
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.Bundle0001
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.SheetDensityEqSetSheetDensity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0018
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0039
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0049
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0018
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0057
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0006
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0005
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0032
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0054
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0042
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0056
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0038

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MemChartComponents
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxChart

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def chartSet (S : Set ((Σ k, ι k) → ℂ)) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) :
    Set (Fin m → ℂ) :=
  {x | ∃ z ∈ S, segre z i = 1 ∧ x = fun a => segre z (σ a)}

def chartIdeal (S : Set ((Σ k, ι k) → ℂ)) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) :
    Ideal (MvPolynomial (Fin m) ℂ) :=
  MvPolynomial.vanishingIdeal ℂ (chartSet S σ i)

def chartComponents (S : Set ((Σ k, ι k) → ℂ)) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (i : (k : K) → ι k) : Finset (Ideal (MvPolynomial (Fin m) ℂ)) :=
  (Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin m) ℂ)
    (chartIdeal S σ i)).toFinset

omit [∀ k, Fintype (ι k)] in
theorem mem_chartComponents {S : Set ((Σ k, ι k) → ℂ)} {m : ℕ} {σ : Fin m ≃ ((k : K) → ι k)}
    {i : (k : K) → ι k} {J : Ideal (MvPolynomial (Fin m) ℂ)} :
    J ∈ chartComponents S σ i ↔ J ∈ (chartIdeal S σ i).minimalPrimes :=
  Set.Finite.mem_toFinset _

def chartSection [DecidableEq K] {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (s : MRingOver ℂ ι) : MvPolynomial (Fin m) ℂ :=
  aeval (fun q : Σ k, ι k => (X (σ.symm (Function.update i q.1 q.2)) : MvPolynomial (Fin m) ℂ)) s

def domCell (i : (k : K) → ι k) : Set ((Σ k, ι k) → ℂ) :=
  {z | ∀ i', ‖segre z i'‖ ≤ ‖segre z i‖}

open Classical in

def absLogNorm (A : HermLine ι) (s : MRingOver ℂ ι) (z : (Σ k, ι k) → ℂ) : ℝ :=
  if ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0 then |logNormC A s z| else 0

end GlobalTheory.CompanionTheory.Ar.Pub.CxChart
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorIJLowerUniSwap
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.PFl.MatRead

theorem det_of_key {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) (f : Fin m → ℕ) (hf : Function.Injective f)
    (h : ∀ i j, f i < f j → A i j = 0) : A.det = ∏ i, A i i := by
  rw [Matrix.det_apply, Finset.sum_eq_single 1]
  · simp
  · intro σ _ hσ
    obtain ⟨i, hi⟩ : ∃ i, f (σ i) < f i := by
      by_contra hne
      simp only [not_exists, not_lt] at hne
      apply hσ
      have hsum : ∑ i, f (σ i) = ∑ i, f i := Equiv.sum_comp σ f
      have heq := (Finset.sum_eq_sum_iff_of_le (fun i _ => hne i)).mp hsum.symm
      refine Equiv.ext (fun i => ?_)
      exact (hf (heq i (Finset.mem_univ i)).symm : σ i = i)
    have hz : ∏ j, A (σ j) j = 0 := Finset.prod_eq_zero (Finset.mem_univ i) (h _ _ hi)
    rw [hz, smul_zero]
  · intro h1
    exact absurd (Finset.mem_univ 1) h1

private theorem minor_col_lemma {N : ℕ} (X : Matrix (Fin N) (Fin N) ℂ) (hX : IsLowerUni X)
    (S I : Finset (Fin N)) (a b : Fin N) (hb : b ∈ S) (hIS : I.erase a = S.erase b)
    (hcol : ∀ d ∈ I, d ≠ a → X d b = 0) (k : ℕ) (hI : I.card = k) (hS : S.card = k)
    (p q : Fin k) (hp : I.orderEmbOfFin hI p = a) (hq : S.orderEmbOfFin hS q = b) :
    (X.submatrix (I.orderEmbOfFin hI) (S.orderEmbOfFin hS)).det = (-1) ^ ((p : ℕ) + (q : ℕ)) * X a b := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by have := Finset.card_pos.mpr ⟨b, hb⟩; omega⟩
  have hcol' : ∀ i, i ≠ p → X (I.orderEmbOfFin hI i) b = 0 := by
    intro i hi
    refine hcol _ (Finset.orderEmbOfFin_mem I hI i) (fun h1 => hi ?_)
    apply (I.orderEmbOfFin hI).injective
    rw [h1, hp]
  have hT : (S.erase b).card = n := by
    rw [Finset.card_erase_of_mem hb, hS, Nat.add_sub_cancel]
  have hg' : ⇑(S.orderEmbOfFin hS) ∘ q.succAbove = (S.erase b).orderEmbOfFin hT := by
    apply Finset.orderEmbOfFin_unique hT
    · intro x
      rw [Function.comp_apply, Finset.mem_erase]
      exact ⟨fun h1 => Fin.succAbove_ne q x ((S.orderEmbOfFin hS).injective (h1.trans hq.symm)),
        Finset.orderEmbOfFin_mem S hS _⟩
    · exact (S.orderEmbOfFin hS).strictMono.comp (Fin.strictMono_succAbove q)
  have hg : ⇑(I.orderEmbOfFin hI) ∘ p.succAbove = (S.erase b).orderEmbOfFin hT := by
    apply Finset.orderEmbOfFin_unique hT
    · intro x
      rw [Function.comp_apply, ← hIS, Finset.mem_erase]
      exact ⟨fun h1 => Fin.succAbove_ne p x ((I.orderEmbOfFin hI).injective (h1.trans hp.symm)),
        Finset.orderEmbOfFin_mem I hI _⟩
    · exact (I.orderEmbOfFin hI).strictMono.comp (Fin.strictMono_succAbove p)
  have hdetT : (X.submatrix ((S.erase b).orderEmbOfFin hT) ((S.erase b).orderEmbOfFin hT)).det = 1 := by
    rw [det_of_key _ (fun i => (((S.erase b).orderEmbOfFin hT i : Fin N) : ℕ)) ?_ ?_]
    · exact Finset.prod_eq_one (fun i _ => hX.1 _)
    · intro i j hij
      exact ((S.erase b).orderEmbOfFin hT).injective (Fin.ext hij)
    · intro i j hij
      exact hX.2 _ _ hij
  rw [Matrix.det_succ_column _ q, Finset.sum_eq_single p]
  · have e1 : (X.submatrix (I.orderEmbOfFin hI) (S.orderEmbOfFin hS)) p q = X a b := by
      rw [Matrix.submatrix_apply, hp, hq]
    rw [e1, Matrix.submatrix_submatrix, hg, hg', hdetT, mul_one]
  · intro i _ hi
    rw [Matrix.submatrix_apply, hq, hcol' i hi, mul_zero, zero_mul]
  · intro h1
    exact absurd (Finset.mem_univ p) h1

theorem exists_sign {N : ℕ} (S : Finset (Fin N)) (a b : Fin N) (ha : a ∉ S) (hb : b ∈ S) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ X : Matrix (Fin N) (Fin N) ℂ, IsLowerUni X → (∀ d ∈ S, d ≠ b → X d b = 0) →
      minorIJ X (insert a (S.erase b)) S = c * X a b := by
  have haS : a ∉ S.erase b := fun h1 => ha (Finset.mem_of_mem_erase h1)
  have hcard : (insert a (S.erase b)).card = S.card := by
    rw [Finset.card_insert_of_notMem haS, Finset.card_erase_of_mem hb]
    have := Finset.card_pos.mpr ⟨b, hb⟩
    omega
  obtain ⟨p, hp⟩ : ∃ p, (insert a (S.erase b)).orderEmbOfFin hcard p = a := by
    have h1 : a ∈ Set.range ((insert a (S.erase b)).orderEmbOfFin hcard) := by
      rw [Finset.range_orderEmbOfFin]
      exact Finset.mem_insert_self _ _
    exact h1
  obtain ⟨q, hq⟩ : ∃ q, S.orderEmbOfFin rfl q = b := by
    have h1 : b ∈ Set.range (S.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]
      exact hb
    exact h1
  refine ⟨(-1) ^ ((p : ℕ) + (q : ℕ)), pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero), fun X hX hcol => ?_⟩
  rw [minorIJ, dif_pos hcard]
  refine minor_col_lemma X hX S _ a b hb (Finset.erase_insert haS) ?_ _ hcard rfl p q hp hq
  intro d hd hda
  rcases Finset.mem_insert.mp hd with h1 | h1
  · exact absurd h1 hda
  · exact hcol d (Finset.mem_of_mem_erase h1) (Finset.ne_of_mem_erase h1)

theorem minor_replace : ∀ (N : ℕ) (X : Matrix (Fin N) (Fin N) ℂ) (S : Finset (Fin N)) (a b : Fin N), IsLowerUni X → a ∉ S → b ∈ S → b < a → (∀ c ∈ S, c ≠ b → X c b = 0) → minorIJ X (insert a (S.erase b)) S = pSgn S a b * X a b ∧ pSgn S a b ≠ 0 := by
  intro N X S a b hX ha hb hba hcol
  obtain ⟨c, hc0, hc⟩ := exists_sign S a b ha hb
  have hab : a ≠ b := (ne_of_lt hba).symm
  have hY : IsLowerUni (1 + Matrix.single a b (1 : ℂ)) := by
    refine ⟨fun i => ?_, fun i j hij => ?_⟩
    · rw [Matrix.add_apply, Matrix.one_apply_eq, Matrix.single_apply,
        if_neg (fun h1 => hab (h1.1.trans h1.2.symm)), add_zero]
    · rw [Matrix.add_apply, Matrix.one_apply_ne (ne_of_lt hij), Matrix.single_apply,
        if_neg (fun h1 => lt_asymm hba (by rw [h1.1, h1.2]; exact hij)), add_zero]
  have hYcol : ∀ d ∈ S, d ≠ b → (1 + Matrix.single a b (1 : ℂ)) d b = 0 := by
    intro d hd hdb
    have hda : d ≠ a := fun h1 => ha (h1 ▸ hd)
    rw [Matrix.add_apply, Matrix.one_apply_ne hdb, Matrix.single_apply,
      if_neg (fun h1 => hda h1.1.symm), add_zero]
  have hp : pSgn S a b = c := by
    rw [pSgn, hc _ hY hYcol, Matrix.add_apply, Matrix.one_apply_ne hab, Matrix.single_apply,
      if_pos ⟨rfl, rfl⟩, zero_add, mul_one]
  rw [hp]
  exact ⟨hc X hX hcol, hc0⟩

end GlobalTheory.CompanionTheory.Ar.PB.PFl.MatRead
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.NefThresholdGapCondition
section
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Conj.GapThreshold

theorem ent_of_lt {T : Type} [Fintype T] {N : ℕ} (mu : GlobalTheory.CompanionTheory.Ar.Top.Wt T N) (τ : T) {i : ℕ} (h : i < N) :
    GlobalTheory.CompanionTheory.Ar.Top.ent mu τ i = mu τ ⟨i, h⟩ := by
  unfold GlobalTheory.CompanionTheory.Ar.Top.ent
  rw [dif_pos h]

theorem abs_le_norm {T : Type} [Fintype T] {N : ℕ} (mu : GlobalTheory.CompanionTheory.Ar.Top.Wt T N) (τ : T) (i : Fin N) :
    |mu τ i| ≤ ‖mu‖ := by
  have h1 : ‖mu τ i‖ ≤ ‖mu τ‖ := norm_le_pi_norm (mu τ) i
  have h2 : ‖mu τ‖ ≤ ‖mu‖ := norm_le_pi_norm mu τ
  rw [Real.norm_eq_abs] at h1
  exact h1.trans h2

theorem gapCond_of_threshold {T : Type} [Fintype T] {N j p : ℕ} (mu : GlobalTheory.CompanionTheory.Ar.Top.Wt T N)
    (hp : 2 < p) (hj : 1 ≤ j) (hjN : j < N) (hd : GlobalTheory.CompanionTheory.Ar.Top.Dominant mu)
    (ht : GlobalTheory.CompanionTheory.Ar.Top.NefThreshold j p mu) :
    GapCond p j (N - j) (fun τ i => GlobalTheory.CompanionTheory.Ar.Top.ent mu τ (i - 1)) := by
  unfold GlobalTheory.CompanionTheory.Ar.Top.NefThreshold GlobalTheory.CompanionTheory.Ar.Top.gap at ht
  unfold GlobalTheory.CompanionTheory.Ar.Top.Dominant at hd
  have hp' : (0 : ℝ) < (p : ℝ) - 2 := by
    have : (2 : ℝ) < p := by exact_mod_cast hp
    linarith
  unfold GapCond
  refine ⟨?_, ‖mu‖, 4 * (Fintype.card T) * ‖mu‖ / ((p : ℝ) - 2), ?_, ?_, ?_⟩
  · intro τ i hi hiN
    have h1 : i < N := by omega
    have h0 : i - 1 < N := by omega
    simp only [Nat.add_sub_cancel]
    rw [ent_of_lt mu τ h1, ent_of_lt mu τ h0]
    exact hd τ ⟨i - 1, h0⟩ ⟨i, h1⟩ (Fin.mk_le_mk.2 (by omega))
  · intro τ i hi hiN
    have h0 : i - 1 < N := by omega
    simp only
    rw [ent_of_lt mu τ h0]
    exact abs_le_norm mu τ _
  · intro τ
    simp only [Nat.add_sub_cancel]
    rw [div_le_iff₀ hp']
    linarith [ht τ, mul_comm ((p : ℝ) - 2) (GlobalTheory.CompanionTheory.Ar.Top.ent mu τ (j - 1) - GlobalTheory.CompanionTheory.Ar.Top.ent mu τ j)]
  · have e : ((p : ℝ) - 2) * (4 * (Fintype.card T) * ‖mu‖ / ((p : ℝ) - 2)) = 4 * (Fintype.card T) * ‖mu‖ := by
      field_simp
    exact e.ge

theorem lmuNum_eq_sum {T : Type} [Fintype T] {N j : ℕ} (mu : GlobalTheory.CompanionTheory.Ar.Top.Wt T N)
    (x : T × Fin N → ℝ) (w l : T → ℕ → ℝ) (hjN : j < N)
    (hx : ∀ τ (i : Fin N), (i : ℕ) < j → x (τ, i) = w τ (i + 1) - w τ i)
    (hy : ∀ τ (i : Fin N), j ≤ (i : ℕ) → x (τ, i) = -(l τ (N - 1 - i + 1) - l τ (N - 1 - i))) :
    lmuNum j (N - j) (fun τ i => GlobalTheory.CompanionTheory.Ar.Top.ent mu τ (i - 1)) w l = ∑ r : T × Fin N, -mu r.1 r.2 * x r := by
  classical
  unfold lmuNum
  set xx : T → ℕ → ℝ := fun τ i => if h : i < N then x (τ, ⟨i, h⟩) else 0 with hxx
  have hrow : ∀ τ, ∑ i : Fin N, -mu τ i * x (τ, i) =
      ∑ i ∈ Finset.range N, -GlobalTheory.CompanionTheory.Ar.Top.ent mu τ i * xx τ i := by
    intro τ
    rw [← Fin.sum_univ_eq_sum_range (fun i => -GlobalTheory.CompanionTheory.Ar.Top.ent mu τ i * xx τ i) N]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hxx, dif_pos i.isLt, ent_of_lt mu τ i.isLt]
  rw [Fintype.sum_prod_type, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [hrow τ, ← Finset.sum_range_add_sum_Ico _ hjN.le, Finset.sum_Ico_eq_sum_range, neg_add]
  congr 1
  · rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hij : i < j := Finset.mem_range.1 hi
    have hiN : i < N := by omega
    have hx' := hx τ ⟨i, hiN⟩ hij
    simp only [hxx, dif_pos hiN, Nat.add_sub_cancel, hx']
    ring
  · rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hmj : m < N - j := Finset.mem_range.1 hm
    have hiN : j + m < N := by omega
    have hy' := hy τ ⟨j + m, hiN⟩ (by simp)
    have e1 : N - 1 - (j + m) + 1 = N - j - m := by omega
    have e2 : N - 1 - (j + m) = N - j - m - 1 := by omega
    simp only [hxx, dif_pos hiN, Nat.add_sub_cancel, hy']
    rw [e1, e2]
    ring

theorem gapCond_and_lmuNum : ∀ (T : Type) [Fintype T] (N j p : ℕ) (mu : GlobalTheory.CompanionTheory.Ar.Top.Wt T N) (x : T × Fin N → ℝ) (w l : T → ℕ → ℝ), 2 < p → 1 ≤ j → j < N → GlobalTheory.CompanionTheory.Ar.Top.Dominant mu → GlobalTheory.CompanionTheory.Ar.Top.NefThreshold j p mu → (∀ τ (i : Fin N), (i : ℕ) < j → x (τ, i) = w τ (i + 1) - w τ i) → (∀ τ (i : Fin N), j ≤ (i : ℕ) → x (τ, i) = -(l τ (N - 1 - i + 1) - l τ (N - 1 - i))) → GapCond p j (N - j) (fun τ i => GlobalTheory.CompanionTheory.Ar.Top.ent mu τ (i - 1)) ∧ lmuNum j (N - j) (fun τ i => GlobalTheory.CompanionTheory.Ar.Top.ent mu τ (i - 1)) w l = ∑ r : T × Fin N, -mu r.1 r.2 * x r := by
  intro T _ N j p mu x w l hp hj hjN hd ht hx hy
  exact ⟨gapCond_of_threshold mu hp hj hjN hd ht, lmuNum_eq_sum mu x w l hjN hx hy⟩

end GlobalTheory.CompanionTheory.Ar.Conj.GapThreshold
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.OrthogonalFlagDegreeComparison
section
open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.FlagPair

theorem iSup_part_degree_rank {K : Type} [Field K] [NumberField K] {E : HermitianBundle.{0} K}
    {Ψ : Type} [Fintype Ψ] {j k : ℕ} (A : FlagPair E Ψ j k) (h : A.IsOrthFull) :
    E.normDegree (⨆ a, A.part a) =
        ∑ τ, E.normDegree (A.W τ).top + ∑ τ, E.normDegree (A.S τ).top ∧
      E.rank (⨆ a, A.part a) = Module.finrank (𝓞 K) E.carrier := by
  unfold GlobalTheory.CompanionTheory.Ar.FlagPair.IsOrthFull at h
  obtain ⟨hort, hcard⟩ := h
  obtain ⟨hdeg, hrk⟩ := GlobalTheory.T.normalized_degree_orthogonal_sum K E (Ψ ⊕ Ψ) A.part hort
  refine ⟨?_, ?_⟩
  · rw [hdeg, Fintype.sum_sum_type]
    rfl
  · have hW : ∀ τ, E.rank (A.part (Sum.inl τ)) = j := fun τ => by
      show E.rank ((A.W τ).F (Fin.last j)) = j
      rw [(A.W τ).rank (Fin.last j), Fin.val_last]
    have hS : ∀ τ, E.rank (A.part (Sum.inr τ)) = k := fun τ => by
      show E.rank ((A.S τ).F (Fin.last k)) = k
      rw [(A.S τ).rank (Fin.last k), Fin.val_last]
    rw [hrk, Fintype.sum_sum_type, ← hcard]
    simp only [hW, hS, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    ring

theorem two_sum_neg_degree_W : ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K)
    (Ψ : Type) [Fintype Ψ] (j k : ℕ) (A : FlagPair E Ψ j k), A.IsOrthFull →
    -E.normDegree ⊤ - ∑ τ, A.flatDeg τ ≤ 2 * ∑ τ, -E.normDegree (A.W τ).top ∧
      ∀ d : ℤ, d ≠ 0 → (∀ x : E.carrier, d • x ∈ ⨆ a, A.part a) →
        2 * ∑ τ, -E.normDegree (A.W τ).top ≤
          -E.normDegree ⊤ - ∑ τ, A.flatDeg τ +
            Module.finrank (𝓞 K) E.carrier * Real.log |(d : ℝ)| := by
  intro K _ _ E Ψ _ j k A h
  obtain ⟨hdeg, hrk⟩ := iSup_part_degree_rank A h
  obtain ⟨hle, hge⟩ := GlobalTheory.T.normalized_degree_full_rank_sublattice K E (⨆ a, A.part a) hrk
  have hflat : ∑ τ, A.flatDeg τ =
      ∑ τ, E.normDegree (A.W τ).top - ∑ τ, E.normDegree (A.S τ).top := by
    simp only [GlobalTheory.CompanionTheory.Ar.FlagPair.flatDeg, Finset.sum_sub_distrib]
  rw [hdeg] at hle
  refine ⟨?_, ?_⟩
  · rw [hflat, Finset.sum_neg_distrib]
    linarith
  · intro d hd hsub
    have hb := hge d hd hsub
    rw [hdeg] at hb
    rw [hflat, Finset.sum_neg_distrib]
    linarith

end GlobalTheory.CompanionTheory.Ar.FlagPair
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.PMatStepColsEntry
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.PFl.SmallStep

theorem stepCols_subset_of_le {N j : ℕ} (hj : j ≤ N) {m i b x : Fin N} (hmi : m ≤ i)
    (hb : b ∈ stepCols N j m) (hb' : b ∈ stepCols N j i) (hx : x ∈ stepCols N j m) : x ∈ stepCols N j i := by
  have h1 := m.2
  have h2 := i.2
  have h3 := b.2
  have h4 := x.2
  have h5 : (m : ℕ) ≤ i := hmi
  simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at hb hb' hx ⊢
  split_ifs at hb hb' hx ⊢ <;> omega

theorem pStep_reads (Ψ : Type) (N j : ℕ) (keep : Ψ × Fin N → Prop) (q : PIdx j keep) (hj : j ≤ N) :
    keep (q.1.1.1, pStep j keep q.1.1.1 q.1.1.2.2) ∧ IsProperStep N j (pStep j keep q.1.1.1 q.1.1.2.2) ∧
      q.1.1.2.2 ∈ stepCols N j (pStep j keep q.1.1.1 q.1.1.2.2) ∧
      q.1.1.2.1 ∉ stepCols N j (pStep j keep q.1.1.1 q.1.1.2.2) ∧
      ∀ c : PIdx j keep → ℂ, pMat keep c q.1.1.1 q.1.1.2.1 q.1.1.2.2 = c q ∧
        ∀ x ∈ stepCols N j (pStep j keep q.1.1.1 q.1.1.2.2), x ≠ q.1.1.2.2 →
          pMat keep c q.1.1.1 x q.1.1.2.2 = 0 := by
  obtain ⟨⟨⟨τ, a, b⟩, hlt, hblk⟩, hsep⟩ := q
  obtain ⟨i, hk, hp, hb, ha⟩ := id hsep
  dsimp only at hk hp hb ha hlt hblk ⊢
  have hne : (pSteps j keep τ b).Nonempty :=
    ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk, hp, hb⟩⟩
  have hm : pStep j keep τ b ∈ pSteps j keep τ b := by
    unfold pStep
    rw [dif_pos hne]
    exact Finset.min'_mem _ _
  have hmin : ∀ i' ∈ pSteps j keep τ b, pStep j keep τ b ≤ i' := by
    intro i' hi'
    unfold pStep
    rw [dif_pos hne]
    exact Finset.min'_le _ _ hi'
  obtain ⟨hmk, hmp, hmb⟩ := (Finset.mem_filter.mp hm).2
  refine ⟨hmk, hmp, hmb, fun hx => ha (stepCols_subset_of_le hj (hmin i ?_) hmb hb hx), fun c => ⟨?_, ?_⟩⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk, hp, hb⟩
  · unfold pMat lowMat
    rw [dif_pos (⟨hlt, hblk⟩ : b < a ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j))]
    unfold cExt
    rw [dif_pos hsep]
  · intro x hx hxb
    unfold pMat lowMat
    by_cases hc : b < x ∧ ((x : ℕ) < N - j ↔ (b : ℕ) < N - j)
    · rw [dif_pos hc]
      unfold cExt
      refine dif_neg ?_
      rintro ⟨i', hk', hp', hb', hx'⟩
      exact hx' (stepCols_subset_of_le hj
        (hmin i' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk', hp', hb'⟩)) hmb hb' hx)
    · rw [dif_neg hc, if_neg hxb]

end GlobalTheory.CompanionTheory.Ar.PB.PFl.SmallStep
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularFunctionAnalyticOnChart
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem analyticAt_valAt_lift_family : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (x : (Σ k, ι k) → Ω) (s : Ω) (e n : ℕ) (Rb : AnLogRes (mCoordIdeal x) ⊤ n) (Un : Set (Fin e → ℂ)) (bp : (Fin e → ℂ) → Rb.X) (w₀ : Fin e → ℂ), IsOpen Un → w₀ ∈ Un → ContinuousOn bp Un → (∀ k, AnalyticOnNhd ℂ (Rb.A.chart k ∘ bp) (Un ∩ bp ⁻¹' (Rb.A.chart k).source)) → RegAt x (mCoordIdeal (Rb.lift (bp w₀) (bp w₀))) s → AnalyticAt ℂ (fun w => valAt x s (Rb.lift (bp w) (bp w))) w₀ := by
  intro K _ ι _ Ω _ x s e n Rb Un bp w₀ hUn hw₀ hbp hchart hreg
  obtain ⟨W', hW'o, hx₀W', hW'U, hW'holo⟩ :=
    GlobalTheory.CompanionTheory.Ar.PB.StepW.ValHolo.holoOn_valAt K ι Ω x s n Rb.X Rb.A (Rb.U (bp w₀))
      (Rb.lift (bp w₀)) (bp w₀) (Rb.isOpen_U _) (Rb.mem_U _) (fun q => Rb.holo _ q)
      (fun y hy => Rb.mem _ y hy) hreg
  obtain ⟨j, hj⟩ := Rb.A.cover (bp w₀)
  have hg : AnalyticAt ℂ ((fun y => GroundTheory.Heights₂.Heights.LowerBoundFree.valAt x s (Rb.lift (bp w₀) y)) ∘ (Rb.A.chart j).symm) ((Rb.A.chart j) (bp w₀)) := by
    apply hW'holo j
    refine ⟨(Rb.A.chart j).map_source hj, ?_⟩
    show (Rb.A.chart j).symm ((Rb.A.chart j) (bp w₀)) ∈ W'
    rw [(Rb.A.chart j).left_inv hj]
    exact hx₀W'
  have hf : AnalyticAt ℂ ((Rb.A.chart j) ∘ bp) w₀ := hchart j w₀ ⟨hw₀, hj⟩
  have hcomp : AnalyticAt ℂ (((fun y => GroundTheory.Heights₂.Heights.LowerBoundFree.valAt x s (Rb.lift (bp w₀) y)) ∘ (Rb.A.chart j).symm) ∘ ((Rb.A.chart j) ∘ bp)) w₀ :=
    AnalyticAt.comp_of_eq (g := (fun y => GroundTheory.Heights₂.Heights.LowerBoundFree.valAt x s (Rb.lift (bp w₀) y)) ∘ (Rb.A.chart j).symm) (f := (Rb.A.chart j) ∘ bp) hg hf rfl
  refine hcomp.congr ?_
  have hcont : ContinuousAt bp w₀ := hbp.continuousAt (hUn.mem_nhds hw₀)
  have hnhds : bp ⁻¹' ((Rb.A.chart j).source ∩ W') ∈ 𝓝 w₀ :=
    hcont.preimage_mem_nhds (((Rb.A.chart j).open_source.inter hW'o).mem_nhds ⟨hj, hx₀W'⟩)
  filter_upwards [hnhds] with w hw
  obtain ⟨hws, hwW⟩ := hw
  show GroundTheory.Heights₂.Heights.LowerBoundFree.valAt x s (Rb.lift (bp w₀) ((Rb.A.chart j).symm ((Rb.A.chart j) (bp w)))) = GroundTheory.Heights₂.Heights.LowerBoundFree.valAt x s (Rb.lift (bp w) (bp w))
  rw [(Rb.A.chart j).left_inv hws]
  exact (GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.valAt_eq_of_sameOrbit K ι Ω x s _ _ (Rb.mem _ _ (Rb.mem_U _))
    (Rb.compat (bp w) (bp w₀) (bp w) ⟨Rb.mem_U _, hW'U hwW⟩)).symm

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SncAdaptedAtlasProjectionStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.snc_adapted_atlas_projection : ∀ (e n : ℕ) (X Z : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] [TopologicalSpace Z] [CompactSpace Z] [T2Space Z] (A : FinHolAtlas e X) (Ab Bb : FinHolAtlas n Z) (pr : X → Z) (hp : HoloMap A Ab pr) (L : LocPot Z) (s : Z → Z → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set Z), IsPotential Ab L → IsSection Ab L s → IsSNC Ab L s m W → (∀ x, logNormSec L s x ≤ 0) → (∀ x, ∃ (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (kb : Fin Ab.n) (σ : Fin n ↪ Fin e), IsCompatChart A ψ ∧ x ∈ ψ.source ∧ (∀ x' ∈ ψ.source, pr x' ∈ (Ab.chart kb).source ∧ ∀ i, Ab.chart kb (pr x') i = ψ x' (σ i))) → IsPotential A (L.pullback pr hp.1) ∧ IsSection A (L.pullback pr hp.1) (fun x y => s (pr x) (pr y)) ∧ IsSNC A (L.pullback pr hp.1) (fun x y => s (pr x) (pr y)) m (fun k => pr ⁻¹' W k) ∧ ∃ B : FinHolAtlas e X, IsAdaptedAtlas A B (L.pullback pr hp.1) (fun x y => s (pr x) (pr y)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.SncPull.pullback_projection | exact GlobalTheory.CompanionTheory.Ar.PB.SncPull.pullback_projection | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.SncPull.pullback_projection <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.StepFactorNeZeroStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.step_factor_ne_zero : ∀ (N j : ℕ) (a i : Fin N) (h : Matrix (Fin N) (Fin N) ℂ), IsBlockDiag j h → h.det ≠ 0 → facOf N j a h i ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.facOf_ne_zero | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.facOf_ne_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.facOf_ne_zero <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.StepRowsInverseNonzeroEntryStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.step_rows_inverse_nonzero_entry : ∀ (L : Type) [Field L] (V : ValuationSubring L) (N j : ℕ) (i : Fin N) (H : Matrix (Fin N) (Fin N) L) (κ : Type) [Fintype κ] (u : κ → Finset (Fin N) → L) (u' : Finset (Fin N) → κ → L), j ≤ N → IsBlockDiag j H → (∀ a b, H a b ∈ V) → H.det ≠ 0 → (H.det)⁻¹ ∈ V → (∀ I m, u' I m ∈ V) → (∀ m I, u m I ∈ V) → (∀ I I', IsStepRows N j i I → IsStepRows N j i I' → ∑ m, u' I m * u m I' = if I = I' then 1 else 0) → ∃ m, (∑ I, u m I * minorIJ H I (stepCols N j i)) ≠ 0 ∧ (∑ I, u m I * minorIJ H I (stepCols N j i))⁻¹ ∈ V := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.UnitComb.unit_comb | exact GlobalTheory.CompanionTheory.Ar.PB.UnitComb.unit_comb | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.UnitComb.unit_comb <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoByTwoMinorGramIdentityStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_by_two_minor_gram_identity : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (τ : Ψ) (a b ca cb : Fin N) (Gf hf : Ψ → Matrix (Fin N) (Fin N) ℂ) (u : Ψ × Fin N → ℝ) (t : ℂ) (G₂ : Matrix (Fin 2) (Fin 2) ℂ), j ≤ N → (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsBlockDiag j (Gf τ) → (Gf τ).PosDef → IsBlockDiag j (hf τ) → (hf τ).det ≠ 0 → (∀ r s : Fin 2, G₂ r s = minorIJ ((hf τ)ᴴ * Gf τ * hf τ) (insert (![ca, cb] r) ((stepCols N j a).erase ca)) (insert (![ca, cb] s) ((stepCols N j a).erase ca)) / minorIJ ((hf τ)ᴴ * Gf τ * hf τ) ((stepCols N j a).erase ca) ((stepCols N j a).erase ca)) → ∑ p, (xiCoef τ a p : ℝ) * (blockPot j p.2 (Gf p.1) (if p.1 = τ then hf τ * (1 + Matrix.single cb ca t) else hf p.1) - u p) = xiPot G₂ t - ∑ i : Fin N, (xiCoef τ a (τ, i) : ℝ) * ((if IsProperStep N j i then 0 else Real.log ‖facOf N j a (hf τ) i‖) + u (τ, i)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.xi_sum_potentials | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.xi_sum_potentials | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.xi_sum_potentials <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoPointFibreChartSecondStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_point_fibre_chart_second : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (X : Type) (q : Fin 2 → X → FA.S.X) (Un : Set (Fin d → ℂ)) (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → X) (l : Fin BM.q) (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X), IsOpen Un → IsFibreData FA τ a ca cb q Un Gn ΦYn ΦWn l H bp → ∀ w ∈ Un, (Gn w).PosDef := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.gramPlane_posDef | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.gramPlane_posDef | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.gramPlane_posDef <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.UnipotentValueNeZero
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.UpsNe

theorem upsVal_ne_zero : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n)  (l : Fin BM.q) (p : Ψ × Fin N) (b : BM.Rb.X), b ∈ BM.O l → M.blk p = none → upsVal BM l p b ≠ 0 := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM l p b hb hp
  obtain ⟨hne, hreg, hreg'⟩ := (BM.good l b hb).2.2 p hp
  exact ValNe.valAt_ne_zero_of_regAt_inv _ _ M.Ω M.x _ _ (BM.Rb.mem b b (BM.Rb.mem_U b)) hne hreg hreg'

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.UpsNe
end

