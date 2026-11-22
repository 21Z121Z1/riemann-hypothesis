import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PlueckerCoordinates.IsHodgeFibrePt
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PlueckerCoordinates.MuLine
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsHodgeFlag
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PlueckerCoordinates.FlagLine
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.IsFrameOverLine
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0017
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.StatementsVerticalGeneric

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.EventuallyInFrameDomain
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ}

namespace HermMetricEq

theorem isValueAt_iff {s : Ω} {v : ℂ} :
    IsValueAt y s z v ↔ IndefiniteRowSideFullHecke.LowerBoundFree.IsValueAt y s z v := by
  constructor
  · rintro ⟨d, g, h, hg, hh, hy, hyg, hz, hv⟩
    exact ⟨d, g, h, hg, hh, hy, hyg, hz, by rw [hv, div_mul_cancel₀ _ hz]⟩
  · rintro ⟨d, g, h, hg, hh, hy, hyg, hz, hv⟩
    exact ⟨d, g, h, hg, hh, hy, hyg, hz, by rw [hv, mul_div_cancel_right₀ _ hz]⟩

theorem regularAt_inv {f : Ω} (hf0 : f ≠ 0) (hf : IsUnitAt y f z) :
    IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y f⁻¹ z := by
  obtain ⟨v, ⟨d, g, h, hg, hh, hy, hyg, hz, hv⟩, hv0⟩ := hf
  have hgz : eval z (map (Int.castRingHom ℂ) g) ≠ 0 := by
    intro h0
    rw [h0, zero_div] at hv
    exact hv0 hv
  have hgy : aeval y g ≠ 0 := by
    rw [hyg]
    exact mul_ne_zero hf0 hy
  refine ⟨v⁻¹, d, h, g, hh, hg, hgy, ?_, hgz, ?_⟩
  · rw [hyg, inv_mul_cancel_left₀ hf0]
  · rw [hv, inv_div, div_mul_cancel₀ _ hgz]

theorem regularAt_pow {a : Ω} (ha : IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y a z) (n : ℕ) :
    IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y (a ^ n) z := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact ⟨1, IndefiniteRowSideFullHecke.LowerBoundFree.isValueAt_one⟩
  | succ n ih =>
    rw [pow_succ]
    exact ih.mul ha

theorem segreCoord_ne_zero (hz : z ∈ mcPts (mCoordIdeal y)) {c : (k : K) → ι k}
    (hc : ∀ k, z ⟨k, c k⟩ ≠ 0) : segreCoord y c ≠ 0 := by
  intro h0
  have hm := IndefiniteRowSideFullHecke.LowerBoundFree.mem_mCoordIdeal_of_aeval (y := y)
    (IndefiniteRowSideFullHecke.LowerBoundFree.isMultiHomog_chartMonomial c) (by simpa [segreCoord] using h0)
  have := hz.2 _ hm
  simp only [map_prod, map_X, eval_X] at this
  exact Finset.prod_ne_zero_iff.2 (fun k _ => hc k) this

variable {E : Type} [AddCommGroup E] [Module Ω E] {N : ℕ}

theorem isFrameAt_of_isFrameOver {W : ChartBundle ℤ (segreCoord y) N E} {c : (k : K) → ι k} {f : Ω}
    {b : Fin N → E} (hb : IsFrameOver y W c f b) (hz : z ∈ mcPts (mCoordIdeal y))
    (hd : InFrameDomain y c f z) : IndefiniteRowSideFullHecke.LowerBoundFree.IsFrameAt y W z b := by
  obtain ⟨hx, -, hf0, -, hiff⟩ := hb
  have hfi : IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y f⁻¹ z := regularAt_inv hf0 hd.2
  have hloc : ∀ a : Ω, (∃ n : ℕ, f ^ n * a ∈ chartRing ℤ (segreCoord y) c) →
      IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y a z := by
    rintro a ⟨n, hn⟩
    have h1 := (regularAt_pow hfi n).mul (IndefiniteRowSideFullHecke.LowerBoundFree.regularAt_of_mem_chartRing hz hd.1 hn)
    rwa [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hf0, one_pow, one_mul] at h1
  have hsec : ∀ c' : (k : K) → ι k, (∀ k, z ⟨k, c' k⟩ ≠ 0) → ∀ s ∈ W.lat c',
      ∃ a : Fin N → Ω, (∀ q, IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y (a q) z) ∧ s = ∑ q, a q • b q := by
    intro c' hc' s hs
    have hx' := segreCoord_ne_zero hz hc'
    obtain ⟨m, hm⟩ := W.overlap c' c hx' hx s hs
    obtain ⟨a, ha, hae⟩ := (hiff _).1 ⟨0, by rwa [pow_zero, one_smul]⟩
    have hr : IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y ((segreCoord y c / segreCoord y c') ^ m) z :=
      regularAt_pow (IndefiniteRowSideFullHecke.LowerBoundFree.regularAt_of_mem_chartRing hz hc'
        (Algebra.subset_adjoin ⟨c, rfl⟩)) m
    refine ⟨fun q => (segreCoord y c / segreCoord y c') ^ m * a q,
      fun q => hr.mul (hloc _ (ha q)), ?_⟩
    have hone : (segreCoord y c / segreCoord y c') ^ m * (segreCoord y c' / segreCoord y c) ^ m = 1 := by
      rw [← mul_pow, div_mul_div_comm, mul_comm (segreCoord y c) (segreCoord y c'),
        div_self (mul_ne_zero hx' hx), one_pow]
    calc s = ((segreCoord y c / segreCoord y c') ^ m * (segreCoord y c' / segreCoord y c) ^ m) • s := by
          rw [hone, one_smul]
      _ = (segreCoord y c / segreCoord y c') ^ m • ∑ q, a q • b q := by rw [mul_smul, hae]
      _ = ∑ q, ((segreCoord y c / segreCoord y c') ^ m * a q) • b q := by
          rw [Finset.smul_sum]
          simp only [mul_smul]
  refine ⟨fun q => ?_, fun e he => ?_⟩
  · have hex : ∃ n : ℕ, f ^ n • b q ∈ W.lat c := by
      refine (hiff (b q)).2 ⟨Pi.single q 1, fun q' => ⟨0, ?_⟩, ?_⟩
      · rw [pow_zero, one_mul]
        rcases eq_or_ne q' q with rfl | h
        · rw [Pi.single_eq_same]
          exact one_mem _
        · rw [Pi.single_eq_of_ne h]
          exact zero_mem _
      · simp [Pi.single_apply, ite_smul]
    obtain ⟨n, hn⟩ := hex
    refine ⟨c, hd.1, 1, fun _ => (f ^ n)⁻¹, fun _ => f ^ n • b q, fun _ => hn, fun _ => ?_, ?_⟩
    · rw [← inv_pow]
      exact regularAt_pow hfi n
    · rw [Fin.sum_univ_one]
      exact (inv_smul_smul₀ (pow_ne_zero _ hf0) _).symm
  · obtain ⟨c', hc', m, a, s, hs, ha, rfl⟩ := he
    choose α hα hαe using fun l => hsec c' hc' (s l) (hs l)
    refine ⟨fun q => ∑ l, a l * α l q,
      fun q => IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt.sum _ fun l _ => (ha l).mul (hα l q), ?_⟩
    simp only [Finset.sum_smul, mul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hαe l, Finset.smul_sum]

theorem coeff_unique {b : Fin N → E} (hli : LinearIndependent Ω b) {S S' : Matrix (Fin N) (Fin N) Ω}
    (h : ∀ q, ∑ p, S p q • b p = ∑ p, S' p q • b p) : S = S' := by
  ext p q
  exact Fintype.linearIndependent_iffₛ.1 hli (fun p => S p q) (fun p => S' p q) (h q) p

theorem exists_coeff {W : ChartBundle ℤ (segreCoord y) N E} {c : (k : K) → ι k} {f : Ω}
    {b : Fin N → E} (hb : IsFrameOver y W c f b) (hz : z ∈ mcPts (mCoordIdeal y))
    (hd : InFrameDomain y c f z) {b' : Fin N → E}
    (hb' : ∀ q, IndefiniteRowSideFullHecke.LowerBoundFree.IsLocSection y W z (b' q)) :
    ∃ S : Matrix (Fin N) (Fin N) Ω, (∀ p q, IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y (S p q) z) ∧
      ∀ q, b' q = ∑ p, S p q • b p := by
  choose a ha hae using fun q => (isFrameAt_of_isFrameOver hb hz hd).2 _ (hb' q)
  exact ⟨Matrix.of fun p q => a q p, fun p q => ha q p, fun q => hae q⟩

def valM (y : (Σ k, ι k) → Ω) (S : Matrix (Fin N) (Fin N) Ω) (z : (Σ k, ι k) → ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun p q => IndefiniteRowSideFullHecke.LowerBoundFree.valAt y (S p q) z

theorem isValueAt_mul {S T : Matrix (Fin N) (Fin N) Ω} {Sz Tz : Matrix (Fin N) (Fin N) ℂ}
    (hS : ∀ p q, IndefiniteRowSideFullHecke.LowerBoundFree.IsValueAt y (S p q) z (Sz p q))
    (hT : ∀ p q, IndefiniteRowSideFullHecke.LowerBoundFree.IsValueAt y (T p q) z (Tz p q)) (p q : Fin N) :
    IndefiniteRowSideFullHecke.LowerBoundFree.IsValueAt y ((S * T) p q) z ((Sz * Tz) p q) := by
  simp only [Matrix.mul_apply]
  exact IndefiniteRowSideFullHecke.LowerBoundFree.IsValueAt.sum _ fun r _ => (hS p r).mul (hT r q)

theorem isValueAt_one_matrix (p q : Fin N) :
    IndefiniteRowSideFullHecke.LowerBoundFree.IsValueAt y ((1 : Matrix (Fin N) (Fin N) Ω) p q) z
      ((1 : Matrix (Fin N) (Fin N) ℂ) p q) := by
  rcases eq_or_ne p q with rfl | h
  · simpa using IndefiniteRowSideFullHecke.LowerBoundFree.isValueAt_one (y := y) (z := z)
  · simpa [Matrix.one_apply_ne h] using IndefiniteRowSideFullHecke.LowerBoundFree.isValueAt_zero (y := y) (z := z)

theorem valM_eq (hz : z ∈ mcPts (mCoordIdeal y)) {S : Matrix (Fin N) (Fin N) Ω}
    {Sz : Matrix (Fin N) (Fin N) ℂ} (hS : ∀ p q, IndefiniteRowSideFullHecke.LowerBoundFree.IsValueAt y (S p q) z (Sz p q)) :
    valM y S z = Sz := by
  ext p q
  exact IndefiniteRowSideFullHecke.LowerBoundFree.valAt_eq hz (hS p q)

theorem regularAt_smul {a : Ω} (s : K → ℂ) (hs : ∀ k, s k ≠ 0)
    (ha : IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y a z) :
    IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y a (fun p => s p.1 * z p) :=
  ⟨_, ha.choose_spec.smul s hs⟩

theorem regularAt_conj {a : Ω} (ha : IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y a z) :
    IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y a (fun p => starRingEnd ℂ (z p)) :=
  ⟨_, ha.choose_spec.conj⟩

theorem isLocSection_smul {W : ChartBundle ℤ (segreCoord y) N E} {e : E} (s : K → ℂ)
    (hs : ∀ k, s k ≠ 0) {z' : (Σ k, ι k) → ℂ} (hz' : z' = fun p => s p.1 * z p)
    (he : IndefiniteRowSideFullHecke.LowerBoundFree.IsLocSection y W z e) : IndefiniteRowSideFullHecke.LowerBoundFree.IsLocSection y W z' e := by
  subst hz'
  obtain ⟨c, hc, m, a, t, ht, ha, rfl⟩ := he
  exact ⟨c, fun k => mul_ne_zero (hs k) (hc k), m, a, t, ht, fun l => regularAt_smul s hs (ha l), rfl⟩

theorem isLocSection_conj {W : ChartBundle ℤ (segreCoord y) N E} {e : E}
    (he : IndefiniteRowSideFullHecke.LowerBoundFree.IsLocSection y W z e) :
    IndefiniteRowSideFullHecke.LowerBoundFree.IsLocSection y W (fun p => starRingEnd ℂ (z p)) e := by
  obtain ⟨c, hc, m, a, t, ht, ha, rfl⟩ := he
  exact ⟨c, fun k => (map_ne_zero _).2 (hc k), m, a, t, ht, fun l => regularAt_conj (ha l), rfl⟩

theorem isFrameAt_smul {W : ChartBundle ℤ (segreCoord y) N E} {b : Fin N → E} (s : K → ℂ)
    (hs : ∀ k, s k ≠ 0) (hb : IndefiniteRowSideFullHecke.LowerBoundFree.IsFrameAt y W z b) :
    IndefiniteRowSideFullHecke.LowerBoundFree.IsFrameAt y W (fun p => s p.1 * z p) b := by
  refine ⟨fun q => isLocSection_smul s hs rfl (hb.1 q), fun e he => ?_⟩
  have he' : IndefiniteRowSideFullHecke.LowerBoundFree.IsLocSection y W z e :=
    isLocSection_smul (fun k => (s k)⁻¹) (fun k => inv_ne_zero (hs k))
      (funext fun p => (inv_mul_cancel_left₀ (hs p.1) (z p)).symm) he
  obtain ⟨a, ha, hae⟩ := hb.2 e he'
  exact ⟨a, fun q => regularAt_smul s hs (ha q), hae⟩

theorem isFrameAt_conj {W : ChartBundle ℤ (segreCoord y) N E} {b : Fin N → E}
    (hb : IndefiniteRowSideFullHecke.LowerBoundFree.IsFrameAt y W z b) :
    IndefiniteRowSideFullHecke.LowerBoundFree.IsFrameAt y W (fun p => starRingEnd ℂ (z p)) b := by
  refine ⟨fun q => isLocSection_conj (hb.1 q), fun e he => ?_⟩
  have he' : IndefiniteRowSideFullHecke.LowerBoundFree.IsLocSection y W z e := by
    have h := isLocSection_conj he
    simp only [RCLike.conj_conj] at h
    exact h
  obtain ⟨a, ha, hae⟩ := hb.2 e he'
  exact ⟨a, fun q => regularAt_conj (ha q), hae⟩

theorem inFrameDomain_smul {c : (k : K) → ι k} {f : Ω} (s : K → ℂ) (hs : ∀ k, s k ≠ 0)
    (hd : InFrameDomain y c f z) : InFrameDomain y c f (fun p => s p.1 * z p) := by
  obtain ⟨hc, v, hv, hv0⟩ := hd
  exact ⟨fun k => mul_ne_zero (hs k) (hc k), v, isValueAt_iff.2 ((isValueAt_iff.1 hv).smul s hs), hv0⟩

theorem inFrameDomain_conj {c : (k : K) → ι k} {f : Ω} (hd : InFrameDomain y c f z) :
    InFrameDomain y c f (fun p => starRingEnd ℂ (z p)) := by
  obtain ⟨hc, v, hv, hv0⟩ := hd
  exact ⟨fun k => (map_ne_zero _).2 (hc k), starRingEnd ℂ v, isValueAt_iff.2 (isValueAt_iff.1 hv).conj,
    (map_ne_zero _).2 hv0⟩

theorem eventually_regularAt {m : ℕ} {γ : (Fin m → ℂ) → (Σ k, ι k) → ℂ} {w : Fin m → ℂ}
    (hγ : ContinuousAt γ w) {a : Ω} (ha : IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y a (γ w)) :
    ∀ᶠ w' in 𝓝 w, IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y a (γ w') := by
  obtain ⟨v, d, g, h, hg, hh, hy, hyg, hz, -⟩ := ha
  have hc : ContinuousAt (fun w' => eval (γ w') (map (Int.castRingHom ℂ) h)) w :=
    (MvPolynomial.continuous_eval (map (Int.castRingHom ℂ) h)).continuousAt.comp hγ
  filter_upwards [hc.eventually_ne hz] with w' hw'
  exact ⟨_, d, g, h, hg, hh, hy, hyg, hw', (div_mul_cancel₀ _ hw').symm⟩

theorem eventually_inFrameDomain {m : ℕ} {γ : (Fin m → ℂ) → (Σ k, ι k) → ℂ} {w : Fin m → ℂ}
    (hγ : ContinuousAt γ w) {c : (k : K) → ι k} {f : Ω} (hd : InFrameDomain y c f (γ w)) :
    ∀ᶠ w' in 𝓝 w, InFrameDomain y c f (γ w') := by
  obtain ⟨hc, v, ⟨d, g, h, hg, hh, hy, hyg, hz, hv⟩, hv0⟩ := hd
  have hgz : eval (γ w) (map (Int.castRingHom ℂ) g) ≠ 0 := by
    intro h0
    rw [h0, zero_div] at hv
    exact hv0 hv
  have hG : ContinuousAt (fun w' => eval (γ w') (map (Int.castRingHom ℂ) g)) w :=
    (MvPolynomial.continuous_eval (map (Int.castRingHom ℂ) g)).continuousAt.comp hγ
  have hH : ContinuousAt (fun w' => eval (γ w') (map (Int.castRingHom ℂ) h)) w :=
    (MvPolynomial.continuous_eval (map (Int.castRingHom ℂ) h)).continuousAt.comp hγ
  have hC : ∀ᶠ w' in 𝓝 w, ∀ k, γ w' ⟨k, c k⟩ ≠ 0 := Filter.eventually_all.2 fun k =>
    ((continuous_apply (⟨k, c k⟩ : Σ k, ι k)).continuousAt.comp hγ).eventually_ne (hc k)
  filter_upwards [hG.eventually_ne hgz, hH.eventually_ne hz, hC] with w' hg' hh' hc'
  exact ⟨hc', _, ⟨d, g, h, hg, hh, hy, hyg, hh', rfl⟩, div_ne_zero hg' hh'⟩

end HermMetricEq

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsFlagGrassSteps
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def plToIncr {j m N s : ℕ} (hs : s = j) (hN : j + m = N) (I : PlIdx j m) : PlueckerData.Incr s N :=
  ⟨fun a => Fin.cast hN (I.1.orderEmbOfFin I.2 (Fin.cast hs a)), fun a b hab => by
    rw [Fin.lt_def] at hab ⊢
    simp only [Fin.val_cast]
    exact (I.1.orderEmbOfFin I.2).strictMono (by rw [Fin.lt_def]; simpa using hab)⟩

section Block

variable (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ)

def grFlKappa (hj : 1 ≤ j) (hjN : j ≤ N - 1) : Fin (Fintype.card Ψ) → FlBlock Ψ N :=
  fun t => ((Fintype.equivFin Ψ).symm t, ⟨j - 1, by omega⟩)

def grFlV (hj : 1 ≤ j) (hjN : j ≤ N - 1) :
    (Σ _ : Fin (Fintype.card Ψ), PlIdx j (N - j)) → (Σ q : FlBlock Ψ N, FlIdx Ψ N q) :=
  fun p => ⟨grFlKappa Ψ N j hj hjN p.1, plToIncr (by simp only [grFlKappa]; omega) (by omega) p.2⟩

end Block

section Lines

variable (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ)

def linForm (ℓ : Ψ × Fin N → ℤ) : RootPoly Ψ N := ∑ p, (ℓ p : ℚ) • X p

def linDeg (ℓ : Ψ × Fin N → ℤ) : FlBlock Ψ N → ℤ := fun q => ∑ p, ℓ p * xDeg Ψ N p q

def linLine (ℓ : Ψ × Fin N → ℤ) : HermLine (FlIdx Ψ N) := fsHerm (FlIdx Ψ N) (linDeg Ψ N ℓ)

variable (j : ℕ)

def muForm : Ψ × Fin N → ℤ := fun p => if (p.2 : ℕ) < j then 0 else 1

abbrev VandPair : Type :=
  {t : Ψ × Fin N × Fin N // t.2.1 < t.2.2 ∧ ((t.2.1 : ℕ) < j ↔ (t.2.2 : ℕ) < j)}

def vandForm (t : VandPair Ψ N j) : Ψ × Fin N → ℤ := fun p =>
  (if p = (t.1.1, t.1.2.1) then 1 else 0) - (if p = (t.1.1, t.1.2.2) then 1 else 0)

def vandCount : ℕ := Fintype.card (VandPair Ψ N j)

def vandLine (i : Fin (vandCount Ψ N j)) : HermLine (FlIdx Ψ N) :=
  linLine Ψ N (vandForm Ψ N j ((Fintype.equivFin (VandPair Ψ N j)).symm i))

end Lines

def FlagArithVar.Statement : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] [Nonempty Ψ] (N : ℕ), 2 ≤ N →
    IsArithVar (PFl Ψ N) (dimFl Ψ N + 1)

def FlagImageGrass.Statement : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (hj : 1 ≤ j) (hjN : j ≤ N - 1),
    imageZ (grFlV Ψ N j hj hjN) (PFl Ψ N) = grassIdeal (Fintype.card Ψ) j (N - j)

def VandCount.Statement : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ), j ≤ N → dimN Ψ N j + vandCount Ψ N j = dimFl Ψ N

def HFlProdLinear.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] [Nonempty Ψ] (N d : ℕ) (c : ℚ)
    (ℓ : Fin d → Ψ × Fin N → ℤ),
    IsIntersectionSystem II → 2 ≤ N → d = dimFl Ψ N + 1 →
    hFl Ψ N II (C c * ∏ i, linForm Ψ N (ℓ i)) =
      (c : ℝ) * II (FlBlock Ψ N) (FlIdx Ψ N) (PFl Ψ N) d (fun i => linLine Ψ N (ℓ i))

def FsInvPow.Statement : Prop :=
  ∀ (II : IntersectionSystem) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (d : ℕ), IsIntersectionSystem II → IsArithVar P d →
    II K ι P d (fun _ => fsHerm ι (fun _ => -1)) = (-1) ^ d * II K ι P d (fun _ => GroundTheory.Heights₂.Heights.fsMulti ι)

def FlagGrassFibreDeg.Statement : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] [Nonempty Ψ] (N j : ℕ) (hj : 1 ≤ j) (hjN : j ≤ N - 1),
    ∃ (G : GenFibre (grFlV Ψ N j hj hjN) (PFl Ψ N))
      (J : IFamily G.Φ (fibreIdx (FlIdx Ψ N) (grFlKappa Ψ N j hj hjN))),
      IsFieldIntersection J ∧
        ((J (fibreIdeal (grFlKappa Ψ N j hj hjN) G) (vandCount Ψ N j)
          (fun i => fibreDeg (grFlKappa Ψ N j hj hjN) (vandLine Ψ N j i).a) : ℤ) : ℚ) = fdeg Ψ N j

def GrassDegFlagInt.Statement : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] [Nonempty Ψ] (N j : ℕ), 2 ≤ N → 1 ≤ j → j ≤ N - 1 →
    ((flagInt Ψ N (muPoly Ψ N j ^ dimN Ψ N j * vandBlocks Ψ N j) : ℚ) : ℝ) =
      (-1) ^ dimN Ψ N j * (fdeg Ψ N j : ℝ) *
        geomDeg (grassIdeal (Fintype.card Ψ) j (N - j))
          (GroundTheory.Heights₂.Heights.fsMulti (plBlocks (Fintype.card Ψ) j (N - j))) (dimN Ψ N j)

example : Nonempty Unit ∧ 2 ≤ 2 ∧ 1 ≤ 1 ∧ 1 ≤ 2 - 1 ∧ vandCount Unit 2 1 = 0 ∧ dimFl Unit 2 + 1 = 2 := by
  refine ⟨⟨()⟩, le_rfl, le_rfl, le_rfl, ?_, rfl⟩
  unfold vandCount
  rw [Fintype.card_eq_zero_iff]
  constructor
  rintro ⟨⟨u, a, b⟩, hab, hh⟩
  fin_cases a <;> fin_cases b <;> simp_all

example : IsArithVar (⊥ : Ideal (MRing (PBlk 2))) 2 := Inter.isArithVar_projLine

example : Nonempty Unit ∧ 2 ≤ 2 ∧ (2 = dimFl Unit 2 + 1) ∧
    linForm Unit 2 (fun p => if p = ((), 1) then 1 else 0) = X ((), 1) := by
  refine ⟨⟨()⟩, le_rfl, rfl, ?_⟩
  unfold linForm
  rw [Fintype.sum_eq_single ((), 1)]
  · simp
  · intro p hp
    simp [hp]

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsHodgeFibrePtNeZero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree

open ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

def HodgeFibrePtNeZero.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentDataHodge II Ψ K ι Ω E) (P : PlueckerData D) (τ : Ψ)
    (z : (Σ k, ι k) → ℂ) (wF : Fin (P.M τ (jIdx D)) → ℂ) (wW : Fin (P.M τ (lastIdx D)) → ℂ),
    z ∈ mcPts (mCoordIdeal D.y) → IsHodgeFibrePt P τ z wF wW → (∃ m, wF m ≠ 0) ∧ ∃ m, wW m ≠ 0

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsHodgeFlagNeZero
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def HodgeFlagNeZero.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (Pl : PlueckerData D) (H : HodgeData D)
    (B : AdaptedBasis H) (τ : Ψ) (i : Fin (D.N - 1)), ∃ m, Pl.pluecker0 B τ i m ≠ 0

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsMuModelLineIso
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree

open ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.HilbertSamuel

def MuModelLineIso.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentDataHodge II Ψ K ι Ω E) (P : PlueckerData D)
    (H : HodgeData D.toComponentData), (∀ τ, H.F τ = D.F τ) →
    genDeg (PXmu P) D.toComponentData.n (muDeg D) =
      genDeg (PXmu P) D.toComponentData.n (Sum.elim H.aMu (0 : Ψ ⊕ Ψ → ℤ))

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPlueckerNeZero
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def PlueckerNeZero.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (Pl : PlueckerData D)
    (τ : Ψ) (i : Fin (D.N - 1)), ∃ m, Pl.pluecker τ i m ≠ 0

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPlueckerRatioTrdeg
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def PlueckerRatioTrdeg.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (Pl : PlueckerData D)
    (c : ∀ k, Pl.ιY k), (∀ k, Pl.yY ⟨k, c k⟩ ≠ 0) →
    Algebra.trdeg ℤ (Subfield.closure (coneRatios Pl.yY c)) = ((D.n + D.flagDim : ℕ) : Cardinal)

theorem PlueckerData.yY_inl {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {K : Type} [Fintype K]
    {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] {D : ComponentData II Ψ K ι Ω E} (Pl : PlueckerData D) (k : K) (t : ι k) :
    Pl.yY ⟨Sum.inl k, t⟩ = Pl.ofΩ (D.y ⟨k, t⟩) := rfl

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsVerticalTwistGenDeg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.HilbertSamuel

def VerticalTwistGenDeg.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ) (a : K → ℤ)
    (s : Finset ℕ) (b : ℕ → K → ℤ) (f g : ℕ → MRing ι),
    IsArithVar P (d + 1) → (∀ p ∈ s, p.Prime ∧ IsVerticalDivisorAt P p (b p) (f p) (g p)) →
    genDeg P d (a + ∑ p ∈ s, b p) = genDeg P d a

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

