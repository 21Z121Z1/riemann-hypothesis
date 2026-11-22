import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0100
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0032
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0099
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0028
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0029
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0090
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0096
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVertFactorSmooth
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0029
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0042

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionNumberMetricChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Tele

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem ptsIntegral_congr_on {e : ℕ} (P : Ideal (MRing J)) (φ : Fin e → ((Σ k, J k) → ℂ) → ℝ)
    {g g' : ((Σ k, J k) → ℂ) → ℝ} (h : ∀ z ∈ mcPts P, g z = g' z) :
    ptsIntegral P φ g = ptsIntegral P φ g' := by
  have hs : ∀ (Ψ : (((k : K) → J k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) y w,
      sheetDensity P Ψ φ g y w = sheetDensity P Ψ φ g' y w := by
    intro Ψ y w
    unfold sheetDensity
    by_cases hs : ∃ c, IsSheet P Ψ y w c
    · rw [dif_pos hs, dif_pos hs, h _ hs.choose_spec.2.self_of_nhds.2.1]
    · rw [dif_neg hs, dif_neg hs]
  unfold ptsIntegral ptsIntegralAt
  simp only [hs]

def logDiff (A B : HermLine J) (z : (Σ k, J k) → ℂ) : ℝ := by
  classical
  exact if ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 then Real.log (A.h z) - Real.log (B.h z) else 0

theorem cone_smul_iff (c : K → ℂ) (hc : ∀ k, c k ≠ 0) (z : (Σ k, J k) → ℂ) :
    (∀ k, ∃ i, (fun p : (Σ k, J k) => c p.1 * z p) ⟨k, i⟩ ≠ 0) ↔ ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 := by
  simp only [ne_eq, mul_eq_zero, hc, false_or]

theorem logDiff_smul {A B : HermLine J} (hab : B.a = A.a) (c : K → ℂ) (z : (Σ k, J k) → ℂ)
    (hc : ∀ k, c k ≠ 0) : logDiff A B (fun p => c p.1 * z p) = logDiff A B z := by
  unfold logDiff
  by_cases hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0
  · rw [if_pos hz, if_pos ((cone_smul_iff c hc z).2 hz), A.smul c z hc, B.smul c z hc, hab]
    have hp : (∏ k, ‖c k‖ ^ A.a k) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc k))
    rw [Real.log_mul hp (A.pos z hz).ne', Real.log_mul hp (B.pos z hz).ne']
    ring
  · rw [if_neg hz, if_neg fun h => hz ((cone_smul_iff c hc z).1 h)]

theorem logDiff_smooth {A B : HermLine J} (hA : IsSmoothHerm A) (hB : IsSmoothHerm B) :
    ReciprocityTheory.ChartRestriction.G.AI.I2.SmoothFn (logDiff A B) := by
  have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => Real.log (A.h z) - Real.log (B.h z))
      {z : (Σ k, J k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} :=
    (ContDiffOn.log hA fun z hz => (A.pos z hz).ne').sub
      (ContDiffOn.log hB fun z hz => (B.pos z hz).ne')
  refine h1.congr fun z hz => ?_
  unfold logDiff
  exact if_pos hz

theorem step (hLoc : ReciprocityTheory.ChartRestriction.G.AI.I2.MetricLocalStatement)
    (I : Ideal (MRing J) → (n : ℕ) → (Fin n → HermLine J) → ℝ) (hI : IsIntersectionFamily I)
    (P : Ideal (MRing J)) (n : ℕ) (L : Fin n → HermLine J) (A B : HermLine J)
    (hP : IsArithVar P (n + 1)) (hL : ∀ j, IsSmoothHerm (L j)) (hA : IsSmoothHerm A)
    (hB : IsSmoothHerm B) (hab : B.a = A.a) :
    I P (n + 1) (Fin.snoc L B) = I P (n + 1) (Fin.snoc L A) -
      ptsIntegral P (pot L) (fun z => Real.log (A.h z) - Real.log (B.h z)) := by
  have hu := fun (c : K → ℂ) z (hc : ∀ k, c k ≠ 0) => logDiff_smul (A := A) (B := B) hab c z hc
  have hus := logDiff_smooth hA hB
  have hch := metricChange K J I hI P n L A (logDiff A B) hu hP hL hA hus
  set T := A.tensor (HermLine.ofWeight (logDiff A B) hu) with hT
  have hTh : ∀ z, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → T.h z = B.h z := by
    intro z hz
    have e : T.h z = A.h z * Real.exp (-logDiff A B z) := rfl
    rw [e]
    unfold logDiff
    rw [if_pos hz, neg_sub, Real.exp_sub, Real.exp_log (B.pos z hz), Real.exp_log (A.pos z hz)]
    have := (A.pos z hz).ne'
    field_simp
  have hTs : IsSmoothHerm T := by
    unfold IsSmoothHerm
    exact (ContDiffOn.congr hB fun z hz => hTh z hz)
  have hTa : T.a = B.a := by
    rw [hab]
    show A.a + 0 = A.a
    simp
  have hSn : ∀ X : HermLine J, IsSmoothHerm X → ∀ j, IsSmoothHerm ((Fin.snoc L X : Fin (n + 1) → HermLine J) j) := by
    intro X hX j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa using hX
    · simpa using hL j
  have hloc : I P (n + 1) (Fin.snoc L T) = I P (n + 1) (Fin.snoc L B) := by
    refine hLoc K J I hI P (n + 1) _ _ hP (hSn T hTs) (hSn B hB) (fun j => ?_) (fun j z hz => ?_)
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa using hTa
      · simp
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa using hTh z hz.1
      · simp
  rw [← hloc, hch]
  congr 1
  refine ptsIntegral_congr_on P _ fun z hz => ?_
  unfold logDiff
  rw [if_pos hz.1]

def toLast {n : ℕ} (p : Fin (n + 1)) : Equiv.Perm (Fin (n + 1)) :=
  (finSuccEquiv' p).trans finSuccEquivLast.symm

theorem toLast_self {n : ℕ} (p : Fin (n + 1)) : toLast p p = Fin.last n := by
  simp [toLast]

theorem toLast_succAbove {n : ℕ} (p : Fin (n + 1)) (j : Fin n) :
    toLast p (p.succAbove j) = j.castSucc := by
  simp [toLast]

def word (A B : HermLine J) (m i : ℕ) : Fin m → HermLine J := fun j => if (j : ℕ) < i then B else A

theorem word_snoc (A B X : HermLine J) (n : ℕ) (p : Fin (n + 1)) (q : Fin (n + 1)) :
    (Fin.snoc (word A B n p) X : Fin (n + 1) → HermLine J) (toLast p q) =
      if (q : ℕ) < p then B else if q = p then X else A := by
  rcases Fin.eq_self_or_eq_succAbove p q with rfl | ⟨j, rfl⟩
  · simp [toLast_self]
  · rw [toLast_succAbove, Fin.snoc_castSucc]
    have hne := Fin.succAbove_ne p j
    rw [if_neg hne]
    unfold word
    by_cases h : (j : ℕ) < p
    · have : p.succAbove j = j.castSucc := Fin.succAbove_of_castSucc_lt _ _ (by simpa [Fin.lt_def] using h)
      simp [this, h]
    · have : p.succAbove j = j.succ := Fin.succAbove_of_le_castSucc _ _ (by simpa [Fin.le_def] using h)
      have h' : ¬ ((j : ℕ) + 1 < p) := by omega
      simp [this, h, h']

theorem smooth_snoc {n : ℕ} {L : Fin n → HermLine J} {X : HermLine J} (hL : ∀ j, IsSmoothHerm (L j))
    (hX : IsSmoothHerm X) (j : Fin (n + 1)) :
    IsSmoothHerm ((Fin.snoc L X : Fin (n + 1) → HermLine J) j) := by
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simpa using hX
  · simpa using hL j

theorem word_smooth {A B : HermLine J} (hA : IsSmoothHerm A) (hB : IsSmoothHerm B) (m i : ℕ)
    (j : Fin m) : IsSmoothHerm (word A B m i j) := by
  unfold word
  split_ifs
  · exact hB
  · exact hA

theorem word_step (hLoc : ReciprocityTheory.ChartRestriction.G.AI.I2.MetricLocalStatement)
    (I : Ideal (MRing J) → (n : ℕ) → (Fin n → HermLine J) → ℝ) (hI : IsIntersectionFamily I)
    (P : Ideal (MRing J)) (n : ℕ) (A B : HermLine J)
    (hP : IsArithVar P (n + 1)) (hA : IsSmoothHerm A)
    (hB : IsSmoothHerm B) (hab : B.a = A.a) (i : ℕ) (hi : i < n + 1) :
    I P (n + 1) (word A B (n + 1) (i + 1)) = I P (n + 1) (word A B (n + 1) i) -
      ptsIntegral P (pot (word A B n i)) (fun z => Real.log (A.h z) - Real.log (B.h z)) := by
  let p : Fin (n + 1) := ⟨i, hi⟩
  have hL := word_smooth (J := J) hA hB n i
  have sB : word A B (n + 1) (i + 1) = (Fin.snoc (word A B n i) B : Fin (n + 1) → HermLine J) ∘ toLast p := by
    funext q
    have h := word_snoc A B B n p q
    simp only [Function.comp_apply]
    refine Eq.trans ?_ h.symm
    unfold word
    have hq : q = p ↔ (q : ℕ) = i := by simp [p, Fin.ext_iff]
    by_cases h1 : (q : ℕ) < i
    · have h2 : (q : ℕ) < i + 1 := by omega
      simp only [p, h1, h2, if_true]
    · by_cases h3 : (q : ℕ) = i
      · have h2 : (q : ℕ) < i + 1 := by omega
        simp [p, h1, h2, hq.2 h3]
      · have h2 : ¬ (q : ℕ) < i + 1 := by omega
        have h4 : q ≠ p := fun e => h3 (hq.1 e)
        simp [p, h1, h2, h4]
  have sA : word A B (n + 1) i = (Fin.snoc (word A B n i) A : Fin (n + 1) → HermLine J) ∘ toLast p := by
    funext q
    have h := word_snoc A B A n p q
    simp only [Function.comp_apply]
    refine Eq.trans ?_ h.symm
    unfold word
    by_cases h1 : (q : ℕ) < i
    · simp [p, h1]
    · simp [p, h1]
  rw [sB, sA, hI.1 P (n + 1) _ (toLast p) hP (smooth_snoc hL hB),
    hI.1 P (n + 1) _ (toLast p) hP (smooth_snoc hL hA)]
  exact step hLoc I hI P n _ A B hP hL hA hB hab

theorem telescope : ReciprocityTheory.ChartRestriction.G.AI.I2.MetricLocalStatement → ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing J)) (n : ℕ) (A B : HermLine J), IsFullIntersectionSystem II → IsArithVar P (n + 1) → IsSmoothHerm A → IsSmoothHerm B → B.a = A.a → II K J P (n + 1) (fun _ => B) = II K J P (n + 1) (fun _ => A) - ∑ i ∈ Finset.range (n + 1), ptsIntegral P (pot fun j : Fin n => if (j : ℕ) < i then B else A) (fun z => Real.log (A.h z) - Real.log (B.h z)) := by
  intro hLoc K _ J _ II P n A B hII hP hA hB hab
  have hI : IsIntersectionFamily (II K J) := hII.1 K J
  have key : ∀ i, i ≤ n + 1 → II K J P (n + 1) (word A B (n + 1) i) =
      II K J P (n + 1) (word A B (n + 1) 0) - ∑ k ∈ Finset.range i,
        ptsIntegral P (pot (word A B n k)) (fun z => Real.log (A.h z) - Real.log (B.h z)) := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      rw [word_step hLoc _ hI P n A B hP hA hB hab i (by omega), ih (by omega),
        Finset.sum_range_succ]
      ring
  have e1 : word A B (n + 1) (n + 1) = fun _ => B := by
    funext j
    simp [word, j.isLt]
  have e0 : word A B (n + 1) 0 = fun _ => A := by
    funext j
    simp [word]
  have h := key (n + 1) le_rfl
  rw [e1, e0] at h
  exact h

end GlobalTheory.CompanionTheory.Ar.Tele
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionNumberTelescoping
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.Giv.Mix

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Giv.Mix.Tele

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def positionPerm {n : ℕ} (m : Fin (n + 1)) : Equiv.Perm (Fin (n + 1)) :=
  finSuccEquivLast.trans (finSuccEquiv' m).symm

theorem positionPerm_last {n : ℕ} (m : Fin (n + 1)) : positionPerm m (Fin.last n) = m := by
  simp [positionPerm]

theorem positionPerm_castSucc {n : ℕ} (m : Fin (n + 1)) (j : Fin n) :
    positionPerm m (Fin.castSucc j) = m.succAbove j := by
  simp [positionPerm]

def word {n : ℕ} (a a₀ A' : HermLine ι) (k m : ℕ) : Fin (n + 1) → HermLine ι :=
  fun j => if (j : ℕ) < m then a else if (j : ℕ) < k then a₀ else A'

theorem word_comp_low {n : ℕ} (a a₀ A' : HermLine ι) (k m : ℕ) (hm : m < n + 1) (hk : m < k) :
    word (n := n) a a₀ A' k m ∘ positionPerm ⟨m, hm⟩ = Fin.snoc (mixWord (n := n) a a₀ A' k m) a₀ := by
  funext j
  induction j using Fin.lastCases with
  | last => simp [word, positionPerm_last, hk]
  | cast i =>
    simp only [Function.comp_apply, positionPerm_castSucc, Fin.snoc_castSucc, word, mixWord]
    rcases lt_or_ge (i : ℕ) m with h | h
    · rw [Fin.succAbove_of_castSucc_lt ⟨m, hm⟩ i (Fin.lt_def.mpr h)]
      simp [h]
    · rw [Fin.succAbove_of_le_castSucc ⟨m, hm⟩ i (Fin.le_def.mpr h)]
      have h1 : ¬ (i : ℕ) + 1 < m := by omega
      have h2 : ¬ (i : ℕ) < m := by omega
      simp [h1, h2]

theorem word_comp_high {n : ℕ} (a a₀ A' : HermLine ι) (k m : ℕ) (hm : m < n + 1) :
    word (n := n) a a₀ A' k (m + 1) ∘ positionPerm ⟨m, hm⟩ = Fin.snoc (mixWord (n := n) a a₀ A' k m) a := by
  funext j
  induction j using Fin.lastCases with
  | last => simp [word, positionPerm_last]
  | cast i =>
    simp only [Function.comp_apply, positionPerm_castSucc, Fin.snoc_castSucc, word, mixWord]
    rcases lt_or_ge (i : ℕ) m with h | h
    · rw [Fin.succAbove_of_castSucc_lt ⟨m, hm⟩ i (Fin.lt_def.mpr h)]
      have h1 : (i : ℕ) < m + 1 := by omega
      simp [h, h1]
    · rw [Fin.succAbove_of_le_castSucc ⟨m, hm⟩ i (Fin.le_def.mpr h)]
      have h1 : ¬ (i : ℕ) + 1 < m + 1 := by omega
      have h2 : ¬ (i : ℕ) < m := by omega
      simp [h1, h2]

theorem forall_snoc {n : ℕ} {p : HermLine ι → Prop} {L : Fin n → HermLine ι} {x : HermLine ι}
    (hL : ∀ j, p (L j)) (hx : p x) : ∀ j, p ((Fin.snoc L x : Fin (n + 1) → HermLine ι) j) := by
  intro j
  induction j using Fin.lastCases with
  | last => simpa using hx
  | cast i => simpa using hL i

theorem cone_smul (c : K → ℂ) (z : (Σ k, ι k) → ℂ) (hc : ∀ k, c k ≠ 0) :
    (∀ k, ∃ i, (fun p : Σ k, ι k => c p.1 * z p) ⟨k, i⟩ ≠ 0) ↔ ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 := by
  constructor
  · intro h k
    obtain ⟨i, hi⟩ := h k
    exact ⟨i, right_ne_zero_of_mul hi⟩
  · intro h k
    obtain ⟨i, hi⟩ := h k
    exact ⟨i, mul_ne_zero (hc k) hi⟩

theorem logRatio_smul {a a₀ : HermLine ι} (hd : a.a = a₀.a) (c : K → ℂ) (z : (Σ k, ι k) → ℂ)
    (hc : ∀ k, c k ≠ 0) : logRatio a a₀ (fun p => c p.1 * z p) = logRatio a a₀ z := by
  have hcone := cone_smul c z hc
  unfold logRatio
  by_cases h : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0
  · rw [if_pos (hcone.mpr h), if_pos h, a.smul c z hc, a₀.smul c z hc, hd]
    have hprod : (∏ k, ‖c k‖ ^ a₀.a k) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc k))
    rw [Real.log_mul hprod (a₀.pos z h).ne', Real.log_mul hprod (a.pos z h).ne']
    ring
  · rw [if_neg (fun h' => h (hcone.mp h')), if_neg h]

theorem logRatio_smooth {a a₀ : HermLine ι} (ha : IsSmoothHerm a) (ha₀ : IsSmoothHerm a₀) :
    ReciprocityTheory.ChartRestriction.G.AI.I2.SmoothFn (logRatio a a₀) := by
  have h0 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a₀.h {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := ha₀
  have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a.h {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := ha
  show ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (logRatio a a₀) {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}
  refine ((h0.log fun z hz => (a₀.pos z hz).ne').sub (h1.log fun z hz => (a.pos z hz).ne')).congr ?_
  intro z hz
  have hz' : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 := hz
  simp only [logRatio, if_pos hz']

theorem tensor_logRatio_h {a a₀ : HermLine ι}
    (hu : ∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) → logRatio a a₀ (fun p => c p.1 * z p) = logRatio a a₀ z)
    (z : (Σ k, ι k) → ℂ) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    (a₀.tensor (HermLine.ofWeight (logRatio a a₀) hu)).h z = a.h z := by
  have h0 := a₀.pos z hz
  have h1 := a.pos z hz
  show a₀.h z * Real.exp (-logRatio a a₀ z) = a.h z
  rw [logRatio, if_pos hz, neg_sub, Real.exp_sub, Real.exp_log h1, Real.exp_log h0,
    ← mul_div_assoc, mul_div_right_comm, div_self h0.ne', one_mul]

theorem word_step (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ)
    (hI : IsIntersectionFamily I) (P : Ideal (MRing ι)) (n : ℕ) (a a₀ A' : HermLine ι) (k m : ℕ)
    (hP : IsArithVar P (n + 1)) (ha : IsSmoothHerm a) (ha₀ : IsSmoothHerm a₀) (hA' : IsSmoothHerm A')
    (hd : a.a = a₀.a) (hk : k ≤ n + 1) (hm : m < k) :
    I P (n + 1) (word a a₀ A' k (m + 1)) - I P (n + 1) (word a a₀ A' k m) =
      -ptsIntegral P (pot (mixWord (n := n) a a₀ A' k m)) (logRatio a a₀) := by
  have hu : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) →
      logRatio a a₀ (fun p => c p.1 * z p) = logRatio a a₀ z := fun c z hc => logRatio_smul hd c z hc
  have hMs : ∀ j, IsSmoothHerm (mixWord (n := n) a a₀ A' k m j) := fun j => by
    simp only [mixWord]
    split_ifs <;> assumption
  have hWs : ∀ r (j : Fin (n + 1)), IsSmoothHerm (word (n := n) a a₀ A' k r j) := fun r j => by
    simp only [word]
    split_ifs <;> assumption
  have hmn : m < n + 1 := lt_of_lt_of_le hm hk
  have h0 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a₀.h {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := ha₀
  have hlr : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (logRatio a a₀)
      {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := logRatio_smooth ha ha₀
  have hT : IsSmoothHerm (a₀.tensor (HermLine.ofWeight (logRatio a a₀) hu)) := by
    show ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => a₀.h z * Real.exp (-logRatio a a₀ z))
      {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}
    exact h0.mul hlr.neg.exp
  have e1 : I P (n + 1) (word (n := n) a a₀ A' k (m + 1)) =
      I P (n + 1) (Fin.snoc (mixWord (n := n) a a₀ A' k m) a) := by
    rw [← word_comp_high a a₀ A' k m hmn, hI.1 P (n + 1) _ _ hP (hWs (m + 1))]
  have e0 : I P (n + 1) (word (n := n) a a₀ A' k m) =
      I P (n + 1) (Fin.snoc (mixWord (n := n) a a₀ A' k m) a₀) := by
    rw [← word_comp_low a a₀ A' k m hmn hm, hI.1 P (n + 1) _ _ hP (hWs m)]
  have e2 : I P (n + 1) (Fin.snoc (mixWord (n := n) a a₀ A' k m) a) =
      I P (n + 1) (Fin.snoc (mixWord (n := n) a a₀ A' k m)
        (a₀.tensor (HermLine.ofWeight (logRatio a a₀) hu))) := by
    refine metricLocal K ι I hI P (n + 1) _ _ hP (forall_snoc (p := IsSmoothHerm) hMs ha)
      (forall_snoc (p := IsSmoothHerm) hMs hT) ?_ ?_
    · intro j
      induction j using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last]
        show a.a = a₀.a + 0
        rw [add_zero, hd]
      | cast i => simp only [Fin.snoc_castSucc]
    · intro j z hz
      induction j using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last]
        exact (tensor_logRatio_h hu z hz.1).symm
      | cast i => simp only [Fin.snoc_castSucc]
  have e3 := metricChange K ι I hI P n (mixWord (n := n) a a₀ A' k m) a₀ (logRatio a a₀) hu hP hMs ha₀
    (logRatio_smooth ha ha₀)
  rw [e1, e0, e2, e3]
  ring

theorem positionTelescope : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ), IsIntersectionFamily I →
    ∀ (P : Ideal (MRing ι)) (n : ℕ) (a a₀ A' : HermLine ι) (k : ℕ), IsArithVar P (n + 1) →
      IsSmoothHerm a → IsSmoothHerm a₀ → IsSmoothHerm A' → a.a = a₀.a → k ≤ n + 1 →
      I P (n + 1) (fun j => if (j : ℕ) < k then a else A') -
          I P (n + 1) (fun j => if (j : ℕ) < k then a₀ else A') =
        -∑ i ∈ Finset.range k, ptsIntegral P (pot (mixWord (n := n) a a₀ A' k i)) (logRatio a a₀) := by
  intro K _ ι _ I hI P n a a₀ A' k hP ha ha₀ hA' hd hk
  have h1 : (fun j : Fin (n + 1) => if (j : ℕ) < k then a else A') = word (n := n) a a₀ A' k k := by
    funext j
    by_cases h : (j : ℕ) < k <;> simp [word, h]
  have h0 : (fun j : Fin (n + 1) => if (j : ℕ) < k then a₀ else A') = word (n := n) a a₀ A' k 0 := by
    funext j
    simp [word]
  have hs := Finset.sum_range_sub (fun r => I P (n + 1) (word (n := n) a a₀ A' k r)) k
  rw [h1, h0, ← hs, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  exact word_step I hI P n a a₀ A' k i hP ha ha₀ hA' hd hk (Finset.mem_range.mp hi)

end GlobalTheory.CompanionTheory.Ar.Giv.Mix.Tele
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsRegularLocalRingLocRingOfSpan
section
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Kreg

open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp

theorem isRegularLocalRing_locRing_of_span :
    ∀ (m e : ℕ) (I : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ)
      (r : Fin e → MvPolynomial (Fin m) ℂ), (∀ h ∈ I, eval t h = 0) →
      ringKrullDim (locRing I t) = e →
      Ideal.span (Set.range fun l => algebraMap _ (locRing I t) (r l)) =
        Ideal.map (algebraMap _ (locRing I t)) (ptIdeal t) →
      IsRegularLocalRing (locRing I t) := by
  intro m e I t r hI hdim hspan
  obtain ⟨hloc, hnoeth⟩ := locRing_isLocalRing_isNoetherian I t hI
  haveI := hloc
  haveI := hnoeth
  have hle : I ≤ ptIdeal t := (le_ptIdeal_iff' I t).2 hI
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  rw [maximalIdeal_locRing hle, ← hspan, hdim]
  have h1 : (Set.range fun l => algebraMap (MvPolynomial (Fin m) ℂ) (locRing I t) (r l)).ncard ≤ e := by
    rw [← Set.image_univ]
    calc _ ≤ (Set.univ : Set (Fin e)).ncard := Set.ncard_image_le Set.finite_univ
      _ = e := by rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  have h2 : (Ideal.span (Set.range fun l => algebraMap (MvPolynomial (Fin m) ℂ) (locRing I t) (r l))).spanFinrank ≤ e :=
    (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range _)).trans h1
  exact_mod_cast h2

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Kreg
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalSectionVerticalFactor
section
noncomputable section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.Giv.Mix

namespace GlobalTheory.CompanionTheory.Ar.Giv.Mix

theorem log_vertFactor_eq_re_holo : ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (p : ℕ) (M : XModel D) (U : Set M.Xc) (s : M.Xc → (Σ k, ι k) → ℂ), p ∈ D.S → IsOpen U → (∀ y ∈ U, s y ∈ mcPts (mCoordIdeal D.y)) → (∀ q, M.atlas.HoloOn U fun y => s y q) → ∀ y₀ ∈ U, ∃ V : Set M.Xc, IsOpen V ∧ y₀ ∈ V ∧ V ⊆ U ∧ ∃ G : M.Xc → ℂ, M.atlas.HoloOn V G ∧ ∀ y ∈ V, Real.log (D.vertFactor p (s y)) = (G y).re := by
  intro II Ψ _ K _ ι _ Ω _ _ E _ _ D p M U s hp hU hs hhol y₀ hy₀
  obtain ⟨dG, dH, G, H, hG, hH, hdeg, hrel, hHz⟩ := VertFactorSmooth.exists_forms D hp (hs y₀ hy₀)
  have hpos := VertFactorPos.proof II Ψ K ι Ω E D p hp (s y₀) (hs y₀ hy₀)
  rw [VertFactorSmooth.vertFactor_eq D hp (hs y₀ hy₀) hG hH hdeg hrel hHz] at hpos
  have hGz : eval (s y₀) (map (Int.castRingHom ℂ) G) ≠ 0 := by
    intro h
    rw [h, zero_div, norm_zero] at hpos
    exact lt_irrefl _ hpos
  set A := M.atlas with hA
  have HG := GlobalTheory.CompanionTheory.Ar.PB.StepW.ValHolo.holoOn_eval A hhol G
  have HH := GlobalTheory.CompanionTheory.Ar.PB.StepW.ValHolo.holoOn_eval A hhol H
  set Gf : M.Xc → ℂ := fun y => eval (s y) (map (Int.castRingHom ℂ) G) with hGf
  set Hf : M.Xc → ℂ := fun y => eval (s y) (map (Int.castRingHom ℂ) H) with hHf
  set W₁ : Set M.Xc := U ∩ {y | Hf y ≠ 0} with hW₁
  have hW₁o : IsOpen W₁ := GlobalTheory.CompanionTheory.Ar.PB.StepW.ValHolo.isOpen_inter_ne A hU HH
  have hsub : W₁ ⊆ U := Set.inter_subset_left
  have mono : ∀ {f : M.Xc → ℂ} {S T : Set M.Xc}, T ⊆ S → A.HoloOn S f → A.HoloOn T f := by
    intro f S T hTS hf j
    exact (hf j).mono (Set.inter_subset_inter_right _ (Set.preimage_mono hTS))
  set g : M.Xc → ℂ := fun y => Gf y / Hf y with hg
  have Hg : A.HoloOn W₁ g :=
    GlobalTheory.CompanionTheory.Ar.PB.StepW.ValHolo.holoOn_div_congr A hW₁o (mono hsub HG) (mono hsub HH)
      (fun y hy => hy.2) fun y _ => rfl
  set c : ℂ := g y₀ with hc
  have hc0 : c ≠ 0 := div_ne_zero hGz hHz
  set V : Set M.Xc := W₁ ∩ {y | g y / c ∈ Complex.slitPlane} with hV
  have hVo : IsOpen V := by
    rw [isOpen_iff_mem_nhds]
    rintro y ⟨hy, hsl⟩
    have hcont : ContinuousAt (fun y => g y / c) y :=
      (GlobalTheory.CompanionTheory.Ar.PB.StepW.ValHolo.continuousAt_of_holoOn A Hg hy).div_const c
    filter_upwards [hW₁o.mem_nhds hy, hcont (Complex.isOpen_slitPlane.mem_nhds hsl)] with u h1 h2
    exact ⟨h1, h2⟩
  have hy₀V : y₀ ∈ V := by
    refine ⟨⟨hy₀, hHz⟩, ?_⟩
    show g y₀ / c ∈ Complex.slitPlane
    rw [← hc, div_self hc0]
    exact Complex.one_mem_slitPlane
  refine ⟨V, hVo, hy₀V, fun y hy => hsub hy.1, fun y => Complex.log (g y / c) + (Real.log ‖c‖ : ℂ), ?_, ?_⟩
  · intro j u hu
    have hgu : AnalyticAt ℂ (g ∘ (A.chart j).symm) u :=
      Hg j u ⟨hu.1, hu.2.1⟩
    have hsl : (g ∘ (A.chart j).symm) u / c ∈ Complex.slitPlane := hu.2.2
    have h1 : AnalyticAt ℂ (fun v => (g ∘ (A.chart j).symm) v / c) u := hgu.div analyticAt_const hc0
    have h2 := (h1.clog hsl).add (analyticAt_const (v := ((Real.log ‖c‖ : ℝ) : ℂ)))
    exact h2
  · rintro y ⟨hy, hsl⟩
    have hsl' : g y / c ∈ Complex.slitPlane := hsl
    have hgy : g y ≠ 0 := by
      intro h
      rw [h, zero_div] at hsl'
      exact Complex.slitPlane_ne_zero hsl' rfl
    rw [VertFactorSmooth.vertFactor_eq D hp (hs y (hsub hy)) hG hH hdeg hrel hy.2]
    show Real.log ‖g y‖ = (Complex.log (g y / c) + ((Real.log ‖c‖ : ℝ) : ℂ)).re
    rw [Complex.add_re, Complex.ofReal_re, Complex.log_re, norm_div (g y) c,
      Real.log_div (norm_ne_zero_iff.2 hgy) (norm_ne_zero_iff.2 hc0)]
    ring

end GlobalTheory.CompanionTheory.Ar.Giv.Mix
end
end

