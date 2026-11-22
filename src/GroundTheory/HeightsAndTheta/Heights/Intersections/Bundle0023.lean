import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0018
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0015
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0017
import GroundTheory.HeightsAndTheta.Heights.Intersections.PrimeComplMapLeNonZeroDivisorsQuot
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.APrime
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsAntisym
import GroundTheory.HeightsAndTheta.Heights.Intersections.ProjLineRankTwoPushforwardHypotheses
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0013
import GroundTheory.HeightsAndTheta.Heights.Intersections.PRFormula
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0011

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.MultAtHorizontalEqZero
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

section Lemmas

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem isSec_iff_isSectionOn (P : Ideal (MRing ι)) (A : HermLine ι) (s : MRing ι) :
    IsSec P A s ↔ IsSectionOn P A s := by
  constructor
  · rintro ⟨a, ha, hdeg, hs⟩
    exact ⟨a, fun k => (hdeg k).symm, ha, hs⟩
  · rintro ⟨a, hdeg, ha, hs⟩
    exact ⟨a, ha, fun k => (hdeg k).symm, hs⟩

omit [∀ k, Fintype (ι k)] in

theorem vecEmpty_eq_elim0 : (![] : Fin 0 → HermLine ι) = Fin.elim0 := Subsingleton.elim _ _

open Classical in

theorem multAt_horizontal_eq_zero {P : Ideal (MRing ι)} {A : HermLine ι} {s : MRing ι}
    (hs : IsSectionOn P A s)
    (hind : ∀ (I : Family ι) (t : MRing ι), IsSectionOn P A t →
      recR I P (Fin.elim0 : Fin 0 → HermLine ι) A s = recR I P Fin.elim0 A t)
    {W₀ : Ideal (MRing ι)} (hW₀ : W₀ ∈ divSupp P s) (hh : IsHorizontal W₀) :
    (multAt (P ⊔ Ideal.span {s}) W₀ : ℝ) = 0 := by
  obtain ⟨a, hdeg, -, -⟩ := hs
  have hprime : W₀.IsPrime := hW₀.1.1.1
  have hle : P ⊔ Ideal.span {s} ≤ W₀ := hW₀.1.1.2
  choose i hi using hW₀.2
  have ht0 : secOf i a ∉ W₀ := secOf_not_mem hprime hi a
  have ht : IsSectionOn P A (secOf i a) :=
    ⟨a, hdeg, isMultiHomog_secOf i a, fun h => ht0 (le_sup_left.trans hle h)⟩
  have hnot : W₀ ∉ divSupp P (secOf i a) := fun h =>
    ht0 (h.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
  let F : ℝ → Family ι := fun c W _ _ => if W = W₀ then c else 0
  have hFt : recR (F 1) P (Fin.elim0 : Fin 0 → HermLine ι) A (secOf i a) =
      recR (F 0) P Fin.elim0 A (secOf i a) := by
    unfold recR
    congr 1
    refine finsum_mem_congr rfl fun W hW => ?_
    have hne : W ≠ W₀ := fun h => hnot (h ▸ hW)
    simp [F, hne]
  have key := (hind (F 1) _ ht).trans (hFt.trans (hind (F 0) _ ht).symm)
  unfold recR at key
  rw [finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite P s),
    finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite P s)] at key
  have hmem : W₀ ∈ (divSupp_finite P s).toFinset := (Set.Finite.mem_toFinset _).mpr hW₀
  have hsum := sub_left_inj.mp key
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib,
    Finset.sum_eq_single W₀ (fun W _ hne => by simp [F, hne]) (fun h => absurd hmem h)] at hsum
  simpa [F, hh] using hsum

theorem recR_family_eq {P : Ideal (MRing ι)} {A : HermLine ι} {s : MRing ι}
    (hs : IsSectionOn P A s)
    (hind : ∀ (I : Family ι) (t : MRing ι), IsSectionOn P A t →
      recR I P (Fin.elim0 : Fin 0 → HermLine ι) A s = recR I P Fin.elim0 A t)
    (I J : Family ι) :
    recR I P (Fin.elim0 : Fin 0 → HermLine ι) A s = recR J P Fin.elim0 A s := by
  unfold recR
  congr 1
  refine finsum_mem_congr rfl fun W hW => ?_
  by_cases hh : IsHorizontal W
  · rw [multAt_horizontal_eq_zero hs hind hW hh, zero_mul, zero_mul]
  · simp [hh]

end Lemmas

def IndependenceOfSmoothMetric.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι))
    (A : HermLine ι) (s t : MRing ι),
    IsArithVar P 1 → IsSmoothHerm A → IsSectionOn P A s → IsSectionOn P A t →
    recR I P (Fin.elim0 : Fin 0 → HermLine ι) A s = recR I P (Fin.elim0 : Fin 0 → HermLine ι) A t

theorem IndependenceOfSmoothMetric.of_indep (h : GroundTheory.Heights₂.Heights.Inter.RegularityIndependence.Statement) :
    IndependenceOfSmoothMetric.Statement :=
  fun K _ ι _ I P A s t hP _ hs ht => h K ι I P A s t hP hs ht

theorem R1.equiv_smooth :
    (IndependenceOfSmoothMetric.Statement ∧ GroundTheory.Heights₂.Heights.Inter.RegularityAdditive.Statement) ↔ R1.Statement := by
  constructor
  · rintro ⟨hind, hadd⟩ K _ ι _ P hP
    refine ⟨fun I J A s s' hA hs hs' => ?_, fun I A B s t hA hB hs ht => ?_⟩
    · rw [isSec_iff_isSectionOn] at hs hs'
      simp only [vecEmpty_eq_elim0, rhsR.equiv]
      rw [recR_family_eq hs (fun F t ht => hind K ι F P A s t hP hA hs ht) I J]
      exact hind K ι J P A s s' hP hA hs hs'
    · rw [isSec_iff_isSectionOn] at hs ht
      simp only [vecEmpty_eq_elim0, rhsR.equiv]
      exact hadd K ι I P A B s t hP hA hB hs ht
  · intro h
    refine ⟨fun K _ ι _ I P A s t hP hA hs ht => ?_, fun K _ ι _ I P A B s t hP hA hB hs ht => ?_⟩
    · have := (h K ι P hP).1 I I A s t hA ((isSec_iff_isSectionOn _ _ _).mpr hs)
        ((isSec_iff_isSectionOn _ _ _).mpr ht)
      simpa only [vecEmpty_eq_elim0, rhsR.equiv] using this
    · have := (h K ι P hP).2 I A B s t hA hB ((isSec_iff_isSectionOn _ _ _).mpr hs)
        ((isSec_iff_isSectionOn _ _ _).mpr ht)
      simpa only [vecEmpty_eq_elim0, rhsR.equiv] using this

theorem R1.of_first
    (h : GroundTheory.Heights₂.Heights.Inter.RegularityIndependence.Statement ∧ GroundTheory.Heights₂.Heights.Inter.RegularityAdditive.Statement) :
    R1.Statement :=
  R1.equiv_smooth.mp ⟨IndependenceOfSmoothMetric.of_indep h.1, h.2⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.OneNotMemOfIsPrime
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo IsLocalRing

noncomputable section

namespace regularityLocalFlat_holds

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

section Forms

theorem homog_zero (a : K → ℕ) : IsMultiHomog (0 : MRing ι) a := by
  intro m hm
  simp at hm

theorem homog_one : IsMultiHomog (1 : MRing ι) 0 := by
  classical
  intro m hm k
  rw [support_one, Finset.mem_singleton] at hm
  subst hm
  simp

theorem homog_mul {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) :
    IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf m1 hm1 k, hg m2 hm2 k]

theorem homog_add {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f + g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (support_add hm) with h | h
  · exact hf m h k
  · exact hg m h k

theorem homog_neg {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) : IsMultiHomog (-f) a := by
  intro m hm k
  rw [support_neg] at hm
  exact hf m hm k

theorem homog_X [DecidableEq K] (k : K) (i : ι k) :
    IsMultiHomog (X ⟨k, i⟩ : MRing ι) (Pi.single k 1) := by
  classical
  intro m hm k'
  rw [support_X, Finset.mem_singleton] at hm
  subst hm
  by_cases h : k' = k
  · subst h
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [Finsupp.single_apply, if_neg]
      intro e
      exact hj (sigma_mk_injective e).symm
    · simp
  · have : ∀ j : ι k', (⟨k, i⟩ : Σ k, ι k) ≠ ⟨k', j⟩ := fun j e => h (congrArg Sigma.fst e).symm
    simp [Finsupp.single_apply, this, h, Pi.single_apply]

theorem homog_pow {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (n : ℕ) :
    IsMultiHomog (f ^ n) (n • a) := by
  induction n with
  | zero => simpa using (homog_one (ι := ι))
  | succ n ih =>
    rw [pow_succ, succ_nsmul]
    exact homog_mul ih hf

theorem mem_of_sum_mem {I : Ideal (MRing ι)} (hI : IsMultiHomogIdeal I) {β : Type*} (s : Finset β)
    (h : β → MRing ι) (d : β → K → ℕ) (hd : Set.InjOn d s) (hh : ∀ b ∈ s, IsMultiHomog (h b) (d b))
    (hsum : ∑ b ∈ s, h b ∈ I) : ∀ b ∈ s, h b ∈ I := by
  classical
  intro b hb
  obtain ⟨g, hgI, hg⟩ :=
    exists_blockComponent (isHomogeneous_of_isMultiHomogIdeal hI) (d b) Finset.univ hsum
  convert hgI using 1
  ext m
  rw [hg, coeff_sum]
  by_cases hm : coeff m (h b) = 0
  · rw [hm]
    split_ifs with hdeg
    · refine (Finset.sum_eq_zero fun b' hb' => ?_).symm
      by_contra hne
      have h1 := hh b' hb' m (mem_support_iff.mpr hne)
      have hbb : b' = b := hd hb' hb (funext fun k => (h1 k).symm.trans (hdeg k (Finset.mem_univ k)))
      exact hne (hbb ▸ hm)
    · rfl
  · have hdeg := hh b hb m (mem_support_iff.mpr hm)
    rw [if_pos (fun k _ => hdeg k), Finset.sum_eq_single b]
    · intro b' hb' hne
      by_contra h'
      exact hne (hd hb' hb (funext fun k => (hh b' hb' m (mem_support_iff.mpr h') k).symm.trans (hdeg k)))
    · intro h'
      exact absurd hb h'

end Forms

section Loc

variable (P W : Ideal (MRing ι)) [P.IsPrime] [W.IsPrime]

def fracHom : MRing ι →+* FractionRing (MRing ι ⧸ P) :=
  (algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P))).comp (Ideal.Quotient.mk P)

theorem fracHom_apply (u : MRing ι) :
    fracHom P u = algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u) :=
  rfl

variable {P} in
theorem fracHom_eq_zero_iff {u : MRing ι} : fracHom P u = 0 ↔ u ∈ P := by
  rw [fracHom_apply, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]

theorem one_notMem_of_isPrime : (1 : MRing ι) ∉ W :=
  (Ideal.ne_top_iff_one W).mp (Ideal.IsPrime.ne_top ‹_›)

variable {P W} in

theorem mem_locRing_iff (hPW : P ≤ W) {x : FractionRing (MRing ι ⧸ P)} :
    x ∈ locRing P W ↔ ∃ (u v : MRing ι) (a : K → ℕ), IsMultiHomog u a ∧ IsMultiHomog v a ∧ v ∉ W ∧
      x * fracHom P v = fracHom P u := by
  constructor
  · intro hx
    induction hx using Subring.closure_induction with
    | mem x hx =>
      obtain ⟨u, v, a, hv, hvW, hu, hva, rfl⟩ := hx
      exact ⟨u, v, a, hu, hva, hvW, IsLocalization.mk'_spec _ _ _⟩
    | zero => exact ⟨0, 1, 0, homog_zero 0, homog_one, one_notMem_of_isPrime W, by simp⟩
    | one => exact ⟨1, 1, 0, homog_one, homog_one, one_notMem_of_isPrime W, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨u, v, a, hu, hv, hvW, hx⟩ := hx
      obtain ⟨u', v', a', hu', hv', hvW', hy⟩ := hy
      refine ⟨u * v' + u' * v, v * v', a + a', homog_add (homog_mul hu hv') ?_, homog_mul hv hv', ?_, ?_⟩
      · rw [add_comm a a']
        exact homog_mul hu' hv
      · exact fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hvW hvW'
      · simp only [map_add, map_mul]
        rw [← hx, ← hy]
        ring
    | neg x _ hx =>
      obtain ⟨u, v, a, hu, hv, hvW, hx⟩ := hx
      exact ⟨-u, v, a, homog_neg hu, hv, hvW, by rw [map_neg, ← hx, neg_mul]⟩
    | mul x y _ _ hx hy =>
      obtain ⟨u, v, a, hu, hv, hvW, hx⟩ := hx
      obtain ⟨u', v', a', hu', hv', hvW', hy⟩ := hy
      refine ⟨u * u', v * v', a + a', homog_mul hu hu', homog_mul hv hv', ?_, ?_⟩
      · exact fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hvW hvW'
      · simp only [map_mul]
        rw [← hx, ← hy]
        ring
  · rintro ⟨u, v, a, hu, hv, hvW, hx⟩
    have hv' : Ideal.Quotient.mk P v ∈ nonZeroDivisors (MRing ι ⧸ P) := by
      refine mem_nonZeroDivisors_of_ne_zero ?_
      rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
      exact fun h => hvW (hPW h)
    refine Subring.subset_closure ⟨u, v, a, hv', hvW, hu, hv, ?_⟩
    rw [IsLocalization.eq_mk'_iff_mul_eq]
    exact hx

variable {P W} in

theorem div_mem_locRing (hPW : P ≤ W) {u v : MRing ι} {a : K → ℕ} (hu : IsMultiHomog u a)
    (hv : IsMultiHomog v a) (hvW : v ∉ W) : fracHom P u / fracHom P v ∈ locRing P W := by
  refine (mem_locRing_iff hPW).mpr ⟨u, v, a, hu, hv, hvW, div_mul_cancel₀ _ ?_⟩
  rw [Ne, fracHom_eq_zero_iff]
  exact fun h => hvW (hPW h)

variable {P W} in

theorem isUnit_iff (hPW : P ≤ W) (x : locRing P W) {u v : MRing ι} {a : K → ℕ} (hu : IsMultiHomog u a)
    (hv : IsMultiHomog v a) (hvW : v ∉ W)
    (hx : (x : FractionRing (MRing ι ⧸ P)) * fracHom P v = fracHom P u) : IsUnit x ↔ u ∉ W := by
  constructor
  · intro hunit huW
    obtain ⟨y, hxy⟩ := hunit.exists_right_inv
    obtain ⟨u', v', a', -, -, hvW', hy⟩ := (mem_locRing_iff hPW).mp y.2
    have h1 : (x : FractionRing (MRing ι ⧸ P)) * (y : FractionRing (MRing ι ⧸ P)) = 1 :=
      congrArg Subtype.val hxy
    have h2 : fracHom P (u * u' - v * v') = 0 := by
      rw [map_sub, map_mul, map_mul, ← hx, ← hy]
      linear_combination (fracHom P v * fracHom P v') * h1
    rw [fracHom_eq_zero_iff] at h2
    have hvv : v * v' ∈ W := by
      have := W.sub_mem (W.mul_mem_right u' huW) (hPW h2)
      simpa using this
    exact (Ideal.IsPrime.mem_or_mem ‹_› hvv).elim hvW hvW'
  · intro huW
    have hu0 : fracHom P u ≠ 0 := by
      rw [Ne, fracHom_eq_zero_iff]
      exact fun h => huW (hPW h)
    have hv0 : fracHom P v ≠ 0 := by
      rw [Ne, fracHom_eq_zero_iff]
      exact fun h => hvW (hPW h)
    refine IsUnit.of_mul_eq_one (⟨_, div_mem_locRing hPW hv hu huW⟩ : locRing P W) (Subtype.ext ?_)
    change (x : FractionRing (MRing ι ⧸ P)) * (fracHom P v / fracHom P u) = 1
    rw [eq_div_of_mul_eq hv0 hx]
    field_simp

variable {P W} in

theorem isLocalRing (hPW : P ≤ W) : IsLocalRing (locRing P W) := by
  refine IsLocalRing.of_nonunits_add fun x y hx hy hxy => ?_
  obtain ⟨u, v, a, hu, hv, hvW, hx'⟩ := (mem_locRing_iff hPW).mp x.2
  obtain ⟨u', v', a', hu', hv', hvW', hy'⟩ := (mem_locRing_iff hPW).mp y.2
  have huW : u ∈ W := by
    by_contra h
    exact hx ((isUnit_iff hPW x hu hv hvW hx').mpr h)
  have hu'W : u' ∈ W := by
    by_contra h
    exact hy ((isUnit_iff hPW y hu' hv' hvW' hy').mpr h)
  have hnum : IsMultiHomog (u * v' + u' * v) (a + a') := by
    refine homog_add (homog_mul hu hv') ?_
    rw [add_comm a a']
    exact homog_mul hu' hv
  have hden : v * v' ∉ W := fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hvW hvW'
  have heq : ((x + y : locRing P W) : FractionRing (MRing ι ⧸ P)) * fracHom P (v * v') =
      fracHom P (u * v' + u' * v) := by
    change ((x : FractionRing (MRing ι ⧸ P)) + y) * _ = _
    simp only [map_add, map_mul]
    rw [← hx', ← hy']
    ring
  exact (isUnit_iff hPW (x + y) hnum (homog_mul hv hv') hden heq).mp hxy
    (W.add_mem (W.mul_mem_right _ huW) (W.mul_mem_right _ hu'W))

variable {P W} in

theorem mem_maximalIdeal_iff (hPW : P ≤ W) (x : locRing P W) {u v : MRing ι} {a : K → ℕ}
    (hu : IsMultiHomog u a) (hv : IsMultiHomog v a) (hvW : v ∉ W)
    (hx : (x : FractionRing (MRing ι ⧸ P)) * fracHom P v = fracHom P u) :
    haveI := isLocalRing hPW
    x ∈ maximalIdeal (locRing P W) ↔ u ∈ W := by
  have := isLocalRing hPW
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff hPW x hu hv hvW hx, not_not]

end Loc

end regularityLocalFlat_holds

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PAPrime
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem yyBlockMap_thm : YYBlockMapStatement := by
  intro ι ν κ j
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b h
    fin_cases j <;> cases a <;> cases b <;> simp_all [diagonalBlockIndex]
  · rintro ⟨a, x⟩ ⟨b, y⟩ h
    fin_cases j <;> cases a <;> cases b <;> simp [T.yyEmb] at h <;> injection h with h1 h2 <;>
      first | (cases h2; rfl) | cases h1
  · rintro ⟨a, x⟩
    fin_cases j <;> cases a <;> rfl
  · rintro ⟨b, y⟩ ⟨a, ha⟩
    fin_cases j <;> cases a <;> cases b <;>
      first
        | (refine ⟨⟨.base, y⟩, ?_⟩; simp [T.yyEmb]; done)
        | (refine ⟨⟨.det, y⟩, ?_⟩; simp [T.yyEmb]; done)
        | (refine ⟨⟨.line, y⟩, ?_⟩; simp [T.yyEmb]; done)
        | simp [diagonalBlockIndex] at ha

theorem PropAPrime.proof (h₁ : ToFibreSquare.Statement) (h₂ : FibreInt.Statement) : PropAPrime.Statement := by
  intro I hI D S X A hX hAs hAb k hk hkD
  have hb := yyBlockMap_thm S.ι S.ν S.κ
  have p0 := IndefiniteRowSideFullHecke.Inter.isPullHerm_pullHerm (hb 0) X
  have p1 := IndefiniteRowSideFullHecke.Inter.isPullHerm_pullHerm (hb 1) X
  have pA := IndefiniteRowSideFullHecke.Inter.isPullHerm_pullHerm (hb 0) A
  obtain ⟨F, hFI, hFΦ⟩ := h₁ I hI D S X A _ _ _ hX hAs hAb p0 p1 pA
  have hfib := h₂ D S X A _ _ _ hX hAs hAb p0 p1 pA k hk hkD
  have hF := aPrime_thm D F k hk hkD
  rw [hFI (2 * k) (by omega),
    Finset.sum_congr rfl (fun i hi => hFΦ k i hk hkD (Finset.mem_range.1 hi)), ← Finset.mul_sum, hfib,
    ← mul_neg] at hF
  exact mul_left_cancel₀ (by positivity) hF

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PDiagDiv
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

namespace DiagonalDivisor

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem divCycle_of_mem {P W : Ideal (MRing ι)} {s : MRing ι} (hW : W ∈ divSupp P s) :
    divCycle P s W = multAt (P ⊔ Ideal.span {s}) W := by
  unfold divCycle
  simp [Finsupp.ofSupportFinite_coe, hW]

theorem divCycle_of_not_mem {P W : Ideal (MRing ι)} {s : MRing ι} (hW : W ∉ divSupp P s) :
    divCycle P s W = 0 := by
  unfold divCycle
  simp [Finsupp.ofSupportFinite_coe, hW]

open Classical in

theorem divCycle_eq_ite {P : Ideal (MRing ι)} [P.IsPrime] {s u : MRing ι} (hu : u ∉ P)
    (W : Ideal (MRing ι)) :
    divCycle P s W = if W ∈ divSupp P (s * u) then multAt (P ⊔ Ideal.span {s}) W else 0 := by
  by_cases hW : W ∈ divSupp P (s * u)
  · rw [if_pos hW]
    by_cases hWs : W ∈ divSupp P s
    · exact divCycle_of_mem hWs
    rw [divCycle_of_not_mem hWs]
    have hWp : W.IsPrime := hW.1.1.1
    by_cases hsW : s ∈ W
    · exfalso
      refine hWs ⟨⟨⟨hWp, sup_le (le_sup_left.trans hW.1.1.2)
        ((Ideal.span_singleton_le_iff_mem _).mpr hsW)⟩, fun Q hQ hQW => hW.1.2 ⟨hQ.1, ?_⟩ hQW⟩, hW.2⟩
      exact (sup_le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr
        (Ideal.mul_mem_right u _ (Ideal.mem_span_singleton_self s))) P).trans hQ.2
    · have hnle : ¬ P ⊔ Ideal.span {s} ≤ W := fun h => hsW (h (Ideal.mem_sup_right (Ideal.subset_span rfl)))
      unfold multAt
      rw [dif_pos hWp, Module.length_eq_zero_iff.mpr
        (NumbersDVR.localizedQuot_subsingleton_of_not_le _ W hnle)]
      rfl
  · rw [if_neg hW]
    refine divCycle_of_not_mem fun hWs => hW ⟨?_, hWs.2⟩
    exact NumbersDVR.mem_minimalPrimes_sup_span_mul hu hWs.1

end DiagonalDivisor

open DiagonalDivisor in

theorem DiagDiv.proof (hF : DiagForms.Statement) (hO : DiagOrd.Statement) : DiagDiv.Statement := by
  intro Ω _ ι ν κ _ _ _ E _ _ Φ _ _ x B e φ δ hS hG hD hx a ha
  refine ⟨hF Ω ι ν κ E Φ x B e φ δ hS hG hD hx a ha, ?_⟩
  intro n g h hg hh hP hq
  obtain ⟨hΔ, hW⟩ := hO Ω ι ν κ E Φ x B e φ δ hS hG hD hx a ha n g h hg hh hP hq
  have hPp : (T.wwIdeal x δ e φ (a 0) (a 1)).IsPrime := RingHom.ker_isPrime _
  have ht : T.diagSec a ≠ 0 := by
    unfold T.diagSec
    exact sub_ne_zero.mpr (fun h01 => absurd (ha.injective h01) (by decide))
  have hgP : g ∉ T.wwIdeal x δ e φ (a 0) (a 1) := by
    have hh' := (DiagRAux.not_mem_ker_iff_aeval_ne _ h _ hh).1 hP
    exact (DiagRAux.not_mem_ker_iff_aeval_ne _ g _ hg).2 (hq ▸ mul_ne_zero ht hh')
  ext W
  have hcg := divCycle_eq_ite (s := g) hP W
  have hch := divCycle_eq_ite (s := h) hgP W
  rw [mul_comm h g] at hch
  simp only [T.toZCycle, Finsupp.coe_sub, Pi.sub_apply, Finsupp.mapRange_apply, Finsupp.single_apply, hcg, hch]
  by_cases hWm : W ∈ divSupp (T.wwIdeal x δ e φ (a 0) (a 1)) (g * h)
  · rw [if_pos hWm, if_pos hWm, hW W hWm]
    simp only [eq_comm]
  · rw [if_neg hWm, if_neg hWm, if_neg (fun h' : T.wwIdeal x δ e φ (a 0) (a 0) = W => hWm (h' ▸ hΔ))]
    simp

end

end GroundTheory.Heights₂.Heights.Inter
end

