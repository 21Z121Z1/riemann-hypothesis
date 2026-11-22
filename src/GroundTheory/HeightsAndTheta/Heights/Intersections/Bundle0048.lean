import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0028
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0025
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0044
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0045
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0037
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0033
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0043
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0018
import GroundTheory.HeightsAndTheta.Heights.Intersections.PBaseChange
import GroundTheory.HeightsAndTheta.Heights.Intersections.PReducedCutLength
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0026
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0001

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.IntCastMemRegMaxAt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem regRing_mem_locRing {P W : Ideal (MRing ι)} (hW : IsClosedPt W) (hPW : P ≤ W) (x : regRing P) :
    ((x : funField P) : FractionRing (MRing ι ⧸ P)) ∈ locRing P W :=
  x.2 W hW hPW

def regToLoc (P W : Ideal (MRing ι)) (hW : IsClosedPt W) (hPW : P ≤ W) : regRing P →+* locRing P W where
  toFun x := ⟨((x : funField P) : FractionRing (MRing ι ⧸ P)), regRing_mem_locRing hW hPW x⟩
  map_one' := Subtype.ext (by simp)
  map_mul' _ _ := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' _ _ := Subtype.ext (by simp)

theorem regToLoc_apply {P W : Ideal (MRing ι)} (hW : IsClosedPt W) (hPW : P ≤ W) (x : regRing P) :
    regToLoc P W hW hPW x = ⟨((x : funField P) : FractionRing (MRing ι ⧸ P)), regRing_mem_locRing hW hPW x⟩ :=
  rfl

theorem regToLoc_coe {P W : Ideal (MRing ι)} (hW : IsClosedPt W) (hPW : P ≤ W) (x : regRing P) :
    ((regToLoc P W hW hPW x : locRing P W) : FractionRing (MRing ι ⧸ P)) =
      ((x : funField P) : FractionRing (MRing ι ⧸ P)) :=
  (congrArg Subtype.val (regToLoc_apply hW hPW x)).trans (Subtype.coe_mk _ _)

def regMaxAt (P W : Ideal (MRing ι)) (hW : IsClosedPt W) (hPW : P ≤ W) (hloc : IsLocalRing (locRing P W)) :
    Ideal (regRing P) :=
  (IsLocalRing.maximalIdeal (locRing P W)).comap (regToLoc P W hW hPW)

theorem not_mem_regMaxAt_iff {P W : Ideal (MRing ι)} (hW : IsClosedPt W) (hPW : P ≤ W)
    (hloc : IsLocalRing (locRing P W)) (x : regRing P) :
    x ∉ regMaxAt P W hW hPW hloc ↔
      ∃ z ∈ locRing P W, ((x : funField P) : FractionRing (MRing ι ⧸ P)) * z = 1 := by
  have hc : ∀ b : locRing P W, ((regToLoc P W hW hPW x * b : locRing P W) : FractionRing (MRing ι ⧸ P)) =
      ((x : funField P) : FractionRing (MRing ι ⧸ P)) * b := fun b => by
    rw [Subring.coe_mul, regToLoc_coe]
  simp only [regMaxAt, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
  constructor
  · intro h
    obtain ⟨b, hb⟩ := h.exists_right_inv
    refine ⟨b.1, b.2, ?_⟩
    rw [← hc b, hb, Subring.coe_one]
  · rintro ⟨z, hz, h⟩
    refine IsUnit.of_mul_eq_one (a := regToLoc P W hW hPW x) ⟨z, hz⟩ (Subtype.ext ?_)
    rw [hc, Subring.coe_one]
    exact h

theorem intCast_mem_regMaxAt (hL : LocRingLocal.Statement) {P W : Ideal (MRing ι)} (hPp : P.IsPrime)
    (hW : IsClosedPt W) (hPW : P ≤ W) (hloc : IsLocalRing (locRing P W)) {n : ℤ} (hn : C n ∈ W) :
    (n : regRing P) ∈ regMaxAt P W hW hPW hloc := by
  by_contra h
  obtain ⟨z, hz, h⟩ := (not_mem_regMaxAt_iff hW hPW hloc _).1 h
  have h1W : (1 : MRing ι) ∉ W := fun h => hW.1.1.ne_top ((Ideal.eq_top_iff_one _).mpr h)
  have hu := ((hL K ι P W hPp hW.1.1 hPW).2 (n : locRing P W) (C n) 1 0 (RegularityDenominator.isMultiHomog_C n)
    AvoidRing.isMultiHomog_one h1W (by simp [eq_intCast C n])).1
  refine hu (IsUnit.of_mul_eq_one (a := (n : locRing P W)) ⟨z, hz⟩ (Subtype.ext ?_)) hn
  simpa using h

theorem regMaxAt_isMaximal (hO : RegularityOrder.Statement) (hL : LocRingLocal.Statement) {P W : Ideal (MRing ι)}
    (hP : IsArithVar P 1) (hW : IsClosedPt W) (hPW : P ≤ W) (hloc : IsLocalRing (locRing P W)) :
    (regMaxAt P W hW hPW hloc).IsMaximal := by
  have : (regMaxAt P W hW hPW hloc).IsPrime := by unfold regMaxAt; infer_instance
  have : Module.Finite ℤ (regRing P) := (hO K ι P hP).2.1
  have hvert : W.comap (C : ℤ →+* MRing ι) ≠ ⊥ := fun hh =>
    arithVarZero K ι W ⟨hP.1, hW.1, hh, by rw [zero_add]; exact hW.2⟩
  obtain ⟨n, hnW, hn0⟩ := (Submodule.ne_bot_iff _).mp hvert
  have hn : n ∈ (regMaxAt P W hW hPW hloc).comap (algebraMap ℤ (regRing P)) := by
    rw [Ideal.mem_comap, algebraMap_int_eq, eq_intCast]
    exact intCast_mem_regMaxAt hL hP.2.1.1 hW hPW hloc hnW
  exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := ℤ) _
    (_root_.IsPrime.to_maximal_ideal fun h => hn0 (by rw [h] at hn; exact hn))

theorem RegularityMaximalSpectrum.proof (hO : RegularityOrder.Statement)
    (hZ : RegularityLocalize.Statement) (hI : LocRingInj.Statement) (hS : RegularityMaximalSurjective.Statement) :
    RegularityMaximalSpectrum.Statement := by
  classical
  have hL : LocRingLocal.Statement := LocRingLocal.proof LocRingFrac.proof
  intro K _ ι _ P hP
  have hPp : P.IsPrime := hP.2.1.1
  have hloc : ∀ W : {W : Ideal (MRing ι) // IsClosedPt W ∧ P ≤ W}, IsLocalRing (locRing P W.1) :=
    fun W => (hL K ι P W.1 hPp W.2.1.1.1 W.2.2).1
  let m : {W : Ideal (MRing ι) // IsClosedPt W ∧ P ≤ W} → Ideal (regRing P) := fun W =>
    regMaxAt P W.1 W.2.1 W.2.2 (hloc W)
  have hm : ∀ W (x : regRing P), x ∉ m W ↔
      ∃ z ∈ locRing P W.1, ((x : funField P) : FractionRing (MRing ι ⧸ P)) * z = 1 :=
    fun W => not_mem_regMaxAt_iff W.2.1 W.2.2 (hloc W)

  have hsub : ∀ W W', m W = m W' → locRing P W.1 ≤ locRing P W'.1 := by
    intro W W' hWW' y hy
    obtain ⟨s, x, hsu, hys⟩ := hZ K ι P W.1 y hP W.2.1 W.2.2 hy
    obtain ⟨z, hz, hsz⟩ := (hm W' s).1 (hWW' ▸ (hm W s).2 hsu)
    rw [show y = ((x : funField P) : FractionRing (MRing ι ⧸ P)) * z by rw [← hys, mul_assoc, hsz, mul_one]]
    exact mul_mem (regRing_mem_locRing W'.2.1 W'.2.2 x) hz
  let f : {W : Ideal (MRing ι) // IsClosedPt W ∧ P ≤ W} → MaximalSpectrum (regRing P) := fun W =>
    ⟨m W, regMaxAt_isMaximal hO hL hP W.2.1 W.2.2 (hloc W)⟩
  have hbij : Function.Bijective f := by
    refine ⟨fun W W' h => Subtype.ext (hI K ι P W.1 W'.1 hPp W.2.1.1 W'.2.1.1 W.2.2 W'.2.2
      (le_antisymm (hsub W W' (congrArg MaximalSpectrum.asIdeal h))
        (hsub W' W (congrArg MaximalSpectrum.asIdeal h).symm))), ?_⟩
    rintro ⟨M, hM⟩
    obtain ⟨W, hWc, hPW, hW⟩ := hS K ι P hP M hM
    refine ⟨⟨W, hWc, hPW⟩, ?_⟩
    have hle : M ≤ m ⟨W, hWc, hPW⟩ := fun x hx => by
      by_contra hc
      obtain ⟨z, hz, h⟩ := (hm _ x).1 hc
      exact hW x hx z hz h
    exact MaximalSpectrum.ext (hM.eq_of_le (regMaxAt_isMaximal hO hL hP hWc hPW _).ne_top hle).symm
  refine ⟨Equiv.ofBijective f hbij, fun W y => ⟨fun hy => ?_, ?_⟩⟩
  · obtain ⟨s, x, hsu, hys⟩ := hZ K ι P W.1 y hP W.2.1 W.2.2 hy
    exact ⟨x, s, (hm W s).2 hsu, hys⟩
  · rintro ⟨x, s, hs, hys⟩
    obtain ⟨z, hz, hsz⟩ := (hm W s).1 hs
    rw [show y = ((x : funField P) : FractionRing (MRing ι ⧸ P)) * z by rw [← hys, mul_assoc, hsz, mul_one]]
    exact mul_mem (regRing_mem_locRing W.2.1 W.2.2 x) hz

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.KerIsMultiHomogIdeal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

attribute [local instance] MvPolynomial.weightedGradedAlgebra

namespace RegularityValuationCentre

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem ltIdeal_one_isPrime {R Γ : Type*} [CommRing R] [LinearOrderedCommGroupWithZero Γ] (v : Valuation R Γ) :
    (v.ltIdeal 1).IsPrime := by
  refine ⟨fun h => ?_, fun {x y} hxy => ?_⟩
  · have h1 : (1 : v.integer) ∈ v.ltIdeal 1 := h ▸ Submodule.mem_top
    simp [Valuation.mem_ltIdeal_iff] at h1
  · simp only [Valuation.mem_ltIdeal_iff, Units.val_one] at hxy ⊢
    by_contra hc
    push Not at hc
    have hx : v x = 1 := le_antisymm x.2 hc.1
    have hy : v y = 1 := le_antisymm y.2 hc.2
    simp [Subring.coe_mul, map_mul, hx, hy] at hxy

def tWeight [DecidableEq K] (k : K) : K → ℕ := fun k' => if k' = k then 1 else 0

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem specMap_component [DecidableEq K] {E : Type*} [Field E] (ψ : MRing ι →+* E) (k : K) (d : ℕ)
    (g : MRing ι) :
    RegularityFunctionFieldNumber.specMap ψ ∅ (weightedHomogeneousComponent (blockWeight k) d g) =
      weightedHomogeneousComponent (tWeight k) d (RegularityFunctionFieldNumber.specMap ψ ∅ g) := by
  induction g using MvPolynomial.induction_on' with
  | monomial m c =>
    have hX : ∀ p : Σ k, ι k, IsWeightedHomogeneous (tWeight k)
        (RegularityFunctionFieldNumber.cS E ∅ p.1 * MvPolynomial.C (ψ (X p))) (tWeight k p.1) := by
      intro p
      simp only [RegularityFunctionFieldNumber.cS, Finset.notMem_empty, if_false]
      rw [mul_comm]
      exact (isWeightedHomogeneous_X E (tWeight k) p.1).C_mul _
    have hh : IsWeightedHomogeneous (tWeight k) (RegularityFunctionFieldNumber.specMap ψ ∅ (monomial m c))
        (Finsupp.weight (blockWeight k) m) := by
      rw [RegularityFunctionFieldNumber.specMap, aeval_monomial, Finsupp.weight_apply, Finsupp.prod, Finsupp.sum,
        show algebraMap ℤ (MvPolynomial K E) c = MvPolynomial.C (c : E) by simp]
      exact (IsWeightedHomogeneous.prod _ _ _ fun p _ => (hX p).pow (m p)).C_mul _
    have hm : IsWeightedHomogeneous (blockWeight k) (monomial m c) (Finsupp.weight (blockWeight k) m) :=
      isWeightedHomogeneous_monomial _ _ _ rfl
    by_cases h : d = Finsupp.weight (blockWeight k) m
    · rw [h, hm.weightedHomogeneousComponent_same, hh.weightedHomogeneousComponent_same]
    · rw [hm.weightedHomogeneousComponent_ne d h, hh.weightedHomogeneousComponent_ne d h, map_zero]
  | add p q hp hq =>
    rw [map_add, map_add, hp, hq, map_add (RegularityFunctionFieldNumber.specMap ψ ∅) p q]
    exact ((weightedHomogeneousComponent (R := E) (tWeight k) d).map_add _ _).symm

set_option backward.isDefEq.respectTransparency.types false in

theorem ker_isMultiHomogIdeal [DecidableEq K] {E : Type*} [Field E] (ψ : MRing ι →+* E) :
    IsMultiHomogIdeal (RingHom.ker (RegularityFunctionFieldNumber.specMap ψ ∅)) := by
  refine isMultiHomogIdeal_of_isHomogeneous fun k d g hg => ?_
  have hc : weightedHomogeneousComponent (blockWeight k) d g ∈ RingHom.ker (RegularityFunctionFieldNumber.specMap ψ ∅) := by
    rw [RingHom.mem_ker] at hg ⊢
    rw [specMap_component, hg, map_zero]
  rw [← weightedDecomposition.decompose'_apply] at hc
  exact hc

end RegularityValuationCentre

set_option maxHeartbeats 400000 in
open regularityEmbedding_holds in

theorem RegularityValuationCentre.proof : RegularityValuationCentre.Statement := by
  intro K _ ι _ P hP Γ _ v n hn
  classical
  obtain ⟨hPp, hPh, hPr⟩ := hP
  have := hPp
  have hX0 : ∀ {f : MRing ι}, f ∉ P → toFrac P f ≠ 0 := fun hf h => hf (toFrac_eq_zero.mp h)

  have hratio : ∀ (p : Σ k, ι k) (i : ι p.1), (X ⟨p.1, i⟩ : MRing ι) ∉ P → ∃ x : funField P,
      (x : FractionRing (MRing ι ⧸ P)) * toFrac P (X ⟨p.1, i⟩) = toFrac P (X p) := fun p i hi =>
    exists_funField_mul_eq (isMultiHomog_X_single p.1 p.2) (isMultiHomog_X_single p.1 i) hi
  choose j0 hj0 using hPr
  choose s hs using fun p : Σ k, ι k => hratio p (j0 p.1) (hj0 p.1)

  have hj : ∀ k, ∃ i, (X ⟨k, i⟩ : MRing ι) ∉ P ∧
      ∀ i', (X ⟨k, i'⟩ : MRing ι) ∉ P → v (s ⟨k, i'⟩) ≤ v (s ⟨k, i⟩) := by
    intro k
    obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image (Finset.univ.filter fun i => (X ⟨k, i⟩ : MRing ι) ∉ P)
      (fun i => v (s ⟨k, i⟩)) ⟨j0 k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj0 k⟩⟩
    exact ⟨i, (Finset.mem_filter.mp hi).2,
      fun i' hi' => hmax i' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi'⟩)⟩
  choose j hjP hjmax using hj
  choose r hr using fun p : Σ k, ι k => hratio p (j p.1) (hjP p.1)

  have hrle : ∀ p, v (r p) ≤ 1 := by
    intro p
    by_cases hp : (X p : MRing ι) ∈ P
    · have h0 : r p = 0 := Subtype.ext <|
        (mul_eq_zero.mp ((hr p).trans (toFrac_eq_zero.mpr hp))).resolve_right (hX0 (hjP p.1))
      simp [h0]
    · obtain ⟨t, ht⟩ := hratio ⟨p.1, j0 p.1⟩ (j p.1) (hjP p.1)
      have hs' := hs ⟨p.1, j p.1⟩
      dsimp only at ht hs'
      have hst : s ⟨p.1, j p.1⟩ * t = 1 := Subtype.ext <| mul_right_cancel₀ (hX0 (hjP p.1)) <| by
        rw [Subring.coe_mul, Subring.coe_one, mul_assoc, ht, hs', one_mul]
      have hrs : r p * s ⟨p.1, j p.1⟩ = s p := Subtype.ext <| mul_right_cancel₀ (hX0 (hj0 p.1)) <| by
        rw [Subring.coe_mul, mul_assoc, hs', hr, hs]
      have hvs : v (s ⟨p.1, j p.1⟩) ≠ 0 := fun h => by
        have h1 := congrArg v hst
        rw [map_mul, h, zero_mul, map_one] at h1
        exact zero_ne_one h1
      have hle : v (r p) * v (s ⟨p.1, j p.1⟩) ≤ 1 * v (s ⟨p.1, j p.1⟩) := by
        rw [← map_mul, hrs, one_mul]
        exact hjmax p.1 p.2 hp
      exact le_of_mul_le_mul_right hle (zero_lt_iff.mpr hvs)

  have hψle : ∀ g, chartHom r g ∈ v.integer := by
    intro g
    induction g using MvPolynomial.induction_on with
    | C a => simp [chartHom]
    | add f g hf hg => rw [map_add]; exact add_mem hf hg
    | mul_X f p hf =>
      rw [map_mul]
      exact mul_mem hf (by simpa [chartHom] using (Valuation.mem_integer_iff v (r p)).mpr (hrle p))
  have : (v.ltIdeal 1).IsPrime := RegularityValuationCentre.ltIdeal_one_isPrime v

  obtain ⟨E, _, ψE, hψE⟩ : ∃ (E : Type) (_ : Field E) (ψE : MRing ι →+* E),
      ∀ g, ψE g = 0 ↔ v (chartHom r g) < 1 := by
    refine ⟨FractionRing (v.integer ⧸ v.ltIdeal 1), inferInstance, (algebraMap (v.integer ⧸ v.ltIdeal 1) _).comp
      ((Ideal.Quotient.mk (v.ltIdeal 1)).comp ((chartHom r).codRestrict v.integer hψle)), fun g => ?_⟩
    rw [RingHom.comp_apply, RingHom.comp_apply, map_eq_zero_iff _ (IsFractionRing.injective _ _),
      Ideal.Quotient.eq_zero_iff_mem, Valuation.mem_ltIdeal_iff, Units.val_one]
    rfl

  have hform : ∀ (g : MRing ι) (a : K → ℕ), IsMultiHomog g a →
      (g ∈ RingHom.ker (RegularityFunctionFieldNumber.specMap ψE ∅) ↔ v (chartHom r g) < 1) := by
    intro g a hg
    rw [RingHom.mem_ker, RegularityFunctionFieldNumber.specMap_form ψE ∅ hg, ← hψE, mul_eq_zero, MvPolynomial.C_eq_zero]
    refine or_iff_right (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ ?_)
    simp [RegularityFunctionFieldNumber.cS, MvPolynomial.X_ne_zero]
  have hWp : (RingHom.ker (RegularityFunctionFieldNumber.specMap ψE ∅)).IsPrime := RingHom.ker_isPrime _
  have hPW : P ≤ RingHom.ker (RegularityFunctionFieldNumber.specMap ψE ∅) := by
    obtain ⟨S, hS, hPS⟩ := hPh
    refine hPS.le.trans (Ideal.span_le.mpr fun g hg => ?_)
    obtain ⟨a, ha⟩ := hS g hg
    have hgP : g ∈ P := hPS ▸ Ideal.subset_span hg
    rw [SetLike.mem_coe, hform g a ha]
    have h1 := chartHom_mul j r hr ha
    rw [toFrac_eq_zero.mpr hgP] at h1
    have hφ : chartHom r g = 0 :=
      Subtype.ext ((mul_eq_zero.mp h1).resolve_right (toFrac_prod_ne_zero j hjP a))
    rw [hφ, map_zero]
    exact zero_lt_one
  have hC : IsMultiHomog (C n : MRing ι) 0 := fun μ hμ k => by
    rw [mem_support_iff, coeff_C] at hμ
    split_ifs at hμ with h
    · subst h
      simp
    · exact absurd rfl hμ
  refine ⟨RingHom.ker (RegularityFunctionFieldNumber.specMap ψE ∅),
    ⟨hWp, RegularityValuationCentre.ker_isMultiHomogIdeal ψE, fun k => ⟨j k, ?_⟩⟩, hPW, ?_, fun z hz => ?_⟩
  ·
    have hrj : r ⟨k, j k⟩ = 1 :=
      Subtype.ext (mul_right_cancel₀ (hX0 (hjP k)) ((hr ⟨k, j k⟩).trans (one_mul _).symm))
    rw [hform _ _ (isMultiHomog_X_single k (j k))]
    have hXr : chartHom r (X ⟨k, j k⟩) = r ⟨k, j k⟩ := eval₂Hom_X' _ _ _
    rw [hXr, hrj, Valuation.map_one]
    exact lt_irrefl 1
  · rw [hform _ 0 hC]
    have hCn : chartHom r (C n) = (n : funField P) := eval₂Hom_C _ _ _
    rw [hCn]
    exact hn
  ·
    obtain ⟨u, w, a, hu, hw, hwW, e⟩ := LocRingFrac.proof K ι P _ hPp hWp hPW z hz
    have hzw : z * chartHom r w = chartHom r u :=
      Subtype.ext <| mul_right_cancel₀ (toFrac_prod_ne_zero j hjP a) <| by
        rw [Subring.coe_mul, mul_assoc, chartHom_mul j r hr hw, chartHom_mul j r hr hu]
        exact e
    have hvw : v (chartHom r w) = 1 :=
      le_antisymm (hψle w) (not_lt.mp fun h => hwW ((hform w a hw).mpr h))
    have h1 := congrArg v hzw
    rw [map_mul, hvw, mul_one] at h1
    exact h1 ▸ hψle u

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PBCMult
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial IsLocalRing
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing)

noncomputable section

namespace BCMultProof

theorem length_quot_map_of_flat {A L : Type*} [CommRing A] [IsLocalRing A] [CommRing L]
    [IsLocalRing L] (φ : A →+* L) [IsLocalHom φ] (hflat : φ.Flat)
    (hmax : (maximalIdeal A).map φ = maximalIdeal L) (J : Ideal A) :
    Module.length L (L ⧸ J.map φ) = Module.length A (A ⧸ J) := by
  let _ := φ.toAlgebra
  have : Module.Flat A L := hflat
  have : IsLocalHom (algebraMap A L) := ‹IsLocalHom φ›
  have key := IsLocalRing.length_baseChange A L (A ⧸ J)
  rw [← (Algebra.TensorProduct.quotIdealMapEquivTensorQuot L J).toLinearEquiv.length_eq,
    RingHom.algebraMap_toAlgebra, hmax] at key
  have h1 : Module.length L (L ⧸ maximalIdeal L) = 1 :=
    Module.length_eq_one_iff.mpr
      (isSimpleModule_iff_quot_maximal.mpr ⟨_, inferInstance, ⟨LinearEquiv.refl _ _⟩⟩)
  rw [h1, mul_one] at key
  exact key

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [DecidableEq K] in

theorem flat_map : (MvPolynomial.map (algebraMap ℚ ℂ) : MRing ι ℚ →+* MRing ι ℂ).Flat :=
  ReciprocityTheory.AnForm.R.BaseChangeC.flat_mvPolynomial_rat_complex (σ := Σ k, ι k)

end BCMultProof

open BCMultProof BaseChange

theorem BCMult.intersectionNumber_baseChange : BCMult.Statement := by
  intro K _ _ ι _ P0 e s a W Wa hP hs hsP hW hWa
  classical
  have := hP.1.isPrime
  have : W.IsPrime := hW.1.1.1
  have : Wa.IsPrime := hWa.1.1
  have hWc : Wa.comap (MvPolynomial.map (algebraMap ℚ ℂ)) = W :=
    ReciprocityTheory.AnForm.R.comap_of_mem_minimalPrimes_extC W Wa hWa
  have hrel : NumbersDVR.IsRelevant Wa := isRelevant_of_comap hW.2 hWc
  have hext : (P0 ⊔ Ideal.span {s}).map (MvPolynomial.map (algebraMap ℚ ℂ)) =
      extC P0 ⊔ Ideal.span {sC s} := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
    rfl

  have hWaMin : Wa ∈ (extC P0 ⊔ Ideal.span {sC s}).minimalPrimes := by
    rw [← hext]
    refine ⟨⟨‹Wa.IsPrime›, (Ideal.map_mono hW.1.1.2).trans hWa.1.2⟩, fun Q hQ hQWa => ?_⟩
    have : Q.IsPrime := hQ.1
    have hle : Q.comap (MvPolynomial.map (algebraMap ℚ ℂ)) ≤ W := hWc ▸ Ideal.comap_mono hQWa
    have hge : W ≤ Q.comap (MvPolynomial.map (algebraMap ℚ ℂ)) :=
      hW.1.2 ⟨Ideal.IsPrime.comap _, Ideal.map_le_iff_le_comap.mp hQ.2⟩ hle
    exact hWa.2 ⟨this, Ideal.map_le_iff_le_comap.mpr hge⟩ hQWa

  have hcomp : (Localization.localRingHom W Wa (MvPolynomial.map (algebraMap ℚ ℂ)) hWc.symm).comp
      (algebraMap (MRing ι ℚ) (Localization.AtPrime W)) =
      (algebraMap (MRing ι ℂ) (Localization.AtPrime Wa)).comp
        (MvPolynomial.map (algebraMap ℚ ℂ)) :=
    RingHom.ext fun z => Localization.localRingHom_to_map _ _ _ hWc.symm z
  have hmaxL : (maximalIdeal (Localization.AtPrime W)).map
      (Localization.localRingHom W Wa (MvPolynomial.map (algebraMap ℚ ℂ)) hWc.symm) =
      maximalIdeal (Localization.AtPrime Wa) := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal W (Localization.AtPrime W), Ideal.map_map, hcomp,
      ← Ideal.map_map]
    exact map_eq_maximalIdeal_of_isRadical (ReciprocityTheory.AnForm.R.extC_isRadical W) hWa
  have hflat := length_quot_map_of_flat
    (Localization.localRingHom W Wa (MvPolynomial.map (algebraMap ℚ ℂ)) hWc.symm)
    (RingHom.Flat.localRingHom flat_map Wa W hWc.symm) hmaxL
    ((P0 ⊔ Ideal.span {s}).map (algebraMap (MRing ι ℚ) (Localization.AtPrime W)))
  have hJ : ((P0 ⊔ Ideal.span {s}).map (algebraMap (MRing ι ℚ) (Localization.AtPrime W))).map
      (Localization.localRingHom W Wa (MvPolynomial.map (algebraMap ℚ ℂ)) hWc.symm) =
      (extC P0 ⊔ Ideal.span {sC s}).map (algebraMap (MRing ι ℂ) (Localization.AtPrime Wa)) := by
    rw [Ideal.map_map, hcomp, ← Ideal.map_map, hext]
  have h1 : NumbersDVR.multAt (P0 ⊔ Ideal.span {s}) W =
      NumbersDVR.multAt (extC P0 ⊔ Ideal.span {sC s}) Wa := by
    unfold NumbersDVR.multAt
    rw [ObjectsChow.VerticalPartMultiplicity.length_localizedModule_quotient,
      ObjectsChow.VerticalPartMultiplicity.length_localizedModule_quotient, ← hJ, hflat]

  have h2 : NumbersDVR.multAt (extC P0 ⊔ Ideal.span {sC s}) Wa =
      ∑ᶠ Z ∈ (extC P0).minimalPrimes, NumbersDVR.multAt (Z ⊔ Ideal.span {sC s}) Wa :=
    ReducedCutLength.intersectionNumber_baseChange (MRing ι ℂ) (extC P0) (sC s) Wa (ReciprocityTheory.AnForm.R.extC_isRadical P0)
      (fun _ hZ => sC_not_mem (comap_extC hZ) hsP) hWaMin
  have hfin : NumbersDVR.multAt (extC P0 ⊔ Ideal.span {sC s}) Wa ≠ ⊤ :=
    NumbersDVR.length_localizedQuot_ne_top _ Wa hWaMin

  have hterm : ∀ Z ∈ (extC P0).minimalPrimes, NumbersDVR.divCycle Z (sC s) Wa =
      ((NumbersDVR.multAt (Z ⊔ Ideal.span {sC s}) Wa).toNat : ℤ) := by
    intro Z hZ
    unfold NumbersDVR.divCycle
    by_cases hZW : Z ⊔ Ideal.span {sC s} ≤ Wa
    · have hm : Wa ∈ (Z ⊔ Ideal.span {sC s}).minimalPrimes :=
        ⟨⟨‹Wa.IsPrime›, hZW⟩, fun Q hQ hQW =>
          hWaMin.2 ⟨hQ.1, (sup_le_sup_right hZ.1.2 _).trans hQ.2⟩ hQW⟩
      rw [dif_pos ⟨hm, hrel⟩]
    · rw [dif_neg (fun h => hZW h.1.1.2)]
      unfold NumbersDVR.multAt
      rw [Module.length_eq_zero_iff.mpr (NumbersDVR.localizedQuot_subsingleton_of_not_le _ Wa hZW)]
      rfl
  have hL : NumbersDVR.divCycle P0 s W =
      ((NumbersDVR.multAt (P0 ⊔ Ideal.span {s}) W).toNat : ℤ) := by
    unfold NumbersDVR.divCycle
    rw [dif_pos (show W ∈ (P0 ⊔ Ideal.span {s}).minimalPrimes ∧ NumbersDVR.IsRelevant W from hW)]
  have hM : (extC P0).minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ _
  rw [hL, finsum_mem_congr rfl hterm, h1, h2]
  rw [h2] at hfin
  rw [finsum_mem_eq_finite_toFinset_sum _ hM] at hfin ⊢
  rw [ENat.toNat_sum fun Z hZ hZt => hfin (top_unique
    (hZt ▸ Finset.single_le_sum (fun _ _ => zero_le) hZ)), Nat.cast_sum,
    finsum_mem_eq_finite_toFinset_sum _ hM]

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PLocRingIntClosure
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

open Classical in

theorem subfield_closure_coords_eq_top {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
    (P' : Ideal (MRing ι')) [P'.IsPrime] :
    Subfield.closure ((Finset.univ.image fun q : Σ k, ι' k =>
      algebraMap (MRing ι' ⧸ P') (FractionRing (MRing ι' ⧸ P')) (Ideal.Quotient.mk P' (X q)) :
        Finset (FractionRing (MRing ι' ⧸ P'))) : Set (FractionRing (MRing ι' ⧸ P'))) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := MRing ι' ⧸ P') x
  have h : ∀ f : MRing ι', algebraMap (MRing ι' ⧸ P') (FractionRing (MRing ι' ⧸ P')) (Ideal.Quotient.mk P' f) ∈
      Subfield.closure ((Finset.univ.image fun q : Σ k, ι' k =>
        algebraMap (MRing ι' ⧸ P') (FractionRing (MRing ι' ⧸ P')) (Ideal.Quotient.mk P' (X q)) :
          Finset (FractionRing (MRing ι' ⧸ P'))) : Set (FractionRing (MRing ι' ⧸ P'))) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C r => rw [eq_intCast C r, map_intCast, map_intCast]; exact intCast_mem _ r
    | add f g hf hg => rw [map_add, map_add]; exact add_mem hf hg
    | mul_X f q hf =>
      rw [map_mul, map_mul]
      exact mul_mem hf (Subfield.subset_closure (by simp))
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective b
  exact div_mem (h f) (h g)

theorem LocRingIntClosureFinite.proof (h₁ : LocRingChartLoc.Statement) (h₂ : IntClosureLocFinite.Statement) :
    LocRingIntClosureFinite.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n s α W _hv hP' _hQ _hs _hsQ hW
  have := hP'.2.1.1
  have := imageZ_isPrime_of_prime v P'
  obtain ⟨T, hTA, hloc⟩ := h₁ K ι (imageZ v P') W hW.1.1.1 (le_sup_left.trans hW.1.1.2) hW.2
  obtain ⟨t, ht⟩ := h₂ _ _ (fracMapZ v P') _ (subfield_closure_coords_eq_top P') _ T hTA hloc
  exact ⟨t, fun x _ hx => ht x hx⟩

end GroundTheory.Heights₂.Heights.Inter
end
end

