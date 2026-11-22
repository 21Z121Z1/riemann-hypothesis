import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0020
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0017
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0021
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.MemDivSuppOfDivCycleNeZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0018
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0023

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.LogCardLocIdealUnitMul
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem card_quot_span_mul {S : Type*} [CommRing S] [IsDomain S] (u v : S) (hu : u ≠ 0) :
    Nat.card (S ⧸ Ideal.span {u * v}) = Nat.card (S ⧸ Ideal.span {u}) * Nat.card (S ⧸ Ideal.span {v}) := by
  let f : S →+ S := AddMonoidHom.mulLeft u
  have hf : Function.Injective f := fun a b h => mul_left_cancel₀ hu h
  have e1 : (Ideal.span {v}).toAddSubgroup.map f = (Ideal.span {u * v}).toAddSubgroup := by
    ext z
    simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨_, ⟨r, rfl⟩, rfl⟩
      exact ⟨r, by simp only [f, AddMonoidHom.coe_mulLeft]; ring⟩
    · rintro ⟨r, rfl⟩
      exact ⟨r * v, ⟨r, rfl⟩, by simp only [f, AddMonoidHom.coe_mulLeft]; ring⟩
  have e2 : (⊤ : AddSubgroup S).map f = (Ideal.span {u}).toAddSubgroup := by
    ext z
    simp only [AddSubgroup.mem_map, AddSubgroup.mem_top, true_and, Submodule.mem_toAddSubgroup,
      Ideal.mem_span_singleton', f, AddMonoidHom.coe_mulLeft]
    exact ⟨fun ⟨y, hy⟩ => ⟨y, by rw [← hy, mul_comm]⟩, fun ⟨r, hr⟩ => ⟨r, by rw [← hr, mul_comm]⟩⟩
  have hle : (Ideal.span {u * v}).toAddSubgroup ≤ (Ideal.span {u}).toAddSubgroup :=
    fun z hz => Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_right u v) hz
  have h2 : (Ideal.span {u * v}).toAddSubgroup.relIndex (Ideal.span {u}).toAddSubgroup =
      (Ideal.span {v}).toAddSubgroup.index := by
    rw [← e1, ← e2, AddSubgroup.relIndex_map_map_of_injective _ _ hf, AddSubgroup.relIndex_top_right]
  have hc : ∀ I : Ideal S, Nat.card (S ⧸ I) = I.toAddSubgroup.index :=
    fun I => (AddSubgroup.index_eq_card _).symm
  rw [hc, hc, hc, ← AddSubgroup.relIndex_mul_index hle, h2, mul_comm]

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem log_card_locIdeal_mul {P W : Ideal (MRing ι)} [P.IsPrime] {y₁ y₂ : FractionRing (MRing ι ⧸ P)}
    (h₁ : y₁ ∈ locRing P W) (h₂ : y₂ ∈ locRing P W) (hne : y₁ ≠ 0)
    (hf₁ : Finite (locRing P W ⧸ locIdeal P W y₁)) (hf₂ : Finite (locRing P W ⧸ locIdeal P W y₂)) :
    Real.log (Nat.card (locRing P W ⧸ locIdeal P W (y₁ * y₂))) =
      Real.log (Nat.card (locRing P W ⧸ locIdeal P W y₁)) + Real.log (Nat.card (locRing P W ⧸ locIdeal P W y₂)) := by
  rw [locIdeal_eq_span h₁] at hf₁ ⊢
  rw [locIdeal_eq_span h₂] at hf₂ ⊢
  rw [locIdeal_eq_span (mul_mem h₁ h₂)]
  have : (⟨y₁ * y₂, mul_mem h₁ h₂⟩ : locRing P W) = ⟨y₁, h₁⟩ * ⟨y₂, h₂⟩ := rfl
  rw [this, card_quot_span_mul _ _ (fun h => hne (congrArg Subtype.val h)), Nat.cast_mul,
    Real.log_mul (Nat.cast_ne_zero.mpr Nat.card_pos.ne') (Nat.cast_ne_zero.mpr Nat.card_pos.ne')]

theorem log_card_locIdeal_unit {P W : Ideal (MRing ι)} [P.IsPrime] {y z : FractionRing (MRing ι ⧸ P)}
    (hy : y ∈ locRing P W) (hz : z ∈ locRing P W) (h : y * z = 1) :
    Real.log (Nat.card (locRing P W ⧸ locIdeal P W y)) = 0 := by
  rw [locIdeal_eq_span hy, Ideal.span_singleton_eq_top.mpr
    (IsUnit.of_mul_eq_one (⟨z, hz⟩ : locRing P W) (Subtype.ext h))]
  have : Subsingleton (locRing P W ⧸ (⊤ : Ideal (locRing P W))) := Ideal.Quotient.subsingleton_iff.mpr rfl
  rw [Nat.card_of_subsingleton (0 : locRing P W ⧸ (⊤ : Ideal (locRing P W)))]
  simp

theorem log_card_locIdeal_unit_mul {P W : Ideal (MRing ι)} [P.IsPrime] {y z c : FractionRing (MRing ι ⧸ P)}
    (hy : y ∈ locRing P W) (hz : z ∈ locRing P W) (h : y * z = 1) (hc : c ∈ locRing P W) :
    Real.log (Nat.card (locRing P W ⧸ locIdeal P W (y * c))) =
      Real.log (Nat.card (locRing P W ⧸ locIdeal P W c)) := by
  rw [locIdeal_eq_span (mul_mem hy hc), locIdeal_eq_span hc]
  have : (⟨y * c, mul_mem hy hc⟩ : locRing P W) = ⟨y, hy⟩ * ⟨c, hc⟩ := rfl
  rw [this, Ideal.span_singleton_mul_left_unit (IsUnit.of_mul_eq_one (⟨z, hz⟩ : locRing P W) (Subtype.ext h))]

theorem frac_mem_locRing {P W : Ideal (MRing ι)} (hPW : P ≤ W) {u v : MRing ι} {a : K → ℕ}
    (hu : IsMultiHomog u a) (hv : IsMultiHomog v a) (hvW : v ∉ W) [P.IsPrime] {y : FractionRing (MRing ι ⧸ P)}
    (hy : y * algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P v) =
      algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u)) :
    y ∈ locRing P W := by
  have hvP : Ideal.Quotient.mk P v ∈ nonZeroDivisors (MRing ι ⧸ P) :=
    mem_nonZeroDivisors_of_ne_zero (by rw [Ne, Ideal.Quotient.eq_zero_iff_mem]; exact fun h => hvW (hPW h))
  exact Subring.subset_closure ⟨u, v, a, hvP, hvW, hu, hv, IsLocalization.eq_mk'_iff_mul_eq.mpr hy⟩

theorem frac_unit_locRing {P W : Ideal (MRing ι)} (hPW : P ≤ W) {u v : MRing ι} {a : K → ℕ}
    (hu : IsMultiHomog u a) (hv : IsMultiHomog v a) (huW : u ∉ W) (hvW : v ∉ W) [P.IsPrime]
    {y : FractionRing (MRing ι ⧸ P)}
    (hy : y * algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P v) =
      algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u)) :
    y ∈ locRing P W ∧ ∃ z ∈ locRing P W, y * z = 1 := by
  have hu0 : algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u) ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
    exact fun h => huW (hPW h)
  have hv0 : algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P v) ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
    exact fun h => hvW (hPW h)
  set z := algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P v) /
    algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u)
  refine ⟨frac_mem_locRing hPW hu hv hvW hy, z, frac_mem_locRing hPW hv hu huW (div_mul_cancel₀ _ hu0), ?_⟩
  rw [mul_div_assoc', hy, div_self hu0]

theorem RegularityLocalProduct.proof (hN : RegularityFunctionFieldNumber.Statement) (hR : RegularityFormula.Statement)
    (hD : RegularityDenominator.Statement) (hC : RegularityDivisorSupportClosed.Statement) (hF : RegularityLocalFinite.Statement) :
    RegularityLocalProduct.Statement := by
  classical
  intro K _ ι _ P f g a x t yf yg hP hf hg hfP hgP hx ht
  have : P.IsPrime := hP.2.1.1
  obtain ⟨c, hc0, hcW⟩ := hD K ι P x hP
  have hφ : ∀ s, s ∉ P → algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P s) ≠ 0 :=
    fun s hs => by rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]; exact hs
  have hx0 : x ≠ 0 := fun h => hφ f hfP (by rw [← hx, h]; simp)
  have hb0 : x * c ≠ 0 := mul_ne_zero hx0 hc0
  have hxc : ((x * c : funField P) : FractionRing (MRing ι ⧸ P)) = x * c := rfl
  have hmem : ∀ {s : MRing ι} {W}, IsMultiHomog s a → s ∉ P → IsClosedPt W → P ≤ W → (W ∈ divSupp P s ↔ s ∈ W) :=
    fun hs hsP hWc hPW => (hC K ι P _ a _ hP hs hsP).trans ⟨fun h => h.2.2, fun h => ⟨hWc, hPW, h⟩⟩
  have key : ∀ W, IsClosedPt W → P ≤ W →
      (if W ∈ divSupp P f then Real.log (Nat.card (locRing P W ⧸ locIdeal P W (yf W))) else 0) -
          (if W ∈ divSupp P g then Real.log (Nat.card (locRing P W ⧸ locIdeal P W (yg W))) else 0) =
        Real.log (Nat.card (locRing P W ⧸ locIdeal P W ((x * c : funField P) : FractionRing (MRing ι ⧸ P)))) -
          Real.log (Nat.card (locRing P W ⧸ locIdeal P W (c : FractionRing (MRing ι ⧸ P)))) := by
    intro W hWc hPW
    obtain ⟨hcS, hbS⟩ := hcW W hWc hPW
    by_cases hU : W ∈ divSupp P f ∪ divSupp P g
    · obtain ⟨htW, htn, hyf, hyg⟩ := ht W hU
      have hyfS := frac_mem_locRing hPW hf htW htn hyf
      have hygS := frac_mem_locRing hPW hg htW htn hyg
      have hyf0 : yf W ≠ 0 := fun h => hφ f hfP (by rw [← hyf, h, zero_mul])
      have hyg0 : yg W ≠ 0 := fun h => hφ g hgP (by rw [← hyg, h, zero_mul])
      have hrel : yf W = x * yg W :=
        mul_right_cancel₀ (hφ _ fun h => htn (hPW h)) (by rw [hyf, mul_assoc, hyg, hx])
      obtain ⟨s, hs, hsP, hWs⟩ : ∃ s, IsMultiHomog s a ∧ s ∉ P ∧ W ∈ divSupp P s := by
        rcases hU with h | h
        exacts [⟨f, hf, hfP, h⟩, ⟨g, hg, hgP, h⟩]
      have fin : ∀ y, y ∈ locRing P W → y ≠ 0 → Finite (locRing P W ⧸ locIdeal P W y) :=
        fun y hy hy0 => hF K ι P s a W y hP hs hsP hWs hy hy0
      have hc0' : (c : FractionRing (MRing ι ⧸ P)) ≠ 0 := fun h => hc0 (Subtype.ext h)
      have hb0' : ((x * c : funField P) : FractionRing (MRing ι ⧸ P)) ≠ 0 := fun h => hb0 (Subtype.ext h)
      have e : yf W * c = ((x * c : funField P) : FractionRing (MRing ι ⧸ P)) * yg W := by
        rw [hrel, hxc]; ring
      have hm := log_card_locIdeal_mul hyfS hcS hyf0 (fin _ hyfS hyf0) (fin _ hcS hc0')
      have hm' := log_card_locIdeal_mul hbS hygS hb0' (fin _ hbS hb0') (fin _ hygS hyg0)
      rw [e] at hm
      by_cases h1 : W ∈ divSupp P f <;> by_cases h2 : W ∈ divSupp P g
      · rw [if_pos h1, if_pos h2]; linarith
      · obtain ⟨-, z, hz, hz1⟩ := frac_unit_locRing hPW hg htW (fun h => h2 ((hmem hg hgP hWc hPW).mpr h)) htn hyg
        have := log_card_locIdeal_unit hygS hz hz1
        rw [if_pos h1, if_neg h2]; linarith
      · obtain ⟨-, z, hz, hz1⟩ := frac_unit_locRing hPW hf htW (fun h => h1 ((hmem hf hfP hWc hPW).mpr h)) htn hyf
        have := log_card_locIdeal_unit hyfS hz hz1
        rw [if_neg h1, if_pos h2]; linarith
      · exact absurd hU (by simp [h1, h2])
    · have h1 : W ∉ divSupp P f := fun h => hU (Or.inl h)
      have h2 : W ∉ divSupp P g := fun h => hU (Or.inr h)
      obtain ⟨hxS, z, hz, hz1⟩ := frac_unit_locRing hPW hf hg (fun h => h1 ((hmem hf hfP hWc hPW).mpr h))
        (fun h => h2 ((hmem hg hgP hWc hPW).mpr h)) hx
      rw [if_neg h1, if_neg h2, hxc, log_card_locIdeal_unit_mul hxS hz hz1 hcS]
      ring
  obtain ⟨hbfin, hbsum⟩ := hR K ι P (x * c) hP hb0 (fun W h1 h2 => (hcW W h1 h2).2)
  obtain ⟨hcfin, hcsum⟩ := hR K ι P c hP hc0 (fun W h1 h2 => (hcW W h1 h2).1)
  have eq1 : ∀ (s : MRing ι) (y : Ideal (MRing ι) → FractionRing (MRing ι ⧸ P)),
      ∑ᶠ W ∈ divSupp P s, Real.log (Nat.card (locRing P W ⧸ locIdeal P W (y W))) =
        ∑ᶠ W, (if W ∈ divSupp P s then Real.log (Nat.card (locRing P W ⧸ locIdeal P W (y W))) else 0) := by
    intro s y
    rw [finsum_mem_def]
    rfl
  have fsA : ∀ (s : MRing ι) (y : Ideal (MRing ι) → FractionRing (MRing ι ⧸ P)),
      (Function.support fun W =>
        if W ∈ divSupp P s then Real.log (Nat.card (locRing P W ⧸ locIdeal P W (y W))) else 0).Finite :=
    fun s y => (divSupp_finite P s).subset fun W hW => by
      by_contra h
      exact hW (if_neg h)
  have fsB : ∀ z : FractionRing (MRing ι ⧸ P),
      {W | IsClosedPt W ∧ P ≤ W ∧ Nat.card (locRing P W ⧸ locIdeal P W z) ≠ 1}.Finite →
      (Function.support ({W : Ideal (MRing ι) | IsClosedPt W ∧ P ≤ W}.indicator
        fun W => Real.log (Nat.card (locRing P W ⧸ locIdeal P W z)))).Finite :=
    fun z hz => hz.subset fun W hW => by
      rw [Function.mem_support] at hW
      by_cases hWC : W ∈ {W : Ideal (MRing ι) | IsClosedPt W ∧ P ≤ W}
      · rw [Set.indicator_of_mem hWC] at hW
        exact ⟨hWC.1, hWC.2, fun h1 => hW (by rw [h1]; simp)⟩
      · rw [Set.indicator_of_notMem hWC] at hW
        exact absurd rfl hW
  obtain ⟨hFld, hNF⟩ := hN K ι P hP
  let _ := hFld.toField
  have hσ : ∀ y : funField P, y ≠ 0 → ∀ σ : funField P →+* ℂ, σ y ≠ 0 := fun y hy σ h => by
    obtain ⟨z, hz⟩ := hFld.mul_inv_cancel hy
    have := congrArg σ hz
    rw [map_mul, h, zero_mul, map_one] at this
    exact zero_ne_one this
  calc _ = ∑ᶠ W, ((if W ∈ divSupp P f then Real.log (Nat.card (locRing P W ⧸ locIdeal P W (yf W))) else 0) -
          (if W ∈ divSupp P g then Real.log (Nat.card (locRing P W ⧸ locIdeal P W (yg W))) else 0)) := by
        rw [eq1 f yf, eq1 g yg, finsum_sub_distrib (fsA f yf) (fsA g yg)]
    _ = ∑ᶠ W, ({W : Ideal (MRing ι) | IsClosedPt W ∧ P ≤ W}.indicator
            (fun W => Real.log (Nat.card (locRing P W ⧸
              locIdeal P W ((x * c : funField P) : FractionRing (MRing ι ⧸ P))))) W -
          {W : Ideal (MRing ι) | IsClosedPt W ∧ P ≤ W}.indicator
            (fun W => Real.log (Nat.card (locRing P W ⧸ locIdeal P W (c : FractionRing (MRing ι ⧸ P))))) W) := by
        refine finsum_congr fun W => ?_
        by_cases hWC : W ∈ {W : Ideal (MRing ι) | IsClosedPt W ∧ P ≤ W}
        · rw [Set.indicator_of_mem hWC, Set.indicator_of_mem hWC]
          exact key W hWC.1 hWC.2
        · rw [Set.indicator_of_notMem hWC, Set.indicator_of_notMem hWC,
            if_neg fun h => hWC ⟨((hC K ι P f a W hP hf hfP).mp h).1, ((hC K ι P f a W hP hf hfP).mp h).2.1⟩,
            if_neg fun h => hWC ⟨((hC K ι P g a W hP hg hgP).mp h).1, ((hC K ι P g a W hP hg hgP).mp h).2.1⟩]
    _ = ∑ᶠ σ : funField P →+* ℂ, Real.log ‖σ (x * c)‖ - ∑ᶠ σ : funField P →+* ℂ, Real.log ‖σ c‖ := by
        rw [finsum_sub_distrib (fsB _ hbfin) (fsB _ hcfin), ← finsum_mem_def, ← finsum_mem_def, hbsum, hcsum]
    _ = _ := by
        rw [← finsum_sub_distrib (Set.toFinite _) (Set.toFinite _)]
        refine finsum_congr fun σ => ?_
        rw [map_mul, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr (hσ x hx0 σ)) (norm_ne_zero_iff.mpr (hσ c hc0 σ))]
        ring

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.NotIsHorizontalOfDimOne
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

section Cycles

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem mem_of_mem_divSupp' {P W : Ideal (MRing ι)} {f : MRing ι} (hW : W ∈ divSupp P f) : f ∈ W :=
  hW.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))

theorem mem_divSupp_mul_left' {P W : Ideal (MRing ι)} (hP : P.IsPrime) {f g : MRing ι}
    (hgP : g ∉ P) (hW : W ∈ divSupp P f) : W ∈ divSupp P (f * g) := by
  refine ⟨⟨⟨hW.1.1.1, (sup_span_mul_le P f g).trans hW.1.1.2⟩, fun Q hQ hQW => ?_⟩, hW.2⟩
  have hfg : f * g ∈ Q := hQ.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  rcases hQ.1.mem_or_mem hfg with hf | hg
  · exact hW.1.2 ⟨hQ.1, sup_le (le_sup_left.trans hQ.2) (Ideal.span_singleton_le_iff_mem _ |>.mpr hf)⟩
      hQW
  · exact (eq_of_le_of_mem_minimalPrimes hP hW.1 hQ.1 (le_sup_left.trans hQ.2) hg hgP hQW).ge

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem mem_divSupp_of_mul' {P W : Ideal (MRing ι)} {f g : MRing ι}
    (hW : W ∈ divSupp P (f * g)) (hf : f ∈ W) : W ∈ divSupp P f :=
  ⟨⟨⟨hW.1.1.1, sup_le (le_sup_left.trans hW.1.1.2) (Ideal.span_singleton_le_iff_mem _ |>.mpr hf)⟩,
    fun _ hQ hQW => hW.1.2 ⟨hQ.1, (sup_span_mul_le P f g).trans hQ.2⟩ hQW⟩, hW.2⟩

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem multAt_eq' (J W : Ideal (MRing ι)) (hW : W.IsPrime) :
    multAt J W = (locLen (MRing ι ⧸ J) ⟨W, hW⟩).toNat := by
  simp [multAt, hW, locLen]

theorem divCycle_mul' {P : Ideal (MRing ι)} (hP : P.IsPrime) {f g : MRing ι}
    (hf : f ∉ P) (hg : g ∉ P) : divCycle P (f * g) = divCycle P f + divCycle P g := by
  classical
  ext W
  simp only [Finsupp.add_apply, divCycle, Finsupp.ofSupportFinite_coe]
  by_cases h : W ∈ divSupp P (f * g)
  · have hWp := h.1.1.1
    have h' : W ∈ divSupp P (g * f) := by rwa [mul_comm]
    have key := locLen_mul hP hf g ⟨W, hWp⟩
    have hfin := locLen_ne_top h.1
    rw [key] at hfin
    rw [if_pos h, multAt_eq' _ _ hWp, key]
    by_cases hfW : f ∈ W <;> by_cases hgW : g ∈ W
    · rw [if_pos (mem_divSupp_of_mul' h hfW), if_pos (mem_divSupp_of_mul' h' hgW),
        multAt_eq' _ _ hWp, multAt_eq' _ _ hWp, ENat.toNat_add (WithTop.add_ne_top.mp hfin).1
          (WithTop.add_ne_top.mp hfin).2, add_comm]
    · rw [if_pos (mem_divSupp_of_mul' h hfW), if_neg fun h2 => hgW (mem_of_mem_divSupp' h2),
        multAt_eq' _ _ hWp, locLen_quot_eq_zero _ hgW, zero_add, add_zero]
    · rw [if_neg fun h2 => hfW (mem_of_mem_divSupp' h2), if_pos (mem_divSupp_of_mul' h' hgW),
        multAt_eq' _ _ hWp, locLen_quot_eq_zero (V := P) (g := f) _ hfW, add_zero, zero_add]
    · exact absurd (hWp.mem_or_mem (mem_of_mem_divSupp' h)) (by tauto)
  · rw [if_neg h, if_neg fun h2 => h (mem_divSupp_mul_left' hP hg h2),
      if_neg fun h2 => h (by rw [mul_comm]; exact mem_divSupp_mul_left' hP hf h2)]

open Classical in

def cycWeight (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) {n : ℕ}
    (L : Fin n → HermLine ι) (W : Ideal (MRing ι)) : ℝ :=
  if IsHorizontal W then I W n L else (geoNum n W (fun j => (L j).a) : ℝ) * Real.log (charOf W)

theorem cycR_eq_sum (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι))
    {n : ℕ} (L : Fin n → HermLine ι) (s : MRing ι) :
    cycR I P L s = (divCycle P s).sum fun W m => (m : ℝ) * cycWeight I L W := by
  classical
  unfold cycR
  rw [finsum_mem_def, finsum_eq_sum_of_support_subset _ (s := (divCycle P s).support)]
  · refine Finset.sum_congr rfl fun W _ => ?_
    by_cases h : W ∈ divSupp P s
    · simp [Set.indicator, h, divCycle, Finsupp.ofSupportFinite_coe, cycWeight]
    · simp [Set.indicator, h, divCycle, Finsupp.ofSupportFinite_coe]
  · intro W hW
    rw [Function.mem_support] at hW
    rw [Finset.mem_coe, Finsupp.mem_support_iff]
    intro h0
    apply hW
    by_cases h : W ∈ divSupp P s
    · have : multAt (P ⊔ Ideal.span {s}) W = 0 := by
        simpa [divCycle, Finsupp.ofSupportFinite_coe, h] using h0
      simp [Set.indicator, h, this]
    · simp [Set.indicator, h]

theorem cycR_mul (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) {P : Ideal (MRing ι)}
    (hP : P.IsPrime) {n : ℕ} (L : Fin n → HermLine ι) {s t : MRing ι} (hs : s ∉ P) (ht : t ∉ P) :
    cycR I P L (s * t) = cycR I P L s + cycR I P L t := by
  rw [cycR_eq_sum, cycR_eq_sum, cycR_eq_sum, divCycle_mul' hP hs ht]
  exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by push_cast; ring)

end Cycles

section NoHorizontal

theorem not_isHorizontal_of_dimOne (h0 : ArithVarZeroStatement) {P : Ideal (MRing ι)} {A : HermLine ι}
    {s : MRing ι} {W : Ideal (MRing ι)} (hP : IsArithVar P 1) (hs : IsSectionOn P A s)
    (hW : W ∈ divSupp P s) : ¬ IsHorizontal W := fun hh =>
  h0 K ι W ((divSuppArith K ι P 0 A s W hP hs hW).1 hh)

theorem eval_ne_zero_of_dimOne (h0 : ArithVarZeroStatement) {P : Ideal (MRing ι)} {A : HermLine ι}
    {s : MRing ι} (hP : IsArithVar P 1) (hs : IsSectionOn P A s) {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts P) : eval z (map (Int.castRingHom ℂ) s) ≠ 0 := by
  intro hzero
  let φ : MRing ι →+* ℂ := (eval z).comp (map (Int.castRingHom ℂ))
  have hQ : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  have hle : P ⊔ Ideal.span {s} ≤ RingHom.ker φ := by
    refine sup_le (fun f hf => ?_) ?_
    · rw [RingHom.mem_ker]
      exact hz.2 f hf
    · rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
      exact hzero
  obtain ⟨W, hW, hWQ⟩ := Ideal.exists_minimalPrimes_le hle
  have hrel : IsRelevant W := fun k => by
    obtain ⟨i, hi⟩ := hz.1 k
    refine ⟨i, fun hX => hi ?_⟩
    have h1 := hWQ hX
    rw [RingHom.mem_ker] at h1
    simpa [φ] using h1
  have hhor : IsHorizontal W := by
    unfold IsHorizontal
    refine eq_bot_iff.mpr fun n hn => ?_
    rw [Ideal.mem_comap] at hn
    have h1 := hWQ hn
    rw [RingHom.mem_ker] at h1
    simp [φ] at h1
    simp [h1]
  exact not_isHorizontal_of_dimOne h0 hP hs ⟨hW, hrel⟩ hhor

end NoHorizontal

section Integral

theorem ptsIntegral_add_of_dimOne (hFF : FibreFiniteStatement) {P : Ideal (MRing ι)}
    (hP : IsArithVar P 1) (φ : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ) {g g₁ g₂ : ((Σ k, ι k) → ℂ) → ℝ}
    (h : ∀ z ∈ mcPts P, g z = g₁ z + g₂ z) :
    ptsIntegral P φ g = ptsIntegral P φ g₁ + ptsIntegral P φ g₂ := by
  unfold ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    rw [MeasureTheory.integral_unique, MeasureTheory.integral_unique, MeasureTheory.integral_unique,
      ← smul_add]
    congr 1
    have hfin : ∀ y, (fibre P hΨ.choose y).Finite := hFF K ι P 0 hΨ.choose hP hΨ.choose_spec
    refine Eq.trans ?_ (finsum_mem_add_distrib' ((hfin _).subset Set.inter_subset_left)
      ((hfin _).subset Set.inter_subset_left))
    refine finsum_mem_congr rfl fun w _ => ?_
    unfold sheetDensity
    split_ifs with hγ
    · have hz : ∀ y : Fin 0 → ℂ, hγ.choose y ∈ mcPts P := fun y =>
        (Subsingleton.elim _ y) ▸ hγ.choose_spec.2.self_of_nhds.2.1
      rw [h _ (hz _), add_mul]
    · simp
  · simp

theorem arInt_mul_of_dimOne (h0 : ArithVarZeroStatement) (hFF : FibreFiniteStatement)
    {P : Ideal (MRing ι)} (hP : IsArithVar P 1) {A B : HermLine ι} {s t : MRing ι}
    (hs : IsSectionOn P A s) (ht : IsSectionOn P B t) :
    arInt P (s * t) (A.tensor B) (Fin.elim0 : Fin 0 → HermLine ι) =
      arInt P s A (Fin.elim0 : Fin 0 → HermLine ι) + arInt P t B (Fin.elim0 : Fin 0 → HermLine ι) := by
  unfold arInt
  refine ptsIntegral_add_of_dimOne hFF hP _ fun z hz => ?_
  have hs0 := eval_ne_zero_of_dimOne h0 hP hs hz
  have ht0 := eval_ne_zero_of_dimOne h0 hP ht hz
  have hA := A.pos z hz.1
  have hB := B.pos z hz.1
  unfold logNorm
  rw [show (A.tensor B).h z = A.h z * B.h z from rfl, map_mul, map_mul, norm_mul, mul_div_mul_comm]
  exact Real.log_mul (div_ne_zero (norm_ne_zero_iff.mpr hs0) hA.ne')
    (div_ne_zero (norm_ne_zero_iff.mpr ht0) hB.ne')

end Integral

theorem SpecIntHeightFormula.proof (h0 : ArithVarZeroStatement) : SpecIntHeightFormula.Statement := by
  intro K _ ι _ I P A s hP _ hs
  rw [recR_eq]
  congr 1
  unfold cycR vertR
  refine finsum_mem_congr rfl fun W hW => ?_
  simp [not_isHorizontal_of_dimOne h0 hP hs hW]

theorem RegularityAdditive.proof (h0 : ArithVarZeroStatement) (hFF : FibreFiniteStatement) : RegularityAdditive.Statement := by
  intro K _ ι _ I P A B s t hP _ _ hs ht
  obtain ⟨_, _, _, hsP⟩ := id hs
  obtain ⟨_, _, _, htP⟩ := id ht
  rw [recR_eq, recR_eq, recR_eq, cycR_mul I hP.2.1.1 _ hsP htP, arInt_mul_of_dimOne h0 hFF hP hs ht]
  ring

theorem cycR_eq_vertR_of_dimOne (h0 : ArithVarZeroStatement) (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ)
    {P : Ideal (MRing ι)} {A : HermLine ι} {s : MRing ι} (hP : IsArithVar P 1) (hs : IsSectionOn P A s) :
    cycR I P (Fin.elim0 : Fin 0 → HermLine ι) s = vertR P (Fin.elim0 : Fin 0 → HermLine ι) s := by
  unfold cycR vertR
  refine finsum_mem_congr rfl fun W hW => ?_
  simp [not_isHorizontal_of_dimOne h0 hP hs hW]

theorem RegularityIndependence.proof (h0 : ArithVarZeroStatement) (hFF : FibreFiniteStatement)
    (hPF : RegularityProductFormula.Statement) : RegularityIndependence.Statement := by
  intro K _ ι _ I P A s t hP hs ht
  obtain ⟨a, ha, hsa, hsP⟩ := id hs
  obtain ⟨b, hb, htb, htP⟩ := id ht
  have hab : b = a := funext fun k => by exact_mod_cast (hb k).symm.trans (ha k)
  subst hab
  have hφ : (fun (j : Fin 0) (z : (Σ k, ι k) → ℂ) => Real.log (((Fin.elim0 : Fin 0 → HermLine ι) j).h z)) =
      (Fin.elim0 : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ) := funext fun j => j.elim0
  have hsplit : arInt P s A (Fin.elim0 : Fin 0 → HermLine ι) =
      ptsIntegral P (Fin.elim0 : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ)
        (fun z => Real.log (‖eval z (map (Int.castRingHom ℂ) s)‖ / ‖eval z (map (Int.castRingHom ℂ) t)‖)) +
      arInt P t A (Fin.elim0 : Fin 0 → HermLine ι) := by
    unfold arInt
    rw [hφ]
    refine ptsIntegral_add_of_dimOne hFF hP _ fun z hz => ?_
    have hs0 := norm_ne_zero_iff.mpr (eval_ne_zero_of_dimOne h0 hP hs hz)
    have ht0 := norm_ne_zero_iff.mpr (eval_ne_zero_of_dimOne h0 hP ht hz)
    have hA := (A.pos z hz.1).ne'
    unfold logNorm
    rw [← Real.log_mul (div_ne_zero hs0 ht0) (div_ne_zero ht0 hA)]
    congr 1
    field_simp
  have hpf := hPF K ι P s t b hP hsa htb hsP htP
  rw [recR_eq, recR_eq, cycR_eq_vertR_of_dimOne h0 I hP hs, cycR_eq_vertR_of_dimOne h0 I hP ht, hsplit]
  linarith

theorem R1.proof (h0 : ArithVarZeroStatement) (hFF : FibreFiniteStatement)
    (hPF : RegularityProductFormula.Statement) : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.R1.Statement :=
  GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.R1.of_first ⟨RegularityIndependence.proof h0 hFF hPF, RegularityAdditive.proof h0 hFF⟩

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StFlagConeTrdeg
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def FlagConeTrdeg.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (N1 n : ℕ)
    (P : Ideal (MRing ι)) (B : Matrix (Fin n) (Fin N1) (FnField P)),
    P.IsPrime → IsHorizontal P → LinearIndependent (FnField P) B →
    Algebra.trdeg ℤ (MRing (FlagBundleBlocks ι N1 n) ⧸ flagIdeal P B) =
      Algebra.trdeg ℤ (MRing ι ⧸ P) + ((flagDim n + (n - 1) : ℕ) : Cardinal)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StFlagMultiHomog
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def FlagMultiHomog.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (N1 t n : ℕ)
    (P : Ideal (MRing ι)) (c : Fin t → Fin N1 → MRing ι) (m : K → ℕ)
    (B : Matrix (Fin n) (Fin N1) (FnField P)),
    P.IsPrime → IsMultiHomogIdeal P → (∀ a j, IsMultiHomog (c a j) m) → IsKerBasis P c B →
    IsMultiHomogIdeal (flagIdeal P B)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

