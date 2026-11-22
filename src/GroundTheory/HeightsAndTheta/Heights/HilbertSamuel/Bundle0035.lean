import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0025
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0028
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0027
import ReciprocityTheory.GeometryOfNumbers.AsymptoticSequences.ClosingHS
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0026

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHeightsirationalHilb
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace BlockBirationalHilbert

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]

def blockSum (γ : (Σ k, ι k) →₀ ℕ) : K → ℕ := fun k => ∑ i, γ ⟨k, i⟩

omit [Fintype K] in
theorem isMultiHomog_monomial {γ : (Σ k, ι k) →₀ ℕ} {a : K → ℕ} (h : blockSum γ = a) (r : ℤ) :
    IsMultiHomog (monomial γ r : MRing ι) a := by
  intro m hm k
  rw [Finset.mem_singleton.mp (support_monomial_subset hm)]
  exact congrFun h k

omit [Fintype K] in
theorem isMultiHomog_mul {f g : MRing ι} {a b c : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b)
    (habc : a + b = c) : IsMultiHomog (f * g) c := by
  classical
  intro m hm k
  obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := Finset.mem_add.mp (support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, hf m₁ hm₁ k, hg m₂ hm₂ k, ← habc, Pi.add_apply]

omit [Fintype K] in
theorem isMultiHomog_prod {J : Type} (s : Finset J) (f : J → MRing ι) (d : J → K → ℕ)
    (h : ∀ j ∈ s, IsMultiHomog (f j) (d j)) : IsMultiHomog (∏ j ∈ s, f j) (∑ j ∈ s, d j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h1 := isMultiHomog_monomial (ι := ι) (γ := 0) (a := 0) (by funext k; simp [blockSum]) 1
    simpa using h1
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    exact isMultiHomog_mul (h j (Finset.mem_insert_self j s))
      (ih fun j' hj' => h j' (Finset.mem_insert_of_mem hj')) rfl

open Classical in

def monoSet (a : K → ℕ) : Finset ((Σ k, ι k) →₀ ℕ) :=
  (Finset.Icc 0 (Finsupp.equivFunOnFinite.symm fun p : (Σ k, ι k) => a p.1)).filter (blockSum · = a)

theorem mem_monoSet {a : K → ℕ} {γ : (Σ k, ι k) →₀ ℕ} : γ ∈ monoSet a ↔ blockSum γ = a := by
  classical
  unfold monoSet
  rw [Finset.mem_filter]
  refine ⟨fun h => h.2, fun h => ⟨Finset.mem_Icc.mpr ⟨by simp, fun p => ?_⟩, h⟩⟩
  rw [Finsupp.coe_equivFunOnFinite_symm, ← h]
  exact Finset.single_le_sum (f := fun i => γ ⟨p.1, i⟩) (fun _ _ => Nat.zero_le _) (Finset.mem_univ p.2)

omit [Fintype K] [∀ k, Fintype (ι k)] [CharZero Ω] in
theorem aeval_monomial_int (y : (Σ k, ι k) → Ω) (γ : (Σ k, ι k) →₀ ℕ) (r : ℤ) :
    aeval y (monomial γ r : MRing ι) = ((r : ℚ) : Ω) * aeval y (monomial γ (1 : ℤ) : MRing ι) := by
  simp [aeval_monomial]

omit [Fintype K] in

theorem valueSpan_le (y : (Σ k, ι k) → Ω) (a : K → ℕ) (W : Submodule ℚ Ω)
    (hW : ∀ γ : (Σ k, ι k) →₀ ℕ, blockSum γ = a → aeval y (monomial γ (1 : ℤ) : MRing ι) ∈ W) :
    valueSpan y a ≤ W := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨g, hg, rfl⟩
  rw [g.as_sum, map_sum]
  refine Submodule.sum_mem _ fun γ hγ => ?_
  rw [aeval_monomial_int, ← Rat.smul_def]
  exact W.smul_mem _ (hW γ (funext fun k => hg γ hγ k))

theorem finiteDimensional_valueSpan (y : (Σ k, ι k) → Ω) (a : K → ℕ) :
    FiniteDimensional ℚ (valueSpan y a) := by
  classical
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℚ
    (((monoSet a).image fun γ => aeval y (monomial γ (1 : ℤ) : MRing ι) : Finset Ω) : Set Ω))
    (valueSpan_le y a _ fun γ hγ => Submodule.subset_span ?_)
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
  exact ⟨γ, mem_monoSet.mpr hγ, rfl⟩

omit [Fintype K] [∀ k, Fintype (ι k)] [CharZero Ω] in

theorem finrank_le_of_mul [CharZero Ω] {V W : Submodule ℚ Ω} [FiniteDimensional ℚ W] {t : Ω} (ht : t ≠ 0)
    (h : V ≤ W.comap (LinearMap.mulLeft ℚ t)) : Module.finrank ℚ V ≤ Module.finrank ℚ W := by
  have hinj : Function.Injective (LinearMap.mulLeft ℚ t) := fun a b hab => mul_left_cancel₀ ht hab
  rw [LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj V)]
  exact Submodule.finrank_mono (Submodule.map_le_iff_le_comap.mpr h)

end BlockBirationalHilbert

open BlockBirationalHilbert in

theorem BlockBirationalHilbert.proof (hV : HilbFnValueSpan.Statement) : BlockBirationalHilbert.Statement := by
  intro K _ _ ι _ Ω _ _ y k₀ hy hbir m
  classical
  choose i hi using hy
  have hV' := hV K ι Ω y
  have := finiteDimensional_valueSpan (Ω := Ω) y

  have L : ∀ n : ℕ, GroundTheory.Heights₂.Heights.NumbersDVR.hilbFn
      ((mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ))) (fun k => if k = k₀ then (n : ℤ) else 0) =
      (Module.finrank ℚ (valueSpan y (blockDeg k₀ n)) : ℤ) := fun n => by
    rw [← hV']; congr 1; funext k; by_cases hk : k = k₀ <;> simp [hk, blockDeg]
  have M : ∀ n : ℕ, GroundTheory.Heights₂.Heights.NumbersDVR.hilbFn
      ((mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ))) (fun k => if k = k₀ then (n : ℤ) else m k) =
      (Module.finrank ℚ (valueSpan y (fun k => if k = k₀ then n else m k)) : ℤ) := fun n => by
    rw [← hV']; congr 1; funext k; by_cases hk : k = k₀ <;> simp [hk]

  set m₀ : K → ℕ := fun k => if k = k₀ then 0 else m k with hm₀
  let β : (Σ k, ι k) →₀ ℕ :=
    Finsupp.equivFunOnFinite.symm fun p => if p.1 ≠ k₀ ∧ p.2 = i p.1 then m p.1 else 0
  have hβ : blockSum β = m₀ := by
    funext k
    by_cases hk : k = k₀ <;> simp [blockSum, β, hk, m₀]
  set u : Ω := aeval y (monomial β (1 : ℤ) : MRing ι) with hu_def
  have hu : u ≠ 0 := by
    rw [hu_def, aeval_monomial, map_one, one_mul, Finsupp.prod]
    refine Finset.prod_ne_zero_iff.mpr fun p hp => pow_ne_zero _ ?_
    rcases p with ⟨k, j⟩
    have h0 : β ⟨k, j⟩ ≠ 0 := Finsupp.mem_support_iff.mp hp
    simp only [β, Finsupp.coe_equivFunOnFinite_symm] at h0
    split_ifs at h0 with h
    · obtain ⟨_, rfl⟩ := h
      exact hi k
    · exact absurd rfl h0

  have key : ∀ α ∈ monoSet (ι := ι) m₀, ∃ (c : ℕ) (g h : MRing ι), IsMultiHomog g (blockDeg k₀ c) ∧
      IsMultiHomog h (blockDeg k₀ c) ∧ aeval y h ≠ 0 ∧
      aeval y (monomial α (1 : ℤ) : MRing ι) * aeval y h = aeval y g * u := fun α hα =>
    hbir m₀ _ _ (isMultiHomog_monomial (mem_monoSet.mp hα) 1) (isMultiHomog_monomial hβ 1) hu
  choose c g h hg hh hh0 hgh using key
  refine ⟨∑ a ∈ (monoSet (ι := ι) m₀).attach, c a.1 a.2, fun n => ⟨?_, ?_⟩⟩
  ·
    rw [L, M]
    refine Nat.cast_le.mpr (finrank_le_of_mul hu (valueSpan_le y _ _ fun γ hγ => ?_))
    rw [Submodule.mem_comap, LinearMap.mulLeft_apply]
    refine Submodule.subset_span ⟨monomial β 1 * monomial γ 1,
      isMultiHomog_mul (isMultiHomog_monomial hβ 1) (isMultiHomog_monomial hγ 1) ?_, by
        simp only [map_mul, hu_def]⟩
    funext k; by_cases hk : k = k₀ <;> simp [hk, m₀, blockDeg]
  ·
    rw [M, L]
    have hH : aeval y (∏ a ∈ (monoSet (ι := ι) m₀).attach, h a.1 a.2) ≠ 0 := by
      rw [map_prod]; exact Finset.prod_ne_zero_iff.mpr fun a _ => hh0 a.1 a.2
    refine Nat.cast_le.mpr (finrank_le_of_mul (mul_ne_zero (inv_ne_zero hu) hH)
      (valueSpan_le y _ _ fun γ hγ => ?_))
    rw [Submodule.mem_comap, LinearMap.mulLeft_apply]

    set γ₀ := γ.filter (fun p => p.1 = k₀) with hγ₀
    set α := γ.filter (fun p => ¬ p.1 = k₀) with hα_def
    have hsplit : γ₀ + α = γ := Finsupp.filter_add_filter_not γ _
    have hα : blockSum α = m₀ := by
      funext k
      have := congrFun hγ k
      by_cases hk : k = k₀ <;> simp_all [blockSum, m₀]
    have hγ₀' : blockSum γ₀ = blockDeg k₀ n := by
      funext k
      have := congrFun hγ k
      by_cases hk : k = k₀ <;> simp_all [blockSum, blockDeg]
    have hαS : α ∈ monoSet (ι := ι) m₀ := mem_monoSet.mpr hα
    have hmem : (⟨α, hαS⟩ : {x // x ∈ monoSet (ι := ι) m₀}) ∈ (monoSet (ι := ι) m₀).attach :=
      Finset.mem_attach _ _
    refine Submodule.subset_span ⟨monomial γ₀ 1 * g α hαS *
      ∏ a ∈ (monoSet (ι := ι) m₀).attach.erase ⟨α, hαS⟩, h a.1 a.2,
      isMultiHomog_mul (isMultiHomog_mul (isMultiHomog_monomial hγ₀' 1) (hg α hαS) rfl)
        (isMultiHomog_prod _ _ (fun a => blockDeg k₀ (c a.1 a.2)) fun a _ => hh a.1 a.2) ?_, ?_⟩
    · funext k
      by_cases hk : k = k₀
      · simp only [Pi.add_apply, Finset.sum_apply, blockDeg, hk, if_true]
        rw [← Finset.add_sum_erase _ _ hmem]
        ring
      · simp [blockDeg, hk, Finset.sum_apply]
    · have e1 : aeval y (monomial γ (1 : ℤ) : MRing ι) =
          aeval y (monomial γ₀ (1 : ℤ) : MRing ι) * aeval y (monomial α (1 : ℤ) : MRing ι) := by
        rw [← map_mul, monomial_mul, hsplit, mul_one]
      rw [map_mul, map_mul, e1, map_prod, map_prod, ← Finset.mul_prod_erase _ _ hmem]
      have e2 := hgh α hαS
      calc aeval y (monomial γ₀ (1 : ℤ) : MRing ι) * aeval y (g α hαS) *
            ∏ a ∈ (monoSet (ι := ι) m₀).attach.erase ⟨α, hαS⟩, aeval y (h a.1 a.2)
          = (u⁻¹ * u) * (aeval y (monomial γ₀ (1 : ℤ) : MRing ι) * aeval y (g α hαS) *
            ∏ a ∈ (monoSet (ι := ι) m₀).attach.erase ⟨α, hαS⟩, aeval y (h a.1 a.2)) := by
            rw [inv_mul_cancel₀ hu, one_mul]
        _ = u⁻¹ * (aeval y (g α hαS) * u) * (aeval y (monomial γ₀ (1 : ℤ) : MRing ι) *
            ∏ a ∈ (monoSet (ι := ι) m₀).attach.erase ⟨α, hαS⟩, aeval y (h a.1 a.2)) := by ring
        _ = u⁻¹ * (aeval y (monomial α (1 : ℤ) : MRing ι) * aeval y (h α hαS)) *
            (aeval y (monomial γ₀ (1 : ℤ) : MRing ι) *
            ∏ a ∈ (monoSet (ι := ι) m₀).attach.erase ⟨α, hαS⟩, aeval y (h a.1 a.2)) := by rw [e2]
        _ = u⁻¹ * (aeval y (h α hαS) *
            ∏ a ∈ (monoSet (ι := ι) m₀).attach.erase ⟨α, hαS⟩, aeval y (h a.1 a.2)) *
            (aeval y (monomial γ₀ (1 : ℤ) : MRing ι) * aeval y (monomial α (1 : ℤ) : MRing ι)) := by ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHilbertSamuelProjective
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

theorem chiP_zero_dim (n : ℕ) : chiP 0 n = 0 := by
  simp [chiP, monoNormSq, Finset.Nat.antidiagonalTuple_one]

theorem HilbertSamuelProjective.proof (hR : ReductionToProjective.Statement) (hV : SecondVeronese.Statement)
    (h0 : PointHeightFS.Statement) : HilbertSamuelProjective.Statement := by
  intro D I hI
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · have hh := h0 I hI
    refine (isLittleO_zero (fun n : ℕ => (n : ℝ) ^ (0 + 1)) atTop).congr' ?_ EventuallyEq.rfl
    refine Eventually.of_forall fun n => ?_
    simp [hsDefect, hh, chiP_zero_dim]
  · obtain ⟨Ω, _, _, κ, _, d, hchi, htop, hdeg⟩ := hV D hD
    have h2 := (hR D Ω κ I d hI).2
    have hfun : resChi d = fun m => chiP D (2 * m) := funext hchi
    rw [hfun, htop I hI, hdeg] at h2
    push_cast at h2
    exact hilbertSamuelDefect_projectiveSpace_isLittleO D (hhOf I D) h2

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PIntegralClosureFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem secM_mul_mem (y : (Σ k, ι k) → Ω) {d e : K → ℕ} {s t : Ω} (hs : s ∈ secM y d)
    (ht : t ∈ secM y e) : s * t ∈ secM y (d + e) := by
  have hgen : ∀ g : MRing ι, IsMultiHomog g d → aeval y g * t ∈ secM y (d + e) := by
    intro g hg
    change t ∈ Submodule.span ℤ _ at ht
    change _ ∈ Submodule.span ℤ _
    induction ht using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, hh, rfl⟩ := hx
      exact Submodule.subset_span ⟨g * h, ProjLine.mhMul hg hh, by rw [map_mul]⟩
    | zero => simp
    | add x z _ _ hx hz => rw [mul_add]; exact add_mem hx hz
    | smul n x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx
  change s ∈ Submodule.span ℤ _ at hs
  induction hs using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    exact hgen g hg
  | zero => simp
  | add x z _ _ hx hz => rw [add_mul]; exact add_mem hx hz
  | smul n x _ hx => rw [smul_mul_assoc]; exact zsmul_mem hx n

theorem IntegralClosureFinite.proof (hR : NmSectionsRational.Statement) (hF : NmSectionsFinite.Statement) :
    IntegralClosureFinite.Statement := by
  unfold IntegralClosureFinite.Statement KH.NormalizationBoundedIndexStatement
  unfold NmSectionsRational.Statement at hR
  unfold NmSectionsFinite.Statement at hF
  intro K _ ι _ Ω _ _ y a ha hy hbir hnorm
  obtain ⟨τ₀, hτ₀⟩ := hR K ι Ω y a ha hy hbir hnorm
  obtain ⟨J, _, d, e, τ₁, he, hgen⟩ := hF K ι Ω y a ha hy hbir τ₀
  choose m hm1 hme using fun j => hτ₀ (d j) (he j).1 (e j) (he j).2.2
  classical
  refine ⟨∏ j, m j, τ₁, Nat.one_le_iff_ne_zero.mpr (Finset.prod_pos fun j _ => hm1 j).ne', ?_⟩
  intro τ hτ s hs
  obtain ⟨r, hr, rfl⟩ := hgen τ hτ s hs
  rw [Finset.mul_sum]
  refine sum_mem fun j _ => ?_
  have hsplit : (∏ i, m i : ℕ) = (∏ i ∈ Finset.univ.erase j, m i) * m j :=
    (Finset.prod_erase_mul _ _ (Finset.mem_univ j)).symm
  have hdeg : (fun k => τ * a k) = (fun k => (τ - d j) * a k) + (fun k => d j * a k) := by
    funext k
    simp only [Pi.add_apply]
    rw [← add_mul, Nat.sub_add_cancel (le_trans (he j).2.1 hτ)]
  have hval : ((∏ i, m i : ℕ) : Ω) * (r j * e j) =
      ((∏ i ∈ Finset.univ.erase j, m i : ℕ) : ℤ) • (r j * ((m j : Ω) * e j)) := by
    rw [hsplit, zsmul_eq_mul]
    push_cast
    ring
  rw [hval, hdeg]
  exact zsmul_mem (secM_mul_mem y (hr j) (hme j)) _

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLocalRep
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace LocalRep

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

omit [Fintype K] in

theorem isMultiHomog_mul {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a)
    (hg : IsMultiHomog g b) : IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf m1 hm1 k, hg m2 hm2 k]

omit [Fintype K] in

theorem isMultiHomog_add {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a)
    (hg : IsMultiHomog g a) : IsMultiHomog (f + g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
  · exact hf m h k
  · exact hg m h k

omit [Fintype K] in

theorem isMultiHomog_C (r : ℤ) : IsMultiHomog (C r : MRing ι) 0 := by
  classical
  intro m hm k
  have : m = 0 := by
    by_contra h
    exact (mem_support_iff.mp hm) (by rw [coeff_C, if_neg (Ne.symm h)])
  subst this
  simp

omit [Fintype K] in

theorem isMultiHomog_X [DecidableEq K] (k : K) (i : ι k) :
    IsMultiHomog (X ⟨k, i⟩ : MRing ι) (Pi.single k 1) := by
  classical
  intro m hm k'
  rw [MvPolynomial.support_X, Finset.mem_singleton] at hm
  subst hm
  by_cases h : k' = k
  · subst h
    simp [Finsupp.single_apply]
  · have : ∀ j : ι k', (⟨k, i⟩ : Σ k, ι k) ≠ ⟨k', j⟩ := fun j e => h (congrArg Sigma.fst e).symm
    simp [h]

theorem isMultiHomog_chartMono (c : ∀ k, ι k) (e : K → ℕ) :
    IsMultiHomog (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ e k) e := by
  classical
  have key : ∀ s : Finset K, IsMultiHomog (∏ k ∈ s, (X ⟨k, c k⟩ : MRing ι) ^ e k)
      (∑ k ∈ s, e k • Pi.single k 1) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using isMultiHomog_C (ι := ι) 1
    | insert k s hk ih =>
      rw [Finset.prod_insert hk, Finset.sum_insert hk]
      refine isMultiHomog_mul ?_ ih
      induction e k with
      | zero => simpa using isMultiHomog_C (ι := ι) 1
      | succ m ihm =>
        rw [pow_succ, succ_nsmul]
        exact isMultiHomog_mul ihm (isMultiHomog_X k (c k))
  have h : (∑ k, e k • (Pi.single k 1 : K → ℕ)) = e := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  have := key Finset.univ
  rwa [h] at this

theorem exists_form_of_mem_chartRingZ (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    {x : Ω} (hx : x ∈ chartRingZ y c) :
    ∃ (N : K → ℕ) (H : MRing ι), IsMultiHomog H N ∧ aeval y H = x * ∏ k, y ⟨k, c k⟩ ^ N k := by
  classical
  induction hx using Algebra.adjoin_induction with
  | mem u hu =>
    obtain ⟨⟨k, i⟩, rfl⟩ := hu
    refine ⟨Pi.single k 1, X ⟨k, i⟩, isMultiHomog_X k i, ?_⟩
    rw [aeval_X, Finset.prod_eq_single k (fun b _ hb => by simp [hb]) (by simp)]
    simp only [Pi.single_eq_same, pow_one]
    exact (div_mul_cancel₀ _ (hc k)).symm
  | algebraMap r =>
    exact ⟨0, C r, isMultiHomog_C r, by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨N₁, H₁, h₁, e₁⟩ := hu
    obtain ⟨N₂, H₂, h₂, e₂⟩ := hv
    refine ⟨N₁ + N₂, H₁ * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ N₂ k + H₂ * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ N₁ k,
      isMultiHomog_add (isMultiHomog_mul h₁ (isMultiHomog_chartMono c N₂))
        (add_comm N₂ N₁ ▸ isMultiHomog_mul h₂ (isMultiHomog_chartMono c N₁)), ?_⟩
    simp only [map_add, map_mul, map_prod, map_pow, aeval_X, e₁, e₂, Pi.add_apply, pow_add,
      Finset.prod_mul_distrib]
    ring
  | mul u v _ _ hu hv =>
    obtain ⟨N₁, H₁, h₁, e₁⟩ := hu
    obtain ⟨N₂, H₂, h₂, e₂⟩ := hv
    refine ⟨N₁ + N₂, H₁ * H₂, isMultiHomog_mul h₁ h₂, ?_⟩
    simp only [map_mul, e₁, e₂, Pi.add_apply, pow_add, Finset.prod_mul_distrib]
    ring

theorem proof : LocalRep.Statement := by
  intro K _ ι _ Ω _ y a n s z hs hz
  classical
  choose c hzc using hz.1
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := by
    intro k h0
    apply hzc k
    have hmem : (X ⟨k, c k⟩ : MRing ι) ∈ mCoordIdeal y := by
      show mConeMap y (X ⟨k, c k⟩) = 0
      simp [mConeMap, h0]
    simpa using hz.2 _ hmem
  obtain ⟨N, H, hH, he⟩ := exists_form_of_mem_chartRingZ y c hyc (hs c hyc)
  refine ⟨N + fun k => ((n : ℤ) * a k).toNat, N + fun k => (-((n : ℤ) * a k)).toNat,
    H * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ ((n : ℤ) * a k).toNat,
    ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ (N + fun k => (-((n : ℤ) * a k)).toNat) k,
    isMultiHomog_mul hH (isMultiHomog_chartMono c _), isMultiHomog_chartMono c _, fun k => ?_, ?_, ?_⟩
  · simp only [Pi.add_apply]
    push_cast
    omega
  · simp only [map_mul, map_prod, map_pow, aeval_X]
    rw [he, mul_assoc, mul_assoc, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hyc k), ← zpow_add₀ (hyc k)]
    congr 1
    simp only [Pi.add_apply]
    push_cast
    omega
  · simp only [map_prod, map_pow, map_X, eval_X]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hzc k)

end LocalRep

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPerturb
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

variable {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isMultiHomogIdeal_map_coeff {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)
    {P : Ideal (MRingOver R ι)} (hP : IsMultiHomogIdeal P) :
    IsMultiHomogIdeal (P.map (MvPolynomial.map φ : MRingOver R ι →+* MRingOver S ι)) := by
  obtain ⟨T, hT, rfl⟩ := hP
  refine ⟨MvPolynomial.map φ '' T, ?_, by rw [Ideal.map_span]⟩
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨a, ha⟩ := hT f hf
  exact ⟨a, fun m hm k => ha m (MvPolynomial.support_map_subset φ f hm) k⟩

theorem zcomb_fsH_a [Fintype K] (L : HermLine ι) (q p : ℕ) :
    (HermLine.zcomb L (fsH ι) q p).a = (q : ℤ) • L.a + fun _ => (p : ℤ) := by
  funext k
  simp [HermLine.zcomb, fsH, HermLine.ofMetrics]

theorem Perturb.proof (hGen : SmallGenTwist.Statement) (hSemi : SemiposTwist.Statement)
    (hDeg : GenDegTwist.Statement) (hFib : GenOnFibres.Statement) (hAmp : AmpleOfGenTwist.Statement) :
    Perturb.Statement := by
  intro K _ _ ι _ _ Ω _ _ y D L P0 p q _ hV _ hL hp hq
  obtain ⟨n, w, hw, hgw, -⟩ := hL.gen
  have hhom : IsMultiHomogIdeal (mCoordIdeal y) := hV.2.1.2.1
  have hfib := hFib K ι Ω y L.a n w hw hgw
  refine ⟨⟨hL.normalForm_baseLattice_le_dualSpan_sup_line, hSemi K ι P0 _ L p q hL.semipos, ?_, hGen K ι Ω y L p q hL.gen⟩, ?_, ?_⟩
  · rw [zcomb_fsH_a]
    exact hDeg K ι Ω y D L.a n w p q hV hw hgw hL.deg_pos hq
  · rw [zcomb_fsH_a]
    exact hAmp ℚ K ι (KH.genIdeal y) L.a p q (isMultiHomogIdeal_map_coeff _ hhom) hfib.1 hp
  · intro ℓ hℓ
    have := Fact.mk hℓ
    rw [zcomb_fsH_a]
    exact hAmp (ZMod ℓ) K ι (fibreIdeal ℓ y) L.a p q (isMultiHomogIdeal_map_coeff _ hhom) (hfib.2 ℓ hℓ) hp

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

