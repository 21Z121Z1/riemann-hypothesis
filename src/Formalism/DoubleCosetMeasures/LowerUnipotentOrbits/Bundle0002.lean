import Formalism.DoubleCosetMeasures.Statement

-- bundled from Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.IsOpenIsIntSet
section
noncomputable section

open MeasureTheory Matrix

namespace Formalism.DoubleCosetMeasures.P

open Formalism.DoubleCosetMeasures

section SlopeTestRemainingChoices

variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]

theorem isOpen_isInt_set (R : Subring K) (hR : IsOpen (R : Set K)) (n : ℕ) :
    IsOpen {g : GL (Fin n) K | IsInt R (g : Matrix (Fin n) (Fin n) K) ∧
      IsInt R ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)} := by
  have hset : {g : GL (Fin n) K | IsInt R (g : Matrix (Fin n) (Fin n) K) ∧
      IsInt R ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)} =
      (⋂ a, ⋂ b, {g : GL (Fin n) K | (g : Matrix (Fin n) (Fin n) K) a b ∈ R}) ∩
      (⋂ a, ⋂ b, {g : GL (Fin n) K | ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b ∈ R}) := by
    ext g
    simp [IsInt, Set.mem_iInter]
  rw [hset]
  apply IsOpen.inter
  · refine isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b => ?_
    exact hR.preimage (Units.continuous_val.matrix_elem a b)
  · refine isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b => ?_
    exact hR.preimage (Units.continuous_coe_inv.matrix_elem a b)

theorem isOpen_intSub (R : Subring K) (hR : IsOpen (R : Set K)) {n : ℕ}
    (H : Subgroup (GL (Fin n) K)) : IsOpen (intSub R H : Set H) := by
  exact (isOpen_isInt_set R hR n).preimage continuous_subtype_val

end SlopeTestRemainingChoices

theorem sLow_mem {K : Type} [CommRing K] (R : Subring K) {n : ℕ} (x : Matrix (Fin n) (Fin n) K)
    (hx : IsInt R x) : sLow x ∈ R := by
  unfold sLow
  refine R.sum_mem fun j _ => ?_
  split_ifs
  · exact hx _ _
  · exact R.zero_mem

theorem sUp_mem {K : Type} [CommRing K] (R : Subring K) {n : ℕ} (x : Matrix (Fin n) (Fin n) K)
    (hx : IsInt R x) : sUp x ∈ R := by
  unfold sUp
  refine R.sum_mem fun j _ => ?_
  split_ifs
  · exact hx _ _
  · exact R.zero_mem

theorem phi_inv (hIntInv : IntInv) (hIsoInv : IsoInv) (hSA : SimpleAdd)
    {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (s : List ℕ) (t : ℕ → Kˣ) (ψ : AddChar K ℂ) (hψ : ∀ r ∈ R, ψ r = 1)
    (C : Type) [AddCommGroup C] [Module R C] (e : C) (lam : C →ₗ[R] KR R) :
    ∀ a ∈ intSub R (lowW K s t), ∀ b ∈ intSub R (upUniG K s.sum), ∀ x : lowW K s t,
      ∀ y : upUniG K s.sum, phi R s t ψ C e lam (a * x, y * b) = phi R s t ψ C e lam (x, y) := by
  intro a ha b hb x y
  have haI : IsInt R (((a : GL (Fin s.sum) K)) : Matrix (Fin s.sum) (Fin s.sum) K) := ha.1
  have hbI : IsInt R (((b : GL (Fin s.sum) K)) : Matrix (Fin s.sum) (Fin s.sum) K) := hb.1
  have haL : IsLowUni (((a : GL (Fin s.sum) K)) : Matrix (Fin s.sum) (Fin s.sum) K) := a.2.1
  have hxL : IsLowUni (((x : GL (Fin s.sum) K)) : Matrix (Fin s.sum) (Fin s.sum) K) := x.2.1
  have hbU : IsUpUni (((b : GL (Fin s.sum) K)) : Matrix (Fin s.sum) (Fin s.sum) K) := b.2
  have hyU : IsUpUni (((y : GL (Fin s.sum) K)) : Matrix (Fin s.sum) (Fin s.sum) K) := y.2
  unfold phi
  simp only [Subgroup.coe_mul, Units.val_mul]
  have hM : ((a : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) *
        ((x : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) * pt s t *
        (((y : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) *
          ((b : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K)) =
      ((a : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) *
        (((x : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) * pt s t *
          ((y : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K)) *
        ((b : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) := by
    simp only [Matrix.mul_assoc]
  rw [(hSA K _ _ _).1 haL hxL, (hSA K _ _ _).2 hyU hbU]
  have hI : IsInt R (((a : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) * ((x : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) * pt s t * (((y : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) * ((b : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K))) ↔ IsInt R (((x : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) * pt s t * ((y : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K)) := by
    rw [hM]; exact hIntInv K R _ _ _ _ haL hbU haI hbI
  have hC : Nat.card (isoSet R (((a : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) * ((x : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) * pt s t * (((y : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) * ((b : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K))) C e lam) =
      Nat.card (isoSet R (((x : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) * pt s t * ((y : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K)) C e lam) := by
    rw [hM]; exact hIsoInv K R _ _ _ _ haL hbU haI hbI C e lam
  have hψ' : ψ (sLow ((a : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) + sLow ((x : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) + (sUp ((y : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) + sUp ((b : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K))) = ψ (sLow ((x : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) + sUp ((y : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K)) := by
    rw [show sLow ((a : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) + sLow ((x : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) + (sUp ((y : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) + sUp ((b : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K)) =
        (sLow ((a : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) + sUp ((b : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K)) + (sLow ((x : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) + sUp ((y : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K)) by ring,
      AddChar.map_add_eq_mul, AddChar.map_add_eq_mul ψ (sLow ((a : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K)),
      hψ _ (sLow_mem R _ haI), hψ _ (sUp_mem R _ hbI), one_mul, one_mul]
  rw [hψ']
  congr 1
  by_cases h : IsInt R (((x : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) * pt s t * ((y : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K))
  · rw [if_pos (hI.2 h), if_pos h, hC]
  · rw [if_neg (fun h' => h (hI.1 h')), if_neg h]

theorem bbFinite_of : IntTwoSided → IntInv → IsoInv → SimpleAdd → BBFinite := by
  intro hTS hII hIso hSA K _ _ _ R hR s t ψ hψ μ₁ μ₂ _ _ _ _ C _ _ e lam hcs
  have h := hTS (lowW K s t) (upUniG K s.sum) μ₁ μ₂ (intSub R (lowW K s t))
    (intSub R (upUniG K s.sum)) (isOpen_intSub R hR _) (isOpen_intSub R hR _) ℂ
    (phi R s t ψ C e lam) (phi_inv hII hIso hSA R s t ψ hψ C e lam) hcs
  refine ⟨h.1, ?_⟩
  rw [BB, h.2]
  congr 1

theorem bbNorm_of : BBFinite → BBNorm := by
  intro hBB K _ _ _ R hR s t ψ hψ μ₁ μ₂ _ _ _ _ h1 h2 C _ _ e lam hcs
  rw [(hBB K R hR s t ψ hψ μ₁ μ₂ C e lam hcs).2, h1, h2]
  simp

end Formalism.DoubleCosetMeasures.P
end
end

-- bundled from Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.TwoSided
section
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory

namespace Formalism.DoubleCosetMeasures.P

theorem mem_preimage_rightRel_mk {G : Type} [Group G] (K : Subgroup G)
    (q : Quotient (QuotientGroup.rightRel K)) (x : G) :
    Quotient.mk (QuotientGroup.rightRel K) x = q ↔ x * q.out⁻¹ ∈ K := by
  conv_lhs => rw [← Quotient.out_eq q]
  rw [Quotient.eq, QuotientGroup.rightRel_apply, ← K.inv_mem_iff, mul_inv_rev, inv_inv]

theorem mem_preimage_leftQuot_mk {G : Type} [Group G] (K : Subgroup G) (q : G ⧸ K) (y : G) :
    (y : G ⧸ K) = q ↔ q.out⁻¹ * y ∈ K := by
  conv_lhs => rw [← QuotientGroup.out_eq' q]
  rw [QuotientGroup.eq, ← K.inv_mem_iff, mul_inv_rev, inv_inv]

def box {G₁ G₂ : Type} [Group G₁] [Group G₂] (K₁ : Subgroup G₁) (K₂ : Subgroup G₂)
    (p : Quotient (QuotientGroup.rightRel K₁) × (G₂ ⧸ K₂)) : Set (G₁ × G₂) :=
  ((fun x => x * p.1.out⁻¹) ⁻¹' (K₁ : Set G₁)) ×ˢ ((fun y => p.2.out⁻¹ * y) ⁻¹' (K₂ : Set G₂))

def clsTS {G₁ G₂ : Type} [Group G₁] [Group G₂] (K₁ : Subgroup G₁) (K₂ : Subgroup G₂)
    (z : G₁ × G₂) : Quotient (QuotientGroup.rightRel K₁) × (G₂ ⧸ K₂) :=
  (Quotient.mk _ z.1, (z.2 : G₂ ⧸ K₂))

theorem mem_box_iff {G₁ G₂ : Type} [Group G₁] [Group G₂] (K₁ : Subgroup G₁) (K₂ : Subgroup G₂)
    (p : Quotient (QuotientGroup.rightRel K₁) × (G₂ ⧸ K₂)) (z : G₁ × G₂) :
    z ∈ box K₁ K₂ p ↔ clsTS K₁ K₂ z = p := by
  simp only [box, clsTS, Prod.ext_iff, Set.mem_prod, Set.mem_preimage, SetLike.mem_coe,
    mem_preimage_rightRel_mk, mem_preimage_leftQuot_mk]

theorem cls_out {G₁ G₂ : Type} [Group G₁] [Group G₂] (K₁ : Subgroup G₁) (K₂ : Subgroup G₂)
    (p : Quotient (QuotientGroup.rightRel K₁) × (G₂ ⧸ K₂)) :
    clsTS K₁ K₂ (p.1.out, p.2.out) = p := by
  simp only [clsTS, Quotient.out_eq, QuotientGroup.out_eq']

theorem inv_eq_cls {G₁ G₂ : Type} [Group G₁] [Group G₂] (K₁ : Subgroup G₁) (K₂ : Subgroup G₂)
    {E : Type} (f : G₁ × G₂ → E)
    (hf : ∀ a ∈ K₁, ∀ b ∈ K₂, ∀ x : G₁, ∀ y : G₂, f (a * x, y * b) = f (x, y)) (z : G₁ × G₂) :
    f z = f ((clsTS K₁ K₂ z).1.out, (clsTS K₁ K₂ z).2.out) := by
  have h1 := (mem_preimage_rightRel_mk K₁ (Quotient.mk (QuotientGroup.rightRel K₁) z.1) z.1).1 rfl
  have h2 := (mem_preimage_leftQuot_mk K₂ (z.2 : G₂ ⧸ K₂) z.2).1 rfl
  have h := hf _ h1 _ h2 (Quotient.mk (QuotientGroup.rightRel K₁) z.1).out (z.2 : G₂ ⧸ K₂).out
  simp only [inv_mul_cancel_right, mul_inv_cancel_left] at h
  simpa [clsTS] using h

theorem intTwoSided : Formalism.DoubleCosetMeasures.IntTwoSided := by
  classical
  intro G₁ G₂ _ _ _ _ _ _ _ _ _ _ μ₁ μ₂ _ _ _ _ K₁ K₂ hK₁ hK₂ E _ _ _ f hf hcs
  set g : Quotient (QuotientGroup.rightRel K₁) × (G₂ ⧸ K₂) → E := fun p => f (p.1.out, p.2.out) with hg
  have hopen : ∀ p, IsOpen (box K₁ K₂ p) := fun p =>
    (hK₁.preimage (continuous_mul_right _)).prod (hK₂.preimage (continuous_mul_left _))
  have hmeas : ∀ p, MeasurableSet (box K₁ K₂ p) := fun p =>
    (hK₁.preimage (continuous_mul_right _)).measurableSet.prod
      (hK₂.preimage (continuous_mul_left _)).measurableSet
  have hfg : ∀ z, f z = g (clsTS K₁ K₂ z) := fun z => inv_eq_cls K₁ K₂ f hf z
  have hfin : (Function.support g).Finite := by
    obtain ⟨t, ht⟩ := hcs.elim_finite_subcover (fun p => box K₁ K₂ p) hopen
      (fun z _ => Set.mem_iUnion.2 ⟨clsTS K₁ K₂ z, (mem_box_iff K₁ K₂ _ z).2 rfl⟩)
    refine t.finite_toSet.subset fun p hp => ?_
    have hz : ((p.1.out, p.2.out) : G₁ × G₂) ∈ tsupport f := subset_tsupport f hp
    obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion₂.1 (ht hz)
    have hpi := (mem_box_iff K₁ K₂ i _).1 hzi
    rw [cls_out] at hpi
    rw [hpi]
    exact hi
  refine ⟨hfin, ?_⟩
  change ∫ p, f p ∂(μ₁.prod μ₂) = ∑ᶠ p : Quotient (QuotientGroup.rightRel K₁) × (G₂ ⧸ K₂),
    ((μ₁ (K₁ : Set G₁)).toReal * (μ₂ (K₂ : Set G₂)).toReal) • g p
  set S := hfin.toFinset with hS
  have hsum : ∑ᶠ p : Quotient (QuotientGroup.rightRel K₁) × (G₂ ⧸ K₂),
      ((μ₁ (K₁ : Set G₁)).toReal * (μ₂ (K₂ : Set G₂)).toReal) • g p =
      ∑ p ∈ S, ((μ₁ (K₁ : Set G₁)).toReal * (μ₂ (K₂ : Set G₂)).toReal) • g p := by
    apply finsum_eq_sum_of_support_subset
    intro p hp
    rw [hS, Set.Finite.coe_toFinset]
    intro h
    apply hp
    simp [h]
  rw [hsum]
  have hdecomp : f = fun z => ∑ p ∈ S, (box K₁ K₂ p).indicator (fun _ => g p) z := by
    funext z
    have hind : ∀ p, (box K₁ K₂ p).indicator (fun _ => g p) z =
        if clsTS K₁ K₂ z = p then g p else 0 := by
      intro p
      simp only [Set.indicator, mem_box_iff]
    simp only [hind, Finset.sum_ite_eq]
    rw [hfg z]
    split_ifs with h
    · rfl
    · rw [hS, Set.Finite.mem_toFinset, Function.mem_support, not_not] at h
      exact h
  have hbox : ∀ p, (μ₁.prod μ₂) (box K₁ K₂ p) = μ₁ (K₁ : Set G₁) * μ₂ (K₂ : Set G₂) := by
    intro p
    rw [box, Measure.prod_prod, measure_preimage_mul_right, measure_preimage_mul]
  have hpiece : ∀ p, ∫ z, (box K₁ K₂ p).indicator (fun _ => g p) z ∂(μ₁.prod μ₂) =
      ((μ₁ (K₁ : Set G₁)).toReal * (μ₂ (K₂ : Set G₂)).toReal) • g p := by
    intro p
    rw [integral_indicator_const _ (hmeas p), Measure.real, hbox p, ENNReal.toReal_mul]
  by_cases hint : Integrable f (μ₁.prod μ₂)
  · have hI : ∀ p ∈ S, Integrable ((box K₁ K₂ p).indicator (fun _ => g p)) (μ₁.prod μ₂) := by
      intro p _
      refine (hint.indicator (hmeas p)).congr (Filter.Eventually.of_forall fun z => ?_)
      by_cases hz : z ∈ box K₁ K₂ p
      · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, hfg z, (mem_box_iff K₁ K₂ p z).1 hz]
      · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]
    conv_lhs => rw [hdecomp]
    rw [integral_finset_sum S hI]
    exact Finset.sum_congr rfl fun p _ => hpiece p
  · rw [integral_undef hint]
    have hex : ∃ p ∈ S, ¬ Integrable ((box K₁ K₂ p).indicator (fun _ => g p)) (μ₁.prod μ₂) := by
      by_contra hne
      push_neg at hne
      apply hint
      rw [hdecomp]
      exact integrable_finset_sum S hne
    obtain ⟨p, -, hnp⟩ := hex
    have htop : μ₁ (K₁ : Set G₁) * μ₂ (K₂ : Set G₂) = ⊤ := by
      by_contra hne
      apply hnp
      rw [integrable_indicator_iff (hmeas p)]
      exact integrableOn_const (by rw [hbox p]; exact hne)
    have h0 : (μ₁ (K₁ : Set G₁)).toReal * (μ₂ (K₂ : Set G₂)).toReal = 0 := by
      rw [← ENNReal.toReal_mul, htop, ENNReal.toReal_top]
    simp [h0]

end Formalism.DoubleCosetMeasures.P
end
end

