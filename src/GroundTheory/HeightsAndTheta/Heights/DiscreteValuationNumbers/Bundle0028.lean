import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0017
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0014
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SameGenericSymm
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0023

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinJoinVertDivRight
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (IsVertDiv mcIdeal mcMap joinCoord midDeg midVar)

noncomputable section

namespace JoinVerticalDivisorRight

variable {K K' K₂ : Type} {ι : K → Type} {ι' : K' → Type} {ι₂ : K₂ → Type}

def midNat (a : K ⊕ K' → ℕ) : K ⊕ (K₂ ⊕ K') → ℕ :=
  Sum.elim (fun k => a (.inl k)) (Sum.elim 0 (fun k => a (.inr k)))

theorem midNat_injective : Function.Injective (midNat (K := K) (K' := K') (K₂ := K₂)) := by
  intro a b e
  funext l
  rcases l with k | k
  · exact congrFun e (.inl k)
  · exact congrFun e (.inr (.inr k))

theorem midVar_injective : Function.Injective (midVar (ι := ι) (ι' := ι') ι₂) := by
  rintro ⟨k | k, i⟩ ⟨l | l, j⟩ h <;> dsimp only [midVar] at h <;> cases h <;> rfl

theorem mcMap_rename_midVar (R : Type) [CommRing R] {Ω : Type} [Field Ω] [Algebra R Ω]
    (x : (Σ k, ι k) → Ω) (w : (Σ k, ι₂ k) → Ω) (z : (Σ k, ι' k) → Ω)
    (h : MvPolynomial (Σ k : K ⊕ K', Sum.elim ι ι' k) R) :
    mcMap R (joinCoord x (joinCoord w z)) (rename (midVar ι₂) h) =
      rename (Sum.map id Sum.inr) (mcMap R (joinCoord x z) h) := by
  induction h using MvPolynomial.induction_on with
  | C a => simp [mcMap, algebraMap_eq]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, rename_X]
    congr 1
    obtain ⟨k | k, i⟩ := v <;> simp [mcMap, midVar, joinCoord]

theorem rename_mem_mcIdeal_iff (R : Type) [CommRing R] {Ω : Type} [Field Ω] [Algebra R Ω]
    (x : (Σ k, ι k) → Ω) (w : (Σ k, ι₂ k) → Ω) (z : (Σ k, ι' k) → Ω)
    (h : MvPolynomial (Σ k : K ⊕ K', Sum.elim ι ι' k) R) :
    rename (midVar ι₂) h ∈ mcIdeal R (joinCoord x (joinCoord w z)) ↔ h ∈ mcIdeal R (joinCoord x z) := by
  simp only [mcIdeal, RingHom.mem_ker, mcMap_rename_midVar]
  exact map_eq_zero_iff _ (rename_injective _ (Sum.map_injective.mpr ⟨Function.injective_id,
    Sum.inr_injective⟩))

variable [Fintype K] [Fintype K'] [Fintype K₂] [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]
  [∀ k, Fintype (ι₂ k)]

theorem weight_mapDomain_midVar [DecidableEq K] [DecidableEq K'] [DecidableEq K₂]
    (d : (Σ k : K ⊕ K', Sum.elim ι ι' k) →₀ ℕ) :
    Finsupp.weight (blockWeight (Sum.elim ι (Sum.elim ι₂ ι'))) (Finsupp.mapDomain (midVar ι₂) d) =
      midNat (Finsupp.weight (blockWeight (Sum.elim ι ι')) d) := by
  funext l
  rw [Objects.weight_blockWeight_apply]
  rcases l with k | k | k
  · change _ = Finsupp.weight (blockWeight (Sum.elim ι ι')) d (.inl k)
    rw [Objects.weight_blockWeight_apply]
    exact Finset.sum_congr rfl fun i _ => Finsupp.mapDomain_apply midVar_injective d ⟨.inl k, i⟩
  · change _ = 0
    refine Finset.sum_eq_zero fun i _ => Finsupp.mapDomain_of_notMem_range _ _ ?_
    rintro ⟨⟨k' | k', j⟩, h⟩ <;> dsimp only [midVar] at h <;> cases h
  · change _ = Finsupp.weight (blockWeight (Sum.elim ι ι')) d (.inr k)
    rw [Objects.weight_blockWeight_apply]
    exact Finset.sum_congr rfl fun i _ => Finsupp.mapDomain_apply midVar_injective d ⟨.inr k, i⟩

theorem isMultiHomog_rename [DecidableEq K] [DecidableEq K'] [DecidableEq K₂] {R : Type} [CommRing R]
    {f : MvPolynomial (Σ k : K ⊕ K', Sum.elim ι ι' k) R} {a : K ⊕ K' → ℕ} (hf : IsMultiHomog f a) :
    IsMultiHomog (rename (midVar ι₂) f) (midNat a) := by
  unfold IsMultiHomog at hf ⊢
  induction hf using IsWeightedHomogeneous.induction_on with
  | zero => simpa using isWeightedHomogeneous_zero R _ _
  | add p q hp hq ihp ihq => simpa [map_add] using ihp.add ihq
  | monomial d r hr =>
    rw [rename_monomial]
    exact isWeightedHomogeneous_monomial _ _ _ (by rw [weight_mapDomain_midVar, hr])

theorem isMultiHomog_rename' {R : Type} [CommRing R] {f : MvPolynomial (Σ k : K ⊕ K', Sum.elim ι ι' k) R}
    {a : K ⊕ K' → ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (rename (midVar ι₂) f) (midNat a) := by
  classical
  rw [← Objects.isMultiHomog_iff] at hf ⊢
  exact isMultiHomog_rename hf

theorem rename_weightedHomogeneousComponent [DecidableEq K] [DecidableEq K'] [DecidableEq K₂] {R : Type}
    [CommRing R] (b : K ⊕ K' → ℕ) (h : MvPolynomial (Σ k : K ⊕ K', Sum.elim ι ι' k) R) :
    rename (midVar ι₂) (weightedHomogeneousComponent (blockWeight (Sum.elim ι ι')) b h) =
      weightedHomogeneousComponent (blockWeight (Sum.elim ι (Sum.elim ι₂ ι'))) (midNat b)
        (rename (midVar ι₂) h) := by
  induction h using MvPolynomial.induction_on' with
  | monomial d r =>
    have hm : IsMultiHomog (monomial d r : MvPolynomial (Σ k : K ⊕ K', Sum.elim ι ι' k) R)
        (Finsupp.weight (blockWeight (Sum.elim ι ι')) d) := isWeightedHomogeneous_monomial _ _ _ rfl
    have hj := isMultiHomog_rename (ι₂ := ι₂) hm
    by_cases hb : b = Finsupp.weight (blockWeight (Sum.elim ι ι')) d
    · subst hb
      rw [IsWeightedHomogeneous.weightedHomogeneousComponent_same hm,
        IsWeightedHomogeneous.weightedHomogeneousComponent_same hj]
    · rw [IsWeightedHomogeneous.weightedHomogeneousComponent_ne b hm hb,
        IsWeightedHomogeneous.weightedHomogeneousComponent_ne _ hj (fun e => hb (midNat_injective e)),
        map_zero]
  | add p q hp hq => simp only [map_add, hp, hq]

theorem comap_isMultiProjPrime {R : Type} [CommRing R]
    {Q : Ideal (MvPolynomial (Σ k : K ⊕ (K₂ ⊕ K'), Sum.elim ι (Sum.elim ι₂ ι') k) R)}
    (hQ : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiProjPrime Q) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiProjPrime (Q.comap (rename (midVar (ι := ι) (ι' := ι') ι₂))) := by
  classical
  rw [← Objects.isMultiProjPrime_iff] at hQ ⊢
  have := hQ.isPrime
  refine ⟨Ideal.comap_isPrime _ Q, fun h hh b => ?_, fun k => ?_⟩
  · rw [Ideal.mem_comap] at hh ⊢
    rw [rename_weightedHomogeneousComponent]
    exact hQ.multiHomog _ hh _
  · rcases k with k | k
    · obtain ⟨i, hi⟩ := hQ.relevant (Sum.inl k)
      exact ⟨i, by rw [Ideal.mem_comap, rename_X]; exact hi⟩
    · obtain ⟨i, hi⟩ := hQ.relevant (Sum.inr (Sum.inr k))
      exact ⟨i, by rw [Ideal.mem_comap, rename_X]; exact hi⟩

end JoinVerticalDivisorRight

open JoinVerticalDivisorRight in

theorem JoinVerticalDivisorRight.proof : JoinVerticalDivisorRight.Statement := by
  intro O _ _ _ Ω _ _ K _ ι _ x K' _ ι' _ z K₂ _ ι₂ _ w b f g hD
  obtain ⟨⟨α, β, hf, hg, hb⟩, hfP, hgP, hU⟩ := hD
  refine ⟨⟨midNat α, midNat β, isMultiHomog_rename' hf, isMultiHomog_rename' hg, ?_⟩, ?_, ?_, ?_⟩
  · rintro (k | k | k)
    · exact hb (.inl k)
    · simp [midNat, midDeg]
    · exact hb (.inr k)
  · rwa [rename_mem_mcIdeal_iff]
  · rwa [rename_mem_mcIdeal_iff]
  · intro Q hQ hPQ hQO
    have hle : mcIdeal O (joinCoord x z) ≤ Q.comap (rename (midVar (ι := ι) (ι' := ι') ι₂)) :=
      fun h hh => Ideal.mem_comap.mpr (hPQ ((rename_mem_mcIdeal_iff O x w z h).mpr hh))
    have hO : (Q.comap (rename (midVar (ι := ι) (ι' := ι') ι₂))).comap
        (C : O →+* ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O (Sum.elim ι ι')) = ⊥ := by
      rw [eq_bot_iff] at hQO ⊢
      intro c hc
      apply hQO
      simpa [Ideal.mem_comap, rename_C] using hc
    obtain ⟨u, v, ⟨γ, hu⟩, ⟨δ, hv⟩, huQ, hvQ, huv⟩ := hU _ (comap_isMultiProjPrime hQ) hle hO
    refine ⟨rename (midVar ι₂) u, rename (midVar ι₂) v, ⟨_, isMultiHomog_rename' hu⟩,
      ⟨_, isMultiHomog_rename' hv⟩, huQ, hvQ, ?_⟩
    have := (rename_mem_mcIdeal_iff O x w z _).mpr huv
    simpa only [map_sub, map_mul] using this

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SegreFlagIndepHomogeneousImpliesGeneral
section
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

universe u

namespace SegreFlagIndep

theorem isSymmetric_homogeneousComponent {σ R : Type*} [CommSemiring R] {G : MvPolynomial σ R}
    (hG : G.IsSymmetric) (c : ℕ) : (homogeneousComponent c G).IsSymmetric := by
  intro e
  ext d
  obtain ⟨d', rfl⟩ : ∃ d', d = d'.mapDomain e :=
    ⟨d.mapDomain e.symm, by rw [← Finsupp.mapDomain_comp]; simp⟩
  rw [coeff_rename_mapDomain _ e.injective, coeff_homogeneousComponent,
    coeff_homogeneousComponent, Finsupp.degree_mapDomain]
  conv_rhs => rw [← hG e, coeff_rename_mapDomain _ e.injective]

section Numbers

variable {F : Type*} [Field F] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  (I : IFamily F ι) (V : Ideal (MRingOver F ι)) (n : ℕ)

def listNum (L : List (K → ℤ)) : ℤ :=
  if h : L.length = n then I V n (fun j => L.get (Fin.cast h.symm j)) else 0

theorem polyNum_eq {r : ℕ} (deg : Fin r → K → ℤ) (Q : MvPolynomial (Fin r) ℤ) :
    polyNum I V n deg Q = ∑ μ ∈ Q.support, Q.coeff μ * listNum I V n (monoList deg μ) := rfl

theorem polyNum_eq_of_subset {r : ℕ} (deg : Fin r → K → ℤ) (Q : MvPolynomial (Fin r) ℤ)
    (S : Finset (Fin r →₀ ℕ)) (hS : Q.support ⊆ S) :
    polyNum I V n deg Q = ∑ μ ∈ S, Q.coeff μ * listNum I V n (monoList deg μ) := by
  rw [polyNum_eq]
  exact Finset.sum_subset hS fun μ _ hμ => by rw [notMem_support_iff.mp hμ, zero_mul]

def polyNumHom {r : ℕ} (deg : Fin r → K → ℤ) : MvPolynomial (Fin r) ℤ →+ ℤ where
  toFun := polyNum I V n deg
  map_zero' := by simp [polyNum]
  map_add' P Q := by
    classical
    rw [polyNum_eq_of_subset I V n deg (P + Q) (P.support ∪ Q.support) support_add,
      polyNum_eq_of_subset I V n deg P (P.support ∪ Q.support) Finset.subset_union_left,
      polyNum_eq_of_subset I V n deg Q (P.support ∪ Q.support) Finset.subset_union_right,
      ← Finset.sum_add_distrib]
    simp only [coeff_add, add_mul]

theorem polyNumHom_apply {r : ℕ} (deg : Fin r → K → ℤ) (Q : MvPolynomial (Fin r) ℤ) :
    polyNumHom I V n deg Q = polyNum I V n deg Q := rfl

theorem polyNum_monomial {r : ℕ} (deg : Fin r → K → ℤ) (μ : Fin r →₀ ℕ) (a : ℤ) :
    polyNum I V n deg (monomial μ a) = a * listNum I V n (monoList deg μ) := by
  classical
  rw [polyNum_eq_of_subset I V n deg _ {μ} support_monomial_subset]
  simp

end Numbers

section Lists

variable {K : Type}

theorem monoList_append {N r : ℕ} (d : Fin N → K → ℤ) (Y : Fin r → K → ℤ) (α : Fin N →₀ ℕ)
    (ν : Fin r →₀ ℕ) :
    monoList (Fin.append d Y) (α.mapDomain (Fin.castAdd r) + ν.mapDomain (Fin.natAdd N)) =
      monoList d α ++ monoList Y ν := by
  unfold monoList
  rw [← List.ofFn_id, List.ofFn_add, List.flatMap_append, List.ofFn_eq_map, List.ofFn_eq_map,
    List.flatMap_map, List.flatMap_map]
  congr 1
  · congr 1
    funext s
    have h1 : (Fin.castLE (Nat.le_add_right N r) s) = Fin.castAdd r s := rfl
    simp only [id, h1, Finsupp.add_apply,
      Finsupp.mapDomain_apply (Fin.castAdd_injective N r), Fin.append_left]
    rw [Finsupp.mapDomain_of_notMem_range, add_zero]
    rintro ⟨j, hj⟩
    have := congrArg Fin.val hj
    simp at this
    omega
  · congr 1
    funext s
    simp only [id, Finsupp.add_apply,
      Finsupp.mapDomain_apply (Fin.natAdd_injective r N), Fin.append_right]
    rw [Finsupp.mapDomain_of_notMem_range, zero_add]
    rintro ⟨j, hj⟩
    have := congrArg Fin.val hj
    simp at this
    omega

theorem length_monoList {N : ℕ} (d : Fin N → K → ℤ) (α : Fin N →₀ ℕ) :
    (monoList d α).length = α.degree := by
  rw [Finsupp.degree_eq_sum]
  simp [monoList, List.length_flatMap, Fin.sum_univ_def]

theorem monoList_ones {n : ℕ} (Y : Fin n → K → ℤ) :
    monoList Y (∑ j : Fin n, Finsupp.single j 1) = List.ofFn Y := by
  classical
  rw [List.ofFn_eq_map]
  unfold monoList
  have : ∀ s : Fin n, (∑ j : Fin n, Finsupp.single j 1) s = 1 := by
    intro s
    simp [Finsupp.finsetSum_apply, Finsupp.single_apply]
  simp only [this, List.replicate_one]
  induction List.finRange n with
  | nil => rfl
  | cons a l ih => simp [ih]

end Lists

section Expand

variable {F : Type*} [Field F] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  (I : IFamily F ι) (V : Ideal (MRingOver F ι)) (e : ℕ)

theorem polyNum_mul_monomial {N r : ℕ} (d : Fin N → K → ℤ) (Y : Fin r → K → ℤ)
    (A : MvPolynomial (Fin N) ℤ) (ν : Fin r →₀ ℕ) :
    polyNum I V e (Fin.append d Y) (rename (Fin.castAdd r) A * rename (Fin.natAdd N) (monomial ν 1)) =
      ∑ α ∈ A.support, A.coeff α * listNum I V e (monoList d α ++ monoList Y ν) := by
  conv_lhs => rw [as_sum A]
  rw [map_sum, Finset.sum_mul, ← polyNumHom_apply, map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [rename_monomial, rename_monomial, monomial_mul, polyNumHom_apply, polyNum_monomial,
    monoList_append, mul_one]

theorem polyNum_mul_eq_sum {N r : ℕ} (d : Fin N → K → ℤ) (Y : Fin r → K → ℤ)
    (A : MvPolynomial (Fin N) ℤ) (R : MvPolynomial (Fin r) ℤ) :
    polyNum I V e (Fin.append d Y) (rename (Fin.castAdd r) A * rename (Fin.natAdd N) R) =
      ∑ ν ∈ R.support, R.coeff ν *
        polyNum I V e (Fin.append d Y) (rename (Fin.castAdd r) A * rename (Fin.natAdd N) (monomial ν 1)) := by
  conv_lhs => rw [as_sum R]
  rw [map_sum, Finset.mul_sum, ← polyNumHom_apply, map_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  have : monomial ν (R.coeff ν) = R.coeff ν • monomial ν (1 : ℤ) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [this, map_zsmul, mul_smul_comm, map_zsmul, polyNumHom_apply, smul_eq_mul]

theorem prod_X_natAdd (N n : ℕ) :
    (∏ j : Fin n, X (Fin.natAdd N j) : MvPolynomial (Fin (N + n)) ℤ) =
      rename (Fin.natAdd N) (monomial (∑ j : Fin n, Finsupp.single j 1) 1) := by
  rw [monomial_sum_one, map_prod]
  simp [rename_X, ← X.eq_1]

end Expand

end SegreFlagIndep

variable (F : Type*) [Field F] (Ω : Type*) [Field Ω] [Algebra F Ω]
variable {K : Type} [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]

def SegreFlagIndep₂.Statement : Prop :=
  ∀ (x : (Σ k, ι k) → Ω) (e : ℕ), IsProjVarF (mcIdeal F x) e →
    ∀ (N : ℕ) (E : Type u) [AddCommGroup E] [Module Ω E] (B : ChartBundle F (mseg x) N E)
      (fl₁ fl₂ : FullFlag F x B) (I₀ : IFamily F ι), IsFieldIntersection I₀ →
    ∀ G : MvPolynomial (Fin N) ℤ, G.IsSymmetric →
    ∀ (r : ℕ) (Y : Fin r → K → ℤ) (R : MvPolynomial (Fin r) ℤ),
      polyNum I₀ (mcIdeal F x) e (Fin.append fl₁.deg Y)
          (rename (Fin.castAdd r) G * rename (Fin.natAdd N) R) =
        polyNum I₀ (mcIdeal F x) e (Fin.append fl₂.deg Y)
          (rename (Fin.castAdd r) G * rename (Fin.natAdd N) R)

namespace SegreFlagIndep

theorem segreFlagIndep_homogeneous_implies_general (h : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.SegreFlagIndep.Statement.{u} F Ω ι) :
    SegreFlagIndep₂.Statement.{u} F Ω ι := by
  intro x e hV N E _ _ B fl₁ fl₂ I₀ hI G hG r Y R
  have hsplit : ∀ d : Fin N → K → ℤ,
      polyNum I₀ (mcIdeal F x) e (Fin.append d Y) (rename (Fin.castAdd r) G * rename (Fin.natAdd N) R) =
        ∑ c ∈ Finset.range (G.totalDegree + 1), polyNum I₀ (mcIdeal F x) e (Fin.append d Y)
          (rename (Fin.castAdd r) (homogeneousComponent c G) * rename (Fin.natAdd N) R) := by
    intro d
    conv_lhs => rw [← sum_homogeneousComponent G]
    rw [map_sum, Finset.sum_mul, ← polyNumHom_apply, map_sum]
    rfl
  rw [hsplit, hsplit]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [polyNum_mul_eq_sum, polyNum_mul_eq_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  congr 1
  set Gc := homogeneousComponent c G
  have hGc : Gc.IsHomogeneous c := homogeneousComponent_isHomogeneous c G
  set L := monoList Y ν

  have hmono : ∀ d : Fin N → K → ℤ,
      polyNum I₀ (mcIdeal F x) e (Fin.append d Y)
          (rename (Fin.castAdd r) Gc * rename (Fin.natAdd N) (monomial ν 1)) =
        polyNum I₀ (mcIdeal F x) e (Fin.append d L.get)
          (rename (Fin.castAdd L.length) Gc * ∏ j : Fin L.length, X (Fin.natAdd N j)) := by
    intro d
    rw [prod_X_natAdd, polyNum_mul_monomial, polyNum_mul_monomial, monoList_ones, List.ofFn_get]
  rw [hmono, hmono]
  by_cases hce : c + L.length = e
  · exact h x e hV N E B fl₁ fl₂ I₀ hI Gc (isSymmetric_homogeneousComponent hG c) c L.length L.get
      hGc hce
  · have hzero : ∀ d : Fin N → K → ℤ, polyNum I₀ (mcIdeal F x) e (Fin.append d L.get)
        (rename (Fin.castAdd L.length) Gc * ∏ j : Fin L.length, X (Fin.natAdd N j)) = 0 := by
      intro d
      rw [prod_X_natAdd, polyNum_mul_monomial, monoList_ones, List.ofFn_get]
      refine Finset.sum_eq_zero fun α hα => ?_
      have hdeg : α.degree = c := by
        have := hGc (mem_support_iff.mp hα)
        rwa [Finsupp.degree_eq_weight_one]
      rw [listNum, dif_neg, mul_zero]
      rw [List.length_append, length_monoList, hdeg]
      exact hce
    rw [hzero, hzero]

end SegreFlagIndep

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpHorizontal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Lemmas

def BlowUpHorizontalSat.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ), IsModelOver P n →
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    (∀ W : Ideal (MRing ι O), W.IsPrime → P ≤ W → IsRelevant W → (C ϖ : MRing ι O) ∉ W →
      ∃ j, ∀ j', ∃ v w : MRing ι O, v ∉ W ∧ v * u j' - w * u j ∈ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing (extIdx ι J) O), divCycle (blowUpOf P u) (liftForm x) W ≠ 0 →
      (C ϖ : MRing (extIdx ι J) O) ∉ W →
      ∀ F : MRing (extIdx ι J) O, F ∈ W ↔ ∃ s : MRing ι O, s ∉ W.comap (liftForm (ι := ι) (J := J) (R := O)) ∧
        (liftForm (ι := ι) (J := J) (R := O)) s * F ∈ blowUpOf P u ⊔ Ideal.map (liftForm (ι := ι) (J := J) (R := O)) (W.comap (liftForm (ι := ι) (J := J) (R := O)))

def BlowUpHorizontalMult.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ), IsModelOver P n →
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    (∀ W : Ideal (MRing ι O), W.IsPrime → P ≤ W → IsRelevant W → (C ϖ : MRing ι O) ∉ W →
      ∃ j, ∀ j', ∃ v w : MRing ι O, v ∉ W ∧ v * u j' - w * u j ∈ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing (extIdx ι J) O), divCycle (blowUpOf P u) (liftForm x) W ≠ 0 →
      (C ϖ : MRing (extIdx ι J) O) ∉ W →
      divCycle P x (W.comap (liftForm (ι := ι) (J := J) (R := O))) = divCycle (blowUpOf P u) (liftForm x) W

def BlowUpHorizontalLift.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ), IsModelOver P n →
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    (∀ W : Ideal (MRing ι O), W.IsPrime → P ≤ W → IsRelevant W → (C ϖ : MRing ι O) ∉ W →
      ∃ j, ∀ j', ∃ v w : MRing ι O, v ∉ W ∧ v * u j' - w * u j ∈ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing ι O), divCycle P x W ≠ 0 → (C ϖ : MRing ι O) ∉ W →
      ∃ W' : Ideal (MRing (extIdx ι J) O), divCycle (blowUpOf P u) (liftForm x) W' ≠ 0 ∧
        (C ϖ : MRing (extIdx ι J) O) ∉ W' ∧ W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W

def BlowUpHorizontalStrict.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ), IsModelOver P n →
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    (∀ W : Ideal (MRing ι O), W.IsPrime → P ≤ W → IsRelevant W → (C ϖ : MRing ι O) ∉ W →
      ∃ j, ∀ j', ∃ v w : MRing ι O, v ∉ W ∧ v * u j' - w * u j ∈ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing (extIdx ι J) O), divCycle (blowUpOf P u) (liftForm x) W ≠ 0 →
      (C ϖ : MRing (extIdx ι J) O) ∉ W →
      (∃ j, u j ∉ W.comap (liftForm (ι := ι) (J := J) (R := O))) → W = blowUpOf (W.comap (liftForm (ι := ι) (J := J) (R := O))) u

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagBundleChartSection
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def FlagBundleChartSection.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) (y : (Σ k, ι k) → Ω)
    (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E]
      (B : ChartBundle F (segreVec y) N E) (w : Module.Basis (Fin N) Ω E) (b : Fin N → K → ℤ),
      IsFlagFrame y B w b →
    ∀ (M : ℕ) (a : K → ℤ) (φ : Fin M → Module.Dual Ω E), IsTwistedDualGens y B a φ →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] (t : Fin N → Φ), AlgebraicIndependent Ω t →
    ∀ (i : Fin N) (c : ∀ k, ι k), segreVec y c ≠ 0 →
      ∃ (dl dm : Option K → ℕ) (l μ : MRing (bundleIdx ι M) F) (m : K → ℕ),
        μ = ∏ k, (X ⟨some k, c k⟩ : MRing (bundleIdx ι M) F) ^ m k ∧
        IsMultiHomog l dl ∧ IsMultiHomog μ dm ∧
        (fun o => (dl o : ℤ) - dm o) = zetaDeg + liftDeg (b i - a) ∧
        eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ (truncCoord t ((i : ℕ) + 1))) l =
          t i * eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω))
            (projCoord y w φ (truncCoord t ((i : ℕ) + 1))) μ ∧
        ∀ q ∈ projIdeal F y w φ (truncCoord t i), ∃ n : ℕ,
          (∏ k, (X ⟨some k, c k⟩ : MRing (bundleIdx ι M) F)) ^ n * q ∈
            projIdeal F y w φ (truncCoord t ((i : ℕ) + 1)) ⊔ Ideal.span {l}

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

