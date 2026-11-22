import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0016
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0018
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0015
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0011
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0019
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0014
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PPFContracted
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.Intersections.TableDegreeThreeBase
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0020

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PLocalIntegralClosureFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem LocalIntegralClosureFinite.proof (hN : NoetherIntegralClosureFinite.Statement.{u})
    (hF : FunctionFieldFinite.Statement.{u}) (hQ : DegZeroLocQuot.Statement.{u})
    (hD : MChartDehomog.Statement.{u}) (hFr : DegZeroLocFrac.Statement.{u}) :
    LocalIntegralClosureFinite.Statement.{u} := by
  intro F _ K K' _ _ _ _ j ι' _ P' hP' hdim W hW hle
  have := hP'.isPrime
  have := hW.isPrime
  set P := contractPrime j P'
  set φ := contractFracMap j P'
  set A' := (degZeroLoc P {W}).map φ
  set L := homFracDegZero P'
  choose u hu using hW.relevant
  obtain ⟨hRA, hloc⟩ := degZeroLoc_map_eq_mul_inv hQ hD P W hle u hu φ
  set S := Set.range fun v => φ (chartMap P u (X v))
  have hAL : ∀ a ∈ A', a ∈ L := by
    rintro _ ⟨a, ha, rfl⟩
    exact map_homFracDegZero_le j ι' P' ⟨a, mem_homFracDegZero_of_mem_degZeroLoc P {W} a ha, rfl⟩
  have hEL : IntermediateField.adjoin F S ≤ L :=
    IntermediateField.adjoin_le_iff.mpr fun _ hx => hAL _ (hRA (Algebra.subset_adjoin hx))
  have hAE : ∀ a ∈ A', a ∈ IntermediateField.adjoin F S := fun a ha => by
    obtain ⟨r, hr, d, hd, -, -, rfl⟩ := hloc a ha
    exact mul_mem (IntermediateField.algebra_adjoin_le_adjoin F S hr)
      (inv_mem (IntermediateField.algebra_adjoin_le_adjoin F S hd))
  have hκE : (homFracDegZero P).map φ ≤ IntermediateField.adjoin F S := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨y, hy, w, hw, -, rfl⟩ := hFr F K (fun k => ι' (j k)) P
      (isMultiProjPrime_contractPrime j ι' hP') {W} (Set.finite_singleton W)
      (fun W' h => by rw [Set.mem_singleton_iff.mp h]; exact hW) z hz
    rw [map_div₀]
    exact div_mem (hAE _ ⟨y, hy, rfl⟩) (hAE _ ⟨w, hw, rfl⟩)
  have hdeg : IntermediateField.relfinrank ((homFracDegZero P).map φ) L ≠ 0 :=
    hF F K K' j ι' P' hP' hdim
  rw [← IntermediateField.relfinrank_mul_relfinrank hκE hEL,
    IntermediateField.relfinrank_eq_finrank_of_le hEL] at hdeg
  exact exists_finset_integral_span hN (Set.finite_range _) A' L hRA hloc hEL
    (FiniteDimensional.of_finrank_pos (Nat.pos_of_ne_zero (right_ne_zero_of_mul hdeg)))

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PSemilocalIntegral
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

namespace SemilocalIntegral

section Dim

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {F : Type u} [Field F]

omit [DecidableEq K] in

theorem exists_ringKrullDim_eq_nat (Q : Ideal (MRing ι F)) [Q.IsPrime] :
    ∃ D : ℕ, ringKrullDim (MRing ι F ⧸ Q) = D := by
  have h1 : (0 : WithBot ℕ∞) ≤ ringKrullDim (MRing ι F ⧸ Q) := ringKrullDim_nonneg_of_nontrivial
  have h2 := PFContracted.ringKrullDim_lt_top (F := F) Q
  cases h : ringKrullDim (MRing ι F ⧸ Q) with
  | bot =>
    rw [h] at h1
    exact absurd h1 (by simp)
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      rw [h] at h2
      exact absurd h2 (by simp)
    | coe D => exact ⟨D, rfl⟩

theorem exists_relDim_eq_int (Q : Ideal (MRing ι F)) [Q.IsPrime] :
    ∃ d : ℤ, relDim Q = ((d : WithTop ℤ) : WithBot (WithTop ℤ)) := by
  obtain ⟨D, hD⟩ := exists_ringKrullDim_eq_nat Q
  exact ⟨_, PFContracted.relDim_eq_int hD⟩

theorem relDim_lt_of_lt {Q Q₂ : Ideal (MRing ι F)} [Q.IsPrime] [Q₂.IsPrime] (h : Q < Q₂) :
    relDim Q₂ < relDim Q := by
  obtain ⟨x, hx, hxQ⟩ := SetLike.exists_of_lt h
  have hle := Inter.krullDim_quot_add_one_le h.le hx hxQ
  obtain ⟨D, hD⟩ := exists_ringKrullDim_eq_nat Q
  obtain ⟨D₂, hD₂⟩ := exists_ringKrullDim_eq_nat Q₂
  rw [hD, hD₂] at hle
  have : D₂ + 1 ≤ D := by exact_mod_cast hle
  rw [PFContracted.relDim_eq_int hD, PFContracted.relDim_eq_int hD₂]
  exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr (by omega))

end Dim

section Centre

variable {F : Type u} [Field F] {K K' : Type} [Fintype K] [DecidableEq K] [Fintype K']
  [DecidableEq K'] {j : K ↪ K'} {ι' : K' → Type} [∀ k, Fintype (ι' k)]

omit [Fintype K'] [∀ k, Fintype (ι' k)] in

theorem contract_le {P' : Ideal (MRing ι' F)} [P'.IsPrime] {W : Ideal (MRing (fun k => ι' (j k)) F)}
    (hPW : contractPrime j P' ≤ W) (R : ValuationSubring (FractionRing (MRing ι' F ⧸ P')))
    (hR : ∀ a ∈ degZeroLoc (contractPrime j P') {W}, contractFracMap j P' a ∈ R)
    {y : Ideal (MRing ι' F)} (hy : IsMultiProjPrime y) (hP'y : P' ≤ y)
    (hcen : ∀ (b : K' → ℕ) (f g : MRing ι' F), IsMultiHomog f b → IsMultiHomog g b → g ∉ y →
      algebraMap (MRing ι' F ⧸ P') (FractionRing (MRing ι' F ⧸ P')) (Ideal.Quotient.mk P' f) /
          algebraMap (MRing ι' F ⧸ P') _ (Ideal.Quotient.mk P' g) ∈ R ∧
        (f ∈ y ↔ algebraMap (MRing ι' F ⧸ P') (FractionRing (MRing ι' F ⧸ P'))
            (Ideal.Quotient.mk P' f) / algebraMap (MRing ι' F ⧸ P') _ (Ideal.Quotient.mk P' g) ∈
          R.nonunits)) :
    contractPrime j y ≤ W := by
  have hy₀ := isMultiProjPrime_contractPrime j ι' hy
  intro a ha
  rw [← sum_weightedHomogeneousComponent (blockWeight _) a]
  refine finsum_induction (· ∈ W) W.zero_mem (fun _ _ => W.add_mem) (fun c => ?_)
  have hac := hy₀.multiHomog a ha c
  have hf : IsMultiHomog (weightedHomogeneousComponent (blockWeight _) c a) c :=
    weightedHomogeneousComponent_isWeightedHomogeneous _ _
  by_contra hfW
  choose i hi using hy₀.relevant
  have hu := isMultiHomog_prod_pow (R := F) i c
  have huy := (haveI := hy₀.isPrime; prod_pow_not_mem _ i hi c)
  have hmem := hR _ (div_mem_degZeroLoc _ {W} hu hf (fun h => hfW (hPW h))
    (fun W' hW' => (Set.mem_singleton_iff.mp hW') ▸ hfW))
  rw [map_div₀, contractFracMap_algebraMap, contractFracMap_algebraMap] at hmem
  have h2 := ((hcen _ _ _ (isMultiHomog_rename j ι' hf) (isMultiHomog_rename j ι' hu) huy).2).mp hac
  have hne : ∀ g, g ∉ P' → algebraMap (MRing ι' F ⧸ P') (FractionRing (MRing ι' F ⧸ P'))
      (Ideal.Quotient.mk P' g) ≠ 0 := fun g hg => by
    rwa [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
  have ha0 := hne _ (fun h => hfW (hPW h))
  have hu0 := hne _ (fun h => huy (hP'y h))
  rw [ValuationSubring.mem_nonunits_iff] at h2
  have h3 := (R.valuation_le_one_iff _).mpr hmem
  have h4 := mul_lt_one_of_lt_of_le h2 h3
  rw [← map_mul, div_mul_div_cancel₀ hu0, div_self ha0, map_one] at h4
  exact lt_irrefl _ h4

theorem semilocal_le (hC : ValuativeCentre.Statement.{u}) {P' : Ideal (MRing ι' F)} [P'.IsPrime]
    (hP' : IsMultiProjPrime P') {n : ℕ} (hP'n : relDim P' = (n + 1 : ℕ))
    (hPn : relDim (contractPrime j P') = (n + 1 : ℕ)) {W : Ideal (MRing (fun k => ι' (j k)) F)}
    (hW : IsMultiProjPrime W) (hWn : relDim W = (n : ℕ)) (hPW : contractPrime j P' ≤ W)
    (R : ValuationSubring (FractionRing (MRing ι' F ⧸ P')))
    (hR : ∀ a ∈ degZeroLoc (contractPrime j P') {W}, contractFracMap j P' a ∈ R) :
    ∀ x ∈ degZeroLoc P' (fibrePrimes j P' W), x ∈ R := by
  have hF : ∀ c : F, algebraMap F (FractionRing (MRing ι' F ⧸ P')) c ∈ R := fun c => by
    rw [← (contractFracMap j P').commutes c]
    exact hR _ (Subalgebra.algebraMap_mem _ c)
  obtain ⟨y, hy, hP'y, hcen⟩ := hC F K' ι' P' hP' R hF
  have hle := contract_le hPW R hR hy hP'y hcen
  have := hy.isPrime
  have := hW.isPrime
  have hcases : contractPrime j y = contractPrime j P' ∨ contractPrime j y = W := by
    by_contra hne
    push Not at hne
    have d1 : relDim (contractPrime j y) < relDim (contractPrime j P') :=
      relDim_lt_of_lt (lt_of_le_of_ne (Ideal.comap_mono hP'y) hne.1.symm)
    have d2 : relDim W < relDim (contractPrime j y) := relDim_lt_of_lt (lt_of_le_of_ne hle hne.2)
    obtain ⟨d, hd⟩ := exists_relDim_eq_int (contractPrime j y)
    rw [hd, hPn, PFContracted.natCast_withBot_withTop] at d1
    rw [hd, hWn, PFContracted.natCast_withBot_withTop] at d2
    have e1 := WithTop.coe_lt_coe.mp (WithBot.coe_lt_coe.mp d1)
    have e2 := WithTop.coe_lt_coe.mp (WithBot.coe_lt_coe.mp d2)
    push_cast at e1
    omega
  have havoid : ∀ g, g ∉ P' → (∀ W' ∈ fibrePrimes j P' W, g ∉ W') → g ∉ y := by
    rcases hcases with h | h
    · have hyP' : y = P' := by
        by_contra hne
        have d1 := relDim_lt_of_lt (lt_of_le_of_ne hP'y (Ne.symm hne))
        have d2 := ContractRelDimLe.proof F K K' j ι' y hy
        rw [h, hPn, ← hP'n] at d2
        exact lt_irrefl _ (lt_of_lt_of_le d1 d2)
      exact fun g hg _ => hyP' ▸ hg
    · exact fun g _ hgW => hgW y ⟨hy, hP'y, h⟩
  intro x hx
  unfold degZeroLoc at hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨b, f, g, hf, hg, hgP, hgW, rfl⟩ := hx
    exact (hcen b f g hf hg (havoid g hgP hgW)).1
  | algebraMap c => exact hF c
  | add a a' _ _ ha ha' => exact R.add_mem _ _ ha ha'
  | mul a a' _ _ ha ha' => exact R.mul_mem _ _ ha ha'

end Centre

theorem proof (hC : ValuativeCentre.Statement.{u}) : SemilocalIntegral.Statement.{u} := by
  intro F _ K K' _ _ _ _ j ι' _ P' hP' n hP'n hPn W hW hWn hPW
  have := hP'.isPrime
  let f : degZeroLoc (contractPrime j P') {W} →+* FractionRing (MRing ι' F ⧸ P') :=
    (algebraMap (degZeroLoc P' (fibrePrimes j P' W)) (FractionRing (MRing ι' F ⧸ P'))).comp
      (algebraMap (degZeroLoc (contractPrime j P') {W}) (degZeroLoc P' (fibrePrimes j P' W)))
  refine ⟨fun b => ?_⟩
  refine RingHom.IsIntegralElem.of_map (g := algebraMap (degZeroLoc P' (fibrePrimes j P' W))
    (FractionRing (MRing ι' F ⧸ P'))) Subtype.val_injective ?_
  have hmem : (b : FractionRing (MRing ι' F ⧸ P')) ∈ ⨅ V : {V : ValuationSubring
      (FractionRing (MRing ι' F ⧸ P')) // Set.range f ⊆ V.toSubring}, V.1.toSubring := by
    rw [Subring.mem_iInf]
    rintro ⟨V, hV⟩
    exact semilocal_le hC hP' hP'n hPn hW hWn hPW V (fun a ha => hV ⟨⟨a, ha⟩, rfl⟩) b b.2
  rw [iInf_valuationSubring_superset, ← RingHom.coe_range, Subring.closure_eq] at hmem
  obtain ⟨p, hp, hpx⟩ := (hmem : IsIntegral f.range (b : FractionRing (MRing ι' F ⧸ P')))
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    ((Polynomial.mem_lifts p).mpr
      (Polynomial.map_surjective f.rangeRestrict (fun ⟨_, a, ha⟩ => ⟨a, Subtype.ext ha⟩) p)) hp
  refine ⟨q, hqm, ?_⟩
  change Polynomial.eval₂ (f.range.subtype.comp f.rangeRestrict) (b : FractionRing _) q = 0
  rw [← Polynomial.eval₂_map, hq]
  exact hpx

end SemilocalIntegral

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PValuativeCentre
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

section Graded

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type*} [Field F]
  {κ : Type*} [CommRing κ]

def blockSpecial (ρ : MRing ι F →+* κ) : MRing ι F →+* MvPolynomial K κ :=
  eval₂Hom (C.comp (ρ.comp C)) fun v => C (ρ (X v)) * X v.1

theorem blockSpecial_monomial (ρ : MRing ι F →+* κ) (d : (Σ k, ι k) →₀ ℕ) (a : F) :
    blockSpecial ρ (monomial d a) = C (ρ (monomial d a)) *
      monomial (Finsupp.equivFunOnFinite.symm (Finsupp.weight (blockWeight ι) d)) 1 := by
  have hT : (monomial (Finsupp.equivFunOnFinite.symm (Finsupp.weight (blockWeight ι) d)) (1 : κ)) =
      d.prod fun v n => (X v.1 : MvPolynomial K κ) ^ n := by
    rw [← prod_pow_blockWeight, monomial_eq, C_1, one_mul,
      Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    rfl
  rw [hT, blockSpecial, coe_eval₂Hom, eval₂_monomial, monomial_eq, map_mul, map_mul,
    map_finsuppProd, map_finsuppProd]
  simp only [RingHom.comp_apply, mul_pow, map_pow]
  rw [Finsupp.prod_mul, mul_assoc]

theorem coeff_blockSpecial (ρ : MRing ι F →+* κ) (f : MRing ι F) (e : K →₀ ℕ) :
    coeff e (blockSpecial ρ f) = ρ (weightedHomogeneousComponent (blockWeight ι) (⇑e) f) := by
  classical
  conv_lhs => rw [f.as_sum]
  rw [weightedHomogeneousComponent_apply, map_sum, coeff_sum, map_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [blockSpecial_monomial, coeff_C_mul, coeff_monomial]
  have hiff : Finsupp.equivFunOnFinite.symm (Finsupp.weight (blockWeight ι) d) = e ↔
      Finsupp.weight (blockWeight ι) d = ⇑e := by
    rw [Equiv.symm_apply_eq]; rfl
  by_cases h : Finsupp.weight (blockWeight ι) d = ⇑e
  · rw [if_pos (hiff.mpr h), if_pos h, mul_one]
  · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h, mul_zero]

end Graded

theorem ValuativeCentre.proof : ValuativeCentre.Statement.{u} := by
  intro F _ K _ _ ι _ P hP
  have := hP.isPrime
  intro R hF
  set L := FractionRing (MRing ι F ⧸ P)
  let φ : MRing ι F →+* L := (algebraMap (MRing ι F ⧸ P) L).comp (Ideal.Quotient.mk P)
  have hφ : ∀ p, φ p = 0 ↔ p ∈ P := fun p => by
    simp only [φ, RingHom.comp_apply, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]

  have hmax : ∀ k, ∃ i, (X ⟨k, i⟩ : MRing ι F) ∉ P ∧
      ∀ j, R.valuation (φ (X ⟨k, j⟩)) ≤ R.valuation (φ (X ⟨k, i⟩)) := by
    intro k
    classical
    obtain ⟨i₀, hi₀⟩ := hP.relevant k
    obtain ⟨i, hi, hmx⟩ := Finset.exists_max_image
      (Finset.univ.filter fun j => (X ⟨k, j⟩ : MRing ι F) ∉ P)
      (fun j => R.valuation (φ (X ⟨k, j⟩))) ⟨i₀, by simp [hi₀]⟩
    refine ⟨i, (Finset.mem_filter.mp hi).2, fun j => ?_⟩
    by_cases hj : (X ⟨k, j⟩ : MRing ι F) ∈ P
    · rw [(hφ _).mpr hj, map_zero]; exact zero_le
    · exact hmx j (by simp [hj])
  choose c hcP hcmax using hmax

  have hchart : ∀ p, chartMap P c p ∈ R := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a => rw [chartMap, aeval_C]; exact hF a
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p v hp =>
      rw [map_mul]
      refine mul_mem hp ?_
      rw [chartMap, aeval_X, ← R.valuation_le_one_iff, map_div₀]
      have h0 : R.valuation (φ (X ⟨v.1, c v.1⟩)) ≠ 0 := by
        rw [Ne, Valuation.zero_iff, hφ]; exact hcP v.1
      exact (div_le_one₀ (zero_lt_iff.mpr h0)).mpr (hcmax v.1 v.2)
  let χ : MRing ι F →+* R := (chartMap P c).toRingHom.codRestrict R hchart
  have hχ : ∀ p, (χ p : L) = chartMap P c p := fun p => rfl
  let ρ : MRing ι F →+* IsLocalRing.ResidueField R := (IsLocalRing.residue R).comp χ
  let θ : MRing ι F →+* MvPolynomial K (IsLocalRing.ResidueField R) := blockSpecial ρ
  have hdeh : ∀ f b, IsMultiHomog f b → chartMap P c f = φ f / φ (chartMonomial c b) :=
    fun f b hf => MChartDehomog.proof F K ι P c hcP f b hf
  have hmon : ∀ b, φ (chartMonomial c b) ≠ 0 := fun b => by
    simp only [chartMonomial, map_prod, map_pow]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (fun h => hcP k ((hφ _).mp h))

  have hy : ∀ f, f ∈ RingHom.ker θ ↔
      ∀ b : K → ℕ, ρ (weightedHomogeneousComponent (blockWeight ι) b f) = 0 := by
    intro f
    rw [RingHom.mem_ker]
    constructor
    · intro h b
      have := congrArg (coeff (Finsupp.equivFunOnFinite.symm b)) h
      rwa [coeff_blockSpecial, coeff_zero, Finsupp.coe_equivFunOnFinite_symm] at this
    · intro h
      ext e
      rw [coeff_blockSpecial, coeff_zero, h]
  have hyform : ∀ f b, IsMultiHomog f b → (f ∈ RingHom.ker θ ↔ ρ f = 0) := by
    intro f b hf
    rw [hy]
    constructor
    · intro h
      have := h b
      rwa [IsWeightedHomogeneous.weightedHomogeneousComponent_same hf] at this
    · intro h b'
      by_cases hb : b' = b
      · rw [hb, IsWeightedHomogeneous.weightedHomogeneousComponent_same hf]; exact h
      · rw [IsWeightedHomogeneous.weightedHomogeneousComponent_ne b' hf hb, map_zero]
  refine ⟨RingHom.ker θ, ⟨RingHom.ker_isPrime θ, ?_, ?_⟩, ?_, ?_⟩
  ·
    intro f hf b
    rw [hy] at hf ⊢
    intro b'
    have hb := weightedHomogeneousComponent_isWeightedHomogeneous (w := blockWeight ι) b f
    by_cases hbb : b' = b
    · rw [hbb, IsWeightedHomogeneous.weightedHomogeneousComponent_same hb]; exact hf b
    · rw [IsWeightedHomogeneous.weightedHomogeneousComponent_ne b' hb hbb, map_zero]
  ·
    intro k
    refine ⟨c k, fun h => ?_⟩
    have hX := isWeightedHomogeneous_X F (blockWeight ι) (⟨k, c k⟩ : Σ k, ι k)
    rw [hyform _ _ hX] at h
    have h1 : χ (X ⟨k, c k⟩) = 1 := by
      apply Subtype.ext
      rw [hχ, chartMap, aeval_X]
      exact div_self (fun h' => hcP k ((hφ _).mp h'))
    simp only [ρ, RingHom.comp_apply, h1, map_one] at h
    exact one_ne_zero h
  ·
    intro f hf
    rw [hy]
    intro b
    have hb := weightedHomogeneousComponent_isWeightedHomogeneous (w := blockWeight ι) b f
    have h0 : χ (weightedHomogeneousComponent (blockWeight ι) b f) = 0 := by
      apply Subtype.ext
      rw [hχ, hdeh _ _ hb, (hφ _).mpr (hP.multiHomog f hf b), zero_div]
      rfl
    simp only [ρ, RingHom.comp_apply, h0, map_zero]
  ·
    intro b f g hf hg hgy
    change φ f / φ g ∈ R ∧ (f ∈ RingHom.ker θ ↔ φ f / φ g ∈ R.nonunits)
    have hgu : IsUnit (χ g) := by
      rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
      exact fun h => hgy ((hyform g b hg).mpr h)
    have hg0 : (χ g : L) ≠ 0 := fun h => hgu.ne_zero (Subtype.ext h)
    have hquot : φ f / φ g = ((χ f * ↑hgu.unit⁻¹ : R) : L) := by
      have e1 : φ f / φ g = (χ f : L) / (χ g : L) := by
        rw [hχ, hχ, hdeh f b hf, hdeh g b hg, div_div_div_cancel_right₀ (hmon b)]
      have e2 : (χ g : L) * ((↑hgu.unit⁻¹ : R) : L) = 1 := by
        rw [← Subring.coe_mul, IsUnit.mul_val_inv]; rfl
      rw [e1, div_eq_iff hg0, Subring.coe_mul, mul_assoc, mul_comm _ (χ g : L), e2, mul_one]
    rw [hquot, ValuationSubring.coe_mem_nonunits_iff, ← IsLocalRing.residue_eq_zero_iff, map_mul,
      hyform f b hf]
    refine ⟨Subtype.mem _, ?_⟩
    have hu : IsLocalRing.residue R (↑hgu.unit⁻¹ : R) ≠ 0 :=
      (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr (Units.isUnit _)
    simp only [ρ, RingHom.comp_apply, mul_eq_zero]
    exact ⟨Or.inl, fun h => h.resolve_right hu⟩

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

