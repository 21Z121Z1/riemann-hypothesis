import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Bundle0018
import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsHodgeFlag
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0001

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PPlueckerNeZero
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

theorem PlueckerNeZero.proof : PlueckerNeZero.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D Pl τ i
  classical

  choose cX hcX using D.arith.2.1.2.2
  have hy : ∀ k, D.y ⟨k, cX k⟩ ≠ 0 := by
    intro k h0
    apply hcX k
    rw [mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0, map_zero, zero_mul]
  have hseg : segreCoord D.y cX ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hy k

  obtain ⟨M, f, cc, -, -, hsum, hPr⟩ := Pl.generates τ i cX hseg
  have hM : 0 < M := by
    rcases Nat.eq_zero_or_pos M with h | h
    · subst h
      simp at hsum
    · exact h
  obtain ⟨b, -, -, hA⟩ := hPr ⟨0, hM⟩
  have hmono : StrictMono (Fin.castLE (step_le i)) := Fin.strictMono_castLE (step_le i)
  obtain ⟨a, -, ha⟩ := hA _ hmono
  have h1 := ha _ hmono
  rw [if_pos rfl] at h1
  obtain ⟨m0, -, hm0⟩ := Finset.exists_ne_zero_of_sum_ne_zero (h1.symm ▸ one_ne_zero)
  have hb : Pl.gen τ i m0 (exteriorPower.ιMulti Ω _ (b ∘ Fin.castLE (step_le i))) ≠ 0 :=
    fun h => hm0 (by rw [h, zero_mul, mul_zero])

  have hc0 : ∃ c0 : Fin ((i : ℕ) + 1) → Fin D.N,
      Pl.gen τ i m0 (exteriorPower.ιMulti Ω _ (Pl.e τ ∘ c0)) ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    let B : Module.Basis (Fin D.N) Ω (E τ) := Module.Basis.mk (Pl.e_indep τ) (Pl.e_span τ).ge
    have hzero : (Pl.gen τ i m0).compAlternatingMap (exteriorPower.ιMulti Ω ((i : ℕ) + 1)) = 0 := by
      refine Module.Basis.ext_alternating B fun v _ => ?_
      simp only [LinearMap.compAlternatingMap_apply, AlternatingMap.zero_apply, B, Module.Basis.coe_mk]
      exact hcon v
    apply hb
    have := congrArg (fun φ => φ (b ∘ Fin.castLE (step_le i))) hzero
    simpa using this
  obtain ⟨c0, hc0⟩ := hc0

  refine ⟨m0, ?_⟩
  let v : (Fin ((i : ℕ) + 1) → Fin D.N) → Fin ((i : ℕ) + 1) → Ψ × Fin D.N × Fin D.N :=
    fun c a => (τ, headIdx (step_le i) a, c a)
  let μ : (Fin ((i : ℕ) + 1) → Fin D.N) → (Ψ × Fin D.N × Fin D.N) →₀ ℕ :=
    fun c => ∑ a, Finsupp.single (v c a) 1
  let g : (Fin ((i : ℕ) + 1) → Fin D.N) → Ω :=
    fun c => Pl.gen τ i m0 (exteriorPower.ιMulti Ω _ (Pl.e τ ∘ c))
  let P : MvPolynomial (Ψ × Fin D.N × Fin D.N) Ω := ∑ c, monomial (μ c) (g c)
  have hP : Pl.pluecker τ i m0 = algebraMap _ Pl.ΩY P := by
    simp only [PlueckerData.pluecker, PlueckerData.gvar, PlueckerData.ofΩ, P, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← map_prod, ← map_mul]
    congr 1
    rw [show monomial (μ c) (g c) = C (g c) * monomial (μ c) 1 by rw [C_mul_monomial, mul_one],
      monomial_sum_one, mul_comm]
    rfl
  have hμ : ∀ c, μ c = μ c0 → c = c0 := by
    intro c h
    funext a
    have h2 := congrArg (fun φ : (Ψ × Fin D.N × Fin D.N) →₀ ℕ => φ (τ, headIdx (step_le i) a, c0 a)) h
    simp only [μ, v, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply, Prod.mk.injEq,
      true_and, headIdx, Fin.castLE_inj] at h2
    rw [Finset.sum_eq_single a (fun a' _ h' => if_neg fun h'' => h' h''.1) (by simp),
      Finset.sum_eq_single a (fun a' _ h' => if_neg fun h'' => h' h''.1) (by simp)] at h2
    by_contra hne
    simp [hne] at h2
  have hcoeff : coeff (μ c0) P = g c0 := by
    simp only [P, coeff_sum, coeff_monomial]
    rw [Finset.sum_eq_single c0 (fun c _ hc => if_neg fun h => hc (hμ c h)) (by simp), if_pos rfl]
  have hPne : P ≠ 0 := fun h => hc0 (by rw [h, coeff_zero] at hcoeff; exact hcoeff.symm)
  rw [hP]
  exact fun h => hPne (IsFractionRing.injective (MvPolynomial (Ψ × Fin D.N × Fin D.N) Ω) Pl.ΩY
    (by rw [h, map_zero]))

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.RingKrullDimLocalizationInt
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open Algebra MvPolynomial TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar)

theorem DimX.ringKrullDim_localization_int (B : Type) [CommRing B] [IsDomain B]
    [inst : Algebra ℤ B] [Algebra.FiniteType ℤ B] (hinj : Function.Injective (algebraMap ℤ B)) (t : ℕ)
    (ht : trdeg ℤ B = t) :
    ringKrullDim (Localization (Algebra.algebraMapSubmonoid B (nonZeroDivisors ℤ))) = t := by
  obtain rfl : inst = Ring.toIntAlgebra B := Subsingleton.elim _ _
  let : Algebra B (ℚ ⊗[ℤ] B) := Algebra.TensorProduct.rightAlgebra
  let M := Algebra.algebraMapSubmonoid B (nonZeroDivisors ℤ)
  have hM : M ≤ nonZeroDivisors B := by
    rintro _ ⟨m, hm, rfl⟩
    apply mem_nonZeroDivisors_of_ne_zero
    intro h
    exact nonZeroDivisors.ne_zero hm (hinj (h.trans (map_zero _).symm))
  have : IsLocalization M (ℚ ⊗[ℤ] B) := IsLocalization.tensorRight _ _
  have : IsDomain (ℚ ⊗[ℤ] B) := IsLocalization.isDomain_of_le_nonZeroDivisors _ hM

  have hBL : Function.Injective (algebraMap B (ℚ ⊗[ℤ] B)) := IsLocalization.injective _ hM
  have : FaithfulSMul B (ℚ ⊗[ℤ] B) := (faithfulSMul_iff_algebraMap_injective _ _).2 hBL
  have : FaithfulSMul ℤ B := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have : FaithfulSMul ℤ ℚ :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap ℤ ℚ).injective_int
  have : FaithfulSMul ℚ (ℚ ⊗[ℤ] B) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap ℚ (ℚ ⊗[ℤ] B)).injective
  have := IsScalarTower.of_algebraMap_eq' (RingHom.ext_int (algebraMap ℤ (ℚ ⊗[ℤ] B))
    ((algebraMap B (ℚ ⊗[ℤ] B)).comp (algebraMap ℤ B)))
  have := IsScalarTower.of_algebraMap_eq' (RingHom.ext_int (algebraMap ℤ (ℚ ⊗[ℤ] B))
    ((algebraMap ℚ (ℚ ⊗[ℤ] B)).comp (algebraMap ℤ ℚ)))
  have : Algebra.IsAlgebraic B (ℚ ⊗[ℤ] B) := IsLocalization.isAlgebraic _ M
  have : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
  have h1 := trdeg_add_eq ℤ B (A := ℚ ⊗[ℤ] B)
  have h2 := trdeg_add_eq ℤ ℚ (A := ℚ ⊗[ℤ] B)
  rw [trdeg_eq_zero (R := B) (A := ℚ ⊗[ℤ] B), add_zero] at h1
  rw [trdeg_eq_zero (R := ℤ) (A := ℚ), zero_add] at h2
  have htL : trdeg ℚ (ℚ ⊗[ℤ] B) = t := by rw [h2, ← h1, ht]

  rw [← ReciprocityTheory.CA.ringKrullDim_eq_of_trdeg_eq_field (K := ℚ) (A := ℚ ⊗[ℤ] B) t htL]
  exact ringKrullDim_eq_of_ringEquiv
    (IsLocalization.algEquiv M (Localization M) (ℚ ⊗[ℤ] B)).toRingEquiv

theorem DimX.proof : DimX.Statement := by
  intro K _ ι _ P n hP
  obtain ⟨-, ⟨hPp, -, -⟩, hhor, hdim⟩ := hP
  have := hPp

  have hinj : Function.Injective (algebraMap ℤ (MRing ι ⧸ P)) := by
    rw [injective_iff_map_eq_zero]
    intro m hm
    have hm' : m ∈ P.comap (C : ℤ →+* MRing ι) := by
      rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem, ← hm]
      exact congrArg (fun f : ℤ →+* MRing ι ⧸ P => f m)
        (RingHom.ext_int ((Ideal.Quotient.mk P).comp C) (algebraMap ℤ (MRing ι ⧸ P)))
    rw [hhor, Ideal.mem_bot] at hm'
    exact hm'

  have : Algebra.FiniteType ℤ (MRing ι ⧸ P) :=
    .of_surjective (Ideal.Quotient.mkₐ ℤ P) (Ideal.Quotient.mkₐ_surjective ℤ P)
  have hfin : trdeg ℤ (MRing ι ⧸ P) < Cardinal.aleph0 := trdeg_lt_aleph0_of_finiteType
  obtain ⟨t, ht⟩ := Cardinal.lt_aleph0.mp hfin
  have hB := IntDomainDim.proof (MRing ι ⧸ P) hinj
  rw [ht, Cardinal.toENat_nat, hdim] at hB
  have htn : t = n + Fintype.card K := by
    have h1 : ((n + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) = ((t + 1 : ℕ) : WithBot ℕ∞) := by
      exact_mod_cast hB
    have h2 : n + 1 + Fintype.card K = t + 1 := by exact_mod_cast h1
    omega
  rw [← htn]
  exact DimX.ringKrullDim_localization_int (MRing ι ⧸ P) hinj t ht

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsHodgeFibreSpecialise
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

def HodgeFibreSpecialise.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentDataHodge II Ψ K ι Ω E) (P : PlueckerData D) (τ : Ψ)
    (b : Fin D.N → E τ) (z : (Σ k, ι k) → ℂ) (wF : Fin (P.M τ (jIdx D)) → ℂ)
    (wW : Fin (P.M τ (lastIdx D)) → ℂ),
    IsHodgeFrame D τ b → z ∈ mcPts (mCoordIdeal D.y) → IsHodgeFibrePt P τ z wF wW →
    (∃ (lam : Ω) (mu : ℂ), lam ≠ 0 ∧ mu ≠ 0 ∧ ∀ m, ∃ (s : Ω) (v : ℂ),
      P.gen τ (jIdx D) m (b ∘ Fin.castLE (jIdx D).isLt) = lam * s ∧ IsValueAt D.y s z v ∧
        wF m = mu * v) ∧
    (∃ (lam : Ω) (mu : ℂ), lam ≠ 0 ∧ mu ≠ 0 ∧ ∀ m, ∃ (s : Ω) (v : ℂ),
      P.gen τ (lastIdx D) m (b ∘ Fin.castLE (lastIdx D).isLt) = lam * s ∧ IsValueAt D.y s z v ∧
        wW m = mu * v)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsHodgeFlagRatioTrdeg
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def HodgeFlagRatioTrdeg.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (Pl : PlueckerData D) (H : HodgeData D)
    (B : AdaptedBasis H) (c : ∀ k, Pl.ιY k), (∀ k, Pl.flagGenericPoint B ⟨k, c k⟩ ≠ 0) →
    Algebra.trdeg ℤ (Subfield.closure (coneRatios (Pl.flagGenericPoint B) c)) = ((D.n + D.flagDim0 : ℕ) : Cardinal)

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsMuModelTrivialSection
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree

open ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

open Classical in

def MuModelTrivialSection.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentDataHodge II Ψ K ι Ω E) (P : PlueckerData D)
    (H : HodgeData D.toComponentData), (∀ τ, H.F τ = D.F τ) →
    ∃ (bf bg : MuBlocks D → ℕ) (f g : MvPolynomial (Σ k : MuBlocks D, ιMu P k) ℚ),
      GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog f bf ∧
      GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog g bg ∧
      f ∉ (PXmu P).map (MvPolynomial.map (Int.castRingHom ℚ)) ∧
      g ∉ (PXmu P).map (MvPolynomial.map (Int.castRingHom ℚ)) ∧
      (∀ k, (bf k : ℤ) - bg k = muDeg D k - Sum.elim H.aMu (0 : Ψ ⊕ Ψ → ℤ) k) ∧
      GroundTheory.Heights₂.Heights.NumbersDVR.ratDiv ((PXmu P).map (MvPolynomial.map (Int.castRingHom ℚ))) f g = 0

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree
end

