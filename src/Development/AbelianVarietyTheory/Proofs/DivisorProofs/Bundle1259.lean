import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1218
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0343
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0033
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0042
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0079
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1219
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1220
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1002
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1092
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1023
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1075
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1239
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1069
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1140
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1132
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1143
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1158
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1097
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1117
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1246
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1025
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1176
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0232

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOrEqOfUnderMaximalRealSubfieldEqCMFieldStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_or_eq_of_under_maximalRealSubfield_eq_CMField : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w u u' : Pl E), u ≠ w → u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) → u'.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) → u' = w ∨ u' = u := by
  first | exact @GlobalTheory.BCT.FiberTwo.eq_or_eq_of_under_eq | exact GlobalTheory.BCT.FiberTwo.eq_or_eq_of_under_eq | (intros; apply GlobalTheory.BCT.FiberTwo.eq_or_eq_of_under_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfOrthogonalTranslates
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeisTotal

theorem star_char {R : Type} [CommRing R] (ψ : AddChar R ℂ) (h : ∀ x, ‖ψ x‖ = 1) (x : R) :
    star (ψ (-x)) = ψ x := by
  have h1 : ψ (-x) * ψ x = 1 := by rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  have h2 : star (ψ (-x)) * ψ (-x) = 1 := by
    rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, h]; simp
  calc star (ψ (-x)) = star (ψ (-x)) * (ψ (-x) * ψ x) := by rw [h1, mul_one]
    _ = ψ x := by rw [← mul_assoc, h2, one_mul]

theorem eq_zero_abstract {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G)
    [DiscreteTopology Γ] (K : Set G) (hK : IsCompact K) (hcov : ∀ x, ∃ γ ∈ Γ, γ + x ∈ K)
    {R : Type} [CommRing R] [TopologicalSpace R] [ContinuousAdd R] (ψ : AddChar R ℂ) (hψc : Continuous ψ)
    (hψn : ∀ x, ‖ψ x‖ = 1) (H : G → G → R)
    (hl : ∀ x y z, H (x + y) z = H x z + H y z) (hr : ∀ x y z, H x (y + z) = H x y + H x z)
    (halt : ∀ x, H x x = 0) (hcont : Continuous fun q : G × G => H q.1 q.2)
    (hann : ∀ x, (∀ γ ∈ Γ, ψ (H x γ + H x γ) = 1) ↔ x ∈ Γ)
    (f₀ f : G → ℂ) (c₀ : Continuous f₀) (c : Continuous f)
    (q₀ : ∀ γ ∈ Γ, ∀ w, f₀ (γ + w) = ψ (-(H γ w)) * f₀ w) (q : ∀ γ ∈ Γ, ∀ w, f (γ + w) = ψ (-(H γ w)) * f w)
    (hne : f₀ ≠ 0) (μ : Measure G) (𝓕 : Set G) (hμ : μ.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain Γ 𝓕 μ)
    (horth : ∀ w, ∫ x in 𝓕, ψ (H x w) * f₀ (x + w) * star (f x) ∂μ = 0) : f = 0 := by
  have hskew : ∀ x y : G, H y x = -H x y := by
    intro x y
    have h := halt (x + y)
    rw [hl, hr, hr, halt x, halt y] at h
    linear_combination h
  have hz : ∀ x : G, H x 0 = 0 := by
    intro x
    have h := hr x 0 0
    rw [add_zero] at h
    linear_combination -h
  have hcy : ∀ y : G, Continuous fun x : G => H x y := fun y =>
    hcont.comp (continuous_id.prodMk continuous_const)
  have key : ∀ a : G, (fun x => ψ (H x a) * f₀ (x + a) * star (f x)) = 0 := by
    intro a
    refine GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero G Γ K hK hcov
      Γ (fun γ x => ψ (H x γ + H x γ)) ?_ ?_ ?_ ?_ ?_ ?_ μ 𝓕 hμ h𝓕 _ ?_ ?_ ?_
    · intro γ
      exact hψc.comp ((hcy _).add (hcy _))
    · intro γ x y
      rw [← AddChar.map_add_eq_mul, hl]
      congr 1; ring
    · intro γ γ' x
      rw [← AddChar.map_add_eq_mul, AddSubgroup.coe_add, hr]
      congr 1; ring
    · intro x
      rw [AddSubgroup.coe_zero, hz, add_zero, AddChar.map_zero_eq_one]
    · intro γ x
      exact hψn _
    · intro x
      rw [← hann x]
      exact ⟨fun h γ hγ => h ⟨γ, hγ⟩, fun h γ => h γ γ.2⟩
    · exact ((hψc.comp (hcy a)).mul (c₀.comp (continuous_id.add continuous_const))).mul c.star
    · intro γ hγ x
      rw [add_assoc, q₀ γ hγ, q γ hγ, star_mul', star_char ψ hψn]
      have e : ψ (H (γ + x) a) * ψ (-(H γ (x + a))) * ψ (H γ x) = ψ (H x a) := by
        rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, hl, hr]
        congr 1; ring
      linear_combination (f₀ (x + a) * star (f x)) * e
    · intro γ
      have h := horth ((γ : G) + a)
      have e : ∀ x : G, ψ (H x γ + H x γ) * (ψ (H x a) * f₀ (x + a) * star (f x))
          = ψ (H γ a) * (ψ (H x (γ + a)) * f₀ (x + (γ + a)) * star (f x)) := by
        intro x
        rw [add_left_comm x, q₀ γ γ.2]
        have e' : ψ (H x γ + H x γ) * ψ (H x a) =
            ψ (H γ a) * ψ (H x (γ + a)) * ψ (-(H γ (x + a))) := by
          rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, hr, hr, hskew x γ]
          congr 1; ring
        linear_combination (f₀ (x + a) * star (f x)) * e'
      simp only [e]
      rw [integral_const_mul, h, mul_zero]
  obtain ⟨y, hy⟩ := Function.ne_iff.mp hne
  funext x
  have h := congrFun (key (y - x)) x
  simp only [add_sub_cancel, Pi.zero_apply, mul_eq_zero, star_eq_zero] at h
  rcases h with (h | h) | h
  · have := hψn (H x (y - x))
    rw [h] at this
    simp at this
  · exact absurd h hy
  · exact h

theorem quasi_of_mem {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {g : WO S T → ℂ} (hg : IsThetaFunO ψ S T g)
    (γ : WO S T) (hγ : γ ∈ ratL T S) (w : WO S T) : g (γ + w) = ψ (-(symplOH S T γ w)) * g w := by
  obtain ⟨γ', rfl⟩ := hγ
  exact hg.quasi γ' w

theorem eq_zero_of_orthogonal_translates (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1))
    (S T : HSp D) (f₀ f : WO S T → ℂ) (h₀ : IsThetaFunO ψ S T f₀) (hne : f₀ ≠ 0) (hf : IsThetaFunO ψ S T f)
    (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratL T S) 𝓕 μ)
    (horth : ∀ w, ∫ x in 𝓕, heisO ψ S T w f₀ x * star (f x) ∂μ = 0) : f = 0 := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨hl, hr, halt, hdbl, hcont, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D S T
  obtain ⟨hψc, hψn, -, -⟩ := hψ.1
  have hann : ∀ x : WO S T, (∀ γ ∈ ratL T S, ψ (symplOH S T x γ + symplOH S T x γ) = 1) ↔ x ∈ ratL T S := by
    intro x
    simp only [hdbl]
    exact GlobalTheory.T.rationalSymplecticPoints_self_annihilator D ψ hψ S T x
  exact eq_zero_abstract (G := WO S T) (ratL T S) K hK hcov ψ hψc hψn (symplOH S T) hl hr halt hcont hann f₀ f
    h₀.cont hf.cont (quasi_of_mem h₀) (quasi_of_mem hf) hne μ 𝓕 hμ h𝓕 horth

end GlobalTheory.HeisTotal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EssFiniteTypeOfLocalRingOfVarietyPointStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.essFiniteType_of_localRingOfVarietyPoint : ∀ {K : Type} [Field K] [Algebra ℂ K] (R : Subring K),
  IsLocModel (algebraMap ℂ K) R → Algebra.EssFiniteType ℂ K := by
  first | exact @GlobalTheory.essFiniteType_of_isLocModel | exact GlobalTheory.essFiniteType_of_isLocModel | (intros; apply GlobalTheory.essFiniteType_of_isLocModel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvenOrdLConjGramDetOfUnitGramAdicCompletionStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.even_ordL_conjGramDet_of_unit_gram_adicCompletion : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (σ : w.adicCompletion E →+* w.adicCompletion E),
    (∀ x, Valued.v (σ x) = Valued.v x) → ∀ (n : ℕ) (V : Submodule (w.adicCompletion E) (Fin n → w.adicCompletion E))
    {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (b : Module.Basis ι (w.adicCompletion E) V)
    (c : Module.Basis κ (w.adicCompletion E) V),
    Valued.v (Matrix.of fun i j => ∑ k, σ ((c i : Fin n → w.adicCompletion E) k) * (c j : Fin n → w.adicCompletion E) k).det = 1 →
    (-1 : ℂ) ^ ordL (Matrix.of fun i j => ∑ k, σ ((b i : Fin n → w.adicCompletion E) k) * (b j : Fin n → w.adicCompletion E) k).det = 1 := by
  first | exact @GlobalTheory.GramParity.gram_det_parity | exact GlobalTheory.GramParity.gram_det_parity | (intros; apply GlobalTheory.GramParity.gram_det_parity <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyBezoutSeparableDerivativeAdicIntegersStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_bezout_separable_derivative_adicIntegers : ∀ (E : Type) [Field E] [NumberField E] (P : E[X]), P.Separable →
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, ∃ u v : (w.adicCompletion E)[X],
      (∀ i, u.coeff i ∈ w.adicCompletionIntegers E) ∧ (∀ i, v.coeff i ∈ w.adicCompletionIntegers E) ∧
      u * P.map (algebraMap E (w.adicCompletion E)) + v * derivative (P.map (algebraMap E (w.adicCompletion E))) = 1 := by
  first | exact @GlobalTheory.BCT.SepBezout.bezout_eventually | exact GlobalTheory.BCT.SepBezout.bezout_eventually | (intros; apply GlobalTheory.BCT.SepBezout.bezout_eventually <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyDefiniteUnitaryLocalPointMemMaxCompactStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_definiteUnitaryLocalPoint_mem_maxCompact : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ γ : UE E n, γ.1.val.charpoly.Separable → ∀ᶠ w in cofinite, locPt w γ ∈ KL n w := by
  first | exact @GlobalTheory.BCT.GoodInt.locPt_mem_KL | exact GlobalTheory.BCT.GoodInt.locPt_mem_KL | (intros; apply GlobalTheory.BCT.GoodInt.locPt_mem_KL <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyExistsIntegralCharpolySplitPlaceStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_exists_integral_charpoly_split_place : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ P ∈ Ell E n, ∀ᶠ w in cofinite, IsSplitAt w → ∃ γ : UL n w, γ ∈ KL n w ∧ γ.1.val.charpoly = atPl w P := by
  first | exact @GlobalTheory.BCT.exists_int_charpoly_atPl_split | exact GlobalTheory.BCT.exists_int_charpoly_atPl_split | (intros; apply GlobalTheory.BCT.exists_int_charpoly_atPl_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyFiniteAdelicUnitaryComponentMemIntegraStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_finiteAdelicUnitaryComponent_mem_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ x : finU E n, ∀ᶠ w in cofinite, toSub (UL n w) (cLoc w (x : UA E n)) ∈ KL n w := by
  first | exact @GlobalTheory.BCT.LocAE.eventually_mem_KL | exact GlobalTheory.BCT.LocAE.eventually_mem_KL | (intros; apply GlobalTheory.BCT.LocAE.eventually_mem_KL <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralConjugatorsDifferByCentralizerStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_integral_conjugators_differ_by_centralizer : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (γ : G.Cˣ), (minpoly G.F (γ : G.C)).natDegree = G.n →
    (minpoly G.F (γ : G.C)).Separable → ∀ (L : Type) [Field L] [NumberField L] (ι : L →ₐ[ℚ] G.C),
    Function.Injective ι → (∀ z : G.C, z * γ = γ * z ↔ ∃ w, ι w = z) → ∀ (κ : Type) (b : Module.Basis κ ℚ G.C),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, ∀ X X' : (v.adicCompletion ℚ ⊗[ℚ] G.C)ˣ,
      IsIntB v b (↑X * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (γ : G.C)) * ↑X⁻¹) →
      IsIntB v b (↑X' * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (γ : G.C)) * ↑X'⁻¹) →
      ∃ m : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ,
        IsIntB v b (↑X * Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι ↑m * ↑X'⁻¹) ∧
        IsIntB v b (↑X' * Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι ↑m⁻¹ * ↑X⁻¹) := by
  first | (exact @GlobalTheory.LatStep.lattice_step) | (exact GlobalTheory.LatStep.lattice_step) | (intros; apply GlobalTheory.LatStep.lattice_step  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralLiftCoprimeDerivativeStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_integral_lift_coprime_derivative : ∀ (E : Type) [Field E] [NumberField E] (P : E[X]), P.Separable →
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, ∃ P₀ : (w.adicCompletionIntegers E)[X],
      P₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) = P.map (algebraMap E (w.adicCompletion E)) ∧
      IsCoprime P₀ (derivative P₀) := by
  first | exact @GlobalTheory.IntCop.eventually_integral_coprime | exact GlobalTheory.IntCop.eventually_integral_coprime | (intros; apply GlobalTheory.IntCop.eventually_integral_coprime <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyKottwitzLatticeSeparableMinpoly
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.FinClsLoc.SepLat

theorem kottwitz_lattice_sep : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (Y : G.Cˣ), (minpoly G.F (Y : G.C)).Separable →
    (minpoly G.F (Y : G.C)).natDegree = G.n →
    ∀ᶠ w : AwayP p in Filter.cofinite, ∀ k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ,
      IntC G w ((k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) * inC G (w.1.adicCompletion ℚ) (Y : G.C) * ((k⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))) →
      IntC G w ((k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) * inC G (w.1.adicCompletion ℚ) ((Y⁻¹ : G.Cˣ) : G.C) * ((k⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))) →
      ∃ z m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ, Commute (z : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) (inC G (w.1.adicCompletion ℚ) (Y : G.C)) ∧
        IntC G w (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) ∧ IntC G w ((m⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) ∧ k⁻¹ = z * m := by
  intro p _ G Y hsep hdeg
  filter_upwards [GlobalTheory.T.eventually_completedTensor_matrix_split_semilocal p G (Y : G.C) hdeg hsep, GlobalTheory.OrbFinAf.isIntV_mul_eventually G,
    GlobalTheory.OrbFinAf.KottLat.eventually_isIntV_map G ((1 : AfP p) ⊗ₜ[ℚ] (Y : G.C))] with w hA _ hY1
  intro k h1 _
  obtain ⟨K, _, R, Φ, hfin, hInt, Q, hQs, hQm⟩ := hA
  let γ₀ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ := Units.map (inC G (w.1.adicCompletion ℚ)).toMonoidHom Y
  have hγv : (γ₀ : w.1.adicCompletion ℚ ⊗[ℚ] G.C) = (1 : w.1.adicCompletion ℚ) ⊗ₜ[ℚ] (Y : G.C) := rfl
  have hγi : (γ₀ : w.1.adicCompletion ℚ ⊗[ℚ] G.C) = inC G (w.1.adicCompletion ℚ) (Y : G.C) := rfl
  have hγ0 : GlobalTheory.OrbFinAf.IsIntV G w (γ₀ : w.1.adicCompletion ℚ ⊗[ℚ] G.C) := by
    rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply] at hY1
    rw [hγv]; exact hY1
  have hconj : GlobalTheory.OrbFinAf.IsIntV G w (((k⁻¹)⁻¹ * γ₀ * k⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) :
      w.1.adicCompletion ℚ ⊗[ℚ] G.C) := by
    rw [inv_inv, Units.val_mul, Units.val_mul, hγi]
    exact h1
  obtain ⟨U, hU, hU1, hU2⟩ := GlobalTheory.OrbFinAf.KottLat.conj_integral R Φ hfin Q hQs γ₀ (by rw [hγv]; exact hQm)
    ((hInt _).1 hγ0) k⁻¹ ((hInt _).1 hconj)
  have hcomm : k⁻¹ * U⁻¹ * γ₀ = γ₀ * (k⁻¹ * U⁻¹) := by
    have e : U * (k * γ₀ * k⁻¹) = γ₀ * U := by simpa using hU
    calc k⁻¹ * U⁻¹ * γ₀ = k⁻¹ * U⁻¹ * (γ₀ * U) * U⁻¹ := by group
      _ = k⁻¹ * U⁻¹ * (U * (k * γ₀ * k⁻¹)) * U⁻¹ := by rw [e]
      _ = γ₀ * (k⁻¹ * U⁻¹) := by group
  refine ⟨k⁻¹ * U⁻¹, U, ?_, (hInt _).2 hU1, (hInt _).2 hU2, by group⟩
  show _ * _ = _ * _
  rw [← hγi, ← Units.val_mul, ← Units.val_mul, hcomm]

end GlobalTheory.FinClsLoc.SepLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyMemKGL
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EulerTw.Fact

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem mem_KGL_of {w : Pl E} (g : GL (Fin n) (w.adicCompletion E))
    (h1 : ∀ i j, g.1 i j ∈ w.adicCompletionIntegers E) (h2 : ∀ i j, g⁻¹.1 i j ∈ w.adicCompletionIntegers E) :
    g ∈ GlobalTheory.LFun.KGL w n := by
  have hi : Function.Injective fun A : Matrix (Fin n) (Fin n) (Ov E w) => A.map (Ov E w).subtype :=
    Matrix.map_injective Subtype.val_injective
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, hi ?_, hi ?_⟩, Units.ext rfl⟩
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.mul_inv
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.inv_mul

theorem eventually_mem_KGL (x : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) :
    ∀ᶠ w : Pl E in cofinite, GeneralLinearGroup.map (pLoc E w) x ∈ GlobalTheory.LFun.KGL w n := by
  have h : ∀ g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E), ∀ᶠ w : Pl E in cofinite,
      ∀ i j, pLoc E w (g.val i j) ∈ w.adicCompletionIntegers E := fun g => by
    simp only [Filter.eventually_all]
    exact fun i j => (g.val i j).2
  filter_upwards [h x, h x⁻¹] with w a b
  exact mem_KGL_of _ a (by rw [← map_inv]; exact b)

theorem map_prjG (T : Finset (Pl E)) (x : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) {w : Pl E} (hw : w ∈ T) :
    GeneralLinearGroup.map (pLoc E w) (prjG E n T x) = GeneralLinearGroup.map (pLoc E w) x := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  have he : pLoc E w (idem E T) = 1 := by
    show (if w ∈ T then (1 : w.adicCompletion E) else 0) = 1
    rw [if_pos hw]
  show pLoc E w ((idem E T • x.val + (1 - idem E T) • (1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E))) i j) =
    pLoc E w (x.val i j)
  simp [Matrix.add_apply, Matrix.smul_apply, map_add, map_mul, map_sub, he]

theorem mem_orb_iff {u w : Pl E} : w ∈ (orb E u : Set (Pl E)) ↔
    w.under (𝓞 (maximalRealSubfield E)) = u.under (𝓞 (maximalRealSubfield E)) := by
  have hm := GlobalTheory.QuadPlaces.main (maximalRealSubfield E) E (Algebra.IsQuadraticExtension.finrank_eq_two _ _)
    (IsCMField.complexConj E) (IsCMField.complexConj_ne_one E) u
  simp only [orb, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (rfl | rfl)
    · rfl
    · exact hm.2.1
  · intro h
    exact hm.1 w h

theorem finprod_orb (S : Set (Pl E)) (φ : ∀ w : Pl E, GLw n w → ℂ) (x : GL (Fin n) (FiniteAdeleRing (𝓞 E) E))
    (u : Pl E) :
    FU E n S φ u (pfU E n u x) = ∏ w ∈ orb E u, (if w ∈ S then φ w (GeneralLinearGroup.map (pLoc E w) x) else
      (GlobalTheory.LFun.KGL w n : Set (GLw n w)).indicator 1 (GeneralLinearGroup.map (pLoc E w) x)) := by
  set f : Pl E → ℂ := fun w => if w ∈ S then φ w (GeneralLinearGroup.map (pLoc E w) x) else
      (GlobalTheory.LFun.KGL w n : Set (GLw n w)).indicator 1 (GeneralLinearGroup.map (pLoc E w) x) with hf
  have hx : ∀ w ∈ (orb E u : Set (Pl E)), GeneralLinearGroup.map (pLoc E w) (pfU E n u x).1 =
      GeneralLinearGroup.map (pLoc E w) x := fun w hw => map_prjG (orb E u) x hw
  have h1 : (∏ᶠ w ∈ S ∩ ↑(orb E u), φ w (GeneralLinearGroup.map (pLoc E w) (pfU E n u x).1)) =
      ∏ᶠ w ∈ ↑(orb E u) ∩ S, f w := by
    rw [Set.inter_comm]
    refine finprod_mem_congr rfl fun w hw => ?_
    rw [hf]; dsimp only; rw [if_pos hw.2, hx w hw.1]
  have h2 : (∏ᶠ w ∈ Sᶜ ∩ ↑(orb E u), (GlobalTheory.LFun.KGL w n : Set (GLw n w)).indicator 1
      (GeneralLinearGroup.map (pLoc E w) (pfU E n u x).1)) = ∏ᶠ w ∈ ↑(orb E u) \ S, f w := by
    rw [Set.diff_eq, Set.inter_comm]
    refine finprod_mem_congr rfl fun w hw => ?_
    rw [hf]; dsimp only; rw [if_neg hw.2, hx w hw.1]
  rw [FU, h1, h2, finprod_mem_inter_mul_diff S (orb E u).finite_toSet, finprod_mem_coe_finset]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)), IsSection S → ∀ K' : ∀ w : Pl E, Subgroup (GLw n w), IsLevelFam (thL n) (fun w : Pl E => GlobalTheory.LFun.KGL w n) K' → ∀ φ : ∀ w : Pl E, GLw n w → ℂ, IsTest (fun w : Pl E => GlobalTheory.LFun.KGL w n) K' φ → ∀ x : GL (Fin n) (FiniteAdeleRing (𝓞 E) E), (∏ᶠ w ∈ S, φ w (GeneralLinearGroup.map (pLoc E w) x)) * ∏ᶠ w ∈ Sᶜ, (GlobalTheory.LFun.KGL w n : Set (GLw n w)).indicator 1 (GeneralLinearGroup.map (pLoc E w) x) = ∏ᶠ u : S, GlobalTheory.EulerTw.FU E n S φ u.1 (GlobalTheory.EulerTw.pfU E n u.1 x) := by
  intro E _ _ _ n S hS K' _ φ hφ x
  set f : Pl E → ℂ := fun w => if w ∈ S then φ w (GeneralLinearGroup.map (pLoc E w) x) else
      (GlobalTheory.LFun.KGL w n : Set (GLw n w)).indicator 1 (GeneralLinearGroup.map (pLoc E w) x) with hf

  have hfin : (Function.mulSupport f).Finite := by
    refine (Filter.eventually_cofinite.1 (hφ.2.and (eventually_mem_KGL (E := E) x))).subset fun w hw => ?_
    rintro ⟨h1, h2⟩
    apply hw
    have hi : (GlobalTheory.LFun.KGL w n : Set (GLw n w)).indicator (1 : GLw n w → ℂ) (GeneralLinearGroup.map (pLoc E w) x) = 1 :=
      Set.indicator_of_mem h2 _
    show f w = 1
    rw [hf]; dsimp only
    split_ifs
    · rw [h1]; exact hi
    · exact hi

  have hL : (∏ᶠ w ∈ S, φ w (GeneralLinearGroup.map (pLoc E w) x)) * ∏ᶠ w ∈ Sᶜ,
      (GlobalTheory.LFun.KGL w n : Set (GLw n w)).indicator 1 (GeneralLinearGroup.map (pLoc E w) x) = ∏ᶠ w, f w := by
    have e1 : (∏ᶠ w ∈ S, φ w (GeneralLinearGroup.map (pLoc E w) x)) = ∏ᶠ w ∈ S, f w :=
      finprod_mem_congr rfl fun w hw => by rw [hf]; dsimp only; rw [if_pos hw]
    have e2 : (∏ᶠ w ∈ Sᶜ, (GlobalTheory.LFun.KGL w n : Set (GLw n w)).indicator 1 (GeneralLinearGroup.map (pLoc E w) x)) =
        ∏ᶠ w ∈ Sᶜ, f w :=
      finprod_mem_congr rfl fun w hw => by rw [hf]; dsimp only; rw [if_neg hw]
    rw [e1, e2, ← finprod_mem_union'' (disjoint_compl_right.mono Set.inter_subset_left Set.inter_subset_left) (hfin.subset Set.inter_subset_right)
      (hfin.subset Set.inter_subset_right), Set.union_compl_self, finprod_mem_univ]

  let r : Pl E → S := fun w => ⟨(hS w).exists.choose, (hS w).exists.choose_spec.1⟩
  have hr : ∀ w, (r w).1.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) :=
    fun w => (hS w).exists.choose_spec.2
  have hru : ∀ (u : S) w, w ∈ (orb E u.1 : Set (Pl E)) ↔ r w = u := fun u w => by
    rw [mem_orb_iff]
    constructor
    · intro h
      exact Subtype.ext ((hS w).unique ⟨(r w).2, hr w⟩ ⟨u.2, h.symm⟩)
    · rintro rfl
      exact (hr w).symm
  set s := hfin.toFinset with hs
  have hsupp : ∀ w, w ∉ s → f w = 1 := fun w hw => by
    rw [hs, Set.Finite.mem_toFinset] at hw
    exact Function.notMem_mulSupport.1 hw
  rw [hL, finprod_eq_prod_of_mulSupport_subset f (s := s) (by rw [hs, Set.Finite.coe_toFinset])]
  have hg : ∀ u : S, FU E n S φ u.1 (pfU E n u.1 x) = ∏ w ∈ s with r w = u, f w := fun u => by
    rw [finprod_orb]
    refine (Finset.prod_subset (fun w hw => ?_) fun w hw hw' => ?_).symm
    · rw [← Finset.mem_coe, hru]
      exact (Finset.mem_filter.1 hw).2
    · by_contra hne
      exact hw' (Finset.mem_filter.2 ⟨by_contra fun h => hne (hsupp w h), (hru u w).1 (Finset.mem_coe.2 hw)⟩)
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := s.image r) fun u hu => ?_]
  · rw [Finset.prod_congr rfl fun u _ => hg u]
    exact (Finset.prod_fiberwise_of_maps_to (fun w hw => Finset.mem_image_of_mem r hw) f).symm

  · rw [Function.mem_mulSupport, hg u] at hu
    obtain ⟨w, hw, -⟩ := Finset.exists_ne_one_of_prod_ne_one hu
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨w, (Finset.mem_filter.1 hw).1, (Finset.mem_filter.1 hw).2⟩)

end GlobalTheory.EulerTw.Fact
end
end

