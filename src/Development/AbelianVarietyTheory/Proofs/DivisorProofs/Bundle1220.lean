import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1082
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1186
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1094
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1066
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1068
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1071
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1060
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1139
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0017
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0309
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0047
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0155
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0092
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1193
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1176
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1179
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1178
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.MeasurePreservingMulRight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Smooth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShapeIntegratedOperatorRangesPolynomial

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyFiniteAdelicUnitaryComponentMemIntegra
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.LocAE

theorem mem_GLint_of_entries_inv {L : Type} [Field L] {k : ℕ} (O : Subring L) (g : GL (Fin k) L)
    (h1 : ∀ i j, g.1 i j ∈ O) (h2 : ∀ i j, g⁻¹.1 i j ∈ O) : g ∈ Formalism.UG.GLint (Fin k) O := by
  have hi : Function.Injective fun A : Matrix (Fin k) (Fin k) O => A.map O.subtype :=
    Matrix.map_injective Subtype.val_injective
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, hi ?_, hi ?_⟩, Units.ext rfl⟩
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.mul_inv
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.inv_mul

theorem eventually_mem_KL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ x : finU E n,
    ∀ᶠ w in cofinite, toSub (UL n w) (cLoc w (x : UA E n)) ∈ KL n w := by
  intro E _ _ _ _ n x
  have h : ∀ y : FiniteAdeleRing (𝓞 E) E, ∀ᶠ w in cofinite, pLoc E w y ∈ Formalism.UG.Ov E w := fun y => y.2
  have h1 : ∀ᶠ w in cofinite, ∀ i j, pLoc E w (pFin E (((x : UA E n) : GA E n).val i j)) ∈ Formalism.UG.Ov E w := by
    simp only [Filter.eventually_all]; exact fun i j => h _
  have h2 : ∀ᶠ w in cofinite, ∀ i j, pLoc E w (pFin E ((((x : UA E n) : GA E n))⁻¹.val i j)) ∈ Formalism.UG.Ov E w := by
    simp only [Filter.eventually_all]; exact fun i j => h _
  filter_upwards [h1, h2] with w a b
  have hK : cLoc w (x : UA E n) ∈ GlobalTheory.LFun.KGL w n := by
    refine mem_GLint_of_entries_inv _ _ (fun i j => a i j) (fun i j => ?_)
    rw [← map_inv]
    exact b i j
  unfold toSub
  split_ifs with hU
  · exact Subgroup.mem_subgroupOf.2 hK
  · exact one_mem _

end GlobalTheory.BCT.LocAE
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralConjugatorsDifferByCentralizer
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LatStep

theorem isIntB_add' (v : HeightOneSpectrum ℤ) {M : Type} [AddCommGroup M] [Module ℚ M] {κ : Type}
    (b : Module.Basis κ ℚ M) {x y : v.adicCompletion ℚ ⊗[ℚ] M} (hx : IsIntB v b x) (hy : IsIntB v b y) :
    IsIntB v b (x + y) := fun i => by
  rw [map_add, Finsupp.add_apply]; exact add_mem (hx i) (hy i)

theorem isIntB_neg' (v : HeightOneSpectrum ℤ) {M : Type} [AddCommGroup M] [Module ℚ M] {κ : Type}
    (b : Module.Basis κ ℚ M) {x : v.adicCompletion ℚ ⊗[ℚ] M} (hx : IsIntB v b x) :
    IsIntB v b (-x) := fun i => by
  rw [map_neg, Finsupp.neg_apply]; exact neg_mem (hx i)

theorem lattice_step : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (γ : G.Cˣ), (minpoly G.F (γ : G.C)).natDegree = G.n →
    (minpoly G.F (γ : G.C)).Separable → ∀ (L : Type) [Field L] [NumberField L] (ι : L →ₐ[ℚ] G.C),
    Function.Injective ι → (∀ z : G.C, z * γ = γ * z ↔ ∃ w, ι w = z) → ∀ (κ : Type) (b : Module.Basis κ ℚ G.C),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, ∀ X X' : (v.adicCompletion ℚ ⊗[ℚ] G.C)ˣ,
      IsIntB v b (↑X * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (γ : G.C)) * ↑X⁻¹) →
      IsIntB v b (↑X' * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (γ : G.C)) * ↑X'⁻¹) →
      ∃ m : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ,
        IsIntB v b (↑X * Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι ↑m * ↑X'⁻¹) ∧
        IsIntB v b (↑X' * Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι ↑m⁻¹ * ↑X⁻¹) := by
  intro p _ G γ hdeg _hsep L _ _ ι hι hcent κ b
  let ℓ := Module.finBasis ℚ L
  obtain ⟨r, e, he⟩ := GlobalTheory.T.exists_basis_over_subfield_embedding L G.C ι
  have hE := fun i i' => GlobalTheory.T.exists_sum_two_sided_mul_eq_matrixUnit_unitaryDatum p G γ hdeg L ι hι hcent r e he i i'
  choose N l c hlc using hE
  have hl := fun (i i' : Fin r) (k : Fin (N i i')) => GlobalTheory.T.eventually_one_tmul_adic_integral_coords L _ ℓ (l i i' k)
  have hc := fun (i i' : Fin r) (k : Fin (N i i')) => GlobalTheory.T.eventually_one_tmul_adic_integral_coords G.C κ b (c i i' k)
  choose Sl hSl using hl
  choose Sc hSc using hc
  obtain ⟨S1, hS1⟩ := GlobalTheory.T.adicIntegralTensorBasis_ring_eventually G.C κ b
  obtain ⟨S2, hS2⟩ := GlobalTheory.T.adicIntegralTensorBasis_ring_eventually L _ ℓ
  obtain ⟨S3, hS3⟩ := GlobalTheory.T.almost_all_places_basis_integral L G.C ι r e he _ ℓ κ b
  obtain ⟨S4, hS4⟩ := GlobalTheory.T.eventually_integral_conj_of_integral_conj_generator p G γ hdeg L ι hι hcent κ b _ ℓ
  obtain ⟨S5, hS5⟩ := GlobalTheory.T.fractional_ideal_integral_lattice L _ ℓ
  let SE : Finset (HeightOneSpectrum ℤ) := Finset.univ.biUnion (fun ii : Fin r × Fin r =>
    Finset.univ.biUnion (fun k : Fin (N ii.1 ii.2) => Sl ii.1 ii.2 k ∪ Sc ii.1 ii.2 k))
  refine ⟨S1 ∪ S2 ∪ S3 ∪ S4 ∪ S5 ∪ SE, ?_⟩
  intro v hv X X' hX hX'
  simp only [Finset.mem_union, not_or] at hv
  obtain ⟨⟨⟨⟨⟨hv1, hv2⟩, hv3⟩, hv4⟩, hv5⟩, hvE⟩ := hv
  have hvE' : ∀ i i' k, v ∉ Sl i i' k ∧ v ∉ Sc i i' k := fun i i' k => by
    have : v ∉ Sl i i' k ∪ Sc i i' k := fun h => hvE (Finset.mem_biUnion.2
      ⟨(i, i'), Finset.mem_univ _, Finset.mem_biUnion.2 ⟨k, Finset.mem_univ _, h⟩⟩)
    simpa [Finset.mem_union, not_or] using this
  let jv := Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι
  have key := GlobalTheory.T.order_lattice_basis_integrality (jv : v.adicCompletion ℚ ⊗[ℚ] L →+* v.adicCompletion ℚ ⊗[ℚ] G.C)
    {y | IsIntB v b y} {x | IsIntB v ℓ x} r (fun i => (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] e i)
    (isIntB_zero v b) (hS1 v hv1).1 (fun x hx y hy => isIntB_add' v b hx hy) (fun x hx => isIntB_neg' v b hx)
    (fun x hx y hy => (hS1 v hv1).2 x y hx hy)
    (isIntB_zero v ℓ) (hS2 v hv2).1 (fun x hx y hy => isIntB_add' v ℓ hx hy) (fun x hx => isIntB_neg' v ℓ hx)
    (fun x hx y hy => (hS2 v hv2).2 x y hx hy)
    (fun a => GlobalTheory.T.existsUnique_left_basis_coords_adicCompletion L G.C ι r e he v a) (hS3 v hv3)
    (fun i i' => ⟨N i i', fun k => (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] l i i' k,
      fun k => (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] c i i' k, fun k => hSl i i' k v (hvE' i i' k).1,
      fun k => hSc i i' k v (hvE' i i' k).2,
      fun β => GlobalTheory.T.basis_change_adic_tensor_identity L G.C ι r e (N i i') (l i i') (c i i') i i' (hlc i i') v β⟩)
    (fun a => by
      obtain ⟨D, hD, h⟩ := GlobalTheory.T.exists_int_smul_isAdicIntegralInTensorBasis G.C κ b v a
      exact ⟨D, hD, by simpa [zsmul_eq_mul] using h⟩)
    (fun I h0 hadd hmul hD => hS5 v hv5 I h0 hadd hmul hD)
  obtain ⟨m, hm1, hm2⟩ := key X (fun ρ hρ => hS4 v hv4 X hX ρ hρ)
  obtain ⟨m', hm1', hm2'⟩ := key X' (fun ρ hρ => hS4 v hv4 X' hX' ρ hρ)
  refine ⟨m * m'⁻¹, ?_, ?_⟩
  · have := (hS1 v hv1).2 _ _ hm1 hm2'
    convert this using 1
    simp only [RingHom.coe_coe, Units.val_mul, map_mul, mul_assoc, jv]
  · have := (hS1 v hv1).2 _ _ hm1' hm2
    convert this using 1
    simp only [RingHom.coe_coe, _root_.mul_inv_rev, inv_inv, Units.val_mul, map_mul, mul_assoc, jv]

end GlobalTheory.LatStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralLiftCoprimeDerivative
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.IntCop

theorem lift_of_val_le {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (Q : E[X]) (h : ∀ n, w.valuation E (Q.coeff n) ≤ 1) :
    ∃ Q₀ : (w.adicCompletionIntegers E)[X],
      Q₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) =
        Q.map (algebraMap E (w.adicCompletion E)) := by
  have : Q.map (algebraMap E (w.adicCompletion E)) ∈
      Polynomial.lifts (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [Polynomial.coeff_map]
    refine ⟨⟨algebraMap E (w.adicCompletion E) (Q.coeff n),
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ?_⟩, rfl⟩
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w (Q.coeff n)).trans_le (h n)
  obtain ⟨Q₀, hQ₀⟩ := (Polynomial.mem_lifts _).1 this
  exact ⟨Q₀, hQ₀⟩

theorem finite_bad {E : Type} [Field E] [NumberField E] (Q : E[X]) :
    {w : HeightOneSpectrum (𝓞 E) | ¬ ∀ n, w.valuation E (Q.coeff n) ≤ 1}.Finite := by
  refine ((Finset.range (Q.natDegree + 1)).finite_toSet.biUnion
    fun n _ => HeightOneSpectrum.Support.finite (𝓞 E) (Q.coeff n)).subset ?_
  intro w hw
  simp only [Set.mem_setOf_eq, not_forall, not_le] at hw
  obtain ⟨n, hn⟩ := hw
  have hn' : n < Q.natDegree + 1 := by
    by_contra hc
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), map_zero] at hn
    exact (not_lt.2 zero_le') hn
  simp only [Set.mem_iUnion]
  exact ⟨n, by simpa using hn', hn⟩

end GlobalTheory.IntCop

namespace GlobalTheory.IntCop

theorem eventually_integral_coprime : ∀ (E : Type) [Field E] [NumberField E] (P : E[X]), P.Separable →
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, ∃ P₀ : (w.adicCompletionIntegers E)[X],
      P₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) = P.map (algebraMap E (w.adicCompletion E)) ∧
      IsCoprime P₀ (derivative P₀) := by
  intro E _ _ P hP
  obtain ⟨a, b, hab⟩ := hP
  have hfin := ((finite_bad P).union (finite_bad a)).union (finite_bad b)
  refine Filter.eventually_cofinite.2 (hfin.subset ?_)
  intro w hw
  by_contra hc
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc
  obtain ⟨⟨hPw, haw⟩, hbw⟩ := hc
  apply hw
  obtain ⟨P₀, hP₀⟩ := lift_of_val_le w P hPw
  obtain ⟨a₀, ha₀⟩ := lift_of_val_le w a haw
  obtain ⟨b₀, hb₀⟩ := lift_of_val_le w b hbw
  refine ⟨P₀, hP₀, a₀, b₀, ?_⟩
  have hinj : Function.Injective
      (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) := Subtype.val_injective
  apply Polynomial.map_injective _ hinj
  rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, ← Polynomial.derivative_map,
    ha₀, hb₀, hP₀, Polynomial.derivative_map, ← Polynomial.map_mul, ← Polynomial.map_mul,
    ← Polynomial.map_add, hab, Polynomial.map_one, Polynomial.map_one]

end GlobalTheory.IntCop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineBoundaryFunctionsOfIsProjOver
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

open ProjSpace

theorem IsAmpleLB.exists_affine_boundary_functions {Y : Scheme.{0}} {L : LB Y} (h : IsAmpleLB L) (U : Y.Opens)
    (x : Y) (hx : x ∈ U) : ∃ (V : Y.Opens) (n : ℕ) (u : Fin n → Γ(Y, V)), x ∈ V ∧ V ≤ U ∧ IsAffineOpen V ∧
      ∀ z : Y, ∃ (Q : Y.Opens) (η : Γ(Y, Q)) (l : Fin n), z ∈ Q ∧ Y.basicOpen η = Q ⊓ V ∧
        resG Y (inf_le_right : Q ⊓ V ≤ V) (u l) * resG Y (inf_le_left : Q ⊓ V ≤ Q) η = 1 := by
  obtain ⟨k, hk, hg⟩ := h.exists_isGenerated_pow
  obtain ⟨d, -, t, hxt, hle, ha⟩ := ((isAmpleLB_pow_iff h.isLB hk).2 h).exists_affine_le hx
  obtain ⟨n, s, hs⟩ := hg.pow d
  refine ⟨nonzeroLocus t, n, fun l => secRatio t (s l), hxt, hle, ha, fun z => ?_⟩
  obtain ⟨l, hl⟩ := Opens.mem_iSup.1 (hs.ge (Set.mem_univ z))
  refine ⟨nonzeroLocus (s l), secRatio (s l) t, l, hl, basicOpen_secRatio _ _, ?_⟩
  rw [secRatio_mul_secRatio t (s l) t inf_le_right inf_le_left, secRatio_self, map_one]

theorem exists_affine_boundary_functions_of_isProjOver :
    ∀ (Y : Scheme.{0}) (p : Y ⟶ Sp ℂ), IsProjOver p → ∀ (U : Y.Opens) (x : Y), x ∈ U →
      ∃ (V : Y.Opens) (n : ℕ) (u : Fin n → Γ(Y, V)), x ∈ V ∧ V ≤ U ∧ IsAffineOpen V ∧
        ∀ z : Y, ∃ (Q : Y.Opens) (η : Γ(Y, Q)) (l : Fin n), z ∈ Q ∧ Y.basicOpen η = Q ⊓ V ∧
          resG Y (inf_le_right : Q ⊓ V ≤ V) (u l) * resG Y (inf_le_left : Q ⊓ V ≤ Q) η = 1 := by
  rintro Y p ⟨N, i, hi, -⟩ U x hx
  exact ((isAmple_projective_O_one ℂ N).pull_of_isAffineHom i).exists_affine_boundary_functions U x hx

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineEtaleFiniteFreeNbhd
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

set_option autoImplicit false

namespace GlobalTheory.GenFinEtField

theorem finrank_app_eq_residueDegree {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (f : Y ⟶ X)
    (h : f (genericPoint Y) = genericPoint X) {U : X.Opens} (hU : IsAffineOpen U)
    (hU' : IsAffineOpen (f ⁻¹ᵁ U)) (hxU₀ : genericPoint X ∈ U) :
    letI := (f.app U).hom.toAlgebra
    Module.finrank Γ(X, U) Γ(Y, f ⁻¹ᵁ U) = f.residueDegree (genericPoint Y) := by
  have hxU : f (genericPoint Y) ∈ U := h ▸ hxU₀
  letI := (f.app U).hom.toAlgebra
  letI := (X.evaluation U _ hxU).hom.toAlgebra
  letI : Algebra Γ(Y, f ⁻¹ᵁ U) (Y.residueField (genericPoint Y)) :=
    (Y.evaluation (f ⁻¹ᵁ U) _ hxU).hom.toAlgebra
  letI := (f.residueFieldMap (genericPoint Y)).hom.toAlgebra
  letI : Algebra Γ(X, U) (Y.residueField (genericPoint Y)) :=
    (f.app U ≫ Y.evaluation (f ⁻¹ᵁ U) _ hxU).hom.toAlgebra
  haveI : IsScalarTower Γ(X, U) Γ(Y, f ⁻¹ᵁ U) (Y.residueField (genericPoint Y)) :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower Γ(X, U) (X.residueField (f (genericPoint Y)))
      (Y.residueField (genericPoint Y)) :=
    IsScalarTower.of_algebraMap_eq' congr($(Scheme.evaluation_naturality f _ hxU).hom).symm
  haveI := GlobalTheory.ProjFin.isFractionRing_evaluation X hU h hxU
  haveI := GlobalTheory.ProjFin.isFractionRing_evaluation Y hU' rfl hxU
  exact (IsFractionRing.finrank_eq Γ(X, U) (X.residueField (f (genericPoint Y)))
    Γ(Y, f ⁻¹ᵁ U) (Y.residueField (genericPoint Y))).symm

theorem exists_affine_finite_etale_free : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) [CharZero k], IsProjOver p → IsProjOver q → ∀ (π : Y ⟶ X), π ≫ p = q → π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∃ U : X.Opens, IsAffineOpen U ∧ genericPoint X ∈ U ∧ IsAffineOpen (π ⁻¹ᵁ U) ∧ (π.app U).hom.Etale ∧ (π.app U).hom.Finite ∧ (letI := (π.app U).hom.toAlgebra; Module.Free Γ(X, U) Γ(Y, π ⁻¹ᵁ U) ∧ Module.finrank Γ(X, U) Γ(Y, π ⁻¹ᵁ U) = π.residueDegree (genericPoint Y)) := by
  intro k _ X Y _ _ p q _ hX hY π hπ hg hδ
  have hpP : IsProper p := by
    obtain ⟨N, j, _, hj⟩ := hX
    have := isProper_str k N
    exact hj ▸ inferInstance
  have hqP : IsProper q := by
    obtain ⟨N, j, _, hj⟩ := hY
    have := isProper_str k N
    exact hj ▸ inferInstance
  have : IsSeparated (π ≫ p) := hπ ▸ (inferInstance : IsSeparated q)
  have hsep : IsSeparated π := IsSeparated.of_comp π p
  have : LocallyOfFiniteType (π ≫ p) := hπ ▸ (inferInstance : LocallyOfFiniteType q)
  have hlft : LocallyOfFiniteType π := locallyOfFiniteType_of_comp π p
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  obtain ⟨U₀, hU₀, hxU₀, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
    (TopologicalSpace.Opens.mem_top (genericPoint X))
  have hyU₀ : genericPoint Y ∈ π ⁻¹ᵁ U₀ := by
    show π (genericPoint Y) ∈ U₀
    rw [hg]; exact hxU₀
  obtain ⟨V₀, hV₀, hyV₀, hVle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens hyU₀
  haveI : Nonempty U₀ := ⟨⟨_, hxU₀⟩⟩
  haveI : Nonempty V₀ := ⟨⟨_, hyV₀⟩⟩
  letI : Algebra Γ(X, U₀) Γ(Y, V₀) := (π.appLE U₀ V₀ hVle).hom.toAlgebra
  haveI : IsNoetherianRing Γ(X, U₀) := IsLocallyNoetherian.component_noetherian ⟨U₀, hU₀⟩
  haveI : CharZero Γ(X, U₀) :=
    (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ U₀ le_top).hom.charZero_iff
      (RingHom.injective (R := k) _)).1 ‹CharZero k›
  haveI : FaithfulSMul Γ(X, U₀) Γ(Y, V₀) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (GlobalTheory.appLE_injective_of_genericPoint_map π hg ⟨_, hyV₀⟩ hVle)
  haveI : Algebra.FiniteType Γ(X, U₀) Γ(Y, V₀) :=
    HasRingHomProperty.appLE @LocallyOfFiniteType π hlft ⟨U₀, hU₀⟩ ⟨V₀, hV₀⟩ hVle
  haveI : Algebra.IsAlgebraic Γ(X, U₀) Γ(Y, V₀) := GlobalTheory.GenDegAlg.isAlgebraic_appLE π hg hδ hU₀ ⟨_, hyV₀⟩ hVle
  obtain ⟨a₁, ha₁, H₁⟩ := GlobalTheory.finite_away_of_isAlgebraic_of_finiteType (A := Γ(X, U₀)) (B := Γ(Y, V₀))
  obtain ⟨a₂, ha₂, H₂⟩ := GlobalTheory.free_away_mul_of_finiteType (A := Γ(X, U₀)) (B := Γ(Y, V₀))
  obtain ⟨a₃, ha₃, H₃⟩ := GlobalTheory.GenericEtale.exists_etale_away_of_isAlgebraic (A := Γ(X, U₀)) (B := Γ(Y, V₀))
  have ha : a₁ * a₂ * a₃ ≠ 0 := mul_ne_zero (mul_ne_zero ha₁ ha₂) ha₃
  have hUU₀ : X.basicOpen (a₁ * a₂ * a₃) ≤ U₀ := X.basicOpen_le _
  have hUa : IsAffineOpen (X.basicOpen (a₁ * a₂ * a₃)) := hU₀.basicOpen _
  have hxU : genericPoint X ∈ X.basicOpen (a₁ * a₂ * a₃) := by
    have hne : X.basicOpen (a₁ * a₂ * a₃) ≠ ⊥ := fun h => ha ((basicOpen_eq_bot_iff _).1 h)
    obtain ⟨z, hz⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hne
    exact ((genericPoint_spec X).mem_open_set_iff (X.basicOpen (a₁ * a₂ * a₃)).isOpen).2
      ⟨z, trivial, hz⟩
  set U : X.Opens := X.basicOpen (a₁ * a₂ * a₃) with hU_def
  set V : Y.Opens := Y.basicOpen (π.appLE U₀ V₀ hVle (a₁ * a₂ * a₃)) with hV_def
  have hVV₀ : V ≤ V₀ := Y.basicOpen_le _
  have hVe : V = V₀ ⊓ π ⁻¹ᵁ U := Scheme.basicOpen_appLE π V₀ U₀ hVle _
  have hVU : V ≤ π ⁻¹ᵁ U := by rw [hVe]; exact inf_le_right
  have hVa : IsAffineOpen V := hV₀.basicOpen _
  have hyV : genericPoint Y ∈ V := by
    rw [hVe]; exact ⟨hyV₀, show π (genericPoint Y) ∈ U from hg ▸ hxU⟩
  letI iA : Algebra Γ(X, U₀) Γ(X, U) := (X.presheaf.map (homOfLE hUU₀).op).hom.toAlgebra
  letI iB : Algebra Γ(Y, V₀) Γ(Y, V) := (Y.presheaf.map (homOfLE hVV₀).op).hom.toAlgebra
  letI iAB : Algebra Γ(X, U) Γ(Y, V) := (π.appLE U V hVU).hom.toAlgebra
  letI iAB' : Algebra Γ(X, U₀) Γ(Y, V) := (π.appLE U₀ V (hVV₀.trans hVle)).hom.toAlgebra
  haveI : IsScalarTower Γ(X, U₀) Γ(X, U) Γ(Y, V) := IsScalarTower.of_algebraMap_eq'
    (congrArg CommRingCat.Hom.hom (π.map_appLE hVU (homOfLE hUU₀).op).symm)
  haveI : IsScalarTower Γ(X, U₀) Γ(Y, V₀) Γ(Y, V) := IsScalarTower.of_algebraMap_eq'
    (congrArg CommRingCat.Hom.hom (π.appLE_map hVle (homOfLE hVV₀).op).symm)
  haveI hlA : IsLocalization.Away (a₁ * a₂ * a₃) Γ(X, U) :=
    hU₀.isLocalization_of_eq_basicOpen _ (homOfLE hUU₀) rfl
  haveI hlB : IsLocalization.Away (algebraMap Γ(X, U₀) Γ(Y, V₀) (a₁ * a₂ * a₃)) Γ(Y, V) :=
    hV₀.isLocalization_of_eq_basicOpen _ (homOfLE hVV₀) rfl
  have e1 : a₁ * (a₂ * a₃) = a₁ * a₂ * a₃ := (mul_assoc _ _ _).symm
  have e2 : a₂ * (a₁ * a₃) = a₁ * a₂ * a₃ := by ring
  have e3 : a₃ * (a₁ * a₂) = a₁ * a₂ * a₃ := by ring
  have hfin : Module.Finite Γ(X, U) Γ(Y, V) :=
    H₁ (a₂ * a₃) Γ(X, U) Γ(Y, V) (by rw [e1]; exact hlA) (by rw [e1]; exact hlB)
  have hfree : Module.Free Γ(X, U) Γ(Y, V) :=
    H₂ (a₁ * a₃) Γ(X, U) Γ(Y, V) (by rw [e2]; exact hlA) (by rw [e2]; exact hlB)
  have het : Algebra.Etale Γ(X, U) Γ(Y, V) :=
    H₃ (a₁ * a₂) Γ(X, U) Γ(Y, V) (by rw [e3]; exact hlA) (by rw [e3]; exact hlB)
  have hpre : π ⁻¹ᵁ U = V := GlobalTheory.preimage_eq_of_finite_appLE π hUa hVa ⟨_, hyV⟩ hVU hfin
  have key : ∀ (W : Y.Opens) (hW : W ≤ π ⁻¹ᵁ U), W = π ⁻¹ᵁ U → (π.appLE U W hW).hom.Etale →
      (π.appLE U W hW).hom.Finite →
      (letI := (π.appLE U W hW).hom.toAlgebra; Module.Free Γ(X, U) Γ(Y, W)) →
      (π.app U).hom.Etale ∧ (π.app U).hom.Finite ∧
      (letI := (π.app U).hom.toAlgebra; Module.Free Γ(X, U) Γ(Y, π ⁻¹ᵁ U)) := by
    rintro W hW rfl h1 h2 h3
    rw [Scheme.Hom.app_eq_appLE]
    exact ⟨h1, h2, h3⟩
  obtain ⟨h1, h2, h3⟩ := key V hVU hpre.symm het hfin hfree
  exact ⟨U, hUa, hxU, hpre ▸ hVa, h1, h2, h3, finrank_app_eq_residueDegree π hg hUa (hpre ▸ hVa) hxU⟩

end GlobalTheory.GenFinEtField
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgEquivFractionFieldOfLocalRingOfVarietyP
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

namespace GlobalTheory

theorem locModel_fracField_algEquiv : ∀ {K κ : Type} [Field K] [Field κ] [Algebra ℂ K] [Algebra ℂ κ]
  (R : Subring K) (π : R →+* κ), IsLocModel (algebraMap ℂ K) R →
  (∀ a (h : algebraMap ℂ K a ∈ R), π ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a) →
  (∀ f : κ, ∃ a b : R, π b ≠ 0 ∧ f * π b = π a) → Function.Injective π →
  ∃ e : K ≃ₐ[ℂ] κ, ∀ r : R, e r = π r := by
  intro K κ _ _ _ _ R π hR hc hsurj hinj
  haveI : FaithfulSMul R K :=
    (faithfulSMul_iff_algebraMap_injective R K).mpr Subtype.val_injective
  haveI : IsFractionRing R K := IsFractionRing.of_field R K (fun z => by
    obtain ⟨a, ha, b, hb, hb0, e⟩ := hR.frac z
    refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ?_⟩
    change z = a / b
    rw [eq_div_iff hb0, e])
  let φ : K →+* κ := IsFractionRing.lift hinj
  have hφ : ∀ r : R, φ (algebraMap R K r) = π r := fun r => IsFractionRing.lift_algebraMap hinj r
  have hφc : ∀ a : ℂ, φ (algebraMap ℂ K a) = algebraMap ℂ κ a := by
    intro a
    have := hφ ⟨algebraMap ℂ K a, hR.const_mem a⟩
    rw [← hc a (hR.const_mem a)]
    exact this
  let ψ : K →ₐ[ℂ] κ := { φ with commutes' := hφc }
  have hbij : Function.Bijective ψ := by
    refine ⟨ψ.toRingHom.injective, fun f => ?_⟩
    obtain ⟨a, b, hb, e⟩ := hsurj f
    have hb' : (b : K) ≠ 0 := by
      intro h
      apply hb
      have : b = 0 := Subtype.ext h
      rw [this, map_zero]
    refine ⟨(a : K) / b, ?_⟩
    change φ ((a : K) / b) = f
    rw [map_div₀]
    have ha := hφ a
    have hb2 := hφ b
    change φ (a : K) = π a at ha
    change φ (b : K) = π b at hb2
    rw [ha, hb2, div_eq_iff hb, e]
  refine ⟨AlgEquiv.ofBijective ψ hbij, fun r => ?_⟩
  exact hφ r

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleSectionNonvanishingAtNotSpecializingStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ampleSection_nonvanishing_at_not_specializing : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (N : LB X) (x z : X), IsAmpleLB N → ¬ z ⤳ x → ∃ (l : ℕ) (s : (lbPow N l).Sec), 0 < l ∧ x ∈ nonzeroLocus s ∧ z ∉ nonzeroLocus s := by
  first | exact @GlobalTheory.PairStep.exists_sec_mem_not_mem_of_not_specializes | exact GlobalTheory.PairStep.exists_sec_mem_not_mem_of_not_specializes | (intros; apply GlobalTheory.PairStep.exists_sec_mem_not_mem_of_not_specializes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjSameSeparableCharpolySplitPlace
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.SplitConj

theorem exists_conj_of_isSplitAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), ∀ P ∈ Ell E n,
    ∀ w : Pl E, IsSplitAt w → ∀ γ γ' : UL n w, γ.1.val.charpoly = atPl w P → γ'.1.val.charpoly = atPl w P →
      ∃ g : UL n w, γ' = g⁻¹ * γ * g := by
  intro E _ _ _ n P hP w hw γ γ' h h'
  have hs : (atPl w P).Separable := hP.2.2.1.map
  obtain ⟨g, hg⟩ := GlobalTheory.BCT.ClsFin.conj_of_charpoly γ.1 γ'.1 (by rw [h]; exact hs) (h.trans h'.symm)
  have hmem : g ∈ UL n w := by
    rw [UL, if_pos hw]
    exact Subgroup.mem_top g
  exact ⟨⟨g, hmem⟩, Subtype.ext hg⟩

end GlobalTheory.BCT.SplitConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousReadOnAffineOpenRingHomsStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_read_on_affineOpen_ringHoms : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (U : X.Opens) (hU : IsAffineOpen U) (u : ∀ σ : k →+* ℂ, CxPts p σ → ℝ), (∀ σ, ContinuousOn (u σ) (ptsIn p σ U)) → (letI : TopologicalSpace (Γ(X, U) →+* ℂ) := TopologicalSpace.induced (fun x : Γ(X, U) →+* ℂ => (x : Γ(X, U) → ℂ)) inferInstance; ∃ ψ : (Γ(X, U) →+* ℂ) → ℝ, Continuous ψ ∧ (∀ (σ : k →+* ℂ) (y : CxPts p σ) (hy : y ∈ ptsIn p σ U), ψ (evHom hy) = u σ y) ∧ (∀ x : Γ(X, U) →+* ℂ, ∃ (σ : k →+* ℂ) (y : CxPts p σ) (hy : y ∈ ptsIn p σ U), evHom hy = x) ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ) (hy : y ∈ ptsIn p σ U) (W : Set (Γ(X, U) →+* ℂ)), W ∈ 𝓝 (evHom hy) → {z : CxPts p σ | ∃ hz : z ∈ ptsIn p σ U, evHom hz ∈ W} ∈ 𝓝 y) := by
  first | exact @GlobalTheory.ContRead.exists_continuous_read | exact GlobalTheory.ContRead.exists_continuous_read | (intros; apply GlobalTheory.ContRead.exists_continuous_read <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicAddRealChartPointStatement
section
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteAdelic_add_realChartPoint : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (nS nT : ℕ)
    (θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)) (ι : (InfinitePlace F → ℂ) →+ AEF F E), IsChartF θ ι →
      ∀ w : WOF F E nS nT, ∃ (u : WOF F E nS nT) (v : IxF F nS nT → ℂ), u.map (infPartF F E) = 0 ∧ w = u + iotaVF ι v := by
  first | exact @GlobalTheory.RealWeilF.exists_realZero_add_iotaVF | exact GlobalTheory.RealWeilF.exists_realZero_add_iotaVF | (intros; apply GlobalTheory.RealWeilF.exists_realZero_add_iotaVF <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteDimStablePolyAveragesWeightsStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteDim_stable_polyAverages_weights : ∀ (n : ℕ) (ε : Fin n → Bool) (d : ℕ), ∃ A : Set (Fin n → ℝ), A.Finite ∧ ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), ReciprocityTheory.ChartRestriction.DS.IsURepOn (ReciprocityTheory.ChartRestriction.DS.UJset ε) σ → ∀ u : H, ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ Formalism.MainNotions.S.IsKStableOn ε σ S ∧ (∀ P : GlobalTheory.PsCo.Pc1.Poly n, P.totalDegree ≤ d → ∫ k : Formalism.REAL.KG ε, GlobalTheory.PsCo.Pc1.ev (Formalism.REAL.toMK k) P • σ (Formalism.REAL.toMK k) u ∂(Formalism.REAL.muK ε) ∈ S) ∧ ∀ (μ : Fin n → ℝ) (s : H), s ∈ S → s ≠ 0 → Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) σ μ s → μ ∈ A := by
  first | exact @GlobalTheory.PsCo.PolyAvg.polyAvg | exact GlobalTheory.PsCo.PolyAvg.polyAvg | (intros; apply GlobalTheory.PsCo.PolyAvg.polyAvg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShapeIntegratedOperatorRangesPolynomialStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shapeIntegratedOperator_ranges_polynomial : GlobalTheory.PsCo.Pc3.RangeShape := by
  first | exact @GlobalTheory.PsCo.Pc3.rangeShape | exact GlobalTheory.PsCo.Pc3.rangeShape | (intros; apply GlobalTheory.PsCo.Pc3.rangeShape <;> assumption)
end

