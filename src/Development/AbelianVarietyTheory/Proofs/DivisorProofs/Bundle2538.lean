import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2212
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2243
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2191
import ReciprocityTheory.AnalyticForms.RegularLocalRings.ClosureFromSpecMemCompsH
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularAtIffForallSpecializes
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.RegCodimOne

theorem regAt_iff_ord_nonneg {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [GlobalTheory.IsNormalScheme X] {z : X} (hz : Order.coheight z = 1) {g : X.functionField} (hg : g ≠ 0) :
    RegAt z g ↔ 0 ≤ Scheme.ord g z := by
  haveI := IsNormalScheme.isDiscreteValuationRing_stalk hz
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk z)
  have h := le_ordTop_vw_iff (F := X.functionField) ht 0 g
  rw [ordTop_vw_of_ne_zero _ hg, WithTop.coe_le_coe] at h
  have e : Scheme.ord g z = WithZero.log (Ring.ordFrac (X.presheaf.stalk z) g) :=
    (Scheme.ord_eq_iff hz hg).2 (WithZero.exp_log ((map_ne_zero _).2 hg)).symm
  rw [e]
  refine Iff.trans ⟨fun ⟨a, ha⟩ => ⟨a, by simp [ha]⟩, fun ⟨a, ha⟩ => ⟨a, by simp [ha]⟩⟩ h.symm

theorem regularAt_iff_forall_specializes : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (D : CartierDiv X) (x : X) (f : X.functionFieldˣ), D.RegularAt x (f : X.functionField) ↔ ∀ z, z ⤳ x → 0 ≤ Scheme.ord (f : X.functionField) z + D.mult z := by
  intro X _ _ _ D x f
  obtain ⟨g, hg⟩ := D.exists_isEqn x
  obtain ⟨U, hU, hgU⟩ := hg.exists_nhds
  have hne : (f : X.functionField) * (g : X.functionField) ≠ 0 := mul_ne_zero f.ne_zero g.ne_zero
  have key : ∀ z, z ⤳ x → Scheme.ord (f : X.functionField) z + D.mult z =
      Scheme.ord ((f : X.functionField) * (g : X.functionField)) z := fun z hz => by
    rw [(hgU z (hz.mem_open U.isOpen hU)).mult_eq, Scheme.ord_mul f.ne_zero g.ne_zero]
  rw [hg.regularAt_iff]
  refine ⟨fun h z hz => ?_, fun h => regAt_of_forall_coheight_eq_one fun z hz h1 => ?_⟩
  · rw [key z hz]
    by_cases h1 : Order.coheight z = 1
    · exact (regAt_iff_ord_nonneg h1 hne).1 (GlobalTheory.Discrepancy.regAt_of_specializes hz h)
    · rw [Scheme.ord_eq_zero_of_coheight_neq_one h1]
  · exact (regAt_iff_ord_nonneg h1 hne).2 (key z hz ▸ h z hz)

end GlobalTheory.RegCodimOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularAtNormalPointOfDivisors
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Discrepancy

theorem regAt_of_isIntegrallyClosed_stalk : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ y : X, IsIntegrallyClosed (X.presheaf.stalk y) → ∀ f : X.functionField, (∀ z, z ⤳ y → ∀ E : DivOver p, E.IsAt z → f ∈ E.ring) → RegAt y f := by
  intro X _ _ p hp y hy f hf
  haveI : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp).1
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) trivial
  haveI : Nonempty U := ⟨⟨y, hx⟩⟩
  letI := X.presheaf.algebra_section_stalk (⟨y, hx⟩ : U)
  haveI := hU.isLocalization_stalk ⟨y, hx⟩
  refine (mem_range_algebraMap_iff_forall_height_eq_one (A := X.presheaf.stalk y) f).2
    fun q hq h1 => ?_
  let P : PrimeSpectrum Γ(X, U) := ⟨q.comap (algebraMap _ (X.presheaf.stalk y)), inferInstance⟩
  have hP1 : P.asIdeal.height = 1 :=
    (IsLocalization.height_comap (hU.primeIdealOf ⟨y, hx⟩).asIdeal.primeCompl q).trans h1
  have hPQ : P ≤ hU.primeIdealOf ⟨y, hx⟩ := fun s hs => by_contra fun hs' =>
    hq.ne_top (q.eq_top_of_isUnit_mem hs (IsLocalization.map_units (X.presheaf.stalk y)
      (⟨s, hs'⟩ : (hU.primeIdealOf ⟨y, hx⟩).asIdeal.primeCompl)))
  have hz : hU.fromSpec P ∈ U := by
    have : hU.fromSpec P ∈ Set.range hU.fromSpec := ⟨P, rfl⟩
    rwa [hU.range_fromSpec] at this
  let z : U := ⟨hU.fromSpec P, hz⟩
  have hP : hU.primeIdealOf z = P :=
    hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf z)
  have hzx : (z : X) ⤳ y := by
    have h := ((PrimeSpectrum.le_iff_specializes P (hU.primeIdealOf ⟨y, hx⟩)).mp hPQ).map
      hU.fromSpec.continuous
    rwa [hU.fromSpec_primeIdealOf ⟨y, hx⟩] at h
  clear_value z
  haveI := hU.isLocalization_stalk z
  have hc : Order.coheight (z : X) = 1 := by
    have := IsLocalization.AtPrime.ringKrullDim_eq_height (hU.primeIdealOf z).asIdeal
      (X.presheaf.stalk (z : X))
    rw [ringKrullDim_stalk_eq_coheight, hP, hP1] at this
    exact_mod_cast this

  haveI hT : IsLocalization.AtPrime (Localization.AtPrime q) P.asIdeal :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (hU.primeIdealOf ⟨y, hx⟩).asIdeal.primeCompl (Localization.AtPrime q) q
  haveI : IsIntegrallyClosed (Localization.AtPrime q) :=
    isIntegrallyClosed_of_isLocalization _ q.primeCompl q.primeCompl_le_nonZeroDivisors
  have hs : (hU.primeIdealOf z).asIdeal.primeCompl = P.asIdeal.primeCompl := by
    ext s; rw [Ideal.mem_primeCompl_iff, Ideal.mem_primeCompl_iff, hP]
  haveI hZ : IsLocalization P.asIdeal.primeCompl (X.presheaf.stalk (z : X)) := by
    rw [← hs]; exact hU.isLocalization_stalk z
  let e : X.presheaf.stalk (z : X) ≃+* Localization.AtPrime q :=
    (IsLocalization.algEquiv P.asIdeal.primeCompl (X.presheaf.stalk (z : X))
      (Localization.AtPrime q)).toRingEquiv
  haveI : IsIntegrallyClosed (X.presheaf.stalk (z : X)) :=
    ((IsNormalScheme.isDomain_and_isIntegrallyClosed_iff_of_ringEquiv e).2
      ⟨inferInstance, inferInstance⟩).2
  haveI : IsDiscreteValuationRing (X.presheaf.stalk (z : X)) := by
    have h1 : Ring.KrullDimLE 1 (X.presheaf.stalk (z : X)) := krullDimLE_of_coheight_le hc.le
    have hf : ¬ IsField (X.presheaf.stalk (z : X)) := fun h => by
      have := ringKrullDim_eq_zero_of_isField h
      rw [ringKrullDim_stalk_eq_coheight, hc] at this
      simp at this
    have hm := IsLocalRing.isField_iff_maximalIdeal_eq.not.mp hf
    have h3 : IsIntegrallyClosed (X.presheaf.stalk (z : X)) ∧
        ∃! P : Ideal (X.presheaf.stalk (z : X)), P ≠ ⊥ ∧ P.IsPrime :=
      ⟨inferInstance, _, ⟨hm, inferInstance⟩, fun P hP => IsLocalRing.eq_maximalIdeal
        (Ring.krullDimLE_one_iff_of_noZeroDivisors.mp h1 P hP.1 hP.2)⟩
    exact ((IsDiscreteValuationRing.TFAE (X.presheaf.stalk (z : X)) hf).out 0 3).mpr h3
  obtain ⟨E, hE⟩ := DivOver.exists_isAt p (z : X)
  obtain ⟨a, rfl⟩ := (hE f).1 (hf z hzx E hE)
  obtain ⟨⟨c, s⟩, e⟩ := IsLocalization.surj (hU.primeIdealOf z).asIdeal.primeCompl a
  refine (mem_primeLocalSubalgebra_iff q _).2 ⟨algebraMap _ _ s.1, ?_, algebraMap _ _ c, ?_⟩
  · have := s.2
    rw [Ideal.mem_primeCompl_iff] at this
    have h' : s.1 ∉ P.asIdeal := by simpa only [hP] using this
    exact h'
  · have e' := congrArg (algebraMap _ X.functionField) e
    rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at e'
    rw [Algebra.smul_def, mul_comm]
    exact ((algebraMap_germ hx c).trans e'.symm).trans (congrArg _ (algebraMap_germ hx s.1).symm)

end GlobalTheory.Discrepancy
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularSequenceExtendCoords
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ParamFrame

theorem linearIndependent_toCotangent {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {m : ℕ} (r : Fin m → R) (hrsp : FinalTheorems.Rsp R m r) (hr : ∀ i, r i ∈ IsLocalRing.maximalIdeal R) :
    LinearIndependent (IsLocalRing.ResidueField R) (fun i =>
      ((IsLocalRing.maximalIdeal R).toCotangent ⟨r i, hr i⟩ : IsLocalRing.CotangentSpace R)) := by
  classical
  haveI : IsRegularLocalRing R := by
    apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
    rw [← hrsp.2, ← hrsp.1]
    have h1 := Submodule.spanFinrank_span_le_ncard_of_finite (R := R) (Set.finite_range r)
    have h2 : (Set.range r).ncard ≤ m := by
      rw [← Set.image_univ]
      exact (Set.ncard_image_le Set.finite_univ).trans (by simp [Set.ncard_univ])
    exact_mod_cast h1.trans h2
  have hfr : Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) = m := by
    have := (IsRegularLocalRing.iff_finrank_cotangentSpace R).1 inferInstance
    rw [← hrsp.2] at this
    exact_mod_cast this
  refine linearIndependent_of_top_le_span_of_card_eq_finrank ?_ (by simp [hfr])
  have hsp : Submodule.span R (Set.range fun i => (⟨r i, hr i⟩ : IsLocalRing.maximalIdeal R)) = ⊤ := by
    apply Submodule.map_injective_of_injective (IsLocalRing.maximalIdeal R).injective_subtype
    rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp]
    exact hrsp.1
  rw [← IsLocalRing.CotangentSpace.span_image_eq_top_iff] at hsp
  rw [← Set.range_comp] at hsp
  exact hsp.ge

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX) in
open GlobalTheory.AdaptedFrame in

theorem exists_frame_of_rsp : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q] (y : Y) (U : Y.affineOpens) (hy : y ∈ U.1) (c : ℕ) (a : Fin c → Γ(Y, U.1)), FinalTheorems.Rsp (Y.presheaf.stalk y) c (fun i => Y.presheaf.germ U.1 y hy (a i)) → ∃ (V : Y.Opens) (hV : V ≤ U.1) (_ : y ∈ V) (z : Fin n → Γ(Y, V)) (e : Fin c ↪ Fin n), (∀ j, z (e j) = resG Y hV (a j)) ∧ IsFrame (dOn q z) := by
  classical
  intro k _ _ X _ _ p n _ y O hyO m s hrsp
  let f : Fin m → X.presheaf.stalk y := fun i => X.presheaf.germ O.1 y hyO (s i)
  have hf : ∀ i, f i ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk y) :=
    fun i => hrsp.1 ▸ Ideal.subset_span ⟨i, rfl⟩
  have hli := linearIndependent_toCotangent f hrsp hf
  obtain ⟨U, x, b, hUO, hyU, hU, hb⟩ := exists_basis_dFun p n hyO
  let z₀ : Fin m → Γ(X, U) := fun j => resG X hUO (s j)
  have hz₀ (j : Fin m) : (X.presheaf.germ U y hyU).hom (z₀ j) = f j := by
    rw [germ_resG]

  let a : Fin m → Fin n → Γ(X, U) := fun j l => b.repr (dFun (algX p U) (z₀ j)) l
  have ha (j : Fin m) : dFun (algX p U) (z₀ j) = ∑ l, a j l • dFun (algX p U) (x l) := by
    conv_lhs => rw [← b.sum_repr (dFun (algX p U) (z₀ j))]
    simp only [hb, a]

  letI iΓ : Algebra k Γ(X, U) := (algX p U).toAlgebra
  letI iA : Algebra k (X.presheaf.stalk y) :=
    ((X.presheaf.germ U y hyU).hom.comp (algX p U)).toAlgebra
  letI iΓA : Algebra Γ(X, U) (X.presheaf.stalk y) := (X.presheaf.germ U y hyU).hom.toAlgebra
  haveI : IsScalarTower k Γ(X, U) (X.presheaf.stalk y) := IsScalarTower.of_algebraMap_eq' rfl
  haveI := formallySmooth_residueField (n := n) p hU y hyU rfl
  have hw := linearIndependent_tmul_D (k := k) f hf hli
  let ρ : Γ(X, U) →+* IsLocalRing.ResidueField (X.presheaf.stalk y) :=
    (IsLocalRing.residue (X.presheaf.stalk y)).comp (X.presheaf.germ U y hyU).hom
  let ab : Fin m → Fin n → IsLocalRing.ResidueField (X.presheaf.stalk y) := fun j l => ρ (a j l)
  have hab : LinearIndependent (IsLocalRing.ResidueField (X.presheaf.stalk y)) ab := by
    let wx : Fin n → IsLocalRing.ResidueField (X.presheaf.stalk y) ⊗[X.presheaf.stalk y]
        Ω[(X.presheaf.stalk y)⁄k] :=
      fun l => 1 ⊗ₜ KaehlerDifferential.D k (X.presheaf.stalk y) ((X.presheaf.germ U y hyU).hom (x l))
    refine LinearIndependent.of_comp (Fintype.linearCombination _ wx) ?_
    have key : ⇑(Fintype.linearCombination (IsLocalRing.ResidueField (X.presheaf.stalk y)) wx) ∘ ab =
        fun j => (1 : IsLocalRing.ResidueField (X.presheaf.stalk y)) ⊗ₜ[X.presheaf.stalk y]
          KaehlerDifferential.D k (X.presheaf.stalk y) (f j) := by
      funext j
      rw [Function.comp_apply, Fintype.linearCombination_apply, ← hz₀ j]
      have e1 := congrArg (KaehlerDifferential.map k k Γ(X, U) (X.presheaf.stalk y)) (ha j)
      rw [map_sum] at e1
      change KaehlerDifferential.map k k Γ(X, U) (X.presheaf.stalk y)
        (KaehlerDifferential.D k Γ(X, U) (z₀ j)) = _ at e1
      rw [KaehlerDifferential.map_D] at e1
      change KaehlerDifferential.D k (X.presheaf.stalk y) ((X.presheaf.germ U y hyU).hom (z₀ j)) = _ at e1
      rw [e1, TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_smul]
      change _ = 1 ⊗ₜ (a j l • KaehlerDifferential.map k k Γ(X, U) (X.presheaf.stalk y)
        (KaehlerDifferential.D k Γ(X, U) (x l)))
      rw [KaehlerDifferential.map_D, ← algebraMap_smul (X.presheaf.stalk y) (a j l),
        TensorProduct.tmul_smul, ← algebraMap_smul (IsLocalRing.ResidueField (X.presheaf.stalk y))]
      rfl
    rw [key]
    exact hw

  obtain ⟨e, he, hdet⟩ := GlobalTheory.T.exists_standard_basis_extension_det_ne_zero ab hab
  let z : Fin n → Γ(X, U) := Function.extend e z₀ x
  let c : Matrix (Fin n) (Fin n) Γ(X, U) :=
    Matrix.of (Function.extend e a (fun i => Pi.single i (1 : Γ(X, U))))
  have hdz (i : Fin n) : dFun (algX p U) (z i) = ∑ l, c i l • dFun (algX p U) (x l) := by
    by_cases hi : ∃ j, e j = i
    · obtain ⟨j, rfl⟩ := hi
      simp only [z, c, Matrix.of_apply, he.extend_apply]
      exact ha j
    · simp only [z, c, Matrix.of_apply, Function.extend_apply' _ _ _ hi]
      simp [Pi.single_apply]
  have hform : dOn p z = c.det • dOn p x := dForm_eq_det_smul z x c hdz
  have hρ : ρ c.det ≠ 0 := by
    have hm : c.map ρ = Matrix.of (Function.extend e ab
        (fun i => Pi.single i (1 : IsLocalRing.ResidueField (X.presheaf.stalk y)))) := by
      ext i l
      by_cases hi : ∃ j, e j = i
      · obtain ⟨j, rfl⟩ := hi
        simp only [c, ab, Matrix.map_apply, Matrix.of_apply, he.extend_apply]
      · simp only [c, Matrix.map_apply, Matrix.of_apply, Function.extend_apply' _ _ _ hi]
        by_cases hil : l = i
        · subst hil
          simp
        · simp [hil]
    rw [RingHom.map_det]
    exact (congrArg Matrix.det hm).trans_ne hdet
  have hunit : IsUnit ((X.presheaf.germ U y hyU).hom c.det) :=
    (IsLocalRing.residue_ne_zero_iff_isUnit _).1 hρ
  have hyW : y ∈ X.basicOpen c.det := (X.mem_basicOpen c.det y hyU).2 hunit
  have hWU : X.basicOpen c.det ≤ U := X.basicOpen_le _
  refine ⟨X.basicOpen c.det, hWU.trans hUO, hyW, fun i => resG X hWU (z i), ⟨e, he⟩, fun j => ?_, ?_⟩
  · simp only [z, z₀, Function.Embedding.coeFn_mk, he.extend_apply]
    exact resG_resG _ _ _
  · have hx : IsFrame (dOn p x) := ⟨hU, isFreeGen_dForm x b hb⟩
    have h1 := hx.res (hU.basicOpen c.det) hWU
    refine ⟨hU.basicOpen c.det, ?_⟩
    rw [← resForm_dOn hWU, hform, resForm_smul]
    exact h1.gen.smul_iff.2 (RingedSpace.isUnit_res_basicOpen X.toRingedSpace c.det)

end GlobalTheory.ParamFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularSequencePrimeDivisors
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

namespace GlobalTheory.RegParPrime

open ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages

theorem exists_mul_eq_of_mem_span {A : Type} [CommRing A] [IsDomain A] (p : Ideal A) [p.IsPrime]
    (R : Type) [CommRing R] [Algebra A R] [IsLocalization.AtPrime R p] {b x : A}
    (h : algebraMap A R x ∈ Ideal.span {algebraMap A R b}) : ∃ t ∉ p, ∃ s, t * x = s * b := by
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 h
  obtain ⟨⟨s, t⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl (S := R) r
  refine ⟨t, t.2, s, ?_⟩
  apply IsLocalization.injective R (M := p.primeCompl) (Ideal.primeCompl_le_nonZeroDivisors p)
  rw [map_mul, map_mul, ← hr, ← mul_assoc, IsLocalization.mk'_spec']

theorem exists_primeDivisors_of_regularParams : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (y : Y) (U : Y.Opens) (hy : y ∈ U) (c : ℕ) (a : Fin c → Γ(Y, U)), IsRegularLocalRing (Y.presheaf.stalk y) → FinalTheorems.Rsp (Y.presheaf.stalk y) c (fun i => Y.presheaf.germ U y hy (a i)) → ∃ (w : Fin c → Y) (u : Fin c → Y.functionFieldˣ), Function.Injective w ∧ ∀ j, (u j : Y.functionField) = fnOf U (gen_mem hy) (a j) ∧ w j ⤳ y ∧ Order.coheight (w j) = 1 ∧ w j ∉ Y.basicOpen (a j) ∧ Scheme.ord (u j : Y.functionField) (w j) = 1 ∧ ∀ v, v ⤳ y → Order.coheight v = 1 → v ≠ w j → v ∈ Y.basicOpen (a j) := by
  intro Y _ _ y U hy c a hreg hrsp
  obtain ⟨V, hV, hyV, hVU⟩ := exists_isAffineOpen_mem_and_subset hy
  have hVU' : V ≤ U := hVU
  let b : Fin c → Γ(Y, V) := fun i => resG Y hVU' (a i)
  have hgerm : ∀ i, Y.presheaf.germ V y hyV (b i) = Y.presheaf.germ U y hy (a i) := fun i =>
    Y.presheaf.germ_res_apply (homOfLE hVU') y hyV (a i)
  have hrsp' : FinalTheorems.Rsp (Y.presheaf.stalk y) c (fun i => Y.presheaf.germ V y hyV (b i)) := by
    simpa only [hgerm] using hrsp
  haveI := hreg
  obtain ⟨q, hq⟩ := exists_parPrimes hV hyV b hrsp'
  have hprime : ∀ i, Prime (Y.presheaf.germ V y hyV (b i)) :=
    prime_of_regular_params _ hrsp'.1 hrsp'.2
  haveI : Nonempty V := ⟨⟨y, hyV⟩⟩
  haveI : IsNoetherianRing Γ(Y, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have hb0 : ∀ i, b i ≠ 0 := fun i h => (hprime i).ne_zero (by rw [h, map_zero])
  have hfn : ∀ i, fnOf U (gen_mem hy) (a i) = fnOf V (gen_mem hyV) (b i) := fun i =>
    (fnOf_resG hVU' (gen_mem hyV) (a i)).symm
  have ha0 : ∀ i, fnOf U (gen_mem hy) (a i) ≠ 0 := fun i h =>
    hb0 i (fnOf_injective V (gen_mem hyV) (by rw [← hfn, h, map_zero]))
  have hbas : ∀ i, Y.basicOpen (b i) ≤ Y.basicOpen (a i) := fun i => by
    have := Scheme.basicOpen_res Y (a i) (homOfLE hVU').op
    intro z hz
    have hz' : z ∈ V ⊓ Y.basicOpen (a i) := by rw [← this]; exact hz
    exact hz'.2

  have hq1 : ∀ j, (q j).asIdeal.height = 1 := by
    intro j
    have hmin : (q j).asIdeal ∈ (Ideal.span {b j}).minimalPrimes := by
      refine ⟨⟨(q j).2, (Ideal.span_singleton_le_iff_mem _).2 (hq.2.1 j)⟩, ?_⟩
      rintro Q ⟨hQp, hQb⟩ hQle
      exact (hq.2.2.1 j ⟨Q, hQp⟩ (le_trans (show (⟨Q, hQp⟩ : PrimeSpectrum Γ(Y, V)) ≤ q j from hQle)
        (hq.1 j))).mp (hQb (Ideal.mem_span_singleton_self _))
    refine le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hmin) ?_
    refine ENat.one_le_iff_ne_zero.2 fun h0 => hb0 j ?_
    have hmin0 := Ideal.height_eq_zero_iff.1 h0
    have hbot : (q j).asIdeal ≤ ⊥ := hmin0.2 ⟨Ideal.isPrime_bot, bot_le⟩ bot_le
    exact hbot (hq.2.1 j)
  let w : Fin c → Y := fun j => hV.fromSpec (q j)
  have hwV : ∀ j, w j ∈ V := fun j => fromSpec_mem hV (q j)
  have hpw : ∀ j, hV.primeIdealOf ⟨w j, hwV j⟩ = q j := fun j => pOf_fromSpec hV (q j)
  have hcoh : ∀ j, Order.coheight (w j) = 1 := by
    intro j
    letI := Y.presheaf.algebra_section_stalk (⟨w j, hwV j⟩ : V)
    haveI := hV.isLocalization_stalk ⟨w j, hwV j⟩
    have := IsLocalization.AtPrime.ringKrullDim_eq_height (hV.primeIdealOf ⟨w j, hwV j⟩).asIdeal
      (Y.presheaf.stalk (w j))
    rw [ringKrullDim_stalk_eq_coheight, hpw, hq1] at this
    exact_mod_cast this
  refine ⟨w, fun j => Units.mk0 _ (ha0 j), ?_, fun j => ?_⟩
  · intro i j h
    have key : ∀ {z z' : Y} (hz : z ∈ V) (hz' : z' ∈ V), z = z' →
        hV.primeIdealOf ⟨z, hz⟩ = hV.primeIdealOf ⟨z', hz'⟩ := by
      rintro z z' hz hz' rfl
      rfl
    have h2 : q i = q j := (hpw i).symm.trans ((key (hwV i) (hwV j) h).trans (hpw j))
    exact (hq.2.2.2 i j (h2 ▸ hq.2.1 j)).symm
  have hwb : w j ∉ Y.basicOpen (b j) := by
    intro h'
    have h1 : q j ∈ hV.fromSpec ⁻¹ᵁ Y.basicOpen (b j) := h'
    rw [hV.fromSpec_preimage_basicOpen] at h1
    exact h1 (hq.2.1 j)
  refine ⟨rfl, fromSpec_specializes hq j, hcoh j, ?_, ?_, ?_⟩
  · intro h'
    exact hwb ((Y.basicOpen_res (a j) (homOfLE hVU').op).symm ▸ ⟨hwV j, h'⟩ : w j ∈ Y.basicOpen (b j))
  · letI := Y.presheaf.algebra_section_stalk (⟨w j, hwV j⟩ : V)
    haveI hloc0 := hV.isLocalization_stalk ⟨w j, hwV j⟩
    haveI hloc : IsLocalization.AtPrime (Y.presheaf.stalk (w j)) (q j).asIdeal := by
      rw [← hpw j]; exact hloc0
    have hgalg : Y.presheaf.germ V (w j) (hwV j) (b j) = algebraMap Γ(Y, V) (Y.presheaf.stalk (w j)) (b j) := rfl
    have hg0 : Y.presheaf.germ V (w j) (hwV j) (b j) ≠ 0 := fun h0 =>
      ha0 j (by rw [hfn, ← algebraMap_germ (hwV j), h0, map_zero])
    have hmax : Ideal.span {Y.presheaf.germ V (w j) (hwV j) (b j)} =
        IsLocalRing.maximalIdeal (Y.presheaf.stalk (w j)) := by
      refine le_antisymm ?_ ?_
      · rw [Ideal.span_singleton_le_iff_mem,
          ← IsLocalization.AtPrime.map_eq_maximalIdeal (q j).asIdeal (Y.presheaf.stalk (w j)), hgalg]
        exact Ideal.mem_map_of_mem _ (hq.2.1 j)
      · rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (q j).asIdeal (Y.presheaf.stalk (w j)),
          Ideal.map_le_iff_le_comap]
        intro x hx
        rw [Ideal.mem_comap]
        letI := Y.presheaf.algebra_section_stalk (⟨y, hyV⟩ : V)
        haveI := hV.isLocalization_stalk ⟨y, hyV⟩
        haveI : (Ideal.span {Y.presheaf.germ V y hyV (b j)}).IsPrime :=
          (Ideal.span_singleton_prime (hprime j).ne_zero).2 (hprime j)
        let P : Ideal Γ(Y, V) := Ideal.comap (algebraMap Γ(Y, V) (Y.presheaf.stalk y))
          (Ideal.span {Y.presheaf.germ V y hyV (b j)})
        have hPp : P.IsPrime := Ideal.IsPrime.comap _
        have hPle : P ≤ (hV.primeIdealOf ⟨y, hyV⟩).asIdeal := by
          intro z hz
          have hz' : algebraMap Γ(Y, V) (Y.presheaf.stalk y) z ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y) :=
            (Ideal.span_singleton_le_iff_mem _).2
              ((IsLocalRing.mem_maximalIdeal _).2 (hprime j).not_unit) hz
          rw [← IsLocalization.AtPrime.comap_maximalIdeal (Y.presheaf.stalk y)
            (hV.primeIdealOf ⟨y, hyV⟩).asIdeal]
          exact hz'
        have hbP : b j ∈ P := Ideal.mem_span_singleton_self _
        have hqP : q j ≤ ⟨P, hPp⟩ := (hq.2.2.1 j ⟨P, hPp⟩ hPle).mp hbP
        obtain ⟨t, ht, s, hts⟩ := exists_mul_eq_of_mem_span (hV.primeIdealOf ⟨y, hyV⟩).asIdeal
          (Y.presheaf.stalk y) (hqP hx)
        have htq : t ∉ (q j).asIdeal := fun h => ht (hq.1 j h)
        have hu : IsUnit (algebraMap Γ(Y, V) (Y.presheaf.stalk (w j)) t) :=
          IsLocalization.map_units (Y.presheaf.stalk (w j)) (⟨t, htq⟩ : (q j).asIdeal.primeCompl)
        have e : algebraMap Γ(Y, V) (Y.presheaf.stalk (w j)) t * algebraMap Γ(Y, V) (Y.presheaf.stalk (w j)) x =
            algebraMap Γ(Y, V) (Y.presheaf.stalk (w j)) s * algebraMap Γ(Y, V) (Y.presheaf.stalk (w j)) (b j) := by
          rw [← map_mul, ← map_mul, hts]
        refine Ideal.mem_span_singleton'.2 ⟨↑hu.unit⁻¹ * algebraMap Γ(Y, V) (Y.presheaf.stalk (w j)) s, ?_⟩
        rw [hgalg, mul_assoc, ← e, ← mul_assoc, hu.val_inv_mul, one_mul]
    have hlen : Module.length (Y.presheaf.stalk (w j))
        (Y.presheaf.stalk (w j) ⧸ Ideal.span {Y.presheaf.germ V (w j) (hwV j) (b j)}) = 1 := by
      rw [hmax, Module.length_eq_one_iff, isSimpleModule_iff_isCoatom]
      exact Ideal.isMaximal_def.1 (IsLocalRing.maximalIdeal.isMaximal _)
    show Scheme.ord (fnOf U (gen_mem hy) (a j)) (w j) = 1
    rw [hfn, ← algebraMap_germ (hwV j), GlobalTheory.Cartier.ord_algebraMap (hcoh j) hg0, hlen]
    rfl
  · intro v hvy hv1 hvw
    by_contra hva
    have hvV : v ∈ V := hvy.mem_open V.isOpen hyV
    have hbQ : b j ∈ (hV.primeIdealOf ⟨v, hvV⟩).asIdeal := by
      by_contra hn
      apply hva
      have h1 : hV.primeIdealOf ⟨v, hvV⟩ ∈ hV.fromSpec ⁻¹ᵁ Y.basicOpen (b j) := by
        rw [hV.fromSpec_preimage_basicOpen]; exact hn
      have h3 : hV.fromSpec (hV.primeIdealOf ⟨v, hvV⟩) ∈ Y.basicOpen (b j) := h1
      rw [hV.fromSpec_primeIdealOf] at h3
      exact hbas j h3
    have hle : q j ≤ hV.primeIdealOf ⟨v, hvV⟩ :=
      (hq.2.2.1 j _ ((specializes_iff_pOf hV hvV hyV).mp hvy)).mp hbQ
    have hQv1 : (hV.primeIdealOf ⟨v, hvV⟩).asIdeal.height = 1 := by
      letI := Y.presheaf.algebra_section_stalk (⟨v, hvV⟩ : V)
      haveI := hV.isLocalization_stalk ⟨v, hvV⟩
      have := IsLocalization.AtPrime.ringKrullDim_eq_height (hV.primeIdealOf ⟨v, hvV⟩).asIdeal
        (Y.presheaf.stalk v)
      rw [ringKrullDim_stalk_eq_coheight, hv1] at this
      exact_mod_cast this.symm
    have heq : q j = hV.primeIdealOf ⟨v, hvV⟩ := by
      by_contra hne
      haveI : (q j).asIdeal.FiniteHeight :=
        (q j).asIdeal.finiteHeight_iff.mpr (Or.inr (by rw [hq1 j]; exact ENat.one_ne_top))
      have hlt : (q j).asIdeal < (hV.primeIdealOf ⟨v, hvV⟩).asIdeal :=
        lt_of_le_of_ne hle (fun h => hne (PrimeSpectrum.ext h))
      have := Ideal.height_strict_mono_of_isPrime hlt
      rw [hq1 j, hQv1] at this
      exact lt_irrefl _ this
    exact hvw (eq_of_pOf_eq hV hvV (hwV j) (by rw [hpw j]; exact heq.symm))

end GlobalTheory.RegParPrime
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReprAlgebraMap
section
set_option autoImplicit false

noncomputable section

open NumberField GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal

namespace GlobalTheory.LatJet

theorem JetRing.repr_algebraMap {R : Type} [CommRing R] {I : Type} [Fintype I] {n : ℕ} (J : JetRing R I n) (a : R) :
    J.b.repr (algebraMap R J.B a) = Finsupp.single ⟨0, by simp⟩ a := by
  rw [Algebra.algebraMap_eq_smul_one, ← J.one, map_smul, Module.Basis.repr_self, Finsupp.smul_single_one]

theorem jetCore_of (h1 : JetRingEx) (h2 : JetLift) (h3 : JetBC) (h4 : JetAnalytic) : JetCore := by
  obtain ⟨ε, hε⟩ := h4
  refine ⟨ε, ?_⟩
  intro E _ _ _ I _ 𝔠 hf R₀ s r hs R _ _ _ _ _ X₀ δ₀ N hN κ
  obtain ⟨J⟩ := h1 R I (∑ i, κ i)
  obtain ⟨Y⟩ := h2 (FR E) 𝔠 R I (∑ i, κ i) J X₀ δ₀ N hN
  letI : Algebra R₀ J.B := ((algebraMap R J.B).comp (algebraMap R₀ R)).toAlgebra
  let ν : Idx I (∑ i, κ i) := ⟨κ, Nat.le_succ _⟩
  refine ⟨J.b.repr (r.val J.B Y.X' trivial Y.δ') ν, ?_⟩
  intro σ hσ φ c y m hφ hc hr T hT g u hg hu
  obtain ⟨J'⟩ := h1 ℂ I (∑ i, κ i)
  obtain ⟨Y', τ, q, hτ, hq, hd⟩ := h3 E I 𝔠 φ (lattice c y) R σ _ J J' X₀ δ₀ N Y T hT
  letI : Algebra R₀ J'.B := ((algebraMap ℂ J'.B).comp R₀.subtype).toAlgebra
  have hcomm : ∀ a : R₀, τ (algebraMap R₀ J.B a) = algebraMap R₀ J'.B a := by
    intro a
    apply J'.b.repr.injective
    ext μ
    rw [hτ]
    change σ (J.b.repr (algebraMap R J.B (algebraMap R₀ R a)) μ) = J'.b.repr (algebraMap ℂ J'.B (a : ℂ)) μ
    rw [J.repr_algebraMap, J'.repr_algebraMap, Finsupp.single_apply, Finsupp.single_apply]
    split_ifs <;> simp [hσ]
  have hbc := r.baseChange J.B J'.B ⟨τ, hcomm⟩ Y.X' trivial Y'.X' trivial q Y.δ' Y'.δ' hq hd
  have key := hε E I 𝔠 φ c y hf hφ hc R₀ s r m hs hr T _ J' Y' (fun _ => rfl) g ν u hg hu
  rw [hbc] at key
  rw [← key]
  exact congrArg (T.C ^ (2 * s) * ·) (hτ _ ν).symm

end GlobalTheory.LatJet
end
end

