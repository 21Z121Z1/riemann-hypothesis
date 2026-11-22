import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0081
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3255
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3110
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2790
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2813
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3250
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3249
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFramedChartSnc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2291
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0569
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2356
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0025
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3252
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3245
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0415
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0320
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3071
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3251
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOneBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2843

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFamilyExpansionEqConstMulAlgClosure
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem gs_liftFun_top {S0 : Scheme.{0}} (A : Over S0) {T : Over S0} (W : (T ⊗ A).left.Opens) (r : Γ(T.left, ⊤))
    {Z : Scheme.{0}} (q : Z ⟶ (T ⊗ A).left) (z : Z) (hz : q z ∈ W) :
    gs q z W (liftFun A W r) = gs (q ≫ (fst T A).left) z ⊤ r :=
  (gs_res q z le_top hz _).trans (gs_pull q (fst T A).left z ⊤ trivial r)

theorem fvalue_const : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ) (wA : LB.Iso C.A.L (C.P.L.L.pull C.α)), wA.IsGen → ∀ E₀ (Φ₀ : IntFam (maximalIdeal R) D.toPre (C.n ^ j) → H0 C.A.L (C.n ^ j)), Eqv D.toPre C.A (Kb R) (C.n ^ j) (C.lab j) E₀ → (∀ F₀ s, F₀.Over s → Agree C.A.L (E₀ s) (Φ₀ F₀)) → ∀ (Φ : IntFam (maximalIdeal R) D.toPre (C.n ^ j) → SecK C.P.L.L C.α (C.n ^ j)), (∀ F₀ (Z : Scheme.{0}) (p : Z ⟶ C.A.A.left) (z : Z) J J', Good C.P.L.L z J → Good C.A.L z J' → sval (Φ F₀) p z J = (gw wA p z (J (p ≫ C.α)) (J' p) ^ (C.n ^ j)).val * sval (Φ₀ F₀) p z J') → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F] (em : Kb R →ₐ[FractionRing R] F), (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∃ c : F, c ≠ 0 ∧ ∀ (F₀ : IntFam (maximalIdeal R) D.toPre (C.n ^ j)) (σ : SecK C.P.L.L T.β (C.n ^ j)), T.ExpBy 1 σ F₀ → ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left), p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = p' ≫ (fst (TFK (R := R) F) C.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z J, Good C.P.L.L z J → sval σ p z J = gs (p' ≫ (fst (TFK (R := R) F) C.A.A).left) z ⊤ (fnF F c) * sval (Φ F₀) (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z J := by
  intro R _ _ _ hR D C j wA hwA E₀ Φ₀ hE₀ hΦ₀ Φ hΦ W _ _ _ T F _ _ _ _ em hem
  obtain ⟨lab, E, hlab, hE, hT⟩ := GlobalTheory.T.trait_inverse_expansion_equivariant_labels R hR D C j wA hwA W T F em hem
  have hodd : Odd (C.n ^ j) := C.n_odd.pow
  obtain ⟨E', hE', hAg⟩ := GlobalTheory.T.exists_equivariant_bijection_larger_closed_field R hR D C.A (C.n ^ j) hodd (C.lab j) E₀ Φ₀ hE₀ hΦ₀ F em lab hlab
  haveI : CharZero R := hR.2
  obtain ⟨c₀, hc₀⟩ := GlobalTheory.Mum.eqv_eq_smul R (maximalIdeal R) D C.A F (C.n ^ j) hodd lab E E' hE hE'
  refine ⟨(c₀ : F)⁻¹, inv_ne_zero c₀.ne_zero, ?_⟩
  intro F₀ σ hσ Z p p' h1 h2 z J hJ
  obtain ⟨s, hs, -⟩ := GlobalTheory.Mum.IntFam.existsUnique_over R (maximalIdeal R) D.toPre (C.n ^ j) F₀ F
  obtain ⟨J', hJ', -⟩ := exists_good C.A.L C.A.isLB z (K := Empty) (fun e => e.elim) (fun e => e.elim)
    (fun a => a.elim) (fun k => k.elim)
  set q := p' ≫ (snd (TFK (R := R) F) C.A.A).left with hq
  have e1 := hT F₀ s σ hs hσ Z p p' h1 h2 z J J' hJ hJ'
  have e2 : sval (E' s) p' z J' = gs (p' ≫ (fst (TFK (R := R) F) C.A.A).left) z ⊤ (fnF F (c₀ : F)) * sval (E s) p' z J' := by
    unfold sval
    refine (congrArg (gs p' z _) (hc₀ s _)).trans ?_
    exact (gs_mul p' z _ (hJ'.mem _ p') _ _).trans (congrArg (· * _) (gs_liftFun_top _ _ _ _ _ (hJ'.mem _ p')))
  have e3 := hAg F₀ s hs Z p' q (Category.comp_id _).symm z J' hJ'
  have e4 := hΦ F₀ Z q z J J' hJ hJ'
  have hβ : J (q ≫ C.α) = J (p ≫ T.β) := by rw [h1, hq, Category.assoc]
  rw [hβ] at e4
  have huv : gs (p' ≫ (fst (TFK (R := R) F) C.A.A).left) z ⊤ (fnF F (c₀ : F)⁻¹) *
      gs (p' ≫ (fst (TFK (R := R) F) C.A.A).left) z ⊤ (fnF F (c₀ : F)) = 1 := by
    rw [← gs_mul (p' ≫ (fst (TFK (R := R) F) C.A.A).left) z ⊤ trivial, fnF, fnF, ← map_mul, inv_mul_cancel₀ c₀.ne_zero,
      map_one, gs_eq (p' ≫ (fst (TFK (R := R) F) C.A.A).left) z ⊤ trivial, map_one, map_one]
  rw [e1, e4, ← e3, e2]
  linear_combination (-(gw wA q z (J (p ≫ T.β)) (J' q) ^ (C.n ^ j)).val * sval (E s) p' z J') * huv

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCharpolyBcMapIff
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AV.AbVar

variable {K : Type} [Field K] (L : Type) [Field L] [Algebra K L]

def bcAdd (A : AbVar K) : End A →+ End (baseChange L A) where
  toFun := bcMap L
  map_zero' := by
    have h := ((bcMap_functorial K L A A A).1 0 0)
    simpa using h
  map_add' := (bcMap_functorial K L A A A).1

theorem bcMap_intCast_sub (A : AbVar K) (n : ℤ) (f : End A) :
    bcMap L ((n : End A) - f) = @HSub.hSub (End (baseChange L A)) (End (baseChange L A)) (End (baseChange L A)) _
      (n : End (baseChange L A)) (bcMap L f) := by
  have h1 : bcMap L (𝟙 A) = 𝟙 _ := (bcMap_functorial K L A A A).2.2.1
  have e : ∀ g : End A, bcMap L g = bcAdd L A g := fun _ => rfl
  rw [e, map_sub, ← zsmul_one, map_zsmul, ← e, ← e]
  congr 1
  rw [← zsmul_one]
  congr 1

theorem isCharpoly_bcMap_iff (A : AbVar K) (f : End A) (P : Polynomial ℤ) :
    IsCharpoly (A := baseChange L A) (bcMap L f) P ↔ IsCharpoly f P := by
  unfold IsCharpoly
  have hd : (baseChange L A).dim = A.dim := rfl
  refine and_congr Iff.rfl (and_congr (by rw [hd]) (forall_congr' fun n => ?_))
  rw [← bcMap_intCast_sub, (isIsogeny_bcMap_iff_and_deg_bcMap K L A A _).2]

theorem isCharpoly_unique {A : AbVar K} (f : End A) {P Q : Polynomial ℤ}
    (hP : IsCharpoly f P) (hQ : IsCharpoly f Q) : P = Q :=
  Polynomial.funext fun n => by rw [hP.2.2 n, hQ.2.2 n]

theorem charpoly_bcMap : ∀ (K : Type) [Field K] (L : Type) [Field L] [Algebra K L] (A : AbVar K) (f : End A),
    charpoly (A := baseChange L A) (bcMap L (A := A) (B := A) f) = charpoly f := by
  intro K _ L _ _ A f
  classical
  unfold charpoly
  by_cases h : ∃ P, IsCharpoly f P
  · have h' : ∃ P, IsCharpoly (A := baseChange L A) (bcMap L f) P :=
      let ⟨P, hP⟩ := h; ⟨P, (isCharpoly_bcMap_iff L A f P).2 hP⟩
    rw [dif_pos h, dif_pos h']
    exact isCharpoly_unique f ((isCharpoly_bcMap_iff L A f _).1 h'.choose_spec) h.choose_spec
  · have h' : ¬ ∃ P, IsCharpoly (A := baseChange L A) (bcMap L f) P :=
      fun ⟨P, hP⟩ => h ⟨P, (isCharpoly_bcMap_iff L A f P).1 hP⟩
    rw [dif_neg h, dif_neg h']

end GlobalTheory.AV.AbVar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImmersionOfProperClosedImmersionModIdealStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosedImmersion_of_proper_closedImmersion_mod_ideal : ∀ (R : Type) [CommRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ → ∀ (X Z : Scheme.{0}) (φ : X ⟶ Z) (p : Z ⟶ Spec (CommRingCat.of R)), IsProper φ → UniversallyClosed p → IsClosedImmersion (((baseIdeal p I).comap φ).subschemeι ≫ φ) → IsClosedImmersion φ := by
  first | exact @GlobalTheory.ClosedLev.isClosedImmersion_of_mod | exact GlobalTheory.ClosedLev.isClosedImmersion_of_mod | (intros; apply GlobalTheory.ClosedLev.isClosedImmersion_of_mod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlatOfConstMulPeriodDeterminantStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFlat_of_const_mul_periodDeterminant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : (Xo.XF c).Opens) (τ : E →+* ℂ) (e : c.F →+* ℂ) (g : ℕ) (en : Fin g ≃ Pad.Letter D) (Fu : Fam Xo c e en) (x : ∀ i, Hor.Idx D τ → (Fu.Di i).La) (hm : Fin Fu.n → Matrix (Hor.Idx D τ) (Hor.Idx D τ) E) (σb : RuleY Y) (σ : RuleU Xo c) (κ : ℂ) (B : GlobalTheory.ProjVar.Var c.F) (io : B.X ⟶ gen Y), IsClosed (U : Set (Xo.XF c)) → IsOpenImmersion io → Set.range io = compactOf Y U → io ≫ genStr Y = B.str → τ (H.rt : E) = H.rt0 → (∀ i, IsPerBasis (Fu.Di i) (x i) (hm i)) → Restricts Y U τ σb σ → (∀ (a : CxFr Y e) v w i Q, Per Fu a i Q → FrY Y (compactOf Y U) τ e a.1.1 v w → Match τ a.2 v w → σb ℂ a.1.1 v w = κ * perVal c e τ (x i) (hm i) Q) → IsFlatAt Xo c U τ σ e := by
  first | exact @GlobalTheory.DetLine.FlatMul.isFlatAt_of_eq_perVal | exact GlobalTheory.DetLine.FlatMul.isFlatAt_of_eq_perVal | (intros; apply GlobalTheory.DetLine.FlatMul.isFlatAt_of_eq_perVal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsReducedAdicCompletionTensorResidueField
section
open IsLocalRing GlobalTheory.Toroidal TensorProduct

namespace GlobalTheory.EtaleCompletionRadical

theorem isRadical_map_of_flat {A B : Type} [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
    [Module.Flat A B] (I : Ideal A) (hI : I.IsRadical)
    (hfib : ∀ (P : Ideal A) [P.IsPrime], _root_.IsReduced (B ⊗[A] P.ResidueField)) :
    (I.map (algebraMap A B)).IsRadical := by
  classical
  haveI : Finite I.minimalPrimes := (Ideal.finite_minimalPrimes_of_isNoetherianRing A I).to_subtype
  haveI : Fintype I.minimalPrimes := Fintype.ofFinite _
  haveI hpr : ∀ P : I.minimalPrimes, P.1.IsPrime := fun P => P.2.1.1
  have hle : ∀ P : I.minimalPrimes, I ≤ P.1 := fun P => P.2.1.2
  let g : ∀ P : I.minimalPrimes, (A ⧸ I) →ₐ[A] P.1.ResidueField := fun P =>
    Ideal.Quotient.liftₐ I (IsScalarTower.toAlgHom A A P.1.ResidueField) (fun a ha => by
      change algebraMap A P.1.ResidueField a = 0
      exact Ideal.algebraMap_residueField_eq_zero.2 (hle P ha))
  let f : (A ⧸ I) →ₗ[A] ∀ P : I.minimalPrimes, P.1.ResidueField := LinearMap.pi fun P => (g P).toLinearMap
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [Ideal.Quotient.eq_zero_iff_mem]
    refine hI (Ideal.sInf_minimalPrimes (I := I) ▸ ?_)
    refine Ideal.mem_sInf.2 fun P hP => ?_
    have h0 := congrFun hy ⟨P, hP⟩
    haveI : P.IsPrime := hP.1.1
    exact Ideal.algebraMap_residueField_eq_zero.1 h0
  have hfB := Module.Flat.lTensor_preserves_injective_linearMap (M := B) f hf
  intro x ⟨n, hn⟩

  have hz : (x ⊗ₜ[A] (1 : A ⧸ I) : B ⊗[A] (A ⧸ I)) = 0 := by
    apply hfB
    rw [map_zero]
    apply (TensorProduct.piRight A A B fun P : I.minimalPrimes => P.1.ResidueField).injective
    rw [map_zero]
    funext P
    simp only [LinearMap.lTensor_tmul, TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul, Pi.zero_apply]
    change x ⊗ₜ[A] (g P 1) = 0
    rw [map_one]
    have hnil : IsNilpotent (x ⊗ₜ[A] (1 : P.1.ResidueField) : B ⊗[A] P.1.ResidueField) := by
      refine ⟨n, ?_⟩
      rw [Algebra.TensorProduct.tmul_pow, one_pow]
      change Algebra.TensorProduct.includeLeft (S := A) (x ^ n) = 0
      have hk : I.map (algebraMap A B) ≤ RingHom.ker
          (Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := B) (B := P.1.ResidueField)).toRingHom := by
        rw [Ideal.map_le_iff_le_comap]
        intro a ha
        simp only [Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          Algebra.TensorProduct.includeLeft_apply]
        rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one,
          Ideal.algebraMap_residueField_eq_zero.2 (hle P ha), TensorProduct.tmul_zero]
      exact hk hn
    exact hnil.eq_zero
  have := congrArg (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).symm hz
  rw [← Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk, AlgEquiv.symm_apply_apply, map_zero,
    Ideal.Quotient.eq_zero_iff_mem] at this
  exact this

end GlobalTheory.EtaleCompletionRadical

namespace GlobalTheory.EtaleCompletionRadical

set_option synthInstance.maxHeartbeats 400000 in

theorem isReduced_adicCompletion_tensor_residueField (A : Type) [CommRing A] [IsLocalRing A]
    [Algebra.EssFiniteType ℤ A] (P : Ideal A) [P.IsPrime] :
    _root_.IsReduced (AdicCompletion (maximalIdeal A) A ⊗[A] P.ResidueField) := by
  have h := GlobalTheory.GeomRegFibTransport.geomRegFib_adicCompletion_of_essFiniteType_int
    GlobalTheory.qeRing_of_finiteType_int A P P.ResidueField (IntermediateField.fg_of_noetherian _)
  obtain ⟨-, hreg⟩ := h
  refine isReduced_ofLocalizationMaximal _ fun Q hQ => ?_
  haveI := hreg Q
  infer_instance

theorem isRadical_map_of_isEtaleCompletion : ∀ (A R : Type) [CommRing A] [IsLocalRing A] [Algebra.EssFiniteType ℤ A]
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (φ : A →+* R), IsAdicComplete (maximalIdeal R) R →
    IsEtaleCompletion φ → ((residue R).comp φ).FormallyUnramified → ∀ I : Ideal A, I.IsRadical →
    (I.map φ).IsRadical := by
  intro A R _ _ _ _ _ _ φ hc het hfu I hI
  haveI : IsNoetherianRing A := Algebra.EssFiniteType.isNoetherianRing ℤ A
  haveI := hc
  letI : Algebra A R := φ.toAlgebra
  obtain ⟨g, hg, het'⟩ := GlobalTheory.NormalBaseChange.exists_etale_of_isEtaleCompletion A R het hfu
  letI : Algebra (AdicCompletion (maximalIdeal A) A) R := g.toAlgebra
  have h1 : (I.map (algebraMap A (AdicCompletion (maximalIdeal A) A))).IsRadical :=
    isRadical_map_of_flat I hI fun P _ => isReduced_adicCompletion_tensor_residueField A P
  have h2 := GlobalTheory.EtaleReducedEq.isRadical_map_of_etale (C := R) _ h1
  rw [Ideal.map_map] at h2
  change (I.map (g.comp _)).IsRadical at h2
  rwa [hg] at h2

end GlobalTheory.EtaleCompletionRadical
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyBaseChangeIffAndDegreeEqStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isogeny_baseChange_iff_and_degree_eq : ∀ (K : Type) [Field K] (L : Type) [Field L] [Algebra K L] (A B : AbVar K) (f : A ⟶ B), (IsIsogeny (bcMap L f) ↔ IsIsogeny f) ∧ deg (bcMap L f) = deg f := by
  first | exact @GlobalTheory.AV.AbVar.isIsogeny_bcMap_iff_and_deg_bcMap | exact GlobalTheory.AV.AbVar.isIsogeny_bcMap_iff_and_deg_bcMap | (intros; apply GlobalTheory.AV.AbVar.isIsogeny_bcMap_iff_and_deg_bcMap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyCompAndDegreeMulStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isogeny_comp_and_degree_mul : ∀ (K : Type) [Field K] (A B C : AbVar K) (f : A ⟶ B) (g : B ⟶ C), IsIsogeny f → IsIsogeny g → IsIsogeny (f ≫ g) ∧ deg (f ≫ g) = deg f * deg g := by
  first | exact @GlobalTheory.AV.AbVar.isIsogeny_comp_and_deg_comp | exact GlobalTheory.AV.AbVar.isIsogeny_comp_and_deg_comp | (intros; apply GlobalTheory.AV.AbVar.isIsogeny_comp_and_deg_comp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyDegreeEqCardKernelOfKilledByInvertibleStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isogenyDegree_eq_card_kernel_of_killed_by_invertible : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B) (n : ℕ), (n : K) ≠ 0 → IsIsogeny f → (∀ (T : Over (Sp K)) (x : T ⟶ A.X), x ≫ f.hom = 1 → x ^ n = 1) → deg f = Nat.card (ptMap f).ker := by
  first | exact @GlobalTheory.AV.DegSep.deg_eq_card_ker_of_killed | exact GlobalTheory.AV.DegSep.deg_eq_card_ker_of_killed | (intros; apply GlobalTheory.AV.DegSep.deg_eq_card_ker_of_killed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedWeilDivisorSumSymmNoCommonDivisor
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MixHt

theorem finsum_mul_comp_eq_sum_indicator {W Z : Type*} (c : W → ℝ) (hc : (Function.support c).Finite) (f : W → Z)
    (F : Finset Z) (hF : f '' Function.support c ⊆ ↑F) (g : Z → ℝ) :
    ∑ᶠ w, c w * g (f w) = ∑ x ∈ F, g x * ∑ᶠ w, c w * Set.indicator {x} 1 (f w) := by
  classical
  have hsub : ∀ h : Z → ℝ, Function.support (fun w => c w * h (f w)) ⊆ ↑hc.toFinset := fun h w hw => by
    rw [Set.Finite.coe_toFinset]; exact left_ne_zero_of_mul hw
  rw [finsum_eq_sum_of_support_subset _ (hsub g)]
  have e : ∀ x : Z, ∑ᶠ w, c w * Set.indicator {x} 1 (f w) = ∑ w ∈ hc.toFinset, c w * Set.indicator {x} 1 (f w) :=
    fun x => finsum_eq_sum_of_support_subset _ (hsub (Set.indicator {x} 1))
  simp_rw [e, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w hw => ?_
  have hwF : f w ∈ F := hF ⟨w, (Set.Finite.mem_toFinset hc).1 hw, rfl⟩
  simp only [Set.indicator_apply, Set.mem_singleton_iff, Pi.one_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq F (f w) (fun x => g x * c w), if_pos hwF, mul_comm]

theorem exists_finset_resCyc {k : Type} [CommRing k] {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    {q : Y ⟶ Sp k} (hq : IsAmb q) {B : LB Y} (hB : B.IsLB) (t : B.Sec) (z : Y) :
    ∃ F : Finset Y, ∀ F' : Finset Y, F ⊆ F' → ∀ g : Y → ℝ,
      resCyc hB t g z = ∑ x ∈ F', g x * resCyc hB t (Set.indicator {x} 1) z := by
  classical
  by_cases h : genericPoint (clo z) ∈ nonzeroLocus (secPull t (cloι z))
  · have : IsNoetherian (clo z) := (hq.sub (cloι z)).isNoetherian
    set D := divOfSec (LB.isLB_pull hB (cloι z)) _ h
    have hc : (Function.support fun w => (D.mult w : ℝ)).Finite :=
      D.finite_support_mult.subset fun w hw h0 => hw (by simp [h0])
    refine ⟨(hc.image fun w => cloι z w).toFinset, fun F' hF' g => ?_⟩
    simp only [resCyc, dif_pos h]
    refine finsum_mul_comp_eq_sum_indicator _ hc _ F' ?_ g
    intro y hy
    exact hF' ((Set.Finite.mem_toFinset _).2 hy)
  · refine ⟨∅, fun F' _ g => ?_⟩
    simp [resCyc, dif_neg h]

end GlobalTheory.MixHt

namespace GlobalTheory.MixHt

theorem iterDiv_symm : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsAmb q → ∀ (A B : LB Y) (hA : A.IsLB) (hB : B.IsLB) (s : A.Sec) (t : B.Sec) (hs : genericPoint Y ∈ nonzeroLocus s) (ht : genericPoint Y ∈ nonzeroLocus t), (∀ z : Y, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t) → ∀ g : Y → ℝ, ∑ᶠ z, ((divOfSec hA s hs).mult z : ℝ) * resCyc hB t g z = ∑ᶠ z, ((divOfSec hB t ht).mult z : ℝ) * resCyc hA s g z := by
  intro k _ Y _ _ q hq A B hA hB s t hs ht hst g
  classical
  have : IsNoetherian Y := hq.isNoetherian
  choose Ft hFt using exists_finset_resCyc hq hB t
  choose Fs hFs using exists_finset_resCyc hq hA s
  have hms : (Function.support fun z => ((divOfSec hA s hs).mult z : ℝ)).Finite :=
    (divOfSec hA s hs).finite_support_mult.subset fun w hw h0 => hw (by simp [h0])
  have hmt : (Function.support fun z => ((divOfSec hB t ht).mult z : ℝ)).Finite :=
    (divOfSec hB t ht).finite_support_mult.subset fun w hw h0 => hw (by simp [h0])
  set F := hms.toFinset.biUnion Ft ∪ hmt.toFinset.biUnion Fs
  have Ls : ∀ h : Y → ℝ, ∑ᶠ z, ((divOfSec hA s hs).mult z : ℝ) * resCyc hB t h z =
      ∑ z ∈ hms.toFinset, ((divOfSec hA s hs).mult z : ℝ) * resCyc hB t h z := fun h =>
    finsum_eq_sum_of_support_subset _ fun z hz => by
      rw [Set.Finite.coe_toFinset]; exact left_ne_zero_of_mul hz
  have Lt : ∀ h : Y → ℝ, ∑ᶠ z, ((divOfSec hB t ht).mult z : ℝ) * resCyc hA s h z =
      ∑ z ∈ hmt.toFinset, ((divOfSec hB t ht).mult z : ℝ) * resCyc hA s h z := fun h =>
    finsum_eq_sum_of_support_subset _ fun z hz => by
      rw [Set.Finite.coe_toFinset]; exact left_ne_zero_of_mul hz
  have Es : ∑ z ∈ hms.toFinset, ((divOfSec hA s hs).mult z : ℝ) * resCyc hB t g z =
      ∑ x ∈ F, g x * ∑ z ∈ hms.toFinset, ((divOfSec hA s hs).mult z : ℝ) * resCyc hB t (Set.indicator {x} 1) z := by
    rw [Finset.sum_congr rfl fun z hz => by
      rw [hFt z F (Finset.subset_union_left.trans' (Finset.subset_biUnion_of_mem Ft hz)) g]]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have Et : ∑ z ∈ hmt.toFinset, ((divOfSec hB t ht).mult z : ℝ) * resCyc hA s g z =
      ∑ x ∈ F, g x * ∑ z ∈ hmt.toFinset, ((divOfSec hB t ht).mult z : ℝ) * resCyc hA s (Set.indicator {x} 1) z := by
    rw [Finset.sum_congr rfl fun z hz => by
      rw [hFs z F (Finset.subset_union_right.trans' (Finset.subset_biUnion_of_mem Fs hz)) g]]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [Ls, Lt, Es, Et]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Ls, ← Lt, GlobalTheory.T.finsum_mult_resCyc_indicator_symm' k Y q hq A B hA hB s t hs ht hst x]

end GlobalTheory.MixHt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieOcExistsSpMap
section
noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {S : Scheme.{0}}

theorem lieOc_spMap_inj {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] {f g : R₁ →+* R₂} (h : spMap f = spMap g) : f = g := by
  have := Spec.map_injective h
  exact congrArg CommRingCat.Hom.hom this

theorem lieOc_exists_spMap {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] (y : Sp R₂ ⟶ Sp R₁) : ∃ f : R₁ →+* R₂, y = spMap f :=
  ⟨(Spec.preimage y).hom, by simp [spMap]⟩

theorem lieOc_spMap_comp {R₁ R₂ R₃ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₃] (f : R₁ →+* R₂) (g : R₂ →+* R₃) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp [spMap, ← Spec.map_comp]

theorem lieHer_closed (b : Base D R) (s : S ⟶ Sp R) (A : Over S) [GrpObj A] [IsCommMonObj A]
    (hA : Smooth A.hom) (act : OActN D.O A) :
    ∃ (Z : Scheme.{0}) (i : Z ⟶ S), IsClosedImmersion i ∧
      ∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ S), x ≫ s = spMap β →
        ((∃ y : Sp R' ⟶ Z, y ≫ i = x) ↔ LieHer b act β x) := by
  let P : ∀ (R' : Type) [CommRing R'], (Sp R' ⟶ S) → Prop := fun R' _ x =>
    ∀ β : R →+* R', x ≫ s = spMap β → LieHer b act β x
  have hP : ∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ S), x ≫ s = spMap β →
      (P R' x ↔ LieHer b act β x) := by
    intro R' _ β x hx
    refine ⟨fun h => h β hx, fun h β' hx' => ?_⟩
    have : β' = β := lieOc_spMap_inj (hx'.symm.trans hx)
    subst this; exact h

  have her : ∀ (R' : Type) [CommRing R'] (R'' : Type) [CommRing R''] (g : R' →+* R'') (x : Sp R' ⟶ S),
      P R' x → P R'' (spMap g ≫ x) := by
    intro R' _ R'' _ g x hx β'' hβ''
    obtain ⟨β, hβ⟩ := lieOc_exists_spMap (x ≫ s)
    have e : β'' = g.comp β := lieOc_spMap_inj (by rw [← hβ'', Category.assoc, hβ, lieOc_spMap_comp])
    subst e
    intro R''' _ g'
    have h := hx β hβ R''' (g'.comp g)
    rw [← lieOc_spMap_comp] at h
    simpa [Category.assoc, RingHom.comp_assoc] using h

  have loc : ∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ S) (t : Finset R'), Ideal.span (t : Set R') = ⊤ →
      (∀ r ∈ t, P (Localization.Away r) (spMap (algebraMap R' (Localization.Away r)) ≫ x)) → P R' x := by
    classical
    intro R' _ x t ht hloc β hβ R'' _ g
    have hloc' : ∀ r ∈ t, LieHer b act ((algebraMap R' (Localization.Away r)).comp β)
        (spMap (algebraMap R' (Localization.Away r)) ≫ x) := fun r hr =>
      hloc r hr _ (by rw [Category.assoc, hβ, lieOc_spMap_comp])
    have key : ∀ r : R', (Localization.awayMap g r).comp (algebraMap R' (Localization.Away r)) =
        (algebraMap R'' (Localization.Away (g r))).comp g := fun r => IsLocalization.map_comp _
    refine ⟨?_, ?_⟩
    · refine GlobalTheory.T.harrisTaylor_lie_condition_of_basicOpen_cover p D R b S A act R'' (g.comp β) (spMap g ≫ x) (t.image g) ?_ ?_
      · rw [Finset.coe_image, ← Ideal.map_span, ht, Ideal.map_top]
      · intro r'' hr''
        obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hr''
        have h := (hloc' r hr (Localization.Away (g r)) (Localization.awayMap g r)).1
        rw [← Category.assoc, lieOc_spMap_comp, ← RingHom.comp_assoc, key] at h
        rw [← Category.assoc, lieOc_spMap_comp, ← RingHom.comp_assoc]
        exact h
    · intro k _ _ g' i
      have hex : ∃ r ∈ t, g' (g r) ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        have : Ideal.span (t : Set R') ≤ RingHom.ker (g'.comp g) :=
          Ideal.span_le.2 fun r hr => by simpa using hcon r hr
        rw [ht] at this
        have h1 : (1 : R') ∈ RingHom.ker (g'.comp g) := this Submodule.mem_top
        simp at h1
      obtain ⟨r, hr, hne⟩ := hex
      let hr' : Localization.Away r →+* k := IsLocalization.Away.lift r (g := g'.comp g) (isUnit_iff_ne_zero.2 hne)
      have hlift : hr'.comp (algebraMap R' (Localization.Away r)) = g'.comp g :=
        IsLocalization.Away.lift_comp r _
      have h := (hloc' r hr (Localization.Away r) (RingHom.id _)).2 k hr' i
      have e1 : spMap hr' ≫ spMap (RingHom.id (Localization.Away r)) ≫ spMap (algebraMap R' (Localization.Away r)) ≫ x =
          spMap g' ≫ spMap g ≫ x := by
        simp only [← Category.assoc, lieOc_spMap_comp]
        rw [RingHom.id_comp, hlift]
      have e2 : hr'.comp ((RingHom.id _).comp ((algebraMap R' (Localization.Away r)).comp β)) = g'.comp (g.comp β) := by
        rw [RingHom.id_comp, ← RingHom.comp_assoc, hlift, RingHom.comp_assoc]
      rw [e1, e2] at h
      exact h
  obtain ⟨Z, i, hi, hZ⟩ := GlobalTheory.T.isClosed_of_local_ideal_point_property S P her loc (fun z => by
    obtain ⟨U, hU, hz, K, hK⟩ := GlobalTheory.T.kottwitzLieCondition_locally_cut_out_by_ideal p D R b S s A hA act z
    refine ⟨U, hU, hz, K, fun R' _ f => ?_⟩
    obtain ⟨β, hβ⟩ := lieOc_exists_spMap (spMap f ≫ hU.fromSpec ≫ s)
    rw [hP R' β _ (by rw [Category.assoc]; exact hβ)]
    exact hK R' f β hβ)
  exact ⟨Z, i, hi, fun R' _ β x hx => (hZ R' x).trans (hP R' β x hx)⟩

end GlobalTheory.UPel.HT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernIntegralAddOfDensityAddStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedChern_integral_add_of_density_add : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) [SecondCountableTopology (CxPts p σ)] (D : ℕ) (L₁ L₂ L₃ : Fin D → MLine p σ), (∀ c : AlgChart p σ D, ∀ y ∈ c.e.source, dens L₁ c y = dens L₂ c y + dens L₃ c y) → ∀ f : CxPts p σ → ℝ, (Intg L₂ f → Intg L₃ f → Intg L₁ f) ∧ (Intg L₁ f → Intg L₂ f → Intg L₃ f → Mix.int L₁ f = Mix.int L₂ f + Mix.int L₃ f) := by
  first | exact @GlobalTheory.Mix.int_add_of_dens_add | exact GlobalTheory.Mix.int_add_of_dens_add | (intros; apply GlobalTheory.Mix.int_add_of_dens_add <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplierPowerMulPullbackSmallFamilyStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplier_power_mul_pullback_small_family : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G), ∀ b, FormalEnd U.toUnifPre a h' b → ∀ (N k : ℕ) (g : ∀ β, SecT D.toPre a N (-1) β) (ρ : ∀ β, SecT D.toPre a 0 k β), Small (maximalIdeal R) (w := id) g → Small (maximalIdeal R) (w := id) ρ → TFE h h' g → TFE h h' ρ → ∃ F : ∀ β, SecT D.toPre a ((N * k : ℕ) : ℤ) 0 β, Small (maximalIdeal R) (w := id) F ∧ TFE h h' F ∧ ∀ (e : ℕ) (τ : SecE U.toUnifPre (b e) N (-1)) (τ' : SecE U.toUnifPre (b e) 0 k), TExp U.toUnifPre τ (w := id) g → TExp U.toUnifPre τ' (w := id) ρ → ∃ τ'' : SecE U.toUnifPre (b e) ((N * k : ℕ) : ℤ) 0, (∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J'), Good U.LG.L z J' → sval τ'' x z J' = sval τ x z J' ^ k * sval τ' x z J') ∧ TExp U.toUnifPre τ'' (w := id) F := by
  first | exact @GlobalTheory.ZmPow.pow_mul_small | exact GlobalTheory.ZmPow.pow_mul_small | (intros; apply GlobalTheory.ZmPow.pow_mul_small <;> assumption)
end

