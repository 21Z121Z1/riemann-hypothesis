import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0496
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0465
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0369
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0410
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0356
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0388
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0363
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0492
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0454
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0494
import Formalism.PairingDivisors.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0498
import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
import Formalism.LocalToGlobal.Divisibility.ProjLemmas

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SheafCohomologyClassSubsingletonOfAcyclicBoundedStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sheafCohomologyClass_subsingleton_of_acyclic_boundedBelow : ∀ (R : Type) [CommRing R] (G : Shv R) (M : Cx R) (a : ℤ) [M.IsStrictlyGE a], M.Acyclic → (∀ t i : ℤ, 0 < i → Subsingleton (CohomologyClass (sgl G) (res R (M.X t)) i)) → ∀ n : ℤ, Subsingleton (CohomologyClass (sgl G) M n) := by
  first | (exact @GlobalTheory.EtC.subsingleton_cohomologyClass_sgl_of_acyclic) | (exact GlobalTheory.EtC.subsingleton_cohomologyClass_sgl_of_acyclic) | (intros; apply GlobalTheory.EtC.subsingleton_cohomologyClass_sgl_of_acyclic  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimplicialSpectralRowExactZeroOfAcyclic
section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.GmStep

noncomputable section

namespace GlobalTheory.EtC.GmStep.DegRow

variable {R : Type} [CommRing R] (F : Shv R)

theorem cobd_disc (P : PSh) (s : (free R).obj ((disc.obj P).obj (op ⦋0⦌)) ⟶ F) :
    cobd (E := disc.obj P) s = 0 := by
  simp [cobd, Fin.sum_univ_two, SimplicialObject.δ]

theorem exists_rep (E : Spc) (x : H R E F 0) : ∃ s : (free R).obj (E.obj (op ⦋0⦌)) ⟶ F, IsCls s x := by
  obtain ⟨-, hneg, hmono, ⟨w, hex⟩, -, hpos⟩ := GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_basic_properties R F
  obtain ⟨z, rfl⟩ := x.mk_surjective
  let b := (z.1 : Cochain ((chains R).obj E) (res R F) 0).v 0 0 (add_zero 0)
  have hb : b ≫ (res R F).d 0 1 = 0 := by
    have e := Cochain.congr_v (Cocycle.δ_eq_zero z 1) 0 1 (zero_add 1)
    rw [δ_v 0 1 (zero_add 1) _ 0 1 (zero_add 1) 0 1 (by omega) (zero_add 1),
      (hpos E 1 one_pos).eq_of_tgt (((chains R).obj E).d 0 1) 0, zero_comp, smul_zero, add_zero] at e
    exact e
  haveI : Mono (ShortComplex.mk _ _ w).f := hmono
  let t' : ((chains R).obj E).X 0 ⟶ F := hex.lift b hb
  have ht' : t' ≫ resι R F = b := hex.lift_f b hb
  refine ⟨(chainsXIso R E 0).inv ≫ t', z, rfl, ?_⟩
  refine Cochain.ext _ _ (fun p q hpq => ?_)
  by_cases hp : p = 0
  · subst hp
    obtain rfl : q = 0 := by omega
    change b = (Cochain.single (p := -((0 : ℕ) : ℤ)) (q := 0) ((chainsXIso R E 0).hom ≫ ((chainsXIso R E 0).inv ≫ t') ≫ resι R F) ((0 : ℕ) : ℤ)).v (-((0 : ℕ) : ℤ)) 0 (by simp)
    rw [Cochain.single_v, ← ht']
    simp
  · rcases lt_or_gt_of_ne hp with hp | hp
    · exact (hneg q (by omega)).eq_of_tgt _ _
    · exact (hpos E p hp).eq_of_src _ _

def clsFun (P : PSh) (s : (free R).obj P ⟶ F) : H R (disc.obj P) F 0 :=
  Classical.choose ((isCls_basic R F (disc.obj P) 0).1 s (cobd_disc F P s))

theorem clsFun_spec (P : PSh) (s : (free R).obj P ⟶ F) : IsCls (E := disc.obj P) (n := 0) s (clsFun F P s) :=
  Classical.choose_spec ((isCls_basic R F (disc.obj P) 0).1 s (cobd_disc F P s))

theorem clsFun_eq (P : PSh) (s : (free R).obj P ⟶ F) (x : H R (disc.obj P) F 0)
    (h : IsCls (E := disc.obj P) (n := 0) s x) : clsFun F P s = x :=
  (isCls_basic R F (disc.obj P) 0).2.2.1 s _ _ (clsFun_spec F P s) h

def cls0 (P : PSh) : ((free R).obj P ⟶ F) →+ H R (disc.obj P) F 0 :=
  AddMonoidHom.mk' (clsFun F P) fun s s' =>
    clsFun_eq F P (s + s') _ ((isCls_basic R F (disc.obj P) 0).2.1 s s' _ _ (clsFun_spec F P s) (clsFun_spec F P s'))

theorem degreeZeroClassConstantSpaceAddHom_represents (P : PSh) (s : (free R).obj P ⟶ F) : IsCls (E := disc.obj P) (n := 0) s (cls0 F P s) :=
  clsFun_spec F P s

theorem degreeZeroClassConstantSpaceAddHom_eq_of_represents (P : PSh) (s : (free R).obj P ⟶ F) (x : H R (disc.obj P) F 0)
    (h : IsCls (E := disc.obj P) (n := 0) s x) : cls0 F P s = x :=
  clsFun_eq F P s x h

theorem etaleSpaceCohomologyPullback_degreeZeroClass {P P' : PSh} (f : P ⟶ P') (s : (free R).obj P' ⟶ F) :
    pull R (disc.map f) F 0 (cls0 F P' s) = cls0 F P ((free R).map f ≫ s) :=
  (degreeZeroClassConstantSpaceAddHom_eq_of_represents F P _ _ ((isCls_basic R F (disc.obj P') 0).2.2.2.2 (disc.obj P) (disc.map f) s _ (degreeZeroClassConstantSpaceAddHom_represents F P' s))).symm

theorem degreeZeroClassConstantSpaceAddHom_eq_zero_imp (P : PSh) (s : (free R).obj P ⟶ F) (h : cls0 F P s = 0) : s = 0 :=
  (leray_inj R F (disc.obj P) 0 (fun k m hm hkm _ => by omega)).1 s (h ▸ degreeZeroClassConstantSpaceAddHom_represents F P s)

theorem simplicialSpectralRowDifferential_degreeZeroClass (E : Spc) (p : ℕ) (s : (free R).obj (E.obj (op ⦋p⦌)) ⟶ F) :
    rowD R E F 0 p (cls0 F _ s) = cls0 F _ (cobd s) := by
  simp only [rowD, AddMonoidHom.finset_sum_apply, AddMonoidHom.smul_apply, etaleSpaceCohomologyPullback_degreeZeroClass, cobd, map_sum, map_zsmul]

end GlobalTheory.EtC.GmStep.DegRow

open GlobalTheory.EtC.GmStep.DegRow in

theorem GlobalTheory.EtC.GmStep.rowExact_zero_of_acyclic : ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc),
    (∀ (p : ℕ) (s : ℤ), 0 < s → Subsingleton (H R (disc.obj (E.obj (op ⦋p⦌))) F s)) →
    (∀ m : ℤ, 0 < m → Subsingleton (H R E F m)) → ∀ p : ℕ, RowExact R E F 0 p := by
  intro R _ F E hlev htot p y hy
  obtain ⟨s, hs⟩ : ∃ s : (free R).obj (E.obj (op ⦋p + 1⦌)) ⟶ F, IsCls (E := disc.obj (E.obj (op ⦋p + 1⦌))) (n := 0) s y :=
    exists_rep F (disc.obj (E.obj (op ⦋p + 1⦌))) y
  obtain rfl : cls0 F (E.obj (op ⦋p + 1⦌)) s = y := degreeZeroClassConstantSpaceAddHom_eq_of_represents F _ s y hs
  rw [simplicialSpectralRowDifferential_degreeZeroClass] at hy
  have hc : cobd s = 0 := degreeZeroClassConstantSpaceAddHom_eq_zero_imp F _ _ hy
  obtain ⟨x, hx⟩ := (isCls_basic R F E (p + 1)).1 s hc
  have hx0 : x = 0 := @Subsingleton.elim _ (htot _ (by positivity)) x 0
  rw [hx0] at hx
  obtain ⟨t, ht⟩ := (leray_inj R F E p (fun k m hm _ y => @Subsingleton.elim _ (hlev k m (by exact_mod_cast hm)) y 0)).2 s hx
  exact ⟨cls0 F _ t, by rw [simplicialSpectralRowDifferential_degreeZeroClass, ht]⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothFibreRegularLocalRing
section
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.FibreRegular

theorem quot_localization_regular (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Smooth R S] (p : Ideal R) [p.IsPrime] (n : Ideal S) [n.IsPrime]
    (hn : n.comap (algebraMap R S) = p) :
    IsRegularLocalRing (Localization.AtPrime n ⧸
      (p.map (algebraMap R S)).map (algebraMap S (Localization.AtPrime n))) := by
  let P : PrimeSpectrum R := ⟨p, inferInstance⟩
  let N : PrimeSpectrum.comap (algebraMap R S) ⁻¹' {P} := ⟨⟨n, inferInstance⟩, PrimeSpectrum.ext hn⟩
  obtain ⟨q, hq⟩ : ∃ q : PrimeSpectrum (p.Fiber S),
      q.asIdeal.comap (Algebra.TensorProduct.includeRight (R := R) (A := p.ResidueField)) = n :=
    ⟨PrimeSpectrum.preimageEquivFiber R S P N,
      congrArg (fun z => z.1.asIdeal) ((PrimeSpectrum.preimageEquivFiber R S P).symm_apply_apply N)⟩
  subst hq
  have hreg : IsRegularRing (p.Fiber S) := GlobalTheory.isRegularRing_of_smooth p.ResidueField (p.Fiber S)
  have := isRegularRing_iff.mp hreg q.asIdeal
  exact IsRegularLocalRing.of_ringEquiv (Ideal.Fiber.algEquivAux₂ p q.asIdeal).toRingEquiv

end GlobalTheory.FibreRegular

namespace GlobalTheory.FibreRegular

theorem isRegularLocalRing_stalk_quot_maximalIdeal :
    ∀ (X Y : Scheme.{0}) (π : Y ⟶ X) [Smooth π] (y : Y),
      IsRegularLocalRing (Y.presheaf.stalk y ⧸
        (IsLocalRing.maximalIdeal (X.presheaf.stalk (π y))).map (π.stalkMap y).hom) := by
  intro X Y π _ y
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (π y)) isOpen_univ
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, hWle⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (show y ∈ π ⁻¹ᵁ U from hxU) (π ⁻¹ᵁ U).isOpen
  replace hWle : W ≤ π ⁻¹ᵁ U := hWle
  have hs : (π.appLE U W hWle).hom.Smooth :=
    HasRingHomProperty.appLE (P := @Smooth) π inferInstance ⟨U, hU⟩ ⟨W, hW⟩ hWle
  letI := (π.appLE U W hWle).hom.toAlgebra
  haveI : Algebra.Smooth Γ(X, U) Γ(Y, W) := hs
  letI := X.presheaf.algebra_section_stalk (⟨π y, hxU⟩ : U)
  haveI := hU.isLocalization_stalk ⟨π y, hxU⟩
  letI := Y.presheaf.algebra_section_stalk (⟨y, hyW⟩ : W)
  haveI := hW.isLocalization_stalk ⟨y, hyW⟩
  set p := (hU.primeIdealOf ⟨π y, hxU⟩).asIdeal with hp
  set n := (hW.primeIdealOf ⟨y, hyW⟩).asIdeal with hn

  have e : ∀ r : Γ(X, U), (Y.presheaf.germ W y hyW).hom ((π.appLE U W hWle).hom r) =
      (π.stalkMap y).hom ((X.presheaf.germ U (π y) hxU).hom r) := by
    have e' : π.appLE U W hWle ≫ Y.presheaf.germ W y hyW =
        X.presheaf.germ U (π y) hxU ≫ π.stalkMap y := by
      refine Eq.trans ?_ (Scheme.Hom.germ_stalkMap π U y hxU).symm
      rw [Scheme.Hom.appLE, Category.assoc, Y.presheaf.germ_res]
    intro r
    exact congr($(e').hom r)
  have hmemU : ∀ a : Γ(X, U), (X.presheaf.germ U (π y) hxU).hom a ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk (π y)) ↔ a ∈ p := fun a =>
    IsLocalization.AtPrime.to_map_mem_maximal_iff (X.presheaf.stalk (π y)) p a
  have hmemW : ∀ a : Γ(Y, W), (Y.presheaf.germ W y hyW).hom a ∈
      IsLocalRing.maximalIdeal (Y.presheaf.stalk y) ↔ a ∈ n := fun a =>
    IsLocalization.AtPrime.to_map_mem_maximal_iff (Y.presheaf.stalk y) n a
  have hlies : n.comap (algebraMap Γ(X, U) Γ(Y, W)) = p := by
    ext r
    rw [Ideal.mem_comap, ← hmemW, ← hmemU]
    change (Y.presheaf.germ W y hyW).hom ((π.appLE U W hWle).hom r) ∈ _ ↔ _
    rw [e, ← Ideal.mem_comap, IsLocalRing.maximalIdeal_comap]
  have hreg := quot_localization_regular Γ(X, U) Γ(Y, W) p n hlies

  have hI : (IsLocalRing.maximalIdeal (X.presheaf.stalk (π y))).map (π.stalkMap y).hom =
      (p.map (algebraMap Γ(X, U) Γ(Y, W))).map (algebraMap Γ(Y, W) (Y.presheaf.stalk y)) := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p (X.presheaf.stalk (π y)), Ideal.map_map,
      Ideal.map_map]
    congr 1
    ext r
    exact (e r).symm
  let eA := IsLocalization.algEquiv n.primeCompl (Y.presheaf.stalk y) (Localization.AtPrime n)
  let eS : Y.presheaf.stalk y ≃+* Localization.AtPrime n := eA.toRingEquiv
  have hcomp : (eS : Y.presheaf.stalk y →+* Localization.AtPrime n).comp
      (algebraMap Γ(Y, W) (Y.presheaf.stalk y)) = algebraMap Γ(Y, W) (Localization.AtPrime n) :=
    RingHom.ext fun r => eA.commutes r
  have hJ : (p.map (algebraMap Γ(X, U) Γ(Y, W))).map (algebraMap Γ(Y, W) (Localization.AtPrime n)) =
      ((IsLocalRing.maximalIdeal (X.presheaf.stalk (π y))).map (π.stalkMap y).hom).map
        (eS : Y.presheaf.stalk y →+* Localization.AtPrime n) := by
    rw [hI, Ideal.map_map (algebraMap Γ(Y, W) (Y.presheaf.stalk y)), hcomp]
  exact IsRegularLocalRing.of_ringEquiv (Ideal.quotientEquiv _ _ eS hJ).symm

end GlobalTheory.FibreRegular
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialUnitaryKottwitzEquivalence
section
open NumberField
open scoped TensorProduct Matrix

namespace GlobalTheory.SEquivOfRat

open Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol IsDedekindDomain

theorem ratM_det {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (γ : Matrix (Fin r) (Fin r) E) :
    (ratM (maximalRealSubfield E) γ).det = (1 : FiniteAdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)) ⊗ₜ γ.det := by
  have h : ratM (maximalRealSubfield E) γ = (Algebra.TensorProduct.includeRight :
      E →ₐ[maximalRealSubfield E] RA (maximalRealSubfield E) E).toRingHom.mapMatrix γ := rfl
  rw [h, ← RingHom.map_det]; rfl

theorem sequiv_of_rat {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (G : Matrix (Fin r) (Fin r) E)
    (L : Set (Fin r → E)) (s s' M : Matrix (Fin r) (Fin r) (GlobalTheory.AdLat.RA (maximalRealSubfield E) E))
    (γ : Matrix (Fin r) (Fin r) E) (hs : GlobalTheory.SUVol.IsSA G s) (hs' : GlobalTheory.SUVol.IsSA G s')
    (hM : GlobalTheory.UCls.IsKM (IsCMField.complexConj E) G L 1 M)
    (h : s' * M = GlobalTheory.UCls.ratM (maximalRealSubfield E) γ * s) (hγ : γ.det = 1) :
    GlobalTheory.SUVol.SEquiv G L 1 s' s := by
  have hγu : IsUnit γ.det := by rw [hγ]; exact isUnit_one
  have hinv : γ * γ⁻¹ = 1 := Matrix.mul_nonsing_inv γ hγu
  have hinv' : γ⁻¹ * γ = 1 := Matrix.nonsing_inv_mul γ hγu
  have hdγ : (ratM (maximalRealSubfield E) γ).det = 1 := by rw [ratM_det, hγ]; rfl
  have hdγi : (ratM (maximalRealSubfield E) γ⁻¹).det = 1 := by
    have := congrArg Matrix.det (ratM_mul (E := E) γ γ⁻¹)
    rw [hinv, ratM_one, det_one, det_mul, hdγ, one_mul] at this
    exact this.symm
  have hsu : IsUnit s.det := by rw [hs.2]; exact isUnit_one
  have hss : s * s⁻¹ = 1 := Matrix.mul_nonsing_inv s hsu

  have hpres : ∀ x y, hermA (IsCMField.complexConj E) G (ratM (maximalRealSubfield E) γ *ᵥ x) (ratM (maximalRealSubfield E) γ *ᵥ y) =
      hermA (IsCMField.complexConj E) G x y := by
    intro x y
    have ex : ∀ z, ratM (maximalRealSubfield E) γ *ᵥ z = s' *ᵥ (M *ᵥ (s⁻¹ *ᵥ z)) := by
      intro z
      rw [mulVec_mulVec, mulVec_mulVec, h, Matrix.mul_assoc, hss, Matrix.mul_one]
    rw [ex, ex, hs'.1.2, hM.1.2, ← hs.1.2]
    simp only [mulVec_mulVec, hss, one_mulVec]
  refine ⟨γ⁻¹, ⟨⟨by rw [hdγi]; exact isUnit_one, fun x y => ?_⟩, hdγi⟩, M, hM, ?_, ?_⟩
  · rw [← hpres, mulVec_mulVec, mulVec_mulVec, ← ratM_mul, hinv, ratM_one, one_mulVec, one_mulVec]
  · have := congrArg Matrix.det h
    rw [det_mul, det_mul, hs'.2, hs.2, hdγ, one_mul, mul_one] at this
    exact this
  · rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc, ← ratM_mul, hinv', ratM_one, Matrix.one_mul]

end GlobalTheory.SEquivOfRat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitLatticeLevelTraceDenominator
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

theorem exists_int_mul_trace_of_hasLevel {F : Type} [Field F] [NumberField F] {N : ℕ} {𝔞 𝔟 : Frac F} {x : F}
    (h : HasLevel N (split 𝔞 𝔟 x)) {ν c : F} (hν : ν ∈ (𝔞 : FractionalIdeal (𝓞 F)⁰ F))
    (hc : c ∈ (1 : Submodule (𝓞 F) F)) : ∃ n : ℤ, (N : ℚ) * Algebra.trace ℚ F (ν * c) = n := by
  have h1 : (![0, c] : Fin 2 → F) ∈ stdLat F := by
    intro i _
    fin_cases i
    · exact Submodule.zero_mem _
    · exact hc
  have h2 := (h.1 _ h1).2
  have h3 : ((N : 𝓞 F) • (![0, c] : Fin 2 → F)) 1 - ((N : 𝓞 F) • (![0, c] : Fin 2 → F)) 0 * x = (N : F) * c := by
    simp [Algebra.smul_def]
  rw [h3, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM_eq_dual, FractionalIdeal.mem_dual 𝔞.ne_zero] at h2
  obtain ⟨n, hn⟩ := h2 ν hν
  refine ⟨n, ?_⟩
  have h4 : (N : F) * c * ν = (N : ℚ) • (ν * c) := by
    rw [Algebra.smul_def, map_natCast]; ring
  rw [Algebra.traceForm_apply, h4, map_smul, smul_eq_mul] at hn
  simpa using hn.symm

theorem trace_denominator_of_hasLevel : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : ℕ) (𝔞 𝔟 : Frac F) (x ξ : F), HasLevel N (split 𝔞 𝔟 x) → ξ ∈ ((𝔞 * 𝔟 : Frac F) : FractionalIdeal (𝓞 F)⁰ F) → (∃ n : ℤ, (N : ℚ) * Algebra.trace ℚ F ξ = n) ∧ ∃ n : ℤ, (N : ℚ) * Algebra.trace ℚ F (ξ * x) = n := by
  intro F _ _ _ N 𝔞 𝔟 x ξ h hξ
  rw [Units.val_mul] at hξ
  refine FractionalIdeal.mul_induction_on hξ (C := fun ξ ↦ (∃ n : ℤ, (N : ℚ) * Algebra.trace ℚ F ξ = n) ∧
    ∃ n : ℤ, (N : ℚ) * Algebra.trace ℚ F (ξ * x) = n) ?_ ?_
  · intro ν hν β hβ
    have h1 : (![β, β * x] : Fin 2 → F) ∈ split 𝔞 𝔟 x := by
      refine ⟨hβ, ?_⟩
      have : (![β, β * x] : Fin 2 → F) 1 - (![β, β * x] : Fin 2 → F) 0 * x = 0 := by simp
      rw [this]
      exact Submodule.zero_mem (latM 𝔞 : Submodule (𝓞 F) F)
    have h2 := h.2 h1
    refine ⟨exists_int_mul_trace_of_hasLevel h hν (h2 0 trivial), ?_⟩
    rw [mul_assoc]
    exact exists_int_mul_trace_of_hasLevel h hν (h2 1 trivial)
  · rintro a b ⟨⟨m, hm⟩, m', hm'⟩ ⟨⟨n, hn⟩, n', hn'⟩
    refine ⟨⟨m + n, ?_⟩, m' + n', ?_⟩
    · rw [map_add, mul_add, hm, hn]; push_cast; ring
    · rw [add_mul, map_add, mul_add, hm', hn']; push_cast; ring

end GlobalTheory.HilbFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitUnitaryWeilRepresentationIsSmooth
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

theorem isKW_isSmoothRep : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure] (κ : ℂ) (ω : Representation ℂ (UG c (stdJ ν E)) (SB (Matrix α ν E))), IsKW c ψ χ Q μ κ ω → GlobalTheory.SplitWeil.IsSmoothRep ω := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q hQ ψ hψ hψ1 hψne χ hχ hη _ _ μ _ κ ω hKW
  intro v
  let U : Subgroup (UG c (stdJ ν E)) :=
    { carrier := {g | ω g v = v}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul, Module.End.mul_apply, hb, ha]
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have key : ∀ u : SB (Matrix α ν E), ∀ᶠ g in nhds (1 : UG c (stdJ ν E)), g ∈ sieg c ν → ω g u = u := by
    intro u
    filter_upwards [GlobalTheory.T.schwartzBruhat_fixed_near_one_siegelParabolic F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hη (u : Matrix α ν E → ℂ) u.2] with g hg hs
    apply Subtype.ext
    rw [hKW.par g hs u]
    exact hg hs
  have hU : IsOpen (U : Set (UG c (stdJ ν E))) := by
    refine GlobalTheory.T.isOpen_subgroup_of_siegel_and_opposite_nhds F E c δ hE ν U (key v) ?_
    filter_upwards [key (ω (weyl c ν) v)] with g hg hs
    change ω ((weyl c ν)⁻¹ * g * weyl c ν) v = v
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hg hs, ← Module.End.mul_apply, ← map_mul,
      inv_mul_cancel, map_one, Module.End.one_apply]
  exact hU

end GlobalTheory.KSp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitsInCMFieldTwoPrimesDegreeOne
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler

namespace GlobalTheory.CMVal.Euler.SplitPlace

theorem two_primes (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (h2 : Module.finrank F E = 2) (p : Ideal (𝓞 F)) [p.IsMaximal] (P P' : p.primesOver (𝓞 E)) (hne : P ≠ P') :
    (∀ R : p.primesOver (𝓞 E), R = P ∨ R = P') ∧
      ∀ R : p.primesOver (𝓞 E), R.1.ramificationIdx (𝓞 F) * R.1.inertiaDeg (𝓞 F) = 1 := by
  classical
  have hsum := Ideal.sum_ramification_inertia_eq_finrank p (𝓞 E)
  rw [← IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E, h2] at hsum
  have hpos : ∀ P : p.primesOver (𝓞 E),
      1 ≤ P.1.ramificationIdx (𝓞 F) * P.1.inertiaDeg (𝓞 F) := fun P =>
    Nat.mul_pos (Ideal.ramificationIdx_pos _ _) (Ideal.inertiaDeg_pos _ _)
  have hall : ∀ R : p.primesOver (𝓞 E), R = P ∨ R = P' := by
    intro R
    by_contra hR
    push Not at hR
    have h3 := Finset.sum_le_sum_of_subset (f := fun P : p.primesOver (𝓞 E) =>
      P.1.ramificationIdx (𝓞 F) * P.1.inertiaDeg (𝓞 F)) (Finset.subset_univ {R, P, P'})
    rw [hsum, Finset.sum_insert (by simp [hR.1, hR.2]), Finset.sum_pair hne] at h3
    have := hpos R
    have := hpos P
    have := hpos P'
    omega
  refine ⟨hall, fun R => ?_⟩
  have h3 := Finset.sum_le_sum_of_subset (f := fun P : p.primesOver (𝓞 E) =>
    P.1.ramificationIdx (𝓞 F) * P.1.inertiaDeg (𝓞 F)) (Finset.subset_univ {P, P'})
  rw [hsum, Finset.sum_pair hne] at h3
  have := hpos P
  have := hpos P'
  rcases hall R with rfl | rfl <;> omega

theorem split_place : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (v : HeightOneSpectrum (OF E)), Splits v → (∀ P P' : HeightOneSpectrum (𝓞 E), Over P v → Over P' v → P ≠ P' → ∀ R : HeightOneSpectrum (𝓞 E), Over R v → R = P ∨ R = P') ∧ ∀ P : HeightOneSpectrum (𝓞 E), Over P v → Ideal.absNorm P.asIdeal = Ideal.absNorm v.asIdeal ∧ (∀ (a : OF E) (k : ℕ), algebraMap (OF E) (𝓞 E) a ∈ P.asIdeal ^ k ↔ a ∈ v.asIdeal ^ k) ∧ ∀ b : 𝓞 E, ∃ a : OF E, b - algebraMap (OF E) (𝓞 E) a ∈ P.asIdeal := by
  intro E _ _ _ v hv
  have h2 : Module.finrank (maximalRealSubfield E) E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have hmax : v.asIdeal.IsMaximal := v.isMaximal
  have hm : ∀ P : HeightOneSpectrum (𝓞 E), Over P v → P.asIdeal ∈ v.asIdeal.primesOver (𝓞 E) :=
    fun P h => ⟨P.isPrime, ⟨h.symm⟩⟩
  have hne : ∀ P P' (h : Over P v) (h' : Over P' v), P ≠ P' →
      (⟨_, hm P h⟩ : v.asIdeal.primesOver (𝓞 E)) ≠ ⟨_, hm P' h'⟩ :=
    fun P P' h h' hn he => hn (HeightOneSpectrum.ext (congrArg Subtype.val he))
  refine ⟨fun P P' h h' hn R hR => ?_, fun P hP => ?_⟩
  · rcases (two_primes _ E h2 v.asIdeal _ _ (hne P P' h h' hn)).1 ⟨_, hm R hR⟩ with e | e
    · exact Or.inl (HeightOneSpectrum.ext (congrArg Subtype.val e))
    · exact Or.inr (HeightOneSpectrum.ext (congrArg Subtype.val e))
  obtain ⟨Q, Q', hn, h, h'⟩ := hv
  have hef := (two_primes _ E h2 v.asIdeal _ _ (hne Q Q' h h' hn)).2 ⟨_, hm P hP⟩
  have hlo : P.asIdeal.LiesOver v.asIdeal := ⟨hP.symm⟩
  have hPm : P.asIdeal.IsMaximal := P.isMaximal
  have he : v.asIdeal.ramificationIdx' P.asIdeal = 1 := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ v.ne_bot]
    exact Nat.eq_one_of_mul_eq_one_right hef
  have hf : v.asIdeal.inertiaDeg' P.asIdeal = 1 := by
    rw [Ideal.inertiaDeg'_eq_inertiaDeg]
    exact Nat.eq_one_of_mul_eq_one_left hef
  refine ⟨?_, fun a k => ?_, fun b => ?_⟩
  · rw [Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver P.asIdeal v.asIdeal v.isPrime v.ne_bot, hf, pow_one]
  · rw [← HeightOneSpectrum.intValuation_le_pow_iff_mem, ← HeightOneSpectrum.intValuation_le_pow_iff_mem,
      ← HeightOneSpectrum.intValuation_liesOver v P a, he, pow_one]
  · rw [Ideal.inertiaDeg'_algebraMap] at hf
    let _ := Ideal.Quotient.field v.asIdeal
    obtain ⟨c, hc⟩ := (Algebra.finrank_eq_one_iff_bijective_algebraMap.1 hf).2 (Ideal.Quotient.mk _ b)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
    exact ⟨a, Ideal.Quotient.eq.1 hc.symm⟩

end GlobalTheory.CMVal.Euler.SplitPlace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumCoeffChiIdemMul
section
open Formalism.L2.DIV

namespace GlobalTheory.IdemChar

open Classical in

theorem sum_coeff_chiIdem_mul {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]
    {φ χ : G → K} (hφ : IsAbsIrrChar φ) (hχ : IsAbsIrrChar χ) :
    ∑ g : G, (chiIdem φ).coeff g * χ g = if φ = χ then χ 1 else 0 := by
  have hG : (Fintype.card G : K) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero

  have hc := conv_char hχ hφ 1
  have hre : ∑ s : G, χ s⁻¹ * φ (s * 1) = ∑ g : G, φ g⁻¹ * χ g :=
    Fintype.sum_equiv (Equiv.inv G) _ _ (fun s => by simp [mul_comm])
  rw [hre] at hc
  have hsum : ∑ g : G, (chiIdem φ).coeff g * χ g
      = ((∑ g : G, φ g⁻¹ * χ g) * φ 1) / (Fintype.card G : K) := by
    rw [Finset.sum_mul, Finset.sum_div]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [coeff_chiIdem]
    ring
  rw [hsum, hc]
  by_cases h : φ = χ
  · subst h
    rw [if_pos rfl, if_pos rfl, mul_div_cancel_left₀ _ hG]
  · have h' : ¬ χ = φ := fun e => h e.symm
    rw [if_neg h', if_neg h, zero_div]

theorem sum_coeff_idemOf_mul : ∀ (K : Type) [Field K] [CharZero K] (G : Type) [Group G] [Fintype G] (X : Finset (G → K)), (∀ χ ∈ X, IsAbsIrrChar χ) → ∀ χ ∈ X, ∑ g : G, (idemOf X).coeff g * χ g = χ 1 := by
  intro K _ _ G _ _ X hX χ hχ
  classical
  calc ∑ g : G, (idemOf X).coeff g * χ g
      = ∑ g : G, ∑ ψ ∈ X, (chiIdem ψ).coeff g * χ g := by
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [coeff_idemOf, Finset.sum_mul]
        refine Finset.sum_congr rfl fun ψ _ => ?_
        rw [coeff_chiIdem]
    _ = ∑ ψ ∈ X, ∑ g : G, (chiIdem ψ).coeff g * χ g := Finset.sum_comm
    _ = ∑ ψ ∈ X, if ψ = χ then χ 1 else 0 :=
        Finset.sum_congr rfl fun ψ hψ => sum_coeff_chiIdem_mul (hX ψ hψ) (hX χ hχ)
    _ = χ 1 := by simp [hχ]

end GlobalTheory.IdemChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumRealEmbeddingsEqTraceTotallyReal
section
set_option autoImplicit false

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

set_option autoImplicit false in
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in

theorem _root_.GlobalTheory.HilbFam.sum_realEmb_eq_trace : ∀ (F : Type) [Field F] [NumberField F]
    [IsTotallyReal F] (y : F),
    ∑ i : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, ((i y : ℝ) : ℂ) = ((Algebra.trace ℚ F y : ℚ) : ℂ) := by
  intro F _ _ _ y
  have h := trace_eq_sum_embeddings (K := ℚ) (L := F) ℂ (x := y)
  rw [show ((Algebra.trace ℚ F y : ℚ) : ℂ) = algebraMap ℚ ℂ (Algebra.trace ℚ F y) from rfl, h]
  refine Fintype.sum_bijective (fun i : F →+* ℝ ↦ (Complex.ofRealHom.comp i).toRatAlgHom)
    ⟨?_, ?_⟩ _ _ ?_
  · intro i j hij
    ext z
    have := congrArg (fun σ : F →ₐ[ℚ] ℂ ↦ σ z) hij
    simpa using this
  · intro σ
    have hσ := IsTotallyReal.complexEmbedding_isReal (K := F) σ.toRingHom
    refine ⟨ComplexEmbedding.IsReal.embedding hσ, ?_⟩
    ext z
    simp [ComplexEmbedding.IsReal.coe_embedding_apply]
  · intro i
    simp

end GlobalTheory.HilbFam
end

