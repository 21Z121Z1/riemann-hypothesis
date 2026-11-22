import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0399
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0481
import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Bundle0001
import Development.EtaleCohomology.EtaleSheaves.Bundle0041
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0008
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0003
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0029
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0024
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0026
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0372
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0373
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0463
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0027
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.CompLeft
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExtFreeEtaleSheafYoneda
import Development.AutomorphicArithmetic.CommutativeAlgebra.BconeDefs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0465
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0015
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0030
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Bundle0004
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Bundle0002
import Development.AutomorphicArithmetic.CommutativeAlgebra.FiniteKummerSelmerOnPrimeStratum
import Development.EtaleCohomology.KummerTheory.Bundle0001
import Development.EtaleCohomology.WeilConjectures.AcycPf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0382

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.CechAugmentationEquivOfSection
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem UpperTheory.cechAugmentation_equiv_of_section :
    ∀ (R : Type) [CommRing R] {Y X : Scheme.{0}} (f : Y ⟶ X) (s : X ⟶ Y), s ≫ f = 𝟙 X → ∀ F : Shv R, Eqv R (cechAug f) F := by
  intro R _ Y X f s hs F
  apply (GlobalTheory.T.etaleCohomologyEquivalence_basic_properties R F).2.2.1
  apply GlobalTheory.T.quasiIso_chains_cechNerve_of_surjective R (yoneda.map f)
  intro U g
  refine ⟨g ≫ s, ?_⟩
  change (g ≫ s) ≫ f = g
  rw [Category.assoc, hs, Category.comp_id]
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.CohomologyPuncturedAffineLine
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry IsLocalRing GlobalTheory.EtC UpperTheory.Et LateralTheory.E.t_E2Cut LateralTheory.E.LineOneCut LateralTheory.E.StandardEtaleChartsMultivariableHensel

private theorem appTop_comp_apply {X Y W : Scheme.{0}} (h : Y ⟶ X) (f : X ⟶ W) (s : Γ(W, ⊤)) :
    h.appTop.hom (f.appTop.hom s) = (h ≫ f).appTop.hom s := by
  rw [Scheme.Hom.comp_appTop]
  rfl

private abbrev st {A : Type} [CommRing A] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of A)) : A →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom

private theorem st_comp {A : Type} [CommRing A] {X Y : Scheme.{0}} (h : Y ⟶ X) (f : X ⟶ Spec (CommRingCat.of A)) (a : A) :
    h.appTop.hom (st f a) = st (h ≫ f) a := by
  exact appTop_comp_apply h f _

private theorem goodRoot_map_ringHom {S S₂ : Type} [CommRing S] [CommRing S₂] (φ : S →+* S₂) {q : ℕ} {ζ : S}
    (h : GoodRoot q ζ) : GoodRoot q (φ ζ) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by rw [← map_pow, h1, map_one], fun a b hab => ?_, fun S' _ ψ x => ?_⟩
  · have := (h2 a b hab).map φ
    simpa only [map_sub, map_pow] using this
  · simpa using h3 S' (ψ.comp φ) x

private theorem notMem_basicOpen_pullback_iff_base_notMem_basicOpen {X Y : Scheme.{0}} (h : Y ⟶ X) (s : Γ(X, ⊤)) (y : Y) :
    y ∉ Y.basicOpen (h.appTop.hom s) ↔ h.base y ∉ X.basicOpen s := by
  rw [← Scheme.preimage_basicOpen_top]
  rfl

private theorem exists_preimage_map_eq_zero_of_mem_mm {A D E F : Type} [CommRing A] [IsLocalRing A] [CommRing D] [Algebra A D]
    [CommRing E] [CommRing F] (B : Subalgebra A D) (φ : E →+* D) (ψ : E →+* F) (σ : A →+* E)
    (hσ : ∀ a, algebraMap A D a = φ (σ a)) (hB : (B : Set D) = Set.range φ)
    (hψ : ∀ a ∈ maximalIdeal A, ψ (σ a) = 0) (y : D) (hy : y ∈ mm B) :
    ∃ y₀, φ y₀ = y ∧ ψ y₀ = 0 := by
  unfold mm at hy
  refine Submodule.smul_induction_on (p := fun y => ∃ y₀, φ y₀ = y ∧ ψ y₀ = 0) hy ?_ ?_
  · intro a ha b hb
    have hb' : b ∈ (B : Set D) := (Subalgebra.mem_toSubmodule B).1 hb
    rw [hB] at hb'
    obtain ⟨b₀, rfl⟩ := hb'
    exact ⟨σ a * b₀, by rw [map_mul, ← hσ, Algebra.smul_def], by rw [map_mul, hψ a ha, zero_mul]⟩
  · rintro x y ⟨x₀, rfl, hx0⟩ ⟨y₀, rfl, hy0⟩
    exact ⟨x₀ + y₀, map_add _ _ _, by rw [map_add, hx0, hy0, add_zero]⟩

private theorem pow_mod_eq_pow_of_pow_eq_one_commutative_algebra {S : Type} [CommRing S] {ζ : S} {q : ℕ} (h : ζ ^ q = 1) (n : ℕ) :
    ζ ^ (n % q) = ζ ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n q, pow_add, pow_mul, h, one_pow, mul_one]

theorem UpperTheory.cohomology_punctured_affine_line : LateralTheory.E.StandardEtaleChartsMultivariableHensel.Heart := by
  unfold LateralTheory.E.StandardEtaleChartsMultivariableHensel.Heart
  intro q A _ _ hSH hq Z U V p hIL hZ ι₁ ι₂ h1 h2 hUa hVa hcov hs g
  obtain ⟨hHens, hsep⟩ := hSH
  letI := hHens
  haveI : NeZero q := ⟨fun h0 => by subst h0; simp at hq⟩
  obtain ⟨ζ, hζ⟩ := UpperTheory.exists_goodRoot_of_henselian_sepClosed_residue A q hq
  by_cases hW : Nonempty ↥(pullback (fibMap p ι₁) (fibMap p ι₂))
  swap
  · refine ⟨0, 0, ?_⟩
    ext x
    exact (hW ⟨x⟩).elim
  haveI := h1
  haveI := h2
  obtain ⟨r, c, hrc, hr1, hr2⟩ := UpperTheory.exists_fiber_pullback_square_of_open_immersions A p ι₁ ι₂
  obtain ⟨hPaff, hP⟩ := UpperTheory.isAffine_isDomain_pullback_standard_opens A p hZ ι₁ ι₂ hs
  haveI := hPaff
  obtain ⟨hWaff, hrsurj, hrker⟩ := UpperTheory.closed_fiber_affine_surjective_ker_maximalIdeal A (pullback.fst ι₁ ι₂ ≫ ι₁ ≫ p) r c hrc
  haveI := hWaff
  obtain ⟨hdom, hinj1, hinj2, T, hTint, hTB, hTC, hB, hC⟩ := hP ⟨r.base hW.some⟩
  obtain ⟨hFUaff, -, hFUker⟩ := UpperTheory.closed_fiber_affine_surjective_ker_maximalIdeal A (ι₁ ≫ p) (pullback.fst (ι₁ ≫ p) (cpt A))
    (pullback.snd _ _) (IsPullback.of_hasPullback _ _)
  obtain ⟨hFVaff, -, hFVker⟩ := UpperTheory.closed_fiber_affine_surjective_ker_maximalIdeal A (ι₂ ≫ p) (pullback.fst (ι₂ ≫ p) (cpt A))
    (pullback.snd _ _) (IsPullback.of_hasPullback _ _)
  haveI := hFUaff
  haveI := hFVaff
  obtain ⟨ζW, hζW⟩ : ∃ z, st (r ≫ pullback.fst ι₁ ι₂ ≫ ι₁ ≫ p) ζ = z := ⟨_, rfl⟩
  have hgW : GoodRoot q ζW := hζW ▸ goodRoot_map_ringHom _ hζ
  have eqU : (pullback.fst (fibMap p ι₁) (fibMap p ι₂)).appTop.hom
      (st (pullback.fst (ι₁ ≫ p) (cpt A) ≫ ι₁ ≫ p) ζ) = ζW := by
    rw [← hζW, st_comp, reassoc_of% hr1]
  have eqV : (pullback.snd (fibMap p ι₁) (fibMap p ι₂)).appTop.hom
      (st (pullback.fst (ι₂ ≫ p) (cpt A) ≫ ι₂ ≫ p) ζ) = ζW := by
    rw [← hζW, st_comp, ← reassoc_of% hr2, pullback.condition_assoc]
  obtain ⟨w, hwq, hw⟩ := (UpperTheory.scheme_roots_of_unity_eq_locallyConstant_powers _ q ζW hgW).1 g
  obtain ⟨w', rfl⟩ := hrsurj w
  letI : Algebra A Γ(pullback ι₁ ι₂, ⊤) := (st (pullback.fst ι₁ ι₂ ≫ ι₁ ≫ p)).toAlgebra
  haveI := hdom
  have toKer : ∀ y, y ∈ mm (⊤ : Subalgebra A Γ(pullback ι₁ ι₂, ⊤)) → r.appTop.hom y = 0 := by
    intro y hy
    unfold mm at hy
    rw [Algebra.top_toSubmodule, Ideal.smul_top_eq_map] at hy
    rw [← RingHom.mem_ker, hrker]
    exact hy
  have hmem : w' ^ q - 1 ∈ mm (⊤ : Subalgebra A Γ(pullback ι₁ ι₂, ⊤)) := by
    have hk : w' ^ q - 1 ∈ RingHom.ker r.appTop.hom := by
      rw [RingHom.mem_ker, map_sub, map_pow, hwq, map_one, sub_self]
    rw [hrker] at hk
    unfold mm
    rw [Algebra.top_toSubmodule, Ideal.smul_top_eq_map]
    exact hk
  obtain ⟨u, hu, v, hv, huq, hvq, hwuv⟩ := UpperTheory.exists_near_root_of_unity_product_decomposition A Γ(pullback ι₁ ι₂, ⊤) T hTint hTB hTC q hq w' hmem
  have hu' : u ∈ (T.B : Set _) := hu
  rw [hB] at hu'
  obtain ⟨u₀, rfl⟩ := hu'
  have hv' : v ∈ (T.C : Set _) := hv
  rw [hC] at hv'
  obtain ⟨v₀, rfl⟩ := hv'
  obtain ⟨e₁, he₁, he₁0⟩ := exists_preimage_map_eq_zero_of_mem_mm T.B (pullback.fst ι₁ ι₂).appTop.hom
    (pullback.fst (ι₁ ≫ p) (cpt A)).appTop.hom (st (ι₁ ≫ p)) (fun a => (st_comp _ _ a).symm) hB
    (fun a ha => by rw [← RingHom.mem_ker, hFUker]; exact Ideal.mem_map_of_mem _ ha) _ huq
  have hcomp2 : ∀ a, algebraMap A Γ(pullback ι₁ ι₂, ⊤) a = (pullback.snd ι₁ ι₂).appTop.hom (st (ι₂ ≫ p) a) := by
    intro a
    rw [st_comp]
    show st (pullback.fst ι₁ ι₂ ≫ ι₁ ≫ p) a = _
    rw [pullback.condition_assoc]
  obtain ⟨e₂, he₂, he₂0⟩ := exists_preimage_map_eq_zero_of_mem_mm T.C (pullback.snd ι₁ ι₂).appTop.hom
    (pullback.fst (ι₂ ≫ p) (cpt A)).appTop.hom (st (ι₂ ≫ p)) hcomp2 hC
    (fun a ha => by rw [← RingHom.mem_ker, hFVker]; exact Ideal.mem_map_of_mem _ ha) _ hvq
  have hu1 : ((pullback.fst (ι₁ ≫ p) (cpt A)).appTop.hom u₀) ^ q = 1 := by
    have : e₁ = u₀ ^ q - 1 := hinj1 (by rw [he₁, map_sub, map_pow, map_one])
    rw [this, map_sub, map_pow, map_one, sub_eq_zero] at he₁0
    exact he₁0
  have hv1 : ((pullback.fst (ι₂ ≫ p) (cpt A)).appTop.hom v₀) ^ q = 1 := by
    have : e₂ = v₀ ^ q - 1 := hinj2 (by rw [he₂, map_sub, map_pow, map_one])
    rw [this, map_sub, map_pow, map_one, sub_eq_zero] at he₂0
    exact he₂0
  obtain ⟨a', ha'⟩ := (UpperTheory.scheme_roots_of_unity_eq_locallyConstant_powers _ q _ (goodRoot_map_ringHom (st (pullback.fst (ι₁ ≫ p) (cpt A) ≫ ι₁ ≫ p)) hζ)).2.1 _ hu1
  obtain ⟨b', hb'⟩ := (UpperTheory.scheme_roots_of_unity_eq_locallyConstant_powers _ q _ (goodRoot_map_ringHom (st (pullback.fst (ι₂ ≫ p) (cpt A) ≫ ι₂ ≫ p)) hζ)).2.1 _ hv1
  refine ⟨a', -b', ?_⟩
  ext x
  have key : g x = a' ((pullback.fst (fibMap p ι₁) (fibMap p ι₂)).base x)
      + b' ((pullback.snd (fibMap p ι₁) (fibMap p ι₂)).base x) := by
    obtain ⟨Px, hPx⟩ := (UpperTheory.scheme_roots_of_unity_eq_locallyConstant_powers _ q ζW hgW).2.2.2 x
    have hx1 : Ideal.Quotient.mk Px (r.appTop.hom w') = Ideal.Quotient.mk Px (ζW ^ (g x).val) :=
      Ideal.Quotient.eq.2 ((hPx _).2 (hw x))
    have hx2 : r.appTop.hom w' = (pullback.fst (fibMap p ι₁) (fibMap p ι₂)).appTop.hom
        ((pullback.fst (ι₁ ≫ p) (cpt A)).appTop.hom u₀) *
        (pullback.snd (fibMap p ι₁) (fibMap p ι₂)).appTop.hom
        ((pullback.fst (ι₂ ≫ p) (cpt A)).appTop.hom v₀) := by
      have h0 := toKer _ hwuv
      rw [map_sub, sub_eq_zero, map_mul] at h0
      rw [h0]
      simp only [appTop_comp_apply, hr1, hr2]
    have hx3 : Ideal.Quotient.mk Px ((pullback.fst (fibMap p ι₁) (fibMap p ι₂)).appTop.hom
        ((pullback.fst (ι₁ ≫ p) (cpt A)).appTop.hom u₀)) =
        Ideal.Quotient.mk Px (ζW ^ (a' ((pullback.fst (fibMap p ι₁) (fibMap p ι₂)).base x)).val) := by
      refine Ideal.Quotient.eq.2 ((hPx _).2 ?_)
      rw [← eqU, ← map_pow, ← map_sub, notMem_basicOpen_pullback_iff_base_notMem_basicOpen]
      exact ha' _
    have hx4 : Ideal.Quotient.mk Px ((pullback.snd (fibMap p ι₁) (fibMap p ι₂)).appTop.hom
        ((pullback.fst (ι₂ ≫ p) (cpt A)).appTop.hom v₀)) =
        Ideal.Quotient.mk Px (ζW ^ (b' ((pullback.snd (fibMap p ι₁) (fibMap p ι₂)).base x)).val) := by
      refine Ideal.Quotient.eq.2 ((hPx _).2 ?_)
      rw [← eqV, ← map_pow, ← map_sub, notMem_basicOpen_pullback_iff_base_notMem_basicOpen]
      exact hb' _
    have hfin : Ideal.Quotient.mk Px (ζW ^ (g x).val) = Ideal.Quotient.mk Px (ζW ^ (a' ((pullback.fst (fibMap p ι₁) (fibMap p ι₂)).base x)
        + b' ((pullback.snd (fibMap p ι₁) (fibMap p ι₂)).base x)).val) := by
      rw [← hx1, hx2, map_mul, hx3, hx4, ← map_mul, ← pow_add, ZMod.val_add, pow_mod_eq_pow_of_pow_eq_one_commutative_algebra hgW.1]
    exact (UpperTheory.scheme_roots_of_unity_eq_locallyConstant_powers _ q ζW hgW).2.2.1 _ _ x ((hPx _).1 (Ideal.Quotient.eq.1 hfin))
  simp only [LocallyConstant.sub_apply, LocallyConstant.neg_apply, LocallyConstant.coe_comap,
    Function.comp_apply, key, sub_neg_eq_add]

end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.EqOfUnitGlobalSectionEq
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace UpperTheory.GmInj
open Polynomial

private noncomputable def evalT {A : Type} [CommRing A] (a : A) : ℤ[X] →+* A :=
  Polynomial.eval₂RingHom (Int.castRingHom A) a

private noncomputable abbrev Line : Scheme.{0} := Spec (CommRingCat.of ℤ[X])

private noncomputable def toLine {V : Scheme.{0}} (a : Γ(V, ⊤)) : V ⟶ Line :=
  V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (evalT a))

private noncomputable def coord {V : Scheme.{0}} (f : V ⟶ Line) : Γ(V, ⊤) :=
  f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℤ[X])).inv.hom X)

private lemma line_sheaf : Presieve.IsSheaf Scheme.etaleTopology (yoneda.obj Line) :=
  Presieve.isSheaf_of_le _ Scheme.etaleTopology_le_proetaleTopology
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)

end UpperTheory.GmInj

private theorem gmInj_coord_toLine {V : Scheme.{0}} (a : Γ(V, ⊤)) :
    UpperTheory.GmInj.coord (UpperTheory.GmInj.toLine a) = a := by
  unfold UpperTheory.GmInj.coord UpperTheory.GmInj.toLine
  rw [Scheme.Hom.comp_appTop]
  simp [UpperTheory.GmInj.evalT]

private theorem comp_gmInj_toLine {V W : Scheme.{0}} (f : W ⟶ V) (a : Γ(V, ⊤)) :
    f ≫ UpperTheory.GmInj.toLine a = UpperTheory.GmInj.toLine (f.appTop.hom a) := by
  unfold UpperTheory.GmInj.toLine
  rw [← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc, ← Spec.map_comp]
  congr 2
  ext1
  apply Polynomial.ringHom_ext
  · intro n
    simp [UpperTheory.GmInj.evalT]
  · simp [UpperTheory.GmInj.evalT]

theorem UpperTheory.eq_of_unitGlobalSection_eq :
    ∀ (U : Scheme.{0}) (u v : (Γ(U, ⊤))ˣ), unitSec u = unitSec v → u = v := by
  intro U u v h
  have hS := Presheaf.equalizerSieve_mem Scheme.etaleTopology
    (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)) (X := op U)
    (ULift.up (Additive.ofMul u)) (ULift.up (Additive.ofMul v)) h
  have key : UpperTheory.GmInj.toLine (u : Γ(U, ⊤)) = UpperTheory.GmInj.toLine (v : Γ(U, ⊤)) := by
    refine (UpperTheory.GmInj.line_sheaf _ hS).isSeparatedFor
      (fun W f _ => f ≫ UpperTheory.GmInj.toLine (u : Γ(U, ⊤)))
      _ _ (fun W f hf => rfl) (fun W f hf => ?_)
    show f ≫ UpperTheory.GmInj.toLine _ = f ≫ UpperTheory.GmInj.toLine _
    rw [comp_gmInj_toLine, comp_gmInj_toLine]
    have h2 := congrArg (fun z : ULift (Additive (Scheme.Γ.obj (op W))ˣ) =>
      ((Additive.toMul z.down : (Scheme.Γ.obj (op W))ˣ) : Scheme.Γ.obj (op W))) hf
    have h3 : f.appTop.hom (u : Γ(U, ⊤)) = f.appTop.hom v := h2
    rw [h3]
  have h4 := congrArg UpperTheory.GmInj.coord key
  rw [gmInj_coord_toLine, gmInj_coord_toLine] at h4
  exact Units.ext h4
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsCohomologyClassToDerivedHomBijectiveOfKInj
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex
open LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafGhostCut UpperTheory.Et.Loc

theorem UpperTheory.exists_cohomologyClass_to_derivedHom_bijective_of_kInjective :
    ∀ (q : ℕ) (B : Scheme.{0}) (I : Cx (ZMod q)), ∃ l : ∀ (C : B.Etale ⥤ Cx (ZMod q)) (h : ∀ n, Presheaf.IsSheaf (EtTop B) (TP C I n)) (U : B.Etale) (n : ℤ), CohomologyClass (C.obj U) I n → ((OU B q).obj U ⟶ (CategoryTheory.shiftFunctor _ n).obj (DerivedCategory.Q.obj (TC C I h))), (∀ C h, (TC C I h).IsKInjective → ∀ U n, Function.Bijective (l C h U n)) ∧ (∀ C h (U U' : B.Etale) (a : U' ⟶ U) n x, l C h U' n (cpre (Cocycle.ofHom (C.map a)) I n n (zero_add n) x) = (OU B q).map a ≫ l C h U n x) ∧ ∀ (C C' : B.Etale ⥤ Cx (ZMod q)) h h' (φ : C' ⟶ C) U n x, l C' h' U n (cpre (Cocycle.ofHom (φ.app U)) I n n (zero_add n) x) = l C h U n x ≫ (CategoryTheory.shiftFunctor _ n).map (DerivedCategory.Q.map (TM φ I h h')) := by
  intro q B I
  obtain ⟨y, hwd, hK, hU, hT⟩ := UpperTheory.ext_free_etale_sheaf_yoneda B q
  have cz : ∀ (C : B.Etale ⥤ Cx (ZMod q)) (h : ∀ n, Presheaf.IsSheaf (EtTop B) (TP C I n)) (U : B.Etale) (n : ℤ)
      (z : Cocycle (C.obj U) I n), dS (TC C I h) n (n + 1) U (z : Cochain (C.obj U) I n) = 0 :=
    fun C h U n z => Cocycle.δ_eq_zero z (n + 1)
  have wd : ∀ (C : B.Etale ⥤ Cx (ZMod q)) (h : ∀ n, Presheaf.IsSheaf (EtTop B) (TP C I n)) (U : B.Etale) (n : ℤ)
      (z z' : Cocycle (C.obj U) I n), CohomologyClass.mk z = CohomologyClass.mk z' →
      y (TC C I h) U n (z : Cochain (C.obj U) I n) (cz C h U n z) =
        y (TC C I h) U n (z' : Cochain (C.obj U) I n) (cz C h U n z') := by
    intro C h U n z z' hzz
    apply hwd
    have h0 : CohomologyClass.mk (z - z') = 0 := by
      rw [CohomologyClass.mk_sub, hzz, sub_self]
    rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)] at h0
    obtain ⟨β, hβ⟩ := h0
    exact ⟨β, hβ⟩
  have lmk : ∀ (C : B.Etale ⥤ Cx (ZMod q)) (h : ∀ n, Presheaf.IsSheaf (EtTop B) (TP C I n)) (U : B.Etale) (n : ℤ)
      (z : Cocycle (C.obj U) I n),
      y (TC C I h) U n ((CohomologyClass.mk_surjective (CohomologyClass.mk z)).choose : Cochain (C.obj U) I n)
        (cz C h U n _) = y (TC C I h) U n (z : Cochain (C.obj U) I n) (cz C h U n z) :=
    fun C h U n z => wd C h U n _ _ (CohomologyClass.mk_surjective _).choose_spec
  refine ⟨fun C h U n x => y (TC C I h) U n ((CohomologyClass.mk_surjective x).choose : Cochain (C.obj U) I n)
    (cz C h U n _), ?_, ?_, ?_⟩
  · intro C h hKI U n
    constructor
    · intro x x' hxx
      obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective x
      obtain ⟨z', rfl⟩ := CohomologyClass.mk_surjective x'
      dsimp only at hxx
      rw [lmk, lmk] at hxx
      obtain ⟨b, hb⟩ := (hK (TC C I h) hKI U n).1 _ _ _ _ hxx
      rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
        mem_coboundaries_iff _ (n - 1) (by omega)]
      exact ⟨b, hb⟩
    · intro x
      obtain ⟨s, hs, hsx⟩ := (hK (TC C I h) hKI U n).2 x
      refine ⟨CohomologyClass.mk (Cocycle.mk s (n + 1) rfl hs), ?_⟩
      dsimp only
      rw [lmk]
      exact hsx
  · intro C h U U' a n x
    obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective x
    dsimp only
    rw [cpre_mk, lmk, lmk]
    exact hU (TC C I h) U U' a n (z : Cochain (C.obj U) I n) (cz C h U n z) _
  · intro C C' h h' φ U n x
    obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective x
    dsimp only
    rw [cpre_mk, lmk, lmk]
    exact hT (TC C I h) (TC C' I h') (TM φ I h h') U n (z : Cochain (C.obj U) I n) (cz C h U n z) _
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsLiftFreeToKernelOfShortExactVanishingSecti
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Bc

theorem UpperTheory.exists_lift_free_to_kernel_of_shortExact_vanishing_sections :
    ∀ (Q : Scheme.{0} → Prop) (S : ShortComplex (Shv ℤ)), S.ShortExact → (∀ U : Scheme.{0}, Q U → Subsingleton (Sec S.X₃ U)) → ∀ P : PSh, Supp Q P → ∀ f : (free ℤ).obj P ⟶ S.X₂, ∃ h : (free ℤ).obj P ⟶ S.X₁, h ≫ S.f = f := by
  intro Q S hS hQ P hP f
  have hsub := UpperTheory.subsingleton_hypercohomology_free_of_supp_of_sections_vanish Q S.X₃ hQ P hP 0
  have hz : f ≫ S.g = 0 := by
    apply (UpperTheory.bijective_cl_hypercohomology_singleton_zero _ _).1
    exact Subsingleton.elim _ _
  haveI := hS.mono_f
  exact ⟨hS.exact.lift f hz, hS.exact.lift_f f hz⟩
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsLiftFreeToMiddleOfShortExactAcy
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Bc

theorem UpperTheory.exists_lift_free_to_middle_of_shortExact_acy :
    ∀ (Q : Scheme.{0} → Prop) (S : ShortComplex (Shv ℤ)), S.ShortExact → Acy Q S.X₁ → ∀ P : PSh, Supp Q P → ∀ f : (free ℤ).obj P ⟶ S.X₃, ∃ h : (free ℤ).obj P ⟶ S.X₂, h ≫ S.g = f := by
  intro Q S hS hA P hP f
  obtain ⟨z, hz⟩ := GlobalTheory.T.etaleCohomology_coefficient_longExactSequence ℤ S hS
  have e := (hz (sgl ((free ℤ).obj P)) 0).2.1
  have hsub := hA P hP (0 + 1) (by norm_num)
  have h0 : HK.ext ℤ (sgl ((free ℤ).obj P)) z 0 (0 + 1) rfl (cl f) = 0 := Subsingleton.elim _ _
  obtain ⟨y, hy⟩ := (e (cl f)).1 h0
  obtain ⟨h, rfl⟩ := (UpperTheory.bijective_cl_hypercohomology_singleton_zero _ _).2 y
  refine ⟨h, (UpperTheory.bijective_cl_hypercohomology_singleton_zero _ _).1 ?_⟩
  rw [← UpperTheory.hypercohomology_post_cl_eq_cl_comp]
  exact hy
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.FiniteKummerSelmerOfCharts
section
open GroundTheory.FunctionField UpperTheory.Et.Sel
open scoped TensorProduct

theorem UpperTheory.finite_kummerSelmer_of_charts :
    ∀ (k K : Type) [Field k] [IsAlgClosed k] [Field K] [Algebra k K] [IsFunctionField k K] (q : ℕ) [NeZero q], Charts k K q → FinCls q (SelAll k K q) := by
  intro k K _ _ _ _ _ q _ hC
  obtain ⟨n, v, hv⟩ := UpperTheory.exists_finite_span_kummerSelmer_representatives k K q
  let P : Set (Fin n → k) → Prop := fun s =>
    FinCls q {f | f ∈ SelAll k K q ∧ ∃ c, (f : K) = ∑ i, c i • v i ∧ c ∈ s}
  have hall : P Set.univ := by
    apply UpperTheory.Et.noethSp k n P
    · refine ⟨∅, ?_⟩
      rintro f ⟨_, c, _, hc⟩
      exact absurd hc (by simp)
    · intro s t hst ⟨T, hT⟩
      refine ⟨T, ?_⟩
      rintro f ⟨hf, c, hfc, hc⟩
      exact hT f ⟨hf, c, hfc, hst hc⟩
    · intro s t ⟨T₁, h₁⟩ ⟨T₂, h₂⟩
      classical
      refine ⟨T₁ ∪ T₂, ?_⟩
      rintro f ⟨hf, c, hfc, hc | hc⟩
      · obtain ⟨x, hx, u, hu⟩ := h₁ f ⟨hf, c, hfc, hc⟩
        exact ⟨x, Finset.mem_union_left _ hx, u, hu⟩
      · obtain ⟨x, hx, u, hu⟩ := h₂ f ⟨hf, c, hfc, hc⟩
        exact ⟨x, Finset.mem_union_right _ hx, u, hu⟩
    · intro I hI
      obtain ⟨g, hg, T, hT⟩ := UpperTheory.finite_kummerSelmer_on_prime_stratum k K q hC n v I hI
      refine ⟨g, hg, T, ?_⟩
      rintro f ⟨hf, c, hfc, hc₁, hc₂⟩
      exact hT f ⟨hf, c, hfc, hc₁, hc₂⟩
  obtain ⟨T, hT⟩ := hall
  refine ⟨T, ?_⟩
  intro f hf
  obtain ⟨g, hg, ⟨c, hgc⟩, u, hfu⟩ := hv f hf
  obtain ⟨t, ht, w, hw⟩ := hT g ⟨hg, c, hgc, Set.mem_univ c⟩
  refine ⟨t, ht, w * u, ?_⟩
  rw [hfu, hw, mul_pow, mul_assoc]
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.HomAcyclicFreePullbackYonedaOfInjectiveRestricti
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex
open LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafGhostCut UpperTheory.Et.Loc

private lemma res_val {R : Type} [CommRing R] {X : Scheme.{0}} {J : Shv R} (φ : (free R).obj (yoneda.obj X) ⟶ J)
    {V : Scheme.{0}} (x : V ⟶ X) :
    Sec.map φ (freeGen R (yoneda.obj X) V x) = Sec.res x (Sec.map φ (freeGen R (yoneda.obj X) X (𝟙 X))) := by
  have h3 := (GlobalTheory.T.free_sections_ext_res_map R (yoneda.obj X) J).2.2.1 V X x (𝟙 X)
  have nat : Sec.res x (Sec.map φ (freeGen R (yoneda.obj X) X (𝟙 X))) =
      Sec.map φ (Sec.res x (freeGen R (yoneda.obj X) X (𝟙 X))) := by
    simp only [Sec.res, Sec.map]
    exact (congrArg (fun f => ModuleCat.Hom.hom f (freeGen R (yoneda.obj X) X (𝟙 X)))
      (φ.hom.naturality x.op)).symm
  rw [nat, h3]
  simp

private noncomputable def evE (R : Type) [CommRing R] (X : Scheme.{0}) (J : Shv R) :
    ((free R).obj (yoneda.obj X) ⟶ J) ≃ₗ[ULift.{1} R] Sec J X :=
  LinearEquiv.ofBijective
    { toFun := fun φ => Sec.map φ (freeGen R (yoneda.obj X) X (𝟙 X))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    ⟨by
      intro φ ψ h
      refine (GlobalTheory.T.free_sections_ext_res_map R (yoneda.obj X) J).2.1 φ ψ fun U x => ?_
      rw [res_val φ x, res_val ψ x]
      exact congrArg (Sec.res x) h,
     by
      intro s
      obtain ⟨φ, hφ⟩ := (GlobalTheory.T.free_sections_ext_res_map R (yoneda.obj X) J).1 (fun U x => Sec.res x s) (by
        intro V U g x
        simp [Sec.res])
      refine ⟨φ, ?_⟩
      refine (hφ X (𝟙 X)).trans ?_
      simp [Sec.res]⟩

private lemma pullbackSymmetry_lift_map_comm {A A' Y B : Scheme.{0}} (p : Y ⟶ B) (u : A ⟶ B) (u' : A' ⟶ B) (l : A' ⟶ A) (hl : l ≫ u = u') :
    pullback.lift (pullback.fst u' p ≫ l) (pullback.snd u' p)
        (by rw [Category.assoc, hl, pullback.condition]) ≫ (pullbackSymmetry p u).inv =
      (pullbackSymmetry p u').inv ≫ pullback.map p u' p u (𝟙 Y) l (𝟙 B) (by simp) (by simp [hl]) := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackSymmetry_inv_comp_fst, pullback.lift_snd, Category.assoc, pullback.lift_fst]
    simp
  · rw [Category.assoc, pullbackSymmetry_inv_comp_snd, pullback.lift_fst, Category.assoc, pullback.lift_snd]
    simp

private lemma sym_nat {B Y : Scheme.{0}} (p : Y ⟶ B) {U U' : B.Etale} (a : U' ⟶ U) :
    (LateralTheory.KummerTheory.tot p).map ((LateralTheory.EWeil.AcycPf.incl B).map a) ≫ (pullbackSymmetry p U.hom).inv =
      (pullbackSymmetry p U'.hom).inv ≫ resY p a := by
  have w : a.left ≫ U.hom = U'.hom := Over.w ((LateralTheory.EWeil.AcycPf.incl B).map a)
  exact pullbackSymmetry_lift_map_comm p U.hom U'.hom a.left w

private lemma res_res {R : Type} [CommRing R] {F : Shv R} {U V W : Scheme.{0}} (f : V ⟶ U) (g : W ⟶ V) (s : Sec F U) :
    Sec.res g (Sec.res f s) = Sec.res (g ≫ f) s := by
  simp [Sec.res]

private lemma ev_pre {R : Type} [CommRing R] {X X' : Scheme.{0}} {J : Shv R} (f : X' ⟶ X)
    (φ : (free R).obj (yoneda.obj X) ⟶ J) :
    Sec.map ((free R).map (yoneda.map f) ≫ φ) (freeGen R (yoneda.obj X') X' (𝟙 X')) =
      Sec.res f (Sec.map φ (freeGen R (yoneda.obj X) X (𝟙 X))) := by
  have h4 := (GlobalTheory.T.free_sections_ext_res_map R (yoneda.obj X') J).2.2.2 (yoneda.obj X) (yoneda.map f) X' (𝟙 X')
  have hc : Sec.map ((free R).map (yoneda.map f) ≫ φ) (freeGen R (yoneda.obj X') X' (𝟙 X')) =
      Sec.map φ (Sec.map ((free R).map (yoneda.map f)) (freeGen R (yoneda.obj X') X' (𝟙 X'))) := rfl
  rw [hc, h4, ← res_val φ f]
  congr 2

private noncomputable def isoHP (q : ℕ) {B Y : Scheme.{0}} (p : Y ⟶ B) (J : Shv (ZMod q)) :
    HP (gY p ⋙ yoneda ⋙ free (ZMod q)) J ≅ (LateralTheory.EWeil.AcycPf.incl B).op ⋙ (LateralTheory.KummerTheory.tot p).op ⋙ J.obj :=
  NatIso.ofComponents (fun U => LinearEquiv.toModuleIso
      ((evE (ZMod q) (YU p U.unop) J).trans
        (J.obj.mapIso (pullbackSymmetry p U.unop.hom).symm.op).toLinearEquiv)) (by
    rintro ⟨U⟩ ⟨U'⟩ ⟨a⟩
    refine ModuleCat.hom_ext (LinearMap.ext fun φ => ?_)
    have h := ev_pre (R := ZMod q) (J := J) (resY p a) φ
    change Sec.res (pullbackSymmetry p U'.hom).inv (Sec.map ((free (ZMod q)).map (yoneda.map (resY p a)) ≫ φ)
        (freeGen (ZMod q) (yoneda.obj (YU p U')) (YU p U') (𝟙 _))) =
      Sec.res ((LateralTheory.KummerTheory.tot p).map ((LateralTheory.EWeil.AcycPf.incl B).map a))
        (Sec.res (pullbackSymmetry p U.hom).inv (Sec.map φ (freeGen (ZMod q) (yoneda.obj (YU p U)) (YU p U) (𝟙 _))))
    rw [h]
    refine (res_res _ _ _).trans (Eq.trans ?_ (res_res _ _ _).symm)
    exact congrArg (fun t => Sec.res (F := J) t _) (sym_nat p a).symm)

theorem UpperTheory.homAcyclic_free_pullback_yoneda_of_injective_restriction :
    LateralTheory.KummerTheory.InjSlice → LateralTheory.EWeil.AcycPf.RestrInj → ∀ (q : ℕ) {B Y : Scheme.{0}} (p : Y ⟶ B), Good (gY p ⋙ yoneda ⋙ free (ZMod q)) := by
  intro hI hR q B Y p J hJ
  obtain ⟨h1, i1⟩ := (hI (ZMod q) J p).1
  obtain ⟨h2, i2⟩ := hR (ZMod q) B ⟨(LateralTheory.KummerTheory.tot p).op ⋙ J.obj, h1⟩
  have e := isoHP q p J
  refine ⟨(Presheaf.isSheaf_of_iso_iff e).2 h2, ?_⟩
  exact Injective.of_iso ((sheafToPresheaf _ _).preimageIso (X := ⟨_, h2⟩) e.symm) i2
end

