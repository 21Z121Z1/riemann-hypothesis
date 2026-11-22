import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Bundle0004
import Development.EtaleCohomology.EtaleSheaves.Bundle0005
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsH1MuOfLocallyUnitTimesPower
import Development.EtaleCohomology.KummerTheory.Bundle0016
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ExistsUnitKummerEqOfPicardTorsionFree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0510
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0038
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0372
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0463
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0583

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.BaseChangeCurveFunctionFieldCompOfNormal
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

namespace UpperTheory.PicRigid

private lemma exists_prim (q : ℕ) [NeZero q] (L : Type) [Field L] [IsAlgClosed L] (hq : IsUnit (q : L)) :
    Nonempty (Prim q L) := by
  have hdeg : (Polynomial.cyclotomic q L).degree ≠ 0 := by
    rw [Polynomial.degree_cyclotomic]
    have := Nat.totient_pos.mpr (NeZero.pos q)
    exact_mod_cast this.ne'
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root _ hdeg
  refine ⟨⟨z, hq, ?_⟩⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
  exact hz

private lemma pl_id (q : ℕ) (i : ℤ) {X : Scheme.{0}} (m : ℤ) (y : Ht q (sch.obj X) m i) :
    pl q i (𝟙 X) m y = y := by
  show pull (ZMod q) (sch.map (𝟙 X)) (tw q i) m y = y
  rw [CategoryTheory.Functor.map_id, pull_id]

private lemma main (hA : LateralTheory.KummerTheory.AlgExt) : Hyps → ∀ (q : ℕ) [NeZero q] (k L : Type) [Field k] [IsAlgClosed k] [Field L] [IsAlgClosed L] [Algebra k L], IsUnit (q : k) → ∀ {C : Scheme.{0}} [IsIntegral C] (c : C ⟶ Sp k), IsCurve c → ∀ {X : Scheme.{0}} [IsIntegral X] (u : X ⟶ C) (x : X ⟶ Sp L), IsPullback u x c (Spec.map (CommRingCat.ofHom (algebraMap k L))) → (∀ y : X, IsIntegrallyClosed (X.presheaf.stalk y)) → ∀ φ : C.functionField →+* X.functionField, Spec.map (CommRingCat.ofHom φ) ≫ (C.fromSpecStalk (genericPoint C)) = (X.fromSpecStalk (genericPoint X)) ≫ u → ∀ F : (X.functionField)ˣ, (∀ y : X, ∃ (u : (X.presheaf.stalk y)ˣ) (h : (X.functionField)ˣ), (F : X.functionField) = algebraMap (X.presheaf.stalk y) X.functionField u * (h : X.functionField) ^ q) → ∃ (f : (C.functionField)ˣ) (h : (X.functionField)ˣ), (F : X.functionField) = φ f * (h : X.functionField) ^ q := by
  intro hy q _ k L _ _ _ _ _ hq C _ c hc X _ u x pb hnorm φ hφ F hF
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, e2, e3⟩ := hy
  have hP : IsProper c := hc.2.1
  have hS1 : SmoothOfRelativeDimension 1 c := hc.2.2
  have hS : Smooth c := SmoothOfRelativeDimension.smooth 1 c
  have hqL : IsUnit (q : L) := by simpa using hq.map (algebraMap k L)
  have hxP : IsProper x := MorphismProperty.of_isPullback (P := @IsProper) pb hP
  have hcpt : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace x
  let ρ : L →+* Γ(X, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫ x.appTop).hom
  have hqX : IsUnit (q : Γ(X, ⊤)) := by simpa using hqL.map ρ
  obtain ⟨ζ⟩ := exists_prim q L hqL
  obtain ⟨xx, hxx⟩ := UpperTheory.exists_h1Mu_of_locally_unit_times_power q X ⟨Prim.map ρ ζ⟩ hqX hcpt hnorm F hF
  have E := hA e2 e3 q k L (algebraMap k L) hq c 1
  obtain ⟨x₀, hx₀⟩ := (E 1).2 (pl q 1 pb.isoPullback.inv 1 xx)
  have hu : pl q 1 u 1 x₀ = xx := by
    rw [← pb.isoPullback_hom_fst, pl_comp]
    have h1 : pl q 1 (pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap k L)))) 1 x₀ =
      pl q 1 pb.isoPullback.inv 1 xx := hx₀
    rw [h1, ← pl_comp, Iso.hom_inv_id, pl_id]

  let gC := C.fromSpecStalk (genericPoint C)
  let hk : k →+* C.functionField := (Spec.preimage (gC ≫ c)).hom
  have hqA : IsUnit (q : C.functionField) := by simpa using hq.map hk
  have hqK : IsUnit (q : X.functionField) := by
    simpa using hqA.map φ
  have hqS : IsUnit (q : Γ(Spec C.functionField, ⊤)) := by
    simpa using hqA.map (Scheme.ΓSpecIso C.functionField).inv.hom
  have hqT : IsUnit (q : Γ(Spec X.functionField, ⊤)) := by
    simpa using hqK.map (Scheme.ΓSpecIso X.functionField).inv.hom
  obtain ⟨w, hw⟩ := UpperTheory.Cb.exists_unit_kummer_eq_of_picard_torsionFree q C.functionField hqA (fun c _ => Subsingleton.elim _ _) (pl q 1 gC 1 x₀)
  have K1 := (GlobalTheory.T.kummerClassOfUnit_cocycle_natural_additive q).2.1 (Spec.map (CommRingCat.ofHom φ)) w hqS
  have K2 : kum q (X := Spec X.functionField) (Units.map (Scheme.ΓSpecIso X.functionField).inv.hom.toMonoidHom F) =
      kum q (Units.map (Spec.map (CommRingCat.ofHom φ)).appTop.hom.toMonoidHom w) := by
    rw [← hxx, ← hu, ← pl_comp, ← hφ, pl_comp]
    have h2 : pl q 1 (C.fromSpecStalk (genericPoint C)) 1 x₀ = kum q w := hw.symm
    rw [h2]
    exact K1
  let iX : (X.functionField)ˣ →* (Γ(Spec X.functionField, ⊤))ˣ :=
    Units.map (Scheme.ΓSpecIso X.functionField).inv.hom.toMonoidHom
  let fK : (C.functionField)ˣ := Units.map (Scheme.ΓSpecIso C.functionField).hom.hom.toMonoidHom w
  let φu : (X.functionField)ˣ := Units.map φ.toMonoidHom fK
  have K3 : Units.map (Spec.map (CommRingCat.ofHom φ)).appTop.hom.toMonoidHom w = iX φu := by
    apply Units.ext
    have e : (Scheme.ΓSpecIso C.functionField).inv.hom
        ((Scheme.ΓSpecIso C.functionField).hom.hom (w : Γ(Spec C.functionField, ⊤))) = (w : Γ(Spec C.functionField, ⊤)) :=
      congrArg (fun m => m.hom (w : Γ(Spec C.functionField, ⊤))) (Scheme.ΓSpecIso C.functionField).hom_inv_id
    have h3 : (Scheme.ΓSpecIso X.functionField).inv.hom (φ ((fK : (C.functionField)ˣ) : C.functionField)) =
        (Spec.map (CommRingCat.ofHom φ)).appTop.hom ((Scheme.ΓSpecIso C.functionField).inv.hom
          ((Scheme.ΓSpecIso C.functionField).hom.hom (w : Γ(Spec C.functionField, ⊤)))) :=
      congrArg (fun m => m.hom ((Scheme.ΓSpecIso C.functionField).hom.hom (w : Γ(Spec C.functionField, ⊤))))
        (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
    rw [e] at h3
    exact h3.symm
  have K4 : kum q (iX (F * φu⁻¹)) = 0 := by
    have h4 := ((GlobalTheory.T.kummerClassOfUnit_cocycle_natural_additive q).2.2 (iX (F * φu⁻¹)) (iX φu) hqT).1
    rw [← map_mul, inv_mul_cancel_right] at h4
    have h5 : kum q (iX F) = kum q (iX φu) := K2.trans (by rw [K3])
    rw [h5] at h4
    exact right_eq_add.mp h4
  obtain ⟨v, hv⟩ := UpperTheory.exists_root_of_kummer_class_eq_zero q (Spec X.functionField) (iX (F * φu⁻¹)) hqT K4
  let h : (X.functionField)ˣ := Units.map (Scheme.ΓSpecIso X.functionField).hom.hom.toMonoidHom v
  have hh : h ^ q = F * φu⁻¹ := by
    have e1 : h ^ q = Units.map (Scheme.ΓSpecIso X.functionField).hom.hom.toMonoidHom (v ^ q) := (map_pow _ v q).symm
    rw [e1, hv]
    apply Units.ext
    exact congrArg (fun m => m.hom (((F * φu⁻¹ : (X.functionField)ˣ)) : X.functionField))
      (Scheme.ΓSpecIso X.functionField).inv_hom_id
  refine ⟨fK, h, ?_⟩
  have h6 : F = φu * h ^ q := by rw [hh, mul_comm F, mul_inv_cancel_left]
  have h7 := congrArg Units.val h6
  rw [Units.val_mul, Units.val_pow_eq_pow_val] at h7
  exact h7

end UpperTheory.PicRigid

theorem UpperTheory.baseChange_curve_functionField_comp_of_normal :
    Hyps → ∀ (q : ℕ) [NeZero q] (k L : Type) [Field k] [IsAlgClosed k] [Field L] [IsAlgClosed L] [Algebra k L], IsUnit (q : k) → ∀ {C : Scheme.{0}} [IsIntegral C] (c : C ⟶ Sp k), IsCurve c → ∀ {X : Scheme.{0}} [IsIntegral X] (u : X ⟶ C) (x : X ⟶ Sp L), IsPullback u x c (Spec.map (CommRingCat.ofHom (algebraMap k L))) → (∀ y : X, IsIntegrallyClosed (X.presheaf.stalk y)) → ∀ φ : C.functionField →+* X.functionField, Spec.map (CommRingCat.ofHom φ) ≫ (C.fromSpecStalk (genericPoint C)) = (X.fromSpecStalk (genericPoint X)) ≫ u → ∀ F : (X.functionField)ˣ, (∀ y : X, ∃ (u : (X.presheaf.stalk y)ˣ) (h : (X.functionField)ˣ), (F : X.functionField) = algebraMap (X.presheaf.stalk y) X.functionField u * (h : X.functionField) ^ q) → ∃ (f : (C.functionField)ˣ) (h : (X.functionField)ˣ), (F : X.functionField) = φ f * (h : X.functionField) ^ q :=
  UpperTheory.PicRigid.main LateralTheory.Fin.AlgExt.intersectionNumber_baseChange
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomologyFunctorialityAxiomsHold
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace UpperTheory.Cb.SHAcyc

private theorem map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U)
    (x : Sec F U) : Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) :=
  congrArg (fun h => h.hom x) (φ.hom.naturality g.op)

private theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U)
    (x : Sec F U) : Sec.res (k ≫ g) x = Sec.res k (Sec.res g x) := by
  change (F.obj.map (k ≫ g).op).hom x = _
  rw [op_comp, Functor.map_comp]
  rfl

private theorem res_id {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (x : Sec F U) :
    Sec.res (𝟙 U) x = x := by
  change (F.obj.map (𝟙 U).op).hom x = x
  rw [op_id, CategoryTheory.Functor.map_id]
  rfl

private theorem exists_section (A : Type) [CommRing A] [HenselianLocalRing A]
    [IsSepClosed (IsLocalRing.ResidueField A)] {V : Scheme.{0}} [IsAffine V]
    (g : V ⟶ Spec (CommRingCat.of A)) [Etale g] (v : V)
    (hv : g v = (IsLocalRing.closedPoint A : PrimeSpectrum A)) :
    ∃ σ : Spec (CommRingCat.of A) ⟶ V, σ ≫ g = 𝟙 _ := by
  let φ : CommRingCat.of A ⟶ Γ(V, ⊤) := Spec.preimage (V.isoSpec.inv ≫ g)
  have hφ : Spec.map φ = V.isoSpec.inv ≫ g := Spec.map_preimage _
  have hE : Etale (Spec.map φ) := by rw [hφ]; infer_instance
  letI : Algebra A Γ(V, ⊤) := φ.hom.toAlgebra
  haveI : Algebra.Etale A Γ(V, ⊤) :=
    RingHom.etale_algebraMap.1 ((HasRingHomProperty.Spec_iff (P := @Etale)).1 hE)
  let y : Spec Γ(V, ⊤) := V.isoSpec.hom v
  have hy : Spec.map φ y = (IsLocalRing.closedPoint A : PrimeSpectrum A) := by
    rw [hφ, Scheme.Hom.comp_apply, ← hv]
    congr 1
    change (V.isoSpec.hom ≫ V.isoSpec.inv) v = v
    simp
  have hq : (PrimeSpectrum.asIdeal y).comap (algebraMap A Γ(V, ⊤)) = IsLocalRing.maximalIdeal A :=
    congrArg PrimeSpectrum.asIdeal hy
  haveI : (PrimeSpectrum.asIdeal y).IsPrime := PrimeSpectrum.isPrime y
  obtain ⟨s, -⟩ := (GlobalTheory.StrictHensel.strictlyHenselian_iff A).2 ⟨inferInstance, inferInstance⟩
    Γ(V, ⊤) (PrimeSpectrum.asIdeal y) hq
  refine ⟨Spec.map (CommRingCat.ofHom s.toRingHom) ≫ V.isoSpec.inv, ?_⟩
  rw [Category.assoc, ← hφ, ← Spec.map_comp]
  have : φ ≫ CommRingCat.ofHom s.toRingHom = 𝟙 _ := by
    ext a
    exact s.commutes a
  rw [this, Spec.map_id]

end UpperTheory.Cb.SHAcyc

open UpperTheory.Cb.SHAcyc in

theorem UpperTheory.etaleCohomology_functorialityAxioms_hold : GlobalTheory.EtC.B2 := by
  intro R _ A _ hA F n hn
  obtain ⟨hH, hS⟩ := hA
  haveI := hH
  suffices h : ∀ x : H R (sp A) F n, x = 0 from ⟨fun a b => by rw [h a, h b]⟩
  intro x
  obtain ⟨α, rfl⟩ := x.mk_surjective
  have hz := (GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff R (Spec (CommRingCat.of A)) (res R F) (n - 1) n (n + 1) (by ring) rfl).2 α
  have hloc := (GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness R F (Spec (CommRingCat.of A))).2.2.1 (n - 1) n (n + 1) hn (by ring) _ rfl hz.1
  have hpts := (GlobalTheory.T.etaleLocally_iff_affine_etale_point_cover (Spec (CommRingCat.of A)) _ (by
    rintro V W g k ⟨y, hy⟩
    refine ⟨Sec.res k y, ?_⟩
    rw [map_res, hy, res_comp])).1 hloc
  obtain ⟨V, g, hV, hg, ⟨v, hv⟩, y, hy⟩ := hpts (IsLocalRing.closedPoint A : PrimeSpectrum A)
  obtain ⟨σ, hσ⟩ := exists_section A g v hv
  refine hz.2.2 ⟨Sec.res σ y, ?_⟩
  rw [map_res, hy, ← res_comp, hσ, res_id]
end

