import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0373
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0382
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0372
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendScalarsUliftHomAdditive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0339
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsSpecProdBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0367
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0336
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0356
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0388

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPrimitiveRootAndRootsOfUnityStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity : ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), (IsUnit (q : Γ(U, ⊤)) → Loc U fun V _ => Nonempty (Prim q Γ(V, ⊤))) ∧ (∀ ζ ξ : Prim q Γ(U, ⊤), Loc U fun _ g => ∃ a : (ZMod q)ˣ, g.appTop.hom ξ.1 = g.appTop.hom ζ.1 ^ (a : ZMod q).val) ∧ (∀ (ζ : Prim q Γ(U, ⊤)) (x : Γ(U, ⊤)), x ^ q = 1 → Loc U fun _ g => ∃ a : ℕ, g.appTop.hom x = g.appTop.hom ζ.1 ^ a) ∧ (IsUnit (q : Γ(U, ⊤)) → ∀ u : (Γ(U, ⊤))ˣ, Loc U fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom u) := by
  first | (exact @GlobalTheory.EtC.PrimLoc.prim_loc) | (exact GlobalTheory.EtC.PrimLoc.prim_loc) | (intros; apply GlobalTheory.EtC.PrimLoc.prim_loc  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleMayerVietorisFreeRightEpi
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC.MVEpi

theorem exists_prime_over (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A)
    (hs : ∀ a' : A', ∃ a : A, a' - algebraMap A A' a ∈ Ideal.span {algebraMap A A' f})
    (hi : ∀ a : A, algebraMap A A' a ∈ Ideal.span {algebraMap A A' f} → a ∈ Ideal.span {f})
    (p : PrimeSpectrum A) (hp : f ∈ p.asIdeal) :
    ∃ q : PrimeSpectrum A', PrimeSpectrum.comap (algebraMap A A') q = p := by
  set I : Ideal A := Ideal.span {f} with hI
  set J : Ideal A' := Ideal.span {algebraMap A A' f} with hJ
  have hIJ : I ≤ J.comap (algebraMap A A') := by
    rw [hI, Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.subset_span rfl
  let φ : A ⧸ I →+* A' ⧸ J := Ideal.quotientMap J (algebraMap A A') hIJ
  have hφ : Function.Bijective φ := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro a ha
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem] at ha
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (hi a ha)
    · intro b
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
      obtain ⟨a, ha⟩ := hs b
      refine ⟨Ideal.Quotient.mk I a, ?_⟩
      rw [Ideal.quotientMap_mk, Ideal.Quotient.eq]
      have := J.neg_mem ha
      simpa using this
  let e : A ⧸ I ≃+* A' ⧸ J := RingEquiv.ofBijective φ hφ
  have hIp : I ≤ p.asIdeal := by
    rw [hI, Ideal.span_le, Set.singleton_subset_iff]
    exact hp
  let p0 : Ideal (A ⧸ I) := p.asIdeal.map (Ideal.Quotient.mk I)
  have hp0 : p0.IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hIp)
  let q : Ideal A' := (p0.comap (e.symm : A' ⧸ J →+* A ⧸ I)).comap (Ideal.Quotient.mk J)
  have hq : q.IsPrime := Ideal.comap_isPrime _ _
  refine ⟨⟨q, hq⟩, ?_⟩
  ext a
  have he : e.symm (Ideal.Quotient.mk J (algebraMap A A' a)) = Ideal.Quotient.mk I a := by
    rw [RingEquiv.symm_apply_eq]
    rfl
  change Ideal.Quotient.mk J (algebraMap A A' a) ∈ p0.comap (e.symm : A' ⧸ J →+* A ⧸ I) ↔ a ∈ p.asIdeal
  rw [Ideal.mem_comap]
  change e.symm (Ideal.Quotient.mk J (algebraMap A A' a)) ∈ p0 ↔ _
  rw [he]
  exact Ideal.mem_quotient_iff_mem hIp

theorem loc_point {X B : Scheme.{0}} (e : B ⟶ X) [Etale e] {T : Scheme.{0}} (x : T ⟶ X) (t : T)
    (ht : x t ∈ Set.range e) :
    ∃ (V : Scheme.{0}) (g : V ⟶ T), IsAffine V ∧ Etale g ∧ t ∈ Set.range g ∧ ∃ y : V ⟶ B, y ≫ e = g ≫ x := by
  obtain ⟨b, hb⟩ := ht
  obtain ⟨z, hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := x) (g := e) t b hb.symm
  obtain ⟨W0, hW, hzW, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (pullback x e).isBasis_affineOpens)
    (show z ∈ (⊤ : (pullback x e).Opens) from trivial)
  let W : (pullback x e).Opens := W0
  haveI : IsAffine W := hW
  refine ⟨W, W.ι ≫ pullback.fst x e, inferInstance, inferInstance, ⟨⟨z, hzW⟩, ?_⟩, W.ι ≫ pullback.snd x e, ?_⟩
  · exact hz1
  · simp [pullback.condition]

theorem epi_of_loc (R : Type) [CommRing R] {P Q E : PSh} (f : P ⟶ E) (g : Q ⟶ E)
    (h : ∀ (T : Scheme.{0}) (x : E.obj (op T)),
      Loc T fun (V : Scheme.{0}) (k : V ⟶ T) => (∃ y, f.app (op V) y = E.map k.op x) ∨ (∃ y, g.app (op V) y = E.map k.op x)) :
    Epi (biprod.desc ((free R).map f) ((free R).map g)) := by
  refine ⟨fun {F} φ ψ hφψ => ?_⟩
  have ef : (free R).map f ≫ φ = (free R).map f ≫ ψ := by
    simpa using congrArg (biprod.inl ≫ ·) hφψ
  have eg : (free R).map g ≫ φ = (free R).map g ≫ ψ := by
    simpa using congrArg (biprod.inr ≫ ·) hφψ
  have res_map : ∀ {G H : Shv R} (χ : G ⟶ H) {V U : Scheme.{0}} (k : V ⟶ U) (s : Sec G U),
      Sec.res k (Sec.map χ s) = Sec.map χ (Sec.res k s) := by
    intro G H χ V U k s
    exact (NatTrans.naturality_apply χ.hom k.op s).symm
  have map_comp : ∀ {G H K : Shv R} (χ : G ⟶ H) (ω : H ⟶ K) {U : Scheme.{0}} (s : Sec G U),
      Sec.map (χ ≫ ω) s = Sec.map ω (Sec.map χ s) := by
    intros; rfl
  obtain ⟨-, hext, hres, -⟩ := GlobalTheory.T.free_sections_ext_res_map R E F
  obtain ⟨-, -, -, hmapP⟩ := GlobalTheory.T.free_sections_ext_res_map R P F
  obtain ⟨-, -, -, hmapQ⟩ := GlobalTheory.T.free_sections_ext_res_map R Q F
  apply hext
  intro T x
  apply (GlobalTheory.T.etaleSheafSections_ext_and_glue R F T).1
  obtain ⟨S, hS, hP⟩ := h T x
  refine ⟨S, hS, fun V k hk => ?_⟩
  rcases hP V k hk with ⟨y, hy⟩ | ⟨y, hy⟩
  · rw [res_map, res_map, hres, ← hy, ← hmapP, ← map_comp, ← map_comp, ef]
  · rw [res_map, res_map, hres, ← hy, ← hmapQ, ← map_comp, ← map_comp, eg]

end GlobalTheory.EtC.MVEpi

namespace GlobalTheory.EtC.MVEpi

theorem mv_right_epi : ∀ (R : Type) [CommRing R] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A']
    [Algebra.Etale A A'] (f : A), (∀ a' : A', ∃ a : A, a' - algebraMap A A' a ∈ Ideal.span {algebraMap A A' f}) →
    (∀ a : A, algebraMap A A' a ∈ Ideal.span {algebraMap A A' f} → a ∈ Ideal.span {f}) →
    Epi (biprod.desc ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f))))))
      ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A A')))))) := by
  intro R _ A A' _ _ _ _ f hs hi
  haveI hd : Etale (Spec.map (CommRingCat.ofHom (algebraMap A A'))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr inferInstance)
  apply epi_of_loc
  intro T (x : T ⟶ Spec (CommRingCat.of A))
  rw [GlobalTheory.T.etaleLocally_iff_affine_etale_point_cover]
  · intro t
    by_cases hf : f ∈ (x t).asIdeal
    · obtain ⟨q, hq⟩ := exists_prime_over A A' f hs hi (x t) hf
      obtain ⟨V, g, hV, hg, ht, y, hy⟩ :=
        loc_point (Spec.map (CommRingCat.ofHom (algebraMap A A'))) x t ⟨q, hq⟩
      exact ⟨V, g, hV, hg, ht, Or.inr ⟨y, hy⟩⟩
    · have hr : x t ∈ Set.range (PrimeSpectrum.comap (algebraMap A (Localization.Away f))) := by
        rw [PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]
        exact hf
      obtain ⟨q, hq⟩ := hr
      obtain ⟨V, g, hV, hg, ht, y, hy⟩ :=
        loc_point (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f)))) x t ⟨q, hq⟩
      exact ⟨V, g, hV, hg, ht, Or.inl ⟨y, hy⟩⟩
  · rintro V W g k (⟨y, hy⟩ | ⟨y, hy⟩)
    · refine Or.inl ⟨k ≫ y, ?_⟩
      change (k ≫ y) ≫ _ = (k ≫ g) ≫ x
      change y ≫ _ = g ≫ x at hy
      rw [Category.assoc, hy, Category.assoc]
    · refine Or.inr ⟨k ≫ y, ?_⟩
      change (k ≫ y) ≫ _ = (k ≫ g) ≫ x
      change y ≫ _ = g ≫ x at hy
      rw [Category.assoc, hy, Category.assoc]

end GlobalTheory.EtC.MVEpi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleModuleSheafSectionsCoprodBijective
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem sec_res_comp' {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (f : W ⟶ V) (g : V ⟶ U) (x : Sec F U) :
    Sec.res (f ≫ g) x = Sec.res f (Sec.res g x) := by
  simp [Sec.res, op_comp, Functor.map_comp]

theorem sec_res_id' {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (x : Sec F U) :
    Sec.res (𝟙 U) x = x := by
  simp [Sec.res]

theorem sec_coprod : ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}) (ι : Type) (V : ι → Scheme.{0}) (j : ∀ i, V i ⟶ U), IsColimit (Cofan.mk U j) → Function.Bijective (fun (x : Sec F U) (i : ι) => Sec.res (j i) x) := by
  intro R _ F U ι V j hU
  let e : ∐ V ≅ U := (coproductIsCoproduct V).coconePointUniqueUpToIso hU
  have he : ∀ i, Sigma.ι V i ≫ e.hom = j i := fun i =>
    (coproductIsCoproduct V).comp_coconePointUniqueUpToIso_hom hU ⟨i⟩
  have hb := GlobalTheory.T.sec_sigma_res_bijective R F V
  have hiso : Function.Bijective (fun x : Sec F U => Sec.res e.hom x) := by
    refine Function.bijective_iff_has_inverse.2 ⟨fun y => Sec.res e.inv y, fun x => ?_, fun y => ?_⟩
    · simp only
      rw [← sec_res_comp', e.inv_hom_id, sec_res_id']
    · simp only
      rw [← sec_res_comp', e.hom_inv_id, sec_res_id']
  have hfun : (fun (x : Sec F U) (i : ι) => Sec.res (j i) x) =
      (fun (a : Sec F (∐ V)) (i : ι) => Sec.res (Sigma.ι V i) a) ∘ (fun x : Sec F U => Sec.res e.hom x) := by
    funext x i
    simp only [Function.comp_apply]
    rw [← sec_res_comp', he i]
  rw [hfun]
  exact hb.comp hiso

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafDescendAlongLocallyBijectiveStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleSheaf_descend_along_locallyBijective : ∀ (S : Type) [CommRing S] (P Q : Scheme.{0}ᵒᵖ ⥤ AddCommGrpCat.{1}) (φ : P ⟶ Q), (∀ (U : Scheme.{0}) (y : Q.obj (op U)), Loc U fun V g => ∃ x, (φ.app (op V)).hom x = (Q.map g.op).hom y) → (∀ (U : Scheme.{0}) (x : P.obj (op U)), (φ.app (op U)).hom x = 0 → Loc U fun _ g => (P.map g.op).hom x = 0) → ∀ (M : Shv S) (b : ∀ U : Scheme.{0}, P.obj (op U) →+ Sec M U), (∀ (V U : Scheme.{0}) (g : V ⟶ U) x, Sec.res g (b U x) = b V ((P.map g.op).hom x)) → ∃ c : ∀ U : Scheme.{0}, Q.obj (op U) →+ Sec M U, (∀ (V U : Scheme.{0}) (g : V ⟶ U) y, Sec.res g (c U y) = c V ((Q.map g.op).hom y)) ∧ ∀ U x, c U ((φ.app (op U)).hom x) = b U x := by
  first | (exact @GlobalTheory.EtC.desc_loc) | (exact GlobalTheory.EtC.desc_loc) | (intros; apply GlobalTheory.EtC.desc_loc  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafExtendScalarsZmodKernelLocallyMultiple
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

open ChangeOfRings in

theorem unit_eq_zero_dvd {Q q : ℕ} [NeZero Q] (hq : q ∣ Q) (N : ModuleCat.{1} (ULift.{1} (ZMod Q))) (y : N)
    (h : ((ModuleCat.extendRestrictScalarsAdj.{1, 1, 1} (uliftHom (ZMod.castHom hq (ZMod q)))).unit.app N).hom y = 0) :
    ∃ z : N, y = q • z := by
  change (1 : ULift.{1} (ZMod q)) ⊗ₜ[ULift.{1} (ZMod Q), uliftHom (ZMod.castHom hq (ZMod q))] y = 0 at h
  let K : AddSubgroup N := (DistribMulAction.toAddMonoidHom N q).range
  let gZ : ℤ →+ (N →+ N ⧸ K) := zmultiplesHom _ (QuotientAddGroup.mk' K)
  have hgZ : gZ q = 0 := by
    ext m
    simp only [gZ, zmultiplesHom_apply, AddMonoidHom.zero_apply, AddMonoidHom.coe_smul, Pi.smul_apply,
      QuotientAddGroup.mk'_apply]
    rw [natCast_zsmul, ← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
    exact ⟨m, rfl⟩
  let g : ZMod q →+ (N →+ N ⧸ K) := ZMod.lift q ⟨gZ, hgZ⟩
  let f : ((ModuleCat.restrictScalars (uliftHom (ZMod.castHom hq (ZMod q)))).obj (ModuleCat.of _ (ULift.{1} (ZMod q))))
      →+ (N →+ N ⧸ K) := g.comp (AddEquiv.ulift : ULift.{1} (ZMod q) ≃+ ZMod q).toAddMonoidHom
  have hf : ∀ (r : ULift.{1} (ZMod Q)) s (n : N), f (r • s) n = f s (r • n) := by
    intro r s n
    obtain ⟨a, ha⟩ := ZMod.intCast_surjective (ULift.down r)
    obtain ⟨b, hb⟩ := ZMod.intCast_surjective (ULift.down (s : ULift.{1} (ZMod q)))
    have hr : r • n = a • n := by
      rw [show r = ((a : ℤ) : ULift.{1} (ZMod Q)) from ULift.ext _ _ (by simp [ha]), Int.cast_smul_eq_zsmul]
    change g (ZMod.castHom hq (ZMod q) (ULift.down r) * ULift.down (s : ULift.{1} (ZMod q))) n =
      g (ULift.down (s : ULift.{1} (ZMod q))) (r • n)
    rw [hr, ← ha, ← hb, map_intCast, ← Int.cast_mul, ZMod.lift_coe, ZMod.lift_coe]
    simp only [gZ, zmultiplesHom_apply, AddMonoidHom.coe_smul, Pi.smul_apply, QuotientAddGroup.mk'_apply,
      map_zsmul, mul_comm a b, mul_zsmul]
    exact smul_comm b a _
  let one : ((ModuleCat.restrictScalars (uliftHom (ZMod.castHom hq (ZMod q)))).obj (ModuleCat.of _ (ULift.{1} (ZMod q)))) :=
    (1 : ULift.{1} (ZMod q))
  have e : f one y = 0 :=
    (TensorProduct.liftAddHom_tmul f hf one y).symm.trans ((congrArg (TensorProduct.liftAddHom f hf) h).trans (map_zero _))
  have e1 : f one = QuotientAddGroup.mk' K := by
    change g ((1 : ZMod q)) = _
    rw [← Int.cast_one, ZMod.lift_coe]
    simp [gZ]
  rw [e1, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff] at e
  obtain ⟨z, hz⟩ := e
  exact ⟨z, hz.symm⟩

theorem extSh_sec_eq_zero_loc : ∀ (Q q : ℕ) [NeZero Q] (hq : q ∣ Q) (M : Shv (ZMod Q)) (U : Scheme.{0}) (x : Sec M U),
    extSh.sec (ZMod.castHom hq (ZMod q)) M U x = 0 → Loc U fun V g => ∃ y : Sec M V, Sec.res g x = q • y := by
  intro Q q _ hq M U x hx
  have hloc := (GlobalTheory.T.etaleToSheafify_locally_bijective_and_lift (ZMod q) (M.obj ⋙ ModuleCat.extendScalars.{1, 1, 1} (uliftHom (ZMod.castHom hq (ZMod q))))).2.1 U
    (((ModuleCat.extendRestrictScalarsAdj.{1, 1, 1} (uliftHom (ZMod.castHom hq (ZMod q)))).unit.app (M.obj.obj (op U))).hom x) hx
  refine GlobalTheory.T.etaleLocal_property_calculus_rules.2.1 U _ _ hloc ?_
  intro V g hg
  have e2 := (ModuleCat.extendRestrictScalarsAdj.{1, 1, 1} (uliftHom (ZMod.castHom hq (ZMod q)))).unit.naturality (M.obj.map g.op)
  have h2 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom e2) x
  exact unit_eq_zero_dvd hq (M.obj.obj (op V)) (Sec.res g x) (h2.trans hg)

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafExtendScalarsZmodSectionLocallyTmul
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped ChangeOfRings

namespace GlobalTheory.EtC.ExtOnto

theorem unit_surjective {R S : Type 1} [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Surjective f)
    (N : ModuleCat.{1} R) (z : (ModuleCat.extendScalars.{1,1,1} f).obj N) :
    ∃ m : N, ((ModuleCat.extendRestrictScalarsAdj.{1, 1, 1} f).unit.app N).hom m = z := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by rw [map_zero]; rfl⟩
  | tmul s m =>
    obtain ⟨r, rfl⟩ := hf s
    refine ⟨r • m, ?_⟩
    erw [ModuleCat.ExtendRestrictScalarsAdj.unit_app, map_smul, ModuleCat.restrictScalars.smul_def]
    exact (ModuleCat.ExtendScalars.smul_tmul (M := N) f (f r) 1 m).trans
      (congrArg (fun t : S => t ⊗ₜ[R,f] m) (mul_one _))
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx; obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add, ha, hb]; rfl⟩

theorem uliftHom_surjective {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (hφ : Function.Surjective φ) :
    Function.Surjective (uliftHom φ) := by
  intro s
  obtain ⟨r, hr⟩ := hφ s.down
  exact ⟨⟨r⟩, ULift.ext _ _ hr⟩

theorem ext_onto : ∀ (Q q : ℕ) [NeZero Q] (hq : q ∣ Q) (M : Shv (ZMod Q)) (U : Scheme.{0})
    (y : Sec ((extSh (ZMod.castHom hq (ZMod q))).obj M) U),
    Loc U fun V g => ∃ x : Sec M V, extSh.sec (ZMod.castHom hq (ZMod q)) M V x = Sec.res g y := by
  intro Q q _ hq M U y
  have hs := uliftHom_surjective (ZMod.castHom hq (ZMod q)) (ZMod.ringHom_surjective _)
  have h1 := (GlobalTheory.T.etaleToSheafify_locally_bijective_and_lift (ZMod q)
    (M.obj ⋙ ModuleCat.extendScalars.{1, 1, 1} (uliftHom (ZMod.castHom hq (ZMod q))))).1 U y
  refine GlobalTheory.EtC.loc_calculus.2.1 _ _ _ h1 ?_
  rintro V g ⟨z, hz⟩
  obtain ⟨m, hm⟩ := unit_surjective _ hs (M.obj.obj (op V)) z
  refine ⟨m, ?_⟩
  subst hm
  exact hz

end GlobalTheory.EtC.ExtOnto
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsSpecProdBijectiveStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleSheafSections_specProd_bijective : ∀ (R : Type) [CommRing R] (A B : Type) [CommRing A] [CommRing B] (F : Shv R), Function.Bijective fun s : Sec F (Spec (CommRingCat.of (A × B))) => (Sec.res (Spec.map (CommRingCat.ofHom (RingHom.fst A B))) s, Sec.res (Spec.map (CommRingCat.ofHom (RingHom.snd A B))) s) := by
  first | exact @GlobalTheory.EtC.sec_prod | exact GlobalTheory.EtC.sec_prod | (intros; apply GlobalTheory.EtC.sec_prod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafShortComplexExactIffLocally
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem exactIff_loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hPQ : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun V g hg => hPQ V g (hP V g hg)⟩

theorem exactIff_map_comp {R : Type} [CommRing R] {F G K : Shv R} (φ : F ⟶ G) (ψ : G ⟶ K) {U : Scheme.{0}}
    (x : Sec F U) : Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

theorem exactIff_map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U)
    (x : Sec F U) : Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) := by
  have := congrArg (fun m => m.hom x) (φ.hom.naturality g.op)
  simpa using this

theorem exactIff_kernel_sec {R : Type} [CommRing R] {G K : Shv R} (ψ : G ⟶ K) {U : Scheme.{0}}
    (b : Sec G U) (hb : Sec.map ψ b = 0) : ∃ k : Sec (kernel ψ) U, Sec.map (kernel.ι ψ) k = b := by
  let Φ : Shv R ⥤ ModuleCat.{1} (ULift.{1} R) :=
    sheafToPresheaf Scheme.etaleTopology _ ⋙ (evaluation _ _).obj (op U)
  let T : ShortComplex (Shv R) := ShortComplex.mk (kernel.ι ψ) ψ (kernel.condition ψ)
  have hT : T.Exact := ShortComplex.exact_of_f_is_kernel T (kernelIsKernel ψ)
  have hTm : Mono T.f := inferInstanceAs (Mono (kernel.ι ψ))
  have hP : PreservesLimit (parallelPair T.g 0) Φ := inferInstanceAs (PreservesLimit (parallelPair ψ 0) Φ)
  have h2 := (ShortComplex.moduleCat_exact_iff _).1 (hT.map_of_mono_of_preservesKernel Φ hTm hP) b hb
  obtain ⟨k, hk⟩ := h2
  exact ⟨k, hk⟩

theorem exactIff : ∀ (R : Type) [CommRing R] (S : ShortComplex (Shv R)), S.Exact ↔ ∀ U (b : Sec S.X₂ U), Sec.map S.g b = 0 → Loc U fun V g => ∃ a : Sec S.X₁ V, Sec.map S.f a = Sec.res g b := by
  intro R _ S
  have hME : ∀ {F G : Shv R} (φ : F ⟶ G), _ := fun {F G} φ => GlobalTheory.T.bigEtaleModuleSheaf_mono_epi_iff_sections R φ
  rw [ShortComplex.exact_iff_epi_kernel_lift, (hME (kernel.lift S.g S.f S.zero)).2.2.1]
  have hinj : ∀ U, Function.Injective (Sec.map (kernel.ι S.g) (U := U)) :=
    ((hME (kernel.ι S.g)).1).1 inferInstance
  have hfac : ∀ {V : Scheme.{0}} (a : Sec S.X₁ V),
      Sec.map (kernel.ι S.g) (Sec.map (kernel.lift S.g S.f S.zero) a) = Sec.map S.f a := fun a => by
    rw [← exactIff_map_comp, kernel.lift_ι]
  constructor
  · intro h U b hb
    obtain ⟨k, rfl⟩ := exactIff_kernel_sec S.g b hb
    refine exactIff_loc_mono (h U k) fun V g ⟨a, ha⟩ => ⟨a, ?_⟩
    rw [← hfac, ha, exactIff_map_res]
  · intro h U k
    have hk : Sec.map S.g (Sec.map (kernel.ι S.g) k) = 0 := by
      rw [← exactIff_map_comp, kernel.condition]; rfl
    refine exactIff_loc_mono (h U _ hk) fun V g ⟨a, ha⟩ => ⟨a, hinj V ?_⟩
    rw [hfac, ha, exactIff_map_res]

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceCohomologyLevelwiseCoproductBijective
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.HCofan

theorem comm_el {C D : AbCx} (φ : C ⟶ D) (i j : ℤ) (x : C.X i) : φ.f j (C.d i j x) = D.d i j (φ.f i x) := by
  have := ConcreteCategory.congr_hom (φ.comm i j) x
  simp only [ConcreteCategory.comp_apply] at this
  exact this.symm

theorem cochains_bij (R : Type) [CommRing R] (F : Shv R) (E : Spc) (ι : Type) (Q : ι → Spc) (a : ∀ i, Q i ⟶ E)
    (hc : ∀ k : SimplexCategoryᵒᵖ, Nonempty (IsColimit (Cofan.mk ((free R).obj (E.obj k)) (fun i => (free R).map ((a i).app k)))))
    (n : ℤ) : Function.Bijective (fun (x : ((HC R F).obj (op E)).X n) (i : ι) => ((HC R F).map (a i).op).f n x) := by
  obtain ⟨π, hπ⟩ := GlobalTheory.T.bijective_HC_component_eval_of_maps R F n
  have nat : ∀ (k : ℕ) (i : ι) (x : ((HC R F).obj (op E)).X n),
      (π k).app (op (Q i)) (((HC R F).map (a i).op).f n x) =
        (free R).map ((a i).app (op (SimplexCategory.mk k))) ≫ (π k).app (op E) x := by
    intro k i x
    have := ConcreteCategory.congr_hom ((π k).naturality (a i).op) x
    exact this
  let hk := fun k : ℕ => (hc (op (SimplexCategory.mk k))).some
  constructor
  · intro x y hxy
    apply (hπ (op E)).1
    funext k
    apply Cofan.IsColimit.hom_ext (hk k)
    intro i
    have h : ((HC R F).map (a i).op).f n x = ((HC R F).map (a i).op).f n y := congrFun hxy i
    change (free R).map ((a i).app (op (SimplexCategory.mk k))) ≫ (π k).app (op E) x =
      (free R).map ((a i).app (op (SimplexCategory.mk k))) ≫ (π k).app (op E) y
    rw [← nat, ← nat, h]
  · intro y
    obtain ⟨x, hx⟩ := (hπ (op E)).2 (fun k => Cofan.IsColimit.desc (hk k) (fun i => (π k).app (op (Q i)) (y i)))
    refine ⟨x, funext fun i => ?_⟩
    apply (hπ (op (Q i))).1
    funext k
    have e : (π k).app (op E) x = Cofan.IsColimit.desc (hk k) (fun i => (π k).app (op (Q i)) (y i)) := congrFun hx k
    show (π k).app (op (Q i)) (((HC R F).map (a i).op).f n x) = (π k).app (op (Q i)) (y i)
    rw [nat, e]
    exact Cofan.IsColimit.fac (hk k) _ i

end GlobalTheory.EtC.HCofan

theorem GlobalTheory.EtC.HCofan.main : ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc) (ι : Type) (Q : ι → Spc) (a : ∀ i, Q i ⟶ E), (∀ k : SimplexCategoryᵒᵖ, Nonempty (IsColimit (Cofan.mk ((free R).obj (E.obj k)) (fun i => (free R).map ((a i).app k))))) → ∀ n : ℤ, Function.Bijective (fun (x : H R E F n) (i : ι) => pull R (a i) F n x) := by
  intro R _ F E ι Q a hc n
  obtain ⟨-, cl, hsurj, heq, -, hpull⟩ := GlobalTheory.EtC.HCElements.main R F
  have hb := fun m => GlobalTheory.EtC.HCofan.cochains_bij R F E ι Q a hc m
  constructor
  · intro x x' hxx
    obtain ⟨z, hz, rfl⟩ := hsurj E n x
    obtain ⟨z', hz', rfl⟩ := hsurj E n x'
    rw [heq]
    have hi : ∀ i, ∃ y, ((HC R F).map (a i).op).f n z =
        ((HC R F).map (a i).op).f n z' + ((HC R F).obj (op (Q i))).d (n - 1) n y := by
      intro i
      have h : pull R (a i) F n (cl E n z hz) = pull R (a i) F n (cl E n z' hz') := congrFun hxx i
      obtain ⟨h1, e1⟩ := hpull (Q i) E (a i) n z hz
      obtain ⟨h2, e2⟩ := hpull (Q i) E (a i) n z' hz'
      rw [e1, e2] at h
      exact (heq _ _ _ h1 _ h2).1 h
    choose y hy using hi
    obtain ⟨w, hw⟩ := (hb (n - 1)).2 y
    have hw' : ∀ i, ((HC R F).map (a i).op).f (n - 1) w = y i := fun i => congrFun hw i
    refine ⟨w, (hb n).1 (funext fun i => ?_)⟩
    show ((HC R F).map (a i).op).f n z = ((HC R F).map (a i).op).f n (z' + ((HC R F).obj (op E)).d (n - 1) n w)
    rw [map_add, GlobalTheory.EtC.HCofan.comm_el, hw' i]
    exact hy i
  · intro x
    choose z hz hzx using fun i => hsurj (Q i) n (x i)
    obtain ⟨w, hw⟩ := (hb n).2 z
    have hw' : ∀ i, ((HC R F).map (a i).op).f n w = z i := fun i => congrFun hw i
    have hdw : ((HC R F).obj (op E)).d n (n + 1) w = 0 := by
      apply (hb (n + 1)).1
      funext i
      show ((HC R F).map (a i).op).f (n + 1) (((HC R F).obj (op E)).d n (n + 1) w) = ((HC R F).map (a i).op).f (n + 1) 0
      rw [GlobalTheory.EtC.HCofan.comm_el, hw' i, hz i, map_zero]
    refine ⟨cl E n w hdw, funext fun i => ?_⟩
    obtain ⟨h1, e1⟩ := hpull (Q i) E (a i) n w hdw
    show pull R (a i) F n (cl E n w hdw) = x i
    rw [e1, ← hzx i]
    exact (heq _ _ _ h1 _ (hz i)).2 ⟨0, by rw [hw' i, map_zero, add_zero]⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechNerveDiagonalIsoZeroOverBase
section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

namespace GlobalTheory.EtC.GmStep

noncomputable def cechDiagApp {Y X : Scheme.{0}} (f : Y ⟶ X) (k : ℕ) :
    yoneda.obj Y ⟶ widePullback (yoneda.obj X) (fun _ : Fin (k + 1) => yoneda.obj Y) (fun _ => yoneda.map f) :=
  WidePullback.lift (yoneda.map f) (fun _ => 𝟙 _) (by intro; exact Category.id_comp _)

@[reassoc (attr := simp)]
theorem cechDiagApp_π {Y X : Scheme.{0}} (f : Y ⟶ X) (k : ℕ) (j : Fin (k + 1)) :
    cechDiagApp f k ≫ WidePullback.π _ j = 𝟙 _ := WidePullback.lift_π _ _ _ _ _

@[reassoc (attr := simp)]
theorem cechDiagApp_base {Y X : Scheme.{0}} (f : Y ⟶ X) (k : ℕ) :
    cechDiagApp f k ≫ WidePullback.base _ = yoneda.map f := WidePullback.lift_base _ _ _ _

noncomputable def cechDiag {Y X : Scheme.{0}} (f : Y ⟶ X) : sch.obj Y ⟶ cech f where
  app n := cechDiagApp f n.unop.len
  naturality n m g := by
    change 𝟙 (yoneda.obj Y) ≫ cechDiagApp f m.unop.len = cechDiagApp f n.unop.len ≫ _
    rw [Category.id_comp]
    apply WidePullback.hom_ext
    · intro j
      rw [cechDiagApp_π]
      erw [Category.assoc, WidePullback.lift_π]
      exact (cechDiagApp_π f _ _).symm
    · rw [cechDiagApp_base]
      refine Eq.trans ?_ (Category.assoc (cechDiagApp f _) ((cech f).map g) _).symm
      erw [WidePullback.lift_base]
      exact (cechDiagApp_base f _).symm

theorem cechDiag_spec {Y X : Scheme.{0}} (f : Y ⟶ X) :
    ∃ Δ : sch.obj Y ⟶ cech f, IsIso (Δ.app (op ⦋0⦌)) ∧ Δ ≫ cechAug f = sch.map f := by
  refine ⟨cechDiag f, ?_, ?_⟩
  · refine ⟨⟨(WidePullback.π (fun _ : Fin (0 + 1) => yoneda.map f) 0 : _ ⟶ yoneda.obj Y), ?_, ?_⟩⟩
    · exact cechDiagApp_π f 0 0
    · change WidePullback.π (fun _ : Fin (0 + 1) => yoneda.map f) 0 ≫ cechDiagApp f 0 = 𝟙 _
      apply WidePullback.hom_ext
      · intro j
        rw [Fin.fin_one_eq_zero j, Category.assoc, cechDiagApp_π, Category.comp_id, Category.id_comp]
      · rw [Category.assoc, cechDiagApp_base, Category.id_comp, WidePullback.π_arrow]
  · ext n : 1
    exact cechDiagApp_base f _

end GlobalTheory.EtC.GmStep
end

