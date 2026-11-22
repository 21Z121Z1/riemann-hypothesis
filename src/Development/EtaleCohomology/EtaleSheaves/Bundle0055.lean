import Development.EtaleCohomology.EtaleSheaves.Bundle0043
import Development.EtaleCohomology.EtaleSheaves.TwistTensorRestriction
import Development.EtaleCohomology.EtaleSheaves.Bundle0052
import Development.EtaleCohomology.EtaleSheaves.Bundle0047
import Development.EtaleCohomology.EtaleSheaves.Bundle0050
import Development.EtaleCohomology.EtaleSheaves.Bundle0002
import Development.EtaleCohomology.EtaleSheaves.Bundle0044

-- bundled from Development.EtaleCohomology.EtaleSheaves.AugHolds
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.TateTwistZeroAugmentationSheaf

variable (q : ℕ)

def CP : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} (ZMod q)) where
  obj U := ModuleCat.of _ C(U.unop, ULift.{1} (ZMod q))
  map {U V} f := ModuleCat.ofHom
    { toFun := fun g => ContinuousMap.comp g f.unop.base.hom
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

theorem isSheaf_etaleTopology_continuousMaps : Presheaf.IsSheaf Scheme.etaleTopology.{0} (CP q) := by
  apply Presheaf.IsSheaf.of_le (le_trans Scheme.etaleTopology_le_proetaleTopology Scheme.proetaleTopology_le_fpqcTopology)
  haveI : ReflectsLimitsOfSize.{0, 1} (forget (ModuleCat.{1} (ULift.{1} (ZMod q)))) :=
    reflectsLimitsOfSize_shrink.{1, 1, 0, 1} _
  apply Presheaf.isSheaf_of_isSheaf_comp _ _ (forget (ModuleCat.{1} (ULift.{1} (ZMod q))))
  exact isSheaf_fpqcTopology_continuousMapPresheaf (ULift.{1} (ZMod q))

def augA (U : Scheme.{0}) : (Scheme.Γ ⋙ twF q 0).obj (Opposite.op U) →ₗ[ULift.{1} (ZMod q)] C(U, ULift.{1} (ZMod q)) :=
  (twRel q 0 Γ(U, ⊤)).liftQ (Finsupp.linearCombination _ (fun _ => (1 : C(U, ULift.{1} (ZMod q))))) (by
    refine Submodule.span_le.2 ?_
    rintro x ⟨ζ, ξ, a, -, rfl⟩
    simp)

def augP : Scheme.Γ ⋙ twF q 0 ⟶ CP q where
  app U := ModuleCat.ofHom (augA q U.unop)
  naturality {U V} f := by
    apply ModuleCat.hom_ext
    apply Submodule.linearMap_qext
    apply Finsupp.lhom_ext
    intro ζ c
    apply ContinuousMap.ext; intro t
    erw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply]
    change (augA q V.unop) (Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map f.unop.appTop.hom) (Finsupp.single ζ c))) t =
      (augA q U.unop (Submodule.Quotient.mk (Finsupp.single ζ c))) (f.unop.base t)
    simp only [augA]
    erw [Submodule.liftQ_apply, Submodule.liftQ_apply, Finsupp.mapDomain_single, Finsupp.linearCombination_single,
      Finsupp.linearCombination_single]
    rfl

def augS : sheafify Scheme.etaleTopology.{0} (Scheme.Γ ⋙ twF q 0) ⟶ CP q :=
  sheafifyLift Scheme.etaleTopology.{0} (augP q) (isSheaf_etaleTopology_continuousMaps q)

def augC (T : Scheme.{0}) (x : Sec (tw q 0) T) : C(T, ULift.{1} (ZMod q)) := ((augS q).app (Opposite.op T)).hom x

def aug (T : Scheme.{0}) : Sec (tw q 0) T →+ LocallyConstant T (ZMod q) :=
  AddMonoidHom.mk' (fun x => ⟨fun t => (augC q T x t).down,
      (IsLocallyConstant.iff_continuous _).2 (continuous_uliftDown.comp (ContinuousMap.continuous _))⟩)
    (fun x y => by
      ext t
      simp only [LocallyConstant.coe_add, Pi.add_apply, LocallyConstant.coe_mk, augC]
      erw [LinearMap.map_add]
      rfl)

theorem aug_nat {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec (tw q 0) U) :
    aug q V (Sec.res g x) = (aug q U x).comap g.base.hom := by
  have h := congrArg (fun h => (ModuleCat.Hom.hom h) x) ((augS q).naturality g.op)
  ext t
  simp only [aug, AddMonoidHom.mk'_apply, LocallyConstant.coe_mk, LocallyConstant.coe_comap, Function.comp_apply]
  exact congrArg (fun k : C(V, ULift.{1} (ZMod q)) => (k t).down) h

theorem aug_gen (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) : aug q U (twGen 0 ζ) = 1 := by
  have h := congrArg (fun h => (ModuleCat.Hom.hom (NatTrans.app h (Opposite.op U))) (Submodule.Quotient.mk (Finsupp.single ζ 1)))
    (toSheafify_sheafifyLift Scheme.etaleTopology.{0} (augP q) (isSheaf_etaleTopology_continuousMaps q))
  ext t
  simp only [aug, AddMonoidHom.mk'_apply, LocallyConstant.coe_mk, LocallyConstant.coe_one, Pi.one_apply]
  have h2 := congrArg (fun k : C(U, ULift.{1} (ZMod q)) => (k t).down) h
  refine h2.trans ?_
  simp only [augP, augA]
  erw [ModuleCat.hom_ofHom, Submodule.liftQ_apply, Finsupp.linearCombination_single]
  simp

theorem Aug_holds : LateralTheory.E.TateTwistZeroAugmentationBijective.Aug := fun q => ⟨aug q, fun g x => aug_nat q g x, aug_gen q⟩

theorem Tw0_of (hB : LateralTheory.E.TateTwistZeroAugmentationBijective.AugBij) : LateralTheory.E.LCIsoPf.Tw0 := LateralTheory.E.TateTwistZeroAugmentationBijective.Tw0_of Aug_holds hB

end LateralTheory.E.TateTwistZeroAugmentationSheaf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.BaerFlatZModCriterion
section
noncomputable section

namespace LateralTheory.E.BaerFlatZModCriterion

open TensorProduct

section General

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

theorem exists_eq_smul_of_baer (hB : Module.Baer R M) {a b : R}
    (hab : ∀ r, b * r = 0 → ∃ s, r = a * s) {m : M} (hm : a • m = 0) : ∃ m' : M, m = b • m' := by
  let f : R →ₗ[R] R := LinearMap.toSpanSingleton R R b
  have hker : LinearMap.ker f ≤ LinearMap.ker (LinearMap.toSpanSingleton R M m) := by
    intro x hx
    simp only [LinearMap.mem_ker, f, LinearMap.toSpanSingleton_apply, smul_eq_mul] at hx ⊢
    obtain ⟨s, rfl⟩ := hab x (by rw [mul_comm]; exact hx)
    rw [mul_comm, mul_smul, hm, smul_zero]
  let g : LinearMap.range f →ₗ[R] M :=
    (LinearMap.ker f).liftQ (LinearMap.toSpanSingleton R M m) hker ∘ₗ f.quotKerEquivRange.symm.toLinearMap
  obtain ⟨g', hg'⟩ := hB (LinearMap.range f) g
  refine ⟨g' 1, ?_⟩
  have h1 : f 1 = b := by simp [f]
  have hmem : b ∈ LinearMap.range f := ⟨1, h1⟩
  have := hg' b hmem
  have hg : g ⟨b, hmem⟩ = m := by
    have e : (⟨b, hmem⟩ : LinearMap.range f) = ⟨f 1, LinearMap.mem_range_self f 1⟩ := Subtype.ext h1.symm
    rw [e]
    simp only [g, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearMap.quotKerEquivRange_symm_apply_image]
    rw [Submodule.mkQ_apply, Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply, one_smul]
  rw [← hg, ← this, ← map_smul, smul_eq_mul, mul_one]

theorem flat_of_baer [IsPrincipalIdealRing R]
    (hA : ∀ a : R, ∃ b, a * b = 0 ∧ ∀ r, b * r = 0 → ∃ s, r = a * s) (hB : Module.Baer R M) :
    Module.Flat R M := by
  rw [Module.Flat.iff_lift_lsmul_comp_subtype_injective]
  intro I _
  obtain ⟨a, ha⟩ := Submodule.IsPrincipal.principal I
  have haI : a ∈ I := by rw [ha]; exact Submodule.mem_span_singleton_self a
  have pure : ∀ x : I ⊗[R] M, ∃ m : M, x = (⟨a, haI⟩ : I) ⊗ₜ m := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, by rw [tmul_zero]⟩
    | tmul y n =>
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (by rw [← ha]; exact y.2)
      refine ⟨c • n, ?_⟩
      rw [← smul_tmul]
      congr 1
      exact Subtype.ext hc.symm
    | add x y hx hy =>
      obtain ⟨m1, rfl⟩ := hx
      obtain ⟨m2, rfl⟩ := hy
      exact ⟨m1 + m2, by rw [tmul_add]⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨m, rfl⟩ := pure x
  simp only [lift.tmul, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
    LinearMap.lsmul_apply] at hx
  obtain ⟨b, hab, hb⟩ := hA a
  obtain ⟨m', rfl⟩ := exists_eq_smul_of_baer hB hb hx
  rw [← smul_tmul]
  have : b • (⟨a, haI⟩ : I) = 0 := Subtype.ext (by simp [smul_eq_mul, mul_comm, hab])
  rw [this, zero_tmul]

end General

section ZModPart

theorem zmod_ann (q : ℕ) [NeZero q] (a : ZMod q) :
    ∃ b : ZMod q, a * b = 0 ∧ ∀ r : ZMod q, b * r = 0 → ∃ s, r = a * s := by
  obtain ⟨n, hn⟩ : ∃ n, n = a.val := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g, g = Nat.gcd n q := ⟨_, rfl⟩
  have hq : 0 < q := NeZero.pos q
  have hg0 : 0 < g := hg ▸ Nat.gcd_pos_of_pos_right _ hq
  have hgq : g ∣ q := hg ▸ Nat.gcd_dvd_right n q
  have hgn : g ∣ n := hg ▸ Nat.gcd_dvd_left n q
  have hqg : 0 < q / g := Nat.div_pos (Nat.le_of_dvd hq hgq) hg0
  have ha : a = (n : ZMod q) := by rw [hn, ZMod.natCast_zmod_val]
  refine ⟨((q / g : ℕ) : ZMod q), ?_, ?_⟩
  · obtain ⟨k, hk⟩ := hgn
    rw [ha, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
    refine ⟨k, ?_⟩
    rw [hk, mul_comm g k, mul_assoc, Nat.mul_div_cancel' hgq, mul_comm]
  · intro r hr
    have hr' : q ∣ (q / g) * r.val := by
      rw [← ZMod.natCast_eq_zero_iff, Nat.cast_mul, ZMod.natCast_zmod_val]
      exact hr
    have hdiv : g ∣ r.val := by
      have h2 : (q / g) * g ∣ (q / g) * r.val := by rw [Nat.div_mul_cancel hgq]; exact hr'
      exact Nat.dvd_of_mul_dvd_mul_left hqg h2
    obtain ⟨t, ht⟩ := hdiv
    have hz := Nat.gcd_eq_gcd_ab n q
    have hgz : (g : ZMod q) = a * (Nat.gcdA n q : ZMod q) := by
      have := congrArg (Int.cast : ℤ → ZMod q) hz
      push_cast at this
      rw [ZMod.natCast_self, zero_mul, add_zero, ← hg] at this
      rw [this, ha]
    refine ⟨(Nat.gcdA n q : ZMod q) * (t : ZMod q), ?_⟩
    rw [← ZMod.natCast_zmod_val r, ht, Nat.cast_mul, hgz, mul_assoc]

end ZModPart

end LateralTheory.E.BaerFlatZModCriterion

open LateralTheory.E.ZModFlatnessFromBaerCriterion LateralTheory.E.BaerFlatZModCriterion in
theorem LateralTheory.E.ZModFlatnessFromBaerCriterion.LeafInjFlatZMod_of : LeafInjFlatZMod := by
  intro q _ M _ _ hinj
  have : IsPrincipalIdealRing (ZMod q) :=
    IsPrincipalIdealRing.of_surjective (Int.castRingHom (ZMod q)) ZMod.intCast_surjective
  have : IsPrincipalIdealRing (ULift.{1} (ZMod q)) :=
    IsPrincipalIdealRing.of_surjective (ULift.ringEquiv (R := ZMod q)).symm
      (ULift.ringEquiv (R := ZMod q)).symm.surjective
  refine flat_of_baer (fun a => ?_) (Module.Baer.of_injective hinj)
  obtain ⟨b, hab, hb⟩ := zmod_ann q a.down
  refine ⟨ULift.up b, ULift.ext _ _ hab, fun r hr => ?_⟩
  obtain ⟨s, hs⟩ := hb r.down (congrArg ULift.down hr)
  exact ⟨ULift.up s, ULift.ext _ _ hs⟩
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.CechLevelsGeneration
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.TruncCokPf Opposite

namespace LateralTheory.E.LevelsPf

def CechLevel : Prop := ∀ (p : ℕ) {D E Y' Y'' : CommRingCat.{0}} (e : D ⟶ E) (φ' : D ⟶ Y') (u : Y' ⟶ Y'') (φ'' : E ⟶ Y'')
    (hpo : IsPushout φ' e u φ''),
    ∃ (Ep Yp : CommRingCat.{0}) (dp : D ⟶ Ep) (wp : Y' ⟶ Yp) (φp : Ep ⟶ Yp), IsPushout φ' dp wp φp ∧
      (∀ {A : CommRingCat.{0}} (d : A ⟶ D) (P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop), PushClosed P → P D d →
        P E (d ≫ e) → P Ep (d ≫ dp)) ∧
      Nonempty (Arrow.mk ((Arrow.mapCechNerve (sq e φ' u φ'' hpo.w)).app (op (SimplexCategory.mk p))) ≅
        Arrow.mk (yoneda.map (Spec.map φp)))

theorem pull_iso_bij (R : Type) [CommRing R] {E E' : Spc} (a : E ≅ E') (F : Shv R) (n : ℤ) :
    Function.Bijective (pull R a.hom F n) := by
  have h1 : ∀ x, pull R a.inv F n (pull R a.hom F n x) = x := fun x => by
    rw [← pull_comp, Iso.inv_hom_id, pull_id]
  have h2 : ∀ x, pull R a.hom F n (pull R a.inv F n x) = x := fun x => by
    rw [← pull_comp, Iso.hom_inv_id, pull_id]
  exact ⟨Function.LeftInverse.injective h1, Function.RightInverse.surjective h2⟩

theorem transfer (R : Type) [CommRing R] (F : Shv R) {P Q P' Q' : PSh} (f : P ⟶ Q) (g : P' ⟶ Q')
    (α : Arrow.mk f ≅ Arrow.mk g) (n : ℤ) :
    (Function.Surjective (pull R (disc.map g) F n) → Function.Surjective (pull R (disc.map f) F n)) ∧
    (Function.Injective (pull R (disc.map g) F n) → Function.Injective (pull R (disc.map f) F n)) := by
  let αl : P ≅ P' := Arrow.leftFunc.mapIso α
  let αr : Q ≅ Q' := Arrow.rightFunc.mapIso α
  have hw : f ≫ αr.hom = αl.hom ≫ g := by
    exact (Arrow.w α.hom).symm
  have hf : f = αl.hom ≫ g ≫ αr.inv := by
    rw [← Category.assoc, Iso.eq_comp_inv]; exact hw
  have he : ⇑(pull R (disc.map f) F n) =
      pull R (disc.mapIso αl).hom F n ∘ pull R (disc.map g) F n ∘ pull R (disc.mapIso αr).symm.hom F n := by
    funext x
    rw [hf, Functor.map_comp, Functor.map_comp, pull_comp, pull_comp]; rfl
  have bl := pull_iso_bij R (disc.mapIso αl) F n
  have br := pull_iso_bij R (disc.mapIso αr).symm F n
  refine ⟨fun hs => ?_, fun hi => ?_⟩
  · rw [he]; exact bl.2.comp (hs.comp br.2)
  · rw [he]; exact bl.1.comp (hi.comp br.1)

theorem Levels_of (hC : CechLevel) : LateralTheory.E.TruncCokPf.Levels := by
  intro hH q _ i n A Y φ hq P hpush het hlow D d hD Y' w φ' hpo E e Y'' u φ'' hpo' he hs hE p m hm
  obtain ⟨Ep, Yp, dp, wp, φp, hpp, hP, ⟨α⟩⟩ := hC p e φ' u φ'' hpo'
  have hsq : IsPushout φ (d ≫ dp) (w ≫ wp) φp := hpo.paste_vert hpp
  have hrel : RelZ q i m φp := hlow m hm Ep (d ≫ dp) (hP d P hpush hD hE) Yp (w ≫ wp) φp hsq
  have ht := fun k => transfer (ZMod q) (tw q i) _ _ α k
  refine ⟨fun k hk => (ht k).1 (hrel.1 k hk), (ht m).2 hrel.2⟩

end LateralTheory.E.LevelsPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.ChernClassEvaluation
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
namespace LateralTheory.E.ChernClassEvaluation

variable {R : Type} [CommRing R]

theorem chains_d (E : Spc) (p : ℕ) :
    ((chains R).obj E).d (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) =
      (chainsXIso R E (p + 1)).hom ≫ (∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i)) ≫ (chainsXIso R E p).inv := by
  refine (HomologicalComplex.extend_d_eq ((chainsN R).obj E) ComplexShape.embeddingDownNat (i := p + 1) (j := p) rfl rfl).trans ?_
  unfold chainsXIso
  congr 2
  simp [chainsN]
  rfl

theorem freeGen_nat {P Q : PSh} (f : P ⟶ Q) (U : Scheme.{0}) (x : P.obj (op U)) :
    (((free R).map f).hom.app (op U)).hom (freeGen R P U x) = freeGen R Q U (f.app (op U) x) := by
  unfold freeGen
  change ((((toSheafify _ ((freeP R).obj P)) ≫ sheafifyMap _ ((freeP R).map f)).app (op U)).hom _) = _
  rw [← toSheafify_naturality, NatTrans.comp_app, ModuleCat.hom_comp]
  exact congrArg (fun y => ((toSheafify Scheme.etaleTopology ((freeP R).obj Q)).app (op U)).hom y)
    (by erw [ModuleCat.free_map_apply]; rfl)

def evH {A B : Shv R} (U : Scheme.{0}) (y : Sec A U) : (A ⟶ B) →+ Sec B U where
  toFun f := (f.hom.app (op U)).hom y
  map_zero' := rfl
  map_add' _ _ := rfl

theorem evH_apply {A B : Shv R} (U : Scheme.{0}) (y : Sec A U) (f : A ⟶ B) :
    (f.hom.app (op U)).hom y = evH U y f := rfl

theorem evDelta_pf : ChernClassExistence.LeafEvDelta := by
  intro R _ E I n m hm α U
  constructor
  · intro x
    unfold ev
    rw [δ_v n m hm α (-((0 : ℕ) : ℤ)) m (by simp) n 1 (by omega) (by simp)]
    have hz : ((chains R).obj E).d (-((0 : ℕ) : ℤ)) 1 = 0 :=
      (HomologicalComplex.isZero_extend_X _ _ 1 (fun i => by show -(i : ℤ) ≠ 1; omega)).eq_of_tgt _ _
    rw [hz]
    simp [Sec.map]
  · intro p s t hs ht x
    unfold ev
    rw [δ_v n m hm α _ t ht s (-(p : ℤ)) (by omega) (by push_cast; omega), chains_d]
    simp only [Preadditive.comp_add, Preadditive.comp_zsmul, Category.assoc, Iso.inv_hom_id_assoc]
    simp [Sec.map, Units.smul_def, Preadditive.comp_sum, Preadditive.sum_comp, Preadditive.zsmul_comp, Preadditive.comp_zsmul, freeGen_nat, Sx.face]
    rw [evH_apply, map_zsmul, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul]
    congr 1
    rw [← evH_apply]
    simp [freeGen_nat]

theorem etale_kummer_chern_cocycle_exists_of_evaluation_values_and_closedness (hmk : ChernClassExistence.LeafEvMk) (h1 : ChernClassExistence.EtaleKummerChernEdgeValuesExistNatural) (h2 : ChernClassExistence.EtaleKummerChernTriangleValuesExistNatural)
    (c1 : ChernClassExistence.EtaleKummerChernCochainCoboundaryVanishesOnEdges) (c2 : ChernClassExistence.EtaleKummerChernCochainCoboundaryVanishesOnTriangles) (c3 : ChernClassExistence.EtaleKummerChernCochainCoboundaryVanishesOnTetrahedra) :
    LateralTheory.E.ChernCocycleExistenceAndUniqueness.EtaleKummerChernCocycleExists :=
  ChernClassExistence.etale_kummer_chern_cocycle_exists_of_evaluation_values_and_closedness hmk evDelta_pf h1 h2 c1 c2 c3

end LateralTheory.E.ChernClassEvaluation
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.CovOfPoints
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafSurj0Pf
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut

theorem cov_of_points {B : Scheme.{0}} (U : B.Etale) (P : ∀ U' : B.Etale, (U' ⟶ U) → Prop)
    (h : ∀ x : U.left, ∃ (U' : B.Etale) (a : U' ⟶ U), x ∈ Set.range a.left ∧
      ∀ (U'' : B.Etale) (b : U'' ⟶ U'), P U'' (b ≫ a)) : Cov U P := by
  choose Z f hx hP using h
  refine ⟨Sieve.ofArrows Z f, ?_, ?_⟩
  · rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    exact Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ⟨x, hx x⟩
  · rintro U' a ⟨Y, b, g, ⟨j⟩, rfl⟩
    exact hP j U' b

def LeafSurj0W : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  SHV q i V p g1 g2 → ∀ (U : B.Etale), ∀ y : Hrel (ZMod q) (sch.map (prU (g2 ≫ g1 ≫ p) ι U)) (tw q i) 0,
  ∀ x : U.left, U.hom x ∈ Set.range ι → ∃ (U' : B.Etale) (a : U' ⟶ U), x ∈ Set.range a.left ∧
    ∀ (U'' : B.Etale) (b : U'' ⟶ U'), rY q i (g2 ≫ g1 ≫ p) ι (b ≫ a) 0 y = 0

def LeafSurj0V : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  SHV q i V p g1 g2 → ∀ (U : B.Etale), ∀ y : Hrel (ZMod q) (sch.map (prU (g2 ≫ g1 ≫ p) ι U)) (tw q i) 0,
  ∀ x : U.left, U.hom x ∈ V → ∃ (U' : B.Etale) (a : U' ⟶ U), x ∈ Set.range a.left ∧
    ∀ (U'' : B.Etale) (b : U'' ⟶ U'), ∃ c : Hrel (ZMod q) (sch.map (prB ι U'')) (tw q i) 0,
      bY q i (g2 ≫ g1 ≫ p) ι U'' 0 c = rY q i (g2 ≫ g1 ≫ p) ι (b ≫ a) 0 y

theorem LeafSurj0_of (hW : LeafSurj0W) (hV : LeafSurj0V) : LateralTheory.E.LeafDegCut.LeafSurj0 := by
  intro hy q _ k _ hq i B W Y0 Y1 Y2 b ι _ V hVW p g1 g2 h0 h1 h2 hS U y
  refine cov_of_points U _ fun x => ?_
  by_cases hx : U.hom x ∈ V
  · exact hV hy q k hq i b ι V hVW p g1 g2 h0 h1 h2 hS U y x hx
  · have hxW : U.hom x ∈ Set.range ι := by
      have : U.hom x ∉ (V : Set B) := hx
      rw [hVW] at this
      simpa using this
    obtain ⟨U', a, hxa, hz⟩ := hW hy q k hq i b ι V hVW p g1 g2 h0 h1 h2 hS U y x hxW
    exact ⟨U', a, hxa, fun U'' b' => ⟨0, by rw [map_zero, hz U'' b']⟩⟩

end LateralTheory.E.LeafSurj0Pf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.CurveUnitsOrderAtInfinity
section
open Polynomial IntermediateField.algebraAdjoinAdjoin

namespace LateralTheory.E.CurveUnitsOrderAtInfinity

theorem minpolyCoeff : LateralTheory.E.E4.LeafMinpolyCoeff := by
  intro k L _ _ _ s hs F hF x hx i
  subst hF
  have : UniqueFactorizationMonoid (Algebra.adjoin k {s}) := hs.uniqueFactorizationMonoid_adjoin
  have : IsIntegrallyClosed (Algebra.adjoin k {s}) := inferInstance
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' (IntermediateField.adjoin k {s}) hx, coeff_map]
  exact ((minpoly (Algebra.adjoin k {s}) x).coeff i).2

theorem ordInfHom : LateralTheory.E.E4.LeafOrdInfHom :=
  LateralTheory.E.E4.LeafOrdInfHom_of_local (LateralTheory.E.E4.LeafOrdInfLocal_of' LateralTheory.E.E4.LeafFinInf_of LateralTheory.E.E4.LeafFinVal_of)

theorem LeafUnits_of : LateralTheory.E.E4.LeafUnits :=
  LateralTheory.E.E4.LeafUnits_of (LateralTheory.E.E4.LeafUnitsFG_of_dim LateralTheory.E.E4.LeafNoetherDim_of
    (LateralTheory.E.E4.LeafOrdAtInfinity_of_cut ordInfHom minpolyCoeff))

end LateralTheory.E.CurveUnitsOrderAtInfinity
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.DescentPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E1Cut LateralTheory.E.LocallyConstantH0

namespace LateralTheory.E.DescentPf

theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (h : W ⟶ V) (g : V ⟶ U) (x : Sec F U) :
    Sec.res (h ≫ g) x = Sec.res h (Sec.res g x) := by
  simp [Sec.res]

theorem val_smul {q : ℕ} [NeZero q] (i : ℤ) {U : Scheme.{0}} (c : ZMod q) (x : Sec (tw q i) U) :
    c.val • x = (ULift.up c : ULift.{1} (ZMod q)) • x := by
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
  congr 1
  apply ULift.ext
  rw [ULift.down_natCast, ZMod.natCast_zmod_val]

theorem Descent_of (hAC : LateralTheory.E.LCBijPf.TwGenNZAC) : LateralTheory.E.LCSurjPf.Descent := by
  intro q _ i m hm B _ ζ y hloc
  obtain ⟨S, hS, hP⟩ := hloc
  have hform : ∀ {V W : Scheme.{0}} (g : V ⟶ Spec (CommRingCat.of B)) (h : W ⟶ V) (c : ZMod q),
      Sec.res g y = c.val • twGen i ((gam ζ).map g.appTop.hom) →
      Sec.res (h ≫ g) y = c.val • twGen i ((gam ζ).map (h ≫ g).appTop.hom) := by
    intro V W g h c hc
    have hs : ∀ x : Sec (tw q i) V, Sec.res h (c.val • x) = c.val • Sec.res h x := fun x => map_nsmul _ _ x
    rw [res_comp, hc, hs, LateralTheory.E.LCBijPf.twGen_res]
    rfl
  have huniq : ∀ {V1 V2 : Scheme.{0}} (g1 : V1 ⟶ Spec (CommRingCat.of B)) (g2 : V2 ⟶ Spec (CommRingCat.of B))
      (c1 c2 : ZMod q), Sec.res g1 y = c1.val • twGen i ((gam ζ).map g1.appTop.hom) →
      Sec.res g2 y = c2.val • twGen i ((gam ζ).map g2.appTop.hom) →
      ∀ v1 v2, g1 v1 = g2 v2 → c1 = c2 := by
    intro V1 V2 g1 g2 c1 c2 h1 h2 v1 v2 hv
    obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback v1 v2 hv
    let A := (pullback g1 g2).affineOpenCover
    obtain ⟨w, -⟩ := A.covers z
    let a := A.f (A.idx z)
    have e1 := hform g1 (a ≫ pullback.fst g1 g2) c1 h1
    have e2 := hform g2 (a ≫ pullback.snd g1 g2) c2 h2
    have hcomp : (a ≫ pullback.snd g1 g2) ≫ g2 = (a ≫ pullback.fst g1 g2) ≫ g1 := by
      simp [pullback.condition]
    rw [hcomp] at e2
    have hne : Nontrivial (A.X (A.idx z)) := PrimeSpectrum.nontrivial w
    obtain ⟨φ, hφ⟩ := Spec.map_surjective ((a ≫ pullback.fst g1 g2) ≫ g1)
    have key := LateralTheory.E.LCBijPf.twGenNZ_of hAC q i (A.X (A.idx z)) (ζ.map φ.hom) (c1 - c2)
    refine sub_eq_zero.1 (key ?_)
    have e := e1.symm.trans e2
    rw [← hφ] at e
    rw [LateralTheory.E.LCBijPf.gam_map]
    rw [val_smul, val_smul] at e
    have hup : (ULift.up (c1 - c2) : ULift.{1} (ZMod q)) = ULift.up c1 - ULift.up c2 := rfl
    rw [val_smul, hup, sub_smul, sub_eq_zero]
    exact e
  obtain ⟨𝒰, h𝒰⟩ := (Scheme.mem_grothendieckTopology_iff (P := @Etale)).1 hS
  have hpiece : ∀ x : PrimeSpectrum B, ∃ (R : CommRingCat.{0}) (g : Spec R ⟶ Spec (CommRingCat.of B)),
      Etale g ∧ S.arrows g ∧ x ∈ Set.range g := by
    intro x
    obtain ⟨j, v, hv⟩ := ((Scheme.presieve₀_mem_precoverage_iff _).1 𝒰.mem₀).1 x
    let A := (𝒰.X j).affineOpenCover
    obtain ⟨w, hw⟩ := A.covers v
    have : Etale (𝒰.f j) := ((Scheme.presieve₀_mem_precoverage_iff _).1 𝒰.mem₀).2 j
    refine ⟨A.X (A.idx v), A.f (A.idx v) ≫ 𝒰.f j, inferInstance, S.downward_closed (h𝒰 _ _ (Presieve.ofArrows.mk j)) _, ⟨w, ?_⟩⟩
    rw [Scheme.Hom.comp_apply, hw, hv]
  choose R g hg hSg hx using hpiece
  have hc : ∀ x, ∃ c : ZMod q, Sec.res (g x) y = c.val • twGen i ((gam ζ).map (g x).appTop.hom) :=
    fun x => hP _ _ (hSg x)
  choose c hc using hc
  have key : ∀ (x : PrimeSpectrum B) {V : Scheme.{0}} (g' : V ⟶ Spec (CommRingCat.of B)) (c' : ZMod q),
      Sec.res g' y = c'.val • twGen i ((gam ζ).map g'.appTop.hom) → ∀ v, g' v = x → c x = c' := by
    intro x V g' c' h' v hv
    obtain ⟨u, hu⟩ := hx x
    exact huniq (g x) g' _ _ (hc x) h' u v (hu.trans hv.symm)
  have hlc : IsLocallyConstant c := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    have := hg x
    refine ⟨Set.range (g x), (g x).isOpenMap.isOpen_range, hx x, fun x' hx' => ?_⟩
    obtain ⟨u, hu⟩ := hx'
    exact key x' (g x) (c x) (hc x) u hu
  let ψ : LocallyConstant (PrimeSpectrum B) (ZMod q) := ⟨c, hlc⟩
  refine ⟨ψ, Sieve.ofArrows (fun x => Spec (R x)) g, ?_, ?_⟩
  · exact Scheme.Cover.mem_grothendieckTopology
      (Scheme.Cover.mkOfCovers (P := @Etale) (PrimeSpectrum B) (fun x => Spec (R x)) g
        (fun x => by obtain ⟨u, hu⟩ := hx x; exact ⟨x, u, hu⟩) hg)
  · intro V k hk
    obtain ⟨W, h, k', hk', rfl⟩ := hk
    obtain ⟨x⟩ := hk'
    rw [res_comp, res_comp]
    congr 1
    rw [hc x]
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (g x)
    have hlc' : lcMap φ.hom ψ = LocallyConstant.const _ (c x) := by
      ext u
      exact key _ (g x) (c x) (hc x) u (by rw [← hφ]; rfl)
    have e := hm.1 B (R x) φ.hom ζ ψ
    rw [hlc', hm.2, LateralTheory.E.LCBijPf.gam_map] at e
    rw [← hφ]
    exact e.symm

end LateralTheory.E.DescentPf
end
end

