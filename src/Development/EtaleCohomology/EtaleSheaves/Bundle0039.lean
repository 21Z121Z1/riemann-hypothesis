import Development.EtaleCohomology.EtaleSheaves.Bundle0026
import Development.EtaleCohomology.EtaleSheaves.Bundle0016
import Development.EtaleCohomology.EtaleSheaves.Bundle0020
import Development.EtaleCohomology.EtaleSheaves.Bundle0028

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafTwTensExPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC
open scoped DirectSum TensorProduct

namespace LateralTheory.E.LeafTwTensExPf

open Classical in
section
variable {R : Type} [CommRing R] (I J : Cx R)

theorem tres_tmul {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) :
    Tens.res g w (DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
      Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) p (a ⊗ₜ b)) =
    DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
      Sec (I.X p.1.1) V ⊗[ULift.{1} R] Sec (J.X p.1.2) V) p (Sec.res g a ⊗ₜ Sec.res g b) := by
  simp [Tens.res]

def TP (w : ℤ) : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R) where
  obj U := ModuleCat.of _ (Tens I J U.unop w)
  map g := ModuleCat.ofHom (Tens.res g.unop w)
  map_id U := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    induction x using DirectSum.induction_on with
    | zero => simp
    | add x y hx hy => simp_all
    | of p y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp_all
      | tmul a b =>
        have := tres_tmul I J (𝟙 U.unop) w p a b
        simp only [DirectSum.lof_eq_of] at this
        simp [this, Sec.res]
  map_comp f g := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    induction x using DirectSum.induction_on with
    | zero => simp
    | add x y hx hy => simp_all
    | of p y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp_all
      | tmul a b =>
        have h1 := tres_tmul I J (g.unop ≫ f.unop) w p a b
        have h2 := tres_tmul I J f.unop w p a b
        have h3 := tres_tmul I J g.unop w p (Sec.res f.unop a) (Sec.res f.unop b)
        simp only [DirectSum.lof_eq_of] at h1 h2 h3
        simp [h1, h2, Sec.res]
        exact h3.symm
end
end LateralTheory.E.LeafTwTensExPf

namespace LateralTheory.E.LeafTwTensExPf
open Classical
variable {R : Type} [CommRing R] (I J : Cx R)

abbrev lo {U : Scheme.{0}} {w : ℤ} (p : {p : ℤ × ℤ // p.1 + p.2 = w}) :
    Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U →ₗ[ULift.{1} R] Tens I J U w :=
  DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} =>
      Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) p

def dT (U : Scheme.{0}) (w : ℤ) : Tens I J U w →ₗ[ULift.{1} R] Tens I J U (w + 1) :=
  DirectSum.toModule _ _ _ fun p =>
    lo I J (U := U) (w := w + 1) ⟨(p.1.1 + 1, p.1.2), by have := p.2; simp only at this ⊢; omega⟩ ∘ₗ
      TensorProduct.map ((I.d p.1.1 (p.1.1 + 1)).hom.app (op U)).hom LinearMap.id +
    ((p.1.1.negOnePow : ℤˣ) : ℤ) • (lo I J (U := U) (w := w + 1) ⟨(p.1.1, p.1.2 + 1), by have := p.2; simp only at this ⊢; omega⟩ ∘ₗ
      TensorProduct.map LinearMap.id ((J.d p.1.2 (p.1.2 + 1)).hom.app (op U)).hom)

theorem dT_tmul (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U) :
    dT I J U w (lo I J ⟨(s, t), h⟩ (a ⊗ₜ b)) =
      lo I J ⟨(s + 1, t), by simp only; omega⟩ (Sec.map (I.d s (s + 1)) a ⊗ₜ b) +
      ((s.negOnePow : ℤˣ) : ℤ) • lo I J ⟨(s, t + 1), by simp only; omega⟩ (a ⊗ₜ Sec.map (J.d t (t + 1)) b) := by
  simp [dT, lo, DirectSum.toModule_lof]

end LateralTheory.E.LeafTwTensExPf

namespace LateralTheory.E.LeafTwTensExPf
open Classical
variable {R : Type} [CommRing R] (I J : Cx R)

theorem dd0 {K : Cx R} {U : Scheme.{0}} (s : ℤ) (a : Sec (K.X s) U) :
    Sec.map (K.d (s + 1) (s + 1 + 1)) (Sec.map (K.d s (s + 1)) a) = 0 := by
  rw [LateralTheory.E.LeafTwPairExistsPf.map_map, HomologicalComplex.d_comp_d]
  simp [Sec.map]

theorem dT_nat {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) :
    dT I J V w ∘ₗ Tens.res g w = Tens.res g (w + 1) ∘ₗ dT I J U w := by
  apply DirectSum.linearMap_ext; rintro ⟨⟨s, t⟩, h⟩
  apply TensorProduct.ext'; intro a b
  simp only [LinearMap.comp_apply]
  erw [tres_tmul, dT_tmul, dT_tmul, map_add, map_zsmul, tres_tmul, tres_tmul,
    LateralTheory.E.LeafTwPairExistsPf.res_map, LateralTheory.E.LeafTwPairExistsPf.res_map]

theorem dT_dT (U : Scheme.{0}) (w : ℤ) : dT I J U (w + 1) ∘ₗ dT I J U w = 0 := by
  apply DirectSum.linearMap_ext; rintro ⟨⟨s, t⟩, h⟩
  apply TensorProduct.ext'; intro a b
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
  rw [dT_tmul, map_add, map_zsmul]
  rw [dT_tmul (s := s + 1) (t := t) (w := w + 1)]
  rw [dT_tmul (s := s) (t := t + 1) (w := w + 1)]
  rw [dd0 (K := I), dd0 (K := J)]
  simp only [TensorProduct.zero_tmul, TensorProduct.tmul_zero, map_zero, zero_add, smul_zero, add_zero,
    Int.negOnePow_succ, Units.val_neg, neg_smul, neg_add_cancel]

end LateralTheory.E.LeafTwTensExPf

namespace LateralTheory.E.LeafTwTensExPf
open Classical
variable {R : Type} [CommRing R] (I J : Cx R)

def dTP (w : ℤ) : TP I J w ⟶ TP I J (w + 1) where
  app U := ModuleCat.ofHom (dT I J U.unop w)
  naturality _ _ g := ModuleCat.hom_ext (dT_nat I J g.unop w)

def PC : CochainComplex (Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) ℤ :=
  CochainComplex.of (TP I J) (dTP I J) (fun w => by
    ext U : 2
    exact ModuleCat.hom_ext (dT_dT I J U.unop w))

def TC : Cx R := ((presheafToSheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).mapHomologicalComplex _).obj (PC I J)

abbrev un (U : Scheme.{0}) (w : ℤ) : Tens I J U w →ₗ[ULift.{1} R] Sec ((TC I J).X w) U :=
  ((toSheafify Scheme.etaleTopology.{0} (TP I J w)).app (op U)).hom

theorem un_nat {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (x : Tens I J U w) :
    Sec.res g (un I J U w x) = un I J V w (Tens.res g w x) :=
  (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom ((toSheafify Scheme.etaleTopology.{0} (TP I J w)).naturality g.op)) x).symm

theorem un_d (U : Scheme.{0}) (w : ℤ) (x : Tens I J U w) :
    Sec.map ((TC I J).d w (w + 1)) (un I J U w x) = un I J U (w + 1) (dT I J U w x) := by
  have := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    (congrArg (fun f => f.app (op U)) (toSheafify_naturality Scheme.etaleTopology.{0} (dTP I J w)))) x
  simp only [TC, PC, Functor.mapHomologicalComplex_obj_d, CochainComplex.of_d] at this ⊢
  exact this.symm

end LateralTheory.E.LeafTwTensExPf

namespace LateralTheory.E.LeafTwTensExPf
open Classical
variable {R : Type} [CommRing R] (I J : Cx R)

def tau : Pair I J (TC I J) where
  mul U s t w h := (TensorProduct.mk _ _ _).compr₂ (un I J U w ∘ₗ lo I J ⟨(s, t), h⟩)
  nat g s t w h a b := by
    simp only [LinearMap.compr₂_apply, TensorProduct.mk_apply, LinearMap.comp_apply]
    rw [un_nat]
    congr 1
    exact tres_tmul I J g w ⟨(s, t), h⟩ a b
  leibniz U s t w h a b := by
    simp only [LinearMap.compr₂_apply, TensorProduct.mk_apply, LinearMap.comp_apply]
    rw [un_d, dT_tmul, map_add, map_zsmul, Units.smul_def]

theorem tau_lift (U : Scheme.{0}) (w : ℤ) : (tau I J).lift U w = un I J U w := by
  apply DirectSum.linearMap_ext; rintro ⟨⟨s, t⟩, h⟩
  apply TensorProduct.ext'; intro a b
  simp [Pair.lift, tau]

theorem tau_isTensor : (tau I J).IsTensor := by
  refine ⟨fun U w y => ?_, fun U w x hx => ?_⟩
  · refine ⟨_, Presheaf.imageSieve_mem Scheme.etaleTopology.{0} (toSheafify Scheme.etaleTopology.{0} (TP I J w))
      (U := op U) y, fun V g ⟨t, ht⟩ => ⟨t, ?_⟩⟩
    rw [tau_lift]
    exact ht
  · rw [tau_lift] at hx
    refine ⟨_, Presheaf.equalizerSieve_mem Scheme.etaleTopology.{0} (toSheafify Scheme.etaleTopology.{0} (TP I J w))
      (X := op U) x 0 (by rw [map_zero]; exact hx), fun V g hg => ?_⟩
    have : Tens.res g w x = Tens.res g w 0 := hg
    rwa [map_zero] at this

end LateralTheory.E.LeafTwTensExPf

namespace LateralTheory.E.LeafTwTensExPf

theorem LeafTwTensEx_of : LateralTheory.E.LeafTwPairExistsPf.LeafTwTensEx := by
  intro q _ i j
  exact ⟨_, tau _ _, tau_isTensor _ _⟩

end LateralTheory.E.LeafTwTensExPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafUnitsPfE
section
namespace LateralTheory.E.E4

def LeafOrdInfHom : Prop := ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B]
  [Algebra k B] [Algebra.FiniteType k B] (g : Polynomial k →ₐ[k] B), Function.Injective g → g.Finite →
  ∃ (n : ℕ) (φ : Bˣ →* Multiplicative (Fin n → ℤ)), ∀ u : Bˣ, φ u = 1 →
    IsIntegral (Algebra.adjoin k {(algebraMap B (FractionRing B) (g Polynomial.X))⁻¹})
      (algebraMap B (FractionRing B) (u : B))

def LeafIntBoth : Prop := ∀ (k L : Type) [Field k] [Field L] [Algebra k L] (t : L), Transcendental k t → ∀ x : L,
  IsIntegral (Algebra.adjoin k {t}) x → IsIntegral (Algebra.adjoin k {t⁻¹}) x → IsIntegral k x

theorem LeafOrdAtInfinity_of (hV : LeafOrdInfHom) (hI : LeafIntBoth) : LeafOrdAtInfinity := by
  intro k B _ _ _ _ _ _ g hg hf
  obtain ⟨n, φ, hφ⟩ := hV k B g hg hf
  refine ⟨n, φ, fun u hu => ?_⟩
  set L := FractionRing B
  set T : L := algebraMap B L (g Polynomial.X)
  have hinjL : Function.Injective (algebraMap B L) := IsFractionRing.injective B L
  let G : Polynomial k →ₐ[k] L := (IsScalarTower.toAlgHom k B L).comp g
  have hG : Function.Injective G := hinjL.comp hg
  have hT : Transcendental k T := by
    intro ⟨p, hp0, hp⟩
    apply hp0
    apply hG
    rw [map_zero]
    have : G p = Polynomial.aeval T p := by
      rw [show G p = G (Polynomial.aeval Polynomial.X p) by simp, ← Polynomial.aeval_algHom_apply]; rfl
    rw [this]; exact hp
  have hint : IsIntegral (Algebra.adjoin k {T}) (algebraMap B L (u : B)) := by
    obtain ⟨p, hpm, hp⟩ := (RingHom.IsIntegral.of_finite hf) (u : B)
    let f : Polynomial k →ₐ[k] Algebra.adjoin k {T} := Polynomial.aeval ⟨T, Algebra.subset_adjoin rfl⟩
    have hfG : ((algebraMap (Algebra.adjoin k {T}) L).comp f.toRingHom) = (algebraMap B L).comp g.toRingHom := by
      have : (IsScalarTower.toAlgHom k (Algebra.adjoin k {T}) L).comp f = G := by
        apply Polynomial.algHom_ext; simp [f, G, T]
      exact congrArg AlgHom.toRingHom this
    refine ⟨p.map f.toRingHom, hpm.map _, ?_⟩
    rw [Polynomial.eval₂_map, hfG, ← Polynomial.hom_eval₂]
    change algebraMap B L (Polynomial.eval₂ g.toRingHom (u : B) p) = 0
    rw [hp, map_zero]
  have := hI k L T hT _ hint (hφ u hu)
  exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom k B L) hinjL).mp this

end LateralTheory.E.E4
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LimIntPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.CoverCut

namespace LateralTheory.E.LimIntPf

theorem key {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (hw : f ≫ g = h) (U : Z.Opens) (V₁ : Y.Opens)
    (W₁ W : X.Opens) (e1 : V₁ ≤ g ⁻¹ᵁ U) (e2 : W₁ ≤ f ⁻¹ᵁ V₁) (e3 : W ≤ W₁) (e : W ≤ h ⁻¹ᵁ U) (x : Γ(Z, U)) :
    X.presheaf.map (homOfLE e3).op (f.appLE V₁ W₁ e2 (g.appLE U V₁ e1 x)) = h.appLE U W e x := by
  subst hw
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, Scheme.Hom.appLE_comp_appLE_assoc,
    Scheme.Hom.appLE_map]

theorem app_surj {J : Type} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0}) (c : Cone D) (hc : IsLimit c)
    [∀ {i k : J} (f : i ⟶ k), IsAffineHom (D.map f)] (hC : ∀ {i k : J} (f : i ⟶ k), IsClosedImmersion (D.map f))
    (j : J) (U : (D.obj j).Opens) (hU : IsAffineOpen U) :
    Function.Surjective ((c.π.app j).app U) := by
  intro s
  have (k : Over j) : IsAffine ((opensDiagram D j U).obj k) := hU.preimage (D.map _)
  obtain ⟨k, t, hk⟩ := exists_appTop_π_eq_of_isAffine_of_isLimit _ _ (isLimitOpensCone D c hc j U)
    (c.pt.presheaf.map (homOfLE (show (c.π.app j ⁻¹ᵁ U).ι ''ᵁ ⊤ ≤ c.π.app j ⁻¹ᵁ U by simp)).op s)
  have := hC k.hom
  obtain ⟨u, hu⟩ := (D.map k.hom).app_surjective U hU
    ((D.obj k.left).presheaf.map (homOfLE (show D.map k.hom ⁻¹ᵁ U ≤ (D.map k.hom ⁻¹ᵁ U).ι ''ᵁ ⊤ by simp)).op t)
  refine ⟨u, ?_⟩
  simp only [opensCone_π_app, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE] at hk hu ⊢
  have e1 : ∀ {X : Scheme.{0}} {V W : X.Opens} (h1 : V ≤ W) (h2 : W ≤ V) (x : Γ(X, W)),
      X.presheaf.map (homOfLE h2).op (X.presheaf.map (homOfLE h1).op x) = x := by
    intro X V W h1 h2 x
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    have : (homOfLE h1).op ≫ (homOfLE h2).op = 𝟙 (Opposite.op W) := Subsingleton.elim _ _
    rw [this, CategoryTheory.Functor.map_id]; rfl
  have hs := e1 (X := c.pt) (show (c.π.app j ⁻¹ᵁ U).ι ''ᵁ ⊤ ≤ c.π.app j ⁻¹ᵁ U by simp)
    (show c.π.app j ⁻¹ᵁ U ≤ (c.π.app j ⁻¹ᵁ U).ι ''ᵁ ⊤ by simp) s
  rw [← hk] at hs
  have ht := e1 (X := D.obj k.left) (show D.map k.hom ⁻¹ᵁ U ≤ (D.map k.hom ⁻¹ᵁ U).ι ''ᵁ ⊤ by simp)
    (show (D.map k.hom ⁻¹ᵁ U).ι ''ᵁ ⊤ ≤ D.map k.hom ⁻¹ᵁ U by simp) t
  rw [← hu] at ht
  rw [← hs, ← ht]
  have cg : ∀ {X Y : Scheme.{0}} (f g : X ⟶ Y) (h : f = g) (U : Y.Opens) (V : X.Opens) e e',
      f.appLE U V e = g.appLE U V e' := by
    intro X Y f g h U V e e'; subst h; rfl
  erw [Scheme.Hom.resLE_appLE]
  simp only [← ConcreteCategory.comp_apply, Scheme.Hom.appLE_map]
  exact (key _ _ _ (c.w k.hom) _ _ _ _ _ _ _ _ u).symm

theorem LimInt_of : LateralTheory.E.BuildCut.LimInt := by
  intro Y y J _ _ D c ι hsys j
  obtain ⟨⟨hl⟩, h2, h3⟩ := hsys
  have hA : ∀ {i k : J} (f : i ⟶ k), IsAffineHom (D.map f) := fun f => (h3 f).2
  have hC : ∀ {i k : J} (f : i ⟶ k), IsClosedImmersion (D.map f) := by
    intro i k f
    have : IsClosedImmersion (ι k) := (h2 k).2.1
    have : IsClosedImmersion (D.map f ≫ ι k) := by rw [(h3 f).1]; exact (h2 i).2.1
    exact IsClosedImmersion.of_comp (D.map f) (ι k)
  have : IsClosedImmersion (ι j) := (h2 j).2.1
  have : IsIntegralHom (c.π.app j) :=
    { toIsAffineHom := isAffineHom_π_app D c hl j
      isIntegral_app := fun U hU =>
        (RingHom.Finite.of_surjective _ (app_surj D c hl hC j U hU)).to_isIntegral }
  infer_instance

end LateralTheory.E.LimIntPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LocalizationIntegralClosure
section
noncomputable section
open Polynomial GlobalTheory.EtC

namespace LateralTheory.E.LocalizationIntegralClosure

theorem aic_loc (B : Type) [CommRing B] [IsDomain B] (M : Submonoid B) (hB : AIC B) :
    AIC (Localization M) := by
  classical
  intro p hp hd
  set L := Localization M
  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples_of_finset (R := B) M
    ((Finset.range (p.natDegree + 1)).image p.coeff) (S := L)
  set t : L := algebraMap B L (s : B) with ht
  have hlift : scaleRoots p t ∈ lifts (algebraMap B L) := by
    rw [lifts_iff_coeff_lifts]
    intro i
    rw [coeff_scaleRoots]
    rcases lt_or_ge i p.natDegree with hi | hi
    · obtain ⟨c, hc⟩ := hs (p.coeff i) (Finset.mem_image.2 ⟨i, Finset.mem_range.2 (by omega), rfl⟩)
      obtain ⟨k, hk⟩ : ∃ k, p.natDegree - i = k + 1 := ⟨p.natDegree - i - 1, by omega⟩
      refine ⟨c * (s : B) ^ k, ?_⟩
      rw [hk, map_mul, map_pow, hc, pow_succ, Algebra.smul_def, ← ht]
      ring
    · rcases eq_or_lt_of_le hi with h | h
      · subst h; rw [hp.coeff_natDegree]; exact ⟨1, by simp⟩
      · rw [coeff_eq_zero_of_natDegree_lt h]; exact ⟨0, by simp⟩
  obtain ⟨q, hq, hqd, hqm⟩ := lifts_and_natDegree_eq_and_monic hlift ((monic_scaleRoots_iff t).2 hp)
  obtain ⟨b, hb⟩ := hB q hqm (by rw [hqd, natDegree_scaleRoots]; exact hd)
  obtain ⟨u, hu⟩ := IsLocalization.map_units L s
  refine ⟨algebraMap B L b * ((u⁻¹ : Lˣ) : L), ?_⟩
  have h1 : (scaleRoots p t).eval (algebraMap B L b) = 0 := by
    rw [← hq, eval_map, eval₂_at_apply, hb, map_zero]
  have h2 : (scaleRoots p t).eval (t * (algebraMap B L b * ((u⁻¹ : Lˣ) : L))) =
      t ^ p.natDegree * p.eval (algebraMap B L b * ((u⁻¹ : Lˣ) : L)) :=
    scaleRoots_eval₂_mul (p := p) (RingHom.id L) (algebraMap B L b * ((u⁻¹ : Lˣ) : L)) t
  have h3 : t * (algebraMap B L b * ((u⁻¹ : Lˣ) : L)) = algebraMap B L b := by
    rw [ht, ← hu, mul_comm (algebraMap B L b), ← mul_assoc, Units.mul_inv, one_mul]
  rw [h3, h1] at h2
  have hunit : IsUnit (t ^ p.natDegree) := (hu ▸ u.isUnit).pow _
  exact (hunit.mul_right_eq_zero).1 h2.symm

theorem LocAIC_of : LateralTheory.E.HensCut.LocAIC := by
  intro B _ _ M h0 hB
  have hle : M ≤ nonZeroDivisors B := fun x hx =>
    mem_nonZeroDivisors_of_ne_zero (fun h => h0 (h ▸ hx))
  exact ⟨IsLocalization.isDomain_localization hle, aic_loc B M hB⟩

end LateralTheory.E.LocalizationIntegralClosure
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.MonicSplitsPf
section
open Polynomial

namespace LateralTheory.E.MonicSplitsPf

theorem selfDualLattice_projection_mem_of_unit_length (R : Type) [CommRing R] [IsDomain R] (hA : GlobalTheory.EtC.AIC R) :
    ∀ n : ℕ, ∀ p : Polynomial R, p.Monic → p.natDegree = n →
      ∃ s : Multiset R, p = (s.map fun a => X - C a).prod := by
  intro n
  induction n with
  | zero =>
    intro p hp hn
    refine ⟨0, ?_⟩
    simpa using hp.natDegree_eq_zero.mp hn
  | succ n ih =>
    intro p hp hn
    obtain ⟨a, ha⟩ := hA p hp (by omega)
    have hroot : IsRoot p a := ha
    have hmul := (mul_divByMonic_eq_iff_isRoot (p := p) (a := a)).mpr hroot
    set q := p /ₘ (X - C a) with hq
    have hqm : q.Monic := Polynomial.Monic.of_mul_monic_left (monic_X_sub_C a) (by rw [hmul]; exact hp)
    have hqd : q.natDegree = n := by
      rw [hq, natDegree_divByMonic _ (monic_X_sub_C a), natDegree_X_sub_C, hn]; omega
    obtain ⟨s, hs⟩ := ih q hqm hqd
    refine ⟨a ::ₘ s, ?_⟩
    rw [Multiset.map_cons, Multiset.prod_cons, ← hs, hmul]

theorem MonicSplits_of : LateralTheory.E.HensCut.MonicSplits := by
  intro R _ _ hA p hp
  exact selfDualLattice_projection_mem_of_unit_length R hA p.natDegree p hp rfl

end LateralTheory.E.MonicSplitsPf
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.ProEqvPfA
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.CoverCut LateralTheory.E.ProEqvPf

theorem LateralTheory.E.ProEqvPf.stageA (hC : Cont) (H : Hyp) (q : ℕ) (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A] (hq : IsUnit (q : A))
    {Y : Scheme.{0}} [CompactSpace Y] [QuasiSeparatedSpace Y] (g : Y ⟶ Spec (CommRingCat.of A)) (y : Y) {J : Type}
    [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0}) (c : Cone D) (ι : ∀ j, D.obj j ⟶ Y)
    (hc : ClopenSys y D c ι) (hp : ∀ j, PB q i ((c.π.app j ≫ ι j) ≫ g)) (n : ℤ)
    (x : Ht q (sch.obj Y) n i) (hx : pull _ (sch.map (pullback.fst g (cpt A))) _ _ x = 0) :
    ∃ j, pull _ (sch.map (ι j)) _ _ x = 0 := by
  obtain ⟨⟨hl⟩, hι, hD⟩ := hc
  obtain ⟨j0⟩ := IsCofiltered.nonempty (C := J)
  have e1 : pull _ (sch.map (pullback.fst ((c.π.app j0 ≫ ι j0) ≫ g) (cpt A))) (tw q i) n
      (pull _ (sch.map (c.π.app j0 ≫ ι j0)) (tw q i) n x) = pull _ (sch.map (pullback.fst ((c.π.app j0 ≫ ι j0) ≫ g) (cpt A))) (tw q i) n 0 := by
    rw [map_zero, ← pull_comp, ← Functor.map_comp]
    have : pullback.fst ((c.π.app j0 ≫ ι j0) ≫ g) (cpt A) ≫ c.π.app j0 ≫ ι j0 =
        fm (c.π.app j0 ≫ ι j0) g ≫ pullback.fst g (cpt A) := by
      unfold fm pullback.map; rw [pullback.lift_fst]
    rw [this, Functor.map_comp, pull_comp, hx, map_zero]
  have e2 := (hp j0 n).1 e1
  rw [Functor.map_comp, pull_comp] at e2
  have hcs : ∀ j, CompactSpace (D.obj j) := fun j => by
    have := (hι j).2.1; exact QuasiCompact.compactSpace_of_compactSpace (ι j)
  have hqs : ∀ j, QuasiSeparatedSpace (D.obj j) := fun j => by
    have := (hι j).1; exact quasiSeparatedSpace_of_quasiSeparated (ι j)
  obtain ⟨k, f, hk⟩ := (hC H q D c hl (fun f => (hD f).2) hcs hqs (fun j => unit_of hq (ι j ≫ g)) n i).2 j0 _ e2
  refine ⟨k, ?_⟩
  rw [← (hD f).1, Functor.map_comp, pull_comp]
  exact hk

namespace LateralTheory.E.ProEqvPf

def StageB : Prop := Cont → Hyp → ∀ (q : ℕ) (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A], IsUnit (q : A) →
  ∀ {Y : Scheme.{0}} [CompactSpace Y] [QuasiSeparatedSpace Y] (g : Y ⟶ Spec (CommRingCat.of A)) (y : Y) {J : Type}
  [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0}) (c : Cone D) (ι : ∀ j, D.obj j ⟶ Y),
  ClopenSys y D c ι → (∀ j, PB q i ((c.π.app j ≫ ι j) ≫ g)) → ∀ n : ℤ,
  ∀ z : Ht q (sch.obj (pullback g (cpt A))) n i, ∃ j, Hit q i n g z (ι j)

theorem stage_of (hB : StageB) : PiLocalization₂ := by
  intro hC H q i A _ _ hq Y _ _ g y J _ _ D c ι hc hp n
  exact ⟨fun x hx => stageA hC H q i A hq g y D c ι hc hp n x hx, hB hC H q i A hq g y D c ι hc hp n⟩

theorem etale_pro_equivalence_of_continuity_mayer_vietoris_lifting_stage_glue (hC : Cont) (hM : MV) (hB : StageB) (hG : Glue) : ProEqv :=
  ProEqv_of hC hM (stage_of hB) hG

end LateralTheory.E.ProEqvPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.RelNormPfAff
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.E.RelNormPf

open AlgebraicGeometry.Scheme.Hom in
theorem closedAt_preimage {Z S : Scheme.{0}} (g : Z ⟶ S) [QuasiCompact g] [QuasiSeparated g]
    (U : S.Opens) (hU : IsAffineOpen U) : ClosedAt g.toNormalization (g.fromNormalization ⁻¹ᵁ U) := by
  intro b hb
  letI := (g.app U).hom.toAlgebra
  have hle : g ⁻¹ᵁ U ≤ g.toNormalization ⁻¹ᵁ g.fromNormalization ⁻¹ᵁ U := by
    simp [← Scheme.Hom.comp_preimage]
  have hle' : g.toNormalization ⁻¹ᵁ g.fromNormalization ⁻¹ᵁ U ≤ g ⁻¹ᵁ U := by
    simp [← Scheme.Hom.comp_preimage]
  set ρ := Z.presheaf.map (homOfLE hle).op with hρ
  have key := g.normalizationObjIso_hom_val hU
  have hρinj : Function.Injective ρ := by
    intro u v huv
    have := congrArg (Z.presheaf.map (homOfLE hle').op) huv
    have h1 : (homOfLE hle).op ≫ (homOfLE hle').op = 𝟙 (Opposite.op (g.toNormalization ⁻¹ᵁ g.fromNormalization ⁻¹ᵁ U)) :=
      Quiver.Hom.unop_inj (Subsingleton.elim _ _)
    simpa [hρ, ← CommRingCat.comp_apply, ← Functor.map_comp, h1] using this

  have hint : IsIntegral (integralClosure Γ(S, U) Γ(Z, g ⁻¹ᵁ U)) (ρ b) := by
    obtain ⟨p, hm, hp⟩ := hb
    refine ⟨p.map (g.normalizationObjIso hU).hom.hom, hm.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have e : (algebraMap (integralClosure Γ(S, U) Γ(Z, g ⁻¹ᵁ U)) Γ(Z, g ⁻¹ᵁ U)).comp
        (g.normalizationObjIso hU).hom.hom = ρ.hom.comp (g.toNormalization.app _).hom := by
      have := congrArg CommRingCat.Hom.hom key
      rw [Scheme.Hom.appLE] at this
      exact this
    rw [e, ← Polynomial.hom_eval₂, hp, map_zero]
  have hmem : ρ b ∈ (⊥ : Subalgebra (integralClosure Γ(S, U) Γ(Z, g ⁻¹ᵁ U)) Γ(Z, g ⁻¹ᵁ U)) := by
    rw [← integralClosure_idem]; exact hint
  obtain ⟨z, hz⟩ := Algebra.mem_bot.mp hmem
  refine ⟨(g.normalizationObjIso hU).inv z, hρinj ?_⟩
  have := congrArg (fun φ => φ ((g.normalizationObjIso hU).inv z)) (congrArg CommRingCat.Hom.hom key)
  simp only [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply] at this
  rw [← this, ← hz]
  simp

end LateralTheory.E.RelNormPf
end
end

